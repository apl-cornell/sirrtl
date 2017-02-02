package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import scala.collection.mutable.Set

object InferLabels extends Pass with PassDebug {
  def name = "Label Inference"
  override def debugThisPass = true

  val top = PolicyHolder.policy.top

  // 1. (Recursively) check that all ports are labeled
  // 2. Collect mapping: male exprs -> Set[female exprs]
  // 3. For males with unknown labels, propagate meet over female set to male
  // 4. Collect set of "locations" with known labels
  // 5. Propagate labels from 4 to declarations
  // 6. Propagate labels from declarations to expressions
  // 7. Forward-propagate: for locs with an empty female-set propagate from 
  //    input
  // 8. 2-7 until labels are all known

  def label_is_known(l: Label): Boolean = LabelExprs.label_is_known(l)
  def to_bundle(t: Type, l: Label) : Label = LabelExprs.to_bundle(t, l)
  def assumeL(l: Label) : Label = LabelExprs.assumeL(l)

  //-----------------------------------------------------------------------------
  // Check that ports are labeled (Step 1)
  //-----------------------------------------------------------------------------
  class UnlabeledPortException(info: Info, name: String) extends PassException(
    s"$info: Port [$name] is not labeled")
  class InferenceFailed(p:Int, m:DefModule) extends PassException(
    s"Label inference failed after $p attempts:\n${m.serialize}")

  val errors = new Errors()

  def check_ports(m: DefModule) : Unit =
    m.ports foreach { p => check_ports_p(p) }

  def check_ports_p(p: Port) : Unit = 
    if(!label_is_known(to_bundle(p.tpe, p.lbl)))
      errors.append(new UnlabeledPortException(p.info, p.name))

  //-----------------------------------------------------------------------------
  // Compute mapping: m:Male Expr -> Set[f: Female Expr] s.t. all f conn to m 
  // (Step 2)
  //-----------------------------------------------------------------------------
  class FemaleEnv extends scala.collection.mutable.HashMap[Expression,Set[Expression]]{
    override def default(e: Expression) = Set[Expression]() 

    // Equivalent up to type, label, kind, gender
    def weak_equiv(e1: Expression, e2: Expression): Boolean = e1 match {
      case e1x: WRef => e2 match {
        case e2x: WRef => e1x.name == e2x.name
        case e2x => false
      }
      case e1x: WSubField => e2 match {
        case e2x: WSubField => e1x.name == e2x.name && weak_equiv(e1x.exp,e2x.exp)
        case e2x => false
      }
      case e1x: WSubIndex => e2 match {
        case e2x: WSubIndex => e1x.value == e2x.value && weak_equiv(e1x.exp,e2x.exp)
        case e2x => false
      }
      case e1x: WSubAccess => e2 match {
        case e2x: WSubAccess => weak_equiv(e1x.index, e2x.index) && weak_equiv(e1x.exp,e2x.exp)
        case e2x => false
      }
      case e1x => e1x == e2
    }

    // get value for any weakly equivalent key
    override def apply(e: Expression) = {
      super.apply(keys.find( k => weak_equiv(k, e)).getOrElse(e))
    }
    // is there a key weakly equivalent to e?
    override def contains(e: Expression) = {
      keys.find( k => weak_equiv(k,e) ) match {
        case Some(_) => true
        case None => false
      }
    }
  }

  def collect_male(m: DefModule): FemaleEnv= {
    val env = new FemaleEnv
    m map collect_male_s(env)
    env
  }
  
  def collect_male_s(fenv: FemaleEnv)(s: Statement): Statement =  {
    s map collect_male_s(fenv) match {
      case sx : Connect => collect_male_e(fenv)(sx.loc)(sx.expr); sx
      case sx : PartialConnect => collect_male_e(fenv)(sx.loc)(sx.expr); sx
      case sx => sx
    }
  }

  def collect_male_e(fenv: FemaleEnv)(loc: Expression)(valu: Expression) : Expression = {
    def up_map(e1: Expression, e2: Expression) =
      fenv += (e1 -> (fenv(e1) ++ Set(e2)))
    valu map collect_male_e(fenv)(loc) match {
      case e: WRef => up_map(e, loc); e
      case e: WSubField => up_map(e, loc); e
      case e: WSubIndex => up_map(e, loc); e
      case e: WSubAccess => up_map(e, loc); e
      case e => e
    }
  }
 
  //-----------------------------------------------------------------------------
  // Propagate Meet over Female Env to Male Exprs
  // (Step 3)
  //-----------------------------------------------------------------------------
  def label_males(fenv: FemaleEnv)(m: DefModule): DefModule =
    m map label_males_s(fenv)

  def label_males_s(fenv: FemaleEnv)(s: Statement): Statement =
    s map label_males_s(fenv) map label_males_e(fenv)

  def label_males_e(fenv: FemaleEnv)(e: Expression): Expression = {
    val ex = e map label_males_e(fenv)
    if(gender(ex) == MALE && !label_is_known(ex.lbl)) {
     // dprintb(s"reaching unlabled male ${ex.serialize} {${ex.lbl}}")
      // fenv(ex) foreach { exx =>
      //   dprintb(s"female: ${exx.serialize} {${exx.lbl}}") }
      // Compute meet over females from which this male is assigned
      val new_lbl = if(fenv(ex).isEmpty) UnknownLabel else
        (fenv(ex) map { _.lbl }).reduceLeft(MeetLabel(_, _))
      // dprintb(s"new label: ${new_lbl.serialize}")

      // Copy new_label to expr
      val exx = ex map { l:Label => new_lbl } 
      //dprintb(s"reaching post-labeling ${exx.serialize} {${exx.lbl}}")
      exx
    } else {
      ex
    }
  }

  //-----------------------------------------------------------------------------
  // Propagate Known Labels (Steps 4-6)
  //-----------------------------------------------------------------------------
  type LabelMap = collection.mutable.LinkedHashMap[String, Label]
  def propagate_known(labels: LabelMap)(m: DefModule) : DefModule = {
    m map LabelExprs.label_exprs_p(labels) map propagate_known_s(labels)
  }

  def propagate_known_s(labels: LabelMap)(s: Statement): Statement = 
    s map propagate_known_s(labels) map propagate_known_e(labels) match {
      case sx: WDefInstance =>
        if(label_is_known(sx.lbl)) {labels += (sx.name -> sx.lbl); sx}
        else if(labels.contains(sx.name)) sx copy (lbl = labels(sx.name))
        else sx
      case sx: DefWire =>
        if(label_is_known(sx.lbl)) {labels += (sx.name -> sx.lbl); sx}
        else if(labels.contains(sx.name)) sx copy (lbl = labels(sx.name))
        else sx
      case sx: DefRegister =>
        if(label_is_known(sx.lbl)) {labels += (sx.name -> sx.lbl); sx}
        else if(labels.contains(sx.name)) sx copy (lbl = labels(sx.name))
        else sx
      case sx: DefNode =>
        if(label_is_known(sx.value.lbl)) labels += (sx.name -> sx.value.lbl)
        sx
      case sx => sx 
    }

  def propagate_known_e(labels: LabelMap)(e: Expression): Expression = {
    //dprintb(s"labeling ${e.serialize} {${e.lbl}}")
    //dprintb(s"labels: ${labels.toString}")
    val eprime = e map propagate_known_e(labels) match {
      case ex: WRef =>
        if(label_is_known(ex.lbl)) { labels += (ex.name -> ex.lbl); ex }
        else if(labels.contains(ex.name)) ex copy (lbl = labels(ex.name))
        else ex
      case ex: Next =>
        if(label_is_known(ex.exp.lbl)) ex copy (lbl = ex.exp.lbl)
        else ex
      case ex: WSubField =>
        if(label_is_known(ex.lbl) && !label_is_known(ex.exp.lbl)) {
          val lprime = propagate_field_up(ex)
          ex copy ( exp = ( relabel(ex.exp, lprime) ) )
        } else if(!label_is_known(ex.lbl) && label_is_known(ex.exp.lbl)) {
          ex copy (lbl = field_label(ex.exp.lbl, ex.name))
        } else ex
      case ex: WSubIndex => ex copy (lbl = ex.exp.lbl)
      case ex: WSubAccess => ex copy (lbl = JoinLabel(ex.exp.lbl, ex.index.lbl))
      case ex: DoPrim => ex copy (lbl = JoinLabel((ex.args map{ _.lbl }):_* ))
      case ex: Mux => ex copy (lbl = JoinLabel(ex.cond.lbl,
        ex.tval.lbl, ex.fval.lbl))
      case ex: ValidIf => ex copy (lbl = JoinLabel(ex.cond.lbl, ex.value.lbl))
      case ex: UIntLiteral => ex copy (lbl = assumeL(ex.lbl))
      case ex: SIntLiteral => ex copy (lbl = assumeL(ex.lbl))
    }
    //dprintb(s"post-labeling: ${eprime.serialize} {${eprime.lbl}}")
    eprime
  }

  // This might be too fancy... attempt to gradually infer bundle
  // labels from the labels of references to subfields
  def propagate_field_up(e: WSubField): Label = {
    e.exp.lbl match {
      case lx : BundleLabel if (lx.fields.contains(e.name)) =>
        lx copy (fields = lx.fields map { f =>
          if( f.name == e.name ) (f copy (lbl = e.lbl)) else f
        })
      case lx : BundleLabel if (!lx.fields.contains(e.name)) =>
        lx copy (fields = lx.fields ++
          Seq(Field(e.name, Default, UnknownType, e.lbl, false)))
      case UnknownLabel =>
        BundleLabel(Seq(Field(e.name, Default, UnknownType, e.lbl, false)))
      case lx => dprintb(s"crazyfield $e"); lx
    }
  }

  //-----------------------------------------------------------------------------
  // Forward-propagate (Step 7)
  //-----------------------------------------------------------------------------
  // For locations w/o explicit outward flows, try to infer labels from inputs
  def forward_propagate(fenv: FemaleEnv)(m: DefModule): DefModule = 
    m map forward_propagate_s(fenv)

  def forward_propagate_s(fenv: FemaleEnv)(s: Statement): Statement = {
    def lk(l: Label) = label_is_known(l)
    
    def forward_prop(loc: Expression, valu: Expression) : Expression =
      if(fenv(loc).isEmpty && !lk(loc.lbl) && lk(valu.lbl))
        loc map {l: Label => valu.lbl}
      else loc

    s map forward_propagate_s(fenv) match {
      case Connect(info,loc,expr) => 
        Connect(info,forward_prop(loc,expr),expr)
      case PartialConnect(info,loc,expr) => 
        PartialConnect(info,forward_prop(loc,expr),expr)
      case sx => sx
    }
  }
  

  //-----------------------------------------------------------------------------
  // Determine if all labels are known
  //-----------------------------------------------------------------------------
  def labels_known(m: DefModule): Boolean = {
    var ret = true

    def lk(l: Label): Boolean = label_is_known(l)

    def labels_known_s(s: Statement): Statement = 
      s map labels_known_s map labels_known_e match {
      case sx: WDefInstance => if(!lk(sx.lbl)) ret = false; sx
      case sx: DefWire => if(!lk(sx.lbl)) ret = false; sx
      case sx: DefRegister => if(!lk(sx.lbl)) ret = false; sx
      case sx => sx
    }

    def labels_known_e(e: Expression): Expression = {
      val ex = e map labels_known_e
      if(!lk(ex.lbl)) ret = false
      ex
    }

    m map labels_known_s
    ret
  }

  //-----------------------------------------------------------------------------
  // Debug utils
  //-----------------------------------------------------------------------------

  def pretty_print_fenv(fenv: FemaleEnv) : String = {
    def ep(e: Expression) = s"${e.serialize} {${e.lbl.serialize}}"
    (fenv map { case (k: Expression, v: Set[Expression]) =>
      s"${k.serialize}" + "->Set(" + (v map ep).reduceLeft(_+", "+_) + ")\n"
    }).foldLeft("")(_+_) + "\n"
  }

  def run(c: Circuit) = {
    bannerprintb(name)
    dprint(c.serialize)

    dprintb("about to check ports")
    c.modules foreach check_ports
    dprintb(s"errors: ${errors.errors}")
    dprintb("past port check")

    val cprime = c copy (modules = c.modules map { m =>
      dprintb(s"checking module ${m.name}")
      var pass = 0;
      var mprime = m
      val labels = new LabelMap
      while(!labels_known(mprime) && pass < 10) {
        bannerprintb(s"about to propagate")
        mprime = propagate_known(labels)(mprime)
        val fenv = collect_male(mprime)
        bannerprintb(s"collected fenv:")
        dprintb(s"fenv:\n${pretty_print_fenv(fenv)}")
        bannerprintb(s"about to collect labels from fenv:")
        mprime = label_males(fenv)(mprime)
        bannerprintb(s"about to forward propagate:")
        mprime = forward_propagate(fenv)(mprime)
        bannerprintb(s"after forward-propagation:")
        dprintb(s"${mprime.serialize}")
        bannerprintb(s"after pass $pass")
        dprintb(s"${mprime.serialize}")
        pass += 1
      }
      if(!labels_known(mprime))
        errors.append(new InferenceFailed(pass,mprime))
      mprime
    })

    bannerprintb("after label inference")
    dprint(cprime.serialize)
 
    errors.trigger()
    cprime
  }
}
