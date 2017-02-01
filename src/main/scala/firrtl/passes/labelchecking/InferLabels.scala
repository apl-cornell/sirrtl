package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import firrtl.UnionTypes._
import scala.collection.mutable.Set

object InferLabels extends Pass with PassDebug {
  def name = "Label Inference"
  override def debugThisPass = true

  val top = PolicyHolder.policy.top

  // 1. (Recursively) check that all output ports are labeled
  // 2. Collect mapping: male exprs -> Set[female vals]
  // 3. For males with unknown labels, propagate meet over female set to male
  // 4. Collect set of "locations" with known labels
  // 5. Propagate labels from 4 to locs and declarations equivalent upto labels
  // 6. 3-5 until labels are all known
  // TODO do we know that all output ports are defined?

  def label_is_known(l: Label): Boolean = LabelExprs.label_is_known(l)
  def to_bundle(t: Type, l: Label) : Label = LabelExprs.to_bundle(t, l)
  def assumeL(l: Label) : Label = LabelExprs.assumeL(l)

  //-----------------------------------------------------------------------------
  // Check that ports are labeled
  //-----------------------------------------------------------------------------
  class UnlabeledPortException(info: Info, name: String) extends PassException(
    s"$info: Port [$name] is not labeled")
  val errors = new Errors()

  def check_ports(m: DefModule) : Unit =
    m.ports foreach { p => check_ports_p(p) }

  def check_ports_p(p: Port) : Unit = 
    if(!label_is_known(to_bundle(p.tpe, p.lbl)))
      errors.append(new UnlabeledPortException(p.info, p.name))

  //-----------------------------------------------------------------------------
  // Compute mapping: m:Male Expr -> Set[f: Female Expr] s.t. all f conn to m
  //-----------------------------------------------------------------------------
  class FemaleEnv extends scala.collection.mutable.HashMap[Expression,Set[Expression]]{
    override def default(e: Expression) = Set[Expression]() 
  }

  def collect_male(m: DefModule): FemaleEnv= {
    val env = new FemaleEnv
    m map collect_male_s(env)
    env
  }
  
  def collect_male_s(fenv: FemaleEnv)(s: Statement): Statement = 
    s map collect_male_s(fenv) match {
      case sx : Connect => fenv += (sx.expr -> (fenv(sx.expr) ++ Set(sx.expr))); sx
      case sx : PartialConnect => fenv += (sx.expr -> (fenv(sx.expr) ++ Set(sx.expr))); sx
  }
 
  //-----------------------------------------------------------------------------
  // Propagate Meet over Female Env to Male Exprs
  //-----------------------------------------------------------------------------
  def label_males(fenv: FemaleEnv)(m: DefModule): DefModule =
    m map label_males_s(fenv)

  def label_males_s(fenv: FemaleEnv)(s: Statement): Statement =
    s map label_males_s(fenv) map label_males_e(fenv)

  def label_males_e(fenv: FemaleEnv)(e: Expression): Expression = {
    val ex = e map label_males_e(fenv)
    if(gender(ex) == MALE && !label_is_known(ex.lbl)) {
      // Compute meet over females from which this male is assigned
      val new_lbl = (fenv(ex) map { _.lbl }).foldLeft(top:Label)(MeetLabel(_, _))
      // Copy new_label to expr
      ex map { l:Label => new_lbl } 
    } else {
      ex
    }
  }
  
  //-----------------------------------------------------------------------------
  // Propagate Known Labels
  //-----------------------------------------------------------------------------
  type LabelMap = collection.mutable.LinkedHashMap[String, Label]
  def propagate_known(m: DefModule) : DefModule = {
    m map propagate_known_s(new LabelMap)
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
        sx
      case sx: DefRegister =>
        if(label_is_known(sx.lbl)) {labels += (sx.name -> sx.lbl); sx}
        else if(labels.contains(sx.name)) sx copy (lbl = labels(sx.name))
        sx
      case sx: DefNode =>
        if(label_is_known(sx.value.lbl)) labels += (sx.name -> sx.value.lbl)
        sx
      case sx => sx 
    }

  def propagate_known_e(labels: LabelMap)(e: Expression): Expression =
    e map propagate_known_e(labels) map propagate_known_e(labels) match {
      case ex: WRef =>
        if(label_is_known(ex.lbl)) labels += (ex.name -> ex.lbl)
        if(labels.contains(ex.name)) ex copy (lbl = labels(ex.name))
        ex
      case ex: Next =>
        if(label_is_known(ex.exp.lbl)) ex copy (lbl = ex.exp.lbl)
        ex
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

  def run(c: Circuit) = {
    bannerprintb(name)
    dprint(c.serialize)

    dprintb("about to check ports")
    c.modules foreach check_ports
    dprintb("past port check")
    val cprime = c 

    bannerprintb("after label inference")
    dprint(cprime.serialize)
 
    errors.trigger()
    cprime
  }
}
