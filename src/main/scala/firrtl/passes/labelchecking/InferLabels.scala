package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import scala.collection.mutable.Set

object InferLabels extends Pass with PassDebug {
  def name = "Label Inference"
  override def debugThisPass = true
  
  val bot = ProdLabel(PolicyHolder.bottom, PolicyHolder.top)
  val top = ProdLabel(PolicyHolder.top, PolicyHolder.bottom)

  // Mapping from label vars to labels
  class LabelVarEnv extends collection.mutable.HashMap[VarLabel, Label] {
    override def default(l:VarLabel) = top
  }

  // Constraints of the form L1 flowsto L2
  class ConstrSet extends collection.mutable.HashSet[(Label, Label)] {
    override def toString: String = {
      var s = ""
      this.foreach { case(l1: Label, l2: Label) =>
        s = s + s"${l1.serialize} flowsto ${l2.serialize}\n"
      }
      s
    }
  }

  // Recursively swap instances of a VarLabel with another Label
  def swapVar(l: Label, newL: Label, id: String): Label = {
    def swapVar_(l: Label): Label = l map swapVar_ match {
      case VarLabel(idx) if idx == id => newL
      case lx => lx
    }
    swapVar_(l)
  }

  //-----------------------------------------------------------------------------
  // Main Label Inference Sequence
  //-----------------------------------------------------------------------------
  def infer_labels(m: DefModule): DefModule = {
    val env = new LabelVarEnv
    val conSet = gen_constr(m)
    dprint("generated constraints:")
    dprint(conSet.toString)
    resolve_constraints(env, conSet)
    prop_env_m(env)(m)
  }

  //-----------------------------------------------------------------------------
  // Constraint Generation
  //-----------------------------------------------------------------------------
  def gen_constr(m: DefModule): ConstrSet = {
    val conSet = new ConstrSet
    gen_constr_m(conSet)(m)
    conSet
  }

  def gen_constr_m(conSet: ConstrSet)(m: DefModule): DefModule = 
    m map gen_constr_s(conSet)
 
  def gen_constr_s(conSet: ConstrSet)(s: Statement): Statement =
    s map gen_constr_s(conSet) match {
      case sx: ConnectPC => 
        canon_labels(sx.expr) foreach { v => conSet += ((v, sx.loc.lbl)) }
        canon_labels(sx.pc)   foreach { v => conSet += ((v, sx.loc.lbl)) }
        sx
      case sx: PartialConnectPC =>
        canon_labels(sx.expr) foreach { v => conSet += ((v, sx.loc.lbl)) }
        canon_labels(sx.pc)   foreach { v => conSet += ((v, sx.loc.lbl)) }
        sx
      case sx: DefNodePC =>
        canon_labels(sx.value) foreach { v => conSet += ((v, sx.lbl)) }
        canon_labels(sx.pc)   foreach { v => conSet += ((v, sx.lbl)) }
        sx
      case sx => sx
    }

  // Returns the set of canonical-form labels in the label of expr e. Labels 
  // resulting from a join cannot appear in the LHS of a constraint in 
  // canonical form.
  // This whole inference algorithm also assumes that meets do not appear in 
  // the syntax of labels (other than as a result of resolving constraints in 
  // this inference algorithm). See CH 5 of Andrew Myers' thesis for more
  // details.
  type lset = collection.mutable.HashSet[Label]
  def canon_labels(e: Expression): Set[Label] = {
    val ret = new lset
    (e map canon_labels_l(ret)); ret
  }

  def canon_labels(l: Label): Set[Label] = {
    val ret = new lset
    canon_labels_l(ret)(l); ret
  }

  def canon_labels_l(s: lset)(l: Label): Label =  l match {
    case lx: MeetLabel => throw new Exception
    case lx: JoinLabel => lx map canon_labels_l(s)
    case lx: ProdLabel => s += lx; lx
    case lx: VarLabel => s += lx; lx
    case lx: BundleLabel  => s += lx; lx 
  }
  
  //-----------------------------------------------------------------------------
  // Constraint Resoluton
  //-----------------------------------------------------------------------------
  // XXX there is supposed to be some contradiction case... this does not test 
  // for a contradiction, but I think z3 will catch contradictions.
  def resolve_constraints(env: LabelVarEnv, conSet: ConstrSet): Unit = {
    conSet foreach { case (l1: Label, l2: Label) =>
      l1 match {
        case lx: VarLabel =>
          env(lx) = env(lx) meet resolve_label(env)(l2)
        case _ =>
      }
    }
  }

  def resolve_label(env: LabelVarEnv)(l: Label): Label = 
    l map resolve_label(env) match {
      case lx: VarLabel => env(lx)
      case lx => lx
    }

  //-----------------------------------------------------------------------------
  // Label Environment Propagation
  //-----------------------------------------------------------------------------
  def prop_env_m(env: LabelVarEnv)(m: DefModule): DefModule =
    m map prop_env_s(env)

  def prop_env_s(env: LabelVarEnv)(s: Statement): Statement = 
    s map prop_env_s(env) map prop_env_e(env) map prop_env_l(env)

  def prop_env_e(env: LabelVarEnv)(e: Expression): Expression =
    e map prop_env_e(env) map prop_env_l(env)

  // Meets/Joins that formerly contained VarLabels should now only 
  // have resolved labels so re-apply the builder to get a simple label
  def prop_env_l(env: LabelVarEnv)(l: Label): Label = 
    l map prop_env_l(env) match {
      case lx: VarLabel => env(lx)
      case JoinLabel(l, r) => l join r
      case MeetLabel(l, r) => l meet r
      case lx => lx
    }

  //-----------------------------------------------------------------------------
  // Run
  //-----------------------------------------------------------------------------
  def run(c: Circuit) = {
    bannerprintb(name)
    dprint(c.serialize)

    val cprime = c copy (modules = c.modules map infer_labels)
    
    bannerprintb(s"after $name")
    dprint(cprime.serialize)
 
    cprime
  }

}
