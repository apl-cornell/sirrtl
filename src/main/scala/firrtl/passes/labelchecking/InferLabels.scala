package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import scala.collection.mutable.Set

object InferLabels extends Pass with PassDebug {
  def name = "Label Inference"
  override def debugThisPass = false

  // TODO: I had to comment out these debug prints since it seems like for real 
  // rocket code evaluting the interpolated strings takes non-trivial time. I 
  // wish I had C-style macros for this, but maybe I can get what I want by 
  // making the argument of dprint a call-by-name argument
  
  val bot = ProdLabel(PolicyHolder.bottom, PolicyHolder.top)
  val top = ProdLabel(PolicyHolder.top, PolicyHolder.bottom)

  def simplifyLabel(l: Label): Label = SimplifyLabels.cnf_lb(l)

  // Mapping from label vars to labels
  class LabelVarEnv extends collection.mutable.HashMap[VarLabel, Label] {
    override def default(l:VarLabel) = top
    override def toString ={
      var s = ""
      this.foreach { case(k: VarLabel, v: Label) =>
        s = s + s"{${k.serialize}} -> {${v.serialize}}, "
      }
      s
    }

  }

  // Constraints of the form L1 flowsto L2
  class ConstrSet extends collection.mutable.LinkedHashSet[(Label, Label)] {
    override def toString: String = {
      var s = ""
      this.foreach { case(l1: Label, l2: Label) =>
        s = s + s"${l1.serialize} flowsto ${l2.serialize}\n"
      }
      s
    }
  }

  class AdjList extends collection.mutable.LinkedHashMap[VarLabel,Set[VarLabel]] {
    override def default(l: VarLabel) = Set()
    override def toString: String = {
      var s = ""
      this.foreach { case(v: VarLabel, adj: Set[VarLabel]) =>
         s = s + s"${v.serialize} ${adj.toString}\n"
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
    dprint("generating constraints")
    val conSet = gen_constr(m)
    dprint(s"generated constraints (${m.name}):")
    dprint(conSet.toString)
    val pred = compute_pred(conSet)
    dprint(s"computed predecessors:")
    dprint(pred.toString)
    resolve_constraints(env, conSet, pred)
    dprint(s"env after resolving constraints (${m.name}):")
    dprint(env.toString)
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
        constrain_flow(conSet)(sx.expr.lbl, sx.loc.lbl)
        constrain_flow(conSet)(sx.pc, sx.loc.lbl)
        sx
      case sx: PartialConnectPC =>
        constrain_flow(conSet)(sx.expr.lbl, sx.loc.lbl)
        constrain_flow(conSet)(sx.pc, sx.loc.lbl)
        sx
      case sx: DefNodePC =>
        constrain_flow(conSet)(sx.value.lbl, sx.lbl)
        sx
      case sx => sx
    }

  def constrain_flow(conSet: ConstrSet)(from: Label, to: Label): Unit =
  {
    (from, to) match {
      case ((fromb: BundleLabel, tob: BundleLabel)) =>
        fromb.fields.foreach { f =>
          val fromx = f.lbl
          val tox = field_label(tob, f.name)
          constrain_flow(conSet)(fromx, tox)
        }
      case ((fromb: BundleLabel, _)) =>
        fromb.fields.foreach { f =>
          val fromx = f.lbl
          constrain_flow(conSet)(fromx, to)
        }
      case ((_, tob: BundleLabel)) =>
        tob.fields.foreach { f =>
          val tox = f.lbl
          constrain_flow(conSet)(from, tox)
        }
      case _ =>
        canon_labels(from) foreach { v => v match {
            case (_:VarLabel) => conSet += ((v, to)) 
            case _ =>
          }
        }
    }
  }

  // Returns the set of canonical-form labels in the label. Labels 
  // resulting from a join cannot appear in the LHS of a constraint in 
  // canonical form.
  // This whole inference algorithm also assumes that meets do not appear in 
  // the syntax of labels (other than as a result of resolving constraints in 
  // this inference algorithm). See CH 5 of Andrew Myers' thesis for more
  // details.
  type lset = collection.mutable.HashSet[Label]
  def canon_labels(l: Label): Set[Label] = {
    val ret = new lset
    canon_labels_l(ret)(l); ret
  }

  def canon_labels_l(s: lset)(l: Label): Label =  l match {
    case lx: MeetLabel => throw new Exception
    case lx: BundleLabel  => throw new Exception
    case lx: IteLabel => lx map canon_labels_l(s)
    case lx: JoinLabel => lx map canon_labels_l(s)
    case lx: ProdLabel => s += lx; lx
    case lx: VarLabel => s += lx; lx
  }
  
  //-----------------------------------------------------------------------------
  // Compute adjacency lists:
  //-----------------------------------------------------------------------------
  def compute_succ(conSet: ConstrSet): AdjList = {
    val ret = new AdjList
    conSet foreach { case(l1: Label, l2: Label) =>
      l1 match {
        case lx: VarLabel =>
          ret(lx) = ret(lx) ++ vars_in(l2)
        case _ =>
      }
    }
    ret
  }

  def compute_pred(conSet: ConstrSet): AdjList = {
    val ret = new AdjList
    conSet foreach { case(l1: Label, l2: Label) =>
      vars_in(l2) foreach { v =>
        ret(v) = ret(v) ++ vars_in(l1)
      }
    }
    ret
  }

  def vars_in(l: Label): Set[VarLabel] = {
    val s = new collection.mutable.HashSet[VarLabel]
    def vars_in_(l: Label): Label = l map vars_in_ match {
      case lx: VarLabel => s += lx; lx
      case lx => lx
    }
    vars_in_(l); s
  }

  //-----------------------------------------------------------------------------
  // Constraint Resoluton
  //-----------------------------------------------------------------------------
  def resolve_constraints(env: LabelVarEnv, conSet: ConstrSet, pred: AdjList): Unit = {
    type ConstrList = collection.mutable.ListBuffer[(Label, Label)]

    while(!conSet.isEmpty) {
      val cons = conSet.last; conSet -= cons;
      cons match { case (l1: Label, l2: Label) =>
        dprint(s"resolving ${l1.lbl.serialize} flowsto ${l2.lbl.serialize}")
        dprint(s"before ${env.toString}")
        l1 match {
          case lx: VarLabel =>
            val lx_ = simplifyLabel(env(lx) meet resolve_label(env)(l2))
            if(lx_ != env(lx)) {
              env(lx) = lx_
              dprint(s"updating ${lx.serialize} to ${lx_.serialize}")
              pred(lx) foreach { v => conSet += ((v, lx_)) }
            }
          case _ =>
        }
        dprint(s"after ${env.toString}\n\n")
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
    simplifyLabel(l map prop_env_l(env) match {
      case lx: VarLabel => env(lx)
      case JoinLabel(l, r) => l join r
      case MeetLabel(l, r) => l meet r
      case lx => lx
    })

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
