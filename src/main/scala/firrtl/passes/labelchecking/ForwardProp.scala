package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import scala.collection.mutable.Set

// This pass infers the labels of some expressions by doing forward propagation 
// only for signals which are assigned in exactly one location.
object ForwardProp extends Pass with PassDebug {
  def name = "Label Forward Propagation"
  override def debugThisPass = false

  val bot = ProdLabel(PolicyHolder.bottom, PolicyHolder.top)
  val top = ProdLabel(PolicyHolder.top, PolicyHolder.bottom)

  def simplifyLabel(l: Label): Label = SimplifyLabels.cnf_lb(l)

  type LabelVarMap = collection.mutable.LinkedHashMap[VarLabel, Label]
  
  def gen_cons(once: LabelVarMap, more: LabelVarMap)(m: DefModule): DefModule = 
    m map gen_cons_s(once, more)

  def gen_cons_s(once: LabelVarMap, more: LabelVarMap)(s: Statement): Statement =
    s map gen_cons_s(once, more) match {
      case sx: ConnectPC => 
        constrain_flow(once, more)(sx.expr.lbl join sx.pc, sx.loc.lbl)
        sx
      case sx: PartialConnectPC =>
        constrain_flow(once, more)(sx.expr.lbl join sx.pc, sx.loc.lbl)
        sx
      case sx: DefNodePC =>
        constrain_flow(once, more)(sx.value.lbl, sx.lbl)
        sx
      case sx => sx
    }

  def constrain_flow(once: LabelVarMap, more: LabelVarMap)(from: Label, to: Label): Unit =
    (from, to) match {
      case ((fromb: BundleLabel, tob: BundleLabel)) =>
        fromb.fields.foreach { f =>
          val fromx = f.lbl
          val tox = field_label(tob, f.name)
          constrain_flow(once, more)(fromx, tox)
        }
      case ((fromb: BundleLabel, _)) =>
        fromb.fields.foreach { f =>
          val fromx = f.lbl
          constrain_flow(once, more)(fromx, to)
        }
      case ((_, tob: BundleLabel)) =>
        tob.fields.foreach { f =>
          val tox = f.lbl
          constrain_flow(once, more)(from, tox)
        }
      case _ => to match {
        case (tox: VarLabel) => 
          if( once.contains(tox) ){
            more(tox) = once(tox)
            once.remove(tox)
          } else if( !more.contains(tox) ) {
            once(tox) = from
          }
        case _ =>
      }
    }

  def prop_env_m(env: LabelVarMap)(m: DefModule): DefModule =
    m map prop_env_s(env)
  
  def prop_env_s(env: LabelVarMap)(s: Statement): Statement = 
    s map prop_env_s(env) map prop_env_e(env) map prop_env_l(env)

  def prop_env_e(env: LabelVarMap)(e: Expression): Expression =
    e map prop_env_e(env) map prop_env_l(env)

  def prop_env_l(env: LabelVarMap)(l: Label): Label = 
    l map prop_env_l(env) match {
      case lx: VarLabel if env.contains(lx) => env(lx)
      case lx => lx
    }

  def forward_prop(m: DefModule): DefModule = {
    val once = new LabelVarMap
    val more = new LabelVarMap
    gen_cons(once, more)(m)
    prop_env_m(once)(m)
  }

  def run(c: Circuit) = {
    bannerprintb(name)
    dprint(c.serialize)

    val cprime = c copy (modules = c.modules map forward_prop)

    bannerprintb(s"after $name")
    dprint(cprime.serialize)

    cprime
  }


}
