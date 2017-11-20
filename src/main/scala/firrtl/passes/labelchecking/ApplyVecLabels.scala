package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.Utils._

object ApplyVecLabels extends Pass with PassDebug {
  override def name = "Apply indexes to vector labels"
  override def debugThisPass = false

  def apply_index_vech(l: Label, idx: Expression): Label = {
    def apply_index_c(idx: Expression)(lc: LabelComp): LabelComp = 
      lc map apply_index_c(idx) match {
        case lcx: VecHLevel => dprintb("applying"); IndexedVecHLevel(lcx.arr, idx)
        case lcx => lcx
      }
    def apply_index_(idx: Expression)(l: Label): Label = 
      l map apply_index_(idx) map apply_index_c(idx)
    apply_index_(idx)(l)
  }
  
  def apply_vec_labels_e(e: Expression) : Expression =
    e map apply_vec_labels_e match {
      case ex: WSubIndex => 
        dprintb(s"subIndex: ${ex.serialize}")
        dprintb(ex.toString)
        val lbl_ = apply_index_vech(ex.exp.lbl, uint(ex.value))
        ex copy (lbl = lbl_)
      case ex: WSubAccess => 
        dprintb(s"subAccess: ${ex.serialize}")
        dprintb(ex.toString)
        val lbl_ = apply_index_vech(ex.exp.lbl, ex.index)
        ex copy (lbl = JoinLabel(lbl_, ex.index.lbl))
      case ex => ex
    }

  def apply_vec_labels_s(s: Statement): Statement =
    s map apply_vec_labels_s map apply_vec_labels_e

  def apply_vec_labels(m: DefModule): DefModule = {
    m map apply_vec_labels_s
  }

  def run(c: Circuit) = {
    bannerprintb(name)
    // dprint(c.serialize)
    val cprime = c copy (modules = c.modules map apply_vec_labels)
    bannerprintb(s"after $name")
    // dprint(cprime.serialize)
    cprime
  }

}
