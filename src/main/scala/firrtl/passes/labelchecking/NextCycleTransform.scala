package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils.{field_seq, _}
import firrtl.Mappers._
import firrtl.Driver._

import collection.mutable.Set

// TODO mems are sequential too!!!!

object NextCycleTransform extends Pass with PassDebug {
  def name = "Next Cycle Transform"
  override def debugThisPass = false
  val bot = PolicyHolder.policy.bottom

  def next_exp(e: Expression) = RipNexts.next_exp(e)
  def next_lbl(l: Label) : Label = RipNexts.next_lbl(l)

  // This function is called on expressions *not* inside of labels.
  // It should replace female sequential references with nextified versions.
  def swap_with_next_e(e: Expression) : Expression =
    e map swap_with_next_e match {
      case ex: WRef if ex.kind == RegKind && ex.gender == FEMALE =>
        next_exp(ex)
      case ex: WSubField if ex.gender == FEMALE && kind(ex) == RegKind =>
        next_exp(ex)
      case ex => ex
    }

  def swap_with_next_s(s: Statement) : Statement = {
    dprint(s.info.serialize)
    s map swap_with_next_s map swap_with_next_e
  }

  def swap_with_next(m: DefModule) : DefModule =
    m map swap_with_next_s map flatten_s

  def run(c: Circuit) = {
    bannerprintb(name)
    dprint(c.serialize)
    val cprime = c copy (modules =
      c.modules map swap_with_next)
    bannerprintb(s"after $name")
    dprint(cprime.serialize)
    cprime
  }

}
