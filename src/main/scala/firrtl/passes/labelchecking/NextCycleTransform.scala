package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import firrtl.Driver._
import collection.mutable.Set

// TODO mems are sequential too!!!!

object NextCycleTransform extends Pass with PassDebug {
  def name = "Next Cycle Transform"
  override def debugThisPass = false
  val bot = PolicyHolder.policy.bottom

  def next_exp(e: Expression) = PullNexts.next_exp(e)
  def next_ident(n: String) = PullNexts.next_ident(n)
  def next_lbl(l: Label) : Label = PullNexts.next_lbl(l)

  def declare_next_s(s: Statement) : Statement =
    s map declare_next_s match {
      case sx : DefRegister =>
        val next_l = next_lbl(sx.lbl)
        val ref_sx = WRef(sx.name, sx.tpe, sx.lbl, WireKind, FEMALE)
        val next_w = next_exp(
          WRef(sx.name, sx.tpe, sx.lbl, WireKind, FEMALE))
        val dec_next = DefWire(sx.info, next_ident(sx.name), sx.tpe, next_l)
        val define_reg = Connect(sx. info, ref_sx,
          WRef(next_ident(sx.name), sx.tpe, next_l, RegKind, MALE))
        val default_next = Connect(sx.info, next_w,
          WRef(sx.name, sx.tpe, sx.lbl, RegKind, MALE))
        Block(Seq(sx, dec_next, define_reg, default_next))
      case sx => sx
    }

  def declare_next(m: DefModule) : DefModule =
    m map declare_next_s

  // This function is called on expressions *not* inside of labels.
  // It should replace female sequential references with nextified versions.
  def swap_with_next_e(e: Expression) : Expression =
    e map swap_with_next_e match {
      case ex: WRef if ex.kind == RegKind && ex.gender == FEMALE =>
        next_exp(ex)
      case ex if kind(ex) == RegKind && gender(ex) == FEMALE =>
        val next_l = next_lbl(ex.lbl)
        setLabel(ex, next_l)
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
      c.modules map swap_with_next map declare_next)

    bannerprintb(s"after $name")
    dprint(cprime.serialize)
    cprime
  }

}
