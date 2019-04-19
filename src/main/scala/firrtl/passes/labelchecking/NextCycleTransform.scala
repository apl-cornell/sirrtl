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
  def next_ident(n: String, t: Type) = PullNexts.next_ident(n,t)

  def declare_next_s(s: Statement) : Statement =
    s map declare_next_s match {
      case sx : DefRegister =>
        val next_l = swap_with_next_l(sx.lbl)
        val ref_sx = WRef(sx.name, sx.tpe, sx.lbl, WireKind, FEMALE)
        val next_w = next_exp(
          WRef(sx.name, sx.tpe, next_l, WireKind, FEMALE))
        val dec_next = DefWire(sx.info, next_ident(sx.name,sx.tpe), sx.tpe, next_l)
        val define_reg = Connect(sx. info, ref_sx,
          WRef(next_ident(sx.name, sx.tpe), sx.tpe, sx.lbl, RegKind, MALE))
        val default_next = Connect(sx.info, next_w,
          WRef(sx.name, sx.tpe, sx.lbl, RegKind, MALE))
        Block(Seq(sx, dec_next, define_reg, default_next))
      case sx => sx
    }

  def declare_next(m: DefModule) : DefModule =
    m map declare_next_s

  def swap_with_next_l(l: Label) : Label =
    l map swap_with_next_l map swap_with_next_lc

  def swap_with_next_lc(l: LabelComp): LabelComp =
    l map swap_with_next_lc map swap_with_next_de

  // This function is only called on expressions appearing in dependant types.
  // Replace sequential dependands with the next-cycle version of the 
  // dependand. It swaps regardless of gender
  def swap_with_next_de(e: Expression) : Expression =
    e map swap_with_next_de match {
      case ex: WRef if ex.kind == RegKind => next_exp(ex)
//      case ex: WRef if ex.kind == PortKind => next_exp(ex)
      case ex: WSubField if PullNexts.is_simple_p_subf(ex) &&
        field_seq(ex.exp.tpe, ex.name) => next_exp(ex)
      case ex => ex
    }

  // This function is called on expressions *not* inside of labels.
  // It should replace female sequential references with nextified versions.
  def swap_with_next_e(e: Expression) : Expression =
    e map swap_with_next_e match {
      case ex: WRef if ex.kind == RegKind && ex.gender == FEMALE =>
        val next_l = swap_with_next_l(ex.lbl)
        next_exp(ex.copy(lbl = next_l))
      case ex: WSubField if kind(ex) == PortKind && gender(ex) == FEMALE
        && field_seq(ex.exp.tpe, ex.name) =>
        val next_l = swap_with_next_l(ex.lbl)
        ex.copy(lbl = next_l)
      case ex if kind(ex) == RegKind && gender(ex) == FEMALE =>
        val next_l = swap_with_next_l(ex.lbl)
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
