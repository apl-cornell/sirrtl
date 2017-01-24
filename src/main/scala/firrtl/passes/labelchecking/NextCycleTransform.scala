package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import firrtl.Driver._
import collection.mutable.Set

object NextCycleTransform extends Pass with PassDebug {
  def name = "Next Cycle Transform"
  override def debugThisPass = true
  val bot = PolicyHolder.policy.bottom

  // TODO
  // Add a way to declare a port as sequential

  def next_ident(n: String) = "$" + n

  def declare_next_s(s: Statement) : Statement =
    s map declare_next_s match {
      case sx : DefRegister =>
        val next_n = next_ident(sx.name)
        val next_l = swap_with_next_l(sx.lbl)
        val dec_next_i = sx.info // TODO?
        val def_next_i = sx.info // TODO?
        val dec_next = DefWire(dec_next_i, next_n, sx.tpe, next_l)
        val def_next = Connect(def_next_i,
          WRef(next_n, sx.tpe, next_l, WireKind, FEMALE),
          WRef(sx.name, sx.tpe, sx.lbl, RegKind, MALE))
        Block(Seq(sx, dec_next, def_next))
      case sx => sx
    }

  def declare_next(m: DefModule) : DefModule =
    m map declare_next_s

  def swap_with_next_l(l: Label) : Label =
    l map swap_with_next_l map swap_with_next_de

  // This function is only called on expressions appearing in dependant types.
  // Replace sequential dependands with the next-cycle version of the 
  // dependand.
  def swap_with_next_de(e: Expression) : Expression = 
    e map swap_with_next_de match {
      case WRef(name, tpe, lbl, RegKind, g) =>
        WRef(next_ident(name), tpe, lbl, RegKind, g)
      case ex => ex
    }

  // This function is called on expressions *not* inside of labels.
  // It should replace female sequential expressions with nextified versions
  def swap_with_next_e(e: Expression) : Expression =
    e map swap_with_next_e match {
      case WRef(name, tpe, lbl, RegKind, FEMALE) =>
        val next_l = swap_with_next_l(lbl)
        WRef(next_ident(name), tpe, next_l, WireKind, FEMALE)
      case ex => ex
    }

  def swap_with_next_s(s: Statement) : Statement =
    s map swap_with_next_s map swap_with_next_e

  def swap_with_next(m: DefModule) : DefModule =
    m map swap_with_next_s

  // TODO For sequential ports connect next-cycle outputs to next-cycle value

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
