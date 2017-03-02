package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import collection.mutable.Set

object RipPCLabels extends Pass with PassDebug {
  def name = "RipPCLabels"
  override def debugThisPass = false

  def ripPC(m: DefModule): DefModule =
    m map ripPCS

  def ripPCS(s: Statement): Statement =
    s map ripPCS match {
      case DefNodePC(info, name, value, _) =>
        DefNode(info, name, value)
      case ConnectPC(info, loc, expr, _) =>
        Connect(info, loc, expr)
      case PartialConnectPC(info, loc, expr, _) =>
        PartialConnect(info, loc, expr)
      case ConditionallyPC(info, pred, conseq, alt, _) =>
        Conditionally(info, pred, conseq, alt)
      case sx => sx
    }

  def run(c: Circuit) = {
    bannerprintb(name)
    dprint(c.serialize)
    
    val cprime = c copy (modules = c.modules map ripPC)

    bannerprintb(s"after $name")
    dprint(cprime.serialize)

    cprime
  }

}
