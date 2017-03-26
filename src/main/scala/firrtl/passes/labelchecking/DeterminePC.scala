package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import collection.mutable.Set

object DeterminePC extends Pass with PassDebug {
  def name    = "DeterminePC"
  override def debugThisPass = false
  
  def bot = ProdLabel(PolicyHolder.bottom, PolicyHolder.top)

  class PCEnv extends collection.mutable.HashMap[String,Label] {
    override def default(key:String) = bot
  }

  def determine_pc_s(pc: Label)(pcEnv: PCEnv)(s: Statement): Statement = s match {
    case sx: Block =>
      val sxx = sx copy (stmts = sx.stmts.reverse map determine_pc_s(pc)(pcEnv))
      sxx copy (stmts = sxx.stmts.reverse)
    case Conditionally(info, pred, conseq, alt) =>
      val pc_ = pred.lbl join pc
      ConditionallyPC(info, pred, conseq, alt, pc) map determine_pc_s(pc_)(pcEnv)
    case DefNode(info, name, value, lbl) =>
      pcEnv(name) = pcEnv(name) join pc
      DefNodePC(info, name, value, lbl, pcEnv(name))
    case Connect(info, loc, expr) =>
      pcEnv(loc.serialize) = pcEnv(loc.serialize) join pc
      ConnectPC(info, loc, expr, pcEnv(loc.serialize))
    case PartialConnect(info, loc, expr) =>
      pcEnv(loc.serialize) = pcEnv(loc.serialize) join pc
      PartialConnectPC(info, loc, expr, pcEnv(loc.serialize))
    case sx => 
      // can't declare regs under a when
      sx map determine_pc_s(pc)(pcEnv)
  }

  def determine_pc(m: DefModule): DefModule = 
    m map determine_pc_s(bot)(new PCEnv)

  def run(c: Circuit) = {
    bannerprintb(name)
    dprint(c.serialize)
    
    val cprime = c copy (modules = c.modules map determine_pc)

    bannerprintb(s"after $name")
    dprint(cprime.serialize)

    cprime
  }

}
