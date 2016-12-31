package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._

object ImplicitFlowElevation extends Pass {
  def name    = "ImplicitFlowElevation"
  type PredEnv = collection.mutable.Stack[Seq[Expression]]
  type AsnEnv = collection.mutable.Set[String]

  def bot = PolicyHolder.policy.bottom
  
  val debugImplicitFlow = true
  def dprint(s:String) = if(debugImplicitFlow) println(s)
  def dprintb(s:String) = dprint(Console.BLUE+ s + Console.RESET)
  def bannerprintb(s:String) = {
    val ndash = (78 - 2 - s.length) / 2
    dprintb("-" * ndash + ' ' + s + ' ' + "-" * ndash)
  }

  def pcLabel(predEnv: PredEnv) = {
    val exprs :Seq[Expression] = predEnv.toSeq.flatten
    JoinLabel( Seq(bot,bot) ++ (exprs map { _.lbl }) :_* )
  }

  def topBlock(predEnv: PredEnv) = predEnv.toSeq.size == 1

  def elevate_e(predEnv: PredEnv)(e: Expression): Expression = 
    e mapLabel { _ join pcLabel(predEnv) }

  def elevate_s(predEnv: PredEnv, asnEnv:AsnEnv)(s: Statement): Statement = {

    def weaklyElevate(n: String, weak: Statement, strong: Statement) = 
      if(topBlock(predEnv) && !asnEnv.contains(n)){
        weak
      } else {
        asnEnv +=  n
        strong
      }

    s match {
      case sx: Block =>
        predEnv.push(Seq[Expression]())
        val sxx = sx copy (stmts = sx.stmts.reverse map elevate_s(predEnv,asnEnv))
        predEnv.pop
        sxx copy (stmts = sxx.stmts.reverse)
      case sx: Conditionally =>
        predEnv.push(predEnv.pop ++ Seq(sx.pred))
        sx map elevate_s(predEnv,asnEnv)
      case sx: DefNode =>
        weaklyElevate(sx.name, sx, sx map elevate_e(predEnv))
      case sx: Connect =>
        weaklyElevate(sx.loc.serialize, sx, sx copy( expr = elevate_e(predEnv)(sx.expr) ))
      case sx: PartialConnect =>
        weaklyElevate(sx.loc.serialize, sx, sx copy( expr = elevate_e(predEnv)(sx.expr) ))
      case sx => 
        sx map elevate_s(predEnv,asnEnv)
    }
  }

  def elevate(m: DefModule): DefModule = {
    val predEnv = new PredEnv
    val asnEnv = collection.mutable.Set[String]()
    m map elevate_s(predEnv,asnEnv)
  }

  def run(c: Circuit) = {
    bannerprintb(name)
    dprint(c.serialize)
    
    val cprime = c copy (modules = c.modules map elevate)

    bannerprintb(s"after $name")
    dprint(cprime.serialize)

    cprime
  }

}
