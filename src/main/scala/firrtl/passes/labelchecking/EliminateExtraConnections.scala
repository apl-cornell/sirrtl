package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import firrtl.Driver._
import collection.mutable.Set

// If a location is assigned multiple times under the same scope, 
// this pass will eliminate all but the last assignment. Prior assignments
// under the same scope will not be used during code generation and make
// information flow tracking imprecise. This pass is particularly important for
// the connections of the form $r <= r generated for registers r during the
// next cycle transformation pass. Often, correct designs will set registers
// to a safe default value in the top-level context (i.e., not under a "when").

object EliminateUnusedConnections extends Pass with PassDebug {
  def name = "Eliminate Unused Connections"
  override def debugThisPass = true

  //--------------------------------------------------------------------------
  // Flatten blocks
  //--------------------------------------------------------------------------
  def flatten_s(s: Statement) : Statement = s map flatten_s match {
    case sx : Block => sx copy (stmts = 
      (sx.stmts map { (sxx: Statement) => sxx match {
        case Block(stmts) => stmts
        case _ => Seq(sxx)
      }}).flatten)
    case _ => s
  }

  //--------------------------------------------------------------------------
  // Eliminate unused connections
  //--------------------------------------------------------------------------
  type AsgnEnv = collection.mutable.Stack[Set[String]]
  def elim_loc(asgnEnv: AsgnEnv, loc: String, s: Statement) : Statement = 
    if(asgnEnv.top.contains(loc)) EmptyStmt
    else { asgnEnv.top += loc; s }

  def elim_s(asgnEnv: AsgnEnv)(s: Statement) : Statement = s match {
    case sx : Connect=> elim_loc(asgnEnv, sx.loc.serialize, sx)
    case sx : PartialConnect=> elim_loc(asgnEnv, sx.loc.serialize, sx)
    case sx : DefNode => elim_loc(asgnEnv, sx.name, sx)
    case sx : Block =>
      asgnEnv.push(Set[String]())
      val sxx = sx copy (stmts = sx.stmts.reverse map elim_s(asgnEnv))
      asgnEnv.pop
      sxx copy (stmts = sxx.stmts.reverse)
    case sx => sx map elim_s(asgnEnv)
  }

  def elim(m: DefModule) : DefModule =
    m map flatten_s map elim_s(new AsgnEnv)

  def run(c: Circuit) = {
    bannerprintb(name)
    dprint(c.serialize)
    val cprime = c copy (modules = c.modules map elim)
    bannerprintb(s"after $name")
    dprint(cprime.serialize)
    cprime
  }
}
