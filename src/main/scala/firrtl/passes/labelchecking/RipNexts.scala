package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Mappers._

// Convert all Expressions of the form "Next(e)" to "e".
// Useful for when you want to push labeled code through the normal toolflow 
// without first doing label-checking.

object RipNexts extends Pass {
  def name = "RipNexts"
  
  def ripNextsE(e: Expression): Expression =
    e map ripNextsE match {
      case ex: Next => ex.exp
      case ex => ex
    }

  def ripNextsS(s: Statement): Statement =
    s map ripNextsS map ripNextsE

  def ripNexts(m: DefModule): DefModule =
    m map ripNextsS

  def run(c: Circuit) = c copy (modules = c.modules map ripNexts)

}
