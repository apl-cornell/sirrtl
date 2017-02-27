package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Mappers._

// Get rid of all downgrade expressions by replacing them with their inner 
// expression. This is run after labelchecking and 
// makes it easier to maintain passes that happen labelchecking - they can 
// remain oblivious to this syntax change.
object RipDowngrades extends Pass with PassDebug {
  def name = "RipDowngrades"
  override def debugThisPass = false

  def ripDowngrades(m: DefModule): DefModule =
    m map ripDowngradesS

  def ripDowngradesS(s: Statement): Statement =
    s map ripDowngradesS map ripDowngradesE

  def ripDowngradesE(e: Expression): Expression =
    e map ripDowngradesE match {
      case Declassify(ex, _) => ex
      case Endorse(ex, _) => ex
      case ex => ex
    }

  def run(c: Circuit) = {

    bannerprintb(name)
    dprint(c.serialize)
    
    val cprime = c copy (modules = c.modules map ripDowngrades)

    bannerprintb(s"after $name")
    dprint(cprime.serialize)

    cprime
  }
}
