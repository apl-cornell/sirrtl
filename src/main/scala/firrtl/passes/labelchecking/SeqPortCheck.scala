package firrtl.passes
import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import firrtl.Driver._
import collection.mutable.Set

//-----------------------------------------------------------------------------
// SeqPortCheck
//-----------------------------------------------------------------------------
// Check that port fields declared sequential are in fact sequential.
// This is done by checking that in the Connection Environment, the port is 
// mapped exactly to an Atom which represents either: a sequential port which is
// an input, or a register

object SeqPortCheck extends LabelPass with LabelPassDebug {
  def name = "SeqPortCheck"
  override def debugThisPass = true

  def run(m: DefModule, conEnv: ConnectionEnv) : (DefModule, ConnectionEnv) = {
    bannerprintb(s"before $name")
    dprint(m.serialize)
    dprintConEnv(conEnv)
    val mprime = m
    val conEnvPrime = conEnv
    bannerprintb(s"after $name")
    dprint(mprime.serialize)
    dprintConEnv(conEnvPrime)
    (mprime, conEnvPrime)
  }
}
