package firrtl
import firrtl.ir._

object PolicyHolder {
  var policy: Policy = null
  def setPolicy(p:Policy): Unit = { policy = p }
  def top = policy.top
  def bottom = policy.bottom
  def preamble: String = policy.preamble
  // TODO set this based on a driver option.
  setPolicy(new HypercubePolicy)
}

trait Policy {
  def top : LabelComp
  def bottom : LabelComp
  def preamble: String
}
