package firrtl
package ir

object PolicyHolder {
  var policy: Policy = null
  def setPolicy(p:Policy): Unit = { policy = p }
  def top = policy.top
  def bottom = policy.bottom
  def preamble: String = policy.preamble
}

trait Policy {
  def top : Label
  def bottom : Label
  def preamble: String
}
