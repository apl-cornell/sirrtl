package firrtl
package ir

object PolicyHolder {
  var policy: Policy = null
  def setPolicy(p:Policy): Unit = { policy = p }
  def top = policy.top
  def bottom = policy.bottom
  def join(l: Label, r: Label): Label =
    policy.join(l, r)
  def meet(l: Label, r: Label): Label =
    policy.meet(l, r)
}

trait Policy {
  def top : Label
  def bottom : Label
  def join(l: Label, r: Label): Label
  def meet(l: Label, r: Label): Label
}
