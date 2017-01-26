package firrtl.passes
import firrtl._
import firrtl.ir._
import firrtl.Mappers._

//-----------------------------------------------------------------------------
// DeLabel
//-----------------------------------------------------------------------------
// This pass recursively replaces all labels with the UnknownLabel. This pass 
// is performed after labelchecking and labels are therefore no longer useful.
// Labels are removed to reduce the chance of breaking compatibility with later 
// passes.

object DeLabel extends Pass {
  def name = "DeLabel"

  def deLabelL(l: Label) : Label = UnknownLabel

  def deLabelE(e: Expression) : Expression =
    e map deLabelE map deLabelL

  def deLabelS(s: Statement) : Statement =
    s map deLabelS map deLabelE map deLabelL

  def deLabelP(p: Port) =
    p copy (lbl = UnknownLabel)

  def deLabel(m: DefModule) : DefModule =
    m map deLabelP map deLabelS

  def run(c: Circuit) = c copy( modules = c.modules map deLabel)
}
