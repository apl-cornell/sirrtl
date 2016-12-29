package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._

object LabelCheck extends Pass {
  def name = "Label Check"
  def run(c:Circuit) = {
    LabelDebug.p(name)
    c
  }
}
