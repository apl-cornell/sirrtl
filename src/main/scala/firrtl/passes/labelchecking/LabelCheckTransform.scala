package firrtl.passes
package labelchecking

import java.io.PrintWriter
import java.io.Writer

import firrtl.Utils.error
import firrtl._
import firrtl.annotations.{Annotation, CircuitName}
import firrtl.SimpleRun

object LabelCheckAnnotation {

  def apply(target: CircuitName, configString: String): Annotation =
    Annotation(target, classOf[LabelCheckTransform], configString)

  def unapply(a: Annotation): Option[(CircuitName, String)] = a match {
    case Annotation(CircuitName(c), t, outputConfig) if t == classOf[LabelCheckTransform] =>
      Some((CircuitName(c), outputConfig))
    case _ => None
  }
}

class LabelCheckTransform extends Transform with SimpleRun {
  /** The [[CircuitForm]] that this transform requires to operate on */
  override def inputForm: CircuitForm = LabeledForm

  /** The [[CircuitForm]] that this transform outputs */
  override def outputForm: CircuitForm = LabeledForm

  def passSeq(constraintWriter: Writer) =  Seq(
    passes.PropNodes,
    // passes.LabelMPorts,
    passes.LabelExprs,
    passes.DepsToWorkingIR,
    passes.DepsResolveKinds,
    passes.DepsInferTypes,
    passes.DeterminePC,
    passes.NextCycleTransform,
   // passes.SimplifyLabels,
    passes.ForwardProp,
   // passes.SimplifyLabels,
    passes.InferLabels,
    passes.ApplyVecLabels,
    new LabelCheck(constraintWriter))

  /** Perform the transform
    *
    * @param state Input Firrtl AST
    * @return A transformed Firrtl AST
    */
  override def execute(state: CircuitState): CircuitState = getMyAnnotations(state) match {
    case Seq(LabelCheckAnnotation(_, out)) =>
      val outputFile = new PrintWriter(out)
      val passes = passSeq(outputFile)
      val newC = runPasses(state.circuit, passes)
      outputFile.close()
      CircuitState(newC, state.form)
    case Nil =>
      val passes = passSeq(null)
      val newC = runPasses(state.circuit, passes)
      CircuitState(newC, state.form)
    case seq => error(s"Found illegal label check annotation(s): $seq")
  }

}
