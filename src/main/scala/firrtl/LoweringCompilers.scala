// See LICENSE for license details.

package firrtl

object deLabel {
  def apply(): Seq[passes.Pass] = Seq(passes.DeLabel, passes.RipNexts, passes.RipDowngrades, passes.RipNexts, passes.RipPCLabels)
}

object highToLblPasses {
  def apply(): Seq[passes.Pass] = Seq(
    passes.PullMuxes,
    passes.ReplaceAccesses,
    passes.ExpandConnects,
    passes.RemoveAccesses,
    passes.ExpandWhens,
    passes.CheckInitialization,
    passes.ResolveKinds,
    passes.InferTypes,
    passes.CheckTypes,
    passes.ResolveGenders,
    passes.InferWidths,
    passes.CheckWidths)
}
sealed abstract class CoreTransform extends PassBasedTransform

/** This transforms "CHIRRTL", the chisel3 IR, to "Firrtl". Note the resulting
  * circuit has only IR nodes, not WIR.
  * TODO(izraelevitz): Create RenameMap from RemoveCHIRRTL
  */

class ChirrtlToAlmostHigh extends CoreTransform {
  def inputForm = ChirrtlForm
  def outputForm = HighForm
  def passSeq = Seq(
    passes.CheckChirrtl,
    passes.CInferTypes,
    passes.CInferMDir)
}

class Resolve extends CoreTransform {
  def inputForm = HighForm
  def outputForm = HighForm
  def passSeq = Seq(
    passes.ResolveKinds,
    passes.InferTypes,
    passes.ResolveGenders,
    passes.InferWidths,
    passes.CheckWidths)
}


class RemoveResolveAndCheck extends CoreTransform {
  def inputForm = HighForm
  def outputForm = HighForm
  def passSeq = Seq(
    passes.RemoveCHIRRTL,
    passes.CheckHighForm,
    passes.ResolveKinds,
    passes.InferTypes,
    passes.CheckTypes,
    passes.Uniquify,
    passes.ResolveKinds,
    passes.InferTypes,
    passes.ResolveGenders,
    passes.CheckGenders,
    passes.InferWidths,
    passes.CheckWidths)
}
 
class ChirrtlToHighFirrtl extends CoreTransform {
  def inputForm = ChirrtlForm
  def outputForm = HighForm
  def passSeq = Seq(
    passes.CheckChirrtl,
    passes.CInferTypes,
    passes.CInferMDir,
    passes.RemoveCHIRRTL)
}

/** Converts from the bare intermediate representation (ir.scala)
  * to a working representation (WIR.scala)
  */
class IRToWorkingIR extends CoreTransform {
  def inputForm = HighForm
  def outputForm = HighForm
  def passSeq = Seq(passes.ToWorkingIR)
}

/** Resolves types, kinds, and genders, and checks the circuit legality.
  * Operates on working IR nodes and high Firrtl.
  */
class ResolveAndCheck extends CoreTransform {
  def inputForm = HighForm
  def outputForm = HighForm
  def passSeq = Seq(
    passes.CheckHighForm,
    passes.ResolveKinds,
    passes.InferTypes,
    passes.CheckTypes,
    passes.Uniquify,
    passes.ResolveKinds,
    passes.InferTypes,
    passes.ResolveGenders,
    passes.CheckGenders,
    passes.InferWidths,
    passes.CheckWidths)
}

// For defaulting to doing nothing when label checking is not desired in the 
// call to getLoweringTransforms. This can't be an anonymous class in that 
// file because CoreTransform is sealed.

class EmptyTransform extends CoreTransform{
  def inputForm = HighForm
  def outputForm = HighForm
  def passSeq = Seq()
}

class LabelChecking extends CoreTransform {
  def inputForm = LabeledForm
  def outputForm = LabeledForm
  def passSeq =  Seq(
    passes.PropNodes,
    // passes.LabelMPorts,
    passes.LabelExprs,
    passes.DepsToWorkingIR, 
    passes.DepsResolveKinds,
    passes.DepsInferTypes,
    passes.DeterminePC,
    passes.InferSeqPorts,
    passes.InferTypes,
    passes.DeterminePC,
    passes.NextCycleTransform,
    passes.SimplifyLabels,
    passes.ForwardProp,
    passes.SimplifyLabels,
    passes.InferLabels,
    passes.ApplyVecLabels,
    passes.LabelCheck)
}

class LabelTeardown extends CoreTransform {
  def inputForm = LabeledForm
  def outputForm = MidForm
  def passSeq = deLabel()
}

class HighFirrtlToLabeledFirrtl extends CoreTransform {
  def inputForm = HighForm
  def outputForm = LabeledForm
  def passSeq = highToLblPasses()
}

/** Expands aggregate connects, removes dynamic accesses, and when
  * statements. Checks for uninitialized values. Must accept a
  * well-formed graph.
  * Operates on working IR nodes.
  */
class HighFirrtlToMiddleFirrtl extends CoreTransform {
  def inputForm = HighForm
  def outputForm = MidForm
  def passSeq = highToLblPasses() ++ deLabel()
}


/** Expands all aggregate types into many ground-typed components. Must
  * accept a well-formed graph of only middle Firrtl features.
  * Operates on working IR nodes.
  * TODO(izraelevitz): Create RenameMap from RemoveCHIRRTL
  */
class MiddleFirrtlToLowFirrtl extends CoreTransform {
  def inputForm = MidForm
  def outputForm = LowForm
  def passSeq = Seq(
    passes.LowerTypes,
    passes.ResolveKinds,
    passes.InferTypes,
    passes.ResolveGenders,
    passes.InferWidths,
    passes.ConvertFixedToSInt,
    passes.Legalize)
}

/** Runs a series of optimization passes on LowFirrtl
  * @note This is currently required for correct Verilog emission
  * TODO Fix the above note
  */
class LowFirrtlOptimization extends CoreTransform {
  def inputForm = LowForm
  def outputForm = LowForm
  def passSeq = Seq(
    passes.RemoveValidIf,
    passes.ConstProp,
    passes.PadWidths,
    passes.ConstProp,
    passes.Legalize,
    passes.memlib.VerilogMemDelays, // TODO move to Verilog emitter
    passes.ConstProp,
    passes.SplitExpressions,
    passes.CommonSubexpressionElimination,
    passes.DeadCodeElimination)
}


import CompilerUtils.getLoweringTransforms
import firrtl.transforms.BlackBoxSourceHelper

/** Emits input circuit
  * Will replace Chirrtl constructs with Firrtl
  */
class HighFirrtlCompiler extends Compiler {
  def emitter = new FirrtlEmitter
  def transforms: Seq[Transform] = getLoweringTransforms(ChirrtlForm, HighForm)
}

/** Emits labeled MidFirrtl after label inference, label related
 *  transformations, and determining the PC value.
 */
class LabeledFirrtlCompiler extends Compiler {
  def emitter = new FirrtlEmitter
  def transforms: Seq[Transform] =
    getLoweringTransforms(ChirrtlForm, LabeledForm)
}

/** Emits middle Firrtl input circuit */
class MiddleFirrtlCompiler extends Compiler {
  def emitter = new FirrtlEmitter
  def transforms: Seq[Transform] = getLoweringTransforms(ChirrtlForm, MidForm)
}

/** Emits lowered input circuit */
class LowFirrtlCompiler extends Compiler {
  def emitter = new FirrtlEmitter
  def transforms: Seq[Transform] = getLoweringTransforms(ChirrtlForm, LowForm)
}

/** Emits Verilog */
class VerilogCompiler extends Compiler {
  def emitter = new VerilogEmitter
  def transforms: Seq[Transform] =
    getLoweringTransforms(ChirrtlForm, LowForm) ++
    Seq(new LowFirrtlOptimization, new BlackBoxSourceHelper)

}
