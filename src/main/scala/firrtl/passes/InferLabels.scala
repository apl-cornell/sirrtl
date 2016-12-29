package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._

// This pass infers the labels of all expresssions in the circuit. It does so 
// by mutating the circuit rather than maintaining a global mapping of labels.
object InferLabels extends Pass {
  def name = "Infer Labels"
  type LabelMap = collection.mutable.LinkedHashMap[String, Label]

  val debugInferLabels = true
  def dprint(s:String) = if(debugInferLabels) println(s)

  val bot = PolicyHolder.policy.bottom
  val top = PolicyHolder.policy.top

  // Assume that if the label was omitted, that the least-restrictive label was 
  // the desired one.
  def assumeL(l:Label) = l match {
    case UnknownLabel => bot
    case _ => l
  }

  // This function is used for register and wire declarations to convert
  // their labels to BundleLabel declarations
  def to_bundle(t: Type, l: Label) : Label = t match {
    case BundleType(fields) =>
      val labelSet = fields.map(_.lbl)
      if(labelSet.contains(UnknownLabel)) l else BundleLabel(fields)
    case _ => l
  }

  def infer_labels_e(labels: LabelMap)(e: Expression) : Expression =  {
    dprint(s"infer_labels_e ${e.serialize}")
    val ret = e map infer_labels_e(labels) match {
      case e: WRef => e copy (lbl = labels(e.name))
      case e: WSubField =>
        e copy (lbl = field_label(e.exp.lbl, e.name))
      case e: WSubIndex => e copy (lbl = e.exp.lbl)
      case e: WSubAccess => e copy (lbl = JoinLabel(e.exp.lbl, e.index.lbl))
      case e: DoPrim => e copy (lbl = JoinLabel((e.args map{ _.lbl }):_* ))
      // TODO relax this when there are deptypes
      case e: Mux => e copy (lbl = JoinLabel(e.cond.lbl,
        e.tval.lbl,e.fval.lbl))
      case e: ValidIf => e copy (lbl = JoinLabel(e.cond.lbl, e.value.lbl))
      case e @ (_: UIntLiteral | _: SIntLiteral) => e
    }
    dprint(s"${ret.serialize} : ${ret.lbl.serialize}")
    ret
  }

  def infer_labels_s(labels: LabelMap)(s: Statement): Statement = {
    dprint(s"infer_labels_s ${s.serialize}")
    val ret = s match {
      case sx: DefWire =>
        val lb = to_bundle(sx.tpe, assumeL(sx.lbl))
        labels(sx.name) = lb
        sx copy (lbl = lb)
      case sx: DefRegister =>
        val lb = to_bundle(sx.tpe, assumeL(sx.lbl))
        labels(sx.name) = lb
        val sxx = ((sx copy (lbl = lb)) map infer_labels_e(labels)
          ).asInstanceOf[DefRegister]
        val lbx = JoinLabel(sxx.lbl, assumeL(sxx.clock.lbl),
          assumeL(sxx.reset.lbl), assumeL(sxx.init.lbl))
        labels(sx.name) = lbx
        sxx copy (lbl = lbx)
      case sx: DefNode =>
        val sxx = (sx map infer_labels_e(labels)).asInstanceOf[DefNode]
        labels(sxx.name) = sxx.value.lbl
        sxx
      // Not sure what should be done for:
      // WDefInstance 
      // DefMemory
      case sx => 
        sx map infer_labels_s(labels) map infer_labels_e(labels)
    }
    dprint(s"${ret.serialize}")
    dprint(s"labels : $labels")
    ret
  }

  // Add each port declaration to the label context
  def infer_labels_p(labels: LabelMap)(p: Port) : Port = {
    dprint(s"infer_labels_p ${p.serialize} ")
    val lb = to_bundle(p.tpe, assumeL(p.lbl))
    labels(p.name) = lb
    val ret = p copy (lbl = lb)
    dprint(s"${ret.serialize} : ${ret.lbl.serialize}")
    dprint(s"labels : $labels")
    ret
  }

  def infer_labels(m: DefModule) : DefModule = {
    val labels = new LabelMap
    dprint(s"infer_labels ${m.serialize} ")
    m map infer_labels_p(labels) map infer_labels_s(labels)
  }

  def run(c: Circuit) = {
    dprint(name)
    c copy (modules = c.modules map infer_labels)
  }
}
