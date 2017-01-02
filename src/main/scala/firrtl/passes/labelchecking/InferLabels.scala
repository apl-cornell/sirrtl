package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._

// This pass infers the labels of all expresssions in the circuit. It does so 
// by mutating the circuit rather than maintaining a global mapping of labels.
object InferLabels extends Pass with PassDebug {
  def name = "Infer Labels"
  override def debugThisPass = false
  type LabelMap = collection.mutable.LinkedHashMap[String, Label]

  val bot = PolicyHolder.policy.bottom
  val top = PolicyHolder.policy.top
    
  val errors = new Errors()

  class UndeclaredException(info: Info, name: String) extends PassException(
    s"$info: [declaration $name] does not have a declared label")

  class UnknownLabelException(info: Info, name: String) extends PassException(
    s"$info: a label could not be inferred for [$name]")

  // Assume that if the label was omitted, that the least-restrictive label was 
  // the desired one.
  def assumeL(l:Label) = l match {
    case UnknownLabel => bot
    case _ => l
  }

  def checkDeclared(l: Label, i: Info, n: String) = l match {
    case UnknownLabel => errors.append(new UndeclaredException(i, n))
    case _ => 
  }

  def checkKnown(l: Label, i: Info, n: String) = l match {
    case UnknownLabel => errors.append(new UnknownLabelException(i, n))
    case _ => 
  }

  // This function is used for register and wire declarations to convert
  // their labels to BundleLabel declarations
  def to_bundle(t: Type, l: Label) : Label = t match {
    case BundleType(fields) =>
      val labelSet = fields.map(_.lbl)
      if(labelSet.contains(UnknownLabel)) l else BundleLabel(fields)
    case _ => l
  }

  def infer_labels_e(labels: LabelMap)(e: Expression) : Expression =
    e map infer_labels_e(labels) match {
      case e: WRef => e copy (lbl = labels(e.name))
      case e: WSubField =>
        e copy (lbl = field_label(e.exp.lbl, e.name))
      case e: WSubIndex => e copy (lbl = e.exp.lbl)
      case e: WSubAccess => e copy (lbl = JoinLabel(e.exp.lbl, e.index.lbl))
      case e: DoPrim => e copy(lbl = JoinLabel((e.args map{ _.lbl }):_* ))
      case e: Mux => e copy (lbl = JoinLabel(e.cond.lbl,
        e.tval.lbl,e.fval.lbl))
      case e: ValidIf => e copy (lbl = JoinLabel(e.cond.lbl, e.value.lbl))
      case e: UIntLiteral => e.copy(lbl = assumeL(e.lbl))
      case e: SIntLiteral => e.copy(lbl = assumeL(e.lbl))
  }

  def infer_labels_s(labels: LabelMap)(s: Statement): Statement = s match {
      case sx: DefWire =>
        val lb = to_bundle(sx.tpe, sx.lbl)
        checkDeclared(lb, sx.info, sx.name)
        labels(sx.name) = lb
        sx copy (lbl = lb)
      case sx: DefRegister =>
        val lb = to_bundle(sx.tpe, sx.lbl)
        checkDeclared(lb, sx.info, sx.name)
        labels(sx.name) = lb
        val sxx = ((sx copy (lbl = lb)) map infer_labels_e(labels)
          ).asInstanceOf[DefRegister]
        val lbx = JoinLabel(sxx.lbl, assumeL(sxx.clock.lbl),
          assumeL(sxx.reset.lbl), sxx.init.lbl)
        labels(sx.name) = lbx
        sxx copy (lbl = lbx)
      case sx: DefNode =>
        val sxx = (sx map infer_labels_e(labels)).asInstanceOf[DefNode]
        labels(sxx.name) = sxx.value.lbl
        checkKnown(sxx.value.lbl, sxx.info, sxx.name)
        sxx
      case sx: Connect =>
        val sxx = (sx map infer_labels_s(labels) map infer_labels_e(labels)
          ).asInstanceOf[Connect]
        checkKnown(sxx.loc.lbl,  sxx.info, "")
        checkKnown(sxx.expr.lbl, sxx.info, "")
        sxx
      // Not sure what should be done for:
      // WDefInstance 
      // DefMemory
      case sx => 
        sx map infer_labels_s(labels) map infer_labels_e(labels)
  }

  // Add each port declaration to the label context
  def infer_labels_p(labels: LabelMap)(p: Port) : Port = {
    val lb = to_bundle(p.tpe, p.lbl)
    checkDeclared(lb, p.info, p.name)
    labels(p.name) = lb
    p copy (lbl = lb)
  }

  def infer_labels(m: DefModule) : DefModule = {
    val labels = new LabelMap
    // dprint(s"infer_labels ${m.serialize} ")
    m map infer_labels_p(labels) map infer_labels_s(labels)
  }

  def run(c: Circuit) = {
    bannerprintb(name)
    dprint(c.serialize)

    val cprime = c copy (modules = c.modules map infer_labels)

    bannerprintb("after label inference")
    dprint(cprime.serialize)
 
    errors.trigger()
    cprime
  }
}
