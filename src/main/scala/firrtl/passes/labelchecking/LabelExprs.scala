package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._

// This pass propagates labels from declarations to expressions (e.g. nodes).
object LabelExprs extends Pass with PassDebug {
  def name = "Label Expressions"
  override def debugThisPass = false
  type LabelMap = collection.mutable.LinkedHashMap[String, Label]

  val bot = ProdLabel(PolicyHolder.bottom, PolicyHolder.top)
  val top = ProdLabel(PolicyHolder.top, PolicyHolder.bottom)

  class UndeclaredException(info: Info, name: String) extends PassException(
    s"$info: [declaration $name] does not have a declared label")
  class UnknownLabelException(info: Info, name: String) extends PassException(
    s"$info: a label could not be inferred for [$name]")
  val errors = new Errors()

  def throwErrors = true

  // Assume that if the label was omitted, that the least-restrictive label was 
  // the desired one. This function should only be used for things like 
  // constants and clocks. This is mostly used to make the places where \bot is
  // assumed very obvious
  def assumeL(l:Label) = if(label_is_known(l)) l else bot

  def labelOrVar(l: Label, id: String) = if(label_is_known(l)) l else VarLabel(id)

  def label_is_known(l: Label): Boolean = {
    var b = true
    def label_is_known_(l: Label): Label =
      l map label_is_known_ map label_comp_is_known

    def label_comp_is_known(lc: LabelComp): LabelComp =
      lc map label_comp_is_known match {
        case UnknownLabelComp => b = false; UnknownLabelComp
        case lx => lx
      }
    label_is_known_(l); b
  }

  def checkDeclared(l: Label, i: Info, n: String) = {
    var b = true
    var scope = collection.immutable.List[Label](UnknownLabel)
    var badParent: Label = UnknownLabel

    def checkDeclared_(l: Label): Label = l match {
      case lx: BundleLabel => 
        scope = lx :: scope
        val ret = lx map checkDeclared_ map checkDeclaredComp
        scope = scope.tail
        ret
      case lx => lx map checkDeclared_ map checkDeclaredComp
    }
    
    def checkDeclaredComp(lc: LabelComp): LabelComp =
      lc map checkDeclaredComp match {
        case UnknownLabelComp => b = false; badParent = scope.head; UnknownLabelComp
        case lx => lx
      }
    checkDeclared_(l);
    
    val parentString = badParent match {
      case UnknownLabel => ""
      case _ => s", with bad internal record ${badParent.serialize}"
    }

    if(!b && throwErrors)
      errors.append(new UndeclaredException(i, n + parentString))

    // if(!label_is_known(l) && throwErrors)
    //   errors.append(new UndeclaredException(i, n))
  }
    
  def checkKnown(l: Label, i: Info, n: String) = 
    if(!label_is_known(l) && throwErrors)
      errors.append(new UnknownLabelException(i, n))
    
  // This function is used for declarations with BundleTypes to convert their 
  // labels into BundleLabels. This also supports type constructions in which a 
  // BundleType may be nested arbitrarily deep within VectorTypes.
  def to_bundle(t: Type, l: Label) : Label = {
    def to_bundle__(t: Type, l: Label) = t match {
      case tx if label_is_known(l) => l
      case BundleType(fields) => BundleLabel(fields)
      case _ => l
    }
    // Recursively convert BundleTypes within a BundleType to BundleLabels
    def to_bundle_(t: Type) : Type = t map to_bundle_ match {
      case tx : BundleType => tx copy (fields = tx.fields map { f =>
        f copy (lbl = to_bundle__(f.tpe, f.lbl))
      })
      case VectorType(tpe, _) => to_bundle_(tpe)
      case tx => tx
    }
    if(label_is_known(l)) l else to_bundle__(to_bundle_(t), l)
  }

  def label_exprs_e(labels: LabelMap)(e: Expression) : Expression =
    if(label_is_known(e.lbl)) e match {
      case ex: Declassify => ex map label_exprs_e(labels)
      case ex: Endorse => ex map label_exprs_e(labels)
      case ex => ex
    }
    else e map label_exprs_e(labels) match {
      case ex: WRef => ex copy (lbl = labels(ex.name))
      case ex: Next => ex copy (lbl = ex.exp.lbl)
      case ex: WSubField =>
        ex copy (lbl = field_label(ex.exp.lbl, ex.name))
      case ex: WSubIndex => ex copy (lbl = ex.exp.lbl)
      case ex: WSubAccess => ex copy (lbl = JoinLabel(ex.exp.lbl, ex.index.lbl))
      case ex: DoPrim => ex copy (lbl = JoinLabel((ex.args map{ _.lbl }):_* ))
      case ex: Mux => ex copy (lbl = JoinLabel(ex.cond.lbl,
        ex.tval.lbl, ex.fval.lbl))
      case ex: ValidIf => ex copy (lbl = JoinLabel(ex.cond.lbl, ex.value.lbl))
      case ex: UIntLiteral => ex copy (lbl = assumeL(ex.lbl))
      case ex: SIntLiteral => ex copy (lbl = assumeL(ex.lbl))
      case ex: Declassify => ex
      case ex: Endorse => ex
    }

  def label_exprs_s(labels: LabelMap)(s: Statement): Statement = 
    s map label_exprs_s(labels) match {
      case sx: WDefInstance =>
        // This relies on the fact that a bundle type has been created for sx 
        // in InferTypes and that both type and label propagation have already 
        // been performed for definition of the instantiated module since 
        // forward instantiation is not permitted. 
        val lb = to_bundle(sx.tpe, UnknownLabel)
        checkDeclared(lb, sx.info, sx.name)
        labels(sx.name) = lb
        (sx copy (lbl = lb)) map label_exprs_e(labels)
      case sx: DefWire =>
        var lb = labelOrVar(to_bundle(sx.tpe, sx.lbl), sx.name)
        labels(sx.name) = lb
        (sx copy (lbl = lb)) map label_exprs_e(labels)
      case sx: DefRegister =>
        val lb = labelOrVar(to_bundle(sx.tpe, sx.lbl), sx.name)
        labels(sx.name) = lb
        (sx copy (lbl = lb)) map label_exprs_e(labels)
      case sx: DefNode =>
        // Node definitions are not inferred. They are essentially
        // "immutable wires" so there is no reason to use a label other than
        // the label of the expression in its only assignment. So node
        // definition labels are not inferred, but forward-propagated.a
        // When compiling from chisel, nodes also don't correspond to 
        // something directly written by the programmer. Using the
        // forward-propaged label means node declarations will never
        // fail to type-check, so the errors will be moved to places
        // like wire and register declarations which correspond
        // directly to things written by the programmer.
        val sxx = (sx map label_exprs_e(labels)).asInstanceOf[DefNode]
        labels(sx.name) = sxx.value.lbl
        sxx.copy(lbl = sxx.value.lbl)
        // var lb = labelOrVar(sx.lbl, sx.name)
        // val sxx = ((sx map label_exprs_e(labels)).asInstanceOf[DefNode]).copy(
        //   lbl = lb)
        // labels(sxx.name) = lb
        // sxx
      case sx: DefMemory =>
        // Don't do inference for memories for now.
        checkDeclared(sx.lbl, sx.info, sx.name)
        labels(sx.name) = sx.lbl
        sx
      case sx => sx map label_exprs_e(labels)
  }

  // Add each port declaration to the label context
  def label_exprs_p(labels: LabelMap)(p: Port) : Port = {
    val lb = to_bundle(p.tpe, p.lbl)
    checkDeclared(lb, p.info, p.name)
    labels(p.name) = lb
    p copy (lbl = lb)
  }

  def label_exprs(m: DefModule) : DefModule = {
    val labels = new LabelMap
    m map label_exprs_p(labels) map label_exprs_s(labels)
  }

  def run(c: Circuit) = {
    bannerprintb(name)
    dprint(c.serialize)

    val cprime = c copy (modules = c.modules map label_exprs)

    bannerprintb(s"after $name")
    dprint(cprime.serialize)
 
    errors.trigger()
    cprime
  }
}
