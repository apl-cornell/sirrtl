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

  //TODO use annotations to pass this via cmd line options
  def assumeBot = true

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
    var badField: String = ""

    def checkDeclared_(l: Label): Label = l match {
      case lx: BundleLabel => 
        scope = lx :: scope
        lx.fields foreach { f =>
          badField = f.name
          checkDeclared_(f.lbl) map checkDeclared_ map checkDeclaredComp
        }

        // val ret = lx map checkDeclared_ map checkDeclaredComp
        scope = scope.tail
        lx
      case lx => lx map checkDeclared_ map checkDeclaredComp
    }
    
    def checkDeclaredComp(lc: LabelComp): LabelComp =
      lc map checkDeclaredComp match {
        case UnknownLabelComp => b = false; badParent = scope.head; UnknownLabelComp
        case lx => lx
      }
    checkDeclared_(l);
    b
  }

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

  def apply_index_vec(idx: Expression, vec: Expression)(lbl: Label) : Label = {
    def apply_index_vec_lc(idx: Expression, vec: Expression)(lc: LabelComp) : LabelComp =
      lc map apply_index_vec_lc(idx, vec) map apply_index_vec_e(idx, vec)

    // Note that (e: Expression) is an expression appearing in a dependent 
    // type, that these expressions have not yet been converted to WIR, and 
    // that the expressions of interest are SubAccesses indexed by "_".
    // "similar" is a sufficiently weak equivalence relation defined in 
    // Utils.scala
    def apply_index_vec_e(idx: Expression, vec: Expression)(e: Expression) : Expression = 
      e map apply_index_vec_e(idx, vec) match {
        case ex : SubAccess if( similar(ex.expr, vec) ) => ex.index match {
          case FnBinding => ex copy (index= idx )
          case _ => ex
        }
        case ex => ex
      }

    lbl map apply_index_vec(idx, vec) map apply_index_vec_lc(idx, vec)
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
      case ex: WSubIndex => 
        val lbl_ = apply_index_vec(uint(ex.value), ex.exp)(ex.exp.lbl)
        val lbl__  = apply_index_vech(lbl_, UIntLiteral(ex.value, vec_size(ex.exp.tpe), bot))
        ex copy (lbl = lbl__)
      case ex: WSubAccess => 
        val app_ex_lbl = apply_index_vec(ex.index, ex.exp)(ex.exp.lbl)
        val lbl__ = apply_index_vech(app_ex_lbl, ex.index)
        ex copy (lbl = JoinLabel(lbl__, ex.index.lbl))
      case ex: DoPrim => ex copy (lbl = JoinLabel((ex.args map{ _.lbl }):_* ))
      case ex: Mux => ex copy (lbl = IteLabel(ex.cond, ex.cond.lbl,
        ex.tval.lbl, ex.fval.lbl))
      case ex: ValidIf => ex copy (lbl = IteLabel(ex.cond, ex.cond.lbl, ex.value.lbl, bot))
      case ex: UIntLiteral => ex copy (lbl = assumeL(ex.lbl))
      case ex: SIntLiteral => ex copy (lbl = assumeL(ex.lbl))
      case ex: Declassify => ex
      case ex: Endorse => ex
    }

  def instance_io_rename(instName: String)(label: Label): Label = {
    def instance_io_rename_e(instName: String)(e: Expression): Expression =
      e map instance_io_rename_e(instName) match {
        // Note that this assumes that Dep Exprs have not been moved to WIR
        case ex: Reference if ex.name == "io" => 
          val iref = Reference(instName, UnknownType, UnknownLabel)
          SubField(iref, "io", ex.tpe, ex.lbl)
        case ex => ex
      }

    def instance_io_rename_lc(instName: String)(lc: LabelComp): LabelComp =
      lc map instance_io_rename_e(instName) map instance_io_rename_lc(instName)

    label map instance_io_rename_lc(instName) map instance_io_rename(instName)
  }

  // This function applies memory port address wire expression to VecHLevels
  // which are used for describing memories with labels that are other
  // memories indexed by the port's address wire. 
  def apply_index_vech(l: Label, idx: Expression): Label = {
    def apply_index_c(idx: Expression)(lc: LabelComp): LabelComp = 
      lc map apply_index_c(idx) match {
        case lcx: VecHLevel => IndexedVecHLevel(lcx.arr, idx)
        case lcx => lcx
      }
    def apply_index_(idx: Expression)(l: Label): Label = 
      l map apply_index_(idx) map apply_index_c(idx)
    apply_index_(idx)(l)
  }

  def rename_mem_in_lb(mem: String, port: String)(l: Label): Label = {
    def rename_mem_lc(mem: String, port: String)(lc: LabelComp): LabelComp =
      lc map rename_mem_lc(mem, port) map rename_mem_e(mem, port)
    def rename_mem_e(mem: String, port: String)(e: Expression): Expression = {
      val ex = e map rename_mem_in_lb(mem, port) map rename_mem_e(mem, port) match {
        // Note that this assumes that Dep Exprs have not been moved to WIR
        case ex: Reference if(ex.name == mem) => ex copy (name = port)
        case ex => ex
      }
      ex
    }
    l map rename_mem_in_lb(mem, port) map rename_mem_lc(mem, port)
  }

  def label_exprs_s(labels: LabelMap)(s: Statement): Statement = 
    s map label_exprs_s(labels) match {
      case sx: WDefInstance =>
        // This relies on the fact that a bundle type has been created for sx 
        // in InferTypes and that both type and label propagation have already 
        // been performed for definition of the instantiated module since 
        // forward instantiation is not permitted. 
        val lb = instance_io_rename(sx.name)(to_bundle(sx.tpe, UnknownLabel))
        val isDeclared = checkDeclared(lb, sx.info, sx.name)
        val lblx = if(isDeclared) { lb } else { bot }
        labels(sx.name) = lblx
        (sx copy (lbl = lblx)) map label_exprs_e(labels)
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
        val lb = labelOrVar(sx.lbl, sx.name)
        labels(sx.name) = lb
        sx copy (lbl = lb)
      case sx: CDefMPort =>
        val lb = labels(sx.mem)
        val isDeclared = checkDeclared(lb, sx.info, sx.mem)
        val lbxx =
          if (isDeclared) {
            // If the label of the memory contains vector labels apply
            // the address expression of the memory port as the index to the vector.
            val idx = sx.exps.head
            val lbx = apply_index_vech(lb, idx)
            // Replace references to the original memory in the labels with
            // references to this port
            rename_mem_in_lb(sx.mem, sx.name)(lbx)
          } else {
            bot
          }
        labels(sx.name) = lbxx
        sx copy (lbl = lbxx)
      case sx => sx map label_exprs_e(labels)
  }

  // Add each port declaration to the label context
  def label_exprs_p(labels: LabelMap)(p: Port) : Port = {
    val lb = to_bundle(p.tpe, p.lbl)
    val isDeclared = checkDeclared(lb, p.info, p.name)
    val lblx =  if(isDeclared) { lb } else { bot }
    labels(p.name) = lblx
    p copy (lbl = lblx)
  }

  def label_exprs(m: DefModule) : DefModule = {
    val labels = new LabelMap
    m map label_exprs_p(labels) map label_exprs_s(labels)
  }

  def vec_size(t: Type) = t match {
    case tx: VectorType => IntWidth(log2Up(tx.size))
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
