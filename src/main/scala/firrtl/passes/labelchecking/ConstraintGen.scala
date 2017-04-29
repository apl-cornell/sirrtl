package firrtl.passes
import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import firrtl.Driver._
import collection.mutable.Set
import collection.mutable.LinkedHashSet
import collection.mutable.Map
import collection.mutable.LinkedHashMap

// A mapping from locations in the constraint domain to their values in the 
// constraint domain.
class ConnectionEnv extends collection.mutable.HashMap[Constraint,Constraint]
  { override def default(c:Constraint) = c }


// A mapping from statements to a constraint which is known to be true upon 
// execution of that statement because of where the statement appears in 
// relation to (possibly nested) when statements.
// Note that even seemingly identical statements are non-unique because they 
// have uniquely identifying info objects, so this mapping correctly determines 
// a fact that is known upon execution of the indexed statement.
class WhenEnv extends collection.mutable.HashMap[Statement,Constraint] {
  var cur : Constraint = CTrue
}

abstract class ConstraintGenerator {
  type MemDataCons = collection.mutable.LinkedHashSet[Constraint]
  // Identifier used for reference expression in Z3 constraints
  def refToIdent(e: Expression): String
  // Representation of expression in Z3
  def exprToCons(e: Expression): Constraint
  def exprToCons(e: Expression, w: BigInt): Constraint
  // Representation of expression in Z3 as a boolean
  def exprToConsBool(e: Expression): Constraint
  // Serialization of labels. May depend on particular constraint generator
  def serialize(l: LabelComp) = l.serialize
  // Declaration string
  def emitDecl(typeDecs: TypeDeclSet, name: String, t: Type): String
  def emitMemDataDecl(typeDecs: TypeDeclSet, mem:DefMemory): String
  // Type declaration string
  def emitTypeDecl(typeDecs: TypeDeclSet)(t: AggregateType): String
  // Generate underlying memory data constraints
  def genMemCons(conEnv: MemDataCons, mem:DefMemory): Unit

  val bot = ProdLabel(PolicyHolder.bottom, PolicyHolder.top)
  val top = ProdLabel(PolicyHolder.top, PolicyHolder.bottom)
  
  //---------------------------------------------------------------------------
  // Connection Environment Population
  //---------------------------------------------------------------------------
  // Generate a connection mapping. This is a set in which each assignable 
  // location is uniquely mapped to a single value in the constraint domain
  def connect(conEnv: ConnectionEnv, whenEnv: WhenEnv, loc: Constraint, cprime: Constraint) {
    if(whenEnv.cur == CTrue || !conEnv.contains(loc)) {
      // This is just to simplify generated constraints
      conEnv(loc) = cprime
    } else {
      conEnv(loc) = CIfTE(whenEnv.cur, cprime, conEnv(loc))
    }
  }

  // The purpose of this function is to mutate conEnv and whenEnv (by populating 
  // them) Note: this is the identity function on the statement argument. 
  def gen_cons_s(conEnv: ConnectionEnv, whenEnv: WhenEnv)(s: Statement): Statement = s match {
      case sx: DefNodePC =>
        connect(conEnv, whenEnv, CAtom(sx.name), exprToCons(sx.value))
        whenEnv(sx) = whenEnv.cur; sx
      case sx: ConnectPC =>
        (sx.loc.tpe, sx.expr.tpe) match {
          case ((loct: BundleType, expt: BundleType))  =>
            loct.fields.foreach { f => if(has_field(expt, f.name)) {
              val locx = WSubField(sx.loc,  f.name, f.tpe, f.lbl, UNKNOWNGENDER)
              val expx = WSubField(sx.expr, f.name, f.tpe, f.lbl, UNKNOWNGENDER)
              val w = bitWidth(locx.tpe)
              connect(conEnv, whenEnv, exprToCons(locx), exprToCons(expx))
            }}
          case ((loct: BundleType, _)) => throw new Exception(s"bad expr: ${sx.info}")
          case ((_, expt: BundleType)) => throw new Exception(s"bad expr: ${sx.info}")
          case _ =>
            val w = bitWidth(sx.loc.tpe)
            connect(conEnv, whenEnv, exprToCons(sx.loc), exprToCons(sx.expr, w))
        }
        whenEnv(sx) = whenEnv.cur; sx
      case sx: PartialConnectPC =>
        (sx.loc.tpe, sx.expr.tpe) match {
          case ((loct: BundleType, expt: BundleType))  =>
            loct.fields.foreach { f => if (has_field(expt, f.name)) {
              val locx = WSubField(sx.loc,  f.name, f.tpe, f.lbl, UNKNOWNGENDER)
              val expx = WSubField(sx.expr, f.name, f.tpe, f.lbl, UNKNOWNGENDER)
              val w = bitWidth(locx.tpe)
              connect(conEnv, whenEnv, exprToCons(locx), exprToCons(expx))
            }}
          case ((loct: BundleType, _)) => throw new Exception(s"bad expr: ${sx.info}")
          case ((_, expt: BundleType)) => throw new Exception(s"bad expr: ${sx.info}")
          case _ =>
            val w = bitWidth(sx.loc.tpe)
            connect(conEnv, whenEnv, exprToCons(sx.loc), exprToCons(sx.expr, w))
        }
        whenEnv(sx) = whenEnv.cur; sx
      case sx: ConditionallyPC =>
        val pred = exprToConsBool(sx.pred)
        val oldWhen = whenEnv.cur
        // True side
        whenEnv.cur = if(whenEnv.cur == CTrue) pred else CConj(whenEnv.cur, pred)
        sx.conseq map gen_cons_s(conEnv, whenEnv)
        whenEnv(sx.conseq) = whenEnv.cur
        // False side
        whenEnv.cur = CNot(whenEnv.cur)
        sx.alt map gen_cons_s(conEnv, whenEnv)
        whenEnv(sx.alt) = whenEnv.cur
        // This statement
        whenEnv.cur = oldWhen
        whenEnv(sx) = whenEnv.cur
        sx
      case sx => 
        sx map gen_cons_s(conEnv, whenEnv)
        whenEnv(sx) = whenEnv.cur
        sx
  }

  def gen_mem_cons_s(memCons: MemDataCons)(s: Statement): Statement =
    s map gen_mem_cons_s(memCons) match {
      case sx: DefMemory => genMemCons(memCons, sx); sx
      case sx => sx
    }

  def gen_cons(conEnv: ConnectionEnv, whenEnv: WhenEnv, memCons: MemDataCons)(m: DefModule) =
    m map gen_cons_s(conEnv, whenEnv) map gen_mem_cons_s(memCons)

  //--------------------------------------------------------------------------- 
  // Collect all declarations and declare them in Z3
  //---------------------------------------------------------------------------
  type DeclSet = LinkedHashSet[String]
  type TypeDeclSet = LinkedHashMap[AggregateType, String]

  def collect_type_decls(typeDecs: TypeDeclSet)(name: String, t: Type): Unit =  t match {
    case tx : BundleType =>
      val n = name.replace("$", "").toUpperCase
      if(!typeDecs.contains(tx)) {
        tx.fields.foreach {f => collect_type_decls(typeDecs)(n + "_" + f.name, f.tpe) }
        typeDecs(tx) = n
      } else typeDecs(tx)
    case VectorType(tpe, _) =>
      // TODO make an array
      collect_type_decls(typeDecs)(name, tpe)
    case tx =>
  }

  def memPortBundle(mem: DefMemory): BundleType = {
    val addrTpe = UIntType(IntWidth(log2Up(mem.depth)))
    BundleType(Seq(
      Field("addr", Default, addrTpe, bot, false),
      Field("clk", Default, ClockType, bot, false),
      Field("en", Default, UIntType(IntWidth(1)), bot, false),
      Field("mask", Default, UIntType(IntWidth(1)), bot, false),
      Field("data", Default, mem.dataType, mem.lbl, true)))
  }

  def decls_s(declSet: DeclSet, typeDecs: TypeDeclSet)(s: Statement): Statement = s match {
    case sx: DefRegister =>
      collect_type_decls(typeDecs)(sx.name, sx.tpe)
      declSet += emitDecl(typeDecs, sx.name, sx.tpe); sx
    case sx: DefWire => 
      collect_type_decls(typeDecs)(sx.name, sx.tpe)
      declSet += emitDecl(typeDecs, sx.name, sx.tpe); sx
    case sx: DefNode =>
      collect_type_decls(typeDecs)(sx.name, sx.value.tpe)
      declSet += emitDecl(typeDecs, sx.name, sx.value.tpe); sx
    case sx: DefNodePC =>
      collect_type_decls(typeDecs)(sx.name, sx.value.tpe)
      declSet += emitDecl(typeDecs, sx.name, sx.value.tpe); sx
    case sx: DefMemory =>
      // TODO address, en, possibly need separate labels from data
      val addrTpe = UIntType(IntWidth(log2Up(sx.depth)))
      val portBundleT = memPortBundle(sx)
      val portBundleL = LabelExprs.to_bundle(portBundleT, UnknownLabel)
      val declType = BundleType(
        (sx.readers ++ sx.writers ++ sx.readwriters) map { pname =>
          Field(pname, Default, portBundleT, portBundleL, false)
        })
      collect_type_decls(typeDecs)(sx.name, declType)
      declSet += emitDecl(typeDecs, sx.name, declType)
      declSet += emitMemDataDecl(typeDecs, sx)
      sx
    case sx => sx map decls_s(declSet, typeDecs)
  }

  def decls_p(declSet: DeclSet, typeDecs: TypeDeclSet)(p: Port): Port ={
    collect_type_decls(typeDecs)(p.name, p.tpe)
    declSet += emitDecl(typeDecs, p.name, p.tpe)
    p
  }

  def declarations(m: DefModule) : LinkedHashSet[String] = {
    val declSet = new LinkedHashSet[String]()
    val typeDecs = new LinkedHashMap[AggregateType, String]()
    m map decls_p(declSet, typeDecs) map decls_s(declSet, typeDecs)
    var type_dec_strs = new LinkedHashSet[String]()
    typeDecs.keys.foreach { k => type_dec_strs += emitTypeDecl(typeDecs)(k) }
    type_dec_strs ++ declSet
  }
}

object BVConstraintGen extends ConstraintGenerator {
  def toBInt(w: Width) =
    w.asInstanceOf[IntWidth].width

  def emitDatatype(typeDecls: TypeDeclSet, t: Type): String = t match {
    case tx : UIntType => s"(_ BitVec ${bitWidth(tx)})"
    case tx : SIntType => s"(_ BitVec ${bitWidth(tx)})"
    case tx : BundleType => typeDecls(tx)
    case VectorType(tpe, _) => 
      // TODO actually represent this as an array
      emitDatatype(typeDecls, tpe)
    case ClockType => s"(_ BitVec 1)"
  }

  def emitDecl(typeDecls: TypeDeclSet, name: String, t: Type): String = t match {
    case tx : UIntType => s"(declare-const $name ${emitDatatype(typeDecls, tx)})\n"
    case tx : SIntType => s"(declare-const $name ${emitDatatype(typeDecls, tx)})\n"
    case tx : BundleType => s"(declare-const $name ${emitDatatype(typeDecls, tx)})\n"
    case VectorType(tpe, _) => 
      // TODO actually represent this as an array
      emitDecl(typeDecls, name, tpe)
    case ClockType => s"(declare-const $name (_ BitVec 1))\n"
  }

  def emitMemDataDecl(td: TypeDeclSet, mem:DefMemory): String = {
    val indextpe = emitDatatype(td, UIntType(IntWidth(log2Up(mem.depth))))
    val datatpe = emitDatatype(td, mem.dataType)
    s"(declare-const ${mem.name}_data (Array $indextpe $datatpe))\n"
  }


  def emitTypeDecl(typeDecs: TypeDeclSet)(t: AggregateType): String = t match {
    case tx : BundleType => 
      val name = typeDecs(tx)
      val field_decls = tx.fields.map { case Field(n,_,tpe,_,_) =>
        s"(field_$n ${emitDatatype(typeDecs, tpe)})"
      } reduceLeft (_ + _)
      s"(declare-datatypes () (($name (mk-$name $field_decls))))\n"
    case tx : VectorType => ""
  }

  def refToIdent(e: Expression) =  e match {
    case ex: WSubIndex => refToIdent(ex.exp)
    case ex: WSubAccess => refToIdent(ex.exp)
    case WRef(name,_,_,_,_) => name
    case WSubField(exp,name,_,_,_) => 
      s"(field_$name ${refToIdent(exp)})"
  }

  def genMemCons(conEnv: MemDataCons, mem: DefMemory): Unit = {
    val addrTpe = UIntType(IntWidth(log2Up(mem.depth)))
    val u1 = UIntType(IntWidth(1))
    val mt = memPortBundle(mem)
    val ul = UnknownLabel; val ug = UNKNOWNGENDER 
    val memr = WRef(mem.name, mt, ul, MemKind, ug)
    def addr(pname:String) = exprToCons(
      WSubField(WSubField(memr, pname, mt, ul, ug),
        "addr", addrTpe, ul, ug))
    def data(pname:String) = exprToCons(
      WSubField(WSubField(memr, pname, mt, ul, ug),
        "data", mem.dataType, ul, ug))
    def en(pname:String) = exprToCons(
      WSubField(WSubField(memr, pname, mt, ul, ug), "en", u1, ul, ug))
    def mask(pname:String) = exprToCons(
      WSubField(WSubField(memr, pname, mt, ul, ug), "mask", u1, ul, ug))

    val arr = mem.name + "_data"

    mem.readers foreach { pname =>
      conEnv += CImpl( CBVWrappedBV(en(pname), 1), 
        CEq(CASelect(arr, addr(pname)), data(pname))) 
    }
    mem.writers foreach { pname =>
      val cond = CConj(CBVWrappedBV(en(pname), 1),
        CBVWrappedBV(mask(pname), 1))
      conEnv += CImpl(cond, CAStore(arr, addr(pname), data(pname)))
    }
    // Not supporting readwriters
  }

  def exprToCons(e: Expression): Constraint = e match {
    case ex : Literal => CBVLit(ex.value, toBInt(ex.width))
    case ex : DoPrim => primOpToBVOp(ex)
    case ex : WSubIndex => CAtom(refToIdent(ex.exp))
    case ex : WSubAccess => CAtom(refToIdent(ex.exp))
    case ex : WRef => CAtom(refToIdent(ex))
    case ex : WSubField => CAtom(refToIdent(ex))
    case ex : Mux => 
      val w = bitWidth(ex.tpe)
      val sel = CBVWrappedBV(exprToCons(ex.cond), bitWidth(ex.cond.tpe))
      CIfTE(sel, exprToCons(ex.tval, w), exprToCons(ex.fval, w))
    case Declassify(exx,_) => exprToCons(exx)
    case Endorse(exx,_) => exprToCons(exx)
  }

  def exprToCons(e: Expression, w: BigInt) = e match {
    case ex : Literal => CBVLit(ex.value, w)
    case _ =>
      val diff = w - bitWidth(e.tpe)
      val c = exprToCons(e)
      if(diff > 0) CBinOp("concat", CBVLit(0, diff), c) 
      else if(diff < 0) CBVExtract(w-1, 0, c)
      else c
  }

  def exprToConsBool(e: Expression) =
    CBVWrappedBV(exprToCons(e), bitWidth(e.tpe))

  def transformMemData(e: Expression): Expression =
    e map transformMemData match {
      case ex: WRef => //if ex.kind == MemKind =>
        // Somehow despite the dependands resolving to MemKinds as expected in 
        // that pass, they seem to all have NodeKind by the time they get 
        // here... For now just assume this is only used with memories and not 
        // other kinds of vectors
        ex.copy(name = ex.name + "_data")
      case ex => ex
    }

  override def serialize(l: LabelComp) = l match {
    case FunLabel(fname, args) => //s"($fname ${refToIdent(arg)})"
      s"($fname ${args map { refToIdent(_) } mkString(" ")})"
    case JoinLabelComp(l,r) => s"(join ${serialize(l)} ${serialize(r)})"
    case MeetLabelComp(l,r) => s"(meet ${serialize(l)} ${serialize(r)})"
    case lx: Level => lx.serialize
    case UnknownLabelComp => l.serialize
    case lx: HLevel => PolicyHolder.policy match {
      case p: HypercubePolicy => exprToCons(lx.arg, p.lvlwidth).serialize
      case _ => throw new Exception("Tried to serialize Hypercube label without Hypercube Policy")
    }
    case IndexedVecHLevel(arr, idx) => PolicyHolder.policy match {
      case p: HypercubePolicy => 
        val idx_cons = exprToCons(idx).serialize
        val arr_cons = exprToCons(transformMemData(arr)).serialize
        s"(select $arr_cons $idx_cons)"
      case _ => throw new Exception("Tried to serialize Hypercube label without Hypercube Policy")
    }
      case lx: VecHLevel => lx.serialize
  }

  // Shortcut for creating a binary operator in the constraint domain
  // when the arguments are not constants
  def mkBin(op: String, e: DoPrim) = {
    def autoExpand(e1: Expression, e2: Expression) = {
      val (w1, w2) = (bitWidth(e1.tpe).toInt, bitWidth(e2.tpe).toInt)
      val w = Math.max(w1, w2)
      (exprToCons(e1, w), exprToCons(e2, w))
    }
    val (c1, c2) = autoExpand(e.args(0), e.args(1))
    CBinOp(op, c1, c2)
  }

  // Shortcut for creating a binary operator in the constraint domain
  // when the arguments are constants
  def mkBinC(op: String, e: DoPrim) =
    CBinOp(op, exprToCons(e.args(0)), CBVLit(e.consts(0), bitWidth(e.args(0).tpe)))

  // So dangeresque ~(*.*)~
  def unimpl(s: String, w:BigInt) =
    // 0xbeef
    if(w > 16) CBVLit(48879, w)
    else CBVLit(0, w)

  def primOpToBVOp(e: DoPrim) = e.op.serialize match {
    case "add" => 
      CBinOp("concat", CBVLit(0, 1), mkBin("bvadd", e))
    case "sub" => mkBin("bvsub", e)
    case "mul" => mkBin("bvmul", e)
    case "div" => e.tpe match {
      case UIntType(_) => mkBin("bvudiv", e)
      case SIntType(_) => mkBin("bvsdiv", e)
    }
    case "rem" => e.tpe match {
      case UIntType(_) => mkBin("bvurem", e)
      case SIntType(_) => mkBin("bvsrem", e)
    }
    case "lt" => CBVWrappedBool(e.tpe match {
      case UIntType(_) => mkBin("bvult", e)
      case SIntType(_) => mkBin("bvslt", e)
    }, bitWidth(e.tpe))
    case "leq" => CBVWrappedBool(e.tpe match {
      case UIntType(_) => mkBin("bvule", e)
      case SIntType(_) => mkBin("bvsle", e)
    }, bitWidth(e.tpe))
    case "gt" => CBVWrappedBool(e.tpe match {
      case UIntType(_) => mkBin("bvugt", e)
      case SIntType(_) => mkBin("bvsgt", e)
    }, bitWidth(e.tpe))
    case "geq" => CBVWrappedBool(e.tpe match {
      case UIntType(_) => mkBin("bvuge", e)
      case SIntType(_) => mkBin("bvsge", e)
    }, bitWidth(e.tpe))
    case "eq"  => CBVWrappedBool(mkBin("=", e), 1)
    case "neq" => CBVWrappedBool(CNot(mkBin("=", e)), 1)
    case "pad" => 
      val w = bitWidth(e.args(0).tpe)
      val diff = e.consts(0).toInt - w
      CBinOp("concat", CBVLit(0, diff), exprToCons(e.args(0)))
    case "asUInt" => exprToCons(e.args(0))
    case "asSInt" => exprToCons(e.args(0))
    case "asClock" => exprToCons(e.args(0))
    case "shl" => 
      val diff = e.consts(0).toInt
      CBinOp("concat", CBVLit(0, diff), mkBinC("bvshl", e))
    case "shr" => 
      val shift = e.tpe match {
        case UIntType(_) => mkBinC("bvlshr", e)
        case SIntType(_) => mkBinC("bvashr", e)
      }
      CBVExtract(bitWidth(e.tpe)-1, 0, shift)
    case "dshl" => 
      val w = Math.max(bitWidth(e.args(0).tpe).toInt, bitWidth(e.args(1).tpe).toInt)
      val diff = bitWidth(e.tpe) - w 
      CBinOp("concat", CBVLit(0, diff), mkBin("bvshl", e))
    case "dshr" => e.tpe match {
      case UIntType(_) => mkBin("bvlshr", e)
      case SIntType(_) => mkBin("bvashr", e)
    }
    case "neg" => CUnOp("bvneg", exprToCons(e.args(0)))
    case "not" => 
      CBVWrappedBool(CNot(exprToConsBool(e.args(0))),bitWidth(e.tpe))
    case "and" => mkBin("bvand", e)
    case "or" => mkBin("bvor", e)
    case "cat" => 
      // Don't autoExpand
      CBinOp("concat", exprToCons(e.args(0)), exprToCons(e.args(1)))
    case "xor" => mkBin("bvxor", e)
    case "bits" => CBVExtract(e.consts(0),e.consts(1),exprToCons(e.args(0)))

    // TODO Multi-arg ops
    case "cvt"  => unimpl(e.op.serialize, bitWidth(e.tpe))
    case "andr" => unimpl(e.op.serialize, bitWidth(e.tpe))
    case "orr"  => unimpl(e.op.serialize, bitWidth(e.tpe))
    case "xorr" => unimpl(e.op.serialize, bitWidth(e.tpe))
    case "head" => unimpl(e.op.serialize, bitWidth(e.tpe))
    case "tail" => unimpl(e.op.serialize, bitWidth(e.tpe))

    // TODO FixPoint Ops
    case "asFixedPoint" => unimpl(e.op.serialize, bitWidth(e.tpe))
    case "bpshl" => unimpl(e.op.serialize, bitWidth(e.tpe))
    case "bpshr" => unimpl(e.op.serialize, bitWidth(e.tpe))
    case "bpset" => unimpl(e.op.serialize, bitWidth(e.tpe))
  }

}
