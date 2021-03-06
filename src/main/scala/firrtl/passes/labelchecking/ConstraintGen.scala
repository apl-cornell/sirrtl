package firrtl.passes
import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import firrtl.Driver._
import firrtl.passes.RipNexts.IllegalNextException

import collection.mutable.Set
import collection.mutable.LinkedHashSet
import collection.mutable.Map
import collection.mutable.LinkedHashMap

// A mapping from locations in the constraint domain to their values in the 
// constraint domain.
class ConnectionEnv extends collection.mutable.LinkedHashMap[Constraint,(Constraint, Info)]
  { override def default(c:Constraint) = ((c, NoInfo)) }


abstract class ConstraintGenerator {
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
  // Type declaration string
  def emitTypeDecl(typeDecs: TypeDeclSet)(t: AggregateType): String


  def nextIdent(s: String) =
    "$" + s
  def next_exp(e: Expression) = RipNexts.next_exp(e)
  val bot = ProdLabel(PolicyHolder.bottom, PolicyHolder.top)
  val top = ProdLabel(PolicyHolder.top, PolicyHolder.bottom)
  
  //---------------------------------------------------------------------------
  // Connection Environment Population
  //---------------------------------------------------------------------------
  // Generate a connection mapping. This is a set in which each assignable 
  // location is uniquely mapped to a single value in the constraint domain
  def connect(conEnv: ConnectionEnv, loc: Expression, cprime: Expression, w: BigInt, info: Info) {
    (loc, cprime) match {
      case (locx: Next, cprimex: Expression) =>
        conEnv(exprToCons(locx)) = ((exprToCons(cprimex, w), info))
      case (locx: Expression, cprimex: Next) =>
        conEnv(exprToCons(locx)) = ((exprToCons(cprimex, w), info))
      case (_,_) =>
        conEnv(exprToCons(loc)) = ((exprToCons(cprime, w), info))
        try {
          val next_loc = next_exp(loc)
          val next_expr = next_exp(cprime)
          conEnv(exprToCons(next_loc)) = ((exprToCons(next_expr, w), info))
        } catch {
          case exc: IllegalNextException =>
          case exc: Exception => throw exc
        }
    }

  }

  def connect_outer(lhs: Expression, rhs: Expression, conEnv: ConnectionEnv, info: Info): Unit =
    (lhs.tpe, rhs.tpe) match {
       case ((loct: VectorType, expt: VectorType)) =>
         val w = bitWidth(lhs.tpe)
         connect(conEnv, lhs, rhs, w, info)
       case ((loct: BundleType, expt: BundleType))  =>
         loct.fields.foreach { f => if (has_field(expt, f.name)) {
           val locx = WSubField(lhs, f.name, f.tpe, f.lbl, UNKNOWNGENDER)
           val expx = WSubField(rhs, f.name, f.tpe, f.lbl, UNKNOWNGENDER)
           val w = bitWidth(locx.tpe)
           connect_outer(locx, expx, conEnv, info)
         }}
       case ((loct: BundleType, _)) => throw new Exception(s"bad expr: ${info}")
       case ((_, expt: BundleType)) => throw new Exception(s"bad expr: ${info}")
       case ((_: GroundType, _:GroundType)) =>
         val w = bitWidth(lhs.tpe)
         connect(conEnv, lhs, rhs, w, info)
       case _ => throw new Exception(s"bad types connected: ${lhs.tpe.serialize}, ${rhs.tpe.serialize}")
    }

  // The purpose of this function is to mutate conEnv and labelEnv (by populating
  // them) Note: this is the identity function on the statement argument. 
  def gen_cons_s(conEnv: ConnectionEnv)(s: Statement): Statement = s match {
      case sx: DefNodePC =>
        val nref = WRef(sx.name, sx.value.tpe, sx.lbl, NodeKind, FEMALE)
        sx.value match {
          case sxv : ValidIf =>
            //TODO overhaul constraint generation so this isn't necessary
            // For constraints, ValidIf is equivalent to a MUX where fv == LHS of assignment
            // Assumes that all ValidIfs appear in node defs, which they do after High->Labeled Transforms run
            val rhs = Mux(sxv.cond, sxv.value, nref, mux_type_and_widths(sxv.value, nref, true), sxv.lbl)
            connect_outer(nref, rhs, conEnv, sx.info)
          case _ => connect_outer(nref, sx.value, conEnv, sx.info)
        }
        sx
      case sx: ConnectPC => 
        connect_outer(sx.loc, sx.expr, conEnv, sx.info)
        sx
      case sx: PartialConnectPC =>
        connect_outer(sx.loc, sx.expr, conEnv, sx.info)
        sx
      case sx =>
        sx map gen_cons_s(conEnv)
        sx
  }

  def gen_cons(conEnv: ConnectionEnv)(m: DefModule) = {
    m map gen_cons_s(conEnv)
  }

  //--------------------------------------------------------------------------- 
  // Collect all declarations and declare them in Z3
  //---------------------------------------------------------------------------
  type DeclSet = LinkedHashSet[String]
  type TypeDeclSet = LinkedHashMap[AggregateType, String]

  // Used to weaken equality within TypeDeclSet 
  case class WeakField(name: String, tpe: Type, isSeq: Boolean) extends FirrtlNode with HasName {
    def serialize: String =  name + " : " + tpe.serialize
  }
  case class WeakBundle(fields: Seq[WeakField]) extends AggregateType {
    def serialize: String = "{ " + (fields map (_.serialize) mkString ", ") + "}"
    def mapType(f: Type => Type): Type =
      WeakBundle(fields map (x => x.copy(tpe = f(x.tpe))))
  }

  def weakenType(tpe: Type): Type = tpe map weakenType match {
    case tx: BundleType => WeakBundle(tx.fields.map(weakenField(_)))
    case tx => tx
  }
  def weakenField(field: Field) = WeakField(field.name, weakenType(field.tpe), field.isSeq)
  def weakenBundle(bundle: BundleType) = weakenType(bundle).asInstanceOf[WeakBundle]

  def collect_type_decls(typeDecs: TypeDeclSet)(name: String, t: Type): Unit =  t match {
    case tx : BundleType =>
      val n = name.toUpperCase
      val txx = weakenBundle(tx)
      if(!typeDecs.contains(txx)) {
        txx.fields.foreach {f => collect_type_decls(typeDecs)(n + "_" + f.name, f.tpe) }
        typeDecs(txx) = n
      } else typeDecs(txx)
    case tx : WeakBundle =>
      val n = name.toUpperCase
      if(!typeDecs.contains(tx)) {
        tx.fields.foreach {f => collect_type_decls(typeDecs)(n + "_" + f.name, f.tpe) }
        typeDecs(tx) = n
      } else typeDecs(tx)
    case VectorType(tpe, _) =>
      collect_type_decls(typeDecs)(name, tpe)
    case tx =>
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
      collect_type_decls(typeDecs)(sx.name, MemPortUtils.memType(sx))
      declSet += emitDecl(typeDecs, sx.name, MemPortUtils.memType(sx))
      sx
    case sx: WDefInstance =>
      collect_type_decls(typeDecs)(sx.name, sx.tpe)
      declSet += emitDecl(typeDecs, sx.name, sx.tpe); sx
    case sx => sx map decls_s(declSet, typeDecs)
  }

  def next_decls_s(declSet: DeclSet, typeDecs: TypeDeclSet)(s: Statement): Statement = s match {
    case sx: DefRegister =>
      collect_type_decls(typeDecs)(nextIdent(sx.name), sx.tpe)
      declSet += emitDecl(typeDecs, nextIdent(sx.name), sx.tpe); sx
    case sx: DefWire =>
      collect_type_decls(typeDecs)(nextIdent(sx.name), sx.tpe)
      declSet += emitDecl(typeDecs, nextIdent(sx.name), sx.tpe); sx
    case sx: WDefInstance =>
      collect_type_decls(typeDecs)(nextIdent(sx.name), sx.tpe)
      declSet += emitDecl(typeDecs, nextIdent(sx.name), sx.tpe); sx
    case sx: DefNodePC =>
      collect_type_decls(typeDecs)(nextIdent(sx.name), sx.value.tpe)
      declSet += emitDecl(typeDecs, nextIdent(sx.name), sx.value.tpe); sx
    case sx: DefMemory =>
      collect_type_decls(typeDecs)(nextIdent(sx.name), MemPortUtils.memType(sx))
      declSet += emitDecl(typeDecs, nextIdent(sx.name), MemPortUtils.memType(sx))
      sx
    case sx => sx map next_decls_s(declSet, typeDecs)
  }

  def decls_p(declSet: DeclSet, typeDecs: TypeDeclSet)(p: Port): Port ={
    collect_type_decls(typeDecs)(p.name, p.tpe)
    declSet += emitDecl(typeDecs, p.name, p.tpe)
    declSet += emitDecl(typeDecs, nextIdent(p.name), p.tpe)
    p
  }

  def declarations(m: DefModule) : LinkedHashSet[String] = {
    val declSet = new LinkedHashSet[String]()
    val typeDecs = new LinkedHashMap[AggregateType, String]()
    m map decls_p(declSet, typeDecs) map decls_s(declSet, typeDecs) map next_decls_s(declSet, typeDecs)
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
    case tx : BundleType => typeDecls(weakenBundle(tx))
    case tx : WeakBundle => typeDecls(tx)
    case tx : VectorType => 
      val indextpe = emitDatatype(typeDecls, UIntType(vec_size(tx)))
      val datatpe = emitDatatype(typeDecls, tx.tpe)
      s"(Array $indextpe $datatpe)"
    case ClockType => s"(_ BitVec 1)"
    case _ => ""
  }

  def emitDecl(typeDecls: TypeDeclSet, name: String, t: Type): String = t match {
    case tx : UIntType => s"(declare-const $name ${emitDatatype(typeDecls, tx)})\n"
    case tx : SIntType => s"(declare-const $name ${emitDatatype(typeDecls, tx)})\n"
    case tx : BundleType => s"(declare-const $name ${emitDatatype(typeDecls, tx)})\n"
    case tx : WeakBundle => s"(declare-const $name ${emitDatatype(typeDecls, tx)})\n"
    case tx : VectorType => s"(declare-const $name ${emitDatatype(typeDecls, tx)})\n"
    case ClockType => s"(declare-const $name (_ BitVec 1))\n"
    case _ => ""
  }

  def emitTypeDecl(typeDecs: TypeDeclSet)(t: AggregateType): String = t match {
    case tx : BundleType if tx.fields.length > 0  =>
      val name = typeDecs(tx)
      val field_decls = tx.fields.map { case Field(n,_,tpe,_,isSeq) =>
        val fieldDecl = s"(field_$n ${emitDatatype(typeDecs, tpe)})"
        s"$fieldDecl"
      } reduceLeft (_ + _)
      s"(declare-datatypes () (($name (mk-$name $field_decls))))\n"
    case tx: WeakBundle if tx.fields.length > 0 =>
      val name = typeDecs(tx)
      val field_decls = tx.fields.map { case WeakField(n, tpe, isSeq) =>
        val fieldDecl = s"(field_$n ${emitDatatype(typeDecs, tpe)})"
        s"$fieldDecl"
      } reduceLeft (_ + _)
      s"(declare-datatypes () (($name (mk-$name $field_decls))))\n"
    case tx : VectorType => throw new Exception
    case _ =>  ""
  }

  // h4x to get around bad compile times for transforms on dependent labels 
  // appearing in bundle types
  def toWIR(e: Expression) = ToWorkingIR.toExp(e)


  def refToIdent(e: Expression):String =  toWIR(e) match {
    case ex: WSubIndex => 
      val idx = CBVLit(ex.value, toBInt(vec_size(ex.exp.tpe)))
      CASelect(refToIdent(ex.exp), idx).serialize
    case ex: WSubAccess => 
      // try {
      //   toBInt(vec_size(ex.exp.tpe))
      // } catch {
      //   case (t: Throwable) =>
      //   println(s"sub_access causing excp: ${ex.serialize}")
      //   println(s"sub_access.exp causing excp: ${ex.exp.serialize}")
      //   t
      // }
      try {
        val idx = exprToCons(ex.index, toBInt(vec_size(ex.exp.tpe)))
        CASelect(refToIdent(ex.exp), idx).serialize
      } catch { 
        case (t: Exception) =>
          val idx = exprToCons(ex.index)
          CASelect(refToIdent(ex.exp), idx).serialize
      }
    case WRef(name,_,_,_,_) => name
    case WSubField(exp,name,_,_,_) => s"(field_$name ${refToIdent(exp)})"
    case ex: Mux =>
      // Why does this even happen? Vecs of Muxes??
      exprToCons(ex).serialize 
    case Declassify(exx, _) => refToIdent(exx)
    case Endorse(exx, _) => refToIdent(exx)
    case ex : DoPrim => ex.op match {
      case PrimOps.Bits => refToIdent(ex.args(0))
    }
    case Next(ex, _, _, _) => ex match {
      case exr : WRef  => refToIdent(exr copy(name = nextIdent(exr.name)))
      case _ => nextIdent(refToIdent(ex))
    }
  }

  def exprToCons(e: Expression): Constraint = toWIR(e) match {
    case ex : Literal => CBVLit(ex.value, toBInt(ex.width))
    case ex : DoPrim => primOpToBVOp(ex)
    case ex : WSubIndex => 
      val idx = CBVLit(ex.value, toBInt(vec_size(ex.exp.tpe)))
      CASelect(refToIdent(ex.exp), idx)
    case ex : WSubAccess => 
      CASelect(refToIdent(ex.exp), exprToCons(ex.index, toBInt(vec_size(ex.exp.tpe))))
    case ex : Next => CAtom(refToIdent(ex))
    case ex : WRef => CAtom(refToIdent(ex))
    case ex : WSubField => CAtom(refToIdent(ex))
    case ex : Mux => 
      val w = bitWidth(ex.tpe)
      val sel = CBVWrappedBV(exprToCons(ex.cond), bitWidth(ex.cond.tpe))
      CIfTE(sel, exprToCons(ex.tval, w), exprToCons(ex.fval, w))
    case Declassify(exx,_) => exprToCons(exx)
    case Endorse(exx,_) => exprToCons(exx)
    case _ => CTrue
  }

  def exprToCons(e: Expression, w: BigInt) = toWIR(e) match {
    case ex : Literal => CBVLit(ex.value, w)
    case _ =>
      var diff = BigInt(0)
      try {
        diff = w - bitWidth(e.tpe)
      } catch {
        case (t: Throwable) =>
        //   println(s"bad expr: ${e.serialize}")
        //   throw t
      }
      val c = exprToCons(e)
      if(diff > 0) CBinOp("concat", CBVLit(0, diff), c) 
      else if(diff < 0) CBVExtract(w-1, 0, c)
      else c
  }

  def exprToConsBool(e: Expression) = {
    val ePrime = toWIR(e)
    CBVWrappedBV(exprToCons(ePrime), bitWidth(ePrime.tpe))
  }

  override def serialize(l: LabelComp) = l match {
    case FunLabel(fname, args) => //s"($fname ${refToIdent(arg)})"
      s"($fname ${args map { refToIdent(_) } mkString(" ")})"
    case IfLabelComp(cond, tcomp, fcomp) =>
      s"(ite ${CBVWrappedBV(exprToCons(cond), bitWidth(cond.tpe)).serialize} ${serialize(tcomp)} ${serialize(fcomp)})"
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
        val arr_cons = exprToCons(arr).serialize
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
    case "sub" => CBinOp("concat", CBVLit(0, 1), mkBin("bvsub", e))
    case "mul" => 
      val w = Math.max(bitWidth(e.args(0).tpe).toInt, bitWidth(e.args(1).tpe).toInt)
      val diff = bitWidth(e.tpe) - w 
      if(diff > 0) CBinOp("concat", CBVLit(0, diff), mkBin("bvmul", e))
      else mkBin("bvmul", e)
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
      if(diff > 0) CBinOp("concat", mkBinC("bvshl", e), CBVLit(0, diff))
      else mkBinC("bvshl", e)
    case "shr" => 
      val shift = e.tpe match {
        case UIntType(_) => mkBinC("bvlshr", e)
        case SIntType(_) => mkBinC("bvashr", e)
      }
      CBVExtract(bitWidth(e.tpe)-1, 0, shift)
    case "dshl" => 
      val w = Math.max(bitWidth(e.args(0).tpe).toInt, bitWidth(e.args(1).tpe).toInt)
      val diff = bitWidth(e.tpe) - w 
      if( diff > 0) CBinOp("concat", mkBin("bvshl", e), CBVLit(0, diff))
      else mkBin("bvshl", e)

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
    case "bits" =>
      CBVExtract(e.consts(0),e.consts(1),exprToCons(e.args(0)))

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

  def vec_size(t: Type) = t match {
    case tx: VectorType => IntWidth(log2Up(tx.size))
  }

}
