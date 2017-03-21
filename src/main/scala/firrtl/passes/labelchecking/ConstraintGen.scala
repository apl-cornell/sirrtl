package firrtl.passes
import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import firrtl.Driver._
import collection.mutable.Set

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
  // Identifier used for reference expression in Z3 constraints
  def refToIdent(e: Expression): String
  // Declaration string for reference expressions
  def exprToDeclaration(e: Expression): String
  // Representation of expression in Z3
  def exprToCons(e: Expression): Constraint
  def exprToCons(e: Expression, w: BigInt): Constraint
  // Representation of expression in Z3 as a boolean
  def exprToConsBool(e: Expression): Constraint
  // Serialization of labels. May depend on particular constraint generator
  def serialize(l: LabelComp) = l.serialize
  
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
    case sx: DefNode =>
        connect(conEnv, whenEnv, CAtom(sx.name), exprToCons(sx.value))
        whenEnv(sx) = whenEnv.cur; sx
      case sx: ConnectPC =>
        (sx.loc.tpe, sx.expr.tpe) match {
          case ((loct: BundleType, expt: BundleType))  =>
            loct.fields.foreach { f =>
              val locx = WSubField(sx.loc,  f.name, f.tpe, f.lbl, UNKNOWNGENDER)
              val expx = WSubField(sx.expr, f.name, f.tpe, f.lbl, UNKNOWNGENDER)
              val w = bitWidth(locx.tpe)
              connect(conEnv, whenEnv, exprToCons(locx), exprToCons(expx))
            }
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
            loct.fields.foreach { f =>
              val locx = WSubField(sx.loc,  f.name, f.tpe, f.lbl, UNKNOWNGENDER)
              val expx = WSubField(sx.expr, f.name, f.tpe, f.lbl, UNKNOWNGENDER)
              val w = bitWidth(locx.tpe)
              connect(conEnv, whenEnv, exprToCons(locx), exprToCons(expx))
            }
          case ((loct: BundleType, _)) => throw new Exception(s"bad expr: ${sx.info}")
          case ((_, expt: BundleType)) => throw new Exception(s"bad expr: ${sx.info}")
          case _ =>
            val w = bitWidth(sx.loc.tpe)
            connect(conEnv, whenEnv, exprToCons(sx.loc), exprToCons(sx.expr, w))
        }
        whenEnv(sx) = whenEnv.cur; sx
      case sx: Conditionally =>
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

  def gen_cons(conEnv: ConnectionEnv, whenEnv: WhenEnv)(m: DefModule) =
    m map gen_cons_s(conEnv, whenEnv)

  //--------------------------------------------------------------------------- 
  // Collect set of all Refs / Subfields that must be declared
  //---------------------------------------------------------------------------
  // This is done by locating all refs/subfields that are referenced in the 
  // module.
  type DeclSet = Set[String]
  def decls_l(declSet: DeclSet)(l: Label) : Label =
    l map decls_lc(declSet) map decls_l(declSet)

  def decls_lc(declSet: DeclSet)(l: LabelComp) : LabelComp =
    l map decls_e(declSet) map decls_lc(declSet)

  def decls_e(declSet: DeclSet)(e: Expression) : Expression = 
    e map decls_l(declSet) match {
    case ex : WSubIndex => declSet += exprToDeclaration(ex); ex
    case ex : WSubAccess => declSet += exprToDeclaration(ex); ex
    case ex : WRef => declSet += exprToDeclaration(ex); ex
    case ex : WSubField => declSet +=  exprToDeclaration(ex); ex
    case ex => ex map decls_e(declSet)
  }

  def decls_s(declSet: DeclSet)(s: Statement) : Statement = s match {
    // do not count references in invalid, defreg, or defwire
    case sx : IsInvalid => sx 
    case sx : DefRegister => sx
    case sx : DefWire => sx
    case PartialConnectPC(info, loc, expr, pc) => (loc.tpe, expr.tpe) match {
      case ((loct: BundleType, exprt: BundleType)) =>
        loct.fields.foreach { f =>
          val locx  = WSubField(loc,  f.name, f.tpe, f.lbl, UNKNOWNGENDER)
          val exprx = WSubField(expr, f.name, f.tpe, f.lbl, UNKNOWNGENDER)
          declSet += exprToDeclaration(locx map decls_l(declSet))
          declSet += exprToDeclaration(exprx map decls_l(declSet))
        }
        s
      case ((loct: BundleType, _)) => throw new Exception(s"bad expr: ${info}")
      case ((_, exprx: BundleType)) => throw new Exception(s"bad expr: ${info}")
      case _ => s map decls_e(declSet) map decls_l(declSet)
    }
    case ConnectPC(info, loc, expr, pc) => (loc.tpe, expr.tpe) match {
      case ((loct: BundleType, exprt: BundleType)) =>
        loct.fields.foreach { f =>
          val locx  = WSubField(loc,  f.name, f.tpe, f.lbl, UNKNOWNGENDER)
          val exprx = WSubField(expr, f.name, f.tpe, f.lbl, UNKNOWNGENDER)
          declSet += exprToDeclaration(locx map decls_l(declSet))
          declSet += exprToDeclaration(exprx map decls_l(declSet))
        }
        s
      case ((loct: BundleType, _)) => throw new Exception(s"bad expr: ${info}")
      case ((_, exprx: BundleType)) => throw new Exception(s"bad expr: ${info}")
      case _ => s map decls_e(declSet) map decls_l(declSet)
    }
    case sx : Block =>
      sx map decls_s(declSet) map decls_e(declSet) map decls_l(declSet)
    case sx => try {
      sx map decls_s(declSet) map decls_e(declSet) map decls_l(declSet)
    } catch {
      case (e: Exception) =>
        throw new Exception(s"bad statement: [${sx.getClass.toString}] ${sx.info} ${sx.serialize}")
      throw e
    }
  }

  def declarations(m: DefModule) : Set[String] = {
    val declSet = Set[String]()
    m map decls_s(declSet)
    declSet
  }
}

object BVConstraintGen extends ConstraintGenerator {
  def toBInt(w: Width) =
    w.asInstanceOf[IntWidth].width

  // XXX This does not include a terribly precise representation of arrays. 
  // Arrays are essentially modeled as single variables as in SecVerilog's 
  // implementation. This is safe as long as vectors are not referenced in 
  // dependent types. For now an exception should be thrown if an array is 
  // referenced in a dependent type. Implementing precise reasoning about arrays 
  // would be difficult - it would also require a representation of arbitrary 
  // record types. Currently record elements are modeled as separate variables. 
  // With a representation of arbitrary record types, the theory of arrays 
  // should work. Arbitrary records can be represented with algebraic 
  // datatypes.
  def exprToDeclaration(e: Expression) = {
    /*
    def tpeToW(tpe: Type) : BigInt = tpe match {
      case UIntType(w) => toBInt(w)
      case SIntType(w) => toBInt(w)
      case FixedType(w,_) => toBInt(w)
      case ClockType => 1
      case VectorType(tx, s) => tpeToW(tx)
    }
    */
    e match {
      case ex : WSubIndex => exprToDeclaration(ex.exp)
      case ex : WSubAccess=> exprToDeclaration(ex.exp)
      case ex : WRef => 
        var s = ""
        try {
          val width = bitWidth(ex.tpe)
          s = s"(declare-const ${refToIdent(ex)} (_ BitVec $width))\n"
        } catch {
          case (excp: Exception) =>
            println(s"bad ex: ${ex.serialize}\n${ex.toString}\n${ex.tpe.serialize}\n${ex.tpe.toString}")
            throw excp
        }
        s
      case ex : WSubField  =>
        val width = bitWidth(ex.tpe)
        s"(declare-const ${refToIdent(ex)} (_ BitVec $width))\n"
      case Declassify(exx, _) =>
        exprToDeclaration(exx)
      case Endorse(exx,_) =>
        exprToDeclaration(exx)
    }
  }

  def refToIdent(e: Expression) =  e match {
    case ex: WSubIndex => refToIdent(ex.exp)
    case ex: WSubAccess => refToIdent(ex.exp)
    case WRef(name,_,_,_,_) => name
    case WSubField(exp,name,_,_,_) => 
      refToIdent(exp) + "_" + name
  }

  def exprToCons(e: Expression) = e match {
    case ex : Literal => CBVLit(ex.value, toBInt(ex.width))
    case ex : DoPrim => primOpToBVOp(ex)
    case ex : WSubIndex => CAtom(refToIdent(ex.exp))
    case ex : WSubAccess => CAtom(refToIdent(ex.exp))
    case ex : WRef => CAtom(refToIdent(ex))
    case ex : WSubField => CAtom(refToIdent(ex))
    case Declassify(exx,_) => exprToCons(exx)
    case Endorse(exx,_) => exprToCons(exx)
  }

  def exprToCons(e: Expression, w: BigInt) = e match {
    case ex : Literal => CBVLit(ex.value, w)
    case _ =>
      val diff = w - bitWidth(e.tpe)
      val c = exprToCons(e)
      if(diff > 0) CBinOp("concat", CBVLit(0, diff), c) else c
  }

  def exprToConsBool(e: Expression) =
    CBVWrappedBV(exprToCons(e), bitWidth(e.tpe))

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

  def unimpl(s: String) =
    CAtom(s"UNIMPL $s")

  def primOpToBVOp(e: DoPrim) = e.op.serialize match {
    case "add" => mkBin("bvadd", e)
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
    case "shl" => mkBinC("bvshl", e)
    case "shr" => e.tpe match {
      case UIntType(_) => mkBinC("bvlshr", e)
      case SIntType(_) => mkBinC("bvashr", e)
    }
    case "dshl" => mkBin("bvshl", e)
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
    case "cvt" => unimpl(e.op.serialize)
    case "andr" => unimpl(e.op.serialize)
    case "orr" => unimpl(e.op.serialize)
    case "xorr" => unimpl(e.op.serialize)
    case "head" => unimpl(e.op.serialize)
    case "tail" => unimpl(e.op.serialize)

    // TODO FixPoint Ops
    case "asFixedPoint" => unimpl(e.op.serialize)
    case "bpshl" => unimpl(e.op.serialize)
    case "bpshr" => unimpl(e.op.serialize)
    case "bpset" => unimpl(e.op.serialize)
  }

}
