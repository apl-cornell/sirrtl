package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import firrtl.Driver._
import collection.mutable.Set

object ConstraintConst {
  def latticeAxioms: String = {
"""; this part encodes a partial order on labels
   |(declare-sort Label)
   |(declare-fun leq (Label Label) Bool)
   |(declare-fun join (Label Label) Label)
   |(declare-fun meet (Label Label) Label)
   |(assert (forall ((x Label)) (leq x x)))
   |(assert (forall ((x Label) (y Label) (z Label)) (implies (and (leq x y) (leq y z)) (leq x z))))
   |(assert (forall ((x Label) (y Label)) (implies (and (leq x y) (leq y x)) (= x y))))

   |; axioms for join
   |(assert (forall ((x Label) (y Label) (z Label)) (implies (leq (join x y) z) (and (leq x z) (leq y z)))))
   |(assert (forall ((x Label) (y Label) (z Label)) (implies (and (leq x z) (leq y z)) (leq (join x y) z))))
   |(assert (forall ((x Label) (y Label)) (and (leq x (join x y)) (leq y (join x y)))))
   |(assert (forall ((x Label) (y Label)) (= (join x y) (join y x))))
   
   |; axioms for meet
   |(assert (forall ((x Label) (y Label) (z Label)) (implies (leq x (meet y z)) (and (leq x y) (leq x z)))))
   |(assert (forall ((x Label) (y Label) (z Label)) (implies (and (leq x y) (leq x z)) (leq x (meet y z)))))
   |(assert (forall ((x Label) (y Label)) (and (leq (meet x y) x) (leq (meet x y) y))))
   |(assert (forall ((x Label) (y Label)) (= (meet x y) (meet y x))))
   |
   |""".stripMargin
 }

}

object PolicyConstraints {
  val policy = PolicyHolder.policy
  val top    = PolicyHolder.policy.top
  val bot    = PolicyHolder.policy.bottom

  def declareLevels: String = {
    "; lattice elements\n" +
    policy.levels.map{ level =>
      s"(declare-const $level Label)\n"
    }.fold(""){_+_} + "\n"
  }

  def declareOrder: String = {
    "; lattice order\n" +
    policy.levels.map{ level =>
      (for( coveringLevel <- PolicyHolder.policy.covers(level) )
        yield s"(assert (leq $level $coveringLevel))\n").fold(""){_+_}
    }.fold(""){_+_} +
    s"(assert (not (= $top $bot)))\n\n"
  }
}

class ConnectionEnv extends collection.mutable.HashMap[String,Constraint]
  { override def default(k:String) = CIdent(k) }

abstract class ConstraintGenerator {
  // Identifier used for reference expression in Z3 constraints
  def refToIdent(e: Expression): String
  // Declaration string for reference expressions
  def exprToDeclaration(e: Expression): String
  // Representation of expression in Z3
  def exprToCons(e: Expression): Constraint
  // Representation of expression in Z3 as a boolean
  def exprToConsBool(e: Expression): Constraint

  //---------------------------------------------------------------------------
  // Connection Environment Population
  //---------------------------------------------------------------------------
  var whenConstraint : Constraint = CTrue

  def connect(conEnv: ConnectionEnv, loc: String, cprime: Constraint) {
    if(whenConstraint == CTrue || !conEnv.contains(loc)) {
      conEnv(loc) = cprime
    } else {
      conEnv(loc) = CIfTE(whenConstraint, cprime, conEnv(loc))
    }
  }

  def gen_cons_s(conEnv: ConnectionEnv)(s: Statement): Statement = s match {
    case sx: DefNode =>
        connect(conEnv,sx.name,exprToCons(sx.value)); sx
      case sx: Connect =>
        connect(conEnv,exprToCons(sx.loc).serialize,exprToCons(sx.expr)); sx
      case sx: PartialConnect =>
        connect(conEnv,exprToCons(sx.loc).serialize,exprToCons(sx.expr)); sx
      case sx: Conditionally =>
        // TODO make the apply function of CConj magic and implement it as a 
        // fake case class like JoinLabel
        val pred = exprToConsBool(sx.pred)
        val oldWhen = whenConstraint
        whenConstraint = if(whenConstraint == CTrue) pred else CConj(whenConstraint, pred)
        val conseqx = sx.conseq map gen_cons_s(conEnv)
        whenConstraint = CNot(whenConstraint)
        val altx = sx.alt map gen_cons_s(conEnv)
        whenConstraint = oldWhen
        Conditionally(sx.info, sx.pred, conseqx, altx)
      case sx => sx map gen_cons_s(conEnv)
  }

  def gen_cons(conEnv: ConnectionEnv)(m: DefModule) = {
    whenConstraint = CTrue
    m map gen_cons_s(conEnv)
  }

  //--------------------------------------------------------------------------- 
  // Collect Declarations for All References in Module 
  //---------------------------------------------------------------------------
  type DeclSet = Set[String]
  def decls_e(declSet: DeclSet)(e: Expression) : Expression = e match {
    case ex : WRef => declSet += exprToDeclaration(ex); ex
    case ex : WSubField => declSet +=  exprToDeclaration(ex); ex
    case ex => ex map decls_e(declSet)
  }
  def decls_s(declSet: DeclSet)(s: Statement) : Statement = s match {
    // do not count references in invalid
    case sx : IsInvalid => sx 
    case sx => sx map decls_s(declSet) map decls_e(declSet)
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

  def exprToDeclaration(e: Expression) = e match {
    case ex : WRef => 
      val width = ex.tpe match {
        case UIntType(w) => toBInt(w)
        case SIntType(w) => toBInt(w)
        case FixedType(w,_) => toBInt(w)
        case ClockType => 1
      }
      s"(declare-const ${refToIdent(ex)} (_ BitVec $width))\n"
    case ex : WSubField  =>
      val width = ex.tpe match {
        case UIntType(w) => toBInt(w)
        case SIntType(w) => toBInt(w)
        case FixedType(w,_) => toBInt(w)
        case ClockType => 1
      }
      s"(declare-const ${refToIdent(ex)} (_ BitVec $width))\n"
  }

  def refToIdent(e: Expression) = e match {
    case WRef(name,_,_,_,_) => name
    case WSubField(exp,name,_,_,_) => exp match {
      case expx : WRef => expx.name + "_" + name
      // else match error
    }
  }

  def exprToCons(e: Expression) = e match {
    case ex : Literal => CBVLit(ex.value, toBInt(ex.width))
    case ex : DoPrim => primOpToBVOp(ex)
    case ex : WRef => CIdent(refToIdent(ex))
    case ex : WSubField => CIdent(refToIdent(ex))
  }

  def exprToConsBool(e: Expression) =
    CBVWrappedBV(exprToCons(e), bitWidth(e.tpe))

  def mkBin(op: String, e: DoPrim) = {
    def autoExpand(e1: Expression, e2: Expression) = {
      val (w1, w2) = (bitWidth(e1.tpe).toInt, bitWidth(e2.tpe).toInt)
      val w = Math.max(w1, w2)
      val c1 = if(w1 < w) CBinOp("concat", CBVLit(0, w-w1), exprToCons(e1)) else exprToCons(e1)
      val c2 = if(w2 < w) CBinOp("concat", CBVLit(0, w-w2), exprToCons(e2)) else exprToCons(e2)
      (c1, c2)
    }
    val (c1, c2) = autoExpand(e.args(0), e.args(1))
    CBinOp(op, c1, c2)
  }

  def mkBinC(op: String, e: DoPrim) =
    CBinOp(op, exprToCons(e.args(0)), CBVLit(e.consts(0), bitWidth(e.args(0).tpe)))

  def unimpl(s: String) =
    CIdent(s"UNIMPL $s")

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
    case "eq" => CBVWrappedBool(
      CEq(exprToCons(e.args(0)),exprToCons(e.args(1))),
      bitWidth(e.args(0).tpe))
    case "neq" => CBVWrappedBool(
      CNot(CEq(exprToCons(e.args(0)),exprToCons(e.args(1)))),
      bitWidth(e.args(0).tpe))
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

object LabelCheck extends Pass with PassDebug {
  def name = "Label Check"
  override def debugThisPass = true

  val cgen = BVConstraintGen

  // To check an assignement:
  // s1 = set of dependand expressions of lhs and rhs labels
  // s2 = set of reference expressions which affect valuations of e in s1
  // emit declarations for s2
  // emit connections for s2
  // emit constraint from when context
  // check that label of lhs < rhs

  def run(c:Circuit) = {
    bannerprintb(name)
    dprint(c.serialize)

    val constraintFile   = new java.io.PrintWriter(Driver.constraintFileName)
    def emit(s:String) = constraintFile.write(s)
   
    //------------------------------------------------------------------------
    // Emit constraints which are common to all modules
    //------------------------------------------------------------------------
    emit(ConstraintConst.latticeAxioms)
    emit(PolicyConstraints.declareLevels)
    emit(PolicyConstraints.declareOrder)

    // For debugging only
    def emitConEnv(conEnv:ConnectionEnv) = conEnv.foreach {
      case(loc, cons) => emit(s"(assert (= $loc ${cons.serialize}))\n")
    }

    val consGenerator = BVConstraintGen
    c.modules foreach { m =>
      emit("(push)\n")
      emit(s"""(echo \"Checking Module: ${m.info}\")\n""")
      emit("\n")
      
      //-----------------------------------------------------------------------
      // Generate Z3-representation of connection graph
      //-----------------------------------------------------------------------
      val conEnv = new ConnectionEnv 
      consGenerator.gen_cons(conEnv)(m)

      //-----------------------------------------------------------------------
      // Emit Declarations
      //-----------------------------------------------------------------------
      consGenerator.declarations(m).foreach { emit(_) }
      emit("\n")

      //-----------------------------------------------------------------------
      // Dump Connection Environment 
      //-----------------------------------------------------------------------
      // This is temporary. In the future, connection checks should be scoped, 
      // and only relevant parts of the connection graph will be printed within 
      // that scope. Possibly the same should be done to the declarations.
      emitConEnv(conEnv)
      emit("\n")
      
      //-----------------------------------------------------------------------
      // Check Assignments
      //-----------------------------------------------------------------------

      emit("(pop)")
    }

    constraintFile.close()

    bannerprintb(s"after $name")
    dprint(c.serialize)
    c
  }
}
