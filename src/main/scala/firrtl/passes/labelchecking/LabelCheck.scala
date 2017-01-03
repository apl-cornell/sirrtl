package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import firrtl.Driver._

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

 def conversions: String = {
"""|; int to bool and bool to int
   |(define-fun toBool ((x Int)) Bool
   |    (ite (= x 0) false true) ) 
   |(define-fun toInt ((x Bool)) Int 
   |    (ite x 1 0) ) 
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
    s"(assert (not (= $top $bot)))\n"
  }
}

class ConnectionEnv extends collection.mutable.HashMap[String,Constraint]
  { override def default(k:String) = CIdent(k) }

abstract class ConstraintGenerator {
  // Identifier used for reference expression in Z3 constraints
  def refToIdent(e: Expression): String
  // Representation of expression in Z3
  def exprToCons(e: Expression): Constraint

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
      case sx: Connect =>
        connect(conEnv,exprToCons(sx.loc).serialize,exprToCons(sx.expr)); sx
      case sx: PartialConnect =>
        connect(conEnv,exprToCons(sx.loc).serialize,exprToCons(sx.expr)); sx
      case sx: Conditionally =>
        // TODO make the apply function of CConj magic and implement it as a 
        // fake case class like JoinLabel
        val pred = exprToCons(sx.pred)
        val oldWhen = whenConstraint
        whenConstraint = if(whenConstraint == CTrue) pred else CConj(whenConstraint, pred)
        val conseqx = sx.conseq map gen_cons_s(conEnv)
        whenConstraint = CNot(whenConstraint)
        val altx = sx.alt map gen_cons_s(conEnv)
        whenConstraint = oldWhen
        Conditionally(sx.info, sx.pred, conseqx, altx)
      case sx => sx map gen_cons_s(conEnv)
  }

  def gen_cons(conEnv: ConnectionEnv)(m: DefModule) =
    m map gen_cons_s(conEnv)
}

object BVConstraintGen extends ConstraintGenerator {
  def toBInt(w: Width) =
    w.asInstanceOf[IntWidth].width

  def exprToDeclaration(e: Expression) = e match {
    case ex : WRef => 
      val width = ex.tpe match {
        case UIntType(w) => w
        case SIntType(w) => w
        case FixedType(w,_) => w
      }
      s"(declare-const ${refToIdent(ex)} (_ BitVec $width))"
    case ex : WSubField  =>
      val width = ex.tpe match {
        case UIntType(w) => w
        case SIntType(w) => w
        case FixedType(w,_) => w
      }
      s"(declare_const ${refToIdent(ex)} (_ BitVec $width))"
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

  def mkBin(op: String, e: DoPrim) =
    CBinOp(op, exprToCons(e.args(0)), exprToCons(e.args(1)))

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
    case "lt" => e.tpe match {
      case UIntType(_) => mkBin("bvult", e)
      case SIntType(_) => mkBin("bvslt", e)
    }
    case "leq" => e.tpe match {
      case UIntType(_) => mkBin("bvule", e)
      case SIntType(_) => mkBin("bvsle", e)
    }
    case "gt" => e.tpe match {
      case UIntType(_) => mkBin("bvugt", e)
      case SIntType(_) => mkBin("bvsgt", e)
    }
    case "geq" => e.tpe match {
      case UIntType(_) => mkBin("bvuge", e)
      case SIntType(_) => mkBin("bvsge", e)
    }
    case "eq" => CEq(exprToCons(e.args(0)),exprToCons(e.args(1)))
    case "neq" => CNot(CEq(exprToCons(e.args(0)),exprToCons(e.args(1))))
    case "pad" => CBinOp("concat",
      CBVLit(0, e.args(1).asInstanceOf[Literal].value),
      exprToCons(e.args(0)))
    case "asUInt" => exprToCons(e.args(0))
    case "asSInt" => exprToCons(e.args(0))
    case "asClock" => exprToCons(e.args(0))
    case "shl" => mkBin("bvshl", e)
    case "shr" => e.tpe match {
      case UIntType(_) => mkBin("bvlshr", e)
      case SIntType(_) => mkBin("bvashr", e)
    }
    case "dshl" => mkBin("bvshl", e)
    case "dshr" => e.tpe match {
      case UIntType(_) => mkBin("bvlshr", e)
      case SIntType(_) => mkBin("bvashr", e)
    }
    case "cvt" => unimpl(e.op.serialize)
    case "neg" => CUnOp("bvneg", exprToCons(e.args(0)))
    case "not" => CNot(exprToCons(e.args(0)))
    case "and" => mkBin("bvand", e)
    case "or" => mkBin("bvor", e)
    case "xor" => mkBin("bvxor", e)
    case "andr" => unimpl(e.op.serialize)
    case "orr" => unimpl(e.op.serialize)
    case "xorr" => unimpl(e.op.serialize)
    case "cat" => mkBin("concat", e)
    case "bits" => CBVExtract(
      e.args(1).asInstanceOf[Literal].value,
      e.args(2).asInstanceOf[Literal].value,
      exprToCons(e.args(0)))
    case "head" => unimpl(e.op.serialize)
    case "tail" => unimpl(e.op.serialize)
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

    //-------------------------------------------------------------------------
    // Constraint Generation
    //-------------------------------------------------------------------------
    val conEnv = new ConnectionEnv 
    val consGenerator = BVConstraintGen
    c.modules map consGenerator.gen_cons(conEnv)

    emit(ConstraintConst.latticeAxioms)
    emit(PolicyConstraints.declareLevels)
    emit(PolicyConstraints.declareOrder)
    
    //------------------------------------------------------------------------- 
    // Temporary: Emit all connections
    //-------------------------------------------------------------------------
    conEnv.foreach { case (loc, cons) =>
      emit(s"(assert (= $loc ${cons.serialize}))\n")
    }

    constraintFile.close()

    val cprime = c

    bannerprintb(s"after $name")
    dprint(cprime.serialize)
    cprime
  }
}
