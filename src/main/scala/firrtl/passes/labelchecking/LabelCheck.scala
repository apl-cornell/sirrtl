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
  var whenConstraint : Constraint = CTrue

  def locString(e: Expression): String
  def exprToCons(e: Expression): Constraint

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
  def locString(e: Expression) = ""
  def exprToCons(e: Expression) = e match {
    case ex : Literal => CIdent(ex.value.toString)
    case ex : DoPrim => CEq(exprToCons(ex.args(0)), exprToCons(ex.args(1)))
    case WRef(name,_,_,_,_) => CIdent(name)
    case WSubField(exp,name,_,_,_) => exp match {
      case expx : WRef => CIdent(expx.name + "_" + name)
      /// scala.lang.MatchERROAAAAARRRRRR or whatever
    }
  }

}

object LabelCheck extends Pass with PassDebug {
  def name = "Label Check"
  override def debugThisPass = true

  val cgen = BVConstraintGen
  
  def run(c:Circuit) = {
    bannerprintb(name)
    dprint(c.serialize)

    val constraintFile   = new java.io.PrintWriter(Driver.constraintFileName)
    def emit(s:String) = constraintFile.write(s)

    //-------------------------------------------------------------------------
    // Constraint Generation
    //---------.modules map----------------------------------------------------------------
    val conEnv = new ConnectionEnv 
    val consGenerator = BVConstraintGen
    c.modules map consGenerator.gen_cons(conEnv)

    emit(ConstraintConst.latticeAxioms)
    emit(PolicyConstraints.declareLevels)
    emit(PolicyConstraints.declareOrder)

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
