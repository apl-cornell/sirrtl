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

 def depTypeFuns: String = {
   """; a simple function for testing
      |(define-fun Dom ((x (_ BitVec 2))) Label
      |  (ite (= x (_ bv0 2)) L 
      |  (ite (= x (_ bv1 2)) D1
      |  (ite (= x (_ bv2 2)) D2 H))))
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


object LabelCheck extends Pass with PassDebug {
  def name = "Label Check"
  override def debugThisPass = false

  val cgen = BVConstraintGen

  def run(c:Circuit) = {
    bannerprintb(name)
    dprint(c.serialize)

    val consGenerator = BVConstraintGen
    val constraintFile   = new java.io.PrintWriter(Driver.constraintFileName)
    def emit(s:String) = constraintFile.write(s)
   
    // For debugging only
    def emitConEnv(conEnv: ConnectionEnv) = conEnv.foreach {
      case(loc, cons) => emit(s"(assert (= ${loc.serialize} ${cons.serialize}))\n")
    }

    //-------------------------------------------------------------------------
    // Collect constraints which may affect the value of a dependent type
    //-------------------------------------------------------------------------
    // A set of (location, value) pairs in the constraint domain
    type ConSet = collection.mutable.HashSet[(Constraint,Constraint)]
    def collect_deps_e(conEnv: ConnectionEnv, conSet: ConSet)(e: Expression) : Expression = {
      val ex: Expression = e map collect_deps_e(conEnv, conSet) 
      val c = consGenerator.exprToCons(ex)
      if(conEnv.contains(c)) conSet += ((c, conEnv(c)))
      ex
    }

    def collect_deps_l(conEnv: ConnectionEnv, conSet: ConSet)(l: Label) : Label = 
      l map collect_deps_l(conEnv, conSet) map collect_deps_e(conEnv, conSet)

    def collect_deps(conEnv: ConnectionEnv)(l: Label) : ConSet =  {
      val s = new ConSet
      collect_deps_l(conEnv, s)(l)
      s
    }

    def emit_deps(conSet: ConSet) : Unit = conSet.foreach {
      case(loc, cons) => emit(s"(assert (= ${loc.serialize} ${cons.serialize}))\n")
    }

    //------------------------------------------------------------------------- 
    // Check connections
    //-------------------------------------------------------------------------

    def label_check(conEnv: ConnectionEnv, whenEnv: WhenEnv)(s: Statement): Statement = {
      def ser(l:Label) = consGenerator.serialize(l)
      s map label_check(conEnv, whenEnv) match {
        case sx: Connect =>
          val lhs = sx.loc.lbl
          val rhs = sx.expr.lbl
          val deps = collect_deps(conEnv)(lhs) ++ collect_deps(conEnv)(rhs)
          emit("(push)\n")
          emit(s"""(echo \"Checking Connection: ${sx.info}\")\n""" )
          emit(s"(assert ${whenEnv(s).serialize})\n")
          emit_deps(deps)
          emit(s"(assert (not (leq ${ser(rhs)} ${ser(lhs)}) ) )\n")
          emit("(check-sat)\n")
          emit("(pop)\n")
          emit("\n")
          sx
        case sx: PartialConnect =>
          val lhs = sx.loc.lbl
          val rhs = sx.expr.lbl
          val deps = collect_deps(conEnv)(lhs) ++ collect_deps(conEnv)(rhs)
          emit("(push)\n")
          emit(s"""(echo \"Checking Connection: ${sx.info}\")\n""" )
          emit(s"(assert ${whenEnv(s).serialize})\n")
          emit_deps(deps)
          emit(s"(assert (not (leq ${ser(rhs)} ${ser(lhs)}) ) )\n")
          emit("(check-sat)\n")
          emit("(pop)\n")
          emit("\n")
          sx
        case _ => s
      }
    }

    //------------------------------------------------------------------------
    // Emit constraints which are common to all modules
    //------------------------------------------------------------------------
    emit(ConstraintConst.latticeAxioms)
    emit(PolicyConstraints.declareLevels)
    emit(PolicyConstraints.declareOrder)
    emit(ConstraintConst.depTypeFuns)

    c.modules foreach { m =>
      dprintb(s"Checking Module: ${m.name}: ${m.info}")

      emit("(push)\n")
      emit(s"""(echo \"Checking Module: ${m.info}\")\n""")
      emit("\n")
      
      //-----------------------------------------------------------------------
      // Generate Z3-representation of connection graph
      //-----------------------------------------------------------------------
      val conEnv = new ConnectionEnv 
      val whenEnv = new WhenEnv
      consGenerator.gen_cons(conEnv, whenEnv)(m)

      //-----------------------------------------------------------------------
      // Run Label Passes
      //-----------------------------------------------------------------------
      val (mprime, conEnvPrime) : (DefModule, ConnectionEnv) = (new LabelPassBased{
        def passSeq = Seq(
          SeqPortCheck  // others?
          )
      }).runPasses(m, conEnv, consGenerator)

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
      // emitConEnv(conEnv)
      // emit("\n")
      
      //-----------------------------------------------------------------------
      // Check Assignments
      //-----------------------------------------------------------------------
      m map label_check(conEnvPrime, whenEnv)
      emit("\n")

      emit("(pop)")
    }

    constraintFile.close()

    bannerprintb(s"after $name")
    dprint(c.serialize)
    c
  }
}
