package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import firrtl.Driver._
import collection.mutable.Set

object LabelCheck extends Pass with PassDebug {
  def name = "Label Check"
  override def debugThisPass = true

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
      l map collect_deps_lc(conEnv, conSet) map collect_deps_l(conEnv, conSet)

    def collect_deps_lc(conEnv: ConnectionEnv, conSet: ConSet)(l: LabelComp) : LabelComp = 
      l map collect_deps_lc(conEnv, conSet) map collect_deps_e(conEnv, conSet)

    def collect_deps(conEnv: ConnectionEnv)(l: Label) : ConSet =  {
      val s = new ConSet
      collect_deps_l(conEnv, s)(l)
      s
    }

    def emit_deps(conSet: ConSet) : Unit = conSet.foreach {
      case(loc, cons) => emit(s"(assert (= ${loc.serialize} ${cons.serialize}))\n")
    }
   
    //-----------------------------------------------------------------------------
    // Collect constraints that define values in the whenEnv constraint
    //-----------------------------------------------------------------------------
    def atoms_in_con(c: Constraint): Set[CAtom] = {
      def atoms_in_con_(s: Set[CAtom])(c: Constraint): Constraint = 
        c mapCons atoms_in_con_(s) match {
          case cx: CAtom => s += cx; cx
          case cx => cx
      }
      val s = Set[CAtom]()
      atoms_in_con_(Set[CAtom]())(c)
      s
    }

    def collect_deps_c(conEnv: ConnectionEnv)(c: Constraint): ConSet = {
      def collect_deps_c_(conEnv: ConnectionEnv, conSet: ConSet)(c: Constraint) : Constraint = {
        val cx: Constraint = c mapCons collect_deps_c_(conEnv, conSet)
        if(conEnv.contains(cx)) conSet += ((c, conEnv(c)))
        cx
      }
      val s = new ConSet
      collect_deps_c_(conEnv, s)(c)
      s
    }

    //------------------------------------------------------------------------- 
    // Check connections
    //-------------------------------------------------------------------------

    def label_check(conEnv: ConnectionEnv, whenEnv: WhenEnv)(s: Statement): Statement = {
      def ser(l:LabelComp) = consGenerator.serialize(l)
      s map label_check(conEnv, whenEnv) match {
        case sx: Connect =>
          val lhs: Label = sx.loc.lbl
          val rhs: Label = sx.expr.lbl
          val whenC: Constraint = whenEnv(sx)
          val deps = collect_deps(conEnv)(lhs) ++
            collect_deps(conEnv)(rhs) ++
            collect_deps_c(conEnv)(whenC)
          emit("(push)\n")
          emit(s"""(echo \"Checking Connection (Conf): ${sx.info}\")\n""" )
          emit(s"(assert ${whenC.serialize})\n")
          emit_deps(deps)
          emit(s"(assert (not (leq ${ser(C(rhs))} ${ser(C(lhs))}) ) )\n")
          emit("(check-sat)\n")
          emit("(pop)\n")

          emit("(push)\n")
          emit(s"""(echo \"Checking Connection (Integ): ${sx.info}\")\n""" )
          emit(s"(assert ${whenC.serialize})\n")
          emit_deps(deps)
          emit(s"(assert (not (leq ${ser(I(lhs))} ${ser(I(rhs))}) ) )\n")
          emit("(check-sat)\n")
          emit("(pop)\n")
          emit("\n")
          sx
        case sx: PartialConnect =>
          val lhs: Label = sx.loc.lbl
          val rhs: Label = sx.expr.lbl
          val whenC: Constraint = whenEnv(sx)
          val deps = collect_deps(conEnv)(lhs) ++
            collect_deps(conEnv)(rhs) ++
            collect_deps_c(conEnv)(whenC)
          emit("(push)\n")
          emit(s"""(echo \"Checking Connection (Conf): ${sx.info}\")\n""" )
          emit(s"(assert ${whenC.serialize})\n")
          emit_deps(deps)
          emit(s"(assert (not (leq ${ser(C(rhs))} ${ser(C(lhs))}) ) )\n")
          emit("(check-sat)\n")
          emit("(pop)\n")

          emit("(push)\n")
          emit(s"""(echo \"Checking Connection (Integ): ${sx.info}\")\n""" )
          emit(s"(assert ${whenC.serialize})\n")
          emit_deps(deps)
          emit(s"(assert (not (leq ${ser(I(lhs))} ${ser(I(rhs))}) ) )\n")
          emit("(check-sat)\n")
          emit("(pop)\n")
          emit("\n")
          sx
        case _ => s
      }
    }

    //------------------------------------------------------------------------
    // Emit preamble which contains constraints common to all modules
    //------------------------------------------------------------------------
    emit(PolicyHolder.preamble)

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
