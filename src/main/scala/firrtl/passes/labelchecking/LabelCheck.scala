package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import firrtl.Driver._
import collection.mutable.Set

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
      case(loc, (cons, info)) => 
        emit(s";${info.serialize}\n")
        emit(s"(assert (= ${loc.serialize} ${cons.serialize}))\n")
    }

    def debugConEnv(conEnv: ConnectionEnv) = conEnv.foreach {
      case(loc, (cons, info)) => 
        emit(s";${info.serialize}\n")
        emit(s";${loc.toString} =>\n    ;${cons.toString}\n")
    }

    //-------------------------------------------------------------------------
    // Collect constraints which may affect the value of a dependent type
    //-------------------------------------------------------------------------
    // A set of (location, value) pairs in the constraint domain
    type ConSet = collection.mutable.LinkedHashSet[(Constraint,(Constraint, Info))]

    def atoms_in_con(c: Constraint): Set[CAtom] = {
      def atoms_in_con_(s: Set[CAtom])(c: Constraint): Constraint = 
        c mapCons atoms_in_con_(s) match {
          case cx: CAtom => s += cx; cx
          case cx => cx
      }
      val s = new collection.mutable.LinkedHashSet[CAtom]()
      atoms_in_con_(s)(c)
      s
    }

    def include_reachable(conEnv: ConnectionEnv, conSet: ConSet): ConSet = {
      def include_reachable_(conEnv: ConnectionEnv, valu: Constraint): Unit = {
        atoms_in_con(valu) foreach {
          atom => if(conEnv.contains(atom)) {
            val (aval, inf) = conEnv(atom)
            conSet += ((atom, (aval, inf)))
            include_reachable_(conEnv, aval)
          }
        }
      }
      conSet foreach { case ((loc, (valu, info))) =>
        include_reachable_(conEnv, valu)
      }
      conSet
    }

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

    // Compute set of exprs on which this label depends, then take transitive 
    // closure over nodes that reach them.
    def collect_deps(conEnv: ConnectionEnv)(l: Label) : ConSet = {
      val s = new ConSet
      collect_deps_l(conEnv, s)(l)
      include_reachable(conEnv, s)
    }

    def emit_deps(conSet: ConSet) : Unit = conSet.foreach {
      case(loc, (cons, info)) => 
        emit(s";${info.serialize}\n")
        emit(s"(assert (= ${loc.serialize} ${cons.serialize}))\n")
    }
    
    //-----------------------------------------------------------------------------
    // Collect constraints that define values in the whenEnv constraint
    //-----------------------------------------------------------------------------
    def collect_deps_c(conEnv: ConnectionEnv)(c: Constraint): ConSet = {
      def collect_deps_c_(conEnv: ConnectionEnv, conSet: ConSet)(c: Constraint) : Constraint = {
        val cx: Constraint = c mapCons collect_deps_c_(conEnv, conSet)
        if(conEnv.contains(cx)) conSet += ((c, conEnv(c)))
        cx
      }
      val s = new ConSet
      collect_deps_c_(conEnv, s)(c)
      include_reachable(conEnv, s)
    }

    //------------------------------------------------------------------------- 
    // Check labels in statements
    //-------------------------------------------------------------------------

    def is_mask_connection(e: Expression): Boolean = {
      var ret = false
      def is_mask_connection_(e: Expression): Expression =
        e map is_mask_connection_ match {
        case ex: WSubField => 
          if(ex.name == "mask" && kind(ex) == MemKind) {
            ret = true
          }
          ex
        case ex => ex
      }
      is_mask_connection_(e)
      ret
    }

    def label_check(conEnv: ConnectionEnv, whenEnv: WhenEnv)(s: Statement): Statement = {
      def ser(l:LabelComp) = consGenerator.serialize(l)
      s map label_check(conEnv, whenEnv) match {
        case sx: ConnectPC => if(!is_mask_connection(sx.loc)) {
            val lhs: Label = sx.loc.lbl
            val rhs: Label = sx.expr.lbl
            val whenC: Constraint = whenEnv(sx)
            val deps = new ConSet
            // val deps = collect_deps(conEnv)(lhs) ++
            //   collect_deps(conEnv)(rhs) ++
            //   collect_deps_c(conEnv)(whenC)
            check_connection(deps, whenC, lhs, rhs, sx.pc, sx.info)
            sx map check_declass_e(deps, whenC, sx.pc, sx.info)
          } else {
            sx
          }
        case sx: PartialConnectPC => if(!is_mask_connection(sx.loc)) {
            val lhs: Label = sx.loc.lbl
            val rhs: Label = sx.expr.lbl
            val whenC: Constraint = whenEnv(sx)
            val deps = new ConSet
            // val deps = collect_deps(conEnv)(lhs) ++
            //   collect_deps(conEnv)(rhs) ++
            //   collect_deps_c(conEnv)(whenC)
            check_connection(deps, whenC, lhs, rhs, sx.pc, sx.info)
            sx map check_declass_e(deps, whenC, sx.pc, sx.info)
          } else {
            sx
          }
        case sx: DefNodePC =>
          val lhs: Label = sx.lbl
          val rhs: Label = sx.value.lbl
          val whenC = whenEnv(sx)
          val deps = new ConSet
          // val deps = collect_deps(conEnv)(lhs) ++
          //   collect_deps(conEnv)(rhs) ++
          //   collect_deps_c(conEnv)(whenC)
          check_connection(deps, whenC, lhs, rhs, sx.pc, sx.info)
          sx map check_declass_e(deps, whenC, sx.pc, sx.info)
        case sx: ConditionallyPC =>
          val whenC = whenEnv(sx)
          val deps = new ConSet
          // val deps = collect_deps_c(conEnv)(whenC)
          sx map check_declass_e(deps, whenC, sx.pc, sx.info)
        case sx => sx
      }
    }

    def check_declass_e(deps: ConSet, whenC: Constraint, pc: Label, info: Info)(e: Expression): Expression = {
      def ser(l:LabelComp) = consGenerator.serialize(l)
      e map check_declass_e(deps, whenC, pc, info) match {
        case Declassify(expr, lbl) =>
          emit("(push)\n")
          emit(s"""(echo \"Checking Declassification: ${info}\")\n""" )
          emit(s"(assert ${whenC.serialize})\n")
          // Prove that the integrity label is not changing.
          emit("(push)\n")
          // Need to introduce a new scope. Otherwise this often lets you prove 
          // false!
          emit(s"(assert (not (= ${ser(I(expr.lbl))} ${ser(I(lbl))})))")
          emit("(check-sat)\n")
          emit("(pop)\n")
          emit(s"(assert (not (leqc ${ser(C(expr.lbl))} ${ser(C(lbl) join I(expr.lbl) join I(pc))})))\n")
          emit("(check-sat)\n")
          emit("(pop)\n")
          e
        case Endorse(expr, lbl) =>
          emit("(push)\n")
          emit(s"""(echo \"Checking Endorsement: ${info}\")\n""" )
          emit(s"(assert ${whenC.serialize})\n")
          // Prove that the integrity label is not changing.
          emit("(push)\n")
          // Need to introduce a new scope. Otherwise this often lets you prove 
          // false!
          emit(s"(assert (not (= ${ser(C(expr.lbl))} ${ser(C(lbl))})))")
          emit("(check-sat)\n")
          emit("(pop)\n")
          emit(s"(assert (not (leqi ${ser(I(expr.lbl))} ${ser(I(lbl) meet C(expr.lbl) meet C(pc))})))\n")
          emit("(check-sat)\n")
          emit("(pop)\n")
          e
        case ex => ex
      }
    }

    def check_connection(deps: ConSet, whenC: Constraint, lhs: Label, rhs: Label, pc: Label, info: Info): Unit = {
      (lhs, rhs) match {
        case((lhsb: BundleLabel, rhsb: BundleLabel)) => 
          lhsb.fields.foreach { f =>
            val lhsx = f.lbl
            val rhsx = field_label(rhs, f.name)
            val inf = s" (field: ${f.name})"
            rhsx match {
              case UnknownLabel =>
              case _ => check_connection(deps, whenC, lhsx, rhsx, pc, info)
            }
          }
        case((lhsb: BundleLabel, rhsx: ProdLabel)) => 
          lhsb.fields.foreach { f =>
            val lhsx = f.lbl
            val inf = s" (field: ${f.name})"
            check_connection(deps, whenC, lhsx, rhs, pc, info)
          }
        case((lhsx: ProdLabel, rhsb: BundleLabel)) => 
          rhsb.fields.foreach { f =>
            val rhsx = f.lbl
            val inf = s" (field: ${f.name})"
            check_connection(deps, whenC, lhs, rhsx, pc, info)
          }
        case (_: ProdLabel, _: ProdLabel) =>
          emit_conn_check(deps, whenC, pc, lhs, rhs, info)
      }
    }

    def emit_conn_check(deps: ConSet, whenC: Constraint, pc: Label, lhs: Label, rhs: Label,
      info: Info, extraInfo: String = ""): Unit = {
      def ser(l:LabelComp) = consGenerator.serialize(l)
      emit("(push)\n")
      emit(s"""(echo \"Checking Connection (Conf): ${info}${extraInfo}\")\n""" )
      emit(s"(assert ${whenC.serialize})\n")
      // emit_deps(deps)
      try {
      emit(s"(assert (not (leqc ${ser(C(rhs) join C(pc))} ${ser(C(lhs))}) ) )\n")
      } catch {
        case (t: Exception) =>
          println(s"Exception at source line ${info}")
          throw t
      }
      emit("(check-sat)\n")
      emit("(pop)\n")

      emit("(push)\n")
      emit(s"""(echo \"Checking Connection (Integ): ${info}${extraInfo}\")\n""" )
      emit(s"(assert ${whenC.serialize})\n")
      // emit_deps(deps)
      // Note that "meet" is the same as the join over integ components
      emit(s"(assert (not (leqi ${ser(I(rhs) meet I(pc))} ${ser(I(lhs))}) ) )\n")
      emit("(check-sat)\n")
      emit("(pop)\n")
      emit("\n")
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
      //
      emit("; Connection Env\n")
      emitConEnv(conEnv)
      // debugConEnv(conEnv)
      emit("\n")
      emit("; End Connection Env\n\n")
      
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
