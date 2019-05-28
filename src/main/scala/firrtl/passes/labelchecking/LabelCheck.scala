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

    def label_check(conEnv: ConnectionEnv)(s: Statement): Statement = {
      def ser(l:LabelComp) = consGenerator.serialize(l)
      s map label_check(conEnv) match {
        case sx: ConnectPC => if(!is_mask_connection(sx.loc)) {
            val lhs: Label = sx.loc.lbl
            val rhs: Label = sx.expr.lbl
            check_connection(lhs, rhs, Seq(), sx.info)
            sx map check_declass_e(sx.pc, sx.info)
          } else {
            sx
          }
        case sx: PartialConnectPC => if(!is_mask_connection(sx.loc)) {
            val lhs: Label = sx.loc.lbl
            val rhs: Label = sx.expr.lbl
            check_connection(lhs, rhs, Seq(), sx.info)
            sx map check_declass_e(sx.pc, sx.info)
          } else {
            sx
          }
        //TODO remove, since nodes don't need to be checked.
        // Only the final assignment needs checking
        case sx: DefNodePC =>
          val lhs: Label = sx.lbl
          val rhs: Label = sx.value.lbl
         // check_connection(lhs, rhs, sx.pc, sx.info)
          sx map check_declass_e(sx.pc, sx.info)
        case sx => sx
      }
    }

    def check_declass_e(pc: Label, info: Info)(e: Expression): Expression = {
      def ser(l:LabelComp) = consGenerator.serialize(l)
      e map check_declass_e(pc, info) match {
        case Declassify(expr, lbl) =>
          emit("(push)\n")
          emit(s"""(echo \"Checking Declassification: ${info}\")\n""" )
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

    def check_connection(lhs: Label, rhs: Label, whens: Seq[Constraint], info: Info): Unit = {
      (lhs, rhs) match {
        case((lhsb: BundleLabel, rhsb: BundleLabel)) => 
          lhsb.fields.foreach { f =>
            val lhsx = f.lbl
            val rhsx = field_label(rhs, f.name)
            val inf = s" (field: ${f.name})"
            rhsx match {
              case UnknownLabel =>
              case _ => check_connection(lhsx, rhsx, whens, info)
            }
          }
        case((lhsb: BundleLabel, rhsx: ProdLabel)) => 
          lhsb.fields.foreach { f =>
            val lhsx = f.lbl
            val inf = s" (field: ${f.name})"
            check_connection(lhsx, rhs, whens, info)
          }
        case((lhsx: ProdLabel, rhsb: BundleLabel)) => 
          rhsb.fields.foreach { f =>
            val rhsx = f.lbl
            val inf = s" (field: ${f.name})"
            check_connection(lhs, rhsx, whens, info)
          }
        case (_: ProdLabel, _: ProdLabel) =>
          emit_conn_check(lhs, rhs, whens, info)
        case  (lhs: IteLabel, rhs: IteLabel) =>
          if (lhs != rhs) { //skip generating obviously true constraints
            check_connection(lhs, rhs.trueL join rhs.condL, whens ++ Seq(consGenerator.exprToConsBool(rhs.cond)), info)
            check_connection(lhs, rhs.falseL join rhs.condL, whens ++ Seq(CNot(consGenerator.exprToConsBool(rhs.cond))), info)
          }
        case (lhs: Label, rhs: IteLabel) =>
          check_connection(lhs, rhs.trueL join rhs.condL, whens ++ Seq(consGenerator.exprToConsBool(rhs.cond)), info)
          check_connection(lhs, rhs.falseL join rhs.condL, whens ++ Seq(CNot(consGenerator.exprToConsBool(rhs.cond))), info)
        case (lhs: IteLabel, rhs: Label) =>
          check_connection(lhs.trueL join lhs.condL, rhs, whens ++ Seq(consGenerator.exprToConsBool(lhs.cond)), info)
          check_connection(lhs.falseL join lhs.condL, rhs, whens ++ Seq(CNot(consGenerator.exprToConsBool(lhs.cond))), info)
        case (lhs: Label,rhs: Label) =>
          throw new Exception
      }
    }

    def emit_conn_check(lhs: Label, rhs: Label,
                        whens: Seq[Constraint], info: Info, extraInfo: String = ""): Unit = {
      def ser(l:LabelComp) = consGenerator.serialize(l)
      emit("(push)\n") //add whens to scope
      whens.foreach(c => {
        emit(s"(assert ${c.serialize})\n")
      })
      emit("(push)\n") //add conf check to scope
      emit(s"""(echo \"Checking Connection (Conf): ${info}${extraInfo}\")\n""" )
      try {
      emit(s"(assert (not (leqc ${ser(C(rhs))} ${ser(C(lhs))}) ) )\n")
      } catch {
        case (t: Exception) =>
          println(s"Exception at source line ${info}")
          throw t
      }
      emit("(check-sat)\n")
      emit("(pop)\n") //remove conf check from scope

      emit("(push)\n") //add int check to scope
      emit(s"""(echo \"Checking Connection (Integ): ${info}${extraInfo}\")\n""" )
      emit(s"(assert (not (leqi ${ser(I(rhs))} ${ser(I(lhs))}) ) )\n")
      emit("(check-sat)\n")
      emit("(pop)\n") //remove int check from scope
      emit("(pop)\n") //remove whens from scope
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
      //
      emit("; Connection Env\n")
      emitConEnv(conEnv)
      // debugConEnv(conEnv)
      emit("\n")
      emit("; End Connection Env\n\n")
      
      //-----------------------------------------------------------------------
      // Check Assignments
      //-----------------------------------------------------------------------
      m map label_check(conEnv)
      emit("\n")

      emit("(pop)")
    }

    constraintFile.close()

    bannerprintb(s"after $name")
    dprint(c.serialize)
    c
  }
}
