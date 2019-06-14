package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import firrtl.Driver._
import collection.mutable.Set
import java.io.Writer


class LabelCheck(constraintWriter: Writer) extends Pass with PassDebug {
  def name = "Label Check"
  override def debugThisPass = false

  val cgen = BVConstraintGen

  def run(c:Circuit) = {
    bannerprintb(name)
    dprint(c.serialize)

    val consGenerator = BVConstraintGen
    def emit(s:String) = if (constraintWriter != null) { constraintWriter.write(s) }
   
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
            sx map check_declass_e(sx.info)
          } else {
            sx
          }
        case sx: PartialConnectPC => if(!is_mask_connection(sx.loc)) {
            val lhs: Label = sx.loc.lbl
            val rhs: Label = sx.expr.lbl
            check_connection(lhs, rhs, Seq(), sx.info)
            sx map check_declass_e(sx.info)
          } else {
            sx
          }
        //TODO remove, since nodes don't need to be checked.
        // Only the final assignment needs checking
        case sx: DefNodePC =>
          val lhs: Label = sx.lbl
          val rhs: Label = sx.value.lbl
          sx map check_declass_e(sx.info)
        case sx => sx
      }
    }

    def check_declass_e(info: Info)(e: Expression): Expression = {
      e map check_declass_e(info) match {
        case Declassify(expr, lbl) =>
         check_dwngrade(Seq(), e, expr.lbl, lbl, info)
          e
        case Endorse(expr, lbl) =>
          check_dwngrade(Seq(), e, expr.lbl, lbl, info)
          e
        case ex => ex
      }
    }

    //expr is just used to determine whether to "emit_declass" or "emit_endorse" at the end
    //we do not use its label in this function anywhere
    def check_dwngrade(whens: Seq[Constraint], expr: Expression, from: Label, to: Label, info: Info): Unit = {
      (from, to) match {
        case (_: ProdLabel, _: ProdLabel) =>
          emit_dwngrade(expr, from, to, whens, info)
        case (_: Label, rhs: IteLabel) =>
          check_dwngrade(whens ++ Seq(consGenerator.exprToConsBool(rhs.cond)), expr, from, rhs.trueL join rhs.condL, info)
          check_dwngrade(whens ++ Seq(CNot(consGenerator.exprToConsBool(rhs.cond))), expr, from, rhs.falseL join rhs.condL, info)
        case (lhs: IteLabel, _: Label) =>
          check_dwngrade(whens ++ Seq(consGenerator.exprToConsBool(lhs.cond)), expr, lhs.trueL join lhs.condL, to, info)
          check_dwngrade(whens ++ Seq(CNot(consGenerator.exprToConsBool(lhs.cond))), expr, lhs.falseL join lhs.condL, to, info)
        case (_: Label, _: Label) =>
          throw new Exception
      }
    }

    def emit_dwngrade(expr: Expression, from: Label, to: Label, whens: Seq[Constraint], info: Info): Unit = {
      expr match {
        case _: Declassify => emit_declass(from, to, whens, info)
        case _: Endorse => emit_endorse(from, to, whens, info)
      }
    }

    def emit_declass(from:Label, to: Label, whens: Seq[Constraint], info: Info): Unit = {
      def ser(l:LabelComp) = consGenerator.serialize(l)
      emit("(push)\n")
        emit(s"""(echo \"Checking Declassification: ${info}\")\n""" )
        whens.foreach(c => { //add when assertions to scope
          emit(s"(assert ${c.serialize})\n")
        })
        // Prove that the integrity label is not changing.
        emit("(push)\n")
          emit(s"(assert (not (= ${ser(I(from))} ${ser(I(to))})))")
          emit("(check-sat)\n")
        emit("(pop)\n")
        emit(s"(assert (not (leqc ${ser(C(from))} ${ser(C(to) join I(from))})))\n")
        emit("(check-sat)\n")
      emit("(pop)\n")
    }

    def emit_endorse(from:Label, to: Label, whens: Seq[Constraint], info: Info): Unit = {
      def ser(l:LabelComp) = consGenerator.serialize(l)
      emit("(push)\n")
        emit(s"""(echo \"Checking Endorsement: ${info}\")\n""" )
        whens.foreach(c => { //add when assertions to scope
          emit(s"(assert ${c.serialize})\n")
        })
        // Prove that the confidentiality label is not changing.
        emit("(push)\n")
          emit(s"(assert (not (= ${ser(C(from))} ${ser(C(to))})))")
          emit("(check-sat)\n")
        emit("(pop)\n")
        emit(s"(assert (not (leqi ${ser(I(from))} ${ser(I(to) meet C(from))})))\n")
        emit("(check-sat)\n")
      emit("(pop)\n")
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
        case (lhs: JoinLabel, rhs: Label) =>
          check_connection(lhs.l, rhs, whens, info)
          check_connection(lhs.r, rhs, whens, info)
        case (lhs: Label, rhs:JoinLabel) => //resolving these joins earlier causes problems
          rhs match {
            case JoinLabel(l:IteLabel, r:IteLabel) =>
              val innerLeft = IteLabel(r.cond, r.condL, r.trueL join l.trueL, r.falseL join l.trueL)
              val innerRight = IteLabel(r.cond, r.condL, r.trueL join l.falseL, r.falseL join l.falseL)
              check_connection(lhs, IteLabel(l.cond, l.condL, innerLeft, innerRight), whens, info)
            case _ =>
              throw new Exception
          }
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

    bannerprintb(s"after $name")
    dprint(c.serialize)
    c
  }
}
