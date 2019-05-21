// See LICENSE for license details.

package firrtl.passes

import java.util.NoSuchElementException

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._

object InferTypes extends InferTypesT
trait InferTypesT extends Pass {
  def name = "Infer Types"
  type TypeMap = collection.mutable.LinkedHashMap[String, Type]

  // These are no longer nested in run so that DepsInferTypes can override the 
  // label one and it can refer to the expression one
  def infer_types_l(types: TypeMap)(l: Label): Label = l
  
  def infer_types_e(types: TypeMap)(e: Expression): Expression =
    try {
    e map infer_types_e(types) map infer_types_l(types) match {
      case e: WRef => e copy (tpe = types(e.name))
      case e: Next => e copy (tpe = e.exp.tpe)
      case e: WSubField => e copy (tpe = field_type(e.exp.tpe, e.name))
      case e: WSubIndex => e copy (tpe = sub_type(e.exp.tpe))
      case e: WSubAccess => e copy (tpe = sub_type(e.exp.tpe))
      case e: DoPrim => PrimOps.set_primop_type(e)
      case e: Mux => e copy (tpe = mux_type_and_widths(e.tval, e.fval))
      case e: ValidIf => e copy (tpe = e.value.tpe)
      case e @ (_: UIntLiteral | _: SIntLiteral) => e
      case FnBinding => e
      case ex: Declassify => ex
      case ex: Endorse => ex
    }
    } catch {
      case e => throw e
    }


  def run(c: Circuit): Circuit = {

    val mtypes = (c.modules map (m => m.name ->  module_type(m))).toMap

    val namespace = Namespace()
    def remove_unknowns_w(w: Width): Width = w match {
      case UnknownWidth => VarWidth(namespace.newName("w"))
      case wx => wx
    }

    def remove_unknowns(t: Type): Type =
      t map remove_unknowns map remove_unknowns_w


    def infer_types_p(types: TypeMap)(p: Port): Port = {
      val t = remove_unknowns(p.tpe)
      types(p.name) = t
      p copy (tpe = t)
    }

    def infer_types_s(types: TypeMap)(s: Statement): Statement = s match {
      case sx: WDefInstance =>
        val t = mtypes(sx.module)
        types(sx.name) = t
        sx copy (tpe = t) map infer_types_l(types)
      case sx: DefWire =>
        val t = remove_unknowns(sx.tpe)
        types(sx.name) = t
        sx copy (tpe = t) map infer_types_l(types)
      case sx: DefNode =>
        val sxx = (sx map infer_types_e(types)).asInstanceOf[DefNode]
        val t = remove_unknowns(sxx.value.tpe)
        types(sx.name) = t
        sxx map infer_types_e(types) map infer_types_l(types)
      case sx: DefNodePC =>
        val sxx = (sx map infer_types_e(types)).asInstanceOf[DefNodePC]
        val t = remove_unknowns(sxx.value.tpe)
        types(sx.name) = t
        sxx map infer_types_e(types) map infer_types_l(types)
      case sx: DefRegister =>
        val t = remove_unknowns(sx.tpe)
        types(sx.name) = t
        sx copy (tpe = t) map infer_types_e(types) map infer_types_l(types)
      case sx: DefMemory =>
        val t = remove_unknowns(MemPortUtils.memType(sx))
        types(sx.name) = t
        sx copy (dataType = remove_unknowns(sx.dataType))
      case sx: CDefMemory =>
        types(sx.name) = sx.tpe
        sx
      case sx: CDefMPort =>
        val t = types getOrElse(sx.mem, UnknownType)
        types(sx.name) = t
        sx copy (tpe = t)
      case sx =>
        sx map infer_types_s(types) map infer_types_e(types) map infer_types_l(types)
    }

    def infer_types(m: DefModule): DefModule = {
      val types = new TypeMap
      m map infer_types_p(types) map infer_types_s(types)
    }
 
    c copy (modules = c.modules map infer_types)
  }
}

object CInferTypes extends Pass {
  def name = "CInfer Types"
  type TypeMap = collection.mutable.LinkedHashMap[String, Type]

  def run(c: Circuit): Circuit = {
    val namespace = Namespace()
    val mtypes = (c.modules map (m => m.name -> module_type(m))).toMap

    def infer_types_e(types: TypeMap)(e: Expression) : Expression =
      e map infer_types_e(types) match {
         case (e: Reference) => e copy (tpe = types.getOrElse(e.name, UnknownType))
         case (e: Next) => e copy (tpe = e.exp.tpe)
         case (e: SubField) => e copy (tpe = field_type(e.expr.tpe, e.name))
         case (e: SubIndex) => e copy (tpe = sub_type(e.expr.tpe))
         case (e: SubAccess) => e copy (tpe = sub_type(e.expr.tpe))
         case (e: DoPrim) => PrimOps.set_primop_type(e)
         case (e: Mux) => e copy (tpe = mux_type(e.tval, e.fval))
         case (e: ValidIf) => e copy (tpe = e.value.tpe)
         case FnBinding => e
         case e @ (_: UIntLiteral | _: SIntLiteral) => e
         case ex: Declassify => ex
         case ex: Endorse => ex
      }

    def infer_types_s(types: TypeMap)(s: Statement): Statement = s match {
      case sx: DefRegister =>
        types(sx.name) = sx.tpe
        sx map infer_types_e(types)
      case sx: DefWire =>
        types(sx.name) = sx.tpe
        sx
      case sx: DefNode =>
        val sxx = (sx map infer_types_e(types)).asInstanceOf[DefNode]
        types(sxx.name) = sxx.value.tpe
        sxx
      case sx: DefNodePC =>
        val sxx = (sx map infer_types_e(types)).asInstanceOf[DefNodePC]
        types(sxx.name) = sxx.value.tpe
        sxx
      case sx: DefMemory =>
        types(sx.name) = MemPortUtils.memType(sx)
        sx
      case sx: CDefMPort =>
        val t = types getOrElse(sx.mem, UnknownType)
        types(sx.name) = t
        sx copy (tpe = t)
      case sx: CDefMemory =>
        types(sx.name) = sx.tpe
        sx
      case sx: DefInstance =>
        types(sx.name) = mtypes(sx.module)
        sx
      case sx => sx map infer_types_s(types) map infer_types_e(types)
    }

    def infer_types_p(types: TypeMap)(p: Port): Port = {
      types(p.name) = p.tpe
      p
    }
 
    def infer_types(m: DefModule): DefModule = {
      val types = new TypeMap
      m map infer_types_p(types) map infer_types_s(types)
    }
   
    c copy (modules = c.modules map infer_types)
  }
}
