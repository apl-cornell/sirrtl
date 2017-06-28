package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._

object PropNodes extends Pass with PassDebug {
  def name = "Propagate Nodes"
  override def debugThisPass = false

  type NodeMap = collection.mutable.LinkedHashMap[String, Expression]

  def tempName(s: String): Boolean = s.startsWith("_T_")

  def collect_nodes_s(nodeMap: NodeMap)(s: Statement): Statement =
    s map collect_nodes_s(nodeMap) match {
      case sx: DefNode if(tempName(sx.name)) => nodeMap(sx.name) = sx.value; sx
      case sx => sx
    }
  
  def sub_nodes_s(nodeMap: NodeMap)(s: Statement): Statement =
    (s map sub_nodes_s(nodeMap)
      map sub_nodes_e(nodeMap)
      map sub_nodes_l(nodeMap)) match {
      case sx: DefNode if(tempName(sx.name)) => EmptyStmt
      case sx: Block => Block(sx.stmts.filter { bs => bs match {
          case EmptyStmt => false
          case _ => true
        }})
      case sx => sx
    }

  def sub_nodes_e(nodeMap: NodeMap)(e: Expression): Expression = 
    e map sub_nodes_l(nodeMap) map sub_nodes_e(nodeMap) match {
      case ex: WRef if nodeMap.contains(ex.name) =>
        sub_nodes_e(nodeMap)(nodeMap(ex.name))
      case ex: Reference if nodeMap.contains(ex.name) =>
        sub_nodes_e(nodeMap)(nodeMap(ex.name))
      case ex => ex
    }

  def sub_nodes_l(nodeMap: NodeMap)(l: Label): Label =
    l map sub_nodes_lc(nodeMap) map sub_nodes_l(nodeMap)

  def sub_nodes_lc(nodeMap: NodeMap)(lc: LabelComp): LabelComp =
    lc map sub_nodes_e(nodeMap) map sub_nodes_lc(nodeMap) match {
      case lx: IndexedVecHLevel => dprint(s"indexedvec: ${lx.toString}"); lx
      case lx => lx
    }

  def prop_nodes(m: DefModule): DefModule = {
    val nodeMap = new NodeMap
    (m map collect_nodes_s(nodeMap)
       map sub_nodes_s(nodeMap))
  }

  def run(c: Circuit) = {
    bannerprintb(name)
    dprint(c.serialize)

    val cprime = c copy (modules = c.modules map prop_nodes)
    
    bannerprintb(s"after $name")
    dprint(cprime.serialize)
 
    cprime
  }

}
