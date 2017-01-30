package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import collection.mutable.Set

object ImplicitFlowElevation extends Pass with PassDebug {
  def name    = "ImplicitFlowElevation"
  override def debugThisPass = false
  
  def bot = PolicyHolder.policy.bottom

  type PredStack = collection.mutable.Stack[Seq[Expression]]

  // This is a mapping from locations (names of objects which can be connected 
  // to) to a stack of expression sequences. The stack a location is mapped to 
  // contains all expressions which may indirectly affect the value of the 
  // location through implcit flows.
  class PredEnv extends collection.mutable.HashMap[String,PredStack] {
    // by overriding this method, if there is no entry for the key, this hash 
    // will return an empty stack of predicates when the key is accessed from 
    // this hash rather than throwing an exception
    override def default(key:String) = new PredStack

    def pushContext(vars: Set[String]) {
      vars.foreach { v => this(v) = this(v).push(Seq[Expression]()) }
    }

    // The explicit check that this contains v avoids creating a new entry for 
    // v if one did not exist
    def popContext(vars: Set[String]) {
      vars.foreach { v => if(this.contains(v)) this(v).pop }
    }

    def appendContext(vars: Set[String], e: Expression) {
      vars.foreach{ v => 
        this(v) = this(v).push(this(v).pop ++ Seq(e))
      }
    }

  }

  // Compute the join over the elements in the predicate stack
  def pcLabel(predStack: PredStack) = {
    val exprs :Seq[Expression] = predStack.toSeq.flatten
    JoinLabel( Seq(bot,bot) ++ (exprs map { _.lbl }) :_* )
  }

  // Return a set containing all the variables assigned (recursively) in this 
  // statement
  def assignedIn(s: Statement) : Set[String] = {
    val vars = Set[String]()
    def assigned_rec(s: Statement) : Statement = s map assigned_rec match {
      case sx : DefNode => vars += sx.name; sx
      case sx : Connect => vars += sx.loc.serialize; sx
      case sx : PartialConnect =>  vars += sx.loc.serialize; sx
      case sx => sx
    }
    assigned_rec(s)
    vars
  }

  def elevate_e(predStack: PredStack)(e: Expression): Expression = 
    e mapLabel { _ join pcLabel(predStack) }

  def elevate_s(predEnv: PredEnv)(s: Statement): Statement = {

    s match {
      case sx: Block =>
        val assigned = assignedIn(sx)
        predEnv.pushContext(assigned)
        val sxx = sx copy (stmts = sx.stmts.reverse map elevate_s(predEnv))
        predEnv.popContext(assigned)
        sxx copy (stmts = sxx.stmts.reverse)
      case sx: Conditionally =>
        predEnv.appendContext(assignedIn(sx), sx.pred)
        sx map elevate_s(predEnv)
      case sx: DefNode =>
        sx map elevate_e(predEnv(sx.name))
      case sx: Connect =>
        sx copy( expr = elevate_e(predEnv(sx.loc.serialize))(sx.expr))
      case sx: PartialConnect =>
        sx copy( expr = elevate_e(predEnv(sx.loc.serialize))(sx.expr))
      case sx => 
        sx map elevate_s(predEnv)
    }
  }

  def elevate(m: DefModule): DefModule = {
    val predEnv = new PredEnv
    m map elevate_s(predEnv)
  }

  def run(c: Circuit) = {
    bannerprintb(name)
    dprint(c.serialize)
    
    val cprime = c copy (modules = c.modules map elevate)

    bannerprintb(s"after $name")
    dprint(cprime.serialize)

    cprime
  }

}
