package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import collection.mutable.Set

object DeterminePC extends Pass with PassDebug {
  def name    = "DeterminePC"
  override def debugThisPass = true
  
  def bot = ProdLabel(PolicyHolder.bottom, PolicyHolder.top)

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
    JoinLabel( Seq(bot, bot) ++ (exprs map { _.lbl }) :_* )
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

  // Only DefNode values are elevated eagerly since nodes are immutable.
  def elevate_e(predStack: PredStack)(e: Expression): Expression = 
    e match {
      case ex: Declassify => ex
      case ex: Endorse => ex
      case ex => ex mapLabel { _ join pcLabel(predStack) }
    }

  def determine_pc_s(predEnv: PredEnv)(s: Statement): Statement = s match {
    case sx: Block =>
      val assigned = assignedIn(sx)
      predEnv.pushContext(assigned)
      val sxx = sx copy (stmts = sx.stmts.reverse map determine_pc_s(predEnv))
      predEnv.popContext(assigned)
      sxx copy (stmts = sxx.stmts.reverse)
    case Conditionally(info, pred, conseq, alt) =>
      predEnv.appendContext(assignedIn(s), pred)
      // TODO PC value?? Not sure if there can be a single value...
      val sx = ConditionallyPC(info, pred, conseq, alt, bot)
      sx map determine_pc_s(predEnv)
    case DefNode(info, name, value) =>
      DefNodePC(info, name, value, pcLabel(predEnv(name))) map
        elevate_e(predEnv(name))
    case Connect(info, loc, expr) =>
      ConnectPC(info, loc, expr, pcLabel(predEnv(loc.serialize)))
    case PartialConnect(info, loc, expr) =>
      PartialConnectPC(info, loc, expr, pcLabel(predEnv(loc.serialize)))
    case sx => 
      sx map determine_pc_s(predEnv)
  }

  def determine_pc(m: DefModule): DefModule = {
    val predEnv = new PredEnv
    m map determine_pc_s(predEnv)
  }

  def run(c: Circuit) = {
    bannerprintb(name)
    dprint(c.serialize)
    
    val cprime = c copy (modules = c.modules map determine_pc)

    bannerprintb(s"after $name")
    dprint(cprime.serialize)

    cprime
  }

}
