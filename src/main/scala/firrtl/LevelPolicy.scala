package firrtl
import firrtl.ir._

class LevelPolicy extends Policy {

  //---------------------------------------------------------------------------
  // Lattice of security levels
  //---------------------------------------------------------------------------
  // TODO parse the covers relation from the firrtl source
  def levelLat = new Lattice[Level]{
    def covers: Map[Level,Set[Level]] = Map(
      Level("L") -> Set(Level("D1"),Level("D2")),
      Level("D1") -> Set(Level("H")),
      Level("D2") -> Set(Level("H")),
      Level("H") -> Set()
    )
  }

  //---------------------------------------------------------------------------
  // Lattice operations
  //---------------------------------------------------------------------------
  def top = levelLat.top
  def bottom = levelLat.bottom
    
  //---------------------------------------------------------------------------
  // Z3 file preamble
  //---------------------------------------------------------------------------
  // Axioms defining lattices in general
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

  // Functions used for SecVerilog-style dependent types. These should be 
  // parsed from a file.
  def depTypeFuns: String = {
   """; a simple function for testing
      |(define-fun Dom ((x (_ BitVec 2))) Label
      |  (ite (= x (_ bv0 2)) L 
      |  (ite (= x (_ bv1 2)) D1
      |  (ite (= x (_ bv2 2)) D2 H))))
      |
      |""".stripMargin
  }

  // Declare the levels in the lattice
  def declareLevels: String = {
    "; lattice elements\n" +
    levelLat.levels.map{ level =>
      s"(declare-const $level Label)\n"
    }.fold(""){_+_} + "\n"
  }

  // Declare the ordering on the levels
  def declareOrder: String = {
    "; lattice order\n" +
    levelLat.levels.map{ level =>
      (for( coveringLevel <- levelLat.covers(level) )
        yield s"(assert (leq $level $coveringLevel))\n").fold(""){_+_}
    }.fold(""){_+_} +
    s"(assert (not (= $top $bottom)))\n\n"
  }

  def preamble: String = 
    latticeAxioms +
    declareLevels +
    declareOrder +
    depTypeFuns

}
