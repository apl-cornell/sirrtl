package firrtl
package ir

class HypercubePolicy extends Policy {
  
  //---------------------------------------------------------------------------
  // TODO Store configurations: (W, K, D)s, mappings from strings to 
  // bitvector constants
  //---------------------------------------------------------------------------
  def lvlwidth = 16
  def ndims = 4
  def dimwidth = 4
    
  implicit class IntWConcat(x: Int) {
      def ::[T<:Int](y: T) = (x.toString + y.toString).toInt
  }

  // TODO parse this thing from a file, exception on wrong width.
  def lvlConsts: Map[String, Int] = Map(
    "L"  -> 0x0000,
    "D1" -> 0x1000,
    "D2" -> 0x0100,
    "D3" -> 0x0010,
    "D4" -> 0x0001,
    "H"  -> 0xFFFF
  )

  //---------------------------------------------------------------------------
  // Lattice Operations
  //---------------------------------------------------------------------------
  // Note, it is assumed that L and H are always constants mapped to the top 
  // and bottom of every configuration (0 and a seq of all ones).
  def bottom = Level("L")
  def top = Level("H")

  //---------------------------------------------------------------------------
  // Z3 file preamble
  //---------------------------------------------------------------------------
  // TODO generate these from a description of the possible configurations  
  def leqFuncs: String = {
"""; leq relations for each configuration
   |(define-fun leq44 ((x (_ BitVec 16))(y (_ BitVec 16))) Bool
   |    (and (bvule ((_ extract 3 0) x)((_ extract 3 0 ) y))
   |    (and (bvule ((_ extract 7 4) x)((_ extract 7 4) y))
   |    (and (bvule ((_ extract 11 8) x)((_ extract 11 8) y))
   |    (bvule ((_ extract 15 12) x)((_ extract 15 12) y))))))
   |
   |(define-fun leq82 ((x (_ BitVec 16))(y (_ BitVec 16))) Bool
   |    (and (bvule ((_ extract 1 0) x)  ((_ extract 1 0 ) y))
   |    (and (bvule ((_ extract 3 2) x)  ((_ extract 3 2 ) y))
   |    (and (bvule ((_ extract 5 4) x)  ((_ extract 5 4 ) y))
   |    (and (bvule ((_ extract 7 6) x)  ((_ extract 7 6 ) y))
   |    (and (bvule ((_ extract 9 8) x)  ((_ extract 9 8 ) y))
   |    (and (bvule ((_ extract 11 10) x)((_ extract 11 10 ) y))
   |    (and (bvule ((_ extract 13 12) x)((_ extract 13 12 ) y))
   |         (bvule ((_ extract 15 14) x)((_ extract 15 14 ) y))))))))))
   |
   |(define-fun leq ((x (_ BitVec 16))(y (_ BitVec 16))) Bool
   |    (ite (= config #b0) (leq44 x y) (leq82 x y)))
   |""".stripMargin
  }

  def meetFuncs: String = {
 """; meet functions for each configuration
    |(define-fun meet44 ((x (_ BitVec 16)) (y (_ BitVec 16))) (_ BitVec 16)
    |    (concat (min4 ((_ extract 3 0) x) ((_ extract 3 0) y))
    |    (concat (min4 ((_ extract 7 4) x) ((_ extract 7 4) y))
    |    (concat (min4 ((_ extract 11 8) x) ((_ extract 11 8) y))
    |    (concat (min4 ((_ extract 15 12) x) ((_ extract 15 12) y)))))))
    |
    |(define-fun meet82 ((x (_ BitVec 16)) (y (_ BitVec 16))) (_ BitVec 16)
    |    (concat (min2 ((_ extract 1 0) x)  ((_ extract 1 0 ) y))
    |    (concat (min2 ((_ extract 3 2) x)  ((_ extract 3 2 ) y))
    |    (concat (min2 ((_ extract 5 4) x)  ((_ extract 5 4 ) y))
    |    (concat (min2 ((_ extract 7 6) x)  ((_ extract 7 6 ) y))
    |    (concat (min2 ((_ extract 9 8) x)  ((_ extract 9 8 ) y))
    |    (concat (min2 ((_ extract 11 10) x)((_ extract 11 10 ) y))
    |    (concat (min2 ((_ extract 13 12) x)((_ extract 13 12 ) y))
    |    (concat (min2 ((_ extract 15 14) x)((_ extract 15 14 ) y)))))))))))
    |
    |(define-fun meet ((x (_ BitVec 16))(y (_ BitVec 16))) (_ BitVec 16)
    |    (ite (= config #b0) (meet44 x y) (meet82 x y)))
    |""".stripMargin
  }

  def joinFuncs: String = {
"""; join functions for each configuration
   |(define-fun join44 ((x (_ BitVec 16)) (y (_ BitVec 16))) (_ BitVec 16)
   |     (concat (max4 ((_ extract 3 0) x) ((_ extract 3 0) y))
   |     (concat (max4 ((_ extract 7 4) x) ((_ extract 7 4) y))
   |     (concat (max4 ((_ extract 11 8) x) ((_ extract 11 8) y))
   |     (concat (max4 ((_ extract 15 12) x) ((_ extract 15 12) y)))))))
   |
   |(define-fun join82 ((x (_ BitVec 16)) (y (_ BitVec 16))) (_ BitVec 16)
   |    (concat (max2 ((_ extract 1 0) x)  ((_ extract 1 0 ) y))
   |    (concat (max2 ((_ extract 3 2) x)  ((_ extract 3 2 ) y))
   |    (concat (max2 ((_ extract 5 4) x)  ((_ extract 5 4 ) y))
   |    (concat (max2 ((_ extract 7 6) x)  ((_ extract 7 6 ) y))
   |    (concat (max2 ((_ extract 9 8) x)  ((_ extract 9 8 ) y))
   |    (concat (max2 ((_ extract 11 10) x)((_ extract 11 10 ) y))
   |    (concat (max2 ((_ extract 13 12) x)((_ extract 13 12 ) y))
   |    (concat (max2 ((_ extract 15 14) x)((_ extract 15 14 ) y)))))))))))
   |
   |(define-fun join ((x (_ BitVec 16))(y (_ BitVec 16))) (_ BitVec 16)
   |    (ite (= config #b0) (join44 x y) (join82 x y)))
   |""".stripMargin
  }

  def maxFuncs: String = {
"""; utility max functions for each config.
   |(define-fun max4 ((x (_  BitVec 4))(y (_ BitVec 4))) (_ BitVec 4)
   |   (ite (bvuge x y) x y ))
   |(define-fun max2 ((x (_  BitVec 2))(y (_ BitVec 2))) (_ BitVec 2)
   |   (ite (bvuge x y) x y ))
   |""".stripMargin
  }
  
  def minFuncs: String = {
"""; utility min functions for each config.
   |(define-fun min4 ((x (_  BitVec 4))(y (_ BitVec 4))) (_ BitVec 4)
   |   (ite (bvule x y) x y ))
   |(define-fun min2 ((x (_  BitVec 2))(y (_ BitVec 2))) (_ BitVec 2)
   |   (ite (bvule x y) x y ))
   |""".stripMargin
  }

// TODO have a way of dynamically determining the current configuration.
  def configDecl: String = {
"""; var for determining which config you are in
   |(declare-const config (_ BitVec 1))
   |; For now, hardcode that we are using 4,4
   |(assert (= config #b0))
   |""".stripMargin
  }

  def declLvlConsts : String =
    "; String literal constant levels as hypercube levels.\n" +
    (lvlConsts map { case(lvl: String, valu: Int)  =>
      s"(declare-const $lvl (_ BitVec $lvlwidth))\n" +
      s"(assert (= $lvl (_ bv$valu $lvlwidth)))\n"
    } reduceLeft {(_:String)+(_:String)}) + "\n"
  
  // Functions used for SecVerilog-style dependent types. These should be 
  // parsed from a file.
  def depTypeFuns: String = {
"""; a simple function for testing
   |(define-fun Dom ((x (_ BitVec 2))) (_ BitVec 16)
   |  (ite (= x (_ bv0 2)) L 
   |  (ite (= x (_ bv1 2)) D1
   |  (ite (= x (_ bv2 2)) D2 H))))
   |
   |""".stripMargin
  }


  def preamble: String = 
    configDecl +
    maxFuncs +
    minFuncs +
    leqFuncs +
    joinFuncs +
    meetFuncs +
    declLvlConsts +
    depTypeFuns

}
