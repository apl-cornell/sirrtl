package firrtl
import firrtl.ir._

class HypercubePolicy extends Policy {
  

  private def log2(x: Int): Int =
    scala.math.ceil(scala.math.log(x) / scala.math.log(2)).toInt

  //---------------------------------------------------------------------------
  // Hypercube configurations 
  //---------------------------------------------------------------------------
  // A hypercube config is a pair (D,K) where D is the number of dimensions and 
  // K is the number of bits per dimension. lvlwidth = k*d for all configs.
  // TODO parse these from a file rather than hardcoding it.
  def lvlwidth = 4 //16
  def cubeConfigs =
    Set[(Int,Int)](
      (2,2),
      (4,1)
      // (4,4),
      // (8,2),
      // (2,8)
    )
  val cwidth = log2(cubeConfigs.size)
    
  implicit class IntWConcat(x: Int) {
      def ::[T<:Int](y: T) = (x.toString + y.toString).toInt
  }

  // TODO parse this thing from a file, exception on wrong width.
  val lvlConsts44: Map[String, Int] = Map(
    "L"  -> 0x0000,
    "D1" -> 0x0001,
    "D2" -> 0x0010,
    "D3" -> 0x0100,
    "D4" -> 0x1000,
    "H"  -> 0xFFFF,
    // Protection rings
    // Not currently sure of the best way to encode these
    "M"  -> 0xFFFF,
    "Hyp" -> 0xEEEE,
    "S"  -> 0xDDDD
  )
  
  val lvlConsts22: Map[String, Int] = Map(
    "L"  -> 0x0,
    "D1" -> 0x1,
    "D2" -> 0x4,
    "H"  -> 0xF,
    "M"  -> 0xF
    )

  val lvlConsts = lvlConsts22

  //---------------------------------------------------------------------------
  // Lattice Operations
  //---------------------------------------------------------------------------
  // Note, it is assumed that L and H are always constants mapped to the bottom
  // and top of every configuration (0 and a seq of all ones).
  def bottom = Level("L")
  def top = Level("H")

  //---------------------------------------------------------------------------
  // Z3 file preamble
  //---------------------------------------------------------------------------
  // TODO generate these from a description of the possible configurations  
  def attacker: Label = {
    val botlbl = ProdLabel(bottom, top)
    val A = HLevel(UIntLiteral(0xA, IntWidth(lvlwidth), botlbl))
    ProdLabel(A, A)
  }

  def confLeqFuncs: String = {
    val w = lvlwidth
    val nconf = cubeConfigs.size

    // leq for a particular config
    def leq(d: Int, k: Int): String = {
      var ret = s"(define-fun leqc$d$k ((x (_ BitVec $w))(y (_ BitVec $w))) Bool\n"
      for( i <- 0 until (w-k) by k) {
        ret += s"   (and (bvule ((_ extract ${i+k-1} $i) x)((_ extract ${i+k-1} $i) y))\n"
      }
      ret += s"        (bvule ((_ extract ${w-1} ${w-k}) x)((_ extract ${w-1} ${w-k}) y))"
      ret += ")" * d + "\n\n"
      ret
    }
    var ret = ";conf leq functions for each configuration\n"

    // leq for each config
    ret += cubeConfigs map {
      case(d: Int, k: Int) => leq(d,k)
    } reduceLeft {(_:String)+(_:String)}
   
    // outer leq function that picks from among leqs for each config
    ret += s"(define-fun leqc ((x (_ BitVec $w))(y (_ BitVec $w))) Bool\n"
    val confsArr = cubeConfigs.toArray 
    for( i <- 0 until confsArr.length-1 ) {
      val d = confsArr(i)._1
      val k = confsArr(i)._2
      ret += s"    (ite (= config (_ bv$i $cwidth)) (leqc$d$k x y)\n"
    }
    val d = confsArr(confsArr.length-1)._1
    val k = confsArr(confsArr.length-1)._2
    ret += s"    (leqc$d$k x y)" + ")" * nconf  + "\n\n\n"
    ret
  }

  def integLeqFuncs: String = {
    val w = lvlwidth
    val nconf = cubeConfigs.size

    // leq for a particular config
    def leq(d: Int, k: Int): String = {
      var ret = s"(define-fun leqi$d$k ((x (_ BitVec $w))(y (_ BitVec $w))) Bool\n"
      for( i <- 0 until (w-k) by k) {
        ret += s"   (and (bvuge ((_ extract ${i+k-1} $i) x)((_ extract ${i+k-1} $i) y))\n"
      }
      ret += s"        (bvuge ((_ extract ${w-1} ${w-k}) x)((_ extract ${w-1} ${w-k}) y))"
      ret += ")" * d + "\n\n"
      ret
    }
    var ret = ";integ leq functions for each configuration\n"

    // leq for each config
    ret += cubeConfigs map {
      case(d: Int, k: Int) => leq(d,k)
    } reduceLeft {(_:String)+(_:String)}
   
    // outer leq function that picks from among leqs for each config
    ret += s"(define-fun leqi ((x (_ BitVec $w))(y (_ BitVec $w))) Bool\n"
    val confsArr = cubeConfigs.toArray 
    for( i <- 0 until confsArr.length-1 ) {
      val d = confsArr(i)._1
      val k = confsArr(i)._2
      ret += s"    (ite (= config (_ bv$i $cwidth)) (leqi$d$k x y)\n"
    }
    val d = confsArr(confsArr.length-1)._1
    val k = confsArr(confsArr.length-1)._2
    ret += s"    (leqi$d$k x y)" + ")" * nconf  + "\n\n\n"
    ret
  }

  def meetFuncs: String = {
    val w = lvlwidth
    val nconf = cubeConfigs.size

    // meet for a particular config
    def meet(d: Int, k: Int): String = {
      var ret = s"(define-fun meet$d$k ((x (_ BitVec $w))(y (_ BitVec $w))) (_ BitVec $w)"
      for( i <- Range(w, 0, -k)) {
        ret += s"\n   (concat (min$k ((_ extract ${i-1} ${i-k}) x)((_ extract ${i-1} ${i-k}) y))"
      }
      ret += ")" * (d+1) + "\n\n"
      ret
    }
    var ret = ";conf meet functions for each configuration\n"

    // meet for each config
    ret += cubeConfigs map {
      case(d: Int, k: Int) => meet(d,k)
    } reduceLeft {(_:String)+(_:String)}
   
    // outer meet function that picks from among meets for each config
    ret += s"(define-fun meet ((x (_ BitVec $w))(y (_ BitVec $w))) (_ BitVec $w)\n"
    val confsArr = cubeConfigs.toArray 
    for( i <- 0 until confsArr.length-1 ) {
      val d = confsArr(i)._1
      val k = confsArr(i)._2
      ret += s"    (ite (= config (_ bv$i $cwidth)) (meet$d$k x y)\n"
    }
    val d = confsArr(confsArr.length-1)._1
    val k = confsArr(confsArr.length-1)._2
    ret += s"    (meet$d$k x y)" + ")" * nconf  + "\n\n\n"
    ret
  }
  
  def joinFuncs: String = {
    val w = lvlwidth
    val nconf = cubeConfigs.size

    // meet for a particular config
    def join(d: Int, k: Int): String = {
      var ret = s"(define-fun join$d$k ((x (_ BitVec $w))(y (_ BitVec $w))) (_ BitVec $w)"
      for( i <- Range(w, 0, -k)) {
        ret += s"\n   (concat (max$k ((_ extract ${i-1} ${i-k}) x)((_ extract ${i-1} ${i-k}) y))"
      }
      ret += ")" * (d+1) + "\n\n"
      ret
    }
    var ret = ";join functions for each configuration\n"

    // join for each config
    ret += cubeConfigs map {
      case(d: Int, k: Int) => join(d,k)
    } reduceLeft {(_:String)+(_:String)}
   
    // outer join function that picks from among joins for each config
    ret += s"(define-fun join ((x (_ BitVec $w))(y (_ BitVec $w))) (_ BitVec $w)\n"
    val confsArr = cubeConfigs.toArray 
    for( i <- 0 until confsArr.length-1 ) {
      val d = confsArr(i)._1
      val k = confsArr(i)._2
      ret += s"    (ite (= config (_ bv$i $cwidth)) (join$d$k x y)\n"
    }
    val d = confsArr(confsArr.length-1)._1
    val k = confsArr(confsArr.length-1)._2
    ret += s"    (join$d$k x y)" + ")" * nconf  + "\n\n\n"
    ret
  }

  def maxFuncs: String = {
    var ret = "; utility max functions for each config.\n"
    cubeConfigs foreach { case (d: Int, k: Int) =>
      ret += s"(define-fun max$k ((x (_  BitVec $k))(y (_ BitVec $k))) (_ BitVec $k)\n"
      ret += "    (ite (bvuge x y) x y))\n"
    }
    ret
  }
  
  def minFuncs: String = {
    var ret = "; utility min functions for each config.\n"
    cubeConfigs foreach { case (d: Int, k: Int) =>
      ret += s"(define-fun min$k ((x (_  BitVec $k))(y (_ BitVec $k))) (_ BitVec $k)\n"
      ret += "    (ite (bvule x y) x y))\n"
    }
    ret
  }

// TODO have a way of dynamically determining the current configuration.
// For now, always use the first config.
  def configDecl: String = {
    "; var for determining which config you are in\n" +
    s"(declare-const config (_ BitVec $cwidth))\n" +
    "(assert (= config #b0))\n"
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
   |(define-fun Dom ((x (_ BitVec 2))) (_ BitVec 4)
   |  (ite (= x (_ bv0 2)) L 
   |  (ite (= x (_ bv1 2)) D1
   |  (ite (= x (_ bv2 2)) D2
   |                       H ))))
   |
   |(define-fun mpriv ((cond (_ BitVec 2)) (alt (_ BitVec 4))) (_ BitVec 4)
   |  (ite (= cond (_ bv3 2)) M alt))
   |
   |""".stripMargin
  }

  def optionDecl: String =  ""
   //"(set-option :timeout 4000)\n\n"


  def preamble: String = 
    optionDecl +
    configDecl +
    maxFuncs +
    minFuncs +
    confLeqFuncs +
    integLeqFuncs +
    joinFuncs +
    meetFuncs +
    declLvlConsts +
    depTypeFuns

}
