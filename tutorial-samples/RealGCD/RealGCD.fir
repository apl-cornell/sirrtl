;buildInfoPackage: chisel3, version: 3.0-SNAPSHOT, scalaVersion: 2.11.7, sbtVersion: 0.13.11, builtAtString: 2016-12-12 22:28:40.596, builtAtMillis: 1481581720596
circuit RealGCD : 
  module RealGCD : 
    input clock : Clock
    input reset : UInt<1>
    output io : {flip in : {flip ready : UInt<1>, valid : UInt<1>, bits : {a : UInt<16>, b : UInt<16>}}, out : {valid : UInt<1>, bits : UInt<16>}}
    
    io is invalid
    io is invalid
    reg x : UInt, clock @[RealGCD.scala 18:14]
    reg y : UInt, clock @[RealGCD.scala 19:14]
    reg p : UInt<1>, clock with : (reset => (reset, UInt<1>("h00"))) @[RealGCD.scala 20:14]
    node _T_42 = eq(p, UInt<1>("h00")) @[RealGCD.scala 22:18]
    io.in.ready <= _T_42 @[RealGCD.scala 22:15]
    node _T_44 = eq(p, UInt<1>("h00")) @[RealGCD.scala 24:24]
    node _T_45 = and(io.in.valid, _T_44) @[RealGCD.scala 24:21]
    when _T_45 : @[RealGCD.scala 24:28]
      x <= io.in.bits.a @[RealGCD.scala 25:7]
      y <= io.in.bits.b @[RealGCD.scala 26:7]
      p <= UInt<1>("h01") @[RealGCD.scala 27:7]
      skip @[RealGCD.scala 24:28]
    when p : @[RealGCD.scala 30:12]
      node _T_47 = gt(x, y) @[RealGCD.scala 31:13]
      when _T_47 : @[RealGCD.scala 31:19]
        x <= y @[RealGCD.scala 31:23]
        y <= x @[RealGCD.scala 31:31]
        skip @[RealGCD.scala 31:19]
      node _T_49 = eq(_T_47, UInt<1>("h00")) @[RealGCD.scala 31:19]
      when _T_49 : @[RealGCD.scala 32:19]
        node _T_50 = sub(y, x) @[RealGCD.scala 32:28]
        node _T_51 = tail(_T_50, 1) @[RealGCD.scala 32:28]
        y <= _T_51 @[RealGCD.scala 32:23]
        skip @[RealGCD.scala 32:19]
      skip @[RealGCD.scala 30:12]
    io.out.bits <= x @[RealGCD.scala 35:16]
    node _T_53 = eq(y, UInt<1>("h00")) @[RealGCD.scala 36:21]
    node _T_54 = and(_T_53, p) @[RealGCD.scala 36:29]
    io.out.valid <= _T_54 @[RealGCD.scala 36:16]
    when io.out.valid : @[RealGCD.scala 37:23]
      p <= UInt<1>("h00") @[RealGCD.scala 38:7]
      skip @[RealGCD.scala 37:23]
    
