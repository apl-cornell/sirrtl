;buildInfoPackage: chisel3, version: 3.0-SNAPSHOT, scalaVersion: 2.11.7, sbtVersion: 0.13.11, builtAtString: 2016-12-12 22:28:40.596, builtAtMillis: 1481581720596
circuit Mux4 : 
  module Mux2 : 
    input clock : Clock
    input reset : UInt<1>
    output io : {flip sel : UInt<1>, flip in0 : UInt<1>, flip in1 : UInt<1>, out : UInt<1>}
    
    io is invalid
    io is invalid
    node _T_10 = and(io.sel, io.in1) @[Mux2.scala 13:21]
    node _T_11 = not(io.sel) @[Mux2.scala 13:34]
    node _T_12 = and(_T_11, io.in0) @[Mux2.scala 13:42]
    node _T_13 = or(_T_10, _T_12) @[Mux2.scala 13:31]
    io.out <= _T_13 @[Mux2.scala 13:10]
    
  module Mux2_1 : 
    input clock : Clock
    input reset : UInt<1>
    output io : {flip sel : UInt<1>, flip in0 : UInt<1>, flip in1 : UInt<1>, out : UInt<1>}
    
    io is invalid
    io is invalid
    node _T_10 = and(io.sel, io.in1) @[Mux2.scala 13:21]
    node _T_11 = not(io.sel) @[Mux2.scala 13:34]
    node _T_12 = and(_T_11, io.in0) @[Mux2.scala 13:42]
    node _T_13 = or(_T_10, _T_12) @[Mux2.scala 13:31]
    io.out <= _T_13 @[Mux2.scala 13:10]
    
  module Mux2_2 : 
    input clock : Clock
    input reset : UInt<1>
    output io : {flip sel : UInt<1>, flip in0 : UInt<1>, flip in1 : UInt<1>, out : UInt<1>}
    
    io is invalid
    io is invalid
    node _T_10 = and(io.sel, io.in1) @[Mux2.scala 13:21]
    node _T_11 = not(io.sel) @[Mux2.scala 13:34]
    node _T_12 = and(_T_11, io.in0) @[Mux2.scala 13:42]
    node _T_13 = or(_T_10, _T_12) @[Mux2.scala 13:31]
    io.out <= _T_13 @[Mux2.scala 13:10]
    
  module Mux4 : 
    input clock : Clock
    input reset : UInt<1>
    output io : {flip in0 : UInt<1>, flip in1 : UInt<1>, flip in2 : UInt<1>, flip in3 : UInt<1>, flip sel : UInt<2>, out : UInt<1>}
    
    io is invalid
    io is invalid
    inst m0 of Mux2 @[Mux4.scala 24:18]
    m0.io is invalid
    m0.clock <= clock
    m0.reset <= reset
    node _T_14 = bits(io.sel, 0, 0) @[Mux4.scala 25:22]
    m0.io.sel <= _T_14 @[Mux4.scala 25:13]
    m0.io.in0 <= io.in0 @[Mux4.scala 26:13]
    m0.io.in1 <= io.in1 @[Mux4.scala 27:13]
    inst m1 of Mux2_1 @[Mux4.scala 29:18]
    m1.io is invalid
    m1.clock <= clock
    m1.reset <= reset
    node _T_15 = bits(io.sel, 0, 0) @[Mux4.scala 30:22]
    m1.io.sel <= _T_15 @[Mux4.scala 30:13]
    m1.io.in0 <= io.in2 @[Mux4.scala 31:13]
    m1.io.in1 <= io.in3 @[Mux4.scala 32:13]
    inst m2 of Mux2_2 @[Mux4.scala 34:18]
    m2.io is invalid
    m2.clock <= clock
    m2.reset <= reset
    node _T_16 = bits(io.sel, 1, 1) @[Mux4.scala 35:22]
    m2.io.sel <= _T_16 @[Mux4.scala 35:13]
    m2.io.in0 <= m0.io.out @[Mux4.scala 36:13]
    m2.io.in1 <= m1.io.out @[Mux4.scala 37:13]
    io.out <= m2.io.out @[Mux4.scala 39:10]
    
