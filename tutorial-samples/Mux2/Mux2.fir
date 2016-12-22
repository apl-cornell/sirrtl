;buildInfoPackage: chisel3, version: 3.0-SNAPSHOT, scalaVersion: 2.11.7, sbtVersion: 0.13.11, builtAtString: 2016-12-12 22:28:40.596, builtAtMillis: 1481581720596
circuit Mux2 : 
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
    
