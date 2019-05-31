;buildInfoPackage: chisel3, version: 3.0-SNAPSHOT, scalaVersion: 2.11.7, sbtVersion: 0.13.11, builtAtString: 2016-12-12 22:28:40.596, builtAtMillis: 1481581720596
circuit LFSR16 : 
  module LFSR16 : 
    input clock : Clock
    input reset : UInt<1>
    output io : {flip inc : UInt<1>, out : UInt<16>}
    
    io is invalid
    io is invalid
    reg res : UInt<16>, clock with : (reset => (reset, UInt<16>("h01"))) @[LFSR16.scala 13:16]
    when io.inc : @[LFSR16.scala 14:17]
      node _T_7 = bits(res, 0, 0) @[LFSR16.scala 15:26]
      node _T_8 = bits(res, 2, 2) @[LFSR16.scala 15:33]
      node _T_9 = xor(_T_7, _T_8) @[LFSR16.scala 15:29]
      node _T_10 = bits(res, 3, 3) @[LFSR16.scala 15:40]
      node _T_11 = xor(_T_9, _T_10) @[LFSR16.scala 15:36]
      node _T_12 = bits(res, 5, 5) @[LFSR16.scala 15:47]
      node _T_13 = xor(_T_11, _T_12) @[LFSR16.scala 15:43]
      node _T_14 = bits(res, 15, 1) @[LFSR16.scala 15:55]
      node _T_15 = cat(_T_13, _T_14) @[Cat.scala 30:58]
      res <= _T_15 @[LFSR16.scala 16:9]
      skip @[LFSR16.scala 14:17]
    io.out <= res @[LFSR16.scala 18:10]
    
