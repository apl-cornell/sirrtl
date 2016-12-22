;buildInfoPackage: chisel3, version: 3.0-SNAPSHOT, scalaVersion: 2.11.7, sbtVersion: 0.13.11, builtAtString: 2016-12-12 22:28:40.596, builtAtMillis: 1481581720596
circuit Memo : 
  module Memo : 
    input clock : Clock
    input reset : UInt<1>
    output io : {flip wen : UInt<1>, flip wrAddr : UInt<8>, flip wrData : UInt<8>, flip ren : UInt<1>, flip rdAddr : UInt<8>, rdData : UInt<8>}
    
    io is invalid
    io is invalid
    cmem mem : UInt<8>[256] @[Memo.scala 16:16]
    when io.wen : @[Memo.scala 25:17]
      infer mport _T_16 = mem[io.wrAddr], clock
      _T_16 <= io.wrData @[Memo.scala 25:34]
      skip @[Memo.scala 25:17]
    io.rdData <= UInt<1>("h00") @[Memo.scala 28:13]
    when io.ren : @[Memo.scala 29:17]
      infer mport _T_18 = mem[io.rdAddr], clock
      io.rdData <= _T_18 @[Memo.scala 29:29]
      skip @[Memo.scala 29:17]
    
