;buildInfoPackage: chisel3, version: 3.0-SNAPSHOT, scalaVersion: 2.11.7, sbtVersion: 0.13.11, builtAtString: 2016-12-12 22:28:40.596, builtAtMillis: 1481581720596
circuit VecShiftRegister : 
  module VecShiftRegister : 
    input clock : Clock
    input reset : UInt<1>
    output io : {flip ins : UInt<4>[4], flip load : UInt<1>, flip shift : UInt<1>, out : UInt<4>}
    
    io is invalid
    io is invalid
    reg delays : UInt[4], clock @[VecShiftRegister.scala 13:19]
    when io.load : @[VecShiftRegister.scala 14:18]
      delays[0] <= io.ins[0] @[VecShiftRegister.scala 15:15]
      delays[1] <= io.ins[1] @[VecShiftRegister.scala 16:15]
      delays[2] <= io.ins[2] @[VecShiftRegister.scala 17:15]
      delays[3] <= io.ins[3] @[VecShiftRegister.scala 18:15]
      skip @[VecShiftRegister.scala 14:18]
    node _T_18 = eq(io.load, UInt<1>("h00")) @[VecShiftRegister.scala 14:18]
    node _T_19 = and(_T_18, io.shift) @[VecShiftRegister.scala 19:25]
    when _T_19 : @[VecShiftRegister.scala 19:25]
      delays[0] <= io.ins[0] @[VecShiftRegister.scala 20:15]
      delays[1] <= delays[0] @[VecShiftRegister.scala 21:15]
      delays[2] <= delays[1] @[VecShiftRegister.scala 22:15]
      delays[3] <= delays[2] @[VecShiftRegister.scala 23:15]
      skip @[VecShiftRegister.scala 19:25]
    io.out <= delays[3] @[VecShiftRegister.scala 25:10]
    
