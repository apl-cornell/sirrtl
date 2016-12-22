;buildInfoPackage: chisel3, version: 3.0-SNAPSHOT, scalaVersion: 2.11.7, sbtVersion: 0.13.11, builtAtString: 2016-12-12 22:28:40.596, builtAtMillis: 1481581720596
circuit VecShiftRegisterParam : 
  module VecShiftRegisterParam : 
    input clock : Clock
    input reset : UInt<1>
    output io : {flip in : UInt<4>, out : UInt<4>}
    
    io is invalid
    io is invalid
    wire _T_17 : UInt<8>[8] @[VecShiftRegisterParam.scala 13:30]
    _T_17 is invalid @[VecShiftRegisterParam.scala 13:30]
    _T_17[0] <= UInt<8>("h00") @[VecShiftRegisterParam.scala 13:30]
    _T_17[1] <= UInt<8>("h00") @[VecShiftRegisterParam.scala 13:30]
    _T_17[2] <= UInt<8>("h00") @[VecShiftRegisterParam.scala 13:30]
    _T_17[3] <= UInt<8>("h00") @[VecShiftRegisterParam.scala 13:30]
    _T_17[4] <= UInt<8>("h00") @[VecShiftRegisterParam.scala 13:30]
    _T_17[5] <= UInt<8>("h00") @[VecShiftRegisterParam.scala 13:30]
    _T_17[6] <= UInt<8>("h00") @[VecShiftRegisterParam.scala 13:30]
    _T_17[7] <= UInt<8>("h00") @[VecShiftRegisterParam.scala 13:30]
    reg delays : UInt<8>[8], clock with : (reset => (reset, _T_17)) @[VecShiftRegisterParam.scala 13:19]
    delays[7] <= delays[6] @[VecShiftRegisterParam.scala 16:15]
    delays[6] <= delays[5] @[VecShiftRegisterParam.scala 16:15]
    delays[5] <= delays[4] @[VecShiftRegisterParam.scala 16:15]
    delays[4] <= delays[3] @[VecShiftRegisterParam.scala 16:15]
    delays[3] <= delays[2] @[VecShiftRegisterParam.scala 16:15]
    delays[2] <= delays[1] @[VecShiftRegisterParam.scala 16:15]
    delays[1] <= delays[0] @[VecShiftRegisterParam.scala 16:15]
    delays[0] <= io.in @[VecShiftRegisterParam.scala 19:13]
    io.out <= delays[7] @[VecShiftRegisterParam.scala 20:10]
    
