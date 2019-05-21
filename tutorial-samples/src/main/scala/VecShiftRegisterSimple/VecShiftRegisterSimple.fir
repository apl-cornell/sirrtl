;buildInfoPackage: chisel3, version: 3.0-SNAPSHOT, scalaVersion: 2.11.7, sbtVersion: 0.13.11, builtAtString: 2016-12-12 22:28:40.596, builtAtMillis: 1481581720596
circuit VecShiftRegisterSimple : 
  module VecShiftRegisterSimple : 
    input clock : Clock
    input reset : UInt<1>
    output io : {flip in : UInt<8>, out : UInt<8>}
    
    io is invalid
    io is invalid
    wire _T_13 : UInt<8>[4] @[VecShiftRegisterSimple.scala 13:30]
    _T_13 is invalid @[VecShiftRegisterSimple.scala 13:30]
    _T_13[0] <= UInt<8>("h00") @[VecShiftRegisterSimple.scala 13:30]
    _T_13[1] <= UInt<8>("h00") @[VecShiftRegisterSimple.scala 13:30]
    _T_13[2] <= UInt<8>("h00") @[VecShiftRegisterSimple.scala 13:30]
    _T_13[3] <= UInt<8>("h00") @[VecShiftRegisterSimple.scala 13:30]
    reg delays : UInt<8>[4], clock with : (reset => (reset, _T_13)) @[VecShiftRegisterSimple.scala 13:19]
    delays[0] <= io.in @[VecShiftRegisterSimple.scala 15:13]
    delays[1] <= delays[0] @[VecShiftRegisterSimple.scala 16:13]
    delays[2] <= delays[1] @[VecShiftRegisterSimple.scala 17:13]
    delays[3] <= delays[2] @[VecShiftRegisterSimple.scala 18:13]
    io.out <= delays[3] @[VecShiftRegisterSimple.scala 19:13]
    
