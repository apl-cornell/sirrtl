;buildInfoPackage: chisel3, version: 3.0-SNAPSHOT, scalaVersion: 2.11.7, sbtVersion: 0.13.11, builtAtString: 2016-12-12 22:28:40.596, builtAtMillis: 1481581720596
circuit MaxN : 
  module MaxN : 
    input clock : Clock
    input reset : UInt<1>
    output io : {flip ins : UInt<16>[8], out : UInt<16>}
    
    io is invalid
    io is invalid
    node _T_9 = gt(io.ins[0], io.ins[1]) @[MaxN.scala 8:46]
    node _T_10 = mux(_T_9, io.ins[0], io.ins[1]) @[MaxN.scala 8:43]
    node _T_11 = gt(_T_10, io.ins[2]) @[MaxN.scala 8:46]
    node _T_12 = mux(_T_11, _T_10, io.ins[2]) @[MaxN.scala 8:43]
    node _T_13 = gt(_T_12, io.ins[3]) @[MaxN.scala 8:46]
    node _T_14 = mux(_T_13, _T_12, io.ins[3]) @[MaxN.scala 8:43]
    node _T_15 = gt(_T_14, io.ins[4]) @[MaxN.scala 8:46]
    node _T_16 = mux(_T_15, _T_14, io.ins[4]) @[MaxN.scala 8:43]
    node _T_17 = gt(_T_16, io.ins[5]) @[MaxN.scala 8:46]
    node _T_18 = mux(_T_17, _T_16, io.ins[5]) @[MaxN.scala 8:43]
    node _T_19 = gt(_T_18, io.ins[6]) @[MaxN.scala 8:46]
    node _T_20 = mux(_T_19, _T_18, io.ins[6]) @[MaxN.scala 8:43]
    node _T_21 = gt(_T_20, io.ins[7]) @[MaxN.scala 8:46]
    node _T_22 = mux(_T_21, _T_20, io.ins[7]) @[MaxN.scala 8:43]
    io.out <= _T_22 @[MaxN.scala 14:10]
    
