;buildInfoPackage: chisel3, version: 3.0-SNAPSHOT, scalaVersion: 2.11.7, sbtVersion: 0.13.11, builtAtString: 2016-12-12 22:28:40.596, builtAtMillis: 1481581720596
circuit Counter : 
  module Counter : 
    input clock : Clock
    input reset : UInt<1>
    output io : {flip inc : UInt<1>, flip amt : UInt<4>, tot : UInt<8>}
    
    io is invalid
    io is invalid
    reg _T_10 : UInt<8>, clock with : (reset => (reset, UInt<8>("h00"))) @[Counter.scala 18:16]
    when io.inc : @[Counter.scala 19:15]
      node _T_11 = add(_T_10, io.amt) @[Counter.scala 19:35]
      node _T_12 = tail(_T_11, 1) @[Counter.scala 19:35]
      node _T_13 = gt(_T_12, UInt<8>("h0ff")) @[Counter.scala 10:11]
      node _T_15 = mux(_T_13, UInt<1>("h00"), _T_12) @[Counter.scala 10:8]
      _T_10 <= _T_15 @[Counter.scala 19:19]
      skip @[Counter.scala 19:15]
    io.tot <= _T_10 @[Counter.scala 34:10]
    
