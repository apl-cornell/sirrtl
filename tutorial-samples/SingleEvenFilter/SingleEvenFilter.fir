;buildInfoPackage: chisel3, version: 3.0-SNAPSHOT, scalaVersion: 2.11.7, sbtVersion: 0.13.11, builtAtString: 2016-12-12 22:28:40.596, builtAtMillis: 1481581720596
circuit SingleEvenFilter : 
  module PredicateFilter : 
    input clock : Clock
    input reset : UInt<1>
    output io : {flip in : {valid : UInt<1>, bits : UInt<16>}, out : {valid : UInt<1>, bits : UInt<16>}}
    
    io is invalid
    io is invalid
    node _T_23 = leq(io.in.bits, UInt<4>("h09")) @[SingleEvenFilter.scala 21:51]
    node _T_24 = and(io.in.valid, _T_23) @[SingleEvenFilter.scala 15:31]
    io.out.valid <= _T_24 @[SingleEvenFilter.scala 15:16]
    io.out.bits <= io.in.bits @[SingleEvenFilter.scala 16:16]
    
  module PredicateFilter_1 : 
    input clock : Clock
    input reset : UInt<1>
    output io : {flip in : {valid : UInt<1>, bits : UInt<16>}, out : {valid : UInt<1>, bits : UInt<16>}}
    
    io is invalid
    io is invalid
    node _T_22 = bits(io.in.bits, 0, 0) @[SingleEvenFilter.scala 26:50]
    node _T_23 = bits(_T_22, 0, 0) @[SingleEvenFilter.scala 26:54]
    node _T_24 = and(io.in.valid, _T_23) @[SingleEvenFilter.scala 15:31]
    io.out.valid <= _T_24 @[SingleEvenFilter.scala 15:16]
    io.out.bits <= io.in.bits @[SingleEvenFilter.scala 16:16]
    
  module SingleEvenFilter : 
    input clock : Clock
    input reset : UInt<1>
    output io : {flip in : {valid : UInt<1>, bits : UInt<16>}, out : {valid : UInt<1>, bits : UInt<16>}}
    
    io is invalid
    io is invalid
    inst single of PredicateFilter @[SingleEvenFilter.scala 21:11]
    single.io is invalid
    single.clock <= clock
    single.reset <= reset
    inst even of PredicateFilter_1 @[SingleEvenFilter.scala 26:11]
    even.io is invalid
    even.clock <= clock
    even.reset <= reset
    single.io.in.bits <= io.in.bits @[SingleEvenFilter.scala 32:17]
    single.io.in.valid <= io.in.valid @[SingleEvenFilter.scala 32:17]
    even.io.in.bits <= single.io.out.bits @[SingleEvenFilter.scala 33:17]
    even.io.in.valid <= single.io.out.valid @[SingleEvenFilter.scala 33:17]
    io.out.bits <= even.io.out.bits @[SingleEvenFilter.scala 34:17]
    io.out.valid <= even.io.out.valid @[SingleEvenFilter.scala 34:17]
    
