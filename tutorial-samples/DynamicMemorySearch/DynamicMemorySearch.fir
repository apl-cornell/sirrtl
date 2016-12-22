;buildInfoPackage: chisel3, version: 3.0-SNAPSHOT, scalaVersion: 2.11.7, sbtVersion: 0.13.11, builtAtString: 2016-12-12 22:28:40.596, builtAtMillis: 1481581720596
circuit DynamicMemorySearch : 
  module DynamicMemorySearch : 
    input clock : Clock
    input reset : UInt<1>
    output io : {flip isWr : UInt<1>, flip wrAddr : UInt<3>, flip data : UInt<4>, flip en : UInt<1>, target : UInt<3>, done : UInt<1>}
    
    io is invalid
    io is invalid
    reg index : UInt<3>, clock with : (reset => (reset, UInt<3>("h00"))) @[DynamicMemorySearch.scala 16:19]
    cmem list : UInt<4>[8] @[DynamicMemorySearch.scala 17:19]
    infer mport memVal = list[index], clock
    node _T_18 = eq(io.en, UInt<1>("h00")) @[DynamicMemorySearch.scala 19:16]
    node _T_19 = eq(memVal, io.data) @[DynamicMemorySearch.scala 19:35]
    node _T_21 = eq(index, UInt<3>("h07")) @[DynamicMemorySearch.scala 19:58]
    node _T_22 = or(_T_19, _T_21) @[DynamicMemorySearch.scala 19:48]
    node over = and(_T_18, _T_22) @[DynamicMemorySearch.scala 19:23]
    when io.isWr : @[DynamicMemorySearch.scala 20:18]
      infer mport _T_23 = list[io.wrAddr], clock
      _T_23 <= io.data @[DynamicMemorySearch.scala 21:21]
      skip @[DynamicMemorySearch.scala 20:18]
    node _T_25 = eq(io.isWr, UInt<1>("h00")) @[DynamicMemorySearch.scala 20:18]
    node _T_26 = and(_T_25, io.en) @[DynamicMemorySearch.scala 22:23]
    when _T_26 : @[DynamicMemorySearch.scala 22:23]
      index <= UInt<1>("h00") @[DynamicMemorySearch.scala 23:11]
      skip @[DynamicMemorySearch.scala 22:23]
    node _T_29 = eq(over, UInt<1>("h00")) @[DynamicMemorySearch.scala 24:21]
    node _T_31 = eq(io.isWr, UInt<1>("h00")) @[DynamicMemorySearch.scala 20:18]
    node _T_33 = eq(io.en, UInt<1>("h00")) @[DynamicMemorySearch.scala 22:23]
    node _T_34 = and(_T_31, _T_33) @[DynamicMemorySearch.scala 22:23]
    node _T_35 = and(_T_34, _T_29) @[DynamicMemorySearch.scala 24:34]
    when _T_35 : @[DynamicMemorySearch.scala 24:34]
      node _T_37 = add(index, UInt<1>("h01")) @[DynamicMemorySearch.scala 25:20]
      node _T_38 = tail(_T_37, 1) @[DynamicMemorySearch.scala 25:20]
      index <= _T_38 @[DynamicMemorySearch.scala 25:11]
      skip @[DynamicMemorySearch.scala 24:34]
    io.done <= over @[DynamicMemorySearch.scala 27:13]
    io.target <= index @[DynamicMemorySearch.scala 28:13]
    
