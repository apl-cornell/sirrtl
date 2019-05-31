;buildInfoPackage: chisel3, version: 3.0-SNAPSHOT, scalaVersion: 2.11.7, sbtVersion: 0.13.11, builtAtString: 2016-12-12 22:28:40.596, builtAtMillis: 1481581720596
circuit VendingMachine : 
  module VendingMachine : 
    input clock : Clock
    input reset : UInt<1>
    output io : {flip nickel : UInt<1>, flip dime : UInt<1>, valid : UInt<1>}
    
    io is invalid
    io is invalid
    reg state : UInt<3>, clock with : (reset => (reset, UInt<3>("h00"))) @[VendingMachine.scala 15:18]
    node _T_9 = eq(state, UInt<3>("h00")) @[VendingMachine.scala 16:15]
    when _T_9 : @[VendingMachine.scala 16:26]
      when io.nickel : @[VendingMachine.scala 17:22]
        state <= UInt<3>("h01") @[VendingMachine.scala 17:30]
        skip @[VendingMachine.scala 17:22]
      when io.dime : @[VendingMachine.scala 18:22]
        state <= UInt<3>("h02") @[VendingMachine.scala 18:30]
        skip @[VendingMachine.scala 18:22]
      skip @[VendingMachine.scala 16:26]
    node _T_10 = eq(state, UInt<3>("h01")) @[VendingMachine.scala 20:15]
    when _T_10 : @[VendingMachine.scala 20:23]
      when io.nickel : @[VendingMachine.scala 21:22]
        state <= UInt<3>("h02") @[VendingMachine.scala 21:30]
        skip @[VendingMachine.scala 21:22]
      when io.dime : @[VendingMachine.scala 22:22]
        state <= UInt<3>("h03") @[VendingMachine.scala 22:30]
        skip @[VendingMachine.scala 22:22]
      skip @[VendingMachine.scala 20:23]
    node _T_11 = eq(state, UInt<3>("h02")) @[VendingMachine.scala 24:15]
    when _T_11 : @[VendingMachine.scala 24:24]
      when io.nickel : @[VendingMachine.scala 25:22]
        state <= UInt<3>("h03") @[VendingMachine.scala 25:30]
        skip @[VendingMachine.scala 25:22]
      when io.dime : @[VendingMachine.scala 26:22]
        state <= UInt<3>("h04") @[VendingMachine.scala 26:30]
        skip @[VendingMachine.scala 26:22]
      skip @[VendingMachine.scala 24:24]
    node _T_12 = eq(state, UInt<3>("h03")) @[VendingMachine.scala 28:15]
    when _T_12 : @[VendingMachine.scala 28:24]
      when io.nickel : @[VendingMachine.scala 29:22]
        state <= UInt<3>("h04") @[VendingMachine.scala 29:30]
        skip @[VendingMachine.scala 29:22]
      when io.dime : @[VendingMachine.scala 30:22]
        state <= UInt<3>("h04") @[VendingMachine.scala 30:30]
        skip @[VendingMachine.scala 30:22]
      skip @[VendingMachine.scala 28:24]
    node _T_13 = eq(state, UInt<3>("h04")) @[VendingMachine.scala 32:15]
    when _T_13 : @[VendingMachine.scala 32:24]
      state <= UInt<3>("h00") @[VendingMachine.scala 33:11]
      skip @[VendingMachine.scala 32:24]
    node _T_14 = eq(state, UInt<3>("h04")) @[VendingMachine.scala 35:22]
    io.valid <= _T_14 @[VendingMachine.scala 35:12]
    
