circuit SeqPortsGenNext:
    module SeqPortsGenNext:
       output io : {L,H} UInt<1>
       io <= UInt(0)

    module SeqPortsOk1:
        input clock : {L,H} Clock
        input rst : {L,H} UInt<1>
        output io : { lbl : seq {L,H} UInt<4>, next_lbl : {L,H} UInt<4> }
        io is invalid

        reg lbl_reg : {L,H} UInt<4> clock with : (reset => (rst UInt(0)))

        io.lbl <= lbl_reg @[allowed, lbl_reg is a reg]

    module SeqPortsOk2:
        input clock : {L,H} Clock
        input rst : {L,H} UInt<1>
        output io : { lbl : seq {L,H} UInt<4>, next_lbl : {L,H} UInt<4>, flip lbl_in : seq {L,H} UInt<4>, flip next_lbl_in : {L,H} UInt<4> }
        io is invalid

        io.lbl <= io.lbl_in @[allowed, lbl_in is a a seq input]
