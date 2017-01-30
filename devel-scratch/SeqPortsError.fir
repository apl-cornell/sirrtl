circuit SeqPortsErrors:
    module SeqPortsErrors:
       output io : {L} UInt<1>
       io <= UInt(0)

    module SeqPortsOk1:
        input clock : {L} Clock
        input rst : {L} UInt<1>
        output io : { lbl : seq {L} UInt<2>, next_lbl : {L} UInt<2> }
        io is invalid

        reg lbl_reg : {L} UInt<2> clock with : (reset => (rst UInt(0)))

        io.lbl <= lbl_reg @[allowed, lbl_reg is a reg]

    module SeqPortsOk2:
        input clock : {L} Clock
        input rst : {L} UInt<1>
        output io : { lbl : seq {L} UInt<2>, next_lbl : {L} UInt<2>, flip lbl_in : seq {L} UInt<2>, flip next_lbl_in : {L} UInt<2> }
        io is invalid

        io.lbl <= io.lbl_in @[allowed, lbl_in is a a seq input]

    module SeqPortsError1:
        input clock : {L} Clock
        input rst : {L} UInt<1>
        output io : { lbl : seq {L} UInt<2>, next_lbl : {L} UInt<2> }
        io is invalid

        wire lbl_wire : {L} UInt<8>
        lbl_wire <= UInt(0)

        io.lbl <= lbl_wire @[not allowed, lbl_wire is not a reg]

    module SeqPortsError2:
        input clock : {L} Clock
        input rst : {L} UInt<1>
        output io : { lbl : seq {L} UInt<2>, next_lbl : {L} UInt<2> }
        io is invalid

        reg lbl_reg1 : {L} UInt<2> clock with : (reset => (rst UInt(0)))
        reg lbl_reg2 : {L} UInt<2> clock with : (reset => (rst UInt(0)))

        when UInt(1):
            io.lbl <= lbl_reg1 @[not allowed, whens are comb]
        when UInt(2):
            io.lbl <= lbl_reg1 @[not allowed, whens are comb]

