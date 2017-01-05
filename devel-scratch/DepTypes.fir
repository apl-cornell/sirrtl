circuit DepTypes :
    module DepTypes:
        input clock : {L} Clock
        input rst: {L} UInt<1>
        output io : {flip in : {L} UInt<2>, out : {H} UInt<8>}

        io is invalid
        io is invalid
        reg foo  : {Dom tmp} UInt<8> clock with : (reset => (rst UInt(0)))

        ; Because syntax of fun labels is {id id} not {id exp}
        node tmp = io.in
        
        wire x : {D1} UInt<8>
        wire y : {D2} UInt<8>

        x <= tmp
        y <= UInt(5) 

        foo <= x
        when eq(io.in, UInt(1)):
            foo <= x
        when eq(io.in, UInt(2)):
            foo <= y
            
        io.out <= foo
