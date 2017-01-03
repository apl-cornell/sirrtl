circuit ImplicitFlow :
    module ImplicitFlow :
        input clock : {L} Clock
        input rst: {L} UInt<1>
        output io : {flip in0 : {L} UInt<8>, flip in1 : {D1} UInt<8>, out : {H} UInt<8>}

        io is invalid
        io is invalid
        reg foo  : {L} UInt<8> clock with : (reset => (rst UInt(0)))
        
        wire x : {D1} UInt<8>
        wire y : {D2} UInt<8>
        wire z: {L} UInt<8>

        x <= io.in0 @[rhs -> L]
        y <= io.in0 @[rhs -> L]
        z <= io.in0 @[rhs -> L]
            
        foo <= x @[rhs -> H]
        when eq(y, UInt(3)):
            foo <= UInt(7) @[rhs -> D2]
            skip
        when eq(z, UInt(2)):
            when eq(x, UInt(2)):
                foo <= UInt(7) @[rhs -> H]
                skip
            when eq(y, UInt(2)):
                foo <= UInt(7) @[rhs -> D2]
                skip
            skip
        
        io.out <= foo
