circuit ImplicitFlow :
    module ImplicitFlow :
        input clock : {L,L} Clock
        input rst: {L,L} UInt<1>
        output io : {flip in0 : {L,L} UInt<8>, flip in1 : {D1,L} UInt<8>, out : {H,L} UInt<8>}

        io is invalid
        io is invalid
        reg foo  : {L,L} UInt<8> clock with : (reset => (rst UInt(0)))
        
        wire x : {D1,L} UInt<8>
        wire y : {D2,L} UInt<8>
        wire z: {L,L} UInt<8>

        x <= io.in0 @[rhs -> L]
        y <= io.in0 @[rhs -> L]
        z <= io.in0 @[rhs -> L]
            
        foo <= x @[rhs -> H]
        when y:
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
