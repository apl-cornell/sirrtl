circuit HyperLitImplicitFlow :
    module HyperLitImplicitFlow :
        input clock : {[[UInt(0)]]} Clock
        input rst: {[[UInt(0)]]} UInt<1>
        output io : {flip in0 : {[[UInt(0)]]} UInt<8>, flip in1 : {[[UInt("h0001")]]} UInt<8>, out : {[[UInt("hFFFF")]]} UInt<8>}

        io is invalid
        io is invalid
        reg foo  : {[[UInt(0)]]} UInt<8> clock with : (reset => (rst UInt(0)))
        
        wire x : {[[UInt("h0001")]]} UInt<8>
        wire y : {[[UInt("h0010")]]} UInt<8>
        wire z:  {[[UInt("h0000")]]} UInt<8>

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
