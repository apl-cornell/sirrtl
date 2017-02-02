circuit InferImplicit:
    module InferImplicit:
        input clock : {L} Clock
        input rst: {L} UInt<1>
        output io : {flip in0 : {L} UInt<8>, flip in1 : {D1} UInt<8>, flip x : {D1} UInt<8>, flip y : {D2} UInt<8>, flip z : {L} UInt<8>, out : {H} UInt<8>, zout : {L} UInt<8>, xout : {D1} UInt<8> }

        io is invalid
        io is invalid
        reg foo : UInt<8> clock with : (reset => (rst UInt(0)))
        
        wire x : UInt<8>
        wire y : UInt<8>
        wire z: UInt<8>

        x <= io.x 
        y <= io.y 
        z <= io.z 

        wire bar : UInt<8>
        bar <= UInt(0)
        when eq(io.in0, UInt(3)):
            io.xout <= bar
        else:
            io.zout <= bar
            
        foo <= x 
        when y:
            foo <= UInt(7) 
            skip
        when eq(z, UInt(2)):
            when eq(x, UInt(2)):
                foo <= UInt(7) 
                skip
            when eq(y, UInt(2)):
                foo <= UInt(7) 
                skip
            skip
        
        io.out <= foo
