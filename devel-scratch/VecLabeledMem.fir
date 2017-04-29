circuit VecLabeledMem:
    module VecLabeledMem:
        input clock : {L, H} Clock
        input rst: {L, H} UInt<1>
        output io: {flip waddr: {L, H} UInt<2>, flip wlabel: {L, H} UInt<16>, flip raddr: {L, H} UInt<2>, flip wdata: {[[io.wlabel]]H, H} UInt<8>, rlabel: {L, H} UInt<16>, rdata: {[[io.rlabel]]H, H} UInt<8>}
        
        cmem conf_labels: {L, H} UInt<16>[4]
        read mport read_conf = conf_labels[io.raddr], clock
        write mport write_conf = conf_labels[io.waddr], clock
        
        cmem regfile: {[[conf_labels]]V, H} UInt<8>[4]
        read mport rport = regfile[io.raddr], clock
        write mport wport = regfile[io.waddr], clock
        
        io.rlabel <= read_conf
        io.rdata <= rport
        write_conf <= io.wlabel
        wport <= io.wdata
