circuit Mems :
    module Mems: 
        input clock : {L, H} Clock
        input rst: {L, H} UInt<1>
        output io: {flip waddr: {L, H} UInt<2>, flip raddr: {L, H} UInt<2>, flip wdata: {L, H} UInt<8>, rdata: {L, H} UInt<8>}

        cmem regfile : {D1, D1} UInt<8>[4]
        read mport rport = regfile[io.raddr], clock
        write mport wport = regfile[io.waddr], clock

        io.rdata <= rport
        wport <= io.wdata

    module LabeledMem:
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


    module MemsSeq: 
        input clock : {L, H} Clock
        input rst: {L, H} UInt<1>
        output io: {flip wdata: {L, H} UInt<8>, rdata: {L, H} UInt<8>}

        smem regfile : {D1, D1} UInt<8>[1]
        read mport rport = regfile[UInt(0)], clock
        write mport wport = regfile[UInt(0)], clock

        io.rdata <= rport
        wport <= io.wdata

    module Mems2W: 
        input clock : {L, H} Clock
        input rst: {L, H} UInt<1>
        output io: {flip waddr1: {L, H} UInt<2>, flip waddr2: {L, H} UInt<2>, flip raddr: {L, H} UInt<2>, flip wdata1: {L, H} UInt<8>, flip wdata2: {L, H} UInt<8>, rdata: {L, H} UInt<8>}

        cmem regfile : {D1, D1} UInt<8>[4]
        read mport rport = regfile[io.raddr], clock
        write mport wport1 = regfile[io.waddr1], clock
        write mport wport2 = regfile[io.waddr2], clock

        io.rdata <= rport
        wport1 <= io.wdata2
        wport2 <= io.wdata2
