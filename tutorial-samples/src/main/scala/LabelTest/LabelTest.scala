package solutions

import chisel3._


class LabelTest extends Module {
  val io = IO(new Bundle {
    val in = Input(UInt(1.W), Label(Level("L"), Level("H")))
    val out = Output(UInt(1.W), Label(Level("L"), Level("H")))
  });

 // val B1 = Module(new Bug1);
  val B2 = Module(new Bug2);
  val ST1 = Module(new ExpectedFail);
  val ST2 = Module(new ExpectedSuccess);
  val ST3 = Module(new ExpectedSuccess2);

}
class Bug1 extends Module {

  val io = IO(new Bundle {
    val in = Input(UInt(1.W), Label(Level("L"), Level("H")))
    val req_conf = Input(UInt(8.W), Label(Level("L"), Level("H")))
    val req_integ = Input(UInt(8.W), Label(Level("L"), Level("H")))
    val req_lvl = Label(HLevel(req_conf), HLevel(req_integ))
    val req_data = Input(UInt(8.W), req_lvl)
  })
  val reg_conf = Reg(UInt(8.W), lbl = Label(Level("L"), Level("H")))
  val reg_integ = Reg(UInt(8.W), lbl = Label(Level("L"), Level("H")))
  val reg_lvl = Label(HLevel(reg_conf), HLevel(reg_integ))
  val reg_data = Reg(UInt(8.W), lbl = reg_lvl)

  when(io.in === 1.U) {
    reg_data := io.req_data
    reg_conf := io.req_conf
    reg_integ := io.req_integ
  }.otherwise {
    reg_data := io.req_data
  }
}

class Bug2 extends Module {
  val io = IO(new Bundle {
    val ns_i    = Input(UInt(4.W), Label(Level("L"), Level("L")))
    val l_i     = Input(UInt(1.W), Label(Level("L"), Level("L")))
    val h_i     = Input(UInt(1.W), Label(Level("H"), Level("L")))
    val h_o     = Output(UInt(1.W), Label(Level("H"), Level("L")))
    val l_o     = Output(UInt(1.W), Label(Level("L"), Level("L")))
  })
  val data_r  = Reg(t = UInt(1.W), lbl = Label(HLevel(io.ns_i), Level("L")))
  when (io.ns_i === "hf".U) {
    data_r := io.h_i
    io.h_o := data_r
  }.elsewhen(io.ns_i === 0.U) {
    data_r := io.l_i
    io.l_o := data_r
    io.h_o := io.h_o
  }.otherwise {
    data_r := 0.U();
    io.l_o := 0.U();
    io.h_o := 0.U();
  }
}


class ExpectedFail extends Module {

  val io = IO(new Bundle {
    val in = Input(UInt(1.W), Label(Level("L"), Level("L")))
    val out = Output(UInt(1.W), Label(Level("H"), Level("H")))
  });

  io.out := io.in;
}

class ExpectedSuccess extends Module {

  val io = IO(new Bundle {
    val in = Input(UInt(1.W), Label(Level("L"), Level("H")))
    val out = Output(UInt(1.W), Label(Level("H"), Level("L")))
  });

  io.out := io.in;
}

class ExpectedSuccess2 extends Module {
  val io = IO(new Bundle {
    val in_lbl = Input(UInt(4.W), Label(Level("L"), Level("H")))
    val in = Input(UInt(1.W), Label(HLevel(in_lbl), Level("L")))
    val out = Output(UInt(1.W), Label(Level("L"), Level("L")))
  });

  when (io.in_lbl === 0.U) {
    io.out := io.in;
  }.otherwise {
    io.out := 1.U;
  }
}