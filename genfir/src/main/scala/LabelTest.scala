package solutions

import chisel3._
import chisel3.util.Decoupled

class LabelTest extends Module {
  val io = IO(new Bundle {
    val in = Input(UInt(1.W), Label(Level("L"), Level("H")))
    val out = Output(UInt(1.W), Label(Level("L"), Level("H")))
  });

 // val testSeqLbl = Module(new SeqOutLbl)
 // val output = Module(new SeqOut2)
 // io.out := output.io.out
 // val I0 = Module(new IssueDef);
  // val B1 = Module(new Issue5);
 //val B2 = Module(new Issue3);
 // val B2Good = Module(new Issue3Fix);
  //val I6 = Module(new Issue6);
  //val I62 = Module(new Issue6_Fix);
 // val ST1 = Module(new ExpectedFail);
//  val ST2 = Module(new ExpectedSuccess);
 // val ST3 = Module(new ExpectedSuccess2);
 // val ST4 = Module(new ExpectedSuccess3);
  //val ST5 = Module(new ExpectedFail2);
 // val vlt = Module(new VectorLabel);
  // val vltf = Module(new VectorLabelFail);
 // val vltn = Module(new NestedVector);
 // val fail = Module(new Fail);
 //  val stest = Module(new STest);
 // val cb = Module(new ChiselBug);
  val interr = Module(new IntError);
}

class STest extends Module {
  val io = IO(new Bundle {
    val in  = Input(UInt(1.W), Label(Level("L"), Level("H")))
    val req_conf = Input(UInt(8.W), Label(Level("L"), Level("H")))
    val req_integ = Input(UInt(8.W), Label(Level("L"), Level("H")))
    val req_lvl = Label(HLevel(req_conf), HLevel(req_integ))
    val req_data = Input(UInt(8.W), req_lvl)
  })
  val reg_conf = Reg(UInt(8.W), lbl = Label(Level("L"), Level("H")))
  val reg_integ = Reg(UInt(8.W), lbl = Label(Level("L"), Level("H")))
  val reg_lvl = Label(HLevel(reg_conf), HLevel(reg_integ))
  val reg_data = Reg(UInt(8.W), lbl = reg_lvl)

  when (io.in === 1.U) {
    reg_data := io.req_data
    reg_conf := io.req_conf
    reg_integ := io.req_integ
  }.otherwise {
    reg_data := io.req_data
  }
}

class Fail extends Module {
  val io = IO(new Bundle {
    val in_conf  = Input(UInt(4.W), Label(Level("L"), Level("H")))
    val in_integ  = Input(UInt(4.W), Label(Level("L"), Level("H")))
    val in_lvl = Label(HLevel(in_conf), HLevel(in_integ))
    val valid = Input(Bool(), in_lvl)
  })
  val confReg = Reg(UInt(4.W), lbl = Label(Level("L"), Level("H")));
  val intReg = Reg(UInt(4.W), lbl = Label(Level("L"), Level("H")));
  val lblReg = Label(HLevel(confReg), HLevel(intReg));
  val reg1 = Reg(Bool(), lbl = lblReg)
  val reg2 = Reg(Bool(), lbl = lblReg)

  reg1 := io.valid          // violation
  when(io.valid) {
    reg2 := 0.U             // violation
  }
}
class SeqOut extends Module {
  class MyBundle extends Bundle {
    val a = UInt(1.W)
    val b = UInt(1.W)
  }
  val io = IO(new Bundle {
    val out = Output(UInt(1.W), Label(Level("L"), Level("H")))
    val out2 = Output(new MyBundle, Label(Level("L"), Level("H")))
  })
  val ax = Reg(init = 0.U(1.W), lbl = Label(Level("L"), Level("H")))
  ax := ~ax
  val bx = Reg(init = 4.U(3.W), lbl = Label(Level("L"), Level("H")))
  io.out := bx(0,0)
  io.out2.a := ax
  io.out2.b := ~ax
}

class SeqOut2 extends Module {
  val io = IO(new Bundle {
    val out = Output(UInt(1.W), Label(Level("L"), Level("H")))
  })
  val a = Reg(init = 1.U(1.W), lbl = Label(Level("L"), Level("H")))
  io.out := a
}


class SeqOutLbl extends Module {
  val io = IO(new Bundle {
    val out = Output(UInt(4.W), Label(Level("L"), Level("H")))
    val v = Output(UInt(1.W), Label(Level("H"), Level("H")))
  })
  io.out := 0xf.U(4.W)
  val a = Reg(UInt(1.W), lbl = Label(HLevel(io.out), Level("H")))
  io.v := a
}
class IssueDef extends Module {
  val io = IO(new Bundle {
    val out = Output(UInt(1.W), Label(Level("L"), Level("H")))
  });
  val lvl = Reg(UInt(4.W), lbl =  Label(Level("L"), Level("H")))
  lvl := ~lvl
  val a = Reg(UInt(1.W), lbl = Label(HLevel(lvl), Level("H")));
}
class Issue6 extends Module {
  val io = IO(new Bundle {
    val out = Output(UInt(8.W), Label(Level("H"), Level("L")))
  });
  val conf = Reg(init = 0.U(4.W), lbl = Label(Level("L"), Level("H")))
  val integ = Reg(init = 0.U(4.W), lbl = Label(Level("L"), Level("H")))
  val lvl = Label(HLevel(conf), HLevel(integ))

  conf := conf;
  integ := integ;

  val a = Reg(UInt(8.W), lbl = lvl)
  val b = Reg(UInt(8.W), lbl = lvl)
  val c = Reg(UInt(8.W), lbl = lvl)

  b := a
  c := c

  io.out := c;
}

class Issue6_Fix extends Module {
  val io = IO(new Bundle {
    val req_valid = Input(UInt(1.W), Label(Level("L"), Level("H")))
    val req_conf = Input(UInt(4.W), Label(Level("L"), Level("H")))
    val req_integ = Input(UInt(4.W), Label(Level("L"), Level("H")))
    val req_lvl = Label(HLevel(req_conf), HLevel(req_integ))
    val req_data = Input(UInt(4.W), req_lvl)

    val resp_valid = Output(UInt(1.W), Label(Level("L"), Level("H")))
    val resp_conf = Output(UInt(4.W), Label(Level("L"), Level("H")))
    val resp_integ = Output(UInt(4.W), Label(Level("L"), Level("H")))
    val resp_lvl = Label(HLevel(resp_conf), HLevel(resp_integ))
    val resp_data = Output(UInt(4.W), resp_lvl)
  })

  val conf = Reg(UInt(4.W), lbl = Label(Level("L"), Level("H")))
  val integ = Reg(UInt(4.W), lbl = Label(Level("L"), Level("H")))
  val lvl = Label(HLevel(conf), HLevel(integ))

  //val conf2 = Reg(UInt(4.W), lbl = Label(Level("L"), Level("H")))
  //val integ2 = Reg(UInt(4.W), lbl = Label(Level("L"), Level("H")))
  //val lvl2 = Label(HLevel(conf2), HLevel(integ2))

  val state = Reg(UInt(8.W), lbl = Label(Level("L"), Level("H")))
  val data = Reg(UInt(8.W), lbl = lvl)
  val temp = Reg(UInt(8.W), lbl = lvl)
  // val temp = Reg(UInt(8.W), lbl = lvl2)

  when(io.req_valid === 1.U) {
    conf := io.req_conf
    integ := io.req_integ
    data := io.req_data
    state := 0.U
    temp := 0.U
  }.elsewhen(state === 0.U) {
    // conf2 := conf
    // integ2 := integ
    temp := data + 1.U
    state := 1.U
  }.elsewhen(state === 1.U) {
    temp := temp + 1.U
    state := 2.U
  }.elsewhen(state === 2.U) {
    io.resp_conf := conf
    io.resp_integ := integ
    // io.resp_conf := conf2
    // io.resp_integ := integ2
    io.resp_data := temp
  }

  io.resp_valid := (state === 2.U)
}
  class Issue5 extends Module {

    val io = IO(new Bundle {
      val in = Input(UInt(1.W), Label(Level("L"), Level("H")))
      val req_conf = Input(UInt(4.W), Label(Level("L"), Level("H")))
      val req_integ = Input(UInt(4.W), Label(Level("L"), Level("H")))
      val req_lvl = Label(HLevel(req_conf), HLevel(req_integ))
      val req_data = Input(UInt(4.W), req_lvl)
    })
    val reg_conf = Reg(UInt(4.W), lbl = Label(Level("L"), Level("H")))
    val reg_integ = Reg(UInt(4.W), lbl = Label(Level("L"), Level("H")))
    val reg_lvl = Label(HLevel(reg_conf), HLevel(reg_integ))
    val reg_data = Reg(UInt(4.W), lbl = reg_lvl)

    when(io.in === 1.U) {
      reg_data := io.req_data
      reg_conf := io.req_conf
      reg_integ := io.req_integ
    }.otherwise {
      reg_data := io.req_data
    }
  }

  class Issue3 extends Module {
    val io = IO(new Bundle {
      val ns_i = Input(UInt(4.W), Label(Level("L"), Level("L")))
      val l_i = Input(UInt(1.W), Label(Level("L"), Level("L")))
      val h_i = Input(UInt(1.W), Label(Level("H"), Level("L")))
      val h_o = Output(UInt(1.W), Label(Level("H"), Level("L")))
      val l_o = Output(UInt(1.W), Label(Level("L"), Level("L")))
    })
    val data_r = Reg(t = UInt(1.W), lbl = Label(HLevel(io.ns_i), Level("L")))
    when(io.ns_i === "hf".U) {
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

  class Issue3Fix extends Module {
    val io = IO(new Bundle {
      val ns_i = Input(UInt(4.W), Label(Level("L"), Level("L")))
      val l_i = Input(UInt(1.W), Label(Level("L"), Level("L")))
      val h_i = Input(UInt(1.W), Label(Level("H"), Level("L")))
      val h_o = Output(UInt(1.W), Label(Level("H"), Level("L")))
      val l_o = Output(UInt(1.W), Label(Level("L"), Level("L")))
    })
    val lbl_r = Reg(t = UInt(4.W), lbl = Label(Level("L"), Level("L")))
    lbl_r := io.ns_i & "hf".U;
    val data_r = Reg(t = UInt(1.W), lbl = Label(HLevel(lbl_r), Level("L")))
    when(io.ns_i === "hf".U) {
      data_r := io.h_i
    }.elsewhen(io.ns_i === 0.U) {
      data_r := io.l_i
    }.otherwise {
      data_r := 0.U();
    }
    when(lbl_r === "hf".U) {
      io.h_o := data_r
    }.elsewhen(lbl_r === 0.U) {
      io.l_o := data_r
      io.h_o := io.h_o
    }.otherwise {
      io.l_o := 0.U();
      io.h_o := 0.U();
    }
  }

  class VectorLabel extends Module {
    val io = IO(new Bundle {
      val in = Input(UInt(2.W), Label(Level("L"), Level("H")))
      val out = Output(UInt(16.W), Label(Level("L"), Level("H")))
    })
    val cl = Reg(t = Vec(4, UInt(4.W)), lbl = Label(Level("L"), Level("H")))
    val il = Reg(t = Vec(4, UInt(4.W)), lbl = Label(Level("L"), Level("H")))
    val rf = Wire(Vec(4, UInt(16.W)), Label(VLabel(cl), VLabel(il)))
    when(cl(io.in) === 0.U && il(io.in) === "hf".U) {
      io.out := rf(io.in)
    }.otherwise{
      io.out := 0.U
    }
  }

class VectorLabelFail extends Module {
  val io = IO(new Bundle {
    val in = Input(UInt(2.W), Label(Level("L"), Level("H")))
    val out = Output(UInt(16.W), Label(Level("L"), Level("H")))
  })
  val cl = Reg(t = Vec(4, UInt(4.W)), lbl = Label(Level("L"), Level("H")))
  val il = Reg(t = Vec(4, UInt(4.W)), lbl = Label(Level("L"), Level("H")))
  val rf = Wire(Vec(4, UInt(16.W)), Label(VLabel(cl), VLabel(il)))
  when(cl(io.in) === "hf".U && il(io.in) === 0.U) {
    io.out := rf(io.in)
  }.otherwise{
    io.out := 0.U
  }
}

class NestedVector extends Module {
  val io = IO(new Bundle {
    val in = Input(UInt(2.W), Label(Level("L"), Level("H")))
    val out = Output(UInt(16.W), Label(Level("L"), Level("H")))
  })
  val inC = Wire(Vec(4, UInt(4.W)), Label(Level("L"), Level("H")))
  val inI = Wire(Vec(4, UInt(4.W)), Label(Level("L"), Level("H")))
  val cl = Wire(Vec(4, UInt(4.W)), Label(VLabel(inC), VLabel(inI)))
  val il = Wire(Vec(4, UInt(4.W)), Label(VLabel(inC), VLabel(inI)))
  val rf = Reg(t = Vec(4, UInt(16.W)), lbl = Label(VLabel(cl), VLabel(il)))

  when(inC(io.in) === 0.U && cl(io.in) === 0.U
    && inI(io.in) === "hf".U && il(io.in) === "hf".U) {
    io.out := rf(io.in)
  }.otherwise{
    io.out := 0.U
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

    when(io.in_lbl === 0.U) {
      io.out := io.in;
    }.otherwise {
      io.out := 1.U;
    }
  }


class ExpectedSuccess3 extends Module {

  val io = IO(new Bundle {
    val in = Input(UInt(1.W), Label(Level("L"), Level("H")))
    val out = Output(UInt(1.W), Label(Level("H"), Level("L")))
  });
  class MyBundle extends Bundle {
    val a = UInt(1.W)
    val b = UInt(1.W)
  }
  val my_reg = Reg(new MyBundle())
  my_reg.a := io.in
  my_reg.b := my_reg.a

  io.out := my_reg.b

}

class ExpectedFail2 extends Module {
  val io = IO(new Bundle {
    val in = Input(UInt(4.W), Label(Level("L"), Level("H")))
    val out = Output(UInt(1.W), Label(Level("L"), Level("L")))
  });

  class MyBundle extends Bundle {
    val a = UInt(4.W)
    val b = UInt(4.W)
  }
  val my_reg = Reg(new MyBundle(), lbl= Label(Level("L"), Level("H")))
  my_reg.a := io.in
  my_reg.b := my_reg.a

  val reg2 = Reg(UInt(1.W), lbl= Label(HLevel(my_reg.a), Level("H")))
  reg2 := my_reg.b
  io.out := reg2

}

class ChiselBug extends Module {
    val io = IO(new Bundle {
      val msg_o = Decoupled(UInt(128.W, Label(Level("L"), Level("H"))), Label(Level("L"), Level("H")), Label(Level("L"), Level("H")))
    })
}

class IntError extends Module {
  val io = IO(new Bundle {
    val way       = Input(UInt(1.W),    Label(Level("L"), Level("L")))
    val index     = Input(UInt(8.W),    Label(Level("L"), Level("L")))
    val tag_in    = Input(UInt(19.W),   Label(Level("L"), Level("L")))
    val write_en  = Input(UInt(1.W),    Label(Level("L"), Level("L")))
    val tag_out   = Output(UInt(19.W),  Label(Level("L"), Level("L")))
  })

  val tag0 = Reg(t=Vec(256, UInt(19.W)), lbl=Label(Level("L"), Level("L")))
  val tag1 = Reg(t=Vec(256, UInt(19.W)), lbl=Label(Level("H"), Level("H")))

  when (io.write_en === 1.U) {
    when (io.way === 0.U)       { tag0(io.index) := io.tag_in }
      .otherwise                  { tag1(io.index) := io.tag_in }
  }
}

object LabelTestDriver extends App {
  chisel3.Driver.execute(args, () => new LabelTest)
}
