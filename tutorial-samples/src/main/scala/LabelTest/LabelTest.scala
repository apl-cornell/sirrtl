package solutions

import chisel3._

class LabelTest extends Module {

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