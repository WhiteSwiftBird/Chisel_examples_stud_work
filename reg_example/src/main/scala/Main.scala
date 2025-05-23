import chisel3._



class Reg_test extends Module {
  val io = IO(new Bundle {
    val a = Input (UInt(4.W))
    val b = Input (UInt(4.W))
    val res = Output (UInt(resWidth.W))
  })
  private val sumWidth = io.a.getWidth + 1
  private val resWidth = sumWidth + io.b.getWidth + 1

  val sum      = io.a +& io.b
  val regb     = RegInit(0.U(4.W))
  val regsum   = RegNext(sum, init=0.U(sumWidth.W))
  val res_reg  = RegInit(0.U(resWidth.W))

  regb     := io.b
  io.res   := res_reg
  res_reg  := regsum +& regb
}

object Reg_test_mod extends App {
  emitVerilog(new Reg_test, 
    Array("--target-dir", "../generated_SV_files/mux4_2/"))
}
