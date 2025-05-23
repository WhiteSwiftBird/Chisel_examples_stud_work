import chisel3._
import _root_.circt.stage.ChiselStage


class Reg_test extends Module {
 private val aWidth = 4
  private val bWidth = 4
  private val sumWidth = aWidth + 1
  private val resWidth = sumWidth + bWidth + 1  

  val io = IO(new Bundle {
    val a = Input(UInt(aWidth.W))
    val b = Input(UInt(bWidth.W))
    val res = Output(UInt(resWidth.W))  
  })

  val sum      = io.a +& io.b
  val regb     = RegInit(0.U(4.W))
  val regsum   = RegNext(sum, init=0.U(sumWidth.W))
  val res_reg  = RegInit(0.U(resWidth.W))

  regb     := io.b
  io.res   := res_reg
  res_reg  := regsum +& regb
  

}


object Reg_test_mod extends App {

  ChiselStage.emitSystemVerilogFile(new Reg_test, 
  args = Array("--target-dir", "../generated_SV_files/Reg_test/"),
  firtoolOpts = Array("-disable-all-randomization",
                      "-strip-debug-info",
                      "--verify-each=false",
                      "-default-layer-specialization=enable"))
}
