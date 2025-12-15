import chisel3._
import _root_.circt.stage.ChiselStage


class ALU_top extends RawModule with SCR1Config {
  
  // Вспомогательные методы для ширины
  def XLEN_W: chisel3.Width = SCR1_XLEN.W
  def XLEN_UINT: UInt = UInt(SCR1_XLEN.W)
  def XLEN_SINT: SInt = SInt(SCR1_XLEN.W)
  
  // RVM extension порты (только если включено)
    val (clk, rst_n, exu2ialu_rvm_cmd_vd_i, ialu2exu_rvm_res_rdy_o) = if (SCR1_RVM_EXT) {
    val clk = IO(Input(Clock())).suggestName("clk")
    val rst_n = IO(Input(Bool())).suggestName("rst_n")
    val exu2ialu_rvm_cmd_vd_i = IO(Input(Bool())).suggestName("exu2ialu_rvm_cmd_vd_i")
    val ialu2exu_rvm_res_rdy_o = IO(Output(Bool())).suggestName("ialu2exu_rvm_res_rdy_o")
    (Some(clk), Some(rst_n), Some(exu2ialu_rvm_cmd_vd_i), Some(ialu2exu_rvm_res_rdy_o))
  } else {
    (None, None, None, None)
  }
  // Main adder порты
  val exu2ialu_main_op1_i = IO(Input(XLEN_SINT)).suggestName("exu2ialu_main_op1_i")
  val exu2ialu_main_op2_i = IO(Input(XLEN_SINT)).suggestName("exu2ialu_main_op2_i")
  val exu2ialu_cmd_i      = IO(Input(UInt(SCR1_IALU_CMD_WIDTH.W))).suggestName("exu2ialu_cmd_i")
  val ialu2exu_main_res_o = IO(Output(XLEN_SINT)).suggestName("ialu2exu_main_res_o")
  val ialu2exu_cmp_res_o  = IO(Output(Bool())).suggestName("ialu2exu_cmp_res_o")
  // Address adder порты  
  val exu2ialu_addr_op1_i = IO(Input(XLEN_UINT)).suggestName("exu2ialu_addr_op1_i")
  val exu2ialu_addr_op2_i = IO(Input(XLEN_UINT)).suggestName("exu2ialu_addr_op2_i")
  val ialu2exu_addr_res_o = IO(Output(XLEN_UINT)).suggestName("ialu2exu_addr_res_o")


  //Address adder
  ialu2exu_addr_res_o := exu2ialu_addr_op1_i + exu2ialu_addr_op2_i

  val main_adder = new Logic_ops

  val (res_main_adder, cmp_res, rvm_rdy) = main_adder.mainAdderMux(exu2ialu_main_op1_i,
                                                      exu2ialu_main_op2_i,
                                                      exu2ialu_cmd_i,
                                                      // RVM extention
                                                      exu2ialu_rvm_cmd_vd_i,
                                                      clk,
                                                      rst_n)

  ialu2exu_main_res_o := res_main_adder
  ialu2exu_cmp_res_o  := cmp_res
  
  if (SCR1_RVM_EXT) {
    require(ialu2exu_rvm_res_rdy_o.isDefined, "RVM ready port should exist when RVM is enabled")
    ialu2exu_rvm_res_rdy_o.get := rvm_rdy
  }
}



object ALU_gen extends App {
    ChiselStage.emitSystemVerilogFile(new ALU_top, 
  args = Array("--target-dir", "../generated_SV_files/ALU_gen/"),
  firtoolOpts = Array("-disable-all-randomization",
                      "-strip-debug-info",
                      "--verify-each=false",
                      "-default-layer-specialization=enable"))
}