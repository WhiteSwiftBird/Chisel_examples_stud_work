import chisel3._
import _root_.circt.stage.ChiselStage


object ALU_gen extends App {
    ChiselStage.emitSystemVerilogFile(new scr1_pipe_ialu, 
  args = Array("--target-dir", "../generated_SV_files/ALU_gen/"),
  firtoolOpts = Array("-disable-all-randomization",
                      "-strip-debug-info",
                      "--verify-each=false",
                      "-default-layer-specialization=enable"))
}