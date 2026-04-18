import chisel3._
import _root_.circt.stage.ChiselStage

import scr1_pipe_ialu._
import scr1_pipe_IFU._


object ALU_gen extends App {
    ChiselStage.emitSystemVerilogFile(new scr1_pipe_ialu, 
  args = Array("--target-dir", "../generated_SV_files/"),
  firtoolOpts = Array("-disable-all-randomization",
                      "-strip-debug-info",
                      "--verify-each=false",
                      "-default-layer-specialization=enable"))
}

object IFU_gen extends App {
    ChiselStage.emitSystemVerilogFile(new scr1_pipe_ifu, 
  args = Array("--target-dir", "../generated_SV_files/"),
  firtoolOpts = Array("-disable-all-randomization",
                      "-strip-debug-info",
                      "--verify-each=false",
                      "-default-layer-specialization=enable"))
}