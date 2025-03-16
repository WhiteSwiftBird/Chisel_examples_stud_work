import chisel3._
import chisel3.stage.ChiselStage

class Mux_Variant_1 extends RawModule {
  val io = IO(new Bundle {
    val d0 = Input (UInt(4.W))
    val d1 = Input (UInt(4.W))
    val d2 = Input (UInt(4.W))
    val d3 = Input (UInt(4.W))
    val sel = Input (UInt(2.W))

    val y = Output (UInt(4.W))
  })

  io.y := Mux(io.sel(1), Mux(io.sel(0), io.d3, io.d2)
                       , Mux(io.sel(0), io.d1, io.d0))
}

object Mux_Variant_1 extends App 
{
    (new ChiselStage).emitVerilog(new Mux_Variant_1, 
    Array("--target-dir", "../systemverilog-homework/01_combinational_logic/01_01_mux_question"))
}