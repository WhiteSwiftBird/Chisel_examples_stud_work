import chisel3._

class Mux_Variant_1 extends RawModule {

    val d0 = IO(Input (UInt(4.W))).suggestName("d0")
    val d1 = IO(Input (UInt(4.W))).suggestName("d1")
    val d2 = IO(Input (UInt(4.W))).suggestName("d2")
    val d3 = IO(Input (UInt(4.W))).suggestName("d3")
    val sel = IO(Input (UInt(2.W))).suggestName("sel")

    val y = IO(Output (UInt(4.W))).suggestName("y")


  y := Mux(sel(1), Mux(sel(0), d3, d2)
                       , Mux(sel(0), d1, d0))
}

object Mux_Variant_1 extends App {
  emitVerilog(new Mux_Variant_1, 
    Array("--target-dir", "../generated_SV_files/mux4_2/"))
}
