import chisel3._

trait SCR1Config {
  // Базовые параметры ширины
  val SCR1_XLEN: Int = 32
  val SCR1_IMEM_AWIDTH: Int = SCR1_XLEN
  val SCR1_IMEM_DWIDTH: Int = SCR1_XLEN
  val SCR1_DMEM_AWIDTH: Int = SCR1_XLEN
  val SCR1_DMEM_DWIDTH: Int = SCR1_XLEN
  
  // RISC-V расширения
  val SCR1_RVM_EXT:  Boolean = true
  val SCR1_RVC_EXT:  Boolean = false
  val SCR1_FAST_MUL: Boolean = true
  
  // Ширина команды (рассчитывается на основе количества опкодов)
  def SCR1_IALU_CMD_WIDTH: Int = {
    val baseOps = 15 
    val rvmOps = if (SCR1_RVM_EXT) 8 else 0
    val totalOps = baseOps + rvmOps
    chisel3.util.log2Ceil(totalOps + 1) 
  }
}