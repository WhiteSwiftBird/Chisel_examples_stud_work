package scr1_memif

import chisel3._

object Type_scr1_mem_cmd_e extends ChiselEnum {
  val SCR1_MEM_CMD_RD = Value(0.U)
  val SCR1_MEM_CMD_WR = Value(1.U)
}

object Type_scr1_mem_resp_e extends ChiselEnum {
  val SCR1_MEM_RESP_NOTRDY = Value(0.U(2.W))  // 2'b00
  val SCR1_MEM_RESP_RDY_OK = Value(1.U(2.W))  // 2'b01
  val SCR1_MEM_RESP_RDY_ER = Value(2.U(2.W))  // 2'b10
}