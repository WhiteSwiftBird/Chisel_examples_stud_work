package IFULocalparams

import chisel3._
import chisel3.util._

object IFU_localparams {
  val SCR1_IFU_Q_SIZE_WORD = 2
  val SCR1_IFU_Q_SIZE_HALF = SCR1_IFU_Q_SIZE_WORD * 2
  val SCR1_TXN_CNT_W = 3
  
  val SCR1_IFU_QUEUE_ADR_W = log2Ceil(SCR1_IFU_Q_SIZE_HALF)
  val SCR1_IFU_QUEUE_PTR_W = SCR1_IFU_QUEUE_ADR_W + 1
  
  val SCR1_IFU_Q_FREE_H_W = log2Ceil(SCR1_IFU_Q_SIZE_HALF + 1)
  val SCR1_IFU_Q_FREE_W_W = log2Ceil(SCR1_IFU_Q_SIZE_WORD + 1)
}