package scr1_pipe_IFU

import chisel3._
import chisel3.util._

import scr1_memif._
import arch_description._
import scr1_memif.Type_scr1_mem_cmd_e._  
import scr1_memif.Type_scr1_mem_resp_e._ 
import IFULocalparams._
import SCR1Config._

//там где надо поменять ширину сделать эточерез Wire

class IFUCtrl_IO extends Bundle{
    val pipe2ifu_stop_fetch_i = Input(Bool())
}

class IFU2Mem_IO extends Bundle {

    val imem2ifu_req_ack_i = Input(Bool())
    val ifu2imem_req_o = Output(Bool())
    val ifu2imem_cmd_o = Output(Type_scr1_mem_cmd_e())
    val ifu2imem_addr_o = Output(UInt(SCR1_IMEM_AWIDTH.W))
    val imem2ifu_rdata_i = Input(UInt(SCR1_IMEM_DWIDTH.W))
    val imem2ifu_resp_i = Input(Type_scr1_mem_resp_e())
} 

class IFU2EXU_newPC_IO extends Bundle {

    val exu2ifu_pc_new_req_i = Input(Bool())
    val exu2ifu_pc_new_i     = Input(UInt(SCR1_XLEN.W))
}

class IFU2IDU_IO extends Bundle {

    val idu2ifu_rdy_i = Input(Bool())
    val ifu2idu_instr_o = Output(UInt(SCR1_IMEM_DWIDTH.W))
    val ifu2idu_imem_err_o = Output(Bool())
    val ifu2idu_err_rvi_hi_o = Output(Bool())
    val ifu2idu_vd_o = Output(Bool())
}

//if clock control en
class ClkCtrl extends Bundle{
    val ifu2pipe_imem_txns_pnd_o = Output(Bool())
}


object IFU_types {
  
  // FSM states
  object SCR1_IFU_FSM extends ChiselEnum {
    val IDLE, FETCH = Value
  }
  // Queue write
  object SCR1_IFU_QUEUE_WR extends ChiselEnum {
    val NONE, FULL, HI = Value
  }
  // Queue read control
  object SCR1_IFU_QUEUE_RD extends ChiselEnum {
    val NONE, HWORD, WORD = Value
  }
  // Instruction types
  object SCR1_IFU_INSTR extends ChiselEnum {
    val NONE,                 
        RVI_HI_RVI_LO,        
        RVC_RVC,              
        RVI_LO_RVC,           
        RVC_RVI_HI,           
        RVI_LO_RVI_HI,        
        RVC_NV,               
        RVI_LO_NV = Value
  }
  
}


class scr1_pipe_ifu_4gen extends Module{
    import IFU_types._

    val io_ctrl = IO(new IFUCtrl_IO)
    val io_2Mem = IO(new IFU2Mem_IO)
    val io_2exu = IO(new IFU2EXU_newPC_IO)
    val io_2idu = IO(new IFU2IDU_IO)

    //if clock control en
    val io_clkCtrl = if (SCR1_CLKCTRL_EN) Some(IO(new ClkCtrl)) else None

    // parts of device 
    val instrTypeFinder = Module(new InstrTypeFinder)
    val instrRviReg = Module(new Instr_rvi_reg)
    val ifuFSM = Module(new IFUFSM)
    val instructionQueue = Module(new InstructionQueue)
    val imemCntr = Module(new IMEM_cntr)

    
    // 1. InstrTypeFinder <-> Instr_rvi_reg
    instrTypeFinder.io.instr_hi_rvi_lo_ff := instrRviReg.io.instr_hi_rvi_lo_ff
    instrRviReg.io.instr_type := instrTypeFinder.io.instr_type

    // 2. InstrTypeFinder -> InstructionQueue
    instructionQueue.io.instr_type_i := instrTypeFinder.io.instr_type

    //3. Queue write/read size decoders
    instructionQueue.io.exu2ifu_pc_new_req_i := io_2exu.exu2ifu_pc_new_req_i
    instructionQueue.io.pipe2ifu_stop_fetch_i := io_ctrl.pipe2ifu_stop_fetch_i
    instructionQueue.io.idu2ifu_rdy_i := io_2idu.idu2ifu_rdy_i
    instructionQueue.io.instr_type := instrTypeFinder.io.instr_type

    val imem_resp_discard_req = imemCntr.io.imem_resp_discard_req
    val imem_resp_ok = Wire(Bool())
    instructionQueue.io.imem_resp_discard_req := imem_resp_discard_req
    instructionQueue.io.imem_resp_ok := imem_resp_ok

    val ifu2idu_vd_o = Wire(Bool())
    val imem_resp_er = Wire(Bool())
    val q_rd_hword = Wire(Bool())

    instructionQueue.io.imem_resp_er := imem_resp_er
    instructionQueue.io.q_rd_hword := q_rd_hword
    instructionQueue.io.ifu2idu_vd_o := ifu2idu_vd_o

    val q_is_empty = instructionQueue.io.q_is_empty
    val q_has_free_slots = instructionQueue.io.q_has_free_slots
    val q_has_1_ocpd_hw = instructionQueue.io.q_has_1_ocpd_hw
    val q_wr_size = instructionQueue.io.q_wr_size
    val q_flush_req = instructionQueue.io.q_flush_req
    val q_wptr = instructionQueue.io.q_wptr
    val q_rptr = instructionQueue.io.q_rptr

    //4. Register to store if the previous IMEM instruction had low part of RVI
    // instruction in its high part
    val imem_resp_vd = Wire(Bool())
    instrRviReg.io.imem_resp_vd := imem_resp_vd
    instrRviReg.io.exu2ifu_pc_new_req_i := io_2exu.exu2ifu_pc_new_req_i

    //5. Instruction type decoder
    instrTypeFinder.io.imem_rdata := io_2Mem.imem2ifu_rdata_i
    instrTypeFinder.io.exu2ifu_pc_new_i := io_2exu.exu2ifu_pc_new_i
    instrTypeFinder.io.exu2ifu_pc_new_req_i := io_2exu.exu2ifu_pc_new_req_i
    instrTypeFinder.io.imem_resp_vd := imem_resp_vd

    //6. IFU FSM
    val imem_resp_er_discard_pnd = Wire(Bool()) 

    ifuFSM.io.exu2ifu_pc_new_req_i := io_2exu.exu2ifu_pc_new_req_i
    ifuFSM.io.pipe2ifu_stop_fetch_i := io_ctrl.pipe2ifu_stop_fetch_i
    ifuFSM.io.imem_resp_er_discard_pnd := imem_resp_er_discard_pnd

    val ifu_fsm_fetch = ifuFSM.io.ifu_fsm_fetch

    
    // 7. Imem
    val imem_handshake_done = Wire(Bool())
    val imem_resp_received = Wire(Bool())

    imemCntr.io.imem_handshake_done := imem_handshake_done
    imemCntr.io.imem_resp_received := imem_resp_received
    imemCntr.io.exu2ifu_pc_new_req_i := io_2exu.exu2ifu_pc_new_req_i
    imemCntr.io.imem_resp_er_discard_pnd := imem_resp_er_discard_pnd

    val imem_pnd_txns_cnt = imemCntr.io.imem_pnd_txns_cnt
    val imem_pnd_txns_q_full = imemCntr.io.imem_pnd_txns_q_full
    instructionQueue.io.imem_vd_pnd_txns_cnt := imemCntr.io.imem_vd_pnd_txns_cnt
    

    // IMEM response logic
    //------------------------------------------------------------------------------

    // IMEM response logic
    imem_resp_er := io_2Mem.imem2ifu_resp_i === SCR1_MEM_RESP_RDY_ER
    imem_resp_ok := io_2Mem.imem2ifu_resp_i === SCR1_MEM_RESP_RDY_OK
    imem_resp_received := imem_resp_ok || imem_resp_er
    imem_resp_vd := imem_resp_received && !imem_resp_discard_req
    imem_resp_er_discard_pnd := imem_resp_er && !imem_resp_discard_req

    imem_handshake_done := io_2Mem.ifu2imem_req_o && io_2Mem.imem2ifu_req_ack_i


    // Queue data and error flag registers
    //------------------------------------------------------------------------------

    val q_data = Mem(IFU_localparams.SCR1_IFU_Q_SIZE_HALF, UInt(16.W))
    val q_err = Mem(IFU_localparams.SCR1_IFU_Q_SIZE_HALF, Bool())

    val imem_rdata_hi = io_2Mem.imem2ifu_rdata_i(31, 16)
    val imem_rdata_lo = io_2Mem.imem2ifu_rdata_i(15, 0)

    val q_wr_en = imem_resp_vd && !q_flush_req

    when(q_wr_en) {
    switch(q_wr_size) {
        is(SCR1_IFU_QUEUE_WR.HI) {
        q_data(q_wptr) := imem_rdata_hi
        q_err(q_wptr) := imem_resp_er
        }
        is(SCR1_IFU_QUEUE_WR.FULL) {
        q_data(q_wptr) := imem_rdata_lo
        q_err(q_wptr) := imem_resp_er
        q_data(q_wptr + 1.U) := imem_rdata_hi
        q_err(q_wptr + 1.U) := imem_resp_er
        }
    }
    }

    val q_data_head = q_data(q_rptr)
    val q_data_next = q_data(q_rptr + 1.U)
    val q_err_head = q_err(q_rptr)
    val q_err_next = q_err(q_rptr + 1.U)

    val q_head_is_rvi = q_data_head(1, 0).andR
    val q_head_is_rvc = !q_head_is_rvi

    q_rd_hword := q_head_is_rvc || q_err_head

    // IMEM address registers
    //------------------------------------------------------------------------------
    val imem_addr_upd = imem_handshake_done || io_2exu.exu2ifu_pc_new_req_i

    val imem_addr_ff_full = RegInit(0.U(SCR1_XLEN.W))
    val imem_addr_next_full = Wire(UInt(SCR1_XLEN.W))
    imem_addr_ff_full := imem_addr_next_full

    val imem_addr_next = Wire(UInt((SCR1_XLEN - 2).W))
    imem_addr_next_full := Cat(imem_addr_next, 0.U(2.W))
    val imem_addr_ff = imem_addr_ff_full(SCR1_XLEN - 1, 2)

    imem_addr_next := Mux(imem_addr_upd,
                        Mux(io_2exu.exu2ifu_pc_new_req_i,
                            io_2exu.exu2ifu_pc_new_i(SCR1_XLEN-1, 2)+ imem_handshake_done,
                            Mux(imem_addr_ff_full(5, 2).andR,
                                    imem_addr_ff       + imem_handshake_done,
                                Cat(imem_addr_ff_full(SCR1_XLEN-1, 6), 
                                    imem_addr_ff_full(5, 2) + imem_handshake_done)
                            )
                        ),
                        imem_addr_ff
                        )

    val imem_resp_discard_cnt_upd = io_2exu.exu2ifu_pc_new_req_i || imem_resp_er || (imem_resp_ok && imem_resp_discard_req)

    // IFU <-> IMEM interface output signals
    //------------------------------------------------------------------------------
    io_2Mem.ifu2imem_req_o := (io_2exu.exu2ifu_pc_new_req_i && !imem_pnd_txns_q_full && !io_ctrl.pipe2ifu_stop_fetch_i) ||
                              (ifu_fsm_fetch && !imem_pnd_txns_q_full && q_has_free_slots)
    
    io_2Mem.ifu2imem_addr_o := Mux(io_2exu.exu2ifu_pc_new_req_i,
                                    Cat(io_2exu.exu2ifu_pc_new_i(SCR1_XLEN-1, 2), 0.U(2.W)),
                                    Cat(imem_addr_ff, 0.U(2.W))                              
                                )
    io_2Mem.ifu2imem_cmd_o := SCR1_MEM_CMD_RD

    if (SCR1_CLKCTRL_EN) {
        io_clkCtrl.get.ifu2pipe_imem_txns_pnd_o := imem_pnd_txns_cnt =/= 0.U
    }

    //------------------------------------------------------------------------------
    // IFU <-> IDU interface
    //------------------------------------------------------------------------------

    // IFU <-> IDU interface status signals
    //------------------------------------------------------------------------------
    io_2idu.ifu2idu_vd_o := ifu2idu_vd_o
    ifu2idu_vd_o := false.B
    io_2idu.ifu2idu_imem_err_o := false.B
    io_2idu.ifu2idu_err_rvi_hi_o := false.B

    when(!q_is_empty) {
        when(q_has_1_ocpd_hw) {
            ifu2idu_vd_o := q_head_is_rvc || q_err_head
            io_2idu.ifu2idu_imem_err_o := q_err_head
        }.otherwise {
            ifu2idu_vd_o := true.B
            io_2idu.ifu2idu_imem_err_o := Mux(q_err_head, 
                                            true.B, 
                                            (q_head_is_rvi && q_err_next).asBool)
            io_2idu.ifu2idu_err_rvi_hi_o := (!q_err_head) && q_head_is_rvi && q_err_next
        }
    }

    // Output instruction multiplexer
    //------------------------------------------------------------------------------
    val instr_full = Wire(UInt(SCR1_IMEM_DWIDTH.W))
    instr_full := Cat(q_data_next, q_data_head)
    io_2idu.ifu2idu_instr_o := Mux(q_head_is_rvc, 
                                q_data_head, 
                                instr_full)
}




//==================================================================================
//==================================================================================
//============================SUBMODULES AND OVER CLASSES===========================
//==================================================================================
//==================================================================================

// Instruction type decoder
//------------------------------------------------------------------------------
class InstrTypeFinder extends Module{
    import IFU_types._

val io = IO(new Bundle {
        val instr_hi_rvi_lo_ff = Input(Bool())
        val imem_rdata = Input(UInt(32.W))
        val exu2ifu_pc_new_req_i = Input(Bool())
        val exu2ifu_pc_new_i = Input(UInt(SCR1_XLEN.W))
        val imem_resp_vd = Input(Bool())
        val instr_type = Output(SCR1_IFU_INSTR())

})

    val new_pc_unaligned_ff = RegInit(false.B)
    val new_pc_unaligned_next = Wire(Bool())
    new_pc_unaligned_ff := new_pc_unaligned_next

    when(io.exu2ifu_pc_new_req_i || io.imem_resp_vd)
    {
        new_pc_unaligned_next := Mux(io.exu2ifu_pc_new_req_i, 
                                    io.exu2ifu_pc_new_i(1).asBool, false.B)
    }.otherwise{
        new_pc_unaligned_next := new_pc_unaligned_ff
    }

    val hi_is_rvi = io.imem_rdata(17, 16).andR
    val lo_is_rvi = io.imem_rdata(1, 0).andR
    
    io.instr_type := MuxLookup(Cat(new_pc_unaligned_ff, io.instr_hi_rvi_lo_ff), SCR1_IFU_INSTR.NONE)(
        Seq(
        // new_pc_unaligned_ff = true
        "b10".U -> Mux(hi_is_rvi, SCR1_IFU_INSTR.RVI_LO_NV, SCR1_IFU_INSTR.RVC_NV),
        "b11".U -> Mux(hi_is_rvi, SCR1_IFU_INSTR.RVI_LO_NV, SCR1_IFU_INSTR.RVC_NV),
        
        // new_pc_unaligned_ff = false, instr_hi_rvi_lo_ff = true
        "b01".U -> Mux(hi_is_rvi, SCR1_IFU_INSTR.RVI_LO_RVI_HI, SCR1_IFU_INSTR.RVC_RVI_HI),
        
        // new_pc_unaligned_ff = false, instr_hi_rvi_lo_ff = false
        "b00".U -> MuxLookup(Cat(hi_is_rvi, lo_is_rvi), SCR1_IFU_INSTR.NONE)(
            Seq(
            "b00".U -> SCR1_IFU_INSTR.RVC_RVC,
            "b10".U -> SCR1_IFU_INSTR.RVI_LO_RVC,
            "b01".U -> SCR1_IFU_INSTR.RVI_HI_RVI_LO,
            "b11".U -> SCR1_IFU_INSTR.RVI_HI_RVI_LO
            )
        )
        )
    )
}


// Register to store if the previous IMEM instruction had low part of RVI
// instruction in its high part
//------------------------------------------------------------------------------
class Instr_rvi_reg extends Module{
    import IFU_types._
    val io = IO(new Bundle {
        // Входы
        val imem_resp_vd = Input(Bool())
        val instr_type = Input(SCR1_IFU_INSTR())
        val exu2ifu_pc_new_req_i = Input(Bool())
        
        // Выход
        val instr_hi_rvi_lo_ff = Output(Bool())
    })

    val instr_hi_rvi_lo_d = RegInit(false.B)
    val instr_hi_rvi_lo_next = Wire(Bool())
    instr_hi_rvi_lo_d := instr_hi_rvi_lo_next

    when(io.exu2ifu_pc_new_req_i){
            instr_hi_rvi_lo_next := false.B
        }.otherwise{
            instr_hi_rvi_lo_next := Mux(io.imem_resp_vd, (io.instr_type === SCR1_IFU_INSTR.RVI_LO_NV)
                                ||(io.instr_type === SCR1_IFU_INSTR.RVI_LO_RVI_HI)
                                ||(io.instr_type === SCR1_IFU_INSTR.RVI_LO_RVC), instr_hi_rvi_lo_d)
        }
    
    io.instr_hi_rvi_lo_ff := instr_hi_rvi_lo_d


}


// Queue write/read size decoders
//------------------------------------------------------------------------------

class InstructionQueue extends Module{
    import IFU_types._
    
    // IOs
    val io = IO(new Bundle{
    val exu2ifu_pc_new_req_i = Input(Bool())
    val pipe2ifu_stop_fetch_i = Input(Bool())
    val ifu2idu_vd_o = Input(Bool())
    val idu2ifu_rdy_i = Input(Bool())
    val instr_type_i = Input(SCR1_IFU_INSTR())
    val imem_resp_discard_req = Input(Bool())
    val imem_resp_ok = Input(Bool())
    val instr_type = Input(SCR1_IFU_INSTR())
    val imem_resp_er = Input(Bool())
    
    val q_is_empty = Output(Bool())
    val q_has_free_slots = Output(Bool())
    val q_has_1_ocpd_hw = Output(Bool())
  
    val q_wr_size = Output(SCR1_IFU_QUEUE_WR())
    val q_rd_hword = Input(Bool())
    val q_flush_req = Output(Bool())
    val q_wptr = Output(UInt(IFU_localparams.SCR1_IFU_QUEUE_PTR_W.W))
    val q_rptr = Output(UInt(IFU_localparams.SCR1_IFU_QUEUE_PTR_W.W))

    val imem_vd_pnd_txns_cnt = Input(UInt(IFU_localparams.SCR1_TXN_CNT_W.W))
    })


    // Write/read pointer registers
    io.q_flush_req := io.exu2ifu_pc_new_req_i || io.pipe2ifu_stop_fetch_i
    
    val q_wptr = RegInit(0.U(IFU_localparams.SCR1_IFU_QUEUE_PTR_W.W))
    val q_wptr_next = Wire(UInt(IFU_localparams.SCR1_IFU_QUEUE_PTR_W.W))
    q_wptr := q_wptr_next
    val q_rptr = RegInit(0.U(IFU_localparams.SCR1_IFU_QUEUE_PTR_W.W))
    val q_rptr_next = Wire(UInt(IFU_localparams.SCR1_IFU_QUEUE_PTR_W.W))
    q_rptr := q_rptr_next

    io.q_wptr := q_wptr
    io.q_rptr := q_rptr

    // status
    val q_ocpd_h = Wire(UInt(IFU_localparams.SCR1_IFU_Q_FREE_H_W.W))
    val q_free_h_next = Wire(UInt(IFU_localparams.SCR1_IFU_Q_FREE_H_W.W))
    val q_free_w_next = Wire(UInt(IFU_localparams.SCR1_IFU_Q_FREE_W_W.W))
    val q_free_w_next_temp = Wire(UInt(IFU_localparams.SCR1_TXN_CNT_W.W))
    
    q_ocpd_h := (io.q_wptr - q_rptr)
    q_free_h_next := (IFU_localparams.SCR1_IFU_Q_SIZE_HALF.U - (q_wptr - q_rptr_next))
    q_free_w_next := (q_free_h_next >> 1)
    q_free_w_next_temp := q_free_w_next

    io.q_is_empty := q_rptr === q_wptr
    io.q_has_free_slots := q_free_w_next_temp > io.imem_vd_pnd_txns_cnt
    io.q_has_1_ocpd_hw := q_ocpd_h === 1.U(IFU_localparams.SCR1_IFU_Q_FREE_H_W.W)

    // Queue write/read size decoders
    // Queue read size decoder
    val q_rd_vd = !io.q_is_empty && io.ifu2idu_vd_o && io.idu2ifu_rdy_i
    

    val q_rd_size = Mux(!q_rd_vd, SCR1_IFU_QUEUE_RD.NONE,
                        Mux(io.q_rd_hword, SCR1_IFU_QUEUE_RD.HWORD, SCR1_IFU_QUEUE_RD.WORD))

    val q_rd_none = q_rd_size === SCR1_IFU_QUEUE_RD.NONE

    // Queue write size decoder
    val q_wr_size = WireDefault(SCR1_IFU_QUEUE_WR.NONE)
    io.q_wr_size := q_wr_size

    when(~io.imem_resp_discard_req) {
    when(io.imem_resp_ok) {
        q_wr_size := MuxCase(SCR1_IFU_QUEUE_WR.FULL, Seq(
            (io.instr_type === SCR1_IFU_INSTR.NONE) -> SCR1_IFU_QUEUE_WR.NONE,
            (io.instr_type === SCR1_IFU_INSTR.RVC_NV) -> SCR1_IFU_QUEUE_WR.HI,
            (io.instr_type === SCR1_IFU_INSTR.RVI_LO_NV) -> SCR1_IFU_QUEUE_WR.HI
        ))
    }.elsewhen(io.imem_resp_er) {
        q_wr_size := SCR1_IFU_QUEUE_WR.FULL
    }
    }

    val q_wr_none = q_wr_size === SCR1_IFU_QUEUE_WR.NONE
    val q_wr_full = q_wr_size === SCR1_IFU_QUEUE_WR.FULL

    // Write/read pointer registers signals
    val q_wptr_upd = io.q_flush_req || !q_wr_none
    val q_rptr_upd = io.q_flush_req || !q_rd_none

    q_wptr_next := Mux(q_wptr_upd,
                    Mux(io.q_flush_req, 
                        0.U(IFU_localparams.SCR1_IFU_QUEUE_PTR_W.W),
                        Mux(~q_wr_none,
                            q_wptr + Mux(q_wr_full, 
                                            2.U(IFU_localparams.SCR1_IFU_QUEUE_PTR_W.W), 
                                            1.U(IFU_localparams.SCR1_IFU_QUEUE_PTR_W.W)),
                            q_wptr)
                    ),
                    q_wptr
                )

    q_rptr_next := Mux(q_rptr_upd,
                    Mux(io.q_flush_req, 
                        0.U(IFU_localparams.SCR1_IFU_QUEUE_PTR_W.W),
                        Mux(~q_rd_none,
                            q_rptr + Mux(io.q_rd_hword, 
                                            1.U(IFU_localparams.SCR1_IFU_QUEUE_PTR_W.W), 
                                            2.U(IFU_localparams.SCR1_IFU_QUEUE_PTR_W.W)),
                            q_rptr)
                    ),
                    q_rptr
                )
}


// IFU FSM
//------------------------------------------------------------------------------
class IFUFSM extends Module{
    import IFU_types._
    
    val io = IO(new Bundle {
        val exu2ifu_pc_new_req_i = Input(Bool())
        val pipe2ifu_stop_fetch_i = Input(Bool())
        val imem_resp_er_discard_pnd = Input(Bool())
        val ifu_fsm_fetch = Output(Bool())
    })
    
    
    val state_curr = RegInit(SCR1_IFU_FSM.IDLE)
    val state_next = Wire(SCR1_IFU_FSM())
    state_curr := state_next
    
    val fetch_req = io.exu2ifu_pc_new_req_i && !io.pipe2ifu_stop_fetch_i
    val stop_req = io.pipe2ifu_stop_fetch_i || 
                   (io.imem_resp_er_discard_pnd && !io.exu2ifu_pc_new_req_i)
    
    state_next := MuxCase(state_curr, Seq(
        (state_curr === SCR1_IFU_FSM.IDLE && fetch_req) -> SCR1_IFU_FSM.FETCH,
        (state_curr === SCR1_IFU_FSM.FETCH && stop_req) -> SCR1_IFU_FSM.IDLE
    ))
    
    io.ifu_fsm_fetch := state_curr === SCR1_IFU_FSM.FETCH
}


//------------------------------------------------------------------------------
class IMEM_cntr extends Module{

    val io = IO(new Bundle{
        val imem_pnd_txns_cnt = Output(UInt(IFU_localparams.SCR1_TXN_CNT_W.W))
        val imem_handshake_done = Input(Bool())
        val imem_resp_received = Input(Bool())
        val imem_pnd_txns_q_full = Output(Bool())
        val exu2ifu_pc_new_req_i = Input(Bool()) 
        val imem_resp_er_discard_pnd = Input(Bool())
        val imem_vd_pnd_txns_cnt = Output(UInt(IFU_localparams.SCR1_TXN_CNT_W.W))
        val imem_resp_discard_req = Output(Bool())
    })

    // Pending IMEM transactions counter

    val imem_pnd_txns_cnt_upd = io.imem_handshake_done ^ io.imem_resp_received

    val imem_pnd_txns_cnt = RegInit(0.U(IFU_localparams.SCR1_TXN_CNT_W.W))
    val imem_pnd_txns_cnt_next = Wire(UInt(IFU_localparams.SCR1_TXN_CNT_W.W))
    imem_pnd_txns_cnt := imem_pnd_txns_cnt_next

    imem_pnd_txns_cnt_next := (imem_pnd_txns_cnt + 
                            Mux(io.imem_handshake_done, 1.U, 0.U) - 
                            Mux(io.imem_resp_received, 1.U, 0.U))

    io.imem_pnd_txns_q_full := imem_pnd_txns_cnt === ((1 << IFU_localparams.SCR1_TXN_CNT_W) - 1).U

    // IMEM discard responses counter
    val imem_resp_discard_cnt = RegInit(0.U(IFU_localparams.SCR1_TXN_CNT_W.W))
    val imem_resp_discard_cnt_next = Wire(UInt(IFU_localparams.SCR1_TXN_CNT_W.W))
    imem_resp_discard_cnt := imem_resp_discard_cnt_next

   imem_resp_discard_cnt_next := MuxCase(imem_resp_discard_cnt - 1.U, Seq(
                                (io.exu2ifu_pc_new_req_i)     -> (imem_pnd_txns_cnt_next - io.imem_handshake_done),
                                (io.imem_resp_er_discard_pnd) -> imem_pnd_txns_cnt_next
                                ))

    io.imem_vd_pnd_txns_cnt := (imem_pnd_txns_cnt - imem_resp_discard_cnt)
    io.imem_resp_discard_req := imem_resp_discard_cnt =/= 0.U
    io.imem_pnd_txns_cnt := imem_pnd_txns_cnt
}



//------------------------------------------------------------------------------
// обертка для интеграции в существующий SV с соответствующими названиями портов
class scr1_pipe_ifu extends RawModule {
    val rst_n = IO(Input(Bool())).suggestName("rst_n")
    val clk = IO(Input(Clock())).suggestName("clk")
    val pipe2ifu_stop_fetch = IO(Input(Bool())).suggestName("pipe2ifu_stop_fetch_i")

    val imem2ifu_req_ack = IO(Input(Bool())).suggestName("imem2ifu_req_ack_i")
    val ifu2imem_req = IO(Output(Bool())).suggestName("ifu2imem_req_o")
    val ifu2imem_cmd = IO(Output(Type_scr1_mem_cmd_e())).suggestName("ifu2imem_cmd_o")
    val ifu2imem_addr = IO(Output(UInt(SCR1_IMEM_AWIDTH.W))).suggestName("ifu2imem_addr_o")
    val imem2ifu_rdata = IO(Input(UInt(SCR1_IMEM_DWIDTH.W))).suggestName("imem2ifu_rdata_i")
    val imem2ifu_resp = IO(Input(Type_scr1_mem_resp_e())).suggestName("imem2ifu_resp_i")

    val exu2ifu_pc_new_req = IO(Input(Bool())).suggestName("exu2ifu_pc_new_req_i")
    val exu2ifu_pc_new = IO(Input(UInt(SCR1_XLEN.W))).suggestName("exu2ifu_pc_new_i")

    val idu2ifu_rdy = IO(Input(Bool())).suggestName("idu2ifu_rdy_i")
    val ifu2idu_instr = IO(Output(UInt(SCR1_IMEM_DWIDTH.W))).suggestName("ifu2idu_instr_o")
    val ifu2idu_imem_err = IO(Output(Bool())).suggestName("ifu2idu_imem_err_o")
    val ifu2idu_err_rvi_hi = IO(Output(Bool())).suggestName("ifu2idu_err_rvi_hi_o")
    val ifu2idu_vd = IO(Output(Bool())).suggestName("ifu2idu_vd_o")

    val ifu2pipe_imem_txns_pnd = if (SCR1_CLKCTRL_EN) 
    Some(IO(Output(Bool())).suggestName("ifu2pipe_imem_txns_pnd_o")) 
    else None

    private val ifu_4gen = withClockAndReset(clk, !rst_n) { 
                            Module(new scr1_pipe_ifu_4gen)}
    
    ifu_4gen.io_ctrl.pipe2ifu_stop_fetch_i := pipe2ifu_stop_fetch

    ifu_4gen.io_2Mem.imem2ifu_req_ack_i := imem2ifu_req_ack
    ifu_4gen.io_2Mem.imem2ifu_rdata_i := imem2ifu_rdata
    ifu_4gen.io_2Mem.imem2ifu_resp_i := imem2ifu_resp

    ifu2imem_req := ifu_4gen.io_2Mem.ifu2imem_req_o
    ifu2imem_cmd := ifu_4gen.io_2Mem.ifu2imem_cmd_o
    ifu2imem_addr := ifu_4gen.io_2Mem.ifu2imem_addr_o

    ifu_4gen.io_2exu.exu2ifu_pc_new_req_i := exu2ifu_pc_new_req
    ifu_4gen.io_2exu.exu2ifu_pc_new_i := exu2ifu_pc_new

    ifu_4gen.io_2idu.idu2ifu_rdy_i := idu2ifu_rdy

    ifu2idu_instr := ifu_4gen.io_2idu.ifu2idu_instr_o
    ifu2idu_imem_err := ifu_4gen.io_2idu.ifu2idu_imem_err_o
    ifu2idu_err_rvi_hi := ifu_4gen.io_2idu.ifu2idu_err_rvi_hi_o
    ifu2idu_vd := ifu_4gen.io_2idu.ifu2idu_vd_o

    if (SCR1_CLKCTRL_EN) {
        ifu2pipe_imem_txns_pnd.get := ifu_4gen.io_clkCtrl.get.ifu2pipe_imem_txns_pnd_o
    }

}