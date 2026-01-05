import chisel3._
import chisel3.util._


trait ALU_cmd extends  SCR1Config{
    val opcodes: Map[String, UInt] = List(
        "NONE", 
        "AND", 
        "OR", 
        "XOR", 
        "ADD", 
        "SUB", 
        "SUB_LT", 
        "SUB_LTU", 
        "SUB_EQ", 
        "SUB_NE", 
        "SUB_GE", 
        "SUB_GEU", 
        "SLL", 
        "SRL", 
        "SRA",
        "MUL",
        "MULHU",
        "MULHSU", 
        "MULH",
        "DIV",
        "DIVU",
        "REM",
        "REMU"
    ).zipWithIndex.map {case (name, index) => (name, index.U)}.toMap

    val SCR1_IALU_CMD_NONE: UInt = opcodes("NONE")       // 0.U - IALU disable
    val SCR1_IALU_CMD_AND: UInt = opcodes("AND")         // 1.U - op1 & op2
    val SCR1_IALU_CMD_OR: UInt = opcodes("OR")           // 2.U - op1 | op2
    val SCR1_IALU_CMD_XOR: UInt = opcodes("XOR")         // 3.U - op1 ^ op2
    val SCR1_IALU_CMD_ADD: UInt = opcodes("ADD")         // 4.U - op1 + op2
    val SCR1_IALU_CMD_SUB: UInt = opcodes("SUB")         // 5.U - op1 - op2
    val SCR1_IALU_CMD_SUB_LT: UInt = opcodes("SUB_LT")   // 6.U - op1 < op2
    val SCR1_IALU_CMD_SUB_LTU: UInt = opcodes("SUB_LTU") // 7.U - op1 u< op2
    val SCR1_IALU_CMD_SUB_EQ: UInt = opcodes("SUB_EQ")   // 8.U - op1 = op2
    val SCR1_IALU_CMD_SUB_NE: UInt = opcodes("SUB_NE")   // 9.U - op1 != op2
    val SCR1_IALU_CMD_SUB_GE: UInt = opcodes("SUB_GE")   // 10.U - op1 >= op2
    val SCR1_IALU_CMD_SUB_GEU: UInt = opcodes("SUB_GEU") // 11.U - op1 u>= op2
    val SCR1_IALU_CMD_SLL: UInt = opcodes("SLL")         // 12.U - op1 << op2
    val SCR1_IALU_CMD_SRL: UInt = opcodes("SRL")         // 13.U - op1 >> op2
    val SCR1_IALU_CMD_SRA: UInt = opcodes("SRA")         // 14.U - op1 >>> op2

    // RVM extension opcodes
    val SCR1_IALU_CMD_MUL: UInt = opcodes("MUL")       // 0хF low(unsig(op1) * unsig(op2))
    val SCR1_IALU_CMD_MULHU: UInt = opcodes("MULHU")   // 0x10 high(unsig(op1) * unsig(op2))
    val SCR1_IALU_CMD_MULHSU: UInt = opcodes("MULHSU") // 0x11 high(op1 * unsig(op2))
    val SCR1_IALU_CMD_MULH: UInt = opcodes("MULH")     // 0x12 high(op1 * op2)
    val SCR1_IALU_CMD_DIV: UInt = opcodes("DIV")       // 0x13 op1 / op2
    val SCR1_IALU_CMD_DIVU: UInt = opcodes("DIVU")     // 0x14 op1 u/ op2
    val SCR1_IALU_CMD_REM: UInt = opcodes("REM")       // 0x15 op1 % op2
    val SCR1_IALU_CMD_REMU: UInt = opcodes("REMU")     // 0x16 op1 u% op2
}


trait RVM_ext_local_params extends SCR1Config{

    val SCR1_MUL_RES_WIDTH = 2 * SCR1_XLEN

    val SCR1_MUL_STG_NUM = 32

    val SCR1_MUL_WIDTH = if(SCR1_FAST_MUL) {SCR1_XLEN} else {32 / SCR1_MUL_STG_NUM}
    val SCR1_MUL_CNT_INIT = if(!SCR1_FAST_MUL) {1.U(32.W) << (SCR1_XLEN / SCR1_MUL_WIDTH - 2)} else{0.U(32.W)}
    val SCR1_MDU_SUM_WIDTH =  if(SCR1_FAST_MUL) {SCR1_XLEN + 1} else {SCR1_XLEN + SCR1_MUL_WIDTH} 

    val SCR1_DIV_WIDTH = 1
    val SCR1_DIV_CNT_INIT = 1.U(32.W) << (SCR1_XLEN / SCR1_DIV_WIDTH - 2)
}


class ALUflagsBundle extends Bundle {
    val zero = Bool()
    val sign = Bool()
    val carry = Bool()
    val overflow = Bool()
}


object AluMduFsmState extends ChiselEnum {
    val IDLE, ITER, CORR = Value
    
    val SCR1_IALU_MDU_FSM_IDLE = IDLE
    val SCR1_IALU_MDU_FSM_ITER = ITER
    val SCR1_IALU_MDU_FSM_CORR = CORR
    }

object AluMduCmd extends ChiselEnum {
    val NONE, MUL, DIV = Value
    
    val SCR1_IALU_MDU_NONE = NONE
    val SCR1_IALU_MDU_MUL = MUL
    val SCR1_IALU_MDU_DIV = DIV
    }

case class MulSignals(
    op1: Option[SInt] = None,
    op2: Option[SInt] = None,
    res: Option[SInt] = None,
    partProd: Option[SInt] = None,
    resHi: Option[UInt] = None,
    resLo: Option[UInt] = None
)


class Logic_ops extends ALU_cmd with RVM_ext_local_params{
    import AluMduCmd._
    import AluMduFsmState._
    
    val flags = Wire(new ALUflagsBundle)
    flags.zero := DontCare
    flags.sign := DontCare
    flags.carry := DontCare
    flags.overflow := DontCare


    def add_main(cmd: UInt, op_1: SInt, op_2: SInt): SInt = {
        val op1_ext = Wire(SInt((SCR1_XLEN + 1).W))
        val op2_ext = Wire(SInt((SCR1_XLEN + 1).W))
        
        op1_ext := op_1.asUInt.zext
        op2_ext := op_2.asUInt.zext
        
        val result_full = (Mux((cmd === SCR1_IALU_CMD_ADD), 
                                op1_ext + op2_ext, 
                                op1_ext - op2_ext)).asSInt

        val carry_t = result_full(SCR1_XLEN)
        val result  = result_full(SCR1_XLEN - 1, 0).asSInt

        val overflow_pos = ~op_1(SCR1_XLEN - 1) & op_2(SCR1_XLEN - 1)  & result(SCR1_XLEN - 1)
        val overflow_neg = op_1(SCR1_XLEN - 1)  & ~op_2(SCR1_XLEN - 1) & ~result(SCR1_XLEN - 1)

        flags.zero := !result(SCR1_XLEN - 1, 0).orR
        flags.carry := carry_t
        flags.overflow := overflow_neg | overflow_pos
        flags.sign := result(SCR1_XLEN - 1)

        result
    }
    
    def RVM_ext_part(
        op_1: UInt,
        op_2: UInt,
        cmd: UInt,
        cmd_vd_i: Bool,
        clock: Clock,
        rst_n: Bool
    ): (SInt, Bool) = {
        // Умножение и деление оссуществляется внутри клокового домена
        withClockAndReset(clock, !rst_n) {

        //объявление связей и их дефолтных значений
        val result = WireDefault(0.S(SCR1_XLEN.W))
        val res_rdy_o = Wire(Bool())
        res_rdy_o := false.B

        val mdu_fsm_next = WireDefault(IDLE)
        val mdu_iter_cnt_next = Wire(UInt(SCR1_XLEN.W))

        // является команда командой умножения или деления или нет
        val mdu_cmd_div = cmd === SCR1_IALU_CMD_DIV ||
                          cmd === SCR1_IALU_CMD_DIVU ||
                          cmd === SCR1_IALU_CMD_REM ||
                          cmd === SCR1_IALU_CMD_REMU

        val mdu_cmd_mul = cmd === SCR1_IALU_CMD_MUL ||
                          cmd === SCR1_IALU_CMD_MULH ||
                          cmd === SCR1_IALU_CMD_MULHU ||
                          cmd === SCR1_IALU_CMD_MULHSU

        //Какая из операций выполняется: никакой, умножение, деление (возвращает одно из значений MuxCase(default, Seq(
                                                                        //     condition1 -> value1,
                                                                        //     condition2 -> value2,
                                                                        //     condition3 -> value3,
                                                                        //     // ...
                                                                        // )))
        val mdu_cmd = MuxCase(SCR1_IALU_MDU_NONE, Seq(
            mdu_cmd_div -> SCR1_IALU_MDU_DIV,
            mdu_cmd_mul -> SCR1_IALU_MDU_MUL
        ))

        //оба оепратора не нулевые
        val main_ops_non_zero = op_1.orR && op_2.orR

        //различаются ли знаки операндов для знакового умножения
        val main_ops_diff_sgn = op_1(SCR1_XLEN-1) ^ op_2(SCR1_XLEN-1)

        //итерационная операция или нет (быстрое умножение подразумевает умножение за один такт)
        val mdu_cmd_is_iter = if (SCR1_FAST_MUL) {
            mdu_cmd_div
        } else {
            mdu_cmd_mul || mdu_cmd_div
        }

        //-------------------------------------------------------------------------------
        // MUL/DIV FSM
        //-------------------------------------------------------------------------------
        //создание регистра состояний КА и проверка на то в каком состоянии он находится
        val mdu_fsm_ff = RegInit(SCR1_IALU_MDU_FSM_IDLE)
        val mdu_fsm_idle = mdu_fsm_ff === SCR1_IALU_MDU_FSM_IDLE
        val mdu_fsm_corr = mdu_fsm_ff === SCR1_IALU_MDU_FSM_CORR

        //объявления связей для деления
        // - перенос остатка
        // - остаток
        // - текущая часть для вычисления
        // -следующий бит, присоединяемый к текущей

        val div_res_rem_c = Wire(Bool())
        val div_res_rem = Wire(UInt(SCR1_XLEN.W))
        val div_res_quo = Wire(UInt(SCR1_XLEN.W))
        val div_quo_bit = Wire(Bool())

        // вспомогательный сигнал для деления
        val div_cmd = Cat(
            cmd === SCR1_IALU_CMD_REM  || cmd === SCR1_IALU_CMD_REMU,
            cmd === SCR1_IALU_CMD_REMU || cmd === SCR1_IALU_CMD_DIVU
        )

        // div_cmd:
        // - знаковые ли операции
        // - проверка старших битов операндов для проверки знака
        // - является ли инструкция просто DIV (1) или одной из 3 других (0)
        // - является ли это операцией поиска остатка
        // - проверка корректности выполненной операции


        val div_ops_are_sgn = !div_cmd(0)
        val div_op1_is_neg = div_ops_are_sgn && op_1(SCR1_XLEN-1)
        val div_op2_is_neg = div_ops_are_sgn && op_2(SCR1_XLEN-1)

        val div_cmd_div = div_cmd === 0.U(2.W)
        val div_cmd_rem = div_cmd(1)

        val div_corr_req = div_cmd_div && main_ops_diff_sgn
        val rem_corr_req = div_cmd_rem && div_res_rem.orR && (div_op1_is_neg ^ div_res_rem_c)
        val mdu_corr_req = mdu_cmd_div && (div_corr_req || rem_corr_req)

        
        val mdu_iter_cnt = Reg(UInt(SCR1_XLEN.W))
        val mdu_iter_cnt_en = cmd_vd_i && !res_rdy_o
        val mdu_iter_req = mdu_cmd_is_iter && main_ops_non_zero && mdu_fsm_idle
        val mdu_iter_rdy = mdu_iter_cnt(0)

        val mdu_sum_sub = WireDefault(false.B)
        val mdu_sum_op1 = WireDefault(0.S(SCR1_MDU_SUM_WIDTH.W))
        val mdu_sum_op2 = WireDefault(0.S(SCR1_MDU_SUM_WIDTH.W))

        val mdu_sum_res = Mux(mdu_sum_sub, 
            mdu_sum_op1 - mdu_sum_op2,
            mdu_sum_op1 + mdu_sum_op2)

        // MDU intermediate results registers
        val mdu_res_c_ff = Reg(Bool())
        val mdu_res_hi_ff = Reg(UInt(SCR1_XLEN.W))
        val mdu_res_lo_ff = Reg(UInt(SCR1_XLEN.W))

        when(cmd_vd_i) {
            switch(mdu_fsm_ff) {
                is(SCR1_IALU_MDU_FSM_IDLE) {
                    mdu_fsm_next := Mux(mdu_iter_req, SCR1_IALU_MDU_FSM_ITER, SCR1_IALU_MDU_FSM_IDLE)
                }
                is(SCR1_IALU_MDU_FSM_ITER) {
                    mdu_fsm_next := Mux(!mdu_iter_rdy, SCR1_IALU_MDU_FSM_ITER,
                                    Mux(mdu_corr_req, SCR1_IALU_MDU_FSM_CORR, SCR1_IALU_MDU_FSM_IDLE))
                }
                is(SCR1_IALU_MDU_FSM_CORR) {
                    mdu_fsm_next := SCR1_IALU_MDU_FSM_IDLE
                }
            }
        }
        mdu_fsm_ff := mdu_fsm_next

        //-------------------------------------------------------------------------------
        // Multiplier logic
        //-------------------------------------------------------------------------------
        // Два бита: хотя бы один операнд Unsigned, обо операнда unsigned/signed
        val mul_cmd = Cat((cmd === SCR1_IALU_CMD_MULHU) || (cmd === SCR1_IALU_CMD_MULHSU), 
                          (cmd === SCR1_IALU_CMD_MULHU) || (cmd === SCR1_IALU_CMD_MULH))

        // нужно вернуть старшие биты
        val mul_cmd_hi     = mul_cmd.orR
        // знаковые ли операндаы и их знаки 
        val mul_op1_is_sgn = !(mul_cmd(1) && mul_cmd(0))  // ~&mul_cmd
        val mul_op2_is_sgn = !mul_cmd(1)
        val mul_op1_sgn    = mul_op1_is_sgn && op_1(SCR1_XLEN-1)
        val mul_op2_sgn    = mul_op2_is_sgn && op_2(SCR1_XLEN-1)


        val mulSignals = if (SCR1_FAST_MUL) {
            // FAST_MUL signals
            // операнды ненулевые только если команда - умножение 
            val mul_op1 = Mux(mdu_cmd_mul, Cat(mul_op1_sgn, op_1).asSInt, 0.S((SCR1_XLEN + 1).W))
            val mul_op2 = Mux(mdu_cmd_mul, Cat(mul_op2_sgn, op_2).asSInt, 0.S((SCR1_XLEN + 1).W))
            val mul_res = Mux(mdu_cmd_mul, 
                (mul_op1 * mul_op2), 
                0.S((SCR1_MUL_RES_WIDTH + 2).W))
            
            // результат заносится в поля класса 
            MulSignals(
                op1 = Some(mul_op1),
                op2 = Some(mul_op2), 
                res = Some(mul_res(SCR1_MUL_RES_WIDTH - 1, 0).asSInt)
            )
        } else {
            // ~FAST_MUL signals
            // mul_op1
            val mul_op1_slow = Mux(mdu_cmd_mul, Cat(mul_op1_sgn, op_1).asSInt, 0.S((SCR1_XLEN + 1).W))

            // mul_op2
            val mul_op2_slow = Mux(!mdu_cmd_mul, 0.S((SCR1_MUL_WIDTH + 1).W),
                        Mux(mdu_fsm_idle, 
                            Cat(0.U(1.W), op_2(SCR1_MUL_WIDTH-1, 0)).asSInt,
                            Cat(mdu_iter_cnt(0) && mul_op2_is_sgn && mdu_res_lo_ff(SCR1_MUL_WIDTH-1),
                                mdu_res_lo_ff(SCR1_MUL_WIDTH-1, 0)).asSInt))

            // mul_part_prod
            val mul_part_prod = Mux(mdu_cmd_mul, 
                (mul_op1_slow * mul_op2_slow).pad(SCR1_MUL_WIDTH), 
                0.S((SCR1_MDU_SUM_WIDTH + 1).W))

            // mul_res_hi and mul_res_lo
            val mul_res_combined = Mux(!mdu_cmd_mul, 0.U((2*SCR1_XLEN).W),
                                    Mux(mdu_fsm_idle,
                                        Cat(mdu_sum_res, op_2(SCR1_XLEN-1, SCR1_MUL_WIDTH)),
                                        Cat(mdu_sum_res, mdu_res_lo_ff(SCR1_XLEN-1, SCR1_MUL_WIDTH))))

            val mul_res_hi = mul_res_combined(2*SCR1_XLEN-1, SCR1_XLEN)
            val mul_res_lo = mul_res_combined(SCR1_XLEN-1, 0)

            MulSignals(
                op1 = Some(mul_op1_slow),
                op2 = Some(mul_op2_slow),
                partProd = Some(mul_part_prod),
                resHi = Some(mul_res_hi),
                resLo = Some(mul_res_lo)
            )
        }

        // MDU iteration counter
        //------------------------------------------------------------------------------
        

        if (SCR1_FAST_MUL) {
            // with FAST_MUL
            when(!mdu_fsm_idle) {
                mdu_iter_cnt_next := mdu_iter_cnt >> 1.U
            }.elsewhen(mdu_cmd_div) {
                mdu_iter_cnt_next := SCR1_DIV_CNT_INIT
            }.otherwise {
                mdu_iter_cnt_next := mdu_iter_cnt
            }
        } else {
            // without FAST_MUL
            when(!mdu_fsm_idle) {
                mdu_iter_cnt_next := mdu_iter_cnt >> 1.U
            }.elsewhen(mdu_cmd_div) {
                mdu_iter_cnt_next := SCR1_DIV_CNT_INIT
            }.elsewhen(mdu_cmd_mul) {
                mdu_iter_cnt_next := SCR1_MUL_CNT_INIT
            }.otherwise {
                mdu_iter_cnt_next := mdu_iter_cnt
            }
        }
        
        when(mdu_iter_cnt_en) {
            mdu_iter_cnt := mdu_iter_cnt_next
        }

        

        // Dividend low part register
        //------------------------------------------------------------------------------
        val div_dvdnd_lo_upd = cmd_vd_i && !res_rdy_o
        val div_dvdnd_lo_ff   = Reg(UInt(SCR1_XLEN.W))
        val div_dvdnd_lo_next = Mux(!mdu_cmd_div || mdu_fsm_corr, 0.U,
                                Mux(mdu_fsm_idle, op_1 << 1.U,
                                                div_dvdnd_lo_ff << 1.U))
        
        div_res_rem_c := false.B
        div_res_rem := 0.U
        div_res_quo := 0.U
        div_quo_bit := false.B

        when(div_dvdnd_lo_upd) {
            div_dvdnd_lo_ff := div_dvdnd_lo_next
        }

        when(mdu_cmd_div && !mdu_fsm_corr) {
            div_res_rem_c := mdu_sum_res(SCR1_MDU_SUM_WIDTH-1)
            div_res_rem   := mdu_sum_res(SCR1_MDU_SUM_WIDTH-2, 0).asUInt(SCR1_XLEN-1, 0)
            
            val rem_zero = (Cat(mdu_sum_res, div_dvdnd_lo_next) === 0.U)
            div_quo_bit := !(div_op1_is_neg ^ div_res_rem_c) || 
                        (div_op1_is_neg && rem_zero)
            
            div_res_quo := Mux(mdu_fsm_idle,
                Cat(0.U((SCR1_XLEN-1).W), div_quo_bit),  
                Cat(mdu_res_lo_ff(SCR1_XLEN-2, 0), div_quo_bit)) 
        }

        //-------------------------------------------------------------------------------
        // MDU adder
        //-------------------------------------------------------------------------------
        

        switch(mdu_cmd) {
            is(SCR1_IALU_MDU_DIV) {
                val sgn = Mux(mdu_fsm_corr, div_op1_is_neg ^ mdu_res_c_ff,
                        Mux(mdu_fsm_idle, false.B,
                                        !mdu_res_lo_ff(0)))
                
                val inv = div_ops_are_sgn && main_ops_diff_sgn
                mdu_sum_sub := !inv ^ sgn
                
                mdu_sum_op1 := Mux(mdu_fsm_corr, Cat(0.U(1.W), mdu_res_hi_ff).asSInt,
                               Mux(mdu_fsm_idle, Cat(div_op1_is_neg, op_1(SCR1_XLEN-1)).asSInt,
                                                 Cat(mdu_res_hi_ff, div_dvdnd_lo_ff(SCR1_XLEN-1)).asSInt))
                
                mdu_sum_op2 := Cat(div_op2_is_neg, op_2).asSInt
            }
            
            is(SCR1_IALU_MDU_MUL) {
            if (!SCR1_FAST_MUL) {
                    mdu_sum_op1 := Mux(mdu_fsm_idle, 0.S,
                                   Cat(mul_op1_is_sgn && mdu_res_hi_ff(SCR1_XLEN-1), mdu_res_hi_ff).asSInt)
                    mdu_sum_op2 := mulSignals.partProd.getOrElse(0.S((SCR1_MDU_SUM_WIDTH + 1).W)).asSInt
                } else{
                    mdu_sum_op1 := 0.S(SCR1_MDU_SUM_WIDTH.W)
                    mdu_sum_op2 := 0.S(SCR1_MDU_SUM_WIDTH.W)
                }
            }
        }


        val mdu_res_upd = cmd_vd_i && !res_rdy_o
        val mdu_res_c_next = Mux(mdu_cmd_div, div_res_rem_c, mdu_res_c_ff)
        
        // Get multiplier signals with getOrElse
        val mul_res_hi_used = mulSignals.resHi.getOrElse(mdu_res_hi_ff)
        val mul_res_lo_used = mulSignals.resLo.getOrElse(mdu_res_lo_ff)

        // For FAST_MUL extract hi/lo from full result
        val (mul_res_hi, mul_res_lo) = if (SCR1_FAST_MUL) {
            val full_res = mulSignals.res.getOrElse(0.S(SCR1_MUL_RES_WIDTH.W))
            val hi = full_res(SCR1_MUL_RES_WIDTH-1, SCR1_XLEN).asUInt
            val lo = full_res(SCR1_XLEN-1, 0).asUInt
            (hi, lo)
        } else {
            (mul_res_hi_used, mul_res_lo_used)
        }

        val mdu_res_hi_next = Mux(mdu_cmd_div, div_res_rem,
                            Mux(mdu_cmd_mul, mul_res_hi, mdu_res_hi_ff))

        val mdu_res_lo_next = Mux(mdu_cmd_div, div_res_quo,
                            Mux(mdu_cmd_mul, mul_res_lo, mdu_res_lo_ff))
        
        when(mdu_res_upd) {
            mdu_res_c_ff := mdu_res_c_next
            mdu_res_hi_ff := mdu_res_hi_next
            mdu_res_lo_ff := mdu_res_lo_next
        }

        //-------------------------------------------------------------------------------
        // Result formation
        //-------------------------------------------------------------------------------
        switch(cmd) {
            is(SCR1_IALU_CMD_MUL, SCR1_IALU_CMD_MULHU, 
               SCR1_IALU_CMD_MULHSU, SCR1_IALU_CMD_MULH) {
                
                if (SCR1_FAST_MUL) {
                    result := Mux(mul_cmd_hi,
                        (mulSignals.res.getOrElse(0.S))(SCR1_MUL_RES_WIDTH-1, SCR1_XLEN).asSInt,
                        (mulSignals.res.getOrElse(0.S))(SCR1_XLEN-1, 0).asSInt)
                    res_rdy_o := true.B

                } else {
                    switch(mdu_fsm_ff) {
                        is(IDLE) { result := 0.S; res_rdy_o := !mdu_iter_req }
                        is(ITER) { 
                            result := Mux(mul_cmd_hi,
                                mulSignals.resHi.map(_.asSInt).getOrElse(0.S),
                                mulSignals.resLo.map(_.asSInt).getOrElse(0.S))
                            res_rdy_o := mdu_iter_rdy
                        }
                    }
                }
            }
            
            is(SCR1_IALU_CMD_DIV, SCR1_IALU_CMD_DIVU,
               SCR1_IALU_CMD_REM, SCR1_IALU_CMD_REMU) {
                
                switch(mdu_fsm_ff) {
                    is(IDLE) {
                        result := Mux(op_2.orR || div_cmd_rem, op_1.asSInt, (-1).S)
                        res_rdy_o := !mdu_iter_req
                    }
                    is(ITER) {
                        result := Mux(div_cmd_rem, div_res_rem.asSInt, div_res_quo.asSInt)
                        res_rdy_o := mdu_iter_rdy && !mdu_corr_req
                    }
                    is(CORR) {
                        result := Mux(div_cmd_rem,
                            mdu_sum_res(SCR1_XLEN-1, 0).asSInt,
                            -mdu_res_lo_ff(SCR1_XLEN-1, 0).asSInt)
                        res_rdy_o := true.B
                    }
                }
            }
        }

        (result, res_rdy_o)
    
    }} //end of RVM fun and "}" for withClockandReset

    def notRVMCommands(
        op_1: SInt,
        op_2: SInt,
        cmd: UInt,
        shiftAmount: UInt
    ): (SInt, Bool) = { 
        val result = WireDefault(0.S(SCR1_XLEN.W))
        val cmp_res = WireDefault(false.B)

        switch(cmd) {
            is(SCR1_IALU_CMD_NONE) { result := 0.S }
            is(SCR1_IALU_CMD_AND)  { result := op_1 & op_2 }
            is(SCR1_IALU_CMD_OR)   { result := op_1 | op_2 }
            is(SCR1_IALU_CMD_XOR)  { result := op_1 ^ op_2 }

            is(SCR1_IALU_CMD_SLL)  { result := op_1 << shiftAmount }
            is(SCR1_IALU_CMD_SRL)  { result := (op_1.asUInt >> shiftAmount).asSInt }
            is(SCR1_IALU_CMD_SRA)  { result := op_1 >> shiftAmount }

            is(SCR1_IALU_CMD_ADD)  { result := add_main(cmd, op_1, op_2) }  
            is(SCR1_IALU_CMD_SUB)  { result := add_main(cmd, op_1, op_2) }  
            
            is(SCR1_IALU_CMD_SUB_LT)  { result  := Cat(0.U((SCR1_XLEN - 1).W), flags.sign ^ flags.overflow).asSInt
                                        cmp_res := flags.sign ^ flags.overflow}  
            is(SCR1_IALU_CMD_SUB_LTU) { result := Cat(0.U((SCR1_XLEN - 1).W), flags.carry).asSInt
                                        cmp_res := flags.carry }   
            is(SCR1_IALU_CMD_SUB_EQ)  { result := Cat(0.U((SCR1_XLEN - 1).W), flags.zero ).asSInt
                                        cmp_res := flags.zero }  
            is(SCR1_IALU_CMD_SUB_NE)  { result := Cat(0.U((SCR1_XLEN - 1).W), ~flags.zero).asSInt
                                        cmp_res := ~flags.zero }  
            is(SCR1_IALU_CMD_SUB_GE)  { result := Cat(0.U((SCR1_XLEN - 1).W), ~(flags.sign ^ flags.overflow)).asSInt
                                        cmp_res := ~(flags.sign ^ flags.overflow) }  
            is(SCR1_IALU_CMD_SUB_GEU) { result := Cat(0.U((SCR1_XLEN - 1).W), ~flags.carry ).asSInt
                                        cmp_res := ~flags.carry }
        } 

        (result, cmp_res)
    }


    def mainAdderMux(
    op_1: SInt,
    op_2: SInt,
    cmd: UInt,
    // RVM extention
    exu2ialu_rvm_cmd_vd_i: Option[Bool] = None,
    clock: Option[Clock] = None,
    rst_n: Option[Bool] = None

    ): (SInt, Bool, Bool) = {
        val result = WireDefault(0.S(SCR1_XLEN.W))
        val shiftAmount = op_2(4, 0).asUInt
        
        val res_rdy_o = WireDefault(false.B)
        val cmp_res = WireDefault(false.B)

        val isRvmCmd = cmd === SCR1_IALU_CMD_MUL || cmd === SCR1_IALU_CMD_MULHU ||
                       cmd === SCR1_IALU_CMD_MULHSU || cmd === SCR1_IALU_CMD_MULH ||
                       cmd === SCR1_IALU_CMD_DIV || cmd === SCR1_IALU_CMD_DIVU ||
                       cmd === SCR1_IALU_CMD_REM || cmd === SCR1_IALU_CMD_REMU


        if (SCR1_RVM_EXT) {
            // RVM команды при включенном расширении
            val cmd_vd = exu2ialu_rvm_cmd_vd_i.getOrElse(false.B)
            val clk = clock.getOrElse(throw new Exception("Clock required for RVM operations"))
            val rst = rst_n.getOrElse(false.B)
            
            val (rvm_result, rdy) = RVM_ext_part(
            op_1.asUInt,
            op_2.asUInt,
            cmd,
            cmd_vd,
            clk,
            rst
            )

            when(isRvmCmd){
                result := rvm_result
                res_rdy_o := rdy
            } otherwise
            {
                val (nonRvmResult, nonRvmCmp) = notRVMCommands(op_1, op_2, cmd, shiftAmount)
            result := nonRvmResult
            cmp_res := nonRvmCmp
            }
            }
        else { 
            val (nonRvmResult, nonRvmCmp) = notRVMCommands(op_1, op_2, cmd, shiftAmount)
            result := nonRvmResult
            cmp_res := nonRvmCmp
        }

        (result, cmp_res, res_rdy_o)
    }
}