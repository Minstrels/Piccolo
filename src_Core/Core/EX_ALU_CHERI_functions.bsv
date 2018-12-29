// Copyright (c) 2016-2018 Bluespec, Inc. All Rights Reserved

//-
// RVFI_DII modifications:
//     Copyright (c) 2018 Jack Deeley
//     Copyright (c) 2018 Peter Rugg
//     All rights reserved.
//
//     This software was developed by SRI International and the University of
//     Cambridge Computer Laboratory (Department of Computer Science and
//     Technology) under DARPA contract HR0011-18-C-0016 ("ECATS"), as part of the
//     DARPA SSITH research programme.
//-

package EX_ALU_CHERI_functions;
// This file is largely duplicated and/or derived from EX_ALU_functions.bsv, but with adaptation for the
// use of capability-mode behaviour and tagged capability values.

// ================================================================
// These are the "ALU" functions in the EX stage of the "Piccolo" CPU.
// EX stands for "Execution".

// ================================================================
// Exports

export
ALU_Inputs (..),
ALU_Outputs (..),
fv_ALU;

// ================================================================
// BSV library imports

// None

// ----------------
// BSV additional libs

// None

// ================================================================
// Project imports

import ISA_Decls   :: *;
import CPU_Globals :: *;

// TODO: Which fields definitely need to be capabilities/tagged_capabilities?
//       Do we need anything from PCC?

// ================================================================
// ALU inputs

typedef struct {
   Priv_Mode            cur_priv;
   Tagged_Capability    pcc;
   Instr                instr;
   Decoded_Instr        decoded_instr;
   Bool                 cap_mode;
   Tagged_Capability    rs1_val;
   Tagged_Capability    rs2_val;
   Bool                 csr_valid;
   WordXL               csr_val;
   // We read and write capability CSRs through separate channels to base CSRs
   Tagged_Capability    ccsr_val;
   WordXL               mstatus;
   MISA                 misa;
   } ALU_Inputs
deriving (Bits, FShow);

// ================================================================
// ALU outputs

typedef struct {
   Control              control;
   Exc_Code             exc_code;        // Relevant if control == CONTROL_TRAP

   Op_Stage2            op_stage2;
   RegName              rd;
   Bool                 csr_valid;
   Bool                 cap_mode;
   Tagged_Capability    addr;       // Branch, jump: newPC
                                    // Mem ops and AMOs: mem addr
                                    // CSRRx: csr addr

   Tagged_Capability    val1;   // OP_Stage2_ALU: result for Rd (ALU ops: result, JAL/JALR: return PC,
                                //                           CSSRx: old value of CSR)
                                // OP_Stage2_M, OP_Stage2_FD: arg1
                                // OP_Stage2_AMO: funct7

   Tagged_Capability    val2;   // Branch: branch target (for Tandem Verification)
                                // OP_Stage2_ST: store-val
                                // OP_Stage2_M, OP_Stage2_FD: arg2
                                // CSSRx: new csr value
   } ALU_Outputs
deriving (Bits, FShow);

ALU_Outputs alu_outputs_base = ALU_Outputs {control:   CONTROL_STRAIGHT,
					    exc_code:  exc_code_ILLEGAL_INSTRUCTION,
					    op_stage2: ?,
					    // Wolf's verification model requires rd to be 0 for non-updating
					    // At the moment we check this later in the sequence.
					    rd:        ?,
					    csr_valid: False,
                        cap_mode:  False,
					    addr:      ?,
					    val1:      ?,
					    val2:      ? };

// ================================================================

// ----------------------------------------------------------------
/* TODO: DELETE? 'factor' RegFile for shift ops

// ----------------------------------------------------------------
// The following is a lookup table of multiplication factors used by the "shift" ops
RegFile #(Bit #(TLog #(XLEN)), Bit #(XLEN))  rf_sh_factors <- mkRegFileFull;
// The following is used during reset to initialize rf_sh_factors
Reg #(Bool)                                  rg_resetting  <- mkReg (False);
Reg #(Bit #(TAdd #(1, TLog #(XLEN))))        rg_j          <- mkRegU;
Reg #(WordXL)                                rg_factor     <- mkRegU;
*/

// ----------------------------------------------------------------
// The following functions implement the 'shift' operators SHL, SHRL and SHRA
// using multiplication instead of actual shifts,
// thus using DSPs (multiplication) and LUTRAMs (rf_sh_factors) instead of LUTs

// Shift-left
// Instead of '>>' operator, uses '*', using DSPs instead of LUTs.
// To SHL(n), do a multiplication by 2^n.
// The 2^n factor is looked up in a RegFile (used as a ROM), which uses a LUTRAM instead of LUTs
function WordXL fn_shl (WordXL x, Bit #(TLog #(XLEN)) shamt);
   IntXL  x_signed = unpack (x);

   // IntXL y_signed = unpack (rf_sh_factors.sub (shamt));
   IntXL  y_signed = unpack ('b1 << shamt);

   IntXL  z_signed = x_signed * y_signed;
   WordXL z        = pack (z_signed);
   return z;
endfunction

// Shift-right-arithmetic
// Instead of '>>' operator, uses '*', using DSPs instead of LUTs
// To SHR(n), do a 2*XLEN-wide multiplication by 2^(32-n), and take upper XLEN bits
// The 2^(32-n) factor is looked up in a RegFile (used as a ROM), which uses a LUTRAM instead of LUTs
function WordXL fn_shra (WordXL x, Bit #(TLog #(XLEN)) shamt);
   // Bit #(TAdd #(1, XLEN)) y = { reverseBits (rf_sh_factors.sub (shamt)), 1'b0 };
   Bit #(TAdd #(1, XLEN)) y = { reverseBits ('b1 << shamt), 1'b0 };

   Int #(XLEN_2) xx_signed = extend (unpack (x));
   Int #(XLEN_2) yy_signed = unpack (extend (y));
   Int #(XLEN_2) zz_signed = xx_signed * yy_signed;
   Bit #(XLEN_2) zz        = pack (zz_signed);
   WordXL        z         = truncateLSB (zz);
   return z;
endfunction

// Shift-right-logical
// Instead of '>>' operator, uses '*', using DSPs instead of LUTs
// To SHR(n), do a 2*XLEN-wide multiplication by 2^(32-n), and take upper XLEN bits
// The 2^(32-n) factor is looked up in a RegFile (used as a ROM), which uses a LUTRAM instead of LUTs
function WordXL fn_shrl (WordXL x, Bit #(TLog #(XLEN)) shamt);
   // Bit #(TAdd #(1, XLEN)) y = { reverseBits (rf_sh_factors.sub (shamt)), 1'b0 };
   Bit #(TAdd #(1, XLEN)) y = { reverseBits ('b1 << shamt), 1'b0 };

   Bit #(XLEN_2) xx = extend (x);
   Bit #(XLEN_2) yy = extend (y);
   Bit #(XLEN_2) zz = xx * yy;
   WordXL        z  = truncateLSB (zz);
   return z;
endfunction

// ----------------------------------------------------------------
// Top-level ALU function

function ALU_Outputs fv_ALU (ALU_Inputs inputs);
   let alu_outputs = alu_outputs_base;

   if (inputs.decoded_instr.opcode == op_BRANCH)
      alu_outputs = fv_BRANCH (inputs);           // IN-PROGRESS

   else if (inputs.decoded_instr.opcode == op_JAL)
      alu_outputs = fv_JAL (inputs);

   else if (inputs.decoded_instr.opcode == op_JALR)
      alu_outputs = fv_JALR (inputs);

`ifdef ISA_M
   // TODO: CHERI ops for M extension?

   // OP 'M' ops MUL/ MULH/ MULHSU/ MULHU/ DIV/ DIVU/ REM/ REMU
   else if (   (inputs.decoded_instr.opcode == op_OP)
	    && f7_is_OP_MUL_DIV_REM (inputs.decoded_instr.funct7))
      begin
	 // Will be executed in MBox in next stage
	 alu_outputs.op_stage2 = OP_Stage2_M;
	 alu_outputs.rd        = inputs.decoded_instr.rd;
	 alu_outputs.val1      = inputs.rs1_val;
	 alu_outputs.val2      = inputs.rs2_val;
      end

`ifdef RV64
   // OP 'M' ops MULW/ DIVW/ DIVUW/ REMW/ REMUW
   else if (   (inputs.decoded_instr.opcode == op_OP_32)
	    && f7_is_OP_MUL_DIV_REM (inputs.decoded_instr.funct7))
      begin
	 // Will be executed in MBox in next stage
	 alu_outputs.op_stage2 = OP_Stage2_M;
	 alu_outputs.rd        = inputs.decoded_instr.rd;
	 alu_outputs.val1      = inputs.rs1_val;
	 alu_outputs.val2      = inputs.rs2_val;
      end
`endif
`endif

   // OP_IMM and OP (shifts)
   else if (   (   (inputs.decoded_instr.opcode == op_OP_IMM)
		|| (inputs.decoded_instr.opcode == op_OP))
	    && (   (inputs.decoded_instr.funct3 == f3_SLLI)
		|| (inputs.decoded_instr.funct3 == f3_SRLI)
		|| (inputs.decoded_instr.funct3 == f3_SRAI)))
      alu_outputs = fv_OP_and_OP_IMM_shifts (inputs);

   // TODO: set up floating point ops for next stage, similar to 'M' setup

   // Remaining OP_IMM and OP (excluding shifts and 'M' ops MUL/DIV/REM)
   else if (   (inputs.decoded_instr.opcode == op_OP_IMM)
	    || (inputs.decoded_instr.opcode == op_OP))
      alu_outputs = fv_OP_and_OP_IMM (inputs);

`ifdef RV64
   else if (inputs.decoded_instr.opcode == op_OP_IMM_32)
      alu_outputs = fv_OP_IMM_32 (inputs);

   // Remaining op_OP_32 (excluding 'M' ops)
   else if (inputs.decoded_instr.opcode == op_OP_32)
      alu_outputs = fv_OP_32 (inputs);
`endif

   else if (inputs.decoded_instr.opcode == op_LUI)
      alu_outputs = fv_LUI (inputs);

   else if (inputs.decoded_instr.opcode == op_AUIPC)
      alu_outputs = fv_AUIPC (inputs);

   else if (inputs.decoded_instr.opcode == op_LOAD)
      alu_outputs = fv_LD (inputs);

   else if (inputs.decoded_instr.opcode == op_STORE)
      alu_outputs = fv_ST (inputs);

   else if (inputs.decoded_instr.opcode == op_MISC_MEM)
      alu_outputs = fv_MISC_MEM (inputs);

   else if (inputs.decoded_instr.opcode == op_SYSTEM)
      alu_outputs = fv_SYSTEM (inputs);

`ifdef ISA_A
   else if (inputs.decoded_instr.opcode == op_AMO)
      alu_outputs = fv_AMO (inputs);
`endif

`ifdef ISA_FD
   // All these just set up for the next stage (Mem box, or FBox)
   // TODO: op_LOAD_FP, op_STORE_FP
   // TODO: op_FP: all the floating-point ops
   // TODO: op_FM_ADD_SUB
   // TODO: op_FNM_ADD_SUB
`endif

    else if (inputs.decoded_instr.opcode == op_CAP)
        alu_outputs = fv_CHERI (inputs);
    
    // Currently only using 0x5b opcode
    //else if (inputs.decoded_instr.opcode == op_CAPLOAD)
        //alu_outputs = fv_CHERILOAD (inputs);

   else begin
      alu_outputs.control = CONTROL_TRAP;
   end

   return alu_outputs;
endfunction

// ----------------------------------------------------------------
// BRANCH

function ALU_Outputs fv_BRANCH (ALU_Inputs inputs);
    let alu_outputs = alu_outputs_base;
    alu_outputs.rd        = 0;
    alu_outputs.exc_code  = exc_code_INSTR_ADDR_MISALIGNED;
    alu_outputs.op_stage2 = OP_Stage2_ALU;
    Bool  branch_taken  = False;
    Bool  trap          = False;
    Addr  branch_target = pack (unpack(cap_addr(inputs.pcc.capability)) + offset);
    
    // TODO: Does capability-mode comparison compare the entire value, or just the 
    //       address/value part as usual? If not, how does ordering work?
    let rs1_val = cap_addr(inputs.rs1_val.capability);
    let rs2_val = cap_addr(inputs.rs2_val.capability);
    IntXL s_rs1_val = unpack (rs1_val);
    IntXL s_rs2_val = unpack (rs2_val);
    IntXL offset        = extend (unpack (inputs.decoded_instr.imm13_SB));
    let funct3 = inputs.decoded_instr.funct3;
    if inputs.cap_mode begin
        let rs1_tag = inputs.rs1_val.tag;
        let rs2_tag = inputs.rs2_val.tag;
        if      (funct3 == f3_BEQ)  branch_taken = ((rs1_tag == rs2_tag)  && (rs1_val == rs2_val));
        else if (funct3 == f3_BNE)  branch_taken = ((rs1_tag != rs2_tag)  || (rs1_val != rs2_val));
        else if (funct3 == f3_BLT)  branch_taken = 
            // Tag ordering           ... or both same tag and values ordered
            ((!rs1_tag && rs2_tag) || (rs1_tag == rs2_tag && s_rs1_val < s_rs2_val));
        else if (funct3 == f3_BGE)  branch_taken = 
            // Greater-or-equal is just the negation of less-than. Checking the other cases
            !((rs1_tag && !rs2_tag) || (rs1_tag == rs2_tag && s_rs1_val < s_rs2_val));
        else if (funct3 == f3_BLTU)  branch_taken = 
            ((!rs1_tag && rs2_tag) || (rs1_tag == rs2_tag && rs1_val < rs2_val));
        else if (funct3 == f3_BGEU)  branch_taken = 
            !((rs1_tag && !rs2_tag) || (rs1_tag == rs2_tag && rs1_val < rs2_val));
        else begin
            trap = True;
            alu_outputs.exc_code = exc_code_ILLEGAL_INSTRUCTION;
        end
    end else begin
        // Signed versions of rs1_val and rs2_val
        if      (funct3 == f3_BEQ)  branch_taken = (rs1_val == rs2_val);
        else if (funct3 == f3_BNE)  branch_taken = (rs1_val != rs2_val);
        else if (funct3 == f3_BLT)  branch_taken = (s_rs1_val < s_rs2_val);
        else if (funct3 == f3_BGE)  branch_taken = (s_rs1_val >= s_rs2_val);
        else if (funct3 == f3_BLTU) branch_taken = (rs1_val < rs2_val);
        else if (funct3 == f3_BGEU) branch_taken = (rs1_val >= rs2_val);
        else begin
            trap = True;
            alu_outputs.exc_code = exc_code_ILLEGAL_INSTRUCTION;
        end
    end
    // TODO: Should we check the LSB here? Need [1:0] == 0 to ensure 4-byte alignment.
    // TODO: Confirm - we simply change the address in PCC for the branch target?
    trap = (trap || (branch_taken && (branch_target [1] == 1'b1)));
    Addr new_pc = branch_taken ? branch_target : (cap_addr(inputs.pcc.capability) + 4);
    alu_outputs.addr = change_tagged_addr(inputs.pcc, new_pc);
    alu_outputs.control   = (trap ? CONTROL_TRAP : (branch_taken ? CONTROL_BRANCH : CONTROL_STRAIGHT));
    // Gives a defined value when in verification mode.
    alu_outputs.val2      = change_tagged_addr(inputs.pcc, branch_target);    // For tandem verifier only
    `ifdef RVFI
    alu_outputs.val1      = 0;
    `endif
    return alu_outputs;
endfunction

// ----------------------------------------------------------------
// JAL

function ALU_Outputs fv_JAL (ALU_Inputs inputs);
   IntXL offset  = extend (unpack (inputs.decoded_instr.imm21_UJ));
   Addr  next_pc = pack (unpack(cap_addr(inputs.pcc.capability)) + offset);
   Addr  ret_pc  = cap_addr(inputs.pcc.capability) + 4;

   // nsharma: 2017-05-26 Bug fix
   // nsharma: next_pc[0] should be cleared for JAL/JALR
   // riscv-spec-v2.2. Secn 2.5. Page 16
   next_pc[0] = 1'b0;

   let alu_outputs = alu_outputs_base;
   alu_outputs.control   = ((next_pc [1] == 1'b0) ? CONTROL_BRANCH : CONTROL_TRAP);
   alu_outputs.exc_code  = exc_code_INSTR_ADDR_MISALIGNED;
   alu_outputs.op_stage2 = OP_Stage2_ALU;
   alu_outputs.rd        = inputs.decoded_instr.rd;
   alu_outputs.addr      = change_tagged_addr(inputs.pcc, next_pc);
   alu_outputs.val1      = change_tagged_addr(inputs.pcc, ret_pc);

   return alu_outputs;
endfunction

// ----------------------------------------------------------------
// JALR


function ALU_Outputs fv_JALR (ALU_Inputs inputs);
   let rs1_val = cap_addr(inputs.rs1_val.capability);

   // Signed versions of rs1_val and rs2_val
   IntXL s_rs1_val = unpack (rs1_val);
   IntXL offset    = extend (unpack (inputs.decoded_instr.imm12_I));
   Addr  next_pc   = pack (s_rs1_val + offset);
   Addr  ret_pc    = inputs.pc + 4;

   // nsharma: 2017-05-26 Bug fix
   // nsharma: next_pc[0] should be cleared for JAL/JALR
   // riscv-spec-v2.2. Secn 2.5. Page 16
   next_pc[0] = 1'b0;

   let alu_outputs = alu_outputs_base;
   alu_outputs.control   = ((next_pc [1] == 1'b0) ? CONTROL_BRANCH : CONTROL_TRAP);
   alu_outputs.exc_code  = exc_code_INSTR_ADDR_MISALIGNED;
   alu_outputs.op_stage2 = OP_Stage2_ALU;
   alu_outputs.rd        = inputs.decoded_instr.rd;
   alu_outputs.addr      = change_tagged_addr(inputs.pcc, next_pc);
   alu_outputs.val1      = change_tagged_addr(inputs.pcc, ret_pc);

   return alu_outputs;
endfunction

// ----------------------------------------------------------------
// Integer Register-Register and Register-Immediate Instructions

// ----------------
// Shifts (funct3 == f3_SLLI/ f3_SRLI/ f3_SRAI)

function ALU_Outputs fv_OP_and_OP_IMM_shifts (ALU_Inputs inputs);
   let rs1_val = cap_addr(inputs.rs1_val.capability);
   let rs2_val = cap_addr(inputs.rs2_val.capability);

   IntXL s_rs1_val = unpack (rs1_val);    // Signed version of rs1, for SRA

   Bit #(TLog #(XLEN)) shamt = (  (inputs.decoded_instr.opcode == op_OP_IMM)
				? truncate (inputs.decoded_instr.imm12_I)
				: truncate (rs2_val));
   WordXL   rd_val    = ?;
   let      funct3    = inputs.decoded_instr.funct3;
   Bit #(1) instr_b30 = inputs.instr [30];

`ifdef SHIFT_BARREL
   // Shifts implemented by Verilog synthesis,
   // mapping to barrel shifters
   if (funct3 == f3_SLLI)
      rd_val = (rs1_val << shamt);
   else begin // assert: (funct3 == f3_SRxI)
      if (instr_b30 == 1'b0)
	 // SRL/SRLI
	 rd_val = (rs1_val >> shamt);
      else
	 // SRA/SRAI
	 rd_val = pack (s_rs1_val >> shamt);
   end
`endif

`ifdef SHIFT_MULT
   // Shifts implemented using multiplication by 2^shamt,
   // mapping to DSPs in FPGA
   if (funct3 == f3_SLLI)
      rd_val = fn_shl (rs1_val, shamt);  // in LUTRAMs/DSPs
   else begin // assert: (funct3 == f3_SRxI)
      if (instr_b30 == 1'b0) begin
	 // SRL/SRLI
	 rd_val = fn_shrl (rs1_val, shamt);  // in LUTRAMs/DSPs
      else
	 // SRA/SRAI
	 rd_val = fn_shra (rs1_val, shamt);     // in LUTRAMs/DSPs
   end
`endif

   // Trap in RV32 if shamt > 31, i.e., if imm12_I [5] is 1
   Bool trap = ((rv_version == RV32) && (inputs.decoded_instr.imm12_I [5] == 1));

   let alu_outputs       = alu_outputs_base;
   alu_outputs.control   = (trap ? CONTROL_TRAP : CONTROL_STRAIGHT);
   alu_outputs.rd        = inputs.decoded_instr.rd;

`ifndef SHIFT_SERIAL
   alu_outputs.op_stage2 = OP_Stage2_ALU;
   alu_outputs.val1      = change_tagged_addr(tc_zero, rd_val);
`else
   // Will be executed in serial Shifter_Box later
   alu_outputs.op_stage2 = OP_Stage2_SH;
   alu_outputs.val1      = change_tagged_addr(tc_zero, rs1_val);
   // Encode 'arith-shift' in bit [7] of val2
   WordXL val2 = extend (shamt);
   val2 = (val2 | { 0, instr_b30, 7'b0});
   alu_outputs.val2 = change_tagged_addr(tc_zero, val2);
`endif

   return alu_outputs;
endfunction: fv_OP_and_OP_IMM_shifts

// ----------------
// Remaining OP and OP_IMM (excluding shifts, M ops MUL/DIV/REM)

function ALU_Outputs fv_OP_and_OP_IMM (ALU_Inputs inputs);
   let rs1_val = cap_addr(inputs.rs1_val.capability);
   let rs2_val = cap_addr(inputs.rs2_val.capability);

   // Signed versions of rs1_val and rs2_val
   IntXL  s_rs1_val = unpack (rs1_val);
   IntXL  s_rs2_val = unpack (rs2_val);

   IntXL  s_rs2_val_local = s_rs2_val;
   WordXL rs2_val_local   = rs2_val;

   Bit #(1) instr_b30  = inputs.instr [30];
   Bool     subtract   = ((inputs.decoded_instr.opcode == op_OP) && (instr_b30 == 1'b1));

   if (inputs.decoded_instr.opcode == op_OP_IMM) begin
      s_rs2_val_local = extend (unpack (inputs.decoded_instr.imm12_I));
      rs2_val_local   = pack (s_rs2_val_local);
   end

   let  funct3 = inputs.decoded_instr.funct3;
   Bool trap   = False;
   WordXL rd_val = ?;

   if      ((funct3 == f3_ADDI) && (! subtract)) rd_val = pack (s_rs1_val + s_rs2_val_local);
   else if ((funct3 == f3_ADDI) && (subtract))   rd_val = pack (s_rs1_val - s_rs2_val_local);

   else if (funct3 == f3_SLTI)  rd_val = ((s_rs1_val < s_rs2_val_local) ? 1 : 0);
   else if (funct3 == f3_SLTIU) rd_val = ((rs1_val  < rs2_val_local)  ? 1 : 0);
   else if (funct3 == f3_XORI)  rd_val = pack (s_rs1_val ^ s_rs2_val_local);
   else if (funct3 == f3_ORI)   rd_val = pack (s_rs1_val | s_rs2_val_local);
   else if (funct3 == f3_ANDI)  rd_val = pack (s_rs1_val & s_rs2_val_local);
   else
      trap = True;

   let alu_outputs       = alu_outputs_base;
   alu_outputs.control   = (trap ? CONTROL_TRAP : CONTROL_STRAIGHT);
   alu_outputs.op_stage2 = OP_Stage2_ALU;
   alu_outputs.rd        = inputs.decoded_instr.rd;
   alu_outputs.val1      = change_tagged_addr(tc_zero, rd_val);

   return alu_outputs;
endfunction: fv_OP_and_OP_IMM

// ----------------
// OP_IMM_32 (ADDIW, SLLIW, SRxIW)

function ALU_Outputs fv_OP_IMM_32 (ALU_Inputs inputs);
   WordXL   rs1_val     = cap_addr(inputs.rs1_val.capability);
   IntXL    s_rs1_val   = unpack (rs1_val);

   Bit #(5) shamt       = truncate (inputs.decoded_instr.imm12_I);
   Bool     shamt5_is_0 = (inputs.instr [25] == 1'b0);

   let    funct3 = inputs.decoded_instr.funct3;
   Bool   trap   = False;
   WordXL rd_val = ?;

   if (funct3 == f3_ADDIW) begin
      IntXL  s_rs2_val = extend (unpack (inputs.decoded_instr.imm12_I));
      IntXL  sum       = s_rs1_val + s_rs2_val;
      WordXL tmp       = pack (sum);
      rd_val           = signExtend (tmp [31:0]);
   end
   else if ((funct3 == f3_SLLIW) && shamt5_is_0) begin
      Bit #(32) tmp = truncate (rs1_val);
      rd_val = signExtend (tmp << shamt);
   end
   else if ((funct3 == f3_SRxIW) && shamt5_is_0) begin
      Bit #(1) instr_b30 = inputs.instr [30];
      if (instr_b30 == 1'b0) begin
	 // SRLIW
	 Bit #(32) tmp = truncate (rs1_val);
	 rd_val = signExtend (tmp >> shamt);
      end
      else begin
	 // SRAIW
	 Int #(32) s_tmp = unpack (rs1_val [31:0]);
	 Bit #(32) tmp   = pack (s_tmp >> shamt);
	 rd_val = signExtend (tmp);
      end
   end
   else
      trap = True;

   let alu_outputs       = alu_outputs_base;
   alu_outputs.control   = (trap ? CONTROL_TRAP : CONTROL_STRAIGHT);
   alu_outputs.op_stage2 = OP_Stage2_ALU;
   alu_outputs.rd        = inputs.decoded_instr.rd;
   alu_outputs.val1      = change_tagged_addr(tc_zero, rd_val);

   return alu_outputs;
endfunction: fv_OP_IMM_32

// ----------------
// OP_32 (excluding 'M' ops: MULW/ DIVW/ DIVUW/ REMW/ REMUW)

function ALU_Outputs fv_OP_32 (ALU_Inputs inputs);
   Bit #(32) rs1_val = cap_addr(inputs.rs1_val.capability)[31:0];
   Bit #(32) rs2_val = cap_addr(inputs.rs2_val.capability)[31:0];

   // Signed version of rs1_val and rs2_val
   Int #(32) s_rs1_val = unpack (rs1_val);
   Int #(32) s_rs2_val = unpack (rs2_val);

   let    funct10 = inputs.decoded_instr.funct10;
   Bool   trap   = False;
   WordXL rd_val = ?;

   if      (funct10 == f10_ADDW) begin
      rd_val = pack (signExtend (s_rs1_val + s_rs2_val));
   end
   else if (funct10 == f10_SUBW) begin
      rd_val = pack (signExtend (s_rs1_val - s_rs2_val));
   end
   else if (funct10 == f10_SLLW) begin
      rd_val = pack (signExtend (rs1_val << (rs2_val [4:0])));
   end
   else if (funct10 == f10_SRLW) begin
      rd_val = pack (signExtend (rs1_val >> (rs2_val [4:0])));
   end
   else if (funct10 == f10_SRAW) begin
      rd_val = pack (signExtend (s_rs1_val >> (rs2_val [4:0])));
   end
   else
      trap = True;

   let alu_outputs       = alu_outputs_base;
   alu_outputs.control   = (trap ? CONTROL_TRAP : CONTROL_STRAIGHT);
   alu_outputs.op_stage2 = OP_Stage2_ALU;
   alu_outputs.rd        = inputs.decoded_instr.rd;
   alu_outputs.val1      = change_tagged_addr(tc_zero, rd_val);

   return alu_outputs;
endfunction: fv_OP_32

// ----------------------------------------------------------------
// Upper Immediates

function ALU_Outputs fv_LUI (ALU_Inputs inputs);
   Bit #(32)  v32    = { inputs.decoded_instr.imm20_U, 12'h0 };
   IntXL      iv     = extend (unpack (v32));
   let        rd_val = pack (iv);

   let alu_outputs       = alu_outputs_base;
   alu_outputs.op_stage2 = OP_Stage2_ALU;
   alu_outputs.rd        = inputs.decoded_instr.rd;
   alu_outputs.val1      = change_tagged_addr(tc_zero, rd_val);

   return alu_outputs;
endfunction

function ALU_Outputs fv_AUIPC (ALU_Inputs inputs);
   IntXL  iv     = extend (unpack ({ inputs.decoded_instr.imm20_U, 12'b0}));
   IntXL  pc_s   = unpack (inputs.pc);
   WordXL rd_val = pack (pc_s + iv);

   let alu_outputs       = alu_outputs_base;
   alu_outputs.op_stage2 = OP_Stage2_ALU;
   alu_outputs.rd        = inputs.decoded_instr.rd;
   alu_outputs.val1      = rd_val;

   return alu_outputs;
endfunction

// ----------------------------------------------------------------
// LOAD

function ALU_Outputs fv_LD (ALU_Inputs inputs);
   // Signed versions of rs1_val and rs2_val
   IntXL s_rs1_val = unpack (inputs.rs1_val);
   IntXL s_rs2_val = unpack (inputs.rs2_val);

   IntXL  imm_s = extend (unpack (inputs.decoded_instr.imm12_I));
   WordXL eaddr = pack (s_rs1_val + imm_s);

   let funct3 = inputs.decoded_instr.funct3;
   Bool legal_LD = (   (funct3 == f3_LB) || (funct3 == f3_LBU)
		    || (funct3 == f3_LH) || (funct3 == f3_LHU)
		    || (funct3 == f3_LW)
`ifdef RV64
		    || (funct3 == f3_LWU)
		    || (funct3 == f3_LD)
`endif
		    );

   let alu_outputs = alu_outputs_base;
   alu_outputs.control   = ((! legal_LD) ? CONTROL_TRAP : CONTROL_STRAIGHT);
   alu_outputs.op_stage2 = OP_Stage2_LD;
   alu_outputs.rd        = inputs.decoded_instr.rd;
   alu_outputs.addr      = eaddr;

   return alu_outputs;
endfunction

// ----------------------------------------------------------------
// STORE

function ALU_Outputs fv_ST (ALU_Inputs inputs);
   // Signed version of rs1_val
   IntXL  s_rs1_val = unpack (inputs.rs1_val);
   IntXL  imm_s     = extend (unpack (inputs.decoded_instr.imm12_S));
   WordXL eaddr     = pack (s_rs1_val + imm_s);

   let funct3 = inputs.decoded_instr.funct3;
   Bool legal_ST = (   (funct3 == f3_SB)
		    || (funct3 == f3_SH)
		    || (funct3 == f3_SW)
`ifdef RV64
		    || (funct3 == f3_SD)
`endif
		    );

   let alu_outputs = alu_outputs_base;
   alu_outputs.control   = ((! legal_ST) ? CONTROL_TRAP : CONTROL_STRAIGHT);
   alu_outputs.op_stage2 = OP_Stage2_ST;
   alu_outputs.addr      = eaddr;
   alu_outputs.val2      = inputs.rs2_val;

   return alu_outputs;
endfunction

// ----------------------------------------------------------------
// MISC_MEM (FENCE and FENCE.I)
// No-ops, for now

function ALU_Outputs fv_MISC_MEM (ALU_Inputs inputs);
   let alu_outputs = alu_outputs_base;
   alu_outputs.control  = (  (inputs.decoded_instr.funct3 == f3_FENCE_I)
			   ? CONTROL_FENCE_I
			   : (  (inputs.decoded_instr.funct3 == f3_FENCE)
			      ? CONTROL_FENCE
			      : CONTROL_TRAP));

   return alu_outputs;
endfunction

// ----------------------------------------------------------------
// System instructions

function ALU_Outputs fv_SYSTEM (ALU_Inputs inputs);
   let funct3      = inputs.decoded_instr.funct3;
   let alu_outputs = alu_outputs_base;

   if (funct3  == f3_PRIV) begin
`ifdef ISA_PRIV_S
      // SFENCE.VMA instruction
      if (   (inputs.decoded_instr.rd  == 0)
	  && (   (inputs.cur_priv == m_Priv_Mode)
	      || (   (inputs.cur_priv == s_Priv_Mode)
		  && (inputs.mstatus [mstatus_tvm_bitpos] == 0)))
	  && (inputs.decoded_instr.funct7 == f7_SFENCE_VMA))
	 begin
	    alu_outputs.control = CONTROL_SFENCE_VMA;
	 end
      else
`endif
      if (   (inputs.decoded_instr.rd  == 0)
	  && (inputs.decoded_instr.rs1 == 0))
	 begin
	    // ECALL instructions
	    if (inputs.decoded_instr.imm12_I == f12_ECALL) begin
	       alu_outputs.control  = CONTROL_TRAP;
	       alu_outputs.exc_code = ((inputs.cur_priv == u_Priv_Mode)
				       ? exc_code_ECALL_FROM_U
				       : ((inputs.cur_priv == s_Priv_Mode)
					  ? exc_code_ECALL_FROM_S
					  : exc_code_ECALL_FROM_M));
	    end

	    // EBREAK instruction
	    else if (inputs.decoded_instr.imm12_I == f12_EBREAK) begin
	       alu_outputs.control  = CONTROL_TRAP;
	       alu_outputs.exc_code = exc_code_BREAKPOINT;
	    end

	    // MRET instruction
	    else if (   (inputs.cur_priv >= m_Priv_Mode)
		     && (inputs.decoded_instr.imm12_I == f12_MRET))
	       begin
		  alu_outputs.control = CONTROL_MRET;
	       end

	    // SRET instruction
	    // TODO: If MSTATUS.TSR bit is set, mode must be >= m_Priv_Mode
	    else if (   (   (inputs.cur_priv == m_Priv_Mode)
			 || (   (inputs.cur_priv == s_Priv_Mode)
			     && (inputs.mstatus [mstatus_tsr_bitpos] == 0)))
		     && (inputs.decoded_instr.imm12_I == f12_SRET))
	       begin
		  alu_outputs.control = CONTROL_SRET;
	       end


	    /*
	    // URET instruction (future: Piccolo does not support 'N' extension)
	    else if (   (inputs.cur_priv >= u_Priv_Mode)
		     && (inputs.decoded_instr.imm12_I == f12_URET))
	       begin
		  alu_outputs.control = CONTROL_URET;
	       end
	    */

	    // WFI instruction
	    else if (   (   (inputs.cur_priv == m_Priv_Mode)
			 || (   (inputs.cur_priv == s_Priv_Mode)
			     && (inputs.mstatus [mstatus_tw_bitpos] == 0))
			 || (   (inputs.cur_priv == u_Priv_Mode)
			     && (inputs.misa.n == 1)))
		     && (inputs.decoded_instr.imm12_I == f12_WFI))
	       begin
		  alu_outputs.control = CONTROL_WFI;
	       end

	    else begin
	       alu_outputs.control = CONTROL_TRAP;
	    end
	 end

      else begin
	 alu_outputs.control = CONTROL_TRAP;
      end
   end    // funct3 is f3_PRIV

   // funct3 is not f3_PRIV
   else if (funct3 == f3_SYSTEM_ILLEGAL) begin
      alu_outputs.control = CONTROL_TRAP;
   end

   // CSRR{W,C,S} and CSRR{W,C,S}I
   else begin
      let  csr_val = inputs.csr_val;
      WordXL rs1_val = ((funct3 [2] == 1)
			? extend (inputs.decoded_instr.rs1)    // Immediate zimm
			: cap_addr(inputs.rs1_val.capability));                     // From rs1 reg

      // New value of Rd = old value of csr
      WordXL rd_val = ((inputs.decoded_instr.rd == 0) ? 0 : csr_val);

      Bool trap      = (   (! inputs.csr_valid)
			|| (   (inputs.decoded_instr.csr == csr_satp)
			    && (inputs.mstatus [mstatus_tvm_bitpos] == 1)));
      Bool write_csr = True;

      // New value of CSR
      case ({1'b0, funct3[1:0]})
	 f3_CSRRW: csr_val = rs1_val;
	 f3_CSRRS: begin
		      csr_val = csr_val | rs1_val;
		      write_csr = (inputs.decoded_instr.rs1 != 0);
		   end
	 f3_CSRRC: begin
		      csr_val = csr_val & (~ rs1_val);
		      write_csr = (inputs.decoded_instr.rs1 != 0);
		   end
      endcase

      if (inputs.decoded_instr.csr == csr_mstatus) begin
	 // Ensure legal mstatus values    TODO: trap on illegal?
	 WordXL mask = {1'h1,      // SD    [XLEN-1]
			0,         // WPRI  [XLEN-2:23]
			1'h1,      // TSR   [22]
			1'h1,      // TW    [21]
			1'h1,      // TVM   [20]
			1'h1,      // MXR   [19]
			1'h1,      // SUM   [18]
			1'h1,      // MPRV  [17]
			2'h3,      // XS    [16:15]
			2'h3,      // FS    [14:13]
			2'h3,      // MPP   [12:11]
			2'h0,      // WPRI  [10:9]
			1'h1,      // SPP   [8]
			4'hB,      // xPIE  [7:4]
			4'hB };    // xIE   [3:0]
`ifdef RV64
	 mask = (mask | {0,
			 2'h3,     // SXL   [35:34]
			 2'h3,     // UXL   [33:32]
			 32'h0});
`endif
	 csr_val = csr_val & mask;

	 if ((inputs.misa.s == 0) && (inputs.misa.f == 0) && (inputs.misa.d == 0)) begin
	    // Force mstatus.FS to 0
	    WordXL mask_in_fs = 'h_6000;
	    csr_val = (csr_val & (~ mask_in_fs));
	 end

	 // If mpp is not supported, force the value to a supported value
	 if (inputs.misa.s == 0) begin
            // Disable spp, spie, sie
	    WordXL mask_in_s = 'h_0122;
	    csr_val = (csr_val & (~ mask_in_s));
	 end

	 if (inputs.misa.u == 1) begin
	    if (inputs.misa.n == 0) begin
               // Disable upie, uie
	       WordXL mask_in_u = 'h_0011;
	       csr_val = (csr_val & (~ mask_in_u));
	    end
	 end
	 else begin
            // Disable upie, uie
	    WordXL mask_in_u = 'h_0011;
	    csr_val = (csr_val & (~ mask_in_u));
	 end

	 Priv_Mode mpp = csr_val [12:11];
	 if (inputs.misa.u == 1'b0) begin
	    // Only M supported
	    mpp = m_Priv_Mode;
	 end
	 else if (inputs.misa.s == 1'b0) begin
	    // Only M and U supported
	    if (mpp != m_Priv_Mode)
	       mpp = u_Priv_Mode;
	 end
	 else begin
	    // Only M, S, and U supported
	    if (mpp == reserved_Priv_Mode)
	       mpp = s_Priv_Mode;
	 end
	 csr_val [12:11] = mpp;

	 // If spp is not supported, force the value
	 Priv_Mode spp = {0, csr_val [8]};
	 if (inputs.misa.s == 1'b0)
	    spp = u_Priv_Mode;
	 csr_val [8] = spp [0];

`ifdef RV64
`ifdef ISA_PRIV_S
	 // Force mstatus.sxl to 2'b10
	 csr_val = { csr_val [63:36], 2'b10, csr_val [33:0] };
`endif
`ifdef ISA_PRIV_U
	 // Force mstatus.uxl to 2'b10
	 csr_val = { csr_val [63:34], 2'b10, csr_val [31:0] };
`endif
`endif
      end

      alu_outputs.control   = (trap ? CONTROL_TRAP : CONTROL_STRAIGHT);
      alu_outputs.op_stage2 = OP_Stage2_ALU;
      alu_outputs.rd        = inputs.decoded_instr.rd;
      alu_outputs.csr_valid = ((! trap) && write_csr);
      alu_outputs.addr      = change_tagged_addr(tc_zero, extend (inputs.decoded_instr.csr));
      alu_outputs.val1      = change_tagged_addr(tc_zero, rd_val);
      alu_outputs.val2      = change_tagged_addr(tc_zero, csr_val);
   end

   return alu_outputs;
endfunction: fv_SYSTEM

// ----------------------------------------------------------------
// AMO
// Just pass through to the memory stage

`ifdef ISA_A
function ALU_Outputs fv_AMO (ALU_Inputs inputs);
   let funct3 = inputs.decoded_instr.funct3;
   let funct5 = inputs.decoded_instr.funct5;
   let funct7 = inputs.decoded_instr.funct7;

   Bool legal_f5 = (   (funct5 == f5_AMO_LR)   || (funct5 == f5_AMO_SC)

		    || (funct5 == f5_AMO_ADD)
		    || (funct5 == f5_AMO_SWAP)

		    || (funct5 == f5_AMO_AND)  || (funct5 == f5_AMO_OR) || (funct5 == f5_AMO_XOR)

		    || (funct5 == f5_AMO_MIN)  || (funct5 == f5_AMO_MINU)
		    || (funct5 == f5_AMO_MAX)  || (funct5 == f5_AMO_MAXU));

   Bool legal_width = (   (funct3 == f3_AMO_W)
		       || ((xlen == 64) && (funct3 == f3_AMO_D)) );

   let alu_outputs = alu_outputs_base;
   alu_outputs.control   = ((legal_f5 && legal_width) ? CONTROL_STRAIGHT : CONTROL_TRAP);
   alu_outputs.op_stage2 = OP_Stage2_AMO;
   alu_outputs.addr      = inputs.rs1_val;
   alu_outputs.val1      = zeroExtend (inputs.decoded_instr.funct7);
   alu_outputs.val2      = inputs.rs2_val;

   return alu_outputs;
endfunction
`endif



// ----------------------------------------------------------------
// CAPABILITY
// Non-memory CHERI ops.

function ALU_Outputs fv_CHERI (ALU_Inputs inputs);
    let alu_outputs = alu_outputs_base;
    if (inputs.decoded_instr.funct7 == f7_CAPINSPECT) begin // 0x7f
        return fv_CINSPECT_ETC (inputs);
    end
    else if (inputs.decoded_instr.funct7 == f7_CSEAL) begin // 0x0b
    
    end
    else if (inputs.decoded_instr.funct7 == f7_CUNSEAL) begin // 0x0c
    
    end
    else if (inputs.decoded_instr.funct7 == f7_ANDPERM) begin // 0x0d
    
    end
    else if (inputs.decoded_instr.funct7 == f7_SETOFFSET) begin // 0x0f
    
    end
    else if (inputs.decoded_instr.funct7 == f7_INCOFFSET) begin // 0x11
    
    end
    else if (inputs.decoded_instr.funct7 == f7_CSETBOUNDS) begin // 0x08
    
    end
    else if (inputs.decoded_instr.funct7 == f7_CSETBOUNDSEX) begin // 0x09
    
    end
    else if (inputs.decoded_instr.funct7 == f7_CBUILDCAP) begin // 0x1d
    
    end
    else if (inputs.decoded_instr.funct7 == f7_CCOPYTYPE) begin // 0x1e
    
    end
    else if (inputs.decoded_instr.funct7 == f7_CCSEAL) begin // 0x1f
    
    end
    else if (inputs.decoded_instr.funct7 == f7_CTOPTR) begin // 0x12
        
    end
    else if (inputs.decoded_instr.funct7 == f7_CFROMPTR) begin // 0x13
        
    end
    else if (inputs.decoded_instr.funct7 == f7_CSPECIALRW) begin // 0x01
    
    end
    else if (inputs.decoded_instr.funct7 == f7_CCALLRET) begin // 0x7e
    
    end
    else if (inputs.decoded_instr.funct7 == f7_MEMORYOP) begin // 0x00
    
    end
    return alu_outputs;
endfunction

// Any operations with opcode 0x5b and f7 0x7f.
// A number of these don't particularly fit with the general structure presented in the
// CHERI-RISC-V design. The elimination of the 256-bit capability format makes the calculation
// of some values awkward and unusual, whereas in MIPS they were immediately available. A good
// example is the definition of getperms. It is well suited to the 256-bit format given the
// distinction between hardware- and software-defined permissions (perms and uperms), but when
// only the 128-bit representation is used the separation looks irrational.
function ALU_Outputs fv_CINSPECT_ETC (ALU_Inputs inputs);
    let alu_outputs = alu_outputs_base;
    let rs1_cap  = inputs.rs1_val.capability;
    // Some CHERI ops have a 5-bit decoding value in the rs2 position rather than the
    // standard position used in the base RISC-V ISA.
    // TODO: Do we need to extend after pack, or does typing sort it out?
    if      (inputs.decoded_instr.rs2 == f5_CGETPERM)   begin
        Bit #(15) perms = rs1_cap[127:113];
        // If we're mimicing the MIPS behaviour, we have a weird gap between perms and uperms
        Bit #(64) newVal = {45'b0, perms[14:11], 4'b0, perms[10:0]};
        alu_outputs.val1 = change_tagged_addr(tc_zero, newVal);
    end
    else if (inputs.decoded_instr.rs2 == f5_CGETTYPE)   begin
        // If sealed capability, return otype, otherwise -1.
        Bit #(64) newVal = fv_checkSealed(inputs.rs1_val) ? 
                                extend({rs1_cap[95:84], rs1_cap[75:64]}) : 
                                pack(-1);
        alu_outputs.val1 = change_tagged_addr(tc_zero, newVal);
    end
    else if (inputs.decoded_instr.rs2 == f5_CGETBASE)   begin
        Bit #(64) newVal = fv_getBase(inputs.rs1_val);
        alu_outputs.val1 = change_tagged_addr(tc_zero, newVal);
    end
    else if (inputs.decoded_instr.rs2 == f5_CGETLEN)    begin
        Bit #(64) newVal = pack(unpack(fv_getTop(inputs.rs1_val)) - unpack(fv_getBase(inputs.rs1_val)));
        alu_outputs.val1 = change_tagged_addr(tc_zero, newVal);
    end
    else if (inputs.decoded_instr.rs2 == f5_CGETTAG)    begin
        alu_outputs.val1 = change_tagged_addr(tc_zero, extend(inputs.rs1_val.tag));
    end
    else if (inputs.decoded_instr.rs2 == f5_CGETSEALED) begin
        Bit #(64) newVal = pack(fv_checkSealed(inputs.rs1_val));
        alu_outputs.val1 = change_tagged_addr(tc_zero, newVal);
    end
    else if (inputs.decoded_instr.rs2 == f5_CGETOFFSET) begin
        Bit #(64) newVal = pack(unpack(rs1_cap[63:0]) - unpack(fv_getBase(inputs.rs1_val)));
        alu_outputs.val1 = change_tagged_addr(tc_zero, newVal);
    end
    else if (inputs.decoded_instr.rs2 == f5_CGETADDR)   begin
        alu_outputs.val1 = change_tagged_addr(tc_zero, rs1_cap[63:0]);
    end
    else if (inputs.decoded_instr.rs2 == f5_CCLEARTAG)  begin
        alu_outputs.val1 = Tagged_Capability {
            tag: 0,
            capability: rs1_cap
        };
    end
    else if (inputs.decoded_instr.rs2 == f5_CMOVE)      begin
        // TODO: this is simply a straight copy, including tag?
        alu_outputs.val1 = inputs.rs1_val;
    end
    else if (inputs.decoded_instr.rs2 == f5_CJALR)      begin
        // Since we're not using a pointer, we only need to add 4 here.
        UInt #(64) retAddr = unpack(inputs.pcc.capability[63:0]) + 4;
        alu_outputs.val1 = change_tagged_addr(inputs.pcc, retAddr);
        // TODO: priority of exceptions?
        match { .trap, .new_pcc } = fv_getCheckAndTarget (rs1_val, pcc);
        alu_outputs.addr = new_pcc;
        if (trap) begin
            alu_outputs.control = CONTROL_TRAP;
            alu_outputs.exc_code = exc_code_CAPABILITY_EXC;
        end
        else begin
            // Other exception remaining is alignment.
            alu_outputs.exc_code = exc_code_INSTR_ADDR_MISALIGNED;
            alu_outputs.control = ((new_pcc.capability[1:0] == 2'b00) ? CONTROL_BRANCH : CONTROL_TRAP);
        end
    end
    // Comments in the spec suggest check-perm/type might be removed in future.
    else if (inputs.decoded_instr.rs2 == f5_CCHECKPERM) begin
    
    end
    else if (inputs.decoded_instr.rs2 == f5_CCHECKTYPE) begin
        
    end
    // As these functions won't write back to registers like most do, it makes sense
    // to use a new CONTROL type.
    // As for ALU output values, we'll set val1[1:0] = quadrant, val2[7:0] = mask, and addr[0] = GP/FP
    else if (inputs.decoded_instr.rs2 == f5_FASTCLEAR)  begin
        alu_outputs.control = CONTROL_CLEAR;
        alu_outputs.val1 = change_tagged_addr(tc_zero, extend(inputs.instr[19:18]));
        alu_outputs.val2 = change_tagged_addr(tc_zero, extend({inputs.instr[17:15], inputs.instr[11:7]}));
        alu_outputs.addr = change_tagged_addr(tc_zero, 64'h0);
    end
    else if (inputs.decoded_instr.rs2 == f5_FPCLEAR)    begin
        alu_outputs.control = CONTROL_CLEAR;
        alu_outputs.val1 = change_tagged_addr(tc_zero, extend(inputs.instr[19:18]));
        alu_outputs.val2 = change_tagged_addr(tc_zero, extend({inputs.instr[17:15], inputs.instr[11:7]}));
        alu_outputs.addr = change_tagged_addr(tc_zero, 64'h1);
    end
    else begin
        alu_outputs.control = CONTROL_TRAP;
        // Exception type = ILLLEGAL_INSTRUCTION?
    end
    return alu_outputs;
endfunction

// ----------------------------------------------------------------
// CAPABILITY LOAD
// Pass through to memory stage? What details do we need?

function ALU_Outputs fv_CHERILOAD (ALU_Inputs inputs);
   match { .trap, .addrval } = fv_getCheckAndTarget (rs1_val, pcc);
endfunction

// ----------------------------------------------------------------
// UTILITY FUNCTIONS

function Bool fv_checkSealed(Tagged_Capability tc);
    return unpack(tc.capability[104]);
endfunction

function Bit #(6)  fv_getExp  (Tagged_Capability tc);
    return (tc.capability[110:105]);
endfunction

function Bit #(20)  fv_getB  (Tagged_Capability tc);
    if (fv_checkSealed(tc))
        return {tc.capability[103:96], 12'h000};
    else
        return tc.capability[103:84];
endfunction

function Bit #(20)  fv_getT  (Tagged_Capability tc);
    if (fv_checkSealed(tc))
        return {tc.capability[83:76], 12'h000};
    else
        return tc.capability[83:64];
endfunction

function UInt #(2) fv_baseCorrection (Bit #(64) A, UInt #(20) B, UInt #(6) e);
    UInt #(20) AMid = unpack(A[19+e:e]);
    UInt #(20) R = unpack(B) - unpack(1 << 12);
    Bool C1 = (AMid < R);
    Bool C2 = (B < R);
    if (C1 && !C2)
        return -1;
    else if (C2 && !C1)
        return 1;
    else
        return 0;
endfunction

function UInt #(2) fv_topCorrection (Bit #(64) A, UInt #(20) B, UInt #(20) T, UInt #(6) e);
    UInt #(20) AMid = unpack(A[19+e:e]);
    UInt #(20) R = unpack(B) - unpack(1 << 12);
    Bool C1 = (AMid < R);
    Bool C2 = (T < R);
    if (C1 && !C2)
        return -1;
    else if (C2 && !C1)
        return 1;
    else
        return 0;
endfunction

function Bit #(64) fv_getBase (Tagged_Capability tc);
    // As defined in 3.3.8/page 81.
    // We can calculate these here or later, the difference should be arbitrary.
    Bit  #(64) result = 64'h0000_0000_0000_0000;
    UInt #(6)  e = unpack(fv_getExp(tc));
    Bit  #(20) B = fv_getB(tc);
    result[63:20+e]  = pack(unpack(tc.capability[63:20+e]) + fv_baseCorrection(tc.capability[63:0],unpack(B),e));
    result[19+e:e] = B;
    return result;
endfunction

function Bit #(64) fv_getTop  (Tagged_Capability tc);
    // As defined in 3.3.8/page 81.
    // We can calculate these here or later, the difference should be arbitrary.
    Bit  #(64) result = 64'h0000_0000_0000_0000;
    UInt #(6)  e = unpack(fv_getExp(tc));
    Bit  #(20) T = fv_getT(tc);
    Bit  #(20) B = fv_getB(tc);
    result[63:20+e]  = pack(unpack(tc.capability[63:20+e]) + fv_topCorrection(tc.capability[63:0],unpack(B),unpack(T),e));
    result[19+e:e] = T;
    return result;
endfunction

// Bool = trap status, capability = target.
// This checks capability issues (permissions, bounds & sealing).
function Tuple2# (Bool , Tagged_Capability) fv_getCheckAndTarget (Tagged_Capability rs1, Tagged_Capability pcc);
    
endfunction

// ================================================================

endpackage
