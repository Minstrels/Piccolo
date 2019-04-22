// Copyright (c) 2016-2018 Bluespec, Inc. All Rights Reserved

//-
// RVFI_DII modifications:
//     Copyright (c) 2018-2019 Jack Deeley
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
import Capability128ccLibs :: *;

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
   Tagged_Capability    ddc;
   Tagged_Capability    rs1_val;
   Tagged_Capability    rs2_val;
   Bool                 csr_valid;
   WordXL               csr_val;
   Tagged_Capability    ccsr_val;
   WordXL               mstatus;
   MISA                 misa;
   } ALU_Inputs
deriving (Bits);

// ================================================================
// ALU outputs

typedef struct {
   Control              control;
   Exc_Code             exc_code;        // Relevant if control == CONTROL_TRAP

   Op_Stage2            op_stage2;
   RegName              rd;

   Bool                 csr_valid;
   Bool                 ccsr_valid;
   Bool                 cap_mode;
   `ifdef CHERIDEBUG
   Bit#(64)             debug_out;
   `endif
   Tagged_Capability    addr;       // Branch, jump: newPC
                                    // Mem ops and AMOs: mem addr
                                    // CSRRx: csr addr, CSpecialRW: CapCSR addr

   Tagged_Capability    val1;   // OP_Stage2_ALU: result for Rd (ALU ops: result, JAL/JALR: return PC,
                                //                           CSSRx: old value of CSR)
                                // OP_Stage2_M, OP_Stage2_FD: arg1
                                // OP_Stage2_AMO: funct7

   Tagged_Capability    val2;   // Branch: branch target (for Tandem Verification)
                                // OP_Stage2_ST: store-val
                                // OP_Stage2_M, OP_Stage2_FD: arg2
                                // CSSRx: new csr value
   } ALU_Outputs
deriving (Bits);

ALU_Outputs alu_outputs_base = ALU_Outputs {control:   CONTROL_STRAIGHT,
					    exc_code:   exc_code_ILLEGAL_INSTRUCTION,
					    op_stage2:  ?,
					    // Wolf's verification model requires rd to be 0 for non-updating
					    // At the moment we check this later in the sequence.
					    rd:         ?,
`ifdef CHERIDEBUG
                        debug_out: 64'hcafe_cafe_cafe_cafe,
`endif
					    csr_valid:  False,
					    ccsr_valid: False,
                        cap_mode:   False,
					    addr:       ?,
					    val1:       ?,
					    val2:       ?
					 };

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
    IntXL offset        = extend (unpack (inputs.decoded_instr.imm13_SB));
    alu_outputs.rd        = 0;
    alu_outputs.exc_code  = exc_code_INSTR_ADDR_MISALIGNED;
    alu_outputs.op_stage2 = OP_Stage2_ALU;
    Bool  branch_taken  = False;
    Bool  trap          = False;
    Addr  branch_target = pack (unpack(cap_addr(inputs.pcc.capability)) + offset);
    
    let rs1_val = cap_addr(inputs.rs1_val.capability);
    let rs2_val = cap_addr(inputs.rs2_val.capability);
    IntXL s_rs1_val = unpack (rs1_val);
    IntXL s_rs2_val = unpack (rs2_val);
    let funct3 = inputs.decoded_instr.funct3;
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
    trap = (trap || (branch_taken && (branch_target [1] == 1'b1)));
    Addr new_pc = branch_taken ? branch_target : (cap_addr(inputs.pcc.capability) + 4);
    alu_outputs.addr = change_tagged_addr(inputs.pcc, new_pc);
    alu_outputs.control   = (trap ? CONTROL_TRAP : (branch_taken ? CONTROL_BRANCH : CONTROL_STRAIGHT));
    // Gives a defined value when in verification mode.
    alu_outputs.val2      = change_tagged_addr(inputs.pcc, branch_target);    // For tandem verifier only
    `ifdef RVFI
        `ifdef CHERI
        alu_outputs.val1      = tc_zero;
        `else
        alu_outputs.val1      = 0;
        `endif
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
/*
   let alu_outputs = alu_outputs_base;
   
   Tagged_Capability next = change_tagged_addr(inputs.pcc, next_pc);
   alu_outputs.addr      = next;
   
   if (!fv_checkRange_withLen(next, 4'h4)) begin
      alu_outputs.control = CONTROL_TRAP;
      alu_outputs.exc_code = exc_code_BOUNDS_VIOLATED;
   end
   else begin
      alu_outputs.control   = ((next_pc [1] == 1'b0) ? CONTROL_BRANCH : CONTROL_TRAP);
      alu_outputs.exc_code  = exc_code_INSTR_ADDR_MISALIGNED;
      alu_outputs.op_stage2 = OP_Stage2_ALU;
      alu_outputs.rd        = inputs.decoded_instr.rd;
      alu_outputs.val1      = change_tagged_addr(inputs.pcc, ret_pc);
   end*/
   
   
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
   Addr  ret_pc    = tagged_addr(inputs.pcc) + 4;

   // nsharma: 2017-05-26 Bug fix
   // nsharma: next_pc[0] should be cleared for JAL/JALR
   // riscv-spec-v2.2. Secn 2.5. Page 16
   next_pc[0] = 1'b0;
   
   let alu_outputs = alu_outputs_base;
   
   /*Tagged_Capability next = change_tagged_addr(inputs.pcc, next_pc);
   
   if (!fv_checkRange_withLen(next, 4'h04)) begin
      alu_outputs.control = CONTROL_TRAP;
      alu_outputs.exc_code = exc_code_BOUNDS_VIOLATED;
   end
   else if (next_pc[1] == 1'b1) begin
      alu_outputs.control = CONTROL_TRAP;
      alu_outputs.exc_code = exc_code_INSTR_ADDR_MISALIGNED;
   end
   else begin
      alu_outputs.addr      = next;
      alu_outputs.control   = CONTROL_BRANCH;
      alu_outputs.op_stage2 = OP_Stage2_ALU;
      alu_outputs.rd        = inputs.decoded_instr.rd;
      alu_outputs.val1      = change_tagged_addr(inputs.pcc, ret_pc);
   end*/


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
   IntXL  pc_s   = unpack (tagged_addr(inputs.pcc));
   WordXL rd_val = pack (pc_s + iv);

   let alu_outputs       = alu_outputs_base;
   alu_outputs.op_stage2 = OP_Stage2_ALU;
   alu_outputs.rd        = inputs.decoded_instr.rd;
   alu_outputs.val1      = change_tagged_addr(tc_zero, rd_val);

   return alu_outputs;
endfunction

// ----------------------------------------------------------------
// LOAD

function ALU_Outputs fv_LD (ALU_Inputs inputs);
   // Signed versions of rs1_val and rs2_val
   IntXL s_rs1_val = unpack (tagged_addr(inputs.rs1_val));
   IntXL s_rs2_val = unpack (tagged_addr(inputs.rs2_val));

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
   let len = ((funct3 == f3_LB) || (funct3 == f3_LBU)) ? 4'h1 :
             ((funct3 == f3_LH) || (funct3 == f3_LHU)) ? 4'h2 :
             ((funct3 == f3_LH) || (funct3 == f3_LHU)) ? 4'h4 :
             4'h8;
   /*let ddc_check = fv_checkOP_DDC(inputs.ddc, eaddr, True, len);
   if (legal_LD && ddc_check != exc_code_NO_EXCEPTION) // Illegal instruction takes priority.
      alu_outputs.exc_code = ddc_check;
   alu_outputs.control   = ((!legal_LD || (ddc_check != exc_code_NO_EXCEPTION)) ? CONTROL_TRAP : CONTROL_STRAIGHT);*/
   alu_outputs.op_stage2 = OP_Stage2_LD;
   alu_outputs.rd        = inputs.decoded_instr.rd;
   alu_outputs.addr      = change_tagged_addr(tc_zero, eaddr);

   return alu_outputs;
endfunction

// ----------------------------------------------------------------
// STORE

function ALU_Outputs fv_ST (ALU_Inputs inputs);
   // Signed version of rs1_val
   IntXL  s_rs1_val = unpack (tagged_addr(inputs.rs1_val));
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
   let len = (funct3 == f3_SB) ? 4'h1 :
             (funct3 == f3_SH) ? 4'h2 :
             (funct3 == f3_SW) ? 4'h4 : 4'h8;
             
   /*let ddc_check = fv_checkOP_DDC(inputs.ddc, eaddr, False, len);
   if (legal_ST && ddc_check != exc_code_NO_EXCEPTION)
      alu_outputs.exc_code = ddc_check;

   alu_outputs.control   = ((!legal_ST || (ddc_check != exc_code_NO_EXCEPTION)) ? CONTROL_TRAP : CONTROL_STRAIGHT);*/
   alu_outputs.op_stage2 = OP_Stage2_ST;
   alu_outputs.addr      = change_tagged_addr(tc_zero, eaddr);
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

// TODO: More permissions checks
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
   // TODO: Do we require permissions checks for existing CSRs, or only capability CSRs?
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
   alu_outputs.val1      = change_tagged_addr(tc_zero, zeroExtend (inputs.decoded_instr.funct7));
   alu_outputs.val2      = inputs.rs2_val;

   return alu_outputs;
endfunction
`endif



// ----------------------------------------------------------------
// CAPABILITY
// CHERI ops, opcode 0x5b

function ALU_Outputs fv_CHERI (ALU_Inputs inputs);
    let alu_outputs = alu_outputs_base;
    let   cs = inputs.rs1_val;
    let   ct = inputs.rs2_val;
    alu_outputs.op_stage2 = OP_Stage2_ALU;
    if (inputs.decoded_instr.funct3 == 3'b001) begin // CIncOffsetImmediate
        // TODO: If we don't have the 256-bit capability format we don't need to worry about representing the bounds as
        // they must be represented in the capability we're incrementing. Do we need to check overflow on the pointer?
        if (cs.tag == 1'b1 && fv_checkSealed(cs)) begin
            alu_outputs.control = CONTROL_TRAP;
            alu_outputs.exc_code = exc_code_CAPABILITY_SEALED;
        end
        alu_outputs.val1 = increment_tagged_addr(cs, signExtend(inputs.decoded_instr.imm12_I));
    end
    else if (inputs.decoded_instr.funct3 == 3'b010) begin // CSetBoundsImmediate
        
    end
    
    else if (inputs.decoded_instr.funct3 == 3'b000) begin // Other instructions
        if (inputs.decoded_instr.funct7 == f7_CAPINSPECT) begin // 0x7f
            alu_outputs = fv_CINSPECT_ETC (inputs);
        end
        else if (inputs.decoded_instr.funct7 == f7_CSEAL) begin // 0x0b
            let check = fv_checkValid_Seal(cs, ct);
            if (check == exc_code_NO_EXCEPTION)
                alu_outputs.val1 = fv_seal(cs, ct);
            else begin
                alu_outputs.control = CONTROL_TRAP;
                alu_outputs.exc_code = check;
            end
        end
        else if (inputs.decoded_instr.funct7 == f7_CUNSEAL) begin // 0x0c
            let check = fv_checkValid_Unseal(cs, ct);
            if (check == exc_code_NO_EXCEPTION)
                alu_outputs.val1 = fv_unseal(cs, ct);
            else begin
                alu_outputs.control = CONTROL_TRAP;
                alu_outputs.exc_code = check;
            end
        end
        else if (inputs.decoded_instr.funct7 == f7_ANDPERM) begin // 0x0d
            // TODO: Where do we get the permission bits from? Still using the same perms/uperms
            // split as in CHERI-MIPS, or just the 15-bit muperms field in the 128-bit version?
            if (cs.tag == 1'b0) begin
                alu_outputs.exc_code = exc_code_TAG_NOT_SET;
                alu_outputs.control  = CONTROL_TRAP;
            end
            else if (fv_checkSealed(cs)) begin
                alu_outputs.exc_code = exc_code_CAPABILITY_SEALED;
                alu_outputs.control  = CONTROL_TRAP;
            end
            else begin
                Bit #(15) newperms = ct.capability[14:0] & cs.capability[127:113];
                Bit #(128) newcap = {newperms, cs.capability[112:0]};
                alu_outputs.val1 = Tagged_Capability {
                    tag: 1'b1,
                    capability: newcap
                };
            end
        end
        else if (inputs.decoded_instr.funct7 == f7_SETOFFSET) begin // 0x0f
            if (fv_checkSealed(cs) && (cs.tag == 1'b1)) begin
                alu_outputs.control  = CONTROL_TRAP;
                alu_outputs.exc_code = exc_code_CAPABILITY_SEALED;
            end
            else begin
                let new_curs = ct.capability[63:0] + fv_getBase(cs)[63:0];
                alu_outputs.val1 = Tagged_Capability {
                    tag: cs.tag,
                    capability: {cs.capability[127:64], new_curs}
                };
            end
        end
        else if (inputs.decoded_instr.funct7 == f7_INCOFFSET) begin // 0x11
            Bit #(64) rs2_v = ct.capability[63:0];
            if (fv_checkSealed(cs) && (cs.tag == 1'b1) && (rs2_v != 0)) begin
                alu_outputs.control  = CONTROL_TRAP;
                alu_outputs.exc_code = exc_code_CAPABILITY_SEALED;
            end
            else begin
                Bit #(64) newOffset = cs.capability[63:0] + ct.capability[63:0];
                alu_outputs.val1 = Tagged_Capability {
                    tag: inputs.rs1_val.tag,
                    capability: {cs.capability[127:64], newOffset}
                };
            end
        end
        // 0x08, 0x09
        else if (inputs.decoded_instr.funct7 == f7_CSETBOUNDS || inputs.decoded_instr.funct7 == f7_CSBOUNDSEX) begin
            if (cs.tag == 1'b0) begin
                alu_outputs.control  = CONTROL_TRAP;
                alu_outputs.exc_code = exc_code_TAG_NOT_SET;
            end
            else if (fv_checkSealed(cs)) begin
                alu_outputs.control  = CONTROL_TRAP;
                alu_outputs.exc_code = exc_code_CAPABILITY_SEALED;
            end
            else begin
                Bit#(64) range = tagged_addr(ct);
`ifdef SIMPLERANGE
                match {
                    .trap,
                    .exact,
                    .out
                } = fv_setBounds_simple(cs,range);
                if (trap != exc_code_NO_EXCEPTION) begin
                    alu_outputs.control = CONTROL_TRAP;
                    alu_outputs.exc_code = trap;
                end
                else if (inputs.decoded_instr.funct7 == f7_CSBOUNDSEX && !exact) begin
                    alu_outputs.control = CONTROL_TRAP;
                    alu_outputs.exc_code = exc_code_BOUNDS_INEXACT;
                end
                else begin
                    alu_outputs.val1 = out;
                end
`else
                CapFat out = setBounds(unpackCap(to129Bit(cs)), range, (inputs.decoded_instr.funct7 == f7_CSBOUNDSEX));
                if (!out.isCapability) begin
                    alu_outputs.control  = CONTROL_TRAP;
                    alu_outputs.exc_code = exc_code_CAPABILITY_EXC;
                end
                alu_outputs.val1 = from129Bit(packCap(out));
`endif
            end
        end
        else if (inputs.decoded_instr.funct7 == f7_CBUILDCAP) begin // 0x1d
            Bit#(20) ct_B      = fv_getB(inputs.rs2_val);
            Bit#(20) ct_T      = fv_getT(inputs.rs2_val);
            Bit#(64) ct_bot    = fv_getBase(inputs.rs2_val)[63:0];
            Bit#(64) ct_top    = fv_getTop(inputs.rs2_val)[63:0];
            Bit#(15) ct_perms  = fv_getPerms(inputs.rs2_val);
            Bit#(64) ct_cursor = inputs.rs2_val.capability[63:0];
            Bit#(6)  ct_exp    = fv_getExp(inputs.rs2_val)[5:0];
            
            Bit#(64) cb_bot    = fv_getBase(inputs.rs1_val)[63:0];
            Bit#(64) cb_top    = fv_getTop(inputs.rs1_val)[63:0];
            Bit#(15) cb_perms  = fv_getPerms(inputs.rs1_val);
            
            // Any permissions in ct but not cb
            Bool perms_valid = ((ct_perms & ~cb_perms) > 0);
            Bool bounds_valid = !(ct_bot < cb_bot || ct_top > cb_top);
            Bit#(1) tag = inputs.rs1_val.tag;
            if ((!perms_valid))
                tag = 1'b0;
            else if (!bounds_valid)
                tag = 1'b0;
            // TODO: What do we do if the conditions AREN'T met?
            alu_outputs.val1 = Tagged_Capability {
                    tag:        tag,
                    capability: {ct_perms, 2'b0, ct_exp, 1'b0, ct_B, ct_T, ct_cursor}
            };
        end
        // This is a poor choice to be included in the specification. 
        // Semantically there's minimal difference from CGetType, and the definitions as given in
        // the MIPS version make little sense when only the 128-bit capability is used.
        
        else if (inputs.decoded_instr.funct7 == f7_CCOPYTYPE) begin // 0x1e
            if (cs.tag == 0) begin
                alu_outputs.control = CONTROL_TRAP;
                alu_outputs.exc_code = exc_code_TAG_NOT_SET;
            end
            else if (fv_checkSealed(cs)) begin
                alu_outputs.control = CONTROL_TRAP;
                alu_outputs.exc_code = exc_code_CAPABILITY_SEALED;
            end
            else if (!fv_checkSealed(ct))begin
                alu_outputs.val1 = change_tagged_addr(tc_zero, -1);
            end
            else begin
                let out_val = change_tagged_addr(cs, extend(fv_getOType(ct)));
                if (!fv_checkRange_withLen(out_val, 1)) begin
                    alu_outputs.control = CONTROL_TRAP;
                    alu_outputs.exc_code = exc_code_BOUNDS_VIOLATED;
                end
                else begin
                    alu_outputs.val1 = out_val;
                end
            end
        end
        else if (inputs.decoded_instr.funct7 == f7_CCSEAL) begin // 0x1f
            IntXL ct_addr = unpack(tagged_addr(ct));
            if (cs.tag == 1'b0) begin
                alu_outputs.control  = CONTROL_TRAP;
                alu_outputs.exc_code = exc_code_TAG_NOT_SET;
            end
            else if (ct.tag == 1'b0 || ct_addr == -1) begin
                alu_outputs.val1 = cs;
            end
            else begin
                let check = fv_checkValid_Seal(cs, ct);
                if (check == exc_code_NO_EXCEPTION)
                    alu_outputs.val1 = fv_seal(cs, ct);
                else begin
                    alu_outputs.control = CONTROL_TRAP;
                    alu_outputs.exc_code = check;
                end
            end
        end
        // XXX: This instruction doesn't exactly match the merged register file mentality.
        else if (inputs.decoded_instr.funct7 == f7_CTOPTR) begin // 0x12
            if (inputs.rs1_val.tag == 1'b0) begin
            // TODO: Description says set rd to 0, pseudocode says throw an exception.
                alu_outputs.val1 = tc_zero;
            end
            else begin
                let cs_base = fv_getBase(inputs.rs2_val)[63:0];
                let cb_addr = tagged_addr(inputs.rs1_val);
                // TODO: Any handling of negative values?
                alu_outputs.val1 = change_tagged_addr(tc_zero, cb_addr - cs_base);
            end
        end
        else if (inputs.decoded_instr.funct7 == f7_CFROMPTR) begin // 0x13
            if(inputs.rs2_val.capability[63:0] == 64'b0)
                alu_outputs.val1 = tc_null;
            else
                alu_outputs.val1 = Tagged_Capability {
                    tag:        cs.tag,
                    capability: {cs.capability[127:64], ct.capability[63:0]}
                };
        end
        else if (inputs.decoded_instr.funct7 == f7_CSPECIALRW) begin // 0x01
            let ccsr_addr = inputs.decoded_instr.rs2;
            Bool addr_valid = fv_check_CapCSR_Addr(ccsr_addr); 
            Bool priv_valid = (inputs.cur_priv >= ccsr_addr[4:3]);
            Bool perm_valid = unpack(inputs.pcc.capability[123]);
            Bool all_valid = addr_valid && priv_valid && perm_valid;
            alu_outputs.ccsr_valid = (inputs.decoded_instr.rs1 != 0);
            // Access/read fault, or trying to write PCC
            if ((!all_valid) || (ccsr_addr == 0 && (inputs.decoded_instr.rs1 != 0))) begin
                alu_outputs.exc_code = (!(addr_valid && priv_valid) ? exc_code_ILLEGAL_INSTRUCTION : exc_code_PERMISSION_DENIED);
                alu_outputs.control = CONTROL_TRAP;
                alu_outputs.ccsr_valid = False;
                alu_outputs.val1 = change_tagged_addr(tc_zero,zeroExtend({pack(priv_valid), pack(perm_valid),pack(addr_valid)}));
            end
            else begin
                // Val1 => rd, Val2 => CCSR register
                alu_outputs.addr = change_tagged_addr(tc_zero,zeroExtend(ccsr_addr));
                alu_outputs.val1 = inputs.ccsr_val;
                alu_outputs.val2 = inputs.rs1_val;
            end
        end
        // This is an absolutely awful design. Why put a source register in the field that is the destination
        // for every other instruction, when the selector field (unique to this instruction) could be put there
        // instead, thereby preventing the need for an unnecessary special case to get the right registers for
        // this specific instruction?
        else if (inputs.decoded_instr.funct7 == f7_CCALLRET) begin // 0x7e
            let selector = instr_rs2 (inputs.instr);
            let cb2 = inputs.rs1_val;
            let cs2 = inputs.rs2_val;
            let check = fv_checkValid_CCALLRET(cb2,cs2,selector);
            if (selector == 5'h01) begin
                let new_pcc = fv_unseal(cs2,cb2);
                alu_outputs.addr = new_pcc;
                if (new_pcc.capability[1:0] != 2'b00) begin
                    alu_outputs.control = CONTROL_TRAP;
                    alu_outputs.exc_code = exc_code_INSTR_ADDR_MISALIGNED;
                end 
                else if (check != exc_code_NO_EXCEPTION) begin
                    alu_outputs.control = CONTROL_TRAP;
                    alu_outputs.exc_code = check;
                end
                else begin
                    alu_outputs.control = CONTROL_BRANCH;
                end
            end
            else begin
                alu_outputs.control = CONTROL_TRAP;
                alu_outputs.exc_code = check;
            end
        end
        else if (inputs.decoded_instr.funct7 == f7_MEMORYOP) begin // 0x00
            Bit#(5) op_spec = inputs.decoded_instr.rs2;
            Tagged_Capability controller = (op_spec[4] == 1'b1) ? inputs.rs1_val : inputs.ddc;
            alu_outputs.addr = controller;
			alu_outputs.val2 = inputs.rs1_val;
            let check = fv_checkMemoryTarget(controller, op_spec);
            if(check != exc_code_NO_EXCEPTION) begin
                alu_outputs.control  = CONTROL_TRAP;
                alu_outputs.exc_code = check;
            end
            else if (fv_isLoad(op_spec)) begin
                alu_outputs.op_stage2 = OP_Stage2_LD;
            end
            else if (fv_isStore(op_spec)) begin
                alu_outputs.op_stage2 = OP_Stage2_ST;
            end
            else begin
                alu_outputs.control  = CONTROL_TRAP;
            end
        end
        else begin
            alu_outputs.control = CONTROL_TRAP;
        end
    end
    else begin
        alu_outputs.control = CONTROL_TRAP;
    end
    return alu_outputs;
endfunction : fv_CHERI

// Any operations with opcode 0x5b, f3 0, and f7 0x7f.
// A number of these don't particularly fit with the general structure presented in the
// CHERI-RISC-V design. The elimination of the 256-bit capability format makes the calculation
// of some values awkward and unusual, whereas in MIPS they were immediately available. A good
// example is the definition of getperms. It is well suited to the 256-bit format given the
// distinction between hardware- and software-defined permissions (perms and uperms), but when
// only the 128-bit representation is used the separation looks irrational.
function ALU_Outputs fv_CINSPECT_ETC (ALU_Inputs inputs);
    let alu_outputs = alu_outputs_base;
    alu_outputs.op_stage2 = OP_Stage2_ALU;
    let rs1_cap  = inputs.rs1_val.capability;
    // Some CHERI ops have a 5-bit decoding value in the rs2 position rather than the
    // standard position used in the base RISC-V ISA.
    if      (inputs.decoded_instr.rs2 == f5_CGETPERM)   begin
        Bit #(15) perms = rs1_cap[127:113];
        // If we're mimicing the MIPS behaviour, we have a weird gap between perms and uperms
        Bit #(64) newVal = {49'b0, perms[14:0]};
        alu_outputs.val1 = change_tagged_addr(tc_zero, newVal);
    end
    else if (inputs.decoded_instr.rs2 == f5_CGETTYPE)   begin
        IntXL v = -1;
        // If sealed capability, return otype, otherwise -1.
        Bit #(64) newVal = fv_checkSealed(inputs.rs1_val) ? extend(fv_getOType(inputs.rs1_val)) : pack(v);
        alu_outputs.val1 = change_tagged_addr(tc_zero, newVal);
    end
    else if (inputs.decoded_instr.rs2 == f5_CGETBASE)   begin
        Bit #(64) newVal = fv_getBase(inputs.rs1_val)[63:0];
        alu_outputs.val1 = change_tagged_addr(tc_zero, newVal);
    end
    else if (inputs.decoded_instr.rs2 == f5_CGETLEN)    begin
        Bit#(64) newVal = fv_getLen(inputs.rs1_val);
        alu_outputs.val1 = change_tagged_addr(tc_zero, newVal);
    `ifdef CHERIDEBUG
        alu_outputs.debug_out = fv_getTop(inputs.rs1_val)[63:0];
    `endif
    end
    else if (inputs.decoded_instr.rs2 == f5_CGETTAG)    begin
        alu_outputs.val1 = change_tagged_addr(tc_zero, extend(inputs.rs1_val.tag));
    end
    else if (inputs.decoded_instr.rs2 == f5_CGETSEALED) begin
        Bit #(64) newVal = zeroExtend(pack(fv_checkSealed(inputs.rs1_val)));
        alu_outputs.val1 = change_tagged_addr(tc_zero, newVal);
    end
    else if (inputs.decoded_instr.rs2 == f5_CGETOFFSET) begin
        IntXL bot = unpack(fv_getBase(inputs.rs1_val)[63:0]);
        Bit #(64) newVal = pack(unpack(rs1_cap[63:0]) - bot);
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
        alu_outputs.val1 = inputs.rs1_val;
    end
    
    else if (inputs.decoded_instr.rs2 == f5_CJALR)      begin
        // Since we're not using a pointer, we only need to add 4 here.
        alu_outputs.val1 = change_tagged_addr(inputs.pcc, inputs.pcc.capability[63:0] + 4);
        alu_outputs.addr = inputs.rs1_val;
        let check = fv_checkValid_Execute (inputs.rs1_val);
        if (check == exc_code_NO_EXCEPTION) begin
            alu_outputs.exc_code = exc_code_INSTR_ADDR_MISALIGNED;
            alu_outputs.control = ((rs1_cap[1:0] == 2'b00) ? CONTROL_BRANCH : CONTROL_TRAP);
        end else begin
            alu_outputs.control = CONTROL_TRAP;
            alu_outputs.exc_code = check;
        end
    end
    // for ALU output values, we'll set val1[9:8] = quadrant, val1[7:0] = mask
    else if (inputs.decoded_instr.rs2 == f5_FASTCLEAR)  begin
        alu_outputs.val1 = change_tagged_addr(tc_zero, extend({inputs.instr[19:18], inputs.instr[17:15], inputs.instr[11:7]}));
        alu_outputs.op_stage2 = OP_Stage2_CLR;
    end
    else begin
        alu_outputs.control = CONTROL_TRAP;
    end
    return alu_outputs;
endfunction : fv_CINSPECT_ETC

// ----------------------------------------------------------------
// UTILITY FUNCTIONS

function Exc_Code fv_checkMemoryTarget(Tagged_Capability tc, Bit#(5) spec);
    Bit#(CLEN) cpv = tc.capability;
    let out = exc_code_NO_EXCEPTION;
    if (tc.tag == 1'b0)     // Tag not set
        out = exc_code_TAG_NOT_SET;
    else if (fv_checkSealed(tc)) // Capability sealed
        out = exc_code_CAPABILITY_SEALED;
    else if ((spec[3:2] == 2'b11)) // Illegal spec
        out = exc_code_ILLEGAL_INSTRUCTION;
    else if ((fv_isLoad(spec) && cpv[117] == 1'b0) || (fv_isLoad(spec) && cpv[116] == 1'b0)) // Store permission
        out = exc_code_PERMISSION_DENIED;
    else if (
        ((spec[1:0] == 2'b00) && fv_checkRange_withLen(tc,4'h1)) || // Bounds
        ((spec[1:0] == 2'b01) && fv_checkRange_withLen(tc,4'h2)) ||
        ((spec[1:0] == 2'b10) && fv_checkRange_withLen(tc,4'h4)) ||
        ((spec[1:0] == 2'b11) && fv_checkRange_withLen(tc,4'h8))
        )
        out = exc_code_BOUNDS_VIOLATED;
    return out; 
endfunction

function Exc_Code fv_checkOP_DDC(Tagged_Capability ddc, Addr target, Bool load, Bit#(4) len);
    let out = exc_code_NO_EXCEPTION;
    if (ddc.tag == 1'b0)
        out = exc_code_TAG_NOT_SET;
    else if (fv_checkSealed(ddc))
        out = exc_code_CAPABILITY_SEALED;
    else if (load && ddc.capability[116] == 1'b0)
        out = exc_code_PERMISSION_DENIED;
    else if (!load && ddc.capability[117] == 1'b0)
        out = exc_code_PERMISSION_DENIED;
    else if (!fv_checkRange_withLen(change_tagged_addr(ddc, target), len))
        out = exc_code_BOUNDS_VIOLATED;
    return out;
endfunction

function Bool fv_isLoad(Bit #(5) func5);
    return (func5[3] == 1'b0) || (func5[2:0] == 3'b101);
endfunction

function Bool fv_isStore(Bit #(5) func5);
    return !(func5[3] == 1'b0 || (func5[2] == 1'b1 && func5[1:0] > 2'b00));
endfunction

function Bool fv_checkSealed(Tagged_Capability tc);
    return (tc.capability[104] == 1'b1);
endfunction

function Bit #(6)  fv_getExp  (Tagged_Capability tc);
    return tc.capability[110:105];
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

function Int #(2) fv_baseCorrection (Bit #(64) a, Bit #(20) b, Bit #(6) e);
    Bit #(20) aMid = unpack(a[19+e:e]);
    Bit #(20) r = b - unpack(1 << 12);
    Bool c1 = (aMid < r);
    Bool c2 = (b < r);
    if (c1 && !c2)
        return -1;
    else if (c2 && !c1)
        return 1;
    else
        return 0;
endfunction

function Bit #(65) fv_topCorrection (Bit #(64) a, Bit #(20) b, Bit #(20) t, Bit #(6) e);
    Bit #(20) aMid = unpack(a[19+e:e]);
    Bit #(20) r = b - unpack(1 << 12);
    Bool c1 = (aMid < r);
    Bool c2 = (t < r);
    if (c1 && !c2)
        return 65'h1_ffff_ffff_ffff_ffff;
    else if (c2 && !c1)
        return 65'h0_0000_0000_0000_0001;
    else
        return 65'h0;
endfunction

function Bit #(65) fv_getBase (Tagged_Capability tc);
    // As defined in 3.3.8/page 81.
    Bit #(6)  e = fv_getExp(tc);
    Bit #(20) b = fv_getB(tc);
    Bit #(65) result = zeroExtend(pack(unpack(tc.capability[63:20+e]) + fv_baseCorrection(tc.capability[63:0],b,e)) << 20 + e);
    Bit #(65) b_val = zeroExtend(b << e);
    result = result + b_val;
    return result;
endfunction

function Bit #(65) fv_getTop  (Tagged_Capability tc);
`ifdef SIMPLERANGE
    Bit #(20) b = fv_getB(tc);
    Bit #(6)  e = fv_getExp(tc);
    Bit #(65) out = (extend(b+1) << e);
    return out;
`else
    // As defined in 3.3.8/page 81.
    Bit #(6)  e = fv_getExp(tc);
    Bit #(20) t = fv_getT(tc);
    Bit #(20) b = fv_getB(tc);
    Bit #(65) result = 65'h0;
    Bit #(65) addrbits = zeroExtend(tc.capability[63:0]) & (65'hffff_ffff_ffff_ffff << (20+e));
    Bit #(65) upperbits = (addrbits + fv_topCorrection(tc.capability[63:0],b,t,e)) << (20 + e);
    Bit #(65) lowerbits = zeroExtend(t << e);
    
    return upperbits+lowerbits;
`endif
endfunction

function Bit #(64) fv_getLen(Tagged_Capability tc);
`ifdef SIMPLERANGE
    return (64'b1 << fv_getExp(tc));
`else
    return (zeroExtend(fv_getT(tc) - fv_getB(tc)) << fv_getExp(tc));
`endif
endfunction

function Bit #(15) fv_getPerms (Tagged_Capability tc);
    return tc.capability[127:113];
endfunction

// Bool = trap status, capability = target.
// This checks capability dereferencing issues for execution (e.g. JALR).
function Exc_Code fv_checkValid_Execute (Tagged_Capability rs1);
    let out = exc_code_NO_EXCEPTION;
    Bit #(15) perms  = rs1.capability[127:113];
    Bool      sealed = fv_checkSealed(rs1);
    if (rs1.tag == 1'b0) // Tag violation
        out = exc_code_TAG_NOT_SET;
    if (sealed) // Seal violation
        out = exc_code_CAPABILITY_SEALED;
    if (perms[1] == 1'b0) // Permit_Execute violation
        out = exc_code_PERMISSION_DENIED;
    if (!fv_checkRange_withLen(rs1, 4'h04)) // Bounds violation - 4-byte value
        out = exc_code_BOUNDS_VIOLATED;
    return out;
endfunction


`ifdef SIMPLERANGE

function Addr fv_simple_lower(Tagged_Capability tc);
    let exp = fv_getExp(tc);
    return zeroExtend(fv_getB(tc) << exp);
endfunction

function Addr fv_simple_top(Tagged_Capability tc);
    let exp = fv_getExp(tc);
    return zeroExtend((fv_getB(tc) + 1) << exp);
endfunction

function Bool fv_simpleRange_withLen(Tagged_Capability tc, Bit#(4) bytes);
	Bit #(6) exp  = fv_getExp(tc);
    Addr lower = tc.capability[63:0];
    Addr upper = lower + zeroExtend(bytes) - 1;
    Bit#(64) b = zeroExtend(fv_getB(tc));
    return (lower >> exp == b) && (upper >> exp == b);
endfunction

function Bool fv_checkRange_simplified (Tagged_Capability rs1);
    return ((rs1.capability[63:0] >> fv_getExp(rs1)) == zeroExtend(fv_getB(rs1)));
endfunction

function Tuple3#(Exc_Code, Bool, Tagged_Capability) fv_setBounds_simple(Tagged_Capability old, Addr rt);
    let trap = exc_code_NO_EXCEPTION;  // Exception of any form - tag, seal etc
    let exact = True; // Whether the resulting bounds are exact or not
    let ret = tc_zero;
    if (old.tag == 1'b0)
        trap = exc_code_TAG_NOT_SET;
    else if (fv_checkSealed(old))
        trap = exc_code_CAPABILITY_SEALED;
    else begin
        // Derive and check bounds 
        //  - consider potential reduction in range for small values of rt.
        // Check new bounds are representable
        //  - "small compartments need to be at the bottom, in order to reach the top we need a bigger exponent"
        // Simplification - exact requires that rt is a power of 2.
        let requested_lower = tagged_addr(old);
        let requested_top = requested_lower + rt;
        let old_lower = fv_simple_lower(old);
        let old_top = fv_simple_top(old);
        if (requested_lower < old_lower || requested_top > old_top || requested_top <= requested_lower)
            trap = exc_code_BOUNDS_INVALID;
        else begin
            match  { 
                .exp,
                .bot,
                .bounds_exact
            } = fv_deriveBounds(requested_lower, rt);
            if (!fv_checkBounds(bot, exp, old_lower, old_top)) begin
                trap = exc_code_BOUNDS_INVALID;
            end
            ret = fv_assemble_new_bounds(old,bot,exp);
        end
    end
    return tuple3(trap, exact, ret);
endfunction

function Bit#(6) fv_getBExp(Bit#(7) leading);
    Bit#(6) exp = 0;
    if (leading < 44)
        exp = (44 - leading)[5:0];
    return exp;
endfunction

function Tuple3#(Bit#(6), Bit#(20), Bool) fv_deriveBounds(Bit#(64) base, Bit#(64) range);
    let exact = True;
    Bit#(6) chosenExp = 0;
    Bit#(6) rangeExp = pack(63 - countZerosMSB(range))[5:0];
    Bit#(64) top = base + range;
    // If we have an non-power-of-two range (range inexact) or we'll get one when we round the base down.
    if ((countOnes(range) > 1) || ((top & ~(64'hffff_ffff_ffff_ffff << rangeExp)) != 0)) begin
        rangeExp = fv_updateExp_increase(base,top,rangeExp);
        exact = False;
    end
    chosenExp = rangeExp;
    Bit#(6) baseExp = fv_getBExp(pack(countZerosMSB(base)));
    if (baseExp > rangeExp) begin // Need a larger exponent to represent base (range inexact)
        exact = False;
        chosenExp = baseExp;
    end
    let b = (base >> chosenExp)[19:0];
    return tuple3(chosenExp, b, exact);
endfunction

// Naive method was to just add 1, but doesn't account for carrying.
function Bit#(6) fv_updateExp_increase(Bit#(64) base, Bit#(64) top, Bit#(6) lastExp);
    Bit#(64) diff = ((base | ~top) >> lastExp);
    Bit#(7) increase = pack(countZerosLSB(diff));
    return (increase + zeroExtend(lastExp))[5:0];
endfunction

function Tagged_Capability fv_assemble_new_bounds(Tagged_Capability old, Bit#(20) newB, Bit#(6) newExp);
    return Tagged_Capability{
        tag: old.tag,
        capability: {old.capability[127:111], newExp, old.capability[104], newB, old.capability[83:0]}
    };
endfunction

function Bool fv_checkBounds(Bit#(20) newB, Bit#(6) newExp, Addr old_low, Addr old_top);
    Bit#(64) top = zeroExtend((newB + 1) << newExp);
    Bit#(64) bot = zeroExtend(newB << newExp);
    return (top <= old_top && bot >= old_low);
endfunction

`endif


function Bool fv_checkRange_withLen (Tagged_Capability rs1, Bit#(4) bytes);
`ifdef SIMPLERANGE
    return fv_simpleRange_withLen(rs1,bytes);
`else
    Bit #(64) base   = fv_getBase(rs1)[63:0];
    Bit #(64) top    = fv_getTop (rs1)[63:0];
    Bool out = True;
    Bit #(64) addr   = rs1.capability[63:0];
    if ((addr + zeroExtend(bytes) - 1 > top) || (addr < base)) // Bounds violation
        out = False;
    return out;
`endif
endfunction

function Bool fv_check_CapCSR_Addr(CapCSR_Addr addr);
    Bool base = ((addr == 5'h00) || (addr == 5'h01));
    Bool user = ((addr[4:2] == 3'b001) && addr[1:0] != 2'b01);
    Bool supr = ((addr[4:2] == 3'b011) && addr[1:0] != 2'b01);
    Bool mach = ((addr[4:2] == 3'b111) && addr[1:0] != 2'b01);
    return (base || user || supr || mach);
endfunction

function Bit#(24) fv_getOType(Tagged_Capability rs1);
    let rs1_cap = rs1.capability;
    return {rs1_cap[95:84], rs1_cap[75:64]};
endfunction

function Exc_Code fv_checkValid_Seal(Tagged_Capability rs, Tagged_Capability rt);
    let out = exc_code_NO_EXCEPTION;
    if (rs.tag == 0 || rt.tag == 0)                 // Tag violation
        out = exc_code_TAG_NOT_SET;
    else if (fv_checkSealed(rs) || fv_checkSealed(rt))   // Sealed violation
        out = exc_code_CAPABILITY_SEALED;
    else if (rt.capability[120] == 0)                    // Permit_Seal violation
        out = exc_code_PERMISSION_DENIED;
    else if (!fv_checkRange_withLen(rt, 4'h01))           // Bounds violation
        out = exc_code_BOUNDS_VIOLATED;
`ifdef SIMPLERANGE
    // SIMPLERANGE simply uses the TOP field as a permanent Otype field. We have a lower number of bits available, but
    // 2^20 should really be enough. With more consideration we could use some of the reserved bits, use a "0 = unsealed"
    // semantic or suchlike, but this would require a huge pile of adjustment which isn't particularly worthwhile in this
    // proof-of-concept
    else if (cap_addr(rt.capability) > 64'h0000_0000_000f_ffff)
        out = exc_code_BOUNDS_VIOLATED;
`else
    else if (cap_addr(rt.capability) > 64'h0000_0000_00ff_ffff)      // Max_OType violation
        out = exc_code_BOUNDS_VIOLATED;
    else if ((rs.capability[95:84] != 0) || (rs.capability[75:64] != 0)) // Bounds representation violation
        out = exc_code_BOUNDS_INVALID;
`endif
    return out;
endfunction

function Tagged_Capability fv_seal(Tagged_Capability rs, Tagged_Capability rt);
    let rsc = rs.capability;
    let rtc = rt.capability;
    `ifdef SIMPLERANGE
    return Tagged_Capability {
        tag: rs.tag,
        capability: {   
                      rsc[127:105], // perms, reserved, exponent
                      1'b1,         // sealed
                      rsc[103:84],  // bottom
                      rtc[19:0],    // otype
                      rsc[63:0]     // cursor address
                    }
    };
    `else
    return Tagged_Capability {
        tag: rs.tag,
        capability: {   
                      rsc[127:105], // perms, reserved, exponent
                      1'b1,         // sealed
                      rsc[103:96],  // bottom
                      rtc[23:12],   // otype_high
                      rsc[83:76],   // top
                      rtc[11:0],    // otype_low
                      rsc[63:0]     // cursor address
                    }
    };
    `endif
endfunction

function Exc_Code fv_checkValid_Unseal(Tagged_Capability rs, Tagged_Capability rt);
    let rsc = rs.capability;
    let rtc = rt.capability;
    let out = exc_code_NO_EXCEPTION;
    if (rs.tag == 0 || rt.tag == 0)                     // Tag violation
        out = exc_code_TAG_NOT_SET;
    else if (!fv_checkSealed(rs))                       // Sealed violation
        out = exc_code_CAPABILITY_NOT_SEALED;
    else if (fv_checkSealed(rt))
        out = exc_code_CAPABILITY_SEALED;
    else if ({rsc[95:84], rsc[75:64]} != rtc[23:0])          // OType violation
        out = exc_code_OBJECT_TYPE_INVALID;
    else if (rtc[122] == 0)                                  // Permit_Unseal violation
        out = exc_code_PERMISSION_DENIED;
    return out;
endfunction

function Tagged_Capability fv_unseal(Tagged_Capability rs, Tagged_Capability rt);
    let rsc = rs.capability;
    let rtc = rt.capability;
    Bit #(1) global = rsc[113] & rtc[113]; // Global bit set to AND of both input capabilities.
    `ifdef SIMPLERANGE
    return Tagged_Capability {
        tag: rs.tag,
        capability: { 
                      rsc[127:114], // perms 1-14
                      global,       // global bit (perm 0)
                      rsc[112:105], // reserved, exponent
                      1'b0,         // sealed
                      rsc[103:0]    // We can keep the bottom, otype and address fields exactly as they are
                    }
    };
    `else
    return Tagged_Capability {
        tag: rs.tag,
        capability: { 
                      rsc[127:114], // perms 1-14
                      global,       // global bit (perm 0)
                      rsc[112:105], // reserved, exponent
                      1'b0,         // sealed
                      rsc[103:96],  // bottom
                      12'b0,        // cleared otype_high
                      rsc[83:76],   // top
                      12'b0,        // cleared otype_low
                      rsc[63:0]     // cursor address
                    }
    };
    `endif
endfunction

function Exc_Code fv_checkValid_CCALLRET(Tagged_Capability cb, Tagged_Capability cs, Bit#(5) selector);
    let out = exc_code_NO_EXCEPTION;
    if (selector == 5'h1f) begin
        out = exc_code_CRETURN;
    end
    else if (selector == 5'h00) begin
        if (cb.tag == 1'b0 || cs.tag == 1'b0)
            out = exc_code_TAG_NOT_SET;
        else if (!fv_checkSealed(cb) || !fv_checkSealed(cs))
            out = exc_code_CAPABILITY_NOT_SEALED;
        else if (fv_getOType(cs) != fv_getOType(cb))
            out = exc_code_OBJECT_TYPE_INVALID;
        else if (cb.capability[114] == 1'b1 || cs.capability[114] == 1'b0)
            out = exc_code_PERMISSION_DENIED;
        else if (!fv_checkRange_withLen(cs,4'h4))
            out = exc_code_BOUNDS_VIOLATED;
        else
            out = exc_code_CCALL;
    end
    else if (selector == 5'h01) begin
        if (cb.tag == 1'b0 || cs.tag == 1'b0)
            out = exc_code_TAG_NOT_SET;
        else if (!fv_checkSealed(cb) || !fv_checkSealed(cs))
            out = exc_code_CAPABILITY_NOT_SEALED;
        else if (fv_getOType(cs) != fv_getOType(cb))
            out = exc_code_OBJECT_TYPE_INVALID;
        else if (cb.capability[114] == 1'b1 || cs.capability[114] == 1'b0)
            out = exc_code_PERMISSION_DENIED;
        else if (!fv_checkRange_withLen(cs,4'h4))
            out = exc_code_BOUNDS_VIOLATED;
        else
            out = fv_checkValid_Unseal(cs,cb);
    end
    else begin
        out = exc_code_ILLEGAL_INSTRUCTION;
    end
    return out;
endfunction

// ================================================================

endpackage
