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

package CPU_Globals;

// ================================================================
// Types common to multiple CPU stages,
// including types communicated from stage to stage.

// ================================================================
// BSV library imports

// None

// ----------------
// BSV additional libs

// None

// ================================================================
// Project imports

import ISA_Decls :: *;

`ifdef INCLUDE_TANDEM_VERIF
import TV_Info   :: *;
`elsif RVFI
import RVFI_DII  :: *;
`endif

// ================================================================
// Run-state, for each stage

typedef enum { STAGE_RESETTING, STAGE_RUNNING } Stage_Run_State
deriving (Eq, Bits, FShow);

// ================================================================
// Output status of each stage

// EMPTY:   Stage has nothing in its input register
// BUSY:    Stage has input, but output is not ready
// PIPE:    Stage has input; driving normal output for pipeline
// NONPIPE: (In some stages) Stage has input; driving output is handled specially
//                (such as traps, CSR access, ...)

typedef enum {OSTATUS_EMPTY,
	      OSTATUS_BUSY,
	      OSTATUS_PIPE,
	      OSTATUS_NONPIPE
   } Stage_OStatus
deriving (Eq, Bits, FShow);

// ================================================================
// Bypass information
// From later to earlier stages.

// For an instruction's Rd (output GPR), a stage may:
// - have no Rd output
// - have Rd output, Rd is known but RdVal unknown
// - have Rd output, Rd is known and RdVal is known
// Note: a bypass has to stall if Rd matches and RdVal is unknown

typedef enum { BYPASS_RD_NONE, BYPASS_RD, BYPASS_RD_RDVAL } Bypass_State
deriving (Eq, Bits, FShow);

// We do not bypass CSR values, since we stall on CSRRxy insructions.

typedef struct {
   Bypass_State         bypass_state;
   RegName              rd;
   `ifdef CHERI
   Tagged_Capability    rd_val;
   `else
   Word                 rd_val;
   `endif
   } Bypass
deriving (Bits);

instance FShow #(Bypass);
   function Fmt fshow (Bypass x);
      let fmt0 = $format ("Bypass {");
      let fmt1 = ((x.bypass_state == BYPASS_RD_NONE)
		  ? $format ("Rd -")
		  : $format ("Rd %0d ", x.rd) + ((x.bypass_state == BYPASS_RD)
						 ? $format ("-")
						 : $format ("rd_val:%h", x.rd_val)));
      let fmt2 = $format ("}");
      return fmt0 + fmt1 + fmt2;
   endfunction
endinstance

// ----------------
// Baseline bypass info

Bypass no_bypass = Bypass {bypass_state: BYPASS_RD_NONE,
			   rd: ?,
			   rd_val: ? };

// ----------------
// Bypass functions for GPRs
// Returns '(busy, val)'
// 'busy' means that the RegName is valid and matches, but the value is not available yet
`ifdef CHERI
function Tuple2 #(Bool, Tagged_Capability) fn_gpr_bypass (Bypass bypass, RegName rd, Tagged_Capability rd_val);
`else
function Tuple2 #(Bool, Word) fn_gpr_bypass (Bypass bypass, RegName rd, Word rd_val);
`endif
   Bool busy = ((bypass.bypass_state == BYPASS_RD) && (bypass.rd == rd));
`ifdef CHERI
   Tagged_Capability val  = (  ((bypass.bypass_state == BYPASS_RD_RDVAL) && (bypass.rd == rd))
		? bypass.rd_val
		: rd_val);
`else
   Word val  = (  ((bypass.bypass_state == BYPASS_RD_RDVAL) && (bypass.rd == rd))
		? bypass.rd_val
		: rd_val);
`endif
   return tuple2 (busy, val);
endfunction

// ================================================================
// Trap information


// TODO: Change this for capability-length EPCC.
typedef struct {
   Addr      epc;
   Exc_Code  exc_code;
   Addr      badaddr;    // Only relevant for mem exceptions
   } Trap_Info
deriving (Bits, FShow);

// ================================================================
// Output from Stage 1

// Outputs from Stage1 to pipeline control
typedef enum {  CONTROL_STRAIGHT
	      , CONTROL_BRANCH
	      , CONTROL_FENCE
	      , CONTROL_FENCE_I
	      , CONTROL_SFENCE_VMA
	      , CONTROL_MRET
	      , CONTROL_SRET
	      , CONTROL_URET
	      , CONTROL_WFI
	      , CONTROL_TRAP
          `ifdef CHERI
          , CONTROL_CLEAR // Indicates a register-clearing instruction
          `endif
   } Control
deriving (Eq, Bits, FShow);

typedef struct {
   Stage_OStatus          ostatus;

   Control                control;

   Trap_Info              trap_info;

   // feedback
   // TODO: We only need one of these, but it requires restructuring work!
`ifdef CHERI
   Tagged_Capability      next_pcc;
`endif
   WordXL                 next_pc;

   // feedforward data
   Data_Stage1_to_Stage2  data_to_stage2;
   } Output_Stage1
deriving (Bits);

instance FShow #(Output_Stage1);
   function Fmt fshow (Output_Stage1 x);
      Fmt fmt = $format ("Output_Stage1");
      if (x.ostatus == OSTATUS_EMPTY)
	 fmt = fmt + $format (" EMPTY");
      else if (x.ostatus == OSTATUS_BUSY)
	 fmt = fmt + $format (" BUSY pc:%h", x.data_to_stage2.pc);
      else begin
	 if (x.ostatus == OSTATUS_NONPIPE) begin
	    fmt = fmt + $format (" NONPIPE: pc:%h", x.data_to_stage2.pc);
	    fmt = fmt + $format (" ", fshow (x.control));
	    fmt = fmt + $format (" ", fshow (x.trap_info));
	 end
	 else
	    fmt = fmt + $format (" PIPE: ", fshow (x.control), " ", fshow (x.data_to_stage2));

	 fmt = fmt + $format (" next_pc 0x%08h", x.next_pc);
      end
      return fmt;
   endfunction
endinstance

// ================================================================
// Data_Stage1_to_Stage2: Data output from Stage1 stage, input to DM stage

// Stage1 stage forwards, to DM, one of these 'opcodes'
// - ALU result (all non-mem, M and FD insructions)
// - DM request (Data Memory LD/ST/...)
// - Shifter Box request (SLL/SLLI, SRL/SRLI, SRA/SRAI)
// - MBox request (integer multiply/divide)
// - FDBox request (floating point ops)

typedef enum {  OP_Stage2_ALU         // Pass-through (non mem, M, FD, AMO)
	      , OP_Stage2_LD
	      , OP_Stage2_ST

`ifdef SHIFT_SERIAL
	      , OP_Stage2_SH
`endif

`ifdef ISA_M
	      , OP_Stage2_M
`endif

`ifdef ISA_A
	      , OP_Stage2_AMO
`endif

`ifdef ISA_FD
	      , OP_Stage2_FD
`endif
   } Op_Stage2
deriving (Eq, Bits, FShow);

typedef struct {
   Priv_Mode  priv;
   Addr       pc;
   Instr      instr;    // For debugging. Just funct3 is enough for functionality.
   Decoded_Instr decoded;
   Op_Stage2  op_stage2;
   RegName    rd;
   Bool       csr_valid;
`ifdef CHERI
   Bool       ccsr_valid;
   Tagged_Capability addr;
   Tagged_Capability val1;
   Tagged_Capability val2;
`else
   Addr       addr;     // Branch, jump: newPC
                        // Mem ops and AMOs: mem addr
                        // CSRRx: csr addr

   Word       val1;     // OP_Stage2_ALU: rd_val
                        // OP_Stage2_M and OP_Stage2_FD: arg1

   Word       val2;     // OP_Stage2_ALU: csr_val
                        // OP_Stage2_ST: store-val;
                        // OP_Stage2_M and OP_Stage2_FD: arg2
`endif
`ifdef RVFI
   Data_RVFI_Stage1 info_RVFI_s1;
`endif

   } Data_Stage1_to_Stage2
deriving (Bits);

`ifdef RVFI
  
typedef struct {
    Bit#(ILEN)  instr;
    // From decode
    Bit#(5)     rs1_addr;
    Bit#(5)     rs2_addr;
    Bit#(XLEN)  rs1_data;
    Bit#(XLEN)  rs2_data;
    Bit#(XLEN)  pc_rdata;
    // TODO: Exceptions?
    Bit#(XLEN)  pc_wdata;
    // TODO: Needs 0'ing when unused?
    Bit#(XLEN)  mem_wdata;

    // From ALU:
    Bit#(5)     rd_addr;
    // Might be killed by memory OPs.
    Bool        rd_alu;
    Bit#(XLEN)  rd_wdata_alu;
    
    Bit#(XLEN)  mem_addr;
    
} Data_RVFI_Stage1 deriving (Bits, Eq);

  
`endif


instance FShow #(Data_Stage1_to_Stage2);
   function Fmt fshow (Data_Stage1_to_Stage2 x);
      Fmt fmt =   $format ("data_to_Stage 2 {pc:%h  instr:%h  priv:%0d\n", x.pc, x.instr, x.priv);
      fmt = fmt + $format ("            op_stage2:", fshow (x.op_stage2), "  rd:%0d  csr_valid:", x.rd, fshow (x.csr_valid), "\n");
      fmt = fmt + $format ("            addr:%h  val1:%h  val2:%h}", x.addr, x.val1, x.val2);
      return fmt;
   endfunction
endinstance

// ================================================================
// Output from Stage 2

typedef struct {
   Stage_OStatus          ostatus;
   Trap_Info              trap_info;    // relevant if ostatus == OSTATUS_NONPIPE

   // feedback
   Bypass                 bypass;

   // feedforward data
   Data_Stage2_to_Stage3  data_to_stage3;
   
   // Verifier info
`ifdef INCLUDE_TANDEM_VERIF
   Info_CPU_to_Verifier   to_verifier;
`endif

   } Output_Stage2
deriving (Bits);

instance FShow #(Output_Stage2);
   function Fmt fshow (Output_Stage2 x);
      Fmt fmt = $format ("Output_Stage2");
      if (x.ostatus == OSTATUS_EMPTY)
	 fmt = fmt + $format (" EMPTY");
      else if (x.ostatus == OSTATUS_BUSY)
	 fmt = fmt + $format (" BUSY: pc:%0h", x.data_to_stage3.pc);
      else if (x.ostatus == OSTATUS_NONPIPE) begin
	 fmt = fmt + $format (" NONPIPE: ") + fshow (x.trap_info);
	 fmt = fmt + $format (" ") + fshow (x.trap_info);
      end
      else
	 fmt = fmt + $format (" PIPE: ") + fshow (x.data_to_stage3);
      return fmt;
   endfunction
endinstance

// ================================================================
// Data communicated from stage 2 to stage 3

typedef struct {
   Addr      pc;            // For debugging only
   Instr     instr;         // For debugging only
   Priv_Mode priv;

   Bool      rd_valid;
   RegName   rd;

   Bool      csr_valid;
   CSR_Addr  csr;
   
`ifdef CHERI
   Tagged_Capability      rd_val;
   Tagged_Capability      csr_val;
`else
   Word      rd_val;
   Word      csr_val;
`endif
   
`ifdef RVFI
   Data_RVFI_Stage2 info_RVFI_s2;
`endif
   
   } Data_Stage2_to_Stage3
deriving (Bits);

`ifdef RVFI
    
typedef struct {
    Data_RVFI_Stage1    stage1;
    // Hard to know what was written as SC pretends to write "0" on failure
    // instead of actual untouched value. So, indicate wmask = 0 perhaps?
    
    Bit#(MASKLEN)       mem_rmask;
    Bit#(MASKLEN)       mem_wmask;
    
}   Data_RVFI_Stage2 deriving (Bits);
    
`endif

instance FShow #(Data_Stage2_to_Stage3);
   function Fmt fshow (Data_Stage2_to_Stage3 x);
      Fmt fmt =   $format ("data_to_Stage3 {pc:%h  instr:%h  priv:%0d\n", x.pc, x.instr, x.priv);
      fmt = fmt + $format ("        rd_valid:", fshow (x.rd_valid), " rd:%0d  rd_val:%h\n", x.rd, x.rd_val);
      fmt = fmt + $format ("        csr_valid:", fshow (x.csr_valid), " csr:%h  csr_val:%h", x.csr, x.csr_val, "}");
      return fmt;
   endfunction
endinstance

// ================================================================
// Output from Stage 3

typedef struct {
   Stage_OStatus  ostatus;
   Bypass         bypass;
   } Output_Stage3
deriving (Bits);

`ifdef CHERI
// TODO: FPClear?
function Bool instr_is_clear(Instr ins);
    //opcode 0x5b, f3 0, and f7 0x7f.
    return (
            (instr_opcode(ins) == op_CAP) && 
            (instr_funct3(ins) == 3'b000) &&
            ((instr_rs2(ins)   == 5'hd) || (instr_rs2(ins) == 5'h10)) &&
            (instr_funct7(ins) == f7_CAPINSPECT)
           );
endfunction
`endif

instance FShow #(Output_Stage3);
   function Fmt fshow (Output_Stage3 x);
      Fmt fmt = $format ("Output_Stage3");
      if (x.ostatus == OSTATUS_EMPTY)
	 fmt = fmt + $format (" EMPTY");
      else if (x.ostatus == OSTATUS_BUSY)
	 fmt = fmt + $format (" BUSY");
      else if (x.ostatus == OSTATUS_PIPE)
	 fmt = fmt + $format (" PIPE");
      else if (x.ostatus == OSTATUS_NONPIPE)
	 fmt = fmt + $format (" NONPIPE");
      return fmt;
   endfunction
endinstance

// ================================================================

endpackage
