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

package CPU_Stage1;

// ================================================================
// This is Stage 1 of the "Piccolo" CPU.
// It contains the IF, RD, and EX functionality.
// IF: "Instruction Fetch".
// RD: "Register Read"
// EX: "Execute"

// Note: $displays are indented by (stage num x 4) spaces.
// for traditional pipeline display
//     IF
//         DM
//             WB
// i.e., 4 spaces for this stage.

// ================================================================
// Exports

export
CPU_Stage1_IFC (..),
mkCPU_Stage1;

// ================================================================
// BSV library imports

import FIFOF        :: *;
import GetPut       :: *;
import ClientServer :: *;
import ConfigReg    :: *;

// ----------------
// BSV additional libs

import Cur_Cycle :: *;

// ================================================================
// Project imports

import ISA_Decls        :: *;
import CPU_Globals      :: *;
import Near_Mem_IFC     :: *;
import GPR_RegFile      :: *;
import CSR_RegFile      :: *;
`ifdef CHERI
import EX_ALU_CHERI_functions :: *;
`else
import EX_ALU_functions :: *;
`endif

// ================================================================
// Interface

interface CPU_Stage1_IFC;
   // ---- Reset
   interface Server #(Token, Token) server_reset;

   // ---- Output
   (* always_ready *)
   method Output_Stage1 out;

   (* always_ready *)
   method Action deq;

   // ---- Input
   (* always_ready *)
   method Action enq (Addr next_pc, Bool trap, Priv_Mode priv, Bit #(1) sstatus_SUM, Bit #(1) mstatus_MXR, WordXL satp);

   (* always_ready *)
   method Action set_full (Bool full);
endinterface

// ================================================================
// Implementation module

module mkCPU_Stage1 #(Bit #(4)         verbosity,
		      GPR_RegFile_IFC  gpr_regfile,
`ifdef ISA_F
		      FPR_RegFile_IFC  fpr_regfile,
`endif
		      CSR_RegFile_IFC  csr_regfile,
		      IMem_IFC         icache,
		      Bypass           bypass_from_stage2,
		      Bypass           bypass_from_stage3,
		      Priv_Mode        cur_priv)
                    (CPU_Stage1_IFC);

   Reg #(Stage_Run_State) rg_run_state  <- mkReg (STAGE_RUNNING);

   FIFOF #(Token) f_reset_reqs <- mkFIFOF;
   FIFOF #(Token) f_reset_rsps <- mkFIFOF;

   Reg #(Bool) rg_full  <- mkReg (False);

`ifdef CHERI
   Reg #(Tagged_Capability) rg_ddc <- mkReg(tc_pcc_vals);
`endif

   // ----------------------------------------------------------------
   // BEHAVIOR

   rule rl_reset;
      f_reset_reqs.deq;
      rg_full <= False;
      f_reset_rsps.enq (?);
      rg_run_state <= STAGE_RUNNING;
   endrule

   // ----------------
   // Combinational output function

   function Output_Stage1 fv_out;
      // TODO: How are we handling memory changes? Where will PCC be derived instead of PC?
      // TODO: Discuss this. We could pass PCC capability bits all the way out to the icache and back, but is there a better way to do it?
      let pc            = icache.pc;
      // TODO: PCC is read-only except for internal manipulation. Are there any cases where we change permissions or bounds on PCC?
      //       If not, we can simply keep upper bits of PCC as a static value (at compile time?) and then only need to pass the standard 
      //       program counter in cache interactions.
`ifdef CHERI
      let pcc = change_tagged_addr(tc_pcc_vals, pc);
`endif
      
      let instr         = icache.instr;
      let decoded_instr = fv_decode (instr);
      let funct3        = decoded_instr.funct3;
      let csr           = decoded_instr.csr;

      // Register rs1 read and bypass
      let rs1 = decoded_instr.rs1;
      let rs1_val = gpr_regfile.read_rs1 (rs1);
      match { .busy1a, .rs1a } = fn_gpr_bypass (bypass_from_stage3, rs1, rs1_val);
      match { .busy1b, .rs1b } = fn_gpr_bypass (bypass_from_stage2, rs1, rs1a);
      Bool rs1_busy = (busy1a || busy1b);
      `ifdef CHERI
      Tagged_Capability rs1_val_bypassed = ((rs1 == 0) ? tc_zero : rs1b);
      `else
      Word rs1_val_bypassed = ((rs1 == 0) ? 0 : rs1b);
      `endif

      // Register rs2 read and bypass
      let rs2 = decoded_instr.rs2;
      let rs2_val = gpr_regfile.read_rs2 (rs2);
      match { .busy2a, .rs2a } = fn_gpr_bypass (bypass_from_stage3, rs2, rs2_val);
      match { .busy2b, .rs2b } = fn_gpr_bypass (bypass_from_stage2, rs2, rs2a);
      Bool rs2_busy = (busy2a || busy2b);
      `ifdef CHERI
      Tagged_Capability rs2_val_bypassed = ((rs2 == 0) ? tc_zero : rs2b);
      `else
      Word rs2_val_bypassed = ((rs2 == 0) ? 0 : rs2b);
      `endif
      
      // ----------------
      // CSR address-based protection checks
      Bool is_csrrx = ((decoded_instr.opcode == op_SYSTEM) && f3_is_CSRR_any (funct3));

      // CSR accessible at this privilege?
      Bool csr_priv_fault = (cur_priv < csr [9:8]);

      // CSR hpm counter read allowed?
      Bool csr_ctr_fault = csr_regfile.csr_counter_read_fault (cur_priv, csr);

      // CSR writing a read-only CSR?
      Bool csr_write_fault = (   (f3_is_CSRR_W (funct3) || (rs1 != 0))    // attempting write
			      && (csr [11:10] == 2'b11));                 // read-only csr

      // CSR reads
      // Note: csr should not be read for CSRRW[I] if Rd=0 (i.e., don't cause its side-effects).
      // But currently csr_reads are pure (no side effects), so we omit this check.

      let m_csr_val = csr_regfile.read_csr (csr);
      let csr_valid = (is_csrrx && isValid (m_csr_val)
		       && (! csr_priv_fault)
		       && (! csr_ctr_fault)
		       && (! csr_write_fault));

        let csr_val   = fromMaybe (?, m_csr_val);
`ifdef CHERI
        let ccsr_val  = (rs2 == 0) ? pcc :
                        (rs2 == 1) ? rg_ddc :
                        csr_regfile.read_csr_cap(rs2);
`endif

        // ALU function
        // TODO: Derive DDC value correctly.
        let alu_inputs = ALU_Inputs {
                   cur_priv:       cur_priv,
                   `ifdef CHERI
                   pcc:            pcc,
                   ddc:            rg_ddc,
                   `else
				   pc:             pc,
                   `endif
				   instr:          instr,
				   decoded_instr:  decoded_instr,
                   `ifdef CHERI
                   cap_mode:       False,
                   ccsr_val:       ccsr_val,
                   `endif
				   rs1_val:        rs1_val_bypassed,
				   rs2_val:        rs2_val_bypassed,
				   csr_valid:      csr_valid,
				   csr_val:        csr_val,
				   mstatus:        csr_regfile.read_mstatus,
				   misa:           csr_regfile.read_misa};

      let alu_outputs = fv_ALU (alu_inputs);
      Output_Stage1 output_stage1 = ?;

      // This stage is empty
      if (! rg_full) begin
	    output_stage1.ostatus = OSTATUS_EMPTY;
      end

      // Stall if ICache not ready
      else if (! icache.valid) begin
	    output_stage1.ostatus = OSTATUS_BUSY;
      end

      // Stall if bypass pending for rs1 or rs2
      else if (rs1_busy || rs2_busy) begin
	    output_stage1.ostatus = OSTATUS_BUSY;
      end

      // Trap on ICache exception
      else if (icache.exc) begin
	    output_stage1.ostatus   = OSTATUS_NONPIPE;
	    output_stage1.control   = CONTROL_TRAP;
	    output_stage1.trap_info = Trap_Info {epc:      pc,
					      exc_code: icache.exc_code,
					      badaddr:  pc};    // TODO: '?', perhaps?
      end

      // Trap on CSR access fault

      else if (is_csrrx && ((! isValid (m_csr_val)) || csr_priv_fault || csr_ctr_fault || csr_write_fault))
	 begin
	    output_stage1.ostatus   = OSTATUS_NONPIPE;
	    output_stage1.control   = CONTROL_TRAP;
	    output_stage1.trap_info = Trap_Info {epc:      pc,
						 exc_code: exc_code_ILLEGAL_INSTRUCTION,
						 badaddr:  zeroExtend(instr)}; // v1.10 - mtval
	  end

      // ALU outputs: normal, trap, and non-pipe instrs (CSR, MRET, FENCE.I, FENCE, WPI)
      else begin
	    let ostatus = (  (   (alu_outputs.control == CONTROL_STRAIGHT)
			   || (alu_outputs.control == CONTROL_BRANCH))
			? OSTATUS_PIPE
			: OSTATUS_NONPIPE);

	 // TODO: change name 'badaddr' to 'tval'
	    let badaddr = 64'b0;
	    if (alu_outputs.exc_code == exc_code_ILLEGAL_INSTRUCTION)
	        badaddr = zeroExtend (instr);
	    else if (alu_outputs.exc_code == exc_code_INSTR_ADDR_MISALIGNED)
	    `ifdef CHERI
	        badaddr = tagged_addr(alu_outputs.addr);    // branch target pc
	    `else
	        badaddr = alu_outputs.addr;    // branch target pc
	    `endif
	    let trap_info = Trap_Info {epc:      pc,
				    exc_code: alu_outputs.exc_code,
				    badaddr:  badaddr};  // v1.10 - mtval
`ifdef CHERI
        let next_pcc = ((alu_outputs.control == CONTROL_BRANCH) ? alu_outputs.addr : change_tagged_addr(pcc,pc+4));
	    let next_pc = ((alu_outputs.control == CONTROL_BRANCH) ? tagged_addr(alu_outputs.addr) : pc + 4);
`else
	    let next_pc = ((alu_outputs.control == CONTROL_BRANCH) ? alu_outputs.addr : pc + 4);
`endif
`ifdef RVFI
	    let info_RVFI = Data_RVFI_Stage1 {
	                        instr:          instr,
	                        rs1_addr:       rs1,
	                        rs2_addr:       rs2,
	                        rd_addr:        alu_outputs.rd,
	                        rd_alu:         (alu_outputs.op_stage2 == OP_Stage2_ALU),
	                        pc_rdata:       pc,
                            `ifdef CHERI
	                        rs1_data:       tagged_addr(rs1_val_bypassed),
	                        rs2_data:       tagged_addr(rs2_val_bypassed),
	                        pc_wdata:       tagged_addr(next_pcc),
	                        mem_wdata:      tagged_addr(alu_outputs.val2),
	                        rd_wdata_alu:   tagged_addr(alu_outputs.val1),
	                        mem_addr:       ((alu_outputs.op_stage2 == OP_Stage2_LD) || (alu_outputs.op_stage2 == OP_Stage2_ST))
                                                ? tagged_addr(alu_outputs.addr) : 0
                            `else
	                        rs1_data:       rs1_val_bypassed,
	                        rs2_data:       rs2_val_bypassed,
	                        pc_wdata:       next_pc,
	                        mem_wdata:      alu_outputs.val2,
	                        rd_wdata_alu:   alu_outputs.val1,
	                        mem_addr:       ((alu_outputs.op_stage2 == OP_Stage2_LD) || (alu_outputs.op_stage2 == OP_Stage2_ST)) ? alu_outputs.addr : 0
                            `endif
                        };
`endif
`ifdef CHERIDEBUG
        //alu_outputs.debug_out = tagged_addr(ccsr_val);
`endif
	    let data_to_stage2 = Data_Stage1_to_Stage2 {priv:      cur_priv,
						     pc:         pc,
						     instr:      instr,
						     
						     decoded:    decoded_instr,
						     
						     op_stage2:  alu_outputs.op_stage2,
						     rd:         alu_outputs.rd,
						     csr_valid:  alu_outputs.csr_valid,
`ifdef CHERI
                             ccsr_valid: alu_outputs.ccsr_valid,
`endif
`ifdef CHERIDEBUG
                             debug_out:  alu_outputs.debug_out,
`endif
						     addr:       alu_outputs.addr,
						     val1:       alu_outputs.val1,
						     val2:       alu_outputs.val2 
`ifdef RVFI
                            ,info_RVFI_s1: info_RVFI
`endif
						     };

	    output_stage1.ostatus        = ostatus;
	    output_stage1.trap_info      = trap_info;
	    output_stage1.control        = alu_outputs.control;
`ifdef CHERI
        output_stage1.next_pcc       = next_pcc;
`endif
	    output_stage1.next_pc        = next_pc;
	    output_stage1.data_to_stage2 = data_to_stage2;
      end
      return output_stage1;
   endfunction: fv_out

   // ================================================================
   // INTERFACE

   // ---- Reset
   interface server_reset = toGPServer (f_reset_reqs, f_reset_rsps);

   // ---- Output
   method Output_Stage1 out;
      return fv_out;
   endmethod
   
   method Action deq ();
      let out = fv_out;
      let data_to_stage2 = out.data_to_stage2;
      let trap_info = out.trap_info;
      Bool wrote_csr_minstret = False;
      if (data_to_stage2.csr_valid) begin
        `ifdef CHERI
        CSR_Addr csr_addr = truncate (tagged_addr(data_to_stage2.addr));
        WordXL   csr_val  = tagged_addr(data_to_stage2.val2);
        `else
        CSR_Addr csr_addr = truncate (data_to_stage2.addr);
        WordXL   csr_val  = data_to_stage2.val2;
        `endif
        csr_regfile.write_csr (csr_addr, csr_val);
        wrote_csr_minstret = ((csr_addr == csr_minstret) || (csr_addr == csr_minstreth));
        if (verbosity > 1)
            $display ("    S1: write CSR 0x%0h, val 0x%0h", csr_addr, csr_val);
      end
      `ifdef CHERI
      else if (data_to_stage2.ccsr_valid) begin
        CapCSR_Addr ccsr = truncate (tagged_addr(data_to_stage2.addr));
        Tagged_Capability new_val = data_to_stage2.val2;
        if (ccsr == ccsr_ddc) begin
            rg_ddc <= new_val;
        end
        else begin
            csr_regfile.write_csr_cap (ccsr, new_val);
        end
        //$display("CCSR val: %h", new_val);
      end
      //$display("Exception code on instr %h: %h", data_to_stage2.instr, trap_info.exc_code);
      //$display("CCSR val option 2: %h", tagged_addr(data_to_stage2.val1));
      //$display("Debug out: %h", data_to_stage2.debug_out);
      `endif
   endmethod

   // ---- Input
   method Action enq (Addr next_pc, Bool trap, Priv_Mode priv, Bit #(1) sstatus_SUM, Bit #(1) mstatus_MXR, WordXL satp);
      icache.req (f3_LW, next_pc, trap, priv, sstatus_SUM, mstatus_MXR, satp);

      if (verbosity > 0)
	 $display ("    S1.enq: 0x%08x", next_pc);
   endmethod

   method Action set_full (Bool full);
      rg_full <= full;
   endmethod
   
endmodule

// ================================================================

endpackage
