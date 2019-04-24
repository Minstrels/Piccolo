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

package CPU;

// ================================================================
// This is the "Piccolo_V3" CPU, implementing the RISC-V ISA.
// RV32I, Privilege Levels U and M.
// This is a simple 3-stage in order pipeline.

`ifdef EXTERNAL_DEBUG_MODULE
`undef INCLUDE_GDB_CONTROL
`endif

// ================================================================
// Exports

export mkCPU;

// ================================================================
// BSV library imports

import Memory       :: *;
import FIFOF        :: *;
import FIFO         :: *;
import SpecialFIFOs :: *;
import GetPut       :: *;
import ClientServer :: *;
import Connectable  :: *;
import ConfigReg    :: *;

// ----------------
// BSV additional libs

import GetPut_Aux :: *;
import Semi_FIFOF :: *;

// ================================================================
// Project imports

import AXI4_Lite_Types :: *;

import ISA_Decls :: *;

`ifdef INCLUDE_TANDEM_VERIF
import Verifier  :: *;
import TV_Info   :: *;
`elsif RVFI
import Verifier  :: *;
import RVFI_DII  :: *;
`endif

`ifdef RVFI_DII
import Piccolo_RVFI_DII_Bridge :: *;
`endif

import GPR_RegFile :: *;
`ifdef ISA_F
import FPR_RegFile :: *;
`endif
import CSR_RegFile :: *;
import CPU_Globals :: *;
import CPU_IFC     :: *;

import CPU_Stage1 :: *;    // Fetch and Execute
import CPU_Stage2 :: *;    // Memory and long-latency ops
import CPU_Stage3 :: *;    // Writeback

import Near_Mem_IFC :: *;    // Caches or TCM

`ifdef Near_Mem_Caches
import Near_Mem_Caches :: *;
`endif

`ifdef Near_Mem_TCM
import Near_Mem_TCM :: *;
`endif

`ifdef INCLUDE_GDB_CONTROL
import Debug_Module :: *;
`endif

// ================================================================
// Major States of CPU

typedef enum {CPU_RESET1,
	      CPU_RESET2,

`ifdef INCLUDE_GDB_CONTROL
	      CPU_GDB_PAUSING,  // On GDB breakpoint, while waiting for fence completion
	      CPU_DEBUG_MODE,   // Stopped for debugger
`endif
	      CPU_RUNNING,      // Normal operation
	      CPU_CSRRX_STALL,
	      CPU_FENCE_I,      // While waiting for FENCE.I to complete in Near_Mem
	      CPU_FENCE,        // While waiting for FENCE to complete in Near_Mem
	      CPU_SFENCE_VMA,

	      CPU_WFI_PAUSED    // On WFI pause
   } CPU_State
deriving (Eq, Bits, FShow);

function Bool fn_is_running (CPU_State  cpu_state);
   return (   (cpu_state != CPU_RESET1)
	   && (cpu_state != CPU_RESET2)
`ifdef INCLUDE_GDB_CONTROL
	   && (cpu_state != CPU_GDB_PAUSING)
	   && (cpu_state != CPU_DEBUG_MODE)
`endif
	   );
endfunction

// ================================================================


(* synthesize *)
module mkCPU #(parameter Bit #(64)  pc_reset_value)  (CPU_IFC);

   // ----------------
   // General purpose registers and CSRs
   GPR_RegFile_IFC  gpr_regfile  <- mkGPR_RegFile;
`ifdef ISA_F
   FPR_RegFile_IFC  fpr_regfile  <- mkFPR_RegFile;
`endif
   CSR_RegFile_IFC  csr_regfile  <- mkCSR_RegFile;

   // Near mem (caches or TCM, for example)
   Near_Mem_IFC  near_mem <- mkNear_Mem;

   // ----------------
   // If using Direct Instruction Injection then make a
   // bridge that can insert instructions as if it were
   // an instruction cache.
`ifdef RVFI_DII
   Piccolo_RVFI_DII_Bridge_IFC rvfi_bridge <- mkPiccoloRVFIDIIBridge;
   IMem_IFC fake_imem = rvfi_bridge.insr_CPU;
`endif

/* `ifdef CHERI
   Reg #(Bool) clear_stall <- mkReg(False);
`endif*/ 

   // ----------------
   // For debugging

`ifdef CPU_VERBOSITY_1
   Bit #(4) initial_verbosity = 1;
`else
   Bit #(4) initial_verbosity = 0;
`endif

   // Verbosity: 0=quiet; 1=instruction trace; 2=more detail
   Reg #(Bit #(4))  cfg_verbosity <- mkConfigReg (initial_verbosity);

   // Verbosity is 0 as long as # of instrs retired is <= cfg_logdelay
   Reg #(Bit #(64))  cfg_logdelay <- mkConfigReg (0);

   // Current verbosity, taking into account log delay
   Bit #(4)  cur_verbosity = (  (csr_regfile.read_csr_minstret < cfg_logdelay)
			      ? 0
			      : cfg_verbosity);

   // 'inum': instruction number.
   // Should be equal to eventual 'instret' (instructions retired) number
   // for an instruction.

   Reg #(Bit #(64))  rg_inum <- mkRegU;
   Bit #(64)         mcycle = csr_regfile.read_csr_mcycle;

   // ----------------
   // Major CPU states
   Reg #(CPU_State)  rg_state    <- mkReg (CPU_RESET1);
   Reg #(Priv_Mode)  rg_cur_priv <- mkRegU;

   // ----------------
   // Pipeline stages

   CPU_Stage3_IFC stage3 <- mkCPU_Stage3 (cur_verbosity,
					  gpr_regfile,
`ifdef ISA_F
					  fpr_regfile,
`endif
					  csr_regfile);

   CPU_Stage2_IFC stage2 <- mkCPU_Stage2 (cur_verbosity, csr_regfile, near_mem.dmem);

   CPU_Stage1_IFC  stage1 <- mkCPU_Stage1 (cur_verbosity,
					   gpr_regfile,
`ifdef ISA_F
					   fpr_regfile,
`endif
					   csr_regfile,
`ifdef RVFI_DII
					   fake_imem,
`else
					   near_mem.imem,
`endif
					   stage2.out.bypass,
					   stage3.out.bypass,
					   rg_cur_priv);

   // ----------------
   // Halt requests (interrupts, debugger stop-request, or dcsr.step step-request).
   // We set this flag on an instruction Fetch and handle it on the next instruction-fetch.
   // When this flag is set, Stage1 is "frozen", i.e., its instruction
   // is not moved forward.  Once Stage2 and Stage3 have drained
   // (OSTATUS_EMPTY), the halt-request is handled.

   Reg #(Bool)  rg_halt <- mkReg (False);

   // Interrupt pending based on current priv, mstatus.ie, mie and mip registers
   Bool interrupt_pending = isValid (csr_regfile.interrupt_pending (rg_cur_priv));

   // ----------------
   // Reset requests and responses

   FIFOF #(Token)  f_reset_reqs <- mkFIFOF;
   FIFOF #(Token)  f_reset_rsps <- mkFIFOF;

   // ----------------
   // Communication to/from External debug module

`ifdef INCLUDE_GDB_CONTROL

   // Debugger run-control
   FIFOF #(Bool)  f_run_halt_reqs <- mkFIFOF;
   FIFOF #(Bool)  f_run_halt_rsps <- mkFIFOF;

   Reg #(Bool)  rg_stop_req      <- mkReg (False);    // stop-request from debugger
   Reg #(Bool)  rg_step_req      <- mkReg (False);    // step-request from dcsr.step
   Reg #(Bool)  rg_self_stop_req <- mkReg (False);    // self-stop-request on infinite loop

   // Debugger GPR read/write request/response
   FIFOF #(MemoryRequest  #(5,  XLEN)) f_gpr_reqs <- mkFIFOF1;
   FIFOF #(MemoryResponse #(    XLEN)) f_gpr_rsps <- mkFIFOF1;

`ifdef ISA_F
   // Debugger FPR read/write request/response
   FIFOF #(MemoryRequest  #(5,  FLEN)) f_fpr_reqs <- mkFIFOF1;
   FIFOF #(MemoryResponse #(    FLEN)) f_fpr_rsps <- mkFIFOF1;
`endif

   // Debugger CSR read/write request/response
   FIFOF #(MemoryRequest  #(12, XLEN)) f_csr_reqs <- mkFIFOF1;
   FIFOF #(MemoryResponse #(    XLEN)) f_csr_rsps <- mkFIFOF1;

`endif

   // ----------------
   // Tandem Verification

`ifdef INCLUDE_TANDEM_VERIF
    FIFOF #(Info_CPU_to_Verifier)  f_to_verifier <- mkFIFOF;

    // State for deciding when a new MIP command needs to be sent
    Reg #(MIP) rg_prev_mip <- mkRegU;
`elsif RVFI

    FIFOF #(RVFI_DII_Execution #(XLEN))  f_to_verifier <- mkFIFOF;
    Reg   #(Bool)                  rg_handler    <- mkReg (False);
    Reg   #(Bool)                  rg_donehalt       <- mkReg (False);    
    
    Reg #(MIP) rg_prev_mip <- mkConfigRegU;
    
`endif

   function Bool mip_cmd_needed ();
`ifdef INCLUDE_TANDEM_VERIF
      // If the MTIP, MSIP, or xEIP bits of MIP have changed, then send a MIP update
      MIP new_mip = csr_regfile.read_csr_mip;
      Bool mip_has_changed = ((new_mip.tips[m_Priv_Mode] != rg_prev_mip.tips[m_Priv_Mode]) ||
	                      (new_mip.sips[m_Priv_Mode] != rg_prev_mip.sips[m_Priv_Mode]) ||
	                      (new_mip.eips              != rg_prev_mip.eips));
      return mip_has_changed;
// Currently this breaks if included - for some reason, it prevents Stage 1 from dequeueing, so
// the pipeline ends up blocked.
`elsif RVFI
      MIP new_mip = csr_regfile.read_csr_mip;
      Bool mip_has_changed = ((new_mip.tips[m_Priv_Mode] != rg_prev_mip.tips[m_Priv_Mode]) ||
	                      (new_mip.sips[m_Priv_Mode] != rg_prev_mip.sips[m_Priv_Mode]) ||
	                      (new_mip.eips              != rg_prev_mip.eips));
      return mip_has_changed;
`else
      return False;
`endif
   endfunction: mip_cmd_needed
   
   


   // ================================================================
   // Debugging: print instruction trace info

   function fa_emit_instr_trace (inum, pc, instr, priv);
      action
	 if (cur_verbosity == 1)
	    $display ("inum:%0d  PC:0x%0h  instr:0x%0h  priv:%0d", inum, pc, instr, priv);
      endaction
   endfunction

   // ================================================================
   // CPI measurement in each 'run' (from Debug Mode pause to Debug Mode pause)

   Reg #(Bit #(64))  rg_start_CPI_cycles <- mkRegU;
   Reg #(Bit #(64))  rg_start_CPI_instrs <- mkRegU;

   function Action fa_report_CPI;
      action
	 Bit #(64) delta_CPI_cycles = mcycle - rg_start_CPI_cycles;
	 Bit #(64) delta_CPI_instrs = csr_regfile.read_csr_minstret - rg_start_CPI_instrs;

	 // Make delta_CPI_instrs at least 1, to avoid divide-by-zero
	 if (delta_CPI_instrs == 0)
	    delta_CPI_instrs = delta_CPI_instrs + 1;

	 // Report CPI to 1 decimal place.
	 let x = (delta_CPI_cycles * 10) / delta_CPI_instrs;
	 let cpi     = x / 10;
	 let cpifrac = x % 10;
	 $display ("CPI: %0d.%0d = (%0d/%0d) since last 'continue'",
		   cpi, cpifrac, delta_CPI_cycles, delta_CPI_instrs);
      endaction
   endfunction

   // ================================================================
   // Feed a new PC into Stage1
   // Feed a new PC into IMem (to do an instruction fetch).
   // Set rg_halt on debugger stop request or dcsr.step step request

   function Action fa_start_ifetch (Word next_pc, Priv_Mode priv, Bool trap);
      action
	 // Initiate the fetch
	 Bit #(1) sstatus_SUM = (csr_regfile.read_sstatus) [18];
	 Bit #(1) mstatus_MXR = (csr_regfile.read_mstatus) [19];
	 stage1.enq (next_pc, trap, priv,
		     sstatus_SUM,
		     mstatus_MXR,
		     csr_regfile.read_satp);

	 // Set rg_halt if requested.
	 Bool do_halt = False;

`ifdef INCLUDE_GDB_CONTROL
	 // Debugger stop-request
	 if ((! do_halt) && (rg_stop_req || rg_self_stop_req) && (cur_verbosity != 0))
	    $display ("    CPU.fa_start_ifetch: debugger/self stop-request: PC = 0x%08h", next_pc);

	 do_halt = (do_halt || rg_stop_req || rg_self_stop_req);

	 // dcsr.step step-request
	 if ((! do_halt) && rg_step_req && (cur_verbosity != 0))
	    $display ("    CPU.fa_start_ifetch: dcsr.step-request");

	 do_halt = (do_halt || rg_step_req);

	 // If single-step mode, set step-request to cause a stop at next fetch
	 if (csr_regfile.read_dcsr_step) begin
	    rg_step_req <= True;
	    if (cur_verbosity != 0)
	       $display ("    CPU.fa_start_ifetch: step request");
	 end
`endif

	 if (do_halt) begin
	    rg_halt <= True;
	    if (cur_verbosity > 1)
	       $display ("    CPU.fa_start_ifetch: rg_halt <= True");
	 end
      endaction
   endfunction

   // ================================================================
   // Actions to restart from Debug Mode (e.g., GDB 'continue' after a breakpoint)
   // We re-initialize CPI_instrs and CPI_cycles.

   function Action fa_restart (Addr resume_pc);
      action
	 fa_start_ifetch (resume_pc, rg_cur_priv, True);
	 stage1.set_full (True);
	 rg_state <= CPU_RUNNING;

`ifdef INCLUDE_GDB_CONTROL
	 // Notify debugger that we've started running
	 f_run_halt_rsps.enq (True);
`endif

	 rg_start_CPI_cycles <= mcycle;
	 rg_start_CPI_instrs <= csr_regfile.read_csr_minstret;

	 if (cur_verbosity != 0)
	    $display ("    restart with PC = 0x%0h", resume_pc);
      endaction
   endfunction

   // ================================================================
   // Debug tracing: show pipe state

   (* no_implicit_conditions, fire_when_enabled *)
   rule rl_show_pipe (   (cur_verbosity > 1)
		      && fn_is_running (rg_state)
		      && (rg_state != CPU_WFI_PAUSED));
      let mstatus = csr_regfile.read_mstatus;
      let misa    = csr_regfile.read_misa;
      $display ("================================================================");
      $display ("%0d: Pipeline State:  inum:%0d  cur_priv:%0d  mstatus:%0x",
		mcycle, rg_inum, rg_cur_priv, mstatus);
      $display ("    ", fshow (word_to_mstatus (misa, mstatus)));

      $display ("    Bypass S1 <= S3: ", fshow (stage3.out.bypass));
      $display ("    S3: ", fshow (stage3.out));
      $display ("    Bypass S1 <= S2: ", fshow (stage2.out.bypass));
      $display ("    S2: pc 0x%08h instr 0x%08h priv %0d",
		stage2.out.data_to_stage3.pc,
		stage2.out.data_to_stage3.instr,
		stage2.out.data_to_stage3.priv);
      $display ("        ", fshow (stage2.out));

      $display ("    S1: pc 0x%08h instr 0x%08h priv %0d",
		stage1.out.data_to_stage2.pc,
		stage1.out.data_to_stage2.instr,
		stage1.out.data_to_stage2.priv);
      $display ("        ", fshow (stage1.out));
   endrule

   // ================================================================
   // Reset

   rule rl_reset_start (rg_state == CPU_RESET1);
   
      // Guessing this reset is automatically queued in the testbench/by bluesim.
      // Either way, it might be what's blocking the program from running
      // let req <- pop (f_reset_reqs);

`ifdef INCLUDE_GDB_CONTROL
      rg_stop_req <= False;
      rg_step_req <= False;
      rg_self_stop_req <= False;
`endif

      /*$display ("================================================================");
      $write   ("CPU: Bluespec  RISC-V  Piccolo  v3.0");
      if (rv_version == RV32)
	 $display (" (RV32)");
      else
	 $display (" (RV64)");
      $display ("Copyright (c) 2016-2018 Bluespec, Inc. All Rights Reserved.");
      $display ("================================================================");*/

      gpr_regfile.server_reset.request.put (?);
`ifdef ISA_F
      fpr_regfile.server_reset.request.put (?);
`endif
      csr_regfile.server_reset.request.put (?);
      near_mem.server_reset.request.put (?);

      stage1.server_reset.request.put (?);
      stage2.server_reset.request.put (?);
      stage3.server_reset.request.put (?);

      rg_cur_priv <= m_Priv_Mode;
      rg_halt     <= False;
      rg_state    <= CPU_RESET2;
      rg_inum     <= 1;

      // These three lines are for simulation only:
      Bool v1 <- $test$plusargs ("v1");
      Bool v2 <- $test$plusargs ("v2");
      cfg_verbosity <= ((v2 ? 2 : (v1 ? 1 : 0)));
      /*
      cfg_verbosity <= 0; // for emulation, where above system tasks are invalid
      */

      if (cur_verbosity != 0)
	 $display ("%0d: CPU.rl_reset_start", mcycle);

`ifdef INCLUDE_TANDEM_VERIF
      let verif = getVerifierInfo(True, fromInteger(pc_tv_cmd), 0, 0, 0, True, fromInteger(tv_cmd_reset));
      f_to_verifier.enq (verif);
      rg_prev_mip <= mip_reset_value;
`endif
   endrule

   rule rl_reset_complete (rg_state == CPU_RESET2);
      let ack_gpr <- gpr_regfile.server_reset.response.get;
`ifdef ISA_F
      let ack_fpr <- fpr_regfile.server_reset.response.get;
`endif
      let ack_csr <- csr_regfile.server_reset.response.get;
      let ack_nm  <- near_mem.server_reset.response.get;

      let ack1 <- stage1.server_reset.response.get;
      let ack2 <- stage2.server_reset.response.get;
      let ack3 <- stage3.server_reset.response.get;

      f_reset_rsps.enq (?);
      
`ifdef CPU_VERBOSITY_1
        // XXX: Not sure if this is right, but it's better than having no 'if' at all
      if (cur_verbosity != 0)
	 $display ("%0d: CPU.reset_complete", mcycle);

      csr_regfile.write_dcsr_cause (DCSR_CAUSE_HALTREQ);
      rg_state <= CPU_DEBUG_MODE;

      if (cur_verbosity != 0)
	 $display ("    entering DEBUG_MODE");
`else
      WordXL dpc = truncate (pc_reset_value);
      fa_restart (dpc);
`endif
   endrule

   // ================================================================
   // Various conditions on the pipe

   Bool pipe_is_empty = (   (stage1.out.ostatus == OSTATUS_EMPTY)
			 && (stage2.out.ostatus == OSTATUS_EMPTY)
			 && (stage3.out.ostatus == OSTATUS_EMPTY));

   Bool pipe_has_busy = (   (stage1.out.ostatus == OSTATUS_BUSY)
			 || (stage2.out.ostatus == OSTATUS_BUSY)
			 || (stage3.out.ostatus == OSTATUS_BUSY));

   Bool pipe_has_nonpipe = (   (stage3.out.ostatus == OSTATUS_NONPIPE)
			    || (   (stage3.out.ostatus == OSTATUS_EMPTY)
				&& (stage2.out.ostatus == OSTATUS_NONPIPE))
			    || (   (stage3.out.ostatus == OSTATUS_EMPTY)
				&& (stage2.out.ostatus == OSTATUS_EMPTY)
				&& (stage1.out.ostatus == OSTATUS_NONPIPE)));

   Bool possible_ST_in_flight = (   (stage2.out.ostatus == OSTATUS_PIPE)
				 || (   (stage2.out.ostatus == OSTATUS_EMPTY)
				     && (stage3.out.ostatus == OSTATUS_PIPE)));

   Bool halting = (rg_halt || mip_cmd_needed || interrupt_pending);
   Bool stage1_halted = (   halting
			 && (   (stage1.out.ostatus == OSTATUS_PIPE)
			     || (stage1.out.ostatus == OSTATUS_NONPIPE))
			 && (stage2.out.ostatus == OSTATUS_EMPTY)
			 && (stage3.out.ostatus == OSTATUS_EMPTY));
   Bool stage1_send_mip_cmd = stage1_halted && mip_cmd_needed;
   Bool stage1_take_interrupt = stage1_halted && (! mip_cmd_needed) && interrupt_pending;
   Bool stage1_stop = stage1_halted && (! mip_cmd_needed) && (! interrupt_pending);

   Bool stage1_is_csrrx = ((stage1.out.ostatus == OSTATUS_PIPE)
			   && fn_instr_is_csrrx (stage1.out.data_to_stage2.instr));
   
   `ifdef CHERI
   Bool stage3_is_clearing = stage3.is_busy();
   `endif

   // ================================================================

`ifdef INCLUDE_TANDEM_VERIF
   rule rl_stage1_mip_cmd (   (rg_state == CPU_RUNNING)
			   && stage1_send_mip_cmd);
      MIP new_mip = csr_regfile.read_csr_mip;
      rg_prev_mip <= new_mip;

      Info_CPU_to_Verifier to_verifier = ?;
      to_verifier.pc = fromInteger(pc_tv_cmd);
      to_verifier.instr = fromInteger(tv_cmd_mip);
      to_verifier.data1 = zeroExtend (mip_to_word (new_mip));
      f_to_verifier.enq (to_verifier);

      if (cur_verbosity > 1)
	 $display ("%0d: CPU.rl_stage1_mip_cmd: new MIP = ", mcycle, fshow(new_mip));
   endrule
`elsif RVFI
   rule rl_stage1_mip_cmd (   (rg_state == CPU_RUNNING)
			   && stage1_send_mip_cmd);
      MIP new_mip = csr_regfile.read_csr_mip;
      rg_prev_mip <= new_mip;

      if (cur_verbosity > 1)
	 $display ("%0d: CPU.rl_stage1_mip_cmd: new MIP = ", mcycle, fshow(new_mip));
   endrule
`endif

   // ================================================================
   // PIPELINE BEHAVIOR (excluding nonpipe special instructions and exceptions)

   // We do not attempt to manage CSR values in the pipeline like GPRs
   // (read reg, writeback, bypassing) because of complexity: too many
   // CSRs can change simultaneously.  A CSRRx instruction in stage1
   // is stalled until downstream stages are empty. Then, we delay for
   // a cycle before fetching the next instr, since the fetch may need
   // the just-written CSR value.

    

   (* fire_when_enabled *)
    rule rl_pipe (   (rg_state == CPU_RUNNING)
		 && (! pipe_is_empty)
		 && (! pipe_has_nonpipe)
		 && (! stage1_halted)
		 `ifdef CHERI
         && (! stage3.is_busy)
         `endif
         );

        Bool stage3_full = (stage3.out.ostatus != OSTATUS_EMPTY);
        Bool stage2_full = (stage2.out.ostatus != OSTATUS_EMPTY);
        Bool stage1_full = (stage1.out.ostatus != OSTATUS_EMPTY);
        
        // ----------------
        // Stage3 sink (does regfile writebacks)
        
        if (stage3.out.ostatus == OSTATUS_PIPE) begin
	        stage3.deq; 
	        stage3_full = False;
        end

        // ----------------
        // Move instruction from Stage2 to Stage3

        if ((! stage3_full) && (stage2.out.ostatus == OSTATUS_PIPE)) begin
	        stage2.deq; stage2_full = False;
	        stage3.enq (stage2.out.data_to_stage3); stage3_full = True;
`ifdef INCLUDE_TANDEM_VERIF
	        // To Verifier
	        f_to_verifier.enq (stage2.out.to_verifier);
`elsif RVFI
            $display("pc_wdata in pipeline S2->S3: 0x%16h, instr: 0x%08h", stage2.out.data_to_stage3.pc, stage2.out.data_to_stage3.instr);
	        let outpacket = getRVFIInfoCondensed(stage2.out.data_to_stage3, ?, rg_inum, False,
	                                0, rg_handler,rg_donehalt);
	        rg_donehalt <= outpacket.rvfi_halt;
	        f_to_verifier.enq(outpacket);
	        rg_handler <= False;
`endif

	    // Accounting
	    rg_inum <= rg_inum + 1;
	    fa_emit_instr_trace (rg_inum, stage2.out.data_to_stage3.pc, 
	    stage2.out.data_to_stage3.instr, rg_cur_priv);
      end
      // TODO: Need to deal with next address for all behaviours.
`ifdef RVFI_DII
      let pcw = stage1.out.next_pc;
`endif
      // ----------------
      // Move instruction from Stage1 to Stage2
      // (but stall if Stage1 is CSRRx and rest of pipe is not empty)
      if (   (! halting)
	  && (! stage2_full)
	  && (stage1.out.ostatus == OSTATUS_PIPE)
	  && (! (stage1_is_csrrx && (   (stage2.out.ostatus != OSTATUS_EMPTY)
				     || (stage3.out.ostatus != OSTATUS_EMPTY)))))
	 begin
	    stage1.deq;                              stage1_full = False;
	    stage2.enq (stage1.out.data_to_stage2);  stage2_full = True;
	 end

      // ----------------
      // Feed Stage 1

      if ((! halting)
	  && (! stage1_full))
	 begin
	    // TODO: Do we need to stall for any capability CSRs? 
	    if (stage1_is_csrrx) begin
	       // Delay for a clock if Stage1 is CSRRx, since fa_start_ifetch reads some
	       // CSRs, which may be stale w.r.t. CSRRx
	       // TODO: delay only if the CSRRx is writing certain CSRs read by fa_start_ifetch?
	       //       i.e., csr_satp/csr_mstatus/csr_sstatus?
	       rg_state <= CPU_CSRRX_STALL;
	    end
	    else
	    /*`ifdef CHERI
	    if (!next_is_stall)
	    `endif*/
	    begin
	    `ifdef RVFI_DII
	       fa_start_ifetch (pcw, rg_cur_priv, False);
	    `else
	       fa_start_ifetch (stage1.out.next_pc, rg_cur_priv, False);
	    `endif
	       stage1_full = True;
	    end
	 end
	 /*`ifdef CHERI
	 clear_stall <= next_is_stall;
	 `endif*/
      stage3.set_full (stage3_full);
      stage2.set_full (stage2_full);
      stage1.set_full (stage1_full);
   endrule: rl_pipe

   // ================================================================
   // Restart the pipe after a CSRRX stall

   rule rl_stage1_restart_after_csrrx (rg_state == CPU_CSRRX_STALL);
      fa_start_ifetch (stage1.out.next_pc, rg_cur_priv, True);
      stage1.set_full (True);
      rg_state <= CPU_RUNNING;
      if (cur_verbosity > 1)
	 $display ("%0d: rl_stage1_restart_after_csrrx: inum:%0d  pc:%0x  cur_priv:%0d",
		   mcycle, rg_inum, stage1.out.next_pc, rg_cur_priv);
   endrule

   // ================================================================
   // Stage2: nonpipe special: all stage2 nonpipe behaviors are traps

   rule rl_stage2_nonpipe (   (rg_state == CPU_RUNNING)
			   && (stage3.out.ostatus == OSTATUS_EMPTY)
			   && (stage2.out.ostatus == OSTATUS_NONPIPE));
      if (cur_verbosity > 1)
	 $display ("%0d: CPU.rl_stage2_nonpipe", mcycle);

      let epc      = stage2.out.trap_info.epc;
      let exc_code = stage2.out.trap_info.exc_code;
      let badaddr  = stage2.out.trap_info.badaddr;
      let instr    = stage2.out.data_to_stage3.instr;

      // Take trap
      match {.next_pc,
	     .new_mstatus,
	     .mcause,
	     .new_priv}    <- csr_regfile.csr_trap_actions (rg_cur_priv,    // from priv
							    epc,
							    False,          // interrupt_req
							    exc_code,
							    badaddr);
      rg_cur_priv <= new_priv;

      fa_start_ifetch (next_pc, new_priv, True);
      stage1.set_full (True);
      stage2.set_full (False);

`ifdef INCLUDE_TANDEM_VERIF
      // Send trapping instr info to Tandem Verifier
      let to_verifier = getVerifierInfo(True,epc,next_pc,new_mstatus,mcause,True,instr);
      f_to_verifier.enq (to_verifier);
`elsif RVFI
      $display("pc_wdata in pipeline S2-TRAP: 0x%16h, instr: 0x%08h", stage2.out.data_to_stage3.pc, stage2.out.data_to_stage3.instr);
      let outpacket = getRVFIInfoCondensed(stage2.out.data_to_stage3, next_pc,
                                rg_inum, True, exc_code, rg_handler,rg_donehalt);
	  rg_donehalt <= outpacket.rvfi_halt;
	  f_to_verifier.enq(outpacket);
	  rg_handler <= True;
`endif

      // Accounting
      csr_regfile.csr_minstret_incr;
      rg_inum <= rg_inum + 1;

      fa_emit_instr_trace (rg_inum, epc, instr, rg_cur_priv);

      // Debug
      if (cur_verbosity != 0)
	 $display ("    mcause:0x%0h  epc 0x%0h  tval:0x%0h  new pc 0x%0h, new mstatus 0x%0h",
		   mcause, epc, badaddr, next_pc, new_mstatus);
   endrule : rl_stage2_nonpipe

   // ================================================================
   // Stage1: nonpipe special: MRET/SRET/URET

   rule rl_stage1_xRET (   (rg_state== CPU_RUNNING)
			&& (! halting)
			&& (stage3.out.ostatus == OSTATUS_EMPTY)
			&& (stage2.out.ostatus == OSTATUS_EMPTY)
			&& (stage1.out.ostatus == OSTATUS_NONPIPE)
			&& (   (stage1.out.control == CONTROL_MRET)
			    || (stage1.out.control == CONTROL_SRET)
			    || (stage1.out.control == CONTROL_URET)));

      // Return-from-exception actions on CSRs
      Priv_Mode from_priv = ((stage1.out.control == CONTROL_MRET) ?
			     m_Priv_Mode : ((stage1.out.control == CONTROL_SRET) ?
					    s_Priv_Mode : u_Priv_Mode));
      match { .next_pc, .new_priv, .new_mstatus } <- csr_regfile.csr_ret_actions (from_priv);
      rg_cur_priv <= new_priv;

      // Redirect PC
      fa_start_ifetch (next_pc, new_priv, True);
      stage1.set_full (True);
      let exc_code = stage1.out.trap_info.exc_code;
`ifdef INCLUDE_TANDEM_VERIF
      // Send info Tandem Verifier
      let to_verifier = getVerifierInfo(False,stage1.out.data_to_stage2.pc,
                        next_pc,new_mstatus,0,True,stage1.out.data_to_stage2.instr);
      f_to_verifier.enq (to_verifier);
`elsif RVFI
      $display("pc_wdata in pipeline S1-RET: 0x%16h, instr: 0x%08h", stage1.out.data_to_stage2.pc, stage1.out.data_to_stage2.instr);
      let outpacket = getRVFIInfoS1(stage1.out.data_to_stage2,?,rg_inum,False,0,rg_handler,rg_donehalt);
	  rg_donehalt <= outpacket.rvfi_halt;
	  f_to_verifier.enq(outpacket);
	  rg_handler <= False;
`endif

      // Accounting
      csr_regfile.csr_minstret_incr;
      rg_inum <= rg_inum + 1;

      // Debug
      fa_emit_instr_trace (rg_inum, stage1.out.data_to_stage2.pc, stage1.out.data_to_stage2.instr, rg_cur_priv);
      if (cur_verbosity != 0)
	 $display ("    xRET: next_pc:0x%0h  new mstatus:0x%0h  new priv:%0d", next_pc, new_mstatus, new_priv);
   endrule : rl_stage1_xRET

   // ================================================================
   // Stage1: nonpipe special: FENCE.I

   rule rl_stage1_FENCE_I (   (rg_state== CPU_RUNNING)
			   && (! halting)
			   && (stage3.out.ostatus == OSTATUS_EMPTY)
			   && (stage2.out.ostatus == OSTATUS_EMPTY)
			   && (stage1.out.ostatus == OSTATUS_NONPIPE)
			   && (stage1.out.control == CONTROL_FENCE_I));
      rg_state <= CPU_FENCE_I;
      near_mem.server_fence_i.request.put (?);

      if (cur_verbosity > 1)
	 $display ("%0d: CPU.rl_stage1_FENCE_I", mcycle);
   endrule

   rule rl_finish_FENCE_I (rg_state == CPU_FENCE_I);
      // Await mem system FENCE.I completion
      let dummy <- near_mem.server_fence_i.response.get;

      // Resume pipe
      rg_state <= CPU_RUNNING;
      fa_start_ifetch (stage1.out.next_pc, rg_cur_priv, True);
      stage1.set_full (True);
      let exc_code = stage1.out.trap_info.exc_code;
`ifdef INCLUDE_TANDEM_VERIF
      // Send info Tandem Verifier
      let to_verifier = getVerifierInfo(False,stage1.out.data_to_stage2.pc,
                        0,0,0,True,stage1.out.data_to_stage2.instr);
      f_to_verifier.enq (to_verifier);
`elsif RVFI
      $display("pc_wdata in pipeline S1-FENCEi: 0x%16h, instr: 0x%08h", stage1.out.data_to_stage2.pc, stage1.out.data_to_stage2.instr);
      let outpacket = getRVFIInfoS1(stage1.out.data_to_stage2,?,rg_inum,False,0,rg_handler,rg_donehalt);
	  rg_donehalt <= outpacket.rvfi_halt;
	  f_to_verifier.enq(outpacket);
	  rg_handler <= False;
`endif

      // Accounting
      csr_regfile.csr_minstret_incr;
      rg_inum <= rg_inum + 1;

      // Debug
      fa_emit_instr_trace (rg_inum, stage1.out.data_to_stage2.pc, stage1.out.data_to_stage2.instr, rg_cur_priv);
      if (cur_verbosity > 1)
	 $display ("    CPU.rl_finish_FENCE_I");
   endrule : rl_finish_FENCE_I

   // ================================================================
   // Stage1: nonpipe special: FENCE

   rule rl_stage1_FENCE (   (rg_state== CPU_RUNNING)
			 && (! halting)
			 && (stage3.out.ostatus == OSTATUS_EMPTY)
			 && (stage2.out.ostatus == OSTATUS_EMPTY)
			 && (stage1.out.ostatus == OSTATUS_NONPIPE)
			 && (stage1.out.control == CONTROL_FENCE));
      rg_state <= CPU_FENCE;
      near_mem.server_fence.request.put (?);

      if (cur_verbosity > 1)
	 $display ("%0d: CPU.rl_stage1_FENCE", mcycle);
   endrule

   // Finish FENCE

   rule rl_finish_FENCE (rg_state == CPU_FENCE);
      // Await mem system FENCE.I completion
      let dummy <- near_mem.server_fence.response.get;

      // Resume pipe
      rg_state <= CPU_RUNNING;
      fa_start_ifetch (stage1.out.next_pc, rg_cur_priv, True);
      stage1.set_full (True);
      let exc_code = stage1.out.trap_info.exc_code;
`ifdef INCLUDE_TANDEM_VERIF
      // Send info Tandem Verifier
      let to_verifier = getVerifierInfo(False,stage1.out.data_to_stage2.pc,
                        0,0,0,True,stage1.out.data_to_stage2.instr);
      f_to_verifier.enq (to_verifier);
`elsif RVFI
      $display("pc_wdata in pipeline S1-FENCE: 0x%16h, instr: 0x%08h", stage1.out.data_to_stage2.pc, stage1.out.data_to_stage2.instr);
      let outpacket = getRVFIInfoS1(stage1.out.data_to_stage2,?,rg_inum,False,0,rg_handler,rg_donehalt);
	  rg_donehalt <= outpacket.rvfi_halt;
	  f_to_verifier.enq(outpacket);
	  rg_handler <= False;
`endif

      // Accounting
      csr_regfile.csr_minstret_incr;
      rg_inum <= rg_inum + 1;

      // Debug
      fa_emit_instr_trace (rg_inum, stage1.out.data_to_stage2.pc, stage1.out.data_to_stage2.instr, rg_cur_priv);
      if (cur_verbosity > 1)
	 $display ("    CPU.rl_finish_FENCE");
   endrule : rl_finish_FENCE

   // ================================================================
   // Stage1: nonpipe special: SFENCE.VMA

    // XXX: Does this instruction even exist? It's not in spec 2.2!

   rule rl_stage1_SFENCE_VMA (   (rg_state== CPU_RUNNING)
			      && (! halting)
			      && (stage3.out.ostatus == OSTATUS_EMPTY)
			      && (stage2.out.ostatus == OSTATUS_EMPTY)
			      && (stage1.out.ostatus == OSTATUS_NONPIPE)
			      && (stage1.out.control == CONTROL_SFENCE_VMA));
      rg_state <= CPU_SFENCE_VMA;
      // Tell Near_Mem to do its SFENCE_VMA
      near_mem.sfence_vma;

      if (cur_verbosity > 1)
	 $display ("%0d: CPU.rl_stage1_SFENCE_VMA", mcycle);
   endrule: rl_stage1_SFENCE_VMA

   rule rl_finish_SFENCE_VMA (rg_state == CPU_SFENCE_VMA);
      // Resume pipe
      rg_state <= CPU_RUNNING;
      fa_start_ifetch (stage1.out.next_pc, rg_cur_priv, True);
      stage1.set_full (True);
      let exc_code = stage1.out.trap_info.exc_code;
`ifdef INCLUDE_TANDEM_VERIF
      // Send info Tandem Verifier
      let to_verifier = getVerifierInfo(False,stage1.out.data_to_stage2.pc,
                        0,0,0,True,stage1.out.data_to_stage2.instr);
      f_to_verifier.enq (to_verifier);
`elsif RVFI
      $display("pc_wdata in pipeline S1-SFENCE.VMA: 0x%16h, instr: 0x%08h", stage1.out.data_to_stage2.pc, stage1.out.data_to_stage2.instr);
      let outpacket = getRVFIInfoS1(stage1.out.data_to_stage2,?,rg_inum,False,0,rg_handler,rg_donehalt);
	  rg_donehalt <= outpacket.rvfi_halt;
	  f_to_verifier.enq(outpacket);
	  rg_handler <= False;
`endif

      // Accounting
      csr_regfile.csr_minstret_incr;
      rg_inum <= rg_inum + 1;

      // Debug
      fa_emit_instr_trace (rg_inum, stage1.out.data_to_stage2.pc, stage1.out.data_to_stage2.instr, rg_cur_priv);
      if (cur_verbosity > 1)
	 $display ("    CPU.rl_finish_SFENCE_VMA");
   endrule: rl_finish_SFENCE_VMA

   // ================================================================
   // Stage1: nonpipe special: WFI

   rule rl_stage1_WFI (   (rg_state== CPU_RUNNING)
		       && (! halting)
		       && (stage3.out.ostatus == OSTATUS_EMPTY)
		       && (stage2.out.ostatus == OSTATUS_EMPTY)
		       && (stage1.out.ostatus == OSTATUS_NONPIPE)
		       && (stage1.out.control == CONTROL_WFI));
      rg_state <= CPU_WFI_PAUSED;

      // Debug
      fa_emit_instr_trace (rg_inum, stage1.out.data_to_stage2.pc, stage1.out.data_to_stage2.instr, rg_cur_priv);
      if (cur_verbosity > 1)
	 $display ("    CPU.rl_stage1_WFI");
   endrule: rl_stage1_WFI

   // ----------------

   rule rl_WFI_resume ((rg_state == CPU_WFI_PAUSED) && csr_regfile.wfi_resume);
      // Debug
      if (cur_verbosity >= 1)
	 $display ("    WFI resume: inum:%0d  PC:0x%0h  instr:0x%0h  priv:%0d",
		   rg_inum, stage1.out.data_to_stage2.pc, stage1.out.data_to_stage2.instr, rg_cur_priv);

      // Resume pipe (it will handle the interrupt, if one is pending)
      rg_state <= CPU_RUNNING;
      fa_start_ifetch (stage1.out.next_pc, rg_cur_priv, True);
      stage1.set_full (True);
      let exc_code = stage1.out.trap_info.exc_code;
`ifdef INCLUDE_TANDEM_VERIF
      // Send info Tandem Verifier
      let to_verifier = getVerifierInfo(False,stage1.out.data_to_stage2.pc,
					    0,0,0,True,stage1.out.data_to_stage2.instr);
      f_to_verifier.enq (to_verifier);
`elsif RVFI
      $display("pc_wdata in pipeline S1-WFI: 0x%16h, instr: 0x%08h", stage1.out.data_to_stage2.pc, stage1.out.data_to_stage2.instr);
      let outpacket = getRVFIInfoS1(stage1.out.data_to_stage2,?,rg_inum,False,0,rg_handler,rg_donehalt);
	  rg_donehalt <= outpacket.rvfi_halt;
	  f_to_verifier.enq(outpacket);
	  rg_handler <= False;
`endif

      // Accounting
      csr_regfile.csr_minstret_incr;
      rg_inum <= rg_inum + 1;

   endrule: rl_WFI_resume

   // ----------------
   rule rl_reset_from_WFI (   (rg_state == CPU_WFI_PAUSED)
			   && f_reset_reqs.notEmpty);
      rg_state <= CPU_RESET1;
   endrule : rl_reset_from_WFI

   // ================================================================
   // Stage1: nonpipe traps (except BREAKs that enter Debug Mode)

`ifdef INCLUDE_GDB_CONTROL
   Bool break_into_Debug_Mode = (   (stage1.out.trap_info.exc_code == exc_code_BREAKPOINT)
				 && csr_regfile.dcsr_break_enters_debug (rg_cur_priv));
`else
   Bool break_into_Debug_Mode = False;
`endif

   let machine_mode_BREAK = (   (rg_cur_priv == m_Priv_Mode)
			     && (stage1.out.trap_info.exc_code == exc_code_BREAKPOINT));

   rule rl_stage1_trap (   (rg_state == CPU_RUNNING)
			&& (! halting)
			&& (stage3.out.ostatus == OSTATUS_EMPTY)
			&& (stage2.out.ostatus == OSTATUS_EMPTY)
			&& (stage1.out.ostatus == OSTATUS_NONPIPE)
			&& (stage1.out.control == CONTROL_TRAP)
			&& (! break_into_Debug_Mode));

      let epc      = stage1.out.trap_info.epc;
      let exc_code = stage1.out.trap_info.exc_code;
      let badaddr  = stage1.out.trap_info.badaddr;
      let instr    = stage1.out.data_to_stage2.instr;

      // Take trap
      match {.next_pc,
	     .new_mstatus,
	     .mcause,
	     .new_priv}    <- csr_regfile.csr_trap_actions (rg_cur_priv,    // from priv
							    epc,
							    False,          // interrupt_req,
							    exc_code,
							    badaddr);       // v1.10 - mtval
      rg_cur_priv <= new_priv;
      fa_start_ifetch (next_pc, new_priv, True);
      stage1.set_full (True);

`ifdef INCLUDE_TANDEM_VERIF
      // Send info on trapping instr Tandem Verifier
      let to_verifier = getVerifierInfo(True,epc,next_pc,new_mstatus,
					    mcause,True,instr);
      f_to_verifier.enq (to_verifier);
`elsif RVFI
      $display("pc_wdata in pipeline S1-TRAP: 0x%16h, instr: 0x%08h", stage1.out.data_to_stage2.pc, stage1.out.data_to_stage2.instr);
      let outpacket = getRVFIInfoS1(stage1.out.data_to_stage2,next_pc,rg_inum,True,exc_code,rg_handler,rg_donehalt);
	  rg_donehalt <= outpacket.rvfi_halt;
	  f_to_verifier.enq(outpacket);
	  rg_handler <= True;
`endif

      // Accounting
      csr_regfile.csr_minstret_incr;
      rg_inum <= rg_inum + 1;

      // Simulation heuristic: finish if trap back to this instr
`ifndef INCLUDE_GDB_CONTROL
`ifndef RVFI_DII
      if (epc == next_pc) begin
	 $display ("%0d: CPU.rl_stage1_trap: Tight infinite trap loop: pc 0x%0x instr 0x%08x", mcycle,
		   next_pc, instr);
	 fa_report_CPI;
	 $finish (0);
      end
`endif
`endif

      // Debug
      fa_emit_instr_trace (rg_inum, epc, instr, rg_cur_priv);
      if (cur_verbosity != 0) begin
	 $display ("%0d: CPU.rl_stage1_trap: priv:%0d  mcause:0x%0h  epc:0x%0h",
		   mcycle, rg_cur_priv, mcause, epc);
	 $display ("    tval:0x%0h  new pc:0x%0h  new mstatus:0x%0h", badaddr, next_pc, new_mstatus);
      end
   endrule: rl_stage1_trap

   // ================================================================
   // Stage1: nonpipe trap: BREAK into Debug Mode when dcsr.ebreakm/s/u is set
   // TODO: We are supposed to set mtval on a machine mode BREAK. Not doing so as we are breaking to the debugger

`ifdef INCLUDE_GDB_CONTROL
   rule rl_trap_BREAK_to_Debug_Mode (   (rg_state == CPU_RUNNING)
				     && (! halting)
				     && (stage3.out.ostatus == OSTATUS_EMPTY)
				     && (stage2.out.ostatus == OSTATUS_EMPTY)
				     && (stage1.out.ostatus == OSTATUS_NONPIPE)
				     && (stage1.out.control == CONTROL_TRAP)
				     && break_into_Debug_Mode);
      let pc    = stage1.out.data_to_stage2.pc;
      let instr = stage1.out.data_to_stage2.instr;

      $display ("%0d: CPU.rl_trap_BREAK_to_Debug_Mode: PC 0x%08h instr 0x%08h", mcycle, pc, instr);
      if (cur_verbosity > 1)
	 $display ("    Flushing caches");

      csr_regfile.write_dcsr_cause (DCSR_CAUSE_EBREAK);
      csr_regfile.write_dpc (pc);    // Where we'll resume on 'continue'
      rg_state <= CPU_GDB_PAUSING;

      // Flush both caches -- using the same interface as that used by FENCE_I
      near_mem.server_fence_i.request.put (?);

      // Notify debugger that we've halted
      f_run_halt_rsps.enq (False);
   endrule: rl_trap_BREAK_to_Debug_Mode

   // Handle the flush responses from the caches when the flush was initiated
   // on entering CPU_PAUSED state
   rule rl_BREAK_cache_flush_finish (rg_state == CPU_GDB_PAUSING);
      let ack <- near_mem.server_fence_i.response.get;
      rg_state <= CPU_DEBUG_MODE;

      fa_report_CPI;
   endrule

   // ----------------
   // Reset while in Debug Mode

   rule rl_reset_from_Debug_Mode (   (rg_state == CPU_DEBUG_MODE)
				  && f_reset_reqs.notEmpty);
      rg_state <= CPU_RESET1;
   endrule
`endif

   // ================================================================
   // EXTERNAL and GDB INTERRUPTS while running
   // We take an interrupt when Stage1 is frozen
   // and Stage2 and Stage3 have drained,
   // encapsulated in condition 'stage1_take_interrupt'

   rule rl_stage1_interrupt (csr_regfile.interrupt_pending (rg_cur_priv) matches tagged Valid .exc_code
			     &&& (rg_state== CPU_RUNNING)
			     &&& stage1_take_interrupt);

      let epc   = stage1.out.data_to_stage2.pc;
      let instr = stage1.out.data_to_stage2.instr;

      // Take trap
      match {.next_pc,
	     .new_mstatus,
	     .mcause,
	     .new_priv}    <- csr_regfile.csr_trap_actions (rg_cur_priv,    // from priv
							    epc,
							    True,           // interrupt_req,
							    exc_code,
							    0);             // badaddr
      rg_cur_priv <= new_priv;

      // Just enq the next_pc into stage1,
      // as the interrupt is taken
      Bit #(1) sstatus_SUM = new_mstatus [18];    // TODO: project new_mstatus to new_sstatus?
      Bit #(1) mstatus_MXR = new_mstatus [19];
      stage1.enq (next_pc, True, new_priv,
		  sstatus_SUM,
		  mstatus_MXR,
		  csr_regfile.read_satp);
      stage1.set_full (True);

      // Accounting: none (instruction is abandoned)

`ifdef INCLUDE_TANDEM_VERIF
      // Send info on trapping instr Tandem Verifier
      let to_verifier = getVerifierInfo(True,epc,next_pc,new_mstatus,
					    mcause,True,instr);
      f_to_verifier.enq (to_verifier);
`endif

      // Debug
      fa_emit_instr_trace (rg_inum, epc, instr, rg_cur_priv);
      if (cur_verbosity > 0)
	 $display ("%0d: CPU.rl_stage1_interrupt: epc 0x%0h  next PC 0x%0h  new_priv %0d  new mstatus 0x%0h",
		   mcycle, epc, next_pc, new_priv, new_mstatus);
   endrule: rl_stage1_interrupt

   // ----------------
   // Stage1: Handle debugger stop-request and dcsr.step step-request while running
   // and no interrupt pending.
   // rg_halt should have allowed the pipeline to drain,
   // i.e., stage1 has completed its fetch,
   // and stage2 and stage3 are empty

`ifdef INCLUDE_GDB_CONTROL
   rule rl_stage1_stop (   (rg_state== CPU_RUNNING)
			&& stage1_stop
			&& (rg_stop_req || rg_step_req || rg_self_stop_req));

      let pc    = stage1.out.data_to_stage2.pc;    // We'll retry this instruction on 'continue'
      let instr = stage1.out.data_to_stage2.instr;

      // Report CPI only stop-req, but not on step-req (where it's not very useful)
      if (rg_stop_req || rg_self_stop_req) begin
	 $display ("%0d: CPU.rl_stop: Stop for debugger. inum %0d priv %0d PC 0x%0h instr 0x%0h",
		   mcycle, rg_inum, rg_cur_priv, pc, instr);
	 fa_report_CPI;
      end
      else begin
	 $display ("%0d: CPU.rl_stop: Stop after single-step. PC = 0x%08h", mcycle, pc);
      end

      DCSR_Cause cause= (rg_stop_req ? DCSR_CAUSE_HALTREQ : DCSR_CAUSE_STEP);
      csr_regfile.write_dcsr_cause (cause);
      csr_regfile.write_dpc (pc);    // We'll retry this instruction on 'continue'
      rg_state    <= CPU_GDB_PAUSING;
      rg_halt     <= False;
      rg_stop_req <= False;
      rg_self_stop_req <= False;
      rg_step_req <= False;

      // Notify debugger that we've halted
      f_run_halt_rsps.enq (False);

      // Flush both caches -- using the same interface as that used by FENCE_I
      near_mem.server_fence_i.request.put (?);

      // Accounting: none (instruction is abandoned)
   endrule: rl_stage1_stop
`endif

   // ================================================================
   // ================================================================
   // ================================================================
   // DEBUGGER ACCESS

   // ----------------
   // Debug Module Run/Halt control

`ifdef INCLUDE_GDB_CONTROL
   rule rl_debug_run ((f_run_halt_reqs.first == True) && (rg_state == CPU_DEBUG_MODE));
      f_run_halt_reqs.deq;

      // Debugger 'resume' request (e.g., GDB 'continue' command)
      let dpc = csr_regfile.read_dpc;
      fa_restart (dpc);
      if (cur_verbosity > 1)
	 $display ("%0d: CPU.rl_debug_run: 'run' from dpc 0x%0h", mcycle, dpc);
   endrule

   rule rl_debug_run_ignore ((f_run_halt_reqs.first == True) && fn_is_running (rg_state));
      f_run_halt_reqs.deq;
      $display ("%0d: CPU.debug_run_ignore: ignoring 'run' command (CPU is not in Debug Mode)", mcycle);
   endrule

   rule rl_debug_halt ((f_run_halt_reqs.first == False) && fn_is_running (rg_state));
      f_run_halt_reqs.deq;

      // Debugger 'halt' request (e.g., GDB '^C' command)
      rg_stop_req <= True;
      if (cur_verbosity > 1)
	 $display ("%0d: CPU.rl_debug_halt", mcycle);
   endrule

   rule rl_debug_halt_ignore ((f_run_halt_reqs.first == False) && (! fn_is_running (rg_state)));
      f_run_halt_reqs.deq;

      $display ("%0d: CPU.rl_debug_halt_ignore: ignoring 'halt' (CPU already halted)", mcycle);
      $display ("    state = ", fshow (rg_state));
   endrule

   // ----------------
   // Debug Module GPR read/write

   rule rl_debug_read_gpr ((rg_state == CPU_DEBUG_MODE) && (! f_gpr_reqs.first.write));
      let req <- pop (f_gpr_reqs);
      Bit #(5) regname = req.address;
      let data = gpr_regfile.read_rs1_port2 (regname);
      let rsp = MemoryResponse {data: data};
      f_gpr_rsps.enq (rsp);
      if (cur_verbosity > 1)
	 $display ("%0d: CPU.rl_debug_read_gpr: Read reg %0d => 0x%0h", mcycle, regname, data);
   endrule

   rule rl_debug_write_gpr ((rg_state == CPU_DEBUG_MODE) && f_gpr_reqs.first.write);
      let req <- pop (f_gpr_reqs);
      Bit #(5) regname = req.address;
      let data = req.data;
      gpr_regfile.write_rd (regname, data);
      if (cur_verbosity > 1)
	 $display ("%0d: CPU.rl_debug_write_gpr: Write reg %0d => 0x%0h", mcycle, regname, data);
   endrule

`ifdef ISA_F
   // ----------------
   // Debug Module FPR read/write

   rule rl_debug_read_fpr ((rg_state == CPU_DEBUG_MODE) && (! f_fpr_reqs.first.write));
      let req <- pop (f_fpr_reqs);
      Bit #(5) regname = req.address;
      let data = fpr_regfile.read_rs1_port2 (regname);
      let rsp = MemoryResponse {data: data};
      f_fpr_rsps.enq (rsp);
      if (cur_verbosity > 1)
	 $display ("%0d: CPU.rl_debug_read_fpr: Read reg %0d => 0x%0h", mcycle, regname, data);
   endrule

   rule rl_debug_write_fpr ((rg_state == CPU_DEBUG_MODE) && f_fpr_reqs.first.write);
      let req <- pop (f_fpr_reqs);
      Bit #(5) regname = req.address;
      let data = req.data;
      fpr_regfile.write_rd (regname, data);
      if (cur_verbosity > 1)
	 $display ("%0d: CPU.rl_debug_write_fpr: Write reg %0d => 0x%0h", mcycle, regname, data);
   endrule
`endif

   // ----------------
   // Debug Module CSR read/write

   rule rl_debug_read_csr ((rg_state == CPU_DEBUG_MODE) && (! f_csr_reqs.first.write));
      let req <- pop (f_csr_reqs);
      Bit #(12) csr_addr = req.address;
      let m_data = csr_regfile.read_csr_port2 (csr_addr);
      let data = fromMaybe (?, m_data);
      let rsp = MemoryResponse {data: data};
      f_csr_rsps.enq (rsp);
      if (cur_verbosity > 1)
	 $display ("%0d: CPU.rl_debug_read_csr: Read csr %0d => 0x%0h", mcycle, csr_addr, data);
   endrule

   rule rl_debug_write_csr ((rg_state == CPU_DEBUG_MODE) && f_csr_reqs.first.write);
      let req <- pop (f_csr_reqs);
      Bit #(12) csr_addr = req.address;
      let data = req.data;
      csr_regfile.write_csr (csr_addr, data);
      if (cur_verbosity > 1)
	 $display ("%0d: CPU.rl_debug_write_csr: Write csr %0d => 0x%0h", mcycle, csr_addr, data);
   endrule
`endif

`ifdef RVFI_DII
   mkConnection(rvfi_bridge.trace_report, toGet(f_to_verifier));
`endif

   // ================================================================
   // ================================================================
   // ================================================================
   // INTERFACE

   // Reset
   interface Server  hart0_server_reset = toGPServer (f_reset_reqs, f_reset_rsps);

   // ----------------
   // SoC fabric connections

   // IMem to fabric master interface
   interface  imem_master = near_mem.imem_master;

   // DMem to fabric master interface
   interface  dmem_master = near_mem.dmem_master;

   // Near_Mem back door slave interface
   interface  near_mem_slave = near_mem.near_mem_slave;

   // ----------------
   // Interrupts

   method Action  external_interrupt_req (x) = csr_regfile.external_interrupt_req (x);
   method Action  software_interrupt_req (x) = csr_regfile.software_interrupt_req (x);
   method Action  timer_interrupt_req (x)    = csr_regfile.timer_interrupt_req (x);

   // ----------------
   // Optional interface to Tandem Verifier

`ifdef INCLUDE_TANDEM_VERIF

   interface Get to_verifier = toGet (f_to_verifier);
   
`elsif RVFI
`ifdef RVFI_DII

   interface rvfi_dii_server = rvfi_bridge.insr_inject;

`else

   interface Get to_verifier = toGet (f_to_verifier);
   method Bool halted = rg_donehalt;

`endif
`endif

   // ----------------
   // Optional interface to Debug Module

`ifdef INCLUDE_GDB_CONTROL
   // run-control, other
   interface Server  hart0_server_run_halt = toGPServer (f_run_halt_reqs, f_run_halt_rsps);

   interface Put  hart0_put_other_req;
      method Action  put (Bit #(4) req);
	 cfg_verbosity <= req;
      endmethod
   endinterface

   // GPR access
   interface MemoryServer  hart0_gpr_mem_server = toGPServer (f_gpr_reqs, f_gpr_rsps);

`ifdef ISA_F
   // FPR access
   interface MemoryServer  hart0_fpr_mem_server = toGPServer (f_fpr_reqs, f_fpr_rsps);
`endif

   // CSR access
   interface MemoryServer  hart0_csr_mem_server = toGPServer (f_csr_reqs, f_csr_rsps);
`endif

endmodule: mkCPU

// ================================================================

endpackage
