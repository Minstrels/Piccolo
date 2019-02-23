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

package GPR_RegFile;

// ================================================================
// GPR (General Purpose Register) Register File

// ================================================================
// Exports

export GPR_RegFile_IFC (..), mkGPR_RegFile;

// ================================================================
// BSV library imports

import ConfigReg    :: *;
import RegFile      :: *;
import FIFOF        :: *;
import GetPut       :: *;
import ClientServer :: *;

// BSV additional libs

import GetPut_Aux :: *;

// ================================================================
// Project imports

import ISA_Decls :: *;

// ================================================================

interface GPR_RegFile_IFC;
   // Reset
   interface Server #(Token, Token) server_reset;


`ifdef CHERI
   // Capability register read
   (* always_ready *)
   method Tagged_Capability read_rs1 (RegName rs1);
   (* always_ready *)
   method Tagged_Capability read_rs1_port2 (RegName rs1);   
   (* always_ready *)
   method Tagged_Capability read_rs2 (RegName rs2);
   // Capability register write
   (* always_ready *)
   method Action write_rd (RegName rd, Tagged_Capability rd_val);
   // Integer register write. Clears tag and upper XLEN bits
   (* always_ready *)
   method Action write_rd_int (RegName rd, WordXL rd_val);
   (* always_ready *)
   method Action clear_quarter (Bit #(2) QID, Bit #(8) Mask);
`else
   // GPR read
   (* always_ready *)
   method Word read_rs1 (RegName rs1);
   (* always_ready *)
   method Word read_rs1_port2 (RegName rs1);    // For debugger access only
   (* always_ready *)
   method Word read_rs2 (RegName rs2);
   // GPR write
   (* always_ready *)
   method Action write_rd (RegName rd, Word rd_val);
`endif

endinterface

// ================================================================
// Major states of mkGPR_RegFile module

typedef enum { RF_RESET_START, RF_RESETTING, RF_RUNNING
`ifdef CHERI
    , RF_CLEARING // CLEAR instruction in progress.
`endif
 } RF_State
deriving (Eq, Bits, FShow);

// ================================================================

(* synthesize *)
module mkGPR_RegFile (GPR_RegFile_IFC);

   Reg #(RF_State) rg_state      <- mkReg (RF_RESET_START);

   // Reset
   FIFOF #(Token) f_reset_rsps <- mkFIFOF;

   // General Purpose Registers
   // TODO: can we use Reg [0] for some other purpose?
`ifdef CHERI
   RegFile #(RegName, Tagged_Capability) regfile <- mkRegFileFull;
   // Starting register ID for CLEAR
   Reg #(Bit #(2)) rg_base <- mkRegU;
   // Bit mask for CLEAR
   Reg #(Bit #(8)) rg_mask <- mkRegU;
   // Currently examined register
   Reg #(Bit #(3)) rg_sub  <- mkRegU;
`else
   RegFile #(RegName, Word) regfile <- mkRegFileFull;
`endif

   // ----------------------------------------------------------------
   // CHERI-RISC-V Fast-clearing instructions
   // This loop clears a subset of the registers (up to 1/8 of the file)
   
`ifdef CHERI
   rule rl_fastclear (rg_state == RF_CLEARING);
      if (rg_mask[rg_sub] == 1)
         regfile.upd ({rg_base, rg_sub}, tc_zero);
      if (rg_sub == 7)
         rg_state <= RF_RUNNING;
      rg_sub <= rg_sub + 1;
   endrule
`endif

   // ----------------------------------------------------------------
   // Reset.
   // This loop initializes all GPRs to 0.
   // The RISC-V spec does not require this, but it's useful for debugging
   // and tandem verification

`ifdef INCLUDE_TANDEM_VERIF
   Reg #(RegName) rg_j <- mkRegU;    // reset loop index
`elsif RVFI
   Reg #(RegName) rg_j <- mkRegU;
`endif

   rule rl_reset_start (rg_state == RF_RESET_START);
      rg_state <= RF_RESETTING;
`ifdef INCLUDE_TANDEM_VERIF
      rg_j <= 1;
`elsif RVFI
      rg_j <= 1;
`endif
   endrule

    rule rl_reset_loop (rg_state == RF_RESETTING);
`ifdef INCLUDE_TANDEM_VERIF
        regfile.upd (rg_j, 0);
        rg_j <= rg_j + 1;
        if (rg_j == 31)
            rg_state <= RF_RUNNING;
`elsif RVFI
    `ifdef CHERI
        regfile.upd (rg_j, tc_default);
        rg_j <= rg_j + 1;
        if (rg_j == 31)
            rg_state <= RF_RUNNING;
    `else
        regfile.upd (rg_j, 0);
        rg_j <= rg_j + 1;
        if (rg_j == 31)
            rg_state <= RF_RUNNING;
    `endif
`else
      rg_state <= RF_RUNNING;
`endif
   endrule

   // ----------------------------------------------------------------
   // INTERFACE

   // Reset
   interface Server server_reset;
      interface Put request;
	 method Action put (Token token);
	    rg_state <= RF_RESET_START;

	    // This response is placed here, and not in rl_reset_loop, because
	    // reset_loop can happen on power-up, where no response is expected.
	    f_reset_rsps.enq (?);
	 endmethod
      endinterface
      interface Get response;
	 method ActionValue #(Token) get if (rg_state == RF_RUNNING);
	    let token <- pop (f_reset_rsps);
	    return token;
	 endmethod
      endinterface
   endinterface

   // GPR read
`ifdef CHERI
   method Tagged_Capability read_rs1 (RegName rs1);
      return ((rs1 == 0) ? 0 : regfile.sub (rs1));
   endmethod

   method Tagged_Capability read_rs1_port2 (RegName rs1);
      return ((rs1 == 0) ? 0 : regfile.sub (rs1));
   endmethod

   method Tagged_Capability read_rs2 (RegName rs2);
      return ((rs2 == 0) ? 0 : regfile.sub (rs2));
   endmethod
`else
   method Word read_rs1 (RegName rs1);
      return ((rs1 == 0) ? 0 : regfile.sub (rs1));
   endmethod

   method Word read_rs1_port2 (RegName rs1);        // For debugger access only
      return ((rs1 == 0) ? 0 : regfile.sub (rs1));
   endmethod

   method Word read_rs2 (RegName rs2);
      return ((rs2 == 0) ? 0 : regfile.sub (rs2));
   endmethod
`endif
   
   // GPR write
`ifdef CHERI

   // Write the register given a full capability.
   method Action write_rd_cap (RegName rd, Tagged_Capability rd_val);
      if (rd != 0) regfile.upd (rd, rd_val);
   endmethod
   
   // Write the register with only a 64-bit value available.
   method Action write_rd (RegName rd, WordXL rd_val);
      if (rd != 0) regfile.upd(rd, Tagged_Capability { tag: 0, capability: {64'h0, rd_val} );
   endmethod
   
   method Action clear_quarter (Bit #(2) QID, Bit #(8) Mask);
      rg_base  <= QID;
      rg_mask  <= Mask;
      rg_sub   <= 3'b000;
      rg_state <= RF_CLEARING;
   endmethod
`else
   method Action write_rd (RegName rd, Word rd_val);
      if (rd != 0) regfile.upd (rd, rd_val);
   endmethod
`endif
   
endmodule

// ================================================================

endpackage
