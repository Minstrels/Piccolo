/*-
 * Copyright (c) 2018 Jack Deeley
 * Copyright (c) 2018 Peter Rugg
 * All rights reserved.
 *
 * This software was developed by SRI International and the University of
 * Cambridge Computer Laboratory (Department of Computer Science and
 * Technology) under DARPA contract HR0011-18-C-0016 ("ECATS"), as part of the
 * DARPA SSITH research programme.
 *
 * @BERI_LICENSE_HEADER_START@
 *
 * Licensed to BERI Open Systems C.I.C. (BERI) under one or more contributor
 * license agreements.  See the NOTICE file distributed with this work for
 * additional information regarding copyright ownership.  BERI licenses this
 * file to you under the BERI Hardware-Software License, Version 1.0 (the
 * "License"); you may not use this file except in compliance with the
 * License.  You may obtain a copy of the License at:
 *
 *   http://www.beri-open-systems.org/legal/license-1-0.txt
 *
 * Unless required by applicable law or agreed to in writing, Work distributed
 * under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * @BERI_LICENSE_HEADER_END@
 */

package Verifier;


`ifdef INCLUDE_TANDEM_VERIF
import TV_Info :: *;
`elsif RVFI
import RVFI_DII :: *;
`endif
import ISA_Decls   :: *;
import CPU_Globals :: *;

`ifdef RVFI
// This function relies on info that is only passed in RVFI-mode.

Bit#(32) ecall_insn = 32'h73;

function RVFI_DII_Execution #(XLEN) getRVFIInfoCondensed(
            // Using the full data gives us access to rd_valid and a few other fields.
            Data_Stage2_to_Stage3   data_s2_s3,
            WordXL                  trapPC,
            Bit#(64)                order,
            Bool                    isTrap,
            Exc_Code                exc,
            Bool                    handler,
            Bool                    halted
            );
            
    Data_RVFI_Stage2 s2 = data_s2_s3.info_RVFI_s2;
    Data_RVFI_Stage1 s1 = s2.stage1;
    
    return RVFI_DII_Execution {
        rvfi_order:     order,
        // Not all traps are relevant in the Clifford-RVFI framework, e.g. page faults.
        rvfi_trap:      isTrap,
        rvfi_halt:      (halted) ? True : (data_s2_s3.instr == ecall_insn),
        rvfi_intr:      handler,
        rvfi_insn:      data_s2_s3.instr,
        rvfi_rs1_addr:  s1.rs1_addr,
        rvfi_rs2_addr:  s1.rs2_addr,
        rvfi_rd_addr:   data_s2_s3.rd_valid ? data_s2_s3.rd : 0,
        rvfi_rs1_data:  s1.rs1_data,
        rvfi_rs2_data:  s1.rs2_data,
        rvfi_pc_rdata:  data_s2_s3.pc,
        rvfi_pc_wdata:  isTrap ? trapPC : s1.pc_wdata,
        rvfi_mem_wdata: s1.mem_wdata,
        rvfi_mem_addr:  s1.mem_addr,
        rvfi_mem_rmask: s2.mem_rmask,
        rvfi_mem_wmask: s2.mem_wmask,
        `ifdef CHERI
        rvfi_rd_wdata:  data_s2_s3.rd == 0 ? 0 : tagged_addr(data_s2_s3.rd_val),
        rvfi_mem_rdata: tagged_addr(data_s2_s3.rd_val)
        `else
        rvfi_rd_wdata:  data_s2_s3.rd == 0 ? 0 : data_s2_s3.rd_val,
        rvfi_mem_rdata: data_s2_s3.rd_val
        `endif
    };
endfunction : getRVFIInfoCondensed
            
            
            
function RVFI_DII_Execution #(XLEN) getRVFIInfoS1 (
            Data_Stage1_to_Stage2   data_s1_s2,
            WordXL                  next_pc,
            Bit#(64)                order,
            Bool                    isTrap,
            Exc_Code                exc,
            Bool                    handler,
            Bool                    halted
            );
    
    Data_RVFI_Stage1 s1 = data_s1_s2.info_RVFI_s1;
    
    return RVFI_DII_Execution {
        rvfi_order:     order,
        `ifdef CHERI
        rvfi_trap:      ( isTrap ? ((exc[0] == 1'b0 && exc < 7) || exc > 16) : (False) ),
        `else
        rvfi_trap:      ( isTrap ? ((exc[0] == 1'b0 && exc < 7)) : (False)),
        `endif
        rvfi_halt:      (halted) ? True : (data_s1_s2.instr == ecall_insn),
        rvfi_intr:      handler,
        rvfi_insn:      data_s1_s2.instr,
        rvfi_rs1_addr:  s1.rs1_addr,
        rvfi_rs2_addr:  s1.rs2_addr,
        rvfi_rs1_data:  s1.rs1_data,
        rvfi_rs2_data:  s1.rs2_data,
        rvfi_pc_rdata:  data_s1_s2.pc,
        rvfi_pc_wdata:  isTrap ? next_pc : s1.pc_wdata,
        rvfi_mem_addr:  s1.mem_addr,
        // Although we know what rd *would* be, the fact that we're using this function
        // means we can't have actually written to it.
        rvfi_rd_addr:   0,
        rvfi_rd_wdata:  0,
        rvfi_mem_rmask: 0,
        rvfi_mem_wmask: 0,
        rvfi_mem_wdata: 0,
        rvfi_mem_rdata: 0
    };
endfunction : getRVFIInfoS1

`elsif INCLUDE_TANDEM_VERIF
/*
typedef struct {
   Bool       exc_taken;
   Bit #(64)  pc;
   Bit #(64)  addr;
   Bit #(64)  data1;
   Bit #(64)  data2;
   Bool       instr_valid;
   Bit #(32)  instr;
} Info_CPU_to_Verifier deriving (Bits, FShow);*/

function Info_CPU_to_Verifier getVerifierInfo(Bool exc, Bit#(64) pc, Bit#(64) addr,
                                    Bit#(64) data1, Bit#(64) data2, Bool valid, Bit#(32) instr) ;
    return Info_CPU_to_Verifier {
        exc_taken:   exc,
        pc:          pc,
        addr:        addr,
        data1:       data1,
        data2:       data2,
        instr_valid: valid,
        instr:       instr
    };
endfunction

`endif

function Bit #(MASKLEN) getMemMask(Bit #(3) f3, Bit #(XLEN) addr);
    Bit #(MASKLEN) result    = 0;
`ifdef RV64
    Bit #(3)  addr_lsbs = addr [2:0];
`else
    Bit #(2)  addr_lsbs = addr [1:0];
`endif

    case (f3)
        f3_LB: case (addr_lsbs)
		    'h0: result = zeroExtend(4'b0001);
		    'h1: result = zeroExtend(4'b0010);
		    'h2: result = zeroExtend(4'b0100);
		    'h3: result = zeroExtend(4'b1000);
`ifdef RV64
		    'h4: result = 8'b0001_0000;
		    'h5: result = 8'b0010_0000;
		    'h6: result = 8'b0100_0000;
		    'h7: result = 8'b1000_0000;
`endif
	        endcase
        f3_LBU: case (addr_lsbs)
		    'h0: result = zeroExtend(4'b0001);
		    'h1: result = zeroExtend(4'b0010);
		    'h2: result = zeroExtend(4'b0100);
		    'h3: result = zeroExtend(4'b1000);
`ifdef RV64
		    'h4: result = 8'b0001_0000;
		    'h5: result = 8'b0010_0000;
		    'h6: result = 8'b0100_0000;
		    'h7: result = 8'b1000_0000;
`endif
	        endcase

        f3_LH: case (addr_lsbs)
		    'h0: result = zeroExtend(4'b0011);
		    'h2: result = zeroExtend(4'b1100);
`ifdef RV64
		    'h4: result = 8'b0011_0000;
		    'h6: result = 8'b1100_0000;
`endif
	        endcase
        f3_LHU: case (addr_lsbs)
		    'h0: result = zeroExtend(4'b0011);
		    'h2: result = zeroExtend(4'b1100);
`ifdef RV64
		    'h4: result = 8'b0011_0000;
		    'h6: result = 8'b1100_0000;
`endif
	        endcase

        f3_LW: case (addr_lsbs)
		    'h0: result = zeroExtend(4'b1111);
`ifdef RV64
		    'h4: result = 8'b1111_0000;
`endif
	        endcase
	     
	     // LWU and LD only appear in RV64I.
	    `ifdef RV64
        f3_LWU: case (addr_lsbs)
		    'h0: result = 8'b0000_1111;
		    'h4: result = 8'b1111_0000;
	        endcase

        f3_LD: case (addr_lsbs)
		    'h0: result = 8'b1111_1111;
	        endcase
	    `endif
    endcase
    return result;
endfunction : getMemMask



endpackage

