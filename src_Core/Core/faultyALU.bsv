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
        if (inputs.decoded_instr.funct7 == f7_CSEAL) begin // 0x0b
            let check = fv_checkValid_Seal(cs, ct);
            if (check == exc_code_NO_EXCEPTION)
                alu_outputs.val1 = fv_seal(cs, ct);
            else begin
                alu_outputs.control = CONTROL_TRAP;
                alu_outputs.exc_code = check;
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
            
            Bit#(64) cb_bot   = fv_getBase(inputs.rs1_val)[63:0];
            Bit#(64) cb_top   = fv_getTop(inputs.rs1_val)[63:0];
            Bit#(15) cb_perms = fv_getPerms(inputs.rs1_val);
            
            // Any permissions in ct but not cb
            Bool perms_valid = ((ct_perms & ~cb_perms) > 0);
            Bool bounds_valid = (ct_bot >= cb_bot && ct_top <= cb_top);
            Bit#(1) tag = inputs.rs1_val.tag;
            if (!perms_valid || !bounds_valid)
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
    end
    else begin
        alu_outputs.control = CONTROL_TRAP;
    end
    return alu_outputs;
endfunction : fv_CHERI
