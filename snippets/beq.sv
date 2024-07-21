assert property ;
    @(posedge clk) (is_a_beq && axiomize_REG_rs1==axiomize_REG_rs2) |-> ## `REG_DELAY (axiomize_n_pc == branch_addr)
endproperty


assign branch_addr = axiomize_decoded_pc + 
                     {{19{axiomize_instr[31]}},
                       axiomize_instr[31],
                       axiomize_instr[7],
                       axiomize_instr[30:25],
                       axiomize_instr[11:8], 
                       1'b0}; 

assign is_a_beq    = is_a_branch && axiomize_instr[14:12] == 3'b000;
assign is_a_branch = axiomize_instr[6:0] == AXIOMIZE_OPCODE_BRANCH;   