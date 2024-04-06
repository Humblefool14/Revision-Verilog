module ahb_prot_decoder (
    input logic [3:0] ahb_prot,
    output logic opcode_fetch,
    output logic data_access,
    output logic user_access,
    output logic privileged_access,
    output logic non_bufferable,
    output logic bufferable,
    output logic non_cacheable,
    output logic cacheable
);

    // Opcode fetch
    assign opcode_fetch = (ahb_prot[3:1] == 3'bxxx) && (ahb_prot[0] == 1'b0);

    // Data access
    assign data_access = (ahb_prot[3:1] == 3'bxxx) && (ahb_prot[0] == 1'b1);

    // User access
    assign user_access = (ahb_prot[3:2] == 2'bxx0) && (ahb_prot[1:0] != 2'b00);

    // Privileged access
    assign privileged_access = (ahb_prot[3:2] == 2'bxx1) && (ahb_prot[1:0] != 2'b00);

    // Non-bufferable
    assign non_bufferable = (ahb_prot[3:0] == 4'bx0xx) && (ahb_prot[1:0] != 2'b00);

    // Bufferable
    assign bufferable = (ahb_prot[3:0] == 4'bx1xx) && (ahb_prot[1:0] != 2'b00);

    // Non-cacheable
    assign non_cacheable = (ahb_prot[3:0] == 4'b0xxx) && (ahb_prot[1:0] != 2'b00);

    // Cacheable
    assign cacheable = (ahb_prot[3:0] == 4'b1xxx) && (ahb_prot[1:0] != 2'b00);

endmodule