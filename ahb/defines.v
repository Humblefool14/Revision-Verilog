module slave_addresses (
    // Define slave address ranges
    parameter SLAVE1_START_ADDR = 32'h0000_0000;
    parameter SLAVE1_END_ADDR   = 32'h00FF_FFFF;

    parameter SLAVE2_START_ADDR = 32'h0100_0000;
    parameter SLAVE2_END_ADDR   = 32'h01FF_FFFF;

    parameter SLAVE3_START_ADDR = 32'h0200_0000;
    parameter SLAVE3_END_ADDR   = 32'h02FF_FFFF;

    parameter SLAVE4_START_ADDR = 32'h0300_0000;
    parameter SLAVE4_END_ADDR   = 32'h03FF_FFFF;
endmodule