module rp_pio_mask_register (
    input logic clk,
    input logic rst_n,
    input logic [31:0] write_data,
    input logic write_enable,
    output logic [31:0] read_data
);

    // Register bit fields with "msk" appended
    logic cfg_ur_cpl_msk;
    logic cfg_ca_cpl_msk;
    logic cfg_cto_msk;
    logic io_ur_cpl_msk;
    logic io_ca_cpl_msk;
    logic io_cto_msk;
    logic mem_ur_cpl_msk;
    logic mem_ca_cpl_msk;
    logic mem_cto_msk;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Default values (all set to 1b as per the image)
            cfg_ur_cpl_msk <= 1'b1;
            cfg_ca_cpl_msk <= 1'b1;
            cfg_cto_msk <= 1'b1;
            io_ur_cpl_msk <= 1'b1;
            io_ca_cpl_msk <= 1'b1;
            io_cto_msk <= 1'b1;
            mem_ur_cpl_msk <= 1'b1;
            mem_ca_cpl_msk <= 1'b1;
            mem_cto_msk <= 1'b1;
        end else if (write_enable) begin
            // RWS (Read/Write Sticky) logic
            cfg_ur_cpl_msk <= write_data[0];
            cfg_ca_cpl_msk <= write_data[1];
            cfg_cto_msk <= write_data[2];
            io_ur_cpl_msk <= write_data[8];
            io_ca_cpl_msk <= write_data[9];
            io_cto_msk <= write_data[10];
            mem_ur_cpl_msk <= write_data[16];
            mem_ca_cpl_msk <= write_data[17];
            mem_cto_msk <= write_data[18];
        end
    end

    // Read data assignment
    assign read_data = {
        13'b0,                       // Bits 31:19 (RsvdP)
        mem_cto_msk,                 // Bit 18
        mem_ca_cpl_msk,              // Bit 17
        mem_ur_cpl_msk,              // Bit 16
        5'b0,                        // Bits 15:11 (RsvdP)
        io_cto_msk,                  // Bit 10
        io_ca_cpl_msk,               // Bit 9
        io_ur_cpl_msk,               // Bit 8
        5'b0,                        // Bits 7:3 (RsvdP)
        cfg_cto_msk,                 // Bit 2
        cfg_ca_cpl_msk,              // Bit 1
        cfg_ur_cpl_msk               // Bit 0
    };

endmodule