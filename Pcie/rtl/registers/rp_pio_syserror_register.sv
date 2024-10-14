module rp_pio_syserror_register (
    input logic clk,
    input logic rst_n,
    input logic [31:0] write_data,
    input logic write_enable,
    output logic [31:0] read_data
);

    // Register bit fields
    logic cfg_ur_cpl;
    logic cfg_ca_cpl;
    logic cfg_cto;
    logic io_ur_cpl;
    logic io_ca_cpl;
    logic io_cto;
    logic mem_ur_cpl;
    logic mem_ca_cpl;
    logic mem_cto;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Default values (all set to 0b as per the image)
            cfg_ur_cpl <= 1'b0;
            cfg_ca_cpl <= 1'b0;
            cfg_cto <= 1'b0;
            io_ur_cpl <= 1'b0;
            io_ca_cpl <= 1'b0;
            io_cto <= 1'b0;
            mem_ur_cpl <= 1'b0;
            mem_ca_cpl <= 1'b0;
            mem_cto <= 1'b0;
        end else begin
            // RWS (Read/Write Sticky) logic
            if (write_enable) begin
                cfg_ur_cpl <= cfg_ur_cpl | write_data[0];
                cfg_ca_cpl <= cfg_ca_cpl | write_data[1];
                cfg_cto <= cfg_cto | write_data[2];
                io_ur_cpl <= io_ur_cpl | write_data[8];
                io_ca_cpl <= io_ca_cpl | write_data[9];
                io_cto <= io_cto | write_data[10];
                mem_ur_cpl <= mem_ur_cpl | write_data[16];
                mem_ca_cpl <= mem_ca_cpl | write_data[17];
                mem_cto <= mem_cto | write_data[18];
            end
        end
    end

    // Read data assignment
    assign read_data = {
        13'b0,                       // Bits 31:19 (RsvdP)
        mem_cto,                     // Bit 18
        mem_ca_cpl,                  // Bit 17
        mem_ur_cpl,                  // Bit 16
        5'b0,                        // Bits 15:11 (RsvdP)
        io_cto,                      // Bit 10
        io_ca_cpl,                   // Bit 9
        io_ur_cpl,                   // Bit 8
        5'b0,                        // Bits 7:3 (RsvdP)
        cfg_cto,                     // Bit 2
        cfg_ca_cpl,                  // Bit 1
        cfg_ur_cpl                   // Bit 0
    };

endmodule