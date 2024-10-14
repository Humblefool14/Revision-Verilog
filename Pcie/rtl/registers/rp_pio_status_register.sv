module rp_pio_status_register (
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
    logic permanently_reserved;

    // RW1CS (Read/Write 1 to Clear, Sticky) logic
    `define RW1CS_LOGIC(field) \
        if (write_enable && write_data[field]) \
            field <= 1'b0; \
        else if (field_set[field]) \
            field <= 1'b1;

    // Simulating external events that would set these bits
    logic [31:0] field_set;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Default values
            cfg_ur_cpl <= 1'b0;
            cfg_ca_cpl <= 1'b0;
            cfg_cto <= 1'b0;
            io_ur_cpl <= 1'b0;
            io_ca_cpl <= 1'b0;
            io_cto <= 1'b0;
            mem_ur_cpl <= 1'b0;
            mem_ca_cpl <= 1'b0;
            mem_cto <= 1'b0;
            permanently_reserved <= 1'b0;
        end else begin
            `RW1CS_LOGIC(0)  // cfg_ur_cpl
            `RW1CS_LOGIC(1)  // cfg_ca_cpl
            `RW1CS_LOGIC(2)  // cfg_cto
            `RW1CS_LOGIC(8)  // io_ur_cpl
            `RW1CS_LOGIC(9)  // io_ca_cpl
            `RW1CS_LOGIC(10) // io_cto
            `RW1CS_LOGIC(16) // mem_ur_cpl
            `RW1CS_LOGIC(17) // mem_ca_cpl
            `RW1CS_LOGIC(18) // mem_cto

            // Permanently_Reserved is RsvdZ, so it's always 0
            permanently_reserved <= 1'b0;
        end
    end

    // Read data assignment
    assign read_data = {
        permanently_reserved,        // Bit 31
        12'b0,                       // Bits 30:19 (RsvdZ)
        mem_cto,                     // Bit 18
        mem_ca_cpl,                  // Bit 17
        mem_ur_cpl,                  // Bit 16
        5'b0,                        // Bits 15:11 (RsvdZ)
        io_cto,                      // Bit 10
        io_ca_cpl,                   // Bit 9
        io_ur_cpl,                   // Bit 8
        5'b0,                        // Bits 7:3 (RsvdZ)
        cfg_cto,                     // Bit 2
        cfg_ca_cpl,                  // Bit 1
        cfg_ur_cpl                   // Bit 0
    };

endmodule