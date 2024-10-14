typedef struct packed {
    logic [7:0] st_upper;  // Bits 31:24
    logic [7:0] st_lower;  // Bits 23:16
    logic [14:0] reserved; // Bits 15:1
    logic mask_bit;        // Bit 0
} msi_x_vector_control_t;

module msi_x_vector_control_register (
    input logic clk,
    input logic rst_n,
    input logic [31:0] write_data,
    input logic tph_requester_enable,
    input logic [1:0] st_table_location,
    input logic extended_tph_requester_supported,
    output msi_x_vector_control_t read_data
);

    msi_x_vector_control_t reg_data;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Default values
            reg_data.st_upper <= 8'h00;
            reg_data.st_lower <= 8'h00;
            reg_data.reserved <= 15'b0;
            reg_data.mask_bit <= 1'b1;  // Default is masked (1b)
        end else begin
            // ST Upper field
            if (tph_requester_enable && st_table_location == 2'b10 && extended_tph_requester_supported) begin
                reg_data.st_upper <= write_data[31:24];
            end

            // ST Lower field
            if (tph_requester_enable && st_table_location == 2'b10) begin
                reg_data.st_lower <= write_data[23:16];
            end

            // Reserved bits always remain 0
            reg_data.reserved <= 15'b0;

            // Mask Bit
            reg_data.mask_bit <= write_data[0];
        end
    end

    assign read_data = reg_data;

endmodule