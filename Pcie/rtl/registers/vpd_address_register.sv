module vpd_address_register #(
    parameter int REGISTER_WIDTH = 16
) (
    input logic clk,
    input logic rst_n,
    input logic [REGISTER_WIDTH-1:0] write_data,
    input logic write_enable,
    input logic transfer_complete,
    output logic [REGISTER_WIDTH-1:0] read_data,
    output logic [13:0] vpd_address,
    output logic transfer_direction
);

    // Register bit fields
    logic [13:0] vpd_address_reg;
    logic f_bit;

    // Temporary variable for read data
    logic [REGISTER_WIDTH-1:0] read_data_temp;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            vpd_address_reg <= 14'b0;
            f_bit <= 1'b0;
        end else if (write_enable) begin
            // Check if the lowest 2 bits of VPD Address are zero
            if (write_data[1:0] == 2'b00) begin
                vpd_address_reg <= write_data[14:1];
                f_bit <= write_data[15];
            end
        end else if (transfer_complete) begin
            // Flip the F bit when transfer is complete
            f_bit <= ~f_bit;
        end
    end

    // Read logic
    always_comb begin
        read_data_temp = {f_bit, vpd_address_reg, 1'b0};
        
        // If the lowest 2 bits of VPD Address are non-zero, they read as zero
        read_data_temp[1:0] = 2'b00;
    end

    assign read_data = read_data_temp;
    assign vpd_address = vpd_address_reg;
    assign transfer_direction = f_bit;

endmodule