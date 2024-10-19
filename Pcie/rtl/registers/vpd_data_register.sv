module vpd_data_register #(
    parameter int REGISTER_WIDTH = 32
) (
    input logic clk,
    input logic rst_n,
    input logic [REGISTER_WIDTH-1:0] write_data,
    input logic write_enable,
    input logic [3:0] byte_enable,
    input logic [13:0] vpd_address,
    input logic [REGISTER_WIDTH-1:0] vpd_storage [0:16383], // 16K x 32-bit storage
    output logic [REGISTER_WIDTH-1:0] read_data,
    output logic valid_access
);

    // Register for VPD Data
    logic [REGISTER_WIDTH-1:0] vpd_data_reg;

    // Valid access flag
    assign valid_access = (byte_enable == 4'b1111);

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            vpd_data_reg <= '0;
        end else if (valid_access) begin
            if (write_enable) begin
                // Write operation
                vpd_storage[vpd_address[13:2]] <= write_data;
                vpd_data_reg <= write_data;
            end else begin
                // Read operation
                vpd_data_reg <= vpd_storage[vpd_address[13:2]];
            end
        end
    end

    // Read data assignment
    assign read_data = valid_access ? vpd_data_reg : '0;

endmodule