module msi_x_table_offset_bir_register (
    input wire clk,
    input wire rst_n,
    input wire [31:0] write_data,
    input wire write_enable,
    output reg [31:0] read_data,
    input wire [2:0] config_space_type // 0 for 64-bit, 1 for Type 1
);

    reg [28:0] table_offset;
    reg [2:0] table_bir;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            table_offset <= 29'b0;
            table_bir <= 3'b0;
        end else if (write_enable) begin
            // Table Offset is read-only, so we don't update it
            // Table BIR is read-only, so we don't update it
        end
    end

    always @(*) begin
        read_data[31:3] = table_offset;
        read_data[2:0] = table_bir;
    end

    // Function to check if BIR value is valid
    function automatic is_valid_bir;
        input [2:0] bir;
        input [2:0] config_space_type;
        begin
            is_valid_bir = 1'b0;
            case (bir)
                3'b000, 3'b001, 3'b010, 3'b011, 3'b100, 3'b101: 
                    is_valid_bir = (config_space_type == 3'b000) ? 1'b1 : 
                                   (bir <= 3'b001) ? 1'b1 : 1'b0;
                default: is_valid_bir = 1'b0;
            endcase
        end
    endfunction

    // Assertions
    always @(posedge clk) begin
        if (rst_n) begin
            assert(is_valid_bir(table_bir, config_space_type))
            else $error("Invalid Table BIR value for the given Configuration Space type");

            assert(table_offset[2:0] == 3'b000)
            else $error("Lower 3 bits of Table Offset must be zero for QWORD alignment");
        end
    end

    initial begin
        $display("Table Offset/Table BIR Register initialized.");
        $display("Table Offset is read-only and used as an offset from the address in the Base Address Register.");
        $display("Table BIR is read-only and indicates which Base Address Register is used.");
    end

endmodule