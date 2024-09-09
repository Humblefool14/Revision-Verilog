`define ADDR_WIDTH 22
`define MEM_SIZE (2 ** `ADDR_WIDTH)
`define DATA_WIDTH 8

module memory_bus (
    input wire clk,
    input wire reset,
    input wire [`ADDR_WIDTH-1:0] address,
    inout wire [`DATA_WIDTH-1:0] data,
    input wire read_enable,
    input wire write_enable,
    input wire [1:0] chip_select,
    output wire [1:0] output_enable
);

    // Define four memory modules
    reg [`DATA_WIDTH-1:0] memory_0 [0:`MEM_SIZE-1];
    reg [`DATA_WIDTH-1:0] memory_1 [0:`MEM_SIZE-1];
    reg [`DATA_WIDTH-1:0] memory_2 [0:`MEM_SIZE-1];
    reg [`DATA_WIDTH-1:0] memory_3 [0:`MEM_SIZE-1];

    // Output enable signals for each memory
    assign output_enable[0] = (chip_select == 2'b00) & read_enable;
    assign output_enable[1] = (chip_select == 2'b01) & read_enable;

    // Tri-state buffer for data output
    assign data = (output_enable[0]) ? memory_0[address] :
                  (output_enable[1]) ? memory_1[address] :
                  (chip_select == 2'b10 & read_enable) ? memory_2[address] :
                  (chip_select == 2'b11 & read_enable) ? memory_3[address] :
                  {`DATA_WIDTH{1'bz}}; // High impedance state when not reading

    // Write operation
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            // Reset logic (if needed)
        end else if (write_enable) begin
            case (chip_select)
                2'b00: memory_0[address] <= data;
                2'b01: memory_1[address] <= data;
                2'b10: memory_2[address] <= data;
                2'b11: memory_3[address] <= data;
            endcase
        end
    end

endmodule