module multi_port_memory #(
    parameter DATA_WIDTH = 8,
    parameter ADDR_WIDTH = 4,
    parameter NUM_PORTS = 4

) (
    input wire clk,
    input wire [NUM_PORTS-1:0] we, // Write enable for each port
    input wire [ADDR_WIDTH-1:0] addr [NUM_PORTS-1:0], // Address for each port
    input wire [DATA_WIDTH-1:0] wdata [NUM_PORTS-1:0] // Data to write for each port

    input wire [NUM_PORTS-1:0] re, // Read enable for each read port
    input wire [ADDR_WIDTH-1:0] raddr [NUM_PORTS-1:0], // Read address for each read port
    output reg [DATA_WIDTH-1:0] rdata [NUM_PORTS-1:0] // Read data for each read port
);

// Memory array
reg [DATA_WIDTH-1:0] mem [0:(1<<ADDR_WIDTH)-1];

// Write logic
integer i;
always @(posedge clk) begin
    for (i = 0; i < NUM_PORTS; i = i + 1) begin
        if (we[i]) begin
            mem[addr[i]] <= wdata[i];
        end
    end
end

integer j;
always @(posedge clk) begin
    for (j = 0; j < NUM_PORTS; j = j + 1) begin
        if (re[j]) begin
            rdata[j] <= mem[raddr[j]];
        end
    end
end

endmodule