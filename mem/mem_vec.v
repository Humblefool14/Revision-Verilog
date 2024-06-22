module multi_port_memory #(
    parameter DATA_WIDTH = 8,
    parameter ADDR_WIDTH = 4,
    parameter NUM_WRITE_PORTS = 4,
    parameter NUM_READ_PORTS = 2
) (
    input wire clk,
    // Write ports
    input wire [NUM_WRITE_PORTS-1:0] we, // Write enable for each write port
    input wire [(NUM_WRITE_PORTS*ADDR_WIDTH)-1:0] waddr, // Flat vector for write addresses
    input wire [(NUM_WRITE_PORTS*DATA_WIDTH)-1:0] wdata, // Flat vector for write data
    // Read ports
    input wire [NUM_READ_PORTS-1:0] re, // Read enable for each read port
    input wire [(NUM_READ_PORTS*ADDR_WIDTH)-1:0] raddr, // Flat vector for read addresses
    output reg [(NUM_READ_PORTS*DATA_WIDTH)-1:0] rdata // Flat vector for read data
);

// Memory array
reg [DATA_WIDTH-1:0] mem      [0:(1<<ADDR_WIDTH)-1];
reg [DATA_WIDTH-1:0] mem_next [0:(1<<ADDR_WIDTH)-1];

// Write logic
integer i;
always @(posedge clk) begin
    for (i = 0; i < NUM_WRITE_PORTS; i = i + 1) begin
        if (we[i]) begin
            mem[waddr[(i+1)*ADDR_WIDTH-1:i*ADDR_WIDTH]] <= wdata << (i*DATA_WIDTH);
        end
    end
end

// Read logic
integer j;
always @(posedge clk) begin
    for (j = 0; j < NUM_READ_PORTS; j = j + 1) begin
        if (re[j]) begin
            rdata[(j+1)*DATA_WIDTH-1:j*DATA_WIDTH] <= mem[raddr[(j+1)*ADDR_WIDTH-1:j*ADDR_WIDTH]];
        end
    end
end

endmodule