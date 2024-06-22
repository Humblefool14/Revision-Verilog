module Cache #(parameter ADDRESS_WIDTH = 32, 
               parameter BLOCK_SIZE = 64,  // In bytes
               parameter NUM_SETS = 16,    // Number of sets in the cache
               parameter DATA_WIDTH = 32)  // Width of data bus
              (input wire clk,
               input wire rst_n,            // Active-low reset signal
               input wire read,             // Read enable signal
               input wire write,            // Write enable signal
               input wire [ADDRESS_WIDTH-1:0] address, // Address input
               input wire [DATA_WIDTH-1:0] write_data, // Data to write
               output reg [DATA_WIDTH-1:0] read_data,  // Data read from cache
               output reg hit);             // Cache hit indicator

    // Calculate bit widths
    localparam OFFSET_BITS = $clog2(BLOCK_SIZE);
    localparam INDEX_BITS = $clog2(NUM_SETS);
    localparam TAG_BITS = ADDRESS_WIDTH - OFFSET_BITS - INDEX_BITS;

    // Define the cache structure
    reg [TAG_BITS-1:0] tags [NUM_SETS-1:0];
    reg [DATA_WIDTH-1:0] cache_data [NUM_SETS-1:0][(BLOCK_SIZE/DATA_WIDTH)-1:0];
    reg valid [NUM_SETS-1:0];

    // Split the address into tag, index, and offset
    wire [OFFSET_BITS-1:0] offset = address[OFFSET_BITS-1:0];
    wire [INDEX_BITS-1:0] index = address[OFFSET_BITS+INDEX_BITS-1:OFFSET_BITS];
    wire [TAG_BITS-1:0] tag = address[ADDRESS_WIDTH-1:OFFSET_BITS+INDEX_BITS];

    // Read and write operations
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            integer i, j;
            for (i = 0; i < NUM_SETS; i = i + 1) begin
                valid[i] <= 0;
                tags[i] <= 0;
                for (j = 0; j < (BLOCK_SIZE/DATA_WIDTH); j = j + 1) begin
                    cache_data[i][j] <= 0;
                end
            end
            hit <= 0;
            read_data <= 0;
        end else begin
            hit <= 0;
            if (read) begin
                if (valid[index] && tags[index] == tag) begin
                    read_data <= cache_data[index][offset];
                    hit <= 1;  // Cache hit
                end else begin
                    read_data <= 0;  // Cache miss, no data to read
                end
            end
            if (write) begin
                if (valid[index] && tags[index] == tag) begin
                    cache_data[index][offset] <= write_data;
                end else begin
                    tags[index] <= tag;
                    valid[index] <= 1;
                    cache_data[index][offset] <= write_data;
                end
            end
        end
    end

endmodule