module fifo #(
    parameter NUMADDR = 8,
    parameter BITADDR = $clog2(NUMADDR),
    parameter BITCNT  = $clog2(NUMADDR+1),
    parameter BITDATA = 32
) (
    input  logic              clk,
    input  logic              rst_n,
    input  logic              write,
    input  logic              read,
    input  logic [BITDATA-1:0] din [NUMADDR-1:0],      // Unpacked array
    output logic [BITDATA-1:0] ff_dout [NUMADDR-1:0],  // Unpacked array
    output logic              ff_empty,
    output logic              ff_full
);

    logic [BITDATA-1:0] ff_data [NUMADDR-1:0];
    logic [BITDATA-1:0] ff_data_nxt [NUMADDR-1:0];
    logic [BITADDR-1:0] ff_rd_ptr, ff_wr_ptr;
    logic [BITADDR-1:0] ff_rd_ptr_nxt, ff_wr_ptr_nxt;
    logic [BITCNT:0]    ff_count;
    logic [BITCNT:0]    ff_count_nxt;

    // Main combinational logic block
    always_comb begin
        // Default assignments
        ff_dout = '{default: '0};  // Initialize unpacked array
        ff_wr_ptr_nxt = ff_wr_ptr;
        ff_rd_ptr_nxt = ff_rd_ptr;
        
        // Initialize next state of memory
        ff_data_nxt = ff_data;

        // Write operation
        if(write && !ff_full) begin
            ff_data_nxt[ff_wr_ptr] = din[ff_wr_ptr];
            ff_wr_ptr_nxt = (ff_wr_ptr + 1'b1) % NUMADDR;
        end

        // Read operation
        if(read && !ff_empty) begin
            ff_dout[ff_rd_ptr] = ff_data[ff_rd_ptr];
            ff_rd_ptr_nxt = (ff_rd_ptr + 1'b1) % NUMADDR;
        end
    end

    // Pointer update logic
    always_ff @(posedge clk or negedge rst_n) begin
        if(!rst_n) begin
            ff_rd_ptr <= BITADDR'(0);
            ff_wr_ptr <= BITADDR'(0);
        end else begin
            ff_rd_ptr <= ff_rd_ptr_nxt;
            ff_wr_ptr <= ff_wr_ptr_nxt;
        end
    end

    // Memory update logic
    always_ff @(posedge clk) begin
        ff_data <= ff_data_nxt;
    end

    // Count and status flag logic
    always_comb begin
        ff_count_nxt = ff_count;
        case ({write && !ff_full, read && !ff_empty})
            2'b10: ff_count_nxt = ff_count + 1'b1;
            2'b01: ff_count_nxt = ff_count - 1'b1;
            default: ff_count_nxt = ff_count;
        endcase
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if(!rst_n) begin
            ff_count <= '0;
            ff_empty <= 1'b1;
            ff_full  <= 1'b0;
        end else begin
            ff_count <= ff_count_nxt;
            ff_empty <= (ff_count_nxt == '0);
            ff_full  <= (ff_count_nxt >= NUMADDR);
        end
    end

endmodule