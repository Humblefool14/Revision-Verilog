// Simple FIFO module
module fifo
  #(
    parameter WIDTH = 32,
    parameter DEPTH = 4
  )
  (
    input  logic clk,
    input  logic rst_n,
    input  logic [WIDTH-1:0] data_in,
    input  logic wr_en,
    input  logic rd_en,
    output logic [WIDTH-1:0] data_out,
    output logic empty,
    output logic full
  );

  logic [WIDTH-1:0] mem [DEPTH];
  logic [$clog2(DEPTH):0] wr_ptr, rd_ptr;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      wr_ptr <= '0;
      rd_ptr <= '0;
    end else begin
      if (wr_en && !full) begin
        mem[wr_ptr[($clog2(DEPTH)-1):0]] <= data_in;
        wr_ptr <= wr_ptr + 1;
      end
      if (rd_en && !empty) begin
        rd_ptr <= rd_ptr + 1;
      end
    end
  end

  assign data_out = mem[rd_ptr[($clog2(DEPTH)-1):0]];
  assign empty = (wr_ptr == rd_ptr);
  assign full = (wr_ptr[($clog2(DEPTH)-1):0] == rd_ptr[($clog2(DEPTH)-1):0]) && 
                (wr_ptr[$clog2(DEPTH)] != rd_ptr[$clog2(DEPTH)]);

endmodule