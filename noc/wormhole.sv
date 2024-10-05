module wormhole_router
  #(
    parameter FLIT_WIDTH = 32,
    parameter ADDR_WIDTH = 4,
    parameter NUM_PORTS = 5  // 4 cardinal directions + local
  )
  (
    input  logic clk,
    input  logic rst_n,
    
    // Input ports
    input  logic [NUM_PORTS-1:0][FLIT_WIDTH-1:0] flit_in,
    input  logic [NUM_PORTS-1:0] valid_in,
    output logic [NUM_PORTS-1:0] ready_out,
    
    // Output ports
    output logic [NUM_PORTS-1:0][FLIT_WIDTH-1:0] flit_out,
    output logic [NUM_PORTS-1:0] valid_out,
    input  logic [NUM_PORTS-1:0] ready_in
  );

  // Internal FIFOs
  logic [NUM_PORTS-1:0][FLIT_WIDTH-1:0] fifo_data [NUM_PORTS];
  logic [NUM_PORTS-1:0] fifo_empty, fifo_full;
  logic [NUM_PORTS-1:0] fifo_rd_en, fifo_wr_en;

  // Routing table
  logic [NUM_PORTS-1:0] route_table [NUM_PORTS];

  // Route computation
  function automatic logic [NUM_PORTS-1:0] compute_route(logic [ADDR_WIDTH-1:0] dest_addr);
    // Simple XY routing
    logic [NUM_PORTS-1:0] route;
    route = 5'b00001;  // Default to local port
    if (dest_addr[3:2] < 2'b10) route = 5'b00010;  // East
    else if (dest_addr[3:2] > 2'b10) route = 5'b00100;  // West
    else if (dest_addr[1:0] < 2'b10) route = 5'b01000;  // North
    else if (dest_addr[1:0] > 2'b10) route = 5'b10000;  // South
    return route;
  endfunction

  // Input stage
  genvar i;
  generate
    for (i = 0; i < NUM_PORTS; i++) begin : input_stage
      always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
          fifo_wr_en[i] <= 1'b0;
        end else begin
          fifo_wr_en[i] <= valid_in[i] && !fifo_full[i];
        end
      end

      assign ready_out[i] = !fifo_full[i];
    end
  endgenerate

  // Router logic
  genvar j;
  generate
    for (j = 0; j < NUM_PORTS; j++) begin : router_logic
      always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
          route_table[j] <= '0;
          valid_out[j] <= 1'b0;
          flit_out[j] <= '0;
        end else begin
          if (!fifo_empty[j] && ready_in[j]) begin
            if (fifo_data[j][FLIT_WIDTH-1:FLIT_WIDTH-2] == 2'b01) begin  // Header flit
              route_table[j] <= compute_route(fifo_data[j][ADDR_WIDTH-1:0]);
            end
            valid_out[j] <= 1'b1;
            flit_out[j] <= fifo_data[j];
            fifo_rd_en[j] <= 1'b1;
          end else begin
            valid_out[j] <= 1'b0;
            fifo_rd_en[j] <= 1'b0;
          end
        end
      end
    end
  endgenerate

  // Instantiate FIFOs
  genvar k;
  generate
    for (k = 0; k < NUM_PORTS; k++) begin : fifo_inst
      fifo #(
        .WIDTH(FLIT_WIDTH),
        .DEPTH(4)
      ) input_fifo (
        .clk(clk),
        .rst_n(rst_n),
        .data_in(flit_in[k]),
        .wr_en(fifo_wr_en[k]),
        .rd_en(fifo_rd_en[k]),
        .data_out(fifo_data[k]),
        .empty(fifo_empty[k]),
        .full(fifo_full[k])
      );
    end
  endgenerate

endmodule

