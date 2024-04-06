module ahb_decoder (
    input logic HCLK,
    input logic HRESETn,
    input logic [31:0] HADDR,
    output logic [3:0] HSELx,
    output logic HERROR
);
    // Default values
    // assign HSELx = 4'b0000;
    // assign HERROR = 1'b0;

    logic [7:0] hselx = 8'b0000_0000;  // Temporary variable 
    logic       herror; 

    // Address array
    localparam ADDR_RANGE [4:0] = '{SLAVE1_START_ADDR, SLAVE1_END_ADDR,
                                     SLAVE2_START_ADDR, SLAVE2_END_ADDR,
                                     SLAVE3_START_ADDR, SLAVE3_END_ADDR,
                                     SLAVE4_START_ADDR, SLAVE4_END_ADDR, 32'hFFFFFFFF};
   // Local param address range should be taken from ahb defines.  
   // Decode the address to select the appropriate slave
    int i;
    genvar idx;
    always_comb begin
    for (genvar idx = 0; idx < 8; idx = idx + 2) begin : SEL_LOOP
        assign hselx[idx] = (HADDR >= ADDR_RANGE[idx] && HADDR <= ADDR_RANGE[idx + 1]) ? 1'b1 << idx/2: hselx[idx]; 
        assign herror     = (HADDR >= ADDR_RANGE[idx] && HADDR <= ADDR_RANGE[idx + 1]) ? 1'b0 : 1'b1; 
    end
    end 


always @(posedge HCLK or negedge HRESETn) begin
        if (!HRESETn) begin
            HSELx <= 8'b0000_0000;
            HERROR <= 1'b0;
        end else begin 
                HSELx <= hselx;
                HERROR <= herror;
        end
    end
endmodule