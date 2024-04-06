module ahb_decoder (
    input  HCLK,
    input logic HRESETn,
    input logic [31:0] HADDR,
    output logic [3:0] HSELx,
    output logic HERROR
);
    logic [3:0] hselx ;   // Temporary variable 
    logic       herror; 

    // Address array
    localparam ADDR_RANGE [7:0] = '{ 
                                     SLAVE1_START_ADDR, SLAVE1_END_ADDR,
                                     SLAVE2_START_ADDR, SLAVE2_END_ADDR,
                                     SLAVE3_START_ADDR, SLAVE3_END_ADDR,
                                     SLAVE4_START_ADDR, SLAVE4_END_ADDR
                                    };
   // Local param address range should be taken from ahb defines.  
   // Decode the address to select the appropriate slave
    int i;
    for (genvar idx = 0; idx < 8; idx = idx + 2) begin : SEL_LOOP
        assign hselx[idx] = (HADDR >= ADDR_RANGE[idx] && HADDR <= ADDR_RANGE[idx + 1]) ? 1'b1 << idx/2: hselx[idx]; 
    end
    assign herror     = (HADDR >= SLAVE1_START_ADDR && HADDR <= SLAVE4_END_ADDR) ? 1'b0 : 1'b1; 



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