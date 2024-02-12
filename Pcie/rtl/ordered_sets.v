// 
`include 8b_10_defines.v 
`define B_PAD                       8'hF7 
`define K_PAD                       {1'b1, `B_PAD} // K23_7


ts0 [symbol0]  = 0x33; 
ts0 [symbol8]  = 0x33; 

localparam `SYMBOL_0 = 0; 
localparam `SYMBOL_1 = 1; 
localparam `SYMBOL_2 = 2; 
localparam `SYMBOL_3 = 3; 
localparam `SYMBOL_4 = 4; 
localparam `SYMBOL_5 = 5; 
localparam `SYMBOL_6 = 6; 
localparam `SYMBOL_7 = 7; 
localparam `SYMBOL_8 = 8; 

  

localparam  `DATA_SPEED_2_5G = 0; 
localparam  `DATA_SPEED_5G   = 1; 
localparam  `DATA_SPEED_8G   = 2; 
localparam  `DATA_SPEED_16G  = 3;
localparam  `DATA_SPEED_32G  = 4;

   
   ts1[`SYMBOL_3] = num_fts;

// N_FTS - The number of Fast Training Sequences required by the Receiver: 0-255 

if(rx_symbol_0_rcvd)begin 
    if(data_speed == `DATA_SPEED_2_5G || data_speed == `DATA_SPEED_5G) begin 
        ts1[`SYMBOL_0] = 0XBC ; //K28.5 
       // • When operating at 2.5 or 5.0 GT/s: 0-31, PAD. PAD is encoded as K23.7.
   end 
else if  (data_speed >= `DATA_SPEED_8G) begin  
      ts1[`SYMBOL_0] = 0X1E ; //TS1 ordered set. 
      // • When operating at 8.0 GT/s or above: 0-31, PAD. PAD is encoded as F7h.
   end 
end 

if(rx_symbol_2_rcvd)begin 
    if(data_speed == `DATA_SPEED_2_5G || data_speed == `DATA_SPEED_5G) begin 
      ts1[`SYMBOL_2] = {K_PAD};
       // • When operating at 2.5 or 5.0 GT/s: 0-31, PAD. PAD is encoded as K23.7.
   end 
else if  (data_speed >= `DATA_SPEED_8G) begin  
      ts1[`SYMBOL_2] = 0xF7;
      // • When operating at 8.0 GT/s or above: 0-31, PAD. PAD is encoded as F7h.
   end 
end 

// FTS 
// 

// The transmitted SKP Ordered Set consists of the SKPs (F00F_F00F),
//  followed by a SKP_END (FFF0_00F0), followed by PHY Payload (8B),

