//SDS 
// 

localparam [127:0] SDS_8G_identifier = {32'hE1555555,32'h55555555,32'h55555555,32'h55555555}; 
localparam [127:0] SDS_32G_identifier = {32'hE1878787,32'h87878787,32'h87878787,32'h87878787}; 
localparam [127:0] SDS_64G_identifier = {32'hB1C6C6C6,32'hB1C6C6C6,32'hB1C6C6C6,32'hB1C6C6C6}; 

always @(pl_ltssm) begin
    case(pl_ltssm):
    0  : 
    01 : 
    default  : 10
    endcase 
end
