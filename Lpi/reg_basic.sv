module reg_1(
                Ip,
                Sel_i1,
                Sel_o1,
                Sel_o2,
                clk,
                EN,
                RD,
                rst,
                WR
                OP1,
                OP2
);

input bit [31:0] Ip;
input bit [3:0]  Sel_i1,
                 Sel_o1,
                 Sel_o2,
input            clk;
input            EN;
input            RD;
input            rst;
input            WR;
output reg [31:0] OP1;
output reg [31:0] OP2; 

reg [31:0] regfile [0:15]
integer i; 
wire sen; 
assign sen = clk || rst; 

always@(posedge sen)initial 
        begin
            if(EN ==1 )begin 
                if(rst ==1)
                begin 
                    for(i =0; i < 16; i++){
                        begin 
                            regfile[i] = 32'h0; 
                        end 
                    OP1 = 32'hx; 
                end
                else if (rst ==0)
                begin
                    case({RD,WR})
                        2'b00: begin 
                        end 
                        2'b01: begin // If write only
                            regfile[sel_i1]= Ip;
                        end 
                        2'b10: begin // If read only 
                            OP1 = regfile[sel_o1];
                            OP2 = regfile[sel_o2];
                        end 
                        2'b11 : begin // if both read & write are active 
                            OP1 = regfile[sel_o1];
                            OP2 = regfile[sel_o2];
                            regfile[sel_i1]= Ip; 
                        end 
                        default: begin // For undefined inputs 
                        end 
                    endcase 
                end 
            else;
            end  
        else;
        end 
endmodule          


