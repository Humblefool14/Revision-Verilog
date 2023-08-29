`ifndef ECC_84TO86_ENCODER__SV
`define ECC_84TO86_ENCODER__SV
//Description: This module implements the 84B to 86B ECC group encoder
//as defined in Chapter 4 of the PCI Express Base Specification 6.0.
//Input: 84 bytes of Data
//Output: 86 bytes of data. Check is on byte 84, Parity is on byte 85.
module ecc_84to86_encoder
(
    input logic [7:0] data_in[83:0],
    output logic [7:0] data_out[85:0]
);
logic [7:0] synd_parity;
logic [7:0] synd_check;
`include "alpha_powers.vh"
//Calculate the Check and Parity Bytes.
always_comb begin
    synd_parity      = 8'h00;
    synd_check       = 8'h00;
    for(int i = 0 ; i < 84 ; i++) begin
        synd_parity ^= data_in[i];
        synd_check  ^= (({8{data_in[i][0]}} & i_to_alpha_power_i[84-i]) ^
end end
//Assign Output
always_comb begin
for (int i = 0 ; i < 84 ; i++) begin
    data_out[i]  = data_in[i];
    end
    data_out[84]
    data_out[85]
end
endmodule
`endif