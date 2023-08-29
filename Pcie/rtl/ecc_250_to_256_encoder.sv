`ifndef ECC_250TO256_ENCODER__SV
`define ECC_250TO256_ENCODER__SV
//Description: This module implements ECC for Flit level blocks.
//It splits the input 250 bytes into the 3 groups defined by PCIe 6.0
//and assigns the ECC bytes based on the byte positions shown
//in Chapter 4 of PCIe 6.0 Specification.
//
//Input        : 250 bytes of Flit without ECC.
//Output       : 256 bytes of Flit with ECC added.
//Child Module : ecc_84to86_encoder
module ecc_250to256_encoder
(
    input logic [7:0] data_in[249:0],
    output logic [7:0] data_out[255:0]
);
logic [7:0] ecc_output0[85:0];
logic [7:0] ecc_output1[85:0];
logic [7:0] ecc_output2[85:0];
logic [7:0] ecc0_input[83:0];
logic [7:0] ecc1_input[83:0];
logic [7:0] ecc2_input[83:0];
//Split input into the 3 ECC groups
//Groups 1 and 2 get an extra byte of 0 padded to byte 83.
always_comb begin
    for (int i = 0 ; i < 83 ; i++) begin
        ecc0_input[i] = data_in[i*3];
        ecc1_input[i] = data_in[(i*3) + 1];
        ecc2_input[i] = data_in[(i*3) + 2];
end
ecc0_input[83] = data_in[249];
ecc1_input[83] = 8'h00;
ecc2_input[83] = 8'h00;
end
ecc_84to86_encoder enc0 (
    .data_in  ( ecc0_input ),
    .data_out ( ecc_output0 )
);
ecc_84to86_encoder enc1 (
    .data_in  ( ecc1_input ),
    .data_out ( ecc_output1 )
);
ecc_84to86_encoder enc2 (
    .data_in  ( ecc2_input ),
    .data_out ( ecc_output2 )
);
//Assign output
always_comb begin
    //First 250 bytes are assigned directly from input.
    for (int i = 0 ; i < 250 ; i++ ) begin
        data_out[i] = data_in[i];
    end
    //Next Six bytes are assigned using the check and parity
    //from the three ECC groups.
    data_out[250]= ecc_output1[84]; //ECC1[0] = Check of Group 1.
    data_out[251]= ecc_output2[84]; //ECC2[0] = Check of Group 2.
    data_out[252]= ecc_output0[84]; //ECC0[0] = Check of Group 0.
    data_out[253]= ecc_output1[85]; //ECC1[1] = Parity of Group 1.
    data_out[254]= ecc_output2[85]; //ECC2[1] = Parity of Group 2.
    data_out[255]= ecc_output0[85]; //ECC0[1] = Parity of Group 0.
end
endmodule
`endif


