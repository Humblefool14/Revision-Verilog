`ifndef ECC_256TO250_DECODER__SV
`define ECC_256TO250_DECODER__SV
//Description : This module takes in 256 bytes of the flit, and outputs 250 bytes
//of corrected data. It also gives the metrics of the detected error per ECC group
//defined in PCIe 6.0 Specification.
//Note: it is possible that the ECC code corrupted the data further if more than a
//single byte error happened within an ECC group. The final check is the 8B CRC -
//data should only be consumed if CRC passes post FEC correction.
//Input  : 256 bytes of the flit.
//Output : 250 bytes of corrected data
//         synd_check and parity for each ECC group for logging (see signal descriptions)
//         Error metrics for each ECC group (see signal descriptions).
module ecc_256to250_decoder (
    input logic [7:0] data_in[255:0],
    output logic [7:0] data_out[249:0],
    output logic [7:0] synd_check0, //Syndrome Check for ECC Group 0. Flit Error log 1, bits 31:24.
    output logic [7:0] synd_parity0,//Syndrom Parity for ECC Group 0. Flit Error log 1, bits 23:16.
    output logic [7:0] synd_check1, //Syndrome Check for ECC Group 1. Flit Error log 2, bits 15:8.
    output logic [7:0] synd_parity1,//Syndrom Parity for ECC Group 1. Flit Error log 2, bits 7:0.
    output logic [7:0] synd_check2, //Syndrome Check for ECC Group 2. Flit Error log 2, bits 31:24.
    output logic [7:0] synd_parity2,//Syndrom Parity for ECC Group 2. Flit Error log 2, bits 23:16.
    //Error metrics
    //Note that error metrics can be incorrect if more than
    //1 byte per ECC group is corrupted, and CRC check ultimately
    //determines whether the flit is consumed or replayed.
    //
    //If unc_error0 == 0, error_byte0 indicates the error location for ECC Group 0 as the
    //byte position between(including) 0 and 85.
    //If unc_error1 == 0, error_byte1 indicates the error location for ECC Group 1 as the
    //byte position between(including) 0 and 85.
    //If unc_error2 == 0, error_byte2 indicates the error location for ECC Group 2 as the
    //byte position between(including) 0 and 85.
    //
    //ECC Group 0 metrics :
    output logic [7:0] error_magnitude0,
    output logic [6:0] error_byte0,
    output logic no_error0,
    output logic single_error0,
    output logic unc_error0,
    //ECC Group 1 metrics :
    output logic [7:0] error_magnitude1,
    output logic [6:0] error_byte1,
    output logic no_error1,
    output logic single_error1,
    output logic unc_error1,
    //ECC Group 2 metrics :
    output logic [7:0] error_magnitude2,
    output logic [6:0] error_byte2,
    output logic no_error2,
    output logic single_error2,
    output logic unc_error2
);
logic [7:0] dec_data_out0 [83:0];
logic [7:0] dec_data_out1 [83:0];
logic [7:0] dec_data_out2 [83:0];
logic [7:0] dec_data_in0 [85:0];
logic [7:0] dec_data_in1 [85:0];
logic [7:0] dec_data_in2 [85:0];
//Split the received flit into the 3 ECC groups.
always_comb begin
    for (int i=0;i<83;i++) begin
        dec_data_in0[i]   = data_in[i*3];
        dec_data_in1[i]   = data_in[(i*3) + 1];
dec_data_in2[i]   = data_in[(i*3) + 2];
data_out[i*3]     = dec_data_out0[i];
data_out[i*3 + 1] = dec_data_out1[i];
data_out[i*3 + 2] = dec_data_out2[i];
end
dec_data_in0[83] = data_in[249]; //Blue ECC group 0 
dec_data_in0[84] = data_in[252];
dec_data_in0[85] = data_in[255];
dec_data_in1[83] = 8'h00;
dec_data_in1[84] = data_in[250];
dec_data_in1[85] = data_in[253];
dec_data_in2[83] = 8'h00;
dec_data_in2[84] = data_in[251];
dec_data_in2[85] = data_in[254];
data_out[249] = dec_data_out0[83];
end
//Instantiate separate 86to84 decoder for each group.
ecc_86to84_decoder dec0 (
    .data_in ( dec_data_in0 ),
    .data_out ( dec_data_out0 ),
    .synd_check ( synd_check0 ),
    .synd_parity ( synd_parity0 ),
    .error_magnitude ( error_magnitude0 ),
    .error_byte ( error_byte0 ),
    .no_error ( no_error0 ),
    .single_error ( single_error0 ),
    .unc_error ( unc_error0 )
);
ecc_86to84_decoder dec1 (
    .data_in ( dec_data_in1 ),
    .data_out ( dec_data_out1 ),
    .synd_check ( synd_check1 ),
    .synd_parity ( synd_parity1 ),
    .error_magnitude ( error_magnitude1 ),
    .error_byte ( error_byte1 ),
    .no_error ( no_error1 ),
    .single_error ( single_error1 ),
    .unc_error ( unc_error1 )
);
ecc_86to84_decoder dec2 (
    .data_in ( dec_data_in2 ),
    .data_out ( dec_data_out2 ),
    .synd_check ( synd_check2 ),
    .synd_parity ( synd_parity2 ),
    .error_magnitude ( error_magnitude2 ),
    .error_byte ( error_byte2 ),
    .no_error ( no_error2 ),
    .single_error ( single_error2 ),
    .unc_error ( unc_error2 )
);
endmodule
`endif