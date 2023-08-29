`ifndef ECC_86TO84_DECODER__SV
`define ECC_86TO84_DECODER__SV
//Description: This module implements the 86 byte to 84 byte decoder for the
//ECC code defined in PCIe 6.0 Specification.
//
//Input   : 86 bytes of encoded data
//Outputs :
//          84 bytes of decoded data (corrected if applicable)
//          synd_check and synd parity for logging
//          Error magnitude - value of the error term
//          Error byte - location of the error byte, not applicable if
//                       (unc_error == 1)
//          no_error - no error was detected.
//          single_error - single error was detected.
//          unc_error - uncorrectable error (error decoding pointed to
//          non-existant column).
module ecc_86to84_decoder
(
    input logic [7:0] data_in[85:0],
    output logic [7:0] data_out[83:0],
    output logic [7:0] synd_check,
    output logic [7:0] synd_parity,
    output logic [7:0] error_magnitude,
    output logic [6:0] error_byte,
    output logic no_error,
    output logic single_error,
    output logic unc_error
);
logic synd_parity_0;
logic synd_check_0;
logic [7:0] synd_parity_map_i;
logic [7:0] synd_check_map_i;
logic [8:0] error_byte_result;
logic overflow;
`include "alpha_powers.vh"
logic [7:0] encoded_data[85:0];
ecc_84to86_encoder encoder (
    .data_in ( data_in[83:0] ),
    .data_out ( encoded_data[85:0] )
); // The decoder has to first invoke the encoder function to calculate the syndrome
assign synd_parity  = encoded_data[85] ^ data_in[85];
assign synd_check  = encoded_data[84] ^ data_in[84];
assign synd_parity_0  = (synd_parity == 8'h00);
assign synd_check_0  = (synd_check == 8'h00);
assign synd_parity_map_i = alpha_power_i_to_i[synd_parity];
assign synd_check_map_i  = alpha_power_i_to_i[synd_check];
assign error_byte        = error_byte_result[6:0];
always_comb begin
    no_error          = 1'b0;
    single_error      = 1'b0;
    unc_error         = 1'b0;
    error_byte_result = 9'd0;
    error_magnitude   = synd_parity;
    overflow          = 1'b0;
    for (int i = 0 ; i < 84 ; i++) begin
        data_out[i]   = data_in[i];
    end
    unique casez ({synd_check_0, synd_parity_0})
    2'b11: begin
        no_error = 1'b1;
    end
    2'b10: begin
        single_error      = 1'b1;
    end
    2'b01: begin
        single_error      = 1'b1;
        error_magnitude   = synd_check;
        error_byte_result = 9'd84;
    end
    2'b00: begin
        //Overflow term in the equations below is ignored, as those cases are
        //outside the correction capability of the ECC, and
        //we rely on CRC to detect those.
        if (synd_check_map_i < synd_parity_map_i) begin
            {overflow, error_byte_result} = 9'd84 - (9'd255 + {1'b0, synd_check_map_i} - {1'b0,synd_parity_map_i});
        end else begin
            {overflow, error_byte_result} = 9'd84 - ({1'b0,synd_check_map_i} - {1'b0,synd_parity_map_i}) ;
        end
        if (error_byte_result >= 9'd84) begin
            unc_error                     = 1'b1;
        end else begin
            single_error                  = 1'b1;
            data_out[error_byte_result]  ^= synd_parity;
end end
endcase end
endmodule
`endif