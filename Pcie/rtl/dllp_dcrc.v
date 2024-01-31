module pcie_dllp_crc_32_10001000000001011(
	input               clk,
	input               reset,
	input       [ 31:0] d, // Data in
	output reg  [ 31:0] o, // Data
	output reg  [ 15:0] c // CRC
);
	reg                 nd_q;
	reg                 fd_q;
	reg         [ 15:0] dq;

    reg         [ 31:0] data_r; // data sliced in 4 pieces and reversed.  
    genvar  i; 
    for(int i =0; i <= 7; i=i+1):begin 
        assign data_r[i+0]  = d[7-i]; 
        assign data_r[i+8]  = d[15-i]; 
        assign data_r[i+16] = d[23-i]; 
        assign data_r[i+24] = d[31-i]; 
        assign c     [i+0]  = dq[7-i]; 
        assign c     [i+8]  = dq[15-i]; 
    end 

	always @(posedge clk) begin
        // seed is 0xFFFF
        // complemented or uncomplemented doesn't make difference. 
        // FIXME: Have to check. 
		dq[  0] <= data_r[ 31] ^ data_r[ 29] ^ data_r[ 28] ^ data_r[ 26] ^ data_r[ 23] ^ data_r[ 21] ^ data_r[ 20] ^ data_r[ 15] ^ data_r[ 13] ^ data_r[ 12] ^ data_r[  8] ^ data_r[  4] ^ data_r[  0];
		dq[  1] <= data_r[ 31] ^ data_r[ 30] ^ data_r[ 28] ^ data_r[ 27] ^ data_r[ 26] ^ data_r[ 24] ^ data_r[ 23] ^ data_r[ 22] ^ data_r[ 20] ^ data_r[ 16] ^ data_r[ 15] ^ data_r[ 14] ^ data_r[ 12] ^ data_r[  9] ^ data_r[  8] ^ data_r[  5] ^ data_r[  4] ^ data_r[  1] ^ data_r[  0];
		dq[  2] <= data_r[ 31] ^ data_r[ 29] ^ data_r[ 28] ^ data_r[ 27] ^ data_r[ 25] ^ data_r[ 24] ^ data_r[ 23] ^ data_r[ 21] ^ data_r[ 17] ^ data_r[ 16] ^ data_r[ 15] ^ data_r[ 13] ^ data_r[ 10] ^ data_r[  9] ^ data_r[  6] ^ data_r[  5] ^ data_r[  2] ^ data_r[  1];
		dq[  3] <= data_r[ 31] ^ data_r[ 30] ^ data_r[ 25] ^ data_r[ 24] ^ data_r[ 23] ^ data_r[ 22] ^ data_r[ 21] ^ data_r[ 20] ^ data_r[ 18] ^ data_r[ 17] ^ data_r[ 16] ^ data_r[ 15] ^ data_r[ 14] ^ data_r[ 13] ^ data_r[ 12] ^ data_r[ 11] ^ data_r[ 10] ^ data_r[  8] ^ data_r[  7] ^ data_r[  6] ^ data_r[  4] ^ data_r[  3] ^ data_r[  2] ^ data_r[  0];
		dq[  4] <= data_r[ 31] ^ data_r[ 26] ^ data_r[ 25] ^ data_r[ 24] ^ data_r[ 23] ^ data_r[ 22] ^ data_r[ 21] ^ data_r[ 19] ^ data_r[ 18] ^ data_r[ 17] ^ data_r[ 16] ^ data_r[ 15] ^ data_r[ 14] ^ data_r[ 13] ^ data_r[ 12] ^ data_r[ 11] ^ data_r[  9] ^ data_r[  8] ^ data_r[  7] ^ data_r[  5] ^ data_r[  4] ^ data_r[  3] ^ data_r[  1];
		dq[  5] <= data_r[ 27] ^ data_r[ 26] ^ data_r[ 25] ^ data_r[ 24] ^ data_r[ 23] ^ data_r[ 22] ^ data_r[ 20] ^ data_r[ 19] ^ data_r[ 18] ^ data_r[ 17] ^ data_r[ 16] ^ data_r[ 15] ^ data_r[ 14] ^ data_r[ 13] ^ data_r[ 12] ^ data_r[ 10] ^ data_r[  9] ^ data_r[  8] ^ data_r[  6] ^ data_r[  5] ^ data_r[  4] ^ data_r[  2];
		dq[  6] <= data_r[ 28] ^ data_r[ 27] ^ data_r[ 26] ^ data_r[ 25] ^ data_r[ 24] ^ data_r[ 23] ^ data_r[ 21] ^ data_r[ 20] ^ data_r[ 19] ^ data_r[ 18] ^ data_r[ 17] ^ data_r[ 16] ^ data_r[ 15] ^ data_r[ 14] ^ data_r[ 13] ^ data_r[ 11] ^ data_r[ 10] ^ data_r[  9] ^ data_r[  7] ^ data_r[  6] ^ data_r[  5] ^ data_r[  3];
		dq[  7] <= data_r[ 29] ^ data_r[ 28] ^ data_r[ 27] ^ data_r[ 26] ^ data_r[ 25] ^ data_r[ 24] ^ data_r[ 22] ^ data_r[ 21] ^ data_r[ 20] ^ data_r[ 19] ^ data_r[ 18] ^ data_r[ 17] ^ data_r[ 16] ^ data_r[ 15] ^ data_r[ 14] ^ data_r[ 12] ^ data_r[ 11] ^ data_r[ 10] ^ data_r[  8] ^ data_r[  7] ^ data_r[  6] ^ data_r[  4];
		dq[  8] <= data_r[ 30] ^ data_r[ 29] ^ data_r[ 28] ^ data_r[ 27] ^ data_r[ 26] ^ data_r[ 25] ^ data_r[ 23] ^ data_r[ 22] ^ data_r[ 21] ^ data_r[ 20] ^ data_r[ 19] ^ data_r[ 18] ^ data_r[ 17] ^ data_r[ 16] ^ data_r[ 15] ^ data_r[ 13] ^ data_r[ 12] ^ data_r[ 11] ^ data_r[  9] ^ data_r[  8] ^ data_r[  7] ^ data_r[  5];
		dq[  9] <= data_r[ 31] ^ data_r[ 30] ^ data_r[ 29] ^ data_r[ 28] ^ data_r[ 27] ^ data_r[ 26] ^ data_r[ 24] ^ data_r[ 23] ^ data_r[ 22] ^ data_r[ 21] ^ data_r[ 20] ^ data_r[ 19] ^ data_r[ 18] ^ data_r[ 17] ^ data_r[ 16] ^ data_r[ 14] ^ data_r[ 13] ^ data_r[ 12] ^ data_r[ 10] ^ data_r[  9] ^ data_r[  8] ^ data_r[  6];
		dq[ 10] <= data_r[ 31] ^ data_r[ 30] ^ data_r[ 29] ^ data_r[ 28] ^ data_r[ 27] ^ data_r[ 25] ^ data_r[ 24] ^ data_r[ 23] ^ data_r[ 22] ^ data_r[ 21] ^ data_r[ 20] ^ data_r[ 19] ^ data_r[ 18] ^ data_r[ 17] ^ data_r[ 15] ^ data_r[ 14] ^ data_r[ 13] ^ data_r[ 11] ^ data_r[ 10] ^ data_r[  9] ^ data_r[  7];
		dq[ 11] <= data_r[ 31] ^ data_r[ 30] ^ data_r[ 29] ^ data_r[ 28] ^ data_r[ 26] ^ data_r[ 25] ^ data_r[ 24] ^ data_r[ 23] ^ data_r[ 22] ^ data_r[ 21] ^ data_r[ 20] ^ data_r[ 19] ^ data_r[ 18] ^ data_r[ 16] ^ data_r[ 15] ^ data_r[ 14] ^ data_r[ 12] ^ data_r[ 11] ^ data_r[ 10] ^ data_r[  8];
		dq[ 12] <= data_r[ 30] ^ data_r[ 28] ^ data_r[ 27] ^ data_r[ 25] ^ data_r[ 24] ^ data_r[ 22] ^ data_r[ 19] ^ data_r[ 17] ^ data_r[ 16] ^ data_r[ 11] ^ data_r[  9] ^ data_r[  8] ^ data_r[  4] ^ data_r[  0];
		dq[ 13] <= data_r[ 31] ^ data_r[ 29] ^ data_r[ 28] ^ data_r[ 26] ^ data_r[ 25] ^ data_r[ 23] ^ data_r[ 20] ^ data_r[ 18] ^ data_r[ 17] ^ data_r[ 12] ^ data_r[ 10] ^ data_r[  9] ^ data_r[  5] ^ data_r[  1];
		dq[ 14] <= data_r[ 30] ^ data_r[ 29] ^ data_r[ 27] ^ data_r[ 26] ^ data_r[ 24] ^ data_r[ 21] ^ data_r[ 19] ^ data_r[ 18] ^ data_r[ 13] ^ data_r[ 11] ^ data_r[ 10] ^ data_r[  6] ^ data_r[  2];
		dq[ 15] <= data_r[ 31] ^ data_r[ 30] ^ data_r[ 28] ^ data_r[ 27] ^ data_r[ 25] ^ data_r[ 22] ^ data_r[ 20] ^ data_r[ 19] ^ data_r[ 14] ^ data_r[ 12] ^ data_r[ 11] ^ data_r[  7] ^ data_r[  3];
	end
endmodule 