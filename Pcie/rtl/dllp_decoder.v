`include "dllp_defines.svh"

module dllp_decoder (
  input  logic [7:0] encoding,
  output dllp_defines::dllp_type_t dllp_type
);

  import dllp_defines::*;

  always_comb begin
    case(encoding[7:4])
      4'b0000: begin
        case(encoding[3:0])
          4'b0000: dllp_type = DLLP_ACK;
          4'b0001: dllp_type = DLLP_MRINIT;
          4'b0010: dllp_type = DLLP_DATA_LINK_FEATURE;
          default: dllp_type = DLLP_RESERVED;
        endcase
      end
      4'b0001: begin
        case(encoding[3:0])
          4'b0000: dllp_type = DLLP_NAK;
          default: dllp_type = DLLP_RESERVED;
        endcase
      end
      4'b0010: begin
        case(encoding[3:0])
          4'b0000: dllp_type = DLLP_PM_ENTER_L1;
          4'b0001: dllp_type = DLLP_PM_ENTER_L23;
          4'b0011: dllp_type = DLLP_PM_ACTIVE_STATE_REQ_L1;
          4'b0100: dllp_type = DLLP_PM_REQUEST_ACK;
          default: dllp_type = DLLP_RESERVED;
        endcase
      end
      4'b0011: begin
        case(encoding[3:0])
          4'b0000: dllp_type = DLLP_VENDOR_SPECIFIC;
          4'b0001: dllp_type = DLLP_NOP;
          default: dllp_type = DLLP_RESERVED;
        endcase
      end
      4'b0100: dllp_type = DLLP_INITFC1_P;
      4'b0101: dllp_type = DLLP_INITFC1_NP;
      4'b0110: dllp_type = DLLP_INITFC1_CPL;
      4'b0111: dllp_type = DLLP_MRINITFC1;
      4'b1100: dllp_type = DLLP_INITFC2_P;
      4'b1101: dllp_type = DLLP_INITFC2_NP;
      4'b1110: dllp_type = DLLP_INITFC2_CPL;
      4'b1111: dllp_type = DLLP_MRINITFC2;
      4'b1000: dllp_type = DLLP_UPDATEFC_P;
      4'b1001: dllp_type = DLLP_UPDATEFC_NP;
      4'b1010: dllp_type = DLLP_UPDATEFC_CPL;
      4'b1011: dllp_type = DLLP_MRUPDATEFC;
      default: dllp_type = DLLP_RESERVED;
    endcase
  end

endmodule