// Port operation modes
typedef enum logic [1:0] {
  SUPERSPEED      = 2'b01,
  SUPERSPEED_PLUS = 2'b10
} port_mode_e;

// Packet types
typedef enum logic [1:0] {
  HEADER_PKT = 2'b00,  // SuperSpeed header packet
  TYPE1_PKT  = 2'b01,  // SuperSpeedPlus Type 1 packet
  TYPE2_PKT  = 2'b10   // SuperSpeedPlus Type 2 packet
} packet_type_e;

// Task to check if packet transmission is allowed based on credit count
task automatic check_transmit_allowed(
  input  port_mode_e    port_mode,
  input  packet_type_e  pkt_type,
  input  int            remote_rx_header_credit_count,
  input  int            remote_type1_rx_credit_count,
  input  int            remote_type2_rx_credit_count,
  output logic          transmit_allowed,
  output string         reason
);
  
  transmit_allowed = 1'b0;
  reason = "";
  
  case (port_mode)
    
    SUPERSPEED: begin
      // SuperSpeed: Check header packet credits only
      if (pkt_type == HEADER_PKT) begin
        if (remote_rx_header_credit_count == 0) begin
          transmit_allowed = 1'b0;
          reason = "SuperSpeed: Cannot transmit header packet - Remote Rx Header Buffer Credit Count is zero";
        end else begin
          transmit_allowed = 1'b1;
          reason = "SuperSpeed: Header packet transmission allowed";
        end
      end else begin
        transmit_allowed = 1'b0;
        reason = "SuperSpeed: Only header packets are valid in SuperSpeed mode";
      end
    end
    
    SUPERSPEED_PLUS: begin
      // SuperSpeedPlus: Check Type 1 or Type 2 packet credits
      case (pkt_type)
        TYPE1_PKT: begin
          if (remote_type1_rx_credit_count == 0) begin
            transmit_allowed = 1'b0;
            reason = "SuperSpeedPlus: Cannot transmit Type 1 packet - Remote Type 1 Rx Buffer Credit Count is zero";
          end else begin
            transmit_allowed = 1'b1;
            reason = "SuperSpeedPlus: Type 1 packet transmission allowed";
          end
        end
        
        TYPE2_PKT: begin
          if (remote_type2_rx_credit_count == 0) begin
            transmit_allowed = 1'b0;
            reason = "SuperSpeedPlus: Cannot transmit Type 2 packet - Remote Type 2 Rx Buffer Credit Count is zero";
          end else begin
            transmit_allowed = 1'b1;
            reason = "SuperSpeedPlus: Type 2 packet transmission allowed";
          end
        end
        
        default: begin
          transmit_allowed = 1'b0;
          reason = "SuperSpeedPlus: Invalid packet type";
        end
      endcase
    end
    
    default: begin
      transmit_allowed = 1'b0;
      reason = "Invalid port mode";
    end
    
  endcase
  
endtask
