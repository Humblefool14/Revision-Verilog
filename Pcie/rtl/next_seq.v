

always@(tlp_accepted)
      next_seq <= (next_seq + 1)%4096; 
// NEXT_TRANSMIT_SEQ to a TLP accepted from Transmit side of the Transaction Layer, NEXT_TRANSMIT_SEQ is incremented
      
assign tlp_stall = ((next_seq - ackd_seq)%4096 >= 2048) ? 1'b1: 1'b0 ; 
//Transmitter must cease accepting TLPs from Transaction Layer until the equation is no longer true

// tlp_Sequence number. 