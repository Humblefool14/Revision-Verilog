// Why DLLP's ? 
// Note that while DLLPs contain VC ID information for Flow Control accounting, TLPs do not.  



//
// Configuration software is responsible for configuring Ports on both sides of the Link for a matching number of VCs.
// This is accomplished by scanning the hierarchy and using VC or MFVC Extended Capability registers associated with Ports (that support more than default VC0)
//  to establish the number of VCs for the Link.


// VC ID must be same and unique. Unique key and lock combination. 

wire tlp_accepted_layer ; 
wire tlp_rejected_layer ;
tlp_accepted_layer = tlp_accpt_upstream; 

tlp_contents = {4'b0, tlp_next_seq_num,tlp_header}; 
// ▪ prepending the 12-bit value in NEXT_TRANSMIT_SEQ to the TLP
// ▪ prepending 4 bits to the TLP, preceding the sequence number (see § Figure 3-18)

if((tlp_next_seq_num - ackd_seq)%4096 >= 2048) begin 
   tlp_accepted_layer <= 0; 
end 
   else if(tlp_accepted_layer & (!nullified_tlp))begin
    //NEXT_TRANSMIT_SEQ to a TLP accepted from the Transmit side of the Transaction Layer, NEXT_TRANSMIT_SEQ is incremented  
      tlp_next_seq_num <= (tlp_next_seq_num +1)%(4096); 
  end 



always @(posedge pcie_clk or negedge pcie_rst_n or negedge pci_per_rstn) begin
  if (!pcie_rst_n or !pci_per_rstn) begin
    dll_state        <= 1'b0;
  end
  else begin
    int_dst_pcie     <= int_dst_pcie_wire;
    int_dst_usb      <= int_dst_usb_wire ;
    int_dst_pcie_reg <= int_dst[INTPCIX] ;
  end
end
