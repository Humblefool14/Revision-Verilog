
module tlp_hdr_mgmt(
  input  [TLPTYP-1:0] tlp_hdr_type, 
  input  [TLPFMT-1:0] tlp_hdr_fmt, 
  input  [TLPTFC-1:0] tlp_hdr_traffic_cls; 
  input               tlp_hdr_td, 
  input               tlp_hdr_ep, // 1 means poisoned data 
  input  [TLPATR-1:0] tlp_hdr_attr,
  input  [TLPLTH-1:0] tlp_hdr_lth, // tlp_length
  input               tlp_hdr_td,  // 
  input               tlp_hdr_addr_lo, 
  input               tlp_hdr_addr_hi,
  input  [TLPDBE-1:0] tlp_hdr_dw 
); 


// tlp_td == 1 & no tlp_digest --> malformed tlp. 
// tlp_td == 1 & device supports ecrc --> ecrc_check 


logic [TLP_CNTS-1:0] tlp
always_comb begin 
    tlp_0 = 0; 
    case(tlp_fmt)
    0: tlp_type = MRDW; 
    1: tlp_type = MRDLK; 
    


endmodule 