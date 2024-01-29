

// TS1 
if(data_rate == 5.0 || data_rate == 2.5)
     symbol_0 = K28.5 ; //
if(data_rate >= 8.00)
     symbol_0 = 16'h1E; 

// 
 assign symbol_5 [BITSWDTH-1:0] = symbol[5]; 
 assign hot_reset               = symbol_5[`HOT_RESET] ? 1'b1: 1'b0; 
 assign link_disable            = symbol_5[`LINK_DIS]  ? 1'b1: 1'b0;
 assign loopbck_en              = symbol_5[`LPBK_EN]   ? 1'b1: 1'b0; 
 assign disable_scrambling      = symbol_5[`DIS_SCRAMBLING] ? 1'b1: 1'b0; 
 assign compliance_rcvr         = symbol_5[`COMPL_RCVR] ? 1'b1 : 1'b0; 
 assign loopback_head           = symbol_5[`COMPL_PTTR] ? 1'b1 : 1'b0; 