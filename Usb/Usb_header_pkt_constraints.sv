// SuperSpeed
constraint ss_tx  { transmit_header_pkt == 1 -> Remote_Rx_Header_BCC > 0; }

// SuperSpeedPlus (SSP)
constraint ssp_tx_type1 { transmit_type1_pkt == 1 -> Remote_Type1_Rx_BCC > 0; }
constraint ssp_tx_type2 { transmit_type2_pkt == 1 -> Remote_Type2_Rx_BCC > 0; }
