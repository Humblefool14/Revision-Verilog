
logic tx_no_accept = 1'b0; 

 
 reg [10-1: 0] next_tx_flit_seq_num; 
 reg [10-1: 0] tx_ack_nack_flit_seq_num ; 

// DL_STATE 
 if(dl_state == DL_INACTIVE)
    tx_ack_nack_flit_seq_num == 1023;  // 2^10-1 
    next_tx_flit_seq_num     == 1'h001;  

// consecutive_tx_explicit_seq_num_flits < 3 
//standard nack 
if(~explicited_seq_nack_flit)
   if(nack_scheduled_type == 'STANDARD_NAK') 
     send_nack_flit = 1'b1; 

//  A Transmitter must send a Selective Nak Flit if all of the following are true:
// ◦ NAK_SCHEDULED is 1b.
// ◦ NAK_SCHEDULED_TYPE is SELECTIVE_NAK.
// ◦ The conditions for sending an Explicit Sequence Number Flit were not met.
// ◦ The conditions for sending a Standard Nak Flit were not met.

//selective nack 
if(nack_scheduled)
  if(nack_scheduled_type == 'SELECTIVE_NAK')
   if(~explicited_seq_nack_flit)
      if(~standard_nak_flit)
        // 
        send_selective_nak = 1'b1; 

//Send ACK FLIT 
if(~explicited_seq_nack_flit)
  if(~standard_nak_flit)
    if(~selective_nak_flit)
         send_ack_flit   = 1'b1; 

  if(~replay_progress && ~replay_scheduled)
      nop_flit_en   = 1'b1; 
      /// The Transmitter must send a NOP Flit if REPLAY_SCHEDULED is 0b and REPLAY_IN_PROGRESS is 0b.

  if(nop_flit_en)
     flit_seq_num <= flit_seq_num; 

     // • NOP Flits do not consume a Flit Sequence Number.
  if(nop_flit_en && nop_flit_typ == 'EXPLICIT_SEQ_NUM_FLIT)
     flit_seq_num == NEXT_TX_FLIT_SEQ_NUM -1; 
  
  if((NEXT_TX_FLIT_SEQ_NUM - ACKD_FLIT_SEQ_NUM)%1023 > max_unackwoledged_flit)
         tx_no_accept = 1'b1; 
         if (replay_scheduled == 1'b0 && replay_progress  == 1'b0) 
             nop_flit_en = 1'b1;  
         // ◦ The Transmitter must not accept any new TLPs from the Transaction Layer.

  if(replay_progress)
     tx_no_accept = 1'b1; 
     // If REPLAY_IN_PROGRESS is 1b: The Transmitter must not accept any new TLPs from the Transaction Layer. 
 
   replay_progress = (((replay_scheduled_type == 'STANDARD_REPLAY') && ~unack_flits_num) || 
                      (replay_scheduled_type ==  'STANDARD_REPLAY' && (flit_seq_num == tx_flit_seq_num))) ? 1'b1 : 1'b0; 
    // ▪ REPLAY_SCHEDULED_TYPE is STANDARD_REPLAY and all unacknowledged Flits in the TX Retry Buffer have been transmitted.
    //▪ REPLAY_SCHEDULED_TYPE is SELECTIVE_REPLAY and Flit with Flit Sequence Number equal to TX_REPLAY_FLIT_SEQ_NUM has been transmitted.


  
