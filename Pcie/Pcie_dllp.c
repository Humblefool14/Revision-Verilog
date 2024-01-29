if (NON_IDLE_EXPLICIT_SEQ_NUM_FLIT_RCVD == 0) {
   //See Receiver Rules in IDLE Flit Handshake Phase
}
//# Invalid Flit Handling
else if (Received Invalid Flit) {
    if (NAK_SCHEDULED == 1) {
        if (NAK_SCHEDULED_TYPE == STANDARD_NAK) {
            Flit Discard 1
        }
        else {
           // Nak Schedule 6
        } 
   }
    else {
        if (NAK_WITHDRAWAL_ALLOWED == 1) {
            Nak Schedule 1
        }
        else {
            Nak Schedule 0
       } 
}
}

//# Valid Flit Handling
else if (Received Valid Flit) {
    if ((Explicit Sequence Number Flit) && (Flit Sequence Number == 0)) {
        Flit Discard 2
    }
    else if (NAK_WITHDRAWAL_ALLOWED == 1b) {
        NAK_WITHDRAWAL_ALLOWED = 0b;
        if (Prior Flit was Payload) {
            if (NOP Flit) {
                //# Schedule a Standard or Selective Nak
                //Discard Flit's TLP Bytes
                NAK_SCHEDULED = 1b;
                TX_ACKNAK_FLIT_SEQ_NUM = NEXT_EXPECTED_RX_FLIT_SEQ_NUM - 1;
                NAK_SCHEDULED_TYPE = STANDARD_NAK or SELECTIVE_NAK
                NEXT_EXPECTED_RX_FLIT_SEQ_NUM does not change;
                if (Scheduling a Selective Nak) {
                    NEXT_RX_FLIT_SEQ_NUM_TO_STORE = NEXT_EXPECTED_RX_FLIT_SEQ_NUM + 1
} }
          //  # Current Flit is Payload Flit
            else {
                //# Schedule a Standard Nak
                if (Scheduling a Standard Nak) {
                    standard_nak_procedure()
                }
              //  # Schedule a Selective Nak
                else {
                    NEXT_RX_FLIT_SEQ_NUM_TO_STORE = NEXT_EXPECT_RX_FLIT_SEQ_NUM + 1;
                    selective_nak_procedure()
                }
} }
      //  # Prior Flit was NOP
        else {
            if (bad_sequence_number() || ((NOP Flit) && bad_nop_sequence_number())) {
                Nak Schedule 2
            }
         //   # Withdraw Nak
            else {
                if (((Payload Flit) && duplicate_sequence_number()) || (NOP Flit)) {
                    //# Schedule Ack 
                    for NEXT_EXPECTED_RX_FLIT_SEQ_NUM - 1
                    TX_ACKNAK_FLIT_SEQ_NUM is set to NEXT_EXPECTED_RX_FLIT_SEQ_NUM - 1
                   // Discard Flit's TLP Bytes
             }
                if ((Payload Flit) && (NEXT_EXPECTED_RX_FLIT_SEQ_NUM == IMPLICIT_RX_FLIT_SEQ_NUM)) {
                    # Schedule Ack for NEXT_EXPECTED_RX_FLIT_SEQ_NUM
                    TX_ACKNAK_FLIT_SEQ_NUM is set to NEXT_EXPECTED_RX_FLIT_SEQ_NUM
                    Increment NEXT_EXPECTED_RX_FLIT_SEQ_NUM
                } 
             }
        }

        }
//# NAK_WITHDRAWAL_ALLOWED == 0b
else {
    if (NAK_SCHEDULED == 1b) {
        if (NAK_SCHEDULED_TYPE == Standard Nak) {
            if (NOP Flit) {
                if ((Explicit Sequence Number Flit) &&
                     (IMPLICIT_RX_FLIT_SEQ_NUM == (NEXT_EXPECTED_RX_FLIT_SEQ_NUM-1))) {
                   // NAK_SCHEDULED = 0b
                    //Discard Flit's TLP Bytes
                    } else {
                    Flit Discard 0
                }
            }
           // # Payload Flit
            else {
                standard_nak_procedure()
            }
        }
       // # Selective Nak
        else {
            if (NOP Flit) {
                Flit Discard 0
            }
           // # Payload Flit
            else {
                selective_nak_procedure()
            }
        } 
     }
   }
    else {
        if (NOP Flit) {
            if (bad_nop_sequence_number())) {
                Nak Schedule 2
} else {
                Flit Discard 0
            }
        }
        # Payload Flit
        else {
            if (duplicate_sequence_number()) {
                Flit Discard 0
            }
            else if (bad_sequence_number()){
                Nak Schedule 2
            }
            else {
                # Forward Progress
                Ack Schedule 0
} }

} }
}
# Bad Sequence Number Check Logic
def bad_sequence_number() {
    return (NEXT_EXPECT_RX_FLIT_SEQ_NUM - IMPLICIT_RX_FLIT_SEQ_NUM) mod 1023 > 511
}
def bad_nop_sequence_number() {
    return bad_sequence_number() || (IMPLICIT_RX_FLIT_SEQ_NUM ==
NEXT_EXPECTED_RX_FLIT_SEQ_NUM)
}
# Duplicate Sequence Number Check Logic
def duplicate_sequence_number() {
    return ((TX_ACKNAK_FLIT_SEQ_NUM - IMPLICIT_RX_FLIT_SEQ_NUM) mod 1023 < 511)
}
# Ack/Nak/Discard Logic when scheduling a Standard Nak or when a Standard Nak is
outstanding.
def standard_nak_procedure() {
    if (duplicate_sequence_number()) {
        if (NAK_SCHEDULED == 1b) {
            Flit Discard 0
        }
        else {
            Nak Schedule 2
} }
    else if ((Received Flit is Explicit Sequence Number Flit) &&
         (IMPLICIT_RX_FLIT_SEQ_NUM == NEXT_EXPECTED_RX_FLIT_SEQ_NUM)) {
        Ack Schedule 1
    }
    else {
        if (NAK_SCHEDULED == 1b) {
            Flit Discard 0
        }
        else {
            Nak Schedule 2
} }
}
# Ack/Nak/Discard Logic when scheduling a Selective Nak or when a Selective Nak is
outstanding.
def selective_nak_procedure() {
    if (duplicate_sequence_number()) {
        Flit Discard 0
    }
    else if ((Received Flit is Explicit Sequence Number Flit) &&
             (IMPLICIT_RX_FLIT_SEQ_NUM == NEXT_EXPECTED_RX_FLIT_SEQ_NUM)) {
                if (RX_RETRY_BUFFER_OVERFLOW == 1) {
            Nak Schedule 5
} else {
            Ack Schedule 2
        }
    }
    else if (IMPLICIT_RX_FLIT_SEQ_NUM == NEXT_RX_FLIT_SEQ_NUM_TO_STORE) {
        if (RX RETRY BUFFER FULL) {
            Nak Schedule 4
} else {
            Nak Schedule 3
        }
    }
    # Bad Sequence Number
    else {
        Nak Schedule 2
    }
}