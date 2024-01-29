

case (dllp_state)

    DL_INACTIVE: begin 
    dllp_state <= DL_INIT; 
    end 
    DL_FEATURE : begin 
        if(link_up)
           dllp_state <= DL_IN_ACTIVE; 
        else if (())
            dllp_state <= DL_INIT; 

    end 
    DL_INIT: 
    dllp_state <= DL_ACTIVE;

    DL_ACTIVE: 
    dllp_state <= DL_INACTIVE; 
endcase