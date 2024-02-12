
logic flow_control_vc0 = 0; 


always @(negedge resetn or posedge clk) begin 
  dl_up <= 0; 
  dl_down <= 0; 
end  
// dl_up == 1 
// implies Data Link Layer reports entry to the DL_Up status to the Transaction Layer, indicating that the Link is operational.
case (dllp_state)
    DL_FEATURE : begin 
        if(physical_link_up && (data_link_feature_exchan || data_link_feature_exchan_optional))
        // Data Link Feature Exchange completes successfully, and the Physical Layer continues to report Physical LinkUp = 1b,
        // Data Link Feature Exchange determines that the remote Data Link Layer does not support the optional Data Link Feature Exchange protocol
        else if (~(physical_link_up))
            dllp_state <= DL_INACTIVE; 
        // Physical Layer reports Physical LinkUp = 0b
    end 
    DL_INIT: begin 
     flow_control_vc0 = 1; 
    if(fc_state == FC_INIT1) begin 
          dllp_down <= 1; 
          dllp_up   <= 0; 
           // Report DL_Down status while in state FC_INIT1;
    end 
    if(fc_state == FC_INIT2) begin 
         // dllp_up <= DL_UP: 
           dllp_up <= 1; 
           //DL_Up status while in state FC_INIT2
    end 
    // fc_state or fc_done ? 
    if(fc_state == FC_DONE &&  physical_link_up) begin 
           dllp_state <= DL_ACTIVE; 
           dllp_up <= 1; 
    end 
         // Flow Control initialization completes successfully,
         // and the Physical Layer continues to report Physical LinkUp = 1b
    else 
         dllp_state <= DL_INACTIVE; 
         flow_control_vc0 <= 0; 
         // Terminate attempt to initialize Flow Control for VC0 
         // and exit to DL_Inactive if: ▪ Physical Layer reports Physical LinkUp = 0b
    end 
    DL_ACTIVE: begin 
        if(~physical_link_up) begin 
            //Physical Layer reports Physical LinkUp = 0b
            dllp_state <= DL_INACTIVE; 
        end 
    end 
        // else stay in the dl_active state. 
        // ▪ Accept and transfer TLP information with the Transaction and Physical Layers as specified
        // ▪ Generate and accept DLLPs as specified in this chapter
endcase 