

localparam LOOPBACK_ENTRY = 
           LOOPBACK_ACTIVE = 
           LOOPBACK_EXIT   = 
           LOOPBACK_


logic  ltssm_n;
//reset 
perst_n; // pcie reset_n 
always @(negedge perst_n or posedge clk) begin 
    if(perst_n == 1'b0) begin 
        ltssm_n <= `LTSSM_POL_QUIET: 
        // 
    end 
    else begin 
         case (ltssm_n)
          `LTSSM_DETECT_QUIET: begin 
               // The next state is Detect.Active after a 12 ms timeout or if Electrical Idle Exit is detected on any Lane.
                Flit_Mode_Enabled                <= 0; 
                // • The Flit_Mode_Enabled variable is reset to 0b. (When Flit_Mode_Enabled is set to 0b, the link will not operate in Flit Mode.)
                L0p_capable                      <= 0; 
                use_modified_TS1_TS2_Ordered_Set <= 0; 
                // • The use_modified_TS1_TS2_Ordered_Set variable is reset to 0b.
                // • The L0p_capable variable is reset to 0b.
               if(detect_quiet_timeout || ~electrical_idle_exit_detected)
                        ltssm_n <= `LTSSM_DETECT_ACTIVE: 

          end 
              
          `LTSSM_DETECT_ACTIVE: begin 
             if(unconfigured_lines_received[3:0] == 4'b1111)
                  ltssm_n <= `LTSSM_POLLING; 
                  // Next state is Polling if a Receiver is detected on all unconfigured Lanes.
              else 
                ltssm_n <= `LTSSM_DETECT_QUIET; 
                // Next state is Detect.Quiet if a Receiver is not detected on any Lane.
            if()
          end 
         endcase
    end 
end 

