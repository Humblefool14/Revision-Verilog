class lpi_seq_item extends uvm_sequence_item; 
        `uvm_object_utils(lpi_seq_item)
        // Data members 
        rand bit slp_req0; 
        rand bit slp_req1l 
        rand bit wakeup_req0; 
        rand bit wakeup_req1; 
        rand bit ss_wakeup; 
        rand bit ss_sleep; 
        //constructor Has to be every time a new function is called. 
        function.new (String name = " lpi_seq_item");
            super.new(name);
        endfunction

        constraint slp_wakeup_regs{ 
            ((((slp_req0 || slp_req1) && (wakeup_req0 || wakeup_req1))!=1));
        };
    endclass: lpi_seq_item 

        