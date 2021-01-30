class simple_monitor extends uvm_monitor; 
    `uvm_component_utils(simple_monitor)
    // Interface
    virtual monitor_if monitor_vif; 
    function new (string name = "simple_monitor",uvm_component parent);
        super.new(name,parent);
    endfunction : new 

    function void build_phase(uvm_phase phase);      
    endfunction : build_phase


    function void connect_phase(uvm_phase phase);      
    endfunction : connect_phase//  Function: connect_phase

    extern task void run_phase(uvm_phase phase);

endclass : simple_monitor
    
task simple_monitor :: run_phase(uvm_phase phase);
    // 
endtask : run_phase 
