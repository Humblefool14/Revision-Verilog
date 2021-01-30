class lpi_env extends uvm_env; 

    `uvm_component_utils(lpi_env)

    lpi_agent lpi_agent_h; 

    function new(string name = " lpi_env",uvm_component parent);
        super.new(name,parent);
    endfunction: new

    extern function void build_phase(uvm_phase phase);
    
    extern function void connect_phase(uvm_phase phase);

endclass : lpi_env

function void build_phase(uvm_phase phase);

    super.build_phase(phase);

    lpi_agent_h = lpi_agent :: type_id::create("lpi_agent_h",this);

endfunction : build_phase

function void connect_phase(uvm_phase phase);
endfunction : connect_phase