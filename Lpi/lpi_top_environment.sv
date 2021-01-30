class lpi_top_env extends uvm_env; 
        `uvm_component_utils(lpi_top_env)

        uvm_event_poole_pool = uvm_event_pool :: get_global_pool(); 

        lpi_top_v_sequencer lpi_top_v_sqr_h; 

        lpi_env lpi_env_h; 

        extern function new(string name = "lpi_top_env",uvm_component parent);

        extern function void build_phase(uvm_phase phase);

        extern function void connect_phase(uvm_phase phase);

        extern task run_phase(uvm_phase phase);

endclass : lpi_top_env

function lpi_top_env :: new(string name = "lpi_top_env",uvm_component parent);

    super.new(name,parent);

endfunction 

function void lpi_top_env :: build_phase(uvm_phase phase);
    string msg = "\n";

    msg = {msg, "=======================================\n"}; 
    msg = {msg, "*LPI TOP ENV BUILD PHASE SUMMARY*\n"};

    msg = {msg, "=======================================\n"}; // Setting default verbosity to LOW

    if (!$test$plusargs("UVM_VERBOSITY")) begin
            // UVM(ID,MSG,UVM_verbosity)
            `uvm_info (get_name()," \nUVM_VERBOSITY not defined, using UVM_LOW \n ", UVM_LOW) 

            uvm_top.set_report_verbosity_level_hier(UVM_LOW);
     end 
    super.build_phase(phase);


    lpi_env_h = lpi_env::type_id::create("lpi_env_h",this);
//*** Build Virtual Sequencer ***
    msg = {msg, "LPI TOP V_SEQUENCER\n"};

    lpi_top_v_sqr_h = lpi_top_v_sequencer::type_id::create("lpi_top_v_sqr_h", this); 

endfunction:build_phase

//Connect Phase
function void lpi_top_env::connect_phase(uvm_phase phase);

    string msg = "\n";

    int i;

    super.connect();

    msg = {msg, "=======================================\n"}; 

    msg = {msg, "*LPI TOP ENV CONNECT PHASE SUMMARY*\n"};

    msg = {msg, "=======================================\n"};

    lpi_top_v_sqr_h.lpi_sqr = lpi_env_h.lpi_agent_h.lpi_sequencer_h; //Connect other agents sequencers

    uvm_config_db #(lpi_top_v_sequencer)::set(uvm_top, "", "lpi_top_v_sqr_h", lpi_top_v_sqr_h); 

    `uvm_info(get_name(), msg, UVM_LOW)
        //--------------------------------------------------------------- 
endfunction:connect_phase

task lpi_top_env::run_phase(uvm_phase phase); 
        int i;

        super.run_phase(phase);
endtask