class loi_basic_test extends uvm_test; 
    `uvm_component_utils(lpi_basic_test)

    lpi_basic_seq lpi_basic_seq_h; 

    lpi_top_env m_lpi_top_env;
    

    virtual lpi_if lpi_vif; 

    function new(string name = "lpi_monitor",uvm_component parent = null);
        super.new(name,parent);
    endfunction: new

    function void build_phase(uvm_phase phase);
        
        super.build();

        m_lpi_top_env = lpi_top_env :: type_id :: create("m_lpi_top_env",this);

        lpi_basic_seq_h = lpi_basic_seq :: type_id:: create("lpi_basic_seq_h",this);

        set_config_int ("m_lpi_top_env.lpi_env_h.lpi_agent_h","is_active",UVM_ACTIVE);

    endfunction : build_phase

    task run_phase(uvm_phase,phase);

        super.run_phase(phase);

        phase.raise_objection(this,"Starting_test_seq");

        if(!(uvm_config_db #(virtual lpi_if) :: get(null,"","lpi_vif",lpi_vif)))
            begin 
                `uvm_fatal(get_name(),"Can;t retrieve lpi_vif from config db \n")
            end 
        
        if(!lpi_basic_seq_h.randomize() with {num_of_trans == 20;})

        `uvm_fatal(gt_name()),"randomization of lpi_basic_seq_h sequence failed. \n")

        `uvm_info(get_name(),"Starting seq here \n",UVM_LOW)

        wait (lpi_vif.lpi_rstn == 1); 

        `uvm_info(get_name(),"reset done\n",UVM_LOW)

        lpi_basic_seq_h.start(m_lpi_top_env.lpi_env_h.lpi_agent_h.lpi_sequencer_h);

        `uvm_info(get_name(),"#######\n",UVM_LOW);

        `uvm_info(get_name(),"HELLO WORLD \n",UVM_LOW);

        `uvm_info(get_name(),"###### \n",UVM_LOW);

        phase.drop_objection(this,"Finished lpi_basic_test \n");

        endtask

    endclass 

