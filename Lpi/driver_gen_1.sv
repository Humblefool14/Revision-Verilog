class lpi_driver extends uvm_driver #(simple_item,simple_rsp);
    simple_item s_item;
    virtual dut_if vif;

    `uvm_component_utils(lpi_driver)

    function new (string name = "lpi_driver",uvm_component parent);
        super.new(name,parent);
    endfunction : new 

    function  void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_coding_db #(virtual dut_if):: get(this,"","vif",vif))
              begin 
                     `uvm_fatal("NOVIF",{"virtual interface must be set for :",get_full_name(),".vif"});
              end   
    endfunction : build_phase 