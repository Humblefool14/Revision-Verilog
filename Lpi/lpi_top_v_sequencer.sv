class lpi_top_v_sequencer extends uvm_sequencer; 
    `uvm_component_utils(lpi_top_v_sequencer)

    `uvm_sequencer_base lpi_sqr;

    function new(string name = "lpi_top_v_sequencer",uvm_component parent = null);

        super.new(name,parent);

    endfunction: new

endclass : lpi_top_v_sequencer