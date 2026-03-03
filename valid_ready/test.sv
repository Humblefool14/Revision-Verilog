// UVM Valid/Ready Protocol Testbench
// This testbench demonstrates a complete UVM environment for testing valid/ready handshake protocol

`include "uvm_macros.svh"
import uvm_pkg::*;

//=============================================================================
// Transaction Class
//=============================================================================
class vr_transaction extends uvm_sequence_item;
    rand bit [31:0] data;
    rand bit [3:0]  id;
    rand int        delay;
    
    bit valid;
    bit ready;
    bit last;
    
    `uvm_object_utils_begin(vr_transaction)
        `uvm_field_int(data, UVM_ALL_ON)
        `uvm_field_int(id, UVM_ALL_ON)
        `uvm_field_int(delay, UVM_ALL_ON)
        `uvm_field_int(valid, UVM_ALL_ON)
        `uvm_field_int(ready, UVM_ALL_ON)
        `uvm_field_int(last, UVM_ALL_ON)
    `uvm_object_utils_end
    
    constraint c_delay { delay inside {[0:10]}; }
    constraint c_data { data != 0; }
    
    function new(string name = "vr_transaction");
        super.new(name);
    endfunction
endclass

//=============================================================================
// Interface
//=============================================================================
interface vr_if(input logic clk, input logic rst_n);
    logic        valid;
    logic        ready;
    logic [31:0] data;
    logic [3:0]  id;
    logic        last;
    
    // Clocking blocks for synchronous operation
    clocking driver_cb @(posedge clk);
        default input #1 output #1;
        output valid, data, id, last;
        input ready;
    endclocking
    
    clocking monitor_cb @(posedge clk);
        default input #1;
        input valid, ready, data, id, last;
    endclocking
    
    // Modports
    modport DRIVER (clocking driver_cb, input clk, rst_n);
    modport MONITOR (clocking monitor_cb, input clk, rst_n);
    
endinterface

//=============================================================================
// Sequencer
//=============================================================================
class vr_sequencer extends uvm_sequencer #(vr_transaction);
    `uvm_component_utils(vr_sequencer)
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
endclass

//=============================================================================
// Driver
//=============================================================================
class vr_driver extends uvm_driver #(vr_transaction);
    `uvm_component_utils(vr_driver)
    
    virtual vr_if.DRIVER vif;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual vr_if)::get(this, "", "vif", vif))
            `uvm_fatal("NOVIF", "Virtual interface not set for driver")
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        vr_transaction req;
        
        // Initialize signals
        vif.driver_cb.valid <= 0;
        vif.driver_cb.data <= 0;
        vif.driver_cb.id <= 0;
        vif.driver_cb.last <= 0;
        
        // Wait for reset deassertion
        wait(vif.rst_n);
        
        forever begin
            seq_item_port.get_next_item(req);
            drive_transaction(req);
            seq_item_port.item_done();
        end
    endtask
    
    virtual task drive_transaction(vr_transaction tr);
        // Apply random delay before driving
        repeat(tr.delay) @(vif.driver_cb);
        
        // Drive the transaction
        vif.driver_cb.valid <= 1;
        vif.driver_cb.data <= tr.data;
        vif.driver_cb.id <= tr.id;
        vif.driver_cb.last <= tr.last;
        
        // Wait for ready signal (handshake completion)
        do begin
            @(vif.driver_cb);
        end while (!vif.driver_cb.ready);
        
        // Complete the handshake
        vif.driver_cb.valid <= 0;
        vif.driver_cb.data <= 0;
        vif.driver_cb.id <= 0;
        vif.driver_cb.last <= 0;
        
        `uvm_info("DRIVER", $sformatf("Drove transaction: data=0x%08h, id=%0d", tr.data, tr.id), UVM_MEDIUM)
    endtask
endclass

//=============================================================================
// Monitor
//=============================================================================
class vr_monitor extends uvm_monitor;
    `uvm_component_utils(vr_monitor)
    
    virtual vr_if.MONITOR vif;
    uvm_analysis_port #(vr_transaction) item_collected_port;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
        item_collected_port = new("item_collected_port", this);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual vr_if)::get(this, "", "vif", vif))
            `uvm_fatal("NOVIF", "Virtual interface not set for monitor")
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        vr_transaction tr;
        
        // Wait for reset deassertion
        wait(vif.rst_n);
        
        forever begin
            @(vif.monitor_cb);
            
            // Detect valid/ready handshake
            if(vif.monitor_cb.valid && vif.monitor_cb.ready) begin
                tr = vr_transaction::type_id::create("tr");
                tr.data = vif.monitor_cb.data;
                tr.id = vif.monitor_cb.id;
                tr.last = vif.monitor_cb.last;
                tr.valid = vif.monitor_cb.valid;
                tr.ready = vif.monitor_cb.ready;
                
                item_collected_port.write(tr);
                `uvm_info("MONITOR", $sformatf("Collected transaction: data=0x%08h, id=%0d", tr.data, tr.id), UVM_MEDIUM)
            end
        end
    endtask
endclass

//=============================================================================
// Agent
//=============================================================================
class vr_agent extends uvm_agent;
    `uvm_component_utils(vr_agent)
    
    vr_driver    driver;
    vr_monitor   monitor;
    vr_sequencer sequencer;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        monitor = vr_monitor::type_id::create("monitor", this);
        
        if(get_is_active() == UVM_ACTIVE) begin
            driver = vr_driver::type_id::create("driver", this);
            sequencer = vr_sequencer::type_id::create("sequencer", this);
        end
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        if(get_is_active() == UVM_ACTIVE) begin
            driver.seq_item_port.connect(sequencer.seq_item_export);
        end
    endfunction
endclass

//=============================================================================
// Scoreboard
//=============================================================================
class vr_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(vr_scoreboard)
    
    uvm_analysis_imp #(vr_transaction, vr_scoreboard) item_collected_export;
    
    int transactions_received;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
        item_collected_export = new("item_collected_export", this);
        transactions_received = 0;
    endfunction
    
    virtual function void write(vr_transaction tr);
        transactions_received++;
        `uvm_info("SCOREBOARD", $sformatf("Transaction #%0d received: data=0x%08h, id=%0d", 
                  transactions_received, tr.data, tr.id), UVM_MEDIUM)
        
        // Add your checking logic here
        // For example, check data integrity, ordering, etc.
        if(tr.data == 0) begin
            `uvm_error("SCOREBOARD", "Invalid data received (data=0)")
        end
    endfunction
    
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info("SCOREBOARD", $sformatf("Total transactions processed: %0d", transactions_received), UVM_LOW)
    endfunction
endclass

//=============================================================================
// Environment
//=============================================================================
class vr_env extends uvm_env;
    `uvm_component_utils(vr_env)
    
    vr_agent      agent;
    vr_scoreboard scoreboard;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        agent = vr_agent::type_id::create("agent", this);
        scoreboard = vr_scoreboard::type_id::create("scoreboard", this);
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        agent.monitor.item_collected_port.connect(scoreboard.item_collected_export);
    endfunction
endclass

//=============================================================================
// Base Sequence
//=============================================================================
class vr_base_sequence extends uvm_sequence #(vr_transaction);
    `uvm_object_utils(vr_base_sequence)
    
    function new(string name = "vr_base_sequence");
        super.new(name);
    endfunction
    
    virtual task pre_body();
        uvm_phase phase;
        `ifdef UVM_VERSION_1_2
            if(starting_phase != null) begin
                phase = starting_phase;
            end
        `else
            phase = get_starting_phase();
        `endif
        if(phase != null) begin
            phase.raise_objection(this, get_type_name());
            `uvm_info("SEQUENCE", "raise objection", UVM_MEDIUM)
        end
    endtask
    
    virtual task post_body();
        uvm_phase phase;
        `ifdef UVM_VERSION_1_2
            if(starting_phase != null) begin
                phase = starting_phase;
            end
        `else
            phase = get_starting_phase();
        `endif
        if(phase != null) begin
            phase.drop_objection(this, get_type_name());
            `uvm_info("SEQUENCE", "drop objection", UVM_MEDIUM)
        end
    endtask
endclass

//=============================================================================
// Simple Sequence
//=============================================================================
class vr_simple_sequence extends vr_base_sequence;
    `uvm_object_utils(vr_simple_sequence)
    
    function new(string name = "vr_simple_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        vr_transaction req;
        
        repeat(10) begin
            req = vr_transaction::type_id::create("req");
            start_item(req);
            if(!req.randomize()) begin
                `uvm_error("SEQUENCE", "Randomization failed")
            end
            finish_item(req);
        end
    endtask
endclass

//=============================================================================
// Burst Sequence
//=============================================================================
class vr_burst_sequence extends vr_base_sequence;
    `uvm_object_utils(vr_burst_sequence)
    
    rand int burst_length;
    constraint c_burst { burst_length inside {[5:20]}; }
    
    function new(string name = "vr_burst_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        vr_transaction req;
        
        repeat(burst_length) begin
            req = vr_transaction::type_id::create("req");
            start_item(req);
            if(!req.randomize() with {delay inside {[0:2]};}) begin
                `uvm_error("SEQUENCE", "Randomization failed")
            end
            // Mark last transaction in burst
            if($urandom_range(1,10) == 1) req.last = 1;
            finish_item(req);
        end
    endtask
endclass

//=============================================================================
// Test Base Class
//=============================================================================
class vr_base_test extends uvm_test;
    `uvm_component_utils(vr_base_test)
    
    vr_env env;
    
    function new(string name = "vr_base_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env = vr_env::type_id::create("env", this);
    endfunction
    
    virtual function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        uvm_top.print_topology();
    endfunction
endclass

//=============================================================================
// Simple Test
//=============================================================================
class vr_simple_test extends vr_base_test;
    `uvm_component_utils(vr_simple_test)
    
    function new(string name = "vr_simple_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        uvm_config_db#(uvm_object_wrapper)::set(this, "env.agent.sequencer.main_phase", 
                                                "default_sequence", vr_simple_sequence::type_id::get());
    endfunction
endclass

//=============================================================================
// Burst Test
//=============================================================================
class vr_burst_test extends vr_base_test;
    `uvm_component_utils(vr_burst_test)
    
    function new(string name = "vr_burst_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        uvm_config_db#(uvm_object_wrapper)::set(this, "env.agent.sequencer.main_phase", 
                                                "default_sequence", vr_burst_sequence::type_id::get());
    endfunction
endclass

//=============================================================================
// DUT (Simple Valid/Ready Interface)
//=============================================================================
module simple_dut (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        valid,
    input  logic [31:0] data,
    input  logic [3:0]  id,
    input  logic        last,
    output logic        ready
);
    
    // Simple ready generation with random delays
    logic [2:0] ready_delay_cnt;
    logic ready_internal;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            ready_delay_cnt <= 0;
            ready_internal <= 0;
        end else begin
            if (valid && !ready_internal) begin
                ready_delay_cnt <= ready_delay_cnt + 1;
                if (ready_delay_cnt >= $urandom_range(0,3)) begin
                    ready_internal <= 1;
                end
            end else if (valid && ready_internal) begin
                ready_internal <= 0;
                ready_delay_cnt <= 0;
            end
        end
    end
    
    assign ready = ready_internal;
    
endmodule

//=============================================================================
// Top Level Module
//=============================================================================
module tb_top;
    logic clk;
    logic rst_n;
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // Reset generation
    initial begin
        rst_n = 0;
        #20 rst_n = 1;
    end
    
    // Interface instantiation
    vr_if vif(clk, rst_n);
    
    // DUT instantiation
    simple_dut dut (
        .clk(clk),
        .rst_n(rst_n),
        .valid(vif.valid),
        .data(vif.data),
        .id(vif.id),
        .last(vif.last),
        .ready(vif.ready)
    );
    
    // UVM test execution
    initial begin
        uvm_config_db#(virtual vr_if)::set(null, "*", "vif", vif);
        run_test();
    end
    
    // Waveform dumping
    initial begin
        $dumpfile("waves.vcd");
        $dumpvars(0, tb_top);
    end
    
    // Timeout watchdog
    initial begin
        #10000;
        `uvm_fatal("TIMEOUT", "Test timeout reached")
    end
    
endmodule
