//class lpi_basic_seq extends //  Class:  lpi_basic_seq
//
class  lpi_basic_seq extends uvm_sequence #(lpi_seq_item);
    `uvm_object_utils( lpi_basic_seq);

    //  Group: Variables

    rand int num_of_trans; 
    //  Group: Constraints


    //  Group: Functions

    //  Constructor: new
    function new(string name = " lpi_basic_seq");
        super.new(name);
    endfunction: new

    //  Task: pre_start
    //  This task is a user-definable callback that is called before the optional 
    //  execution of <pre_body>.
    // extern virtual task pre_start();

    //  Task: pre_body
    //  This task is a user-definable callback that is called before the execution 
    //  of <body> ~only~ when the sequence is started with <start>.
    //  If <start> is called with ~call_pre_post~ set to 0, ~pre_body~ is not called.
    // extern virtual task pre_body();

    //  Task: pre_do
    //  This task is a user-definable callback task that is called ~on the parent 
    //  sequence~, if any. The sequence has issued a wait_for_grant() call and after
    //  the sequencer has selected this sequence, and before the item is randomized.
    //
    //  Although pre_do is a task, consuming simulation cycles may result in unexpected
    //  behavior on the driver.
    // extern virtual task pre_do(bit is_item);

    //  Function: mid_do
    //  This function is a user-definable callback function that is called after the 
    //  sequence item has been randomized, and just before the item is sent to the 
    //  driver.
    // extern virtual function void mid_do(uvm_sequence_item this_item);

    //  Task: body
    //  This is the user-defined task where the main sequence code resides.
    extern virtual task body();

    //  Function: post_do
    //  This function is a user-definable callback function that is called after the 
    //  driver has indicated that it has completed the item, using either this 
    //  item_done or put methods. 
    // extern virtual function void post_do(uvm_sequence_item this_item);

    //  Task: post_body
    //  This task is a user-definable callback task that is called after the execution 
    //  of <body> ~only~ when the sequence is started with <start>.
    //  If <start> is called with ~call_pre_post~ set to 0, ~post_body~ is not called.
    // extern virtual task post_body();

    //  Task: post_start
    //  This task is a user-definable callback that is called after the optional 
    //  execution of <post_body>.
    // extern virtual task post_start();
    
endclass:  lpi_basic_seq

task lpi_basic_seq :: body();
    lpi_seq_itemseq_item; 
    seq_item = lpi_seq_item :: type_id :: create("seq_item");

    for(int i=0; i<num_of_trans;i++)
    begin 
        `uvm_info(get_type_name(),$psprintf("in seq for count == %d",i,UVM_LOW))
            start_item(seq_item);
            if(!seq_item.randomize())
                begin 
                    `uvm_error("body","randomization failed for seq items")
                end 
                `uvm_info(get_type_name(),$psprintf("Obj is req0=%d,req1=%d,sleep0=%d,sleep1= %d,"
                            seq_item.wakeup_req0,seq_item.wakeup_req1,seq_item.slp_req0,seq_item.slp_req1),UVM_LOW)
            finish_item(seq_item)
    end 
endtask : body 
