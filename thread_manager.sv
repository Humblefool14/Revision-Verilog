module thread_manager;
    
    // Shared variables
    int thread_count = 0;
    bit disable_flag = 0;
    semaphore sem = new(1); // Mutex for thread_count
    
    // Task to simulate thread work
    task automatic thread_work(int thread_id);
        begin
            // Critical section to update thread count
            sem.get(1);
            thread_count++;
            $display("Thread %0d started (Total active: %0d)", thread_id, thread_count);
            
            // Check if this is the 500th thread
            if (thread_count == 500) begin
                disable_flag = 1;
                $display("*** DISABLE TRIGGERED by Thread %0d (500th thread) ***", thread_id);
                sem.put(1);
                disable fork; // Disable all spawned threads
                return;
            end
            sem.put(1);
            
            // Simulate some work (only if not disabled)
            if (!disable_flag) begin
                #(thread_id % 10 + 1); // Variable delay based on thread ID
                $display("Thread %0d completed work", thread_id);
            end
        end
    endtask
    
    // Main test
    initial begin
        $display("Starting 1000 threads...");
        $display("Will disable all threads when 500th thread starts");
        
        // Fork 1000 threads
        fork
            begin : thread_spawner
                for (int i = 1; i <= 1000; i++) begin
                    fork
                        automatic int tid = i;
                        thread_work(tid);
                    join_none
                    
                    // Small delay between thread spawns
                    #0.1;
                    
                    // Break if disable flag is set
                    if (disable_flag) begin
                        $display("Stopping thread creation at thread %0d", i);
                        break;
                    end
                end
            end
        join
        
        // Wait a bit for any remaining threads to complete
        #100;
        
        $display("\n=== FINAL SUMMARY ===");
        $display("Total threads that started: %0d", thread_count);
        $display("Disable flag status: %0d", disable_flag);
        $display("Expected: 500 threads started, then disabled");
        
        $finish;
    end
    
    // Monitor for runaway simulation
    initial begin
        #10000; // Timeout after 10000 time units
        $display("ERROR: Simulation timeout - forcing finish");
        $finish;
    end
    
endmodule

// Alternative implementation using disable with labeled blocks
module thread_manager_v2;
    
    int active_threads = 0;
    
    task automatic worker_thread(int id);
        begin
            $display("Thread %0d: Starting work", id);
            
            // Simulate work with random delay
            repeat(id % 5 + 1) #1;
            
            $display("Thread %0d: Work completed", id);
        end
    endtask
    
    initial begin
        $display("\n=== Alternative Implementation ===");
        $display("Launching 1000 threads with disable on 500th");
        
        begin : main_block
            fork
                // Thread launcher
                begin : launcher
                    for (int i = 1; i <= 1000; i++) begin
                        fork
                            begin
                                automatic int thread_id = i;
                                active_threads++;
                                
                                // Check for 500th thread
                                if (active_threads == 500) begin
                                    $display("*** Thread %0d (500th) triggering disable ***", thread_id);
                                    #1; // Small delay to show the disable effect
                                    disable main_block;
                                end
                                
                                worker_thread(thread_id);
                            end
                        join_none
                        
                        #0.1; // Small spawn delay
                    end
                end
            join
        end
        
        $display("Threads launched before disable: %0d", active_threads);
        #50; // Wait for any remaining work
        $finish;
    end
    
endmodule
