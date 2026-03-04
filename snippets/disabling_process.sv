/* Prototype
class process;
typedef enum { FINISHED, RUNNING, WAITING, SUSPENDED, KILLED } state;
static function process self();
function state status();
function void kill();
task await();
function void suspend();
function void resume();
function void srandom( int seed );
function string get_randstate();
function void set_randstate( string state );
endclass; 
*/

class process;
  enum state { FINISHED, RUNNING, WAITING, SUSPENDED, KILLED };  
  local state current_state = RUNNING;
  local event done_event;  // Event to signal completion
  
  static function process self();
    // Returns the current process handle
    return this;
  endfunction
  
  function state status();
    return current_state;
  endfunction
  
  // AWAIT - Wait for process to finish
  task await();
    wait(current_state == FINISHED);
    // Or alternatively:
    // @(done_event);
  endtask
  
  // KILL - Terminate the process
  function void kill();
    current_state = KILLED;
    // Trigger the done event so any awaiting processes wake up
    -> done_event;
  endfunction
  
  function void suspend();
    current_state = SUSPENDED;
  endfunction
  
  function void resume();
    if(current_state == SUSPENDED)
      current_state = RUNNING;
  endfunction
  
  // Internal: Call this when process naturally completes
  function void mark_finished();
    current_state = FINISHED;
    -> done_event;  // Wake up any awaiting tasks
  endfunction
  
endclass;


  task automatic do_way(int N, int k); 
    process job[] = new[N]; 

    foreach(job[i])
      fork 
        automatic k = i; 
        begin job[k] = process::self(); 
        end; 
      join_none 

    foreach(job[i])
      wait(job[i]!=null); 

    job[k].await(); 

    foreach(job[i])
      if(job[i].status() != process::FINISHED)
        job[i].kill(); 
    end 
  endtask 
      
          
    
