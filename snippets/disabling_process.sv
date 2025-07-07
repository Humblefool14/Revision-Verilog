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
endclass


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
      
          
    
