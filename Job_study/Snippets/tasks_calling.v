class Env;

X_DEV #(
           .C_OUT_FILE  ("results/simulate_c/console_log.txt")
         )  X;

function new (
      X = new();
       ....
       ...
    
  task sv_X_wstr(string str);
    tb.X.write_string(str);
  endtask : sv_X_wrstr
  
endfunction : new 

In X module there is a task called write_string. This is calling that task there. 
