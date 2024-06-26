module test;
  initial begin
    $display("Current scope: %s", svGetNameFromScope(svGetScope()));
  end

  task my_task;
    $display("Task scope: %s", svGetNameFromScope(svGetScope()));
  endtask

  function void my_function();
    $display("Function scope: %s", svGetNameFromScope(svGetScope()));
  endfunction

  initial begin
    my_task();
    my_function();
  end
endmodule