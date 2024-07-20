always @(posedge clk) begin
  a <= b + c;
  assert #0 (a == b + c) else $error("Assignment failed");
end
/// This is deferred assertions. 
/*
Unlike immediate assertions, deferred assertions are evaluated at the end of the current time step.
The #0 delay pushes the evaluation to the Observed region of the simulation event queue.
Purpose:
Allow checking of conditions that may not be stable immediately when the assertion is encountered.
Useful for checking results of assignments or other operations that occur in the same time step.
*/ 