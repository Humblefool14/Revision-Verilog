// Write Constraints

class transaction extends uvm_sequence_item;
    uvm_object_utils(transaction)

    // TODO: Declare rand variable
  rand bit [2:0] a [300];

    constraint constraint_c {
  // Value domain: each element in {0,1,2,3,4,5}
  foreach (a[i]) {
    a[i] inside {0, 1, 2, 3, 4, 5};
  }

  // No consecutive zeros
  foreach (a[i]) {
    if (i < 299) {
      !(a[i] == 0 && a[i+1] == 0);
    }
  }

  // Minimum frequency >= 40 for each value (int cast prevents overflow)
  (a.sum() with (int'(item == 0 ? 1 : 0))) >= 40;
  (a.sum() with (int'(item == 1 ? 1 : 0))) >= 40;
  (a.sum() with (int'(item == 2 ? 1 : 0))) >= 40;
  (a.sum() with (int'(item == 3 ? 1 : 0))) >= 40;
  (a.sum() with (int'(item == 4 ? 1 : 0))) >= 40;
  (a.sum() with (int'(item == 5 ? 1 : 0))) >= 40;
}
    }

    function void display();
       // TODO: Display method
           int count [6];
    int consec_zero_violations = 0;

    $display("=== Transaction Array (size=300) ===");
    for (int i = 0; i < 300; i++) begin
      count[a[i]]++;
      if (i < 299 && a[i] == 0 && a[i+1] == 0)
        consec_zero_violations++;
      $write("%0d ", a[i]);
      if ((i+1) % 20 == 0) $display("");
    end

    $display("\n=== Frequency Count ===");
    for (int v = 0; v < 6; v++)
      $display("  Value %0d : %0d times", v, count[v]);

    $display("=== Consecutive Zero Violations: %0d ===", consec_zero_violations);
    endfunction

    
    function new(string name="transaction");
       //TODO: Constructor
        super.new(name);
    endfunction
endclass


module tb_array;
    initial begin
        // TODO: Instantiate transaction
    transaction tr;
    tr = new("tr");

    if (!tr.randomize())
      $fatal(1, "Randomization FAILED!");
    else
      $display("Randomization PASSED!");

    tr.display();

    $finish;
  end
        // TODO: Randomize and display
endmodule
