class magicsquare;
  
  parameter int N = 4;
 
  rand bit [7:0] a [N][N];
  
  constraint c1 {
    foreach(a[i,j]) {
      a[i].sum(row) with (int'(row)) == 15; // rows
      a.sum(row) with (row.sum(col) with (col.index == j  ? int'(col) : 0))== 15; // cols
    }
    a.sum(row) with (row.sum(col) with (row.index==col.index ? int'(col) : 0 )) == 15; // diag1
    a.sum(row) with (row.sum(col) with (($size(a)-row.index-1)==col.index ? int'(col) : 0)) == 15; // diag2
  }
 
  function void display ();
    $display ("The value of array is");
    foreach(a[i]) $display("%p = ",a[i], a[i].sum(row) with (int'(row)));
    foreach(a[,j]) $write("%3d ",a.sum(row) with (row.sum(col) with (col.index == j  ? int'(col) : 0)));
    $display("\ndiag1 = ", a.sum(row) with (row.sum(col) with (row.index==col.index ? int'(col) : 0)));
    $display("diag2 = ",  a.sum(row) with (row.sum(col) with (($size(a)-row.index-1)==col.index ? int'(col) : 0)));
  endfunction
 
endclass
 
module test;
  magicsquare m1;
 
  initial begin
    m1=new();
    repeat(10) begin
      assert (m1.randomize());
       m1.display();
    end 
    m1.display();
  end
endmodule
/*
Meaning of row.index and col.index
In expressions like:
a.sum(row) with (row.sum(col) with (row.index == col.index ? int'(col) : 0))
Let’s go step-by-step.

➤ a.sum(row) with (...)
Here, a is the 2D array. So row will iterate over each element in the first dimension (i.e., each row a[0], a[1], etc.). Each row is itself a 1D array (a[i]).

row is a 1D array, each time one of the a[i] rows.
row.index is the current index i of that row (same as the row number in a[i]).
row = a[i], so row.index == i.

➤ row.sum(col) with (...)
Now, for that particular row (say, a[i]), col iterates over each of its elements (a[i][j]).

col is the actual data value: a[i][j]
col.index is the index j into the row a[i].

This helps express constraints that depend on positions:
Main diagonal is where i == j → row.index == col.index
Anti-diagonal is where i + j == N - 1 → row.index + col.index == N - 1

a.sum(row) with (row.sum(col) with (row.index==col.index ? int'(col) : 0 )) == 15;
This says:
For all rows:
For all elements in that row:
If the row index == column index (i.e., diagonal element), add it
Sum up all such elements → they should equal 15
That’s a constraint for the main diagonal (a[0][0] + a[1][1] + a[2][2] + a[3][3])
*/ 
