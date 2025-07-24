class my_class;

  rand int a;
  rand int b;

  constraint a_b_c{
    a > b;
  }

  function new();
  endfunction
  
  function void pre_randomize();
    if ($value$plusargs("VALUE_A=%0d", a)) a.rand_mode(0);
    if ($value$plusargs("VALUE_B=%0d", b)) b.rand_mode(0);
  endfunction
  
  function void display();
    $display("a is: %0d  b is %0d", a, b);
  endfunction
 
endclass

class top;
  my_class m1;
  
  function new();
    m1 = new();
  endfunction
