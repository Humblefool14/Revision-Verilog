class packet;
  rand int array[];
  constraint s{array.size==20;}
  constraint b { array.sum() with (int'(item==5)) == 3; }
  constraint c { array.sum() with (int'(item==10)) == 5; }
  constraint d { array.sum() with (int'(item==15)) == 8; }
  constraint e { array.sum() with (int'(item==20)) == 4; }
endclass



module tb;
  packet h;
  initial 
    begin 
      h=new();
      assert(h.randomize);
      $display("array=%p",h);
      end
endmodule
