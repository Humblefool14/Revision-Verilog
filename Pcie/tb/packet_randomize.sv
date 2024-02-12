typedef enum {low, mid, high} AddrType;

class SList; 
rand int n;
rand Slist next;
constraint sort { if( next != null ) n < next.n; }
endclass 

class Bus;
  rand bit[15:0] addr; 
  rand bit[31:0] data;
  constraint word_align {addr[1:0] == 2'b0;} 
endclass

class MyBus extends Bus; 
rand AddrType atype; constraint addr_range {
  (atype == low ) -> addr inside { [0 : 15] }; 
  (atype == mid ) -> addr inside { [16 : 127]}; 
  (atype == high) -> addr inside {[128 : 255]};
}
endclass

module rand_methods;
  initial begin
    Bus bus = new(); 
    repeat (50) begin 
      if(bus.randomize() == 1)
       $display("Addr : 0x%x, Data : 0x%x",bus.addr,bus.data); 
       else
        $display("Randomization failed \n"); 
   end
  end 
endmodule 

task excercise_bus(MyBus bus); 
  int res = 1; 
  res = bus.randomize with {atype == low;}; 
  res = bus.randomize with {atype == mid;}; 
endtask 