module tb;

int array[5] = '{1,2,3,4,5};
int sum;

initial begin 
foreach(array[i]) begin
    $display("array[%0d] =%0d",i,array[i]);
  end 
foreach(array[i]) begin
    sum = sum+ array[i];
    $display("sum = %0d","array[%0d]=%0d",sum,i,array[i]);
 end 
 
 
