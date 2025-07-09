function int count_ones ( bit [9:0] w );
for(count_ones = 0; w != 0; w = w >> 1 )
    count_ones += w & 1'b1;
endfunction

constraint C1 { length == count_ones( v ) ; }

The function name count_ones itself becomes an implicit return variable of type int.
What happens:

count_ones = 0 - This initializes the function's return value to 0
count_ones += w & 1'b1 - This increments the function's return value
No explicit return statement needed - The value of count_ones is automatically returned
