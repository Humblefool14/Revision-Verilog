always@(a,b)
  begin 
    sum = a+b;
    sub = a-b;
    prod = a*b;
  end 

// An edge sensitive event control at the very beginning of an 
// always procedural block is typically referred to as 
// the sensitivity list for that procedural block
