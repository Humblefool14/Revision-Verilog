class soft_unique; 
  rand intA[9:0]
  rand a; 
  extern constraint soft_unique; 
endclass 

constraint soft_unique{
  foreach(intA[i]){
    intA[i] inside [10:100];
  }
    a inside [10:100]; 
  soft unique(intA, a); // both of them will be unique variable now. 
}

function void post_randomize(); 
  intA[0] = a; 
  intA[1] = a;
  intA[2] = a;
  intA.shuffle(); 
endfunction 
