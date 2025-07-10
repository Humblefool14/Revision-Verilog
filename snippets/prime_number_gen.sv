class prime_num_gen; 

int number; 
int bitQ[$]
rand int divisorsQ[$]; 
static bit is_prime; 

function void pre_randomize(); 
  divisorsQ.delete(); 
  for(int j = 2; j <= number/2; j++)begin 
      divisorsQ.push_back(j); 
  end
  is_prime = 1; 
endfunction  

constraint bitq_c{
    bitQ.size() == divisorsQ.size(); 
}

constraint prime_gen{
    foreach(divisorsQ[i]){
        ((number % divisorsQ[i]) == 0 ) -> (bitQ[i] == 1); 
        ((number % divisorsQ[i]) != 0 ) -> (bitQ[i] == 0); 
    }
}

function void post_randomize(); 
   //for(int j=0; )
   // if prime_flag is all 1 , then it is a 1. 
   // if it's 0 even once, then it's a non prime. 
    
    //foreach(bitQ[i])begin 
    //    if(bitQ[i]==1) begin 
    //       is_prime = 0; 
    //        break; 
    //    end 
    //end 
    is_prime = ~(|bitQ); // or all elements. if it's 1 --> no prime and is_prime should be 0. 
    if(is_prime == 1) prime_q.push_back(number); 
    number++; 
endfunction

endclass 
