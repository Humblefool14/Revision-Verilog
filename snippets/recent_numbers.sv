class A;
 typedef bit [9:0] number_t;
 rand number_t number;
 number_t recent_numbers[$];
 constraint uniq_recent { unique {number, recent_numbers}; }

 function void post_randomize;
   recent_numbers.push_front(number);
   if (recent_numbers.size() > 4)
      void'(recent_numbers.pop_back());
  endfunction
endclass
