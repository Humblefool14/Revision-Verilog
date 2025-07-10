class SList;
  rand int n;
  rand Slist next;
  constraint sort { if( next != null ) n < next.n; }
endclass
