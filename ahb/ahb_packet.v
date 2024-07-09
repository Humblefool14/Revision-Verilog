class ahb_packet;
  // Transaction type
  typedef enum {READ, WRITE, IDLE} ahb_trans_type_t;

  // Packet fields
  rand ahb_trans_type_t trans_type;
  rand bit [31:0] address;
  rand bit [31:0] data;
  rand int burst_length;
  rand bit [2:0] burst_size;
  rand bit [2:0] burst_type;
  rand bit [3:0] prot;
  
  // Constraints
  constraint c_burst_length {
    burst_length inside {1, 4, 8, 16};
  }
  
  constraint c_burst_size {
    burst_size inside {[0:2]}; // 8-bit, 16-bit, 32-bit
  }
  
  constraint c_burst_type {
    burst_type inside {0, 1, 2, 3}; // SINGLE, INCR, WRAP4, INCR4
  }
  
  constraint c_address_alignment {
    address[1:0] == 0; // 32-bit aligned addresses
  }

  // Constructor
  function new();
    // Initialize with default values if needed
  endfunction

  // Method to print packet details
  function void print();
    $display("AHB Packet:");
    $display("  Transaction Type: %s", trans_type.name());
    $display("  Address: 0x%0h", address);
    $display("  Data: 0x%0h", data);
    $display("  Burst Length: %0d", burst_length);
    $display("  Burst Size: %0d", burst_size);
    $display("  Burst Type: %0d", burst_type);
    $display("  Protection: 0x%0h", prot);
  endfunction

  // Method to pack the transaction into a bit stream
  function bit [127:0] pack();
    bit [127:0] packed_data;
    packed_data[1:0]   = trans_type;
    packed_data[33:2]  = address;
    packed_data[65:34] = data;
    packed_data[73:66] = burst_length;
    packed_data[76:74] = burst_size;
    packed_data[79:77] = burst_type;
    packed_data[83:80] = prot;
    return packed_data;
  endfunction

  // Method to unpack a bit stream into the transaction
  function void unpack(bit [127:0] packed_data);
    trans_type   = ahb_trans_type_t'(packed_data[1:0]);
    address      = packed_data[33:2];
    data         = packed_data[65:34];
    burst_length = packed_data[73:66];
    burst_size   = packed_data[76:74];
    burst_type   = packed_data[79:77];
    prot         = packed_data[83:80];
  endfunction
endclass