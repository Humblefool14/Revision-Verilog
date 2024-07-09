class ahb_packet extends uvm_object;
  `uvm_object_utils(ahb_packet)

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

  `uvm_object_utils_begin(ahb_packet)
    `uvm_field_enum(ahb_trans_type_t, trans_type, UVM_ALL_ON)
    `uvm_field_int(address, UVM_ALL_ON)
    `uvm_field_int(data, UVM_ALL_ON)
    `uvm_field_int(burst_length, UVM_ALL_ON)
    `uvm_field_int(burst_size, UVM_ALL_ON)
    `uvm_field_int(burst_type, UVM_ALL_ON)
    `uvm_field_int(prot, UVM_ALL_ON)
  `uvm_object_utils_end
  
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

  function void pre_randomize(); 
  endfunction

  function void post_randomize(); 
  endfunction 

  // Constructor
  function new(string name = "ahb_packet");
    super.new(name);
  endfunction

  // Convert to string method (replaces print method)
  virtual function string convert2string();
    return $sformatf("AHB Packet:\n  Transaction Type: %s\n  Address: 0x%0h\n  Data: 0x%0h\n  Burst Length: %0d\n  Burst Size: %0d\n  Burst Type: %0d\n  Protection: 0x%0h",
      trans_type.name(), address, data, burst_length, burst_size, burst_type, prot);
  endfunction

  // do_copy method
  virtual function void do_copy(uvm_object rhs);
    ahb_packet rhs_cast;
    super.do_copy(rhs);
    $cast(rhs_cast, rhs);
    this.trans_type = rhs_cast.trans_type;
    this.address = rhs_cast.address;
    this.data = rhs_cast.data;
    this.burst_length = rhs_cast.burst_length;
    this.burst_size = rhs_cast.burst_size;
    this.burst_type = rhs_cast.burst_type;
    this.prot = rhs_cast.prot;
  endfunction

  // do_compare method
  virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
    ahb_packet rhs_cast;
    if (!$cast(rhs_cast, rhs)) return 0;
    return (super.do_compare(rhs, comparer) &&
            this.trans_type == rhs_cast.trans_type &&
            this.address == rhs_cast.address &&
            this.data == rhs_cast.data &&
            this.burst_length == rhs_cast.burst_length &&
            this.burst_size == rhs_cast.burst_size &&
            this.burst_type == rhs_cast.burst_type &&
            this.prot == rhs_cast.prot);
  endfunction

  // Pack and unpack methods
  virtual function void do_pack(uvm_packer packer);
    super.do_pack(packer);
    `uvm_pack_enum(trans_type)
    `uvm_pack_int(address)
    `uvm_pack_int(data)
    `uvm_pack_int(burst_length)
    `uvm_pack_int(burst_size)
    `uvm_pack_int(burst_type)
    `uvm_pack_int(prot)
  endfunction

  virtual function void do_unpack(uvm_packer packer);
    super.do_unpack(packer);
    `uvm_unpack_enum(trans_type, ahb_trans_type_t)
    `uvm_unpack_int(address)
    `uvm_unpack_int(data)
    `uvm_unpack_int(burst_length)
    `uvm_unpack_int(burst_size)
    `uvm_unpack_int(burst_type)
    `uvm_unpack_int(prot)
  endfunction
endclass