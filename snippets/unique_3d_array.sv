class transaction extends uvm_sequence_item;

  `uvm_object_utils(transaction)

  // 3D array
  rand bit [7:0] a[3][3][3];

  // Flattened helper array
  rand bit [7:0] flat[27];

  // ---------------------------
  // Constraints
  // ---------------------------
  constraint c_flat_unique {

    // Domain (256 values ≥ 27 required)
    foreach (flat[i])
      flat[i] inside {[0:255]};

    // All values unique
    unique {flat};

    // Map flat -> 3D
    foreach (a[i,j,k])
      a[i][j][k] == flat[i*9 + j*3 + k];
  }
endclass 
