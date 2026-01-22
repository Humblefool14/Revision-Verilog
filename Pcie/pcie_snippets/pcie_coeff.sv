// PCIe Gen 4 - 3-tap equalization (C-1, C0, C+1)

// Check if FS = |C-1| + C0 + |C+1|
function automatic check_coeff_sum_gen4 (
  input [5:0] fs, 
  input [5:0] c_minus_1, 
  input [5:0] c0, 
  input [5:0] c_plus_1
);
  reg [6:0] sum;
begin
  sum = {1'b0, c_minus_1} + {1'b0, c0} + {1'b0, c_plus_1};
  check_coeff_sum_gen4 = (sum == {1'b0, fs}) ? 1'b1 : 1'b0;
end
endfunction

// Check if LF <= (C0 - |C-1| - |C+1|)
function automatic check_coeff_diff_gen4 (
  input [5:0] lf, 
  input [5:0] c_minus_1, 
  input [5:0] c0, 
  input [5:0] c_plus_1
);
  reg [6:0] diff;
begin
  diff = {1'b0, c0} - {1'b0, c_minus_1} - {1'b0, c_plus_1};
  check_coeff_diff_gen4 = (diff >= {1'b0, lf}) ? 1'b1 : 1'b0;
end
endfunction

// Check if |C-1| <= Floor(FS/4)
function automatic check_precursor_gen4 (
  input [5:0] fs, 
  input [5:0] c_minus_1
);
begin
  check_precursor_gen4 = (c_minus_1 <= {2'b0, fs[5:2]}) ? 1'b1 : 1'b0;
end
endfunction

// Calculate C0 from FS = |C-1| + C0 + |C+1|
// Therefore: C0 = FS - |C-1| - |C+1|
function automatic [5:0] calc_c0_gen4 (
  input [5:0] fs,
  input [5:0] c_minus_1,
  input [5:0] c_plus_1
);
  reg [6:0] temp;
begin
  temp = {1'b0, fs} - {1'b0, c_minus_1} - {1'b0, c_plus_1};
  calc_c0_gen4 = temp[5:0];
end
endfunction

// Calculate next coefficient
function automatic [6:0] calc_next_coeff_gen4 (
  input [1:0] dirchg, 
  input [5:0] coeff
);
begin
  calc_next_coeff_gen4 = (dirchg == 2'b01) ? {1'b0, coeff} + 1'b1 :
                         (dirchg == 2'b10) ? {1'b0, coeff} - 1'b1 :
                                             {1'b0, coeff};
end
endfunction


// PCIe 64GT - 3-tap equalization (C-2 ,C-1, C0, C+1)
// Check if FS = |C-1| + |C-2| + C0 + |C+1|
function automatic check_coeff_sum (
  input [5:0] fs, 
  input [5:0] c_minus_1, 
  input [5:0] c_minus_2, 
  input [5:0] c0, 
  input [5:0] c_plus_1
);
  reg [6:0] sum;
begin
  sum = {1'b0, c_minus_1} + {1'b0, c_minus_2} + {1'b0, c0} + {1'b0, c_plus_1};
  check_coeff_sum = (sum == {1'b0, fs}) ? 1'b1 : 1'b0;
end
endfunction

// Check if LF <= (C0 - |C-1| + |C-2| - |C+1|)
function automatic check_coeff_diff (
  input [5:0] lf, 
  input [5:0] c_minus_1, 
  input [5:0] c_minus_2, 
  input [5:0] c0, 
  input [5:0] c_plus_1
);
  reg [6:0] diff;
begin
  diff = {1'b0, c0} - {1'b0, c_minus_1} + {1'b0, c_minus_2} - {1'b0, c_plus_1};
  check_coeff_diff = (diff >= {1'b0, lf}) ? 1'b1 : 1'b0;
end
endfunction

// Check if |C-1| <= FS/4 and |C-2| <= FS/8
function automatic check_precursor (
  input [5:0] fs, 
  input [5:0] c_minus_1, 
  input [5:0] c_minus_2
);
begin
  check_precursor = (c_minus_1 <= {2'b0, fs[5:2]}) && (c_minus_2 <= {3'b0, fs[5:3]}) ? 1'b1 : 1'b0;
end
endfunction

// Calculate next coefficient
function automatic [6:0] calc_next_coeff (
  input [1:0] dirchg, 
  input [5:0] coeff
);
begin
  calc_next_coeff = (dirchg == 2'b01) ? {1'b0, coeff} + 1'b1 :
                    (dirchg == 2'b10) ? {1'b0, coeff} - 1'b1 :
                                        {1'b0, coeff};
end
endfunction

// Calculate C0 from FS = |C-1| + |C-2| + C0 + |C+1|
// Therefore: C0 = FS - |C-1| - |C-2| - |C+1|
function automatic [5:0] calc_c0 (
  input [5:0] fs,
  input [5:0] c_minus_1,
  input [5:0] c_minus_2,
  input [5:0] c_plus_1
);
  reg [6:0] temp;
begin
  temp = {1'b0, fs} - {1'b0, c_minus_1} - {1'b0, c_minus_2} - {1'b0, c_plus_1};
  calc_c0 = temp[5:0];
end
endfunction
