module count_demo;
  int arr[] = '{1, 2, 2, 3, 3, 4};
  int uniq[$];
  int freq[int];   // associative array: value -> count

  initial begin
    // 1. Total number of elements
    $display("Total count    = %0d", arr.size());          // 6

    // 2. Number of distinct values
    uniq = arr.unique();
    $display("Distinct count = %0d", uniq.size());         // 4

    // 3. Frequency of each value
    foreach (arr[i]) freq[arr[i]]++;
    foreach (freq[k]) $display("%0d occurs %0d time(s)", k, freq[k]);
    // freq.num() also gives the distinct count (4)

    // Count of one specific value, e.g. 2
    $display("Count of 2     = %0d", arr.sum() with (int'(item == 2)));  // 2
  end
endmodule
