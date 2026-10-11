// ============================================================================
// rot_matrix.sv
// N x N matrix A and its 90-degree CCW rotation B:  B[N-1-j][i] == A[i][j]
//
// Two implementation styles:
//   rot_matrix_c : A and B both rand, rotation enforced as a constraint
//                  (bidirectional -> you can constrain B and the solver
//                   back-solves A)
//   rot_matrix_p : only A rand, B derived procedurally in post_randomize
//                  (B is a state var -> cannot be constrained)
// ============================================================================
`include "uvm_macros.svh"

package rot_pkg;
  import uvm_pkg::*;

  // --------------------------------------------------------------------------
  // Common base: typedefs + checkers shared by both styles
  // --------------------------------------------------------------------------
  virtual class rot_base #(int N = 4, int W = 8) extends uvm_object;
    typedef bit [W-1:0] elem_t;
    typedef elem_t      mat_t [N][N];

    function new(string name = "rot_base");
      super.new(name);
    endfunction

    // Each style returns its A and B through this hook
    pure virtual function void get_ab(output mat_t a, output mat_t b);

    // TC1: B[N-1-j][i] == A[i][j] for all i,j
    function bit check_mapping();
      mat_t a, b;
      get_ab(a, b);
      foreach (a[i, j])
        if (b[N-1-j][i] !== a[i][j]) begin
          `uvm_error("ROT_MAP", $sformatf("%s: B[%0d][%0d]=%0d != A[%0d][%0d]=%0d",
                     get_name(), N-1-j, i, b[N-1-j][i], i, j, a[i][j]))
          return 0;
        end
      return 1;
    endfunction

    // TC3: flatten, sort, compare
    function bit check_multiset();
      mat_t  a, b;
      elem_t qa[$], qb[$];
      get_ab(a, b);
      foreach (a[i, j]) begin
        qa.push_back(a[i][j]);
        qb.push_back(b[i][j]);
      end
      qa.sort();
      qb.sort();
      if (qa != qb) begin
        `uvm_error("ROT_MSET", $sformatf("%s: multiset mismatch\n sorted A=%p\n sorted B=%p",
                   get_name(), qa, qb))
        return 0;
      end
      return 1;
    endfunction

    static function string mat2str(mat_t m);
      string s = "";
      for (int i = 0; i < N; i++) begin
        s = {s, "  "};
        for (int j = 0; j < N; j++) s = {s, $sformatf("%4d", m[i][j])};
        s = {s, "\n"};
      end
      return s;
    endfunction

    function string show();
      mat_t a, b;
      get_ab(a, b);
      return $sformatf("%s (N=%0d)\nA:\n%sB (CCW):\n%s", get_name(), N, mat2str(a), mat2str(b));
    endfunction
  endclass

  // --------------------------------------------------------------------------
  // Style 1: rotation as a constraint (both rand)
  // --------------------------------------------------------------------------
  class rot_matrix_c #(int N = 4, int W = 8) extends rot_base #(N, W);
    `uvm_object_param_utils(rot_matrix_c #(N, W))

    rand bit [W-1:0] A[N][N];
    rand bit [W-1:0] B[N][N];

    // No "c_a" needed: rand alone randomizes every element.
    // Add a value-shaping constraint here only if you want one, e.g.
    //   constraint c_a_range { foreach (A[i,j]) A[i][j] inside {[0:99]}; }

    constraint c_rot_ccw {
      foreach (A[i, j]) B[N-1-j][i] == A[i][j];
    }

    function new(string name = "rot_matrix_c");
      super.new(name);
    endfunction

    virtual function void get_ab(output mat_t a, output mat_t b);
      a = A;
      b = B;
    endfunction
  endclass

  // --------------------------------------------------------------------------
  // Style 2: B derived procedurally (only A rand)
  // --------------------------------------------------------------------------
  class rot_matrix_p #(int N = 4, int W = 8) extends rot_base #(N, W);
    `uvm_object_param_utils(rot_matrix_p #(N, W))

    rand bit [W-1:0] A[N][N];
         bit [W-1:0] B[N][N];   // NOT rand: solver never sees it

    function new(string name = "rot_matrix_p");
      super.new(name);
    endfunction

    function void post_randomize();
      super.post_randomize();
      foreach (A[i, j]) B[N-1-j][i] = A[i][j];
    endfunction

    virtual function void get_ab(output mat_t a, output mat_t b);
      a = A;
      b = B;
    endfunction
  endclass

  // --------------------------------------------------------------------------
  // Generic randomized test for any N: TC1 + TC3 + TC5 on both styles
  // --------------------------------------------------------------------------
  class rot_tests #(int N = 4, int W = 8);
    typedef rot_base #(N, W)::mat_t mat_t;

    static function void run(int iters = 20);
      rot_matrix_c #(N, W) mc = new($sformatf("mc_N%0d", N));
      rot_matrix_p #(N, W) mp = new($sformatf("mp_N%0d", N));
      mat_t prev_c, prev_p;
      int   changed_c = 0, changed_p = 0;

      for (int k = 0; k < iters; k++) begin
        if (!mc.randomize()) `uvm_fatal("RAND", {mc.get_name(), " randomize failed"})
        if (!mp.randomize()) `uvm_fatal("RAND", {mp.get_name(), " randomize failed"})

        void'(mc.check_mapping());   void'(mc.check_multiset());
        void'(mp.check_mapping());   void'(mp.check_multiset());

        // TC5: A actually changes between randomizations and B keeps tracking
        if (k > 0 && mc.A != prev_c) changed_c++;
        if (k > 0 && mp.A != prev_p) changed_p++;
        prev_c = mc.A;
        prev_p = mp.A;
      end

      // With N*N*W random bits, a repeated A is essentially impossible except N=1
      if (iters > 1 && (changed_c == 0 || changed_p == 0))
        `uvm_error("ROT_TC5", $sformatf("N=%0d: A never changed across %0d randomizations", N, iters))

      `uvm_info("ROT", $sformatf("N=%0d: %0d iters done, A changed %0d/%0d (constraint) %0d/%0d (procedural)",
                N, iters, changed_c, iters-1, changed_p, iters-1), UVM_LOW)
    endfunction
  endclass

endpackage


// ============================================================================
// Testbench
// ============================================================================
module tb_rot;
  import uvm_pkg::*;
  import rot_pkg::*;

  initial begin
    // ---------------- TC2: small sizes ----------------
    begin
      rot_matrix_c #(1) m1 = new("tc2_N1");
      rot_matrix_c #(2) m2 = new("tc2_N2");
      void'(m1.randomize());  void'(m1.check_mapping());  void'(m1.check_multiset());
      `uvm_info("TC2", m1.show(), UVM_LOW)
      void'(m2.randomize());  void'(m2.check_mapping());  void'(m2.check_multiset());
      `uvm_info("TC2", m2.show(), UVM_LOW)
      // Explicit N=2 hand check: A={{a,b},{c,d}} -> B={{b,d},{a,c}}
      if (!(m2.B[0][0] == m2.A[0][1] && m2.B[0][1] == m2.A[1][1] &&
            m2.B[1][0] == m2.A[0][0] && m2.B[1][1] == m2.A[1][0]))
        `uvm_error("TC2", "N=2 hand check failed")
    end

    // ---------------- TC4: N=3 known example ----------------
    begin
      typedef rot_base #(3)::mat_t mat3_t;
      rot_matrix_c #(3) m3  = new("tc4_N3");
      rot_matrix_p #(3) m3p = new("tc4_N3_proc");
      mat3_t exp_b = '{'{3,6,9}, '{2,5,8}, '{1,4,7}};

      // Pin A = {{1,2,3},{4,5,6},{7,8,9}}
      if (!m3.randomize() with { foreach (A[i,j]) A[i][j] == 3*i + j + 1; })
        `uvm_fatal("TC4", "randomize failed")
      `uvm_info("TC4", m3.show(), UVM_LOW)
      if (m3.B != exp_b) `uvm_error("TC4", "constraint style: B != expected")

      if (!m3p.randomize() with { foreach (A[i,j]) A[i][j] == 3*i + j + 1; })
        `uvm_fatal("TC4", "randomize failed")
      if (m3p.B != exp_b) `uvm_error("TC4", "procedural style: B != expected")

      // Reverse direction (constraint style only): pin B, solver back-solves A
      if (!m3.randomize() with { foreach (B[i,j]) B[i][j] == exp_b[i][j]; })
        `uvm_fatal("TC4", "reverse randomize failed")
      foreach (m3.A[i,j])
        if (m3.A[i][j] != 3*i + j + 1) `uvm_error("TC4", "reverse solve: wrong A")
      `uvm_info("TC4", "reverse solve (constrain B -> derive A) OK", UVM_LOW)
    end

    // ---------------- TC1 + TC3 + TC5 over a range of N ----------------
    rot_tests #(1)::run(10);
    rot_tests #(2)::run(20);
    rot_tests #(3)::run(20);
    rot_tests #(4)::run(20);
    rot_tests #(8)::run(20);
    rot_tests #(16, 16)::run(10);

    begin
      uvm_report_server rs = uvm_report_server::get_server();
      int errs = rs.get_severity_count(UVM_ERROR) + rs.get_severity_count(UVM_FATAL);
      $display("\n==== ROT MATRIX TESTS %s (%0d errors) ====", errs ? "FAILED" : "PASSED", errs);
    end
    $finish;
  end
endmodule
