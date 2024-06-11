module Arbiter #(
  parameter NumRequests = 4
) (
  input  logic [NumRequests-1:0] request,
  output logic [NumRequests-1:0] grant
);

  always_comb begin
    grant = '0;

    for (int i = 0; i < NumRequests; i++) begin
      if (request[i]) begin
        grant[i] = 1;
        break;
      end
    end
  end

endmodule