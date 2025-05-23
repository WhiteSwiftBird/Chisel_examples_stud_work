// Generated by CIRCT firtool-1.114.1
module Reg_test(
  input        clock,
               reset,
  input  [3:0] io_a,
               io_b,
  output [9:0] io_res
);

  reg [3:0] regb;
  reg [4:0] regsum;
  reg [9:0] res_reg;
  always @(posedge clock) begin
    if (reset) begin
      regb <= 4'h0;
      regsum <= 5'h0;
      res_reg <= 10'h0;
    end
    else begin
      regb <= io_b;
      regsum <= {1'h0, io_a} + {1'h0, io_b};
      res_reg <= {4'h0, {1'h0, regsum} + {2'h0, regb}};
    end
  end // always @(posedge)
  assign io_res = res_reg;
endmodule

