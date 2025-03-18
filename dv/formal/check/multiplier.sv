`define OP_L 15:0
`define OP_H 31:16

module multiplier #()(
  input  logic [31:0]      op_a_i,
  input  logic [31:0]      op_b_i,
  output logic [31:0]      result_o);

logic [15:0] mult_op_a1;
logic [15:0] mult_op_b1;

logic [15:0] mult_op_a2;
logic [15:0] mult_op_b2;

logic signed [34:0] mac_res_signed1;
logic        [34:0] mac_res_ext1;
logic        [33:0] accum1;

logic signed [34:0] mac_res_signed2;
logic        [34:0] mac_res_ext2;
logic        [33:0] accum2;

// Raw output of MAC calculation
logic [33:0] mac_res1;
logic [33:0] mac_res2;

// Values that get written out as intermediate
logic [33:0] mac_res_d1;
logic [33:0] mac_res_d2;

assign mult_op_a1    = op_a_i[`OP_L];  // Line 292
assign mult_op_b1    = op_b_i[`OP_L];  // Line 293
assign accum1        = '0; // Line 296

// Lines 272-274 unrolled
assign mac_res_signed1 = $signed({1'b0, mult_op_a1}) * $signed({1'b0, mult_op_b1}) + $signed(accum1);
assign mac_res_ext1    = $unsigned(mac_res_signed1);
assign mac_res1        = mac_res_ext1[33:0];

assign mac_res_d1      = mac_res1; // Line 297

Mult_ALBL: assert property (mac_res_d1[31:0] == (op_a_i[15:0] * op_b_i[15:0]));

assign mult_op_a2    = op_a_i[`OP_L];  // Line 303
assign mult_op_b2    = op_b_i[`OP_H];  // Line 304
assign accum2        = {18'b0, mac_res_d1[31:16]};  // Line 308

// Lines 272-274 unrolled
assign mac_res_signed2 = $signed({1'b0, mult_op_a2}) * $signed({1'b0, mult_op_b2}) + $signed(accum2);
assign mac_res_ext2    = $unsigned(mac_res_signed2);
assign mac_res2        = mac_res_ext2[33:0];

assign mac_res_d2 = {2'b0, mac_res2[`OP_L], mac_res_d1[`OP_L]}; // Line 310

logic [63:0] albhspec; 
assign albhspec = $unsigned({16'b0, op_a_i[15:0]}) * $unsigned(op_b_i[31:0]);

Mult_ALBH: assert property (mac_res_d2[31:0] == albhspec[31:0]);

endmodule
