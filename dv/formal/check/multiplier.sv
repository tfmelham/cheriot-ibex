`define OP_L 15:0
`define OP_H 31:16

module multiplier #()(
  input  logic [31:0]      op_a_i,
  input  logic [31:0]      op_b_i,
  output logic [31:0]      result_o);

logic [15:0] mult_op_a1; // Line 260
logic [15:0] mult_op_b1; // Line 261

logic [15:0] mult_op_a2; // Line 260
logic [15:0] mult_op_b2; // Line 261

logic signed [34:0] mac_res_signed1;  // Line 51
logic        [34:0] mac_res_ext1;     // Line 52
logic        [33:0] accum1;           // Line 53

logic signed [34:0] mac_res_signed2;  // Line 51
logic        [34:0] mac_res_ext2;     // Line 52
logic        [33:0] accum2;           // Line 53

// Raw output of MAC calculation
logic [33:0] mac_res1; // Line 61
logic [33:0] mac_res2; // Line 61

// Signals that get written out as intermediate values.
logic [33:0] mac_res_d1; // Line 59
logic [33:0] mac_res_d2; // Line 59

// ****** ALBL calculation. Lines 290-298.
assign mult_op_a1    = op_a_i[`OP_L];  // Line 292
assign mult_op_b1    = op_b_i[`OP_L];  // Line 293
assign accum1        = '0; // Line 296

// Lines 272-274 - signs are set to zero at lines 294, 295
assign mac_res_signed1 = $signed({1'b0, mult_op_a1}) * $signed({1'b0, mult_op_b1}) + $signed(accum1);
assign mac_res_ext1    = $unsigned(mac_res_signed1);
assign mac_res1        = mac_res_ext1[33:0];

assign mac_res_d1      = mac_res1; // Line 297

Mult_ALBL: assert property (mac_res_d1[31:0] == (op_a_i[15:0] * op_b_i[15:0]));

// ****** ALBH calculation. Lines 301-316.
// We know op_a_i and op_b_i are stable, so we can unroll like this.
// We also know that imd_val_i[0] == $past(mac_res_d).
assign mult_op_a2    = op_a_i[`OP_L];  // Line 303
assign mult_op_b2    = op_b_i[`OP_H];  // Line 304
assign accum2        = {18'b0, mac_res_d1[31:16]};  // Line 308

// Lines 272-274 - second instance. Signs are either set to zero or depend on signed_mode_i[1], 
// which we know will be 2b'00.
assign mac_res_signed2 = $signed({1'b0, mult_op_a2}) * $signed({1'b0, mult_op_b2}) + $signed(accum2);
assign mac_res_ext2    = $unsigned(mac_res_signed2);
assign mac_res2        = mac_res_ext2[33:0];

assign mac_res_d2 = {2'b0, mac_res2[`OP_L], mac_res_d1[`OP_L]}; // Line 310

logic [63:0] albhspec; 
assign albhspec = $unsigned({16'b0, op_a_i[15:0]}) * $unsigned(op_b_i[31:0]);

Mult_ALBH: assert property (mac_res_d2[31:0] == albhspec[31:0]);

endmodule
