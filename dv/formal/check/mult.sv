// Copyright lowRISC contributors.
// Copyright 2024 University of Oxford, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0 (see LICENSE for details).
// Original Author: Tom Melham
// SPDX-License-Identifier: Apache-2.0

// The multiplier breaks 32 bit multiplication into four 76-bit multiplications, the extra bit being a sign bit added to handle signed intgegers.
// The basic algorithm corresponds to pencil-and-paper block-multiplication:
//
//     Let {AH[15:0], AL[15:0]} and {AB[15:0], BL[15:0]} be our two 32-bit operands. Then, in essence,
//
//     {BH,BL} x {AH,AL} = (AL*BL) + (AL*BH)<<16 + (AH*BL)<<16 + (AH*BH)<<32 
//
// The calculation is distributed over 3 (for MUL) or 4 (for MULH, MULHU, MULHSU) clock cycles, using only one 17 bit multiplier. 

// State machine forward progress: ALBL -> ALBH -> AHBL
// Mult_idle_ALBL: assert property (~`MULT.mult_en_i |-> `MULTG.mult_state_q == `MULTG.ALBL);
// Mult_ALBL_ALBH: assert property (`MULT.mult_en_i && `MULTG.mult_state_q == `MULTG.ALBL |=> `MULTG.mult_state_q == `MULTG.ALBH);
// Mult_ALBH_AHBL: assert property (`MULT.mult_en_i && `MULTG.mult_state_q == `MULTG.ALBH |=> `MULTG.mult_state_q == `MULTG.AHBL);

// Mult_ALBH_AHBL: assert property (`MULT.mult_en_i && `MULTG.mult_state_q == `MULTG.ALBH |=> `MULTG.mult_state_q == `MULTG.AHBL);
// Mult_ALBH_ALBL: assert property (`MULT.mult_en_i && `MULTG.mult_state_q == `MULTG.ALBH |-> $past(`MULTG.mult_state_q) == `MULTG.ALBL);

// Inputs are stable during the multiplication
// Mult_mult_en_i_stable: assert property (`MULT.mult_en_i && `MULTG.mult_state_q == `MULTG.ALBL |=> $stable(`MULT.mult_en_i)[*2]);
// Mult_mult_operator_i_stable: assert property (`MULT.mult_en_i && `MULTG.mult_state_q == `MULTG.ALBL |=> $stable(`MULT.operator_i)[*2]);
// Mult_op_a_i_stable: assert property (`MULT.mult_en_i && `MULTG.mult_state_q == `MULTG.ALBL |=> $stable(`MULT.op_a_i)[*2]); 
// Mult_op_b_i_stable: assert property (`MULT.mult_en_i && `MULTG.mult_state_q == `MULTG.ALBL |=> $stable(`MULT.op_b_i)[*2]); 

// Mult_mult_en_i_past: assert property  (`MULT.mult_en_i && `MULTG.mult_state_q == `MULTG.ALBH |-> $past(`MULT.mult_en_i));

// Constant input: when doing a MUL, the product is an unsigned multiplication
// MULL_signed_mode_i: assert property (`MULT.operator_i == MD_OP_MULL && `MULT.mult_en_i |-> `MULT.signed_mode_i == 2'b00);
// MULL_div_sel_i: assert property (`MULT.operator_i == MD_OP_MULL && `MULT.mult_en_i |-> `MULT.div_sel_i == 1'b0);

// The results calculated in the first two cycles and sent to an external intermediate value register comes back for the next cycle
// Mult_ALBH_imd_val_q_i: assert property (`MULT.mult_en_i && `MULTG.mult_state_q == `MULTG.ALBH |-> `MULT.imd_val_q_i[0] == $past(`MULT.mac_res_d));  // slow
// Mult_AHBL_imd_val_q_i: assert property (`MULT.mult_en_i && `MULTG.mult_state_q == `MULTG.AHBL |-> `MULT.imd_val_q_i[0] == $past(`MULT.mac_res_d));  // slow

// ---------------------------------------------------------------------
// First cycle, calculation of AL*BL.
// ---------------------------------------------------------------------

// Mult_ALBL: assert property (`MULT.mult_en_i && `MULTG.mult_state_q == `MULTG.ALBL |-> `MULT.imd_val_d_o[0][31:0] == alxblspec[31:0]);
// Mult_ALBL_ext: assert property (`MULT.mult_en_i && `MULTG.mult_state_q == `MULTG.ALBL |-> `MULT.imd_val_d_o[0][33:32] == 2'b00);

// ---------------------------------------------------------------------
// Second stage, calculation of (AL*BL) + (AL*BH)<<16 + (AH*BL)<<16 
//
// The result mac_res_d[31:0] = {((AL*BH) + (AL*BL)[31:16])[15:0], (AL*BL)[15:0])}.
// This should equal (AL*{BH,BL})[31:0]
// ---------------------------------------------------------------------

// ALBH property with helper constraints in the entecedent
// Mult_ALBH_helper: assert property (`MULT.operator_i == MD_OP_MULL && `MULT.mult_en_i && (`MULTG.mult_state_q == `MULTG.ALBL) 
                                 //    ##1 
                                 //   `MULT.operator_i == MD_OP_MULL && `MULT.mult_en_i && (`MULTG.mult_state_q == `MULTG.ALBH) && 
                                 //   `MULT.op_a_i == $past(`MULT.op_a_i) && `MULT.op_b_i == $past(`MULT.op_b_i) && 
                                 //   `MULT.signed_mode_i == 2'b00 && 
                                 //   `MULT.div_sel_i == 1'b0 &&
                                 //   `MULT.imd_val_q_i[0] == $past(`MULT.imd_val_d_o[0])
                                 //   |-> 
                                 //   `MULT.mac_res_d[31:0] == $past(alxbspec[31:0]));

// Mult_ALBH: assert property (`MULT.operator_i == MD_OP_MULL && `MULT.mult_en_i && (`MULTG.mult_state_q == `MULTG.ALBL) 
                              //   |=> 
                              //   `MULT.mac_res_d[31:0] == $past(alxbspec[31:0]));


// Mult_ALBH_ext: assert property (`MULT.operator_i == MD_OP_MULL && `MULT.mult_en_i && `MULTG.mult_state_q == `MULTG.ALBH |-> `MULT.mac_res_d[33:32] == 2'b00);

// ---------------------------------------------------------------------
// Third stage, calculation of (AH*BH)<<32 + (AL*BH)<<16 + (AH*BL)<<16
// ---------------------------------------------------------------------

// AHBL property with helper constraints in the entecedent
Mult_AHBL_helper: assert property (`MULT.operator_i == MD_OP_MULL && `MULT.mult_en_i && (`MULTG.mult_state_q == `MULTG.ALBL) 
                                    ##1 
                                   `MULT.operator_i == MD_OP_MULL && `MULT.mult_en_i && (`MULTG.mult_state_q == `MULTG.ALBH) && 
                                   `MULT.op_a_i == $past(`MULT.op_a_i) && `MULT.op_b_i == $past(`MULT.op_b_i) && 
                                   `MULT.signed_mode_i == 2'b00 && 
                                   `MULT.div_sel_i == 1'b0 &&
                                   `MULT.imd_val_q_i[0] == $past(`MULT.imd_val_d_o[0])
                                    ##1
                                   `MULT.operator_i == MD_OP_MULL && `MULT.mult_en_i && (`MULTG.mult_state_q == `MULTG.AHBL) && 
                                   `MULT.op_a_i == $past(`MULT.op_a_i,2) && `MULT.op_b_i == $past(`MULT.op_b_i,2) && 
                                   `MULT.signed_mode_i == 2'b00 && 
                                   `MULT.div_sel_i == 1'b0 &&
                                   `MULT.imd_val_q_i[0] == $past(`MULT.imd_val_d_o[0])
                                   |-> 
//                                  `MULT.mac_res_d[31:0] == $past(alxbspec[31:0],2) + {$past(ahxbspec[15:0],2),16'b0});
                                    `MULT.multdiv_result_o[31:0] == $past(axbspec[31:0],2));

Mult_AHBL: assert property (`MULT.operator_i == MD_OP_MULL && `MULT.mult_en_i && (`MULTG.mult_state_q == `MULTG.ALBL) 
                             |-> ##(2)
 //                         `MULT.mac_res_d[31:0] == $past(alxbspec[31:0]) + {$past(ahxbspec[15:0]),16'b0});
                            `MULT.multdiv_result_o[31:0] == $past(axbspec[31:0],2));

// Mult_ID_AHBL: assert property (`MULT.operator_i == MD_OP_MULL && `MULT.mult_en_i && (`MULTG.mult_state_q == `MULTG.ALBL) 
//                                  |-> ##2
//                               `MULT.mac_res_d[31:0] == $signed($past(`ID.multdiv_operand_a_ex_o,2)) * $signed($past(`ID.multdiv_operand_b_ex_o,2)));
                                     
// MType_Mul_Data2: assert property (`IS_MUL && finishing_executed & ~wbexc_illegal && `ID.multdiv_ready_i |-> data_match);
