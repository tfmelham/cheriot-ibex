// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0 (see LICENSE for details).
// Original Author: Tom Melham
// SPDX-License-Identifier: Apache-2.0

/* This file defines signals used to state propertiues of some intermediate results in the multiplier.
The multiplier breaks 32 bit multiplication into four 76-bit multiplications, the extra bit being a sign bit added to handle signed intgegers.
The basic algorithm corresponds to pencil-and-paper block-multiplication:
  
   Let {AH[15:0], AL[15:0]} and {AB[15:0], BL[15:0]} be our two 32-bit operands. Then, in essence,

   {BH,BL} x {AH,AL} = (AL*BL) + (AL*BH)<<16 + (AH*BL)<<16 + (AH*BH)<<32 

The calculation is distributed over 3 (for MUL) or 4 (for MULH, MULHU, MULHSU) clock cycles, using only one 17 bit multiplier. 
*/

// ---------------------------------------------------------------------
// First cycle, calculation of AL*BL.
// ---------------------------------------------------------------------

logic [63:0] alxblspec; 
assign alxblspec = $signed({1'b0, `MULT.op_a_i[15:0]}) * $signed({1'b0,`MULT.op_b_i[15:0]});

// ---------------------------------------------------------------------
// Second stage, calculation of (AL*BL) + (AL*BH)<<16 + (AH*BL)<<16 
//
// The result mac_res_d[31:0] = {((AL*BH) + (AL*BL)[31:16])[15:0], (AL*BL)[15:0])}.
// This should equal (AL*{BH,BL})[31:0]
// ---------------------------------------------------------------------

logic [63:0] alxbspec; 
assign alxbspec = $signed({18'b0, `MULT.op_a_i[15:0]}) * $signed({2'b00,`MULT.op_b_i[31:0]});

// ---------------------------------------------------------------------
// Third stage, calculation of (AH*BH)<<32 + (AL*BH)<<16 + (AH*BL)<<16
// ---------------------------------------------------------------------

// Simple specification 
logic [63:0] ahxbspec; 
assign ahxbspec = $signed({18'b0,`MULT.op_a_i[31:16]}) * $signed({2'b00,`MULT.op_b_i[31:0]});

// Top-level multiplication. In the case of MUL, the Sail spec has the operands as signed.
logic [63:0] axbspec;
assign axbspec = $signed(`MULT.op_a_i[31:0]) * $signed(`MULT.op_b_i[31:0]);
