
source verify.tcl

set_engine_mode auto

# Properties of the internal state machine.
prove -property top.Mult_idle_ALBL
prove -property top.Mult_ALBL_ALBH
prove -property top.Mult_ALBH_AHBL
prove -property top.Mult_ALBH_ALBL

# Stability of the important inputs to the module.
prove -property top.Mult_mult_en_i_stable
prove -property top.Mult_mult_operator_i_stable
prove -property top.Mult_op_a_i_stable  ;# a bit slow. Assuming en_i stable helps a bit
prove -property top.Mult_op_b_i_stable  ;# a bit slow. Assuming en_i stable helps a bit

# Constant inputs during a MULL instruction.
prove -property top.Mult_MULL_signed_mode_i
prove -property top.Mult_MULL_div_sel_i

# These used to get exponentially slower, but are better now for some reason.
prove -property top.Mult_ALBH_imd_val_q_i  ;# 21.2 without en_i_stable assume
prove -property top.Mult_AHBL_imd_val_q_i  ;# 15.4
prove -property top.Mult_AHBH_imd_val_q_i  ;# 14.7

# We now have all the top-level interface properties we need, so this module can be isolated from the surrounding code.
stopat `MULT.mult_en_i `MULT.operator_i `MULT.op_a_i `MULT.op_b_i `MULT.signed_mode_i `MULT.div_sel_i {`MULT.imd_val_q_i[0]}

# Recommended settings for word-level engines
set_proofmaster off             ;# machine learning - is off by default
set_proofgrid_max_jobs 21       
set_proofgrid_max_local_jobs 21
set_word_level_engine_flow on
set_engineWL_processes 21

# First cycle properties - WHp just gets them. 
prove -orchestration off -engine WHp -property top.Mult_ALBL        ;# 12.6
prove -orchestration off -engine Whp -property top.Mult_ALBL_ext    ;# 4.7

# This proof of helper does not converge, even when the above lemmas are already proved
# # prove -with_proven -property top.Mult_ALBH_helper -engine {WHps WA1}

# Converting the cycle 1 correctness properties to assumptions makes the helper converge, fairly quickly
# * 16.5 with the cycle 1 correctness properties
# 
assume -from_assert top.Mult_ALBL top.Mult_ALBL_ext
prove -orchestration off -property top.Mult_ALBH_helper -engine {WHps WA1}

# This direct proof of ALBH does not converge, even when the lemmas are assumed.
# prove -with_proven -property top.Mult_ALBH -engine {WHps WA1}

# Converting the input and state lemmas AND the helper to assumptions makes ALBH converge, and quickly
# The auto engine mode works just fine for this.
assume -from_assert top.Mult_ALBL_ALBH 
# assume -from_assert top.Mult_mult_en_i_stable
assume -from_assert top.Mult_op_*_i_stable top.Mult_mult_operator_i_stable
assume -from_assert top.Mult_MULL_signed_mode_i 
assume -from_assert top.Mult_MULL_div_sel_i 
assume -from_assert top.Mult_ALBH_imd_val_q_i 
assume -from_assert top.Mult_ALBH_helper 
prove -property top.Mult_ALBH -engine auto
prove -property top.Mult_ALBH_ext -engine auto

stop

# Proving the helper property for the third cycle.
assume -from_assert top.Mult_AHBL_imd_val_q_i 
assume -from_assert top.Mult_ALBH top.Mult_ALBH_ext    
prove -orchestration off -property top.Mult_AHBL_helper -engine {WHps WA1}  ;# 24873.20

# This top-level property proves with Hp and all helpers
assume -from_assert top.Mult_AHBL_helper
prove -property top.Mult_AHBL -engine auto

# 
# prove -property top.Mult_ID_AHBL -engine {WHps WA1}

# task -edit Step12 -copy {top.Mult_AHBL}
# assume -from_assert {top.Mult_ID_AHBL}
# prove -property {Step12::top.MType_Mul_Data} -engine {WA1 WHps}
# prove -property {Step12::top.MType_Mul_Data} -sst
# prove -property {Step12::top.MType_Mul_Data} -engine {WI}
