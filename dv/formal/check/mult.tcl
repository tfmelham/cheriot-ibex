
source verify.tcl

set_engine_mode auto

# prove -property top.Mult_idle_ALBL
# prove -property top.Mult_ALBL_ALBH
# prove -property top.Mult_ALBH_AHBL

# prove -property top.Mult_mult_en_i_stable
# prove -property top.Mult_mult_operator_i_stable

# assume -from_assert top.Mult_mult_en_i_stable ;# speeds up the below
# prove -property top.Mult_op_a_i_stable
# prove -property top.Mult_op_b_i_stable

# prove -property top.Mult_MULL_signed_mode_i

# prove -property top.Mult_ALBH_imd_val_q_i
# prove -property top.Mult_AHBL_imd_val_q_i

# Recommended settings for word-level engines
# set_prove_orchestration off     ;# orchestration does not play nicely with the word-level engines
# set_proofmaster off             ;# machine learning - is off by default
# set_proofgrid_max_jobs 21       
# set_proofgrid_max_local_jobs 21
set_word_level_engine_flow on
set_engineWL_processes 21

# First cycle properties - WHp just gets them
# prove -orchestration off -property top.Mult_ALBL -engine WHp
# prove -property top.Mult_ALBL_ext -engine WHp

# This proof of helper does not converge, even when the above lemmas are already proved
# # prove -with_proven -property top.Mult_ALBH_helper -engine {WHps WA1}

# Converting the cycle 1 correctness properties to assumptions makes the helper converge, fairly quickly
# 265.9 with only the helper
# 59.4 with the lemmas as well
# assume -from_assert top.Mult_idle_ALBL top.Mult_ALBL_ALBH 
# assume -from_assert top.Mult_op_*_i_stable top.Mult_mult_operator_i_stable
# assume -from_assert top.Mult_MULL_signed_mode_i 
# assume -from_assert top.Mult_ALBH_imd_val_q_i 
# assume -from_assert top.Mult_ALBL top.Mult_ALBL_ext - not needed?
# prove -property top.Mult_ALBH_helper -engine {WHps WA1}

# This proof of ALBH does not converge, when the lemmas as well as the helper are already proved
# This proof of ALBH also does not converge even when the lemmas are assumed.
# # prove -with_proven -property top.Mult_ALBH -engine {WHps WA1}

# Converting the lemmas AND the helper to assumptons makes ALBH converge, and quickly
# The auto engine mode works just fine for this.
# assume -from_assert top.Mult_ALBH_helper 
# prove -property top.Mult_ALBH -engine auto
# prove -property top.Mult_ALBH_ext -engine auto

# Proving the helper property for the third cycle.
#
# Proof timing:
#   - WHps+WA1 with no helpers proved or assumed: 78.8 sec
#   - WHps+WA1 but with helpers previously proved and -with_proven: 90.1 sec 
#   - WHps+WA1 with (unproved) helpers converted to assumptions: 78.8 sec
#   - auto engine mode with (unproved) helpers converted to assumptions
# prove -property top.Mult_AHBL_helper -engine auto
prove -property top.Mult_AHBL_helper -engine {WHps WA1}

# This top-level property proves with Hp and all helpers
set_word_level_engine_flow off
prove -property top.Mult_AHBL -engine Hp

# assume -from_assert top.Mult_AHBL
# prove -property top.Mult_ID_AHBL -engine {WHps WA1}

task -edit Step12 -copy {top.Mult_ID_AHBL}
assume -from_assert {top.Mult_ID_AHBL}
# prove -property {Step12::top.MType_Mul_Data} -engine {WA1 WHps}
# prove -property {Step12::top.MType_Mul_Data} -sst
# prove -property {Step12::top.MType_Mul_Data} -engine {WI}
