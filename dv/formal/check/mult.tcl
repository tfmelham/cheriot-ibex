
source verify.tcl

set_engine_mode auto

prove -property top.Mult_idle_ALBL
prove -property top.Mult_ALBL_ALBH
prove -property top.Mult_ALBH_AHBL

prove -property top.Mult_mult_en_i_stable
prove -property top.Mult_mult_operator_i_stable
prove -property top.Mult_op_a_stable ;# slow
prove -property top.Mult_op_b_stable ;# slow

prove -property top.Mult_MULL_signed_mode_i

prove -property top.Mult_ALBH_imd_val_q_i ;# slow
prove -property top.Mult_AHBL_imd_val_q_i ;# slow

# Recommended settings for word-level engines
set_prove_orchestration off
set_proofmaster off
set_proofgrid_max_jobs 16
set_proofgrid_max_local_jobs 16
set_word_level_engine_flow on
set_engineWL_processes 16

# First cycle properties - WHp just gets them
prove -property top.Mult_ALBL -engine WHp
prove -property top.Mult_ALBL_signs -engine WHp

# This proof of helper does not converge, even when the above lemmas are already proved
# prove -with_proven -property top.Mult_ALBH_helper -engine {WHps WA1}

# Converting the cycle 1 correctness properties to assumptions makes the helper converge, fairly quickly
# 265.9 with only the helper
# 59.4 with the lemmas as well
assume -from_assert top.Mult_idle_ALBL top.Mult_ALBL_ALBH 
assume -from_assert top.Mult_*_stable 
assume -from_assert top.Mult_MULL_signed_mode_i 
assume -from_assert top.Mult_ALBH_imd_val_q_i 
assume -from_assert top.Mult_ALBL top.Mult_ALBL_signs
prove -property top.Mult_ALBH_helper -engine {WHps WA1}

# This proof of ALBH does not converge, when the lemmas as well as the helper are already proved
# This proof of ALBH also does not converge even when the lemmas are assumed.
# prove -with_proven -property top.Mult_ALBH -engine {WHps WA1}

# Converting the helper and lemmas to assumptons makes ALBH converge, and quickly
# The auto engine mode works just fine for this.

assume -from_assert top.Mult_ALBH_helper 
prove -property top.Mult_ALBH -engine auto

prove -property top.Mult_ALBH_signs -engine WHp

# Proving the helper property for the third cycle.
assume -from_assert top.Mult_ALBH top.Mult_ALBH_signs
prove -property top.Mult_AHBL_helper -engine {WHps WA1}

stop

# Need some word level reasoning here. This is pretty slow.
assume -from_assert top.Mult_ALBH_AHBL
assume -from_assert top.Mult_AHBL_imd_val_q_i
assume -from_assert top.Mult_AHBL_helper
prove -property top.Mult_AHBL -engine {WHps WA1}

