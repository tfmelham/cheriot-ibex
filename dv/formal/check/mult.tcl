
source verify.tcl

set_engine_mode auto

stop

prove -property top.Mult_idle_ALBL
prove -property top.Mult_ALBL_ALBH
prove -property top.Mult_ALBH_AHBL

prove -property top.Mult_mult_en_i_stable
prove -property top.Mult_mult_operator_i_stable
prove -property top.Mult_op_a_stable ;# slow
prove -property top.Mult_op_b_stable ;# slow

prove -property top.Mult_MULL_signed_mode_i

# First cycle properties - WHp just gets them
prove -property top.Mult_ALBL -engine WHp
prove -property top.Mult_ALBL_signs -engine WHp

prove -property top.Mult_ALBH_imd_val_q_i ;# slow
prove -property top.Mult_AHBL_imd_val_q_i ;# slow

set_prove_orchestration off
set_proofmaster off
set_proofgrid_max_jobs 10
set_proofgrid_max_local_jobs 16
set_word_level_engine_flow on
set_engineWL_processes 16

# This proof of helper does not converge, even when the above lemmas are already proved
# ** 
# prove -with_proven -property top.Mult_ALBH_helper -engine {WHps WA1}

stop

# Converting the properties to assumptions makes the helper converge, fairly quickly
assume -from_assert top.Mult_idle_ALBL top.Mult_ALBL_ALBH -remove_original
assume -from_assert top.Mult_*_stable -remove_original
assume -from_assert top.Mult_MULL_signed_mode_i -remove_original
assume -from_assert top.Mult_ALBL top.Mult_ALBL_signs -remove_original
assume -from_assert top.Mult_ALBH_imd_val_q_i -remove_original
prove -property top.Mult_ALBH_helper -engine {WHps WA1}

# This proof of ALBH does not converge, when the lemmas as well as the helper are already proved
# This proof of ALBH also does not converge even when the lemmas are assumed.
prove -with_proven -property top.Mult_ALBH -engine {WHps WA1}

# Converting the helper to an assumpton makes ALBH converge, and quickly
assume -from_assert top.Mult_ALBH_helper -remove_original
prove -property top.Mult_ALBH -engine {WHps WA1}

# Proving the helper property for the third cycle.
assume -from_assert top.Mult_ALBL top.Mult_ALBL_signs -remove_original
prove -property top.Mult_AHBL_helper -engine {WHps WA1}

