
source verify.tcl

set_engine_mode auto

prove -property top.Mult_idle_ALBL
prove -property top.Mult_ALBL_ALBH
prove -property top.Mult_ALBH_AHBL

prove -property top.Mult_mult_en_i_stable
prove -property top.Mult_mult_operator_i_stable
prove -property top.Mult_op_a_stable 
prove -property top.Mult_op_b_stable

prove -property top.Mult_MULL_signed_mode_i

set_proofgrid_max_local_jobs 15
set_word_level_engine_flow on
set_engineWL_processes 15

# 15244620 microseconds per iteration, with proven
# 13333638 microseconds per iteration, without proven!
prove -property top.Mult_ALBL -engine WHp
prove -property top.Mult_ALBL_signs -engine WHp

prove -property top.Mult_ALBH_imd_val_q_i

set_engine_mode {WHp WHt WI WAM K C I N}

stop

prove -with_proven -property top.Mult_ALBH

