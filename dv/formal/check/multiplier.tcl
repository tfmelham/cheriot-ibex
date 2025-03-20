clear -all

analyze -sv12 check/multiplier.sv
elaborate -top multiplier -disable_auto_bbox
clock -none
reset -none

set_proofgrid_max_local_jobs 15
set_word_level_engine_flow on
set_engineWL_processes 15

stop

prove -property multiplier.Mult_ALBL -engine WHp
prove -property multiplier.Mult_ALBH -engine WHp