From griotte Require
  fundamental_binary
  cmdc_adequacy_binary
  stack_secret_adequacy_binary
  stack_callee_secret_adequacy_binary
  write_only_secret_adequacy_binary
.
(** Uncomment the following to print assumptions.  *)

(*
Goal True. idtac "
Assumptions of the binary fundamental theorem:". Abort.
Print Assumptions fundamental_binary.fundamental.

Goal True. idtac "
Assumptions of the compartmentalisation (CMDC) confidentiality end-to-end theorem:". Abort.
Print Assumptions cmdc_adequacy_binary.cmdc_conf_adequacy.

Goal True. idtac "
Assumptions of the stack confidentiality end-to-end theorem:". Abort.
Print Assumptions stack_secret_adequacy_binary.stack_secret_adequacy.

Goal True. idtac "
Assumptions of the trusted-callee stack confidentiality end-to-end theorem:". Abort.
Print Assumptions stack_callee_secret_adequacy_binary.stack_callee_secret_adequacy.

Goal True. idtac "
Assumptions of the write-only sharing confidentiality end-to-end theorem:". Abort.
Print Assumptions write_only_secret_adequacy_binary.write_only_secret_adequacy.
*)
