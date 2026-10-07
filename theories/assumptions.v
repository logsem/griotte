From griotte Require
  fundamental
  cmdc_adequacy
  deep_locality_adequacy
  deep_immutability_adequacy
  lse_adequacy
  stack_object_adequacy
  vae_adequacy
  fundamental_binary
  cmdc_adequacy_binary
  stack_secret_adequacy_binary
  stack_callee_secret_adequacy_binary
  write_only_secret_adequacy_binary
.
(** Uncomment the following to print assumptions.  *)

(*
Goal True. idtac "
Assumptions of fundamental theorem:". Abort.
Print Assumptions fundamental.fundamental.

Goal True. idtac "
Assumptions of the compartmentalisation (CMDC) end-to-end theorem:". Abort.
Print Assumptions cmdc_adequacy.cmdc_adequacy.

Goal True. idtac "
Assumptions of the deep locality end-to-end theorem:". Abort.
Print Assumptions deep_locality_adequacy.dle_adequacy.

Goal True. idtac "
Assumptions of the deep immutability end-to-end theorem:". Abort.
Print Assumptions deep_immutability_adequacy.droe_adequacy.

Goal True. idtac "
Assumptions of the 'protection against dangling pointers' (LSE downward) end-to-end theorem:". Abort.
Print Assumptions lse_adequacy.lse_adequacy.

Goal True. idtac "
Assumptions of the 'stack object' end-to-end theorem:". Abort.
Print Assumptions stack_object_adequacy.so_adequacy.

Goal True. idtac "
Assumptions of Very Awkward Example (VAE) end-to-end theorem:". Abort.
Print Assumptions vae_adequacy.vae_adequacy.

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
