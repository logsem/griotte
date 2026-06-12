From cap_machine Require
  fundamental
  cmdc_adequacy
  deep_locality_adequacy
  deep_immutability_adequacy
  lse_adequacy
  stack_object_adequacy
  vae_adequacy
.

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
