From griotte Require
  fundamental
  kvs_adequacy
  cmdc_adequacy
  deep_locality_adequacy
  deep_immutability_adequacy
  lse_adequacy
  stack_object_adequacy
  vae_adequacy
  heap_temporal_safety_adequacy
.
From griotte Require Import
  machine_base griotte_opsem switcher assert allocator_resources compartment_layout
  kvs kvs_main cmdc deep_locality deep_immutability lse stack_object vae.
(* Imported last: the fields of the image records. *)
From griotte Require Import
  image firmware firmware_ok print
  kvs_firmware cmdc_firmware dle_firmware droe_firmware lse_firmware so_firmware vae_firmware
  hts_firmware
  kvs_concrete cmdc_concrete deep_locality_concrete deep_immutability_concrete lse_concrete
  stack_object_concrete vae_concrete heap_temporal_safety_concrete.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

(** * The audited statements

    Per case study: the assumptions of its end-to-end theorem, its
    initial-state predicate and the memory map of its concrete demo image.

    The initial-state predicate is what the end-to-end theorem assumes of
    the initial state. [Print <cs>_initial_state_ok] is the reference; the
    annotated form [<cs>_initial_state_ok_annot], printed after it, states
    the same conditions with headings and comments as reading aids. The files
    [docs/firmware-image/<cs>_print.txt] are snapshots of these prints.

    Uncomment the following to print them. *)

(*
Goal True. idtac "
Assumptions of fundamental theorem:". Abort.
Print Assumptions fundamental.fundamental.
*)

(** ** Key-value store (KVS) *)

(*
Goal True. idtac "
Assumptions of the key-value store (KVS) end-to-end theorem:". Abort.
Print Assumptions kvs_adequacy.kvs_adequacy.

Print kvs_initial_state_ok.

Section kvs_initial_state.
  Import FwPrintNotations.
  Import (notations) Stdlib.Strings.String.
  Open Scope string_scope.
  Open Scope OType_scope.
  Open Scope Addr_scope.
  Ltac2 Eval print_initial_state constr:(@kvs_initial_state_ok_annot).
End kvs_initial_state.

Section kvs_memory_map.
  Import FwMapNotations.
  Open Scope string_scope.
  Open Scope Z_scope.
  Ltac2 Eval print_memory_map constr:(kvs_demo_image).
End kvs_memory_map.
*)

(** ** Compartmentalisation (CMDC) *)

(*
Goal True. idtac "
Assumptions of the compartmentalisation (CMDC) end-to-end theorem:". Abort.
Print Assumptions cmdc_adequacy.cmdc_adequacy.

Print cmdc_initial_state_ok.

Section cmdc_initial_state.
  Import FwPrintNotations.
  Import (notations) Stdlib.Strings.String.
  Open Scope string_scope.
  Open Scope OType_scope.
  Open Scope Addr_scope.
  Ltac2 Eval print_initial_state constr:(@cmdc_initial_state_ok_annot).
End cmdc_initial_state.

Section cmdc_memory_map.
  Import FwMapNotations.
  Open Scope string_scope.
  Open Scope Z_scope.
  Ltac2 Eval print_memory_map constr:(cmdc_demo_image).
End cmdc_memory_map.
*)

(** ** Deep locality *)

(*
Goal True. idtac "
Assumptions of the deep locality end-to-end theorem:". Abort.
Print Assumptions deep_locality_adequacy.dle_adequacy.

Print dle_initial_state_ok.

Section dle_initial_state.
  Import FwPrintNotations.
  Import (notations) Stdlib.Strings.String.
  Open Scope string_scope.
  Open Scope OType_scope.
  Open Scope Addr_scope.
  Ltac2 Eval print_initial_state constr:(@dle_initial_state_ok_annot).
End dle_initial_state.

Section dle_memory_map.
  Import FwMapNotations.
  Open Scope string_scope.
  Open Scope Z_scope.
  Ltac2 Eval print_memory_map constr:(dle_demo_image).
End dle_memory_map.
*)

(** ** Deep immutability *)

(*
Goal True. idtac "
Assumptions of the deep immutability end-to-end theorem:". Abort.
Print Assumptions deep_immutability_adequacy.droe_adequacy.

Print droe_initial_state_ok.

Section droe_initial_state.
  Import FwPrintNotations.
  Import (notations) Stdlib.Strings.String.
  Open Scope string_scope.
  Open Scope OType_scope.
  Open Scope Addr_scope.
  Ltac2 Eval print_initial_state constr:(@droe_initial_state_ok_annot).
End droe_initial_state.

Section droe_memory_map.
  Import FwMapNotations.
  Open Scope string_scope.
  Open Scope Z_scope.
  Ltac2 Eval print_memory_map constr:(droe_demo_image).
End droe_memory_map.
*)

(** ** Protection against dangling pointers (LSE downward) *)

(*
Goal True. idtac "
Assumptions of the 'protection against dangling pointers' (LSE downward) end-to-end theorem:". Abort.
Print Assumptions lse_adequacy.lse_adequacy.

Print lse_initial_state_ok.

Section lse_initial_state.
  Import FwPrintNotations.
  Import (notations) Stdlib.Strings.String.
  Open Scope string_scope.
  Open Scope OType_scope.
  Open Scope Addr_scope.
  Ltac2 Eval print_initial_state constr:(@lse_initial_state_ok_annot).
End lse_initial_state.

Section lse_memory_map.
  Import FwMapNotations.
  Open Scope string_scope.
  Open Scope Z_scope.
  Ltac2 Eval print_memory_map constr:(lse_demo_image).
End lse_memory_map.
*)

(** ** Stack object *)

(*
Goal True. idtac "
Assumptions of the 'stack object' end-to-end theorem:". Abort.
Print Assumptions stack_object_adequacy.so_adequacy.

Print so_initial_state_ok.

Section so_initial_state.
  Import FwPrintNotations.
  Import (notations) Stdlib.Strings.String.
  Open Scope string_scope.
  Open Scope OType_scope.
  Open Scope Addr_scope.
  Ltac2 Eval print_initial_state constr:(@so_initial_state_ok_annot).
End so_initial_state.

Section so_memory_map.
  Import FwMapNotations.
  Open Scope string_scope.
  Open Scope Z_scope.
  Ltac2 Eval print_memory_map constr:(so_demo_image).
End so_memory_map.
*)

(** ** Very Awkward Example (VAE) *)

(*
Goal True. idtac "
Assumptions of Very Awkward Example (VAE) end-to-end theorem:". Abort.
Print Assumptions vae_adequacy.vae_adequacy.

Print vae_initial_state_ok.

Section vae_initial_state.
  Import FwPrintNotations.
  Import (notations) Stdlib.Strings.String.
  Open Scope string_scope.
  Open Scope OType_scope.
  Open Scope Addr_scope.
  Ltac2 Eval print_initial_state constr:(@vae_initial_state_ok_annot).
End vae_initial_state.

Section vae_memory_map.
  Import FwMapNotations.
  Open Scope string_scope.
  Open Scope Z_scope.
  Ltac2 Eval print_memory_map constr:(vae_demo_image).
End vae_memory_map.
*)

(** ** Heap temporal safety (HTS) *)

(*
Goal True. idtac "
Assumptions of the 'heap temporal safety' end-to-end theorem:". Abort.
Print Assumptions heap_temporal_safety_adequacy.hts_adequacy.

Print hts_initial_state_ok.

Section hts_initial_state.
  Import heap_temporal_safety allocator allocator_common_code.
  Import FwPrintNotations.
  Import (notations) Stdlib.Strings.String.
  Open Scope string_scope.
  Open Scope OType_scope.
  Open Scope Addr_scope.
  Ltac2 Eval print_initial_state constr:(@hts_initial_state_ok_annot).
End hts_initial_state.

Section hts_memory_map.
  Import FwMapNotations.
  Open Scope string_scope.
  Open Scope Z_scope.
  Ltac2 Eval print_memory_map constr:(hts_demo_image).
End hts_memory_map.
*)
