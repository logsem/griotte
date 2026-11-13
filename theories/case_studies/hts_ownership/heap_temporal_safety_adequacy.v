From iris.proofmode Require Import proofmode.
From griotte Require Import image firmware firmware_ok firmware_adequacy.
From griotte.case_studies.hts_ownership Require Import hts_firmware.
From griotte Require Import hw_lang logrel seal_registry.
From griotte.allocators.ownership Require Import allocator_owners.
From griotte Require Export heap_temporal_safety_adequacy_obligations.

(** We initialise concretely the compartments name typeclass: the
    adversary and the scheduler. *)

Inductive CmptNames_hts := | B | Sched.
#[local] Instance CmptNames_hts_eq_dec : EqDecision CmptNames_hts.
Proof. intros C1 C2; destruct C1, C2; solve_decision. Qed.
#[local] Instance CmptNames_hts_finite : finite.Finite CmptNames_hts.
Proof.
  refine {| finite.enum := [B; Sched] |}.
  + constructor; [ by rewrite list_elem_of_singleton | apply NoDup_singleton ].
  + intros [|]; [ left | right; left ].
Defined.

#[local] Program Instance CmptNames_hts_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_hts; |}.

(** The logical compartments of the adversary and of the scheduler. *)
Definition hts_adv_B : @CmptName CmptNames_hts_CmptNameG := B.
Definition hts_sched : @CmptName CmptNames_hts_CmptNameG := Sched.

(* The fields of the image records, for the end-to-end statement. *)
Import image.

(** END-TO-END THEOREM. The scheduler starts with no interrupt-enabling
    sentry: [firmware_ok_sched_no_enabling]. *)
Theorem hts_adequacy `{MP : MachineParameters} (flag : Addr) (σ σ' : ExecConf)
    (es : list (language.expr griotte_hw_lang)) :
  hts_initial_state_ok flag σ →
  rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], σ) (es, σ') →
  mem σ' !! flag = Some (WInt 0).
Proof.
  intros Hok Hstep.
  destruct (hts_initial_state_ok_start _ _ Hok)
    as (sw & assert & assert_flag & t0 & idle & boot & main & allocator & B & sched & ot_alloc
        & <- & Hfw).
  eapply (firmware_adequacy_closed (Cname := CmptNames_hts_CmptNameG)
            #[allocator_ownerΣ; @seal_registryΣ CmptNames_hts_CmptNameG LAddr _ _]
            (hts_firmware ot_alloc)
            (hts_img sw assert assert_flag t0 idle boot main allocator B sched));
    [| exact Hfw | exact Hstep].
  apply (hts_fw_obligations (B := hts_adv_B) (Sched := hts_sched)); done.
Qed.
