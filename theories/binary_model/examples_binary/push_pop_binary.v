From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel stack_macros_helpers.
From cap_machine Require Export iris_extra addr_reg_sample contiguous.
From cap_machine Require Import macros.
From cap_machine.binary_model.rules_binary Require Import rules_binary rules_binary_StoreU_derived.

(** This file contains specification side specs for macros.
    The file contains pushz, rclear and prepstack (for now, only the macros needed by example)
 *)

Ltac iPrologue_s prog :=
  (try iPrologue_pre);
  iDestruct prog as "[Hi Hprog]".

Ltac iEpilogue_s :=
   iMod (do_step_pure _ [] with "[$Hspec $Hj]") as "Hj";auto;
   iSimpl in "Hj".

Section macros.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ} {cfg : cfgSG Σ}
          `{MP: MachineParameters}.

  (* --------------------------------------------------------------------------------- *)
  (* --------------------------------------- PUSH ------------------------------------ *)
  (* --------------------------------------------------------------------------------- *)

  Definition pushU_z_s a1 r_stk z : iProp Σ := (a1 ↣ₐ pushU_z_instr r_stk z)%I.

  Lemma pushU_z_spec E a1 a2 w z p g b e stk_b stk_e stk_a stk_a' :
    isCorrectPC (inr ((p,g),b,e,a1)) →
    withinBounds ((URWLX,Directed),stk_b,stk_e,stk_a) = true →
    (a1 + 1)%a = Some a2 →
    (stk_a + 1)%a = Some stk_a' →
    nclose specN ⊆ E →

    spec_ctx
    ∗ ⤇ Seq (Instr Executable)
    ∗ ▷ pushU_z_s a1 r_stk z
    ∗ ▷ PC ↣ᵣ inr ((p,g),b,e,a1)
    ∗ ▷ r_stk ↣ᵣ inr ((URWLX,Directed),stk_b,stk_e,stk_a)
    ∗ ▷ stk_a ↣ₐ w
    ={E}=∗ ⤇ Seq (Instr Executable)
         ∗ PC ↣ᵣ inr ((p,g),b,e,a2) ∗ pushU_z_s a1 r_stk z ∗
         r_stk ↣ᵣ inr ((URWLX,Directed),stk_b,stk_e,stk_a') ∗ stk_a ↣ₐ inl z.
  Proof.
    iIntros (Hvpc1 Hwb Hsuc Hstk Hnclose)
            "(#Hspec & Hj & Ha1 & HPC & Hr_stk & Hstk_a')".
    iMod (step_storeU_success_0_z _ [SeqCtx] with "[$Hspec $Hj $HPC $Ha1 $Hr_stk $Hstk_a']")
      as "(Hj & HPC & Ha1 & Hr_stk & Hstk_a)";
      [apply decode_encode_instrW_inv|eauto..].
    iEpilogue_s.
    iFrame. done.
  Qed.

End macros.
