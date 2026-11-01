From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import iprop base_logic.
From griotte Require Export erasure.
From griotte Require Import resources.

(** * The link of the critical sections

    The state interpretation of a thread is completed by a link [crit_link]:
    the part that depends on the interrupt status and on mtdc. A step that
    keeps MIE and the physical mtdc keeps the link. The link is per thread:
    the core link is [True] ([link_core]); the switcher's link
    ([crit_link_full]) holds the thread's [handover_res] at
    InterruptEnabled. *)

(** MIE of a configuration (InterruptDisabled if mstatus is absent). *)
Definition mie_st (σ : ExecConf) : InterruptStatus :=
  match sreg σ !! mstatus with Some w => mie_of (get_a w) | None => InterruptDisabled end.

(** MPIE of a configuration (InterruptDisabled if mstatus is absent). *)
Definition mpie_st (σ : ExecConf) : InterruptStatus :=
  match sreg σ !! mstatus with Some w => mpie_of (get_a w) | None => InterruptDisabled end.

Lemma mstatus_ok_mie_st σ mie mpie : mstatus_ok σ mie mpie → mie_st σ = mie.
Proof. rewrite /mstatus_ok /mie_st. intros ->. apply mie_of_mstatus_enc. Qed.

Lemma mstatus_ok_mpie_st σ mie mpie : mstatus_ok σ mie mpie → mpie_st σ = mpie.
Proof. rewrite /mstatus_ok /mpie_st. intros ->. apply mpie_of_mstatus_enc. Qed.

Class CritLink Σ (th : Thread) := {
  crit_link : ExecConf → iProp Σ;
  crit_link_stable σ σ' :
    mie_st σ = mie_st σ' → sreg σ !! mtdc = sreg σ' !! mtdc →
    crit_link σ ⊢ crit_link σ';
}.
#[export] Hint Mode CritLink + - : typeclass_instances.

(** The core link [True]. Not a global instance: a section without a
    [CritLink] binder that needs it imports [core_link], which declares it
    with a low priority (a [CritLink] binder still takes precedence). *)
Definition link_core {Σ} {th : Thread} : CritLink Σ th :=
  {| crit_link _ := True%I; crit_link_stable _ _ _ _ := reflexivity _ |}.

Module core_link.
  #[export] Existing Instance link_core | 1000.
End core_link.

(** A step that keeps MIE and the physical mtdc. *)
Definition sys_kept (σ σ' : ExecConf) : Prop :=
  mie_st σ' = mie_st σ ∧ sreg σ' !! mtdc = sreg σ !! mtdc.

Lemma sys_kept_refl σ : sys_kept σ σ.
Proof. done. Qed.

Lemma sys_kept_trans σ1 σ2 σ3 : sys_kept σ1 σ2 → sys_kept σ2 σ3 → sys_kept σ1 σ3.
Proof. intros [H1 H2] [H3 H4]. split; congruence. Qed.

Lemma sys_kept_same_sreg σ σ' : sreg σ' = sreg σ → sys_kept σ σ'.
Proof. rewrite /sys_kept /mie_st. by intros ->. Qed.

(** A write to a system register other than MTDC and mstatus. *)
Lemma sys_kept_insert_sreg (pc : Word) (r : Reg) (sr : SReg) m st x w :
  x ≠ mtdc → x ≠ mstatus → sys_kept (pc, r, sr, m, st) (pc, r, <[x := w]> sr, m, st).
Proof. intros H1 H2. rewrite /sys_kept /mie_st /=. by rewrite !lookup_insert_ne. Qed.

(** The link-transfer premise of a step that may change MIE or mtdc: [P]
    relates the states before and after the step; [T1] is given up and [T2]
    obtained with the link. *)
Definition link_transfer {Σ} {th : Thread} `{!CritLink Σ th} (P : ExecConf → ExecConf → Prop)
    (T1 T2 : iProp Σ) : Prop :=
  ∀ σ σ', P σ σ' → crit_link σ ∗ T1 ⊢ |==> crit_link σ' ∗ T2.

(** At the core link, it holds with [True]. *)
Lemma link_transfer_core {Σ} {th : Thread} P : @link_transfer Σ th link_core P True True.
Proof. iIntros (σ σ' _) "_". done. Qed.

(** The relation of the MIE writers: MIE goes from [b] to [b'], mtdc is
    unchanged. The mtdc writers keep MIE. *)
Definition mie_move (b b' : InterruptStatus) (σ σ' : ExecConf) : Prop :=
  mie_st σ = b ∧ mie_st σ' = b' ∧ sreg σ' !! mtdc = sreg σ !! mtdc.
Definition mtdc_written (σ σ' : ExecConf) : Prop := mie_st σ' = mie_st σ.

(** The relations of the writers are closed under a following step that
    keeps MIE and mtdc. *)
Lemma mie_move_kept b b' σ0 σ1 σ' : mie_move b b' σ0 σ1 → sys_kept σ1 σ' → mie_move b b' σ0 σ'.
Proof. intros (H1 & H2 & H3) [Hk1 Hk2]. split_and!; congruence. Qed.

Lemma mtdc_written_kept σ0 σ1 σ' : mtdc_written σ0 σ1 → sys_kept σ1 σ' → mtdc_written σ0 σ'.
Proof. rewrite /mtdc_written. intros H1 [Hk1 _]. congruence. Qed.
