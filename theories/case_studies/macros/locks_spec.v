From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants na_invariants.
From griotte Require Import proofmode rules.
From griotte Require Import locks.

(** * The specifications of the lock library

    A lock is a word [ℓ] in an invariant of the critical-section pool: at
    [0] it holds the resource [R] of the lock. [try_lock] runs with
    interrupts disabled, so it holds the critical-section token across its
    test-and-set; the release is one store inside a borrow of the token. *)

Section lock_inv.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ}.

  Definition lock_inv (N : namespace) (ℓ : Addr) (R : iProp Σ) : iProp Σ :=
    na_inv crit N (∃ z : Z, ℓ ↦ₐ lword_of_word (WInt z) ∗ if decide (z = 0) then R else True).
  #[global] Instance lock_inv_persistent N ℓ R : Persistent (lock_inv N ℓ R).
  Proof. apply _. Qed.

  Lemma lock_inv_alloc E N ℓ R :
    ℓ ↦ₐ lword_of_word (WInt 0) -∗
    ▷ R
    ={E}=∗
    lock_inv N ℓ R.
  Proof.
    iIntros "Hl HR".
    iApply (na_inv_alloc crit E N with "[Hl HR]").
    iNext. iExists 0%Z. iFrame "Hl".
    destruct (decide (0%Z = 0)) as [_ | Hne]; [iExact "HR" | by destruct Hne].
  Qed.

  (** The release, inside one step with the critical-section token. *)
  Lemma lock_inv_release_acc E N ℓ R :
    ↑N ⊆ E →
    lock_inv N ℓ R -∗
    na_own crit ⊤
    ={E}=∗
    (∃ w, ℓ ↦ₐ w) ∗
    (ℓ ↦ₐ lword_of_word (WInt 0) -∗ ▷ R ={E}=∗ na_own crit ⊤).
  Proof.
    iIntros (HE) "#Hinv Hcrit".
    iMod (na_inv_acc with "Hinv Hcrit") as "(Hc & Hcrit & Hclose)"; [done | done |].
    (* The old content is dropped: the lock is held *)
    iDestruct "Hc" as (z) "[>Hl _]".
    iModIntro. iSplitL "Hl"; first by iExists _.
    iIntros "Hl HR".
    iApply ("Hclose" with "[$Hcrit Hl HR]").
    iNext. iExists 0%Z. iFrame "Hl".
    destruct (decide (0%Z = 0)) as [_ | Hne]; [iExact "HR" | by destruct Hne].
  Qed.
End lock_inv.

Section locks_spec.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} {th : Thread} `{MP : MachineParameters}
    {CL : ∀ t, CritLink Σ t} {CR : ∀ t, CritRoute Σ t (CL t)}
    {LK : locksLayout}.

  (** The code of the library, persistent and thread-free. *)
  Definition lock_static : iProp Σ :=
    ⌜ (b_locks + length locks_try_lock_instrs)%a = Some e_locks ⌝ ∗
    codefrag_pers b_locks locks_try_lock_instrs.
  #[global] Instance lock_static_persistent : Persistent lock_static.
  Proof. apply _. Qed.

  (** [try_lock] on a lock of the pool, entered at InterruptDisabled from a
      call through its sentry. *)
  Lemma try_lock_spec N (ℓ : Addr) (R : iProp Σ) (p : Perm) (g : Locality) (b e : Addr)
      (wret wct1 : LWord) :
    readAllowed p = true →
    writeAllowed p = true →
    withinBounds b e ℓ = true →
    is_shadow_address ℓ = false →
    jalr_target_ok cnull cra wret.(lw) = true →
    th ≠ CtxSwitch →
    lock_static ∗
    lock_inv N ℓ R ∗
    PC ↦ₚ[th] Cap RX Global b_locks e_locks b_locks ∗
    ct0 ↦ᵣ[th] Cap p g b e ℓ ∗
    ct1 ↦ᵣ[th] wct1 ∗
    cra ↦ᵣ[th] wret ∗
    MIE ↦ₜ[th] InterruptDisabled ∗
    held (th := th) (CL := CL th) (CR := CR th) InterruptDisabled ∗
    ▷ (PC ↦ₚ[th] lupdatePcPerm wret ∗
       ct1 ↦ᵣ[th] WInt 0 ∗
       cra ↦ᵣ[th] wret ∗
       MIE ↦ₜ[th] default InterruptDisabled (jalr_target_mie wret.(lw)) ∗
       held (th := th) (CL := CL th) (CR := CR th)
         (default InterruptDisabled (jalr_target_mie wret.(lw))) ∗
       ((ct0 ↦ᵣ[th] WInt 0 ∗ R) ∨ ct0 ↦ᵣ[th] WInt (-1)) -∗
       safe[th])
    ⊢ safe[th].
  Proof.
    iIntros (Hra Hwa Hbounds Hshadow Htgt Hth)
      "(#Hstatic & #Hinv & HPC & Hct0 & Hct1 & Hcra & HMIE & Hheld & Hpost)".
    iDestruct "Hstatic" as "[%Hsize Hcode]".
    (* The critical-section token, out of the posture; the lock's cell *)
    rewrite held_disabled. iDestruct "Hheld" as "[Hho Hpart]".
    iDestruct (handover_res_crit with "Hho") as "[Hcrit Hho]".
    iMod (na_inv_acc with "Hinv Hcrit") as "(Hlock & Hcrit & Hclose)"; [done | done |].
    iDestruct "Hlock" as (z) "[>Hl HR]".
    rewrite /locks_try_lock_instrs. codefrag_facts "Hcode".
    assert (SubBounds b_locks e_locks b_locks (b_locks ^+ length (encodeInstrsW locks_try_lock)))
      as Hsub by (rewrite /locks_try_lock_instrs in Hsize; solve_addr).
    (* CLoad ct1 ct0. *)
    iInstr "Hcode".
    { done. }
    { by split. }
    iEval (rewrite /lload_word /lift_word /= load_word_int) in "Hct1".
    destruct (decide (z = 0)) as [->|Hz].
    - (* Jne try_lock_busy ct1 0. *)
      iInstr "Hcode".
      (* Store ct0 1. *)
      iInstr "Hcode".
      iMod ("Hclose" with "[Hl $Hcrit]") as "Hcrit".
      { iNext. iExists 1%Z. by iFrame "Hl". }
      (* Mov ct0 0. *)
      iInstr "Hcode".
      iDestruct ("Hho" with "Hcrit") as "Hho".
      iAssert (held (th := th) (CL := CL th) (CR := CR th) InterruptDisabled)%I
        with "[Hho Hpart]" as "Hheld".
      { rewrite held_disabled. iFrame. }
      (* Jalr cnull cra. *)
      iInstr "Hcode".
      destruct (decide (ct0 = cnull)) as [Hct0_null | _]; first done.
      iApply "Hpost". iFrame "HPC Hct1 Hcra HMIE Hheld". iLeft. iFrame "Hct0 HR".
    - (* Jne try_lock_busy ct1 0. *)
      iInstr "Hcode".
      { rewrite /nonZero /=. by apply negb_true_iff, Z.eqb_neq. }
      iMod ("Hclose" with "[Hl $Hcrit]") as "Hcrit".
      { iNext. iExists z. iFrame "Hl".
        destruct (decide (z = 0)) as [Hz0 | _]; [by destruct Hz | done]. }
      (* Mov ct0 (-1). *)
      iInstr "Hcode".
      (* Mov ct1 0. *)
      iInstr "Hcode".
      iDestruct ("Hho" with "Hcrit") as "Hho".
      iAssert (held (th := th) (CL := CL th) (CR := CR th) InterruptDisabled)%I
        with "[Hho Hpart]" as "Hheld".
      { rewrite held_disabled. iFrame. }
      (* Jalr cnull cra. *)
      iInstr "Hcode".
      iApply "Hpost". iFrame "HPC Hct1 Hcra HMIE Hheld". iRight. iFrame "Hct0".
  Qed.
End locks_spec.
