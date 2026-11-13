From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic Require Import invariants na_invariants.
From griotte Require Import resources posture region_maps world_ghost_theory.

(** * The flag of the thread-synchronisation case study

    [K]'s global [flag] lives in an invariant of the critical-section pool.
    While it holds [0], nothing else is in it. The thread that sets it to
    [1] puts in it the map of the Permanent regions of [B] and the relation
    of the region of [b]; the thread that waits for it takes them out and leaves its
    token instead. The invariant names no thread: both threads open it. *)

Definition Nflag : namespace := nroot .@ "tsy" .@ "flag".

Section tsy_flag.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} {Cname : CmptNameG} {relg : relGS Σ}.

  (** The token of the waiting thread. *)
  Definition tsy_tok (γ : gname) : iProp Σ := own γ (Excl () : exclR unitO).

  (** What the flag hands over: the map of the Permanent regions of [C],
      and the region of [b] in it, whose predicate holds of every integer. *)
  Definition tsy_handed (C : CmptName) (b : Addr) : iProp Σ :=
    perm_region_map C ∅ ∗
    ∃ φ : CmptName * LWord → iProp Σ,
      ⌜∀ Cv, Persistent (φ Cv)⌝ ∗
      LNonHeap b ↪ᵖ[C]{RW} φ ∗
      □ (∀ z : Z, φ (C, lword_of_word (WInt z))).

  Definition tsy_flag_inv (γ : gname) (C : CmptName) (flag b : Addr) : iProp Σ :=
    flag ↦ₐ lword_of_word (WInt 0) ∨
    (flag ↦ₐ lword_of_word (WInt 1) ∗ (tsy_handed C b ∨ tsy_tok γ)).

  Definition tsy_flag (γ : gname) (C : CmptName) (flag b : Addr) : iProp Σ :=
    na_inv crit Nflag (tsy_flag_inv γ C flag b).

  #[global] Instance tsy_flag_persistent γ C flag b : Persistent (tsy_flag γ C flag b).
  Proof. apply _. Qed.
  #[global] Instance tsy_tok_timeless γ : Timeless (tsy_tok γ).
  Proof. apply _. Qed.

  Lemma tsy_tok_excl γ : tsy_tok γ -∗ tsy_tok γ -∗ False.
  Proof. iIntros "H1 H2". by iDestruct (own_valid_2 with "H1 H2") as %[]. Qed.

  (** The allocation, in the update before the threads start. *)
  Lemma tsy_flag_alloc E C (flag b : Addr) :
    flag ↦ₐ lword_of_word (WInt 0) ={E}=∗ ∃ γ, tsy_flag γ C flag b ∗ tsy_tok γ.
  Proof.
    iIntros "Hflag".
    iMod (own_alloc (Excl () : exclR unitO)) as (γ) "Htok"; first done.
    iMod (na_inv_alloc crit E Nflag (tsy_flag_inv γ C flag b) with "[Hflag]") as "#Hinv".
    { iNext. by iLeft. }
    iModIntro. iExists γ. by iFrame "Hinv Htok".
  Qed.

  (** The setting thread, with the token of the pool: the cell of [flag];
      writing [1] there and giving [tsy_handed] closes the invariant. *)
  Lemma tsy_flag_deposit E γ C (flag b : Addr) :
    ↑Nflag ⊆ E →
    tsy_flag γ C flag b -∗
    na_own crit ⊤
    ={E}=∗
    (∃ w, flag ↦ₐ w) ∗
    (flag ↦ₐ lword_of_word (WInt 1) -∗ tsy_handed C b ={E}=∗ na_own crit ⊤).
  Proof.
    iIntros (HE) "#Hinv Hcrit".
    iMod (na_inv_acc with "Hinv Hcrit") as "(Hc & Hcrit & Hclose)"; [done | done |].
    (* The old content of the 1-branch is dropped *)
    iDestruct "Hc" as "[>Hf | [>Hf _] ]".
    all: iModIntro; iSplitL "Hf"; first by iExists _.
    all: iIntros "Hf Hhanded".
    all: iApply ("Hclose" with "[$Hcrit Hf Hhanded]").
    all: iNext; iRight; iFrame "Hf"; by iLeft.
  Qed.

  (** The waiting thread, with the token of the pool and its own token:
      the cell of [flag], which holds [0] or [1]; at [1], [tsy_handed] one
      later away, and the token stays in the invariant; at [0], the token
      comes back. *)
  Lemma tsy_flag_take E γ C (flag b : Addr) :
    ↑Nflag ⊆ E →
    tsy_flag γ C flag b -∗
    na_own crit ⊤ -∗
    tsy_tok γ
    ={E}=∗
    ∃ z : Z, ⌜z = 0 ∨ z = 1⌝ ∗
      flag ↦ₐ lword_of_word (WInt z) ∗
      (if decide (z = 1) then ▷ tsy_handed C b else tsy_tok γ) ∗
      (flag ↦ₐ lword_of_word (WInt z) ={E}=∗ na_own crit ⊤).
  Proof.
    iIntros (HE) "#Hinv Hcrit Htok".
    iMod (na_inv_acc with "Hinv Hcrit") as "(Hc & Hcrit & Hclose)"; [done | done |].
    iDestruct "Hc" as "[>Hf | [>Hf [Hhanded | >Htok'] ] ]".
    - (* [flag] holds [0]: the token comes back *)
      iModIntro. iExists 0%Z. iFrame "Hf Htok". iSplit; first by iLeft.
      iIntros "Hf". iApply ("Hclose" with "[$Hcrit Hf]"). iNext. by iLeft.
    - (* [flag] holds [1]: the token takes the place of [tsy_handed] *)
      iModIntro. iExists 1%Z. iFrame "Hf Hhanded". iSplit; first by iRight.
      iIntros "Hf". iApply ("Hclose" with "[$Hcrit Hf Htok]").
      iNext. iRight. iFrame "Hf". by iRight.
    - iDestruct (tsy_tok_excl with "Htok Htok'") as %[].
  Qed.

  (** The holder of [tsy_handed] opens the region of [b] and keeps it open;
      it closes it with any integer. *)
  Lemma tsy_handed_acc C (b : Addr) :
    tsy_handed C b -∗
    (∃ w, b ↦ₐ w) ∗
    (∀ z : Z, b ↦ₐ lword_of_word (WInt z) -∗ perm_region_map C ∅).
  Proof.
    iIntros "[Hmap (%φ & %Hpers & #Hrel & #Hint)]".
    (* The accessors are stated at a thread; any thread's memory and
       registry are the base's *)
    iDestruct (open_perm_region_map (th := UserThread 0)
                 C ∅ (LNonHeap b) RW φ with "Hmap Hrel")
      as "[Hmap Hres]"; first set_solver+.
    rewrite union_empty_r_L.
    iDestruct "Hres" as (w) "Hres".
    (* The old value's [▷ φ] is dropped *)
    iDestruct (PermRes_acc (th := UserThread 0) with "Hres")
      as "[(Hb & _) _]".
    iEval (rewrite key_pointsto_nonheap) in "Hb".
    iSplitL "Hb"; first by iExists w.
    iIntros (z) "Hb".
    rewrite -(union_empty_r_L {[ LNonHeap b ]}).
    iApply (close_perm_region_map
              C ∅ (LNonHeap b) RW φ (WInt z) with "Hmap Hrel");
      first set_solver+.
    iApply (init_PermRes (th := UserThread 0)
              C (LNonHeap b) RW φ (WInt z) with "[Hb] []").
    { done. }
    { by iEval (rewrite key_pointsto_nonheap). }
    { iApply "Hint". }
  Qed.
End tsy_flag.
