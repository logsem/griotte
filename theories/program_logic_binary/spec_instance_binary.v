From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl_auth.
From iris.bi.lib Require Import fractional.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Import language ectx_language.
From griotte Require Export rules_base.
From griotte Require Import griotte_opsem.

(** * Spec-side state of the binary model

    The spec (right-hand side) run is a ghost copy of the machine:
    - three [gen_heap]s for the spec registers, system registers and memory;
    - an exclusive [⤇ e] ghost (excl_auth) for the spec thread.
    They are tied to the actual spec execution by [spec_inv ρ], which states
    that the spec configuration is reachable from the initial configuration [ρ].

    The spec [gen_heapGS] instances are deliberately *not* instances: the
    implementation memory is also a [gen_heapGS Addr Word Σ], so global instances
    would make instance search ambiguous. The spec points-to are sealed
    definitions with their own head symbols, with the spec [gen_heapGS] passed
    explicitly. *)

Class specGpreS Σ := SpecGpreS {
  specGpreS_reg : gen_heapGpreS RegName Word Σ;
  specGpreS_sreg : gen_heapGpreS SRegName Word Σ;
  specGpreS_mem : gen_heapGpreS Addr Word Σ;
  specGpreS_expr :: inG Σ (excl_authR (leibnizO griotte_lang.expr));
}.

Definition specΣ : gFunctors :=
  #[gen_heapΣ RegName Word;
    gen_heapΣ SRegName Word;
    gen_heapΣ Addr Word;
    GFunctor (excl_authR (leibnizO griotte_lang.expr))].

Global Instance subG_specGpreS {Σ} : subG specΣ Σ → specGpreS Σ.
Proof.
  intros [? [? [? ?%subG_inG]%subG_inv]%subG_inv]%subG_inv.
  constructor; first [apply subG_gen_heapGpreS; assumption | apply _].
Qed.

Class specG Σ := SpecG {
  (* Not instances, on purpose (see above). *)
  spec_reg_heapG : gen_heapGS RegName Word Σ;
  spec_sreg_heapG : gen_heapGS SRegName Word Σ;
  spec_mem_heapG : gen_heapGS Addr Word Σ;
  spec_exprG :: inG Σ (excl_authR (leibnizO griotte_lang.expr));
  spec_expr_name : gname;
}.

(** ** Sealed spec points-to *)

Section definitions.
  Context `{specg : specG Σ}.

  Local Definition spec_reg_pointsto_def (r : RegName) (dq : dfrac) (w : Word) : iProp Σ :=
    pointsto (hG := spec_reg_heapG) r dq w.
  Local Definition spec_reg_pointsto_aux : seal (@spec_reg_pointsto_def).
  Proof. by eexists. Qed.
  Definition spec_reg_pointsto := spec_reg_pointsto_aux.(unseal).
  Definition spec_reg_pointsto_unseal :
    @spec_reg_pointsto = @spec_reg_pointsto_def := spec_reg_pointsto_aux.(seal_eq).

  Local Definition spec_sreg_pointsto_def (sr : SRegName) (dq : dfrac) (w : Word) : iProp Σ :=
    pointsto (hG := spec_sreg_heapG) sr dq w.
  Local Definition spec_sreg_pointsto_aux : seal (@spec_sreg_pointsto_def).
  Proof. by eexists. Qed.
  Definition spec_sreg_pointsto := spec_sreg_pointsto_aux.(unseal).
  Definition spec_sreg_pointsto_unseal :
    @spec_sreg_pointsto = @spec_sreg_pointsto_def := spec_sreg_pointsto_aux.(seal_eq).

  Local Definition spec_mem_pointsto_def (a : Addr) (dq : dfrac) (w : Word) : iProp Σ :=
    pointsto (hG := spec_mem_heapG) a dq w.
  Local Definition spec_mem_pointsto_aux : seal (@spec_mem_pointsto_def).
  Proof. by eexists. Qed.
  Definition spec_mem_pointsto := spec_mem_pointsto_aux.(unseal).
  Definition spec_mem_pointsto_unseal :
    @spec_mem_pointsto = @spec_mem_pointsto_def := spec_mem_pointsto_aux.(seal_eq).

  Local Definition spec_res_def (e : griotte_lang.expr) : iProp Σ :=
    own spec_expr_name (◯E (e : leibnizO griotte_lang.expr)).
  Local Definition spec_res_aux : seal (@spec_res_def).
  Proof. by eexists. Qed.
  Definition spec_res := spec_res_aux.(unseal).
  Definition spec_res_unseal : @spec_res = @spec_res_def := spec_res_aux.(seal_eq).

  (** Interpretation of the spec machine state. Same nesting as the unary
      [state_interp], so that unary rule proofs can be replayed. *)
  Definition spec_regs_interp (regs : Reg) : iProp Σ :=
    gen_heap_interp (hG := spec_reg_heapG) regs.
  Definition spec_sregs_interp (sregs : SReg) : iProp Σ :=
    gen_heap_interp (hG := spec_sreg_heapG) sregs.
  Definition spec_mem_interp (m : Mem) : iProp Σ :=
    gen_heap_interp (hG := spec_mem_heapG) m.
  Definition spec_state_interp (σ : ExecConf) : iProp Σ :=
    ((spec_regs_interp (reg σ) ∗ spec_sregs_interp (sreg σ)) ∗ spec_mem_interp (mem σ))%I.

End definitions.

(* Points to predicates for spec registers *)
Notation "r ↣ᵣ{ q } w" := (spec_reg_pointsto r q w)
  (at level 20, q at level 50, format "r  ↣ᵣ{ q }  w") : bi_scope.
Notation "r ↣ᵣ w" := (spec_reg_pointsto r (DfracOwn 1) w) (at level 20) : bi_scope.

(* Points to predicates for spec system registers *)
Notation "sr ↣ₛᵣ{ q } w" := (spec_sreg_pointsto sr q w)
  (at level 20, q at level 50, format "sr  ↣ₛᵣ{ q }  w") : bi_scope.
Notation "sr ↣ₛᵣ w" := (spec_sreg_pointsto sr (DfracOwn 1) w) (at level 20) : bi_scope.

(* Points to predicates for spec memory *)
Notation "a ↣ₐ{ q } w" := (spec_mem_pointsto a q w)
  (at level 20, q at level 50, format "a  ↣ₐ{ q }  w") : bi_scope.
Notation "a ↣ₐ w" := (spec_mem_pointsto a (DfracOwn 1) w) (at level 20) : bi_scope.

(* Spec thread *)
Notation "⤇ e" := (spec_res e) (at level 20) : bi_scope.

(** ** Spec points-to lemmas *)

Section pointsto.
  Context `{specg : specG Σ}.
  Implicit Types r : RegName.
  Implicit Types sr : SRegName.
  Implicit Types a : Addr.
  Implicit Types w : Word.

  Ltac unseal_pt :=
    rewrite ?spec_reg_pointsto_unseal ?spec_sreg_pointsto_unseal
      ?spec_mem_pointsto_unseal ?spec_res_unseal
      /spec_reg_pointsto_def /spec_sreg_pointsto_def /spec_mem_pointsto_def /spec_res_def.

  (* registers *)
  Global Instance spec_reg_pointsto_timeless r dq w : Timeless (r ↣ᵣ{dq} w).
  Proof. unseal_pt. apply _. Qed.
  Global Instance spec_reg_pointsto_fractional r w : Fractional (λ q, r ↣ᵣ{DfracOwn q} w)%I.
  Proof. unseal_pt. apply _. Qed.
  Global Instance spec_reg_pointsto_as_fractional r q w :
    AsFractional (r ↣ᵣ{DfracOwn q} w) (λ q, r ↣ᵣ{DfracOwn q} w)%I q.
  Proof. split; [done | apply _]. Qed.
  Global Instance spec_reg_pointsto_persistent r w : Persistent (r ↣ᵣ{DfracDiscarded} w).
  Proof. unseal_pt. apply _. Qed.

  Lemma spec_reg_pointsto_valid_2 r dq1 dq2 w1 w2 :
    r ↣ᵣ{dq1} w1 -∗ r ↣ᵣ{dq2} w2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ w1 = w2⌝.
  Proof. unseal_pt. apply pointsto_valid_2. Qed.
  Lemma spec_reg_pointsto_agree r dq1 dq2 w1 w2 :
    r ↣ᵣ{dq1} w1 -∗ r ↣ᵣ{dq2} w2 -∗ ⌜w1 = w2⌝.
  Proof. unseal_pt. apply pointsto_agree. Qed.
  Lemma spec_reg_pointsto_persist r dq w : r ↣ᵣ{dq} w ==∗ r ↣ᵣ{DfracDiscarded} w.
  Proof. unseal_pt. apply pointsto_persist. Qed.

  Lemma spec_regname_dupl_false r w1 w2 :
    r ↣ᵣ w1 -∗ r ↣ᵣ w2 -∗ False.
  Proof.
    iIntros "Hr1 Hr2".
    iDestruct (spec_reg_pointsto_valid_2 with "Hr1 Hr2") as %[Hv _].
    by eapply dfrac_full_exclusive in Hv.
  Qed.

  Lemma spec_regname_neq r1 r2 w1 w2 :
    r1 ↣ᵣ w1 -∗ r2 ↣ᵣ w2 -∗ ⌜ r1 ≠ r2 ⌝.
  Proof.
    iIntros "H1 H2" (?). subst r1. iApply (spec_regname_dupl_false with "H1 H2").
  Qed.

  (* system registers *)
  Global Instance spec_sreg_pointsto_timeless sr dq w : Timeless (sr ↣ₛᵣ{dq} w).
  Proof. unseal_pt. apply _. Qed.
  Global Instance spec_sreg_pointsto_fractional sr w : Fractional (λ q, sr ↣ₛᵣ{DfracOwn q} w)%I.
  Proof. unseal_pt. apply _. Qed.
  Global Instance spec_sreg_pointsto_as_fractional sr q w :
    AsFractional (sr ↣ₛᵣ{DfracOwn q} w) (λ q, sr ↣ₛᵣ{DfracOwn q} w)%I q.
  Proof. split; [done | apply _]. Qed.
  Global Instance spec_sreg_pointsto_persistent sr w : Persistent (sr ↣ₛᵣ{DfracDiscarded} w).
  Proof. unseal_pt. apply _. Qed.

  Lemma spec_sreg_pointsto_valid_2 sr dq1 dq2 w1 w2 :
    sr ↣ₛᵣ{dq1} w1 -∗ sr ↣ₛᵣ{dq2} w2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ w1 = w2⌝.
  Proof. unseal_pt. apply pointsto_valid_2. Qed.
  Lemma spec_sreg_pointsto_agree sr dq1 dq2 w1 w2 :
    sr ↣ₛᵣ{dq1} w1 -∗ sr ↣ₛᵣ{dq2} w2 -∗ ⌜w1 = w2⌝.
  Proof. unseal_pt. apply pointsto_agree. Qed.
  Lemma spec_sreg_pointsto_persist sr dq w : sr ↣ₛᵣ{dq} w ==∗ sr ↣ₛᵣ{DfracDiscarded} w.
  Proof. unseal_pt. apply pointsto_persist. Qed.

  Lemma spec_sregname_dupl_false sr w1 w2 :
    sr ↣ₛᵣ w1 -∗ sr ↣ₛᵣ w2 -∗ False.
  Proof.
    iIntros "Hr1 Hr2".
    iDestruct (spec_sreg_pointsto_valid_2 with "Hr1 Hr2") as %[Hv _].
    by eapply dfrac_full_exclusive in Hv.
  Qed.

  Lemma spec_sregname_neq sr1 sr2 w1 w2 :
    sr1 ↣ₛᵣ w1 -∗ sr2 ↣ₛᵣ w2 -∗ ⌜ sr1 ≠ sr2 ⌝.
  Proof.
    iIntros "H1 H2" (?). subst sr1. iApply (spec_sregname_dupl_false with "H1 H2").
  Qed.

  (* memory *)
  Global Instance spec_mem_pointsto_timeless a dq w : Timeless (a ↣ₐ{dq} w).
  Proof. unseal_pt. apply _. Qed.
  Global Instance spec_mem_pointsto_fractional a w : Fractional (λ q, a ↣ₐ{DfracOwn q} w)%I.
  Proof. unseal_pt. apply _. Qed.
  Global Instance spec_mem_pointsto_as_fractional a q w :
    AsFractional (a ↣ₐ{DfracOwn q} w) (λ q, a ↣ₐ{DfracOwn q} w)%I q.
  Proof. split; [done | apply _]. Qed.
  Global Instance spec_mem_pointsto_persistent a w : Persistent (a ↣ₐ{DfracDiscarded} w).
  Proof. unseal_pt. apply _. Qed.

  Lemma spec_mem_pointsto_valid a dq w : a ↣ₐ{dq} w -∗ ⌜✓ dq⌝.
  Proof. unseal_pt. apply pointsto_valid. Qed.
  Lemma spec_mem_pointsto_valid_2 a dq1 dq2 w1 w2 :
    a ↣ₐ{dq1} w1 -∗ a ↣ₐ{dq2} w2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ w1 = w2⌝.
  Proof. unseal_pt. apply pointsto_valid_2. Qed.
  Lemma spec_mem_pointsto_agree a dq1 dq2 w1 w2 :
    a ↣ₐ{dq1} w1 -∗ a ↣ₐ{dq2} w2 -∗ ⌜w1 = w2⌝.
  Proof. unseal_pt. apply pointsto_agree. Qed.
  Lemma spec_mem_pointsto_combine a dq1 dq2 w1 w2 :
    a ↣ₐ{dq1} w1 -∗ a ↣ₐ{dq2} w2 -∗ a ↣ₐ{dq1 ⋅ dq2} w1 ∗ ⌜w1 = w2⌝.
  Proof. unseal_pt. apply pointsto_combine. Qed.
  Lemma spec_mem_pointsto_persist a dq w : a ↣ₐ{dq} w ==∗ a ↣ₐ{DfracDiscarded} w.
  Proof. unseal_pt. apply pointsto_persist. Qed.

  Lemma spec_addr_dupl_false a w1 w2 :
    a ↣ₐ w1 -∗ a ↣ₐ w2 -∗ False.
  Proof.
    iIntros "Ha1 Ha2".
    iDestruct (spec_mem_pointsto_valid_2 with "Ha1 Ha2") as %[Hv _].
    by eapply dfrac_full_exclusive in Hv.
  Qed.

  Lemma spec_address_neq a1 a2 w1 w2 :
    a1 ↣ₐ w1 -∗ a2 ↣ₐ w2 -∗ ⌜a1 ≠ a2⌝.
  Proof.
    iIntros "H1 H2" (?). subst a1. iApply (spec_addr_dupl_false with "H1 H2").
  Qed.

  (* spec thread *)
  Global Instance spec_res_timeless e : Timeless (⤇ e).
  Proof. unseal_pt. apply _. Qed.

  Lemma spec_res_dupl_false e1 e2 : ⤇ e1 -∗ ⤇ e2 -∗ False.
  Proof.
    unseal_pt. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    by apply excl_auth_frag_op_valid in Hv.
  Qed.

  (** *** Spec state interpretation: validity and update *)

  Lemma spec_regs_valid regs r dq w :
    spec_regs_interp regs -∗ r ↣ᵣ{dq} w -∗ ⌜regs !! r = Some w⌝.
  Proof. unseal_pt. rewrite /spec_regs_interp. apply gen_heap_valid. Qed.

  Lemma spec_regs_update regs r w w' :
    spec_regs_interp regs -∗ r ↣ᵣ w ==∗ spec_regs_interp (<[r:=w']> regs) ∗ r ↣ᵣ w'.
  Proof. unseal_pt. rewrite /spec_regs_interp. apply gen_heap_update. Qed.

  Lemma spec_regs_valid_inclSepM regs rmap :
    spec_regs_interp regs -∗ ([∗ map] k↦y ∈ rmap, k ↣ᵣ y) -∗ ⌜rmap ⊆ regs⌝.
  Proof. unseal_pt. rewrite /spec_regs_interp. apply gen_heap_valid_inclSepM. Qed.

  Lemma spec_regs_update_inSepM regs rmap r w :
    is_Some (rmap !! r) →
    spec_regs_interp regs -∗ ([∗ map] k↦y ∈ rmap, k ↣ᵣ y)
    ==∗ spec_regs_interp (<[r:=w]> regs) ∗ [∗ map] k↦y ∈ (<[r:=w]> rmap), k ↣ᵣ y.
  Proof. unseal_pt. rewrite /spec_regs_interp. apply gen_heap_update_inSepM. Qed.

  Lemma spec_sregs_valid sregs sr dq w :
    spec_sregs_interp sregs -∗ sr ↣ₛᵣ{dq} w -∗ ⌜sregs !! sr = Some w⌝.
  Proof. unseal_pt. rewrite /spec_sregs_interp. apply gen_heap_valid. Qed.

  Lemma spec_sregs_update sregs sr w w' :
    spec_sregs_interp sregs -∗ sr ↣ₛᵣ w ==∗ spec_sregs_interp (<[sr:=w']> sregs) ∗ sr ↣ₛᵣ w'.
  Proof. unseal_pt. rewrite /spec_sregs_interp. apply gen_heap_update. Qed.

  Lemma spec_sregs_valid_inclSepM sregs srmap :
    spec_sregs_interp sregs -∗ ([∗ map] k↦y ∈ srmap, k ↣ₛᵣ y) -∗ ⌜srmap ⊆ sregs⌝.
  Proof. unseal_pt. rewrite /spec_sregs_interp. apply gen_heap_valid_inclSepM. Qed.

  Lemma spec_sregs_update_inSepM sregs srmap sr w :
    is_Some (srmap !! sr) →
    spec_sregs_interp sregs -∗ ([∗ map] k↦y ∈ srmap, k ↣ₛᵣ y)
    ==∗ spec_sregs_interp (<[sr:=w]> sregs) ∗ [∗ map] k↦y ∈ (<[sr:=w]> srmap), k ↣ₛᵣ y.
  Proof. unseal_pt. rewrite /spec_sregs_interp. apply gen_heap_update_inSepM. Qed.

  Lemma spec_mem_valid m a dq w :
    spec_mem_interp m -∗ a ↣ₐ{dq} w -∗ ⌜m !! a = Some w⌝.
  Proof. unseal_pt. rewrite /spec_mem_interp. apply gen_heap_valid. Qed.

  Lemma spec_mem_update m a w w' :
    spec_mem_interp m -∗ a ↣ₐ w ==∗ spec_mem_interp (<[a:=w']> m) ∗ a ↣ₐ w'.
  Proof. unseal_pt. rewrite /spec_mem_interp. apply gen_heap_update. Qed.

  Lemma spec_mem_valid_inclSepM m mmap :
    spec_mem_interp m -∗ ([∗ map] k↦y ∈ mmap, k ↣ₐ y) -∗ ⌜mmap ⊆ m⌝.
  Proof. unseal_pt. rewrite /spec_mem_interp. apply gen_heap_valid_inclSepM. Qed.

  Lemma spec_mem_valid_inSepM mmap m a w :
    mmap !! a = Some w →
    spec_mem_interp m -∗ ([∗ map] a↦w ∈ mmap, a ↣ₐ w) -∗ ⌜m !! a = Some w⌝.
  Proof.
    iIntros (Ha) "Hm Hmap".
    rewrite (big_sepM_delete _ _ a) //. iDestruct "Hmap" as "[Ha _]".
    iApply (spec_mem_valid with "Hm Ha").
  Qed.

  Lemma spec_mem_valid_inSepM_general mmap m a w dq :
    mmap !! a = Some (dq, w) →
    spec_mem_interp m -∗ ([∗ map] a↦dqw ∈ mmap, a ↣ₐ{dqw.1} dqw.2) -∗ ⌜m !! a = Some w⌝.
  Proof.
    iIntros (Ha) "Hm Hmap".
    rewrite (big_sepM_delete _ _ a) //. iDestruct "Hmap" as "[Ha _]".
    iApply (spec_mem_valid with "Hm Ha").
  Qed.

  Lemma spec_mem_update_inSepM m mmap a w' w :
    mmap !! a = Some w' →
    spec_mem_interp m -∗ ([∗ map] a↦w ∈ mmap, a ↣ₐ w)
    ==∗ spec_mem_interp (<[a:=w]> m) ∗ ([∗ map] a↦w ∈ <[a:=w]> mmap, a ↣ₐ w).
  Proof.
    iIntros (Ha) "Hm Hmap".
    rewrite (big_sepM_delete _ _ a) //. iDestruct "Hmap" as "[Ha Hmap]".
    iMod (spec_mem_update with "Hm Ha") as "[$ Ha]".
    iModIntro. rewrite -insert_delete_eq big_sepM_insert ?lookup_delete_eq //. iFrame.
  Qed.

  (** *** Building maps of spec points-to (spec copies of [rules_base]) *)

  Lemma spec_map_of_regs_1 (r1: RegName) (w1: Word) :
    r1 ↣ᵣ w1 -∗
    ([∗ map] k↦y ∈ {[r1 := w1]}, k ↣ᵣ y).
  Proof. rewrite big_sepM_singleton; auto. Qed.

  Lemma spec_regs_of_map_1 (r1: RegName) (w1: Word) :
    ([∗ map] k↦y ∈ {[r1 := w1]}, k ↣ᵣ y) -∗
    r1 ↣ᵣ w1.
  Proof. rewrite big_sepM_singleton; auto. Qed.

  Lemma spec_map_of_regs_2 (r1 r2: RegName) (w1 w2: Word) :
    r1 ↣ᵣ w1 -∗ r2 ↣ᵣ w2 -∗
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> ∅)), k ↣ᵣ y) ∗ ⌜ r1 ≠ r2 ⌝.
  Proof.
    iIntros "H1 H2". iPoseProof (spec_regname_neq with "H1 H2") as "%".
    rewrite !big_sepM_insert ?big_sepM_empty; eauto.
    2: by apply lookup_insert_None; split; eauto.
    iFrame. eauto.
  Qed.

  Lemma spec_regs_of_map_2 (r1 r2: RegName) (w1 w2: Word) :
    r1 ≠ r2 →
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> ∅)), k ↣ᵣ y) -∗
    r1 ↣ᵣ w1 ∗ r2 ↣ᵣ w2.
  Proof.
    iIntros (?) "Hmap". rewrite !big_sepM_insert ?big_sepM_empty; eauto.
    + by iDestruct "Hmap" as "(? & ? & _)"; iFrame.
    + apply lookup_insert_None; split; eauto.
  Qed.

  Lemma spec_map_of_regs_3 (r1 r2 r3: RegName) (w1 w2 w3: Word) :
    r1 ↣ᵣ w1 -∗ r2 ↣ᵣ w2 -∗ r3 ↣ᵣ w3 -∗
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> ∅))), k ↣ᵣ y) ∗
     ⌜ r1 ≠ r2 ∧ r1 ≠ r3 ∧ r2 ≠ r3 ⌝.
  Proof.
    iIntros "H1 H2 H3".
    iPoseProof (spec_regname_neq with "H1 H2") as "%".
    iPoseProof (spec_regname_neq with "H1 H3") as "%".
    iPoseProof (spec_regname_neq with "H2 H3") as "%".
    rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iFrame. eauto.
  Qed.

  Lemma spec_regs_of_map_3 (r1 r2 r3: RegName) (w1 w2 w3: Word) :
    r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 →
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> ∅))), k ↣ᵣ y) -∗
    r1 ↣ᵣ w1 ∗ r2 ↣ᵣ w2 ∗ r3 ↣ᵣ w3.
  Proof.
    iIntros (? ? ?) "Hmap". rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iDestruct "Hmap" as "(? & ? & ? & _)"; iFrame.
  Qed.

  Lemma spec_map_of_regs_4 (r1 r2 r3 r4: RegName) (w1 w2 w3 w4: Word) :
    r1 ↣ᵣ w1 -∗ r2 ↣ᵣ w2 -∗ r3 ↣ᵣ w3 -∗ r4 ↣ᵣ w4 -∗
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> (<[r4:=w4]> ∅)))), k ↣ᵣ y) ∗
     ⌜ r1 ≠ r2 ∧ r1 ≠ r3 ∧ r1 ≠ r4 ∧ r2 ≠ r3 ∧ r2 ≠ r4 ∧ r3 ≠ r4 ⌝.
  Proof.
    iIntros "H1 H2 H3 H4".
    iPoseProof (spec_regname_neq with "H1 H2") as "%".
    iPoseProof (spec_regname_neq with "H1 H3") as "%".
    iPoseProof (spec_regname_neq with "H1 H4") as "%".
    iPoseProof (spec_regname_neq with "H2 H3") as "%".
    iPoseProof (spec_regname_neq with "H2 H4") as "%".
    iPoseProof (spec_regname_neq with "H3 H4") as "%".
    rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iFrame. eauto.
  Qed.

  Lemma spec_regs_of_map_4 (r1 r2 r3 r4: RegName) (w1 w2 w3 w4: Word) :
    r1 ≠ r2 → r1 ≠ r3 → r1 ≠ r4 → r2 ≠ r3 → r2 ≠ r4 → r3 ≠ r4 →
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> (<[r4:=w4]> ∅)))), k ↣ᵣ y) -∗
    r1 ↣ᵣ w1 ∗ r2 ↣ᵣ w2 ∗ r3 ↣ᵣ w3 ∗ r4 ↣ᵣ w4.
  Proof.
    intros. iIntros "Hmap". rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iDestruct "Hmap" as "(? & ? & ? & ? & _)"; iFrame.
  Qed.

  Lemma spec_map_of_sregs_1 (sr1: SRegName) (w1: Word) :
    sr1 ↣ₛᵣ w1 -∗
    ([∗ map] k↦y ∈ {[sr1 := w1]}, k ↣ₛᵣ y).
  Proof. rewrite big_sepM_singleton; auto. Qed.

  Lemma spec_sregs_of_map_1 (sr1: SRegName) (w1: Word) :
    ([∗ map] k↦y ∈ {[sr1 := w1]}, k ↣ₛᵣ y) -∗
    sr1 ↣ₛᵣ w1.
  Proof. rewrite big_sepM_singleton; auto. Qed.

  Lemma spec_memMap_resource_1_dq (a : Addr) (w : Word) dq :
    a ↣ₐ{dq} w ⊣⊢ ([∗ map] a↦w ∈ <[a:=w]> ∅, a ↣ₐ{dq} w)%I.
  Proof. by rewrite big_sepM_insert ?big_sepM_empty ?right_id. Qed.

  Lemma spec_memMap_resource_1 (a : Addr) (w : Word) :
    a ↣ₐ w ⊣⊢ ([∗ map] a↦w ∈ <[a:=w]> ∅, a ↣ₐ w)%I.
  Proof. apply spec_memMap_resource_1_dq. Qed.

  Lemma spec_memMap_resource_2ne (a1 a2 : Addr) (w1 w2 : Word) :
    a1 ≠ a2 →
    ([∗ map] a↦w ∈ <[a1:=w1]> (<[a2:=w2]> ∅), a ↣ₐ w)%I ⊣⊢ a1 ↣ₐ w1 ∗ a2 ↣ₐ w2.
  Proof.
    intros. rewrite !big_sepM_insert ?big_sepM_empty ?right_id //.
    by rewrite lookup_insert_ne.
  Qed.

End pointsto.

(** ** Spec invariant *)

Definition specN : namespace := nroot .@ "spec".

Local Instance griotte_expr_inhabited : Inhabited griotte_lang.expr :=
  populate (Instr Executable).

Section spec_inv.
  Context `{MP: MachineParameters} `{!invGS Σ} `{specg : specG Σ}.
  Implicit Types σ : ExecConf.
  Implicit Types e : griotte_lang.expr.
  Implicit Types ρ : cfg griotte_lang.

  Definition spec_inv ρ : iProp Σ :=
    ∃ e σ,
      own spec_expr_name (●E (e : leibnizO griotte_lang.expr)) ∗
      spec_state_interp σ ∗
      ⌜rtc erased_step ρ ([e], σ)⌝.

  (* The initial configuration is existentially quantified; adequacy
     proofs keep the concrete [inv specN (spec_inv ρ)] from [spec_init]. *)
  Definition spec_ctx : iProp Σ := ∃ ρ, inv specN (spec_inv ρ).

  Global Instance spec_ctx_persistent : Persistent spec_ctx.
  Proof. apply _. Qed.

  Lemma spec_ctx_intro ρ : inv specN (spec_inv ρ) -∗ spec_ctx.
  Proof. iIntros "H". by iExists ρ. Qed.

  Lemma spec_auth_agree e e' :
    own spec_expr_name (●E (e : leibnizO griotte_lang.expr)) -∗ ⤇ e' -∗ ⌜e = e'⌝.
  Proof.
    rewrite spec_res_unseal. iIntros "H1 H2".
    by iDestruct (own_valid_2 with "H1 H2") as %?%excl_auth_agree_L.
  Qed.

  Lemma spec_auth_update e e' e'' :
    own spec_expr_name (●E (e : leibnizO griotte_lang.expr)) -∗ ⤇ e' ==∗
    own spec_expr_name (●E (e'' : leibnizO griotte_lang.expr)) ∗ ⤇ e''.
  Proof.
    rewrite spec_res_unseal. iIntros "H1 H2".
    iMod (own_update_2 with "H1 H2") as "[$ $]"; last done.
    apply excl_auth_update.
  Qed.

  (** The most general spec step: one thread step without forks. *)
  Lemma spec_step E e Ψ :
    ↑specN ⊆ E →
    spec_ctx -∗
    ⤇ e -∗
    (∀ σ, spec_state_interp σ ==∗
       ∃ e' σ', ⌜language.prim_step e σ [] e' σ' []⌝ ∗ spec_state_interp σ' ∗ Ψ e')
    ={E}=∗
    ∃ e', ⤇ e' ∗ Ψ e'.
  Proof.
    iIntros (HE) "[%ρ #Hinv] Hj Hstep".
    iInv specN as (e0 σ) ">(Hauth & Hσ & %Hrtc)" "Hclose".
    iDestruct (spec_auth_agree with "Hauth Hj") as %<-.
    iMod ("Hstep" with "Hσ") as (e' σ' Hps) "[Hσ HΨ]".
    iMod (spec_auth_update _ _ e' with "Hauth Hj") as "[Hauth Hj]".
    iMod ("Hclose" with "[Hauth Hσ]") as "_".
    { iNext. iExists e', σ'. iFrame. iPureIntro.
      eapply rtc_r; first exact Hrtc.
      exists []. eapply (step_atomic _ _ _ _ _ [] []); eauto. }
    iModIntro. iExists e'. iFrame.
  Qed.

  (** Pure spec steps. *)
  Lemma pure_steps_erased_step n e e' σ :
    nsteps pure_step n e e' →
    rtc erased_step ([e], σ) ([e'], σ).
  Proof.
    induction 1 as [|n e1 e2 e3 Hstep _ IH]; first done.
    eapply rtc_l; last exact IH.
    destruct (pure_step_safe _ _ Hstep σ) as (e2' & σ2 & efs & Hps).
    destruct (pure_step_det _ _ Hstep _ _ _ _ _ Hps) as (_ & -> & -> & ->).
    exists []. eapply (step_atomic _ _ _ _ _ [] []); eauto.
  Qed.

  Lemma spec_pure_exec E φ n e e' :
    PureExec φ n e e' →
    φ →
    ↑specN ⊆ E →
    spec_ctx -∗
    ⤇ e
    ={E}=∗
    ⤇ e'.
  Proof.
    iIntros (Hpure Hφ HE) "[%ρ #Hinv] Hj".
    iInv specN as (e0 σ) ">(Hauth & Hσ & %Hrtc)" "Hclose".
    iDestruct (spec_auth_agree with "Hauth Hj") as %<-.
    iMod (spec_auth_update _ _ e' with "Hauth Hj") as "[Hauth Hj]".
    iMod ("Hclose" with "[Hauth Hσ]") as "_".
    { iNext. iExists e', σ. iFrame. iPureIntro.
      etrans; first exact Hrtc.
      eapply pure_steps_erased_step, Hpure, Hφ. }
    by iFrame.
  Qed.

  (* Instruction rules step [Seq (Instr Executable)] to [Seq (Instr c)];
     the [Seq] is reduced by a separate spec step. *)
  Lemma step_seq_nexti E :
    ↑specN ⊆ E →
    spec_ctx -∗
    ⤇ Seq (Instr NextI)
    ={E}=∗
    ⤇ Seq (Instr Executable).
  Proof. intros. by iApply spec_pure_exec. Qed.

  Lemma step_seq_halted E :
    ↑specN ⊆ E →
    spec_ctx -∗
    ⤇ Seq (Instr Halted)
    ={E}=∗
    ⤇ Instr Halted.
  Proof. intros. by iApply spec_pure_exec. Qed.

  Lemma step_seq_failed E :
    ↑specN ⊆ E →
    spec_ctx -∗
    ⤇ Seq (Instr Failed)
    ={E}=∗
    ⤇ Instr Failed.
  Proof. intros. by iApply spec_pure_exec. Qed.

  (** Generic instruction step. The continuation receives an arbitrary machine
      step from the spec state, mirroring the unary [wp_lift_atomic_base_step_no_fork]
      proofs: unary rule bodies can be replayed after [prim_step_exec_inv]. *)
  Lemma spec_step_exec_gen E Φ :
    ↑specN ⊆ E →
    spec_ctx -∗
    ⤇ Seq (Instr Executable) -∗
    (∀ σ c σ', ⌜step (Executable, σ) (c, σ')⌝ -∗
       spec_state_interp σ ==∗
       spec_state_interp σ' ∗ from_option Φ False (to_val (Instr c)))
    ={E}=∗
    ∃ v, ⤇ Seq (of_val v) ∗ Φ v.
  Proof.
    iIntros (HE) "#Hctx Hj Hcont".
    iMod (spec_step _ _ (λ e', ∃ v, ⌜e' = Seq (of_val v)⌝ ∗ Φ v)%I
           with "Hctx Hj [Hcont]") as (e') "[Hj (%v & -> & HΦ)]"; first done.
    2: { iModIntro. iExists v. iFrame. }
    iIntros (σ) "Hσ".
    destruct (normal_always_step σ) as (c & σ' & Hstep).
    iMod ("Hcont" $! σ c σ' with "[//] Hσ") as "[Hσ HΦ]".
    destruct (to_val (Instr c)) as [v|] eqn:Hv; last done.
    iModIntro. iExists (Seq (Instr c)), σ'. iFrame. iSplit.
    - iPureIntro. eapply (Ectx_step [SeqCtx] (Instr Executable) (Instr c)); [done|done|].
      by constructor.
    - iPureIntro. by rewrite (of_to_val _ _ Hv).
  Qed.

  (** Generic instruction step, with the step computed by [exec]. The register
      map and the instruction points-to are handed back to the continuation. *)
  Lemma spec_step_exec E Φ (regs : Reg) pc_p pc_g pc_b pc_e pc_a dq w :
    ↑specN ⊆ E →
    regs !! PC = Some (WCap pc_p pc_g pc_b pc_e pc_a) →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    spec_ctx -∗
    ⤇ Seq (Instr Executable) -∗
    ([∗ map] k↦y ∈ regs, k ↣ᵣ y) -∗
    pc_a ↣ₐ{dq} w -∗
    (∀ σ c σ',
       ⌜regs ⊆ reg σ⌝ -∗
       ⌜mem σ !! pc_a = Some w⌝ -∗
       ⌜exec (decodeInstrW w) pc_p σ = (c, σ')⌝ -∗
       spec_state_interp σ -∗
       ([∗ map] k↦y ∈ regs, k ↣ᵣ y) -∗
       pc_a ↣ₐ{dq} w ==∗
       spec_state_interp σ' ∗ from_option Φ False (to_val (Instr c)))
    ={E}=∗
    ∃ v, ⤇ Seq (of_val v) ∗ Φ v.
  Proof.
    iIntros (HE HPC Hvpc) "#Hctx Hj Hmap Hpc_a Hcont".
    iApply (spec_step_exec_gen with "Hctx Hj"); first done.
    iIntros ([[r sr] m] c σ' Hstep) "[[Hr Hsr] Hm]".
    iDestruct (spec_regs_valid_inclSepM with "Hr Hmap") as %Hregs.
    iDestruct (spec_mem_valid with "Hm Hpc_a") as %Hpc_a.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    eapply step_exec_inv in Hstep; eauto.
    iApply ("Hcont" with "[//] [//] [//] [$Hr $Hsr $Hm] Hmap Hpc_a").
  Qed.

  (** Failing on an incorrect PC. *)
  Lemma step_notCorrectPC E w :
    ↑specN ⊆ E →
    ¬ isCorrectPC w →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ w
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    PC ↣ᵣ w.
  Proof.
    iIntros (HE Hnpc) "(#Hctx & Hj & HPC)".
    iMod (spec_step_exec_gen _ (λ v, ⌜v = FailedV⌝ ∗ PC ↣ᵣ w)%I with "Hctx Hj [HPC]")
      as (v) "(Hj & -> & HPC)"; first done; last by iFrame.
    iIntros (σ c σ' Hstep) "[[Hr Hsr] Hm]".
    iDestruct (spec_regs_valid with "Hr HPC") as %HPC.
    eapply step_fail_inv in Hstep as [-> ->]; eauto.
    by iFrame.
  Qed.

  Lemma step_halt E pc_p pc_g pc_b pc_e pc_a dq w :
    ↑specN ⊆ E →
    decodeInstrW w = Halt →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w
    ={E}=∗
    ⤇ Seq (Instr Halted) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w.
  Proof.
    iIntros (HE Hinstr Hvpc) "(#Hctx & Hj & HPC & Hpc_a)".
    iDestruct (spec_map_of_regs_1 with "HPC") as "Hmap".
    iMod (spec_step_exec _
            (λ v, ⌜v = HaltedV⌝ ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↣ₐ{dq} w)%I
           with "Hctx Hj Hmap Hpc_a [] ")
      as (v) "(Hj & -> & HPC & Hpc_a)"; first done.
    1,2: by simplify_map_eq.
    2: by iFrame.
    iIntros (σ c σ' _ _ Hexec) "Hσ Hmap Hpc_a".
    rewrite Hinstr /exec /= in Hexec. simplify_eq.
    iDestruct (spec_regs_of_map_1 with "Hmap") as "HPC".
    by iFrame.
  Qed.

  Lemma step_fail E pc_p pc_g pc_b pc_e pc_a dq w :
    ↑specN ⊆ E →
    decodeInstrW w = Fail →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w.
  Proof.
    iIntros (HE Hinstr Hvpc) "(#Hctx & Hj & HPC & Hpc_a)".
    iDestruct (spec_map_of_regs_1 with "HPC") as "Hmap".
    iMod (spec_step_exec _
            (λ v, ⌜v = FailedV⌝ ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↣ₐ{dq} w)%I
           with "Hctx Hj Hmap Hpc_a [] ")
      as (v) "(Hj & -> & HPC & Hpc_a)"; first done.
    1,2: by simplify_map_eq.
    2: by iFrame.
    iIntros (σ c σ' _ _ Hexec) "Hσ Hmap Hpc_a".
    rewrite Hinstr /exec /= in Hexec. simplify_eq.
    iDestruct (spec_regs_of_map_1 with "Hmap") as "HPC".
    by iFrame.
  Qed.

  (** For adequacy: the spec thread is reachable from the initial configuration. *)
  Lemma spec_inv_reachable E ρ e :
    ↑specN ⊆ E →
    inv specN (spec_inv ρ) -∗
    ⤇ e
    ={E}=∗
    ⤇ e ∗ ⌜∃ σ, rtc erased_step ρ ([e], σ)⌝.
  Proof.
    iIntros (HE) "#Hinv Hj".
    iInv specN as (e0 σ) ">(Hauth & Hσ & %Hrtc)" "Hclose".
    iDestruct (spec_auth_agree with "Hauth Hj") as %<-.
    iMod ("Hclose" with "[Hauth Hσ]") as "_".
    { iNext. iExists e0, σ. by iFrame. }
    iModIntro. iFrame. eauto.
  Qed.

End spec_inv.

(** ** Initialisation, for adequacy *)

Lemma spec_init `{MP: MachineParameters} `{!invGS Σ} `{Hpre : !specGpreS Σ} E
  (e : griotte_lang.expr) (σ : ExecConf) :
  ⊢ |={E}=> ∃ (specg : specG Σ),
      inv specN (spec_inv ([e], σ)) ∗
      spec_ctx ∗
      ⤇ e ∗
      ([∗ map] r↦w ∈ reg σ, r ↣ᵣ w) ∗
      ([∗ map] sr↦w ∈ sreg σ, sr ↣ₛᵣ w) ∗
      ([∗ map] a↦w ∈ mem σ, a ↣ₐ w).
Proof.
  iMod (@gen_heap_init _ _ _ _ _ specGpreS_reg (reg σ)) as (reg_heapg) "(Hr_ctx & Hr & _)".
  iMod (@gen_heap_init _ _ _ _ _ specGpreS_sreg (sreg σ)) as (sreg_heapg) "(Hsr_ctx & Hsr & _)".
  iMod (@gen_heap_init _ _ _ _ _ specGpreS_mem (mem σ)) as (mem_heapg) "(Hm_ctx & Hm & _)".
  iMod (own_alloc (●E (e : leibnizO griotte_lang.expr) ⋅ ◯E (e : leibnizO griotte_lang.expr)))
    as (γ) "[Hauth Hfrag]".
  { apply excl_auth_valid. }
  set (specg := SpecG Σ reg_heapg sreg_heapg mem_heapg _ γ).
  iMod (inv_alloc specN E (spec_inv (specg := specg) ([e], σ)) with "[Hauth Hr_ctx Hsr_ctx Hm_ctx]")
    as "#Hinv".
  { iNext. iExists e, σ. iFrame. done. }
  iModIntro. iExists specg.
  rewrite spec_res_unseal spec_reg_pointsto_unseal spec_sreg_pointsto_unseal spec_mem_pointsto_unseal.
  iFrame "∗ #".
Qed.
