From iris.base_logic Require Export invariants na_invariants gen_heap ghost_map ghost_var.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import proofmode.
From griotte Require Import griotte_lang entry.
From griotte Require Export logical_words alloc_registry erasure.



(* Non atomic invariants *)
Class cerise_na_invs Σ :=
  {
    na_invG :: na_invG Σ;
    cerise_nais : na_inv_pool_name;
  }.

(* CMRA for Cerise. Registers and memory hold logical words; system registers
   hold identifier-less words. *)
Class ceriseG Σ :=
  CeriseG {
      cerise_invG : invGS Σ;
      cerise_nainvG :: cerise_na_invs Σ;
      mem_gen_memG :: gen_heapGS Addr LWord Σ; (* memory *)
      shadowtbl_gen_regG :: gen_heapGS Addr AllocStatus Σ; (* shadow table *)
      reg_gen_regG :: gen_heapGS RegName LWord Σ; (* register *)
      sreg_gen_regG :: gen_heapGS SRegName Word Σ; (* system register *)
      entryG :: entryGS Σ; (* entry point *)
      cerise_registryG :: allocRegistryG Σ; (* allocation registry *)
      cerise_addr_allocG :: addrAllocG Σ (* address claims *)
    }.

(** The state interpretation: the logical registers and memory, the physical
    system registers and shadow table, the registry and the address claims,
    related to the machine state by erasure. *)
Section state_interp.
  Context `{MP : MachineParameters}.
  Context `{!gen_heapGS RegName LWord Σ, !gen_heapGS SRegName Word Σ,
            !gen_heapGS Addr LWord Σ, !gen_heapGS Addr AllocStatus Σ,
            !allocRegistryG Σ, !addrAllocG Σ}.

  Definition cerise_state_interp (σ : ExecConf) : iProp Σ :=
    ∃ (lreg : LReg) (lmem : LMem) (R : RegState) (C : gmap Addr AddrClaim),
      gen_heap_interp lreg ∗ gen_heap_interp (sreg σ) ∗
      gen_heap_interp lmem ∗ gen_heap_interp (shadowtbl σ) ∗
      reg_auth R ∗ addr_alloc_auth C ∗
      ⌜erasure R C σ lreg lmem⌝.

  Global Instance cerise_state_interp_timeless σ : Timeless (cerise_state_interp σ).
  Proof. apply _. Qed.
End state_interp.

(* invariants for memory, and a state interpretation for (mem,reg) *)
Global Instance memG_irisG `{MachineParameters} `{!ceriseG Σ} : irisGS griotte_lang Σ := {
  iris_invGS := cerise_invG;
  state_interp σ _ κs _ := cerise_state_interp σ;
  fork_post _ := True%I;
  num_laters_per_step _ := 0;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.

(* Points to predicates for registers *)
Notation "r ↦ᵣ{ q } w" := (pointsto (L:=RegName) (V:=LWord) r q w)
  (at level 20, q at level 50, format "r  ↦ᵣ{ q }  w") : bi_scope.
Notation "r ↦ᵣ w" := (pointsto (L:=RegName) (V:=LWord) r (DfracOwn 1) w) (at level 20) : bi_scope.
Notation "r ↦ᵣ -" := (∃ w, pointsto (L:=RegName) (V:=LWord) r (DfracOwn 1) w)%I (at level 20) : bi_scope.

(* Points to predicates for system registers *)
Notation "sr ↦ₛᵣ{ q } w" := (pointsto (L:=SRegName) (V:=Word) sr q w)
  (at level 20, q at level 50, format "sr  ↦ₛᵣ{ q }  w") : bi_scope.
Notation "sr ↦ₛᵣ w" := (pointsto (L:=SRegName) (V:=Word) sr (DfracOwn 1) w) (at level 20) : bi_scope.
Notation "sr ↦ₛᵣ -" := (∃ w, pointsto (L:=SRegName) (V:=Word) sr (DfracOwn 1) w)%I (at level 20) : bi_scope.

(* Points to predicates for memory *)
Notation "a ↦ₐ{ q } w" := (pointsto (L:=Addr) (V:=LWord) a q w)
  (at level 20, q at level 50, format "a  ↦ₐ{ q }  w") : bi_scope.
Notation "a ↦ₐ w" := (pointsto (L:=Addr) (V:=LWord) a (DfracOwn 1) w) (at level 20) : bi_scope.
Notation "a ↦ₐ -" := (∃ w, pointsto (L:=Addr) (V:=LWord) a (DfracOwn 1) w)%I (at level 20) : bi_scope.

(* Points to predicates for shadow table *)
Notation "a ↦ₛ{ q } b" := (pointsto (L:=Addr) (V:=AllocStatus) a q b)
  (at level 20, q at level 50, format "a  ↦ₛ{ q }  b") : bi_scope.
Notation "a ↦ₛ b" := (pointsto (L:=Addr) (V:=AllocStatus) a (DfracOwn 1) b) (at level 20) : bi_scope.
Notation "a ↦ₛ -" := (∃ b, pointsto (L:=Addr) (V:=AllocStatus) a (DfracOwn 1) b)%I (at level 20) : bi_scope.

(** * Initialisation of the ghost state

    The logical heaps start without identifiers: the logical registers and
    memory are the physical ones (with [lnull] at [cnull]), the registry is
    empty, and the heap addresses are heap roots on a given set [H] and
    unclaimed elsewhere. *)

Class ceriseGpreS Σ := {
  cerise_preG_mem :: gen_heapGpreS Addr LWord Σ;
  cerise_preG_shadow :: gen_heapGpreS Addr AllocStatus Σ;
  cerise_preG_reg :: gen_heapGpreS RegName LWord Σ;
  cerise_preG_sreg :: gen_heapGpreS SRegName Word Σ;
  cerise_preG_registry :: allocRegistryPreG Σ;
  cerise_preG_addr_alloc :: addrAllocPreG Σ;
}.

Definition ceriseGpreΣ : gFunctors :=
  #[gen_heapΣ Addr LWord; gen_heapΣ Addr AllocStatus; gen_heapΣ RegName LWord;
    gen_heapΣ SRegName Word; allocRegistryΣ; addrAllocΣ].

Global Instance subG_ceriseGpreS {Σ} : subG ceriseGpreΣ Σ → ceriseGpreS Σ.
Proof. solve_inG. Qed.

Section ghost_init.
  Context `{MP : MachineParameters}.

  (** The initial logical registers: the physical ones without identifiers,
      and [lnull] at [cnull]. *)
  Definition init_lregs (regs : Reg) : LReg :=
    match regs !! cnull with
    | Some _ => <[cnull := lnull]> (lword_of_word <$> regs)
    | None => lword_of_word <$> regs
    end.

  Definition init_lmem (m : Mem) : LMem := lword_of_word <$> m.

  (** The initial claims: heap roots on [H], unclaimed elsewhere in the heap. *)
  Definition init_claims (H : gset Addr) : gmap Addr AddrClaim :=
    map_imap (λ a _, Some (if decide (a ∈ H) then HeapRoot else Unclaimed))
      (gset_to_gmap tt heap_addresses).

  (** Every initial word with authority is based on a heap root, heap roots
      are unpainted, and [cnull] holds zero. *)
  Record ghost_init_cond (σ : ExecConf) (H : gset Addr) : Prop := {
    gi_roots_heap a : a ∈ H → is_heap_address a = true;
    gi_roots_unpainted a : a ∈ H → shadowtbl σ !! a = Some ShadowLive;
    gi_shadow a : is_heap_address a = true → is_Some (shadowtbl σ !! a);
    gi_mem a w b : mem σ !! a = Some w → get_tag w = true → heap_authority_base w = Some b → b ∈ H;
    gi_regs r w b : r ≠ cnull → reg σ !! r = Some w → get_tag w = true →
                    heap_authority_base w = Some b → b ∈ H;
    gi_sregs sr w b : sreg σ !! sr = Some w → get_tag w = true →
                      heap_authority_base w = Some b → b ∈ H;
    gi_mmio : mem_avoids_mmio (mem σ);
    gi_cnull w : reg σ !! cnull = Some w → w = WInt 0;
  }.

  Lemma lookup_init_claims H a :
    init_claims H !! a =
      if is_heap_address a then Some (if decide (a ∈ H) then HeapRoot else Unclaimed) else None.
  Proof.
    rewrite /init_claims map_lookup_imap lookup_gset_to_gmap.
    destruct (is_heap_address a) eqn:Ha.
    - rewrite option_guard_True //=. by apply elem_of_heap_addresses.
    - rewrite option_guard_False //=. by rewrite elem_of_heap_addresses Ha.
  Qed.

  Lemma lookup_init_lregs regs r :
    init_lregs regs !! r = if decide (r = cnull) then (λ _, lnull) <$> regs !! r
                           else lword_of_word <$> regs !! r.
  Proof.
    rewrite /init_lregs. destruct (regs !! cnull) eqn:Hc.
    - case_decide as Hr; first subst r.
      + by rewrite lookup_insert_eq Hc.
      + by rewrite lookup_insert_ne // lookup_fmap.
    - case_decide; subst; by rewrite lookup_fmap ?Hc.
  Qed.

  Lemma init_erasure σ H :
    ghost_init_cond σ H →
    erasure ∅ (init_claims H) σ (init_lregs (reg σ)) (init_lmem (mem σ)).
  Proof.
    intros Hinit.
    assert (∀ w, (∀ b, get_tag w = true → heap_authority_base w = Some b → b ∈ H) →
              reg_word_ok ∅ (init_claims H) (lword_of_word w)) as Hok.
    { intros w Hroot. split; first by apply lword_prov_no_id.
      intros b Ht Hab; cbn. rewrite lookup_init_claims.
      assert (is_heap_address b = true) as ->.
      { apply heap_authority_base_memory_cap_bounds in Hab as (? & ? & ? & ?). done. }
      case_decide as Hb; first done. exfalso. apply Hb, Hroot; done. }
    constructor.
    - constructor.
      + intros ι x a Hx. by rewrite lookup_empty in Hx.
      + intros ι x a Hx. by rewrite lookup_empty in Hx.
      + intros ι x a Hx. by rewrite lookup_empty in Hx.
      + intros a. rewrite lookup_init_claims. destruct (is_heap_address a); naive_solver.
      + intros a ι. rewrite lookup_init_claims. split.
        * destruct (is_heap_address a); last done. case_decide; done.
        * intros (x & Hx & _). by rewrite lookup_empty in Hx.
      + intros a. rewrite lookup_init_claims. destruct (is_heap_address a); last done.
        case_decide; last done. intros _. by apply Hinit.
      + apply Hinit.
    - apply map_eq. intros r. rewrite lookup_lregs_erase lookup_init_lregs.
      case_decide as Hr.
      + subst r. destruct (reg σ !! cnull) as [w|] eqn:Hc; last done.
        cbn. by rewrite Hc (gi_cnull _ _ Hinit w Hc).
      + destruct (reg σ !! r) eqn:E; rewrite ?E; done.
    - intros v. rewrite lookup_init_lregs. case_decide; last done. intros Hv.
      apply fmap_Some in Hv as (? & _ & ->). done.
    - intros r v. rewrite lookup_init_lregs. case_decide.
      + intros Hv. apply fmap_Some in Hv as (? & _ & ->). apply reg_word_ok_lnull.
      + intros Hv. apply fmap_Some in Hv as (w & Hw & ->).
        apply Hok. intros b. eapply gi_regs; eauto.
    - intros sr w Hw. apply Hok. intros b. eapply gi_sregs; eauto.
    - by rewrite /init_lmem dom_fmap_L.
    - intros a v pw Hv Hpw. rewrite /init_lmem lookup_fmap Hpw /= in Hv.
      injection Hv as <-.
      apply (reg_word_ok_mem _ _ (lword_of_word pw)), Hok. intros b. eapply gi_mem; eauto.
    - apply Hinit.
  Qed.

  Context `{!ceriseGpreS Σ}.

  (** The generic ghost initialisation of every adequacy theorem. It returns
      the state interpretation, the logical register, system register, memory
      and shadow points-to, and the address claims. *)
  Lemma cerise_ghost_init σ H :
    ghost_init_cond σ H →
    ⊢ |==> ∃ (mg : gen_heapGS Addr LWord Σ) (sg : gen_heapGS Addr AllocStatus Σ)
             (rg : gen_heapGS RegName LWord Σ) (srg : gen_heapGS SRegName Word Σ)
             (regg : allocRegistryG Σ) (ag : addrAllocG Σ),
      cerise_state_interp σ ∗
      ([∗ map] r ↦ w ∈ init_lregs (reg σ), r ↦ᵣ w) ∗
      ([∗ map] sr ↦ w ∈ sreg σ, sr ↦ₛᵣ w) ∗
      ([∗ map] a ↦ w ∈ init_lmem (mem σ), a ↦ₐ w) ∗
      ([∗ map] a ↦ s ∈ shadowtbl σ, a ↦ₛ s) ∗
      ([∗ map] a ↦ c ∈ init_claims H, addr_alloc a c).
  Proof.
    iIntros (Hinit).
    iMod (gen_heap_init (init_lregs (reg σ))) as (rg) "(Hr & Hrs & _)".
    iMod (gen_heap_init (sreg σ)) as (srg) "(Hsr & Hsrs & _)".
    iMod (gen_heap_init (init_lmem (mem σ))) as (mg) "(Hm & Hms & _)".
    iMod (gen_heap_init (shadowtbl σ)) as (sg) "(Hst & Hsts & _)".
    iMod registry_init as (regg) "HR".
    iMod (addr_alloc_init (init_claims H)) as (ag) "[HC HCs]".
    iModIntro. iExists mg, sg, rg, srg, regg, ag. iFrame.
    iPureIntro. by apply init_erasure.
  Qed.

  (** The projection of the initial logical memory onto the physical one. *)
  Lemma init_lmem_pointsto `{!gen_heapGS Addr LWord Σ} (m : Mem) :
    ([∗ map] a ↦ w ∈ init_lmem m, a ↦ₐ w) ⊣⊢ [∗ map] a ↦ w ∈ m, a ↦ₐ lword_of_word w.
  Proof. by rewrite /init_lmem big_sepM_fmap. Qed.
End ghost_init.
