From iris.base_logic Require Export invariants na_invariants gen_heap ghost_map ghost_var.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl_auth.
From griotte Require Import griotte_lang.
From griotte Require Export logical_words alloc_registry erasure.
From griotte Require Import named_props_extra.



(* Non atomic invariants *)
Class cerise_na_invs Σ :=
  {
    na_invG :: na_invG Σ;
    cerise_nais : na_inv_pool_name;
  }.
#[export] Hint Mode cerise_na_invs - : typeclass_instances.

(** The logical PC: a single exclusive value, whose authoritative part is in
    the state interpretation. The PC is not a general register. *)
Definition pcUR := excl_authUR (leibnizO LWord).

Class pcG Σ := PcG {
  pc_inG :: inG Σ pcUR;
  pc_name : gname;
}.
#[export] Hint Mode pcG - : typeclass_instances.

Class pcGpreS Σ := { pc_preG_inG :: inG Σ pcUR }.
#[export] Hint Mode pcGpreS - : typeclass_instances.
Definition pcΣ : gFunctors := #[GFunctor pcUR].
#[global] Instance subG_pcGpreS {Σ} : subG pcΣ Σ → pcGpreS Σ.
Proof. solve_inG. Qed.

Section pc_resource.
  Context `{!pcG Σ}.

  Definition PC_auth (lpc : LWord) : iProp Σ := own pc_name (●E (lpc : leibnizO LWord)).
  Definition PC_frag (lpc : LWord) : iProp Σ := own pc_name (◯E (lpc : leibnizO LWord)).

  #[global] Instance PC_auth_timeless lpc : Timeless (PC_auth lpc).
  Proof. apply _. Qed.
  #[global] Instance PC_frag_timeless lpc : Timeless (PC_frag lpc).
  Proof. apply _. Qed.

  Lemma PC_agree lpc lpc' : PC_auth lpc -∗ PC_frag lpc' -∗ ⌜lpc = lpc'⌝.
  Proof.
    iIntros "Ha Hf". iCombine "Ha Hf" gives %Hv.
    by apply excl_auth_agree_L in Hv.
  Qed.

  Lemma PC_update lpc lpc' lpc'' : PC_auth lpc -∗ PC_frag lpc' ==∗ PC_auth lpc'' ∗ PC_frag lpc''.
  Proof.
    iIntros "Ha Hf". iMod (own_update_2 with "Ha Hf") as "[$ $]"; last done.
    apply excl_auth_update.
  Qed.

  Lemma PC_frag_excl lpc lpc' : PC_frag lpc -∗ PC_frag lpc' -∗ False.
  Proof.
    iIntros "H1 H2". iCombine "H1 H2" gives %Hv.
    by apply excl_auth_frag_op_valid in Hv.
  Qed.
End pc_resource.

Lemma PC_init `{!pcGpreS Σ} (lpc : LWord) :
  ⊢ |==> ∃ (pg : pcG Σ), PC_auth lpc ∗ PC_frag lpc.
Proof.
  iMod (own_alloc (●E (lpc : leibnizO LWord) ⋅ ◯E (lpc : leibnizO LWord))) as (γ) "[Ha Hf]".
  { apply excl_auth_valid. }
  iModIntro. iExists (PcG _ _ γ). iFrame.
Qed.

(** The trap vector: the word that MTCC holds in every state, the
    capability of the exception entry stub. It is tagged, so a fault never
    stops the machine. *)
Class trapVector := {
  mtcc_vec : Word;
  mtcc_vec_tagged : get_tag mtcc_vec = true;
}.
(* No [Hint Mode]: the class has no parameter, hence no input position. *)

(* CMRA for Cerise. The PC, registers, system registers and memory hold
   logical words. *)
Class ceriseG Σ :=
  CeriseG {
      cerise_invG : invGS Σ;
      cerise_nainvG :: cerise_na_invs Σ;
      mem_gen_memG :: gen_heapGS Addr LWord Σ; (* memory *)
      shadowtbl_gen_regG :: gen_heapGS Addr AllocStatus Σ; (* shadow table *)
      cerise_pcG :: pcG Σ; (* PC *)
      reg_gen_regG :: gen_heapGS RegName LWord Σ; (* register *)
      sreg_gen_regG :: gen_heapGS SRegName LWord Σ; (* system register *)
      cerise_registryG :: allocRegistryG Σ; (* allocation registry *)
      cerise_addr_allocG :: addrAllocG Σ; (* address claims *)
      cerise_trapVector :: trapVector (* trap vector *)
    }.
#[export] Hint Mode ceriseG - : typeclass_instances.

(** The namespace of the non-atomic token of trap entry: a fault hands it
    to the state interpretation, in exchange for MEPCC and mcause. *)
Definition N_trap : namespace := nroot .@ "trap_entry".

(** The state interpretation: the logical PC, registers, system registers and
    memory, the physical shadow table, the registry and the address claims,
    related to the machine state by erasure. *)
Section state_interp.
  Context `{MP : MachineParameters}.
  Context `{!pcG Σ,
            !gen_heapGS RegName LWord Σ, !gen_heapGS SRegName LWord Σ,
            !gen_heapGS Addr LWord Σ, !gen_heapGS Addr AllocStatus Σ,
            !allocRegistryG Σ, !addrAllocG Σ, !trapVector, !cerise_na_invs Σ}.

  (** The only points-to of the system registers that no client holds:
      mstatus, the registers trap entry writes (MEPCC, mcause, mtval) and
      MTCC, which holds the trap vector [mtcc_vec]. MEPCC and mcause are
      held here, or lent to the code after trap entry, in which case the
      state interpretation holds the trap-entry token instead. mtval holds
      an integer. *)
  Definition sreg_reserved : iProp Σ :=
    "Hmstatus" ∷ (∃ v, pointsto (L:=SRegName) (V:=LWord) MSTATUS (DfracOwn 1) v) ∗
    "Hwin" ∷ (((∃ v, pointsto (L:=SRegName) (V:=LWord) MEPCC (DfracOwn 1) v) ∗
               (∃ v, pointsto (L:=SRegName) (V:=LWord) MCAUSE (DfracOwn 1) v)) ∨
              na_own cerise_nais (↑N_trap)) ∗
    "Hmtval" ∷ (∃ z : Z, pointsto (L:=SRegName) (V:=LWord) MTVAL (DfracOwn 1)
                           (lword_of_word (WInt z))) ∗
    "Hmtcc" ∷ pointsto (L:=SRegName) (V:=LWord) MTCC (DfracOwn 1) (lword_of_word mtcc_vec).

  (** The logical system registers, with the reserved points-to. *)
  Definition sreg_interp (lsreg : LSReg) : iProp Σ :=
    gen_heap_interp lsreg ∗ sreg_reserved.

  Lemma sreg_interp_update_mstatus lsreg v :
    sreg_interp lsreg ==∗ sreg_interp (<[MSTATUS := v]> lsreg).
  Proof.
    iIntros "[Hsr Hres]". iNamed "Hres". iDestruct "Hmstatus" as (v0) "Hmstatus".
    iMod (gen_heap_update _ _ _ v with "Hsr Hmstatus") as "[$ Hmstatus]".
    iModIntro. iFrame.
  Qed.

  Lemma sreg_interp_mstatus lsreg :
    sreg_interp lsreg -∗ ⌜∃ v, lsreg !! MSTATUS = Some v⌝.
  Proof.
    iIntros "[Hsr Hres]". iNamed "Hres". iDestruct "Hmstatus" as (v) "Hmstatus".
    iDestruct (gen_heap_valid with "Hsr Hmstatus") as %Hlookup. eauto.
  Qed.

  (** MTCC holds the trap vector. *)
  Lemma sreg_interp_mtcc lsreg :
    sreg_interp lsreg -∗ ⌜lsreg !! MTCC = Some (lword_of_word mtcc_vec)⌝.
  Proof.
    iIntros "[Hsr Hres]". iNamed "Hres".
    iDestruct (gen_heap_valid with "Hsr Hmtcc") as %Hlookup. eauto.
  Qed.

  Definition cerise_state_interp (σ : ExecConf) : iProp Σ :=
    ∃ (lpc : LWord) (lreg : LReg) (lsreg : LSReg) (lmem : LMem) (R : RegState)
      (C : gmap Addr AddrClaim),
      "HPCa" ∷ PC_auth lpc ∗
      "Hr" ∷ gen_heap_interp lreg ∗
      "Hsr" ∷ sreg_interp lsreg ∗
      "Hm" ∷ gen_heap_interp lmem ∗
      "Hst" ∷ gen_heap_interp (shadowtbl σ) ∗
      "HR" ∷ reg_auth R ∗
      "HC" ∷ addr_alloc_auth C ∗
      "%Her" ∷ ⌜erasure R C σ lpc lreg lsreg lmem⌝.

  #[global] Instance cerise_state_interp_timeless σ : Timeless (cerise_state_interp σ).
  Proof. apply _. Qed.
End state_interp.

(* invariants for memory, and a state interpretation for (mem,reg) *)
#[global] Instance memG_irisG `{MachineParameters} `{!ceriseG Σ} : irisGS griotte_lang Σ := {
  iris_invGS := cerise_invG;
  state_interp σ _ κs _ := cerise_state_interp σ;
  fork_post _ := True%I;
  num_laters_per_step _ := 0;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.

(* Points to predicate for the PC *)
Notation "'PC' ↦ₚ w" := (PC_frag w) (at level 20, format "'PC'  ↦ₚ  w") : bi_scope.

(* Points to predicates for registers *)
Notation "r ↦ᵣ{ q } w" := (pointsto (L:=RegName) (V:=LWord) r q w)
  (at level 20, q at level 50, format "r  ↦ᵣ{ q }  w") : bi_scope.
Notation "r ↦ᵣ w" := (pointsto (L:=RegName) (V:=LWord) r (DfracOwn 1) w) (at level 20) : bi_scope.
Notation "r ↦ᵣ -" := (∃ w, pointsto (L:=RegName) (V:=LWord) r (DfracOwn 1) w)%I (at level 20) : bi_scope.

(* Points to predicates for system registers *)
Notation "sr ↦ₛᵣ{ q } w" := (pointsto (L:=SRegName) (V:=LWord) sr q w)
  (at level 20, q at level 50, format "sr  ↦ₛᵣ{ q }  w") : bi_scope.
Notation "sr ↦ₛᵣ w" := (pointsto (L:=SRegName) (V:=LWord) sr (DfracOwn 1) w) (at level 20) : bi_scope.
Notation "sr ↦ₛᵣ -" := (∃ w, pointsto (L:=SRegName) (V:=LWord) sr (DfracOwn 1) w)%I (at level 20) : bi_scope.

(* Points to predicates for memory *)
Notation "a ↦ₐ{ q } w" := (pointsto (L:=Addr) (V:=LWord) a q w)
  (at level 20, q at level 50, format "a  ↦ₐ{ q }  w") : bi_scope.
Notation "a ↦ₐ w" := (pointsto (L:=Addr) (V:=LWord) a (DfracOwn 1) w) (at level 20) : bi_scope.
Notation "a ↦ₐ -" := (∃ w, pointsto (L:=Addr) (V:=LWord) a (DfracOwn 1) w)%I (at level 20) : bi_scope.
Notation "a ↦ₐ□ w" := (pointsto (L:=Addr) (V:=LWord) a DfracDiscarded w)
  (at level 20, format "a  ↦ₐ□  w") : bi_scope.

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
  cerise_preG_pc :: pcGpreS Σ;
  cerise_preG_reg :: gen_heapGpreS RegName LWord Σ;
  cerise_preG_sreg :: gen_heapGpreS SRegName LWord Σ;
  cerise_preG_registry :: allocRegistryPreG Σ;
  cerise_preG_addr_alloc :: addrAllocPreG Σ;
}.
#[export] Hint Mode ceriseGpreS - : typeclass_instances.

Definition ceriseGpreΣ : gFunctors :=
  #[gen_heapΣ Addr LWord; gen_heapΣ Addr AllocStatus; pcΣ; gen_heapΣ RegName LWord;
    gen_heapΣ SRegName LWord; allocRegistryΣ; addrAllocΣ].

#[global] Instance subG_ceriseGpreS {Σ} : subG ceriseGpreΣ Σ → ceriseGpreS Σ.
Proof. solve_inG. Qed.

(** The system registers that the state interpretation reserves. *)
Definition reserved_sregs : list SRegName := [MSTATUS; MEPCC; MCAUSE; MTVAL; MTCC].

(** The system registers that adequacy hands out: those not reserved. *)
Definition sregs_handed_out (sr : SReg) : SReg :=
  delete MTCC (delete MTVAL (delete MCAUSE (delete MEPCC (delete MSTATUS sr)))).

Lemma lookup_sregs_handed_out_mtdc (sr : SReg) w :
  sr !! MTDC = Some w → sregs_handed_out sr !! MTDC = Some w.
Proof. intros Hw. by rewrite /sregs_handed_out !lookup_delete_ne. Qed.

Section ghost_init.
  Context `{MP : MachineParameters, TV : !trapVector}.

  (** The initial logical registers: the physical ones without identifiers,
      and [lnull] at [cnull]. *)
  Definition init_lregs (regs : Reg) : LReg :=
    match regs !! cnull with
    | Some _ => <[cnull := lnull]> (lword_of_word <$> regs)
    | None => lword_of_word <$> regs
    end.

  Definition init_lmem (m : Mem) : LMem := lword_of_word <$> m.

  Definition init_lsregs (sregs : SReg) : LSReg := lword_of_word <$> sregs.

  (** The initial claims: heap roots on [H], unclaimed elsewhere in the heap. *)
  Definition init_claims (H : gset Addr) : gmap Addr AddrClaim :=
    map_imap (λ a _, Some (if decide (a ∈ H) then HeapRoot else Unclaimed))
      (gset_to_gmap tt heap_addresses).

  (** Every initial word with authority is based on a heap root, heap roots
      are unpainted, [cnull] holds zero, and every tagged executable word
      has closed bounds that avoid the heap; a tagged PC, MTCC or MEPCC is an
      unsealed executable capability; the system registers that the state
      interpretation reserves exist, MTCC holds the trap vector and mtval an
      integer. *)
  Record ghost_init_cond (σ : ExecConf) (H : gset Addr) : Prop := {
    gi_roots_heap a : a ∈ H → is_heap_address a = true;
    gi_roots_unpainted a : a ∈ H → shadowtbl σ !! a = Some ShadowLive;
    gi_shadow a : is_heap_address a = true → is_Some (shadowtbl σ !! a);
    gi_mem a w b : mem σ !! a = Some w → get_tag w = true → heap_authority_base w = Some b → b ∈ H;
    gi_pc b : get_tag (pcc σ) = true → heap_authority_base (pcc σ) = Some b → b ∈ H;
    gi_regs r w b : r ≠ cnull → reg σ !! r = Some w → get_tag w = true →
                    heap_authority_base w = Some b → b ∈ H;
    gi_sregs sr w b : sreg σ !! sr = Some w → get_tag w = true →
                      heap_authority_base w = Some b → b ∈ H;
    gi_mmio : mem_avoids_mmio (mem σ);
    gi_cnull w : reg σ !! cnull = Some w → w = WInt 0;
    gi_mem_exec a w : mem σ !! a = Some w → lword_exec (lword_of_word w);
    gi_pc_exec : lword_exec (lword_of_word (pcc σ));
    gi_regs_exec r w : reg σ !! r = Some w → lword_exec (lword_of_word w);
    gi_sregs_exec sr w : sreg σ !! sr = Some w → lword_exec (lword_of_word w);
    gi_pc_ok : pc_ok (pcc σ);
    gi_sregs_pc_ok sr w : is_pc_sreg sr = true → sreg σ !! sr = Some w → pc_ok w;
    gi_reserved_sregs sr : sr ∈ reserved_sregs → is_Some (sreg σ !! sr);
    gi_mtcc : sreg σ !! MTCC = Some mtcc_vec;
    gi_mtval : ∃ z, sreg σ !! MTVAL = Some (WInt z);
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
    erasure ∅ (init_claims H) σ (lword_of_word (pcc σ)) (init_lregs (reg σ))
      (init_lsregs (sreg σ)) (init_lmem (mem σ)).
  Proof.
    intros Hinit.
    assert (∀ w, (∀ b, get_tag w = true → heap_authority_base w = Some b → b ∈ H) →
              lword_exec (lword_of_word w) →
              reg_word_ok ∅ (init_claims H) (lword_of_word w)) as Hok.
    { intros w Hroot Hexec. split; first by apply lword_prov_no_id. split; last done.
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
    - split.
      + apply set_eq. intros r. rewrite !elem_of_dom lookup_init_lregs.
        case_decide; by rewrite fmap_is_Some.
      + intros r v. rewrite lookup_init_lregs. case_decide as Hr.
        * subst r. intros Hv. apply fmap_Some in Hv as (w & Hc & ->).
          exists w. split; first done. rewrite (gi_cnull _ _ Hinit w Hc). apply reg_phys_lnull.
        * intros Hv. apply fmap_Some in Hv as (w & Hw & ->).
          exists w. split; first done. apply reg_phys_lword_of_word.
    - intros v. rewrite lookup_init_lregs. case_decide; last done. intros Hv.
      apply fmap_Some in Hv as (? & _ & ->). done.
    - intros r v. rewrite lookup_init_lregs. case_decide.
      + intros Hv. apply fmap_Some in Hv as (? & _ & ->). apply reg_word_ok_lnull.
      + intros Hv. apply fmap_Some in Hv as (w & Hw & ->).
        apply Hok; last by eapply gi_regs_exec. intros b. eapply gi_regs; eauto.
    - intros sr v. rewrite /init_lsregs lookup_fmap. intros Hv.
      apply fmap_Some in Hv as (w & Hw & ->).
      exists w. split; first done. apply reg_phys_lword_of_word.
    - intros sr v. rewrite /init_lsregs lookup_fmap. intros Hv.
      apply fmap_Some in Hv as (w & Hw & ->).
      apply Hok; last by eapply gi_sregs_exec. intros b. eapply gi_sregs; eauto.
    - intros sr v _. rewrite /init_lsregs lookup_fmap. intros Hv _.
      by apply fmap_Some in Hv as (w & Hw & ->).
    - intros sr v Hsr. rewrite /init_lsregs lookup_fmap. intros Hv.
      apply fmap_Some in Hv as (w & Hw & ->). by eapply gi_sregs_pc_ok.
    - by rewrite /init_lmem dom_fmap_L.
    - intros a v pw Hv Hpw. rewrite /init_lmem lookup_fmap Hpw /= in Hv.
      injection Hv as <-.
      apply (reg_phys_mem_word_ok _ _ (lword_of_word pw)); last apply reg_phys_lword_of_word.
      apply Hok; last by eapply gi_mem_exec.
      intros b. eapply gi_mem; eauto.
    - apply Hinit.
    - apply reg_phys_lword_of_word.
    - apply Hok; last by apply (gi_pc_exec _ _ Hinit). intros b. by apply gi_pc.
    - apply Hinit.
  Qed.

  Context `{!ceriseGpreS Σ, !cerise_na_invs Σ}.

  (** The generic ghost initialisation of every adequacy theorem. It returns
      the state interpretation, the logical PC, register, system register,
      memory and shadow points-to, and the address claims. *)
  Lemma cerise_ghost_init σ H :
    ghost_init_cond σ H →
    ⊢ |==> ∃ (mg : gen_heapGS Addr LWord Σ) (sg : gen_heapGS Addr AllocStatus Σ)
             (pg : pcG Σ)
             (rg : gen_heapGS RegName LWord Σ) (srg : gen_heapGS SRegName LWord Σ)
             (regg : allocRegistryG Σ) (ag : addrAllocG Σ),
      cerise_state_interp σ ∗
      PC ↦ₚ lword_of_word (pcc σ) ∗
      ([∗ map] r ↦ w ∈ init_lregs (reg σ), r ↦ᵣ w) ∗
      ([∗ map] sr ↦ w ∈ sregs_handed_out (sreg σ), sr ↦ₛᵣ lword_of_word w) ∗
      ([∗ map] a ↦ w ∈ init_lmem (mem σ), a ↦ₐ w) ∗
      ([∗ map] a ↦ s ∈ shadowtbl σ, a ↦ₛ s) ∗
      ([∗ map] a ↦ c ∈ init_claims H, addr_alloc a c).
  Proof.
    iIntros (Hinit).
    iMod (PC_init (lword_of_word (pcc σ))) as (pg) "[Hpc Hpcs]".
    iMod (gen_heap_init (init_lregs (reg σ))) as (rg) "(Hr & Hrs & _)".
    iMod (gen_heap_init (init_lsregs (sreg σ))) as (srg) "(Hsr & Hsrs & _)".
    iMod (gen_heap_init (init_lmem (mem σ))) as (mg) "(Hm & Hms & _)".
    iMod (gen_heap_init (shadowtbl σ)) as (sg) "(Hst & Hsts & _)".
    iMod registry_init as (regg) "HR".
    iMod (addr_alloc_init (init_claims H)) as (ag) "[HC HCs]".
    iModIntro. iExists mg, sg, pg, rg, srg, regg, ag.
    rewrite /init_lsregs big_sepM_fmap.
    destruct (gi_reserved_sregs _ _ Hinit MSTATUS) as [wst Hwst]; first set_solver.
    destruct (gi_reserved_sregs _ _ Hinit MEPCC) as [wepcc Hwepcc]; first set_solver.
    destruct (gi_reserved_sregs _ _ Hinit MCAUSE) as [wcause Hwcause]; first set_solver.
    destruct (gi_mtval _ _ Hinit) as [ztval Hwtval].
    pose proof (gi_mtcc _ _ Hinit) as Hwtcc.
    iDestruct (big_sepM_delete _ _ MSTATUS with "Hsrs") as "[Hmstatus Hsrs]"; first exact Hwst.
    iDestruct (big_sepM_delete _ _ MEPCC with "Hsrs") as "[Hmepcc Hsrs]";
      first by rewrite lookup_delete_ne.
    iDestruct (big_sepM_delete _ _ MCAUSE with "Hsrs") as "[Hmcause Hsrs]";
      first by rewrite !lookup_delete_ne.
    iDestruct (big_sepM_delete _ _ MTVAL with "Hsrs") as "[Hmtval Hsrs]";
      first by rewrite !lookup_delete_ne.
    iDestruct (big_sepM_delete _ _ MTCC with "Hsrs") as "[Hmtcc Hsrs]";
      first by rewrite !lookup_delete_ne.
    iAssert (sreg_interp (lword_of_word <$> sreg σ))
      with "[Hsr Hmstatus Hmepcc Hmcause Hmtval Hmtcc]" as "Hsr".
    { iFrame "Hsr Hmstatus Hmtval Hmtcc". iLeft. iFrame "Hmepcc Hmcause". }
    iFrame. iPureIntro. by apply init_erasure.
  Qed.

  (** The projection of the initial logical memory onto the physical one. *)
  Lemma init_lmem_pointsto `{!gen_heapGS Addr LWord Σ} (m : Mem) :
    ([∗ map] a ↦ w ∈ init_lmem m, a ↦ₐ w) ⊣⊢ [∗ map] a ↦ w ∈ m, a ↦ₐ lword_of_word w.
  Proof. by rewrite /init_lmem big_sepM_fmap. Qed.
End ghost_init.
