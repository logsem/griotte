From iris.proofmode Require Import proofmode.
From griotte Require Export rules_base si_modality.

(** * Ghost steps on the state interpretation (§4.5)

    The registry and the address claims live in the state interpretation,
    so every change to them, and every observation of them, needs it. They
    are stated with the state-interpretation update modality [|~{E}~> P]
    (after Iris MR 1172), which [iMod] eliminates under the WP of any
    expression that is not a value. The [wp_*] forms are corollaries. *)

Section rules_registry.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ}.
  Implicit Types P Q : iProp Σ.

  (** Opens the state interpretation for a ghost update that keeps the
      physical state. *)
  Lemma si_ghost_update σ P Q :
    (∀ lreg lmem R C,
       ⌜erasure R C σ lreg lmem⌝ -∗
       gen_heap_interp lreg -∗ gen_heap_interp (sreg σ) -∗ gen_heap_interp lmem -∗
       gen_heap_interp (shadowtbl σ) -∗ reg_auth R -∗ addr_alloc_auth C -∗ P ==∗
       ∃ R' C', ⌜erasure R' C' σ lreg lmem⌝ ∗
         gen_heap_interp lreg ∗ gen_heap_interp (sreg σ) ∗ gen_heap_interp lmem ∗
         gen_heap_interp (shadowtbl σ) ∗ reg_auth R' ∗ addr_alloc_auth C' ∗ Q) →
    cerise_state_interp σ -∗ P ==∗ cerise_state_interp σ ∗ Q.
  Proof.
    iIntros (Hupd) "Hσ HP".
    iDestruct "Hσ" as (lreg lmem R C) "(Hr & Hsr & Hm & Hst & HR & HC & %Her)".
    iMod (Hupd with "[//] Hr Hsr Hm Hst HR HC HP")
      as (R' C' Her') "(Hr & Hsr & Hm & Hst & HR & HC & HQ)".
    iModIntro. iFrame "HQ". iExists lreg, lmem, R', C'. by iFrame.
  Qed.


  (** ** Registry transitions *)

  (** [ALive → APainting], given the whole token. *)
  Lemma reg_painting E ι :
    ι ↦st{1} ALive ⊢ |~{E}~> ι ↦st{1} APainting.
  Proof.
    apply si_upd_ghost. intros σ. iApply si_ghost_update.
    iIntros (lreg lmem R C Her) "Hr Hsr Hm Hst HR HC Htok".
    iDestruct (reg_lookup_own with "HR Htok") as %(b & e' & γ & HRι).
    iMod (reg_step _ _ _ _ _ _ APainting with "HR Htok") as "[HR Htok]";
      [done|simpl; lia|].
    iModIntro. iExists _, C. iFrame. iPureIntro.
    eapply erasure_reg_step; eauto; done.
  Qed.

  Lemma wp_reg_painting E e Φ ι :
    to_val e = None →
    ι ↦st{1} ALive -∗
    (ι ↦st{1} APainting -∗ WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros (He) "Htok Hwp". iMod (reg_painting with "Htok") as "Htok".
    by iApply "Hwp".
  Qed.

  (** [APainting → AQuar], given the whole token and the painted range. It
      issues the quarantine witness. *)
  Lemma reg_quarantine E ι b e' :
    alloc_obj ι b e' -∗
    ι ↦st{1} APainting -∗
    ([∗ list] a ∈ finz.seq_between b e', a ↦ₛ ShadowQuarantined) -∗
    |~{E}~>
      ι ↦st{1} AQuar ∗ ι ⊒ AQuar ∗
      [∗ list] a ∈ finz.seq_between b e', a ↦ₛ ShadowQuarantined.
  Proof.
    iIntros "#Hobj Htok Hcells".
    iApply (si_upd_ghost _
      (alloc_obj ι b e' ∗ ι ↦st{1} APainting ∗
       [∗ list] a ∈ finz.seq_between b e', a ↦ₛ ShadowQuarantined)%I
      with "[$Hobj $Htok $Hcells]").
    intros σ. iApply si_ghost_update.
    iIntros (lreg lmem R C Her) "Hr Hsr Hm Hst HR HC (#Hobj & Htok & Hcells)".
    iDestruct (reg_lookup_own with "HR Htok") as %(b1 & e1 & γ & HRι).
    iDestruct (reg_lookup_obj with "HR Hobj") as %(γ' & s & HRι').
    rewrite HRι in HRι'. simplify_eq.
    iAssert (⌜∀ a, (b <= a < e')%a → shadowtbl σ !! a = Some ShadowQuarantined⌝)%I
      as %Hpainted.
    { iIntros (a Ha).
      iDestruct (big_sepL_elem_of with "Hcells") as "Hc".
      { by apply elem_of_finz_seq_between. }
      iApply (gen_heap_valid with "Hst Hc"). }
    iMod (reg_step _ _ _ _ _ _ AQuar with "HR Htok") as "[HR Htok]";
      [done|simpl; lia|].
    iDestruct (st_lb_get with "Htok") as "#Hq".
    iModIntro. iExists _, C. iFrame "∗#". iPureIntro.
    eapply erasure_reg_step; eauto; done.
  Qed.

  Lemma wp_reg_quarantine E e Φ ι b e' :
    to_val e = None →
    alloc_obj ι b e' -∗
    ι ↦st{1} APainting -∗
    ([∗ list] a ∈ finz.seq_between b e', a ↦ₛ ShadowQuarantined) -∗
    (ι ↦st{1} AQuar -∗ ι ⊒ AQuar -∗
     ([∗ list] a ∈ finz.seq_between b e', a ↦ₛ ShadowQuarantined) -∗
     WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros (He) "Hobj Htok Hcells Hwp".
    iMod (reg_quarantine with "Hobj Htok Hcells") as "(Htok & Hq & Hcells)".
    iApply ("Hwp" with "Htok Hq Hcells").
  Qed.

  (** ** Allocation (strong, with a freshness set) *)

  Lemma lookup_claim_range (C : gmap Addr AddrClaim) (l : list Addr) (c : AddrClaim) a :
    (list_to_map ((λ a, (a, c)) <$> l) ∪ C) !! a =
      if decide (a ∈ l) then Some c else C !! a.
  Proof.
    rewrite lookup_union. case_decide as Ha.
    - rewrite (elem_of_list_to_map_1' _ a c).
      + by destruct (C !! a).
      + intros y (x & Hx & _)%list_elem_of_fmap. by simplify_eq.
      + apply list_elem_of_fmap. eauto.
    - rewrite not_elem_of_list_to_map_1.
      + by destruct (C !! a).
      + rewrite -list_fmap_compose. intros (x & Hxa & Hx)%list_elem_of_fmap.
        cbn in Hxa. by subst.
  Qed.

  (** Allocates a fresh identifier [ι ∉ S] over cells that are unclaimed and
      unpainted; they become claimed by [ι]. *)
  Lemma reg_alloc E b e' (S : gset AId) :
    ([∗ list] a ∈ finz.seq_between b e', a ↦ₛ ShadowLive ∗ addr_alloc a Unclaimed) ⊢
    |~{E}~> ∃ ι, ⌜ι ∉ S⌝ ∗ alloc_obj ι b e' ∗ ι ↦st{1} ALive ∗
      [∗ list] a ∈ finz.seq_between b e', a ↦ₛ ShadowLive ∗ addr_alloc a (Claimed ι).
  Proof.
    apply si_upd_ghost. intros σ. iApply si_ghost_update.
    iIntros (lreg lmem R C Her) "Hr Hsr Hm Hst HR HC Hcells".
    set (ι := fresh (dom R ∪ S)).
    assert (ι ∉ dom R ∪ S) as Hfresh by apply is_fresh.
    assert (R !! ι = None) as HRι by (apply not_elem_of_dom; set_solver).
    rewrite big_sepL_sep. iDestruct "Hcells" as "[Hsh Hcl]".
    iAssert (⌜∀ a, a ∈ finz.seq_between b e' → shadowtbl σ !! a = Some ShadowLive⌝)%I as %Hlive.
    { iIntros (a Ha). iDestruct (big_sepL_elem_of with "Hsh") as "Hc"; first exact Ha.
      iApply (gen_heap_valid with "Hst Hc"). }
    iDestruct (addr_alloc_lookup_list _ _ (λ _, Unclaimed) with "HC Hcl") as %Hun.
    iMod (reg_alloc R ι b e' with "HR") as (γ) "(HR & Hobj & Htok)"; first done.
    iMod (addr_alloc_update_list _ _ (λ _, Unclaimed) (λ _, Claimed ι) with "HC Hcl") as "[HC Hcl]".
    iModIntro. iExists _, _. iFrame "Hr Hsr Hm Hst HR HC". iSplit.
    - iPureIntro. eapply erasure_alloc; eauto.
      + intros a Ha%elem_of_finz_seq_between. split; [by apply Hun | by apply Hlive].
      + intros a. rewrite lookup_claim_range.
        repeat case_decide; try done; exfalso.
        * by rewrite elem_of_finz_seq_between in H.
        * by apply H, elem_of_finz_seq_between.
    - iExists ι. iFrame. iSplit; first (iPureIntro; set_solver).
      rewrite big_sepL_sep. iFrame.
  Qed.

  Lemma wp_reg_alloc E e Φ b e' (S : gset AId) :
    to_val e = None →
    ([∗ list] a ∈ finz.seq_between b e', a ↦ₛ ShadowLive ∗ addr_alloc a Unclaimed) -∗
    (∀ ι, ⌜ι ∉ S⌝ -∗ alloc_obj ι b e' -∗ ι ↦st{1} ALive -∗
       ([∗ list] a ∈ finz.seq_between b e', a ↦ₛ ShadowLive ∗ addr_alloc a (Claimed ι)) -∗
       WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros (He) "Hcells Hwp".
    iMod (reg_alloc _ _ _ S with "Hcells") as (ι HιS) "(Hobj & Htok & Hcells)".
    iApply ("Hwp" with "[//] Hobj Htok Hcells").
  Qed.

  (** ** Observation (D18)

      A register word with authority is not dead, and its base is claimed by
      its identifier, or is a heap root if it has none. *)
  Lemma observe_dead E r v ι :
    has_authority v.(lw) → v.(lprov) = Some ι →
    r ↦ᵣ v -∗ ι ⊒ ADead -∗ |~{E}~> False.
  Proof.
    iIntros ([Ht [b Hab]] Hι) "Hr #Hd".
    iApply (si_upd_ghost _ (r ↦ᵣ v ∗ ι ⊒ ADead) with "[$Hr $Hd]").
    intros σ. iApply si_ghost_update.
    iIntros (lreg lmem R C Her) "Hlr Hsr Hm Hst HR HC [Hr Hd]".
    iDestruct (gen_heap_valid with "Hlr Hr") as %Hv.
    pose proof (erasure_observe _ _ _ _ _ _ _ _ Her Hv Ht Hab) as Hobs.
    rewrite Hι in Hobs. destruct Hobs as (x & Hx & Hnd & _).
    iDestruct (reg_lookup_lb with "HR Hd") as %(b' & e' & γ & s & HRι & Hle).
    rewrite Hx in HRι. simplify_eq. destruct s; cbn in Hle, Hnd; try lia; done.
  Qed.

  Lemma wp_observe_dead E e Φ r v ι :
    to_val e = None →
    has_authority v.(lw) → v.(lprov) = Some ι →
    r ↦ᵣ v -∗ ι ⊒ ADead -∗ WP e @ E {{ Φ }}.
  Proof.
    iIntros (He Ha Hι) "Hr Hd". by iMod (observe_dead _ _ _ _ Ha Hι with "Hr Hd") as "[]".
  Qed.

  Lemma observe_claim E r v b c :
    get_tag v.(lw) = true → heap_authority_base v.(lw) = Some b →
    r ↦ᵣ v -∗ addr_alloc b c -∗
    |~{E}~>
      r ↦ᵣ v ∗ addr_alloc b c ∗
      ⌜match v.(lprov) with Some ι => c = Claimed ι | None => c = HeapRoot end⌝.
  Proof.
    iIntros (Ht Hab) "Hr Hc".
    iApply (si_upd_ghost _ (r ↦ᵣ v ∗ addr_alloc b c) with "[$Hr $Hc]").
    intros σ. iApply si_ghost_update.
    iIntros (lreg lmem R C Her) "Hlr Hsr Hm Hst HR HC [Hr Hc]".
    iDestruct (gen_heap_valid with "Hlr Hr") as %Hv.
    iDestruct (addr_alloc_lookup with "HC Hc") as %HCb.
    pose proof (erasure_observe _ _ _ _ _ _ _ _ Her Hv Ht Hab) as Hobs.
    iModIntro. iExists R, C. iFrame. iPureIntro. split; first done.
    destruct (lprov v) as [ι|].
    - destruct Hobs as (_ & _ & _ & HC'). congruence.
    - congruence.
  Qed.

  Lemma wp_observe_claim E e Φ r v b c :
    to_val e = None →
    get_tag v.(lw) = true → heap_authority_base v.(lw) = Some b →
    r ↦ᵣ v -∗ addr_alloc b c -∗
    (r ↦ᵣ v -∗ addr_alloc b c -∗
     ⌜match v.(lprov) with Some ι => c = Claimed ι | None => c = HeapRoot end⌝ -∗
     WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros (He Ht Hab) "Hr Hc Hwp".
    iMod (observe_claim _ _ _ _ _ Ht Hab with "Hr Hc") as "(Hr & Hc & %H)".
    iApply ("Hwp" with "Hr Hc [//]").
  Qed.

  (** Every tagged, non-empty register capability with an identifier lies in
      the heap: provenance and the registry's heap clause (§4.3). *)
  Definition regs_prov_heap (regs : LReg) : Prop :=
    ∀ r v ι b e, regs !! r = Some v →
      get_tag v.(lw) = true → memory_cap_bounds v.(lw) = Some (b, e) → (b < e)%a →
      v.(lprov) = Some ι → ∀ x, (b <= x < e)%a → is_heap_address x = true.

  Lemma observe_regs_prov_heap E (regs : LReg) :
    ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    |~{E}~> ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗ ⌜regs_prov_heap regs⌝.
  Proof.
    iIntros "Hmap".
    iApply (si_upd_ghost _ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) with "Hmap").
    intros σ. iApply si_ghost_update.
    iIntros (lreg lmem R C Her) "Hlr Hsr Hm Hst HR HC Hmap".
    iDestruct (gen_heap_valid_inclSepM with "Hlr Hmap") as %Hincl.
    iModIntro. iExists R, C. iFrame. iPureIntro. split; first done.
    intros r v ι b e Hv Ht Hb Hlt Hι x Hx.
    destruct (erasure_reg_word _ _ _ _ _ r v Her (lookup_weaken _ _ _ _ Hv Hincl)) as [Hprov _].
    destruct (Hprov ι b e Ht Hb Hlt Hι) as (y & Hy & Hyb & Hye).
    eapply (reg_ok_heap _ _ _ (er_registry _ _ _ _ _ Her)); first exact Hy.
    rewrite /re_covers. solve_addr.
  Qed.

End rules_registry.
