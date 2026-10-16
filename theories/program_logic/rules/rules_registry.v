From iris.proofmode Require Import proofmode.
From griotte Require Export rules_base si_modality.

(** * Ghost steps on the state interpretation

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
    (∀ lpc lreg lmem R C,
       ⌜erasure R C σ lpc lreg lmem⌝ -∗
       gen_heap_interp lreg -∗ gen_heap_interp (sreg σ) -∗ gen_heap_interp lmem -∗
       gen_heap_interp (shadowtbl σ) -∗ reg_auth R -∗ addr_alloc_auth C -∗ P ==∗
       ∃ R' C', ⌜erasure R' C' σ lpc lreg lmem⌝ ∗
         gen_heap_interp lreg ∗ gen_heap_interp (sreg σ) ∗ gen_heap_interp lmem ∗
         gen_heap_interp (shadowtbl σ) ∗ reg_auth R' ∗ addr_alloc_auth C' ∗ Q) →
    cerise_state_interp σ -∗ P ==∗ cerise_state_interp σ ∗ Q.
  Proof.
    iIntros (Hupd) "Hσ HP".
    iDestruct "Hσ" as (lpc lreg lmem R C) "(HPCa & Hr & Hsr & Hm & Hst & HR & HC & %Her)".
    iMod (Hupd with "[//] Hr Hsr Hm Hst HR HC HP")
      as (R' C' Her') "(Hr & Hsr & Hm & Hst & HR & HC & HQ)".
    iModIntro. iFrame "HQ". iExists lpc, lreg, lmem, R', C'. by iFrame.
  Qed.


  (** The same, with the PC authority. *)
  Lemma si_ghost_update_pc σ P Q :
    (∀ lpc lreg lmem R C,
       ⌜erasure R C σ lpc lreg lmem⌝ -∗
       PC_auth lpc -∗
       gen_heap_interp lreg -∗ gen_heap_interp (sreg σ) -∗ gen_heap_interp lmem -∗
       gen_heap_interp (shadowtbl σ) -∗ reg_auth R -∗ addr_alloc_auth C -∗ P ==∗
       ∃ R' C', ⌜erasure R' C' σ lpc lreg lmem⌝ ∗ PC_auth lpc ∗
         gen_heap_interp lreg ∗ gen_heap_interp (sreg σ) ∗ gen_heap_interp lmem ∗
         gen_heap_interp (shadowtbl σ) ∗ reg_auth R' ∗ addr_alloc_auth C' ∗ Q) →
    cerise_state_interp σ -∗ P ==∗ cerise_state_interp σ ∗ Q.
  Proof.
    iIntros (Hupd) "Hσ HP".
    iDestruct "Hσ" as (lpc lreg lmem R C) "(HPCa & Hr & Hsr & Hm & Hst & HR & HC & %Her)".
    iMod (Hupd with "[//] HPCa Hr Hsr Hm Hst HR HC HP")
      as (R' C' Her') "(HPCa & Hr & Hsr & Hm & Hst & HR & HC & HQ)".
    iModIntro. iFrame "HQ". iExists lpc, lreg, lmem, R', C'. by iFrame.
  Qed.

  (** ** Registry transitions *)

  (** [ALive → APainting], given the whole token. *)
  Lemma reg_painting E ι :
    ι ↦st{1} ALive ⊢ |~{E}~> ι ↦st{1} APainting.
  Proof.
    apply si_upd_ghost. intros σ. iApply si_ghost_update.
    iIntros (lpc lreg lmem R C Her) "Hr Hsr Hm Hst HR HC Htok".
    iDestruct (reg_lookup_own with "HR Htok") as %(b & e' & γ & HRι).
    iMod (reg_step _ _ _ _ _ _ APainting with "HR Htok") as "[HR Htok]";
      [done|simpl; lia|].
    iModIntro. iExists _, C. iFrame. iPureIntro.
    eapply erasure_reg_step; eauto; done.
  Qed.

  (** [APainting → AQuar], given the whole token and the painted range. It
      issues the quarantine witness. The whole register file and the PC are
      owned, and none of their words with authority carries [ι] ([cnull]
      always holds the null word). *)
  Lemma reg_quarantine E ι b e' lpc (regs : LReg) :
    (∀ x, is_Some (regs !! x)) →
    (∀ v, (v = lpc ∨ ∃ x, x ≠ cnull ∧ regs !! x = Some v) →
       has_authority v.(lw) → v.(lprov) ≠ Some ι) →
    alloc_obj ι b e' -∗
    ι ↦st{1} APainting -∗
    ([∗ list] a ∈ finz.seq_between b e', a ↦ₛ ShadowQuarantined) -∗
    PC ↦ₚ lpc -∗
    ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    |~{E}~>
      ι ↦st{1} AQuar ∗ ι ⊒ AQuar ∗
      ([∗ list] a ∈ finz.seq_between b e', a ↦ₛ ShadowQuarantined) ∗
      PC ↦ₚ lpc ∗
      [∗ map] k↦y ∈ regs, k ↦ᵣ y.
  Proof.
    iIntros (Hfull Hclean) "#Hobj Htok Hcells HPC Hmap".
    iApply (si_upd_ghost _
      (alloc_obj ι b e' ∗ ι ↦st{1} APainting ∗
       ([∗ list] a ∈ finz.seq_between b e', a ↦ₛ ShadowQuarantined) ∗
       PC ↦ₚ lpc ∗ [∗ map] k↦y ∈ regs, k ↦ᵣ y)%I
      with "[$Hobj $Htok $Hcells $HPC $Hmap]").
    intros σ. iApply si_ghost_update_pc.
    iIntros (lpc' lreg lmem R C Her) "HPCa Hr Hsr Hm Hst HR HC (#Hobj & Htok & Hcells & HPC & Hmap)".
    iDestruct (PC_agree with "HPCa HPC") as %<-.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hincl.
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
    eapply erasure_reg_step; eauto; try done.
    intros _ v Hv Hauth. destruct Hv as [-> | (x & Hx)].
    { apply Hclean; [by left | done]. }
    destruct (decide (x = cnull)) as [->|Hxn].
    { (* [cnull] holds the null word, which has no authority. *)
      destruct Her as [_ _ Hcnull _ _ _ _ _ _ _].
      rewrite (Hcnull _ Hx) in Hauth. by inversion Hauth. }
    apply Hclean; last done.
    right. exists x. split; first done. destruct (Hfull x) as [v' Hv'].
    by rewrite (lookup_weaken _ _ _ _ Hv' Hincl) in Hx; simplify_eq.
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
    iIntros (lpc lreg lmem R C Her) "Hr Hsr Hm Hst HR HC Hcells".
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

  (** ** Observation

      A register word with authority is claimed at its base by its
      identifier while the identifier is not dead, as a status token shows;
      its base is a heap root if it has no identifier. *)
  Lemma observe_claim E r v b c q s :
    get_tag v.(lw) = true → heap_authority_base v.(lw) = Some b → s ≠ ADead →
    r ↦ᵣ v -∗ addr_alloc b c -∗
    (if v.(lprov) is Some ι then ι ↦st{q} s else True) -∗
    |~{E}~>
      r ↦ᵣ v ∗ addr_alloc b c ∗
      (if v.(lprov) is Some ι then ι ↦st{q} s else True) ∗
      ⌜match v.(lprov) with Some ι => c = Claimed ι | None => c = HeapRoot end⌝.
  Proof.
    iIntros (Ht Hab Hs) "Hr Hc Htok".
    iApply (si_upd_ghost _ (r ↦ᵣ v ∗ addr_alloc b c ∗
      (if v.(lprov) is Some ι then ι ↦st{q} s else True))%I with "[$Hr $Hc $Htok]").
    intros σ. iApply si_ghost_update.
    iIntros (lpc lreg lmem R C Her) "Hlr Hsr Hm Hst HR HC (Hr & Hc & Htok)".
    iDestruct (gen_heap_valid with "Hlr Hr") as %Hv.
    iDestruct (addr_alloc_lookup with "HC Hc") as %HCb.
    pose proof (erasure_observe _ _ _ _ _ _ _ _ _ Her Hv Ht Hab) as Hobs.
    destruct (lprov v) as [ι|].
    - iDestruct (reg_lookup_own with "HR Htok") as %(b' & e' & γ & HRι).
      iModIntro. iExists R, C. iFrame. iPureIntro. split; first done.
      destruct Hobs as (x & Hx & HC'). rewrite HRι in Hx. simplify_eq.
      rewrite HC' in HCb; [by simplify_eq | done].
    - iModIntro. iExists R, C. iFrame. iPureIntro. split; first done. congruence.
  Qed.

  (** ** Re-filtering a register

      A register word with authority whose identifier is quarantined or dead
      already has an untagged physical copy: its logical tag can be
      cleared. *)
  Lemma reg_refilter E r v ι :
    has_authority v.(lw) → v.(lprov) = Some ι →
    ι ⊒ AQuar -∗ r ↦ᵣ v -∗ |~{E}~> r ↦ᵣ lclear_tag v.
  Proof.
    iIntros (Hauth Hι) "#Hq Hr".
    iApply (si_upd_ghost _ (r ↦ᵣ v ∗ ι ⊒ AQuar)%I with "[$Hr $Hq]").
    iIntros (σ) "Hσ [Hr #Hq]".
    iDestruct "Hσ" as (lpc lreg lmem R C) "(HPCa & Hlr & Hsr & Hm & Hst & HR & HC & %Her)".
    iDestruct (gen_heap_valid with "Hlr Hr") as %Hv.
    iDestruct (reg_lookup_lb with "HR Hq") as %(b & e & γ & s & HRι & Hs).
    iMod (gen_heap_update with "Hlr Hr") as "[Hlr Hr]".
    iModIntro. iFrame "Hr". iExists lpc, (<[r := lclear_tag v]> lreg), lmem, R, C. iFrame.
    iPureIntro.
    destruct σ as [[[[pc rg] sr] m] st].
    assert (quar_or_dead s) as Hqd.
    { rewrite /quar_or_dead. destruct s; cbn in Hs; try lia; auto. }
    pose proof Her as Her'.
    destruct Her' as [_ [_ Hregs] Hcnull _ _ _ _ _ _ _].
    destruct (Hregs r v Hv) as (w & Hw & Hrel).
    assert (w = clear_tag v.(lw)) as ->.
    { destruct Hrel as [_ Hstrip]. by eapply Hstrip. }
    assert (r ≠ cnull) as Hr.
    { intros ->. rewrite (Hcnull _ Hv) in Hauth. by inversion Hauth. }
    pose proof (erasure_insert_reg _ _ _ _ _ _ _ _ _ _ r (lclear_tag v) (clear_tag v.(lw))
                  Hr Her (reg_word_ok_lclear_tag _ _ _)) as Her_new.
    cbn in Hw. rewrite (insert_id rg) in Her_new; last exact Hw.
    apply Her_new.
    apply reg_phys_untagged. rewrite lw_lclear_tag. apply get_tag_clear_tag.
  Qed.

  (** Every tagged, non-empty register capability with an identifier lies in
      the heap: provenance and the registry's heap clause. *)
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
    iIntros (lpc lreg lmem R C Her) "Hlr Hsr Hm Hst HR HC Hmap".
    iDestruct (gen_heap_valid_inclSepM with "Hlr Hmap") as %Hincl.
    iModIntro. iExists R, C. iFrame. iPureIntro. split; first done.
    intros r v ι b e Hv Ht Hb Hlt Hι x Hx.
    destruct (erasure_reg_word _ _ _ _ _ _ r v Her (lookup_weaken _ _ _ _ Hv Hincl)) as [Hprov _].
    destruct (Hprov ι b e Ht Hb Hlt Hι) as (y & Hy & Hyb & Hye).
    eapply (reg_ok_heap _ _ _ (er_registry _ _ _ _ _ _ Her)); first exact Hy.
    rewrite /re_covers. solve_addr.
  Qed.

End rules_registry.
