From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From cap_machine Require Import monotone.
From cap_machine Require Import region_invariants_revocation region_invariants_allocation.
From stdpp Require Import base.

Section world_ghost_theory.

  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
  .
  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation K := (CSTK -n> list WORLD -n> leibnizO (list CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (V).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Definition stsRes (W : WORLD) (C : CmptName) : iProp Σ :=
    region W C ∗ sts_full_world W C.

  Definition stsRes_open (W : WORLD) (C : CmptName) (s : list Addr) : iProp Σ :=
    open_region_many W C s ∗ sts_full_world W C.

  Definition TmpRes (W : WORLD) (C : CmptName) (a : Addr) (p : Perm) Φ (w : Word) : iProp Σ :=
    ⌜ isO p = false ⌝ ∗ a ↦ₐ w ∗ Φ (W,C,w) ∗
    if (decide ( isWL p = true ∨ isDL p = true )) then future_pub_mono C Φ w else future_priv_mono C Φ w.

  Definition PermRes (W : WORLD) (C : CmptName) (a : Addr) (p : Perm) Φ (w : Word) : iProp Σ :=
    ⌜ isO p = false ⌝ ∗ a ↦ₐ w ∗ Φ (W,C,w) ∗ future_priv_mono C Φ w.

  Definition RevokedRes (W : WORLD) (C : CmptName) (s : list Addr) : iProp Σ :=
    [∗ list] a ∈ s, (∃ pa Φa, ⌜∀ WCv, Persistent (Φa WCv)⌝ ∗ rel C a pa Φa ∗ ∃ wa, TmpRes W C a pa Φa wa).

  Definition reinstate (W : WORLD) (s : list Addr) := close_list s W.

  Lemma safety_invariant_enforcement
    (W : WORLD) (C : CmptName) (a : Addr) (p : Perm) (P : V) :
    (std W) !! a = Some Permanent ∨ (std W) !! a = Some Temporary ->
    stsRes W C -∗
    rel C a p (safeC P) ==∗
    ∃ w, a ↦ₐ w ∗ ▷ P W C w.
  Proof.
    iIntros (HWa) "[Hr Hsts] Hrel".
    rewrite rel_eq region_eq /rel_def /region_def /region_map_def.
    iDestruct "Hrel" as (γpred) "#(Hγpred & Hφ)".
    iDestruct "Hr" as (M Mρ) "(HM & % & % & Hpreds)"; simplify_map_eq.
    iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq;eauto.
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete_eq].
    iDestruct "Hpreds" as "[(%ρ & %Hρ & Hstate & Hl) Hpreds]".
    iDestruct "Hl" as (γpred' p' φ' HH1 Hpers) "(#Hφ' & Hl)".
    simplify_eq.
    iDestruct (sts_full_state_std with "Hsts Hstate") as "%HWa'"; rewrite HWa' in HWa; simplify_eq.
    destruct HWa ; simplify_eq.
    - iDestruct "Hl" as (w) "(?&?&?&HP)"; iFrame.
      iModIntro.
      iDestruct (saved_pred_agree _ _ _ _ _ (W,C,w) with "Hφ Hφ'") as "H".
      iNext.
      iRewrite - "H" in "HP".
      iFrame.
    - iDestruct "Hl" as (w) "(?&?&?&HP)"; iFrame.
      iModIntro.
      iDestruct (saved_pred_agree _ _ _ _ _ (W,C,w) with "Hφ Hφ'") as "H".
      iNext.
      iRewrite - "H" in "HP".
      iFrame.
  Qed.

  Lemma open_empty (W : WORLD) (C : CmptName) :
    stsRes_open W C [] ⊣⊢ stsRes W C.
  Proof.
    rewrite /stsRes_open /stsRes.
    iSplit ; iIntros "[Hr $]"; iApply region_open_nil; done.
  Qed.

  Lemma open_temporary (W : WORLD) (C : CmptName) (s : list Addr) (a : Addr) (p : Perm) Φ :
    a ∉ s ->
    (std W) !! a = Some Temporary ->
    stsRes_open W C s -∗
    rel C a p Φ
    -∗
    stsRes_open W C ({[ a ]} ∪ s) ∗ sts_state_std C a Temporary ∗ ▷ (∃ w, TmpRes W C a p Φ w).
  Proof.
    iIntros (Ha HWa) "[Hr Hsts] Hrel".
    destruct (isWL p) eqn:Hp_WL.
    - iDestruct (region_open_next_temp_pwl with "[$Hr $Hrel $Hsts]")
        as "(%w & Hr & Hsts & Hstd_sta & Ha & Hp & Hmono & HΦ)" ;[set_solver|..]; eauto.
      iFrame.
      rewrite decide_True; eauto.
    - iDestruct (region_open_next_temp_nwl with "[$Hr $Hrel $Hsts]")
        as "(%w & Hr & Hsts & Hstd_sta & Ha & Hp & Hmono & HΦ)" ;[set_solver|..]; eauto.
      iFrame.
      destruct (isDL p) eqn:Hp_DL; [rewrite decide_True | rewrite decide_False]; eauto.
      rewrite Hp_WL; intros []; done.
  Qed.

  Lemma close_temporary
    (W : WORLD) (C : CmptName) (s : list Addr) (a : Addr) (p : Perm) Φ (w : Word)
    `{forall WCv, Persistent (Φ WCv)}:
    a ∉ s ->
    stsRes_open W C ({[ a ]} ∪ s) -∗
    rel C a p Φ -∗
    sts_state_std C a Temporary -∗
    TmpRes W C a p Φ w -∗
    stsRes_open W C s ∗ rel C a p Φ.
  Proof.
    iIntros (Ha) "[Hr Hsts] #Hrel Hstd_sta (HpO & Ha & HΦ & Hmono)".
    destruct (isWL p) eqn:Hp_WL.
    - iDestruct (region_close_next_temp_pwl with "[Hr Hrel Hstd_sta HpO Ha HΦ Hmono]") as "Hr"
      ; eauto; iFrame "∗ #".
    - iDestruct (region_close_next_temp_nwl with "[Hr Hrel Hstd_sta HpO Ha HΦ Hmono]") as "Hr"
      ; eauto; iFrame "∗ #".
      destruct (isDL p) eqn:Hp_DL.
      + destruct ( decide (false = true ∨ true = true) ) as [ Hdex | Hdec ]; auto.
        exfalso; apply Hdec; right; done.
      + destruct ( decide (false = true ∨ true = true) ) as [ Hdex | Hdec ]; auto.
  Qed.

  Lemma open_permanent (W : WORLD) (C : CmptName) (s : list Addr) (a : Addr) (p : Perm) Φ :
    a ∉ s ->
    (std W) !! a = Some Permanent ->
    stsRes_open W C s -∗
    rel C a p Φ
    -∗
    stsRes_open W C ({[ a ]} ∪ s) ∗ sts_state_std C a Permanent ∗ ▷ (∃ w, PermRes W C a p Φ w).
  Proof.
    iIntros (Ha HWa) "[Hr Hsts] Hrel".
    iDestruct (region_open_next_perm with "[$Hr $Hrel $Hsts]")
      as "(%w & Hr & Hsts & Hstd_sta & Ha & Hp & Hmono & HΦ)" ;[set_solver|..]; eauto.
    iFrame.
  Qed.

  Lemma close_permanent (W : WORLD) (C : CmptName)
    (s : list Addr) (a : Addr) (p : Perm) Φ (w : Word) `{forall WCv, Persistent (Φ WCv)}:
    a ∉ s ->
    stsRes_open W C ({[ a ]} ∪ s) -∗
    rel C a p Φ -∗
    sts_state_std C a Permanent -∗
    PermRes W C a p Φ w -∗
    stsRes_open W C s ∗ rel C a p Φ.
  Proof.
    iIntros (Ha) "[Hr Hsts] #Hrel Hstd_sta (HpO & Ha & HΦ & Hmono)".
    iDestruct (region_close_next_perm with "[Hr Hrel Hstd_sta HpO Ha HΦ Hmono]") as "Hr"
    ; eauto; iFrame "∗ #".
  Qed.

  Lemma revoke_world (W : WORLD) (C : CmptName) (s : list Addr) :
    NoDup s →
    ( ∀ a, a ∈ s ↔ (std W) !! a = Some Temporary ) →
    stsRes W C
    ==∗
    stsRes (revoke W) C ∗ ▷ RevokedRes W C s.
  Proof.
    iIntros (Hnodup HaS) "[Hr Hsts]".
    iMod ( monotone_revoke_keep W C s with "[$Hr $Hsts]") as "(Hr & Hsts & Hres & %Hrevoked)"
    ; auto.
    { iPureIntro; intros k a Hk; cbn. apply HaS. apply list_elem_of_lookup; eauto. }
    iFrame.
    iModIntro; iNext.
    iApply (big_sepL_impl with "Hres").
    iModIntro ; iIntros (k a Hk) "(%p & %Φ & Hpers & Htmp & $)".
    cbn.
    iDestruct "Htmp" as (w) "(HpO & Ha & Hmono & HΦ)".
    iFrame.
    destruct (isWL p) eqn:Hp_WL.
    - destruct (decide (true = true ∨ isDL p = true)) as [Hdec | Hdec]; auto.
      exfalso; apply Hdec; left; done.
    - destruct (isDL p) eqn:Hp_DL.
      + destruct (decide (false = true ∨ true = true)) as [Hdec | Hdec]; auto.
        exfalso; apply Hdec; right; done.
      + destruct (decide (false = true ∨ false = true)) as [Hdec | Hdec]; auto.
        destruct Hdec as []; done.
  Qed.

  Lemma restore_world (W W' : WORLD) (C : CmptName) (s : list Addr) :
    related_sts_pub_world W (reinstate W' s) →
    stsRes W' C -∗
    RevokedRes W C s
    ==∗
    stsRes (reinstate W' s) C.
  Proof.
    rewrite /reinstate.
    iIntros (Hpub) "[Hr Hsts] HrevokedRes".
    iAssert (close_list_resources C W s false) with "[HrevokedRes]" as "H".
    { iFrame.
      iApply (big_sepL_impl with "HrevokedRes").
      iModIntro ; iIntros (k a Hk) "(%p & %Φ & Hrel & H & (%wa & HpO & Ha & HΦ & Hmono))".
      iFrame; iFrame.
      destruct (isWL p) eqn:Hp_WL.
      - destruct (decide (true = true ∨ isDL p = true)) as [Hdec | Hdec]; auto.
        exfalso; apply Hdec; left; done.
      - destruct (isDL p) eqn:Hp_DL.
        + destruct (decide (false = true ∨ true = true)) as [Hdec | Hdec]; auto.
          exfalso; apply Hdec; right; done.
        + destruct (decide (false = true ∨ false = true)) as [Hdec | Hdec]; auto.
          destruct Hdec as []; done.
    }
    iMod (monotone_close_list_region with "[%] [$Hsts $Hr $H]") as "[$ $]"; eauto.
  Qed.

End world_ghost_theory.
