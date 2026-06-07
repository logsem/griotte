From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From cap_machine Require Import region_invariants_revocation region_invariants_allocation.
From stdpp Require Import base.

Section world_ghost_theory.

  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    `{MP: MachineParameters}
  .
  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation Vc := (WORLD * CmptName * Word → iProp Σ).

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Definition world_interp_def (W : WORLD) (C : CmptName) : iProp Σ :=
    region W C ∗ sts_full_world W C.
  Definition world_interp_aux : { x | x = @world_interp_def }. by eexists. Qed.
  Definition world_interp := proj1_sig world_interp_aux.
  Definition world_interp_eq : @world_interp = @world_interp_def := proj2_sig world_interp_aux.

  Definition world_interp_open_def (W : WORLD) (C : CmptName) (s : list Addr) : iProp Σ :=
    open_region_many W C s ∗ sts_full_world W C.
  Definition world_interp_open_aux : { x | x = @world_interp_open_def }. by eexists. Qed.
  Definition world_interp_open := proj1_sig world_interp_open_aux.
  Definition world_interp_open_eq : @world_interp_open = @world_interp_open_def := proj2_sig world_interp_open_aux.

  Definition mono_temporary (C : CmptName) (p : Perm) (Φ : Vc) (w : Word) : iProp Σ :=
    if (decide ( isWL p = true ∨ isDL p = true )) then future_pub_mono C Φ w else future_priv_mono C Φ w.
  Definition mono_permanent (C : CmptName) (Φ : Vc) (w : Word) : iProp Σ :=
    future_priv_mono C Φ w.
  Definition mono_invariant (C : CmptName) (p : Perm) (Φ : Vc) (w : Word) (ρ : region_type) : iProp Σ :=
    (if (decide (ρ = Temporary))
     then mono_temporary C p Φ w
     else mono_permanent C Φ w).

  Lemma mono_temporary_eq (C : CmptName) (p : Perm) (Φ : Vc) (w : Word) :
    mono_temporary C p Φ w
    ⊣⊢ (if isWL p
        then future_pub_mono C Φ w
        else if isDL p then future_pub_mono C Φ w else future_priv_mono C Φ w).
  Proof.
    rewrite /mono_temporary.
    destruct isWL; cbn.
    - case_decide; first done.
      exfalso; apply H; by left.
    - destruct isDL; cbn.
      + case_decide; first done.
        exfalso; apply H; by right.
      + case_decide; last done.
        destruct H; done.
  Qed.

  Lemma mono_invariant_eq (C : CmptName) (p : Perm) (Φ : Vc) (w : Word) (ρ : region_type) :
    mono_invariant C p Φ w ρ
    ⊣⊢
      (if decide (ρ = Temporary)
       then
         if isWL p
         then future_pub_mono C Φ w
         else if isDL p then future_pub_mono C Φ w else future_priv_mono C Φ w
       else future_priv_mono C Φ w).
  Proof.
    rewrite /mono_invariant.
    case_decide as Hρ;auto.
    apply mono_temporary_eq.
  Qed.

  Definition TmpRes (W : WORLD) (C : CmptName) (a : Addr) (p : Perm) Φ (w : Word) : iProp Σ :=
    ⌜ isO p = false ⌝ ∗ a ↦ₐ w ∗ Φ (W,C,w) ∗ mono_temporary C p Φ w.

  Definition PermRes (W : WORLD) (C : CmptName) (a : Addr) (p : Perm) Φ (w : Word) : iProp Σ :=
    ⌜ isO p = false ⌝ ∗ a ↦ₐ w ∗ Φ (W,C,w) ∗ mono_permanent C Φ w.

  Definition WorldRes
    (W : WORLD) (C : CmptName)
    (a : Addr) (p : Perm) Φ (w : Word) (ρ : region_type) : iProp Σ :=
    ⌜ isO p = false ⌝ ∗ a ↦ₐ w ∗ Φ (W,C,w) ∗ mono_invariant C p Φ w ρ.

  (* TODO that is "essentially" close_list_resources,
     defined in regions_invariant_revocation.v,
     only missing is_later.
     This is essentially like RevokedResources in logrel_extra.v
   *)
  Definition RevokedRes (W : WORLD) (C : CmptName) (s : list Addr) : iProp Σ :=
    [∗ list] a ∈ s, (∃ pa Φa, ⌜∀ WCv, Persistent (Φa WCv)⌝ ∗ rel C a pa Φa ∗ ∃ wa, TmpRes W C a pa Φa wa).

  Definition reinstate (W : WORLD) (s : list Addr) := close_list s W.

  Local Notation safeC P := (λ WCv : WORLD * CmptName * (leibnizO Word), P WCv.1.1 WCv.1.2 WCv.2).

  Lemma safety_invariant_enforcement
    (W : WORLD) (C : CmptName) (a : Addr) (p : Perm) (P : V) :
    (std W) !! a = Some Permanent ∨ (std W) !! a = Some Temporary ->
    world_interp W C -∗
    rel C a p (safeC P)
    ==∗
    ∃ w, a ↦ₐ w ∗ ▷ P W C w.
  Proof.
    rewrite world_interp_eq /world_interp_def.
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

  Lemma world_interp_init (W : WORLD) (C : CmptName) :
    region W C ∗ sts_full_world W C -∗ world_interp W C.
  Proof. rewrite world_interp_eq /world_interp_def; iIntros "[? ?]"; iFrame. Qed.

  Lemma open_world_interp_empty (W : WORLD) (C : CmptName) :
    world_interp_open W C [] ⊣⊢ world_interp W C.
  Proof.
    rewrite world_interp_eq /world_interp_def.
    rewrite world_interp_open_eq /world_interp_open_def.
    rewrite /world_interp_open /world_interp.
    iSplit ; iIntros "[Hr $]"; iApply region_open_nil; done.
  Qed.

  Lemma open_world_interp_temporary (W : WORLD) (C : CmptName) (s : list Addr) (a : Addr) (p : Perm) Φ :
    a ∉ s ->
    (std W) !! a = Some Temporary ->
    world_interp_open W C s -∗
    rel C a p Φ
    -∗
    world_interp_open W C ({[ a ]} ∪ s) ∗
    sts_state_std C a Temporary ∗
    ▷ (∃ w, TmpRes W C a p Φ w).
  Proof.
    rewrite world_interp_open_eq /world_interp_open_def.
    iIntros (Ha HWa) "[Hr Hsts] Hrel".
    destruct (isWL p) eqn:Hp_WL.
    - iDestruct (region_open_next_temp_pwl with "[$Hr $Hrel $Hsts]")
        as "(%w & Hr & Hsts & Hstd_sta & Ha & Hp & Hmono & HΦ)" ;[set_solver|..]; eauto.
      iFrame.
      rewrite /mono_temporary decide_True; eauto.
    - iDestruct (region_open_next_temp_nwl with "[$Hr $Hrel $Hsts]")
        as "(%w & Hr & Hsts & Hstd_sta & Ha & Hp & Hmono & HΦ)" ;[set_solver|..]; eauto.
      iFrame.
      rewrite /mono_temporary ; destruct (isDL p) eqn:Hp_DL; [rewrite decide_True | rewrite decide_False]; eauto.
      rewrite Hp_WL; intros []; done.
  Qed.

  Lemma close_world_interp_temporary
    (W : WORLD) (C : CmptName) (s : list Addr) (a : Addr) (p : Perm) Φ (w : Word)
    `{forall WCv, Persistent (Φ WCv)}:
    a ∉ s ->
    world_interp_open W C ({[ a ]} ∪ s) -∗
    rel C a p Φ -∗
    sts_state_std C a Temporary -∗
    TmpRes W C a p Φ w
    -∗
    world_interp_open W C s ∗ rel C a p Φ.
  Proof.
    rewrite world_interp_open_eq /world_interp_open_def.
    iIntros (Ha) "[Hr Hsts] #Hrel Hstd_sta (HpO & Ha & HΦ & Hmono)".
    rewrite /mono_temporary.
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

  Lemma open_world_interp_permanent (W : WORLD) (C : CmptName) (s : list Addr) (a : Addr) (p : Perm) Φ :
    a ∉ s ->
    (std W) !! a = Some Permanent ->
    world_interp_open W C s -∗
    rel C a p Φ
    -∗
    world_interp_open W C ({[ a ]} ∪ s) ∗
    sts_state_std C a Permanent ∗
    ▷ (∃ w, PermRes W C a p Φ w).
  Proof.
    rewrite world_interp_open_eq /world_interp_open_def.
    iIntros (Ha HWa) "[Hr Hsts] Hrel".
    iDestruct (region_open_next_perm with "[$Hr $Hrel $Hsts]")
      as "(%w & Hr & Hsts & Hstd_sta & Ha & Hp & Hmono & HΦ)" ;[set_solver|..]; eauto.
    iFrame.
  Qed.

  Lemma close_world_interp_permanent (W : WORLD) (C : CmptName)
    (s : list Addr) (a : Addr) (p : Perm) Φ (w : Word) `{forall WCv, Persistent (Φ WCv)}:
    a ∉ s ->
    world_interp_open W C ({[ a ]} ∪ s) -∗
    rel C a p Φ -∗
    sts_state_std C a Permanent -∗
    PermRes W C a p Φ w
    -∗
    world_interp_open W C s ∗ rel C a p Φ.
  Proof.
    rewrite world_interp_open_eq /world_interp_open_def.
    iIntros (Ha) "[Hr Hsts] #Hrel Hstd_sta (HpO & Ha & HΦ & Hmono)".
    iDestruct (region_close_next_perm with "[Hr Hrel Hstd_sta HpO Ha HΦ Hmono]") as "Hr"
    ; eauto; iFrame "∗ #".
  Qed.

  Lemma open_world_interp
    (W : WORLD) (C : CmptName) (a : Addr) (p : Perm) (φ : Vc) (ρ : region_type) :
    ρ = Temporary ∨ ρ = Permanent →
    (std W) !! a = Some ρ →
    rel C a p φ -∗
    world_interp W C
    -∗
    world_interp_open W C [a] ∗
    sts_state_std C a ρ ∗
    ▷ (∃ v, WorldRes W C a p φ v ρ).
  Proof.
    rewrite world_interp_eq /world_interp_def.
    rewrite world_interp_open_eq /world_interp_open_def.
    iIntros (Hne Htemp) "Hrel [Hreg Hfull]".
    iDestruct (region_open with "[$Hrel $Hreg $Hfull]") as (v) "(Hr & Hfull & Hstate & Hl & Hp & Hmono & φ)"; eauto.
    rewrite -(mono_invariant_eq C p φ v ρ).
    rewrite -region_open_prepare; iFrame.
  Qed.

  Lemma close_world_interp
    (W : WORLD) (C : CmptName) (a : Addr) (p : Perm) (φ : Vc) (v : Word)
    (ρ : region_type) `{forall Wv, Persistent (φ Wv)} :
    ρ = Temporary ∨ ρ = Permanent →

    world_interp_open W C [a] -∗
    sts_state_std C a ρ -∗
    rel C a p φ -∗
    WorldRes W C a p φ v ρ
    -∗
    world_interp W C.
  Proof.
    rewrite world_interp_eq /world_interp_def.
    rewrite world_interp_open_eq /world_interp_open_def.
    rewrite -region_open_prepare.
    iIntros (Hρ) "[Hreg_open $] Hstate Hrel (Hp&Ha&Hφ&Hmono)".
    rewrite (mono_invariant_eq C p φ v ρ).
    iApply (region_close with "[$Hstate $Hreg_open $Ha $Hp $Hmono $Hφ $Hrel]"); eauto.
  Qed.


  Lemma world_interp_revoke_world (W : WORLD) (C : CmptName) (s : list Addr) :
    NoDup s →
    ( ∀ a, a ∈ s ↔ (std W) !! a = Some Temporary ) →
    world_interp W C
    ==∗
    world_interp (revoke W) C ∗ ▷ RevokedRes W C s.
  Proof.
    rewrite world_interp_eq /world_interp_def.
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
    rewrite /mono_temporary.
    destruct (isWL p) eqn:Hp_WL.
    - destruct (decide (true = true ∨ isDL p = true)) as [Hdec | Hdec]; auto.
      exfalso; apply Hdec; left; done.
    - destruct (isDL p) eqn:Hp_DL.
      + destruct (decide (false = true ∨ true = true)) as [Hdec | Hdec]; auto.
        exfalso; apply Hdec; right; done.
      + destruct (decide (false = true ∨ false = true)) as [Hdec | Hdec]; auto.
        destruct Hdec as []; done.
  Qed.

  Lemma world_interp_restore_world (W W' : WORLD) (C : CmptName) (s : list Addr) :
    related_sts_pub_world W (reinstate W' s) →
    world_interp W' C -∗
    RevokedRes W C s
    ==∗
    world_interp (reinstate W' s) C.
  Proof.
    rewrite world_interp_eq /world_interp_def.
    rewrite /reinstate.
    iIntros (Hpub) "[Hr Hsts] HrevokedRes".
    iAssert (close_list_resources C W s false) with "[HrevokedRes]" as "H".
    { iFrame.
      iApply (big_sepL_impl with "HrevokedRes").
      iModIntro ; iIntros (k a Hk) "(%p & %Φ & Hrel & H & (%wa & HpO & Ha & HΦ & Hmono))".
      iFrame; iFrame.
      rewrite /mono_temporary.
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

  Lemma PermRes_acc (W : WORLD) (C : CmptName) (a : Addr) (p : Perm) (Φ : Vc) (w : Word) :
    PermRes W C a p Φ w -∗
    ( a ↦ₐ w ∗ Φ (W,C,w) ) ∗
    ( ( a ↦ₐ w ∗ Φ (W,C,w) ) -∗ PermRes W C a p Φ w ).
  Proof.
    iIntros "(#Hp&Ha&HΦ&#Hmono)".
    iSplitL "Ha HΦ"; iFrame.
    iIntros "[Ha HΦ]"; iFrame "∗#".
  Qed.

  Lemma PermRes_acc' (W : WORLD) (C : CmptName) (a : Addr) (p : Perm) (Φ : Vc) (w : Word) :
    PermRes W C a p Φ w -∗
    ( a ↦ₐ w ∗ Φ (W,C,w) ∗ mono_permanent C Φ w ) ∗
    ( ∀ w', ( a ↦ₐ w' ∗ Φ (W,C,w') ∗ mono_permanent C Φ w' ) -∗ PermRes W C a p Φ w' ).
  Proof.
    iIntros "(#Hp&Ha&HΦ&Hmono)".
    iSplitL "Ha HΦ Hmono"; iFrame.
    iIntros (w') "($&$&$)".
    done.
  Qed.

End world_ghost_theory.
