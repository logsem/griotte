From iris.proofmode Require Import proofmode.
From cap_machine Require Import region_invariants_revocation region_invariants_allocation sealing_invariants.
From cap_machine Require Export sts world_std_revocation sts_multiple_updates.
From cap_machine Require Export stdpp_extra iris_extra.

  (*** World Ghost Theory *)

  (** This file define the ghost theory of worlds.
      It is intended to be a clean interface between the model defined in [region_invariant_*.v] and the user. *)

  (** * Disclaimer to the users of Griotte:

      All the proofs in this file are use the Griotte internal model defined in [region_invariant_*.v].
      This file defines the interface that one should use in the proofs.

  *)


Section world_ghost_theory.

  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG} {CNames : gset CmptName}
    {stsg : STSG Addr region_type OType Word Σ}
    {relg : relGS Σ}
    `{MP: MachineParameters}
  .
  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation Vc := (WORLD * CmptName * Word → iProp Σ).
  Notation safeC P := (λ WCv : WORLD * CmptName * (leibnizO Word), P WCv.1.1 WCv.1.2 WCv.2).

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (** ** Definitions of world interpretation *)

  (** Definition of [world_interp].
      All safety resources of the addresses in the world are owned by the world interpretation. *)
  Definition world_interp_def (W : WORLD) (C : CmptName) : iProp Σ :=
    region W C ∗ sts_full_world W C ∗ sealing_map W C.
  Definition world_interp_aux : { x | x = @world_interp_def }. by eexists. Qed.
  Definition world_interp := proj1_sig world_interp_aux.
  Definition world_interp_eq : @world_interp = @world_interp_def := proj2_sig world_interp_aux.

  (** Definition of [world_interp_open].
      The safety resources of the addresses in [s] are not owned by the world interpretation. *)
  Definition world_interp_open_def (W : WORLD) (C : CmptName) (s : list Addr) : iProp Σ :=
    open_region_many W C s ∗ sts_full_world W C ∗ sealing_map W C.
  Definition world_interp_open_aux : { x | x = @world_interp_open_def }. by eexists. Qed.
  Definition world_interp_open := proj1_sig world_interp_open_aux.
  Definition world_interp_open_eq : @world_interp_open = @world_interp_open_def := proj2_sig world_interp_open_aux.


  (** Definition of safety resources *)
  Definition mono_temporary (C : CmptName) (p : Perm) (Φ : Vc) (w : Word) : iProp Σ :=
    if (decide ( isWL p = true ∨ isDL p = true )) then future_pub_mono C Φ w else future_priv_mono C Φ w.

  Definition mono_permanent (C : CmptName) (Φ : Vc) (w : Word) : iProp Σ :=
    future_priv_mono C Φ w.

  Definition mono_invariant (C : CmptName) (p : Perm) (Φ : Vc) (w : Word) (ρ : region_type) : iProp Σ :=
    (if (decide (ρ = Temporary))
     then mono_temporary C p Φ w
     else mono_permanent C Φ w).

  (** ** Definitions of safety resources *)

  (** Temporary Safety Resources *)
  Definition TmpRes (W : WORLD) (C : CmptName) (a : Addr) (p : Perm) Φ (w : Word) : iProp Σ :=
    ⌜ isO p = false ⌝ ∗ a ↦ₐ w ∗ Φ (W,C,w) ∗ mono_temporary C p Φ w.

  (** Permanent Safety Resources *)
  Definition PermRes (W : WORLD) (C : CmptName) (a : Addr) (p : Perm) Φ (w : Word) : iProp Σ :=
    ⌜ isO p = false ⌝ ∗ a ↦ₐ w ∗ Φ (W,C,w) ∗ mono_permanent C Φ w.

  (** Unknown Safety Resources *)
  Definition WorldRes
    (W : WORLD) (C : CmptName)
    (a : Addr) (p : Perm) Φ (w : Word) (ρ : region_type) : iProp Σ :=
    ⌜ isO p = false ⌝ ∗ a ↦ₐ w ∗ Φ (W,C,w) ∗ mono_invariant C p Φ w ρ.

  (** Revoked Safety Resources *)
  Definition RevokedResources (W : WORLD) (C : CmptName) (s : list Addr) : iProp Σ :=
    [∗ list] a ∈ s, (∃ pa Φa, ⌜∀ WCv, Persistent (Φa WCv)⌝ ∗ rel C a pa Φa ∗ ∃ wa, TmpRes W C a pa Φa wa).

  Definition reinstate (W : WORLD) (s : list Addr) := close_list s W.


  (** ** Lemmas about monotonicity *)
  Global Instance mono_temporary_Persistent C p Φ w:
    Persistent (mono_temporary C p Φ w).
  Proof. rewrite /mono_temporary; destruct ( decide (isWL p = true ∨ isDL p = true) ); apply _. Qed.

  Global Instance mono_permanent_Persistent C Φ w: Persistent (mono_permanent C Φ w).
  Proof. apply _. Qed.

  Global Instance mono_invariant_Persistent C p Φ w ρ:
    Persistent (mono_invariant C p Φ w ρ).
  Proof. rewrite /mono_invariant; destruct ( decide (ρ = Temporary) ); apply _. Qed.

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

  Lemma mono_invariant_monotonicity_guarantees_region
    (C : CmptName) (Φ : Vc) (p : Perm) (w : Word) (ρ : region_type) :
    ρ ≠ Revoked ->
    mono_invariant C p Φ w ρ ⊣⊢ monotonicity_guarantees_region C Φ p w ρ.
  Proof.
    intros Hne.
    rewrite /monotonicity_guarantees_region mono_invariant_eq.
    iSplit; iIntros "H".
    all: destruct ρ; simplify_eq; cbn; case_decide; try done.
    all: destruct (isWL p); auto.
    all: destruct (isDL p); auto.
  Qed.

  (** ** Lemmas about the safety resources *)

  (* For internal use only, links [RevokedResources] from the clean interface with
     [close_list_resources] from the internal model *)
  Local Lemma RevokedResources_eq (W : WORLD) ( C : CmptName ) (l : list Addr) :
    RevokedResources W C l ⊣⊢ close_list_resources C W l false.
  Proof.
    iSplit; iIntros "H"; iApply (big_sepL_impl with "H")
    ; iModIntro ; iIntros (k ka Hka) "H".
    + iDestruct "H" as "(% &% & $ & $ & [% ($&$&$&?)])"; by rewrite mono_temporary_eq.
    + iDestruct "H" as "(% &% & $ & [% ($&$&?&$)] & $)"; by rewrite mono_temporary_eq.
  Qed.

  Global Instance RevokedResources_Permutation_proper (W : WORLD) (C : CmptName) :
    Proper (Permutation ==> equiv) (RevokedResources W C).
  Proof. iIntros (l l' Hl); rewrite /RevokedResources; setoid_rewrite Hl; done. Defined.

  Lemma RevokedResources_app (W : WORLD) (C' : CmptName) (l l' : list Addr) :
    RevokedResources W C' (l++l') ⊣⊢ RevokedResources W C' l ∗ RevokedResources W C' l'.
  Proof. apply big_sepL_app. Qed.

  Lemma RevokedResources_disjoint
    (C1 C2 : CmptName) (W1 W2 : WORLD) (l1 l2 : list Addr) :
    RevokedResources W1 C1 l1 ∗ RevokedResources W2 C2 l2 -∗ ⌜ l1 ## l2 ⌝.
  Proof.
    rewrite !RevokedResources_eq.
    apply close_list_resources_separation_many_alt.
  Qed.

  Lemma RevokedResources_mono_pub (W W' : WORLD) (C : CmptName) (l_unk la : list Addr) :
    related_sts_pub_world W W' ->
    RevokedResources W C l_unk -∗
    RevokedResources W' C l_unk.
  Proof.
    iIntros (Hrelated) "H".
    rewrite /RevokedResources.
    iApply (big_sepL_impl with "H").
    iIntros "!> %k %a %Ha H".
    iDestruct "H" as (pa Pa) "($ & $ & (%va & $ & $ & Hp & #Hmono))"; iFrame "Hmono".
    iAssert (future_pub_mono C Pa va) as "HmonoP".
    { rewrite mono_temporary_eq.
      destruct (isWL pa); auto.
      destruct (isDL pa); auto.
      by iApply future_priv_mono_is_future_pub_mono.
    }
    iApply "HmonoP"; eauto.
  Qed.

  (* [PermRes] can give access to the current points-to.
     We have to relinquish it to get [PermRes] again. *)
  Lemma PermRes_acc (W : WORLD) (C : CmptName) (a : Addr) (p : Perm) (Φ : Vc) (w : Word) :
    PermRes W C a p Φ w -∗
    ( a ↦ₐ w ∗ Φ (W,C,w) ) ∗
    ( ( a ↦ₐ w ∗ Φ (W,C,w) ) -∗ PermRes W C a p Φ w ).
  Proof.
    iIntros "(#Hp&Ha&HΦ&#Hmono)".
    iSplitL "Ha HΦ"; iFrame.
    iIntros "[Ha HΦ]"; iFrame "∗#".
  Qed.

  (* [PermRes] can give access to the current points-to.
     If we mutate the value of the points-to, we have to show that the new value respects the safety predicate,
     before getting [PermRes] again. *)
  Lemma PermRes_acc_forall (W : WORLD) (C : CmptName) (a : Addr) (p : Perm) (Φ : Vc) (w : Word) :
    PermRes W C a p Φ w -∗
    ( a ↦ₐ w ∗ Φ (W,C,w) ∗ mono_permanent C Φ w ) ∗
    ( ∀ w', ( a ↦ₐ w' ∗ Φ (W,C,w') ∗ mono_permanent C Φ w' ) -∗ PermRes W C a p Φ w' ).
  Proof.
    iIntros "(#Hp&Ha&HΦ&Hmono)".
    iSplitL "Ha HΦ Hmono"; iFrame.
    iIntros (w') "($&$&$)"; done.
  Qed.

  (* [WorldRes] can give access to the current points-to.
     If we mutate the value of the points-to, we have to show that the new value respects the safety predicate,
     before getting [WorldRes] again. *)
  Lemma WorldRes_acc (W : WORLD) (C : CmptName) (a : Addr) (p : Perm) (Φ : Vc) (w : Word) ρ :
    WorldRes W C a p Φ w ρ -∗
    ( a ↦ₐ w ∗ Φ (W,C,w) ) ∗
    ( ( a ↦ₐ w ∗ Φ (W,C,w) ) -∗ WorldRes W C a p Φ w ρ ).
  Proof.
    iIntros "(Hp&Ha&HΦ&Hmono)".
    iSplitL "Ha HΦ"; iFrame.
    iIntros "[Ha HΦ]"; iFrame "∗#".
  Qed.

  (* [WorldRes] can give access to the current points-to.
     If we mutate the value of the points-to, we have to show that the new value respects the safety predicate,
     before getting [WorldRes] again. *)
  Lemma WorldRes_acc_forall (W : WORLD) (C : CmptName) (a : Addr) (p : Perm) (Φ : Vc) (w : Word) ρ :
    WorldRes W C a p Φ w ρ -∗
    ( a ↦ₐ w ∗ Φ (W,C,w) ∗ mono_invariant C p Φ w ρ ) ∗
    ( ∀ w', ( a ↦ₐ w' ∗ Φ (W,C,w') ∗ mono_invariant C p Φ w' ρ ) -∗ WorldRes W C a p Φ w' ρ ).
  Proof.
    iIntros "(#Hp&Ha&HΦ&Hmono)".
    iSplitL "Ha HΦ Hmono"; iFrame.
    iIntros (w') "($&$&$)"; done.
  Qed.

  (* NOTE we don't strictly need to have the equivalent lemmas for [TmpRes],
     because we usually revoke the world instead. *)


  (** ** World Ghost Theory *)

  (* The combination of the safety invariant [rel C a p ϕ] and
     the (closed) world interpretation [world_interp]
     means that the safety predicate currently holds.

     NOTE Lemma [safety_invariant_enforcement] is never used and only showcases the above statement. *)
  Lemma safety_invariant_enforcement
    (W : WORLD) (C : CmptName) (a : Addr) (p : Perm) (P : V) :
    (std W) !! a = Some Permanent ∨ (std W) !! a = Some Temporary ->
    world_interp W C -∗
    rel C a p (safeC P)
    ==∗
    ∃ w, a ↦ₐ w ∗ ▷ P W C w.
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros (HWa) "[Hr [Hsts Hseals] ] Hrel".
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


  (** ** World opening/closing *)

  (* A closed world is like a world open on no addresses. *)
  Lemma open_world_interp_empty (W : WORLD) (C : CmptName) :
    world_interp W C ⊣⊢ world_interp_open W C [].
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
    iIntros (Ha HWa) "[Hr [Hsts Hseals] ] Hrel".
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
    iIntros (Ha) "[Hr [Hsts Hseals] ] #Hrel Hstd_sta (HpO & Ha & HΦ & Hmono)".
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
    iIntros (Ha HWa) "[Hr [Hsts Hseals] ] Hrel".
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

  Lemma open_world_interp_next
    (W : WORLD) (C : CmptName) (s : list Addr) (a : Addr) (p : Perm) (φ : Vc) (ρ : region_type) :
    a ∉ s ->
    ρ = Temporary ∨ ρ = Permanent →
    (std W) !! a = Some ρ →
    rel C a p φ -∗
    world_interp_open W C s
    -∗
    world_interp_open W C ({[ a ]} ∪ s) ∗
    sts_state_std C a ρ ∗
    ▷ (∃ v, WorldRes W C a p φ v ρ).
  Proof.
    rewrite world_interp_open_eq /world_interp_open_def.
    iIntros (Hs Hne Htemp) "Hrel [Hr [Hsts Hseals] ]".
    iDestruct (region_open_next with "[$Hrel $Hr $Hsts]") as (v) "(Hr & Hfull & Hstate & Hl & Hp & Hmono & φ)"; eauto.
    { destruct Hne; simplify_eq; done. }
    iFrame.
    iNext.
    rewrite mono_invariant_monotonicity_guarantees_region; eauto.
    destruct Hne; simplify_eq; done.
  Qed.

  Lemma close_world_interp_next
    (W : WORLD) (C : CmptName) (s : list Addr) (a : Addr) (p : Perm) (φ : Vc) (v : Word)
    (ρ : region_type) `{forall Wv, Persistent (φ Wv)} :
    a ∉ s ->
    ρ = Temporary ∨ ρ = Permanent →
    world_interp_open W C ({[ a ]} ∪ s) -∗
    sts_state_std C a ρ -∗
    rel C a p φ -∗
    WorldRes W C a p φ v ρ
    -∗
    world_interp_open W C s.
  Proof.
    rewrite world_interp_open_eq /world_interp_open_def.
    iIntros (Hs Hρ) "[Hr [$ $] ] Hstate Hrel (Hp&Ha&Hφ&Hmono)".
    rewrite mono_invariant_monotonicity_guarantees_region; eauto; cycle 1.
    { destruct Hρ; simplify_eq; done. }
    iApply (region_close_next with "[$Hstate $Hr $Ha $Hp $Hmono $Hφ $Hrel]"); eauto.
    { destruct Hρ; simplify_eq; done. }
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
    iIntros (Hne Htemp) "#Hrel Hworld".
    rewrite open_world_interp_empty.
    iApply open_world_interp_next; eauto.
    set_solver+.
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
    rewrite open_world_interp_empty.
    iIntros (Htemp) "Hworld Hstd #Hrel".
    iApply (close_world_interp_next with "Hworld Hstd Hrel"); eauto.
    set_solver+.
  Qed.

  (** ** Lemma for world Revocation and Restoration. *)

  (* [extract_temporaries_condition] states that [la] is the full set of addresses
     that are Temporary in [W]. *)
  Definition extract_temporaries_condition (W : WORLD) (la : list Addr) :=
      NoDup la ∧ (forall (a : Addr), (std W) !! a = Some Temporary <-> a ∈ la).

  Lemma extract_temporaries_condition_lookup (W : WORLD) (l : list Addr) (a : Addr) :
    extract_temporaries_condition W l ->
    a ∈ l ->
    std W !! a = Some Temporary.
  Proof. intros [_ H] Ha; by apply H in Ha. Qed.

  Lemma extract_temporaries_condition_revoke W s :
    extract_temporaries_condition W s -> Forall (λ a, std (revoke W) !! a = Some Revoked) s.
  Proof.
    intros [H1 H2].
    rewrite Forall_forall; intros a Ha.
    apply H2 in Ha.
    by apply revoke_lookup_Monotemp.
  Qed.

  (* Revocation of the world *)
  Lemma world_interp_revoke W C s :
    extract_temporaries_condition W s ->
    world_interp W C
    ==∗
    world_interp (revoke W) C
    ∗ ▷ RevokedResources W C s
    (* This last pure predicate is useful for bookkeeping. *)
    ∗ ⌜ Forall (λ a, std (revoke W) !! a = Some Revoked) s ⌝.
  Proof.
    rewrite world_interp_eq /world_interp_def RevokedResources_eq.
    intros [Hnodup HaS].
    iIntros "[Hr [Hsts Hseals] ]".
    iMod ( monotone_revoke_keep _ _ s with "[$Hr $Hsts]") as "($ & $ & Hres & $)"; auto.
    { iPureIntro; intros k a Ha; apply HaS; apply list_elem_of_lookup; eauto. }
    iDestruct (sealing_map_monotone with "Hseals") as "$"; auto.
    apply revoke_related_sts_priv_world.
  Qed.

  (* Restoration of the world, after revocation.

     NOTE [world_interp_restore_world] is not use in practice,
     because we use a more general version of the lemma. *)
  Lemma world_interp_restore_world (W W' : WORLD) (C : CmptName) (s : list Addr) :
    related_sts_pub_world W (reinstate W' s) →
    world_interp W' C -∗
    RevokedResources W C s
    ==∗
    world_interp (reinstate W' s) C.
  Proof.
    rewrite world_interp_eq /world_interp_def.
    rewrite /reinstate.
    iIntros (Hpub) "[Hr [Hsts Hseals] ] HrevokedRes".
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
    iDestruct (sealing_map_monotone_pub with "Hseals") as "$"; auto.
    apply close_list_related_sts_pub.
  Qed.

  (** ** Revocation by separation.

      The following lemmas are useful lemmas to know that same addresses are in the Revoked state in the world.
      When one owns the points-to predicate of an address [a], that the world is closed,
      but that it exists a safety predicate for [a],
      then it means that the address [a] must be Revoked in the world.

      This is an argument by separation.
   *)

  Lemma world_interp_revoked_by_separation
    (W : WORLD) (C' : CmptName)
    (a : Addr) (w : Word) :
    a ∈ dom (std W) →
    world_interp W C'
    ∗ a ↦ₐ w
    ==∗
    world_interp W C'
    ∗ a ↦ₐ w
    ∗ ⌜ std W !! a = Some Revoked ⌝
  .
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros (?) "([Hr [Hsts Hseals] ] & Ha)".
    iMod (revoked_by_separation with "[$Hr $Hsts $Ha]") as "($&$&$)";auto.
  Qed.

  Lemma world_interp_revoked_by_separation_many
    (W : WORLD) (C : CmptName)
    (la : list Addr) (lw : list Word) :
    Forall (λ a, a ∈ dom (std W)) la →
    world_interp W C
    ∗ ([∗ list] a;w ∈ la;lw, a ↦ₐ w)
    ==∗
    world_interp W C
    ∗ ([∗ list] a;w ∈ la;lw, a ↦ₐ w)
    ∗ ⌜ Forall (λ a, std W !! a = Some Revoked) la⌝
  .
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros (?) "([Hr [Hsts Hseals] ] & Hl)".
    iMod (revoked_by_separation_many with "[$Hr $Hsts $Hl]")
      as "($ & $ & $ & $)"; auto.
  Qed.

  (* [RevokedResources] owns the points-to predicates for the addresses in [la]. *)
  Lemma world_interp_revoked_by_separation_many_with_RevokedResources
    (W W' : WORLD) (C' : CmptName)
    (la : list Addr) :
    Forall (λ a, a ∈ dom (std W')) la →
    world_interp W' C' ∗
    RevokedResources W C' la
    ==∗
    world_interp W' C' ∗
    RevokedResources W C' la ∗
    ⌜ Forall (λ a, std W' !! a = Some Revoked) la⌝.
  Proof.
    rewrite world_interp_eq /world_interp_def RevokedResources_eq.
    iIntros (Hin) "([Hr [Hsts Hseals] ] & Hl)"; cbn.
    iMod (revoked_by_separation_many_with_temp_resources with "[$Hsts $Hr Hl]") as "(H & $ & $ & $)"; auto.
    by iFrame.
  Qed.

  (** ** Extension the world interpretation for safety invariants. *)

  (* Extend the world with a permanent safety invariant. *)
  Lemma world_interp_extend_perm
    {E : coPset}
    (W : WORLD) (C : CmptName) (a : Addr) (v : Word) (p : Perm) (φ : Vc)
    `{∀ Wv, Persistent (φ Wv)} :
    a ∉ dom (std W) →
    world_interp W C -∗
    PermRes W C a p φ v

    ={E}=∗

    world_interp (<s[a := Permanent ]s>W) C ∗
    rel C a p φ.
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros (?) "[Hr [Hsts Hseals] ] (%&?&?&?)".
    iMod (extend_region_perm with "[$] [$] [$] [$] [$]") as "($ & $ & $)"; auto.
    iDestruct (sealing_map_monotone_pub with "Hseals") as "$"; auto.
    apply related_sts_pub_world_fresh; auto.
  Qed.

  (* Extend the world with a temporary safety invariant. *)
  Lemma world_interp_extend_temp
    {E : coPset}
    (W : WORLD) (C : CmptName) (a : Addr) (v : Word) (p : Perm) (φ : Vc)
    `{∀ Wv, Persistent (φ Wv)} :
    a ∉ dom (std W) →
    world_interp W C -∗
    TmpRes W C a p φ v

    ={E}=∗

    world_interp (<s[a := Temporary ]s>W) C ∗
    rel C a p φ.
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros (?) "[Hr [Hsts Hseals] ] (%&?&?&?)"; rewrite  mono_temporary_eq.
    iMod (extend_region_temp with "[$] [$] [$] [$] [$]") as "($ & $ & $)"; auto.
    iDestruct (sealing_map_monotone_pub with "Hseals") as "$"; auto.
    apply related_sts_pub_world_fresh; auto.
  Qed.

  (* Extend the world with several permanent safety invariants. *)
  Lemma world_interp_extend_perm_sepL2
    {E : coPset}
    (W : WORLD) (C : CmptName) (la : list Addr) (lw : list Word) (p : Perm) (φ : Vc)
    `{∀ Wv, Persistent (φ Wv)} :
    isO p = false ->
    Forall (λ k, std W !! k = None) la →
    world_interp W C -∗
    ([∗ list] a;v ∈ la;lw, PermRes W C a p φ v)

    ={E}=∗

    world_interp (std_update_multiple W la Permanent) C ∗
    ([∗ list] k ∈ la, rel C k p φ).
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros (??) "[Hr [Hsts Hseals] ] Hres".
    iMod (extend_region_perm_sepL2 with "Hsts Hr [Hres]") as "($&$&$)"; eauto.
    { iApply (big_sepL2_impl with "Hres").
      iModIntro; iIntros (k a v Ha Hv) "(%&?&?&?)"; iFrame. }
    iDestruct (sealing_map_monotone_pub with "Hseals") as "$"; auto.
    - by rewrite std_update_multiple_seals.
    - apply related_sts_pub_update_multiple.
      eapply Forall_impl; eauto.
      intros a Ha; cbn in *.
      by rewrite not_elem_of_dom.
  Qed.

  (* Extend the world with several temporary safety invariants. *)
  Lemma world_interp_extend_temp_sepL2
    {E : coPset}
    (W : WORLD) (C : CmptName) (la : list Addr) (lw : list Word) (p : Perm) (φ : Vc)
    `{∀ Wv, Persistent (φ Wv)} :
    isO p = false ->
    Forall (λ k, std W !! k = None) la →
    world_interp W C -∗
    ([∗ list] a;v ∈ la;lw, TmpRes W C a p φ v)

    ={E}=∗

    world_interp (std_update_multiple W la Temporary) C ∗
    ([∗ list] k ∈ la, rel C k p φ).
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros (??) "[Hr [Hsts Hseals] ] Hres".
    iMod (extend_region_temp_sepL2 with "Hsts Hr [Hres]") as "($&$&$)"; auto.
    { iApply (big_sepL2_impl with "Hres").
      iModIntro; iIntros (k a v Ha Hv) "(%&?&?&?)"; iFrame.
      by rewrite mono_temporary_eq.
    }
    iDestruct (sealing_map_monotone_pub with "Hseals") as "$"; auto.
    - by rewrite std_update_multiple_seals.
    - apply related_sts_pub_update_multiple.
      eapply Forall_impl; eauto.
      intros a Ha; cbn in *.
      by rewrite not_elem_of_dom.
  Qed.

  (* Pre-allocate safety invariant: extend the world with several Revoked safety invariants. *)
  Lemma world_interp_extend_revoked_sepL2
    {E : coPset}
    (W : WORLD) (C : CmptName) (la : list Addr) (p : Perm) (φ : Vc)
    `{∀ Wv, Persistent (φ Wv)}:
    Forall (λ k, std W !! k = None) la →
    world_interp W C

     ={E}=∗

     world_interp (std_update_multiple W la Revoked) C ∗
     ([∗ list] k ∈ la, rel C k p φ).
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros (?) "[Hr [Hsts Hseals] ]".
    iMod (extend_region_revoked_sepL2 with "Hsts Hr") as "($&$&$)"; auto.
    iDestruct (sealing_map_monotone_pub with "Hseals") as "$"; auto.
    - by rewrite std_update_multiple_seals.
    - apply related_sts_pub_update_multiple.
      eapply Forall_impl; eauto.
      intros a Ha; cbn in *.
      by rewrite not_elem_of_dom.
  Qed.


  (* Extend the world with several permanent safety invariants.
     This lemma assumes that the safety invariants only hold if they have already been allocated,
     for in-region capabilities. *)
  Lemma world_interp_extend_perm_sepL2_open
    {E : coPset}
    (W : WORLD) (C : CmptName) (la : list Addr) (lw : list Word) (p : Perm) (φ : Vc)
    `{∀ Wv, Persistent (φ Wv)} :
    let W' := (std_update_multiple W la Permanent) in
    NoDup la ->
    isO p = false ->
    Forall (λ k, std W !! k = None) la →
    world_interp W C -∗
    ([∗ list] k;v ∈ la;lw, k ↦ₐ v) -∗
    (
      ([∗ list] k ∈ la, rel C k p φ)
      -∗
      ([∗ list] v ∈ lw, (φ (W', C, v)) ∗ future_priv_mono C φ v)
    )

    ={E}=∗

    world_interp W' C ∗
    ([∗ list] k ∈ la, rel C k p φ) ∗
    ([∗ list] v ∈ lw, (φ (W', C, v)) ∗ future_priv_mono C φ v).
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros (HNoDup Hp Hla) "[Hr [Hsts Hseals] ] Hreg Hl".
    iMod (extend_region_perm_sepL2_open with "Hsts Hr Hreg Hl") as "($&$&$)"; auto.
    iDestruct (sealing_map_monotone_pub with "Hseals") as "$"; auto.
    - by rewrite std_update_multiple_seals.
    - apply related_sts_pub_update_multiple.
      eapply Forall_impl; eauto.
      intros a Ha; cbn in *.
      by rewrite not_elem_of_dom.
  Qed.

  Lemma world_interp_extend_perm_sepL2_open'
    {E : coPset}
    (W : WORLD) (C : CmptName) (la : list Addr) (lw : list Word) (p : Perm) (φ : Vc)
    (o : OType) (ws ws_sealed : gset Word)
    `{∀ Wv, Persistent (φ Wv)} :
    let W' := (<o[ o := ws ]o> (std_update_multiple W la Permanent)) in
    NoDup la ->
    isO p = false ->
    Forall (λ k, std W !! k = None) la →
    world_interp W C -∗
    ([∗ list] k;v ∈ la;lw, k ↦ₐ v) -∗
    (
      ([∗ list] k ∈ la, rel C k p φ) ∗
      world_interp_open (std_update_multiple W la Permanent) C la
      ==∗
      world_interp_open W' C la ∗
      ([∗ list] v ∈ lw, (φ (W', C, v)) ∗ future_priv_mono C φ v) ∗
      ([∗ set] v ∈ ws_sealed, (φ (W', C, v)))
    )

    ={E}=∗

    world_interp W' C ∗
    ([∗ list] k ∈ la, rel C k p φ) ∗
    ([∗ list] v ∈ lw, (φ (W', C, v)) ∗ future_priv_mono C φ v) ∗
    ([∗ set] v ∈ ws_sealed, (φ (W', C, v)))
  .
  Proof.
    rewrite world_interp_eq /world_interp_def.
    rewrite world_interp_open_eq /world_interp_open_def.
    iIntros (HNoDup Hp Hla) "[Hr [Hsts Hseals] ] Hreg Hl".
    iMod (extend_region_perm_sepL2_open' with "Hsts Hr Hseals Hreg [Hl]") as "($&$&$)"; auto.
    iIntros "(Hrel & Hsts & Hseals & Hr)".
    iMod ("Hl" with "[$Hrel $Hr $Hsts $Hseals]") as "(($&$&$)&$&$)".
    done.
  Qed.


  (** ** Interface with custom world. *)

  (* Allocation of a new custom invariant in the world. *)
  Lemma world_interp_alloc_loc
    { D : Type } {eqd : EqDecision D} {countD : Countable D}
    {E : coPset}
    (W : WORLD) (C : CmptName) (d : D) (rpub rpriv : D → D → Prop) :
    let i := fresh_cus_name W in
    world_interp W C
    ={E}=∗
    world_interp (<l[ i := d , (rpub,rpriv) ]l> W) C ∗
    ⌜i ∉ dom (loc W)⌝ ∗
    ⌜i ∉ dom (wrel W)⌝ ∗
    sts_state_loc C i d ∗ sts_rel_loc C i rpub rpriv.
  Proof.
    intros i.
    rewrite world_interp_eq /world_interp_def.

    iIntros "[Hr [Hsts Hseals] ]".
    iDestruct (sts_alloc_loc W C d rpub rpriv with "Hsts") as ">($ & $ & $ & $ & $)"; auto.
    iDestruct (region_monotone with "Hr") as "$"; auto.
    - subst i.
      eapply related_sts_pub_world_fresh_loc; eauto
      ; intro Hcontra
      ; apply (fresh_name_notin W (fresh_cus_name W))
      ; try done ; [by left | by right].
    - iDestruct (sealing_map_monotone_pub with "Hseals") as "$"; auto.
      apply related_sts_pub_world_fresh_loc; subst i.
      + intro H; apply (fresh_name_notin W (fresh_cus_name W)); auto.
      + intro H; apply (fresh_name_notin W (fresh_cus_name W)); auto.
  Qed.

  (* Update of custom invariant in the world. *)
  Lemma world_interp_update_loc
    { D : Type } {eqd : EqDecision D} {countD : Countable D}
    {E : coPset}
    (W : WORLD) (C' : CmptName) (i : positive) (d d' : D) :
    revoke_condition W ->
    related_sts_priv_world W (<l[i:=d']l>W) ->
    world_interp W C' -∗
    sts_state_loc C' i d
    ={E}=∗
    world_interp (<l[ i := d' ]l> W) C' ∗
    sts_state_loc C' i d'.
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros (Hrevoke_conditions Hrelated) "[Hr [Hsts Hseals] ] Hst_i".
    iMod (sts_update_loc _ _ _ _ d' with "Hsts Hst_i") as "[Hsts Hst_i]".
    iMod (update_region_revoked_update_loc with "Hsts Hr" ) as "[Hr Hsts]"; auto.
    iFrame.
    iDestruct (sealing_map_monotone with "Hseals") as "$"; auto.
  Qed.

  (* Get the STS (relations) of a custom invariant in the world. *)
  Lemma world_interp_rel_loc_valid
    { D : Type } {eqd : EqDecision D} {countD : Countable D}
    (W : WORLD) (C' : CmptName) (i : positive)
    (rpub rpriv: D -> D -> Prop) :
    world_interp W C' -∗
    sts_rel_loc C' i rpub rpriv
    -∗
    ⌜ wrel W !! i = Some (convert_rel rpub,convert_rel rpriv)⌝.
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros "[Hr [Hsts Hseals] ] Hsts_rel".
    iDestruct (sts_full_rel_loc  with "Hsts Hsts_rel") as "$".
  Qed.

  (* Get the STS (current state) of a custom invariant in the world. *)
  Lemma world_interp_loc_valid
    { D : Type } {eqd : EqDecision D} {countD : Countable D}
    (W : WORLD) (C' : CmptName) (i : positive) (d : D) :
    world_interp W C' -∗
    sts_state_loc C' i d
    -∗
    ⌜loc W !! i = Some (encode d)⌝.
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros "[Hr [Hsts Hseals] ] Hst_i".
    iDestruct (sts_full_state_loc  with "Hsts Hst_i") as "$".
  Qed.

  (** ** Interface with sealing map *)
  Lemma world_interp_seal_pred_singleton (W : WORLD) (C : CmptName) (o : OType) Po `{Hpers: ∀ WCv, Persistent (Po WCv)} (w : Word) :
    seal_pred o Po -∗
    sts_seals_std C o {[ w ]} -∗
    world_interp W C -∗
    ▷ (world_interp W C ∗ Po (W, C, force_global w)).
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros "#Hspred Hseal ($ & Hsts & Hseals)".
    iDestruct (sealing_map_seal_pred with "Hspred Hseal Hseals Hsts") as "($ & $ & H)"; eauto.
    by rewrite normalise_sealed_words_singleton big_sepS_singleton.
  Qed.

  Lemma world_interp_open_seal_pred_singleton
    (W : WORLD) (C : CmptName) (s : list Addr) (o : OType) Po `{Hpers: ∀ WCv, Persistent (Po WCv)} (w : Word) :
    seal_pred o Po -∗
    sts_seals_std C o {[ w ]} -∗
    world_interp_open W C s -∗
    ▷ (world_interp_open W C s ∗ Po (W, C, force_global w)).
  Proof.
    rewrite world_interp_open_eq /world_interp_open_def.
    iIntros "#Hspred Hseal ($ & Hsts & Hseals)".
    iDestruct (sealing_map_seal_pred with "Hspred Hseal Hseals Hsts") as "($ & $ & H)"; eauto.
    by rewrite normalise_sealed_words_singleton big_sepS_singleton.
  Qed.

  Lemma world_interp_sealing_update (W : WORLD) (C : CmptName) (Po : WORLD * CmptName * Word → iProp Σ)
    (o : OType) (ws ws' : gset Word)  :
    let W' := (<o[ o := ws' ∪ ws ]o> W) in
    (seal_std W) !! o = Some ws ->
    seal_pred o Po -∗
    ([∗ set] w ∈ (normalise_sealed_words ws'), ▷ Po (W', C, w)) -∗
    world_interp W C
    ==∗
    world_interp W' C ∗ sts_seals_std C o (ws' ∪ ws).
  Proof.
    intros W' HWo.
    rewrite world_interp_eq /world_interp_def.
    iIntros "Hpred Hs (Hr & Hsts & Hseals)".
    iMod (sealing_map_update with "Hpred Hs [$Hseals $Hsts]") as "($&$&$)"; eauto.
    iApply (region_monotone with "Hr"); auto.
    subst W'.
    apply related_sts_pub_world_update_ot.
  Qed.

  Lemma world_interp_sealing_update' (W : WORLD) (C : CmptName) (Po : WORLD * CmptName * Word → iProp Σ)
    (o : OType) (ws : gset Word)  :
    let W' := (<o[ o := ws ]o> W) in
    seal_pred o Po -∗
    (∀ w : Word, future_priv_mono C Po w) -∗
    ([∗ set] w ∈ (normalise_sealed_words ws), ▷ Po (W', C, w)) -∗
    world_interp W C
    ==∗
    world_interp W' C ∗ sts_seals_std C o ws.
  Proof.
    intros W'.
    rewrite world_interp_eq /world_interp_def.
    iIntros "Hpred Hmono Hs (Hr & Hsts & Hseals)".
    iMod (sealing_map_update' with "Hpred Hmono Hs [$Hseals $Hsts]") as "($&$&$)"; eauto.
    iApply (region_monotone with "Hr"); auto.
    subst W'.
    apply related_sts_pub_world_update_ot.
  Qed.

  Lemma world_interp_open_sealing_update'
    (W : WORLD) (C : CmptName) (s : list Addr) (Po : WORLD * CmptName * Word → iProp Σ)
    (o : OType) (ws : gset Word)  :
    let W' := (<o[ o := ws ]o> W) in
    seal_pred o Po -∗
    (∀ w : Word, future_priv_mono C Po w) -∗
    ([∗ set] w ∈ (normalise_sealed_words ws), ▷ Po (W', C, w)) -∗
    world_interp_open W C s
    ==∗
    world_interp_open W' C s ∗ sts_seals_std C o ws.
  Proof.
    intros W'.
    rewrite world_interp_open_eq /world_interp_open_def.
    iIntros "Hpred Hmono Hs (Hr & Hsts & Hseals)".
    iMod (sealing_map_update' with "Hpred Hmono Hs [$Hseals $Hsts]") as "($&$&$)"; eauto.
    iApply (open_region_many_monotone with "Hr"); auto.
    subst W'.
    apply related_sts_pub_world_update_ot.
  Qed.

  Lemma world_interp_salloc
    (W : WORLD) (C : CmptName) (Po : WORLD * CmptName * Word → iProp Σ) (o : OType) (ws : gset Word)  :
    let W' := (<o[ o := ws ]o> W) in
    o ∉ dom (seal_std W) ->
    seal_pred o Po -∗
    (∀ w : Word, future_priv_mono C Po w) -∗
    ([∗ set] w ∈ (normalise_sealed_words ws), ▷ Po (W', C, w)) -∗
    world_interp W C ==∗
    world_interp W' C ∗ sts_seals_std C o ws.
  Proof.
    intros.
    rewrite world_interp_eq /world_interp_def.
    iIntros "Hpred Hmono Hs [Hr [Hsts Hseals] ]".
    iMod (sealing_map_alloc with "Hpred Hmono Hs [$Hsts $Hseals]") as "($&$&$)"; auto.
    iApply (region_monotone with "Hr"); auto.
    apply related_sts_pub_world_update_ot.
  Qed.

  (** ** Initialisation of the world interpretation and resources. *)

  (* Initialise the permanent resources *)
  Definition init_PermRes (W : WORLD) (C : CmptName) (a : Addr) (p : Perm) (Φ : Vc) (w : Word) :
    isO p = false ->
    future_priv_mono C Φ w -∗
    a ↦ₐ w -∗
    Φ (W,C,w)
    -∗
    PermRes W C a p Φ w.
    Proof. iIntros (HpO) "Hmono Ha HΦ"; iFrame; done. Qed.

    (* Initialise the temporary resources *)
    Definition init_TmpRes (W : WORLD) (C : CmptName) (a : Addr) (p : Perm) (Φ : Vc) (w : Word) :
      isO p = false ->
      (if isWL p then future_pub_mono C Φ w else
         (if isDL p then future_pub_mono C Φ w else future_priv_mono C Φ w))-∗
      a ↦ₐ w -∗
      Φ (W,C,w)
      -∗
      TmpRes W C a p Φ w.
    Proof. rewrite -mono_temporary_eq; iIntros (HpO) "Hmono Ha HΦ"; iFrame; done. Qed.

    Definition init_WorldRes (W : WORLD) (C : CmptName) (a : Addr) (p : Perm) (Φ : Vc) (w : Word) (ρ: region_type) :
      ρ ≠ Revoked ->
      isO p = false ->
      monotonicity_guarantees_region C Φ p w ρ -∗
      a ↦ₐ w -∗
      Φ (W,C,w)
      -∗
      WorldRes W C a p Φ w ρ.
    Proof.
      iIntros (Hne HpO) "Hmono Ha HΦ"; iFrame "%∗".
      rewrite mono_invariant_monotonicity_guarantees_region; eauto.
    Qed.

End world_ghost_theory.

(** ** Initialise the world in the adequacy theorem *)
Section world_interp_Pre.
  Context {Σ:gFunctors}
          {Cname : CmptNameG}
          {ceriseg : ceriseG Σ}
          {sts_preg: STS_preG Addr region_type OType Word Σ}
          {relpreg : relGpreS Σ}
          {sealstorepreg: sealStorePreG Σ}
.

  Lemma world_interp_init (oset : gset OType) :
    ⊢ |==> (∃ (relg: relGS Σ) (stsg : STSG Addr region_type OType Word Σ) (sstoreg : sealStoreG Σ),
            ([∗ set] C ∈ CNames, world_interp (∅, (∅,∅), ∅) C) ∗
            ([∗ set] o ∈ oset, can_alloc_pred o)).
  Proof.
    iMod (gen_sts_init) as (stsg) "Hsts". (*XX*)
    iMod (rel_init) as (relg) "HRELS".
    iMod (seal_store_init) as (sstoreg) "Hseals".
    iExists relg, stsg, sstoreg; iFrame "Hseals".
    set (Wempty := (∅, (∅,∅), ∅)).
    iAssert ([∗ set] C ∈ CNames, region Wempty C)%I with "[HRELS]" as "Hr".
    { iApply (big_sepS_impl with "HRELS").
      iModIntro; iIntros (C HC) "HRELS".
      rewrite region_eq /region_def. iExists ∅, ∅. iFrame.
      rewrite /= !dom_empty_L //. repeat iSplit; eauto.
      rewrite /region_map_def. by rewrite big_sepM_empty.
    }
    iCombine "Hr" "Hsts" as "H".
    rewrite -big_sepS_sep.
    iModIntro.
    iApply (big_sepS_impl with "H").
    rewrite world_interp_eq /world_interp_def.
    iModIntro; iIntros (C HC) "[$ $]".
    iApply sealing_map_empty.
  Qed.

End world_interp_Pre.
