From iris.algebra Require Import gmap agree auth excl csum excl_auth.
From iris.proofmode Require Import proofmode.
From griotte Require Export stdpp_extra rules_base.
From griotte Require Export sts world_std_sts world_ghost_resources heap_region.

  (*** Interpretation of the standard world *)

  (** This file defines the interpretation of the standard world.
      In particular, the standard world owns the safety resources,
      which interprets the safety predicates.

      This file also defines the interpretation of opened standards worlds,
      which means that the world does not own the safety resources (owned by the user),
      and which means that the safety predicate do not have to be currently enforced.

      Finally, this file defines lemma to open / close the standard world.
   *)

  (** * Disclaimer to the users of Griotte:

      All the lemmas and definitions in this file are internal to the Griotte model.
      To manipulate the world in the proofs, see [world_ghost_theory.v].

  *)

Section standard_world_interp.

  Context {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {Cname : CmptNameG} {CNames : gset CmptName}
    {stsg : STSG LAddr region_type OType Word Σ}
    {relg : relGS Σ} {allocatorg : allocatorG Σ}
    `{MP: MachineParameters}.

  (* ----------------------------------------------------------------------------------------------- *)
  (* ------------------------------------------- REGION_MAP ---------------------------------------- *)
  (* ----------------------------------------------------------------------------------------------- *)

  (** The standard-world state interpretation, independently of physical
      heap quarantine. *)
  Definition region_std_interp (W : WORLD) (C : CmptName) (k : LAddr)
    (p : Perm) (φ : WORLD * CmptName * Word → iProp Σ) (ρ : region_type) : iProp Σ :=
    (match ρ with
     | Temporary =>
         ∃ (v : Word), ⌜isO p = false⌝
                       ∗ k ↦ₖ v
                       ∗ (if isWL p then future_pub_mono C φ v
                          else if isDL p then future_pub_mono C φ v
                          else future_priv_mono C φ v)
                       ∗ ▷ φ (W,C,v)
     | Permanent =>
         ∃ (v : Word), ⌜isO p = false⌝
                       ∗ k ↦ₖ v
                       ∗ future_priv_mono C φ v
                       ∗ ▷ φ (W,C,v)
     | Revoked => emp
     end)%I.

  Definition region_map_def
    (W : WORLD)
    (C : CmptName)
    (MC : gmap LAddr (gname * Perm))
    (Mρ: gmap LAddr region_type) :=
    (⌜heap_keys_known (heap_std W) (dom (std W))⌝ ∗
     (heap_std_fragments C (heap_std W) ∗
      heap_provenance (heap_std W)) ∗
     [∗ map] k↦γp ∈ MC,
       ∃ ρ, ⌜Mρ !! k = Some ρ⌝
            ∗ sts_state_std C k ρ
            ∗ ∃ γpred p φ, ⌜γp = (γpred,p)⌝
                    ∗ ⌜∀ Wv, Persistent (φ Wv)⌝
                    ∗ saved_pred_own γpred DfracDiscarded φ
                    ∗ heap_key_resource (heap_std W) k (region_std_interp W C k p φ ρ))%I.

  Definition region_def (W : WORLD) (C : CmptName) : iProp Σ :=
    (∃ (M : relT) (Mρ: gmap LAddr region_type),
        RELS C M
        ∗ ⌜dom (std W) = dom M⌝
        ∗ ⌜dom Mρ = dom M⌝
        ∗ region_map_def W C M Mρ)%I.
  Definition region_aux : { x | x = @region_def }. by eexists. Qed.
  Definition region := proj1_sig region_aux.
  Definition region_eq : @region = @region_def := proj2_sig region_aux.

  Lemma region_rel_get (W : WORLD) (C : CmptName) (a : LAddr) :
    (std W) !! a = Some Temporary ->
    region W C ∗ sts_full_world W C
    ==∗
    region W C ∗ sts_full_world W C ∗ ∃ p φ, ⌜forall WCv, Persistent (φ WCv)⌝ ∗ rel C a p φ.
  Proof.
    iIntros (Hlookup) "[Hr Hsts]".
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ) "(HM & %Hdom & %Hdom' & Hr)".
    iDestruct "Hr" as "[%Hcovered Hr]".
    iDestruct "Hr" as "[Hheap Hr]".
    assert (is_Some (M !! a)) as [ [γ p] Hγp].
    { apply elem_of_dom.
      rewrite -Hdom. rewrite elem_of_dom; eauto.
    }
    iMod (reg_get with "[$HM]") as "[HM Hrel]";[eauto|].
    iDestruct (big_sepM_delete _ _ a with "Hr") as "[Hstate Hr]";[eauto|].
    iDestruct "Hstate" as (ρ Ha) "[Hρ Hstate]".
    iDestruct (sts_full_state_std with "Hsts Hρ") as %Hx''; simplify_eq.
    all: iDestruct "Hstate" as (γpred p' φ Heq Hpers) "(#Hsaved & Ha)".
    all: iDestruct (big_sepM_delete _ _ a with "[Hρ Ha $Hr]") as "Hr";[eauto| |].
    { iExists Temporary. iFrame "∗#%". }
    all: iModIntro.
    all: iSplitL "HM Hr Hheap".
    { iExists M. iFrame "∗#%". }
    all: iFrame; iExists p,φ; iSplit;auto; rewrite rel_eq /rel_def; iExists γpred.
    all: simplify_eq; iFrame "Hsaved Hrel".
  Qed.

  Lemma region_rel_get_state W C (a : LAddr) ρ :
    std W !! a = Some ρ ->
    region W C ∗ sts_full_world W C
    ==∗
    region W C ∗ sts_full_world W C ∗
    ∃ p φ, ⌜∀ WCv, Persistent (φ WCv)⌝ ∗ rel C a p φ.
  Proof.
    iIntros (Hlookup) "[Hr Hsts]".
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ) "(HM & %Hdom & %Hdomρ & Hmap)".
    rewrite /region_map_def.
    iDestruct "Hmap" as "(%Hcovered & Hheap & Hentries)".
    assert (is_Some (M !! a)) as [γp Hγp].
    { apply elem_of_dom. rewrite -Hdom elem_of_dom. eauto. }
    destruct γp as [γ p].
    iMod (reg_get with "[$HM]") as "[HM Hrel]";
      first (iPureIntro; exact Hγp).
    iDestruct (big_sepM_delete _ _ a with "Hentries") as "[Hentry Hentries]";
      first exact Hγp.
    iDestruct "Hentry" as (ρ' Hρ') "[Hstate Hentry]".
    iDestruct (sts_full_state_std with "Hsts Hstate") as %Hρeq.
    rewrite Hlookup in Hρeq. injection Hρeq as <-.
    iDestruct "Hentry" as (γpred p' φ Heq Hpers) "(#Hsaved & Haddr)".
    iDestruct (big_sepM_delete _ _ a with "[Hstate Haddr $Hentries]")
      as "Hentries"; [exact Hγp| |].
    { iExists ρ. iFrame "∗#%". }
    iModIntro. iSplitL "HM Hheap Hentries".
    { iExists M, Mρ. iFrame "HM".
      iFrame "%". rewrite /region_map_def. iFrame "Hheap Hentries". }
    iFrame "Hsts".
    iExists p', φ. iSplit; first done.
    rewrite rel_eq /rel_def. iExists γpred.
    simplify_eq. iFrame "Hsaved Hrel".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* region_map is monotone with regards to public future world relation *)
  Lemma region_map_monotone (C : CmptName) (W W' : WORLD) M Mρ :
    related_sts_pub_world W W' ->
    heap_std W = heap_std W'
    → heap_wf (heap_std W') ->
    heap_keys_known (heap_std W') (dom (std W')) ->
    region_map_def W C M Mρ
    -∗ region_map_def W' C M Mρ.
  Proof.
    iIntros (Hrelated Hheap Hheap_wf Hknown') "Hr".
    iDestruct "Hr" as "[%Hknown Hr]".
    iDestruct "Hr" as "[Hheap Hr]".
    iSplit; first done.
    iSplitL "Hheap".
    { rewrite -Hheap. iFrame. }
    iApply (big_sepM_mono with "Hr").
    iIntros (a γ Hsome) "Hm".
    iDestruct "Hm" as (ρ Hρ) "[Hstate Hm]".
    iExists ρ. iFrame. iSplitR; first done.
    iDestruct "Hm" as (γpred p φ Heq Hpers) "(#Hsavedφ & Hl)".
    iExists γpred, p, φ. iFrame "%#". rewrite -Hheap.
    iApply (heap_key_resource_mono with "[] Hl"). iIntros "Hl".
    destruct ρ; cbn [region_std_interp]; last done.
    - iDestruct "Hl" as (v Hne) "(Hl & #HmonoV & Hφ)".
      iFrame "%#∗".
      destruct (isWL p); [| destruct (isDL p)]; (iApply "HmonoV"; eauto; iFrame).
      iPureIntro; apply related_sts_pub_priv_world in Hrelated; naive_solver.
    - iDestruct "Hl" as (v Hne) "(Hl & #HmonoV & Hφ)".
      iFrame "%#∗".
      iApply "HmonoV"; iFrame "∗#"; auto.
      iPureIntro; apply related_sts_pub_priv_world in Hrelated; naive_solver.
  Qed.

  Lemma region_monotone C W W':
    dom (std W) = dom (std W')
    -> related_sts_pub_world W W'
    -> heap_std W = heap_std W'
    → heap_wf (heap_std W') ->
    region W C
    -∗ region W' C.
  Proof.
    iIntros (Hdomeq Hrelated Hheap Hheap_wf) "HW". rewrite region_eq.
    iDestruct "HW" as (M Mρ) "(HM & %Hdom & %Hdomρ & Hmap)"; simplify_map_eq.
    iExists M, Mρ. iFrame "HM".
    iSplitR.
    { iPureIntro. rewrite -Hdomeq Hdom; done. }
    iSplitR; first done.
    iAssert (⌜heap_keys_known (heap_std W) (dom (std W))⌝)%I as %Hknown.
    { by iDestruct "Hmap" as "[% _]". }
    iApply region_map_monotone; last eauto; eauto.
    by rewrite -Hdomeq -Hheap.
  Qed.

  (* ----------------------------------------------------------------------------------------------- *)
  (* ------------------------------------------- OPEN_REGION --------------------------------------- *)
  (* ----------------------------------------------------------------------------------------------- *)

  Definition open_region_def (W : WORLD) (C : CmptName) (a : LAddr) : iProp Σ :=
    (∃ (M : relT) (Mρ: gmap LAddr region_type),
        RELS C M
        ∗ ⌜dom (std W) = dom M⌝
        ∗ ⌜dom Mρ = dom M⌝
        ∗ region_map_def W C (delete a M) (delete a Mρ))%I.
  Definition open_region_aux : { x | x = @open_region_def }. by eexists. Qed.
  Definition open_region := proj1_sig open_region_aux.

  (* ----------------------------------------------------------------------------------------------- *)
  (* ------------------------- LEMMAS FOR OPENING THE REGION MAP ----------------------------------- *)
  (* ----------------------------------------------------------------------------------------------- *)

  Lemma region_map_delete W C M Mρ a :
    region_map_def W C (delete a M) Mρ -∗
    region_map_def W C (delete a M) (delete a Mρ).
  Proof.
    iIntros "Hr". iDestruct "Hr" as "[%Hknown Hr]".
    iDestruct "Hr" as "[Hheap Hr]".
    iSplit; first done.
    iFrame "Hheap".
    iApply (big_sepM_mono with "Hr").
    iIntros (a' γr Ha') "HH".
    iDestruct "HH" as (ρ Hρ) "(Hsts & HH)".
    iExists ρ.
    iSplitR; eauto.
    { iPureIntro. destruct (decide (a' = a)); simplify_map_eq/=. congruence. }
    iFrame.
  Qed.

  (* It is important here that we have (delete l Mρ) and not simply Mρ.
     Otherwise, [Mρ !! l] could in principle map to a frozen region (although
     it's not the case in practice), that it would be incorrect to overwrite
     with a non-frozen state. *)
  Lemma region_map_undelete W C M Mρ a :
    region_map_def W C (delete a M) (delete a Mρ) -∗
    region_map_def W C (delete a M) Mρ.
  Proof.
    iIntros "Hr". iDestruct "Hr" as "[%Hknown Hr]".
    iDestruct "Hr" as "[Hheap Hr]".
    iSplit; first done.
    iFrame "Hheap".
    iApply (big_sepM_mono with "Hr").
    iIntros (a' γr Ha) "HH". iDestruct "HH" as (ρ Hρ) "(Hsts & HH)".
    iExists ρ.
    iSplitR; eauto.
    { iPureIntro. destruct (decide (a' = a)); simplify_map_eq/=. congruence. }
    iFrame.
  Qed.

  Lemma region_map_insert W C M Mρ a ρ :
    region_map_def W C (delete a M) (delete a Mρ) -∗
    region_map_def W C (delete a M) (<[ a := ρ ]> Mρ).
  Proof.
    iIntros "HH".
    rewrite {1}(_: delete a Mρ = delete a (<[ a := ρ ]> Mρ)). 2: by rewrite delete_insert_eq//.
    iDestruct (region_map_undelete with "HH") as "HH".
    auto.
  Qed.

  (* ---------------------------------------------------------------------------------------- *)
  (* ----------------------- OPENING MULTIPLE LOCATIONS IN REGION --------------------------- *)
  (* ---------------------------------------------------------------------------------------- *)

  Definition open_region_many_def  (W : WORLD) (C : CmptName) (l : list LAddr) : iProp Σ :=
    (∃ (M : relT) (Mρ: gmap LAddr region_type),
        RELS C M
        ∗ ⌜dom (std W) = dom M⌝
        ∗ ⌜dom Mρ = dom M⌝
        ∗ region_map_def W C (delete_list l M) (delete_list l Mρ))%I.
  Definition open_region_many_aux : { x | x = @open_region_many_def }. by eexists. Qed.
  Definition open_region_many := proj1_sig open_region_many_aux.
  Definition open_region_many_eq : @open_region_many = @open_region_many_def := proj2_sig open_region_many_aux.

  Lemma open_region_many_permutation W C l1 l2:
    l1 ≡ₚ l2 → open_region_many W C l1 -∗ open_region_many W C l2.
  Proof.
    intros Hperm.
    rewrite open_region_many_eq /open_region_many_def.
    iIntros "H". iDestruct "H" as (? ?) "(? & % & ?)".
    rewrite !(delete_list_permutation l1 l2); try done.
    iExists _,_. iFrame. eauto.
  Qed.

  Lemma open_region_many_monotone (C : CmptName) (W W' : WORLD) l:
    dom (std W) = dom (std W')
    -> related_sts_pub_world W W'
    -> heap_std W = heap_std W'
    -> heap_wf (heap_std W') ->
    open_region_many W C l -∗ open_region_many W' C l.
  Proof.
    iIntros (Hdomeq Hrelated Hheap Hheap_wf) "HW".
    rewrite open_region_many_eq /open_region_many_def.
    iDestruct "HW" as (M Mρ) "(Hm & %Hdom & %Hdomρ & Hmap)" ; simplify_eq.
    iExists M, Mρ. iFrame "Hm".
    iSplitR; first (iPureIntro; congruence).
    iSplitR; first done.
    iAssert (⌜heap_keys_known (heap_std W) (dom (std W))⌝)%I as %Hknown.
    { by iDestruct "Hmap" as "[% _]". }
    iApply region_map_monotone; last eauto; eauto.
    by rewrite -Hdomeq -Hheap.
  Qed.

  (** The world knows the identifier of every heap key, open or not. *)
  Lemma open_region_many_keys_known W C l :
    open_region_many W C l -∗ ⌜heap_keys_known (heap_std W) (dom (std W))⌝.
  Proof.
    rewrite open_region_many_eq /open_region_many_def.
    iIntros "H". iDestruct "H" as (M Mρ) "(_ & _ & _ & % & _)". done.
  Qed.

  Lemma region_open_nil W C :
    region W C ⊣⊢ open_region_many W C [].
  Proof.
    iSplit; iIntros "H";
    rewrite region_eq open_region_many_eq /=;
            iFrame.
  Qed.

  Lemma region_open_next_temp_pwl W C φ als k p :
    heap_key_live (heap_std W) k ->
    k ∉ als →
    (std W) !! k = Some Temporary ->
    isWL p = true →
    open_region_many W C als ∗ rel C k p φ ∗ sts_full_world W C -∗
    ∃ v, open_region_many W C (k :: als)
         ∗ sts_full_world W C
         ∗ sts_state_std C k Temporary
         ∗ k ↦ₖ v
         ∗ ⌜isO p = false⌝
         ∗ ▷ future_pub_mono C φ v
         ∗ ▷ φ (W,C,v).
  Proof.
    intros Hlive.
    rewrite open_region_many_eq .
    iIntros (Hnin Htemp Hpwl) "(Hopen & #Hrel & Hfull)".
    rewrite /open_region_many_def /region_map_def /=.
    rewrite rel_eq /rel_def /rel_def /region_def /rel /region.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]".
    iDestruct "Hopen" as (M Mρ) "(HM & % & % & Hpreds)"; simplify_eq.
    iDestruct "Hpreds" as "[%Hknown Hpreds]".
    iDestruct "Hpreds" as "[Hheap Hpreds]".
    iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq;eauto.
    rewrite HMeq delete_list_insert; auto.
    rewrite delete_list_delete; auto.
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete_eq].
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ Hρ) "[Hstate Hl]".
    iDestruct (sts_full_state_std with "Hfull Hstate") as %Hst.
    rewrite Htemp in Hst. (destruct ρ; try by simplify_eq); [].
    iDestruct "Hl" as (γpred' p' φ' HH Hpers) "(#Hφ' & Hl)".
    iDestruct (heap_key_resource_live_elim _ _ _ Hlive with "Hl") as "Hl".
    iDestruct "Hl" as (v Hne) "(Hl & #HmonoV & Hφv)".
    inversion HH; subst. rewrite Hpwl.
    iDestruct (saved_pred_agree _ _ _ _ _ (W,C,v) with "Hφ Hφ'") as "#Hφeq".
    iFrame "HM Hfull Hstate Hl".
    iSplitR "Hφv".
    - iExists Mρ. repeat (rewrite -HMeq).
      iSplitR; first eauto.
      iSplitR; first eauto.
      iApply region_map_delete; iFrame "%∗".
    - repeat (iSplitR).
      + auto.
      + iApply future_pub_mono_eq_pred; auto.
      + iNext; iRewrite "Hφeq". iFrame.
  Qed.

  Lemma region_open_next_temp_nwl W C φ als k p :
    heap_key_live (heap_std W) k ->
    k ∉ als →
    (std W) !! k = Some Temporary ->
    isWL p = false →
    open_region_many W C als ∗ rel C k p φ ∗ sts_full_world W C -∗
    ∃ v, open_region_many W C (k :: als)
         ∗ sts_full_world W C
         ∗ sts_state_std C k Temporary
         ∗ k ↦ₖ v
         ∗ ⌜isO p = false⌝
         ∗ ▷ (if isDL p then future_pub_mono C φ v else future_priv_mono C φ v)
         ∗ ▷ φ (W,C,v).
  Proof.
    intros Hlive.
    rewrite open_region_many_eq .
    iIntros (Hnin Htemp Hpwl) "(Hopen & #Hrel & Hfull)".
    rewrite /open_region_many_def /region_map_def /=.
    rewrite rel_eq /rel_def /rel_def /region_def /rel /region.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]".
    iDestruct "Hopen" as (M Mρ) "(HM & % & % & Hpreds)"; simplify_eq.
    iDestruct "Hpreds" as "[%Hknown Hpreds]".
    iDestruct "Hpreds" as "[Hheap Hpreds]".
    iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq;eauto.
    rewrite HMeq delete_list_insert; auto.
    rewrite delete_list_delete; auto.
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete_eq].
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ Hρ) "[Hstate Hl]".
    iDestruct (sts_full_state_std with "Hfull Hstate") as %Hst.
    rewrite Htemp in Hst. (destruct ρ; try by simplify_eq); [].
    iDestruct "Hl" as (γpred' p' φ' HH Hpers) "(#Hφ' & Hl)".
    iDestruct (heap_key_resource_live_elim _ _ _ Hlive with "Hl") as "Hl".
    iDestruct "Hl" as (v Hne) "(Hl & #HmonoV & Hφv)".
    inversion HH; subst. rewrite Hpwl.
    iDestruct (saved_pred_agree _ _ _ _ _ (W,C,v) with "Hφ Hφ'") as "#Hφeq".
    iFrame "HM Hfull Hstate Hl".
    iSplitR "Hφv".
    - iExists Mρ. repeat (rewrite -HMeq).
      iSplitR; first eauto.
      iSplitR; first eauto.
      iApply region_map_delete; iFrame "%∗".
    - repeat (iSplitR).
      + auto.
      + destruct (isDL p').
        * iApply future_pub_mono_eq_pred; auto.
        * iApply future_priv_mono_eq_pred; auto.
      + iNext; iRewrite "Hφeq". iFrame.
  Qed.

  Lemma region_open_next_perm W C φ als k p :
    heap_key_live (heap_std W) k ->
    k ∉ als → (std W) !! k = Some Permanent ->
    open_region_many W C als
    ∗ rel C k p φ
    ∗ sts_full_world W C
    -∗ ∃ v,
        sts_full_world W C
        ∗ sts_state_std C k Permanent
        ∗ open_region_many W C (k :: als)
        ∗ k ↦ₖ v
        ∗ ⌜isO p = false⌝
        ∗ ▷ (future_priv_mono C φ v)
        ∗ ▷ φ (W,C,v).
  Proof.
    intros Hlive.
    rewrite open_region_many_eq .
    iIntros (Hnin Htemp) "(Hopen & #Hrel & Hfull)".
    rewrite /open_region_many_def /= /region_map_def.
    rewrite rel_eq /rel_def /rel_def /region_def /rel /region.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]".
    iDestruct "Hopen" as (M Mρ) "(HM & % & % & Hpreds)"; simplify_eq.
    iDestruct "Hpreds" as "[%Hknown Hpreds]".
    iDestruct "Hpreds" as "[Hheap Hpreds]".
    iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq;eauto.
    rewrite HMeq delete_list_insert; auto.
    rewrite delete_list_delete; auto.
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete_eq].
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ Hρ) "[Hstate Hl]".
    iDestruct (sts_full_state_std with "Hfull Hstate") as %Hst.
    rewrite Htemp in Hst. (destruct ρ; try by simplify_eq); [].
    iDestruct "Hl" as (γpred' p' φ' HH Hpers) "(#Hφ' & Hl)".
    iDestruct (heap_key_resource_live_elim _ _ _ Hlive with "Hl") as "Hl".
    iDestruct "Hl" as (v Hne) "(Hl & #HmonoV & Hφv)".
    inv HH.
    iDestruct (saved_pred_agree _ _ _ _ _ (W,C,v) with "Hφ Hφ'") as "#Hφeq".
    iExists _. iFrame "HM Hfull Hstate Hl".
    iSplitR "Hφv".
    - rewrite /open_region.
      iExists Mρ. repeat (rewrite -HMeq).
      iSplitR; first eauto.
      iSplitR; first eauto.
      iApply region_map_delete; iFrame "%∗".
    - repeat (iSplitR).
      + auto.
      + iApply future_priv_mono_eq_pred; auto.
      + iNext; iRewrite "Hφeq". iFrame.
  Qed.

  Lemma region_close_next_temp_pwl W C φ als k p v `{forall Wv, Persistent (φ Wv)} :
    heap_key_live (heap_std W) k ->
    k ∉ als ->
    isWL p = true →
    sts_state_std C k Temporary
    ∗ open_region_many W C (k :: als)
    ∗ k ↦ₖ v
    ∗ ⌜isO p = false⌝
    ∗ future_pub_mono C φ v
    ∗ ▷ φ (W,C,v)
    ∗ rel C k p φ
    -∗ open_region_many W C als.
  Proof.
    intros Hlive.
    rewrite open_region_many_eq /open_region_many_def.
    iIntros (Hnin Hpwl) "(Hstate & Hreg_open & Hl & % & #HmonoV & Hφ & #Hrel)".
    rewrite rel_eq /rel_def /rel /region.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & % & %Hdomρ & Hpreds)".
    iDestruct (region_map_insert _ _ _ _ _ Temporary with "Hpreds") as "Hpreds".
    iDestruct "Hpreds" as "[%Hknown Hpreds]".
    iDestruct "Hpreds" as "[Hheap Hpreds]".
    rewrite -!/delete_list.
    iDestruct (big_sepM_insert _ (delete k (delete_list als M)) k with "[-HM Hheap]") as "test";
      first by rewrite lookup_delete_eq.
    { iFrame. iSplitR; [by simplify_map_eq|].
      iExists _,p,_. iSplitR; first done. iFrame "%#". iApply heap_key_resource_live_intro; first exact Hlive.
      rewrite /region_std_interp Hpwl. iFrame "∗ #%". }
    rewrite -(delete_list_delete _ M) //.
    rewrite -(delete_list_insert _ (delete k M)) //.
    rewrite -(delete_list_insert _ Mρ) //.
    iExists M, (<[k :=Temporary]> Mρ).
    iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq;eauto.
    rewrite -HMeq.
    iFrame "∗ # %".
    repeat(iSplitR; eauto).
    all: try (by rewrite HMeq insert_delete_eq !dom_insert_L Hdomρ).
    all: iFrame "∗#%".
  Qed.

  Lemma region_close_next_temp_nwl W C φ als k p v `{forall Wv, Persistent (φ Wv)} :
    heap_key_live (heap_std W) k ->
    k ∉ als ->
    isWL p = false →
    sts_state_std C k Temporary
    ∗ open_region_many W C (k :: als)
    ∗ k ↦ₖ v
    ∗ ⌜isO p = false⌝
    ∗ (if isDL p then future_pub_mono C φ v else future_priv_mono C φ v)
    ∗ ▷ φ (W,C,v)
    ∗ rel C k p φ
      -∗ open_region_many W C als.
  Proof.
    intros Hlive.
    rewrite open_region_many_eq /open_region_many_def.
    iIntros (Hnin Hpwl) "(Hstate & Hreg_open & Hl & % & #HmonoV & Hφ & #Hrel)".
    rewrite rel_eq /rel_def /rel /region.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & % & %Hdomρ & Hpreds)".
    iDestruct (region_map_insert _ _ _ _ _ Temporary with "Hpreds") as "Hpreds".
    iDestruct "Hpreds" as "[%Hknown Hpreds]".
    iDestruct "Hpreds" as "[Hheap Hpreds]".
    rewrite -!/delete_list.
    iDestruct (big_sepM_insert _ (delete k (delete_list als M)) k with "[-HM Hheap]") as "test";
      first by rewrite lookup_delete_eq.
    { iFrame. iSplitR; [by simplify_map_eq|].
      iExists _,p,_. iSplitR; first done. iFrame "%#". iApply heap_key_resource_live_intro; first exact Hlive.
      rewrite /region_std_interp Hpwl. iFrame "∗ #%". }
    rewrite -(delete_list_delete _ M) //.
    rewrite -(delete_list_insert _ (delete k M)) //.
    rewrite -(delete_list_insert _ Mρ) //.
    iExists M, (<[k :=Temporary]> Mρ).
    iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq;eauto.
    rewrite -HMeq.
    iFrame "∗ # %".
    repeat(iSplitR; eauto).
    all: try (by rewrite HMeq insert_delete_eq !dom_insert_L Hdomρ).
    all: iFrame "∗#%".
  Qed.

  Lemma region_close_next_perm W C φ als k p v `{forall Wv, Persistent (φ Wv)} :
    heap_key_live (heap_std W) k ->
    k ∉ als ->
    ⊢ sts_state_std C k Permanent
    ∗ open_region_many W C (k :: als)
    ∗ k ↦ₖ v
    ∗ ⌜isO p = false⌝
    ∗ future_priv_mono C φ v
    ∗ ▷ φ (W,C,v)
    ∗ rel C k p φ
      -∗ open_region_many W C als.
  Proof.
    intros Hlive.
    rewrite open_region_many_eq /open_region_many_def.
    iIntros (Hnin) "(Hstate & Hreg_open & Hl & % & #HmonoV & Hφ & #Hrel)".
    rewrite rel_eq /rel_def /rel /region.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & % & %Hdomρ & Hpreds)".
    iDestruct (region_map_insert _ _ _ _ _ Permanent with "Hpreds") as "Hpreds".
    iDestruct "Hpreds" as "[%Hknown Hpreds]".
    iDestruct "Hpreds" as "[Hheap Hpreds]".
    rewrite -!/delete_list.
    iDestruct (big_sepM_insert _ (delete k (delete_list als M)) k with "[-HM Hheap]") as "test";
      first by rewrite lookup_delete_eq.
    { iFrame.
      iSplitR; [by simplify_map_eq|].
      iExists _,_,_. iSplitR; first done. iFrame "%#". iApply heap_key_resource_live_intro; first exact Hlive. cbn [region_std_interp]. iFrame "∗ #%".
    }
    rewrite -(delete_list_delete _ M) // -(delete_list_insert _ (delete _ M)) //.
    rewrite -(delete_list_insert _ Mρ) //.
    iExists M, (<[k :=Permanent]> Mρ).
    iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq;eauto.
    rewrite -HMeq.
    iFrame "∗ # %".
    repeat(iSplitR; eauto).
    all: try (by rewrite HMeq insert_delete_eq !dom_insert_L Hdomρ).
    all: iFrame "∗#%".
  Qed.

  Definition monotonicity_guarantees_region
    (C : CmptName) (φ : WORLD * CmptName * Word → iProp Σ)
    (p : Perm) (w : Word) (ρ : region_type) :=
    (match ρ with
     | Temporary => (if isWL p then future_pub_mono else (if isDL p then future_pub_mono else future_priv_mono))
     | Permanent => future_priv_mono
     | Revoked => λ _ _ _, True
     end C φ w)%I.

  Definition monotonicity_guarantees_decide
    (C : CmptName) (φ : WORLD * CmptName * Word → iProp Σ)
    (p : Perm) (w : Word) (ρ : region_type) :=
    (if decide (ρ = Temporary)
     then (if isWL p then future_pub_mono C φ w else (if isDL p then future_pub_mono C φ w else future_priv_mono C φ w))
     else future_priv_mono C φ w )%I.

  (*Lemma that allows switching between the two different formulations of monotonicity, to alleviate the effects of inconsistencies*)
  Lemma switch_monotonicity_formulation
    (C : CmptName) (φ : WORLD * CmptName * Word → iProp Σ)
    (p : Perm) (w : Word) (ρ : region_type) :
    ρ ≠ Revoked →
    monotonicity_guarantees_region C φ p w ρ  ≡ monotonicity_guarantees_decide C φ p w ρ.
  Proof.
    intros Hrev.
    unfold monotonicity_guarantees_region, monotonicity_guarantees_decide.
    iSplit; iIntros "HH".
    - destruct ρ;simpl;auto;try done.
      destruct (isWL p), (isDL p);done.
    - destruct ρ;simpl;auto;try done.
      destruct (isWL p), (isDL p); done.
  Qed.

  Global Instance monotonicity_guarantees_region_Persistent C P p w ρ :
    Persistent (monotonicity_guarantees_region C P p w ρ).
  Proof.
    destruct ρ; cbn; try apply _.
    all: destruct (isWL p), (isDL p); try apply _.
  Qed.

  Lemma region_open_next
    (W : WORLD) (C : CmptName)
    (φ : WORLD * CmptName * Word → iProp Σ)
    (als : list LAddr) (k : LAddr) (p : Perm) (ρ : region_type)
    (Hρnotrevoked : ρ <> Revoked) :
    heap_key_live (heap_std W) k ->
    k ∉ als →
    std W !! k = Some ρ →
    ⊢ open_region_many W C als
    ∗ rel C k p φ
    ∗ sts_full_world W C
    -∗ ∃ v : Word,
        sts_full_world W C
        ∗ sts_state_std C k ρ
        ∗ open_region_many W C (k :: als)
        ∗ k ↦ₖ v
        ∗ ▷ monotonicity_guarantees_region C φ p v ρ
        ∗ ▷ φ (W, C, v)
        ∗ ⌜isO p = false⌝.
  Proof.
    intros Hlive.
    rewrite /monotonicity_guarantees_region.
    intros. iIntros "H".
    destruct ρ; try congruence.
    - case_eq (isWL p); intros.
      + iDestruct (region_open_next_temp_pwl with "H") as (v) "[A [B [C [D [E [F G]]]]]]"
        ; eauto; iFrame.
      + iDestruct (region_open_next_temp_nwl with "H") as (v) "[A [B [C [D [E [F G]]]]]]"
        ; eauto; iFrame.
        destruct (isDL p); eauto.
    - iDestruct (region_open_next_perm with "H") as (v) "[A [B [C [D [E [F G]]]]]]"
      ; eauto; iFrame.
  Qed.

  Lemma region_open_list (W : WORLD) (C : CmptName)
    (l : list (LAddr * Perm * (WORLD * CmptName * Word → iProp Σ) * region_type))
    (l' : list LAddr)
   :

    let la  := (fmap (fun '(a,p,φ,ρ) => a) l) in
    Forall (fun '(a,p,φ,ρ) => heap_key_live (heap_std W) a) l ->
    NoDup la ->
    la ## l' ->
    Forall (fun '(a,p,φ,ρ) => ρ ≠ Revoked) l ->
    Forall (fun '(a,p,φ,ρ) => (std W) !! a = Some ρ) l ->

    ([∗ list] '(a,p,φ,ρ) ∈ l, rel C a p φ)
    ∗ open_region_many W C l'
    ∗ sts_full_world W C -∗

    ∃ lv,
      open_region_many W C (la++l')
      ∗ sts_full_world W C
      ∗ ([∗ list] '(a,p,φ,ρ) ∈ l, sts_state_std C a ρ)
      ∗ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, a ↦ₖ v)
      ∗ ▷ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, monotonicity_guarantees_region C φ p v ρ)
      ∗ ▷ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, φ (W,C,v))
      ∗ ⌜ length lv = length la ⌝
      ∗ ([∗ list] '(a,p,φ,ρ) ∈ l , ⌜ isO p = false ⌝)
  .
  Proof.
    induction l; intros la Hlive Hnodup Hdis Hregion_state Ha_state ;
      iIntros "(Hrel & Hr & Hsts)"; cbn in * |- *.
    - iExists []; cbn in *.
      by iFrame.
    - destruct a as [[[a p] φ] ρ]; cbn in * |- *.
      apply Forall_cons_1 in Hlive as [Hlive_a Hlive].
      iDestruct "Hrel" as "[Hrel_a Hrel]".
      apply NoDup_cons in Hnodup; destruct Hnodup as [Hnotin Hnodup].
      apply Forall_cons_1 in Hregion_state; destruct Hregion_state as [Hρ_a Hregion_state].
      apply Forall_cons_1 in Ha_state; destruct Ha_state as [HWa Ha_state].
      pose proof (disjoint_cons _ _ _ Hdis) as Ha_notin_l'.
      eapply disjoint_weak in Hdis.
      iDestruct (IHl with "[$Hrel $Hr $Hsts]") as "IH"; eauto.
      iDestruct "IH" as (lv) "(Hr & Hsts & Hsts_stds & Hlv & Hmono & Hlφ & %Hlen & Hp)".
      iDestruct (region_open_next with "[$Hr $Hrel_a $Hsts]") as "Ha"; eauto.
      {
        intros Hcontra.
        apply elem_of_app in Hcontra. destruct Hcontra as [Hcontra|Hcontra]
        ; [set_solver+Hcontra Hnotin|set_solver+Hcontra Ha_notin_l'].
      }
      iDestruct "Ha" as (va) "(Hsts & Hsts_std_a & Hr & Hv_a & Hmono_a & Hφ_a & %Hp_a)".
      iExists (va::lv); iFrame.
      iDestruct (big_sepL2_cons (fun _ '(a, _, _, _) v => (a ↦ₖ v)%I) (a,p,φ,ρ) va with "[$]") as "Hlv".
      iFrame.
      iSplitR "Hlφ Hφ_a"; [iNext|iSplit;[iNext|]].
      + iDestruct (big_sepL2_cons (fun _ '(a, p, φ, ρ) v => monotonicity_guarantees_region C φ p v ρ) (a,p,φ,ρ) va with "[$]") as "Hlφ".
        iFrame.
      + iDestruct (big_sepL2_cons (fun _ '(a, _, φ, _) v => φ (W, C, v)) (a,p,φ,ρ) va with "[$]") as "Hlφ".
        iFrame.
      + by cbn ; rewrite Hlen.
  Qed.

  Lemma region_close_next
    (W : WORLD) (C : CmptName)
    (φ : WORLD * CmptName * Word → iProp Σ)
    `{forall Wv, Persistent (φ Wv)}
    (als : list LAddr) (k : LAddr) (p : Perm) (v : Word) (ρ : region_type)
    (Hρnotrevoked : ρ <> Revoked) :
    heap_key_live (heap_std W) k ->
    k ∉ als
    → sts_state_std C k ρ
    ∗ open_region_many W C (k :: als)
    ∗ k ↦ₖ v
    ∗ ⌜isO p = false⌝
    ∗ monotonicity_guarantees_region C φ p v ρ
    ∗ ▷ φ (W, C, v)
    ∗ rel C k p φ
      -∗ open_region_many W C als.
  Proof.
    intros Hlive.
    rewrite /monotonicity_guarantees_region.
    intros. iIntros "[A [B [C [D [E [F G]]]]]]".
    destruct ρ; try congruence.
    - case_eq (isWL p); intros.
      + iApply (region_close_next_temp_pwl with "[A B C D E F G]"); eauto; iFrame.
      + iApply (region_close_next_temp_nwl with "[A B C D E F G]"); eauto; iFrame.
        destruct (isDL p); eauto.
    - iApply (region_close_next_perm with "[A B C D E F G]"); eauto; iFrame.
  Qed.

  Lemma region_close_list (W : WORLD) (C : CmptName)
    (l : list (LAddr * Perm * (WORLD * CmptName * Word → iProp Σ) * region_type))
    (l' : list LAddr)
    (lv : list Word)
   :

    let la  := (fmap (fun '(a,p,φ,ρ) => a) l) in
    length l = length lv ->
    Forall (fun '(a,p,φ,ρ) => heap_key_live (heap_std W) a) l ->
    NoDup la ->
    la ## l' ->
    Forall (fun '(a,p,φ,ρ) => ρ ≠ Revoked) l ->
    Forall (fun '(a,p,φ,ρ) => ∀ Wv : WORLD * CmptName * Word, Persistent (φ Wv)) l ->

    open_region_many W C (la++l')
    ∗ ([∗ list] '(a,p,φ,ρ) ∈ l, sts_state_std C a ρ)
    ∗ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, a ↦ₖ v)
    ∗ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, monotonicity_guarantees_region C φ p v ρ)
    ∗ ▷ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, φ (W,C,v))
    ∗ ([∗ list] '(a,p,φ,ρ) ∈ l, rel C a p φ)
    ∗ ([∗ list] '(a,p,φ,ρ) ∈ l , ⌜ isO p = false ⌝)
      -∗ open_region_many W C l'.
  Proof.
    generalize dependent lv.
    induction l; intros lv la Hlen Hlive Hnodup Hdis Hregion_state Hpers ;
      iIntros "(Hr & Hstd & Hv & Hmono & Hφ & Hrel & Hp)"; cbn in * |- *.
    - by iFrame.
    - destruct a as [[[a p] φ] ρ]; cbn in * |- *.
      apply Forall_cons_1 in Hlive as [Hlive_a Hlive].
      iDestruct "Hrel" as "[Hrel_a Hrel]".
      apply NoDup_cons in Hnodup; destruct Hnodup as [Hnotin Hnodup].
      apply Forall_cons_1 in Hregion_state; destruct Hregion_state as [Hρ_a Hregion_state].
      apply Forall_cons_1 in Hpers; destruct Hpers as [Hpers_a Hpers].
      pose proof (disjoint_cons _ _ _ Hdis) as Ha_notin_l'.
      eapply disjoint_weak in Hdis.
      destruct lv as [|va lv]; cbn in Hlen; simplify_eq.
      cbn.
      iDestruct "Hstd" as "[Hstd_a Hstd]".
      iDestruct "Hv" as "[Hv_a Hv]".
      iDestruct "Hφ" as "[Hφ_a Hφ]".
      iDestruct "Hmono" as "[Hmono_a Hmono]".
      iDestruct "Hp" as "[Hp_a Hp]".
      iDestruct (region_close_next with "[$Hstd_a $Hr $Hv_a $Hmono_a $Hφ_a $Hrel_a $Hp_a]") as "Hr"; eauto.
      {
        intros Hcontra.
        apply elem_of_app in Hcontra. destruct Hcontra as [Hcontra|Hcontra]
        ; [set_solver+Hcontra Hnotin|set_solver+Hcontra Ha_notin_l'].
      }
      iDestruct (IHl with "[$Hr $Hstd $Hv $Hmono $Hφ $Hrel $Hp]") as "IH"; eauto.
  Qed.

  (** A region of a quarantined object holds nothing: opening and closing it
      does not depend on its logical standard state. *)
  Lemma region_open_next_quarantined_heap W C als a ι p φ ρ o :
    heap_std W !! ι = Some o ->
    alloc_object_status o = AllocObjectQuarantined ->
    LHeap a ι ∉ als -> std W !! LHeap a ι = Some ρ ->
    open_region_many W C als ∗ rel C (LHeap a ι) p φ ∗ sts_full_world W C -∗
    open_region_many W C (LHeap a ι :: als) ∗ sts_full_world W C ∗
    sts_state_std C (LHeap a ι) ρ ∗ ⌜alloc_object_contains o a⌝.
  Proof.
    iIntros (Hι Hstatus Hnin Hstd) "(Hopen & #Hrel & Hfull)".
    rewrite open_region_many_eq /open_region_many_def /= /region_map_def.
    rewrite rel_eq /rel_def.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]".
    iDestruct "Hopen" as (M Mρ) "(HM & %Hdom & %Hdomρ & Hpreds)".
    iDestruct "Hpreds" as "[%Hknown Hpreds]".
    iDestruct "Hpreds" as "[Hheap Hpreds]".
    iDestruct (reg_in with "[$HM $Hγpred]") as %HMeq.
    rewrite HMeq delete_list_insert; auto.
    rewrite delete_list_delete; auto.
    rewrite HMeq big_sepM_insert; last by rewrite lookup_delete_eq.
    iDestruct "Hpreds" as "[Ha Hpreds]".
    iDestruct "Ha" as (ρ' Ha) "[Hstate Ha]".
    iDestruct (sts_full_state_std with "Hfull Hstate") as %Hstd'.
    rewrite Hstd in Hstd'. simplify_eq.
    iDestruct "Ha" as (γpred' p' φ' Heq Hpers) "[#Hsaved Ha]".
    iEval (rewrite /heap_key_resource Hι Hstatus) in "Ha".
    iDestruct "Ha" as "[%Hcontains _]".
    rewrite -!HMeq.
    iDestruct (region_map_delete with "[Hpreds Hheap]") as
      "[%Hknown' [Hheap Hpreds]]".
    { iFrame "%∗". }
    iSplitR "Hfull Hstate"; last by iFrame.
    iExists M,Mρ. iFrame "HM Hheap Hpreds %".
  Qed.

  Lemma region_close_next_quarantined_heap W C als a ι p φ ρ o
    `{∀ Wv, Persistent (φ Wv)} :
    heap_std W !! ι = Some o ->
    alloc_object_status o = AllocObjectQuarantined ->
    alloc_object_contains o a ->
    LHeap a ι ∉ als ->
    sts_state_std C (LHeap a ι) ρ ∗ open_region_many W C (LHeap a ι :: als) ∗
    rel C (LHeap a ι) p φ -∗ open_region_many W C als.
  Proof.
    iIntros (Hι Hstatus Hcontains Hnin) "(Hstate & Hopen & #Hrel)".
    rewrite open_region_many_eq /open_region_many_def.
    rewrite rel_eq /rel_def.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hsaved]".
    iDestruct "Hopen" as (M Mρ) "(HM & %Hdom & %Hdomρ & Hpreds)".
    iDestruct (region_map_insert _ _ _ _ _ ρ with "Hpreds") as "Hpreds".
    iDestruct "Hpreds" as "[%Hknown Hpreds]".
    iDestruct "Hpreds" as "[Hheap Hpreds]".
    rewrite -!/delete_list.
    iDestruct (big_sepM_insert _ (delete (LHeap a ι) (delete_list als M)) (LHeap a ι)
      with "[Hstate $Hpreds]") as "Hpreds";
      first by rewrite lookup_delete_eq.
    { iExists ρ. iFrame. iSplitR; first by rewrite lookup_insert_eq.
      iExists γpred,p,φ. iSplitR; first done. iFrame "%#".
      by iApply heap_key_resource_quarantined. }
    rewrite -(delete_list_delete _ M) // -(delete_list_insert _ (delete _ M)) //.
    rewrite -(delete_list_insert _ Mρ) //.
    iExists M,(<[LHeap a ι :=ρ]> Mρ).
    iDestruct (reg_in with "[$HM $Hγpred]") as %HMeq.
    rewrite -HMeq. iFrame "%∗".
    iPureIntro. by rewrite HMeq insert_delete_eq !dom_insert_L Hdomρ.
  Qed.

  (** The region map follows a heap future, given the new heap fragments and provenance. *)
  Lemma region_map_def_heap_future C W W' M Mρ (R : iProp Σ) :
    related_sts_pub_world W W' ->
    std W = std W' ->
    heap_wf (heap_std W') ->
    (heap_std_fragments C (heap_std W) ∗ heap_provenance (heap_std W) ==∗
       heap_std_fragments C (heap_std W') ∗ heap_provenance (heap_std W') ∗ R) -∗
    region_map_def W C M Mρ ==∗
    region_map_def W' C M Mρ ∗ R.
  Proof.
    iIntros (Hrelated Hstd Hheap_wf) "Hupd Hr".
    iDestruct "Hr" as "[%Hknown [Hheap Hr]]".
    iMod ("Hupd" with "Hheap") as "(Hfrags & Hprov & $)".
    iModIntro. iSplit.
    { iPureIntro. rewrite -Hstd. eapply heap_keys_known_mono; [|done|exact Hknown].
      intros ι Hι. apply elem_of_dom in Hι as [o Ho].
      destruct (proj1 (proj2 (proj2 (proj2 Hrelated))) ι o Ho) as (o' & Ho' & _).
      by apply elem_of_dom_2 in Ho'. }
    iFrame "Hfrags Hprov".
    iApply (big_sepM_mono with "Hr").
    iIntros (a γ Hsome) "Hm".
    iDestruct "Hm" as (ρ Hρ) "[Hstate Hm]".
    iExists ρ. iFrame. iSplitR; first done.
    iDestruct "Hm" as (γpred p φ Heq Hpers) "(#Hsavedφ & Hl)".
    iExists γpred, p, φ. iFrame "%#".
    iApply (heap_key_resource_future with "Hl"); first exact (proj2 (proj2 (proj2 Hrelated))).
    iIntros "Hl".
    destruct ρ; cbn [region_std_interp]; last done.
    - iDestruct "Hl" as (v Hne) "(Hl & #HmonoV & Hφ)".
      iFrame "%#∗".
      destruct (isWL p); [| destruct (isDL p)]; (iApply "HmonoV"; eauto; iFrame).
      iPureIntro; apply related_sts_pub_priv_world in Hrelated; naive_solver.
    - iDestruct "Hl" as (v Hne) "(Hl & #HmonoV & Hφ)".
      iFrame "%#∗".
      iApply "HmonoV"; iFrame "∗#"; auto.
      iPureIntro; apply related_sts_pub_priv_world in Hrelated; naive_solver.
  Qed.

End standard_world_interp.
