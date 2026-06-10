From iris.algebra Require Import gmap agree auth excl_auth.
From iris.proofmode Require Import proofmode.
From cap_machine Require Export stdpp_extra rules_base.
From cap_machine Require Export sts world_std_sts world_ghost_resources.

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
    {stsg : STSG Addr region_type Σ}
    {relg : relGS Σ}
    `{MP: MachineParameters}.
  Implicit Types W : WORLD.

  (* ----------------------------------------------------------------------------------------------- *)
  (* ------------------------------------------- REGION_MAP ---------------------------------------- *)
  (* ----------------------------------------------------------------------------------------------- *)

  Definition region_map_def
    (W : WORLD)
    (C : CmptName)
    (MC : gmap Addr (gname * Perm))
    (Mρ: gmap Addr region_type) :=
    ([∗ map] a↦γp ∈ MC,
       ∃ ρ, ⌜Mρ !! a = Some ρ⌝
            ∗ sts_state_std C a ρ
            ∗ ∃ γpred p φ, ⌜γp = (γpred,p)⌝
                    ∗ ⌜∀ Wv, Persistent (φ Wv)⌝
                    ∗ saved_pred_own γpred DfracDiscarded φ
                    ∗ match ρ with
                      | Temporary =>
                          ∃ (v : Word), ⌜isO p = false⌝
                                        ∗ a ↦ₐ v
                                        ∗ (if isWL p
                                           then future_pub_mono C φ v
                                           else (if isDL p
                                                 then future_pub_mono C φ v
                                                 else future_priv_mono C φ v)
                                          )
                                        ∗ ▷ φ (W,C,v)
                      | Permanent =>
                          ∃ (v : Word), ⌜isO p = false⌝
                                        ∗ a ↦ₐ v
                                        ∗ future_priv_mono C φ v
                                        ∗ ▷ φ (W,C,v)
                       | Revoked => emp
     end)%I.

  Definition region_def (W : WORLD) (C : CmptName) : iProp Σ :=
    (∃ (M : relT) (Mρ: gmap Addr region_type),
        RELS C M
        ∗ ⌜dom (std W) = dom M⌝
        ∗ ⌜dom Mρ = dom M⌝
        ∗ region_map_def W C M Mρ)%I.
  Definition region_aux : { x | x = @region_def }. by eexists. Qed.
  Definition region := proj1_sig region_aux.
  Definition region_eq : @region = @region_def := proj2_sig region_aux.

  Lemma region_rel_get (W : WORLD) (C : CmptName) (a : Addr) :
    (std W) !! a = Some Temporary ->
    region W C ∗ sts_full_world W C
    ==∗
    region W C ∗ sts_full_world W C ∗ ∃ p φ, ⌜forall WCv, Persistent (φ WCv)⌝ ∗ rel C a p φ.
  Proof.
    iIntros (Hlookup) "[Hr Hsts]".
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ) "(HM & %Hdom & %Hdom' & Hr)".
    assert (is_Some (M !! a)) as [ [γ p] Hγp].
    { apply elem_of_dom.
      rewrite -Hdom. rewrite elem_of_dom; eauto.
    }
    iMod (reg_get with "[$HM]") as "[HM Hrel]";[eauto|].
    iDestruct (big_sepM_delete _ _ a with "Hr") as "[Hstate Hr]";[eauto|].
    iDestruct "Hstate" as (ρ Ha) "[Hρ Hstate]".
    iDestruct (sts_full_state_std with "Hsts Hρ") as %Hx''; simplify_eq.
    all: iDestruct "Hstate" as (γpred p' φ Heq Hpers) "(#Hsaved & Ha)".
    all: iDestruct "Ha" as (v Hne) "(Ha & #HmonoV & #Hφ)".
    all: iDestruct (big_sepM_delete _ _ a with "[Hρ Ha HmonoV Hφ $Hr]") as "Hr";[eauto| |].
    { iExists Temporary. iFrame "∗#%". }
    all: iModIntro.
    all: iSplitL "HM Hr".
    { iExists M. iFrame "∗#%". }
    all: iFrame; iExists p,φ; iSplit;auto; rewrite rel_eq /rel_def; iExists γpred.
    all: simplify_eq; iFrame "Hsaved Hrel".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* region_map is monotone with regards to public future world relation *)
  Lemma region_map_monotone (C : CmptName) (W W' : WORLD) M Mρ :
    related_sts_pub_world W W'
    → region_map_def W C M Mρ
    -∗ region_map_def W' C M Mρ.
  Proof.
    iIntros (Hrelated) "Hr".
    iApply big_sepM_mono; iFrame.
    iIntros (a γ Hsome) "Hm".
    iDestruct "Hm" as (ρ Hρ) "[Hstate Hm]".
    iExists ρ. iFrame. iSplitR;[auto|].
    destruct ρ.
    - iDestruct "Hm" as (γpred p φ Heq Hpers) "(#Hsavedφ & Hl)".
      iDestruct "Hl" as (v Hne) "(Hl & #HmonoV & Hφ)".
      iFrame "%#∗".
      destruct (isWL p); [| destruct (isDL p)]; (iApply "HmonoV"; eauto; iFrame).
      iPureIntro; apply related_sts_pub_priv_world in Hrelated; naive_solver.
    - iDestruct "Hm" as (γpred p φ Heq Hpers) "(#Hsavedφ & Hl)".
      iDestruct "Hl" as (v Hne) "(Hl & #HmonoV & Hφ)".
      iFrame "%#∗".
      iApply "HmonoV"; iFrame "∗#"; auto.
      iPureIntro; apply related_sts_pub_priv_world in Hrelated; naive_solver.
    - done.
  Qed.

  Lemma region_monotone C W W':
    dom (std W) = dom (std W')
    -> related_sts_pub_world W W'
    → region W C
    -∗ region W' C.
  Proof.
    iIntros (Hdomeq Hrelated) "HW". rewrite region_eq.
    iDestruct "HW" as (M Mρ) "(HM & % & % & Hmap)"; simplify_map_eq.
    iExists M, Mρ. iFrame.
    repeat(iSplitR; auto).
    - iPureIntro;congruence.
    - iApply region_map_monotone; last eauto;eauto.
  Qed.

  (* ----------------------------------------------------------------------------------------------- *)
  (* ------------------------------------------- OPEN_REGION --------------------------------------- *)
  (* ----------------------------------------------------------------------------------------------- *)

  Definition open_region_def (W : WORLD) (C : CmptName) (a : Addr) : iProp Σ :=
    (∃ (M : relT) (Mρ: gmap Addr region_type),
        RELS C M
        ∗ ⌜dom (std W) = dom M⌝
        ∗ ⌜dom Mρ = dom M⌝
        ∗ region_map_def W C (delete a M) (delete a Mρ))%I.
  Definition open_region_aux : { x | x = @open_region_def }. by eexists. Qed.
  Definition open_region := proj1_sig open_region_aux.
  Definition open_region_eq : @open_region = @open_region_def := proj2_sig open_region_aux.

  (* open_region is monotone wrt public future worlds *)
  Lemma open_region_monotone C W W' a :
    dom (std W)  = dom (std W')
    -> related_sts_pub_world W W'
    → open_region W C a
    -∗ open_region W' C a.
  Proof.
    iIntros (Hdomeq Hrelated) "HW". rewrite open_region_eq /open_region_def.
    iDestruct "HW" as (M Mρ) "(HM & % & % & Hmap)"; simplify_map_eq.
    iExists M, Mρ. iFrame.
    repeat(iSplitR; auto).
    - iPureIntro;congruence.
    - iApply region_map_monotone; last eauto;eauto.
  Qed.

  (* ----------------------------------------------------------------------------------------------- *)
  (* ------------------------- LEMMAS FOR OPENING THE REGION MAP ----------------------------------- *)
  (* ----------------------------------------------------------------------------------------------- *)

  Lemma region_map_delete W C M Mρ a :
    region_map_def W C (delete a M) Mρ -∗
    region_map_def W C (delete a M) (delete a Mρ).
  Proof.
    iIntros "Hr". iApply (big_sepM_mono with "Hr").
    iIntros (a' γr Ha') "HH".
    iDestruct "HH" as (ρ Hρ) "(Hsts & HH)".
    iExists ρ.
    iSplitR; eauto.
    { iPureIntro. destruct (decide (a' = a)); simplify_map_eq/=. congruence. }
    iFrame.
  Qed.

  Lemma region_open_temp_pwl W C l p φ :
    (std W) !! l = Some Temporary →
    isWL p = true →
    rel C l p φ ∗ region W C ∗ sts_full_world W C -∗
    ∃ v, open_region W C l
         ∗ sts_full_world W C
         ∗ sts_state_std C l Temporary
         ∗ l ↦ₐ v
         ∗ ⌜isO p = false⌝
         ∗ ▷ future_pub_mono C φ v
         ∗ ▷ φ (W,C,v).
  Proof.
    iIntros (Htemp Hpwl) "(#Hrel & Hreg & Hfull)".
    rewrite rel_eq region_eq /rel_def /region_def /region_map_def.
    iDestruct "Hrel" as (γpred) "#(Hγpred & Hφ)".
    iDestruct "Hreg" as (M Mρ) "(HM & % & % & Hpreds)"; simplify_map_eq.
    (* assert that γrel = γrel' *)
    iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq;eauto.
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete_eq].
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ Hρ) "[Hstate Hl]".
    iDestruct (sts_full_state_std with "Hfull Hstate") as %Hst.
    rewrite Htemp in Hst. (destruct ρ; try by simplify_eq); [].
    iDestruct "Hl" as (γpred' p' φ' HH1 Hpers) "(#Hφ' & Hl)".
    iDestruct "Hl" as (v Hne) "(Hl & #HmonoV & Hφv)".
    inversion HH1; subst. rewrite Hpwl.
    iDestruct (saved_pred_agree _ _ _ _ _ (W,C,v) with "Hφ Hφ'") as "#Hφeq".
    iExists v. iFrame.
    iSplitR "Hφv".
    - rewrite open_region_eq /open_region_def.
      iExists _,Mρ. rewrite -HMeq.
      iFrame "∗ #".
      repeat (iSplitR; eauto).
      iApply region_map_delete;auto.
    - repeat (iSplitR).
      + auto.
      + iApply future_pub_mono_eq_pred; auto.
      + iNext; iRewrite "Hφeq". iFrame "∗ #".
  Qed.


  Lemma region_open_temp_nwl W C l p φ :
    (std W) !! l = Some Temporary →
    isWL p = false →
    rel C l p φ ∗ region W C ∗ sts_full_world W C -∗
        ∃ v, open_region W C l
           ∗ sts_full_world W C
           ∗ sts_state_std C l Temporary
           ∗ l ↦ₐ v
           ∗ ⌜isO p = false⌝
           ∗ ▷ (if isDL p then future_pub_mono C φ v else future_priv_mono C φ v)
           ∗ ▷ φ (W,C,v).
  Proof.
    iIntros (Htemp Hpwl) "(#Hrel & Hreg & Hfull)".
    rewrite rel_eq region_eq /rel_def /region_def /region_map_def.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]".
    iDestruct "Hreg" as (M Mρ) "(HM & % & % & Hpreds)"; simplify_map_eq.
    iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq;eauto.
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete_eq].
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ Hρ) "[Hstate Hl]".
    iDestruct (sts_full_state_std with "Hfull Hstate") as %Hst.
    rewrite Htemp in Hst. (destruct ρ; try by simplify_eq); [].
    iDestruct "Hl" as (γpred' p' φ' HH Hpers) "(#Hφ' & Hl)".
    iDestruct "Hl" as (v Hne) "(Hl & #HmonoV & Hφv)".
    inversion HH; subst. rewrite Hpwl.
    iDestruct (saved_pred_agree _ _ _ _ _ (W,C,v) with "Hφ Hφ'") as "#Hφeq".
    iExists v. iFrame.
    iSplitR "Hφv".
    - rewrite open_region_eq /open_region_def.
      iExists _,Mρ. iFrame "∗ #".
      rewrite -HMeq.
      repeat (iSplitR; eauto).
      iApply region_map_delete; auto.
    - repeat (iSplitR).
      + auto.
      + destruct (isDL p').
        * iApply future_pub_mono_eq_pred; auto.
        * iApply future_priv_mono_eq_pred; auto.
      + iNext; iRewrite "Hφeq". iFrame "∗ #".
  Qed.

  Lemma region_open_perm W C l p φ :
    (std W) !! l = Some Permanent →
    rel C l p φ ∗ region W C ∗ sts_full_world W C -∗
    ∃ v, open_region W C l
         ∗ sts_full_world W C
         ∗ sts_state_std C l Permanent
         ∗ l ↦ₐ v
         ∗ ⌜isO p = false⌝
         ∗ ▷ future_priv_mono C φ v
         ∗ ▷ φ (W,C,v).
  Proof.
    iIntros (Htemp) "(#Hrel & Hreg & Hfull)".
    rewrite rel_eq region_eq /rel_def /region_def /region_map_def.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]".
    iDestruct "Hreg" as (M Mρ) "(HM & % & % & Hpreds)"; simplify_map_eq.
    (* assert that γrel = γrel' *)
    iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq;eauto.
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete_eq].
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ Hρ) "[Hstate Hl]".
    iDestruct (sts_full_state_std with "Hfull Hstate") as %Hst.
    rewrite Htemp in Hst. (destruct ρ; try by simplify_eq); [].
    iDestruct "Hl" as (γpred' p' φ' HH Hpers) "(#Hφ' & Hl)".
    iDestruct "Hl" as (v Hne) "(Hl & #HmonoV & Hφv)".
    inversion HH; subst.
    iDestruct (saved_pred_agree _ _ _ _ _ (W,C,v) with "Hφ Hφ'") as "#Hφeq".
    iExists v. iFrame.
    iSplitR "Hφv".
    - rewrite open_region_eq /open_region_def.
      iExists _,Mρ. iFrame "∗ #".
      rewrite -HMeq.
      repeat (iSplitR; eauto).
      iApply region_map_delete; auto.
    - repeat (iSplitR).
      + auto.
      + iApply future_priv_mono_eq_pred; auto.
      + iNext; iRewrite "Hφeq". iFrame "∗ #".
  Qed.

  Lemma region_open W C a p φ (ρ : region_type) :
    ρ = Temporary ∨ ρ = Permanent →
    (std W) !! a = Some ρ →
    rel C a p φ ∗ region W C ∗ sts_full_world W C -∗
    ∃ v, open_region W C a
         ∗ sts_full_world W C
         ∗ sts_state_std C a ρ
         ∗ a ↦ₐ v
         ∗ ⌜isO p = false⌝
         ∗ (▷ if (decide (ρ = Temporary))
              then ( if isWL p
                     then future_pub_mono C φ v
                     else (if isDL p then future_pub_mono C φ v else future_priv_mono C φ v))
              else future_priv_mono C φ v)
         ∗ ▷ φ (W,C,v).
  Proof.
    iIntros (Hne Htemp) "(Hrel & Hreg & Hfull)".
    destruct ρ; try (destruct Hne; exfalso; congruence).
    - destruct (isWL p) eqn:Hpwl.
      + iDestruct (region_open_temp_pwl with "[$Hrel $Hreg $Hfull]") as (v) "(Hr & Hfull & Hstate & Hl & Hp & Hmono & φ)"; auto.
        iExists _; iFrame.
      + iDestruct (region_open_temp_nwl with "[$Hrel $Hreg $Hfull]") as (v) "(Hr & Hfull & Hstate & Hl & Hp & Hmono & φ)"; auto.
        iExists _; iFrame.
    - iDestruct (region_open_perm with "[$Hrel $Hreg $Hfull]") as (v) "(Hr & Hfull & Hstate & Hl & Hp & Hmono & φ)"; auto.
      iExists _; iFrame.
  Qed.

  (* It is important here that we have (delete l Mρ) and not simply Mρ.
     Otherwise, [Mρ !! l] could in principle map to a frozen region (although
     it's not the case in practice), that it would be incorrect to overwrite
     with a non-frozen state. *)
  Lemma region_map_undelete W C M Mρ a :
    region_map_def W C (delete a M) (delete a Mρ) -∗
    region_map_def W C (delete a M) Mρ.
  Proof.
    iIntros "Hr". iApply (big_sepM_mono with "Hr").
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

   (* Closing the region without updating the sts collection *)
  Lemma region_close_temp_pwl W C a φ p v `{forall Wv, Persistent (φ Wv)} :
    isWL p = true →
    sts_state_std C a Temporary
    ∗ open_region W C a
    ∗ a ↦ₐ v
    ∗ ⌜isO p = false⌝
    ∗ future_pub_mono C φ v
    ∗ ▷ φ (W,C,v)
    ∗ rel C a p φ
    -∗ region W C.
  Proof.
    iIntros (Hpwl) "(Hstate & Hreg_open & Hl & % & #HmonoV & Hφ & #Hrel)".
    rewrite open_region_eq rel_eq region_eq /open_region_def /rel_def /region_def.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & % & %Hdomρ & Hpreds)".
    iDestruct (region_map_insert _ _ _ _ _ Temporary  with "Hpreds") as "Hpreds".
    iDestruct ( (big_sepM_insert _ (delete a M) a) with "[-HM]") as "test";
      first by rewrite lookup_delete_eq.
    { iFrame. iSplitR; [by simplify_map_eq|].
      iExists _,p,_. rewrite Hpwl. iFrame "#∗". repeat (iSplitR;eauto).
    }
    iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq;eauto.
    rewrite -HMeq.
    iFrame "∗ # %".
    iPureIntro.
    by rewrite HMeq insert_delete_eq !dom_insert_L Hdomρ.
  Qed.

  Lemma region_close_temp_nwl W C a φ p v `{forall Wv, Persistent (φ Wv)} :
    isWL p = false →
    sts_state_std C a Temporary
    ∗ open_region W C a
    ∗ a ↦ₐ v
    ∗ ⌜isO p = false⌝
    ∗ (if isDL p then future_pub_mono C φ v else future_priv_mono C φ v)
    ∗ ▷ φ (W,C,v)
    ∗ rel C a p φ
    -∗ region W C.
  Proof.
    iIntros (Hpwl) "(Hstate & Hreg_open & Hl & % & #HmonoV & Hφ & #Hrel)".
    rewrite open_region_eq rel_eq region_eq /open_region_def /rel_def /region_def.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & % & %Hdomρ & Hpreds)".
    iDestruct (region_map_insert _ _ _ _ _ Temporary  with "Hpreds") as "Hpreds".
    iDestruct ( (big_sepM_insert _ (delete a M) a) with "[-HM]") as "test";
      first by rewrite lookup_delete_eq.
    { iFrame. iSplitR; [by simplify_map_eq|].
      iExists _,p,_. rewrite Hpwl. iFrame "#∗". repeat (iSplitR;eauto).
    }
    iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq;eauto.
    rewrite -HMeq.
    iFrame "∗ # %".
    iPureIntro.
    by rewrite HMeq insert_delete_eq !dom_insert_L Hdomρ.
  Qed.

  Lemma region_close_perm W C a p φ v `{forall Wv, Persistent (φ Wv)}:
    ⊢ sts_state_std C a Permanent
      ∗ open_region W C a
      ∗ a ↦ₐ v
      ∗ ⌜isO p = false⌝
      ∗ future_priv_mono C φ v
      ∗ ▷ φ (W,C,v)
      ∗ rel C a p φ
      -∗ region W C.
  Proof.
    iIntros "(Hstate & Hreg_open & Hl & % & #HmonoV & Hφ & #Hrel)".
    rewrite open_region_eq rel_eq region_eq /open_region_def /rel_def /region_def.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & % & %Hdomρ & Hpreds)".
    iDestruct (region_map_insert _ _ _ _ _ Permanent  with "Hpreds") as "Hpreds".
    iDestruct ( (big_sepM_insert _ (delete a M) a) with "[-HM]") as "test";
      first by rewrite lookup_delete_eq.
    { iFrame. iSplitR; [by simplify_map_eq|].
      iFrame "∗ #". repeat (iSplitR;[eauto|]). iFrame. auto. }
    iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq;eauto.
    rewrite -HMeq.
    iFrame "∗ # %".
    iPureIntro.
    by rewrite HMeq insert_delete_eq !dom_insert_L Hdomρ.
  Qed.

  Lemma region_close W C a φ p v (ρ : region_type) `{forall Wv, Persistent (φ Wv)} :
    ρ = Temporary ∨ ρ = Permanent →
    sts_state_std C a ρ
    ∗ open_region W C a
    ∗ a ↦ₐ v
    ∗ ⌜isO p = false⌝
    ∗ (if (decide (ρ = Temporary))
       then ( if isWL p
              then future_pub_mono C φ v
              else (if isDL p then future_pub_mono C φ v else future_priv_mono C φ v))
       else future_priv_mono C φ v)
    ∗ ▷ φ (W,C,v)
    ∗ rel C a p φ
      -∗ region W C.
  Proof.
    iIntros (Htp) "(Hstate & Hreg_open & Hl & Hp & HmonoV & Hφ & Hrel)".
    destruct ρ; try (destruct Htp; exfalso; congruence).
    - destruct (isWL p) eqn:Hpwl.
      + iApply region_close_temp_pwl; eauto; iFrame.
      + iApply region_close_temp_nwl; eauto; iFrame.
    - iApply region_close_perm; eauto; iFrame.
  Qed.

  (* ---------------------------------------------------------------------------------------- *)
  (* ----------------------- OPENING MULTIPLE LOCATIONS IN REGION --------------------------- *)
  (* ---------------------------------------------------------------------------------------- *)

  Definition open_region_many_def  (W : WORLD) (C : CmptName) (l : list Addr) : iProp Σ :=
    (∃ (M : relT) (Mρ: gmap Addr region_type),
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
    rewrite !(delete_list_permutation l1 l2) //. iExists _,_. iFrame. eauto.
  Qed.

   Lemma region_open_prepare W C a :
    open_region W C a ⊣⊢ open_region_many W C [a].
  Proof.
    iSplit; iIntros "Hopen";
    rewrite open_region_eq open_region_many_eq /=;
    iFrame.
  Qed.

  Lemma region_open_nil W C :
    region W C ⊣⊢ open_region_many W C [].
  Proof.
    iSplit; iIntros "H";
    rewrite region_eq open_region_many_eq /=;
            iFrame.
  Qed.

  Lemma region_open_next_temp_pwl W C φ als a p :
    a ∉ als →
    (std W) !! a = Some Temporary ->
    isWL p = true →
    open_region_many W C als ∗ rel C a p φ ∗ sts_full_world W C -∗
    ∃ v, open_region_many W C (a :: als)
         ∗ sts_full_world W C
         ∗ sts_state_std C a Temporary
         ∗ a ↦ₐ v
         ∗ ⌜isO p = false⌝
         ∗ ▷ future_pub_mono C φ v
         ∗ ▷ φ (W,C,v).
  Proof.
    rewrite open_region_many_eq .
    iIntros (Hnin Htemp Hpwl) "(Hopen & #Hrel & Hfull)".
    rewrite /open_region_many_def /region_map_def /=.
    rewrite rel_eq /rel_def /rel_def /region_def /rel /region.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]".
    iDestruct "Hopen" as (M Mρ) "(HM & % & % & Hpreds)"; simplify_eq.
    iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq;eauto.
    rewrite HMeq delete_list_insert; auto.
    rewrite delete_list_delete; auto.
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete_eq].
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ Hρ) "[Hstate Hl]".
    iDestruct (sts_full_state_std with "Hfull Hstate") as %Hst.
    rewrite Htemp in Hst. (destruct ρ; try by simplify_eq); [].
    iDestruct "Hl" as (γpred' p' φ' HH Hpers) "(#Hφ' & Hl)".
    iDestruct "Hl" as (v Hne) "(Hl & #HmonoV & Hφv)".
    inversion HH; subst. rewrite Hpwl.
    iDestruct (saved_pred_agree _ _ _ _ _ (W,C,v) with "Hφ Hφ'") as "#Hφeq".
    iFrame.
    iSplitR "Hφv".
    - iExists Mρ. repeat (rewrite -HMeq).
      repeat (iSplitR; eauto).
      iApply region_map_delete; auto.
    - repeat (iSplitR).
      + auto.
      + iApply future_pub_mono_eq_pred; auto.
      + iNext; iRewrite "Hφeq". iFrame.
  Qed.

  Lemma region_open_next_temp_nwl W C φ als a p :
    a ∉ als →
    (std W) !! a = Some Temporary ->
    isWL p = false →
    open_region_many W C als ∗ rel C a p φ ∗ sts_full_world W C -∗
    ∃ v, open_region_many W C (a :: als)
         ∗ sts_full_world W C
         ∗ sts_state_std C a Temporary
         ∗ a ↦ₐ v
         ∗ ⌜isO p = false⌝
         ∗ ▷ (if isDL p then future_pub_mono C φ v else future_priv_mono C φ v)
         ∗ ▷ φ (W,C,v).
  Proof.
    rewrite open_region_many_eq .
    iIntros (Hnin Htemp Hpwl) "(Hopen & #Hrel & Hfull)".
    rewrite /open_region_many_def /region_map_def /=.
    rewrite rel_eq /rel_def /rel_def /region_def /rel /region.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]".
    iDestruct "Hopen" as (M Mρ) "(HM & % & % & Hpreds)"; simplify_eq.
    iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq;eauto.
    rewrite HMeq delete_list_insert; auto.
    rewrite delete_list_delete; auto.
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete_eq].
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ Hρ) "[Hstate Hl]".
    iDestruct (sts_full_state_std with "Hfull Hstate") as %Hst.
    rewrite Htemp in Hst. (destruct ρ; try by simplify_eq); [].
    iDestruct "Hl" as (γpred' p' φ' HH Hpers) "(#Hφ' & Hl)".
    iDestruct "Hl" as (v Hne) "(Hl & #HmonoV & Hφv)".
    inversion HH; subst. rewrite Hpwl.
    iDestruct (saved_pred_agree _ _ _ _ _ (W,C,v) with "Hφ Hφ'") as "#Hφeq".
    iFrame.
    iSplitR "Hφv".
    - iExists Mρ. repeat (rewrite -HMeq).
      repeat (iSplitR; eauto).
      iApply region_map_delete; auto.
    - repeat (iSplitR).
      + auto.
      + destruct (isDL p').
        * iApply future_pub_mono_eq_pred; auto.
        * iApply future_priv_mono_eq_pred; auto.
      + iNext; iRewrite "Hφeq". iFrame.
  Qed.

  Lemma region_open_next_perm W C φ als a p :
    a ∉ als → (std W) !! a = Some Permanent ->
    open_region_many W C als
    ∗ rel C a p φ
    ∗ sts_full_world W C
    -∗ ∃ v,
        sts_full_world W C
        ∗ sts_state_std C a Permanent
        ∗ open_region_many W C (a :: als)
        ∗ a ↦ₐ v
        ∗ ⌜isO p = false⌝
        ∗ ▷ (future_priv_mono C φ v)
        ∗ ▷ φ (W,C,v).
  Proof.
    rewrite open_region_many_eq .
    iIntros (Hnin Htemp) "(Hopen & #Hrel & Hfull)".
    rewrite /open_region_many_def /= /region_map_def.
    rewrite rel_eq /rel_def /rel_def /region_def /rel /region.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]".
    iDestruct "Hopen" as (M Mρ) "(HM & % & % & Hpreds)"; simplify_eq.
    iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq;eauto.
    rewrite HMeq delete_list_insert; auto.
    rewrite delete_list_delete; auto.
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete_eq].
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ Hρ) "[Hstate Hl]".
    iDestruct (sts_full_state_std with "Hfull Hstate") as %Hst.
    rewrite Htemp in Hst. (destruct ρ; try by simplify_eq); [].
    iDestruct "Hl" as (γpred' p' φ' HH Hpers) "(#Hφ' & Hl)".
    iDestruct "Hl" as (v Hne) "(Hl & #HmonoV & Hφv)".
    inv HH.
    iDestruct (saved_pred_agree _ _ _ _ _ (W,C,v) with "Hφ Hφ'") as "#Hφeq".
    iExists _. iFrame.
    iSplitR "Hφv".
    - rewrite /open_region.
      iExists Mρ. repeat (rewrite -HMeq).
      repeat (iSplitR; eauto).
      iApply region_map_delete; auto.
    - repeat (iSplitR).
      + auto.
      + iApply future_priv_mono_eq_pred; auto.
      + iNext; iRewrite "Hφeq". iFrame.
  Qed.

   Lemma region_close_next_temp_pwl W C φ als a p v `{forall Wv, Persistent (φ Wv)} :
    a ∉ als ->
    isWL p = true →
    sts_state_std C a Temporary
    ∗ open_region_many W C (a::als)
    ∗ a ↦ₐ v
    ∗ ⌜isO p = false⌝
    ∗ future_pub_mono C φ v
    ∗ ▷ φ (W,C,v)
    ∗ rel C a p φ
    -∗ open_region_many W C als.
  Proof.
    rewrite open_region_many_eq /open_region_many_def.
    iIntros (Hnin Hpwl) "(Hstate & Hreg_open & Hl & % & #HmonoV & Hφ & #Hrel)".
    rewrite rel_eq /rel_def /rel /region.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & % & %Hdomρ & Hpreds)".
    iDestruct (region_map_insert _ _ _ _ _ Temporary with "Hpreds") as "Hpreds".
    rewrite -!/delete_list.
    iDestruct (big_sepM_insert _ (delete a (delete_list als M)) a with "[-HM]") as "test";
      first by rewrite lookup_delete_eq.
    { iFrame. iSplitR; [by simplify_map_eq|].
      iExists _,p,_. rewrite Hpwl. iFrame "∗ #". repeat (iSplitR;[eauto|]).
      auto. }
    rewrite -(delete_list_delete _ M) //.
    rewrite -(delete_list_insert _ (delete a M)) //.
    rewrite -(delete_list_insert _ Mρ) //.
    iExists M, (<[a:=Temporary]> Mρ).
    iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq;eauto.
    rewrite -HMeq.
    iFrame "∗ # %".
    repeat(iSplitR; eauto).
    by rewrite HMeq insert_delete_eq !dom_insert_L Hdomρ.
  Qed.

  Lemma region_close_next_temp_nwl W C φ als a p v `{forall Wv, Persistent (φ Wv)} :
    a ∉ als ->
    isWL p = false →
    sts_state_std C a Temporary
    ∗ open_region_many W C (a::als)
    ∗ a ↦ₐ v
    ∗ ⌜isO p = false⌝
    ∗ (if isDL p then future_pub_mono C φ v else future_priv_mono C φ v)
    ∗ ▷ φ (W,C,v)
    ∗ rel C a p φ
      -∗ open_region_many W C als.
  Proof.
    rewrite open_region_many_eq /open_region_many_def.
    iIntros (Hnin Hpwl) "(Hstate & Hreg_open & Hl & % & #HmonoV & Hφ & #Hrel)".
    rewrite rel_eq /rel_def /rel /region.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & % & %Hdomρ & Hpreds)".
    iDestruct (region_map_insert _ _ _ _ _ Temporary with "Hpreds") as "Hpreds".
    rewrite -!/delete_list.
    iDestruct (big_sepM_insert _ (delete a (delete_list als M)) a with "[-HM]") as "test";
      first by rewrite lookup_delete_eq.
    { iFrame. iSplitR; [by simplify_map_eq|].
      iExists _,p,_. rewrite Hpwl. iFrame "∗ #". repeat (iSplitR;[eauto|]).
      auto. }
    rewrite -(delete_list_delete _ M) //.
    rewrite -(delete_list_insert _ (delete a M)) //.
    rewrite -(delete_list_insert _ Mρ) //.
    iExists M, (<[a:=Temporary]> Mρ).
    iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq;eauto.
    rewrite -HMeq.
    iFrame "∗ # %".
    repeat(iSplitR; eauto).
    by rewrite HMeq insert_delete_eq !dom_insert_L Hdomρ.
  Qed.

  Lemma region_close_next_perm W C φ als a p v `{forall Wv, Persistent (φ Wv)} :
    a ∉ als ->
    ⊢ sts_state_std C a Permanent
    ∗ open_region_many W C (a::als)
    ∗ a ↦ₐ v
    ∗ ⌜isO p = false⌝
    ∗ future_priv_mono C φ v
    ∗ ▷ φ (W,C,v)
    ∗ rel C a p φ
      -∗ open_region_many W C als.
  Proof.
    rewrite open_region_many_eq /open_region_many_def.
    iIntros (Hnin) "(Hstate & Hreg_open & Hl & % & #HmonoV & Hφ & #Hrel)".
    rewrite rel_eq /rel_def /rel /region.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & % & %Hdomρ & Hpreds)".
    iDestruct (region_map_insert _ _ _ _ _ Permanent with "Hpreds") as "Hpreds".
    iDestruct (big_sepM_insert _ (delete a (delete_list als M)) a with "[-HM]") as "test";
      first by rewrite lookup_delete_eq.
    { iFrame.
      iSplitR; [by simplify_map_eq|].
      iExists _,_,_. iFrame "∗ #". repeat (iSplitR;[eauto|]). auto.
    }
    rewrite -(delete_list_delete _ M) // -(delete_list_insert _ (delete _ M)) //.
    rewrite -(delete_list_insert _ Mρ) //.
    iExists M, (<[a:=Permanent]> Mρ).
    iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq;eauto.
    rewrite -HMeq.
    iFrame "∗ # %".
    repeat(iSplitR; eauto).
    by rewrite HMeq insert_delete_eq !dom_insert_L Hdomρ.
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
    (als : list Addr) (a : Addr) (p : Perm) (ρ : region_type)
    (Hρnotrevoked : ρ <> Revoked) :
    a ∉ als →
    std W !! a = Some ρ →
    ⊢ open_region_many W C als
    ∗ rel C a p φ
    ∗ sts_full_world W C
    -∗ ∃ v : Word,
        sts_full_world W C
        ∗ sts_state_std C a ρ
        ∗ open_region_many W C (a :: als)
        ∗ a ↦ₐ v
        ∗ ▷ monotonicity_guarantees_region C φ p v ρ
        ∗ ▷ φ (W, C, v)
        ∗ ⌜isO p = false⌝.
  Proof.
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
    (l : list (Addr * Perm * (WORLD * CmptName * Word → iProp Σ) * region_type))
    (l' : list Addr)
    :

    let la  := (fmap (fun '(a,p,φ,ρ) => a) l) in
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
      ∗ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, a ↦ₐ v)
      ∗ ▷ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, monotonicity_guarantees_region C φ p v ρ)
      ∗ ▷ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, φ (W,C,v))
      ∗ ⌜ length lv = length la ⌝
      ∗ ([∗ list] '(a,p,φ,ρ) ∈ l , ⌜ isO p = false ⌝)
  .
  Proof.
    induction l; intros la Hnodup Hdis Hregion_state Ha_state ;
      iIntros "(Hrel & Hr & Hsts)"; cbn in * |- *.
    - iExists []; cbn in *.
      by iFrame.
    - destruct a as [[[a p] φ] ρ]; cbn in * |- *.
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
      iDestruct (big_sepL2_cons (fun _ '(a, _, _, _) v => (a ↦ₐ v)%I) (a,p,φ,ρ) va with "[$]") as "Hlv".
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
    (als : list Addr) (a : Addr) (p : Perm) (v : Word) (ρ : region_type)
    (Hρnotrevoked : ρ <> Revoked) :
    a ∉ als
    → sts_state_std C a ρ
    ∗ open_region_many W C (a :: als)
    ∗ a ↦ₐ v
    ∗ ⌜isO p = false⌝
    ∗ monotonicity_guarantees_region C φ p v ρ
    ∗ ▷ φ (W, C, v)
    ∗ rel C a p φ
      -∗ open_region_many W C als.
  Proof.
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
    (l : list (Addr * Perm * (WORLD * CmptName * Word → iProp Σ) * region_type))
    (l' : list Addr)
    (lv : list Word)
    :

    let la  := (fmap (fun '(a,p,φ,ρ) => a) l) in
    length l = length lv ->
    NoDup la ->
    la ## l' ->
    Forall (fun '(a,p,φ,ρ) => ρ ≠ Revoked) l ->
    Forall (fun '(a,p,φ,ρ) => ∀ Wv : WORLD * CmptName * Word, Persistent (φ Wv)) l ->

    open_region_many W C (la++l')
    ∗ ([∗ list] '(a,p,φ,ρ) ∈ l, sts_state_std C a ρ)
    ∗ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, a ↦ₐ v)
    ∗ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, monotonicity_guarantees_region C φ p v ρ)
    ∗ ▷ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, φ (W,C,v))
    ∗ ([∗ list] '(a,p,φ,ρ) ∈ l, rel C a p φ)
    ∗ ([∗ list] '(a,p,φ,ρ) ∈ l , ⌜ isO p = false ⌝)
      -∗ open_region_many W C l'.
  Proof.
    generalize dependent lv.
    induction l; intros lv la Hlen Hnodup Hdis Hregion_state Hpers ;
      iIntros "(Hr & Hstd & Hv & Hmono & Hφ & Hrel & Hp)"; cbn in * |- *.
    - by iFrame.
    - destruct a as [[[a p] φ] ρ]; cbn in * |- *.
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

End standard_world_interp.
