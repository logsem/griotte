From iris.proofmode Require Import proofmode.
From cap_machine Require Export stdpp_extra iris_extra region_invariants world_std_revocation.

  (*** REVOCATION OF THE WORLD INTERPRETATION *)

  (** * Disclaimer to the users of Griotte:

      All the lemmas and definitions in this file are internal to the Griotte model.
      To manipulate the world in the proofs, see [world_ghost_theory.v].

  *)

Section region_invariant_revocation.

  Context {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {Cname : CmptNameG} {CNames : gset CmptName}
    {stsg : STSG Addr region_type Σ}
    {relg : relGS Σ}
    `{MP: MachineParameters}.
  Implicit Types W : WORLD.

  (* The following lemma takes a revoked region and makes it Temporary. *)

  (* In the following variant, we only require monotonicity of the updated world *)
  Lemma update_region_revoked_temp_pwl_updated E W C a p v φ `{∀ Wv, Persistent (φ Wv)} :
    let W' := (<s[ a := Temporary ]s> W) in
    (std W) !! a = Some Revoked →
    isO p = false → isWL p = true →

    future_pub_mono C φ v -∗
    sts_full_world W C -∗
    region W C -∗
    a ↦ₐ v -∗
    φ (W',C, v) -∗
    rel C a p φ

    ={E}=∗

    region W' C
    ∗ sts_full_world W' C.
  Proof.
    intro.
    iIntros (Hrev Hne Hpwl) "#HmonoV Hsts Hreg Hl #Hφ #Hrel".
    rewrite region_eq /region_def.
    iDestruct "Hreg" as (M Mρ) "(Hγrel & %Hdom & %Hdom' & Hpreds)";simplify_eq.
    rewrite rel_eq /rel_def. iDestruct "Hrel" as (γ) "[HREL Hsaved]".
    iDestruct ( (reg_in C M) with "[$HREL $Hγrel]") as %HMeq;eauto.
    rewrite /region_map_def HMeq big_sepM_insert; [|by rewrite lookup_delete_eq].
    iDestruct "Hpreds" as "[Hl' Hr]".
    iDestruct "Hl'" as (ρ Hl) "[Hstate Hresources]".
    iDestruct (sts_full_state_std with "Hsts Hstate") as %Hρ.
    rewrite Hrev in Hρ. inversion Hρ as [Hρrev]. subst.
    iMod (sts_update_std _ _ _ _ Temporary with "Hsts Hstate") as "[Hsts Hstate]".
    assert (related_sts_pub_world W (<s[a := Temporary ]s> W)) as Hrelated.
    { apply related_sts_pub_revoked_temp; auto. }
    iDestruct (region_map_monotone _ _ _ _ _ Hrelated with "Hr") as "Hr".
    assert (is_Some (M !! a)) as [x Hsome].
    { apply elem_of_dom. rewrite -Hdom. rewrite elem_of_dom. done. }
    iDestruct (region_map_delete with "Hr") as "Hr".
    iDestruct (region_map_insert _ _ _ _ _ Temporary with "Hr") as "Hr";auto.
    iDestruct (big_sepM_delete _ _ a _ Hsome with "[Hl Hstate $Hr]") as "Hr".
    { iExists Temporary. iFrame. iSplitR;[iPureIntro;apply lookup_insert_eq|].
      iExists γ, p, φ. rewrite HMeq lookup_insert_eq in Hsome.
      inversion Hsome.
      rewrite Hpwl.
      repeat (iSplit; auto).
    }
    subst W'.
    iFrame "Hsts".
    iExists M.
    rewrite -HMeq.
    iFrame "∗%".
    iPureIntro.
    apply insert_id in Hsome; rewrite -Hsome.
    apply insert_id in Hl; rewrite -Hl.
    split.
    - repeat rewrite dom_insert_L;rewrite Hdom;set_solver.
    - repeat rewrite insert_insert_eq dom_insert_L;rewrite Hdom';set_solver.
  Qed.

  Lemma update_region_revoked_temp_nwl_updated E W C a p v φ `{∀ Wv, Persistent (φ Wv)} :
    let W' := (<s[ a := Temporary ]s> W) in
    (std W) !! a = Some Revoked →
    isO p = false → isWL p = false →

    (if isDL p then future_pub_mono C φ v else future_priv_mono C φ v) -∗
    sts_full_world W C -∗
    region W C -∗
    a ↦ₐ v -∗
    φ (W',C, v) -∗
    rel C a p φ

    ={E}=∗

    region W' C
    ∗ sts_full_world W' C.
  Proof.
    intro.
    iIntros (Hrev Hne Hpwl) "#HmonoV Hsts Hreg Hl #Hφ #Hrel".
    rewrite region_eq /region_def.
    iDestruct "Hreg" as (M Mρ) "(Hγrel & %Hdom & %Hdom' & Hpreds)";simplify_eq.
    rewrite rel_eq /rel_def. iDestruct "Hrel" as (γ) "[HREL Hsaved]".
    iDestruct ( (reg_in C M) with "[$HREL $Hγrel]") as %HMeq;eauto.
    rewrite /region_map_def HMeq big_sepM_insert; [|by rewrite lookup_delete_eq].
    iDestruct "Hpreds" as "[Hl' Hr]".
    iDestruct "Hl'" as (ρ Hl) "[Hstate Hresources]".
    iDestruct (sts_full_state_std with "Hsts Hstate") as %Hρ.
    rewrite Hrev in Hρ. inversion Hρ as [Hρrev]. subst.
    iMod (sts_update_std _ _ _ _ Temporary with "Hsts Hstate") as "[Hsts Hstate]".
    assert (related_sts_pub_world W (<s[a := Temporary ]s> W)) as Hrelated.
    { apply related_sts_pub_revoked_temp; auto. }
    iDestruct (region_map_monotone _ _ _ _ _ Hrelated with "Hr") as "Hr".
    assert (is_Some (M !! a)) as [x Hsome].
    { apply elem_of_dom. rewrite -Hdom. rewrite elem_of_dom. done. }
    iDestruct (region_map_delete with "Hr") as "Hr".
    iDestruct (region_map_insert _ _ _ _ _ Temporary with "Hr") as "Hr";auto.
    iDestruct (big_sepM_delete _ _ a _ Hsome with "[Hl Hstate $Hr]") as "Hr".
    { iExists Temporary. iFrame. iSplitR;[iPureIntro;apply lookup_insert_eq|].
      iExists γ, p, φ. rewrite HMeq lookup_insert_eq in Hsome.
      inversion Hsome. rewrite Hpwl.
      repeat (iSplit; auto).
    }
    subst W'.
    iFrame "Hsts".
    iExists M.
    rewrite -HMeq.
    iFrame "∗%".
    iPureIntro.
    apply insert_id in Hsome; rewrite -Hsome.
    apply insert_id in Hl; rewrite -Hl.
    split.
    - repeat rewrite dom_insert_L;rewrite Hdom;set_solver.
    - repeat rewrite insert_insert_eq dom_insert_L;rewrite Hdom';set_solver.
  Qed.

  Lemma update_region_revoked_temp_pwl E W C a p v φ `{∀ Wv, Persistent (φ Wv)} :
    (std W) !! a = Some Revoked →
    isO p = false → isWL p = true →

    future_pub_mono C φ v -∗
    sts_full_world W C -∗
    region W C -∗
    a ↦ₐ v -∗
    φ (W,C,v) -∗
    rel C a p φ

    ={E}=∗

    region (<s[ a := Temporary ]s> W) C
    ∗ sts_full_world (<s[a := Temporary ]s>W) C.
  Proof.
    iIntros (Hrev Hne Hpwl) "#HmonoV Hsts Hreg Hl #Hφ #Hrel".
    assert (related_sts_pub_world W (<s[a := Temporary ]s> W)) as Hrelated.
    { apply related_sts_pub_revoked_temp; auto. }
    iDestruct ("HmonoV" $! W ((<s[ a := Temporary ]s> W)) with "[] [Hφ]") as "Hφ'"; eauto.
    iApply (update_region_revoked_temp_pwl_updated with "HmonoV Hsts Hreg Hl Hφ' Hrel");auto.
  Qed.

  Lemma update_region_revoked_temp_nwl E W C a p v φ `{∀ Wv, Persistent (φ Wv)} :
    (std W) !! a = Some Revoked →
    isO p = false → isWL p = false →

    (if isDL p then future_pub_mono C φ v else future_priv_mono C φ v) -∗
    sts_full_world W C -∗
    region W C -∗
    a ↦ₐ v -∗
    φ (W,C,v) -∗
    rel C a p φ

    ={E}=∗

    region (<s[ a := Temporary ]s> W) C
    ∗ sts_full_world (<s[ a := Temporary ]s> W) C.
  Proof.
    iIntros (Hrev Hne Hpwl) "#HmonoV Hsts Hreg Hl #Hφ #Hrel".
    destruct (isDL p) eqn:Hpdl.
    + assert (related_sts_pub_world W (<s[ a := Temporary ]s> W)) as Hrelated.
      { apply related_sts_pub_revoked_temp; auto. }
      iDestruct ("HmonoV" $! W ((<s[ a := Temporary ]s> W)) with "[] [Hφ]") as "Hφ'"; eauto.
      replace (future_pub_mono C φ v)
        with (if isDL p then future_pub_mono C φ v else future_priv_mono C φ v)
      by (rewrite Hpdl;done).
      iApply (update_region_revoked_temp_nwl_updated with "HmonoV Hsts Hreg Hl Hφ' Hrel");auto.
    + assert (related_sts_priv_world W (<s[ a := Temporary ]s> W)) as Hrelated.
      { apply related_sts_pub_priv_world,related_sts_pub_revoked_temp; auto. }
      iDestruct ("HmonoV" $! W ((<s[ a := Temporary ]s> W)) with "[] [Hφ]") as "Hφ'"; eauto.
      replace (future_priv_mono C φ v)
        with (if isDL p then future_pub_mono C φ v else future_priv_mono C φ v)
      by (rewrite Hpdl;done).
      iApply (update_region_revoked_temp_nwl_updated with "HmonoV Hsts Hreg Hl Hφ' Hrel");auto.
  Qed.


  (* ---------------------------------------------------------------------------------------- *)
  (* ------------------- IF THΕ FULL STS IS REVOKED, WΕ CAN REVOKE REGION ------------------- *)
  (* ---------------------------------------------------------------------------------------- *)

  (* Note that Mρ by definition matches up with the full sts. Mρ starts out by being indirectly revoked *)
  Lemma monotone_revoke_region_def W C MC Mρ :
    ⌜dom (std W) = dom MC⌝
    -∗ sts_full_world (revoke W) C
    -∗ region_map_def W C MC Mρ
    -∗ sts_full_world (revoke W) C ∗ region_map_def (revoke W) C MC Mρ.
  Proof.
    iIntros (Hdom) "Hfull Hr".
    rewrite /revoke in Hdom |- *.
    destruct W as [Wstd_sta Wloc].
    iDestruct (big_sepM_exists with "Hr") as (m') "Hr".
    iDestruct (big_sepM2_sep with "Hr") as "[HMρ Hr]".
    iDestruct (big_sepM2_sep with "Hr") as "[Hstates Hr]".
    iAssert (∀ a ρ, ⌜m' !! a = Some ρ⌝ → ⌜ρ ≠ Temporary⌝)%I as %Hmonotemp.
    { iIntros (a ρ Hsome).
      iDestruct (big_sepM2_lookup_l _ _ _ a with "Hstates") as (γp) "[Hl Hstate]"; eauto.
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hρ.
      iPureIntro.
      eapply revoke_lookup_non_temp; eauto.
    }
    iFrame.
    iApply big_sepM_exists. iExists m'.
    iApply big_sepM2_sep. iFrame.
    iDestruct (big_sepM2_sep with "[$Hstates $Hr]") as "Hr".
    iApply (big_sepM2_mono with "Hr").
    iIntros (a ρ γp Hm' HM) "/= [Hstate Ha]".
    specialize (Hmonotemp a ρ Hm').
    destruct ρ;iFrame;[contradiction|].
    iDestruct "Ha" as (γpred p φ) "(%Hγp & % & Hpred & Ha)".
    iDestruct "Ha" as (v Hne) "(Ha & #HmonoV & #Hφ)".
    iFrame "∗%#".
    iNext. iApply ("HmonoV" with "[] Hφ").
    iPureIntro.
    apply revoke_related_sts_priv_world.
  Qed.

  (* ---------------------------------------------------------------------------------------- *)
  (* ------------------- A REVOKED W IS MONOTONE WRT PRIVATE FUTURE WORLD ------------------- *)
  (* ---------------------------------------------------------------------------------------- *)

  (* The following statements discard all the resources of temporary regions *)

  Lemma monotone_revoke_list_sts_full_world W C MC Mρ l :
    ⌜∀ (a : Addr), a ∈ l → is_Some (MC !! a)⌝ -∗
    ⌜dom Mρ = dom MC⌝ -∗
    ⌜NoDup l⌝ -∗
    sts_full_world W C ∗ region_map_def W C MC Mρ
    ==∗
    ∃ Mρ, ⌜dom Mρ = dom MC⌝
              ∧ (sts_full_world (revoke_list l W) C ∗ region_map_def W C MC Mρ).
  Proof.
    iIntros (Hin Hdom Hdup) "[Hfull Hr]".
    iInduction (l) as [|x l] "IH".
    - iExists _. rewrite revoke_list_empty.
      by iFrame "%∗".
    - apply NoDup_cons in Hdup as [Hnin Hdup].
      iMod ("IH" with "[] [] Hfull Hr") as (Mρ' Hdom_new) "[Hfull Hr]"; auto.
      { iPureIntro. intros a Ha. apply Hin. apply elem_of_cons. by right. }
      rewrite /revoke_list /=.
      destruct W as [Wstd_sta Wloc].
      destruct (Wstd_sta !! x) eqn:Hsome;[|iExists _; cbn; rewrite Hsome ; by iFrame "%∗"].
      destruct r;[|iExists _; cbn; rewrite Hsome; by iFrame..].
      destruct Hin with x as [γp Hsomea];[apply list_elem_of_here|].
      iDestruct (big_sepM_delete _ _ x with "Hr") as "[Hρ Hr]"; eauto.
      iDestruct "Hρ" as (ρ' Hρ') "(Hstate & Ha)".
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hlookup; simplify_eq.
      simpl in Hlookup; subst.
      rewrite revoke_list_not_elem_of_lookup in Hlookup; auto.
      rewrite Hsome in Hlookup. inversion Hlookup as [Heq]. subst ρ'.
      iMod (sts_update_std _ _ _ _ (Revoked) with "Hfull Hstate") as "[Hfull Hstate]".
      iFrame.
      iDestruct (region_map_delete with "Hr") as "Hr".
      iDestruct (region_map_insert _ _ _ _ _ Revoked with "Hr") as "Hr";auto.
      iExists _.
      iDestruct "Ha" as (γpred p0 φ Heq Hpers) "[#Hsaved Ha]".
      iDestruct (big_sepM_delete _ _ x with "[$Hr Hstate]") as "$"; eauto.
      { iExists Revoked. iFrame.
        iSplitR; first (iPureIntro; apply lookup_insert_eq).
        iExists _. iFrame "#". auto.
      }
      rewrite Hsome /=.
      iFrame "%∗".
      iPureIntro. rewrite -Hdom_new dom_insert_L.
      assert (x ∈ dom Mρ') as Hin'.
      { apply elem_of_dom;eauto. }
      set_solver.
  Qed.

  Lemma monotone_revoke_sts_full_world W C :
    sts_full_world W C ∗ region W C
    ==∗ (sts_full_world (revoke W) C ∗ region W C).
  Proof.
    iIntros "[Hfull Hr]".
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ) "(HM & %Hdom & %Hdom' & Hr)".
    rewrite revoke_list_dom.
    iMod (monotone_revoke_list_sts_full_world _ _ _ _ (map_to_list (std W)).*1
            with "[] [] [] [$Hfull $Hr]") as (Mρ' Hin) "[Hfull Hr]";auto.
    { iPureIntro. intros i Hin. apply map_to_list_fst in Hin as [x Hin].
      apply elem_of_dom. rewrite -Hdom. apply elem_of_map_to_list in Hin.
      rewrite elem_of_dom. eauto.
    }
    { iPureIntro. apply (NoDup_fst_map_to_list (M:=gmap Addr) (A:=region_type)). }
    iFrame.
    iModIntro.
    done.
  Qed.

  Lemma monotone_revoke W C :
    sts_full_world W C ∗ region W C
    ==∗
    sts_full_world (revoke W) C ∗ region (revoke W) C.
  Proof.
    iIntros "[HW Hr]".
    iMod (monotone_revoke_sts_full_world with "[$HW $Hr]") as "[HW Hr]".
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ) "(HM & %Hdom & % & Hpreds)".
    iDestruct (monotone_revoke_region_def with "[] [$HW] [$Hpreds]") as "[Hpreds HW]"; auto.
    iModIntro. iFrame.
    iPureIntro.
    rewrite /revoke in Hdom |- *.
    repeat (split;auto).
    by rewrite -revoke_dom_eq.
  Qed.

  (* ---------------------------------------------------------------------------------------- *)
  (* ---------------- IF WΕ HAVE THE REGION, THEN WE CAN REVOKE THE FULL STS ---------------- *)
  (* ---------------------------------------------------------------------------------------- *)

  (* This matches the temprary resources in the map *)
  Definition temp_resources (W : WORLD) (C : CmptName) φ (a : Addr) (p : Perm) : iProp Σ :=
    (∃ (v : Word),
           ⌜isO p = false⌝
          ∗ a ↦ₐ v
          ∗ (if isWL p
             then future_pub_mono C φ v
             else (if isDL p then future_pub_mono C φ v else future_priv_mono C φ v))
          ∗ φ (W,C,v))%I.

  Definition close_addr_resources C W (a : Addr) (is_later: bool) :=
    (∃ p φ, ⌜forall Wv, Persistent (φ Wv)⌝
                       ∗ if_later_P is_later (temp_resources W C φ a p)
                       ∗ rel C a p φ)%I.
  Definition close_list_resources C W (l : list Addr) (is_later: bool) :=
   ([∗ list] a ∈ l, close_addr_resources C W a is_later)%I.

  Lemma monotone_revoke_list_sts_full_world_keep W C (l : list Addr) (l' : list Addr) :
    ⊢ ⌜NoDup l'⌝ → ⌜NoDup l⌝ → ⌜l' ⊆+ l⌝ →
    ([∗ list] a ∈ l', ⌜(std W) !! a = Some Temporary⌝)
    ∗ sts_full_world W C ∗ region W C
    ==∗
    (sts_full_world (revoke_list l W) C
     ∗ region W C
     ∗ close_list_resources C W l' true).
  Proof.
   rewrite region_eq /region_def /= /close_list_resources /close_addr_resources.
    iInduction (l) as [|x l] "IH" forall (l');
    iIntros (Hdup' Hdup Hsub) "(#Hrel & Hfull & Hr)".
    - iFrame. apply submseteq_nil_r in Hsub as ->. repeat rewrite big_sepL_nil. done.
    - destruct (decide (x ∈ l')).
      + apply list_elem_of_split in e as [l1 [l2 Heq] ].
        rewrite Heq in Hsub.
        iRevert (Hsub Hdup Hdup'). rewrite Heq -Permutation_middle. iIntros (Hsub Hdup Hdup').
        apply NoDup_cons in Hdup as [Hnin Hdup].
        apply NoDup_cons in Hdup' as [Hnin' Hdup'].
        assert (x ∈ l') as Ha.
        { rewrite Heq. apply elem_of_app. right. apply list_elem_of_here. }
        apply elem_of_Permutation in Ha as [l'' Hleq].
        simpl. iDestruct "Hrel" as "[ Htemp Hrel]".
        iDestruct "Htemp" as %Htemp.
        iMod (region_rel_get with "[$Hfull Hr]") as "(Hfull & Hr & #Hx)";[apply Htemp|..].
        { rewrite region_eq /region_def. iFrame. }
        rewrite region_eq /region_def.
        iMod ("IH" with "[] [] [] [$Hrel $Hfull $Hr]") as "(Hfull & Hr & Hl)"; auto.
        { iPureIntro. apply submseteq_cons_l in Hsub as [k' [Hperm Hsub] ].
          apply Permutation.Permutation_cons_inv in Hperm. etrans;eauto. rewrite Hperm. done. }
        rewrite /revoke_list /= /=.
        rewrite Htemp.
        rewrite rel_eq /rel_def.
        iDestruct "Hr" as (M Mρ) "(HM & % & #Hdom & Hpreds)".
        iDestruct "Hdom" as %Hdom.
        iDestruct "Hx" as (p' φ' Hpers) "Hx".
        iDestruct "Hx" as (γpred) "#(Hγpred & Hφ)".
        iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq; auto.
        rewrite /region_map_def.
        rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete_eq].
        iDestruct "Hpreds" as "[Ha Hpreds]".
        iDestruct "Ha" as (ρ Ha) "[Hstate Ha]".
        iDestruct (sts_full_state_std with "Hfull Hstate") as %Hlookup.
        simpl in Hlookup.
        simpl in Hlookup. subst. rewrite revoke_list_not_elem_of_lookup in Hlookup; auto.
        rewrite Htemp in Hlookup. inversion Hlookup. subst ρ.
        iMod (sts_update_std _ _ _ _ (Revoked) with "Hfull Hstate") as "[Hfull Hstate]".
        iDestruct (region_map_delete with "Hpreds") as "Hpreds".
        iDestruct (region_map_insert _ _ _ _ _ Revoked with "Hpreds") as "Hpreds";auto.
        iDestruct (big_sepM_insert _ _ x (γpred, p') with "[$Hpreds Hstate]") as "Hpreds"
        ; [apply lookup_delete_eq|..]
        ; iClear "IH"
        ; iFrame "∗ #".
        { iSplitR;[iPureIntro; apply lookup_insert_eq|]; iExists _ ;iSplit;auto. }
        rewrite -HMeq.
        iModIntro. iSplitR.
        ++ iSplit; auto.
           iPureIntro. rewrite dom_insert_L.
           assert (x ∈ dom M) as Hin.
           { rewrite -Hdom. apply elem_of_dom. eauto. }
           revert Hin Hdom. clear; intros Hin Hdom. rewrite Hdom. set_solver.
        ++ iSplitR;auto.
           iDestruct "Ha" as (γpred0 p0 φ0 Heq0 Hpers0) "(#Hsaved & Ha)".
           iDestruct "Ha" as (v Hne0) "(Hx & #HmonoV & #Hφ0)"; simplify_eq.
           iExists v; iFrame "%∗".
           destruct W as [ Wstd_sta Wloc].
           iDestruct (saved_pred_agree _ _ _ _ _ (Wstd_sta, Wloc, C, v) with "Hφ Hsaved") as "#Hφeq". iFrame.
           iDestruct (internal_eq_iff with "Hφeq") as "Hφeq'".
           iSplitL "HmonoV";[|by iNext; iApply "Hφeq'"].
           all: destruct (isWL p0).
           +++ iApply future_pub_mono_eq_pred; auto.
           +++ destruct (isDL p0).
               ++++ iApply future_pub_mono_eq_pred; auto.
               ++++ iApply future_priv_mono_eq_pred; auto.
      + apply NoDup_cons in Hdup as [Hnin Hdup].
        apply submseteq_cons_r in Hsub as [Hsub | [l'' [Hcontr _] ] ].
        2: { exfalso. apply n. rewrite Hcontr. apply list_elem_of_here. }
        iMod ("IH" with "[] [] [] [$Hrel $Hfull $Hr]") as "(Hfull & Hr & Hl)"; auto.
        iDestruct "Hr" as (M Mρ) "(HM & #Hdom & #Hdom' & Hr)".
        iDestruct "Hdom" as %Hdom. iDestruct "Hdom'" as %Hdom'. iClear "IH".
        rewrite /revoke_list /=. destruct W as [ Wstd_sta Wloc].
        destruct (Wstd_sta !! x) eqn:Hsome.
        2: { iFrame. iModIntro. rewrite Hsome. iFrame. iFrame. auto. }
        rewrite Hsome.
        destruct (decide (r = Temporary)).
        2: { destruct r; try contradiction; iFrame; iModIntro; iFrame; auto. }
        assert (is_Some (M !! x)) as [γp Hsomea].
        { apply elem_of_dom. rewrite -Hdom. rewrite elem_of_dom. eauto. }
        iDestruct (big_sepM_delete _ _ x with "Hr") as "[Hx Hr]"; eauto.
        iDestruct "Hx" as (ρ Ha) "[Hstate Hρ]".
        iDestruct (sts_full_state_std with "Hfull Hstate") as %Hlookup.
        iMod (sts_update_std _ _ _ _ (Revoked) with "Hfull Hstate") as "[Hfull Hstate]".
        iDestruct (region_map_delete with "Hr") as "Hpreds".
        simplify_map_eq.
        simpl in *. rewrite revoke_list_not_elem_of_lookup in Hlookup;auto.
        rewrite Hlookup in Hsome. inversion Hsome. subst.
        iDestruct (region_map_insert _ _ _ _ _ Revoked with "Hpreds") as "Hpreds";auto.
        iDestruct (big_sepM_delete _ _ x with "[Hstate $Hpreds Hρ]") as "Hr"; eauto.
        { iExists Revoked; iSplitR; first (by iPureIntro ; simplify_map_eq).
          iFrame.
          iDestruct "Hρ" as (? ? ? ? ?) "[? _]". iExists _,_,_. repeat iSplit;eauto.
        }
        iModIntro. iFrame.
        iSplit; auto.
        iPureIntro. rewrite dom_insert_L.
        assert (x ∈ dom M) as Hin.
        { rewrite -Hdom'. apply elem_of_dom. eauto. }
        revert Hin Hdom'. clear; intros Hin Hdom. rewrite Hdom. set_solver.
  Qed.

  Lemma monotone_revoke_sts_full_world_keep W C (l : list Addr) :
    ⌜NoDup l⌝ -∗
    ([∗ list] a ∈ l, ⌜(std W) !! a = Some Temporary⌝)
    ∗ sts_full_world W C ∗ region W C
    ==∗
    (sts_full_world (revoke W) C
     ∗ region W C
     ∗ close_list_resources C W l true).
  Proof.
    iIntros (Hdup) "(Hl & Hfull & Hr)".
    rewrite revoke_list_dom.
    iAssert (⌜l ⊆+ (map_to_list (std W)).*1⌝)%I as %Hsub.
    { iClear "Hfull Hr". iInduction l as [| x l] "IH".
      - iPureIntro. apply submseteq_nil_l.
      - iDestruct "Hl" as "[ Hin Hl]".
        iDestruct "Hin" as %Hin. apply NoDup_cons in Hdup as [Hnin Hdup].
        iDestruct ("IH" with "[] Hl") as %Hsub; auto.
        iPureIntro.
        assert (x ∈ (map_to_list (std W)).*1) as Helem.
        { apply map_to_list_fst. exists Temporary. by apply elem_of_map_to_list. }
        apply elem_of_Permutation in Helem as [l' Hl']. rewrite Hl'.
        apply submseteq_skip. revert Hsub. rewrite Hl'; intros Hsub.
        apply submseteq_cons_r in Hsub as [Hsub | [l'' [Heq _] ] ]; auto.
        assert (countable.encode x ∈ countable.encode <$> l) as Hcontr.
        { rewrite Heq. apply list_elem_of_here. }
        apply list_elem_of_fmap_1 in Hcontr as [y [Hxy Hy] ].
        apply encode_inj in Hxy. subst. contradiction.
    }
    iMod (monotone_revoke_list_sts_full_world_keep _ _ (map_to_list (std W)).*1 l
            with "[] [] [] [$Hl $Hfull $Hr]") as "(Hfull & Hr & Hi)"; auto.
    { iPureIntro. apply (NoDup_fst_map_to_list (M:=gmap Addr) (A:=region_type)). }
    by iFrame.
  Qed.

  (* revoke and keep temp resources in list l, with unknown p and φ *)
  Lemma monotone_revoke_keep W C l :
    NoDup l ->
    ([∗ list] a ∈ l, ⌜(std W) !! a = Some Temporary⌝)
    ∗ sts_full_world W C
    ∗ region W C
    ==∗
    sts_full_world (revoke W) C
    ∗ region (revoke W) C
    ∗ close_list_resources C W l true
    ∗ ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) l⌝.
  Proof.
    iIntros (Hdup) "(Hl & HW & Hr)".
    iAssert (⌜Forall (λ a, std W !! a = Some Temporary) l⌝)%I as %Htemps.
    { iDestruct (big_sepL_forall with "Hl") as %Htemps.
      iPureIntro. apply Forall_lookup. done. }
    iMod (monotone_revoke_sts_full_world_keep with "[] [$HW $Hr $Hl]") as "(HW & Hr & Hl)"; eauto.
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ) "(HM & %Hdom & % & Hpreds)".
    iDestruct (monotone_revoke_region_def with "[] [$HW] [$Hpreds]") as "[Hpreds HW]"; auto.
    iModIntro. iFrame. iSplitR.
    - iPureIntro.
      rewrite /revoke in Hdom |- *.
      repeat (split;auto).
      by rewrite -revoke_dom_eq.
    - iPureIntro.
      eapply Forall_impl; eauto; cbn.
      intros a Ha.
      by apply revoke_lookup_Monotemp.
  Qed.


  (* ---------------------------------------------------------------------------------------- *)
  (* ----------------- REVOKING ALL TEMPORARY REGIONS, KNOWN AND UNKNOWN  ------------------- *)
  (* ---------------------------------------------------------------------------------------- *)

  (* The following helper lemmas are for revoking all temporary regions in the world *)

  (* However, we also want to be able to close regions that were valid in some world W, and which will be valid again
     in a public future world close l W' ! This is slightly more tricky: we must first update the region monotonically,
     after which it will be possible to consolidate the full_sts and region *)

  Definition close_addr_resources_gen C W (l : list Addr) (a : Addr) (is_later: bool) :=
    (∃ p φ, ⌜forall Wv, Persistent (φ Wv)⌝
                       ∗ (∃ W', ⌜related_sts_pub_world W' (close_list l W)⌝
                                 ∗ if_later_P is_later (temp_resources W' C φ a p))
                       ∗ rel C a p φ)%I.

  Definition close_list_resources_gen C W (l l' : list Addr) (is_later : bool) :=
   ([∗ list] a ∈ l', close_addr_resources_gen C W l a is_later)%I.

  Lemma close_list_resources_gen_eq C W W' (l l' : list Addr) (is_later : bool) :
    related_sts_pub_world W (close_list l W') ->
    close_list_resources C W l' is_later -∗
    close_list_resources_gen C W' l l' is_later.
  Proof.
    iIntros (Hrelated) "Htemps".
    iApply (big_sepL_impl with "Htemps"); auto.
    iIntros "!> %k %a %Ha (%p & %φ & %Hpers & Htemps & Hrel)"; iFrame "∗%".
  Qed.

  Lemma close_list_consolidate_gen W C (l' l : list Addr) :
    ⊢ ⌜l' ⊆+ l⌝ →
    (region (close_list l W) C
     ∗ sts_full_world W C
     ∗ close_list_resources_gen C W l l' false
       )
      ==∗
      (sts_full_world (close_list l' W) C
       ∗ region (close_list l W) C).
  Proof.
    rewrite /close_list_resources_gen /close_addr_resources_gen.
    iIntros (Hsub) "(Hr & Hsts & Htemps)".
    iInduction l' as [|x l'] "IH".
    - simpl. iFrame. done.
    - iDestruct "Htemps" as "[Hx Htemps]".
      assert (l' ⊆+ l) as Hsub'.
      { apply submseteq_cons_l in Hsub as [k [Hperm Hsub] ]. rewrite Hperm.
        apply submseteq_cons_r. left. auto. }
      iMod ("IH" $! Hsub' with "Hr Hsts Htemps") as "[Hsts Hr]".
      iClear "IH".
      rewrite /close_list /close_list /close_list_std_sta /=.
      iDestruct "Hx" as (p φ Hpers) "(Htemp & #Hrel)".
      iDestruct "Htemp" as (W') "(%Hrelated & Htemp)".
      iDestruct "Htemp" as (v) "(%Hne & Hx' & #HmonoV & Hφ)".
      destruct (std W !! x) eqn:Hsome;[|iFrame;done].
      destruct (decide (Revoked = r)).
      + subst.
        assert (x ∈ l) as Hinl.
        { apply elem_of_submseteq with (x:=x) in Hsub;[auto|apply elem_of_cons;by left]. }
        rewrite region_eq /region_def /region_map_def.
        iDestruct "Hr" as (M Mρ) "(HM & %Hdom & %Hdom' & Hr)".
        rewrite rel_eq /rel_def.
        iDestruct "Hrel" as (γpred) "#[Hrel Hsaved]".
        iDestruct (reg_in with "[$HM $Hrel]") as %HMeq;eauto. rewrite HMeq.
        iDestruct (big_sepM_delete _ _ x with "Hr") as "[Hx Hr]";[apply lookup_insert_eq|].
        rewrite delete_insert_id;[|apply lookup_delete_eq].
        iDestruct "Hx" as (ρ Hx) "[Hstate Hx]".
        destruct ρ.
        { iDestruct "Hx" as (γpred' p' φ' Heq Hpers') "(_ & Hx)".
          iDestruct "Hx" as (v' Hne') "(Hx & _)".
          inversion Heq; subst.
          iApply bi.False_elim. iApply (addr_dupl_false with "Hx' Hx"); auto. }
        { iDestruct "Hx" as (γpred' p' φ' Heq Hpers') "(_ & Hx)".
          iDestruct "Hx" as (v' Hne') "(Hx & _)".
          inversion Heq; subst.
          iApply bi.False_elim. iApply (addr_dupl_false with "Hx' Hx"); auto. }

        iMod (sts_update_std _ _ _ _ Temporary with "Hsts Hstate") as "[Hsts Hstate]".
        rewrite HMeq.
        iDestruct (region_map_delete with "Hr") as "Hr".
        iDestruct (region_map_insert _ _ _ _ _ Temporary with "Hr") as "Hr"; auto.
        iDestruct (big_sepM_delete _ _ x with "[ Hx' HmonoV Hφ Hstate $Hr]") as "Hr"
        ;[apply lookup_insert_eq|..].

        { iExists Temporary. iFrame. rewrite lookup_insert_eq. iSplit;auto. iExists γpred,p,φ. repeat (iSplit;auto).
          rewrite /close_list in Hrelated.
          destruct (isWL p).
          - iFrame "∗#"; iApply ("HmonoV" with "[] Hφ"); auto.
          - destruct (isDL p).
            + iFrame "∗#"; iApply ("HmonoV" with "[] Hφ"); auto.
            + iFrame "∗#"; iApply ("HmonoV" with "[] Hφ"); auto.
              iPureIntro; apply related_sts_pub_priv_world; auto.
        }
        iFrame.
        rewrite -!HMeq /std_update /=.
        iFrame.
        iModIntro.
        repeat (iSplit; auto).
        iPureIntro. rewrite dom_insert_L. rewrite -Hdom'.
        assert (x ∈ dom  Mρ);[apply elem_of_dom;eauto|]. set_solver.
      + iFrame; done.
  Qed.

  Lemma monotone_close_list_region_gen W W' C (l : list Addr) :
    ⊢ sts_full_world W' C
     ∗ region W' C
     ∗ close_list_resources_gen C W' l l false
     ==∗
     (sts_full_world (close_list l W') C
      ∗ region (close_list l W') C
     ).
  Proof.
    iIntros "(Hsts & Hr & Htemp)".
    assert (related_sts_pub_world W' (close_list l W')) as Hrelated'.
    { apply close_list_related_sts_pub; auto. }
    assert (dom (std W') = dom (std (close_list l W'))) as Heq.
    { rewrite /close_list.
      apply close_list_dom_eq. }
    iDestruct (region_monotone with "Hr") as "Hr";[apply Heq|apply Hrelated'| ].
    iMod (close_list_consolidate_gen _ _ l l with "[] [$Hr $Hsts Htemp]") as "[Hsts Hr]"
    ;[auto|eauto|iFrame;done].
  Qed.

  Lemma monotone_close_list_region W W' C (l : list Addr) :
    ⊢ ⌜related_sts_pub_world W (close_list l W')⌝ -∗
     sts_full_world W' C
     ∗ region W' C
     ∗ (close_list_resources C W l false)
     ==∗
     (sts_full_world (close_list l W') C
      ∗ region (close_list l W') C
     ).
  Proof.
    iIntros (Hrelated) "(Hsts & Hr & Htemp)".
    iApply monotone_close_list_region_gen; eauto; iFrame.
    iApply close_list_resources_gen_eq; eauto.
  Qed.


  (* ---------------------------------------------------------------- *)
  (* ----------------- UPDATE OF A REVOKED WORLD  ------------------- *)
  (* ---------------------------------------------------------------- *)

  Lemma monotone_revoke_region_def_update_loc W W' C MC Mρ :
    ⌜revoke_condition W⌝
    -∗ ⌜dom (std W) = dom MC⌝
    -∗ ⌜std W = std W'⌝
    -∗ ⌜related_sts_priv_world W W' ⌝
    -∗ sts_full_world W' C
    -∗ region_map_def W C MC Mρ
    -∗ sts_full_world W' C ∗ region_map_def W' C MC Mρ.
  Proof.
    iIntros (Hrevoked Hdom Hstd Hrelated) "Hfull Hr".
    rewrite /revoke in Hdom |- *.
    destruct W as [Wstd_sta Wloc].
    iDestruct (big_sepM_exists with "Hr") as (m') "Hr".
    iDestruct (big_sepM2_sep with "Hr") as "[HMρ Hr]".
    iDestruct (big_sepM2_sep with "Hr") as "[Hstates Hr]".
    iAssert (∀ a ρ, ⌜m' !! a = Some ρ⌝ → ⌜ρ ≠ Temporary⌝)%I as %Hmonotemp.
    { iIntros (a ρ Hsome).
      iDestruct (big_sepM2_lookup_l _ _ _ a with "Hstates") as (γp) "[Hl Hstate]"; eauto.
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hρ.
      iPureIntro.
      cbn in *; simplify_eq.
      rewrite /revoke_condition /= in Hrevoked.
      specialize (Hrevoked a); rewrite Hρ in Hrevoked.
      by intros ->.
    }
    iFrame.
    iApply big_sepM_exists. iExists m'.
    iApply big_sepM2_sep. iFrame.
    iDestruct (big_sepM2_sep with "[$Hstates $Hr]") as "Hr".
    iApply (big_sepM2_mono with "Hr").
    iIntros (a ρ γp Hm' HM) "/= [Hstate Ha]".
    specialize (Hmonotemp a ρ Hm').
    destruct ρ;iFrame;[contradiction|].
    iDestruct "Ha" as (γpred p φ) "(%Hγp & % & Hpred & Ha)".
    iDestruct "Ha" as (v Hne) "(Ha & #HmonoV & #Hφ)".
    iFrame "∗%#".
    iNext. iApply ("HmonoV" with "[] Hφ").
    iPureIntro.
    apply Hrelated.
  Qed.

  Lemma update_region_revoked_update_loc E W W' C :
    revoke_condition W →
    std W = std W' →
    (related_sts_priv_world W W') →
    sts_full_world W' C -∗
    region W C

    ={E}=∗

    region W' C
    ∗ sts_full_world W' C.
  Proof.
    intros Hrevoked Hstd Hrelated.
    iIntros "Hsts Hreg".
    rewrite region_eq /region_def.
    iDestruct "Hreg" as (M Mρ) "(Hγrel & %Hdom & %Hdom' & Hpreds)";simplify_eq.
    iDestruct (monotone_revoke_region_def_update_loc _ _ _ _ with "[] [] [] [] [$] [$]") as "[Hsts Hpreds]"; eauto.
    rewrite Hstd in Hdom.
    iFrame; eauto.
  Qed.


(* ------------------------------------------------------------------------------- *)
(* ----------------------------- SEPARATION LEMMAS ------------------------------- *)
(* ------------------------------------------------------------------------------- *)

  Lemma close_addr_resources_separation
    (C : CmptName) (W : WORLD) (a1 a2 : Addr) (v : Word) :
    a1 ↦ₐ v -∗
    close_addr_resources C W a2 false -∗
    ⌜ a1 ≠ a2 ⌝.
  Proof.
    iIntros "Hl1 (%&%&%&H&_)".
    iDestruct "H" as "(%&_&H&_)".
    iApply (address_neq with "Hl1 H"); eauto.
  Qed.

  Lemma close_addr_resources_gen_separation
    (C : CmptName) (W : WORLD) (a1 a2 : Addr) (l : list Addr) (v : Word) :
    a1 ↦ₐ v -∗
    close_addr_resources_gen C W l a2 false -∗
    ⌜ a1 ≠ a2 ⌝.
  Proof.
    iIntros "Hl1 (%&%&%&H&_)".
    iDestruct "H" as (? ?) "(%&_&H&_)".
    iApply (address_neq with "Hl1 H"); eauto.
  Qed.

  Lemma close_list_resources_separation
    (C : CmptName) (W : WORLD) (l : list Addr) (a : Addr) (v : Word) :
    a ↦ₐ v -∗
    close_list_resources C W l false -∗
    ⌜ a ∉ l ⌝.
  Proof.
    iIntros "Ha Hl".
    iInduction (l) as [|x l]; cbn; first (iPureIntro;set_solver).
    iDestruct "Hl" as "[Hx Hl]".
    iDestruct (close_addr_resources_separation with "[$] [$]") as "%H".
    iDestruct ("IHl" with "[$] [$]") as "%Hl".
    iPureIntro.
    apply not_elem_of_cons; split ; auto.
  Qed.

  Lemma close_list_resources_gen_separation
    (C : CmptName) (W : WORLD) (l' l : list Addr) (a : Addr) (v : Word) :
    a ↦ₐ v -∗
    close_list_resources_gen C W l' l false -∗
    ⌜ a ∉ l ⌝.
  Proof.
    iIntros "Ha Hl".
    iInduction (l) as [|x l]; cbn; first (iPureIntro;set_solver).
    iDestruct "Hl" as "[Hx Hl]".
    iDestruct (close_addr_resources_gen_separation with "[$] [$]") as "%H".
    iDestruct ("IHl" with "[$] [$]") as "%Hl".
    iPureIntro.
    apply not_elem_of_cons; split ; auto.
  Qed.

  Lemma close_addr_list_resources_separation
    (C1 C2 : CmptName) (W1 W2 : WORLD) (a1 : Addr) (l2 : list Addr) :
    close_addr_resources C1 W1 a1 false -∗
    close_list_resources C2 W2 l2 false -∗
    ⌜ a1 ∉ l2 ⌝.
  Proof.
    iIntros "(%&%&%&(%&_&H1&_)&_) H".
    iApply (close_list_resources_separation with "[$] [$]").
  Qed.

  Lemma close_addr_list_gen_resources_separation
    (C1 C2 : CmptName) (W1 W2 : WORLD) (a1 : Addr) (l' l2 : list Addr) :
    close_addr_resources C1 W1 a1 false -∗
    close_list_resources_gen C2 W2 l' l2 false -∗
    ⌜ a1 ∉ l2 ⌝.
  Proof.
    iIntros "(%&%&%&(%&_&H1&_)&_) H".
    iApply (close_list_resources_gen_separation with "[$] [$]").
  Qed.

  Lemma close_list_resources_separation_many
    (C1 C2 : CmptName) (W1 W2 : WORLD) (la l2 : list Addr) (lv : list Word) :
    ([∗ list] a;v ∈ la;lv, a ↦ₐ v) -∗
    close_list_resources C2 W2 l2 false -∗
    ⌜ la ## l2 ⌝.
  Proof.
    iIntros "Hl1 Hl2".
    iInduction (la) as [|a la] "IH" forall (lv); first (iPureIntro; set_solver+).
    - iDestruct (big_sepL2_length with "Hl1") as "%Hl1".
      destruct lv; simplify_eq.
      iDestruct "Hl1" as "[Ha Hl1]".
      iDestruct (close_list_resources_separation with "[$] [$]") as "%Ha".
      iDestruct ("IH" with "[$] [$]") as "%Hl".
      iPureIntro; set_solver.
  Qed.

  Lemma close_list_resources_gen_separation_many
    (C2 : CmptName) (W2 : WORLD) (la l' l2 : list Addr) (lv : list Word) :
    ([∗ list] a;v ∈ la;lv, a ↦ₐ v) -∗
    close_list_resources_gen C2 W2 l' l2 false -∗
    ⌜ la ## l2 ⌝.
  Proof.
    iIntros "Hl1 Hl2".
    iInduction (la) as [|a la] "IH" forall (lv); first (iPureIntro; set_solver+).
    - iDestruct (big_sepL2_length with "Hl1") as "%Hl1".
      destruct lv; simplify_eq.
      iDestruct "Hl1" as "[Ha Hl1]".
      iDestruct (close_list_resources_gen_separation with "[$] [$]") as "%Ha".
      iDestruct ("IH" with "[$] [$]") as "%Hl".
      iPureIntro; set_solver.
  Qed.

  Lemma close_list_resources_separation_many_alt
    (C1 C2 : CmptName) (W1 W2 : WORLD) (l1 l2 : list Addr) :
    close_list_resources C1 W1 l1 false
    ∗ close_list_resources C2 W2 l2 false
      -∗ ⌜ l1 ## l2 ⌝.
  Proof.
    iIntros "[Hl1 Hl2]".
    iInduction (l1) as [|a1 l1]; first (iPureIntro;set_solver+).
    iDestruct "Hl1" as "[Ha Hl1]".
    iDestruct (close_addr_list_resources_separation with "[$] [$Hl2]") as "%Ha".
    iDestruct ("IHl1" with "[$] [$]") as "%Hl".
    iPureIntro; set_solver.
  Qed.


  (** Obtain that an address is Revoked if we own the points-to *)
   Lemma revoked_by_separation
     (W : WORLD) (C : CmptName)
     (a : Addr) (w : Word) :
     a ∈ dom (std W) →
     region W C
     ∗ sts_full_world W C
     ∗ a ↦ₐ w
     ==∗
     region W C
     ∗ sts_full_world W C
     ∗ a ↦ₐ w
     ∗ ⌜ std W !! a = Some Revoked ⌝
   .
   Proof.
     iIntros (Hstd_a) "(Hregion & Hworld & Ha)".
     rewrite region_eq /region_def.
     iDestruct "Hregion" as (M Mρ) "(HM & %Hdom & %Hdom' & Hr)".
     rewrite /region_map_def.
     assert (is_Some (M !! a)) as [ [γ p] Hγp].
     { apply elem_of_dom. rewrite -Hdom. auto. }
     iMod (reg_get with "[$HM]") as "[HM Hrel]";[eauto|].
     iDestruct (big_sepM_delete _ _ a with "Hr") as "[Hstate Hr]";[eauto|].
     iDestruct "Hstate" as (ρ Ha) "[Hρ Hstate]".
     iDestruct (sts_full_state_std with "Hworld Hρ") as %Hx''; simplify_eq.
     iDestruct "Hstate" as (γ' p' φ) "(% & % & Hφ & Hstate)"; simplify_eq.
     iFrame "Hworld".
     iAssert ( ⌜ ρ = Revoked ⌝ )%I as "%" ; last iFrame "%".
     {
       destruct ρ; last done; iExFalso.
       - iDestruct "Hstate" as (v) "(% & Ha' & _)"; simplify_eq.
         iApply (addr_dupl_false with "[$] [$]"); eauto.
       - iDestruct "Hstate" as (v) "(% & Ha' & _)"; simplify_eq.
         iApply (addr_dupl_false with "[$] [$]"); eauto.
     }
     iDestruct (big_sepM_delete _ _ a with "[Hρ Hφ Hstate $Hr]") as "Hr";[eauto| |].
     { iFrame "∗%"; done. }
     simplify_eq.
     by iFrame.
   Qed.

   Lemma revoked_by_separation_many
     (W : WORLD) (C : CmptName)
     (la : list Addr) (lw : list Word) :
     Forall (λ a, a ∈ dom (std W)) la →
     region W C
     ∗ sts_full_world W C
     ∗ ([∗ list] a;w ∈ la;lw, a ↦ₐ w)
     ==∗
     region W C
     ∗ sts_full_world W C
     ∗ ([∗ list] a;w ∈ la;lw, a ↦ₐ w)
     ∗ ⌜ Forall (λ a, std W !! a = Some Revoked) la⌝
   .
   Proof.
     generalize dependent lw.
     induction la; iIntros (lw Hla) "(Hregion & Hworld & Hla)".
     - iFrame; done.
     - iDestruct (big_sepL2_length with "Hla") as "%Hlen_lw".
       destruct lw as [|w lw]; first (cbn in Hlen_lw ; congruence).
       rewrite big_sepL2_cons.
       iDestruct "Hla" as "[Ha Hla]".
       apply Forall_cons_iff in Hla.
       destruct Hla as [Ha Hla].
       iMod (IHla with "[$Hregion $Hworld $Hla]")
         as "(Hregion & Hworld & Hla & %Hforall_la)"; eauto.
       iMod (revoked_by_separation with "[$Hregion $Hworld $Ha]")
         as "(Hregion & Hworld & Ha & %Hforall_a)"; eauto; simplify_eq.
       rewrite Forall_cons_iff.
       iFrame; done.
   Qed.

  Lemma revoked_by_separation_with_temp_resources W W' C a :
    a ∈ dom (std W') ->
    close_addr_resources C W a false
    ∗ sts_full_world W' C
    ∗ region W' C
    ==∗
    close_addr_resources C W a false
    ∗ sts_full_world W' C
    ∗ region W' C
    ∗ ⌜ std W' !! a = Some Revoked ⌝.
  Proof.
    iIntros (Hin) "( (%&%&%& (%&%&Hv&Hmono&Hφ) &Hrel) & Hsts & Hr )".
    rewrite elem_of_dom in Hin; destruct Hin as [? Hin].
    iMod (revoked_by_separation with "[$Hsts $Hr $Hv]") as "(Hsts & Hr & Hv & %H')"; eauto.
    { by rewrite elem_of_dom. }
    simplify_eq.
    iModIntro.
    iFrame "∗%".
  Qed.

  Lemma revoked_by_separation_many_with_temp_resources W W' C la :
    Forall (λ a, a ∈ dom (std W')) la →
    close_list_resources C W la false
    ∗ sts_full_world W' C
    ∗ region W' C
    ==∗
    close_list_resources C W la false
    ∗ sts_full_world W' C
    ∗ region W' C
    ∗ ⌜ Forall (λ a, std W' !! a = Some Revoked) la⌝.
  Proof.
    induction la; iIntros (Hin) "(Hl & Hsts & Hr)"; cbn.
    - iModIntro; iFrame. by iPureIntro; apply Forall_nil.
    - iDestruct "Hl" as "[ Hl IHl]".
      apply Forall_cons in Hin as [Hin_a Hin].
      iMod (revoked_by_separation_with_temp_resources with "[$Hl $Hsts $Hr]")
        as "(Hl & Hsts & Hr & %)"; first done.
      iMod (IHla with "[$IHl $Hsts $Hr]") as "(IHl & Hsts & Hr & %)"; first done.
      iModIntro.
      iFrame "∗%".
      by iPureIntro; apply Forall_cons.
  Qed.

End region_invariant_revocation.
