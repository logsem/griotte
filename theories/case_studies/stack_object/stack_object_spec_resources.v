From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region proofmode.
From griotte Require Import switcher assert.
From griotte Require Import region_invariants_revocation region_invariants_allocation.
From griotte Require Import interp_weakening monotone world_std_revocation.
From griotte Require Import stack_object stack_object_helpers.

Section Stack_Object_Resources.
  Context
    {Σ : gFunctors}
    {ceriseg : ceriseG Σ}
    `{MP : MachineParameters}
    {swlayout : switcherLayout}
    {assertlayout : assertLayout}.

  Lemma so_main_imports_pointsto
      pc_b pc_a (C_f : Sealable) :
    (pc_b + length (so_main_imports C_f))%a = Some pc_a ->
    [[pc_b, pc_a]] ↦ₐ [[so_main_imports C_f]]
    ⊣⊢
      pc_b ↦ₐ
        WSentry XSRW_ Local b_switcher e_switcher a_switcher_call
      ∗ (pc_b ^+ 1)%a ↦ₐ
        WSentry RX Global b_assert e_assert b_assert
      ∗ (pc_b ^+ 2)%a ↦ₐ WSealed ot_switcher C_f
      ∗ region_pointsto (pc_b ^+ 3)%a pc_a [].
  Proof.
    intros Himports.
    cbn in Himports.
    rewrite /so_main_imports.
    iSplit.
    - iIntros "Himports".
      iDestruct (region_pointsto_cons with "Himports") as "[Hswitcher Himports]".
      { transitivity (Some (pc_b ^+ 1)%a); auto; solve_addr. }
      { solve_addr. }
      iDestruct (region_pointsto_cons with "Himports") as "[Hassert Himports]".
      { transitivity (Some (pc_b ^+ 2)%a); auto; solve_addr. }
      { solve_addr. }
      iDestruct (region_pointsto_cons with "Himports") as "[Htarget Himports]".
      { transitivity (Some (pc_b ^+ 3)%a); auto; solve_addr. }
      { solve_addr. }
      iFrame.
    - iIntros "(Hswitcher & Hassert & Htarget & Himports)".
      iApply (region_pointsto_cons _ (pc_b ^+ 1)%a); [solve_addr|solve_addr|].
      iFrame.
      iApply (region_pointsto_cons _ (pc_b ^+ 2)%a); [solve_addr|solve_addr|].
      iFrame.
      iApply (region_pointsto_cons _ (pc_b ^+ 3)%a); [solve_addr|solve_addr|].
      iFrame.
  Qed.

End Stack_Object_Resources.

Section Stack_Object_Region_Resources.
  Context
    {Σ : gFunctors}
    {ceriseg : ceriseG Σ} {sealsg : sealStoreG Σ}
    {Cname : CmptNameG} {CNames : gset CmptName}
    {stsg : STSG Addr region_type Σ}
    {relg : relGS Σ} {cstackg : CSTACKG Σ}
    `{MP : MachineParameters}.

  Lemma stack_object_open_region_for_checkints
      (W0 : WORLD) (C : CmptName)
      (p : Perm) (g : Locality) (b e cur : Addr)
      (csp_b csp_e : Addr)
      (l_revoked : list Addr) (stk_mem : list Word) :
    let W1 := revoke W0 in
    let object := so_object_addresses b e in
    let temps := so_object_temporaries W0 b e in
    let perms := so_object_permanents W0 b e in
    let rest := so_revoked_without_object W0 b e l_revoked in
    extract_temporaries_condition
      W0 (l_revoked ++ finz.seq_between csp_b csp_e) ->
    object ## finz.seq_between csp_b csp_e ->
    readAllowed p = true ->
    interp W0 C (WCap p g b e cur)
    ∗ world_interp W1 C
    ∗ ▷ RevokedResources W0 C l_revoked
    ∗ [[csp_b, csp_e]] ↦ₐ [[stk_mem]]
    ∗ £ 1
    ={⊤}=∗
    ∃ object_mem,
      ⌜length object_mem = length object⌝
      ∗ ⌜object ≡ₚ perms ++ temps⌝
      ∗ ([∗ list] a;v ∈ perms ++ temps;object_mem, a ↦ₐ v)
      ∗ ▷ (
          ⌜Forall (fun w => exists z : Z, w = WInt z) object_mem⌝
          ∗ ([∗ list] a;v ∈ perms ++ temps;object_mem, a ↦ₐ v)
          ∗ £ 1
          ={⊤}=∗
          world_interp (close_list temps W1) C
          ∗ RevokedResources W0 C rest
          ∗ [[csp_b, csp_e]] ↦ₐ [[stk_mem]]
          ∗ interp
              (close_list temps W1) C
              (WCap p g b e (finz.max b e))).
  Proof.
    intros W1 object temps perms rest.
    iIntros (Hextract Hobject_stack Hread)
      "(#Hinterp_wca0_W0 & Hworld_interp_C & Hl_revoked & Hstk & Hlc)".
    destruct Hextract as [Hrevoked_nodup Hrevoked_temps].

    (* Classify the readable object region, then partition it into permanent
       cells and temporary cells that were revoked with the current frame. *)
    iAssert (⌜Forall
      (fun a => std W0 !! a = Some Permanent \/
                std W0 !! a = Some Temporary) object⌝)%I
      as %Hobject_states.
    { iDestruct (readAllowed_valid_cap with "Hinterp_wca0_W0") as %Hvalid; auto.
      iPureIntro.
      eapply Forall_impl; eauto; cbn.
      intros a (ρ & Ha & Hρ).
      destruct ρ; [right|left|]; done.
    }
    assert (object ≡ₚ perms ++ temps) as Hobject_partition.
    { apply so_object_addresses_partition. exact Hobject_states. }
    change (finz.seq_between b e ≡ₚ perms ++ temps) in Hobject_partition.

    assert (temps ⊆ l_revoked) as Htemps_subset.
    { intros a Ha.
      subst temps object.
      apply list_elem_of_filter in Ha as [Ha Ha_object].
      apply Hrevoked_temps in Ha.
      apply elem_of_app in Ha as [Ha|Ha]; first done.
      rewrite elem_of_disjoint in Hobject_stack.
      exfalso. eapply Hobject_stack; eauto.
    }
    apply NoDup_app in Hrevoked_nodup as (Hl_revoked_nodup & _ & _).
    assert (temps ≡ₚ filter (fun a => a ∈ temps) l_revoked)
      as Htemps_filter.
    { apply NoDup_subset_filter_membership; auto.
      apply so_object_temporaries_NoDup.
    }
    assert (l_revoked ≡ₚ temps ++ rest) as Hl_revoked_partition.
    { subst rest.
      rewrite {1}Htemps_filter.
      apply filter_complement_list.
    }
    iDestruct (lc_fupd_elim_later with "Hlc Hl_revoked") as ">Hl_revoked".
    iEval (setoid_rewrite Hl_revoked_partition) in "Hl_revoked".
    iDestruct (RevokedResources_app with "Hl_revoked") as
      "[Hrevoked_temps Hrevoked_rest]".

    (* Open only the permanent part through the world interpretation.  The
       permission, predicate, and STS witnesses stay local to this helper. *)
    iDestruct (read_allowed_inv_full_cap with "Hinterp_wca0_W0")
      as "Hinterp_wca0_invs"; auto.
    iAssert (
        ∃ (wca0_invs : list
             (Addr * Perm * (WORLD * CmptName * Word -> iProp Σ) * region_type)),
          ⌜(fun '(a, _, _, _) => a) <$> wca0_invs = perms⌝ ∗
          ⌜Forall
              (fun '(a, _, _, ρ) =>
                 std W0 !! a = Some ρ /\ ρ = Permanent)
              wca0_invs⌝ ∗
          ([∗ list] '(a, p0, φ, _) ∈ wca0_invs, rel C a p0 φ) ∗
          ⌜Forall
              (fun '(_, _, φ, _) =>
                 forall Wv : WORLD * CmptName * Word, Persistent (φ Wv))
              wca0_invs⌝)%I
      as (wca0_invs)
        "(%Hwca0_invs_perma & %Hwca0_invs_std_perma
         & Hrels_wca0 & %Hpers_wca0_invs)".
    { iDestruct "Hinterp_wca0_invs" as "-#Hinterp_wca0_invs".
      iClear "#".
      setoid_rewrite Hobject_partition.
      iDestruct (big_sepL_app with "Hinterp_wca0_invs") as "[H _]".
      iDestruct "H" as "#H".
      assert (Forall (fun a => std W0 !! a = Some Permanent) perms)
        as Hperms.
      { subst perms.
        rewrite /so_object_permanents /so_object_addresses.
        clear.
        induction (finz.seq_between b e); first done.
        cbn.
        destruct (decide (std W0 !! a = Some Permanent)); last done.
        apply Forall_cons; split; auto.
      }
      generalize perms, Hperms.
      clear; intros l Hl.
      iInduction (l) as [|a l] "IH".
      - iExists []; cbn.
        repeat (iSplit; iPureIntro; done).
      - apply Forall_cons in Hl as [Ha Hl].
        cbn.
        iDestruct "H" as
          "[(%p' & %P' & %Hpermflow & %HpersP & HrelP
             & Hzcond & Hrcond & Hwcond & Hmono) H]".
        iDestruct ("IH" with "[%] [$]") as
          (invs) "(%Hl_ & %Hperma & #Hrels & %Hpers)"; auto.
        iExists (((a, p', safeC P'), Permanent) :: invs).
        iSplit; first (iPureIntro; cbn; by rewrite Hl_).
        iSplit; first (iPureIntro; apply Forall_cons; split; auto).
        iSplit; first (cbn; iFrame "#").
        iPureIntro. apply Forall_cons; split; auto.
    }

    rewrite open_world_interp_empty.
    iDestruct (open_world_interp_list with
      "[$Hrels_wca0 $Hworld_interp_C]") as
      (wca0_lv_perma)
      "(Hworld_interp_C & Hsts_std_wca0 & Hperms_lv
       & Hwca0_mono & Hwca0_φs & %Hlength_wca0_lv & Hwca0_pO)".
    { rewrite Hwca0_invs_perma. apply so_object_permanents_NoDup. }
    { rewrite Hwca0_invs_perma. set_solver+. }
    { rewrite !Forall_forall in Hwca0_invs_std_perma |- *.
      intros [ [ [ ] ] ] Hx; cbn in *; simplify_eq.
      apply Hwca0_invs_std_perma in Hx.
      destruct Hx as [_ ->]; done.
    }
    { cbn in *.
      rewrite !Forall_forall in Hwca0_invs_std_perma |- *.
      intros [ [ [ ] ] ] Hx; cbn in *; simplify_eq.
      apply Hwca0_invs_std_perma in Hx.
      destruct Hx as [Hx ->].
      by apply revoke_lookup_Perm.
    }
    iAssert ([∗ list] a;v ∈ perms;wca0_lv_perma, a ↦ₐ v)%I
      with "[Hperms_lv]" as "Hperms_lv".
    { iClear "#". clear -Hwca0_invs_perma.
      iStopProof.
      rewrite -Hwca0_invs_perma big_sepL2_fmap_l.
      generalize dependent perms; intros l Hl.
      generalize dependent wca0_invs.
      generalize dependent wca0_lv_perma.
      induction l; iIntros (lv linvs Hl) "Hl".
      - apply fmap_nil_inv in Hl; simplify_eq; done.
      - apply fmap_cons_inv in Hl; simplify_eq.
        destruct Hl as (apφρ & l' & Ha & Hl' & Hl); cbn in *.
        destruct apφρ as [ [ [] ] ]; simplify_eq; cbn.
        iDestruct (big_sepL2_length with "Hl") as %Hlen.
        destruct lv; simplify_eq.
        cbn. iDestruct "Hl" as "[$ Hl]".
        iApply IHl; eauto.
    }
    assert (Forall
      (fun a => std (revoke W0) !! a = Some Revoked) temps)
      as Hrevoked_temps_pure.
    { apply Forall_forall. intros a Ha.
      apply revoke_lookup_Monotemp.
      apply Hrevoked_temps.
      apply elem_of_app; left.
      by apply Htemps_subset.
    }

    iAssert (
        ∃ (lp : list Perm)
          (lφ : list (WORLD * CmptName * Word -> iPropI Σ))
          (lv : list Word),
          ⌜length lp = length temps⌝
          ∗ ⌜length lφ = length temps⌝
          ∗ ⌜length lv = length temps⌝
          ∗ ([∗ list] φ ∈ lφ,
               ⌜forall Wv : WORLD * CmptName * Word, Persistent (φ Wv)⌝)
          ∗ ([∗ list] a;pφ ∈ temps;(zip lp lφ), rel C a pφ.1 pφ.2)
          ∗ ([∗ list] p0 ∈ lp, ⌜isO p0 = false⌝)
          ∗ ([∗ list] a;v ∈ temps;lv, a ↦ₐ v)
          ∗ ([∗ list] lpφ;v ∈ (zip lp lφ);lv,
               if isWL lpφ.1 then future_pub_mono C lpφ.2 v
               else if isDL lpφ.1 then future_pub_mono C lpφ.2 v
                    else future_priv_mono C lpφ.2 v)
          ∗ ([∗ list] φ;v ∈ lφ;lv, φ (W0, C, v)))%I
      with "[Hrevoked_temps]" as
      (lp lφ wca0_lv_temps)
      "(%Hlen_lp & %Hlen_lφ & %Hlen_lv & Hlφ_pers
       & #Hlpφ_rels & HlpO & Htemps_lv & Hlpφ_mono & Hlφ_lv)".
    { iClear "#".
      generalize temps. clear; intros l.
      iInduction (l) as [|a l] "IH".
      - iExists [], [], []; cbn; done.
      - iDestruct "Hrevoked_temps" as "[Ha Hl]".
        iDestruct ("IH" with "Hl") as "Hl".
        iDestruct "Ha" as (p0 P HpersP) "[Hrel_a Ha]".
        iDestruct "Ha" as (v) "(HpO & Hv & HP & HmonoP)".
        iDestruct "Hl" as (lp0 lP lv)
          "(% & % & % & %Hpers_lP & Hrels & HpOs & Hvs & Hmonos & HPs)".
        iExists (p0 :: lp0), (P :: lP), (v :: lv).
        rewrite mono_temporary_eq.
        iFrame. iFrame "%".
        iPureIntro. cbn; lia.
    }
    (* Present [checkints] with one points-to list.  Its address order may be
       permuted, but the object contents and length remain unchanged. *)
    iDestruct (big_sepL2_app with "Hperms_lv Htemps_lv") as "Hobject_mem".

    iModIntro.
    iExists (wca0_lv_perma ++ wca0_lv_temps).
    iSplit; first iPureIntro.
    { rewrite length_app Hlength_wca0_lv Hlen_lv Hwca0_invs_perma.
      change
        (length perms + length temps = length (finz.seq_between b e)).
      rewrite -length_app.
      symmetry. by apply Permutation_length.
    }
    iSplit; first done.
    iFrame "Hobject_mem".
    iNext.
    iIntros "(%Hobject_ints & Hobject_mem & Hlc)".

    iDestruct (big_sepL2_app' with "Hobject_mem") as
      "[Hperms_lv Htemps_lv]".
    { by rewrite Hlength_wca0_lv Hwca0_invs_perma. }
    iAssert
      ([∗ list] '(a0, _, _, _);v ∈ wca0_invs;wca0_lv_perma,
         a0 ↦ₐ v)%I
      with "[Hperms_lv]" as "Hperms_lv".
    { iClear "#". clear -Hwca0_invs_perma.
      iStopProof.
      rewrite -Hwca0_invs_perma big_sepL2_fmap_l.
      generalize dependent perms; intros l Hl.
      generalize dependent wca0_invs.
      generalize dependent wca0_lv_perma.
      induction l; iIntros (lv linvs Hl) "Hl".
      - apply fmap_nil_inv in Hl; simplify_eq; done.
      - apply fmap_cons_inv in Hl; simplify_eq.
        destruct Hl as (apφρ & l' & Ha & Hl' & Hl); cbn in *.
        destruct apφρ as [ [ [] ] ]; simplify_eq; cbn.
        iDestruct (big_sepL2_length with "Hl") as %Hlen.
        destruct lv; simplify_eq.
        cbn. iDestruct "Hl" as "[$ Hl]".
        iApply IHl; eauto.
    }

    (* The continuation first closes permanent resources back into [W1], then
       uses the integer-valued temporary cells to reinstate the object. *)
    iDestruct (close_world_interp_list W1 C wca0_invs [] with
      "[$Hworld_interp_C $Hsts_std_wca0 $Hperms_lv $Hwca0_mono
        $Hwca0_φs $Hrels_wca0 $Hwca0_pO]") as "Hworld_interp_C".
    { by rewrite Hlength_wca0_lv length_fmap. }
    { rewrite Hwca0_invs_perma. apply so_object_permanents_NoDup. }
    { set_solver+. }
    { rewrite !Forall_forall in Hwca0_invs_std_perma |- *.
      intros [ [ [ ] ] ] Hx; cbn in *; simplify_eq.
      apply Hwca0_invs_std_perma in Hx.
      destruct Hx as [_ ->]; done.
    }
    { auto. }
    rewrite -open_world_interp_empty.

    iAssert (▷ [∗ list] φ ∈ lφ, zcond (safeUC φ) C)%I as "#Hzcond_lφ".
    { iClear "∗".
      iDestruct "Hlpφ_rels" as "-#Hrels".
      iDestruct "Hinterp_wca0_invs" as "-#Hinterp".
      iClear "#".
      setoid_rewrite Hobject_partition.
      iDestruct (big_sepL_app with "Hinterp") as "[_ #Hinterp]".
      generalize temps, Hlen_lp, Hlen_lφ. clear.
      intros l Hlen_lp Hlen_lφ.
      iInduction (l) as [|a l] "IH" forall (lp lφ Hlen_lp Hlen_lφ).
      all: destruct lφ; simplify_eq.
      all: destruct lp; simplify_eq.
      - done.
      - cbn.
        iDestruct "Hinterp" as
          "[(%p' & %P' & _ & _ & Hrel' & Hzcond & _) Hinterp]".
        iDestruct "Hrels" as "[Hrel #Hrels]".
        iDestruct (rel_agree with "[$Hrel $Hrel']") as "[_ #Heq]".
        iSplitL "Heq"; last (iApply "IH"; eauto).
        iNext. iIntros (???) "!> H"; cbn.
        iDestruct ("Heq" $! (W1, C, WInt z)) as "-#Heq0".
        iDestruct ("Heq" $! (W2, C, WInt z)) as "-#Heq1".
        iDestruct (internal_eq_iff with "Heq1") as "[_ Heq1]".
        iDestruct (internal_eq_iff with "Heq0") as "[Heq0 _]".
        iApply "Heq1".
        iDestruct ("Heq0" with "H") as "H".
        iApply "Hzcond"; eauto.
    }
    iDestruct (lc_fupd_elim_later with "Hlc Hzcond_lφ") as ">Hzcond_lφ'".
    iAssert ([∗ list] φ;v ∈ lφ;wca0_lv_temps, φ (W1, C, v))%I
      with "[Hlφ_lv Hzcond_lφ']" as "Hlφ_lv".
    { iClear "#".
      apply Forall_app in Hobject_ints as [_ Htemps_ints].
      generalize wca0_lv_temps, Htemps_ints, Hlen_lv.
      generalize temps, Hlen_lp, Hlen_lφ. clear.
      intros la Hlen_lp Hlen_lφ lv Hl_ints Hlen_lv.
      iInduction (la) as [|a la] "IH"
        forall (lp lφ lv Hlen_lp Hlen_lφ Hlen_lv Hl_ints).
      all: destruct lφ; simplify_eq.
      all: destruct lp; simplify_eq.
      all: destruct lv; simplify_eq.
      - done.
      - cbn.
        iDestruct "Hlφ_lv" as "[Hb Hlb]".
        iDestruct "Hzcond_lφ'" as "[#Hz Hzl]".
        apply Forall_cons in Hl_ints as [ [z ->] Hl_ints].
        iSplitL "Hb Hz";
          last (iApply ("IH" with "[] [] [] [] [$] [$]"); eauto).
        rewrite /zcond.
        iSpecialize ("Hz" $! W0 W1 z). cbn.
        iApply "Hz"; auto.
    }
    iDestruct (big_sepL2_disjoint with "[$Hstk $Htemps_lv]") as %Htemps_stack.
    iAssert
      ([∗ list] a ∈ temps,
         ∃ p0 φ,
           ⌜forall Wv, Persistent (φ Wv)⌝ ∗
           temp_resources W1 C φ a p0 ∗ rel C a p0 φ)%I
      with "[Hlφ_pers HlpO Hlpφ_mono Htemps_lv Hlφ_lv]"
      as "Htemps_closing_resources".
    { iDestruct "Hlpφ_rels" as "-#Hlpφ_rels".
      iClear "#".
      clear -Hlen_lp Hlen_lφ Hlen_lv.
      generalize dependent temps; intros l Hlen_lp Hlen_lφ Hlen_lv.
      generalize wca0_lv_temps Hlen_lv; intros lv.
      clear Hlen_lv wca0_lv_temps; intros Hlen_lv.
      iRename "Htemps_lv" into "Hlv".
      iInduction (l) as [|a l] "IH"
        forall (lφ lp lv Hlen_lp Hlen_lφ Hlen_lv); first done.
      destruct lv as [|v lv]; cbn in Hlen_lv; simplify_eq.
      destruct lφ as [|φ lφ]; cbn in Hlen_lφ; simplify_eq.
      destruct lp as [|p0 lp]; cbn in Hlen_lp; simplify_eq.
      cbn in *.
      iDestruct "Hlφ_pers" as "[Hlφ_pers_a Hlφ_pers]".
      iDestruct "HlpO" as "[HlpO_a HlpO]".
      iDestruct "Hlpφ_mono" as "[Hlpφ_mono_a Hlpφ_mono]".
      iDestruct "Hlv" as "[Hlv_a Hlv]".
      iDestruct "Hlφ_lv" as "[Hlφ_lv_a Hlφ_lv]".
      iDestruct "Hlpφ_rels" as "[Hlpφ_rels_a Hlpφ_rels]".
      iFrame.
      iApply ("IH" $! lφ lp lv with
        "[%] [%] [%] [$] [$] [$] [$] [$] [$]"); eauto.
    }
    iMod (world_interp_restore_world W1 W1 C temps with
      "[$Hworld_interp_C] [Htemps_closing_resources]")
      as "Hworld_interp_C".
    { apply close_list_related_sts_pub. }
    { iClear "#".
      iApply (big_sepL_impl with "Htemps_closing_resources").
      iModIntro; iIntros (k ka Hka) "(% & % & $ & (% & $ & $ & ? & $) & $)".
      by rewrite mono_temporary_eq.
    }
    set (W2 := close_list temps W1).

    iAssert (interp W2 C (WCap p g b e (finz.max b e)))%I
      as "#Hinterp_wca0_W2".
    { iEval (rewrite fixpoint_interp1_eq interp1_eq).
      iEval (rewrite fixpoint_interp1_eq interp1_eq) in "Hinterp_wca0_W0".
      destruct (isO p); first done.
      destruct (has_sreg_access p); first done.
      iDestruct "Hinterp_wca0_W0" as "[Hinterp $]".
      iClear "∗".
      iApply (big_sepL_impl with "Hinterp").
      iModIntro.
      iIntros (k x Hx)
        "(%px & %Px & %Hpx_flow & %Hpers_Px & Hrelx
         & Hzcondx & Hrcondx & Hwcondx & Hmonox & %Hstatex)".
      iFrame "∗%".
      apply list_elem_of_lookup_2 in Hx.
      rewrite Forall_forall in Hobject_states.
      assert (std W0 !! x = std W2 !! x) as Hxeq.
      { destruct (Hobject_states x Hx) as [Hx'|Hx']; rewrite Hx'; symmetry.
        - rewrite close_list_lookup_not_in.
          { cbn. by apply revoke_lookup_Perm. }
          intro Hcontra.
          apply list_elem_of_filter in Hcontra as [Hcontra _].
          by rewrite Hcontra in Hx'.
        - apply close_list_lookup_in; auto.
          + cbn; apply revoke_lookup_Monotemp; auto.
          + apply list_elem_of_filter; split; done.
      }
      iSplitL "Hmonox".
      - rewrite /monoReq. by rewrite Hxeq.
      - iPureIntro.
        destruct (isWL p);
          rewrite !/region_state_nwl !/region_state_pwl in Hstatex |- *;
          rewrite -Hxeq; done.
    }
    iEval (rewrite /reinstate) in "Hworld_interp_C".
    iModIntro. iFrame.
    iExact "Hinterp_wca0_W2".
  Qed.

  Lemma stack_object_reinstate_fresh_object
      (W0 W2 : WORLD) (C : CmptName)
      (stack_b stack_e stack_a a_stk1 a_stk2 : Addr) :
    let W3 := reinstate W2 [a_stk1] in
    (a_stk1 + 1)%a = Some a_stk2 ->
    (stack_b <= a_stk1)%a /\
    (a_stk1 < a_stk2)%a /\
    (a_stk2 <= stack_e)%a ->
    std W0 !! a_stk1 = Some Temporary ->
    std W2 !! a_stk1 = Some Revoked ->
    related_sts_priv_world W0 W2 ->
    interp W0 C (WCap RWL Local stack_b stack_e stack_a)
    ∗ world_interp W2 C
    ∗ a_stk1 ↦ₐ WInt 0
    ∗ £ 1
    ={⊤}=∗
      world_interp W3 C
      ∗ ⌜related_sts_pub_world W2 W3⌝
      ∗ ⌜std W3 !! a_stk1 = Some Temporary⌝
      ∗ interp W3 C (WCap RWL Local a_stk1 a_stk2 a_stk1).
  Proof.
    intros W3 Ha_stk2 Hbounds Ha_stk1_W0 Ha_stk1_W2 Hpriv.
    iIntros "(#Hinterp_stack & Hworld_interp & Ha_stk1 & Hlc)".
    destruct Hbounds as (Hstack_b_stk1 & Hastk1_stk2 & Hastk2_stack_e).

    (* Turn the freshly zeroed stack cell into the closing resource required
       by [world_interp_restore_world], consuming exactly one later credit. *)
    iAssert (
        |={⊤}=> ([∗ list] a ∈ [a_stk1],
          ∃ p φ, ⌜forall Wv, Persistent (φ Wv)⌝
            ∗ temp_resources W2 C φ a p ∗ rel C a p φ)
      )%I with "[Ha_stk1 Hlc]" as ">Hclosing_resources".
    { cbn.
      iDestruct (read_allowed_inv _ _ a_stk1 with "Hinterp_stack")
        as "(%pastk1 & %Pastk1 & %Hpastk1_rwl & %Hpers_Pastk1
             & #Hrel_astk1 & Hzcond_Pastk1 & Hrcond_Pastk1
             & Hwcond_Pastk1 & Hmono_Pastk1)"; auto.
      { solve_addr+Ha_stk2 Hstack_b_stk1 Hastk1_stk2 Hastk2_stack_e. }
      replace (writeAllowed pastk1) with true.
      2: { symmetry; eapply writeAllowed_flowsto; eauto. }
      iDestruct (lc_fupd_elim_later with "[$] [$Hwcond_Pastk1]")
        as ">#Hwcond_Pastk1'".
      assert (isWL pastk1 = true) as Hpastk1_wl.
      { apply isWL_flowsto in Hpastk1_rwl; done. }
      iModIntro.
      iSplitL; last done.
      iExists pastk1, (safeC Pastk1).
      iSplit; first iPureIntro.
      { intros Wcv; apply Hpers_Pastk1. }
      iSplit; last iFrame "#".
      iFrame "Ha_stk1".
      iSplit; first iPureIntro.
      { by apply isWL_nonO. }
      rewrite /monoReq !Hpastk1_wl Ha_stk1_W0.
      iSplit; first iApply "Hmono_Pastk1".
      rewrite /=.
      iApply "Hwcond_Pastk1'".
      iApply interp_int.
    }

    (* Reinstate the cell and package both its state transition and the safe
       singleton RWL capability needed by the adversary call. *)
    iMod (world_interp_restore_world W2 W2 C [a_stk1]
      with "[$Hworld_interp] [Hclosing_resources]")
      as "Hworld_interp".
    { apply close_list_related_sts_pub. }
    { iClear "#".
      iApply (big_sepL_impl with "Hclosing_resources").
      iModIntro; iIntros (k ka Hka) "(%&%&$&(%&$&$&?&$)&$)".
      by rewrite mono_temporary_eq.
    }

    assert (related_sts_pub_world W2 W3) as Hpub.
    { apply close_list_related_sts_pub. }
    assert (std W3 !! a_stk1 = Some Temporary) as Ha_stk1_W3.
    { apply close_list_lookup_in; auto; set_solver+. }

    iAssert (interp W3 C (WCap RWL Local a_stk1 a_stk2 a_stk1))%I
      as "#Hinterp_fresh".
    { iEval (rewrite fixpoint_interp1_eq interp1_eq).
      cbn.
      iSplit; last done.
      rewrite (finz_seq_between_singleton a_stk1 a_stk2);
        last solve_addr+Ha_stk2 Hastk1_stk2.
      cbn.
      iSplit; last done.
      iClear "∗".
      iDestruct "Hinterp_stack" as "-#Hinterp"; iClear "#".
      iDestruct (read_allowed_inv _ _ a_stk1 with "Hinterp")
        as "(%px & %Px & %Hpx_flow & %HPx_pers & Hrelx
             & Hzcondx & Hrcondx & Hwcondx & Hmonox)"; auto.
      { solve_addr+Ha_stk2 Hstack_b_stk1 Hastk1_stk2 Hastk2_stack_e. }
      iFrame "∗%".
      apply readAllowed_flowsto in Hpx_flow; last done.
      rewrite Hpx_flow; iFrame.
      rewrite /monoReq Ha_stk1_W0 Ha_stk1_W3; done.
    }
    iModIntro. iFrame "#∗%".
  Qed.

End Stack_Object_Region_Resources.
