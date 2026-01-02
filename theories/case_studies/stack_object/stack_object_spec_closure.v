From iris.proofmode Require Import proofmode.
From cap_machine Require Import region_invariants_allocation region_invariants_revocation interp_weakening monotone.
From cap_machine Require Import rules logrel logrel_extra monotone proofmode register_tactics.
From cap_machine Require Import fetch_spec assert_spec checkints checkra check_no_overlap_spec.
From cap_machine Require Import
  switcher interp_switcher_call switcher_spec_call switcher_spec_return.
From cap_machine Require Import stack_object.
From cap_machine Require Import proofmode.

Section SO.
  Lemma filter_complement_list {A : Type} (l : list A) (P : A -> Prop) {Hdec: ∀ x, Decision (P x)} :
    l ≡ₚ filter P l ∪ filter (λ x : A, ¬ P x) l.
  Proof.
    induction l; cbn; first done.
    rewrite /union /disjoint_regions_tactics.Union_list.
    destruct ( decide (P a) ); destruct ( decide (¬ P a) ); try done.
    + rewrite -app_comm_cons {1}IHl; done.
    + rewrite -Permutation_middle {1}IHl; done.
  Qed.

  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  (* TODO move *)
  Lemma close_list_lookup_not_in W l a :
    a ∉ l -> std (close_list l W) !! a = std W !! a.
  Proof.
    intros Ha.
    induction l as [|a' l]; cbn; first done.
    apply not_elem_of_cons in Ha; destruct Ha as [Haeq Ha].
    apply IHl in Ha.
    rewrite -Ha.
    destruct (W.1 !! a') eqn:Ha'; last done.
    destruct (decide (Revoked = r)); last done.
    simplify_map_eq.
    done.
  Qed.
  Lemma close_list_lookup_in W l a :
    std W !! a = Some Revoked -> a ∈ l -> std (close_list l W) !! a = Some Temporary.
  Proof.
    intros Hrevoked Ha.
    induction l as [|a' l]; cbn;first set_solver.
    destruct (decide (a = a')) as [-> | Ha'].
    + rewrite Hrevoked.
      destruct (decide (Revoked = Revoked)); last done.
      by simplify_map_eq.
    + apply elem_of_cons in Ha; destruct Ha as [-> | Ha]; first done.
      apply IHl in Ha.
      destruct (W.1 !! a') eqn:Ha''; auto.
      destruct (decide (Revoked = r)); auto.
      by simplify_map_eq.
  Qed.
  Lemma close_list_lookup_Temporary W l a :
    std W !! a = Some Temporary -> std (close_list l W) !! a = Some Temporary.
  Proof.
    intros Hrevoked.
    induction l as [|a' l]; cbn;first set_solver.
    destruct (decide (a = a')) as [-> | Ha'].
    + rewrite Hrevoked.
      destruct (decide (Revoked = Temporary)); first done.
      by rewrite IHl.
    + destruct (W.1 !! a') eqn:Ha''; auto.
      destruct (decide (Revoked = r)); auto.
      by simplify_map_eq.
  Qed.
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
  Lemma close_addr_resources_separation_alt
    (C1 C2 : CmptName) (W1 W2 : WORLD) (a1 a2 : Addr) :
    close_addr_resources C1 W1 a1 false -∗
    close_addr_resources C2 W2 a2 false -∗
    ⌜ a1 ≠ a2 ⌝.
  Proof.
    iIntros "(%&%&%&(%&_&H1&_)&_) (%&%&%&(%&_&H2&_)&_)".
    iApply (address_neq with "H1 H2"); eauto.
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

  Context {C : CmptName}.

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).

  Lemma stack_object_f_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)

    (b_so_exp_tbl e_so_exp_tbl : Addr)
    (g_so_exp_tbl : Locality)

    (b_assert e_assert : Addr) (a_flag : Addr)
    (C_f : Sealable)

    (W : WORLD)

    (Nassert Nswitcher Nso SON : namespace)

    :

    let imports :=
     so_main_imports
       b_switcher e_switcher a_switcher_call ot_switcher b_assert e_assert C_f
    in

    Nswitcher ## Nassert ->
    Nswitcher ## Nso ->
    Nassert ## Nso ->
    (b_so_exp_tbl <= b_so_exp_tbl ^+ 2 < e_so_exp_tbl)%a ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length so_main_code)%a ->
    (pc_b + length imports)%a = Some pc_a ->
    (cgp_b + length so_main_data)%a = Some cgp_e ->

    na_inv logrel_nais Nassert (assert_inv b_assert e_assert a_flag)
    ∗ na_inv logrel_nais Nswitcher switcher_inv
    ∗ na_inv logrel_nais Nso
        ([[ pc_b , pc_a ]] ↦ₐ [[ imports ]] ∗ codefrag pc_a so_main_code)
    ∗ inv (export_table_PCCN SON) (b_so_exp_tbl ↦ₐ WCap RX Global pc_b pc_e pc_b)
    ∗ inv (export_table_CGPN SON) ((b_so_exp_tbl ^+ 1)%a ↦ₐ WCap RW Global cgp_b cgp_e cgp_b)
    ∗ inv (export_table_entryN SON (b_so_exp_tbl ^+ 2)%a)
        ((b_so_exp_tbl ^+ 2)%a ↦ₐ WInt (encode_entry_point 2 (length (imports ++ SO_main_code_run))))
    ∗ WSealed ot_switcher (SCap RO g_so_exp_tbl b_so_exp_tbl e_so_exp_tbl (b_so_exp_tbl ^+ 2)%a)
        ↦□ₑ 2
    ∗ seal_pred ot_switcher ot_switcher_propC
      -∗
    ot_switcher_prop W C (WCap RO g_so_exp_tbl b_so_exp_tbl e_so_exp_tbl (b_so_exp_tbl ^+ 2)%a).
  Proof.
    intros imports.
    iIntros (Hswitcher_assert HNswitcher_so HNassert_so
               Hso_exp_tbl_size Hso_size_code Hso_imports Hcgp_size)
      "(#Hassert & #Hswitcher
      & #Hso_code
      & #Hso_exp_PCC
      & #Hso_exp_CGP
      & #Hso_exp_awkward
      & #Hentry_SO & #Hot_switcher)".
    iExists g_so_exp_tbl, b_so_exp_tbl, e_so_exp_tbl, (b_so_exp_tbl ^+ 2)%a,
    pc_b, pc_e, cgp_b, cgp_e, 2, _, SON.
    iFrame "#".
    iSplit; first done.
    iSplit; first solve_addr.
    iSplit; first (iPureIntro; solve_addr).
    iSplit; first (iPureIntro; solve_addr).
    iSplit; first (iPureIntro; lia).
    iIntros "!> %W0 %Hpriv_W_W0 !> %cstk %Ws %Cs %rmap %csp_b' %csp_e".
    iIntros "(HK & %Hframe_match & Hregister_state & Hrmap & Hr_C & Hsts_C & %Hsync_csp & Hcstk & Hna)".
    iDestruct "Hregister_state" as
      "(%Hrmap_init & %HPC & %Hcgp & %Hcra & %Hcsp & #Hinterp_W0_csp & Hinterp_rmap & Hzeroed_rmap)".
    rewrite /interp_conf.
    rewrite /registers_pointsto.

    iDestruct (big_sepM_delete _ _ PC with "Hrmap") as "[HPC Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cgp with "Hrmap") as "[Hcgp Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ csp with "Hrmap") as "[Hcsp Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cra with "Hrmap") as "[Hcra Hrmap]"; first by simplify_map_eq.

    iMod (na_inv_acc with "Hso_code Hna")
      as "(( >Himports_main & >Hcode_main) & Hna & Hso_code_close)"; auto.
    codefrag_facts "Hcode_main" ; rename H into Hpc_contiguous; clear H0.

    (* --- Extract registers ca0  --- *)
    assert ( is_Some (rmap !! ct0) ) as [wct0 Hwct0].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ct0 with "Hrmap") as "[Hct0 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! cs0) ) as [wcs0 Hwcs0].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ cs0 with "Hrmap") as "[Hcs0 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! cs1) ) as [wcs1 Hwcs1].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ cs1 with "Hrmap") as "[Hcs1 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ct1) ) as [wct1 Hwct1].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ct1 with "Hrmap") as "[Hct1 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ca0) ) as [wca0 Hwca0].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca0 with "Hrmap") as "[Hca0 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ca1) ) as [wca1 Hwca1].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca1 with "Hrmap") as "[Hca1 Hrmap]"; first by simplify_map_eq.

    (* Extract the imports *)
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_switcher Himports_main]".
    { transitivity (Some (pc_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_assert Himports_main]".
    { transitivity (Some (pc_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_C_f Himports_main]".
    { transitivity (Some (pc_b ^+ 3)%a); auto; solve_addr. }
    { solve_addr. }

    iAssert (interp W0 C wca0) as "#Hinterp_wca0_W0".
    { iApply "Hinterp_rmap"; eauto.
      cbn; set_solver+.
    }

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)

    rewrite /so_main_code /SO_main_code_run.
    rewrite -!app_assoc.
    rewrite /SO_main_code_f.
    assert (SubBounds pc_b pc_e (pc_a ^+ length SO_main_code_run)%a
              (pc_a ^+ length so_main_code)%a).
    { solve_addr. }
    focus_block_nochangePC 3 "Hcode_main" as a_f Ha_f "Hcode" "Hcont"; iHide "Hcont" as hcont.
    replace (pc_b ^+ 23%nat)%a with a_f by solve_addr.

    (* Mov ct1 ca1 *)
    iInstr "Hcode" with "Hlc".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* ----------------------------------------------- *)
    (* ------------- BLOCK 4 : CHECKRA --------------- *)
    (* ----------------------------------------------- *)

    focus_block 4 "Hcode_main" as a_checkra Ha_checkra "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_f.
    iApply (checkra_spec with "[- $HPC $Hca0 $Hcs0 $Hcs1 $Hcode]"); eauto.
    iSplitL; last ( iNext ; iIntros (?); done).
    iNext ; iIntros "H"; iDestruct "H" as (p g b e a) "([%Hp ->] & HPC & Hca0 & Hcs0 & Hcs1 & Hcode)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* ------------------------------------------------------ *)
    (* ------------- BLOCK 5:  CHECK_NO_OVERLAP ------------- *)
    (* ------------------------------------------------------ *)
    focus_block 5 "Hcode_main" as a_check_overlap Ha_check_overlap "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent Ha_checkra.
    iApply (check_no_overlap_spec with "[- $HPC $Hca0 $Hcs0 $Hcs1 $Hcsp $Hcode]"); eauto.
    iSplitL; last ( iNext ; iIntros (?); done).
    iNext ; iIntros "(HPC & Hca0 & Hcsp & Hcs1 & Hcs0 & %Hno_overlap & Hcode)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* ------------------------------------------------------- *)
    (* ----------------- BLOCK 6:  CHECKINTS ----------------- *)
    (* ------------------------------------------------------- *)
    focus_block 6 "Hcode_main" as a_checkints Ha_checkints "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent Ha_check_overlap.

    (* Revoke the world to get the stack frame *)
    set ( csp_b := (csp_b' ^+ 4)%a ).
    set (stk_frame_addrs := finz.seq_between csp_b csp_e).
    iAssert ([∗ list] a ∈ stk_frame_addrs, ⌜W0.1 !! a = Some Temporary⌝)%I as "Hstk_frm_tmp_W0".
    { iApply (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp_W0_csp"); eauto. }

    iMod (monotone_revoke_stack_alt with "[$Hinterp_W0_csp $Hsts_C $Hr_C]")
        as (l
           ) "(%Hl_unk & Hsts_C & Hr_C & #Hfrm_close_W0 & >%Hfrm_close_W0 & >[%stk_mem Hstk] & [Hrevoked_l %Hrevoked_l])".

    set (W1 := revoke W0).
    assert (related_sts_priv_world W0 W1) as
      Hrelated_priv_W0_W1 by eapply revoke_related_sts_priv_world.
    iAssert ( ⌜ Forall (fun a => std W0 !! a = Some Permanent ∨ std W0 !! a = Some Temporary)
                (finz.seq_between b e) ⌝)%I
    as "%Harg_std_states".
    { iDestruct (readAllowed_valid_cap with "Hinterp_wca0_W0" ) as "%Hbe_revoked"; auto.
      iPureIntro.
      clear -Hbe_revoked.
      eapply Forall_impl; eauto; cbn.
      intros a Ha.
      destruct Ha as (ρ & Ha & Hρ).
      destruct ρ; [ right | left |]; done.
    }
    set (wca0_temp := filter (fun a => std W0 !! a = Some Temporary) (finz.seq_between b e)).
    set (wca0_perma := filter (fun a => std W0 !! a = Some Permanent) (finz.seq_between b e)).
    assert ( (finz.seq_between b e) ≡ₚ wca0_perma ++ wca0_temp ) as Hwca0_range.
    { clear - Harg_std_states Harg_std_states.
      subst wca0_perma wca0_temp.
      generalize (finz.seq_between b e), Harg_std_states.
      clear Harg_std_states b e .
      induction l; intros Hl; cbn; first done.
      apply Forall_cons in Hl as [Ha Hl]
      ; apply IHl in Hl
      ; destruct Ha as [Ha | Ha]
      ; [ assert (W0.1 !! a ≠ Some Temporary) as Ha' by (intro ; simplify_map_eq)
        | assert (W0.1 !! a ≠ Some Permanent) as Ha' by (intro ; simplify_map_eq) ]
      ; rewrite (decide_True _ _ Ha); auto; rewrite (decide_False _ _ Ha'); auto
      ; cbn ; [|rewrite -Permutation_middle] ; rewrite -Hl; done.
    }
    set (l' := filter (fun a => a ∉ wca0_temp) l).
    assert (
       wca0_temp ≡ₚ filter (fun a => a ∈ wca0_temp) l
      ) as Hwca0_temp_l.
    {
      clear -Hl_unk Hno_overlap.
      destruct Hl_unk as [Hnodup_l Hl_unk].
      assert (wca0_temp ⊆ l).
      {
        intros a Ha.
        subst wca0_temp.
        apply elem_of_list_filter in Ha as [Ha Ha_be].
        apply (Hl_unk a) in Ha.
        apply elem_of_app in Ha as [Ha|Ha]; first done.
        rewrite elem_of_disjoint in Hno_overlap.
        exfalso; eapply Hno_overlap; eauto.
      }
      apply NoDup_app in Hnodup_l as (Hnodup_l & _ & _).
      assert (NoDup wca0_temp) as Hnodup_wca0_temp.
      { subst wca0_temp. apply NoDup_filter, finz_seq_between_NoDup. }
      (* can the proofs below be a lemma instead? *)
      generalize wca0_temp, H, Hnodup_wca0_temp; intros l' Hl' Hnodup_l'.
      clear -Hl' Hnodup_l Hnodup_l'.
      generalize dependent l'.
      induction l as [|a l]; intros l' Hl' Hnodup_l'.
      + destruct l' ; last set_solver.
        done.
      + cbn.
        apply NoDup_cons in Hnodup_l as [Ha_l Hnodup_l].
        destruct (decide (a ∈ l')) as [Ha_l' | Ha_l'].
        * apply elem_of_Permutation in Ha_l' as [l0 Ha_l'].
          setoid_rewrite Ha_l' in Hnodup_l'.
          apply NoDup_cons in Hnodup_l' as [Ha_l0 Hnodup_l0].
          setoid_rewrite Ha_l' in Hl'.
          setoid_rewrite Ha_l' at 1.
          assert (l0 ⊆ l).
          { clear -Ha_l Hl' Ha_l0.
            intros x Hx.
            assert (x ≠ a) by (intro; simplify_eq; done).
            apply (elem_of_list_further _ a) in Hx.
            apply Hl' in Hx.
            apply elem_of_cons in Hx as [Hx|Hx]; auto.
            done.
          }
          eapply (IHl) in H; eauto.
          apply Permutation_cons; first done.
          rewrite H.
          clear -Hnodup_l Ha_l' Ha_l.
          induction l; cbn; first done.
          apply not_elem_of_cons in Ha_l as [Ha_a0 Ha_l].
          apply NoDup_cons in Hnodup_l as [_ Hnodup_l].
          destruct ( decide (a0 ∈ l0) ) as [Ha0|Ha0].
          ** apply (elem_of_list_further _ a) in Ha0.
             setoid_rewrite <- Ha_l' in Ha0.
             rewrite decide_True; last done.
             rewrite IHl; auto.
          ** rewrite decide_False; first (rewrite IHl; auto).
             intros Ha0'.
             setoid_rewrite Ha_l' in Ha0'.
             apply elem_of_cons in Ha0' as [Ha0'|?]; auto.
        * eapply IHl; auto.
          clear -Hl' Ha_l Ha_l'.
          intros x Hx.
          assert (x ≠ a) by (intro; simplify_eq; done).
          apply Hl' in Hx.
          apply elem_of_cons in Hx as [Hx|Hx]; auto.
          done.
    }
    assert ( l ≡ₚ wca0_temp ∪ l') as Hl_wca0_l'.
    { subst l'.
      rewrite {1}Hwca0_temp_l.
      apply filter_complement_list.
    }
    iAssert (▷ (close_list_resources C W0 l false))%I with "[Hrevoked_l]" as "Hrevoked_l".
    { rewrite /close_list_resources /close_addr_resources.
      iNext; done.
    }
    iDestruct (lc_fupd_elim_later with "[$] [$Hrevoked_l]") as ">Hrevoked_l".
    rewrite /close_list_resources.
    iEval (setoid_rewrite Hl_wca0_l') in "Hrevoked_l".
    iDestruct (big_sepL_app with "Hrevoked_l") as "[Hrevoked_wca0_temp Hrevoked_l']".

    rewrite region_open_nil.
    iDestruct (read_allowed_inv_full_cap with "Hinterp_wca0_W0") as "Hinterp_wca0_invs"; auto.
    iAssert (
        ∃ (wca0_invs : list (finz MemNum * Perm * (WORLD * CmptName * Word → iProp Σ) * region_type)),
          ⌜ (λ '(a, _, _, _), a) <$> wca0_invs = wca0_perma ⌝ ∗
          ⌜ Forall (λ '(a, _, _, ρ), std W0 !! a = Some ρ ∧ ρ = Permanent) wca0_invs ⌝ ∗
          ([∗ list] '(a, p, φ, _) ∈ wca0_invs, rel C a p φ) ∗
          ⌜ Forall (λ '(_, _, φ, _), ∀ Wv : WORLD * CmptName * Word, Persistent (φ Wv)) wca0_invs⌝
      )%I as "(%wca0_invs & %Hwca0_invs_perma & %Hwca0_invs_std_perma & Hrels_wca0 & %Hpers_wca0_invs)".
    {
      iDestruct "Hinterp_wca0_invs" as "-#Hinterp_wca0_invs".
      iClear "#".
      setoid_rewrite Hwca0_range.
      iDestruct (big_sepL_app with "Hinterp_wca0_invs") as "[H _]".
      iDestruct "H" as "#H".
      assert (Forall (λ a : finz MemNum, W0.1 !! a = Some Permanent) wca0_perma) as Hwca0_perma.
      { subst wca0_perma.
        clear.
        induction (finz.seq_between b e); first done.
        cbn.
        destruct ( decide (W0.1 !! a = Some Permanent) ); last done.
        apply Forall_cons; split ;auto.
      }
      generalize wca0_perma, Hwca0_perma.
      clear; intros l Hl.
      iInduction (l) as [|a l] "IH".
      + iExists []; cbn.
        repeat (iSplit; iPureIntro; done).
      + apply Forall_cons in Hl as [Ha Hl].
        cbn.
        iDestruct "H" as "[ (%p'& %P' & %Hpermflow & %HpersP
                              & HrelP & Hzcond & Hrcond & Hwcond & Hmono) H ]".
        iDestruct ("IH" with "[%] [$]") as "(%invs & %Hl_ & %Hperma & #Hrels & %Hpers )"; auto.
        iExists (( (a,p',safeC P'), Permanent)::invs).
        iSplit; first iPureIntro.
        { cbn; by rewrite Hl_. }
        iSplit; first iPureIntro.
        { apply Forall_cons; split; auto. }
        iSplit; first cbn; iFrame "#".
        iPureIntro.
        apply Forall_cons; split; auto.
    }

    iDestruct (region_open_list with "[$Hrels_wca0 $Hr_C $Hsts_C]") as
      "(%wca0_lv_perma & Hr_C & Hsts_C & Hsts_std_wca0 & Hwca0_perma_lv & Hwca0_mono & Hwca0_φs
     & %Hlength_wca0_lv & Hwca0_pO)".
    { rewrite Hwca0_invs_perma.
      subst wca0_perma.
      apply NoDup_filter, finz_seq_between_NoDup.
    }
    { rewrite Hwca0_invs_perma; set_solver+. }
    { rewrite !Forall_forall in Hwca0_invs_std_perma |- *.
      intros [ [ [  ] ] ] Hx; cbn in *; simplify_eq.
      apply Hwca0_invs_std_perma in Hx.
      destruct Hx as [_ ->]; done.
    }
    { cbn in *.
      rewrite !Forall_forall in Hwca0_invs_std_perma |- *.
      intros [ [ [  ] ] ] Hx; cbn in *; simplify_eq.
      apply Hwca0_invs_std_perma in Hx.
      destruct Hx as [Hx ->].
      by apply revoke_lookup_Perm.
    }
    iAssert ( [∗ list] a;v ∈ wca0_perma ; wca0_lv_perma, a ↦ₐ v )%I with "[Hwca0_perma_lv]"
      as "Hwca0_perma_lv".
    { iClear "#". clear -Hwca0_invs_perma.
      iStopProof.
      rewrite -Hwca0_invs_perma big_sepL2_fmap_l.
      generalize dependent wca0_perma; intros l Hl.
      generalize dependent wca0_invs.
      generalize dependent wca0_lv_perma.
      induction l; iIntros (lv linvs Hl) "Hl".
      + apply fmap_nil_inv in Hl; simplify_eq; done.
      + apply fmap_cons_inv in Hl; simplify_eq.
        destruct Hl as ( apφρ & l' & Ha & Hl' & Hl); cbn in *.
        destruct apφρ as [ [ [] ] ]; simplify_eq; cbn.
        iDestruct (big_sepL2_length with "Hl") as "%Hlen"
        ; destruct lv ; simplify_eq.
        cbn.
        iDestruct "Hl" as "[$ Hl]".
        iApply IHl; eauto.
    }
    assert (Forall (λ a : finz MemNum, (revoke W0).1 !! a = Some Revoked) wca0_temp) as
      Hrevoked_wca0_temp.
    { clear - Hl_wca0_l' Hrevoked_l.
      setoid_rewrite Hl_wca0_l' in Hrevoked_l.
      apply Forall_app in Hrevoked_l as [? ?].
      auto.
    }

    iAssert (
        ∃ (lp : list Perm)
          (lφ : list (WORLD * CmptName * Word → iPropI Σ) )
          (lv : list Word),
          ⌜ length lp = length wca0_temp ⌝
          ∗ ⌜ length lφ = length wca0_temp ⌝
          ∗ ⌜ length lv = length wca0_temp ⌝
          ∗ ([∗ list] φ ∈ lφ, ⌜∀ Wv : WORLD * CmptName * Word, Persistent (φ Wv)⌝)
          ∗ ([∗ list] a;pφ ∈ wca0_temp;(zip lp lφ), rel C a pφ.1 pφ.2)
          ∗ ([∗ list] p ∈ lp, ⌜isO p = false⌝)
          ∗ ([∗ list] a;v ∈ wca0_temp;lv, a ↦ₐ v)
          ∗ ([∗ list] lpφ;v ∈ (zip lp lφ);lv,
               (if isWL lpφ.1
                then future_pub_mono C lpφ.2 v
                else (if isDL lpφ.1 then future_pub_mono C lpφ.2 v else future_priv_mono C lpφ.2 v))
            )
          ∗ ([∗ list] φ;v ∈ lφ;lv, φ (W0,C,v)))%I
      with "[Hrevoked_wca0_temp]"
      as (lp lφ wca0_lv_temps)
           "(%Hlen_lp & %Hlen_lφ & %Hlen_lv & Hlφ_pers & #Hlpφ_rels & HlpO & Hwca0_temp_lv & Hlpφ_mono & Hlφ_lv)".
    { iClear "#".
      generalize wca0_temp.
      clear; intros l.
      iInduction (l) as [| a l]; first (iExists [],[],[]; cbn; done).
      iDestruct "Hrevoked_wca0_temp" as "[Ha Hl]".
      iDestruct ("IHl" with "Hl") as "Hl".
      iDestruct "Ha" as (p P HpersP) "[Ha Hrel_a]".
      iDestruct "Ha" as (v) "(HpO & Hv & Hmono & HP)".
      iDestruct "Hl" as (lp lP lv) "(% & % & % & %Hpers_lP & Hrels & HpOs & Hvs & Hmonos & HPs)".
      iExists (p::lp), (P::lP), (v::lv).
      iFrame.
      iFrame "%".
      iPureIntro.
      cbn; lia.
    }
    iDestruct (big_sepL2_app with "Hwca0_perma_lv Hwca0_temp_lv") as "Hwca0_lvs".

    iApply (checkints_spec_alt with "[- $HPC $Hca0 $Hcs1 $Hcs0 $Hwca0_lvs $Hcode]"); eauto.
    { symmetry; auto. }
    iSplitL; last ( iNext ; iIntros (?); done).
    iNext ; iIntros "(HPC & Hca0 & Hcs0 & Hcs1 & Hwca0_lvs & %Hwca0_lvs_ints & Hcode & Hlc)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    iDestruct (big_sepL2_app' with "Hwca0_lvs") as "[Hwca0_perma_lv Hwca0_temp_lv]".
    { by rewrite Hlength_wca0_lv Hwca0_invs_perma. }
    iAssert ( [∗ list] '(a0, _, _, _);v ∈ wca0_invs;wca0_lv_perma, a0 ↦ₐ v )%I with "[Hwca0_perma_lv]"
      as "Hwca0_perma_lv".
    { iClear "#". clear -Hwca0_invs_perma.
      iStopProof.
      rewrite -Hwca0_invs_perma big_sepL2_fmap_l.
      generalize dependent wca0_perma; intros l Hl.
      generalize dependent wca0_invs.
      generalize dependent wca0_lv_perma.
      induction l; iIntros (lv linvs Hl) "Hl".
      + apply fmap_nil_inv in Hl; simplify_eq; done.
      + apply fmap_cons_inv in Hl; simplify_eq.
        destruct Hl as ( apφρ & l' & Ha & Hl' & Hl); cbn in *.
        destruct apφρ as [ [ [] ] ]; simplify_eq; cbn.
        iDestruct (big_sepL2_length with "Hl") as "%Hlen"
        ; destruct lv ; simplify_eq.
        cbn.
        iDestruct "Hl" as "[$ Hl]".
        iApply IHl; eauto.
    }
    iDestruct (region_close_list W1 C wca0_invs [] with
             "[$Hr_C $Hsts_std_wca0 $Hwca0_perma_lv $Hwca0_mono $Hwca0_φs $Hrels_wca0 $Hwca0_pO]"
      ) as "Hr_C".
    { by rewrite Hlength_wca0_lv length_fmap. }
    { rewrite Hwca0_invs_perma. apply NoDup_filter, finz_seq_between_NoDup. }
    { set_solver+. }
    { rewrite !Forall_forall in Hwca0_invs_std_perma |- *.
      intros [ [ [  ] ] ] Hx; cbn in *; simplify_eq.
      apply Hwca0_invs_std_perma in Hx.
      destruct Hx as [_ ->]; done.
    }
    { auto. }
    rewrite -region_open_nil.
    iAssert (▷ [∗ list] φ ∈ lφ, zcond (safeUC φ) C)%I as "#Hzcond_lφ".
    { iClear "∗".
      iDestruct "Hlpφ_rels" as "-#Hrels".
      iDestruct "Hinterp_wca0_invs" as "-#Hinterp".
      iClear "#".
      setoid_rewrite Hwca0_range.
      iDestruct (big_sepL_app with "Hinterp") as "[_ #Hinterp]".
      generalize wca0_temp, Hlen_lp, Hlen_lφ.
      clear.
      intros l Hlen_lp Hlen_lφ.
      iInduction (l) as [|a l] "IH" forall (lp lφ Hlen_lp Hlen_lφ).
      all: destruct lφ; simplify_eq.
      all: destruct lp; simplify_eq.
      + done.
      + cbn.
        iDestruct "Hinterp" as "[(%p' & %P' & _ & _ & Hrel' & Hzcond & _) Hinterp]".
        iDestruct "Hrels" as "[Hrel #Hrels]".
        iDestruct (rel_agree  with "[$Hrel $Hrel']") as "[_ #Heq]".
        iSplitL "Heq"; last iApply "IH"; eauto.
        iNext.
        iIntros (???) "!> H".
        iDestruct ("Heq" $! (W1, C, WInt z)) as "Heq0".
        iDestruct ("Heq" $! (W2, C, WInt z)) as "Heq1".
        cbn.
        (* TODO for some reason, I cant rewrite Heq0 and Heq1... *)
        admit.
    }
    iDestruct "Hlc" as "[Hlc' Hlc]".
    iDestruct (lc_fupd_elim_later with "[$Hlc'] [$Hzcond_lφ]") as ">Hzcond_lφ'".
    iAssert (
        [∗ list] φ;v ∈ lφ;wca0_lv_temps, φ (W1, C, v)
      )%I with "[Hlφ_lv Hzcond_lφ']" as "Hlφ_lv".
    { iClear "#".
      apply Forall_app in Hwca0_lvs_ints as [_ Hl].
      generalize wca0_lv_temps, Hl, Hlen_lv.
      generalize wca0_temp, Hlen_lp, Hlen_lφ.
      clear.
      intros la Hlen_lp Hlen_lφ lv Hl_ints Hlen_lv.
      iInduction (la) as [|a la] "IH" forall (lp lφ lv Hlen_lp Hlen_lφ Hlen_lv Hl_ints).
      all: destruct lφ; simplify_eq.
      all: destruct lp; simplify_eq.
      all: destruct lv; simplify_eq.
      + done.
      + cbn.
        iDestruct "Hlφ_lv" as "[Hb Hlb]".
        iDestruct "Hzcond_lφ'" as "[#Hz Hzl]".
        apply Forall_cons in Hl_ints as [ [z ->] Hl_ints].
        iSplitL "Hb Hz"; last (iApply ("IH" with "[] [] [] [] [$] [$]") ; eauto).
        rewrite /zcond.
        iSpecialize ("Hz" $! W0 W1 z).
        cbn.
        iApply "Hz"; auto.
    }
    iDestruct (big_sepL2_disjoint with "[$Hstk $Hwca0_temp_lv]") as "%".
    iAssert (
        ([∗ list] a ∈ wca0_temp,
           ∃ p φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗ temp_resources W1 C φ a p ∗ rel C a p φ)
      )%I with "[Hlφ_pers HlpO Hlpφ_mono Hwca0_temp_lv Hlφ_lv]" as "Hwca0_temp_closing_resources".
    { iDestruct "Hlpφ_rels" as "-#Hlpφ_rels".
      iClear "#".
      assert (Forall (λ w : Word, ∃ z : Z, w = WInt z) wca0_lv_temps) as Hlvs_temp_int.
      { clear -Hwca0_lvs_ints.
        by apply Forall_app in Hwca0_lvs_ints as [??].
      }
      clear -Hlen_lp Hlen_lφ Hlen_lv.
      generalize dependent wca0_temp; intros l Hlen_lp Hlen_lφ Hlen_lv.
      generalize wca0_lv_temps Hlen_lv; intros lv.
      clear Hlen_lv wca0_lv_temps; intros Hlen_lv.
      iRename "Hwca0_temp_lv" into "Hlv".
      iInduction (l) as [|a l] "IH" forall (lφ lp lv Hlen_lp Hlen_lφ Hlen_lv); first done.
      destruct lv as [|v lv]; cbn in Hlen_lv; simplify_eq.
      destruct lφ as [|φ lφ]; cbn in Hlen_lφ; simplify_eq.
      destruct lp as [|p lp]; cbn in Hlen_lp; simplify_eq.
      cbn in *.
      iDestruct "Hlφ_pers" as "[Hlφ_pers_a Hlφ_pers]".
      iDestruct "HlpO" as "[HlpO_a HlpO]".
      iDestruct "Hlpφ_mono" as "[Hlpφ_mono_a Hlpφ_mono]".
      iDestruct "Hlv" as "[Hlv_a Hlv]".
      iDestruct "Hlφ_lv" as "[Hlφ_lv_a Hlφ_lv]".
      iDestruct "Hlpφ_rels" as "[Hlpφ_rels_a Hlpφ_rels]".
      iFrame.
      iApply ("IH" $! lφ lp lv with "[%] [%] [%] [$] [$] [$] [$] [$] [$]"); eauto.
    }
    iMod (monotone_close_list_region W1 W1 C wca0_temp with
      "[] [$Hsts_C $Hr_C $Hwca0_temp_closing_resources]") as "[Hsts_C Hr_C]".
    { iPureIntro; apply close_list_related_sts_pub. }
    set ( W2 := (close_list wca0_temp W1)).
    iAssert (interp W2 C (WCap p g b e (finz.max b e)))%I as "#Hinterp_wca0_W2".
    {
      iEval (rewrite fixpoint_interp1_eq interp1_eq).
      iEval (rewrite fixpoint_interp1_eq interp1_eq) in "Hinterp_wca0_W0".
      destruct (isO p); first done.
      destruct (has_sreg_access p); first done.
      iDestruct "Hinterp_wca0_W0" as "[ Hinterp $ ]".
      iClear "∗".
      iApply (big_sepL_impl with "Hinterp").
      iModIntro.
      iIntros (k x Hx) "(%px & %Px & %Hpx_flow & %Hpers_Px & Hrelx
                             & Hzcondx & Hrcondx & Hwcondx & Hmonox & %Hstatex)".
      iFrame "∗%".
      apply elem_of_list_lookup_2 in Hx.
      rewrite Forall_forall in Harg_std_states.
      assert (std W0 !! x = std W2 !! x) as Hxeq.
      { destruct (Harg_std_states x Hx) as [Hx' | Hx']; rewrite Hx'; symmetry.
        * rewrite close_list_lookup_not_in.
          { cbn.
            by apply revoke_lookup_Perm.
          }
          intro Hcontra.
          apply elem_of_list_filter in Hcontra as [ hcontra _ ].
          by rewrite hcontra in Hx'.
        * apply close_list_lookup_in; auto; last (apply elem_of_list_filter; split; done).
          cbn; apply revoke_lookup_Monotemp; auto.
      }
      iSplitL "Hmonox".
      + rewrite /monoReq.
        by rewrite Hxeq.
      + iPureIntro.
        destruct (isWL p); rewrite !/region_state_nwl !/region_state_pwl in Hstatex |- *
        ; rewrite -Hxeq; done.
    }


    (* ------------------------------------------------------- *)
    (* ------------------ BLOCK 7: ALLOC_SO ------------------ *)
    (* ------------------------------------------------------- *)
    focus_block 7 "Hcode_main" as a_alloc_so Ha_alloc_so "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent Ha_checkints.

    (* Store csp so_secret; *)
    destruct ( decide ((csp_b < csp_e)%a) ) as [Hcsp_size|Hcsp_size]; cycle 1.
    {
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_z with "[$HPC $Hi $Hcsp]"); try solve_pure.
      { rewrite /withinBounds; solve_addr+Hcsp_size. }
      iIntros "!> _".
      wp_pure; wp_end; iIntros (?); done.
    }
    iDestruct (big_sepL2_length with "Hstk") as %Hstklen.
    rewrite finz_seq_between_length in Hstklen.
    rewrite finz_dist_S in Hstklen; last solve_addr+Hcsp_size.
    destruct stk_mem as [|w0 stk_mem]; simplify_eq.
    assert (is_Some (csp_b + 1)%a) as [a_stk1 Hastk1];[solve_addr+Hcsp_size|].
    iDestruct (region_pointsto_cons with "Hstk") as "[Hastk1 Hstk]"; eauto.
    { solve_addr+Hcsp_size Hastk1. }
    iInstr "Hcode".
    { rewrite /withinBounds; solve_addr+Hcsp_size. }
    (* Lea csp 1; *)
    iInstr "Hcode".
    (* Mov ca1 csp; *)
    iInstr "Hcode".
    (* GetA cs0 ca1; *)
    iInstr "Hcode".
    (* Add cs1 cs0 1; *)
    iInstr "Hcode".
    (* Subseg ca1 cs0 cs1; *)
    destruct ( decide ((a_stk1 < csp_e)%a) ) as [Hcsp_size'|Hcsp_size']; cycle 1.
    {
      destruct (z_to_addr (a_stk1 + 1))%a as [a_stk2|] eqn:Hastk2; cycle 1.
      + iInstr_lookup "Hcode" as "Hi" "Hcode".
        wp_instr.
        iApply (wp_subseg_fail_src2_nonaddr with "[$HPC $Hi $Hca1 $Hcs0 $Hcs1]"); try solve_pure.
        iIntros "!> _".
        wp_pure; wp_end; iIntros (?); done.
      + iInstr_lookup "Hcode" as "Hi" "Hcode".
        wp_instr.
        iApply (wp_subseg_fail_not_iswithin_cap with "[$HPC $Hi $Hca1 $Hcs0 $Hcs1]"); try solve_pure.
        { eauto. }
        {
          assert (csp_e < a_stk2)%a as Hcsp_e_stk2 by solve_addr+Hastk1 Hcsp_size Hcsp_size' Hastk2.
          rewrite /isWithin.
          apply andb_false_iff.
          right.
          solve_addr+Hcsp_e_stk2.
        }
        iIntros "!> _".
        wp_pure; wp_end; iIntros (?); done.
    }
    iDestruct (big_sepL2_length with "Hstk") as %Hstklen'.
    rewrite finz_seq_between_length in Hstklen'.
    rewrite finz_dist_S in Hstklen'; last solve_addr+Hcsp_size'.
    destruct stk_mem as [|w1 stk_mem]; simplify_eq.
    assert (is_Some (a_stk1 + 1)%a) as [a_stk2 Hastk2];[solve_addr+Hcsp_size'|].
    iDestruct (region_pointsto_cons with "Hstk") as "[Hastk2 Hstk]"; eauto.
    { solve_addr+Hcsp_size Hastk1 Hcsp_size' Hastk2. }
    iInstr "Hcode".
    { transitivity (Some (a_stk2)%a); auto.
      solve_addr+Hastk2.
    }
    { solve_addr+Hcsp_size Hastk1 Hcsp_size' Hastk2. }
    (* Store ca1 0; *)
    iInstr "Hcode".
    { solve_addr+Hcsp_size Hastk1 Hcsp_size' Hastk2. }
    (* Lea csp 1; *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ---------------- BLOCK 8 : FETCH ------------------ *)
    (* --------------------------------------------------- *)

    focus_block 8 "Hcode_main" as a_fetch Ha_fetch "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_alloc_so.
    iApply (fetch_spec with "[- $HPC $Hct0 $Hcs0 $Hcs1 $Hcode]"); eauto.
    { apply withinBounds_true_iff; solve_addr. }
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext ; iIntros "(HPC & Hct0 & Hcs0 & Hcs1 & Hcode & Himport_switcher)".
    iEval (cbn) in "Hct0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 9 : CALL ------------------ *)
    (* --------------------------------------------------- *)

    focus_block 9 "Hcode_main" as a_call Ha_call "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_fetch.
    (* Mov cs0 cra *)
    iInstr "Hcode".
    (* Mov cs1 ct1 *)
    iInstr "Hcode".
    (* Jalr cra ct0 *)
    iInstr "Hcode" with "Hl".


    (* and the hard part should be mostly done at that point *)

    (* -- separate argument registers -- *)
    assert ( is_Some (rmap !! ca2) ) as [wca2 Hwca2].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca2 with "Hrmap") as "[Hca2 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ca3) ) as [wca3 Hwca3].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca3 with "Hrmap") as "[Hca3 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ca4) ) as [wca4 Hwca4].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca4 with "Hrmap") as "[Hca4 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ca5) ) as [wca5 Hwca5].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca5 with "Hrmap") as "[Hca5 Hrmap]"; first by simplify_map_eq.

    set ( rmap_arg :=
           {[ ca0 := WCap p g b e (finz.max b e);
              ca1 := WCap RWL Local a_stk1 a_stk2 a_stk1;
              ca2 := wca2;
              ca3 := wca3;
              ca4 := wca4;
              ca5 := wca5;
              ct0 := WSentry XSRW_ Local b_switcher e_switcher a_switcher_call
           ]} : Reg
        ).

    set (rmap' := (delete ca5 _)).

    assert (related_sts_pub_world W1 W2) as Hrelated_pub_W1_W2.
    { apply close_list_related_sts_pub. }

    assert (related_sts_priv_world W0 W2) as Hrelated_priv_W0_W2.
    { eapply related_sts_priv_pub_trans_world; eauto. }
    assert (related_sts_priv_world W W2) as
      Hrelated_priv_W_W2 by (by eapply related_sts_priv_trans_world; eauto).

    (* Show that the arguments are safe, when necessary *)
    iAssert ( ⌜ wca2 = WInt 0 ⌝ )%I as "->".
    { iApply "Hzeroed_rmap"; eauto.
      set_solver+.
    }
    iAssert ( ⌜ wca3 = WInt 0 ⌝ )%I as "->".
    { iApply "Hzeroed_rmap"; eauto.
      set_solver+.
    }
    iAssert ( ⌜ wca4 = WInt 0 ⌝ )%I as "->".
    { iApply "Hzeroed_rmap"; eauto.
      set_solver+.
    }
    iAssert ( ⌜ wca5 = WInt 0 ⌝ )%I as "->".
    { iApply "Hzeroed_rmap"; eauto.
      set_solver+.
    }
    (* TODO: we need to update the world with [a_stk1],
       but we already have rel because we have the interp for the full stack frame
     *)
    iAssert (
        |={⊤}=> ([∗ list] a ∈ [a_stk1],
           ∃ p φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗ temp_resources W2 C φ a p ∗ rel C a p φ)
      )%I with "[Hastk2 Hlc]" as ">Hastk1_closing_resources".
    { cbn.
      iDestruct (read_allowed_inv _ _ a_stk1 with "Hinterp_W0_csp")
        as "(%pastk1 & %Pastk1 &
      %Hpastk1_rwl & %Hpers_Pastk1 & #Hrel_astk1
      & Hzcond_Pastk1 & Hrcond_Pastk1 & Hwcond_Pastk1 & Hmono_Pastk1
      )";auto.
      { solve_addr+Hastk1 Hcsp_size'. }
      replace (writeAllowed pastk1) with true.
      2:{ symmetry; eapply writeAllowed_flowsto; eauto. }
      iDestruct (lc_fupd_elim_later with "[$] [$Hwcond_Pastk1]") as ">#Hwcond_Pastk1'".
      assert (isWL pastk1 = true) as Hpastk1_wl by (apply isWL_flowsto in Hpastk1_rwl;done).
      iModIntro.
      iSplitL; last done.
      iExists pastk1, (safeC Pastk1).
      iSplit; first iPureIntro.
      { intros Wcv; apply Hpers_Pastk1. }
      iSplit; last iFrame "#".
      iFrame "Hastk2".
      iSplit; first iPureIntro.
      { by apply isWL_nonO. }
      rewrite /monoReq !Hpastk1_wl.
      iSplit.
      + replace (W0.1 !! a_stk1) with (Some Temporary); first iApply "Hmono_Pastk1".
        assert (a_stk1 ∈ finz.seq_between csp_b csp_e) as Hastk1_range.
        { rewrite elem_of_finz_seq_between.
          solve_addr+Hastk1 Hcsp_size' Hcsp_size.
        }
        clear -Hl_unk Hastk1_range.
        assert ( a_stk1 ∈ l ++ finz.seq_between csp_b csp_e ) as Ha.
        { apply elem_of_app; right; done. }
        destruct Hl_unk as [_ Hl_unk].
        by specialize (Hl_unk a_stk1); apply Hl_unk in Ha.
      + (* apply Hwcond_Pastk1, but remove the later... *)
        rewrite /safeC /=.
        iApply "Hwcond_Pastk1'".
        iApply interp_int.
    }
    iMod (monotone_close_list_region W2 W2 C [a_stk1] with
      "[] [$Hsts_C $Hr_C $Hastk1_closing_resources]") as "[Hsts_C Hr_C]".
    { iPureIntro; apply close_list_related_sts_pub. }
    set (W3 := close_list _ W2).
    assert (related_sts_pub_world W2 W3) as Hrelated_pub_W2_W3.
    { apply close_list_related_sts_pub. }
    assert (related_sts_priv_world W0 W3) as Hrelated_priv_W0_W3.
    { eapply related_sts_priv_pub_trans_world; eauto. }

    assert (W0.1 !! a_stk1 = Some Temporary) as Ha_stk1_W0.
    { destruct Hl_unk as [_ Hl].
      apply Hl.
      apply elem_of_app; right.
      apply elem_of_finz_seq_between; solve_addr+Hastk1 Hastk2 Hcsp_size Hcsp_size'.
    }
    assert (W3.1 !! a_stk1 = Some Temporary) as Ha_stk1_W3.
    {
      apply close_list_lookup_in; last set_solver+.
      rewrite close_list_lookup_not_in.
      * cbn; apply revoke_lookup_Monotemp; done.
      * subst wca0_temp.
        intro Ha'.
        rewrite elem_of_disjoint in H0; eapply H0; eauto.
        apply elem_of_finz_seq_between; solve_addr+Hastk1 Hastk2 Hcsp_size Hcsp_size'.
    }
    iAssert (interp W3 C (WCap RWL Local a_stk1 a_stk2 a_stk1))%I
      as "#Hinterp_W2_wca1".
    {
      iEval (rewrite fixpoint_interp1_eq interp1_eq).
      cbn.
      iSplit; last done.
      rewrite (finz_seq_between_singleton a_stk1 a_stk2);last solve_addr+Hastk1 Hastk2 Hcsp_size.
      cbn.
      iSplit; last done.
      iClear "∗".
      iDestruct "Hinterp_W0_csp" as "-#Hinterp"; iClear "#".
      iDestruct (read_allowed_inv _ _ a_stk1 with "Hinterp")
        as "(%px & %Px & %Hpx_flow & %HPx_pers & Hrelx & Hzcondx & Hrcondx & Hwcondx & Hmonox)"; auto
      ; first solve_addr+Hastk1 Hastk2 Hcsp_size Hcsp_size'.
      iFrame "∗%".
      apply readAllowed_flowsto in Hpx_flow; last done.
      rewrite Hpx_flow; iFrame.
      rewrite /monoReq.
      rewrite Ha_stk1_W0 Ha_stk1_W3; done.
    }
    iDestruct (interp_monotone with "[] Hinterp_wca0_W2") as "Hinterp_wca0_W3"; eauto.

    iAssert (if is_sealed_with_o wca1 ot_switcher
             then (interp W3 C wca1)
             else True)%I as "#Hinterp_W3_wct1".
    { destruct (is_sealed_with_o wca1 ot_switcher) eqn:His_sealed_wct1; last done.
      destruct wca1 as [| [|] | |]; try discriminate.
      iApply (interp_monotone_sd W0 W3); eauto.
      iApply "Hinterp_rmap"; eauto.
      iPureIntro ; set_solver.
    }

    iAssert ([∗ map] rarg↦warg ∈ rmap_arg , rarg ↦ᵣ warg ∗ interp W3 C warg)%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg.
      iAssert (interp W3 C (WInt 0)) as "Hinterp_0"; first iApply interp_int.
      iAssert (interp W3 C (WSentry XSRW_ Local b_switcher e_switcher a_switcher_call)) as
        "Hinterp_sw_call"; first iApply interp_switcher_call; auto.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done.
    }

    rewrite (finz_seq_between_cons csp_b csp_e); last solve_addr+Hcsp_size.
    iEval (cbn) in "Hfrm_close_W0".
    iDestruct "Hfrm_close_W0" as "[Hfrm_close_W0_a_stk1 Hfrm_close_W0]".
    rewrite (finz_seq_between_cons ((csp_b ^+ 1)%a) csp_e)
    ; last solve_addr+Hcsp_size Hcsp_size' Hastk1.
    iEval (cbn) in "Hfrm_close_W0".
    iDestruct "Hfrm_close_W0" as "[Hfrm_close_W0_a_stk2 Hfrm_close_W0]".
    (* Prepare the closing resources for the switcher call spec *)
    assert (
        Forall (λ k : finz MemNum, W3.1 !! k = Some Revoked) (finz.seq_between a_stk2 csp_e)
      ) as HW3_revoked_callee_frm.
    {
      apply Forall_forall; intros x Hx.
      subst W3 W2 W1.
      rewrite close_list_lookup_not_in.
      2: { intros Hx'; apply elem_of_list_singleton in Hx'; simplify_eq.
           apply elem_of_finz_seq_between in Hx.
           solve_addr+Hx Hastk2 Hcsp_size'.
      }
      rewrite close_list_lookup_not_in.
      2: { intro Hx'.
           apply H0 in Hx'; first done.
           apply elem_of_finz_seq_between in Hx.
           apply elem_of_finz_seq_between.
           solve_addr+Hx Hastk2 Hcsp_size' Hastk1 Hcsp_size.
      }
      apply revoke_lookup_Monotemp.
      clear -Hl_unk Hx Hastk2 Hcsp_size' Hastk1 Hcsp_size.
      destruct Hl_unk as [_ Hl_unk].
      specialize (Hl_unk x) ; apply Hl_unk.
      apply elem_of_app; right.
      apply elem_of_finz_seq_between in Hx.
      apply elem_of_finz_seq_between.
      solve_addr+Hx Hastk2 Hcsp_size' Hastk1 Hcsp_size.
    }
    iAssert (
        ([∗ list] a ∈ finz.seq_between a_stk2 csp_e, closing_revoked_resources W3 C a)
      )%I with "[Hfrm_close_W0]" as "Hfrm_close_W3".
    { replace (((csp_b ^+ 1) ^+ 1)%a)
        with a_stk2%a by solve_addr+Hastk2 Hastk1 Hcsp_size'.
      iApply (big_sepL_impl with "Hfrm_close_W0").
      iModIntro; iIntros (k a' Ha') "Hclose".
      iDestruct (mono_priv_closing_revoked_resources with "Hclose") as "$"; auto.
    }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    iMod ("Hso_code_close" with "[$Hna Himport_assert Himport_switcher Himport_C_f Himports_main $Hcode_main]")
      as "Hna".
    { iNext.
      iDestruct (region_pointsto_cons with "[$Himport_C_f $Himports_main]") as "Himports_main"
      ; [solve_addr|solve_addr|].
      iDestruct (region_pointsto_cons with "[$Himport_assert $Himports_main]") as "Himports_main"
      ; [solve_addr|solve_addr|].
      iDestruct (region_pointsto_cons with "[$Himport_switcher $Himports_main]") as "$" ;solve_addr.
    }

    (* Apply the spec switcher call *)
    iApply (switcher_cc_specification_alt with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hstk $Hr_C $Hsts_C $Hfrm_close_W3 $Hcstk
              $Hinterp_W3_wct1 $HK]"); eauto; iFrame "%".
    { subst rmap'.
      repeat (rewrite dom_delete_L); repeat (rewrite dom_insert_L).
      apply regmap_full_dom in Hrmap_init.
      rewrite /dom_arg_rmap Hrmap_init.
      set_solver+.
    }
    { by rewrite /is_arg_rmap. }

    iClear "Hinterp_rmap Hzeroed_rmap".
    clear dependent wct1 wct0 wcs0 wcs1 rmap stk_mem.
    iNext.
    iIntros (W4 rmap stk_mem l'')
      "( %Hl_unk'' & Hrevoked_l'' & %Hrevoked_l''
      & %Hrelated_pub_2ext_W4 & Hrel_stk_C' & %Hdom_rmap & Hfrm_close_W4 & %Hfrm_close_W4
      & Hna & %Hcsp_bounds
      & Hsts_C & Hr_C
      & Hcstk_frag
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hstk & HK)".
    iEval (cbn) in "HPC".

    assert (related_sts_pub_world W3 W4) as Hrelated_pub_W3_W4.
    {
      eapply related_sts_pub_trans_world ; eauto.
      apply related_sts_pub_update_multiple_temp.
      apply Forall_forall; intros x Hx.
      rewrite Forall_forall in HW3_revoked_callee_frm.
      apply HW3_revoked_callee_frm.
      rewrite !elem_of_finz_seq_between in Hx |- *; solve_addr+Hx.
    }
    set (W5 := revoke W4).

    Set Nested Proofs Allowed.
    Lemma revoked_by_separation_close_addr_resources B W W' a :
      a ∈ dom (std W) →
      region W B
      ∗ sts_full_world W B
      ∗ close_addr_resources B W' a false
      ==∗
      region W B
      ∗ sts_full_world W B
      ∗ close_addr_resources B W' a false
      ∗ ⌜std W !! a = Some Revoked⌝.
    Proof. Admitted.
    Lemma revoked_by_separation_close_list_resources B W' W la :
      Forall (λ a : finz MemNum, a ∈ dom (std W)) la →
      region W B
      ∗ sts_full_world W B
      ∗ close_list_resources B W' la false
      ==∗
      region W B
      ∗ sts_full_world W B
      ∗ close_list_resources B W' la false
      ∗ ⌜Forall (λ a : finz MemNum, std W !! a = Some Revoked) la⌝.
    Proof. Admitted.
    iMod (revoked_by_separation_close_list_resources with "[$Hrevoked_l' $Hr_C $Hsts_C]")
      as "(Hr_C & Hsts_C & Hrevoked_l' & %Hrevoked_l'_W5)".
    { admit. }
    iMod (revoked_by_separation_close_list_resources with "[$Hrevoked_l'' $Hr_C $Hsts_C]")
      as "(Hr_C & Hsts_C & Hrevoked_l'' & %Hrevoked_l''_W5)".
    { admit. }
    iMod (revoked_by_separation_many with "[$Hstk $Hr_C $Hsts_C]")
      as "(Hr_C & Hsts_C & Hstk & %Hstk_W5)".
    { admit. }
    iMod (revoked_by_separation with "[$Hastk1 $Hr_C $Hsts_C]")
      as "(Hr_C & Hsts_C & Hastk1 & %Hastk1_W5)".
    { admit. }

    assert (a_stk1 ∈ l'') as Hastk1_l''.
    { assert (a_stk1 ∉ finz.seq_between (a_stk2 ^+ 4)%a csp_e).
      {
        apply not_elem_of_finz_seq_between.
        solve_addr+Hcsp_bounds Hastk1 Hastk2 Hcsp_size' Hcsp_size.
      }
      clear -Hl_unk'' Hrelated_pub_2ext_W4 H Ha_stk1_W3 H1.
      destruct Hl_unk'' as [_ Hl''].
      assert (std W4 !! a_stk1 = Some Temporary) as Htemp.
      { eapply region_state_pub_temp; eauto.
        rewrite std_sta_update_multiple_lookup_same_i; auto.
      }
      apply Hl'' in Htemp.
      apply elem_of_app in Htemp as [?|?]; done.
    }

    assert (a ∈ l ++ finz.seq_between csp_b csp_e -> std (revoke W4) !! a = Some Revoked) as
    Ha_5.
    { intros Ha.
      apply elem_of_app in Ha as [Ha|Ha]; cycle 1.
      - rewrite finz_seq_between_cons in Ha; last solve_addr+Hcsp_size' Hastk1.
        replace (csp_b ^+1)%a with a_stk1 in Ha by solve_addr+Hcsp_size' Hastk2 Hastk1 Hcsp_bounds.
        rewrite finz_seq_between_cons in Ha; last solve_addr+Hcsp_size' Hastk1 Hcsp_bounds.
        replace (a_stk1 ^+1)%a with a_stk2 in Ha by solve_addr+Hcsp_size' Hastk2 Hastk1 Hcsp_bounds.
        apply elem_of_cons in Ha as [Ha | Ha]; simplify_eq; first auto.
        apply elem_of_cons in Ha as [Ha | Ha]; simplify_eq.
        { rewrite Forall_forall in Hrevoked_l''; apply Hrevoked_l'' in Hastk1_l''; auto. }
        rewrite Forall_forall in Hstk_W5; apply Hstk_W5 in Ha; auto.
      - setoid_rewrite Hl_wca0_l' in Ha.
        apply elem_of_app in Ha as [Ha|Ha]; cycle 1.
        + rewrite Forall_forall in Hrevoked_l'_W5; apply Hrevoked_l'_W5 in Ha; auto.
        + apply revoke_lookup_Monotemp.
          eapply region_state_pub_temp; eauto.
          rewrite close_list_lookup_not_in; auto.
          * rewrite close_list_lookup_in; auto.
            rewrite Forall_forall in Hrevoked_wca0_temp; apply Hrevoked_wca0_temp; auto.
          * intro Ha' ; apply elem_of_list_singleton in Ha'; simplify_eq.
            apply elem_of_list_filter in Ha as [_ Ha].
            rewrite elem_of_disjoint in Hno_overlap; eapply Hno_overlap; eauto.
            apply elem_of_finz_seq_between; subst csp_b; solve_addr+Hastk1 Hcsp_size'.
    }

    (* simplify the knowledge about the new rmap *)
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap Hrmap_zero]".
    iDestruct (big_sepM_pure with "Hrmap_zero") as "%Hrmap_zero".
    assert (∀ r : RegName, r ∈ dom rmap → rmap !! r = Some (WInt 0)) as Hrmap_init.
    { intros r Hr.
      rewrite elem_of_dom in Hr. destruct Hr as [wr Hr].
      pose proof Hr as Hr'.
      eapply map_Forall_lookup in Hr'; eauto.
      by cbn in Hr' ; simplify_eq.
    }
    iClear "Hrmap_zero".

    (* ---- extract the needed registers ct0 ct1 ----  *)
    iExtractList "Hrmap" [ct0;ct1] as ["Hct0"; "Hct1"].

    iMod (na_inv_acc with "Hso_code Hna")
      as "(( >Himports_main & >Hcode_main) & Hna & Hso_code_close)"; auto.
    clear Hpc_contiguous.
    codefrag_facts "Hcode_main" ; rename H into Hpc_contiguous; clear H0.

    (* Extract the imports *)
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_switcher Himports_main]".
    { transitivity (Some (pc_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_assert Himports_main]".
    { transitivity (Some (pc_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }

    focus_block 10 "Hcode_main" as a_assert_prep Ha_assert_prep "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_call.

    (* Lea csp (-2)%Z *)
    iInstr "Hcode".
    { transitivity (Some csp_b); auto.
      solve_addr+Hastk1 Hastk2 Hcsp_size Hcsp_size'.
    }
    (* Load ct0 csp *)
    iInstr "Hcode".
    { split;auto; solve_addr+Hcsp_size. }
    (* Mov ct1 so_secret *)
    iInstr "Hcode".

    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 11: ASSERT ----------------- *)
    (* --------------------------------------------------- *)

    focus_block 11 "Hcode_main" as a_assert_c Ha_assert_c "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_assert_prep.
    iExtractList "Hrmap" [ct2;ct3;ct4] as ["Hct2"; "Hct3";"Hct4"].
    iApply (assert_success_spec
             with
             "[- $Hassert $Hna $HPC $Hct2 $Hct3 $Hct4 $Hct0 $Hct1 $Hcra
              $Hcode $Himport_assert]") ; auto.
    { apply withinBounds_true_iff; solve_addr. }
    { solve_ndisj. }
    iNext; iIntros "(Hna & HPC & Hct2 & Hct3 & Hct4 & Hcra & Hct0 & Hct1
                    & Hcode & Himport_assert)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 12: RETURN ----------------- *)
    (* --------------------------------------------------- *)
    focus_block 12 "Hcode_main" as a_halt Ha_halt "Hcode" "Hcont"; iHide "Hcont" as hcont ; clear dependent Ha_assert_c.
    (* Mov cra cs0; *)
    iInstr "Hcode".
    (* Mov ca0 0%Z; *)
    iInstr "Hcode".
    (* Mov ca1 0%Z; *)
    iInstr "Hcode".
    (* JmpCap cra *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    iMod ("Hso_code_close" with "[$Hna Himport_switcher Himport_assert Himports_main $Hcode_main]")
      as "Hna".
    { iNext.
      iDestruct (region_pointsto_cons with "[$Himport_assert $Himports_main]") as "Himports_main"
      ; [solve_addr|solve_addr|].
      iDestruct (region_pointsto_cons with "[$Himport_switcher $Himports_main]") as "$" ;solve_addr.
    }

    (* Put all the registers under the same map *)
    iInsertList "Hrmap" [ct4;ct3;ct2;ct1;ct0].
    iDestruct (big_sepM_insert _ _ cs0 with "[$Hrmap $Hcs0]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap; set_solver+. }
    iDestruct (big_sepM_insert _ _ cs1 with "[$Hrmap $Hcs1]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap; set_solver+. }
    iDestruct (big_sepM_insert _ _ cgp with "[$Hrmap $Hcgp]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap; set_solver+. }
    iDestruct (big_sepM_insert _ _ cra with "[$Hrmap $Hcra]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap; set_solver+. }

    rewrite -/(close_list_resources C W0 l' false).
    iDestruct (close_list_resources_separation_many_alt with "[$Hrevoked_l' $Hrevoked_l'']") as "%Hdisjoint_l_l''".
    assert (∃ l''0, l'' ≡ₚ a_stk1::l''0 ∧ a_stk1 ∉ l''0) as (l''0 & Hl'' & Ha_stk1_l''0).
    {
      clear -Hastk1_l'' Hl_unk''.
      apply elem_of_Permutation in Hastk1_l''.
      destruct Hastk1_l'' as [l''0 Hl''0].
      exists l''0; split; first done.
      destruct Hl_unk'' as [Hnodup _].
      setoid_rewrite Hl''0 in Hnodup.
      apply NoDup_app in Hnodup; destruct Hnodup as (Hnodup & _ & _).
      apply NoDup_cons in Hnodup; destruct Hnodup as [? _]; done.
    }
    iAssert (
       close_list_resources C W4 l''0 false
       ∗ close_addr_resources C W4 a_stk1 false
      )%I with "[Hrevoked_l'']" as "[Hrevoked_l'' Ha_stk1]".
    { rewrite /close_list_resources.
      setoid_rewrite Hl''.
      iDestruct "Hrevoked_l''" as "[$ $]".
    }
    set (l''0_no_wca0 := filter (fun a => a ∉ wca0_temp) l''0).
    set (l''0_wca0 := filter (fun a => a ∈ wca0_temp) l''0).
    assert (l''0 ≡ₚ l''0_wca0 ∪ l''0_no_wca0) as Hl''0_p.
    { clear.
      subst l''0_wca0 l''0_no_wca0.
      apply filter_complement_list.
    }
    assert ( l ≡ₚ l' ∪ l''0_wca0) as Hl_l''0_wca0.
    { subst l' l''0_wca0 l''0_no_wca0.
      destruct Hl_unk as [Hnodup_l Hl_unk].
      apply NoDup_app in Hnodup_l as (Hnodup_l&?&?).
      destruct Hl_unk'' as [Hnodup_l'' Hl_unk''].
      apply NoDup_app in Hnodup_l'' as (Hnodup_l''&?&?).
      eapply NoDup_Permutation; eauto.
      { apply NoDup_app.
        split;[|split]; try (apply NoDup_filter); auto; cycle 1.
        + apply (NoDup_cons_1_2 a_stk1).
          setoid_rewrite <- Hl''; auto.
        + intros x Hx Hx'.
          apply elem_of_list_filter in Hx as [Hx _].
          apply elem_of_list_filter in Hx' as [Hx' _].
          done.
      }
      intros x; split; intros Hx.
      + apply elem_of_app.
        destruct (decide (x ∈ wca0_temp)) as [Hx_temp|Hx_temp]; [right|left]; cycle 1.
        * apply elem_of_list_filter; split; auto.
        * apply elem_of_list_filter; split; auto.
          assert (std W4 !! x = Some Temporary) as Hx_W4.
          { eapply region_state_pub_temp; eauto.
            destruct (decide (x ∈ [a_stk1])) as [Hx'|Hx'].
            + rewrite elem_of_list_singleton in Hx'; simplify_eq; done.
            + rewrite close_list_lookup_not_in; eauto.
              apply close_list_lookup_in; eauto.
              rewrite Forall_forall in Hrevoked_l; apply Hrevoked_l; auto.
          }
          apply elem_of_list_filter in Hx_temp as [Hx_temp_W0 Hx_temp].
          subst wca0_temp.
          apply Hl_unk'' in Hx_W4.
          apply elem_of_app in Hx_W4 as [Hx_W4|Hx_W4].
          { setoid_rewrite Hl'' in Hx_W4.
            apply elem_of_cons in Hx_W4 as [Hx_W4|Hx_W4]; last done; simplify_eq.
            assert (a_stk1 ∈ finz.seq_between csp_b csp_e)
              by (apply elem_of_finz_seq_between; solve_addr+Hastk1 Hcsp_size').
            exfalso; rewrite elem_of_disjoint in Hno_overlap ; eapply Hno_overlap; eauto.
          }
          { apply elem_of_finz_seq_between in Hx_W4.
            assert (x ∈ finz.seq_between csp_b csp_e)
              by (apply elem_of_finz_seq_between; solve_addr+Hastk1 Hastk2 Hcsp_size' Hx_W4).
            exfalso; rewrite elem_of_disjoint in Hno_overlap ; eapply Hno_overlap; eauto.
          }
      + apply elem_of_app in Hx as [Hx | Hx]
        ; apply elem_of_list_filter in Hx as [Hx Hx']; first done.
        assert (x ∈ finz.seq_between b e)
          as Hx_be by (by apply elem_of_list_filter in Hx as [_ ?]).
        assert ( W0.1 !! x = Some Temporary )
          as Hx_W0 by (by apply elem_of_list_filter in Hx as [? _]).
        apply Hl_unk in Hx_W0.
        apply elem_of_app in Hx_W0 as [Hx_W0|Hx_W0]; auto.
            exfalso; rewrite elem_of_disjoint in Hno_overlap ; eapply Hno_overlap; eauto.
    }
    set (closing_list := ((l++l''0_no_wca0) ++ finz.seq_between csp_b csp_e)).
    assert (related_sts_pub_world W4 (close_list closing_list W5)) as Hrelated_pub_W4_Wfixed.
    { subst W5.
      assert ( l'' ++ finz.seq_between (a_stk2 ^+ 4)%a csp_e ⊆ closing_list ).
      { clear a.
        intros a Ha.
        apply elem_of_app in Ha as [Ha|Ha]; cycle 1.
        { apply elem_of_app; right.
          apply elem_of_finz_seq_between in Ha;
          apply elem_of_finz_seq_between.
          solve_addr+Ha Hcsp_bounds Hastk1 Hastk2.
        }
        setoid_rewrite Hl'' in Ha.
        apply elem_of_cons in Ha as [Ha|Ha]; simplify_eq; cycle 1.
        + apply elem_of_app; left.
          setoid_rewrite Hl_l''0_wca0.
          rewrite -app_assoc.
          setoid_rewrite <- Hl''0_p.
          apply elem_of_app; right.
          done.
        + apply elem_of_app; right.
          rewrite elem_of_finz_seq_between; solve_addr+Hcsp_size' Hastk1.
      }
      destruct W4 as [W4std W4cus]; cbn.
      split; cbn; last apply related_sts_pub_refl.
      split; first (by setoid_rewrite <- close_list_dom_eq; setoid_rewrite <- revoke_dom_eq).
      clear a.
      intros a ρ4 ρ5 Ha_4 Ha_6.
      destruct ρ4.
      - (* Temporary in W4 *)
        assert ( a ∈  l'' ++ finz.seq_between (a_stk2 ^+ 4)%a csp_e ) as Ha_closing.
        { destruct Hl_unk'' as [_ Hl]; apply Hl; auto. }
        rewrite close_list_std_sta_revoked in Ha_6; auto.
        + simplify_eq; apply rtc_refl.
        + by apply revoke_lookup_Monotemp.
      - (* Permanent in W4 *)
        apply revoke_lookup_Perm in Ha_4.
        rewrite -close_list_std_sta_same_alt in Ha_6; [|intro]; simplify_eq.
        apply rtc_refl.
     - (* Revoked in W4 *)
       destruct ρ5; try apply rtc_refl ; apply rtc_once; econstructor.
    }
    iAssert (close_list_resources_gen C W5 closing_list l''0 false) with "[Hrevoked_l'']" as "Hrevoked_l''".
    { iApply close_list_resources_gen_eq; eauto. }
    assert (related_sts_pub_world W0 (close_list closing_list W5)) as Hrelated_pub_W0_Wfixed.
    { subst W5.
      assert ( l ++ finz.seq_between csp_b csp_e ⊆ closing_list ).
      { clear a.
        intros a Ha.
        apply elem_of_app in Ha as [Ha|Ha]; last (by apply elem_of_app; right).
         by do 2 (apply elem_of_app; left).
      }
      destruct W0 as [W0std W0cus]; cbn.
      destruct W4 as [W4std W4cus]; cbn.
      split; cbn; cycle 1.
      { destruct Hrelated_priv_W0_W3 as [_ H_W0_W3].
        destruct Hrelated_pub_W3_W4 as [_ H_W3_W4].
        clear -H_W0_W3 H_W3_W4.
        cbn in *.
        eapply related_sts_pub_trans; eauto.
        apply related_sts_pub_refl.
      }
      split.
      {
        destruct Hrelated_priv_W0_W3 as [ [H_W0_W3 _] _].
        destruct Hrelated_pub_W3_W4 as [ [H_W3_W4 _] _].
        clear -H_W0_W3 H_W3_W4.
        setoid_rewrite <- close_list_dom_eq; setoid_rewrite <- revoke_dom_eq.
        set_solver.
      }
      clear a.
      intros a ρ0 ρ5 Ha_0 Ha_6.
      destruct ρ0.
      - (* Temporary in W0 *)
        assert ( a ∈  l ++ finz.seq_between csp_b csp_e ) as Ha_closing.
        { destruct Hl_unk as [_ Hl]; apply Hl; auto. }
        assert (std W1 !! a = Some Revoked)
          as Ha_1 by (by apply revoke_lookup_Monotemp).
        assert ( a ∈ l ++ finz.seq_between csp_b csp_e -> revoke_std_sta W4std !! a = Some Revoked ) as Ha_5.
        (* iAssert (⌜ a ∈ l ++ finz.seq_between csp_b csp_e -> std W4 !! a = Some Revoked ⌝). *)
        (* Revoked in W3, we need to know that they are still revoked in W4,
             from the separation during the proof *)
        { admit. }
        specialize (Ha_5 Ha_closing).
        apply H in Ha_closing.
        rewrite close_list_std_sta_revoked in Ha_6; auto.
        simplify_eq; apply rtc_refl.
        (* assert (std W3 !! a = Some Revoked ∨ std W3 !! a = Some Temporary) as [Ha_3|Ha_3]. *)
        (* { subst W3 W2. *)
        (*   destruct ( decide (a ∈ wca0_temp) ) as [Ha_temp | Ha_temp] *)
        (*   ; destruct ( decide (a = a_stk1) ) as [-> | Ha_astk1]. *)
        (*   + right. *)
        (*     rewrite close_list_lookup_Temporary; eauto. *)
        (*     apply close_list_lookup_in; eauto. *)
        (*   + right. *)
        (*     rewrite close_list_lookup_Temporary; eauto. *)
        (*     apply close_list_lookup_in; eauto. *)
        (*   + right. *)
        (*     apply close_list_lookup_in; eauto; last set_solver+. *)
        (*     rewrite close_list_lookup_not_in; eauto. *)
        (*   + left. *)
        (*     rewrite close_list_lookup_not_in; eauto; last (set_solver+Ha_astk1). *)
        (*     rewrite close_list_lookup_not_in; eauto. *)
        (* } *)
        (* + *)
      (* Revoked in W3, we need to know that they are still revoked in W4,
             from the separation during the proof *)
        (* + eapply region_state_pub_temp in Ha_3; eauto. *)
        (*   eapply region_state_pub_temp in Ha_3; eauto. *)
        (*   rewrite Ha_3 in Ha_6; simplify_eq. *)
        (*   apply rtc_refl. *)
      - (* Permanent in W0 *)
        assert (std W3 !! a = Some Permanent) as Ha_3.
        { eapply region_state_priv_perm; eauto. }
        assert (std (W4std, W4cus) !! a = Some Permanent) as Ha_4.
        { eapply region_state_priv_perm; eauto.
          by apply related_sts_pub_priv_world.
        }
        apply revoke_lookup_Perm in Ha_4.
        rewrite -close_list_std_sta_same_alt in Ha_6; [|intro Hcontra]; cbn; simplify_eq.
        + rewrite Ha_4 in Ha_6; simplify_eq; apply rtc_refl.
        + rewrite Ha_4 in Hcontra; done.
      - (* Revoked in W0 *)
        destruct ρ5; try apply rtc_refl ; apply rtc_once; econstructor.
    }
    iAssert (close_list_resources_gen C W5 closing_list l' false) with "[Hrevoked_l']" as "Hrevoked_l'".
    { iApply close_list_resources_gen_eq; eauto. }

    iAssert (
       close_list_resources_gen C W5 closing_list l''0_no_wca0 false
       ∗ close_list_resources_gen C W5 closing_list l''0_wca0 false
      )%I with "[Hrevoked_l'']" as "[Hrevoked_l''_no_wca0 Hrevoked_l''_wca0]".
    { rewrite /close_list_resources_gen.
      setoid_rewrite Hl''0_p.
      iDestruct (big_sepL_app with "Hrevoked_l''") as "[$ $]".
    }
    iDestruct (close_list_resources_gen_separation with "[$Hastk1] [$Hrevoked_l''_wca0]") as "%Hcsp_b_notin_l''0_no_wca0".
    iDestruct (close_addr_list_gen_resources_separation with "[$Ha_stk1] [$Hrevoked_l''_wca0]") as "%Hastk_1_notin_l''0_no_wca0".
    iDestruct (close_list_resources_gen_separation_many
                 with "[$Hstk] [$Hrevoked_l''_wca0]") as "%Hfrm_notin_l''0_no_wca0".
    iAssert (close_list_resources_gen C W5 closing_list l false)
      with "[Hrevoked_l' Hrevoked_l''_wca0]" as "Hrevoked_l'".
    { rewrite /close_list_resources_gen.
      setoid_rewrite Hl_l''0_wca0.
      iApply big_sepL_app; iFrame.
    }
    iAssert (close_list_resources_gen C W5 closing_list (l++l''0_no_wca0) false)
      with "[Hrevoked_l' Hrevoked_l''_no_wca0]" as "Hrevoked".
    { rewrite /close_list_resources_gen; iApply big_sepL_app; iFrame. }


    rewrite /close_addr_resources.
    iDestruct "Ha_stk1" as (???) "[Ha_stk1 _]".
    iEval (cbn) in "Ha_stk1".
    iDestruct "Ha_stk1" as (?) "(_ & Ha_stk1 & _)".
    iDestruct (region_pointsto_cons with "[$Ha_stk1 $Hstk]") as "Hstk"; auto.
    { solve_addr+Hcsp_size' Hastk2. }
    iDestruct (region_pointsto_cons with "[$Hastk1 $Hstk]") as "Hstk"; auto.
    { solve_addr+Hcsp_size Hastk1. }

    iApply (switcher_ret_specification_gen _ W0 W5
             with
             "[ $Hswitcher $Hstk $Hcstk_frag $HK $Hsts_C $Hna $HPC $Hr_C
             $Hrmap $Hca0 $Hca1 $Hcsp $Hrevoked]"
           ); eauto.
    { repeat (rewrite dom_insert_L); rewrite Hdom_rmap; set_solver+. }
    { subst csp_b.
      clear -Hsync_csp.
      destruct Hsync_csp as [].
      rewrite -H0; auto.
    }
    {
      apply NoDup_app.
      split;[|split]; cycle -1.
      - apply finz_seq_between_NoDup.
      - setoid_rewrite Hl_l''0_wca0.
        subst l'.
        rewrite /union /disjoint_regions_tactics.Union_list.
        apply NoDup_app.
        split;[|split]; cycle -1.
        + subst l''0_no_wca0.
          apply NoDup_filter.
          clear -Hl_unk'' Hl''.
          destruct Hl_unk'' as [Hnodup _].
          apply NoDup_app in Hnodup as (Hnodup&_&_).
          setoid_rewrite Hl'' in Hnodup.
          apply NoDup_cons in Hnodup as [_ Hnodup].
          done.
        + apply NoDup_app.
          split;[|split]; cycle -1.
          * subst l''0_wca0.
            apply NoDup_filter.
            clear -Hl_unk'' Hl''.
            destruct Hl_unk'' as [Hnodup _].
            apply NoDup_app in Hnodup as (Hnodup&_&_).
            setoid_rewrite Hl'' in Hnodup.
            apply NoDup_cons in Hnodup as [_ Hnodup].
            done.
          * apply NoDup_filter.
            clear -Hl_unk.
            destruct Hl_unk as [Hnodup _].
            apply NoDup_app in Hnodup as (Hnodup&_&_).
            done.
          * cbn; intros x Hx.
            clear -Hx.
            apply elem_of_list_filter in Hx as [Hx _].
            subst l''0_wca0.
            intros Hx'.
            apply elem_of_list_filter in Hx' as [Hx' _].
            done.
        + cbn; intros x Hx.
          intros Hx'.
          subst l''0_no_wca0.
          apply elem_of_list_filter in Hx' as [Hx_no_wca0_temp Hx'].
          apply elem_of_app in Hx as [Hx|Hx].
          * apply elem_of_list_filter in Hx as [_ Hx].
            apply (elem_of_list_further _ a_stk1) in Hx'.
            setoid_rewrite <- Hl'' in Hx'.
            setoid_rewrite Hl_wca0_l' in Hx.
            clear -Hx Hx_no_wca0_temp Hx' Hdisjoint_l_l''.
            rewrite elem_of_disjoint in Hdisjoint_l_l''.
            apply elem_of_app in Hx as [Hx|Hx]; first done.
            apply (Hdisjoint_l_l'' x); eauto.
          * subst l''0_wca0.
            apply elem_of_list_filter in Hx as [Hx _].
            done.
      - cbn; intros x Hx.
        apply elem_of_app in Hx as [Hx|Hx].
        + clear -Hx Hl_unk.
          destruct Hl_unk as [Hnodup _].
          apply NoDup_app in Hnodup as (_&Hnodup&_).
          by apply Hnodup.
        + rewrite finz_seq_between_cons; last solve_addr+Hcsp_bounds Hastk1 Hastk2.
          apply not_elem_of_cons; split.
          { intros ->; done. }
          replace (csp_b ^+ 1)%a with a_stk1; last solve_addr+Hcsp_bounds Hastk1 Hastk2.
          rewrite finz_seq_between_cons; last solve_addr+Hcsp_bounds Hastk1 Hastk2.
          apply not_elem_of_cons; split.
          { intros ->; done. }
          replace (a_stk1 ^+ 1)%a with a_stk2; last solve_addr+Hcsp_bounds Hastk1 Hastk2.
          intro Hx'.
          rewrite elem_of_disjoint in Hfrm_notin_l''0_no_wca0.
          eapply Hfrm_notin_l''0_no_wca0; eauto.
    }
    { intros x Hx.
      destruct Hl_unk as [_ Hl_unk].
      specialize (Hl_unk x); apply Hl_unk in Hx.
      apply elem_of_app in Hx as [Hx | Hx].
      + apply elem_of_app; left.
        apply elem_of_app; left; done.
      + apply elem_of_app; right; done.
    }
    { iSplit; iApply interp_int. }
  Qed.

  Lemma vae_awkward_safe

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)

    (b_vae_exp_tbl e_vae_exp_tbl : Addr)

    (b_assert e_assert : Addr) (a_flag : Addr)
    (C_f : Sealable)

    (W : WORLD)

    (Nassert Nswitcher Nvae VAEN : namespace)
    i

    :

    let imports :=
     vae_main_imports
       b_switcher e_switcher a_switcher_call ot_switcher b_assert e_assert C_f
    in

    Nswitcher ## Nassert ->
    Nswitcher ## Nvae ->
    Nassert ## Nvae ->
    (b_vae_exp_tbl <= b_vae_exp_tbl ^+ 2 < e_vae_exp_tbl)%a ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (vae_main_code ot_switcher))%a ->
    (pc_b + length imports)%a = Some pc_a ->
    (cgp_b + length vae_main_data)%a = Some cgp_e ->
    (exists b : bool, loc W !! i = Some (encode b)) ->
    wrel W !! i =
    Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->

    na_inv logrel_nais Nassert (assert_inv b_assert e_assert a_flag)
    ∗ na_inv logrel_nais Nswitcher switcher_inv
    ∗ na_inv logrel_nais Nvae
        ([[ pc_b , pc_a ]] ↦ₐ [[ imports ]] ∗ codefrag pc_a (vae_main_code ot_switcher))
    ∗ inv (export_table_PCCN VAEN) (b_vae_exp_tbl ↦ₐ WCap RX Global pc_b pc_e pc_b)
    ∗ inv (export_table_CGPN VAEN) ((b_vae_exp_tbl ^+ 1)%a ↦ₐ WCap RW Global cgp_b cgp_e cgp_b)
    ∗ inv (export_table_entryN VAEN (b_vae_exp_tbl ^+ 2)%a)
        ((b_vae_exp_tbl ^+ 2)%a ↦ₐ WInt (encode_entry_point 1 (length (imports ++ VAE_main_code_init))))
    ∗ WSealed ot_switcher (SCap RO Global b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a)
        ↦□ₑ 1
    ∗ WSealed ot_switcher (SCap RO Local b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a)
        ↦□ₑ 1
    ∗ seal_pred ot_switcher ot_switcher_propC
    ∗ (∃ ι, inv ι (awk_inv C i cgp_b))
    ∗ sts_rel_loc (A:=Addr) C i awk_rel_pub awk_rel_priv
      -∗
    interp W C
      (WSealed ot_switcher (SCap RO Global b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a)).
  Proof.
    intros imports; subst imports.
    iIntros (Hswitcher_assert HNswitcher_vae HNassert_vae
               Hvae_exp_tbl_size Hvae_size_code Hvae_imports Hcgp_size Hloc_i_W Hrel_i_W)
      "(#Hassert & #Hswitcher
      & #Hvae_code
      & #Hvae_exp_PCC
      & #Hvae_exp_CGP
      & #Hvae_exp_awkward
      & #Hentry_VAE & #Hentry_VAE' & #Hot_switcher
      & [%ι #Hι] & #Hsts_rel)".
    iEval (rewrite fixpoint_interp1_eq /=).
    rewrite /interp_sb.
    iFrame "Hot_switcher".
    iSplit; [iPureIntro; apply persistent_cond_ot_switcher |].
    iSplit; [iIntros (w); iApply mono_priv_ot_switcher|].
    iSplit; iNext ; iApply vae_awkward_spec; try iFrame "#"; eauto.
  Qed.


End VAE.
