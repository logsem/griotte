From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel fundamental interp_weakening addr_reg_sample rules proofmode.
From cap_machine Require Import multiple_updates region_invariants_revocation region_invariants_allocation.
From cap_machine Require Import switcher.


Definition tstk_addrR := excl_authR (leibnizO Addr).
Definition tstk_addrUR := excl_authUR (leibnizO Addr).

Class TSTK_ADDR_preG Σ :=
  { tstk_addr_preG :: inG Σ tstk_addrUR; }.

Class TSTK_ADDRG Σ :=
  { tstk_addr_inG :: inG Σ tstk_addrUR;
    γtstk_addr : gname;
  }.

Definition TSTK_ADDR_preΣ :=
  #[ GFunctor tstk_addrUR ].

Instance subG_TSTK_ADDR_preΣ {Σ} :
  subG TSTK_ADDR_preΣ Σ → TSTK_ADDR_preG Σ.
Proof. solve_inG. Qed.

Section TStack.
  Context {Σ : gFunctors} {tstk_addrg : TSTK_ADDRG Σ} .

  Definition tstk_addr_full (a : Addr) : iProp Σ
    := own γtstk_addr (@excl_auth_auth (leibnizO Addr) a).

  Definition tstk_addr_frag (a : Addr) : iProp Σ
    := own γtstk_addr (@excl_auth_frag (leibnizO Addr) a).

  Lemma tstk_addr_agree (a a' : Addr) :
   tstk_addr_full a -∗
   tstk_addr_frag a' -∗
   ⌜ a = a' ⌝.
  Proof.
    iIntros "Hfull Hfrag".
    rewrite /tstk_addr_full /tstk_addr_frag.
    iCombine "Hfull Hfrag" as "H".
    iDestruct (own_valid with "H") as "%H".
    by apply excl_auth_agree_L in H.
  Qed.

  Lemma tstk_addr_update (a a' a'' : Addr) :
   tstk_addr_full a -∗
   tstk_addr_frag a' ==∗
   tstk_addr_full a'' ∗ tstk_addr_frag a''.
  Proof.
    iIntros "Hfull Hfrag".
    rewrite /tstk_addr_full /tstk_addr_frag.
    iCombine "Hfull Hfrag" as "H".
    iMod ( own_update _ _ _  with "H" ) as "H".
    { apply excl_auth_update. }
    iDestruct "H" as "[? ?]".
    by iFrame.
  Qed.

End TStack.

Section Switcher.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {tstk_addrg : TSTK_ADDRG Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Definition ot_switcher_prop : (WORLD * CmptName * Word) → iPropI Σ :=
    (fun (WCw : (WORLD * CmptName * Word) ) =>
       let W := WCw.1.1 in
       let C := WCw.1.2 in
       let w := WCw.2 in
         ∃ (b_tbl e_tbl a_tbl : Addr),
        ⌜ w = WCap RO Global b_tbl e_tbl a_tbl ⌝
        ∗ ⌜ (b_tbl <= a_tbl < e_tbl)%a ⌝
        ∗ ⌜ (b_tbl < (b_tbl ^+1))%a ⌝
        ∗ ⌜ ((b_tbl ^+1) < a_tbl)%a ⌝
        ∗ interp W C w
        ∗ rel C b_tbl RO (fun WCv => ∃ bpcc epcc apcc, ⌜ WCv.2 = WCap RX Global bpcc epcc apcc ⌝ ∗ interp W C WCv.2 )
        ∗ rel C (b_tbl ^+ 1)%a RO (fun WCv => ∃ bcgp ecgp, ⌜ WCv.2 = WCap RX Global bcgp ecgp bcgp ⌝ ∗ interp W C WCv.2 )
        ∗ rel C a_tbl RO (fun WCv => ∃ (nargs off : Z), ⌜ WCv.2 = WInt (encode_entry_point nargs off) ⌝ ∗ ⌜ (0 <= nargs <= 7 )%Z ⌝)
    )%I.

  Definition switcher_inv
    (b_switcher e_switcher a_switcher_cc b_tstk e_tstk : Addr)
    (ot_switcher : OType) : iProp Σ :=
    ∃ (a_tstk : Addr) (tstk_next : list Word),
     mtdc ↦ₛᵣ WCap RWL Local b_tstk e_tstk a_tstk
     ∗ ⌜ SubBounds
         b_switcher e_switcher
         a_switcher_cc (a_switcher_cc ^+ length switcher_instrs)%a ⌝
     ∗ codefrag a_switcher_cc switcher_instrs
     ∗ b_switcher ↦ₐ WSealRange (true,true) Global ot_switcher (ot_switcher^+1)%ot ot_switcher
     ∗ [[ (a_tstk ^+1)%a, e_tstk ]] ↦ₐ [[ tstk_next ]]
     ∗ tstk_addr_full a_tstk
     ∗ seal_pred ot_switcher ot_switcher_prop
  .

   Definition frame_inv (C : CmptName) (i : positive) (P : iProp Σ) (a : Addr) :=
     (∃ x:bool, sts_state_loc C i x ∗ if x then P ∗ tstk_addr_frag a else emp)%I.

   Definition frame_rel_pub := λ (a b : bool), False.
   Definition frame_rel_priv := λ (a b : bool), True.
   Definition frame_W (W : WORLD) : WORLD :=
     let ι := fresh_cus_name W in
      <l[ ι := true , ( frame_rel_pub, (frame_rel_pub, frame_rel_priv)) ]l> W.

   Lemma frame_W_related_sts_pub_world (W : WORLD) : related_sts_pub_world W (frame_W W).
   Proof.
     rewrite /frame_W.
     destruct W as [Wstd [fs fr] ].
     assert (fresh (dom fs ∪ dom fr) ∉ (dom fs ∪ dom fr)) as Hfresh by apply is_fresh.
     apply related_sts_pub_world_fresh_loc; set_solver.
   Qed.

   Lemma revoked_by_separation
     (W : WORLD) (C : CmptName)
     (a : Addr) (w : Word) (ρ : region_type) :
     std W !! a = Some ρ →
     region W C
     ∗ sts_full_world W C
     ∗ a ↦ₐ w
     ==∗
     region W C
     ∗ sts_full_world W C
     ∗ a ↦ₐ w
     ∗ ⌜ ρ = Revoked ⌝
   .
   Proof.
     iIntros (Hstd_a) "(Hregion & Hworld & Ha)".
     rewrite region_eq /region_def.
     iDestruct "Hregion" as (M Mρ) "(HM & %Hdom & %Hdom' & Hr)".
     rewrite /region_map_def.
     assert (is_Some (M !! a)) as [ [γ p] Hγp].
     { apply elem_of_dom. rewrite /std in Hstd_a,Hdom'.
       rewrite -Hdom. rewrite elem_of_dom; eauto.
     }
     iMod (reg_get with "[$HM]") as "[HM Hrel]";[eauto|].
     iDestruct (big_sepM_delete _ _ a with "Hr") as "[Hstate Hr]";[eauto|].
     iDestruct "Hstate" as (ρ' Ha) "[Hρ Hstate]".
     iDestruct (sts_full_state_std with "Hworld Hρ") as %Hx''; simplify_eq.
     rewrite Hx'' in Hstd_a ; simplify_eq.
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
       rewrite elem_of_dom in Ha.
       destruct Ha as [ρ Ha].
       iMod (revoked_by_separation with "[$Hregion $Hworld $Ha]")
         as "(Hregion & Hworld & Ha & %Hforall_a)"; eauto; simplify_eq.
       rewrite Forall_cons_iff.
       iFrame; done.
   Qed.

   Lemma revoked_by_revoked_resources
     (W W' : WORLD) (C : CmptName) (la : list Addr) :
     Forall (λ a : finz MemNum, a ∈ dom (std W)) la ->
     region W C
     ∗ sts_full_world W C
     ∗ ([∗ list] a ∈ la,
          (∃ (p : Perm) (φ : WORLD * CmptName * Word → iPropI Σ),
              ⌜∀ Wv : WORLD * CmptName * Word, Persistent (φ Wv)⌝
                                               ∗ temp_resources W' C φ a p ∗ rel C a p φ)
          ∗ ⌜std (revoke W') !! a = Some Revoked⌝)
     ==∗
     region W C
     ∗ sts_full_world W C
     ∗ ([∗ list] a ∈ la,
          (∃ (p : Perm) (φ : WORLD * CmptName * Word → iPropI Σ),
              ⌜∀ Wv : WORLD * CmptName * Word, Persistent (φ Wv)⌝
                                               ∗ temp_resources W' C φ a p ∗ rel C a p φ)
          ∗ ⌜std (revoke W') !! a = Some Revoked⌝)
     ∗ ⌜ Forall (λ a, std W !! a = Some Revoked) la⌝.
   Proof.
     iIntros (Hla) "(Hregion & Hworld & Hla)".
     rewrite big_sepL_sep.
     iDestruct "Hla" as "[Hla Hla']"; iFrame "Hla'".
     rewrite region_addrs_exists.
     iDestruct "Hla" as (ps) "Hla".
     rewrite region_addrs_exists2.
     iDestruct "Hla" as (φs) "[%Hlen_φs Hla]".
     rewrite big_sepL2_sep.
     iDestruct "Hla" as "[Hla_φ Hla]".
     rewrite big_sepL2_sep.
     iDestruct "Hla" as "[Hla Hla_rel]".
     rewrite /temp_resources.
     rewrite region_addrs_exists2.
     iDestruct "Hla" as (lw) "[%Hlen_lw Hla]".
     rewrite big_sepL2_sep.
     iDestruct "Hla" as "[Hla_isO Hla]".
     rewrite big_sepL2_sep.
     iDestruct "Hla" as "[Hla Hla_rest]".
     iAssert (  [∗ list] y1;y2 ∈ la;lw, y1 ↦ₐ y2 )%I with "[Hla]" as "Hla".
     { admit. (* NOTE iris manipulations *) }
     iMod (revoked_by_separation_many with "[$Hregion $Hworld $Hla]")
       as "(Hregion & Hworld & Hla & %Hrevoked)"; eauto.
     iFrame "∗%".
     iModIntro.
     iExists ps.
     rewrite region_addrs_exists2.
     iExists φs; iFrame "%".
     iEval (rewrite big_sepL2_sep); iFrame.
     iEval (rewrite big_sepL2_sep); iFrame.
     rewrite region_addrs_exists2.
     iExists lw; iFrame "%".
     iEval (rewrite big_sepL2_sep); iFrame.
     iEval (rewrite big_sepL2_sep); iFrame.
     admit. (* NOTE iris manipulations *)
   Admitted.

   Set Nested Proofs Allowed.
   Lemma region_close_many_revoked W C als als' p φ  `{forall Wv, Persistent (φ Wv)} :
     NoDup als ->
     NoDup als' ->
     als' ⊆ als ->
     ([∗ list] a ∈ als',rel C a p φ ∗ sts_state_std C a Revoked)
     -∗ open_region_many W C als
        -∗ open_region_many W C (list_difference als als').
   Proof.
     revert als'.
     induction als; intros als' ; iIntros (HNoDup_als HNoDup_als' Hals') "Hres Hregion".
     - by apply list_nil_subseteq in Hals'; rewrite Hals'.
     - rewrite NoDup_cons in HNoDup_als; destruct HNoDup_als as [Ha_notin HNoDup_als].
       iEval (cbn) in "Hres".
       destruct (decide_rel elem_of a als') as [Ha_in|Ha_in]; cycle 1.
   Admitted.


   Lemma region_close_revoked_many W C als p φ  `{forall Wv, Persistent (φ Wv)}:
     NoDup als ->
     ⊢ ([∗ list] a ∈ als, rel C a p φ ∗ sts_state_std C a Revoked)
     ∗ open_region_many W C als
       -∗ region W C.
   Proof.
     iIntros (HnoDup) "(Hstd & Hregion)".
     iApply region_open_nil.
     replace [] with (list_difference als als) by (by apply list_difference_same).
     iApply (region_close_many_revoked with "[Hstd] [$Hregion]"); eauto.
   Qed.


  Lemma monotone_revoke_keep_some_open_many W C (ltemp_unknown ltemp_known ltemp_opened : list Addr) (p : Perm) φ:
    NoDup (ltemp_unknown ++ ltemp_known ++ ltemp_opened ) →
    (* unknown Temporary *)
    ([∗ list] a ∈ ltemp_unknown, ⌜(std W) !! a = Some Temporary⌝)
    (* known Temporary *)
    ∗ ([∗ list] a ∈ ltemp_known, ⌜(std W) !! a = Some Temporary⌝ ∗ rel C a p φ)
    (* opened Temporary *)
    ∗ ([∗ list] a ∈ ltemp_opened, ⌜(std W) !! a = Some Temporary⌝ ∗ rel C a p φ ∗ sts_state_std C a Temporary)

    ∗ sts_full_world W C
    ∗ open_region_many W C ltemp_opened

    ==∗

    sts_full_world (revoke W) C
    ∗ open_region_many (revoke W) C ltemp_opened

    (* unknown Revoked *)
    ∗ ([∗ list] a ∈ ltemp_unknown,
         (∃ p' φ', ⌜forall Wv, Persistent (φ' Wv)⌝
                               ∗ ▷ temp_resources W C φ' a p'
                               ∗ rel C a p' φ')
         ∗ ⌜(std (revoke W)) !! a = Some Revoked⌝)
    (* known Revoked *)
    ∗ ([∗ list] a ∈ ltemp_known,
         (▷ temp_resources W C φ a p ∗ rel C a p φ)
         ∗ ⌜(std (revoke W)) !! a = Some Revoked⌝)
    (* opened Revoked *)
    ∗ ([∗ list] a ∈ ltemp_opened,
         (rel C a p φ ∗ sts_state_std C a Revoked )
         ∗ ⌜(std (revoke W)) !! a = Some Revoked⌝).
  Admitted.

  Lemma update_region_revoked_temp_pwl_multiple E W C la lv p φ `{∀ Wv, Persistent (φ Wv)} :
    isO p = false → isWL p = true →

    sts_full_world W C -∗
    region W C -∗
    ([∗ list] a;v ∈ la;lv ,
       a ↦ₐ v
       ∗ φ (W,C,v)
       ∗ rel C a p φ
       ∗ future_pub_mono C φ v
       ∗ ⌜(std W) !! a = Some Revoked ⌝
    )

    ={E}=∗

    region (std_update_multiple W la Temporary) C
    ∗ sts_full_world (std_update_multiple W la Temporary) C.
  Proof.
  Admitted.


  Lemma frame_W_lookup_std (W : WORLD) (a : Addr) :
    std (frame_W W) !! a = (std W) !!a.
  Proof.
    rewrite /frame_W.
    by cbn.
  Qed.

  Lemma frame_W_lookup_loc1 (W : WORLD) (ι : positive) :
    ι ≠ fresh_cus_name W ->
    loc1 (frame_W W) !! ι = (loc1 W) !! ι.
  Proof.
    intros Hι.
    rewrite /frame_W /loc1 /=.
    rewrite lookup_insert_ne //.
  Qed.
  Lemma frame_W_lookup_loc2 (W : WORLD) (ι : positive) :
    ι ≠ fresh_cus_name W ->
    loc2 (frame_W W) !! ι = (loc2 W) !! ι.
  Proof.
    intros Hι.
    rewrite /frame_W /loc2 /=.
    rewrite lookup_insert_ne //.
  Qed.

  Lemma ι0_in_Wloc_helper (W0 : WORLD) (ι0 : positive) (callee_stk_frm_addr : list Addr) :
    ι0 ∈ (dom (loc1 (std_update_multiple
                       (<l[ι0:=false]l>(revoke W0))
                       callee_stk_frm_addr Temporary))).
  Proof.
    rewrite /loc1 /loc std_update_multiple_loc_sta dom_insert_L; set_solver.
  Qed.

  Lemma ι0_isnot_fresh (W0 : WORLD) (ι0 : positive) (callee_stk_frm_addr : list Addr) :
    ι0 ≠ fresh_cus_name (std_update_multiple
                           (<l[ι0:=false]l>(revoke W0))
                           callee_stk_frm_addr Temporary).
  Proof.
    apply fresh_name_notin. left.
    apply ι0_in_Wloc_helper.
  Qed.

  Lemma helper_switcher_final_pub
    (W0 W2 : WORLD) (ltemp_unknown a_local_args : list Addr) (ι0 : positive)
    (a_stk e_stk : Addr) :
    let callee_stk_frm_addr :=
      finz.seq_between (a_stk ^+ 4)%a e_stk
    in
    let W1 :=
      std_update_multiple
        (frame_W
           (std_update_multiple (<l[ι0:=encode false]l>(revoke W0))
              (finz.seq_between (a_stk ^+ 4)%a e_stk) Temporary)) a_local_args Temporary : WORLD
    in
    let ι :=
      fresh_cus_name
        (std_update_multiple (<l[ι0:=false]l>(revoke W0)) callee_stk_frm_addr Temporary)
    in

    (a_stk ^+ 4 < e_stk)%a ->

    NoDup (ltemp_unknown ++ finz.seq_between a_stk e_stk) ->
    (* we know that it's true, by separation! *)
    a_local_args ## ltemp_unknown ->
    (∀ a : Addr,
       std W0 !! a = Some Temporary ↔ a ∈ ltemp_unknown ++ finz.seq_between a_stk e_stk) ->
    loc1 W0 !! ι0 = Some (encode true) ->
    loc1 W2 !! ι0 = Some (encode false) ->
    loc2 W0 !! ι0 =
    Some (convert_rel frame_rel_pub, convert_rel frame_rel_pub, convert_rel frame_rel_priv) ->
    loc2 W2 !! ι0 =
    Some (convert_rel frame_rel_pub, convert_rel frame_rel_pub, convert_rel frame_rel_priv) ->
    ι0 ≠ ι ->
    related_sts_pub_world W1 W2 ->
    loc1 W2 !! ι = Some (encode true) ->
    loc2 W2 !! ι =
    Some (convert_rel frame_rel_pub, convert_rel frame_rel_pub, convert_rel frame_rel_priv) ->

    Forall (λ a : Addr, std W2 !! a = Some Temporary)
      (finz.seq_between (a_stk ^+ 4)%a e_stk) ->
    Forall (λ a : Addr, std W2 !! a = Some Temporary) a_local_args ->
    (* we know that it's true, by separation! *)
    Forall (λ a : Addr , std W2 !! a = Some Revoked ) ltemp_unknown ->
    (* requirement on a_local_args *)
    Forall (λ a : Addr,  a ∉ dom (std W0)) a_local_args ->

    related_sts_pub_world W0
      (close_list ltemp_unknown
         (std_update_multiple (<l[ι:=false]l>(<l[ι0:=true]l>(revoke W2)))
            (finz.seq_between a_stk e_stk) Temporary)).
  Proof.
    intros callee_stk_frm_addr W1 ι
      Haestk HNoDup Hdis_locals_unkw W_temps
      Hι0_loc_W0 Hι0_loc_W2 Hι0_rel_W1 Hι0_rel_W2 Hι0_ι Hrelated_W1_W2
      Hι_loc_W2 Hι_rel_W2 Hcallee_frame_W2_temporary Hlocal_args_W2_temporary
      Hunknown_W2_revoked Hlocal_notin_W0.
    destruct W0 as [Wstd0 [ Wloc0 Wrel0 ] ]; cbn in *.
    destruct W2 as [Wstd2 [ Wloc2 Wrel2 ] ]; cbn in *.
    split ; cycle 1; cbn.

    (* --- CUSTOM WORLD ---*)
    - (* Show that the custom world is a public transition*)
      rewrite std_update_multiple_loc_sta std_update_multiple_loc_rel /=.
      split; [|split].
      + assert (dom Wloc0 ⊆ dom (loc1 W1)) as Hdom_loc_W0_W1.
        { subst W1.
          rewrite /loc1 std_update_multiple_loc_sta dom_insert_L.
          rewrite std_update_multiple_loc_sta dom_insert_L.
          set_solver.
        }
        assert (dom (loc1 W1) ⊆ dom (<[ι:=encode false]> (<[ι0:=encode true]> Wloc2)))
          as Hdom_loc_W0_WF.
        { rewrite 2!dom_insert_L.
          destruct Hrelated_W1_W2 as [? [? ?] ] ; cbn in *.
          set_solver.
        }
        set_solver.
      + assert (dom Wrel0 ⊆ dom (loc2 W1)) as Hdom_rel_W0_W1.
        { subst W1.
          rewrite /loc2 std_update_multiple_loc_rel dom_insert_L.
          rewrite std_update_multiple_loc_rel.
          set_solver.
        }
        assert (dom (loc2 W1) ⊆ dom Wrel2) as Hdom_rel_W0_WF.
        { destruct Hrelated_W1_W2 as [? [? [? ?] ] ] ; cbn in *.
          set_solver.
        }
        set_solver.
      + intros ι' r1 r2 r1' r2' r3 r3' HWrel0_ι' HWrel2_ι'.
        assert (ι' ≠ ι) as Hι_ι'.
        { apply fresh_name_notin.
          right.
          rewrite /loc2 std_update_multiple_loc_rel.
          destruct (decide (ι' = ι0)); simplify_map_eq; by rewrite elem_of_dom.
        }
        assert ((loc2 W1) !! ι' = Some (r1, r2, r3)) as HWrel1_ι'.
        { subst W1.
          rewrite /loc2 std_update_multiple_loc_rel.
          rewrite lookup_insert_ne //.
          rewrite std_update_multiple_loc_rel.
          destruct (decide (ι' = ι0)); simplify_map_eq; done.
        }
        destruct Hrelated_W1_W2 as [_ [_ [_ Hrelated_rel_W1_W2] ] ] ; cbn in *.
        specialize (Hrelated_rel_W1_W2 _ _ _ _ _ _ _ HWrel1_ι' HWrel2_ι').
        destruct Hrelated_rel_W1_W2 as (-> & -> & -> & Hrtc).
        repeat (split ; first done).

        intros b0 b2 Hloc0_ι' Hloc2_ι'.
        destruct (decide (ι' = ι0)); simplify_eq.
        * (* case ι' = ι0 *)
          rewrite lookup_insert_ne // lookup_insert in Hloc2_ι'; simplify_eq.
          apply rtc_refl.
        *(* case ι' ≠ ι0 *)
          assert ((loc1 W1) !! ι' = Some b0) as HWloc1_ι'.
          { subst W1.
            rewrite /loc1 std_update_multiple_loc_sta.
            rewrite lookup_insert_ne //.
            rewrite std_update_multiple_loc_sta.
            destruct (decide (ι' = ι0)); simplify_map_eq; try done.
          }
          do 2 (rewrite lookup_insert_ne // in Hloc2_ι').
          by apply Hrtc.

    (* --- STANDARD WORLD ---*)
    - assert ( dom Wstd0 ⊆ dom (std W1) ) as Hdom_std_W0_W1.
      { subst W1.
        etransitivity ; last apply std_update_multiple_sta_dom_subseteq.
        cbn.
        etransitivity ; last apply std_update_multiple_sta_dom_subseteq.
        cbn.
        by rewrite -revoke_dom_eq.
      }
      split.
      + (* monotonic domains *)
        rewrite -close_list_dom_eq.
        etransitivity; last apply std_update_multiple_sta_dom_subseteq.
        cbn.
        rewrite -revoke_dom_eq.
        destruct Hrelated_W1_W2 as [ [? _] _] ; cbn in *.
        set_solver.
      + (* each address has public transition*)
        clear Hι0_loc_W0 Hι0_loc_W2 Hι0_rel_W1 Hι0_rel_W2 Hι0_ι Hι_loc_W2 Hι_rel_W2.
        intros a ρ0 ρF Hstd0_a HstdF_a.

        assert (is_Some (std W1 !! a)) as [ρ1 Hstd1_a].
        {
          rewrite -elem_of_dom.
          apply Hdom_std_W0_W1.
          by rewrite elem_of_dom.
        }
        assert (is_Some (Wstd2 !! a)) as [ρ2 Hstd2_a].
        {
          destruct Hrelated_W1_W2 as [ [Hdom _] _] ; cbn in *.
          rewrite -elem_of_dom.
          apply Hdom.
          by rewrite elem_of_dom.
        }

        destruct (decide (a ∈ ltemp_unknown)) as [Ha_temps_unknown | Ha_temps_unknown].
        { rewrite close_list_std_sta_revoked in HstdF_a; eauto.
          + simplify_eq.
            specialize (W_temps a).
            destruct W_temps as [_ W_temps].
            ospecialize (W_temps _); first set_solver.
            rewrite Hstd0_a in W_temps; simplify_eq.
            by apply rtc_refl.
          + rewrite std_sta_update_multiple_lookup_same_i; cycle 1.
            { apply NoDup_app in HNoDup ; destruct HNoDup as [_  [HNoDup _] ].
              by apply HNoDup.
            }
            assert ( (std W1) !! a = Some Revoked) as Hstd1'_a.
            {
              subst W1.
              rewrite std_sta_update_multiple_lookup_same_i; cycle 1.
              { eapply elem_of_disjoint in Ha_temps_unknown; eauto. }
              cbn.
              rewrite std_sta_update_multiple_lookup_same_i; cycle 1.
              { apply NoDup_app in HNoDup ; destruct HNoDup as [_  [HNoDup _] ].
                apply HNoDup in Ha_temps_unknown.
                rewrite (finz_seq_between_split  a_stk (a_stk ^+ 4)%a)
                  in Ha_temps_unknown ; last by solve_addr.
                apply not_elem_of_app in Ha_temps_unknown; naive_solver.
              }
              cbn.
              apply revoke_lookup_Monotemp.
              apply W_temps. apply elem_of_app; naive_solver.
            }
            apply revoke_lookup_Revoked; cbn.
            apply elem_of_list_lookup_1 in Ha_temps_unknown.
            destruct Ha_temps_unknown as [? ?].
            eapply Forall_lookup_1 in Hunknown_W2_revoked; eauto.
        }

        rewrite -close_list_std_sta_same in HstdF_a; last done.
        destruct (decide (a ∈ (finz.seq_between a_stk e_stk))) as [Ha_stk | Ha_stk].
        { rewrite std_sta_update_multiple_lookup_in_i in HstdF_a; simplify_eq; auto.
          assert ( a ∈ ltemp_unknown ++ finz.seq_between a_stk e_stk) as Ha_stk'.
          { apply elem_of_app; naive_solver. }
          apply W_temps in Ha_stk'.
          rewrite Hstd0_a in Ha_stk'; simplify_eq.
          apply rtc_refl.
        }

        rewrite std_sta_update_multiple_lookup_same_i in HstdF_a; last done.
        cbn in HstdF_a.
        assert (a ∉ a_local_args) as Ha_local.
        { intro Hcontra.
          apply elem_of_list_lookup_1 in Hcontra.
          destruct Hcontra as [k Hcontra].
          eapply Forall_lookup_1 in Hlocal_notin_W0; eauto.
          rewrite not_elem_of_dom in Hlocal_notin_W0.
          rewrite Hlocal_notin_W0 in Hstd0_a ; simplify_eq.
        }

        destruct ρ0.
        * (* Case ρ0 = Temporary --- not possible *)
          apply W_temps in Hstd0_a.
          apply elem_of_app in Hstd0_a.
          destruct Hstd0_a ; done.
        * (* Case ρ0 = Permanent --- ρF Permanent *)
          destruct Hrelated_W1_W2 as [ [_ Hrelated] _] ; cbn in *.
          specialize (Hrelated _ _ _ Hstd1_a Hstd2_a).
          subst W1.
          rewrite std_sta_update_multiple_lookup_same_i in Hstd1_a; last done.
          cbn in Hstd1_a.
          rewrite std_sta_update_multiple_lookup_same_i in Hstd1_a.
          2: {
            rewrite (finz_seq_between_split  a_stk (a_stk ^+ 4)%a)
            in Ha_stk ; last by solve_addr.
            apply not_elem_of_app in Ha_stk; naive_solver.
          }
          cbn in Hstd1_a.
          rewrite revoke_lookup_Perm in Hstd1_a ; eauto; simplify_eq.
          eapply std_rel_pub_rtc_Permanent in Hrelated; eauto; simplify_eq.
          rewrite revoke_lookup_Perm in HstdF_a ; eauto; simplify_eq.
          apply rtc_refl.
        * (* Case ρ0 = Revoked --- ρF Revoked *)
          destruct Hrelated_W1_W2 as [ [_ Hrelated] _] ; cbn in *.
          specialize (Hrelated _ _ _ Hstd1_a Hstd2_a).
          subst W1.
          rewrite std_sta_update_multiple_lookup_same_i in Hstd1_a; last done.
          cbn in Hstd1_a.
          rewrite std_sta_update_multiple_lookup_same_i in Hstd1_a.
          2: {
            rewrite (finz_seq_between_split  a_stk (a_stk ^+ 4)%a)
            in Ha_stk ; last by solve_addr.
            apply not_elem_of_app in Ha_stk; naive_solver.
          }
          cbn in Hstd1_a.
          rewrite revoke_lookup_Revoked in Hstd1_a ; eauto; simplify_eq.
          eapply std_rel_pub_rtc_Revoked in Hrelated; eauto; simplify_eq.
          destruct Hrelated as [ -> | [  -> | -> ] ].
          ** rewrite revoke_lookup_Perm in HstdF_a ; eauto; simplify_eq.
             apply rtc_once; constructor.
          ** rewrite revoke_lookup_Monotemp in HstdF_a ; eauto; simplify_eq.
             apply rtc_refl.
          ** rewrite revoke_lookup_Revoked in HstdF_a ; eauto; simplify_eq.
             apply rtc_refl.
  Qed.

  Lemma switcher_ret_specification
    (Nswitcher Nframes : namespace)
    (W0 : WORLD)
    (C : CmptName)
    (b_switcher e_switcher a_switcher_cc : Addr)
    (b_stk e_stk a_stk : Addr)
    (ot_switcher : OType)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : Word)
    (stk_mem : list Word)
    (arg_rmap rmap : Reg)
    (ltemp_unknown : list Addr)
    ( b_tstk a_tstk e_tstk a_jmp : Addr )
    (tstk_a1 : Word)
    (ι0 : positive) (Pframe0 : iProp Σ)
    (a_local_args : list Addr)
    (φ : val -> iPropI Σ) :

    let stk_caller_save_area :=
      [wcs0_caller;wcs1_caller;wcra_caller;wcgp_caller]
    in
    let callee_stk_frm_addr :=
      finz.seq_between (a_stk ^+ 4)%a e_stk
    in

    let W1 :=
      std_update_multiple
        (frame_W
           (std_update_multiple (<l[ι0:=encode false]l>(revoke W0))
              (finz.seq_between (a_stk ^+ 4)%a e_stk) Temporary)) a_local_args Temporary
    in

    let Hφ : iPropI Σ :=
      ((∃ W2 (rmap' : Reg), ⌜related_sts_pub_world W0 W2⌝ ∗
        ⌜dom rmap' = all_registers_s ∖ {[PC; cgp; cra; csp; ca0; ca1]}⌝ ∗
        na_own logrel_nais ⊤ ∗ sts_full_world W2 C ∗
        open_region_many W2 C (finz.seq_between a_stk e_stk) ∗
        ([∗ list] a ∈ finz.seq_between a_stk e_stk, rel C a RWL interpC) ∗
        PC ↦ᵣ updatePcPerm wcra_caller ∗ cgp ↦ᵣ wcgp_caller ∗ cra ↦ᵣ wcra_caller ∗
        csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk ∗
        (∃ warg0 : Word, ca0 ↦ᵣ warg0) ∗
        (∃ warg1 : Word, ca1 ↦ᵣ warg1) ∗
        ([∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜w = WInt 0⌝) ∗
        ([∗ list] a ∈ a_local_args, ∃ w : Word, a ↦ₐ w) ∗
        [[a_stk,e_stk]]↦ₐ[[region_addrs_zeroes a_stk e_stk]]) -∗
     WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I
    in
    let htemp_unknown :=
     ([∗ list] x ∈ ltemp_unknown, (∃ (x0 : Perm) (x1 : WORLD * CmptName * Word → iPropI Σ),
                                    ⌜∀ Wv : WORLD * CmptName * Word, Persistent (x1 Wv)⌝ ∗ temp_resources W0 C x1 x x0 ∗
                                    rel C x x0 x1) ∗ ⌜std (revoke W0) !! x = Some Revoked⌝)%I
    in
    let Pframe :=
     (Hφ ∗ Pframe0 ∗ (a_tstk ^+ 1)%a ↦ₐ WCap RWL Local b_stk e_stk (a_stk ^+ 4)%a ∗
     [[a_stk,(a_stk ^+ 4)%a]]↦ₐ[[stk_caller_save_area]] ∗ htemp_unknown)%I
    in
    let ι := fresh_cus_name (std_update_multiple (<l[ι0:=false]l>(revoke W0)) callee_stk_frm_addr Temporary)
    in

    Nswitcher ## Nframes ->
    (a_switcher_cc + 79%nat)%a = Some a_jmp ->
    (a_stk ^+ 4 < e_stk)%a ->
    (b_stk <= a_stk)%a ->
    (a_tstk ^+ 2 < e_tstk)%a ->
    (b_tstk <= a_tstk)%a  ->
    NoDup (ltemp_unknown ++ finz.seq_between a_stk e_stk) ->
    NoDup (finz.seq_between (a_stk ^+ 4)%a e_stk ++ a_local_args) ->
    (∀ a : finz MemNum, std W0 !! a = Some Temporary ↔ a ∈ ltemp_unknown ++ finz.seq_between a_stk e_stk) ->
    (loc1 W0) !! ι0 = Some (encode true) ->
    loc2 W0 !! ι0 =
    Some (convert_rel frame_rel_pub, convert_rel frame_rel_pub, convert_rel frame_rel_priv) ->
    Forall (λ a : finz MemNum, a ∉ dom (std W0)) a_local_args ->
    a_local_args ## ltemp_unknown ->

    ( na_inv logrel_nais Nswitcher (switcher_inv b_switcher e_switcher a_switcher_cc b_tstk e_tstk ot_switcher )
      ∗ na_inv logrel_nais (Nframes.@ι0) (frame_inv C ι0 Pframe0 a_tstk)
      ∗ ([∗ list] y ∈ finz.seq_between a_stk (a_stk ^+ 4)%a, rel C y RWL interpC)
      ∗ ([∗ list] y ∈ finz.seq_between (a_stk ^+ 4)%a e_stk, rel C y RWL interpC)
      ∗ ([∗ list] x ∈ finz.seq_between a_stk e_stk, ⌜std (revoke W0) !! x = Some Revoked⌝)
      ∗ sts_rel_loc C ι frame_rel_pub frame_rel_pub frame_rel_priv
      ∗ na_inv logrel_nais (Nframes.@ι) (frame_inv C ι Pframe (a_tstk ^+ 1)%a)
      -∗ interp W1 C (WSentry XSRW_ Local b_switcher e_switcher (a_jmp ^+ 1)%a)
    ).
  Proof.
    intros stk_caller_save_area callee_stk_frm_addr W1 Hφ htemp_unknown Pframe ι
      HN Ha_jmp Hstk_ae Hstk_ba Htstk_ae Htstk_ba HNoDup_temps HNoDup_local W_temps
      Hι0_loc Hι0_sts Ha_args_locals Hdis_locals_unk.
    iIntros "#(Hinv_switcher & #Hinv_frame0 & Hrel_reg_saved & Hrel_callee_frm
    & Htemp_opened_revoked & Hsts_rel_ι & #Hinv_frame)".

    assert (ι0 ≠ ι) as Hι0_neq_ι by apply ι0_isnot_fresh.
    iEval (rewrite fixpoint_interp1_eq //=).
    iModIntro; iIntros (rmap' W2 Hrelated_W1_W2).
    iAssert (interp_expr interp rmap' W2 C
               (WCap XSRW_ Local b_switcher e_switcher (a_jmp ^+ 1)%a))
              as "Hinterp_expr" ; last iFrame "Hinterp_expr".

    iIntros "([%Hfull_rmap #Hinterp_rmap] & Hrmap & Hregion & Hworld & Hna)".
    rewrite /interp_conf /registers_pointsto.
    iDestruct (big_sepM_delete _ _ PC with "Hrmap") as "[HPC Hrmap]"; first by rewrite lookup_insert.
    rewrite delete_insert_delete.

    (* extract register points-to *)
    assert (exists wcra, rmap' !! cra = Some wcra)
      as [wcra Hwcra] by (by specialize (Hfull_rmap cra)).
    iDestruct (big_sepM_delete _ _ cra with "Hrmap") as "[Hcra Hrmap]"; first by simplify_map_eq.
    assert (exists wcsp, rmap' !! csp = Some wcsp)
      as [wcsp Hwcsp] by (by specialize (Hfull_rmap csp)).
    iDestruct (big_sepM_delete _ _ csp with "Hrmap") as "[Hcsp Hrmap]"; first by simplify_map_eq.
    assert (exists wcgp, rmap' !! cgp = Some wcgp)
      as [wcgp Hwcgp] by (by specialize (Hfull_rmap cgp)).
    iDestruct (big_sepM_delete _ _ cgp with "Hrmap") as "[Hcgp Hrmap]"; first by simplify_map_eq.
    assert (exists wca0, rmap' !! ca0 = Some wca0)
      as [wca0 Hwca0] by (by specialize (Hfull_rmap ca0)).
    iDestruct (big_sepM_delete _ _ ca0 with "Hrmap") as "[Hca0 Hrmap]"; first by simplify_map_eq.
    assert (exists wca1, rmap' !! ca1 = Some wca1)
      as [wca1 Hwca1] by (by specialize (Hfull_rmap ca1)).
    iDestruct (big_sepM_delete _ _ ca1 with "Hrmap") as "[Hca1 Hrmap]"; first by simplify_map_eq.
    assert (exists wctp, rmap' !! ctp = Some wctp)
      as [wctp Hwctp] by (by specialize (Hfull_rmap ctp)).
    iDestruct (big_sepM_delete _ _ ctp with "Hrmap") as "[Hctp Hrmap]"; first by simplify_map_eq.
    assert (exists wca2, rmap' !! ca2 = Some wca2)
      as [wca2 Hwca2] by (by specialize (Hfull_rmap ca2)).
    iDestruct (big_sepM_delete _ _ ca2 with "Hrmap") as "[Hca2 Hrmap]"; first by simplify_map_eq.
    assert (exists wcs1, rmap' !! cs1 = Some wcs1)
      as [wcs1 Hwcs1] by (by specialize (Hfull_rmap cs1)).
    iDestruct (big_sepM_delete _ _ cs1 with "Hrmap") as "[Hcs1 Hrmap]"; first by simplify_map_eq.
    assert (exists wcs0, rmap' !! cs0 = Some wcs0)
      as [wcs0 Hwcs0] by (by specialize (Hfull_rmap cs0)).
    iDestruct (big_sepM_delete _ _ cs0 with "Hrmap") as "[Hcs0 Hrmap]"; first by simplify_map_eq.
    assert (exists wct0, rmap' !! ct0 = Some wct0)
      as [wct0 Hwct0] by (by specialize (Hfull_rmap ct0)).
    iDestruct (big_sepM_delete _ _ ct0 with "Hrmap") as "[Hct0 Hrmap]"; first by simplify_map_eq.
    assert (exists wct1, rmap' !! ct1 = Some wct1)
      as [wct1 Hwct1] by (by specialize (Hfull_rmap ct1)).
    iDestruct (big_sepM_delete _ _ ct1 with "Hrmap") as "[Hct1 Hrmap]"; first by simplify_map_eq.

    (* open frame invariant *)
    iMod (na_inv_acc with "Hinv_frame Hna")
      as "(Hframe & Hna & Hclose_frame_inv)" ; auto.
    iEval (rewrite /frame_inv) in "Hframe".
    iDestruct "Hframe" as (ι_state) "[Hι_loc Hframe]".

    (* open frame0 invariant *)
    iMod (na_inv_acc with "Hinv_frame0 Hna")
      as "(Hframe0 & Hna & Hclose_frame0_inv)" ; auto.
    { solve_ndisj. }
    iEval (rewrite /frame_inv) in "Hframe0".
    iDestruct "Hframe0" as (ι0_state) "[Hι0_loc _]".

    (* open switcher invariant *)
    iMod (na_inv_acc with "Hinv_switcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    { solve_ndisj. }
    rewrite /switcher_inv.
    iDestruct "Hswitcher_inv"
      as (a_tstk' tstk_next')
           "(>Hmtdc & >%Hbounds & >Hcode & >Hb_switcher & >Htstk & Htstk_addr_full & #Hp_ot_switcher)".
    codefrag_facts "Hcode".
    rename H into Hcont_switcher_region; clear H0.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hinv_switcher" as hinv_switcher.

    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.
    focus_block_nochangePC 5 "Hcode" as a5 Ha5 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    assert (a5 = a_jmp) by solve_addr ; simplify_eq.


    (* ReadSR ctp mtdc *)
    iInstr "Hcode".
    { done. }

    (* TODO extract as lemma about frame_W *)
    iDestruct (sts_full_state_loc with "[$] [$Hι_loc]") as "%Hι_state".
    iDestruct (sts_full_rel_loc with "[$] [$Hsts_rel_ι]") as "%Hι_rel".
    assert (ι_state = true) as ->.
    {
      assert (W1.2.1 !! ι = Some (encode true))
        by (by rewrite /W1 std_update_multiple_loc_sta /frame_W /ι lookup_insert).
      assert (W1.2.2 !! ι = Some ( convert_rel frame_rel_pub, convert_rel frame_rel_pub, convert_rel frame_rel_priv))
        by (by rewrite /W1 std_update_multiple_loc_rel /frame_W /ι lookup_insert).
      assert (related_sts_pub_world W1 W2) as Hrelated by done.

      destruct Hrelated as [ _ [_ [_ Hrelated ] ] ].
      specialize (Hrelated ι _ _ _ _ _ _ H2 Hι_rel).
      destruct Hrelated as (_ & _ & _ & Hrelated).
      specialize (Hrelated _ _ H1 Hι_state).
      rewrite /convert_rel /frame_rel_pub /= in Hrelated.
      apply rtc_inv in Hrelated.
      destruct Hrelated.
      + by inv H3.
      + destruct H3 as (? & (? & ? & Hcontra) & _).
        naive_solver.
    }
    iDestruct (sts_full_state_loc with "[$] [$Hι0_loc]") as "%Hι0_state".
    assert (ι0_state = false) as ->.
    {
      assert (W1.2.1 !! ι0 = Some (encode false)).
      { rewrite /W1 std_update_multiple_loc_sta frame_W_lookup_loc1 //.
        by rewrite /loc1 std_update_multiple_loc_sta lookup_insert.
      }
      assert (W1.2.2 !! ι0 = Some (convert_rel frame_rel_pub, convert_rel frame_rel_pub, convert_rel frame_rel_priv)).
      { rewrite /W1 std_update_multiple_loc_rel frame_W_lookup_loc2 //.
        rewrite /loc2 std_update_multiple_loc_rel //=.
      }
      assert (
          W2.2.2 !! ι0 =
          Some (convert_rel frame_rel_pub, convert_rel frame_rel_pub, convert_rel frame_rel_priv)
        ) as Hι0_rel by (by eapply related_sts_pub_rel).

      destruct Hrelated_W1_W2 as [ _ [_ [_ Hrelated_W1_W2 ] ] ].
      specialize (Hrelated_W1_W2 ι0 _ _ _ _ _ _ H2 Hι0_rel).
      destruct Hrelated_W1_W2 as (_ & _ & _ & Hrelated_W1_W2).
      specialize (Hrelated_W1_W2 _ _ H1 Hι0_state).
      rewrite /convert_rel /frame_rel_pub /= in Hrelated_W1_W2.
      apply rtc_inv in Hrelated_W1_W2.
      destruct Hrelated_W1_W2.
      + by inv H3.
      + destruct H3 as (? & (? & ? & Hcontra) & _).
        naive_solver.
    }

    iDestruct "Hframe" as "(Hframe & Htstk_addr_frag)".
    iDestruct "Hframe" as "(Hφ & HPframe0 & tstk & Hsaved_register_area & Htemp_unknown)".
    iDestruct (tstk_addr_agree with "[$] [$]") as "->".
    rewrite /stk_caller_save_area.
    iDestruct (region_pointsto_cons with "Hsaved_register_area") as "[Ha0_stk Hsaved_register_area]".
    { transitivity (Some (a_stk ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Hsaved_register_area") as "[Ha1_stk Hsaved_register_area]".
    { transitivity (Some (a_stk ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Hsaved_register_area") as "[Ha2_stk Hsaved_register_area]".
    { transitivity (Some (a_stk ^+ 3)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Hsaved_register_area") as "[Ha3_stk _]".
    { transitivity (Some (a_stk ^+ 4)%a); auto; solve_addr. }
    { solve_addr. }


    (* Load csp ctp *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr ]. }

    (* Lea ctp (-1)%Z *)
    iInstr "Hcode".
    { by transitivity (Some a_tstk); solve_addr. }
    (* WriteSR mtdc ctp *)
    iInstr "Hcode".
    { done. }
    (* Lea csp (-1)%Z *)
    iInstr "Hcode".
    { by transitivity (Some (a_stk ^+ 3)%a); solve_addr. }
    (* Load cgp csp *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr ]. }
    iEval (cbn) in "Hcgp".
    (* Lea csp (-1)%Z *)
    iInstr "Hcode".
    { by transitivity (Some (a_stk ^+ 2)%a); solve_addr. }
    (* Load ca2 csp *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr ]. }
    iEval (cbn) in "Hca2".
    (* Lea csp (-1)%Z *)
    iInstr "Hcode".
    { by transitivity (Some (a_stk ^+ 1)%a); solve_addr. }
    (* Load cs1 csp *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr ]. }
    iEval (cbn) in "Hcs1".
    (* Lea csp (-1)%Z *)
    iInstr "Hcode".
    { by transitivity (Some a_stk); solve_addr. }
    (* Load cs0 csp *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr ]. }
    iEval (cbn) in "Hcs0".
    (* GetE ct0 csp *)
    iInstr "Hcode".
    (* GetA ct1 csp *)
    iInstr "Hcode".

    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    assert (Forall (fun a => (std W2) !! a = Some Temporary) (finz.seq_between (a_stk ^+4)%a e_stk ))
      as Hcallee_stk_temporary.
    { clear -W1 Hrelated_W1_W2.
      apply Forall_forall.
      intros a Ha.
      eapply region_state_pub_temp; eauto.
      subst W1.
      cbn.
      destruct (decide (a ∈ a_local_args)).
      - by apply std_sta_update_multiple_lookup_in_i.
      - rewrite std_sta_update_multiple_lookup_same_i; last done.
        rewrite frame_W_lookup_std.
        by apply std_sta_update_multiple_lookup_in_i.
    }
    assert (Forall (fun a => (std W2) !! a = Some Temporary) a_local_args)
      as Hlocal_args_temporary.
    { clear -W1 Hrelated_W1_W2.
      apply Forall_forall.
      intros a Ha.
      eapply region_state_pub_temp; eauto.
      subst W1.
      by apply std_sta_update_multiple_lookup_in_i.
    }

    iMod ( revoked_by_revoked_resources with "[$Hworld $Hregion $Htemp_unknown]")
      as "(Hworld & Hregion & Htemp_unknown & %Hstd2_unknown)".
    { apply Forall_forall.
      intros a Ha.
      (* NOTE: true because a ∈ ltemp_unknown, and so it's Temporary in WO *)
      admit. }

    iMod ( monotone_revoke_keep _ _
             ( (finz.seq_between (a_stk ^+ 4)%a e_stk) ++ a_local_args)
           with "[ $Hworld $Hregion ]") as "(Hworld & Hregion & Hstk)".
    { auto. }
    { iApply big_sepL_pure; iPureIntro.
      intros k a Ha.
      apply lookup_app_Some in Ha.
      destruct Ha as [ Ha | [ _ Ha] ].
      - eapply Forall_lookup_1 in Hcallee_stk_temporary; eauto.
      - eapply Forall_lookup_1 in Hlocal_args_temporary; eauto.
    }
    iEval (rewrite big_sepL_sep) in "Hstk"
    ; iDestruct "Hstk" as "[Hstk %Htemporary_revoked]".
    iEval (rewrite region_addrs_exists) in "Hstk"; iDestruct "Hstk" as (pl) "Hstk".
    iEval (rewrite region_addrs_exists2) in "Hstk"; iDestruct "Hstk" as (φl) "[%Hlen Hstk]".
    iEval (rewrite big_sepL2_sep) in "Hstk"
    ; iDestruct "Hstk" as "[_ Htemp_res]".
    iEval (rewrite big_sepL2_sep) in "Htemp_res"
    ; iDestruct "Htemp_res" as "[Htemp_res _]".
    iEval (rewrite /temp_resources) in "Htemp_res".
    iEval (rewrite big_sepL2_later_2) in "Htemp_res".
    iEval (rewrite region_addrs_exists2) in "Htemp_res"; iDestruct "Htemp_res" as (wl) "[>%Hlen2 Htemp_res]".
    iEval (rewrite big_sepL2_sep) in "Htemp_res"
    ; iDestruct "Htemp_res" as "[_ Htemp_res]".
    iEval (rewrite big_sepL2_sep) in "Htemp_res"
    ; iDestruct "Htemp_res" as "[>Htemp_res _]".

    iAssert (
        [∗ list] a;w ∈ (finz.seq_between (a_stk ^+ 4)%a e_stk ++ a_local_args);
         wl, a ↦ₐ w
      )%I with "[Htemp_res]" as "Htemp_res".
    { admit. (* TODO just Iris manipulation *) }
    iEval (rewrite big_sepL2_app_inv_l) in "Htemp_res"
    ; iDestruct "Htemp_res" as (stk arg_locals) "(%Hwl & Hstk & Hargs_locals)".
    rewrite -/(region_pointsto (a_stk ^+ 4)%a e_stk stk).
    iDestruct (region_pointsto_cons with "[$Ha3_stk $Hstk]") as "Hstk".
    { solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "[$Ha2_stk $Hstk]") as "Hstk".
    { solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "[$Ha1_stk $Hstk]") as "Hstk".
    { solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "[$Ha0_stk $Hstk]") as "Hstk".
    { solve_addr. }
    { solve_addr. }

    focus_block 6 "Hcode" as a6 Ha6 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (clear_stack_spec with "[ - $HPC $Hcsp $Hct0 $Hct1 $Hcode $Hstk]"); eauto.
    { solve_addr. }
    { admit. (* TODO not entirely clear how to get that, but seems reasonable *) }
    iNext ; iIntros "(HPC & Hcsp & Hct0 & Hct1 & Hcode & Hstk)".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    focus_block 7 "Hcode" as a7 Ha7 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Mov cra ca2 *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    focus_block 8 "Hcode" as a8 Ha8 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iDestruct (big_sepM_insert_delete with "[$Hrmap $Hct1]") as "Hrmap".
    rewrite -delete_insert_ne //.
    iDestruct (big_sepM_insert_delete with "[$Hrmap $Hct0]") as "Hrmap".
    do 2 (rewrite -delete_insert_ne //).
    iDestruct (big_sepM_insert_delete with "[$Hrmap $Hcs0]") as "Hrmap".
    do 3 (rewrite -delete_insert_ne //).
    iDestruct (big_sepM_insert_delete with "[$Hrmap $Hcs1]") as "Hrmap".
    do 4 (rewrite -delete_insert_ne //).
    iDestruct (big_sepM_insert_delete with "[$Hrmap $Hca2]") as "Hrmap".
    do 5 (rewrite -delete_insert_ne //).
    iDestruct (big_sepM_insert_delete with "[$Hrmap $Hctp]") as "Hrmap".

    iApply (clear_registers_post_call_spec with "[- $HPC $Hrmap $Hcode]"); try solve_pure.
    { clear -Hfull_rmap.
      repeat (rewrite -delete_insert_ne //).
      repeat (rewrite dom_delete_L).
      repeat (rewrite dom_insert_L).
      apply regmap_full_dom in Hfull_rmap.
      rewrite Hfull_rmap.
      set_solver.
    }
    iNext; iIntros "H".
    iDestruct "H" as (arg_rmap') "(%Harg_rmap' & HPC & Harg_rmap' & Hcode)".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    focus_block 9 "Hcode" as a9 Ha9 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    (* close switcher invariant *)
    iDestruct (tstk_addr_update _ _ a_tstk with "Htstk_addr_full Htstk_addr_frag")
                as ">[Htstk_addr_full Htstk_addr_frag]".
    iDestruct (region_pointsto_cons with "[$tstk $Htstk]") as "Htstk".
    { solve_addr. }
    { solve_addr. }
    iMod ("Hclose_switcher_inv" with
           "[$Hna $Hmtdc $Hcode $Hb_switcher $Htstk $Htstk_addr_full $Hp_ot_switcher]")
      as "Hna"; first done.


    iMod (sts_update_loc _ _ _ _ true with "[$Hworld] [$Hι0_loc]") as "[Hworld Hι0_loc]".
    iMod ("Hclose_frame0_inv" with "[$Hna $Hι0_loc $HPframe0 $Htstk_addr_frag]") as "Hna".
    iMod (update_region_revoked with "[$] [$]") as "[Hregion Hworld]".
    { admit. (* NOTE by definition of Hι0_sts *) }

    iMod (sts_update_loc _ _ _ _ false with "[$Hworld] [$Hι_loc]") as "[Hworld Hι_loc]".
    iMod ("Hclose_frame_inv" with "[$Hna $Hι_loc]") as "Hna".
    iMod (update_region_revoked' with "[$] [$]") as "[Hregion Hworld]".
    { admit. (* NOTE by definition of Hι0_sts *) }

    iDestruct (big_sepL_app _ (finz.seq_between a_stk (a_stk ^+ 4)%a)
                           (finz.seq_between (a_stk ^+ 4)%a e_stk)
                with "[$Hrel_reg_saved $Hrel_callee_frm]")
      as "Hrel_stk".
    rewrite -finz_seq_between_split; last solve_addr.

    iMod (update_region_revoked_temp_pwl_multiple ⊤ _ _
                 (finz.seq_between a_stk e_stk) (region_addrs_zeroes a_stk e_stk) RWL interpC
                with "[$] [$] [Hstk]") as "[Hregion Hworld]".
    { done. }
    { done. }
    { assert (
          length (finz.seq_between a_stk e_stk) = length (region_addrs_zeroes a_stk e_stk)
        )
        by (by rewrite /region_addrs_zeroes length_replicate finz_seq_between_length).
      rewrite big_sepL2_sep; iFrame.
      rewrite big_sepL2_sep; iSplit.
      { rewrite big_sepL2_const_sepL_r.
        iSplit; first done.
        iApply big_sepL_intro.
        iModIntro ; iIntros (k w Hw).
        apply region_addrs_zeroes_lookup in Hw; simplify_eq.
        rewrite /interpC; cbn.
        by rewrite fixpoint_interp1_eq; cbn.
      }
      rewrite big_sepL2_sep; iSplit.
      { rewrite big_sepL2_const_sepL_l.
        iSplit ; done.
      }
      rewrite big_sepL2_sep; iSplit.
      { rewrite big_sepL2_const_sepL_r.
        iSplit ; first done.
        iApply big_sepL_intro.
        iModIntro ; iIntros (k w Hw).
        apply region_addrs_zeroes_lookup in Hw; simplify_eq.
        iApply future_pub_mono_interp_z.
      }
      rewrite big_sepL2_const_sepL_l.
      iSplit ; first done.
      iApply big_sepL_pure.
      iPureIntro ; intros k a Ha.
      cbn.
      destruct (decide (a < (a_stk ^+4))%a) as [Halt | Halt].
      - apply revoke_lookup_Revoked.
        admit. (* TODO should be Revoked, by separation and public transition *)
      - apply revoke_lookup_Monotemp.
        assert ( (a_stk ^+4) <= a)%a as Hage by solve_addr.
        admit. (* TODO see Hcallee_stk_temporary *)
    }

    assert
      (loc2 W2 !! ι0 =
        Some (convert_rel frame_rel_pub, convert_rel frame_rel_pub, convert_rel frame_rel_priv))
      as Hrel2_ι0.
    { admit. (* NOTE easy, it doesnt change *) }

    iDestruct (big_sepL_sep with "Htemp_unknown") as "[Htemp_unknown %Hunknown_revoked]".
    iMod (monotone_close_list_region W0 _ _ ltemp_unknown
                with "[] [$Hworld $Hregion $Htemp_unknown]") as "[Hworld Hregion]".
    { iPureIntro; eapply helper_switcher_final_pub; eauto. }

    (* TODO we need to re-open region the stack *)
    iApply ("Hφ" with "[-]"); iFrame "∗#".
    iSplit.
    { iPureIntro; eapply helper_switcher_final_pub; eauto. }
    iSplit.
    { by rewrite Harg_rmap'. }
    iSplitL "Hregion".
    { admit. (* TODO easy, once open *) }
    iSplitL "Hargs_locals".
    { rewrite region_addrs_exists; iFrame. }
    { admit. (* TODO if I close the world when it's
                  Temporary, I lose the information that it actually was zeroes.
                  Does it means that I need to open the world before?
              *)
    }
  Admitted.



  (* TODO:
     - How to encode the number of registers to pass as arguments?
       A possibility is to use a resource that encodes it.
   *)
  Lemma switcher_cc_specification
    (Nswitcher Nframe : namespace)
    (W0 : WORLD)
    (C : CmptName)
    (b_switcher e_switcher a_switcher_cc : Addr)
    (b_stk e_stk a_stk : Addr)
    (ot_switcher : OType)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : Word)
    (w_entry_point : Sealable)
    (stk_mem : list Word)
    (arg_rmap rmap : Reg)
    (a_local_args : list Addr)
    (b_tstk e_tstk : Addr)
    (φ : val -> iPropI Σ) :

    (* ct1 must contain the target entry points, which needs to be sealed with ot_switcher *)
    let wct1_caller := WSealed ot_switcher w_entry_point in
    (* the state of the stack before the jump  *)
    let stk_caller_save_area :=
      [wcs0_caller;wcs1_caller;wcra_caller;wcgp_caller]
    in
    let stk_callee_frame_pre_jmp :=
        (region_addrs_zeroes (a_stk ^+4)%a e_stk)
    in
    let stk_pre_jmp :=
     stk_caller_save_area ++ stk_callee_frame_pre_jmp
    in

    let W0' ι0 := frame_W
                 (std_update_multiple
                    (<l[ ι0 := encode false ]l> (revoke W0))
                    (finz.seq_between (a_stk ^+ 4)%a e_stk) Temporary)
                   in
    let W1 ι0 := (std_update_multiple (W0' ι0) a_local_args Temporary) in


    Nswitcher ## Nframe ->
    is_arg_rmap arg_rmap ->
    dom rmap = all_registers_s ∖ ((dom arg_rmap) ∪ {[ PC ; cgp ; cra ; csp ; cs0 ; cs1 ; ct1 ]} ) ->
    Forall (fun a => a ∉ dom (std W0) ) a_local_args ->

    ( ∃ (ι0 : positive) (Pframe0 : iProp Σ) (a0 : Addr),
      na_inv logrel_nais Nswitcher (switcher_inv b_switcher e_switcher a_switcher_cc b_tstk e_tstk ot_switcher )

      (* PRE-CONDITION *)
      ∗ na_own logrel_nais ⊤
      ∗ ⌜ (loc1 W0) !! ι0 = Some (encode true) ⌝
      ∗ ⌜ (loc2 W0) !! ι0 = Some ( convert_rel frame_rel_pub, convert_rel frame_rel_pub , convert_rel frame_rel_priv )  ⌝
      ∗ na_inv logrel_nais (Nframe.@ι0) (frame_inv C ι0 Pframe0 a0)
      (* Registers *)
      ∗ PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_cc
      ∗ cgp ↦ᵣ wcgp_caller
      ∗ cra ↦ᵣ wcra_caller
      (* Stack register *)
      ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
      (* Entry point of the target compartment *)
      ∗ ct1 ↦ᵣ wct1_caller ∗ interp (W1 ι0) C wct1_caller
      ∗ cs0 ↦ᵣ wcs0_caller
      ∗ cs1 ↦ᵣ wcs1_caller
      (* Argument registers, need to be safe-to-share *)
      ∗ ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg ∗ interp (W1 ι0) C warg )
      (* All the points-to predicate of the addresses shared as local argument have to be passed by the user,
         via the list a_local_args; and they have to not be in the domain
       *)
      ∗ ([∗ list] a ∈ a_local_args, ∃ w, a ↦ₐ w ∗ interp (W1 ι0) C w )
      (* All the other registers *)
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

      (* Stack frame *)
      ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]

      (* Interpretation of the world, at the moment of the switcher_call *)
      ∗ sts_full_world W0 C
      (* region W0 C *)
      ∗ open_region_many W0 C (finz.seq_between a_stk e_stk)
      ∗ ([∗ list] a ∈ (finz.seq_between a_stk e_stk), rel C a RWL interpC ∗ sts_state_std C a Temporary)


      (* Transformation of the world, before the jump to the adversary *)
      ∗ (
          region (W0' ι0) C ∗ sts_full_world (W0' ι0) C
          ∗ ([∗ list] a ∈ a_local_args, ∃ w : Word, a ↦ₐ w ∗ interp (W1 ι0) C w )
          ==∗
          region (W1 ι0) C ∗ sts_full_world (W1 ι0) C)


      (* POST-CONDITION *)
      ∗ ▷ ( (∃ (W2 : WORLD) (rmap' : Reg),
                (* We receive a public future world of the world pre switcher call *)
                ⌜ related_sts_pub_world W0 W2 ⌝
                ∗ ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ca0 ; ca1 ]} ⌝
                ∗ na_own logrel_nais ⊤
                (* Interpretation of the world *)
                ∗ sts_full_world W2 C
                ∗ open_region_many W2 C (finz.seq_between a_stk e_stk)
                ∗ ([∗ list] a ∈ (finz.seq_between a_stk e_stk), rel C a RWL interpC )
                ∗ PC ↦ᵣ updatePcPerm wcra_caller
                (* cgp is restored, cra points to the next  *)
                ∗ cgp ↦ᵣ wcgp_caller ∗ cra ↦ᵣ wcra_caller
                ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
                ∗ (∃ warg0, ca0 ↦ᵣ warg0)
                ∗ (∃ warg1, ca1 ↦ᵣ warg1)
                ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
                ∗ ([∗ list] a ∈ a_local_args, ∃ w, a ↦ₐ w )
                ∗ [[ a_stk , e_stk ]] ↦ₐ [[ region_addrs_zeroes a_stk e_stk ]])
            -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})
    )
    ⊢ WP Seq (Instr Executable)
       {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}.
  Proof.
    intros Hwct1_caller Hstk_caller_save_area Hstk_caller_frm_pre Hstk_pre_jmp W0' W1
      HN Harg_map Hrmap Hlocal_args_None.
    iIntros "HPRE".
    iDestruct "HPRE"
      as (ι0 Pframe0 a0)
           "(#Hinv_switcher & Hna & %Hι0_state & %Hι0_sts & #Hι0_inv
           & HPC & Hcgp & Hcra & Hcsp & Hct1 & #Hinterp_ct1 & Hcs0 & Hcs1
           & Hargmap & Hlocal_args & Hrmap & Hstk & Hworld & Hregion
           & Hstd_stk & Hnext_world & Hφ)".
    iEval (rewrite big_sepL_sep) in "Hstd_stk".
    iDestruct "Hstd_stk" as "[#Hrel_stk Hstd_state_stk]".

    (* ------------------------------------------------ *)
    (* -------- Prepare resources for the proof ------- *)
    (* ------------------------------------------------ *)

    (* --- Extract the code from the invariant --- *)
    iMod (na_inv_acc with "Hinv_switcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    rewrite /switcher_inv.
    iDestruct "Hswitcher_inv"
      as (a_tstk tstk_next)
           "(>Hmtdc & >%Hbounds & >Hcode & >Hb_switcher & >Htstk & Htstk_addr_full & #Hp_ot_switcher)".
    codefrag_facts "Hcode".
    rename H into Hcont_switcher_region; clear H0.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hinv_switcher" as hinv_switcher.
    iHide "Hφ" as hφ.

    (* --- Open the previous frame invariant --- *)
    iMod (na_inv_acc with "Hι0_inv Hna")
      as "(Hι0_inv_open & Hna & Hclose_ι0_inv)" ; auto.
    { solve_ndisj. }

    (* --- Extract scratch registers ct2 ctp --- *)
    assert (exists wct2, rmap !! ct2 = Some wct2) as [wct2 Hwct2].
    { admit. (* NOTE easy but tedious *) }
    iDestruct (big_sepM_delete _ _ ct2 with "Hrmap") as "[Hct2 Hrmap]"; first by simplify_map_eq.
    assert (exists wctp, rmap !! ctp = Some wctp) as [wctp Hwctp].
    { admit. (* NOTE easy but tedious *) }
    iDestruct (big_sepM_delete _ _ ctp with "Hrmap") as "[Hctp Hrmap]"; first by simplify_map_eq.
    (* ------------------------------------------------ *)
    (* ----- Start the proof of the switcher here ----- *)
    (* ------------------------------------------------ *)

    (* --- First, we destruct cases where it will quickly fail ---  *)
    destruct (decide ((a_stk ^+ 4) < e_stk))%a as [Hstk_ae|Hstk_ae]; cycle 1.
    { admit. (* NOTE will fail in the next upcoming instructions *) }
    destruct (decide (b_stk <= a_stk))%a as [Hstk_ba|Hstk_ba]; cycle 1.
    { admit. (* NOTE will fail in the next upcoming instructions *) }

    iAssert (⌜ (finz.seq_between a_stk e_stk) ## a_local_args ⌝)%I
      with "[ Hlocal_args Hstk]" as "%Hdisjoint_locals_stk".
    { rewrite /region_pointsto.
      rewrite region_addrs_exists.
      iDestruct "Hlocal_args" as (ws) "Hlocal_args".
      rewrite big_sepL2_sep.
      iDestruct "Hlocal_args" as  "[Hlocal_args _]".
      iClear "#"; clear.
      iApply big_sepL2_disjoint; eauto; iFrame.
    }
    iAssert (⌜ NoDup a_local_args ⌝)%I
      with "[Hlocal_args]" as "%HNoDup_locals".
    { rewrite region_addrs_exists.
      iDestruct "Hlocal_args" as (ws) "Hlocal_args".
      rewrite big_sepL2_sep.
      iDestruct "Hlocal_args" as  "[Hlocal_args _]".
      by iApply big_sepL2_nodup. }

    iDestruct (big_sepL2_length with "Hstk") as %Hlen_stk.
    iAssert (⌜ exists stk_wa stk_wa1 stk_wa2 stk_wa3 stk_mem',
                 (stk_mem = stk_wa :: stk_wa1 :: stk_wa2 :: stk_wa3 :: stk_mem')⌝)%I
      as %(stk_wa & stk_wa1 & stk_wa2 & stk_wa3 & stk_mem' & ->).
    { iEval (rewrite /region_pointsto) in "Hstk".
      iPureIntro.
      assert (length (finz.seq_between a_stk e_stk) > 4) as Hlen_stk_ae.
      { rewrite finz_seq_between_length.
        assert (a_stk^+4 < e_stk)%a by solve_addr.
        do 5 (rewrite finz_dist_S; last solve_addr); lia.
      }
      destruct stk_mem as [|stk_wa stk_mem0]; first (cbn in Hlen_stk; lia).
      destruct stk_mem0 as [|stk_wa1 stk_mem1]; first (cbn in Hlen_stk; lia).
      destruct stk_mem1 as [|stk_wa2 stk_mem2]; first (cbn in Hlen_stk; lia).
      destruct stk_mem2 as [|stk_wa3 stk_mem3]; first (cbn in Hlen_stk; lia).
      destruct stk_mem3 as [|stk_wa4 stk_mem4]; first (cbn in Hlen_stk; lia).
      eexists _,_,_,_,_; done.
    }

    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.

    (* ---- store csp cs0 ---- *)
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha1_stk Hstk]".
    { transitivity (Some (a_stk ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iInstr "Hcode".
    { apply withinBounds_true_iff; split;solve_addr. }

    (* ---- lea csp 1 ---- *)
    iInstr "Hcode".
    { transitivity (Some (a_stk ^+ 1%Z)%a); auto;solve_addr. }

    (* ---- store csp cs1 ---- *)
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha2_stk Hstk]".
    { transitivity (Some (a_stk ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }
    iInstr "Hcode".
    { apply withinBounds_true_iff; split;solve_addr. }

    (* ---- lea csp 1 ---- *)
    iInstr "Hcode".
    { transitivity (Some (a_stk ^+ 2%Z)%a); auto;solve_addr. }

    (* ---- store csp cra ---- *)
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha3_stk Hstk]".
    { transitivity (Some (a_stk ^+ 3)%a); auto; solve_addr. }
    { solve_addr. }
    iInstr "Hcode".
    { apply withinBounds_true_iff; split;solve_addr. }

    (* ---- lea csp 1 ---- *)
    iInstr "Hcode".
    { transitivity (Some (a_stk ^+ 3%Z)%a); auto;solve_addr. }

    (* ---- store csp cgp ---- *)
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha4_stk Hstk]".
    { transitivity (Some (a_stk ^+ 4)%a); auto; solve_addr. }
    { solve_addr. }
    iInstr "Hcode".
    { apply withinBounds_true_iff; split;solve_addr. }

    (* ---- lea csp 1 ---- *)
    iInstr "Hcode".
    { transitivity (Some (a_stk ^+ 4%Z)%a); auto;solve_addr. }

    (* --- getp ct2 csp --- *)
    iInstr "Hcode".

    (* --- mov ctp (encodePerm RWL) --- *)
    iInstr "Hcode".

    (* --- sub ct2 ct2 ctp --- *)
    iInstr "Hcode".
    replace ((encodePerm RWL - encodePerm RWL)%Z) with 0%Z by lia.

    (* --- jnz 2 ct2 --- *)
    iInstr "Hcode".

    (* --- jmp 2 --- *)
    iInstr "Hcode".

    (* --- readsr ct2 mtdc --- *)
    iInstr "Hcode".
    { done. (* TODO add to solve_pure *) }

    destruct (decide ((a_tstk ^+ 2) < e_tstk))%a as [Htstk_ae|Htstk_ae]; cycle 1.
    { admit. (* NOTE will fail in the next upcoming instructions *) }
    destruct (decide (b_tstk <= a_tstk))%a as [Htstk_ba|Htstk_ba]; cycle 1.
    { admit. (* NOTE will fail in the next upcoming instructions *) }
    iAssert (⌜ exists tstk_a1 tstk_next', (tstk_next = tstk_a1 :: tstk_next')⌝)%I
      as %(tstk_a1 & tstk_next' & ->).
    { iEval (rewrite /region_pointsto) in "Htstk".
      iDestruct (big_sepL2_length with "Htstk") as %Hlen_tstk.
      iPureIntro.
      assert (1 < length (finz.seq_between (a_tstk ^+ 1)%a e_tstk)) as Hlen_tstk_ae.
      { rewrite finz_seq_between_length.
        assert (a_tstk^+2 < e_tstk)%a by solve_addr.
        rewrite finz_dist_S; last solve_addr.
        rewrite finz_dist_S; last solve_addr; lia.
      }
      destruct tstk_next as [|stk_a1 tstk_next]; first (cbn in Hlen_tstk; lia).
      exists stk_a1, tstk_next; done.
    }
    iDestruct (region_pointsto_cons with "Htstk") as "[Ha1_tstk Htstk]".
    { transitivity (Some (a_tstk ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }

    (* Lea ct2 1%Z; *)
    iInstr "Hcode".
    {  transitivity (Some (a_tstk ^+1)%a); solve_addr. }

    (* Store ct2 csp; *)
    iInstr "Hcode".
    { rewrite /withinBounds andb_true_iff; solve_addr. }

    (* WriteSR mtdc ct2; *)
    iInstr "Hcode".
    { done. (* TODO add to solve_pure *) }

    (* Zero out the callee's stack frame *)
    (* GetE cs0 csp; *)
    iInstr "Hcode".

    (* GetA cs1 csp; *)
    iInstr "Hcode".

    (* Subseg csp cs1 cs0 *)
    iInstr "Hcode".
    { rewrite /isWithin andb_true_iff; solve_addr. }

    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    focus_block 1 "Hcode" as a_clear_stk1 Ha_clear_stk1 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (clear_stack_spec with "[ - $HPC $Hcsp $Hcs0 $Hcs1 $Hcode $Hstk]"); eauto.
    { done. }
    { solve_addr. }
    { clear -Hlen_stk Hstk_ae.
      cbn in Hlen_stk.
      rewrite finz_seq_between_length in Hlen_stk.
      do 4 (rewrite finz_dist_S in Hlen_stk; last solve_addr).
      replace (((((a_stk ^+ 1) ^+ 1) ^+ 1) ^+ 1)%a) with
        (a_stk ^+ 4)%a in Hlen_stk by solve_addr.
      by injection Hlen_stk.
    }
    iNext ; iIntros "(HPC & Hcsp & Hcs0 & Hcs1 & Hcode & Hstk)".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.


    iHide "Hcode" as hcode.
    iHide "Hφ" as hφ.

    iDestruct (big_sepL_sts_full_state_std with "[$] [$]") as "%Hstk_temporary".
    (* UPDATING THE WORLD NOW *)
    opose proof (extract_temps_split_world W0 (finz.seq_between a_stk e_stk) _ _) as (ltemp_unknown & Hnodupl & W_temps).
    { by apply finz_seq_between_NoDup. }
    { done. }

    (* 1) revoke the world *)
    iMod (monotone_revoke_keep_some_open_many
            _ C  ltemp_unknown [] _ RWL interpC
           with "[$Hworld $Hregion Hstd_state_stk]") as
      "(Hworld & Hregion & Htemp_unknown & _ & Htemp_opened)".
    { by cbn. }
    { cbn; iFrame. admit. (* NOTE easy, but tedious *) }

    (* 2) close the world *)
    iDestruct (big_sepL_sep with "Htemp_opened") as "[Htemp_opened #Htemp_opened_revoked]".
    iDestruct (region_close_revoked_many with "[$Hregion $Htemp_opened]") as "Hregion".
    { by apply finz_seq_between_NoDup. }

    (* 3) update the previous frame0 to emp *)
    iDestruct "Hι0_inv_open" as (ι0_state) "[Hι0_loc Hι0_Pframe]".
    iDestruct (sts_full_state_loc with "[$] [$]") as "%Hι0_state'".
    cbn in Hι0_state'.
    rewrite Hι0_state' in Hι0_state; simplify_eq.
    iDestruct (sts_update_loc _ _ _ _ false with "[$Hworld] [$Hι0_loc]") as ">[Hworld Hι0_loc]".

    (* 4) update the callee stack frame as Temporary *)
    rewrite {1}(finz_seq_between_split _ (a_stk^+4)%a e_stk) ; last solve_addr.
    rewrite big_sepL_app;
    iDestruct "Hrel_stk" as "[Hrel_reg_saved Hrel_callee_frm]".
    subst W0'.
    set ( callee_stk_frm_addr := finz.seq_between (a_stk ^+ 4)%a e_stk ).
    iMod (update_region_revoked with "[$] [$]") as "[Hworld Hregion]".
    { admit. (* NOTE by definition of Hι0_sts *) }

    iMod (update_region_revoked_temp_pwl_multiple ⊤ _ _
                 callee_stk_frm_addr (region_addrs_zeroes (a_stk ^+ 4)%a e_stk) RWL interpC
                with "[$] [$] [Hstk]") as "[Hregion Hworld]".
    { done. }
    { done. }
    { admit. (* NOTE easy, but tedious -- see what was done in the return *) }

    iAssert (⌜ a_local_args ## ltemp_unknown ⌝)%I as "%Hdis_local_unknown".
    { admit. (* NOTE just by separation between Htemp_unknown and Hlocal_args *)
    }

    (* 4) add the custom sts for the frame *)
    iMod ( sts_alloc_loc _ C true frame_rel_pub frame_rel_pub frame_rel_priv with "Hworld")
      as "(Hworld & %Hfresh_ι & %Hfresh_ι' & Hsts_loc_ι & #Hsts_rel_ι)".
    rewrite -/(frame_W (std_update_multiple (<l[ι0:=false]l>(revoke W0)) callee_stk_frm_addr Temporary)).

    set (W0' := (frame_W (std_update_multiple (<l[ι0:=false]l>(revoke W0)) callee_stk_frm_addr Temporary))).
    set (ι := fresh_cus_name (std_update_multiple (<l[ι0:=false]l>(revoke W0)) callee_stk_frm_addr Temporary)).

    iDestruct (region_monotone _ _ W0' with "Hregion") as "Hregion".
    { subst W0'. rewrite /frame_W //=. }
    { apply frame_W_related_sts_pub_world. }

    (* 5) make all local_arg Temporary *)
    iMod ("Hnext_world" with "[$Hregion $Hworld $Hlocal_args]") as "[Hregion Hworld]".
    subst hcode.


    focus_block 2 "Hcode" as a_unseal Ha_unseal "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* GetB cs1 PC *)
    iInstr "Hcode".

    (* GetA cs0 PC *)
    iInstr "Hcode".

    (* Sub cs1 cs1 cs0 *)
    iInstr "Hcode".
    (* Mov cs0 PC *)
    iInstr "Hcode".
    (* Lea cs0 cs1 *)
    assert ( (a_unseal ^+ 3 + (b_switcher - (a_unseal ^+ 1)))%a = Some ( (b_switcher ^+ 2%Z)%a ))
    as ?.
    { solve_addr. }
    iInstr "Hcode".

    (* Lea cs0 (-2)%Z *)
    iInstr "Hcode".
    { transitivity (Some b_switcher); solve_addr. }

    iEval (rewrite fixpoint_interp1_eq /= /interp_sb) in "Hinterp_ct1".
    iDestruct "Hinterp_ct1"
      as (Pct1 Hpers_Pct1) "(HmonoReq & Hseal_pred_Pct1 & HPct1 & HPct1_borrow)".
    iDestruct (seal_pred_agree with "Hseal_pred_Pct1 Hp_ot_switcher") as "Hot_switcher_agree".
    iSpecialize ("Hot_switcher_agree" $! (W1 ι0,C,WSealable w_entry_point)).

    (* Load cs0 cs0 *)
    iInstr "Hcode".
    iEval (cbn) in "Hcs0".


    rewrite /ot_switcher_prop.
    iEval (rewrite /safeC /=) in "Hot_switcher_agree".
    iRewrite "Hot_switcher_agree" in "HPct1".
    iDestruct "HPct1" as (b_tbl e_tbl a_tbl Heq_entry_point Hatbl Hbtbl Hbtbl1)
                           "(#Hinterp_tbl & #Hrel_btbl & #Hrel_btbl1 & Hrel_atbl)".
    iClear "Hot_switcher_agree".
    rewrite !Heq_entry_point.
    iEval (rewrite fixpoint_interp1_eq /=) in "Hinterp_tbl".
    rewrite finz_seq_between_cons; last solve_addr.
    iEval (cbn) in "Hinterp_tbl".
    iDestruct "Hinterp_tbl" as "[Hinterp_btbl Hinterp_tbl]".
    rewrite finz_seq_between_cons; last solve_addr.
    iEval (cbn) in "Hinterp_tbl".
    iDestruct "Hinterp_tbl" as "[Hinterp_btbl1 Hinterp_tbl]".
    assert ( a_tbl ∈ finz.seq_between ((b_tbl ^+ 1) ^+ 1)%a e_tbl) as Ha_tbl_in.
    { apply elem_of_finz_seq_between; solve_addr. }
    apply elem_of_list_lookup_1 in Ha_tbl_in.
    destruct Ha_tbl_in as [i_a_tbl Ha_tbl_in].
    iDestruct (big_sepL_take_drop _ _ i_a_tbl with "Hinterp_tbl") as "[_ Hinterp_tbl2]".
    iClear "Hinterp_tbl".
    replace (drop i_a_tbl (finz.seq_between ((b_tbl ^+ 1) ^+ 1)%a e_tbl))
              with (finz.seq_between a_tbl e_tbl) by admit. (* TODO unclear why it's true *)
    rewrite (finz_seq_between_cons a_tbl e_tbl); last solve_addr.
    iEval (cbn) in "Hinterp_tbl2".
    iDestruct "Hinterp_tbl2" as "[Hinterp_atbl _]".
    iDestruct "Hinterp_btbl" as (pbtbl Pbtbl _ _) "(_ & _ & _ & _ & _ & %Hstd_btbl)"; clear pbtbl Pbtbl.
    iDestruct "Hinterp_btbl1" as (pbtbl1 Pbtbl1 _ _) "(_ & _ & _ & _ & _ & %Hstd_btbl1)"; clear pbtbl1 Pbtbl1.
    iDestruct "Hinterp_atbl" as (patbl Patbl _ _) "(_ & _ & _ & _ & _ & %Hstd_atbl)"; clear patbl Patbl.

    (* UnSeal ct1 cs0 ct1 *)
    assert ( ot_switcher < (ot_switcher ^+1) )%ot as Hot_switcher.
    { admit. (* TODO add hyp *) }

    subst Hwct1_caller.
    iInstr "Hcode".
    { done. (* TODO solve_pure *) }
    { apply withinBounds_true_iff; solve_addr. (* TODO solve_pure *) }
    rewrite Heq_entry_point.

    (* Load cs0 ct1 *)
    iDestruct (region_open_perm with "[$Hrel_atbl $Hregion $Hworld]")
      as (watbl) "(Hregion & Hworld & Hstd_atbl & Ha_tbl & _ & HmonoReq_atbl & #HPatbl)"
    ; first done.
    iInstr "Hcode".
    { split ; first solve_pure.
      rewrite /withinBounds; solve_addr. }
    iDestruct "HPatbl" as (nargs off_entry Hwatbl) "%Hnargs".
    cbn in Hwatbl ; subst watbl.
    iEval (cbn) in "Hcs0".
    iDestruct (region_close_perm
                with "[$Hregion $Hstd_atbl $Ha_tbl $HmonoReq_atbl $Hrel_atbl]")
                as "Hregion"; eauto.

    (* LAnd ct2 cs0 7%Z *)
    iInstr "Hcode".

    (* ShiftR cs0 cs0 3%Z *)
    iInstr "Hcode".

    replace ( (Z.land (encode_entry_point nargs off_entry) 7)) with nargs by admit.
    replace ( (encode_entry_point nargs off_entry ≫ 3)%Z) with off_entry by admit.
    (* TODO unclear why the above are true: should be properties of encode_entry_point *)
    (* GetB cgp ct1 *)
    iInstr "Hcode".

    (* GetA cs1 ct1 *)
    iInstr "Hcode".

    (* Sub cs1 cgp cs1 *)
    iInstr "Hcode".

    (* Lea ct1 cs1 *)
    iInstr "Hcode".
    { transitivity (Some b_tbl); solve_addr. }

    (* Load cra ct1 *)
    iDestruct (region_open_perm with "[$Hrel_btbl $Hregion $Hworld]")
      as (wbtbl) "(Hregion & Hworld & Hstd_btbl & Ha_tbl & _ & HmonoReq_btbl & #HPbtbl)"
    ; first done.
    iInstr "Hcode".
    { split ; first solve_pure.
      rewrite /withinBounds; solve_addr. }
    iDestruct "HPbtbl" as (bpcc epcc apcc) "[%Hwbtbl #Hinterp_wbtbl]".
    cbn in Hwbtbl ; subst wbtbl.
    iEval (cbn) in "Hcra".
    iDestruct (region_close_perm
                with "[$Hregion $Hstd_btbl $Ha_tbl $HmonoReq_btbl $Hrel_btbl]")
                as "Hregion"; eauto.
    { iSplit; auto. iNext; eauto. }

    iEval (cbn) in "Hinterp_wbtbl".
    iDestruct (interp_updatePcPerm with "Hinterp_wbtbl") as "Hjmp_callee_pc".

    (* Lea ct1 1%Z *)
    iInstr "Hcode".
    { transitivity (Some (b_tbl ^+ 1)%a); solve_addr. }

    (* Load cgp ct1 *)
    iDestruct (region_open_perm with "[$Hrel_btbl1 $Hregion $Hworld]")
      as (wbtbl1) "(Hregion & Hworld & Hstd_btbl1 & Ha_tbl & _ & HmonoReq_btbl1 & #HPbtbl1)"
    ; first done.
    iInstr "Hcode".
    { split ; first solve_pure.
      rewrite /withinBounds; solve_addr. }
    iDestruct "HPbtbl1" as (bcgp ecgp) "[%Hwbtbl1 #Hinterp_wbtbl1]".
    cbn in Hwbtbl1 ; subst wbtbl1.
    iEval (cbn) in "Hcra".
    iDestruct (region_close_perm
                with "[$Hregion $Hstd_btbl1 $Ha_tbl $HmonoReq_btbl1 $Hrel_btbl1]")
                as "Hregion"; eauto.
    { iSplit; auto. }

    (* Lea cra cs0 *)
    iInstr "Hcode".
    { transitivity (Some (bpcc ^+ off_entry)%a); admit. }
    (* TODO actually, it's fine if the offset fail, the machine fails...
       we just need not to use iInstr, but instead manually choose the wp rule
     *)

    (* Add ct2 ct2 1%Z *)
    iInstr "Hcode".

    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    focus_block 3 "Hcode" as a_clear_pre_reg1 Ha_clear_pre_reg1 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (clear_registers_pre_call_skip_spec with "[- $HPC $Hargmap $Hct2 $Hcode]"); try solve_pure.
    { solve_addr. }
    iNext; iIntros "H".
    iDestruct "H" as (arg_rmap') "(%Harg_rmap' & HPC & Hct2 & Harg_rmap' & Hcode)".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    focus_block 4 "Hcode" as a_clear_pre_reg2 Ha_clear_pre_reg2 "Hcode" "Hcont"; iHide "Hcont" as hcont.

    iDestruct (big_sepM_insert _ _ ctp with "[$Hrmap $Hctp]") as "Hrmap"; first by simplify_map_eq.
    rewrite insert_delete_insert.
    repeat (rewrite -delete_insert_ne //).
    iDestruct (big_sepM_insert _ _ ct2 with "[$Hrmap $Hct2]") as "Hrmap"; first by simplify_map_eq.
    rewrite insert_delete_insert.

    iDestruct (big_sepM_insert _ _ ct1 with "[$Hrmap $Hct1]") as "Hrmap".
    { simplify_map_eq. apply not_elem_of_dom.
      rewrite Hrmap; set_solver+.
    }
    iDestruct (big_sepM_insert _ _ cs0 with "[$Hrmap $Hcs0]") as "Hrmap".
    { simplify_map_eq. apply not_elem_of_dom.
      rewrite Hrmap; set_solver+.
    }
    iDestruct (big_sepM_insert _ _ cs1 with "[$Hrmap $Hcs1]") as "Hrmap".
    { simplify_map_eq. apply not_elem_of_dom.
      rewrite Hrmap; set_solver+.
    }
    iApply (clear_registers_pre_call_spec with "[- $HPC $Hrmap $Hcode]"); try solve_pure.
    { clear -Harg_map Hrmap.
      rewrite !dom_insert_L.
      rewrite Hrmap.

      rewrite -difference_difference_l_L.
      do 4 rewrite union_assoc_L.
      rewrite union_comm_L.
      replace {[cs1; cs0; ct1; ct2; ctp]}
        with ({[cs1; cs0; ct1]} ∪ {[ct2; ctp]} : gset _) by set_solver.
      replace ( (all_registers_s ∖ dom arg_rmap ∖ {[PC; cgp; cra; csp; cs0; cs1; ct1]})
                 ∪ ({[cs1; cs0; ct1]} ∪ {[ct2; ctp]}))
        with ( (all_registers_s ∖ dom arg_rmap ∖ {[PC; cgp; cra; csp; cs0; cs1; ct1]}
                  ∪ {[cs1; cs0; ct1]}) ∪ {[ct2; ctp]}) by set_solver.
      rewrite union_comm_L.
      replace (
         (all_registers_s ∖ dom arg_rmap ∖ {[PC; cgp; cra; csp; cs0; cs1; ct1]} ∪ {[cs1; cs0; ct1]})
        )
        with (
         all_registers_s ∖ dom arg_rmap ∖ {[PC; cgp; cra; csp]}
        ).
      2:{
        replace {[PC; cgp; cra; csp; cs0; cs1; ct1]}
        with ( {[PC; cgp; cra; csp]} ∪ {[cs1; cs0; ct1]} : gset _)
             by set_solver.
      rewrite -(difference_difference_l_L  _ _ {[cs1; cs0; ct1]}).
      rewrite difference_union_L.
      set_solver.
      }
      rewrite subseteq_union_1_L; set_solver.
    }
    iNext; iIntros "H".
    iDestruct "H" as (rmap') "(%Hrmap' & HPC & Hrmap' & Hcode)".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.


    focus_block 5 "Hcode" as a_jmp Ha_jmp "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Jalr cra cra *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    iEval (cbn) in "Hcgp".
    iEval (cbn) in "Hinterp_wbtbl".
    iEval (cbn) in "Hinterp_wbtbl1".

    iAssert ([∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ interp (W1 ι0) C w)%I with "[Hrmap']" as "Hrmap'".
    {
      iApply (big_sepM_impl with "[$]").
      iModIntro ; iIntros (r w Hr) "[$ ->]".
      iEval (rewrite !fixpoint_interp1_eq) ; done.
    }

    (* show that csp in safe-to-share *)
    iAssert ( interp (W1 ι0) C (WCap RWL Local (a_stk ^+ 4)%a e_stk (a_stk ^+ 4)%a)) as "Hinterp_csp".
    { iEval (rewrite fixpoint_interp1_eq); cbn.
      subst callee_stk_frm_addr.
      iApply big_sepL_intro.
      iModIntro. iIntros (? astk Hastk).
      assert ( (std (W1 ι0)) !! astk = Some Temporary) as Hastk_temporary.
      { apply (monotone.region_state_pub_temp W0').
        + subst W1 W0'; cbn.
          apply related_sts_pub_update_multiple.
          apply Forall_forall.
          intros a' Ha'.
          assert (a' ∉ dom (std W0)).
          { rewrite Forall_forall in Hlocal_args_None.
            by specialize (Hlocal_args_None a' Ha').
          }
          intro Hcontra.
          apply H.
          rewrite elem_of_dom in Hcontra.
          destruct Hcontra as [? Hcontra].
          rewrite frame_W_lookup_std in Hcontra.
          rewrite std_sta_update_multiple_lookup_same_i in Hcontra.
          2: { intro Hcontra.
               clear -Ha' Hcontra Hdisjoint_locals_stk.
               rewrite /disjoint /set_disjoint_instance in Hdisjoint_locals_stk.
               eapply Hdisjoint_locals_stk; eauto.
               apply elem_of_finz_seq_between in Hcontra.
               apply elem_of_finz_seq_between.
               solve_addr.
          }
          cbn in Hcontra.
          rewrite elem_of_dom.
          by eapply revoke_std_sta_lookup_Some.
        + eapply std_update_multiple_lookup; eauto.
      }
      iExists RWL, interp; cbn.
      iSplit; first done.
      iSplit; first (iPureIntro; apply persistent_cond_interp).
      iSplit; first (iDestruct (big_sepL_lookup with "Hrel_callee_frm") as "?"; eauto).
      iSplit; first (iNext; iApply zcond_interp).
      iSplit; first (iNext; iApply rcond_interp).
      iSplit; first (iNext; iApply wcond_interp).
      iSplit; first (iApply monoReq_interp; done).
      by rewrite /region_state_pwl.
    }

    (* allocate frame invariant *)
    (* rewrite tstack_frag_combine_cons. *)
    iHide "Htemp_unknown" as htemp_unknown.
    iDestruct "Hι0_Pframe" as "[HPframe0 Htstk_addr_frag]".
    iDestruct (tstk_addr_agree with "Htstk_addr_full Htstk_addr_frag") as "%Htstk_addr".
    symmetry in Htstk_addr; simplify_eq.
    iDestruct (tstk_addr_update _ _ (a_tstk ^+ 1)%a with "Htstk_addr_full Htstk_addr_frag")
                as ">[Htstk_addr_full Htstk_addr_frag]".


    set (Pframe := (hφ0
                    ∗ Pframe0
                    ∗ (a_tstk ^+ 1)%a ↦ₐ WCap RWL Local b_stk e_stk (a_stk ^+ 4)%a
                    ∗ [[a_stk,(a_stk ^+ 4)%a]]↦ₐ[[Hstk_caller_save_area]]
                    ∗ htemp_unknown
                   )%I).
    iMod (na_inv_alloc
            logrel_nais
            ⊤ (Nframe .@ ι)
            (frame_inv C ι Pframe (a_tstk ^+ 1)%a)
           with "[$Hsts_loc_ι $Ha1_tstk $Hφ $Htemp_unknown $Htstk_addr_frag $HPframe0 Ha1_stk Ha2_stk Ha3_stk Ha4_stk ]") as "#Hinv_frame".
    { iNext; iFrame.
      rewrite /Hstk_caller_save_area.
      admit. (* NOTE just iris manipulation *)
    }

    (* close ι0 invariant *)
    iMod ("Hclose_ι0_inv" with "[$Hna $Hι0_loc]") as "Hna".
    (* close switcher invariant *)
    iMod ("Hclose_switcher_inv" with
           "[$Hna Hmtdc Hcode Hb_switcher Htstk Htstk_addr_full]")
      as "Hna"
    .
    { iNext; iFrame "Hmtdc".
      iExists tstk_next'.
      iSplit; first done.
      iFrame.
      replace ((a_tstk ^+ 1) ^+ 1)%a with (a_tstk ^+ 2)%a by solve_addr+Htstk_ae.
      iFrame "∗#".
    }

    iAssert (interp (W1 ι0) C (WSentry XSRW_ Local b_switcher e_switcher (a_jmp ^+ 1)%a)) as "Hinterp_return".
    { shelve. }

    iCombine "Harg_rmap' Hrmap'" as "Hrmap'".
    rewrite -(big_sepM_union _ arg_rmap' rmap').
    2: {
      clear -Harg_rmap' Hrmap'.
      rewrite /is_arg_rmap in Harg_rmap'; simplify_eq.
      apply map_disjoint_dom.
      set_solver.
    }
    iDestruct (big_sepM_insert _ _ cgp with "[$Hrmap' $Hcgp $Hinterp_wbtbl1]") as "Hrmap'".
    {
      clear -Harg_rmap' Hrmap'.
      rewrite /is_arg_rmap in Harg_rmap'; simplify_eq.
      rewrite /dom_arg_rmap in Hrmap'.
      apply not_elem_of_dom.
      set_solver.
    }
    iDestruct (big_sepM_insert _ _ cra with "[$Hrmap' $Hcra $Hinterp_return]") as "Hrmap'".
    {
      clear -Harg_rmap' Hrmap'.
      rewrite /is_arg_rmap in Harg_rmap'; simplify_eq.
      rewrite /dom_arg_rmap in Hrmap'.
      apply not_elem_of_dom.
      set_solver.
    }
    iDestruct (big_sepM_insert _ _ csp with "[$Hrmap' $Hcsp $Hinterp_csp]") as "Hrmap'".
    {
      clear -Harg_rmap' Hrmap'.
      rewrite /is_arg_rmap in Harg_rmap'; simplify_eq.
      rewrite /dom_arg_rmap in Hrmap'.
      do 2 rewrite lookup_insert_ne //.
      apply not_elem_of_dom.
      set_solver.
    }
    iDestruct (big_sepM_insert _ _ PC with "[$Hrmap' $HPC $Hinterp_wbtbl]") as "Hrmap'".
    {
      clear -Harg_rmap' Hrmap'.
      rewrite /is_arg_rmap in Harg_rmap'; simplify_eq.
      rewrite /dom_arg_rmap in Hrmap'.
      do 3 rewrite lookup_insert_ne //.
      apply not_elem_of_dom.
      set_solver.
    }

    match goal with
    | _ : _ |- context [<[PC:=?w]> ?m] =>
        set (rmap'' := <[PC:=w]> m)
    end.
    rewrite -(insert_id rmap'' PC (WCap RX Global bpcc epcc apcc)).
    2: { by subst rmap'' ; rewrite lookup_insert. }
    iEval (rewrite big_sepM_sep) in "Hrmap'".
    iDestruct "Hrmap'" as "[Hrmap_mapsto Hrmap_interp]".
    iApply "Hjmp_callee_pc"; iFrame.
    rewrite /interp_reg //=.

    iSplitR "Hrmap_interp".
    + clear -Hrmap' Harg_rmap'.
      subst hinv_switcher hφ0 htemp_unknown Pframe rmap''.
      iPureIntro.
      intros r; cbn.
      destruct (decide (r = PC)) as [Hrpc | Hrpc]; simplify_eq; first by rewrite lookup_insert.
      rewrite lookup_insert_ne //.
      destruct (decide (r = csp)) as [Hrcsp | Hrcsp]; simplify_eq; first by rewrite lookup_insert.
      rewrite lookup_insert_ne //.
      destruct (decide (r = cra)) as [Hrcra | Hrcra]; simplify_eq; first by rewrite lookup_insert.
      rewrite lookup_insert_ne //.
      destruct (decide (r = cgp)) as [Hrcgp | Hrcgp]; simplify_eq; first by rewrite lookup_insert.
      rewrite lookup_insert_ne //.
      apply elem_of_dom.
      rewrite dom_union.
      rewrite elem_of_union.
      destruct (decide (r ∈ dom arg_rmap')); first by left.
      right.
      rewrite Harg_rmap' in n.
      assert (r ∉ ({[PC; cra; cgp; csp]} : gset RegName)).
      { set_solver.  }
      rewrite Hrmap'.
      rewrite elem_of_difference.
      split; first by apply all_registers_s_correct.
      set_solver.
    + iIntros (r w HrPC Hr).
      subst rmap''.
      admit. (* NOTE easy, just boring stuff *)



    (* Proof of the return *)
    Unshelve.

    iClear
      "Hp_ot_switcher HmonoReq Hseal_pred_Pct1 Hrel_btbl Hrel_btbl1 Hrel_atbl
      HPct1_borrow Hjmp_callee_pc Hinterp_wbtbl1 Hinterp_csp Hinterp_wbtbl".
    clear
      (* Ha_jmp a_jmp *)
      Hrmap' Harg_rmap'
      Ha_clear_pre_reg2 a_clear_pre_reg2
      Ha_clear_pre_reg1 a_clear_pre_reg1
      H1 Ha_unseal a_unseal
      Ha_clear_stk1 a_clear_stk1.
    clear Hwctp Hwct2 Hrmap rmap rmap'.
    subst hclose_switcher_inv hφ.
    clear Hstk_pre_jmp.
    cbn in Ha_jmp.
    clear Harg_map.
    clear Hnargs arg_rmap' nargs off_entry Hot_switcher Hstd_atbl Hstd_btbl1 Hstd_btbl Ha_tbl_in i_a_tbl.
    clear Hatbl Hbtbl Hbtbl1.
    clear Hlen_stk wct2 wctp stk_wa stk_wa1 stk_wa2 stk_wa3 stk_mem' tstk_next'.
    subst W0' W1; cbn.
    match goal with
      | _ : _ |- context [ std_update_multiple ?W a_local_args Temporary ]
        => set (W1 := std_update_multiple W a_local_args Temporary)
    end.

    iApply switcher_ret_specification ; eauto.
    { apply NoDup_app.
      split; first by apply finz_seq_between_NoDup.
      split; last done.
      rewrite /disjoint /set_disjoint_instance in Hdisjoint_locals_stk.
      intros a Ha. intro Hcontra.
      eapply Hdisjoint_locals_stk; eauto.
      apply elem_of_finz_seq_between in Ha.
      apply elem_of_finz_seq_between.
      solve_addr.
    }
    iFrame "#".
  Admitted.


  Lemma switcher_interp (W : WORLD) (C : CmptName) (N : namespace)
    (b_switcher e_switcher a_switcher_cc : Addr) (ot_switcher : OType) :
    na_inv logrel_nais N (switcher_inv b_switcher e_switcher a_switcher_cc ot_switcher) -∗
    interp W C (WSentry XSRW_ Local b_switcher e_switcher a_switcher_cc).
  Proof.
  Admitted.

  Lemma future_priv_mono_interp_switcher (C : CmptName) (N : namespace)
    (b_switcher e_switcher a_switcher_cc : Addr) (ot_switcher : OType) :
    na_inv logrel_nais N (switcher_inv b_switcher e_switcher a_switcher_cc ot_switcher) -∗
    future_priv_mono C interpC (WSentry XSRW_ Local b_switcher e_switcher a_switcher_cc).
  Proof.
  Admitted.


End Switcher.
