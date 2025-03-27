From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel interp_weakening addr_reg_sample rules proofmode.
From cap_machine Require Import multiple_updates.
From cap_machine Require Import switcher.

Section TStack.
  Context {Σ:gFunctors} {A : Type}.

  Definition tstack_full (l : list A) : iProp Σ. Admitted.
  Definition tstack_frag (l : list A) (n : nat) : iProp Σ. Admitted.

  Lemma tstack_agree (l l' : list A) (n : nat) :
    tstack_full l
    -∗ tstack_frag l' n
    -∗ ⌜ ∃ l0 l1, length l0 = n ∧ l = l0++l'++l1 ⌝
  .
  Admitted.

  Lemma tstack_full_unique (l l' : list A) :
    tstack_full l -∗ tstack_full l' -∗ False.
  Admitted.

  Lemma tstack_frag_unique (l l' : list A) (n n' : nat) :
    n <= n' < (n + length l')
    -> tstack_frag l n
    -∗ tstack_frag l' n'
    -∗ False.
  Admitted.

  Lemma tstack_frag_combine (l l' : list A) (n n' : nat) :
    n' = (n + length l)
    -> tstack_frag l n ∗ tstack_frag l' n' ⊣⊢ tstack_frag (l++l') n.
  Admitted.

  Lemma tstack_frag_combine_cons (a : A) (l : list A) (n : nat) :
    tstack_frag (a::l) n ⊣⊢ tstack_frag [a] n ∗ tstack_frag l (n+1).
  Proof.
    iStartProof.
    change (a::l) with ([a]++l).
    rewrite tstack_frag_combine; last done.
    by iSplit; iIntros "H".
  Qed.

End TStack.

Section Switcher.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Ltac iHide0 irisH coqH :=
    let coqH := fresh coqH in
    match goal with
    | h: _ |- context [ environments.Esnoc _ (INamed irisH) ?prop ] =>
        set (coqH := prop)
    end.

  Tactic Notation "iHide" constr(irisH) "as" ident(coqH) :=
    iHide0 irisH coqH.


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
    (b_switcher e_switcher a_switcher_cc : Addr)
    (ot_switcher : OType) : iProp Σ :=
    ∃ (b_tstk e_tstk a_tstk : Addr) (tstk_prev tstk_next : list Word),
     mtdc ↦ₛᵣ WCap RWL Local b_tstk e_tstk a_tstk
     ∗ ⌜ SubBounds
         b_switcher e_switcher
         a_switcher_cc (a_switcher_cc ^+ length switcher_instrs)%a ⌝
     ∗ codefrag a_switcher_cc switcher_instrs
     ∗ b_switcher ↦ₐ WSealRange (true,true) Global ot_switcher (ot_switcher^+1)%ot ot_switcher
     ∗ [[ b_tstk, (a_tstk ^+1)%a ]] ↦ₐ [[ tstk_prev ]]
     ∗ [[ (a_tstk ^+1)%a, e_tstk ]] ↦ₐ [[ tstk_next ]]
     ∗ tstack_full (tstk_prev ++ tstk_next)
     ∗ tstack_frag tstk_next (finz.dist (a_tstk ^+1)%a e_tstk)
     ∗ seal_pred ot_switcher ot_switcher_prop
  .

  (* TODO move *)
  Definition list_max_positive (l : list positive) := fold_right Pos.max xH l.
  Lemma fresh_list_max (l : list positive) (i : positive) :
    ( (list_max_positive l) < i )%positive -> i ∉ l.
  Proof.
    induction l; intros Hle.
    - apply not_elem_of_nil.
    - assert ( (list_max_positive l < i)%positive ∧ (a < i)%positive ) as [Hle_l Hle_a].
      {
        cbn in Hle.
        apply Pos.max_lub_lt_iff in Hle.
        destruct Hle as [Hle_l Hle_a]; auto.
      }
      apply not_elem_of_cons.
      split; [lia | by apply IHl].
  Qed.

  Definition gset_max_positive (g : gset positive) := list_max_positive (elements g).
  Lemma fresh_gset_max (g : gset positive) (i : positive) :
    ( (gset_max_positive g) < i )%positive -> i ∉ g.
  Proof.
    intros Hmax.
    rewrite /gset_max_positive in Hmax.
    apply fresh_list_max in Hmax.
    set_solver.
  Qed.

  Definition fresh_cus_name (W : WORLD) : positive :=
    let WL1 := gset_max_positive (dom (loc1 W)) in
    let WL2 := gset_max_positive (dom (loc2 W)) in
    (Pos.succ ( WL1 `max` WL2 )%positive).

  Lemma fresh_cus_name_fresh1 (W : WORLD) :
    fresh_cus_name W ∉ (dom (loc1 W)).
  Proof.
    rewrite /fresh_cus_name.
    set ( n1 := gset_max_positive (dom (loc1 W))).
    set ( n2 := gset_max_positive (dom (loc2 W))).
    destruct (Pos.max_dec n1 n2) as [Hmax | Hmax].
    - rewrite Hmax.
      assert (n1 < Pos.succ n1)%positive as Hn1 by lia.
      by apply fresh_gset_max in Hn1.
    - assert (n1 <= n2)%positive as H2_le_1 by (by apply Pos.max_r_iff).
      rewrite Hmax.
      assert (n1 < Pos.succ n2)%positive as Hn1 by lia.
      by apply fresh_gset_max in Hn1.
  Qed.

  Lemma fresh_cus_name_fresh2 (W : WORLD) :
    fresh_cus_name W ∉ (dom (loc2 W)).
  Proof.
    rewrite /fresh_cus_name.
    set ( n1 := gset_max_positive (dom (loc1 W))).
    set ( n2 := gset_max_positive (dom (loc2 W))).
    destruct (Pos.max_dec n1 n2) as [Hmax | Hmax].
    - assert (n2 <= n1)%positive as H2_le_1 by (by apply Pos.max_l_iff).
      rewrite Hmax.
      assert (n2 < Pos.succ n1)%positive as Hn1 by lia.
      by apply fresh_gset_max in Hn1.
    - rewrite Hmax.
      assert (n2 < Pos.succ n2)%positive as Hn1 by lia.
      by apply fresh_gset_max in Hn1.
  Qed.

   Definition frame_inv (C : CmptName) (i : positive) (P : iProp Σ) :=
     (∃ x:bool, sts_state_loc C i x ∗ if x then P else emp)%I.

   Definition frame_rel_pub := λ (a b : bool), False.
   Definition frame_rel_priv := λ (a b : bool), True.
   Definition frame_W (W : WORLD) : WORLD :=
     let ι := fresh_cus_name W in
      <l[ ι := false , ( frame_rel_pub, (frame_rel_pub, frame_rel_priv)) ]l> W.


  (* TODO:
     - How to encode the number of registers to pass as arguments?
       A possibility is to use a resource that encodes it.
   *)
  Lemma switcher_cc_specification
    (E : coPset) (N : namespace)
    (W0 : WORLD)
    (C : CmptName)
    (g_switcher : Locality)
    (b_switcher e_switcher a_switcher_cc : Addr)
    (b_stk e_stk a_stk : Addr)
    (ot_switcher : OType)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : Word)
    (w_entry_point : Sealable)
    (stk_mem : list Word)
    (arg_rmap rmap : Reg)
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

    let POST_COND_SWITCHER :=
      ( ( (∃ (W2 : WORLD) (rmap' : Reg),
              (* We receive a public future world of the world pre switcher call *)
              ⌜ related_sts_pub_world W0 W2 ⌝
              ∗ ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ca0 ; ca1 ]} ⌝
              ∗ na_own logrel_nais E
              (* Interpretation of the world *)
              ∗ region W2 C ∗ sts_full_world W2 C
              ∗ PC ↦ᵣ updatePcPerm wcra_caller
              (* cgp is restored, cra points to the next  *)
              ∗ cgp ↦ᵣ wcgp_caller ∗ cra ↦ᵣ wcra_caller
              ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
              ∗ (∃ warg0, ca0 ↦ᵣ warg0 ∗ interp W2 C warg0)
              ∗ (∃ warg1, ca1 ↦ᵣ warg1 ∗ interp W2 C warg1)
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              ∗ [[ a_stk , e_stk ]] ↦ₐ [[ region_addrs_zeroes a_stk e_stk ]])
          -∗ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}
        ))%I
    in

    let W1 := frame_W (std_update_multiple W0 (finz.seq_between (a_stk ^+ 4)%a e_stk) Temporary) in

    let PRE_COND_SWITCHER :=
      (
      na_own logrel_nais E
      (* Registers *)
      ∗ PC ↦ᵣ WCap XSRW_ g_switcher b_switcher e_switcher a_switcher_cc
      ∗ cgp ↦ᵣ wcgp_caller
      ∗ cra ↦ᵣ wcra_caller
      (* Stack register *)
      ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
      (* Entry point of the target compartment *)
      ∗ ct1 ↦ᵣ wct1_caller ∗ interp W1 C wct1_caller
      ∗ cs0 ↦ᵣ wcs0_caller
      ∗ cs1 ↦ᵣ wcs1_caller
      (* Argument registers, need to be safe-to-share *)
      ∗ ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg ∗ interp W1 C warg )
      (* All the other registers *)
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

      (* Stack frame *)
      ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]

      (* Interpretation of the world, at the moment of the switcher_call *)
      ∗ region W0 C ∗ sts_full_world W0 C

      (* (* Transformation of the world, before the jump to the adversary *) *)
      (* ∗ ( [[ a_stk , e_stk ]] ↦ₐ [[ stk_pre_jmp ]] *)
      (*     ∗ region W0 C ∗ sts_full_world W0 C *)
      (*     ==∗ *)
      (*     (* *)
      (*       if the user wants to share capabilities pointing in the callee's frame, *)
      (*       we need to relinquish the points-to predicates. *)
      (*       Which means that the user needs to show safe-to-share. *)
      (*      *) *)
      (*     interp W1 C (WCap RWL Local (a_stk ^+ 4)%a e_stk (a_stk ^+ 4)%a) *)
      (*     (* we forbid the user to share access to caller_save_area *) *)
      (*     ∗ [[ a_stk , (a_stk ^+4)%a ]] ↦ₐ [[ stk_caller_save_area ]] *)
      (*     ∗ region W1 C ∗ sts_full_world W1 C) *)
          )%I
    in


    is_arg_rmap arg_rmap ->
    dom rmap = all_registers_s ∖ ((dom arg_rmap) ∪ {[ PC ; cgp ; cra ; csp ; cs0 ; cs1 ; ct1 ]} ) ->
    ↑N ⊆ E →

    ( na_inv logrel_nais N (switcher_inv b_switcher e_switcher a_switcher_cc ot_switcher)
       ∗ PRE_COND_SWITCHER
       ∗ ▷ POST_COND_SWITCHER )
    ⊢ (WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }})%I.
  Proof.
    intros Hwct1_caller Hstk_caller_save_area Hstk_caller_frm_pre Hstk_pre_jmp
      HPRE W1 HPOST Harg_map Hrmap HNE; subst HPRE HPOST.
    iIntros "[ #Hinv_switcher
              [ (Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & #Hinterp_ct1 & Hcs0 & Hcs1
                & Hargmap & Hrmap & Hstk & Hregion & Hworld)
              Hφ
              ] ]".

    (* ------------------------------------------------ *)
    (* -------- Prepare resources for the proof ------- *)
    (* ------------------------------------------------ *)

    (* --- Extract the code from the invariant --- *)
    iMod (na_inv_acc with "Hinv_switcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    rewrite /switcher_inv.
    iDestruct "Hswitcher_inv"
      as (b_tstk e_tstk a_tstk tstk_prev tstk_next)
           "(>Hmtdc & >%Hbounds & >Hcode & >Hb_switcher & >Htstk_prev & >Htstk & Hstack_full & Hstack_frag_next & #Hp_ot_switcher)".
    codefrag_facts "Hcode".
    rename H into Hcont_switcher_region; clear H0.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hinv_switcher" as hinv_switcher.
    iHide "Hφ" as hφ.

    (* --- Extract scratch registers ct2 ctp --- *)
    (* TODO *)
    assert (exists wct2, rmap !! ct2 = Some wct2) as [wct2 Hwct2].
    { admit. }
    iDestruct (big_sepM_delete _ _ ct2 with "Hrmap") as "[Hct2 Hrmap]"; first by simplify_map_eq.
    assert (exists wctp, rmap !! ctp = Some wctp) as [wctp Hwctp].
    { admit. }
    iDestruct (big_sepM_delete _ _ ctp with "Hrmap") as "[Hctp Hrmap]"; first by simplify_map_eq.
    (* ------------------------------------------------ *)
    (* ----- Start the proof of the switcher here ----- *)
    (* ------------------------------------------------ *)

    (* --- First, we destruct cases where it will quickly fail ---  *)
    destruct (decide ((a_stk ^+ 4) < e_stk))%a as [Hstk_ae|Hstk_ae]; cycle 1.
    { admit. (* will fail in the next upcoming instructions *) }
    destruct (decide (b_stk <= a_stk))%a as [Hstk_ba|Hstk_ba]; cycle 1.
    { admit. (* will fail in the next upcoming instructions *) }

    iAssert (⌜ exists stk_wa stk_wa1 stk_wa2 stk_wa3 stk_mem',
                 (stk_mem = stk_wa :: stk_wa1 :: stk_wa2 :: stk_wa3 :: stk_mem')⌝)%I
      as %(stk_wa & stk_wa1 & stk_wa2 & stk_wa3 & stk_mem' & ->).
    { iEval (rewrite /region_pointsto) in "Hstk".
      iDestruct (big_sepL2_length with "Hstk") as %Hlen_stk.
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
    { admit. (* will fail in the next upcoming instructions *) }
    destruct (decide (b_tstk <= a_tstk))%a as [Htstk_ba|Htstk_ba]; cycle 1.
    { admit. (* will fail in the next upcoming instructions *) }
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
    { admit. }
    iNext ; iIntros "(HPC & Hcsp & Hcs0 & Hcs1 & Hcode & Hstk)".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.


    (* TODO from here *)
    (* revoke the world: all temporary invariant will be "frozen" *)



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
    iSpecialize ("Hot_switcher_agree" $! (W0,C,WSealable w_entry_point)).

    (* Load cs0 cs0 *)
    iInstr "Hcode".
    iEval (cbn) in "Hcs0".


    rewrite /ot_switcher_prop.
    iEval (rewrite /safeC /=) in "Hot_switcher_agree".
    iRewrite "Hot_switcher_agree" in "HPct1".
    iDestruct "HPct1" as (b_tbl e_tbl a_tbl Heq_entry_point Hatbl Hbtbl Hbtbl1)
                           "(#Hinterp_tbl & #Hrel_btbl & #Hrel_btbl1 & Hrel_atbl)".
    iClear "Hot_switcher_agree Hp_ot_switcher".
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
              with (finz.seq_between a_tbl e_tbl) by admit.
    rewrite finz_seq_between_cons; last solve_addr.
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
    { solve_addr. (* TODO solve_pure *) }
    rewrite Heq_entry_point.



    (* Load cs0 ct1 *)
    iDestruct (region_open_perm with "[$Hrel_atbl $Hregion $Hworld]")
      as (watbl) "(Hregion & Hworld & Hstd_atbl & Ha_tbl & _ & HmonoReq_atbl & #HPatbl)"
    ; first done.
    iInstr "Hcode".
    { split ; first solve_pure; last solve_addr. }
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
    { split ; first solve_pure; last solve_addr. }
    iDestruct "HPbtbl" as (bpcc epcc apcc) "[%Hwbtbl #Hinterp_wbtbl]".
    cbn in Hwbtbl ; subst wbtbl.
    iEval (cbn) in "Hcra".
    iDestruct (region_close_perm
                with "[$Hregion $Hstd_btbl $Ha_tbl $HmonoReq_btbl $Hrel_btbl]")
                as "Hregion"; eauto.
    { iSplit; auto. iNext; eauto. }

    (* Lea ct1 1%Z *)
    iInstr "Hcode".
    { transitivity (Some (b_tbl ^+ 1)%a); solve_addr. }

    (* Load cgp ct1 *)
    iDestruct (region_open_perm with "[$Hrel_btbl1 $Hregion $Hworld]")
      as (wbtbl1) "(Hregion & Hworld & Hstd_btbl1 & Ha_tbl & _ & HmonoReq_btbl1 & #HPbtbl1)"
    ; first done.
    iInstr "Hcode".
    { split ; first solve_pure; last solve_addr. }
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

    iEval (cbn) in "Hcgp".
    iEval (cbn) in "Hinterp_wbtbl".
    iEval (cbn) in "Hinterp_wbtbl1".

    iAssert ([∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ interp W1 C w)%I with "[Hrmap']" as "Hrmap'".
    {
      iApply (big_sepM_impl with "[$]").
      iModIntro ; iIntros (r w Hr) "[$ ->]".
      iEval (rewrite !fixpoint_interp1_eq) ; done.
    }
    (* TODO that's the interesting part !!!!

      - show that rmap' is safe to share
      - show that cra is safe to share
      - show that csp is safe to share
      - close the switcher's invariant
      - how do we keep track of Ha1_tstk ??? Frozen, then we revoke it?
     *)


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
