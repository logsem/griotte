From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel.
From cap_machine.proofmode Require Import tactics_helpers map_simpl solve_pure.
From cap_machine Require Export iris_extra addr_reg_sample contiguous.

Section Mclear.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  (* -------------------------------------- MCLEAR ----------------------------------- *)
   (* the following macro clears the region of memory a capability govers over. a denotes
     the list of adresses containing the instructions for the clear. |a| = 23 *)

  Definition mclear_off_end := 10%Z.
  Definition mclear_off_iter := 2%Z.

  (* first we will define the list of Words making up the mclear macro *)
  Definition mclear_instrs r_stk :=
    [ move_r r_t4 r_stk;
      getb r_t1 r_t4;
      geta r_t2 r_t4;
      sub_r_r r_t2 r_t1 r_t2;
      lea_r r_t4 r_t2;
      gete r_t5 r_t4;
      sub_r_z r_t5 r_t5 1; (* we subtract the bound by one so that the lt check becomes a le check *)
      move_r r_t2 PC;
      lea_z r_t2 mclear_off_end; (* offset to "end" *)
      move_r r_t3 PC;
      lea_z r_t3 mclear_off_iter; (* offset to "iter" *)
    (* iter: *)
      lt_r_r r_t6 r_t5 r_t1;
      jnz r_t2 r_t6;
      store_z r_t4 0;
      lea_z r_t4 1;
      add_r_z r_t1 r_t1 1;
      jmp r_t3;
    (* end: *)
      move_z r_t4 0;
      move_z r_t1 0;
      move_z r_t2 0;
      move_z r_t3 0;
      move_z r_t5 0;
      move_z r_t6 0].

  (* Next we define mclear in memory, using a list of addresses of size 23 *)
  Definition mclear (a : list Addr) (r : RegName) : iProp Σ :=
    if ((length a) =? (length (mclear_instrs r)))%nat then
      ([∗ list] k↦a_i;w_i ∈ a;(mclear_instrs r), a_i ↦ₐ w_i)%I
    else
      False%I.

  Lemma mclear_iter_spec (a1 a2 a3 a4 a5 a6 b_r e_r a_r (* e_r' *) : Addr) ws (z : nat)
        p b e rt rt1 rt2 rt3 rt4 rt5 a_end (p_r : Perm) φ :
        isCorrectPC (WCap p b e a1)
      ∧ isCorrectPC (WCap p b e a2)
      ∧ isCorrectPC (WCap p b e a3)
      ∧ isCorrectPC (WCap p b e a4)
      ∧ isCorrectPC (WCap p b e a5)
      ∧ isCorrectPC (WCap p b e a6) →
        (a1 + 1)%a = Some a2
      ∧ (a2 + 1)%a = Some a3
      ∧ (a3 + 1)%a = Some a4
      ∧ (a4 + 1)%a = Some a5
      ∧ (a5 + 1)%a = Some a6 →
        ((b_r + z < e_r)%Z → withinBounds b_r e_r a_r = true) →
        writeAllowed p_r = true →
        (* (e_r + 1)%a = Some e_r' → *)
        (b_r + z)%a = Some a_r →
      ([[a_r,e_r]] ↦ₐ [[ws]]
     ∗ ▷ PC ↦ᵣ WCap p b e a1
     ∗ ▷ rt ↦ᵣ WCap p_r b_r e_r a_r
     ∗ ▷ rt1 ↦ᵣ WInt (b_r + z)%Z
     ∗ ▷ rt2 ↦ᵣ WInt ((z_of e_r) - 1)%Z
     ∗ ▷ (∃ w, rt3 ↦ᵣ w)
     ∗ ▷ rt4 ↦ᵣ WCap p b e a_end
     ∗ ▷ rt5 ↦ᵣ WCap p b e a1
     ∗ ▷ ([∗ list] a_i;w_i ∈ [a1;a2;a3;a4;a5;a6];[lt_r_r rt3 rt2 rt1;
                                                  jnz rt4 rt3;
                                                  store_z rt 0;
                                                  lea_z rt 1;
                                                  add_r_z rt1 rt1 1;
                                                  jmp rt5], a_i ↦ₐ w_i)
     ∗ ▷ (PC ↦ᵣ updatePcPerm (WCap p b e a_end)
             ∗ [[ a_r , e_r ]] ↦ₐ [[ region_addrs_zeroes a_r e_r ]]
             ∗ (∃ a_r, rt ↦ᵣ WCap p_r b_r e_r a_r)
             ∗ rt5 ↦ᵣ WCap p b e a1
             ∗ a3 ↦ₐ store_z rt 0
             ∗ a4 ↦ₐ lea_z rt 1
             ∗ a5 ↦ₐ add_r_z rt1 rt1 1
             ∗ a6 ↦ₐ jmp rt5
             ∗ a1 ↦ₐ lt_r_r rt3 rt2 rt1
             ∗ rt2 ↦ᵣ WInt ((z_of e_r) - 1)%Z
             ∗ (∃ z, rt1 ↦ᵣ WInt (b_r + z)%Z)
             ∗ a2 ↦ₐ jnz rt4 rt3
             ∗ rt4 ↦ᵣ WCap p b e a_end
             ∗ rt3 ↦ᵣ WInt 1%Z
              -∗ WP Seq (Instr Executable) {{ φ }})
     ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    iIntros (Hvpc Hnext Hwb Hwa (* Her' *) Hprogress)
            "(Hbe & >HPC & >Hrt & >Hr_t1 & >Hr_t2 & >Hr_t3 & >Hr_t4 & >Hr_t5 & >Hprog & Hφ)".
    iRevert (Hwb Hprogress).
    iLöb as "IH" forall (a_r ws z).
    iIntros (Hwb Hprogress).
    iDestruct "Hr_t3" as (w) "Hr_t3".
    destruct Hvpc as (Hvpc1 & Hvpc2 & Hvpc3 & Hvpc4 & Hvpc5 & Hvpc6).
    destruct Hnext as (Hnext1 & Hnext2 & Hnext3 & Hnext4 & Hnext5).
    iAssert (⌜rt1 ≠ PC⌝)%I as %Hne1.
    { destruct (reg_eq_dec rt1 PC); auto. rewrite e0.
        by iDestruct (regname_dupl_false with "Hr_t1 HPC") as "Hfalse". }
    iAssert (⌜rt3 ≠ PC⌝)%I as %Hne2.
    { destruct (reg_eq_dec rt3 PC); auto. rewrite e0.
        by iDestruct (regname_dupl_false with "Hr_t3 HPC") as "Hfalse". }
    iAssert (⌜rt ≠ PC⌝)%I as %Hne3.
    { destruct (reg_eq_dec rt PC); auto. rewrite e0.
        by iDestruct (regname_dupl_false with "Hrt HPC") as "Hfalse". }
    iAssert (⌜rt2 ≠ rt3⌝)%I as %Hne4.
    { destruct (reg_eq_dec rt2 rt3); auto. rewrite e0.
        by iDestruct (regname_dupl_false with "Hr_t2 Hr_t3") as "Hfalse". }
    iAssert (⌜rt1 ≠ rt3⌝)%I as %Hne5.
    { destruct (reg_eq_dec rt1 rt3); auto. rewrite e0.
        by iDestruct (regname_dupl_false with "Hr_t1 Hr_t3") as "Hfalse". }
    (* lt rt3 rt2 rt1 *)
    iDestruct "Hprog" as "[Hi Hprog]".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_binop_success_r_r _ rt3 _ _ _ a1 _ _ _ rt2 _ rt1 _ _
      with "[Hi HPC Hr_t3 Hr_t1 Hr_t2]"); [apply decode_encode_instrW_inv | | | ..]; eauto.
    iFrame.
    iEpilogue "(HPC & Ha1 & Hr_t2 & Hr_t1 & Hr_t3)".
    rewrite /region_pointsto /finz.seq_between.
    destruct (Z.le_dec (b_r + z) (e_r - 1))%Z; simpl.
    - assert (Z.b2z (e_r - 1 <? b_r + z)%Z = 0%Z) as Heq0.
      { rewrite /Z.b2z. destruct (e_r - 1 <? b_r + z)%Z eqn:HH; auto.
        apply Z.ltb_lt in HH. lia. }
      rewrite Heq0.
      (* jnz rt4 rt3 *)
      iDestruct "Hprog" as "[Hi Hprog]".
      iApply (wp_bind (fill [SeqCtx])).
      iApply (wp_jnz_success_next _ rt4 rt3 _ _ _ a2 a3 with "[HPC Hi Hr_t3 Hr_t4]");
        first apply decode_encode_instrW_inv; eauto.
      iFrame. iEpilogue "(HPC & Ha2 & Hr_t4 & Hr_t3)".
      (* store rt 0 *)
      rewrite/ withinBounds in Hwb.
      apply andb_prop in Hwb as [Hwb_b%Z.leb_le Hwb_e%Z.ltb_lt].
      rewrite {1}finz_dist_S /=.
      destruct ws as [| w1 ws]; simpl; [by iApply bi.False_elim|].
      iDestruct "Hbe" as "[Ha_r Hbe]".
      iDestruct "Hprog" as "[Hi Hprog]".
      iApply (wp_bind (fill [SeqCtx])).
      iApply (wp_store_success_z _ _ _ _  a3 a4 _ rt 0 _ p_r b_r e_r a_r with "[HPC Hi Hrt Ha_r]"); first apply decode_encode_instrW_inv; eauto.
      { rewrite /withinBounds andb_true_iff; split;[auto|].
          by apply Z.leb_le. by apply Z.ltb_lt. }
      iFrame. iEpilogue "(HPC & Ha3 & Hrt & Ha_r)".
      (* lea rt 1 *)
      assert (∃ a_r', (a_r + 1)%a = Some a_r') as [a_r' Ha_r'].
      { apply addr_next_lt with e_r. apply incr_addr_of_z_i in Hprogress. lia. }
      iDestruct "Hprog" as "[Hi Hprog]".
      iApply (wp_bind (fill [SeqCtx])).
      iApply (wp_lea_success_z _ _ _ _ a4 a5 _ rt p_r _ _ a_r 1 a_r' with "[HPC Hi Hrt]"); first apply decode_encode_instrW_inv; eauto.
      { destruct p_r; auto. }
      iFrame. iEpilogue "(HPC & Ha4 & Hrt)".
      (* add rt1 rt1 1 *)
      iDestruct "Hprog" as "[Hi Hprog]".
      iApply (wp_bind (fill [SeqCtx])).
      iApply (wp_binop_success_dst_z _ rt1 _ _ _ a5 _ _ _ with "[HPC Hi Hr_t1]"); try iFrame;
        [ apply decode_encode_instrW_inv | | |..]; eauto.
      iEpilogue "(HPC & Ha5 & Hr_t1)".
      (* jmp rt5 *)
      iDestruct "Hprog" as "[Hi _]".
      iApply (wp_bind (fill [SeqCtx])).
      iApply (wp_jmp_success _ _ _ _ a6 with "[HPC Hi Hr_t5]");
        first apply decode_encode_instrW_inv; eauto.
      iFrame. iEpilogue "(HPC & Ha6 & Hr_t5)".
      iApply ("IH" $! a_r' ws (z + 1)%nat with
                  "[Hbe] [HPC] [Hrt] [Hr_t1] [Hr_t2] [Hr_t3] [Hr_t4] [Hr_t5] [Ha1 Ha2 Ha3 Ha4 Ha5 Ha6] [Hφ Ha_r]")
      ; iFrame. all: auto.
      + by rewrite (addr_incr_eq Ha_r').
      + assert (updatePcPerm (WCap p b e a1) = (WCap p b e a1)).
        { rewrite /updatePcPerm. destruct p; auto.
          inversion Hvpc1; destruct H4 as [Hc | Hc ]; inversion Hc. }
        rewrite H. iFrame.
      + cbn. assert (b_r + z + 1 = b_r + (z + 1)%nat)%Z as ->;[lia|]. iFrame.
      + iNext.
        iIntros "(HPC & Hregion & Hrt & Hrt5 & Ha3 & Ha4 & Ha5 & Ha6 & Ha1 & Hrt2 & Hrt1 & Ha2 & Hrt4 & Hrt3)".
        iApply "Hφ".
        iFrame.
        rewrite /region_addrs_zeroes.
        rewrite (finz_dist_S a_r e_r) //= (_: (a_r^+1)%a = a_r'); [| solve_addr].
        iFrame.
      + iPureIntro. intro.
        rewrite andb_true_iff -Zle_is_le_bool -Zlt_is_lt_bool. solve_addr.
      + iPureIntro. solve_addr.
      + solve_addr.
    - assert (Z.b2z (e_r - 1 <? b_r + z)%Z = 1%Z) as Heq0.
      { rewrite /Z.b2z. destruct (e_r - 1 <? b_r + z)%Z eqn:HH; auto.
        apply Z.ltb_nlt in HH. lia. }
      rewrite Heq0.
      assert (e_r <= a_r)%Z by solve_addr.
      (* destruct (Z.le_dec a_r e_r). *)
      rewrite finz_dist_0 //=.
      destruct ws;[|by iApply bi.False_elim].
      (* jnz *)
      iDestruct "Hprog" as "[Hi Hprog]".
      iApply (wp_bind (fill [SeqCtx])).
      iApply (wp_jnz_success_jmp _ rt4 rt3 _ _ _ a2 _ _ (WInt 1%Z) with "[HPC Hi Hr_t3 Hr_t4]"); first apply decode_encode_instrW_inv; eauto.
      iFrame. iEpilogue "(HPC & Ha2 & Hr_t4 & Hr_t3)".
      iApply "Hφ". iDestruct "Hprog" as "(Ha3 & Ha4 & Ha5 & Ha6 & _)".
      rewrite /region_addrs_zeroes finz_dist_0 //=. iFrame.
  Qed.

  Lemma mclear_spec (a : list Addr) (r : RegName)
        (a_first a6' a_end : Addr) p b e p_r (b_r e_r a_r : Addr) a'
        w1 w2 w3 w4 w5 w6 ws φ :
    contiguous_between a a_first a' →
    (* We will assume that we are not trying to clear memory in a *)
    r ≠ PC ∧ writeAllowed p_r = true →
    (a !! 7 = Some a6' ∧ (a6' + 10)%a = Some a_end ∧ a !! 17 = Some a_end) →

    isCorrectPC_range p b e a_first a' →

    (* We will also assume the region to clear is non empty *)
    (b_r ≤ e_r)%Z →

     (mclear a r
    ∗ ▷ PC ↦ᵣ WCap p b e a_first
    ∗ ▷ r ↦ᵣ WCap p_r b_r e_r a_r
    ∗ ▷ r_t4 ↦ᵣ w4
    ∗ ▷ r_t1 ↦ᵣ w1
    ∗ ▷ r_t2 ↦ᵣ w2
    ∗ ▷ r_t3 ↦ᵣ w3
    ∗ ▷ r_t5 ↦ᵣ w5
    ∗ ▷ r_t6 ↦ᵣ w6
    ∗ ▷ ([[ b_r , e_r ]] ↦ₐ [[ ws ]])
    ∗ ▷ (PC ↦ᵣ WCap p b e a'
            ∗ r_t1 ↦ᵣ WInt 0%Z
            ∗ r_t2 ↦ᵣ WInt 0%Z
            ∗ r_t3 ↦ᵣ WInt 0%Z
            ∗ r_t4 ↦ᵣ WInt 0%Z
            ∗ r_t5 ↦ᵣ WInt 0%Z
            ∗ r_t6 ↦ᵣ WInt 0%Z
            ∗ r ↦ᵣ WCap p_r b_r e_r a_r
            ∗ [[ b_r , e_r ]] ↦ₐ [[region_addrs_zeroes b_r e_r]]
            ∗ mclear a r -∗
            WP Seq (Instr Executable) {{ φ }})
    ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    iIntros (Hnext [Hne Hwa] Hjnz_off Hvpc Hle)
            "(Hmclear & >HPC & >Hr & >Hr_t4 & >Hr_t1 & >Hr_t2 & >Hr_t3 & >Hr_t5 & >Hr_t6 & >Hregion & Hφ)".
    iAssert (⌜((length a) =? (length (mclear_instrs r)) = true)%nat⌝)%I as %Hlen.
    { destruct (((length a) =? (length (mclear_instrs r)))%nat) eqn:Hlen; auto.
      rewrite /mclear Hlen. by iApply bi.False_elim. }
    rewrite /mclear Hlen /mclear_instrs; simpl in Hlen. apply Nat.eqb_eq in Hlen.
    destruct a as [| a1 a]; inversion Hlen; simpl.
    move: (contiguous_between_cons_inv_first _ _ _ _ Hnext).
    match goal with |- (?a = _) -> _ => intro; subst a end.
    iPrologue "Hmclear".
    iApply (wp_move_success_reg _ _ _ _ a_first _ _ r_t4 _ r with "[HPC Hr Hr_t4 Hi]");
      first apply decode_encode_instrW_inv; first iCorrectPC a_first a'; eauto.
    { iContiguous_next Hnext 0. }
    iFrame. iEpilogue "(HPC & Ha_first & Hr_t4 & Hr)".
    (* getb r_t1 r_t4 *)
    iPrologue "Hprog".
    iApply (wp_Get_success _ _ r_t1 r_t4 _ _ _ a0 with "[$HPC $Hi $Hr_t1 $Hr_t4]");
      first eapply decode_encode_instrW_inv; first eauto; first iCorrectPC a_first a'; eauto.
    { iContiguous_next Hnext 1. }
    iFrame. iEpilogue "(HPC & Ha0 & Hr_t4 & Hr_t1)".
    destruct (reg_eq_dec PC r_t4) as [Hcontr | _]; [inversion Hcontr|].
    iCombine "Ha0 Ha_first" as "Hprog_done".
    (* geta r_t2 r_t4 *)
    iPrologue "Hprog".
    iApply (wp_Get_success _ _ r_t2 r_t4 _ _ _ a1 with "[HPC Hi Hr_t2 Hr_t4]");
      first eapply decode_encode_instrW_inv; first eapply is_Get_GetA ; first iCorrectPC a_first a'; auto.
    { iContiguous_next Hnext 2. }
    2: iFrame. auto. iEpilogue "(HPC & Ha1 & Hr_t4 & Hr_t2)".
    destruct (reg_eq_dec PC r_t4) as [Hcontr | _]; [inversion Hcontr|].
    iCombine "Ha1 Hprog_done" as "Hprog_done".
    (* sub r_t2 r_t1 r_t2 *)
    iPrologue "Hprog".
    (* destruct b_r eqn:Hb_r. *)
    iApply (wp_binop_success_r_dst _ _ _ _ _ a2 _ _ r_t1 with "[HPC Hi Hr_t1 Hr_t2]"); try iFrame;
      [ apply decode_encode_instrW_inv | | |..]; eauto. 2: by iCorrectPC a_first a'.
    assert ((a2 + 1) = Some a3)%a as ->. { iContiguous_next Hnext 3. } by eauto.
    iEpilogue "(HPC & Ha2 & Hr_t1 & Hr_t2)".
    iCombine "Ha2 Hprog_done" as "Hprog_done".
    (* lea r_t4 r_t2 *)
    iPrologue "Hprog".
    assert (a_r + (b_r - a_r) = b_r)%Z as Haddmin; first lia.
    assert ((a_r + (b_r - a_r))%a = Some b_r) as Ha_rb_r by solve_addr.
    iApply (wp_lea_success_reg _ _ _ _ a3 a4 _ r_t4 r_t2 p_r _ _ a_r (b_r - a_r) with "[HPC Hi Hr_t4 Hr_t2]");
      first apply decode_encode_instrW_inv; first iCorrectPC a_first a'; eauto.
    { iContiguous_next Hnext 4. }
    { destruct p_r; inversion Hwa; auto. }
    by iFrame. iEpilogue "(HPC & Ha3 & Hr_t2 & Hr_t4)".
    iCombine "Ha3 Hprog_done" as "Hprog_done".
    (* gete r_t2 r_t4 *)
    iPrologue "Hprog".
    iApply (wp_Get_success _ _ r_t5 r_t4 _ _ _ a4 with "[HPC Hi Hr_t5 Hr_t4]"); try iFrame;
      first apply decode_encode_instrW_inv; first eauto; first iCorrectPC a_first a'; eauto.
    { iContiguous_next Hnext 5. }
    destruct (reg_eq_dec PC r_t4) as [Hcontr | _]; [inversion Hcontr|].
    destruct (reg_eq_dec r_t4 r_t5) as [Hcontr | _]; [inversion Hcontr|].
    iEpilogue "(HPC & Ha4 & Hr_t4 & Hr_t5)".
    iCombine "Ha4 Hprog_done" as "Hprog_done".
    (* sub r_t5 r_t5 1 *)
    iPrologue "Hprog".
    iApply (wp_binop_success_dst_z with "[$HPC $Hi Hr_t5]");
      [apply decode_encode_instrW_inv| | |iCorrectPC a_first a'|..]; eauto.
    assert ((a5 + 1)%a = Some a6) as ->. { iContiguous_next Hnext 6. } eauto.
    iEpilogue "(HPC & Ha5 & Hr_t5)".
    iCombine "Ha5 Hprog_done" as "Hprog_done".
    (* move r_t2 PC *)
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC _ _ _ _ a6 a7 _ r_t2 with "[HPC Hi Hr_t2]");
      first apply decode_encode_instrW_inv; first iCorrectPC a_first a'; eauto.
    { iContiguous_next Hnext 7. }
    iFrame. iEpilogue "(HPC & Ha6 & Hr_t2)".
    iCombine "Ha6 Hprog_done" as "Hprog_done".
    (* lea r_t2 mclear_off_end *)
    iPrologue "Hprog".
    assert (p ≠ E) as Hpne.
    { have: (isCorrectPC (WCap p b e a_first)).
      { apply Hvpc. eapply contiguous_between_middle_bounds'; eauto. constructor. }
      inversion 1; subst.
      destruct H15 as [? | ? ]; subst; auto. }
    iApply (wp_lea_success_z _ _ _ _ a7 a8 _ r_t2 p _ _ a6 10 a_end with "[HPC Hi Hr_t2]");
      first apply decode_encode_instrW_inv; first iCorrectPC a_first a'; auto.
    { iContiguous_next Hnext 8. }
    { destruct Hjnz_off as (Ha7' & Hmclear_off_end & Ha_end). simpl in Ha7'. congruence. }
    iFrame. iEpilogue "(HPC & Ha7 & Hr_t2)".
    iCombine "Ha7 Hprog_done" as "Hprog_done".
    (* move r_t3 PC *)
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC _ _ _ _ a8 a9 _ r_t3 with "[HPC Hi Hr_t3]");
      first apply decode_encode_instrW_inv; first iCorrectPC a_first a'; auto.
    { iContiguous_next Hnext 9. }
    iFrame. iEpilogue "(HPC & Ha8 & Hr_t3)".
    iCombine "Ha8 Hprog_done" as "Hprog_done".
    (* lea r_t3 mclear_off_iter *)
    iPrologue "Hprog".
    iApply (wp_lea_success_z _ _ _ _ a9 a10 _ r_t3 p _ _ a8 2 a10 with "[HPC Hi Hr_t3]");
      first apply decode_encode_instrW_inv; first iCorrectPC a_first a'; auto.
    { iContiguous_next Hnext 10. }
    { assert (2 = 1 + 1)%Z as ->; auto.
      apply incr_addr_trans with a9. iContiguous_next Hnext 9.
      iContiguous_next Hnext 10. }
    iFrame. iEpilogue "(HPC & Ha9 & Hr_t3)".
    iCombine "Ha9 Hprog_done" as "Hprog_done".
    (* iter *)
    clear H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
    do 5 iPrologue_pre. clear H0 H1 H2 H3.
    iDestruct "Hprog" as "[Hi1 Hprog]".
    iDestruct "Hprog" as "[Hi2 Hprog]".
    iDestruct "Hprog" as "[Hi3 Hprog]".
    iDestruct "Hprog" as "[Hi4 Hprog]".
    iDestruct "Hprog" as "[Hi5 Hprog]".
    iDestruct "Hprog" as "[Hi6 Hprog]".
    iApply (mclear_iter_spec a10 a11 a12 a13 a14 a15 b_r e_r b_r _
                        0 p b e r_t4 r_t1 r_t5 r_t6 r_t2 r_t3 _ p_r
              with "[-]"); auto.
    - repeat apply conj; iCorrectPC a_first a'.
    - repeat split; solve [
        iContiguous_next Hnext 11; auto
      | iContiguous_next Hnext 12; auto
      | iContiguous_next Hnext 13; auto
      | iContiguous_next Hnext 14; auto
      | iContiguous_next Hnext 15; auto ].
    - (* rewrite Z.add_0_r. intros Hle. *)
      rewrite /withinBounds. intro.
      rewrite andb_true_iff Z.leb_le Z.ltb_lt. lia.
    - apply addr_add_0.
    - rewrite Z.add_0_r.
      iFrame.
      iSplitR; auto.
      iNext.
      iIntros "(HPC & Hbe & Hr_t4 & Hr_t3 & Ha11 & Ha12 & Ha13 & Ha14 &
      Ha9 & Hr_t5 & Hr_t1 & Ha10 & Hr_t2 & Hr_t6)".
      iCombine "Ha9 Ha10 Ha11 Ha12 Ha13 Ha14 Hprog_done" as "Hprog_done".
      iDestruct "Hr_t4" as (a_r0) "Hr_t4".
      iDestruct "Hr_t1" as (z0) "Hr_t1".
      iPrologue "Hprog".
      assert (a16 = a_end)%a as Ha16.
      { simpl in Hjnz_off.
        destruct Hjnz_off as (Ha16 & Ha16' & Hend).
        by inversion Hend.
      }
      destruct a as [| a17 a]; inversion Hlen.
      iApply (wp_move_success_z _ _ _ _ a16 a17 _ r_t4 _ 0 with "[HPC Hi Hr_t4]");
        first apply decode_encode_instrW_inv;
        first iCorrectPC a_first a'; auto.
      { iContiguous_next Hnext 17; auto. }
      { rewrite Ha16. destruct p; iFrame. contradiction. }
      iEpilogue "(HPC & Ha16 & Hr_t4)".
      (* move r_t1 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z _ _ _ _ a17 a18 _ r_t1 _ 0 with "[HPC Hi Hr_t1]");
        first apply decode_encode_instrW_inv;
        first iCorrectPC a_first a'; auto.
      { iContiguous_next Hnext 18. }
      iFrame. iEpilogue "(HPC & Ha17 & Hr_t1)".
      (* move r_t2 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z _ _ _ _ a18 a19 _ r_t2 _ 0 with "[HPC Hi Hr_t2]");
        first apply decode_encode_instrW_inv;
        first iCorrectPC a_first a'; auto.
      { iContiguous_next Hnext 19. }
      iFrame. iEpilogue "(HPC & Ha18 & Hr_t2)".
      (* move r_t3 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z _ _ _ _ a19 a20 _ r_t3 _ 0 with "[HPC Hi Hr_t3]");
        first apply decode_encode_instrW_inv;
        first iCorrectPC a_first a'; auto.
      { iContiguous_next Hnext 20. }
      iFrame. iEpilogue "(HPC & Ha19 & Hr_t3)".
      (* move r_t5 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z _ _ _ _ a20 a21 _ r_t5 _ 0 with "[HPC Hi Hr_t5]");
        first apply decode_encode_instrW_inv;
        first iCorrectPC a_first a'; auto.
      { iContiguous_next Hnext 21. }
      iFrame. iEpilogue "(HPC & Ha20 & Hr_t5)".
      (* move r_t6 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z _ _ _ _ a21 a' _ r_t6 _ 0 with "[HPC Hi Hr_t6]");
        first apply decode_encode_instrW_inv;
        first iCorrectPC a_first a'; auto.
      { eapply contiguous_between_last. eapply Hnext. reflexivity. }
      iFrame. iEpilogue "(HPC & Ha21 & Hr_t6)".
      iApply "Hφ".
      iDestruct "Hprog_done" as "(Ha_iter & Ha10 & Ha12 & Ha11 & Ha13 & Ha14 & Ha15 & Ha8 & Ha7
      & Ha6 & Ha5 & Ha4 & Ha3 & Ha2 & Ha1 & Ha0 & Ha_first)".
      iFrame.
  Qed.



End Mclear.
