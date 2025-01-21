From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel addr_reg_sample fundamental rules proofmode.
From cap_machine Require Import multiple_updates region_invariants_frozen.

(* A toy malloc implementation *)

(* The routine is initially provided a capability to a contiguous range of
   memory. It implements a bump-pointer allocator, where all memory before the
   pointer of the capability has been allocated, and all memory after is free.
   Allocating corresponds to increasing the pointer and returning the
   corresponding sub-slice.

   There is no free: when all the available memory has been allocated, the
   routine cannot allocate new memory and will fail instead.

   This is obviously not very realistic, but is good enough for our simple case
   studies. *)

Section SimpleMalloc.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ}
      {sealsg: sealStoreG Σ}
      {nainv: logrel_na_invs Σ}
      {MP: MachineParameters}
  .

  Definition malloc_subroutine_instrs' (offset: Z) :=
    encodeInstrsW [
     Lt r_t3 0 r_t1;
     Mov r_t2 PC;
     Lea r_t2 4;
     Jnz r_t2 r_t3;
     Fail;
     Mov r_t2 PC;
     Lea r_t2 offset;
     Load r_t2 r_t2;
     GetA r_t3 r_t2;
     Lea r_t2 r_t1;
     GetA r_t1 r_t2;
     Mov r_t4 r_t2;
     Subseg r_t4 r_t3 r_t1;
     Sub r_t3 r_t3 r_t1;
     Lea r_t4 r_t3;
     Mov r_t3 r_t2;
     Sub r_t1 0%Z r_t1;
     Lea r_t3 r_t1;
     GetB r_t1 r_t3;
     Lea r_t3 r_t1;
     Store r_t3 r_t2;
     Mov r_t1 r_t4;
     Mov r_t2 0%Z;
     Mov r_t3 0%Z;
     Mov r_t4 0%Z;
     Jmp r_t0].

  Definition malloc_subroutine_instrs_length : Z :=
    Eval cbv in (length (malloc_subroutine_instrs' 0%Z)).

  Definition malloc_subroutine_instrs :=
    malloc_subroutine_instrs' (malloc_subroutine_instrs_length - 5).

  Definition malloc_inv (b e : Addr) : iProp Σ :=
    (∃ b_m a_m,
       codefrag b malloc_subroutine_instrs
     ∗ ⌜(b + malloc_subroutine_instrs_length)%a = Some b_m⌝
     ∗ b_m ↦ₐ (WCap RWX Global b_m e a_m)
     ∗ [[a_m, e]] ↦ₐ [[ region_addrs_zeroes a_m e ]]
     ∗ ⌜(b_m < a_m)%a ∧ (a_m <= e)%a⌝)%I.

  Lemma simple_malloc_subroutine_spec (wsize: Word) (cont: Word) g b e rmap N E φ :
    dom rmap = all_registers_s ∖ {[ PC; r_t0; r_t1 ]} →
    ↑N ⊆ E →
    (  na_inv logrel_nais N (malloc_inv b e)
     ∗ na_own logrel_nais E
     ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w)
     ∗ r_t0 ↦ᵣ cont
     ∗ PC ↦ᵣ WCap RX g b e b
     ∗ r_t1 ↦ᵣ wsize
     ∗ ▷ ((na_own logrel_nais E
          ∗ [∗ map] r↦w ∈ <[r_t2 := WInt 0%Z]>
                         (<[r_t3 := WInt 0%Z]>
                         (<[r_t4 := WInt 0%Z]>
                          rmap)), r ↦ᵣ w)
          ∗ r_t0 ↦ᵣ cont
          ∗ PC ↦ᵣ updatePcPerm cont
          ∗ (∃ (ba ea : Addr) size,
            ⌜wsize = WInt size⌝
            ∗ ⌜(ba + size)%a = Some ea⌝
            ∗ r_t1 ↦ᵣ WCap RWX Global ba ea ba
            ∗ [[ba, ea]] ↦ₐ [[region_addrs_zeroes ba ea]])
          -∗ WP Seq (Instr Executable) {{ φ }}))
    ⊢ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}%I.
  Proof.
    iIntros (Hrmap_dom HN) "(#Hinv & Hna & Hrmap & Hr0 & HPC & Hr1 & Hφ)".
    iMod (na_inv_acc with "Hinv Hna") as "(>Hmalloc & Hna & Hinv_close)"; auto.
    rewrite /malloc_inv.
    iDestruct "Hmalloc" as (b_m a_m) "(Hprog & %Hbm & Hmemptr & Hmem & %Hbounds)".
    destruct Hbounds as [Hbm_am Ham_e].
    (* Get some registers *)
    assert (is_Some (rmap !! r_t2)) as [r2w Hr2w].
    { rewrite -elem_of_dom Hrmap_dom. set_solver. }
    assert (is_Some (rmap !! r_t3)) as [r3w Hr3w].
    { rewrite -elem_of_dom Hrmap_dom. set_solver. }
    assert (is_Some (rmap !! r_t4)) as [r4w Hr4w].
    { rewrite -elem_of_dom Hrmap_dom. set_solver. }
    iDestruct (big_sepM_delete _ _ r_t2 with "Hrmap") as "[Hr2 Hrmap]".
      eassumption.
    iDestruct (big_sepM_delete _ _ r_t3 with "Hrmap") as "[Hr3 Hrmap]".
      by rewrite lookup_delete_ne //.
    iDestruct (big_sepM_delete _ _ r_t4 with "Hrmap") as "[Hr4 Hrmap]".
      by rewrite !lookup_delete_ne //.

    codefrag_facts "Hprog".
    rewrite {2}/malloc_subroutine_instrs /malloc_subroutine_instrs'.
    unfold malloc_subroutine_instrs_length in Hbm.
    assert (SubBounds b e b (b ^+ length malloc_subroutine_instrs)%a) by solve_addr.
    destruct wsize as [size | [ | ] | ].
    2,3,4: iInstr "Hprog"; wp_end; eauto.
    do 3 iInstr "Hprog".

    (* we need to destruct on the cases for the size *)
    destruct (decide (0 < size)%Z) as [Hsize | Hsize].
    2: { (* the program will not jump, and go to the fail instruction *)
      rewrite (_: Z.b2z (0%nat <? size)%Z = 0); cycle 1.
      { apply Z.ltb_nlt in Hsize. rewrite Hsize //. }
      iInstr "Hprog". iInstr "Hprog". wp_end. eauto. }

    (* otherwise we continue malloc *)
    iInstr "Hprog". { apply Z.ltb_lt in Hsize. rewrite Hsize. auto. }
    iInstr "Hprog".
    iInstr "Hprog".
    rewrite (_: (b ^+ 26)%a = b_m); [| solve_addr].
    iInstr "Hprog". solve_pure_addr.
    iInstr "Hprog".
    (* Lea r_t1 r_t2 might fail. *)
    destruct (a_m + size)%a as [a_m'|] eqn:Ha_m'; cycle 1.
    { (* Failure case: no registered rule for that yet; do it the manual way *)
      iInstr_lookup "Hprog" as "Hi" "Hcont".
      iAssert ([∗ map] k↦x ∈ (∅:gmap RegName Word), k ↦ᵣ x)%I as "-#Hregs".
        by rewrite big_sepM_empty.
      iDestruct (big_sepM_insert with "[$Hregs $HPC]") as "-#Hregs".
        by apply lookup_empty.
      iDestruct (big_sepM_insert with "[$Hregs $Hr1]") as "-#Hregs".
        by rewrite lookup_insert_ne // lookup_empty.
      iDestruct (big_sepM_insert with "[$Hregs $Hr2]") as "-#Hregs".
        by rewrite !lookup_insert_ne // lookup_empty.
      wp_instr.
      iApply (wp_lea with "[$Hregs $Hi]"); [ | |done|..]; try solve_pure.
      { rewrite /regs_of /regs_of_argument !dom_insert_L dom_empty_L. set_solver-. }
      iNext. iIntros (regs' retv) "(Hspec & ? & ?)". iDestruct "Hspec" as %Hspec.
      destruct Hspec as [| | Hfail].
      { exfalso. rewrite lookup_insert in H1; inv H1.
        cbn in H3.
        rewrite lookup_insert_ne //= lookup_insert in H3; inv H3.
      }
      { exfalso. simplify_map_eq. }
      { cbn. iApply wp_pure_step_later; auto.
        iNext;iIntros "_".
        iApply wp_value. auto. }
    }

    do 3 iInstr "Hprog".
    (* Subseg r_t4 r_t3 r_t1 might fail. *)
    destruct (isWithin a_m a_m' b_m e) eqn:Ha_m'_within; cycle 1.
    { (* Failure case: manual mode. *)
      iInstr_lookup "Hprog" as "Hi" "Hcont".
      iAssert ([∗ map] k↦x ∈ (∅:gmap RegName Word), k ↦ᵣ x)%I as "-#Hregs".
        by rewrite big_sepM_empty.
      iDestruct (big_sepM_insert with "[$Hregs $HPC]") as "-#Hregs".
        by apply lookup_empty.
      iDestruct (big_sepM_insert with "[$Hregs $Hr1]") as "-#Hregs".
        by rewrite lookup_insert_ne // lookup_empty.
      iDestruct (big_sepM_insert with "[$Hregs $Hr3]") as "-#Hregs".
        by rewrite !lookup_insert_ne // lookup_empty.
      iDestruct (big_sepM_insert with "[$Hregs $Hr4]") as "-#Hregs".
        by rewrite !lookup_insert_ne // lookup_empty.
      wp_instr.
      iApply (wp_Subseg with "[$Hregs $Hi]"); [ | |done|..]; try solve_pure.
      { rewrite /regs_of /regs_of_argument !dom_insert_L dom_empty_L. set_solver-. }
      iNext. iIntros (regs' retv) "(Hspec & ? & ?)". iDestruct "Hspec" as %Hspec.
      destruct Hspec as [ | | Hfail].
      { exfalso. unfold addr_of_argument in *. simplify_map_eq.
        repeat match goal with H:_ |- _ => apply finz_of_z_eq_inv in H end; subst.
        rewrite lookup_insert in H1; inv H1.
        congruence. }
      { exfalso. simplify_map_eq. }
      { cbn. wp_pure. wp_end. auto. }
    }
    do 3 iInstr "Hprog". { transitivity (Some a_m); eauto. solve_addr. }
    do 3 iInstr "Hprog". { transitivity (Some 0%a); eauto. solve_addr. }
    do 2 iInstr "Hprog". { transitivity (Some b_m); eauto. solve_addr. }
    iInstr "Hprog". solve_pure_addr.
    iGo "Hprog".
    { by cbn. } (* TODO add a hint somewhere to take care of this proof obligation *)
    iGo "Hprog".
    (* continuation *)
    apply isWithin_implies in Ha_m'_within.
    rewrite (region_addrs_zeroes_split _ a_m') //; [|solve_addr].
    iDestruct (region_pointsto_split _ _ a_m' with "Hmem") as "[Hmem_fresh Hmem]".
    solve_addr. by rewrite length_replicate //.
    iDestruct ("Hinv_close" with "[Hprog Hmemptr Hmem $Hna]") as ">Hna".
    { iNext. iExists b_m, a_m'. iFrame. iSplitR. iPureIntro.
      by unfold malloc_subroutine_instrs_length. iPureIntro; solve_addr. }
    iApply (wp_wand with "[-]").
    { iApply "Hφ". iFrame.
      iDestruct (big_sepM_insert with "[$Hrmap $Hr4]") as "Hrmap".
      by rewrite lookup_delete. rewrite insert_delete_insert.
      iDestruct (big_sepM_insert with "[$Hrmap $Hr3]") as "Hrmap".
      by rewrite lookup_insert_ne // lookup_delete //.
      rewrite insert_commute // insert_delete_insert.
      iDestruct (big_sepM_insert with "[$Hrmap $Hr2]") as "Hrmap".
      by rewrite !lookup_insert_ne // lookup_delete //.
      rewrite (insert_commute _ r_t2 r_t4) // (insert_commute _ r_t2 r_t3) //.
      rewrite insert_delete_insert.
      rewrite (insert_commute _ r_t3 r_t2) // (insert_commute _ r_t4 r_t2) //.
      rewrite (insert_commute _ r_t4 r_t3) //. iFrame.
      iExists size. auto. }
    { auto. }
  Qed.

  (* TODO move in the appropriate section *)
  Lemma related_sts_pub_world_revoked_permanent W a :
    (std W) !! a = Some Revoked →
    related_sts_pub_world W (<s[a:=Permanent]s>W).
  Proof.
    intros Ha.
    rewrite /related_sts_pub_world /=.
    split;[|apply related_sts_pub_refl].
    rewrite /related_sts_pub. split.
    - rewrite dom_insert_L. set_solver.
    - intros i x y Hx Hy.
      destruct (decide (a = i)).
      + subst.
        rewrite Hx in Ha. inversion Ha.
        rewrite lookup_insert in Hy. inversion Hy.
        right with (Permanent);[|left]. constructor.
      + rewrite lookup_insert_ne in Hy;auto.
        rewrite Hx in Hy.
        inversion Hy; subst.
        left.
  Qed.

  Context {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}.
      (* {sealsg: sealStoreG Σ} *)


  Lemma update_region_revoked_perm E W l v φ `{∀ Wv, Persistent (φ Wv)} :
    (std W) !! l = Some Revoked ->
    future_priv_mono φ v -∗
    sts_full_world W -∗
    region W -∗
    l ↦ₐ v -∗ φ (W,v) -∗ rel l φ ={E}=∗ region (<s[l := Permanent ]s>W)
                             ∗ sts_full_world (<s[l := Permanent ]s>W).
  Proof.
    iIntros (Hrev) "#Hmono Hsts Hreg Hl #Hφ #Hrel".
    rewrite region_eq /region_def.
    iDestruct "Hreg" as (M Mρ) "(Hγrel & #Hdom & #Hdom' & Hpreds)".
    iDestruct "Hdom" as %Hdom. iDestruct "Hdom'" as %Hdom'.
    rewrite RELS_eq /RELS_def.
    rewrite rel_eq /rel_def REL_eq /REL_def. iDestruct "Hrel" as (γ) "[HREL Hsaved]".
    iDestruct (reg_in γrel (M) with "[$Hγrel $HREL]") as %HMeq.
    rewrite /region_map_def HMeq big_sepM_insert; [|by rewrite lookup_delete].
    iDestruct "Hpreds" as "[Hl' Hr]".
    iDestruct "Hl'" as (ρ Hl) "[Hstate Hresources]".
    iDestruct (sts_full_state_std with "Hsts Hstate") as %Hρ.
    rewrite Hrev in Hρ. inversion Hρ as [Hρrev]. subst.
    iMod (sts_update_std _ _ _ Permanent with "Hsts Hstate") as "[Hsts Hstate]".
    assert (related_sts_pub_world W (<s[l := Permanent ]s> W)) as Hrelated.
    { apply related_sts_pub_world_revoked_permanent; auto. }
    iDestruct (region_map_monotone with "Hr") as "Hr";[apply Hrelated|].
    pose proof (related_sts_pub_priv_world _ _ Hrelated) as Hrelated'.
    iDestruct ("Hmono" $! _ _ Hrelated' with "Hφ") as "Hφ'".
    assert (is_Some (M !! l)) as [x Hsome].
    { apply elem_of_dom. rewrite -Hdom. rewrite elem_of_dom. eauto. }
    iDestruct (region_map_delete_nonstatic with "Hr") as "Hr"; [intros m;intros Hcontr;congruence|].
    iDestruct (region_map_insert_nonmonostatic Permanent with "Hr") as "Hr";auto.
    iDestruct (big_sepM_delete _ _ l _ Hsome with "[Hl Hstate $Hr]") as "Hr".
    { iExists Permanent. iFrame. iSplitR;[iPureIntro;apply lookup_insert|].
      iExists φ. rewrite HMeq lookup_insert in Hsome.
      inversion Hsome. repeat (iSplit; auto). }
    rewrite /std_update /=. iFrame "Hsts".
    iExists M. iFrame. rewrite -HMeq. iFrame.
    iModIntro. iPureIntro.
    apply insert_id in Hsome. apply insert_id in Hl. rewrite -Hsome -Hl. split.
    - repeat rewrite dom_insert_L;rewrite Hdom;set_solver.
    - repeat rewrite dom_insert_L;rewrite Hdom';set_solver.
  Qed.

  Lemma extend_region_perm_sepL2_from_rev φ E W l1 l2 `{∀ Wv, Persistent (φ Wv)}:
    Forall (λ k, std W !! k = Some Revoked) l1 →
    sts_full_world W -∗ region W -∗
    ([∗ list] k;v ∈ l1;l2, k ↦ₐ v ∗ φ (W, v) ∗ future_priv_mono φ v ∗ rel k φ)

    ={E}=∗

    region (std_update_multiple W l1 Permanent)
    ∗ ([∗ list] k ∈ l1, rel k φ)
    ∗ sts_full_world (std_update_multiple W l1 Permanent).
  Proof.
    revert l2. induction l1.
    { cbn. intros. iIntros "? ? ?". iFrame. eauto. }
    { intros ? [? ?]%Forall_cons_1. iIntros "Hsts Hr Hl".
      iDestruct (big_sepL2_length with "Hl") as %Hlen.
      iDestruct (NoDup_of_sepL2_exclusive with "[] Hl") as %[Hal1 ND]%NoDup_cons.
      { iIntros (? ? ?) "(H1 & ? & ?) (H2 & ? & ?)".
        iApply (addr_dupl_false with "H1 H2"). }
      destruct l2; [ by inversion Hlen |].
      iDestruct (big_sepL2_cons with "Hl") as "[(Ha & Hφ & #Hf & #Hrel) Hl]".
      iMod (IHl1 with "Hsts Hr Hl") as "(Hr & ? & Hsts)"; auto.
      iMod (update_region_revoked_perm with "Hf Hsts Hr Ha [Hφ] Hrel") as "(? & ?)"; auto.
      { erewrite std_sta_update_multiple_lookup_same_i;auto. }
      { iApply ("Hf" with "[] Hφ"). iPureIntro.
        apply related_sts_pub_priv_world,related_sts_pub_update_multiple_perm. auto. }
      iFrame "∗ #". done.
    }
  Qed.

  (* dummy helper to move the later in front of the implication *)
  Lemma helper W' g x :
    (∀ (r0 : leibnizO Reg) (W'0 : prodO (leibnizO (STS_std_states Addr region_type))
                                           (leibnizO (STS_states * STS_rels))),
        future_world g W' W'0 → ▷ ((interp_expr interp r0) W'0) (updatePcPerm x)) -∗
    (▷ ∀ (r0 : leibnizO Reg) (W'0 : prodO (leibnizO (STS_std_states Addr region_type))
                                           (leibnizO (STS_states * STS_rels))),
          future_world g W' W'0 → ((interp_expr interp r0) W'0) (updatePcPerm x)).
  Proof.
    iIntros "Ha". iApply bi.later_forall. iIntros (r0). iApply bi.later_forall. iIntros (W'').
    iSpecialize ("Ha" $! r0 W'').
    destruct g;simpl.
    all: iIntros (Hfuture). all: iSpecialize ("Ha" $! Hfuture);iNext;iFrame.
  Qed.

  Ltac consider_next_reg r1 r2 :=
    destruct (decide (r1 = r2));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
  Ltac consider_next_reg' r1 r2 H :=
    destruct (decide (r1 = r2));[subst;rewrite lookup_insert in H;eauto|rewrite lookup_insert_ne
                                  in H;auto].

  Lemma simple_malloc_subroutine_valid W N g b e :
    Forall (λ a, W.1 !! a = Some Revoked) (finz.seq_between b e) →
    na_inv logrel_nais N (malloc_inv b e) -∗
    ([∗ list] a ∈ finz.seq_between b e, rel a (λne Wv, interp Wv.1 Wv.2)) -∗
    interp W (WCap E g b e b).
  Proof.
    iIntros (Hrev) "#Hmalloc #Hrels".
    rewrite fixpoint_interp1_eq /=.
    iModIntro. rewrite /enter_cond.
    iIntros (r W') "#Hrelated". iNext.
    iIntros "(#[% Hregs_valid] & Hregs & Hr & Hsts & Hown)".

    rewrite /registers_pointsto.
    destruct H with r_t0 as [w0 Hr0].
    destruct H with r_t1 as [w1 Hr1].
    iExtractList "Hregs" [PC;r_t0;r_t1] as ["HPC";"r_t0";"r_t1"].
    iApply (wp_wand with "[-]").
    iApply (simple_malloc_subroutine_spec with "[- $Hown $Hmalloc $Hregs $r_t0 $HPC $r_t1]");[|solve_ndisj|].
    3: { iSimpl. iIntros (v) "[H | ->]". iExact "H". iIntros (Hcontr); done. }
    { rewrite !dom_delete_L. apply regmap_full_dom in H as <-. set_solver. }
    unshelve iDestruct ("Hregs_valid" $! r_t0 _ _ Hr0) as "Hr0_valid";auto.
    iDestruct (jmp_or_fail_spec with "Hr0_valid") as "Hcont".
    destruct (decide (isCorrectPC (updatePcPerm w0))) as [HcorrectPC|HcorrectPC].
    2: { iNext. iIntros "(_ & _ & HPC & _)". iApply "Hcont". iFrame. iIntros (Hcontr). done. }
    iDestruct "Hcont" as (p' g' b' e' a' Heq) "Hcont"; simplify_eq.
    iDestruct (helper with "Hcont") as "Hcont'".
    iNext. iIntros "((Hown & Hregs) & Hr_t0 & HPC & Hres)".
    iDestruct "Hres" as (ba ea size Hsizeq Hsize) "[Hr_t1 Hbe]".

    assert (∃ l1 l2, finz.seq_between b e = l1 ++ finz.seq_between ba ea ++ l2) as [l1 [l2 Heqapp] ].
    { exists (finz.seq_between b ba),(finz.seq_between ea e).
      admit.
      (* rewrite -finz_seq_between_split. [|solve_addr]. *)
      (* rewrite -finz_seq_between_split;[auto|solve_addr]. *)
    }
     (* The following lemma can be derived from the fact that we own the resources for ba,ea, which means they cannot
       be in region W' *)
    iAssert (⌜Forall (λ k : Addr, std W' !! k = Some Revoked) (finz.seq_between ba ea)⌝)%I as %Hrev'.
    { rewrite Heqapp in Hrev. apply Forall_app in Hrev as [_ Hrev]. apply Forall_app in Hrev as [Hrev _].
      revert Hrev. rewrite !Forall_forall. iIntros (Hrev x Hin). specialize (Hrev x Hin).
      opose proof (related_sts_priv_world_std_sta_is_Some W W' x) as [ρ Hρ];[|eauto|].
      admit.
      rewrite /region_pointsto.
      iDestruct (big_sepL_elem_of _ _ x with "Hrels") as "Hrel".
      { rewrite Heqapp. apply elem_of_app. right. apply elem_of_app. by left. }
      apply elem_of_list_lookup in Hin as [k Hk].
      iDestruct (big_sepL2_extract_l with "Hbe") as "[_ Hb]";[eauto|].
      iDestruct "Hb" as (w') "Hw'".
      destruct ρ;auto. (* all the following will lead to duplicate resources for x *)
      - iDestruct (region_open_monotemp with "[$Hrel $Hr $Hsts]") as (v) "(_ & _ & _ & Hw & _)";[eauto|auto|..].
        iDestruct (addr_dupl_false with "Hw' Hw") as "?";auto.
      - iDestruct (region_open_perm with "[$Hrel $Hr $Hsts]") as (v) "(_ & _ & _ & Hw & _)";[eauto|auto|..].
        iDestruct (addr_dupl_false with "Hw' Hw") as "?";auto.
      - iMod (region_open_monostatic with "[$Hr $Hsts]") as "(_ & _ & ? & H & %Hindom)";[apply Hρ|..].
        rewrite /region_invariants_static.static_resources.
        apply elem_of_dom in Hindom as [? Hx].
        iDestruct (big_sepM_delete with "H") as "[H ?]";[apply Hx|].
        iDestruct "H" as (?) "[HH Hw]".
        iDestruct (addr_dupl_false with "Hw' Hw") as "?";auto.
    }
    (* Next is the interesting part of the spec: we must allocate the invariants making the malloced region valid *)
    iMod (extend_region_perm_sepL2_from_rev (λ Wv, interp Wv.1 Wv.2) _ _
                                            (finz.seq_between ba ea)
                                            (region_addrs_zeroes ba ea) with "Hsts Hr [Hbe]") as "(Hr & #Hvalid & Hsts)";auto.
    { rewrite Heqapp.
      iDestruct (big_sepL_app with "Hrels") as "[_ Hrels']".
      iDestruct (big_sepL_app with "Hrels'") as "[Hrels'' _]".
      iDestruct (big_sepL2_to_big_sepL_l _ _ (region_addrs_zeroes ba ea) with "Hrels''") as "Hrels3".
      { by rewrite /region_addrs_zeroes finz_seq_between_length length_replicate. }
      iDestruct (big_sepL2_sep with "[Hrels3 Hbe]") as "Hbe";[iFrame "Hbe"; iFrame "Hrels3"|].
      iApply (big_sepL2_mono with "Hbe").
      iIntros (k a'' w Hin1 Hin2) "(Ha & Hrel)". iFrame.
      apply region_addrs_zeroes_lookup in Hin2 as ->. iSplit.
      - by rewrite fixpoint_interp1_eq /=.
      - iModIntro. iIntros (W1 W2 Hrelated') "Hv /=". by rewrite !fixpoint_interp1_eq /=.
    }
    iInsertList "Hregs" [r_t1;r_t0;PC].
    set regs := <[PC:=updatePcPerm (WCap p' g' b' e' a')]>
                            (<[r_t0:=WCap p' g' b' e' a']>
                               (<[r_t1:=WCap RWX Global ba ea ba]>
                                  (<[r_t2:=WInt 0]> (<[r_t3:=WInt 0]> (<[r_t4:=WInt 0]> r))))).
    iDestruct ("Hcont'" $! regs with "[] [$Hown Hregs $Hr $Hsts]") as "Hcont''".
    { destruct g'; iPureIntro; apply related_sts_pub_priv_world
      ; apply related_sts_pub_update_multiple_perm;auto. }
    { rewrite /regs. iSplitR "Hregs".
      - iSplit.
        + iPureIntro. intros x. consider_next_reg x PC. consider_next_reg x r_t0. consider_next_reg x r_t1.
          consider_next_reg x r_t2. consider_next_reg x r_t3. consider_next_reg x r_t4.
        + iIntros (x wx Hne Hwx).
          consider_next_reg' x PC Hwx;[contradiction|].
          consider_next_reg' x r_t0 Hwx; [inv Hwx|].
          { iDestruct ("Hregs_valid" $! r_t0 with "[] []") as "Hr0_valid'";auto.
            iApply (interp_monotone with "[] Hr0_valid'").
            iPureIntro. apply related_sts_pub_update_multiple_perm;auto. }
          consider_next_reg' x r_t1 Hwx; [inv Hwx|].
          { rewrite !fixpoint_interp1_eq. iApply (big_sepL_mono with "Hvalid").
            iIntros (k y Hky) "Ha". iFrame. iPureIntro. simpl.
            rewrite std_sta_update_multiple_lookup_in_i;auto.
            apply elem_of_list_lookup. exists k. auto.
          }
          consider_next_reg' x r_t2 Hwx; first (inv Hwx; rewrite !fixpoint_interp1_eq //=).
          consider_next_reg' x r_t3 Hwx; first (inv Hwx; rewrite !fixpoint_interp1_eq //=).
          consider_next_reg' x r_t4 Hwx; first (inv Hwx; rewrite !fixpoint_interp1_eq //=).
          iSpecialize ("Hregs_valid" $! _ _ Hne Hwx).
          iApply (interp_monotone with "[] Hregs_valid"). iPureIntro. apply related_sts_pub_update_multiple_perm;auto.
      - rewrite insert_insert. iFrame.
    }
    iApply (wp_wand with "Hcont''").
    iIntros (v) "HH". iIntros (Hv).
    iDestruct ("HH" $! Hv) as (? ?) "(Hfull & Hvals & %Hrelated & Hown & Hsts & Hr)".
    iExists _,_. iFrame. iPureIntro.
    eapply related_sts_priv_trans_world;[|apply Hrelated].
    apply related_sts_pub_priv_world. apply related_sts_pub_update_multiple_perm;auto.
  Admitted.

End SimpleMalloc.
