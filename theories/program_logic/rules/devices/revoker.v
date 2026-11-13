From iris.proofmode Require Import proofmode.
From griotte Require Import instructions.memory_accesses.

(** * The derived rules of the revoker *)
Section mmio_revoker_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types w : LWord.
  Implicit Types reg : gmap RegName LWord.
  Implicit Types ms : gmap Addr LWord.

  (** ** The revoker store

      A store to the revoker sweeps memory. It kills a chosen set [K] of
      quarantined identifiers, whose ranges are painted: their cells become
      unclaimed. Register copies of their words with authority are already
      untagged, by the register clause. *)
  Definition revoke_pre (ι : AId) : iProp Σ :=
    ∃ b e, alloc_obj ι b e ∗ ι ↦st{1} AQuar ∗
      [∗ list] a ∈ finz.seq_between b e, a ↦ₛ ShadowQuarantined ∗ addr_alloc a (Claimed ι).

  Definition revoke_post (ι : AId) : iProp Σ :=
    ∃ b e, alloc_obj ι b e ∗ ι ↦st{1} ADead ∗ ι ⊒ ADead ∗
      [∗ list] a ∈ finz.seq_between b e, a ↦ₛ ShadowQuarantined ∗ addr_alloc a Unclaimed.

  Definition revoke_reg (K : gset AId) (R : RegState) : RegState :=
    map_imap (λ ι (x : RegEntry), Some (if decide (ι ∈ K) then (x.1, ADead) else x)) R.

  Definition revoke_claims (K : gset AId) (C : gmap Addr AddrClaim) : gmap Addr AddrClaim :=
    (λ cl, match cl with
          | Claimed ι => if decide (ι ∈ K) then Unclaimed else cl
          | _ => cl end) <$> C.

  Lemma lookup_revoke_reg K R ι :
    revoke_reg K R !! ι =
      (λ x : RegEntry, if decide (ι ∈ K) then (x.1, ADead) else x) <$> R !! ι.
  Proof. rewrite /revoke_reg map_lookup_imap. by destruct (R !! ι) eqn:Hι; rewrite ?Hι. Qed.

  Lemma lookup_revoke_claims K C a :
    revoke_claims K C !! a =
      (λ cl, match cl with
            | Claimed ι => if decide (ι ∈ K) then Unclaimed else cl
            | _ => cl end) <$> C !! a.
  Proof. apply lookup_fmap. Qed.

  Lemma revoke_ghost_update (K : gset AId) R C :
    (∀ ι a, ι ∈ K → C !! a = Some (Claimed ι) → ∃ x, R !! ι = Some x ∧ re_covers x a) →
    reg_auth R -∗ addr_alloc_auth C -∗ ([∗ set] ι ∈ K, revoke_pre ι) ==∗
    reg_auth (revoke_reg K R) ∗ addr_alloc_auth (revoke_claims K C) ∗
    ([∗ set] ι ∈ K, revoke_post ι) ∗
    ⌜∀ ι, ι ∈ K → ∃ x, R !! ι = Some x ∧ re_status x = AQuar⌝.
  Proof.
    iInduction K as [|ι K HιK] "IH" using set_ind_L forall (R C);
      iIntros (Hcov) "HR HC Hpre".
    - assert (revoke_reg ∅ R = R) as ->.
      { apply map_eq. intros ι. rewrite lookup_revoke_reg.
        destruct (R !! ι) eqn:Hι; rewrite Hι /=; [|done].
        case_decide; [set_solver|done]. }
      assert (revoke_claims ∅ C = C) as ->.
      { apply map_eq. intros a. rewrite lookup_revoke_claims.
        by destruct (C !! a) as [ []|]; cbn; try done. }
      iFrame. iModIntro. iSplit; first by rewrite big_sepS_empty.
      iPureIntro. set_solver.
    - rewrite big_sepS_union; last set_solver. rewrite big_sepS_singleton.
      iDestruct "Hpre" as "[(%b & %e & #Hobj & Htok & Hcells) Hpre]".
      iDestruct (reg_lookup_own with "HR Htok") as %(b' & e' & γ & HRι).
      iDestruct (reg_lookup_obj with "HR Hobj") as %(γ' & s & HRι').
      rewrite HRι in HRι'. simplify_eq.
      rewrite big_sepL_sep. iDestruct "Hcells" as "[Hsh Hcl]".
      iDestruct (addr_alloc_lookup_list _ _ (λ _, Claimed ι) with "HC Hcl") as %Hcl.
      iMod (reg_step _ _ _ _ _ _ ADead with "HR Htok") as "[HR Htok]"; [done|simpl; lia|].
      iDestruct (st_lb_get with "Htok") as "#Hd".
      iMod (addr_alloc_update_list _ _ (λ _, Claimed ι) (λ _, Unclaimed) with "HC Hcl")
        as "[HC Hcl]".
      set (R1 := <[ι:=(b, e, γ', ADead)]> R).
      set (C1 := list_to_map ((λ a, (a, Unclaimed)) <$> finz.seq_between b e) ∪ C).
      assert (∀ a, C1 !! a = if decide (a ∈ finz.seq_between b e) then Some Unclaimed else C !! a)
        as HC1.
      { intros a. rewrite /C1 lookup_union. case_decide as Ha.
        - rewrite (elem_of_list_to_map_1 _ a Unclaimed); first by destruct (C !! a).
          + rewrite -list_fmap_compose. apply NoDup_fmap_2; first (intros ?? [=]; done).
            apply finz_seq_between_NoDup.
          + apply list_elem_of_fmap. eauto.
        - rewrite not_elem_of_list_to_map_1.
          + by destruct (C !! a).
          + rewrite -list_fmap_compose. intros (x & -> & Hx)%list_elem_of_fmap. done. }
      iMod ("IH" $! R1 C1 with "[%] HR HC Hpre") as "(HR & HC & Hpost & %HK)".
      { intros ι' a Hι' Ha. rewrite HC1 in Ha. case_decide; first done.
        destruct (Hcov ι' a ltac:(set_solver) Ha) as (x & Hx & Hc).
        exists x. rewrite /R1 lookup_insert_ne; first done. set_solver. }
      assert (revoke_reg K R1 = revoke_reg ({[ι]} ∪ K) R) as ->.
      { apply map_eq. intros ι'. rewrite !lookup_revoke_reg /R1.
        destruct (decide (ι = ι')) as [<-|Hne].
        - rewrite lookup_insert_eq HRι /=. repeat case_decide; set_solver.
        - rewrite lookup_insert_ne //. destruct (R !! ι') eqn:Hι'; rewrite ?Hι' /=; last done.
          repeat case_decide; set_solver. }
      assert (revoke_claims K C1 = revoke_claims ({[ι]} ∪ K) C) as ->.
      { apply map_eq. intros a. rewrite !lookup_revoke_claims HC1.
        case_decide as Ha.
        - rewrite (Hcl a Ha) /=. case_decide; set_solver.
        - destruct (C !! a) as [ [|ι'|]|] eqn:HCa; rewrite ?HCa /=; try done.
          case_decide as H1; case_decide as H2; try done; [exfalso; set_solver|].
          assert (ι' = ι) as -> by set_solver.
          exfalso. destruct (Hcov ι a ltac:(set_solver) HCa) as (x & Hx & Hc).
          rewrite HRι in Hx. simplify_eq. apply Ha. by apply elem_of_finz_seq_between. }
      iModIntro. iFrame. rewrite big_sepS_union; last set_solver. rewrite big_sepS_singleton.
      iSplitL.
      + iFrame "Hpost". iExists b, e. iFrame "∗#". rewrite big_sepL_sep. iFrame.
      + iPureIntro. intros ι' Hι'. destruct (decide (ι' = ι)) as [->|Hne].
        * eexists. split; first exact HRι. done.
        * destruct (HK ι' ltac:(set_solver)) as (x & Hx & Hs). exists x.
          rewrite /R1 lookup_insert_ne // in Hx.
  Qed.

  Lemma wp_store_revoker E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w (regs : LReg)
      r1 (r2 : Z + RegName) imm p g b e a (K : gset AId) dq :
    decodeInstrW w.(lw) = Store r1 r2 imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Store r1 r2 imm) ⊆ dom regs →
    reg_allows_store_imm regs r1 imm p g b e a revoker_addr →
    (∀ v : LWord, regs !!ₗ r1 = Some v → v.(lprov) = None) →
    (pc_a + 1)%a = Some pc_a' →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        ([∗ set] ι ∈ K, revoke_pre ι) }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        ([∗ set] ι ∈ K, revoke_post ι) }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hallow Hnoid Hpca' φ) "(HPC & Hpc_a & Hmap & Hpre) Hφ".
    iApply (wp_instr_step_nosw with "HPC Hpc_a Hmap"); [rewrite Hinstr; by apply sw_of_none|..]; eauto.
    iNext; iIntros (r sr m st td lreg lsreg lmem R C c σ') "@".
    rewrite Hinstr in Hstep.
    (* The physical step: the sweep, then the PC increment. The revoker
       capability has no identifier and non-empty bounds: its copy is exact. *)
    pose proof Hallow as (Hr1l & Hadd & Hwa & Hwb).
    destruct (regs !!ₗ r1) as [v1|] eqn:Hv1; last done. cbn in Hr1l. simplify_eq.
    destruct (llookup_reg_phys _ _ _ _ _ Hregs Hv1) as (s1 & Hr1 & Hrel1).
    assert (and_tag s1 (lw v1) = lw v1) as Hex.
    { eapply reg_phys_exact_cond; first done.
      - intros (ι & x & Hι & _). by rewrite (Hnoid _ eq_refl) in Hι.
      - eapply (nonempty_exact_cond v1); [by rewrite Hr1l | apply withinBounds_true_iff in Hwb; solve_addr]. }
    rewrite Hex Hr1l in Hr1.
    assert (is_Some (word_of_argument r r2)) as [wv Hwv].
    { destruct r2 as [z|r2]; cbn; first eauto.
      assert (is_Some (regs !!ₗ r2)) as [lv Hl].
      { eapply llookup_reg_of_dom; [exact Dregs | rewrite /regs_of /operands_of /=; set_solver+]. }
      destruct (llookup_reg_phys _ _ _ _ _ Hregs Hl) as (s2 & Hr2 & _). eauto. }
    rewrite /exec /= Hwv Hr1 /= Hadd /= Hwa Hwb /= /is_mmio_address /mmio_store
      revoker_not_shadow_address /= in Hstep.
    rewrite (proj2 (is_revoker_address_spec revoker_addr) eq_refl) /= in Hstep.
    (* The ghost update *)
    iMod (revoke_ghost_update K R C with "HR HC Hpre") as "(HR & HC & Hpost & %HK)".
    { intros ι a' _ Ha'. apply (reg_ok_claimed _ _ _ (er_registry _ _ _ _ _ _ _ Her)) in Ha'
        as (x & Hx & Hcov & _). eauto. }
    assert (erasure (revoke_reg K R) (revoke_claims K C)
              (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr (sweep_mem st m) st td)
              (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) lreg (ls_join lsreg) lmem)
      as Her1.
    { eapply erasure_revoke; eauto.
      - apply lookup_revoke_reg.
      - apply lookup_revoke_claims. }
    assert (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) =
              Some (Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π))
      as Hinc by by rewrite /incrementPC /incrementPC_gen Hpca'.
    destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hinc) as (pc'' & Hu & Her2).
    rewrite /nextPC /advancePC /= Hpca' /update_pcc in Hu. simplify_eq.
    unfold revoker_sweep, nextPC, advancePC in Hstep; cbn in Hstep.
    rewrite Hpca' in Hstep. simplify_eq.
    iMod (PC_update _ _ (Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π) with "HPCa HPC")
      as "[HPCa HPC]".
    iModIntro. iSplit; first (iPureIntro; by apply sys_kept_same_sreg).
    iSplitR "Hφ HPC Hpc_a Hmap Hpost".
    { iApply (SI_close _ _ _ _ _ _ _ Her2 with "HPCa Hr Hsr Hm Hst HR HC"). }
    iApply "Hφ". iFrame.
  Qed.
End mmio_revoker_rules.
