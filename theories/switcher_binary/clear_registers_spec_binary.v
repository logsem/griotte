From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode_binary.
From griotte Require Export clear_registers.

(** * Clearing registers in both runs

    Binary (lockstep) counterparts of the specifications of the register
    clearing macros: both runs execute the same macro, on their own register
    files. *)

Section ClearRegistersMacro.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {specg: specG Σ} `{MP: MachineParameters}.

  Definition dom_arg_rmap (nargs : nat) : gset RegName :=
    let rargs := [ca0 ; ca1 ; ca2 ; ca3 ; ca4 ; ca5 ; ct0] in
    list_to_set (firstn nargs rargs).

  Definition is_arg_rmap (rmap : Reg) (nargs : nat) :=
    dom rmap = dom_arg_rmap nargs.

  (** Both runs clear the registers of [l]. *)
  Lemma rclear_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (l : list RegName)
    (rmap smap : Reg) φ :
    l ≠ [] ->
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (rclear_instrs' l ))%a ->
    dom rmap = list_to_set l ->
    dom smap = list_to_set l ->

    ( spec_ctx
      ∗ ⤇ Seq (Instr Executable)
      ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
      ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )
      ∗ ( [∗ map] r↦w ∈ smap, r ↣ᵣ w )
      ∗ codefrag pc_a (rclear_instrs' l)
      ∗ spec_codefrag pc_a (rclear_instrs' l)
      ∗ ▷ ( (∃ (rmap' smap' : Reg),
              ⌜ dom rmap' = list_to_set l ⌝
              ∗ ⌜ dom smap' = list_to_set l ⌝
              ∗ ⤇ Seq (Instr Executable)
              ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e (pc_a ^+ length (rclear_instrs' l ))%a
              ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e (pc_a ^+ length (rclear_instrs' l ))%a
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              ∗ ( [∗ map] r↦w ∈ smap', r ↣ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              ∗ codefrag pc_a (rclear_instrs' l)
              ∗ spec_codefrag pc_a (rclear_instrs' l))
               -∗ WP Seq (Instr Executable) {{ φ }})
    )
    ⊢ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
    iIntros (Hne Hx Hbounds Hdom Hsdom)
      "(#Hctx & Hj & HPC & HsPC & Hregs & Hsregs & Hcode & Hscode & Hcont)".
    iRevert (Hbounds Hdom Hsdom).
    iInduction (l) as [|r l] "IH" forall (rmap smap pc_a);
      iIntros (Hbounds Hrdom Hsdom); first congruence.
    cbn [list_to_set] in Hrdom, Hsdom.
    assert (is_Some (rmap !! r)) as [rv Hr].
    { apply elem_of_dom; rewrite Hrdom; set_solver. }
    assert (is_Some (smap !! r)) as [srv Hsr].
    { apply elem_of_dom; rewrite Hsdom; set_solver. }
    iDestruct (big_sepM_delete _ _ r with "Hregs") as "[Hr Hregs]"; eauto.
    iDestruct (big_sepM_delete _ _ r with "Hsregs") as "[Hsr Hsregs]"; eauto.
    cbn.
    codefrag_facts "Hcode".

    (* Mov r 0 *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: transitivity (Some (pc_a ^+ 1)%a); auto; solve_addr.
    destruct (decide (l = [])).
    { subst l. iApply "Hcont". iFrame.
      replace (delete r rmap) with (∅ : Reg).
      2: { symmetry. rewrite -dom_empty_iff_L dom_delete_L Hrdom. set_solver. }
      replace (delete r smap) with (∅ : Reg).
      2: { symmetry. rewrite -dom_empty_iff_L dom_delete_L Hsdom. set_solver. }
      iExists (<[r := WInt 0]> ∅), (<[r := WInt 0]> ∅).
      rewrite !big_sepM_insert // !big_sepM_empty. iFrame.
      iPureIntro; split; set_solver. }

    iAssert (codefrag (pc_a ^+ 1)%a (rclear_instrs' l) ∗
             (codefrag (pc_a ^+ 1)%a (rclear_instrs' l) -∗
              codefrag pc_a (rclear_instrs' (r :: l))))%I
      with "[Hcode]" as "[Hcode Hcls]".
    { cbn. unfold codefrag. rewrite (region_pointsto_cons _ (pc_a ^+ 1)%a). 2,3: solve_addr.
      iDestruct "Hcode" as "[? Hr]".
      rewrite (_: ((pc_a ^+ 1) ^+ (length (rclear_instrs' l)))%a =
                    (pc_a ^+ (S (length (rclear_instrs' l))))%a). 2: solve_addr.
      iFrame. eauto. }
    iAssert (spec_codefrag (pc_a ^+ 1)%a (rclear_instrs' l) ∗
             (spec_codefrag (pc_a ^+ 1)%a (rclear_instrs' l) -∗
              spec_codefrag pc_a (rclear_instrs' (r :: l))))%I
      with "[Hscode]" as "[Hscode Hscls]".
    { cbn. unfold spec_codefrag. rewrite (spec_region_pointsto_cons _ (pc_a ^+ 1)%a). 2,3: solve_addr.
      iDestruct "Hscode" as "[? Hr]".
      rewrite (_: ((pc_a ^+ 1) ^+ (length (rclear_instrs' l)))%a =
                    (pc_a ^+ (S (length (rclear_instrs' l))))%a). 2: solve_addr.
      iFrame. eauto. }

    match goal with H : SubBounds _ _ _ _ |- _ =>
      rewrite (_: (pc_a ^+ (length (rclear_instrs' (r :: l))))%a =
                  ((pc_a ^+ 1)%a ^+ length (rclear_instrs' l))%a) in H |- *
    end.
    2: { unfold rclear_instrs'; cbn; solve_addr. }

    destruct (decide (r ∈ l)).
    + iDestruct (big_sepM_insert _ _ r with "[Hr $Hregs]") as "Hregs".
      { by rewrite lookup_delete_eq. }
      { by iFrame. }
      iDestruct (big_sepM_insert _ _ r with "[Hsr $Hsregs]") as "Hsregs".
      { by rewrite lookup_delete_eq. }
      { by iFrame. }
      iApply ("IH" with "[] Hj HPC HsPC Hregs Hsregs Hcode Hscode [Hcont Hcls Hscls]"); eauto.
      { iNext.
        iIntros "H".
        iDestruct "H" as (rmap' smap' Hdom_rmap' Hdom_smap')
          "(Hj & HPC & HsPC & Hregs & Hsregs & Hcode & Hscode)".
        iApply "Hcont"; iFrame.
        iDestruct ("Hcls" with "Hcode") as "$".
        iDestruct ("Hscls" with "Hscode") as "$".
        iPureIntro; split; set_solver. }
      { iPureIntro; solve_pure_addr. }
      { iPureIntro. rewrite insert_delete_eq. set_solver. }
      { iPureIntro. rewrite insert_delete_eq. set_solver. }
    + iApply ("IH" with "[] Hj HPC HsPC Hregs Hsregs Hcode Hscode [Hcont Hcls Hscls Hr Hsr]"); eauto.
      { iNext.
        iIntros "H".
        iDestruct "H" as (rmap' smap' Hdom_rmap' Hdom_smap')
          "(Hj & HPC & HsPC & Hregs & Hsregs & Hcode & Hscode)".
        iDestruct (big_sepM_insert _ _ r with "[Hr $Hregs]") as "Hregs".
        { rewrite -not_elem_of_dom Hdom_rmap'; set_solver. }
        { iFrame. done. }
        iDestruct (big_sepM_insert _ _ r with "[Hsr $Hsregs]") as "Hsregs".
        { rewrite -not_elem_of_dom Hdom_smap'; set_solver. }
        { iFrame. done. }
        iApply "Hcont"; iFrame.
        iDestruct ("Hcls" with "Hcode") as "$".
        iDestruct ("Hscls" with "Hscode") as "$".
        iPureIntro; split; set_solver. }
      { iPureIntro; solve_pure_addr. }
      { iPureIntro; set_solver. }
      { iPureIntro; set_solver. }
  Qed.

  (** Both runs clear the registers that are not callee-saved nor return values. *)
  Lemma clear_registers_post_call_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (rmap smap : Reg) φ :
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length clear_registers_post_call_instrs)%a ->
    dom rmap = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ->
    dom smap = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ->

    ( spec_ctx
      ∗ ⤇ Seq (Instr Executable)
      ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
      ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )
      ∗ ( [∗ map] r↦w ∈ smap, r ↣ᵣ w )
      ∗ codefrag pc_a clear_registers_post_call_instrs
      ∗ spec_codefrag pc_a clear_registers_post_call_instrs
      ∗ ▷ ( (∃ (rmap' smap' : Reg),
              ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝
              ∗ ⌜ dom smap' = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝
              ∗ ⤇ Seq (Instr Executable)
              ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e (pc_a ^+ length clear_registers_post_call_instrs)%a
              ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e (pc_a ^+ length clear_registers_post_call_instrs)%a
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              ∗ ( [∗ map] r↦w ∈ smap', r ↣ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              ∗ codefrag pc_a clear_registers_post_call_instrs
              ∗ spec_codefrag pc_a clear_registers_post_call_instrs)
               -∗ WP Seq (Instr Executable) {{ φ }})
    )
    ⊢ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
    iIntros (Hx Hbounds Hdom Hsdom) "H".
    iApply (rclear_spec _ _ _ _ _ registers_post_call with "H"); eauto.
  Qed.


  (** Both runs clear the registers that are neither arguments nor [PC], [cra], [cgp], [csp]. *)
  Lemma clear_registers_pre_call_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (rmap smap : Reg) φ :
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length clear_registers_pre_call_instrs)%a ->
    dom rmap = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ PC ; cra ; cgp ; csp ]}) ->
    dom smap = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ PC ; cra ; cgp ; csp ]}) ->

    ( spec_ctx
      ∗ ⤇ Seq (Instr Executable)
      ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
      ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )
      ∗ ( [∗ map] r↦w ∈ smap, r ↣ᵣ w )
      ∗ codefrag pc_a clear_registers_pre_call_instrs
      ∗ spec_codefrag pc_a clear_registers_pre_call_instrs
      ∗ ▷ ( (∃ (rmap' smap' : Reg),
              ⌜ dom rmap' = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ PC ; cra ; cgp ; csp ]}) ⌝
              ∗ ⌜ dom smap' = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ PC ; cra ; cgp ; csp ]}) ⌝
              ∗ ⤇ Seq (Instr Executable)
              ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e (pc_a ^+ length clear_registers_pre_call_instrs)%a
              ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e (pc_a ^+ length clear_registers_pre_call_instrs)%a
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              ∗ ( [∗ map] r↦w ∈ smap', r ↣ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              ∗ codefrag pc_a clear_registers_pre_call_instrs
              ∗ spec_codefrag pc_a clear_registers_pre_call_instrs)
               -∗ WP Seq (Instr Executable) {{ φ }})
    )
    ⊢ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
    iIntros (Hx Hbounds Hdom Hsdom) "H".
    iApply (rclear_spec _ _ _ _ _ registers_pre_call with "H"); eauto.
  Qed.

End ClearRegistersMacro.
