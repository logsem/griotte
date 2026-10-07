From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import register_tactics wp_rules_interp.
From griotte Require Import switcher_call_states.

(** * Call routine, blocks 4-7: prepare the callee's stack and unseal

    Block 4 restricts the stack capability to the callee's stack frame,
    block 5 clears it, block 6 loads the unsealing capability of the
    switcher, and the first instruction of block 7 unseals the entry point of
    the callee. *)

Section Switcher_Call_Blocks_3.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Lemma switcher_call_block_4_spec
    pc_b pc_e pc_a
    b_stk e_stk a_stk
    wcs0 wcs1 :
    let switcher_instrs_4 := (switcher_instrs_n 4) in
    let len_switcher_4 := length switcher_instrs_4 in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_4)%a ->
    (isWithin a_stk e_stk b_stk e_stk = true) ->

    PC ↦ᵣ WCap XSRW_ Local pc_b pc_e pc_a ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk ∗
    codefrag pc_a switcher_instrs_4 ∗
    ▷ ( PC ↦ᵣ WCap XSRW_ Local pc_b pc_e (pc_a ^+ len_switcher_4)%a ∗
        cs0 ↦ᵣ WInt e_stk ∗
        cs1 ↦ᵣ WInt a_stk ∗
        csp ↦ᵣ WCap RWL Local a_stk e_stk a_stk ∗
        codefrag pc_a switcher_instrs_4 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_4 len_switcher_4; subst switcher_instrs_4 len_switcher_4.
    iIntros (Hsub_reg Hastk) "(HPC & Hcs0 & Hcs1 & Hcsp & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.
    (* --- GetE cs0 csp --- *)
    iInstr "Hcode".

    (* --- GetA cs1 csp --- *)
    iInstr "Hcode".

    (* --- Subseg csp cs1 cs0 --- *)
    iInstr "Hcode".

    iApply "Hpost"; iFrame.
  Qed.

  Lemma switcher_call_block_6_spec
    pc_b pc_e pc_a
    wcs0 wcs1 wpc_b :
    let switcher_instrs_6 := (switcher_instrs_n 6) in
    let len_switcher_6 := length switcher_instrs_6 in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_6)%a ->

    PC ↦ᵣ WCap XSRW_ Local pc_b pc_e pc_a ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    pc_b ↦ₐ wpc_b ∗
    codefrag pc_a switcher_instrs_6 ∗
    ▷ ( PC ↦ᵣ WCap XSRW_ Local pc_b pc_e (pc_a ^+ len_switcher_6)%a ∗
        cs0 ↦ᵣ wpc_b ∗
        cs1 ↦ᵣ WInt (pc_b - (pc_a ^+ 1)%a) ∗
        pc_b ↦ₐ wpc_b ∗
        codefrag pc_a switcher_instrs_6 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_6 len_switcher_6; subst switcher_instrs_6 len_switcher_6.
    iIntros (Hsub_reg) "(HPC & Hcs0 & Hcs1 & Hpc_b & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* --- GetB cs1 PC --- *)
    iInstr "Hcode".

    (* --- GetA cs0 PC --- *)
    iInstr "Hcode".

    (* --- Sub cs1 cs1 cs0 --- *)
    iInstr "Hcode".

    (* --- Mov cs0 PC --- *)
    iInstr "Hcode".

    (* --- Lea cs0 cs1 --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_lea_success_reg with "[$HPC $Hi $Hcs0 $Hcs1]");auto;[solve_pure..| |].
    { instantiate (1:=(pc_b ^+ 2)%a); solve_addr. }
    iIntros "!> (HPC & Hi & Hcs1 & Hcs0)".
    wp_pure.
    iSpecialize ("Hcode" with "[$]").

    (* --- Lea cs0 -2 --- *)
    iInstr "Hcode".
    { instantiate (1:= pc_b); solve_addr. }

    (* --- Load cs0 cs0 --- *)
    iInstr "Hcode".

    iApply "Hpost"; iFrame.
  Qed.


  (** First instruction of block 7: unseal the entry point. *)
  Lemma switcher_call_block_7_unseal_spec
    pc_a wct1 :
    let switcher_instrs_7 := switcher_instrs_n 7 in
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ length switcher_instrs_7)%a ->

    PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher pc_a ∗
    cs0 ↦ᵣ WSealRange (true, true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
    ct1 ↦ᵣ wct1 ∗
    codefrag pc_a switcher_instrs_7 ∗
    ▷ ( ∀ wsb,
        ⌜ wct1 = WSealed ot_switcher wsb ⌝ ∗
        PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ 1)%a ∗
        cs0 ↦ᵣ WSealRange (true, true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
        ct1 ↦ᵣ WSealable wsb ∗
        codefrag pc_a switcher_instrs_7 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_7; subst switcher_instrs_7.
    iIntros (Hsub_reg) "(HPC & Hcs0 & Hct1 & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* --- UnSeal ct1 cs0 ct1 --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_unseal_unknown _ _ _ _ _ _ (pc_a ^+ 1)%a
             with "[$HPC $Hi $Hcs0 $Hct1]"); try solve_pure.
    iIntros "!>" (ret) "[-> | (% & % & % & % & % & %wsb & -> & HPC & Hi & Hcs0 & Hct1
      & %Heq & % & %Hwct1)]".
    { wp_pure. wp_end. iIntros "%Hcontr";done. }
    simplify_eq.
    wp_pure.
    iSpecialize ("Hcode" with "[$]").
    iApply "Hpost"; iFrame; done.
  Qed.

  (** Blocks 4-7: restrict the stack capability to the callee's stack frame
      [[a ^+ 4, e)], clear it, load the unsealing capability, and unseal the
      entry point [wct1]. *)
  Lemma switcher_call_blocks_3_spec
    (b e a : Addr) (stk_mem : list Word) (wcs0 wcs1 wct1 : Word) :
    switcher_stk_bounds b e a ->

    PC ↦ᵣ switcher_block_pc 4 ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    csp ↦ᵣ WCap RWL Local b e (a ^+ 4)%a ∗
    [[ (a ^+ 4)%a , e ]] ↦ₐ [[ stk_mem ]] ∗
    b_switcher ↦ₐ WSealRange (true,true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
    ct1 ↦ᵣ wct1 ∗
    switcher_code ∗
    ▷ ( ∀ wsb,
        ⌜ wct1 = WSealed ot_switcher wsb ⌝ ∗
        PC ↦ᵣ switcher_pc (switcher_block_offset 7 + 1) ∗
        cs0 ↦ᵣ WSealRange (true,true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
        (∃ wcs1', cs1 ↦ᵣ wcs1') ∗
        csp ↦ᵣ WCap RWL Local (a ^+ 4)%a e (a ^+ 4)%a ∗
        [[ (a ^+ 4)%a , e ]] ↦ₐ [[ region_addrs_zeroes (a ^+ 4)%a e ]] ∗
        b_switcher ↦ₐ WSealRange (true,true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
        ct1 ↦ᵣ WSealable wsb ∗
        switcher_code -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((Hba & Hba3 & Ha4))
      "(HPC & Hcs0 & Hcs1 & Hcsp & Hstk & Hb_switcher & Hct1 & Hcode & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hcode".

    (* Block 4: restrict the stack capability *)
    switcher_focus_block 4 "Hcode" as "Hcode" "Hcls"; iHide "Hcls" as hcont.
    iApply (switcher_call_block_4_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hcsp $Hcode]"); [done| |iNext].
    { rewrite /isWithin; solve_addr+Hba Hba3 Ha4. }
    iIntros "(HPC & Hcs0 & Hcs1 & Hcsp & Hcode)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* Block 5: clear the callee's stack frame *)
    switcher_focus_block 5 "Hcode" as "Hcode" "Hcls"; iHide "Hcls" as hcont.
    iApply (clear_stack_spec with "[- $HPC $Hcode $Hcsp $Hcs0 $Hcs1 $Hstk]");
      try solve_pure.
    { solve_addr+. }
    { solve_addr+Hba Hba3 Ha4. }
    iIntros "!> (HPC & Hcsp & Hcs0 & Hcs1 & Hcode & Hstk)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* Block 6: load the unsealing capability *)
    switcher_focus_block 6 "Hcode" as "Hcode" "Hcls"; iHide "Hcls" as hcont.
    iApply (switcher_call_block_6_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hb_switcher $Hcode]"); first done.
    iNext; iIntros "(HPC & Hcs0 & Hcs1 & Hb_switcher & Hcode)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* Block 7: unseal the entry point *)
    switcher_focus_block 7 "Hcode" as "Hcode" "Hcls"; iHide "Hcls" as hcont.
    iApply (switcher_call_block_7_unseal_spec with
      "[- $HPC $Hcs0 $Hct1 $Hcode]"); first done.
    iNext; iIntros (wsb) "(-> & HPC & Hcs0 & Hct1 & Hcode)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
    switcher_change_pc (switcher_block_offset 7 + 1)%Z.
    iApply "Hpost"; iFrame; done.
  Qed.

End Switcher_Call_Blocks_3.
