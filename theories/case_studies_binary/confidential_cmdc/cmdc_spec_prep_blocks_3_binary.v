From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode proofmode_binary.
From griotte Require Import cmdc_spec_states_binary.

(** * Binary CMDC, block 4: preparation of the call to [C.g]

    On return from the call to [B.f], block 4 sets [c := 0] and stores
    [secret_b] into [b], in both runs, and prepares the argument
    [(RW, Global, c, c+1, c)] of the call to [C.g] in [ca0]. The group ends
    with [cgp] pointing to [b]. *)

Section CMDC_Prep_Blocks_3.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {specg : specG Σ}
    `{MP: MachineParameters}
  .

  Lemma cmdc_prep_blocks_3_spec
    (pc_b pc_e pc_a cgp_b cgp_e : Addr)
    (wca0 swca0 wct0 swct0 wct1 swct1 wb swb wc swc : Word)
    (secret_b1 secret_b2 : Z)
    (φ : language.val griotte_lang -> iProp Σ) :
    SubBounds pc_b pc_e pc_a (pc_a ^+ length cmdc_conf_main_code)%a ->
    (cgp_b + length (cmdc_conf_main_data 0 0))%a = Some cgp_e ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ cmdc_block_offset 4)%a ∗
    PC ↣ᵣ WCap RX Global pc_b pc_e (pc_a ^+ cmdc_block_offset 4)%a ∗
    cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
    cgp ↣ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
    ca0 ↦ᵣ wca0 ∗
    ca0 ↣ᵣ swca0 ∗
    ct0 ↦ᵣ wct0 ∗
    ct0 ↣ᵣ swct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ct1 ↣ᵣ swct1 ∗
    cgp_b ↦ₐ wb ∗
    cgp_b ↣ₐ swb ∗
    (cgp_b ^+ 1)%a ↦ₐ wc ∗
    (cgp_b ^+ 1)%a ↣ₐ swc ∗
    (cgp_b ^+ 2)%a ↦ₐ WInt secret_b1 ∗
    (cgp_b ^+ 2)%a ↣ₐ WInt secret_b2 ∗
    codefrag pc_a cmdc_conf_main_code ∗
    spec_codefrag pc_a cmdc_conf_main_code ∗
    ▷ ( ⤇ Seq (Instr Executable) ∗
        PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ cmdc_block_offset 5)%a ∗
        PC ↣ᵣ WCap RX Global pc_b pc_e (pc_a ^+ cmdc_block_offset 5)%a ∗
        cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
        cgp ↣ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
        ca0 ↦ᵣ WCap RW Global (cgp_b ^+ 1)%a (cgp_b ^+ 2)%a (cgp_b ^+ 1)%a ∗
        ca0 ↣ᵣ WCap RW Global (cgp_b ^+ 1)%a (cgp_b ^+ 2)%a (cgp_b ^+ 1)%a ∗
        (∃ w, ct0 ↦ᵣ w ∗ ct0 ↣ᵣ w) ∗
        (∃ w, ct1 ↦ᵣ w ∗ ct1 ↣ᵣ w) ∗
        cgp_b ↦ₐ WInt secret_b1 ∗
        cgp_b ↣ₐ WInt secret_b2 ∗
        (cgp_b ^+ 1)%a ↦ₐ WInt 0 ∗
        (cgp_b ^+ 1)%a ↣ₐ WInt 0 ∗
        (cgp_b ^+ 2)%a ↦ₐ WInt secret_b1 ∗
        (cgp_b ^+ 2)%a ↣ₐ WInt secret_b2 ∗
        codefrag pc_a cmdc_conf_main_code ∗
        spec_codefrag pc_a cmdc_conf_main_code
        -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (HsubBounds Hcgp_contiguous)
      "(#Hspec & Hj & HPC & HsPC & Hcgp & Hscgp & Hca0 & Hsca0 & Hct0 & Hsct0 & Hct1 & Hsct1
      & Hcgp_b & Hscgp_b & Hcgp_c & Hscgp_c & Hsecret_b & Hssecret_b
      & Hcode_main & Hscode_main & Hpost)".
    cbn in Hcgp_contiguous.
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    set (cgp_c := (cgp_b ^+ 1)%a).
    unfold_code cmdc_conf_main_code "Hcode_main".
    unfold_code cmdc_conf_main_code "Hscode_main".

    (* Block 4: erase c, store secret_b into b, and prepare the argument
       of the call to C.g *)
    focus_block_lockstep 4 "Hscode_main" "Hcode_main" of cmdc_conf_main_blocks at pc_a
      as a_prep Ha_prep "Hscode" "Hscont" "Hcode" "Hcont".
    iHide "Hcont" as hcont. iHide "Hscont" as hscont.

    (* Lea cgp 1%Z *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: transitivity (Some cgp_c); auto; subst cgp_c; solve_addr.

    (* Store cgp 0%Z *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: subst cgp_c; solve_addr.

    (* Mov ca0 cgp *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Lea cgp 1%Z *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: transitivity (Some (cgp_b ^+ 2)%a); auto; subst cgp_c; solve_addr.

    (* Load ct0 cgp *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split; [done| solve_addr].

    (* Lea cgp (-2)%Z *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: transitivity (Some cgp_b%a); auto; solve_addr.

    (* Store cgp ct0 *)
    iInstr_spec_lookup "Hscode" as "Hsi" "Hscode".
    iMod (step_store_success_reg _ _ _ _ _ _ _ _ _ _ _ RW
             with "[$HsPC $Hsi $Hsct0 $Hscgp $Hscgp_b $Hj]")
      as "(Hj & HsPC & Hsi & Hsct0 & Hscgp & Hscgp_b)"
    ; auto; try solve_pure.
    { solve_addr. }
    iSpecSeq.
    iSpecialize ("Hscode" with "[$]").
    (* Store cgp ct0 *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_store_success_reg _ _ _ _ _ _ _ _ _ _ _
             with "[$HPC $Hi $Hct0 Hcgp $Hcgp_b]"); auto; try solve_pure.
    { solve_addr. }
    { by cbn. }
    iIntros "!> (HPC & Hi & Hct0 & Hcgp & Hcgp_b)".
    wp_pure.
    iSpecialize ("Hcode" with "[$]").

    (* GetA ct0 ca0 *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Add ct1 ct0 1%Z *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Subseg ca0 ct0 ct1 *)
    iInstr_lockstep "Hscode" "Hcode".
    1,3: transitivity (Some (cgp_c ^+ 1)%a); auto; subst cgp_c; solve_addr.
    1,2: subst cgp_c; solve_addr.

    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscont" "Hcode" "Hcont" as "Hscode_main" "Hcode_main".
    change_pc_to (pc_a ^+ cmdc_block_offset 5)%a.
    replace (cgp_c ^+ 1)%a with (cgp_b ^+ 2)%a by (subst cgp_c; solve_addr).
    subst cgp_c.
    iApply "Hpost"; iFrame.
  Qed.

End CMDC_Prep_Blocks_3.
