From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel region_invariants.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine Require Import rules proofmode monotone.
From cap_machine.proofmode Require Import map_simpl register_tactics proofmode.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {cstackg : CSTACKG Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Notation CSTK := (leibnizO cstack).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> (leibnizO Word) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation K := (WORLD -n> (leibnizO CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (V).

  Lemma wp_store_interp (E : coPset) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wsrc wdst : Word)
    :
    decodeInstrW wi = Store rdst (inr rsrc) →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

     {{{ interp W C wsrc
           ∗ interp W C wdst
           ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rdst ↦ᵣ wdst
           ∗ region W C
           ∗ sts_full_world W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          ( ∃ p g b e a,
           ⌜ wdst = WCap p g b e a ⌝       
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rdst ↦ᵣ WCap p g b e a
           ∗ region W C
           ∗ sts_full_world W C
           ∗ ⌜ canStore p wsrc = true ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' φ)
      "(#Hinterp_src & #Hinterp_dst & HPC & Hi & Hsrc & Hdst & Hregion & Hworld)".
    iIntros "Hφ".

    destruct (is_cap wdst) eqn:Hcap;cycle 1.
    {
      iApply (wp_store_fail_reg_not_cap _ _ _ _ _ _ _ rdst rsrc with "[$]")
      ; try solve_pure.
      iIntros "!> _". iApply "Hφ"; by iLeft. }
    destruct wdst;try done. destruct sb; try done. 

    destruct (decide (canStore p wsrc = true))%a as [Hstore_src|Hstore_src]; cycle 1.
    {
      iApply (wp_store_fail_reg_perm with "[HPC Hi Hdst Hsrc]")
      ; try iFrame
      ; try solve_pure.
      { by destruct ( canStore p wsrc ); auto. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }
    pose proof ( canStore_writeAllowed p wsrc Hstore_src ) as Hp_stk_wa.
    destruct (decide (b <= a))%a as [Hba|Hba]; cycle 1.
    {
      iApply (wp_store_fail_reg with "[HPC Hi Hdst Hsrc]")
      ; try iFrame
      ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }
    destruct (decide (a < e))%a as [Hae|Hae]; cycle 1.
    {
      iApply (wp_store_fail_reg with "[HPC Hi Hdst Hsrc]")
      ; try iFrame
      ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }

    iDestruct (writeAllowed_valid_cap with "Hinterp_dst") as "%Hdst_in_region"; auto.
    assert ( ∃ ρ, std W !! a = Some ρ ∧ ρ ≠ Revoked) as ( ρ & Hρ & Hρ_not_revoked).
    {
      rewrite Forall_lookup in Hdst_in_region.
      assert ( a ∈ finz.seq_between b e) as Ha.
      { apply elem_of_finz_seq_between; solve_addr. }
      rewrite elem_of_list_lookup in Ha.
      destruct Ha as [ka Hka].
      apply Hdst_in_region in Hka.
      done.
    }

    iDestruct (write_allowed_inv _ _ a with "Hinterp_dst") as (p' P Hflows Hpers) "(Hrel & Hzcond & Hwcond & Hrcond & Hmono)";[solve_addr|auto|..].

    iDestruct (region_open with "[$]") as (v) "(Hr & Hsts & Hstate & Ha & %Hno & _ & _)";[|done|].
    { destruct ρ;auto. done. }
    
    iApply (wp_store_success_reg _ _ _ _ _ _ _ _ rdst rsrc with "[$HPC Hi Hsrc Hdst Ha]")
    ; try iFrame
    ; try solve_pure.
    { rewrite /withinBounds; solve_addr. }
    iNext; iIntros "(HPC & Hi & Hsrc & Hdst & Ha)".

    iDestruct (region_close
                with "[$Hstate $Hr $Ha $Hrel]")
      as "Hregion".
    { rewrite /safeC. auto. }
    { destruct ρ; naive_solver. }
    { iFrame "%". rewrite /safeC /=.
      iDestruct ("Hwcond" with "Hinterp_src") as "HP".
      iFrame "HP".
      rewrite /monoReq Hρ.
      destruct ρ;[simpl..|exfalso;done].
      - destruct (isWL p');auto.
        destruct (isDL p')
        ; by (iSpecialize ("Hmono" with "[%]");[eapply canStore_flowsto;eauto|]).
      - by (iSpecialize ("Hmono" with "[%]");[eapply canStore_flowsto;eauto|]). }

    iApply "Hφ"; iRight; iFrame "∗%".
    iSplit; first done.
    iPureIntro; solve_addr.
  Qed.

  Lemma wp_store_interp_cap (E : coPset) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a : Addr)
    (wi wsrc : Word)
    :
    decodeInstrW wi = Store rdst (inr rsrc) →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

     {{{ interp W C wsrc
           ∗ interp W C (WCap p g b e a)
           ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rdst ↦ᵣ (WCap p g b e a)
           ∗ region W C
           ∗ sts_full_world W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          (⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rdst ↦ᵣ WCap p g b e a
           ∗ region W C
           ∗ sts_full_world W C
           ∗ ⌜ canStore p wsrc = true ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' φ)
      "(#Hinterp_src & #Hinterp_dst & HPC & Hi & Hsrc & Hdst & Hregion & Hworld)".
    iIntros "Hφ".
    iApply (wp_store_interp with "[-Hφ]");eauto;[iFrame "∗ #"|].
    iNext. iIntros (ret) "[? | (%&%&%&%&%&%&?&?&?&?&?&?&?&%&%)]"
    ; iApply "Hφ" ; auto.
    iRight. simplify_eq.  iFrame.
    auto.
  Qed.

  Lemma wp_store_interp_z (E : coPset) (W : WORLD) (C : CmptName) (rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wdst : Word) (z : Z)
    :
    decodeInstrW wi = Store rdst (inl z) →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

     {{{ interp W C wdst
           ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rdst ↦ᵣ wdst
           ∗ region W C
           ∗ sts_full_world W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          ( ∃ p g b e a,
           ⌜ wdst = WCap p g b e a ⌝       
           ∗ ⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rdst ↦ᵣ WCap p g b e a
           ∗ region W C
           ∗ sts_full_world W C
           ∗ ⌜ writeAllowed p ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' φ)
      "(#Hinterp_dst & HPC & Hi & Hdst & Hregion & Hworld)".
    iIntros "Hφ".

    destruct (is_cap wdst) eqn:Hcap;cycle 1.
    {
      iApply (wp_store_fail_z_not_cap with "[$]")
      ; try solve_pure; eauto.
      iIntros "!> _". iApply "Hφ"; by iLeft. }
    destruct wdst;try done. destruct sb; try done. 

    destruct (decide (writeAllowed p = true))%a as [Hstore_src|Hstore_src]; cycle 1.
    {
      iApply (wp_store_fail_z_perm with "[HPC Hi Hdst]")
      ; try iFrame
      ; try solve_pure
      ; eauto.
      { by destruct ( writeAllowed p ); auto. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }
    destruct (decide (b <= a))%a as [Hba|Hba]; cycle 1.
    {
      iApply (wp_store_fail_z with "[HPC Hi Hdst]")
      ; try iFrame
      ; try solve_pure
      ; eauto.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }
    destruct (decide (a < e))%a as [Hae|Hae]; cycle 1.
    {
      iApply (wp_store_fail_z with "[HPC Hi Hdst]")
      ; try iFrame
      ; try solve_pure
      ; eauto.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }

    iDestruct (writeAllowed_valid_cap with "Hinterp_dst") as "%Hdst_in_region"; auto.
    assert ( ∃ ρ, std W !! a = Some ρ ∧ ρ ≠ Revoked) as ( ρ & Hρ & Hρ_not_revoked).
    {
      rewrite Forall_lookup in Hdst_in_region.
      assert ( a ∈ finz.seq_between b e) as Ha.
      { apply elem_of_finz_seq_between; solve_addr. }
      rewrite elem_of_list_lookup in Ha.
      destruct Ha as [ka Hka].
      apply Hdst_in_region in Hka.
      done.
    }

    iDestruct (write_allowed_inv _ _ a with "Hinterp_dst") as (p' P Hflows Hpers) "(Hrel & Hzcond & Hwcond & Hrcond & Hmono)";[solve_addr|auto|..].

    iDestruct (region_open with "[$]") as (v) "(Hr & Hsts & Hstate & Ha & %Hno & _ & _)";[|done|].
    { destruct ρ;auto. done. }
    
    iApply (wp_store_success_z _ _ _ _ _ _ _ _ rdst with "[$HPC Hi Hdst Ha]")
    ; try iFrame
    ; try solve_pure
    ; eauto.
    { rewrite /withinBounds; solve_addr. }
    iNext; iIntros "(HPC & Hi & Hdst & Ha)".

    iDestruct (region_close
                with "[$Hstate $Hr $Ha $Hrel]")
      as "Hregion".
    { rewrite /safeC. auto. }
    { destruct ρ; naive_solver. }
    { iFrame "%". rewrite /safeC /=.
      iSplitL;[|iApply "Hwcond";iClear "∗ #"; by rewrite !fixpoint_interp1_eq /=].
      rewrite /monoReq Hρ.
      destruct ρ;[simpl..|exfalso;done].
      - destruct (isWL p');auto.
        destruct (isDL p')
        ; by (iSpecialize ("Hmono" $! (WInt z) with "[%]");[eapply canStore_flowsto;eauto|]).
      - by (iSpecialize ("Hmono" $! (WInt z) with "[%]");[eapply canStore_flowsto;eauto|]). }

    iApply "Hφ"; iRight; iFrame "∗%".
    iSplit; first done.
    iPureIntro; solve_addr.
  Qed.

  Lemma wp_store_interp_z_cap (E : coPset) (W : WORLD) (C : CmptName) (rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a : Addr)
    (wi : Word) (z : Z)
    :
    decodeInstrW wi = Store rdst (inl z) →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

     {{{  interp W C (WCap p g b e a)
           ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rdst ↦ᵣ (WCap p g b e a)
           ∗ region W C
           ∗ sts_full_world W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          (⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rdst ↦ᵣ WCap p g b e a
           ∗ region W C
           ∗ sts_full_world W C
           ∗ ⌜ writeAllowed p ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' φ)
      "(#Hinterp_dst & HPC & Hi & Hdst & Hregion & Hworld)".
    iIntros "Hφ".
    iApply (wp_store_interp_z with "[-Hφ]");eauto;[iFrame "∗ #"|].
    iNext. iIntros (ret) "[? | (%&%&%&%&%&%&?&?&?&?&?&?&?&%&%)]"
    ; iApply "Hφ" ; auto.
    iRight. simplify_eq.  iFrame.
    auto.
  Qed.

  Lemma clear_stack_interp_spec (W : WORLD) (C : CmptName) (r1 r2 : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (csp_p : Perm) (csp_g : Locality) (csp_b csp_e csp_a : Addr)
    φ :
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (clear_stack_instrs r1 r2))%a ->
    ( PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
      ∗ csp ↦ᵣ WCap csp_p csp_g csp_b csp_e csp_a
      ∗ interp W C (WCap csp_p csp_g csp_b csp_e csp_a)
      ∗ r1 ↦ᵣ WInt csp_e ∗ r2 ↦ᵣ WInt csp_a
      ∗ codefrag pc_a (clear_stack_instrs r1 r2)
      ∗ region W C
      ∗ sts_full_world W C
      ∗ ▷ ( (PC ↦ᵣ WCap pc_p pc_g pc_b pc_e (pc_a ^+ length (clear_stack_instrs r1 r2))%a
             ∗ csp ↦ᵣ WCap csp_p csp_g csp_b csp_e csp_a
             ∗ r1 ↦ᵣ WInt 0 ∗ r2 ↦ᵣ WCap csp_p csp_g csp_b csp_e csp_e
             ∗ codefrag pc_a (clear_stack_instrs r1 r2))
            -∗ WP Seq (Instr Executable) {{ φ }})
      ∗ ▷ φ FailedV
    )
      ⊢ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
    iIntros (Hpc_exec Hbounds)
      "(HPC & Hcsp & Hinterp & Hr1 & Hr2 & Hcode & Hr & Hsts & Hφ & Hfailed)".
    codefrag_facts "Hcode". clear H0.

    (* --- Sub r1 r2 r1 --- *)
    iInstr "Hcode".
    
    (* --- Mov r2 csp --- *)
    iInstr "Hcode".

    remember (WCap csp_p csp_g csp_b csp_e csp_a) as sp.
    rewrite{1 3} Heqsp. clear Heqsp.
    iLöb as "IH" forall (csp_a).
    iDestruct "Hinterp" as "#Hinterp".

    destruct (decide (csp_a = csp_e)).
    - (* csp_a = csp_2 ==> loop has ended *)
      replace (csp_a - csp_e)%Z with 0%Z by solve_addr.
      (* --- Jnz 2 r1 --- *)
      iInstr "Hcode".
      (* --- Jmp 5 ---- *)
      iInstr "Hcode".
      iApply "Hφ". subst. iFrame.
    - (* csp_a ≠ csp_2 ==> another iteration (or failure) *)
      (* --- Jnz 2 r1 --- *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_jnz_success_jmp_z with "[$HPC $Hi $Hr1]"); try solve_pure.
      { intros Hcontr; inversion Hcontr; solve_addr. }
      iIntros "!> (HPC & Hi & Hct2)".
      wp_pure.
      iSpecialize ("Hcode" with "[$]").

      (* --- Store r2 0%Z --- *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_interp_z_cap with "[$HPC $Hi $Hr $Hsts Hr2]"); try solve_pure.
      { iFrame "∗ #". }
      iIntros "!>" (v) "[-> | (-> & HPC & Hi & Hr2
      & Hr & Hsts & %Hwa & _)] /=".
      { wp_pure. wp_end. iFrame. }
      wp_pure.
      iSpecialize ("Hcode" with "[$]").

      (* --- Lea r2 1 --- *)
      destruct (csp_a + 1)%a eqn:Ha;cycle 1.
      { iInstr_lookup "Hcode" as "Hi" "Hcode".
        wp_instr.
        iApply (wp_Lea_fail_none_z with "[$HPC $Hi $Hr2]")
        ; try solve_pure
        ; eauto.
        iIntros "!> _". wp_pure. wp_end. iFrame. }
      iInstr "Hcode".

      (* --- Add r1 r1 1 --- *)
      iInstr "Hcode".

      (* --- Jmp -5 --- *)
      iInstr "Hcode".
      { instantiate (1:=(pc_a ^+ 2)%a). solve_addr. }

      (* IH *)
      replace (csp_a - csp_e + 1)%Z with (f - csp_e)%Z by solve_addr.
      iApply ("IH" $! f with "[] Hr Hsts Hφ Hfailed Hct2 Hcode HPC Hr2 Hcsp").
      iApply interp_lea;eauto.
      destruct csp_p,rx,w;auto. done.
  Qed.

  Lemma wp_unseal_unknown E pc_p pc_g pc_b pc_e pc_a pc_a' wi r1 r2 wsealr wsealed  :
    decodeInstrW wi = UnSeal r2 r1 r2 →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

    {{{  PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
          ∗ pc_a ↦ₐ wi
          ∗ r1 ↦ᵣ wsealr
          ∗ r2 ↦ᵣ wsealed
    }}}
      Instr Executable @ E
      {{{ retv, RET retv;
          ⌜ retv = FailedV ⌝
          ∨ ∃ psr gsr bsr esr asr wsb,
              ⌜ retv = NextIV ⌝
              ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ wi
              ∗ r1 ↦ᵣ wsealr
              ∗ r2 ↦ᵣ WSealable wsb
              ∗ ⌜ wsealr = (WSealRange psr gsr bsr esr asr) ⌝ ∗ ⌜ permit_unseal psr = true ⌝
              ∗ ⌜ wsealed = WSealed asr wsb ⌝
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpc_a' ϕ) "(HPC & Hpc_a & Hr1 & Hr2) Hφ".

    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_UnSeal with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | ]; iApply "Hφ"; [iRight | by iLeft].
    rewrite lookup_insert_ne // lookup_insert  in H2.
    rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert in H3.
    apply incrementPC_Some_inv in H6.
    destruct H6 as ( ppc & gpc & bpc & epc & apc & apc' & HPC & Hapc' & ->).
    rewrite lookup_insert_ne // lookup_insert in HPC.
    simplify_eq.
    iExists p, g, b, e, a, sb.
    rewrite (insert_commute _ _ PC) //.
    rewrite (insert_commute _ _ r1) //.
    rewrite !insert_insert.
    iDestruct (big_sepM_insert with "Hmap") as "[HPC Hmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_insert with "Hmap") as "[Hr1 Hmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_insert with "Hmap") as "[Hr2 Hmap]"; first by simplify_map_eq.
    iFrame; done.
  Qed.

  Lemma wp_unseal_unknown_sealed E pc_p pc_g pc_b pc_e pc_a pc_a' wi r1 r2 psr gsr bsr esr asr wsealed  :
    decodeInstrW wi = UnSeal r2 r1 r2 →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    permit_unseal psr = true ->
    (bsr <= asr < esr)%ot ->

    {{{  PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
          ∗ pc_a ↦ₐ wi
          ∗ r1 ↦ᵣ WSealRange psr gsr bsr esr asr
          ∗ r2 ↦ᵣ wsealed
    }}}
      Instr Executable @ E
      {{{ retv, RET retv;
          ⌜ retv = FailedV ⌝
          ∨ ∃ wsb,
              ⌜ retv = NextIV ⌝
              ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ wi
              ∗ r1 ↦ᵣ WSealRange psr gsr bsr esr asr
              ∗ r2 ↦ᵣ WSealable wsb
              ∗ ⌜ wsealed = WSealed asr wsb ⌝
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpc_a' Hpsr Hsr ϕ) "(HPC & Hpc_a & Hr1 & Hr2) Hφ".

    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_UnSeal with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | ]; iApply "Hφ"; [iRight | by iLeft].
    rewrite lookup_insert_ne // lookup_insert  in H2.
    rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert in H3.
    apply incrementPC_Some_inv in H6.
    destruct H6 as ( ppc & gpc & bpc & epc & apc & apc' & HPC & Hapc' & ->).
    rewrite lookup_insert_ne // lookup_insert in HPC.
    simplify_eq.
    iExists sb.
    rewrite (insert_commute _ _ PC) //.
    rewrite (insert_commute _ _ r1) //.
    rewrite !insert_insert.
    iDestruct (big_sepM_insert with "Hmap") as "[HPC Hmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_insert with "Hmap") as "[Hr1 Hmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_insert with "Hmap") as "[Hr2 Hmap]"; first by simplify_map_eq.
    iFrame; done.
  Qed.

  Lemma clear_registers_pre_call_skip_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (arg_rmap : Reg) (z : Z)
    (W : WORLD) (C : CmptName) φ :
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length clear_registers_pre_call_skip_instrs)%a ->

    is_arg_rmap arg_rmap ->
    (1 <= z <= 8)%Z ->

    ( PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
      ∗ ct2 ↦ᵣ WInt z
      ∗ ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg ∗ interp W C warg )
      ∗ codefrag pc_a clear_registers_pre_call_skip_instrs
      ∗ ▷ ( (∃ arg_rmap',
              ⌜ is_arg_rmap arg_rmap' ⌝
              ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e (pc_a ^+ length clear_registers_pre_call_skip_instrs)%a
              ∗ ct2 ↦ᵣ WInt z
              ∗ (  [∗ map] rarg↦warg ∈ arg_rmap', rarg ↦ᵣ warg ∗ interp W C warg )
              ∗ codefrag pc_a clear_registers_pre_call_skip_instrs)
               -∗ WP Seq (Instr Executable) {{ φ }})
    )
    ⊢ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
  Admitted.

  Lemma clear_registers_pre_call_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (rmap : Reg) φ :
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length clear_registers_pre_call_instrs)%a ->

    dom rmap = all_registers_s ∖ (dom_arg_rmap ∪ {[ PC ; cra ; cgp ; csp ]}) ->

    ( PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )
      ∗ codefrag pc_a clear_registers_pre_call_instrs
      ∗ ▷ ( (∃ (rmap' : Reg),
              ⌜ dom rmap' = all_registers_s ∖ (dom_arg_rmap ∪ {[ PC ; cra ; cgp ; csp ]}) ⌝
              ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e (pc_a ^+ length clear_registers_pre_call_instrs)%a
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              ∗ codefrag pc_a clear_registers_pre_call_instrs)
               -∗ WP Seq (Instr Executable) {{ φ }})
    )
    ⊢ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
  Admitted.
  
  Axiom foo : False.

  Lemma switcher_call_ftlr (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
    (cstk : CSTK) (wstk : Word)
    (Nswitcher : namespace)
    :
    (∀ x, is_Some (regs !! x)) ->
    regs !! csp = Some wstk ->
    ftlr_IH -∗
    (∀ (r : RegName) (v : leibnizO Word) , ⌜r ≠ PC⌝ → ⌜regs !! r = Some v⌝ → interp W C v) -∗
    na_inv logrel_nais Nswitcher switcher_inv -∗
    interp_continuation cstk W C -∗
    sts_full_world W C -∗
    na_own logrel_nais ⊤ -∗
    cstack_frag cstk -∗
    ([∗ map] k↦y ∈ <[PC:=WCap XSRW_ Local b_switcher e_switcher a_switcher_call]> regs , k ↦ᵣ y) -∗
    region W C -∗
    ▷ (£ 1 -∗ WP Seq (Instr Executable) {{ v0, ⌜v0 = HaltedV⌝ → na_own logrel_nais ⊤ }}).
  Proof.
    iIntros (Hfull_rmap Hwstk) "#IH #Hreg #Hinv_switcher Hcont Hsts Hna Hcstk Hrmap Hr".
    iNext; iIntros "_".

    (* --- Extract the code from the invariant --- *)
    iMod (na_inv_acc with "Hinv_switcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    rewrite /switcher_inv.
    iDestruct "Hswitcher_inv"
      as (a_tstk cstk' tstk_next)
           "(>Hmtdc & >%Hot_bounds & >Hcode & >Hb_switcher & >Htstk & >[%Hbounds_tstk_b %Hbounds_tstk_e]
           & Hcstk_full & >%Hlen_cstk & Hstk_interp & #Hp_ot_switcher)".
    codefrag_facts "Hcode".
    rename H into Hcont_switcher_region.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hinv_switcher" as hinv_switcher.

    iExtract "Hrmap" PC as "HPC".
    iExtract "Hrmap" csp as "Hcsp".
    specialize (Hfull_rmap cs0) as HH;destruct HH as [? ?].
    specialize (Hfull_rmap cs1) as HH;destruct HH as [? ?].
    specialize (Hfull_rmap cra) as HH;destruct HH as [? ?].
    specialize (Hfull_rmap cgp) as HH;destruct HH as [? ?].
    specialize (Hfull_rmap ct2) as HH;destruct HH as [? ?].
    specialize (Hfull_rmap ctp) as HH;destruct HH as [? ?].
    specialize (Hfull_rmap ct1) as HH;destruct HH as [? ?].
    iExtract "Hrmap" cs0 as "Hcs0".
    iExtract "Hrmap" cs1 as "Hcs1".
    iExtract "Hrmap" cra as "Hcra".
    iExtract "Hrmap" cgp as "Hcgp".
    iExtract "Hrmap" ct2 as "Hct2".
    iExtract "Hrmap" ctp as "Hctp".
    iExtract "Hrmap" ct1 as "Hct1".

    set (Hcall := switcher_call_entry_point).
    set (Hsize := switcher_size).
    assert (SubBounds b_switcher e_switcher a_switcher_call (a_switcher_call ^+(length switcher_instrs))%a)
      by solve_addr.
    
    (* --- Store csp cs0 --- *)
    iDestruct ("Hreg" $! csp with "[//] [//]") as "#Hspv".
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.    
    iApply (wp_store_interp with "[$HPC $Hi Hcsp Hcs0 $Hr $Hsts]"); try solve_pure.
    { iFrame. iFrame "#". by iApply "Hreg";eauto. }
    iIntros "!>" (v) "[-> | (% & % & % & % & % & -> & -> & HPC & Hi & Hcs0
    & Hcsp & Hr & Hsts & %Hcanstore & %bounds)] /=".
    { wp_pure. wp_end. iIntros "%Hcontr";done. }
    wp_pure.
    iSpecialize ("Hcode" with "[$]").

    (* --- Lea csp 1 --- *)
    destruct (a + 1)%a eqn:Ha1;cycle 1.
    { iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_Lea_fail_none_z with "[$HPC $Hi $Hcsp]")
      ; try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done. }
    iInstr "Hcode".

    (* --- Store csp cs1 --- *)
    assert (isO p = false) as Hno.
    { apply canStore_writeAllowed in Hcanstore.
      destruct p,w,rx;auto. }
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.    
    iApply (wp_store_interp_cap with "[$HPC $Hi Hcsp Hcs1 $Hr $Hsts]"); try solve_pure.
    { iFrame. iSplit;[by iApply "Hreg";eauto|].
      by iApply (interp_lea with "Hspv"). }
    iIntros "!>" (v) "[-> | (-> & HPC & Hi & Hcs1
    & Hcsp & Hr & Hsts & _)] /=".
    { wp_pure. wp_end. iIntros "%Hcontr";done. }
    wp_pure.
    iSpecialize ("Hcode" with "[$]").

    (* --- Lea csp 1 --- *)
    destruct (f + 1)%a eqn:Ha2;cycle 1.
    { iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_Lea_fail_none_z with "[$HPC $Hi $Hcsp]")
      ; try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done. }
    iInstr "Hcode".

    (* --- Store csp cra --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.    
    iApply (wp_store_interp_cap with "[$HPC $Hi Hcsp Hcra $Hr $Hsts]"); try solve_pure.
    { iFrame. iSplit;[by iApply "Hreg";eauto|].
      by iApply (interp_lea with "Hspv"). }
    iIntros "!>" (v) "[-> | (-> & HPC & Hi & Hcra
    & Hcsp & Hr & Hsts & _)] /=".
    { wp_pure. wp_end. iIntros "%Hcontr";done. }
    wp_pure.
    iSpecialize ("Hcode" with "[$]").

    (* --- Lea csp 1 --- *)
    destruct (f0 + 1)%a eqn:Ha3;cycle 1.
    { iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_Lea_fail_none_z with "[$HPC $Hi $Hcsp]")
      ; try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done. }
    iInstr "Hcode".


    (* --- Store csp cs1 --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.    
    iApply (wp_store_interp_cap with "[$HPC $Hi Hcsp Hcgp $Hr $Hsts]"); try solve_pure.
    { iFrame. iSplit;[by iApply "Hreg";eauto|].
      by iApply (interp_lea with "Hspv"). }
    iIntros "!>" (v) "[-> | (-> & HPC & Hi & Hcgp
    & Hcsp & Hr & Hsts & _)] /=".
    { wp_pure. wp_end. iIntros "%Hcontr";done. }
    wp_pure.
    iSpecialize ("Hcode" with "[$]").

    (* --- Lea csp 1 --- *)
    destruct (f1 + 1)%a eqn:Ha4;cycle 1.
    { iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_Lea_fail_none_z with "[$HPC $Hi $Hcsp]")
      ; try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done. }
    iInstr "Hcode".

    (* --- GetP ct2 csp --- *)
    iInstr "Hcode".

    (* ---  Mov ctp (encodePerm RWL) --- *)
    iInstr "Hcode".

    (* --- Sub ct2 ct2 ctp --- *)
    iInstr "Hcode".

    (* --- Jnz 2 ct2 --- *)
    destruct (decide (p = RWL));cycle 1.
    { (* p ≠ RWL *)
      assert ((encodePerm p - encodePerm RWL)%Z ≠ 0) as Hne.
      { destruct (decide (encodePerm p = encodePerm RWL));[|lia].
        apply encodePerm_inj in e0. congruence. }
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_jnz_success_jmp_z with "[$HPC $Hi $Hct2]"); try solve_pure.
      { intros Hcontr; inversion Hcontr; done. }
      iIntros "!> (HPC & Hi & Hct2)".
      wp_pure.
      iSpecialize ("Hcode" with "[$]").
      iInstr "Hcode".
      wp_end. iIntros "%Hcontr";done.
    }
    (* p = RWL *)
    subst p. replace (encodePerm RWL - encodePerm RWL)%Z with 0%Z by lia.
    iInstr "Hcode".

    (* --- Jmp 2 --- *)
    iInstr "Hcode".

    (* --- GetL ct2 csp --- *)
    iInstr "Hcode".

    (* --- Mov ctp (encodeLoc Local) --- *)
    iInstr "Hcode".

    (* --- Sub ct2 ct2 ctp --- *)
    iInstr "Hcode".

    (* --- Jnz 2 ct2 --- *)
    destruct (decide (g = Local));cycle 1.
    { (* g ≠ Local *)
      assert ((encodeLoc g - encodeLoc Local)%Z ≠ 0) as Hne.
      { destruct (decide (encodeLoc g = encodeLoc Local));[|lia].
        apply encodeLoc_inj in e0. congruence. }
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_jnz_success_jmp_z with "[$HPC $Hi $Hct2]"); try solve_pure.
      { intros Hcontr; inversion Hcontr; done. }
      iIntros "!> (HPC & Hi & Hct2)".
      wp_pure.
      iSpecialize ("Hcode" with "[$]").
      iInstr "Hcode".
      wp_end. iIntros "%Hcontr";done.
    }
    (* g = Local *)
    subst g. replace (encodeLoc Local - encodeLoc Local)%Z with 0%Z by lia.
    iInstr "Hcode".

    (* --- Jmp 2 --- *)
    iInstr "Hcode".

    (* --- ReadSR ct2 mtdc --- *)
    iInstr "Hcode".

    (* --- Lea ct2 1 --- *)
    destruct (a_tstk + 1)%a eqn:Hastk;cycle 1.
    { iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_Lea_fail_none_z with "[$HPC $Hi $Hct2]")
      ; try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done. }
    iInstr "Hcode".

    (* --- Store ct2 csp --- *)
    destruct (decide (f3 < e_trusted_stack)%a); cycle 1.
    { iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg with "[$HPC $Hi $Hcsp $Hct2]");try solve_pure.
      { rewrite /withinBounds. solve_addr+n Hastk. }
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done. }
    
    iDestruct (big_sepL2_length with "Htstk") as %Hlen.
    erewrite finz_incr_eq in Hlen;[|eauto].
    rewrite finz_seq_between_length in Hlen.
    destruct tstk_next.
    { exfalso.
      rewrite /= /finz.dist Z2Nat.inj_sub in Hlen;[|solve_addr].
      assert (e_trusted_stack = f3) as Heq;[solve_addr|].
      subst. solve_addr. }
    assert (is_Some (f3 + 1)%a) as [f4 Hf4];[solve_addr|].
    iDestruct (region_pointsto_cons _ f4 with "Htstk") as "[Hf3 Htstk]";[solve_addr|solve_addr|].
    replace (a_tstk ^+ 1)%a with f3 by solve_addr.
    iInstr "Hcode".
    { solve_addr. }

    (* --- WriteSR mtdc ct2 --- *)
    iInstr "Hcode".

    (* --- GetE cs0 csp --- *)
    iInstr "Hcode".

    (* --- GetA cs1 csp --- *)
    iInstr "Hcode".

    (* --- Subseg csp cs1 cs0 --- *)
    iInstr "Hcode".
    { solve_addr. }

    (* --- clear stack --- *)
    rewrite /switcher_instrs /switcher_call_instrs -app_assoc -app_assoc.
    focus_block 1 "Hcode" as a_clear_stk1 Ha_clear_stk1 "Hcode" "Hcls". iHide "Hcls" as hcont.
    iApply (clear_stack_interp_spec with "[- $HPC $Hcode $Hcsp $Hcs0 $Hcs1 $Hr $Hsts]"); try solve_pure.
    iSplit.
    { iApply interp_weakeningEO;eauto. all: solve_addr. }
    iSplitL;cycle 1.
    { iIntros "!> %Hcontr"; done. }
    iIntros "!> (HPC & Hcsp & Hcs0 & Hcs1 & Hcode)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
    focus_block 2 "Hcode" as a_rest Ha_rest "Hcode" "Hcls". iHide "Hcls" as hcont.

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
    iApply (wp_lea_success_reg with "[$HPC $Hi $Hcs0 $Hcs1]");[solve_pure..| |].
    { instantiate (1:=(b_switcher ^+ 2)%a). solve_addr. }
    iIntros "!> (HPC & Hi & Hcs1 & Hcs0)".
    wp_pure.
    iSpecialize ("Hcode" with "[$]").

    (* --- Lea cs0 -2 --- *)
    iInstr "Hcode".
    { instantiate (1:= b_switcher). solve_addr. }

    (* --- Load cs0 cs0 --- *)
    iInstr "Hcode".

    (* --- UnSeal ct1 cs0 ct1 --- *)
    rewrite /load_word. iSimpl in "Hcs0".
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_unseal_unknown with "[$HPC $Hi $Hcs0 $Hct1]"); try solve_pure.
    iIntros "!>" (ret) "[-> | (% & % & % & % & % & %wsb & -> & HPC & Hi & Hcs0 & Hct1 & %Heq & % & %spec)]".
    { wp_pure. wp_end. iIntros "%Hcontr";done. }
    simplify_eq.

    (* get the seal inv and compare with wsb *)
    iDestruct ("Hreg" $! ct1 with "[//] [//]") as "#Hct1v".
    rewrite (fixpoint_interp1_eq _ _ (WSealed ot_switcher wsb)).
    iDestruct "Hct1v" as (P HpersP) "(HmonoP & HPseal & HP & HPborrow)".
    iDestruct (seal_pred_agree with "Hp_ot_switcher HPseal") as "Hagree".
    iSpecialize ("Hagree" $! (W,C,WSealable wsb)).
    
    wp_pure.
    iSpecialize ("Hcode" with "[$]").
    rewrite /safeC.
    iSimpl in "Hagree".
    iRewrite -"Hagree" in "HP".
    iDestruct "HP" as (?????????? Heq????) "(Htbl1 & Htbl2 & Htbl3 & Hexec)". simpl fst. simpl snd.
    inversion Heq.
    
    (* --- Load cs0 ct1 --- *)
    wp_instr.
    iInv "Htbl3" as ">Ha_tbl" "Hcls_tbl".
    iInstr "Hcode".
    { split;auto. solve_addr. }
    iMod ("Hcls_tbl" with "[$]") as "_". iModIntro.
    wp_pure.

    (* --- LAnd ct2 cs0 7 --- *)
    iInstr "Hcode".

    (* --- LShiftR cs0 cs0 3 --- *)
    iInstr "Hcode".

    (* --- GetB cgp ct1 --- *)
    iInstr "Hcode".

    (* --- GetA cs1 ct1 --- *)
    iInstr "Hcode".

    (* --- Sub cs1 cgp cs1 --- *)
    iInstr "Hcode".

    (* --- Lea ct1 cs1 --- *)
    iInstr "Hcode".
    { instantiate (1:=b_tbl). solve_addr-. }

    (* --- Load cra ct1 --- *)
    wp_instr.
    iInv "Htbl1" as ">Hb_tbl" "Hcls_tbl".
    iInstr "Hcode".
    { split;auto. solve_addr. }
    iMod ("Hcls_tbl" with "[$]") as "_". iModIntro.
    wp_pure.

    (* --- Lea ct1 1 --- *)
    iInstr "Hcode".
    { instantiate (1:=(b_tbl ^+ 1)%a). solve_addr. }

    (* --- Load cgp ct1 --- *)
    wp_instr.
    iInv "Htbl2" as ">Hb_tbl" "Hcls_tbl".
    iInstr "Hcode".
    { split;auto. solve_addr. }
    iMod ("Hcls_tbl" with "[$]") as "_". iModIntro.
    wp_pure.

    (* --- Lea cra cs0 --- *)
    destruct (bpcc + encode_entry_point nargs off ≫ 3)%a eqn:Hentry;cycle 1.
    { iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_Lea_fail_none_reg with "[$HPC $Hi $Hcs0 $Hcra]")
      ; try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    iInstr "Hcode".

    (* --- Add ct2 ct2 1 --- *)
    iInstr "Hcode".

    (* clear registers except parameters *)
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
    rewrite -!app_assoc.
    focus_block 3 "Hcode" as a_clear Ha_clear "Hcode" "Hcls". iHide "Hcls" as hcont.

    match goal with |- context [ ([∗ map] k↦y ∈ ?r , k ↦ᵣ y)%I ] => set (rmap' := r) end.
    set (params := ({[ca0; ca1; ca2; ca3; ca4; ca5; ca5; ct0]} : gset RegName)).
    set (Pf := ((λ '(r,_), r ∈ params) : RegName * Word → Prop)).
    rewrite -(map_filter_union_complement Pf rmap').
    iDestruct (big_sepM_union with "Hrmap") as "[Hparams Hrest]".
    { apply map_disjoint_filter_complement. }
    
    iApply (clear_registers_pre_call_skip_spec with "[- $HPC $Hct2 $Hcode]"); try solve_pure.
    { instantiate (1:=filter (λ v : RegName * Word, (Pf v)%type) rmap').
      rewrite /is_arg_rmap /dom_arg_rmap.
      apply dom_filter_L. clear -Hfull_rmap.
      rewrite /rmap'. split.
      - intros Hi.
        repeat (rewrite lookup_delete_ne;[|set_solver]).
        specialize (Hfull_rmap i) as [x Hx].
        exists x. split;auto.
      - intros [? [? ?] ]. auto. }
    { rewrite /encode_entry_point.  bitblast. solve_addr. lia. }
    

    

    
    
End fundamental.
