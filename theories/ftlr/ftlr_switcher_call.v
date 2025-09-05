From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel region_invariants bitblast.
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
             ∗ region W C ∗ sts_full_world W C
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
    iIntros (Hexec Hbounds Hargmap Hz) "(HPC & Hct2 & Hargs & Hcode & Hcont)".
    codefrag_facts "Hcode". clear H0.

    assert (∃ w0 w1 w2 w3 w4 w5 w, arg_rmap = <[ca0:=w0]> (<[ca1:=w1]> (<[ca2:=w2]> (<[ca3:=w3]> (<[ca4:=w4]>
             (<[ca5:=w5]> (<[ct0:=w]> ∅))))))) as [w0 [w1 [w2 [w3 [w4 [w5 [w Heq] ] ] ] ] ] ].
    { assert (is_Some (arg_rmap !! ca0)) as [??];[apply elem_of_dom; rewrite Hargmap; set_solver|].
      assert (is_Some (arg_rmap !! ca1)) as [??];[apply elem_of_dom; rewrite Hargmap; set_solver|].
      assert (is_Some (arg_rmap !! ca2)) as [??];[apply elem_of_dom; rewrite Hargmap; set_solver|].
      assert (is_Some (arg_rmap !! ca3)) as [??];[apply elem_of_dom; rewrite Hargmap; set_solver|].
      assert (is_Some (arg_rmap !! ca4)) as [??];[apply elem_of_dom; rewrite Hargmap; set_solver|].
      assert (is_Some (arg_rmap !! ca5)) as [??];[apply elem_of_dom; rewrite Hargmap; set_solver|].
      assert (is_Some (arg_rmap !! ct0)) as [??];[apply elem_of_dom; rewrite Hargmap; set_solver|].
      exists x,x0,x1,x2,x3,x4,x5. apply map_eq.
      intros i. destruct (decide (ca0 = i));simplify_map_eq=>//.
      destruct (decide (ca1 = i));simplify_map_eq=>//.
      destruct (decide (ca2 = i));simplify_map_eq=>//.
      destruct (decide (ca3 = i));simplify_map_eq=>//.
      destruct (decide (ca4 = i));simplify_map_eq=>//.
      destruct (decide (ca5 = i));simplify_map_eq=>//.
      destruct (decide (ct0 = i));simplify_map_eq=>//.
      apply not_elem_of_dom. rewrite Hargmap. set_solver. }

    rewrite Heq.
    repeat (rewrite big_sepM_insert;[|simplify_map_eq=>//]).
    iDestruct "Hargs" as "([Hca0 #Hca0v] & [Hca1 #Hca1v] & [Hca2 #Hca2v] & [Hca3 #Hca3v]
    & [Hca4 #Hca4v] & [Hca5 #Hca5v] & [Hct0 #Hct0v] & _)".

    (* Hardcoded proof of cases *)
    destruct (decide (1 = z)%Z);[subst|].
    { iGo "Hcode".
      iApply "Hcont".
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      repeat (rewrite big_sepM_insert;[|simplify_map_eq=>//]).
      iFrame. repeat iSplit;[|iApply interp_int..|done].
      iPureIntro. rewrite /is_arg_rmap !dom_insert_L. set_solver. }

    destruct (decide (2 = z)%Z);[subst|].
    { iGo "Hcode".
      iApply "Hcont".
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      repeat (rewrite big_sepM_insert;[|simplify_map_eq=>//]).
      iFrame "∗ #". repeat iSplit;[|iApply interp_int..|done].
      iPureIntro. rewrite /is_arg_rmap !dom_insert_L. set_solver. }

    destruct (decide (3 = z)%Z);[subst|].
    { iGo "Hcode".
      iApply "Hcont".
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      repeat (rewrite big_sepM_insert;[|simplify_map_eq=>//]).
      iFrame "∗ #". repeat iSplit;[|iApply interp_int..|done].
      iPureIntro. rewrite /is_arg_rmap !dom_insert_L. set_solver. }

    destruct (decide (4 = z)%Z);[subst|].
    { iGo "Hcode".
      iApply "Hcont".
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      repeat (rewrite big_sepM_insert;[|simplify_map_eq=>//]).
      iFrame "∗ #". repeat iSplit;[|iApply interp_int..|done].
      iPureIntro. rewrite /is_arg_rmap !dom_insert_L. set_solver. }

    destruct (decide (5 = z)%Z);[subst|].
    { iGo "Hcode".
      iApply "Hcont".
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      repeat (rewrite big_sepM_insert;[|simplify_map_eq=>//]).
      iFrame "∗ #". repeat iSplit;[|iApply interp_int..|done].
      iPureIntro. rewrite /is_arg_rmap !dom_insert_L. set_solver. }

    destruct (decide (6 = z)%Z);[subst|].
    { iGo "Hcode".
      iApply "Hcont".
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      repeat (rewrite big_sepM_insert;[|simplify_map_eq=>//]).
      iFrame "∗ #". repeat iSplit;[|iApply interp_int..|done].
      iPureIntro. rewrite /is_arg_rmap !dom_insert_L. set_solver. }

    destruct (decide (7 = z)%Z);[subst|].
    { iGo "Hcode".
      iApply "Hcont".
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      repeat (rewrite big_sepM_insert;[|simplify_map_eq=>//]).
      iFrame "∗ #". repeat iSplit;[|iApply interp_int..|done].
      iPureIntro. rewrite /is_arg_rmap !dom_insert_L. set_solver. }

    destruct (decide (8 = z)%Z);[subst|].
    { iGo "Hcode".
      iApply "Hcont".
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      repeat (rewrite big_sepM_insert;[|simplify_map_eq=>//]).
      iFrame "∗ #". repeat iSplit;[|iApply interp_int..|done].
      iPureIntro. rewrite /is_arg_rmap !dom_insert_L. set_solver. }

    exfalso. lia.
  Qed.

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
    iIntros (Hx Hbounds Hdom) "(HPC & Hregs & Hcode & Hcont)".

    iAssert ([∗ map] r↦_ ∈ rmap, ∃ w, r ↦ᵣ w)%I with "[Hregs]" as "Hregs".
    { iApply (big_sepM_mono with "Hregs"). intros. eauto. }

    iDestruct (big_sepM_dom with "Hregs") as "Hregs".
    rewrite Hdom.

    iDestruct (big_sepS_delete _ _ cnull with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ ctp with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ ct1 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ ct2 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs0 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs1 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ ca6 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ ca7 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs2 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs3 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs4 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs5 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs6 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs7 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs8 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs9 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs10 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs11 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ ct3 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ ct4 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ ct5 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ ct6 with "Hregs") as "[[% ?] _]";[set_solver|].

    codefrag_facts "Hcode". clear H0.
    iGo "Hcode".
    
    iApply "Hcont".
    iExists (<[cnull:=_]> (<[ctp:=_]> (<[ct1:=_]> (<[ct2:=_]> (<[cs0:=_]> (<[cs1:=_]> (<[ca6:=_]> (<[ca7:=_]> (<[cs2:=_]> (<[cs3:=_]> (<[cs4:=_]> (<[cs5:=_]> (<[cs6:=_]> (<[cs7:=_]> (<[cs8:=_]> (<[cs9:=_]> (<[cs10:=_]> (<[cs11:=_]> (<[ct3:=_]> (<[ct4:=_]> (<[ct5:=_]> (<[ct6:=_]> ∅)))))))))))))))))))))).
    repeat (rewrite big_sepM_insert;[|by simplify_map_eq]).
    iFrame. iSplit.
    { iPureIntro. rewrite !dom_insert_L. set_solver. }
    repeat (iSplit;[done|]). done.
  Qed.   

  Lemma switcher_call_ftlr (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
    (cstk : CSTK) (wstk : Word)
    (Nswitcher : namespace)
    :
    specification_switcher_entry_point W C regs cstk wstk Nswitcher a_switcher_call.
  Proof.
    iIntros (Hfull_rmap Hwstk) "#IH #Hreg #Hinv_switcher Hcont Hsts Hna Hcstk Hrmap Hr".

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
    & Hcsp & Hr & Hsts & _ & %bounds')] /=".
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
    iIntros "!> ((HPC & Hcsp & Hcs0 & Hcs1 & Hcode) & Hr & Hsts)".
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
    { rewrite encode_entry_point_eq_nargs;[lia|]. auto. }
    iSplitL "Hparams".
    { iApply big_sepM_sep. iFrame. iApply big_sepM_forall.
      iIntros (k v [Hin Hspec]%map_lookup_filter_Some).
      iApply ("Hreg" $! k);iPureIntro. set_solver+Hspec.
      repeat (apply lookup_delete_Some in Hin as [_ Hin]). auto. }
    iIntros "!> (%arg_rmap' & %Hisarg_rmap' & HPC & Hct2 & Hparams & Hcode)".
    
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
    focus_block 4 "Hcode" as a_clear' Ha_clear' "Hcode" "Hcls". iHide "Hcls" as hcont.

    rewrite /rmap'. rewrite !map_filter_delete.
    iDestruct (big_sepM_insert with "[$Hrest $Hct1]") as "Hrest"
    ; [clear; by simplify_map_eq|rewrite insert_delete_insert].
    rewrite -(delete_insert_ne _ ctp);[|auto].
    iDestruct (big_sepM_insert with "[$Hrest $Hctp]") as "Hrest"
    ; [clear; by simplify_map_eq|rewrite insert_delete_insert].
    repeat (rewrite -(delete_insert_ne _ ct2);[|auto]).
    iDestruct (big_sepM_insert with "[$Hrest $Hct2]") as "Hrest"
    ; [clear; by simplify_map_eq|rewrite insert_delete_insert].
    repeat (rewrite (delete_commute _ _ cs1)//). repeat rewrite -(delete_insert_ne _ cs1)//.
    iDestruct (big_sepM_insert with "[$Hrest $Hcs1]") as "Hrest"
    ; [clear; by simplify_map_eq|rewrite insert_delete_insert].
    repeat (rewrite (delete_commute _ _ cs0)//). repeat rewrite -(delete_insert_ne _ cs0)//.
    iDestruct (big_sepM_insert with "[$Hrest $Hcs0]") as "Hrest"
    ; [clear; by simplify_map_eq|rewrite insert_delete_insert].

    iApply (clear_registers_pre_call_spec with "[- $HPC $Hcode $Hrest]"); try solve_pure.
    { clear -Hfull_rmap. apply regmap_full_dom in Hfull_rmap as Heq.
      rewrite !dom_insert_L !dom_delete_L.
      cut (dom (filter (λ v, ¬ Pf v) regs) = all_registers_s ∖ dom_arg_rmap);[set_solver|].
      apply (dom_filter_L _ (regs : gmap RegName Word)).
      split.
      - intros [Hi Hni]%elem_of_difference.
        specialize (Hfull_rmap i) as [x Hx]. eauto.
      - intros [? [? ?] ]. apply elem_of_difference.
        split;auto. apply all_registers_s_correct. }

    iIntros "!> (%rmap'' & %Hrmap'' & HPC & Hrest & Hcode)".

    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
    focus_block 5 "Hcode" as a_jalr Ha_halr "Hcode" "Hcls". iHide "Hcls" as hcont.

    eset (frame :=
           {| wret := WInt 0;
              wstk := (WCap RWL Local b e a);
              wcgp := WInt 0;
              wcs0 := WInt 0;
              wcs1 := WInt 0;
              is_untrusted_caller := true
           |}).

    iSpecialize ("Hexec" $! _ W (frame :: cstk) with "[]").
    { iPureIntro. apply related_sts_priv_refl_world. }
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
    rewrite /load_word. iSimpl in "Hcgp".

    iDestruct (cstack_agree with "Hcstk_full Hcstk") as %Heq'. subst.
    iMod (cstack_update _ _ (frame :: cstk) with "Hcstk_full Hcstk") as "[Hcstk_full Hcstk]".
    iMod ("Hclose_switcher_inv" with "[$Hcode $Hna Hb_switcher $Hcstk_full Hmtdc Htstk Hf3 Hstk_interp]") as "HH".
    { iNext. iExists _,_. iFrame "∗ #".
      rewrite (finz_incr_eq Hf4).
      replace (f3 ^+ -1)%a with a_tstk by solve_addr+Hastk.
      iFrame. simpl. iPureIntro.
      repeat (split;auto);[solve_addr..|repeat f_equiv;solve_addr].
    }

    iApply "Hexec".
    iSplitL "Hcont".
    { iFrame. iNext. simpl.
      iSplit.
      - iApply (interp_weakening with "IH Hspv");auto;solve_addr.
      - iIntros (W' HW' ???) "(HPC & _)".
        rewrite /interp_conf.
        wp_instr.
        iApply (wp_notCorrectPC with "[$]").
        { intros Hcontr;inversion Hcontr. }
        iIntros "!> HPC". wp_pure. wp_end. iIntros (Hcontr);done. }
    iFrame.
    rewrite /execute_entry_point_register.
    iDestruct (big_sepM_sep with "Hrest") as "[Hrest #Hnil]".
    iDestruct (big_sepM_sep with "Hparams") as "[Hparams #Hval]".
    iDestruct (big_sepM_union with "[$Hparams $Hrest]") as "Hregs".
    { apply map_disjoint_dom. rewrite Hrmap'' Hisarg_rmap'.
      rewrite /dom_arg_rmap. clear. set_solver. }
    iDestruct (big_sepM_insert_2 with "[Hcsp] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hcra] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hcgp] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[HPC] Hregs") as "Hregs";[iFrame|].
    
    iFrame.
    iSplit.
    { iPureIntro. simpl. intros rr. clear -Hisarg_rmap' Hrmap''.
      destruct (decide (rr = PC));simplify_map_eq;[eauto|].
      destruct (decide (rr = cgp));simplify_map_eq;[eauto|].
      destruct (decide (rr = cra));simplify_map_eq;[eauto|].
      destruct (decide (rr = csp));simplify_map_eq;[eauto|].
      apply elem_of_dom. rewrite dom_union_L Hrmap'' Hisarg_rmap'.
      rewrite difference_union_distr_r_L union_intersection_l.
      rewrite -union_difference_L;[|apply all_registers_subseteq].
      apply elem_of_intersection. split;[apply all_registers_s_correct|].
      apply elem_of_union. right.
      apply elem_of_difference. split;[apply all_registers_s_correct|set_solver]. }

    iSplit;[|iSplit;[|iSplit;[|iSplit;[|iSplit] ] ] ].
    - clear-Hentry. iPureIntro. simplify_map_eq. repeat f_equiv.
      rewrite encode_entry_point_eq_off in Hentry. solve_addr.
    - iPureIntro. clear. simplify_map_eq. auto.
    - iIntros (wstk Hwstk'). simplify_map_eq.
      iApply (interp_weakening with "IH Hspv");auto.
      solve_addr. solve_addr-.
    - iIntros (wret Hwret). simplify_map_eq.
      iApply fixpoint_interp1_eq. iSimpl.
      assert (is_switcher_entry_point XSRW_ Local b_switcher e_switcher (a_jalr ^+ 1)%a = true) as ->;[|done].
      rewrite /is_switcher_entry_point. rewrite bool_decide_true// bool_decide_true// /=.
      rewrite !Z.eqb_refl /=.
      rewrite orb_true_iff;simpl. left.
      rewrite orb_true_iff;simpl. right.
      pose proof switcher_return_entry_point.
      solve_addr.
    - iIntros (r v Hr Hv).
      repeat (rewrite lookup_insert_ne in Hv;[|set_solver+Hr]).
      rewrite lookup_union_l in Hv;cycle 1.
      { apply not_elem_of_dom. rewrite Hrmap''.
        apply not_elem_of_difference. right.
        apply elem_of_union. by left. }
      iDestruct (big_sepM_lookup with "Hval") as "$". apply Hv.
    - iIntros (r Hnin).
      apply not_elem_of_union in Hnin as [Hnin1 Hnin2].
      assert (is_Some (rmap'' !! r)) as [v Hin].
      { apply elem_of_dom. rewrite Hrmap''.
        apply elem_of_difference. split;[apply all_registers_s_correct|].
        apply not_elem_of_union. auto. }
      iDestruct (big_sepM_lookup with "Hnil") as %Hnil;[eauto|].
      iPureIntro.
      repeat (rewrite lookup_insert_ne;[|set_solver+Hnin1 Hnin2]).
      rewrite lookup_union_r;[subst;auto|].
      apply not_elem_of_dom. by rewrite Hisarg_rmap'.
  Qed.
    
End fundamental.
