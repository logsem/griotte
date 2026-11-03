From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import adequacy.
From iris.base_logic Require Import invariants.
From griotte Require Import logrel monotone interp_weakening.
From griotte Require Import assert_spec.
From griotte Require Import
  world_interp_revocation world_interp_allocation world_interp_allocation_compartments.
From griotte Require Import switcher_base_interp.
From griotte Require Import stack_world_resources mkregion_helpers disjoint_regions_tactics.
From griotte Require Import compartment_layout switcher_adequacy adequacy_helpers adequacy_common.
From griotte Require Import allocator_resources heap_region.
From griotte Require Import firmware_ok.
(* Imported last: the fields of the image records shadow the fields of the
   layout records of [compartment_layout] and of [switcherLayout]. *)
From griotte Require Import image firmware.
From griotte Require Export firmware_adequacy_obligations.

Section adequacy.
  (* The user threads [0] and [S k] meet here: every form names its thread. *)
  #[local] Remove Hints ceriseG_of : typeclass_instances.

Theorem firmware_adequacy (Σ : gFunctors)
    {inv_preg : invGpreS Σ}
    {cerise_preg : ceriseGpreS Σ}
    {na_invg : na_invariants.na_invG Σ}
    {Cname : CmptNameG}
    {seal_store_preg : sealStorePreG Σ}
    {sts_preg : STS_preG Σ}
    {cstack_preg : CSTACK_preG Σ}
    {relpreg : relGpreS Σ}
    `{MP : MachineParameters}
    (fw : firmware) (img : fw_image) (σ σ' : ExecConf) (es : list griotte_lang.expr) :
  fw_obligations Σ fw →
  firmware_ok fw img σ →
  rtc erased_step ([Exec], σ) (es, σ') →
  mem σ' !! flag_assert (img_asrt img) = Some (WInt 0).
Proof.
  intros [cthreads Hobl] Hok Hstep.
  destruct σ as [w_pc regs sregs m sh td].
  destruct σ' as [w_pc' regs' sregs' m' sh' td'].
  pose proof Hok as (_ & [_ Hsh] & Hregs & Hwf).
  change (shadowtbl (MkExecConf w_pc regs sregs m sh td)) with sh in Hsh. rewrite /note in Hsh.
  destruct (regs_ok_inv _ _ _ Hregs) as ([fts Hthreads] & _ & _ & _ & _ & _ & _ & _ & Hsreg).
  clear Hregs.
  change (sreg (MkExecConf w_pc regs sregs m sh td)) with sregs in Hsreg.
  pose proof (firmware_ok_thread0 _ _ _ Hok) as H0.
  pose proof (img_wf_switcher_layout _ _ _ _ H0 Hwf) as Hsw.
  pose proof (img_wf_trusted_stack_layout _ _ _ _ H0 Hwf) as Hts.
  pose proof (img_wf_assert_layout _ _ Hwf) as Hasrt.
  destruct (img_wf_otypes _ _ Hwf) as [Hot_nodup _].
  apply NoDup_cons in Hot_nodup as [Hot_notin Hot_nodup].
  destruct (firmware_ok_ghost_init_cond _ _ _ _ _ _ _ _ Hok) as [Hinit Hnull].
  (* The program-logic resources of the initial state. The mtdc of the user
     thread [S k] holds its trusted stack. *)
  eapply (cerise_flag_adequacy Σ (TV := fw_trap_vector img)
            Nassert_flag (flag_assert (img_asrt img)) (fw_set (fw_heap_roots fw))
            _ _ _ (fw_thread_tstack img 0)
            (fw_imap_from (λ i _, fw_thread_tstack img i) 1 fts));
    [exact Hinit | exact Hnull | exact (Hsreg mtdc) | by exists Global | | exact Hstep].
  iIntros (ceriseb Hmtcc Hhome0)
    "HPC Hreg Hmtdc HMIE Hho Hlent Hmem Hshadow Hclaims Hna Hothers".
  iEval (cbn [pcc reg sreg mem shadowtbl]) in "HPC Hreg Hmem Hshadow".
  iEval (rewrite big_sepL_fw_imap_from) in "Hothers".
  iEval (setoid_rewrite bi.sep_assoc) in "Hothers".
  iDestruct (big_sepL_sep with "Hothers") as "[Hmtdcs _]".
  (* The initial MIE is the posture of the entry of the user thread [0]. *)
  assert (mie_st (MkExecConf w_pc regs sregs m sh td) = fw_entry_posture fw img 0) as Hmie.
  { rewrite /mie_st /= Hsreg /= mie_of_mstatus_enc //. }
  (* The seal store, the call stacks and the worlds. *)
  iMod (initialise_world (ceriseg := ceriseG_of (UserThread 0))
          (finite.enum CmptName)
          ({[ot_switcher (img_sw img)]} ∪ list_to_set (fw_otypes fw)) (fw_entry_frame fw img 0)
          (fw_imap_from (λ i _, fw_entry_frame fw img i) 1 fts))
    as (sealsg relg stsg cstackg) "(Hseal_store & Hcstk_full & Hcstk_frag & Hcstks & Hworlds)";
    [done | apply finite.NoDup_enum |].
  iEval (rewrite big_sepL_fw_imap_from) in "Hcstks".
  iDestruct (big_sepL_sep with "Hcstks") as "[Hcstks _]".
  rewrite big_sepS_union; last (apply disjoint_singleton_l; by rewrite elem_of_list_to_set).
  rewrite big_sepS_singleton big_sepS_list_to_set //.
  iDestruct "Hseal_store" as "[Hseal_switcher Hotypes]".
  (* The memory and the registers, by part. *)
  iDestruct (firmware_ok_mem_split (ceriseg := ceriseG_of (UserThread 0))
              fw img (MkExecConf w_pc regs sregs m sh td) Hok with "Hmem")
    as "(Hheap & Hsw_code & Hasrt & Hcmpts & Hthreads_mem)".
  iEval (rewrite Hthreads big_sepL_cons) in "Hthreads_mem".
  iDestruct "Hthreads_mem" as "[Hthread0 Hthreads_mem]".
  iDestruct (firmware_ok_regs_split (ceriseg := ceriseG_of (UserThread 0))
              fw img (MkExecConf w_pc regs sregs m sh td) Hok with "[$HPC $Hreg]")
    as "(HPC & Hcgp & Hcsp & Hcra & Hregs)".
  subst sh.
  (* The assert library. *)
  rewrite (assert_mem_layout _ Hasrt).
  iMod (initialise_assert_compartment _ with "Hasrt") as "[#Hflag #Hassert]".
  (* The code of the switcher. *)
  iEval (rewrite (switcher_mem_layout _ _ _ _ Hts Hsw) /cmpt_switcher_code_mregion)
    in "Hsw_code".
  iMod (initialise_switcher_shared (th := UserThread 0) (swlayout := fw_switcher_layout img)
          (swlayoutwf := fw_switcher_layout_wf fw img Hwf H0) Hmtcc
         with "Hsw_code Hseal_switcher") as "[_ #Hswitcher_static]".
  (* The trusted-stack invariant of each thread, and the stack of the user thread
     [0]. *)
  iMod (fw_thread_trusted_stack_inv_alloc fw img 0 (fw_thread0 fw) ⊤ Hwf H0 H0 Hhome0
         with "Hthread0 Hcstk_full Hmtdc") as "(#Hswitcher & Hstack & Hsave)".
  iDestruct (big_sepL_sep_2 with "Hcstks Hmtdcs") as "Hothers".
  iDestruct (big_sepL_sep_2 with "Hthreads_mem Hothers") as "Hothers".
  iMod (fw_threads_trusted_stack_inv_alloc fw img fts ⊤ Hwf H0 Hthreads with "Hothers") as "_".
  (* The link of the user thread [0] at the initial state, and its posture. *)
  iDestruct (crit_link_full_init (th := UserThread 0) (swlayout := fw_switcher_layout img)
               (MkExecConf w_pc regs sregs m initial_heap_shadow td) ltac:(done)
              with "Hho Hsave Hlent") as "[Hlink Hheld]".
  rewrite Hmie.
  (* The obligations of the trusted code. *)
  iPoseProof (Hobl img _ ceriseb sealsg stsg relg cstackg Hok) as "Hobl".
  iMod ("Hobl" with "[-HPC Hcgp Hcsp Hcra Hregs Hstack Hcstk_frag Hna HMIE Hheld Hlink]
                     [HPC Hcgp Hcsp Hcra Hregs Hstack Hcstk_frag Hna HMIE Hheld]") as "Hwp".
  { rewrite /fw_shared_res /CNames big_sepS_list_to_set; last apply finite.NoDup_enum.
    iFrame "Hotypes Hheap Hshadow Hclaims Hcmpts Hworlds". iFrame "#". }
  { iFrame "HPC Hcgp Hcsp Hcra Hregs Hstack Hcstk_frag Hna HMIE Hheld Hswitcher". }
  iModIntro.
  iExists (crit_link_full (swlayout := fw_switcher_layout img) (UserThread 0)).
  iFrame "Hlink Hflag". iExact "Hwp".
Qed.
End adequacy.

(** The ghost state of the template. A case study with ghost state [Σcs]
    proves [∀ Σ, subG Σcs Σ → fw_obligations Σ fw] in a section whose
    context derives its pre-instances from [subG], and concludes with
    [firmware_adequacy_closed] at [Σcs]. *)
Definition firmwarePreΣ {Cname : CmptNameG} : gFunctors :=
  #[invΣ; ceriseGpreΣ; CSTACK_preΣ; na_invΣ; sealStorePreΣ;
    STS_preΣ; relPreΣ;
    savedPredΣ (WorldT * CmptName * LWord)].

Theorem firmware_adequacy_closed (Σcs : gFunctors) {Cname : CmptNameG}
    `{MP : MachineParameters}
    (fw : firmware) (img : fw_image) (σ σ' : ExecConf) (es : list griotte_lang.expr) :
  fw_obligations #[firmwarePreΣ; Σcs] fw →
  firmware_ok fw img σ →
  rtc erased_step ([Exec], σ) (es, σ') →
  mem σ' !! flag_assert (img_asrt img) = Some (WInt 0).
Proof.
  intros Hobl Hok Hstep.
  eapply (firmware_adequacy #[firmwarePreΣ; Σcs]); eauto; typeclasses eauto.
Qed.
