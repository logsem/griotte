From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import adequacy.
From iris.base_logic Require Import invariants.
From griotte Require Import logrel monotone interp_weakening.
From griotte Require Import assert_spec.
From griotte Require Import
  world_interp_revocation world_interp_allocation world_interp_allocation_compartments.
From griotte Require Import switcher_base_interp.
From griotte Require Import stack_world_resources.
From griotte Require Import compartment_layout switcher_adequacy adequacy_helpers.
From griotte Require Import allocator_resources heap_region.
From griotte Require Export adequacy_common_obligations.

(** ** Iris adequacy for the assert flag

    The premise receives the program-logic resources of the initial state
    (registers, mtdc, memory, shadow table, address claims, the
    non-atomic invariant token) and must produce a WP for the machine together with
    the invariant of the assert flag. The machine runs as the user thread [0]:
    its PC, registers and pool are those of [UserThread 0] in the base; the
    shared heaps are stated at the base. The user thread [S k] receives the
    mtdc value [ms !! k] and the token of its pool; its PC and registers are
    placeholders, unused until the threads are scheduled. *)
Section flag_adequacy.
  (* Threads [0] and [S k] meet here: every form names its thread. *)
  #[local] Remove Hints ceriseG_of : typeclass_instances.

Lemma cerise_flag_adequacy (Σ : gFunctors)
  {inv_preg : invGpreS Σ}
  {cerise_preg : ceriseGpreS Σ}
  {na_invg : na_invariants.na_invG Σ}
  `{MP: MachineParameters} {TV : trapVector}
  (flagN : namespace) (flag : Addr) (H : gset Addr)
  (σ σ' : ExecConf)
  (wmtdc : Word) (m0 : mtdc_val) (ms : list mtdc_val) (es : list griotte_lang.expr) :
  ghost_init_cond σ H →
  reg σ !! cnull = Some (WInt 0) →
  sreg σ !! mtdc = Some wmtdc →
  mtdc_match m0 (lword_of_word wmtdc) →
  (∀ (ceriseb : ceriseBaseG Σ),
     (* the trap vector of [ceriseb] is the one of the initial state *)
     @mtcc_vec (@cb_trapVector Σ ceriseb) = @mtcc_vec TV →
     (* the home value of thread [0]'s mtdc token is its initial mtdc *)
     @mtdc_home Σ (@cb_mtdc_lent_of Σ ceriseb (UserThread 0)) = m0 →
     PC ↦ₚ[u 0] lword_of_word (pcc σ) -∗
     regs[u 0] (lword_of_word <$> reg σ) -∗
     mtdc ↦ₜ[u 0] m0 -∗
     (* thread [0]'s posture: its MIE fragment at the initial MIE, what a
        critical section hands over, and its mtdc token *)
     MIE ↦ₜ[u 0] mie_st σ -∗
     handover_res (ceriseg := ceriseG_of (UserThread 0)) -∗
     @mtdc_lent Σ (@cb_mtdc_lent_of Σ ceriseb (UserThread 0)) -∗
     ([∗ map] a↦w ∈ mem σ, a ↦ₐ lword_of_word w) -∗
     ([∗ map] a↦s ∈ shadowtbl σ, a ↦ₛ s) -∗
     ([∗ map] a↦c ∈ init_claims H, addr_alloc a c) -∗
     (* the pool of thread [0] in [ceriseb], not the [na_invg] parameter *)
     @na_own Σ (@cb_na_invG Σ ceriseb) (tpool (UserThread 0)) ⊤ -∗
     (* the user threads [S k]: the home values of their mtdc tokens, their
        mtdc and the tokens of their pools *)
     ([∗ list] k ↦ m ∈ ms,
        ⌜@mtdc_home Σ (@cb_mtdc_lent_of Σ ceriseb (UserThread (S k))) = m⌝ ∗
        mtdc ↦ₜ[u (S k)] m ∗
        @na_own Σ (@cb_na_invG Σ ceriseb) (tpool (UserThread (S k))) ⊤)
     ={⊤}=∗
     (* the link of thread [0], holding its part of the initial state *)
     ∃ CL : CritLink Σ (UserThread 0),
       crit_link (th := UserThread 0) σ ∗
       WP Exec @[u 0] {{ _, True }} ∗
       inv flagN (flag ↦ₐ WInt 0)) →
  rtc erased_step ([Exec], σ) (es, σ') →
  mem σ' !! flag = Some (WInt 0).
Proof.
  intros Hinit Hnull Hmtdc Hm0 Hwp Hstep.
  pose proof (@wp_invariance Σ griotte_lang _ NotStuck) as WPI. cbn in WPI.
  pose (fun (c: ExecConf) => mem c !! flag = Some (WInt 0%Z)) as state_is_good.
  specialize (WPI Exec σ es σ' (state_is_good σ')).
  eapply WPI. 2: assumption. intros Hinv κs. clear WPI.
  iMod (@na_alloc Σ na_invg) as (pool) "Hna".
  (* The pools of the user threads [S k], of the context-switch thread and
     of the other threads. *)
  iMod (na_pools_alloc ms) as (pools) "Hnas".
  iMod (@na_alloc Σ na_invg) as (pool_c) "_".
  iMod (@na_alloc Σ na_invg) as (pool_d) "_".
  pose cerise_na_invs := Build_cerise_na_invs _ na_invg pool.
  (* The ghost state of the user threads [S k], of the context-switch thread
     and of the other threads; before thread [0]'s, which typeclass search
     must find. Their mtdc tokens are dropped until the threads are
     scheduled. *)
  iMod (threads_ghost_init ms) as (gs Hhomes) "Hgs".
  iMod (thread_ghost_init (ExceptionScratch (lword_of_word (WInt 0))))
    as (pg_c rg_c mtg_c mieg_c mlg_c Hhome_c) "_".
  iMod (thread_ghost_init (ExceptionScratch (lword_of_word (WInt 0))))
    as (pg_d rg_d mtg_d mieg_d mlg_d Hhome_d) "_".
  (* The names of the postures, and the mtdc token of thread [0]. *)
  iMod (@posture_init Σ (@cerise_preG_excl Σ cerise_preg) (@cerise_preG_oneshot Σ cerise_preg)
          na_invg) as (postureg) "(Hcrit & Hunw & Hpending)".
  iMod (@mtdc_lent_init Σ (@cerise_preG_excl Σ cerise_preg) m0) as (mlg Hhome) "Hlent".
  iMod (cerise_ghost_init σ H m0 wmtdc Hinit Hmtdc Hm0 Hhome with "Hpending")
    as (mem_heapg shadow_heapg pc_g reg_heapg sreg_heapg registryg addr_allocg mtdcg mieg mpieg)
       "(Hσ & HPC & Hreg & Hmtdc & Hmem & Hshadow & Hclaims & Hmst & Hmepcc & Hmcause & Hmtval)".
  iDestruct "Hmst" as (mie0 mpie0 Hmst) "[HMIE HMPIE]".
  iDestruct "Hmepcc" as (vepcc) "Hmepcc".
  iDestruct "Hmcause" as (vcause) "Hmcause".
  iDestruct "Hmtval" as (ztval) "Hmtval".
  assert (mie_st σ = mie0) as Hmie0.
  { rewrite /mie_st /= in Hmst |- *. by rewrite Hmst /= mie_of_mstatus_enc. }
  iEval (rewrite init_lmem_pointsto) in "Hmem".
  rewrite (init_lregs_cnull (reg σ) Hnull).
  iDestruct (big_sepL2_nth_l _ _ _ (pg_d, rg_d, mtg_d, mieg_d, mlg_d) with "Hgs") as "Hgs".
  iDestruct (big_sepL_sep with "Hgs") as "[Hgs _]".
  iDestruct (big_sepL2_nth_l _ _ _ pool_d with "Hnas") as "Hnas".
  (* Thread [0] has the PC, the registers, mtdc, MIE and the pool of the
     machine; every other thread its own. *)
  pose ceriseb := {|
    cb_invG := Hinv;
    cb_na_invG := na_invg;
    cb_mem := mem_heapg;
    cb_shadow := shadow_heapg;
    cb_sreg := sreg_heapg;
    cb_registry := registryg;
    cb_addr_alloc := addr_allocg;
    cb_trapVector := TV;
    cb_mpie := mpieg;
    cb_posture := postureg;
    cb_pc_of := λ th, (thread_map (pc_g, reg_heapg, mtdcg, mieg, mlg) gs (pg_c, rg_c, mtg_c,
      mieg_c, mlg_c)
                                (pg_d, rg_d, mtg_d, mieg_d, mlg_d) th).1.1.1.1;
    cb_regs_of := λ th, (thread_map (pc_g, reg_heapg, mtdcg, mieg, mlg) gs (pg_c, rg_c, mtg_c,
      mieg_c, mlg_c)
                                (pg_d, rg_d, mtg_d, mieg_d, mlg_d) th).1.1.1.2;
    cb_mtdc_of := λ th, (thread_map (pc_g, reg_heapg, mtdcg, mieg, mlg) gs (pg_c, rg_c, mtg_c,
      mieg_c, mlg_c)
                                (pg_d, rg_d, mtg_d, mieg_d, mlg_d) th).1.1.2;
    cb_mie_of := λ th, (thread_map (pc_g, reg_heapg, mtdcg, mieg, mlg) gs (pg_c, rg_c, mtg_c,
      mieg_c, mlg_c)
                                (pg_d, rg_d, mtg_d, mieg_d, mlg_d) th).1.2;
    cb_mtdc_lent_of := λ th, (thread_map (pc_g, reg_heapg, mtdcg, mieg, mlg) gs (pg_c, rg_c,
      mtg_c, mieg_c, mlg_c)
                                (pg_d, rg_d, mtg_d, mieg_d, mlg_d) th).2;
    tpool := thread_map pool pools pool_c pool_d |}.
  pose ceriseg := ceriseG_of (base := ceriseb) (UserThread 0).
  iMod (Hwp ceriseb eq_refl Hhome with "HPC Hreg Hmtdc [HMIE] [Hcrit Hunw Hmepcc Hmcause Hmtval
    HMPIE]
          Hlent Hmem Hshadow Hclaims Hna [Hgs Hnas]")
    as (CL) "(Hlink & Hwp & #Hflag)".
  { rewrite Hmie0. iExact "HMIE". }
  { iApply (handover_res_intro vepcc vcause ztval mpie0). iFrame. }
  { iDestruct (big_sepL_sep_2 with "Hgs Hnas") as "Hgs".
    iApply (big_sepL_impl with "Hgs"). iIntros "!>" (k m1 Hk) "[$ $]".
    iPureIntro.
    destruct (Forall2_lookup_r _ _ _ _ _ Hhomes Hk) as (g & Hg & Hgm).
    cbn. by rewrite (nth_lookup_Some _ _ _ _ Hg). }
  iModIntro.
  iExists (fun σ _ _ => cerise_state_interp σ ∗ @crit_link Σ (UserThread 0) CL σ)%I.
  iExists (fun _ => True)%I. cbn. iFrame "Hσ Hlink".
  iSplitL "Hwp".
  { iApply (wp_mono with "Hwp"); iIntros (?) "?"; done. }
  iIntros "[Hσ _]".
  iDestruct (SI_open with "Hσ") as "Hσ". iNamed "Hσ".
  iExists (⊤ ∖ ↑flagN).
  iInv flagN as ">Hflag'" "Hclose".
  iDestruct (gen_heap_valid with "Hm Hflag'") as %Hm'_flag.
  iModIntro. iPureIntro.
  destruct (erasure_lookup_mem _ _ _ _ _ _ _ _ _ Her Hm'_flag)
    as (pw & Hpw & _ & _ & Hnonheap & _).
  destruct (Hnonheap eq_refl) as [Heq | (_ & Hb)]; last by destruct Hb.
  rewrite /state_is_good Hpw Heq //.
Qed.
End flag_adequacy.

(** ** Initial world, seal store and call stack *)
Section world_init.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {Cname : CmptNameG}
    {seal_store_preg : sealStorePreG Σ}
    {sts_preg : STS_preG Σ} {relpreg : relGpreS Σ}
    {cstack_preg : CSTACK_preG Σ}
    `{MP: MachineParameters}.

  (** The call stack of the user thread [0] starts with its entry frame
      [ef] only, that of the user thread [S k] with the entry frame
      [efs !! k] only. The worlds are those of the user thread [0]; the
      local maps of the other threads are empty. *)
  Lemma initialise_world (Cs : list CmptName) (ots : gset OType) (ef : trusted_frame)
      (efs : list trusted_frame) :
    CNames = list_to_set Cs →
    NoDup Cs →
    ⊢ |==> ∃ (seal_storeg : sealStoreG Σ) (relg : relGS Σ)
            (stsg : STSG Σ) (cstackg : CSTACKG Σ),
      ([∗ set] o ∈ ots, can_alloc_pred o) ∗
      ●(CSTK)[u 0] (entry_cstack ef) ∗
      ◯(CSTK)[u 0] (entry_cstack ef) ∗
      ([∗ list] k ↦ ef' ∈ efs,
         ●(CSTK)[u (S k)] (entry_cstack ef') ∗ ◯(CSTK)[u (S k)] (entry_cstack ef')) ∗
      [∗ list] C ∈ Cs, world_interp (th := UserThread 0) (MkWorld ∅ (∅,∅)) C.
  Proof.
    intros HCNames HNoDup.
    iMod (gen_cstack_init (entry_cstack ef) ((λ ef', entry_cstack ef') <$> efs))
      as (cstackg) "(Hcstk_full & Hcstk_frag & Hcstks)".
    iEval (rewrite big_sepL_fmap) in "Hcstks".
    iMod (world_interp_init ots (S (length efs))) as (relg stsg seal_storeg)
      "(Hworld_interp & _ & Hseal_store)"; first lia.
    rewrite HCNames big_sepS_list_to_set //.
    iModIntro; iExists seal_storeg, relg, stsg, cstackg; iFrame.
  Qed.

End world_init.
