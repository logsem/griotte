From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel addr_reg_sample rules proofmode.
From cap_machine Require Import multiple_updates region_invariants_revocation.
(* region_invariants_allocation. *)
From cap_machine Require Export switcher.

Section Switcher_preamble.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {cstackg : CSTACKG Σ}
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

  (** Property of capability sealed by the switcher's otype *)
  Definition export_tableN (C : CmptName) : namespace := nroot .@ "export_tableN" .@ C.
  Definition export_table_PCCN (C : CmptName) : namespace := (export_tableN C) .@ "PCC".
  Definition export_table_CGPN (C : CmptName) : namespace := (export_tableN C) .@ "CGP".
  Definition export_table_entryN (C : CmptName) (a : Addr) : namespace :=
    (export_tableN C) .@ "entry" .@ a.

  Program Definition execute_entry_point_register (wpcc wcgp : Word) :
    (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ) :=
    λne (W : WORLD) (C : CmptName) (reg : leibnizO Reg),
      (full_map reg ∧
       ⌜ reg !! PC = Some wpcc ⌝ ∧
       ⌜ reg !! cgp = Some wcgp ⌝ ∧
       (∀ (wstk : Word), (⌜reg !! csp = Some wstk⌝ → interp W C wstk)) ∧
       (∀ (wret : Word), (⌜reg !! cra = Some wret⌝ → interp W C wret)) ∧
       (∀ (r : RegName) (v : Word), (⌜r ∈ dom_arg_rmap⌝ → ⌜reg !! r = Some v⌝ → interp W C v)) ∧
       (∀ (r : RegName),
          (⌜r ∉ (dom_arg_rmap ∪ {[PC; cra; cgp; csp]})⌝ →  ⌜reg !! r = Some (WInt 0)⌝)))%I.
  Solve All Obligations with solve_proper.

  Program Definition execute_entry_point (wpcc wcgp : Word) (regs : Reg) (cstk : CSTK) : (WORLD -n> (leibnizO CmptName) -n> iPropO Σ) :=
    (λne (W : WORLD) (C : CmptName),
       ( (execute_entry_point_register wpcc wcgp W C regs)
         ∗ registers_pointsto regs
         ∗ region W C
         ∗ sts_full_world W C
         ∗ cstack_frag cstk
         ∗ na_own logrel_nais ⊤
           -∗ interp_conf W C)
    )%I.
  Solve All Obligations with solve_proper.

  (* TODO unclear if it's still the right definition *)
  Program Definition ot_switcher_prop :
    (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ):=
    λne (W : WORLD) (C : CmptName) (w : Word),
       (∃ (g_tbl : Locality) (b_tbl e_tbl a_tbl : Addr)
          (bpcc epcc : Addr)
          (bcgp ecgp : Addr)
          (nargs off : Z),
           ⌜ w = WCap RO g_tbl b_tbl e_tbl a_tbl ⌝
           ∗ ⌜ (b_tbl <= a_tbl < e_tbl)%a ⌝
           ∗ ⌜ (b_tbl < (b_tbl ^+1))%a ⌝
           ∗ ⌜ ((b_tbl ^+1) < a_tbl)%a ⌝
           ∗ ⌜ (0 <= nargs <= 7 )%Z ⌝
           ∗ inv (export_table_PCCN C) ( b_tbl ↦ₐ WCap RX Global bpcc epcc bpcc)
           ∗ inv (export_table_CGPN C) ( (b_tbl ^+ 1)%a ↦ₐ WCap RW Global bcgp ecgp bcgp)
           ∗ inv (export_table_entryN C a_tbl) ( a_tbl ↦ₐ WInt (encode_entry_point nargs off))
           ∗ □ ( ∀ cstk W' regs, ⌜related_sts_priv_world W W'⌝ →
                   ▷ (execute_entry_point
                            (WCap RX Global bpcc epcc (bpcc ^+ off)%a)
                            (WCap RW Global bcgp ecgp bcgp)
                            cstk
                            regs W' C))
      )%I.
  Solve All Obligations with solve_proper.

  Definition ot_switcher_propC : (WORLD * CmptName * Word) -> iPropI Σ :=
    safeC ot_switcher_prop.

  Lemma persistent_cond_ot_switcher :
    persistent_cond ot_switcher_prop.
  Proof. intros [ [] ] ; cbn ; apply _. Qed.

  (* Lemma mono_priv_ot_switcher (C : CmptName) (w : Word) : *)
  (*   ⊢ future_priv_mono C ot_switcher_propC w. *)
  (* Proof. *)
  (*   iIntros (W W' Hrelated_W_W'). *)
  (*   iModIntro. *)
  (*   iIntros "Hot_switcher". *)
  (*   iEval (cbn) in "Hot_switcher". *)
  (*   iEval (cbn). *)
  (*   iDestruct "Hot_switcher" as *)
  (*     (g_tbl b_tbl e_tbl a_tbl bpcc epcc bcgp ecgp nargs off -> *)
  (*      Hatbl Hbtbl Hbtbl1 Hnargs) "(Hinvpcc & Hinvcgp & Hinventry & #Hcont)". *)
  (*   iFrame "Hinvpcc Hinvcgp Hinventry". *)
  (*   iExists _,_. *)
  (*   repeat (iSplit ; first done). *)
  (*   iModIntro. *)
  (*   iIntros (W'' regs Hrelated_W'_W''). *)
  (*   iSpecialize ("Hcont" $! W'' regs). *)
  (*   iApply "Hcont". *)
  (*   iPureIntro. *)
  (*   by eapply related_sts_priv_trans_world. *)
  (* Qed. *)

  (* (** Custom invariant used by the switcher to store the frame  *) *)
  (*  Definition frame_inv (C : CmptName) (i : positive) (P : iProp Σ) := *)
  (*    (∃ x:bool, sts_state_loc C i x ∗ if x then P else emp)%I. *)
  (*  Definition frame_rel_pub := λ (a b : bool), False. *)
  (*  Definition frame_rel_priv := λ (a b : bool), True. *)
  (*  Definition frame_W (W : WORLD) : WORLD := *)
  (*    let ι := fresh_cus_name W in *)
  (*     <l[ ι := true , ( frame_rel_pub, (frame_rel_pub, frame_rel_priv)) ]l> W. *)

  (*  Lemma frame_W_related_sts_pub_world (W : WORLD) : related_sts_pub_world W (frame_W W). *)
  (*  Proof. *)
  (*    rewrite /frame_W. *)
  (*    destruct W as [ [Wstd [fs fr] ] Wfrm ] . *)
  (*    assert (fresh (dom fs ∪ dom fr) ∉ (dom fs ∪ dom fr)) as Hfresh by apply is_fresh. *)
  (*    apply related_sts_pub_world_fresh_loc; set_solver. *)
  (*  Qed. *)

  (*  Set Nested Proofs Allowed. *)

  (* Lemma frame_W_lookup_std (W : WORLD) (a : Addr) : *)
  (*   std (frame_W W) !! a = (std W) !!a. *)
  (* Proof. *)
  (*   rewrite /frame_W. *)
  (*   by cbn. *)
  (* Qed. *)

  (* Lemma frame_W_lookup_loc (W : WORLD) (ι : positive) : *)
  (*   ι ≠ fresh_cus_name W -> *)
  (*   loc (frame_W W) !! ι = (loc W) !! ι. *)
  (* Proof. *)
  (*   intros Hι. *)
  (*   rewrite /frame_W /= lookup_insert_ne //. *)
  (* Qed. *)
  (* Lemma frame_W_lookup_rel (W : WORLD) (ι : positive) : *)
  (*   ι ≠ fresh_cus_name W -> *)
  (*   wrel (frame_W W) !! ι = (wrel W) !! ι. *)
  (* Proof. *)
  (*   intros Hι. *)
  (*   rewrite /frame_W /= lookup_insert_ne //. *)
  (* Qed. *)
  (* Lemma frame_W_lookup_frm (W : WORLD) : frm (frame_W W) = (frm W). *)
  (* Proof. by cbn. Qed. *)

  (* Lemma ι0_in_Wloc_helper (W0 : WORLD) (ι0 : positive) (callee_stk_frm_addr : list Addr) : *)
  (*   ι0 ∈ (dom (loc (std_update_multiple *)
  (*                      (<l[ι0:=false]l>(revoke W0)) *)
  (*                      callee_stk_frm_addr Temporary))). *)
  (* Proof. *)
  (*   rewrite std_update_multiple_loc_sta dom_insert_L; set_solver. *)
  (* Qed. *)

  (* Lemma ι0_isnot_fresh (W0 : WORLD) (ι0 : positive) (callee_stk_frm_addr : list Addr) : *)
  (*   ι0 ≠ fresh_cus_name (std_update_multiple *)
  (*                          (<l[ι0:=false]l>(revoke W0)) *)
  (*                          callee_stk_frm_addr Temporary). *)
  (* Proof. *)
  (*   apply fresh_name_notin. left. *)
  (*   apply ι0_in_Wloc_helper. *)
  (* Qed. *)


  (* (** Evolution of the world in the switcher *) *)
  (* Definition switcher_world_pre_frame (W_init : WORLD) (callee_stk_frm_addr : list Addr) := *)
  (*   (std_update_multiple (<d[ frm W_init + 1]d>(revoke W_init)) callee_stk_frm_addr Temporary). *)

  (* Definition switcher_world_upon_jmp (W_init : WORLD) *)
  (*   (a_local_args callee_stk_frm_addr : list Addr) := *)
  (*   std_update_multiple *)
  (*     (frame_W (switcher_world_pre_frame W_init callee_stk_frm_addr)) *)
  (*     a_local_args Temporary. *)

  (* Lemma related_sts_priv_world_switcher_pre_frame *)
  (*   (W : WORLD) (callee_stk_frm_addr : list Addr) : *)
  (*   Forall (fun a => std W !! a = Some Revoked) callee_stk_frm_addr -> *)
  (*   related_sts_priv_world W (switcher_world_pre_frame W callee_stk_frm_addr). *)
  (* Proof. *)
  (*   intros Ha_local_args. *)
  (*   rewrite /switcher_world_pre_frame. *)
  (*   eapply related_sts_priv_trans_world; cycle 1. *)
  (*   { apply related_sts_pub_priv_world. *)
  (*     apply related_sts_pub_update_multiple_temp. *)
  (*     eapply Forall_impl; eauto. *)
  (*     intros a Ha; cbn in *. *)
  (*     by apply revoke_lookup_Revoked. *)
  (*   } *)
  (*   eapply related_sts_priv_trans_world; cycle 1. *)
  (*   { apply sts.related_sts_priv_world_update_frm. } *)
  (*   apply revoke_related_sts_priv_world. *)
  (* Qed. *)


  Definition cframe_interp (frm : cframe) (a_tstk : Addr) : iProp Σ :=
    match frm.(wstk) with
    | WCap RWL Local b_stk e_stk a_stk =>
        (* TODO do we need some constraints like b_stk <= a_stk - 4 < a_stk -1 < e_stk ? *)
        (a_stk ^+ -4)%a ↦ₐ frm.(wcs0)
        ∗ (a_stk ^+ -3)%a ↦ₐ frm.(wcs1)
        ∗ (a_stk ^+ -2)%a ↦ₐ frm.(wret)
        ∗ (a_stk ^+ -1)%a ↦ₐ frm.(wcgp)
    | _ => False
    end.

  Fixpoint cstack_interp (cstk : cstack) (a_tstk : Addr) : iProp Σ :=
    (match cstk with
    | [] => True
    | frm::cstk' => cstack_interp cstk' (a_tstk ^+ -1)%a ∗ cframe_interp frm a_tstk
    end)%I.

  Definition switcher_inv : iProp Σ :=
    ∃ (a_tstk : Addr) (cstk : CSTK) (tstk_next : list Word),
     mtdc ↦ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk
     (* ∗ ⌜ SubBounds *)
     (*     b_switcher e_switcher *)
     (*     a_switcher_call (a_switcher_call ^+ length switcher_instrs)%a ⌝ *)
     ∗ ⌜ (ot_switcher < (ot_switcher ^+1) )%ot ⌝
     ∗ codefrag a_switcher_call switcher_instrs
     ∗ b_switcher ↦ₐ WSealRange (true,true) Global ot_switcher (ot_switcher^+1)%ot ot_switcher
     ∗ [[ (a_tstk ^+1)%a, e_trusted_stack ]] ↦ₐ [[ tstk_next ]]
     ∗ ⌜ (b_trusted_stack <= a_tstk)%a ∧ (a_tstk <= e_trusted_stack)%a ⌝
     ∗ cstack_full cstk
     ∗ ⌜ (b_trusted_stack + length cstk)%a = Some a_tstk  ⌝
     ∗ cstack_interp cstk a_tstk (* link the topmost frame of cstk to the state *)
     ∗ seal_pred ot_switcher ot_switcher_propC.


End Switcher_preamble.
