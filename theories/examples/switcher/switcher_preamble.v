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

  Program Definition execute_entry_point_register (wpcc wcgp wstk : Word) :
    (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ) :=
    λne (W : WORLD) (C : CmptName) (reg : leibnizO Reg),
      (full_map reg ∧
       ⌜ reg !! PC = Some wpcc ⌝ ∧
       ⌜ reg !! cgp = Some wcgp ⌝ ∧
       ⌜ reg !! cra = Some (WSentry XSRW_ Local b_switcher e_switcher a_switcher_return) ⌝ ∧
       ⌜ reg !! csp = Some wstk ⌝ ∗ interp W C wstk ∗
       (∀ (r : RegName) (v : Word), (⌜r ∉ ({[PC; cra; cgp; csp]} : gset RegName)⌝ → ⌜reg !! r = Some v⌝ → interp W C v))
      (* NOTE I think the zeroes are not necessary and we never rely in it *)
       (* ∧ *)
      (* (∀ (r : RegName), *)
      (*    (⌜r ∉ (dom_arg_rmap nargs ∪ {[PC; cra; cgp; csp]})⌝ →  ⌜reg !! r = Some (WInt 0)⌝)) *)
      )%I.
  Solve All Obligations with solve_proper.

  (* TODO move in machine_base *)
  Definition get_b (w : Word) :=
    match w with
    | WCap _ _ b _ _ => Some b
    | _ => None
    end.

  Definition csp_sync cstk a_stk e_stk :=
    match cstk with
    | frm::_ =>
        get_a frm.(wstk) = Some a_stk
        ∧ get_e frm.(wstk) = Some e_stk
    | _ => True
    end
  .

  Program Definition execute_entry_point
    (wpcc wcgp : Word) (regs : Reg) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    : (WORLD -n> (leibnizO CmptName) -n> iPropO Σ) :=
    (λne (W : WORLD) (C : CmptName),
      ∀ a_stk e_stk,
       let a_stk4 := (a_stk ^+4)%a in
       ( interp_continuation cstk Ws Cs
         ∗ ⌜frame_match Ws Cs cstk W C⌝
         ∗ (execute_entry_point_register wpcc wcgp (WCap RWL Local a_stk4 e_stk a_stk4) W C regs)
         ∗ registers_pointsto regs
         ∗ region W C
         ∗ sts_full_world W C
         ∗ ⌜csp_sync cstk a_stk e_stk⌝
         ∗ cstack_frag cstk
         ∗ na_own logrel_nais ⊤
           -∗ interp_conf W C)
    )%I.
  Solve All Obligations with solve_proper.

  Definition seal_capability ( w : Word ) (ot : OType) :=
    match w with
    | WCap p g b e a => WSealed ot (SCap p g b e a)
    | _ => w
    end.

  (* TODO unclear if it's still the right definition *)
  Program Definition ot_switcher_prop :
    (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ):=
    λne (W : WORLD) (C : CmptName) (w : Word),
       (∃ (g_tbl : Locality) (b_tbl e_tbl a_tbl : Addr)
          (bpcc epcc : Addr)
          (bcgp ecgp : Addr)
          (nargs : nat) (off : Z),
           ⌜ w = WCap RO g_tbl b_tbl e_tbl a_tbl ⌝
           ∗ ⌜ (b_tbl <= a_tbl < e_tbl)%a ⌝
           ∗ ⌜ (b_tbl < (b_tbl ^+1))%a ⌝
           ∗ ⌜ ((b_tbl ^+1) < a_tbl)%a ⌝
           ∗ ⌜ (0 <= nargs <= 7 )%nat ⌝
           ∗ inv (export_table_PCCN C) ( b_tbl ↦ₐ WCap RX Global bpcc epcc bpcc)
           ∗ inv (export_table_CGPN C) ( (b_tbl ^+ 1)%a ↦ₐ WCap RW Global bcgp ecgp bcgp)
           ∗ inv (export_table_entryN C a_tbl) ( a_tbl ↦ₐ WInt (encode_entry_point (Z.of_nat nargs) off))
           ∗ (seal_capability w ot_switcher) ↦□ₑ nargs
           ∗ □ ( ∀ regs cstk Ws Cs W', ⌜related_sts_priv_world W W'⌝ →
                   ▷ (execute_entry_point
                            (WCap RX Global bpcc epcc (bpcc ^+ off)%a)
                            (WCap RW Global bcgp ecgp bcgp)
                            regs cstk Ws Cs W' C))
      )%I.
  Solve All Obligations with solve_proper.

  Definition ot_switcher_propC : (WORLD * CmptName * Word) -> iPropI Σ :=
    safeC ot_switcher_prop.

  Lemma persistent_cond_ot_switcher :
    persistent_cond ot_switcher_prop.
  Proof. intros [ [] ] ; cbn; apply _. Qed.

  Definition cframe_interp (frm : cframe) (a_tstk : Addr) : iProp Σ :=
    ∃ (wtstk4 : Word),
      a_tstk ↦ₐ wtstk4 ∗
      match frm.(wstk) with
      | WCap RWL Local b_stk e_stk a_stk =>
          (⌜ (b_stk <= a_stk)%a ∧ (a_stk ^+ 3 < e_stk)%a ∧ is_Some (a_stk + 4)%a ⌝
           ∗ ⌜ wtstk4 = WCap RWL Local b_stk e_stk (a_stk ^+ 4)%a ⌝
           ∗ if frm.(is_untrusted_caller)
             then True
             else
               a_stk ↦ₐ frm.(wcs0)
               ∗ (a_stk ^+ 1)%a ↦ₐ frm.(wcs1)
               ∗ (a_stk ^+ 2)%a ↦ₐ frm.(wret)
               ∗ (a_stk ^+ 3)%a ↦ₐ frm.(wcgp))%I
      (* Constraints WFness of the register save area *)
      | _ => False
      end.

  Fixpoint cstack_interp (cstk : cstack) (a_tstk : Addr) : iProp Σ :=
    (match cstk with
    | [] => a_tstk ↦ₐ WInt 0
    | frm::cstk' => cstack_interp cstk' (a_tstk ^+ -1)%a
                  ∗ cframe_interp frm a_tstk
    end)%I.

  Definition switcher_inv : iProp Σ :=
    ∃ (a_tstk : Addr) (cstk : CSTK) (tstk_next : list Word),
     mtdc ↦ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk
     ∗ ⌜ (ot_switcher < (ot_switcher ^+1) )%ot ⌝
     ∗ codefrag a_switcher_call switcher_instrs
     ∗ b_switcher ↦ₐ WSealRange (true,true) Global ot_switcher (ot_switcher^+1)%ot ot_switcher
     ∗ [[ (a_tstk ^+1)%a, e_trusted_stack ]] ↦ₐ [[ tstk_next ]]
     ∗ ⌜ (b_trusted_stack <= a_tstk)%a ∧ (a_tstk <= e_trusted_stack)%a ⌝
     ∗ cstack_full cstk
     ∗ ⌜ (b_trusted_stack + length cstk)%a = Some a_tstk ⌝
     ∗ cstack_interp cstk a_tstk (* link the topmost frame of cstk to the state *)
     ∗ seal_pred ot_switcher ot_switcher_propC.

End Switcher_preamble.
