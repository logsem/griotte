From cap_machine Require Export logrel.
From cap_machine.rules Require Export rules_BinOp.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.rules Require Import rules_base.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine.proofmode Require Import map_simpl register_tactics.
From cap_machine Require Import machine_base.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation D := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma binop_case (W : WORLD) (C : CmptName) (regs : leibnizO Reg) (p p' : Perm)
    (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst : RegName)
    (r1 r2: Z + RegName) (P:D):
    validPCperm p g
    → (∀ x : RegName, is_Some (regs !! x))
    → isCorrectPC (WCap p g b e a)
    → (b <= a)%a ∧ (a < e)%a
    → PermFlowsTo p p'
    → isO p' = false
    → persistent_cond P
    → (if isWL p then region_state_pwl W a else region_state_nwl W a g)
    → std W !! a = Some ρ
    → ρ ≠ Revoked
    → (∀ g : Mem, ρ ≠ Frozen g)
    → (decodeInstrW w = Add dst r1 r2 \/
       decodeInstrW w = Sub dst r1 r2 \/
       decodeInstrW w = Mul dst r1 r2 \/
       decodeInstrW w = LAnd dst r1 r2 \/
       decodeInstrW w = LOr dst r1 r2 \/
       decodeInstrW w = LShiftL dst r1 r2 \/
       decodeInstrW w = LShiftR dst r1 r2 \/
       decodeInstrW w = Lt dst r1 r2
      )
    -> ftlr_IH
    -∗ fixpoint interp1 W C (WCap p g b e a)
    -∗ (∀ (r : RegName) v, ⌜r ≠ PC⌝ → ⌜regs !! r = Some v⌝ → fixpoint interp1 W C v)
    -∗ rel C a p' (safeC P)
    -∗ □ (if decide (readAllowed_a_in_regs (<[PC:=WCap p g b e a]> regs) a)
          then ▷ (rcond P C p' interp)
          else emp)
    -∗ □ (if decide (writeAllowed_a_in_regs (<[PC:=(WCap p g b e a)]> regs) a)
          then ▷ wcond P C interp
          else emp)
    -∗ monoReq W C a p' P
    -∗ (▷ (if decide (ρ = Temporary /\ isWL p' = true)
           then future_pub_mono C (safeC P) w
           else future_priv_mono C (safeC P) w))
    -∗ ▷ P W C w
    -∗ sts_full_world W C
    -∗ na_own logrel_nais ⊤
    -∗ open_region W C a
    -∗ sts_state_std C a ρ
    -∗ a ↦ₐ w
    -∗ PC ↦ᵣ (WCap p g b e a)
    -∗ ([∗ map] k↦y ∈ delete PC regs, k ↦ᵣ y)
    -∗ WP Instr Executable
        {{ v, WP Seq (cap_lang.of_val v)
                 {{ v0, ⌜v0 = HaltedV⌝
                        → na_own logrel_nais ⊤}} }}.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp HO Hpers Hpwl Hregion Hnotrevoked Hnotfrozen Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono #HmonoV Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    iInsert "Hmap" PC.

    iApply (wp_BinOp with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec; cycle 1.
    - iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iApply wp_value; auto.
    - incrementPC_inv; simplify_map_eq.
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      assert (dst <> PC) as HdstPC by (intros ->; rewrite lookup_insert in H1; done).
      rewrite lookup_insert_ne in H1; eauto; simplify_map_eq.
      iDestruct (region_close with "[$Hstate $Hr $Ha $HmonoV Hw]") as "Hr"; eauto.
      { destruct ρ;auto;[|specialize (Hnotfrozen g)];contradiction. }
      iApply ("IH" $! _ _ (<[dst:=_]> (<[PC:=_]> regs)) with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]")
      ; eauto.
      + intro; cbn. by repeat (rewrite lookup_insert_is_Some'; right).
      + iIntros (ri wi Hri Hregs_ri).
        destruct (decide (ri = dst)); simplify_map_eq.
        { repeat rewrite fixpoint_interp1_eq; auto. }
        { iApply "Hreg"; eauto. }
      + iApply (interp_next_PC with "Hinv_interp"); eauto.
  Qed.

End fundamental.
