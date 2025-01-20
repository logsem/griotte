From cap_machine Require Export logrel.
From cap_machine.rules Require Export rules_AddSubLt.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.rules Require Import rules_base.
From cap_machine Require Import ftlr_base.
From cap_machine Require Import machine_base.

Section fundamental.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ}
      {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
      {sealsg: sealStoreG Σ}
      {nainv: logrel_na_invs Σ}
      {MP: MachineParameters}
  .

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma add_sub_lt_case (W : WORLD) (regs : leibnizO Reg) (p : Perm)
    (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst : RegName)
    (r1 r2: Z + RegName) (P:D):
    p = RX ∨ p = RWX ∨ (p = RWLX /\ g = Local)
    → (∀ x : RegName, is_Some (regs !! x))
    → isCorrectPC (WCap p g b e a)
    → (b <= a)%a ∧ (a < e)%a
    → (∀ Wv : WORLD * leibnizO Word, Persistent (P Wv.1 Wv.2))
    → (if pwl p then region_state_pwl W a else region_state_nwl W a g)
    → std W !! a = Some ρ
    → ρ ≠ Revoked
    → (∀ g : Mem, ρ ≠ Frozen g)
    → (decodeInstrW w = Add dst r1 r2 \/
       decodeInstrW w = Sub dst r1 r2 \/
       decodeInstrW w = Lt dst r1 r2)
    -> ftlr_IH
    -∗ fixpoint interp1 W (WCap p g b e a)
    -∗ (∀ (r : RegName) v, ⌜r ≠ PC⌝ → ⌜regs !! r = Some v⌝ → fixpoint interp1 W v)
    -∗ rel a (λ Wv, P Wv.1 Wv.2)
    -∗ rcond P interp
    -∗ □ (if decide (writeAllowed_in_r_a (<[PC:=(WCap p g b e a)]> regs) a)
          then wcond P interp
          else emp)
    -∗ (▷ (if decide (ρ = Temporary)
           then future_pub_a_mono a (λ Wv, P Wv.1 Wv.2) w
           else future_priv_mono (λ Wv, P Wv.1 Wv.2) w))
    -∗ ▷ P W w
    -∗ sts_full_world W
    -∗ na_own logrel_nais ⊤
    -∗ open_region a W
    -∗ sts_state_std a ρ
    -∗ a ↦ₐ w
    -∗ PC ↦ᵣ WCap p g b e a
    -∗ ([∗ map] k↦y ∈ delete PC regs, k ↦ᵣ y)
    -∗ WP Instr Executable
        {{ v, WP Seq (cap_lang.of_val v)
                 {{ v0, ⌜v0 = HaltedV⌝
                        → ∃ (regs' : Reg) (W' : WORLD),
                            full_map regs' ∧ registers_pointsto regs'
                            ∗ ⌜related_sts_priv_world W W'⌝
                            ∗ na_own logrel_nais ⊤
                            ∗ sts_full_world W' ∗ region W' }} }}.
  Proof.
    intros Hp Hsome i Hbae Hpers Hpwl Hregion Hnotrevoked Hnotmonostatic Hi.
    iIntros "#IH #Hinv #Hreg #Hinva #Hrcond #Hwcond Hmono Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.

    iApply (wp_AddSubLt with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec; cycle 1.
    - iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iApply wp_value; auto. iIntros; discriminate.
    - incrementPC_inv; simplify_map_eq.
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      assert (dst <> PC) as HdstPC by (intros ->; rewrite lookup_insert in H1; done).
      rewrite lookup_insert_ne in H1; eauto; simplify_map_eq.
      iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono Hw]") as "Hr"; eauto.
      { destruct ρ;auto;[|specialize (Hnotmonostatic g)];contradiction. }
      iApply ("IH" $! _ (<[dst:=_]> (<[PC:=_]> regs)) with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]");
        try iClear "IH"; eauto.
      + intro. cbn. by repeat (rewrite lookup_insert_is_Some'; right).
      + iIntros (ri wi Hri Hregs_ri).
        destruct (decide (ri = dst)); simplify_map_eq.
        { repeat rewrite fixpoint_interp1_eq; auto. }
        { iApply "Hreg"; eauto. }
      + rewrite !fixpoint_interp1_eq /=.
        destruct Hp as [-> | [  -> | [-> ->] ] ]; rewrite /region_conditions //=.
  Qed.

End fundamental.
