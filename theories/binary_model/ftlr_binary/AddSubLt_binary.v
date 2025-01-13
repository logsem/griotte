From cap_machine.binary_model Require Export logrel_binary.
From cap_machine.rules Require Export rules_base rules_AddSubLt.
From cap_machine.binary_model.rules_binary Require Import rules_binary_base rules_binary_AddSubLt.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import machine_base.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          {nainv: logrel_na_invs Σ} {cfgg : cfgSG Σ}
          `{MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (prodO (leibnizO Word) (leibnizO Word)) -n> iPropO Σ).
  Notation R := (WORLD -n> (prodO (leibnizO Reg) (leibnizO Reg)) -n> iPropO Σ).
  Implicit Types v : (prodO (leibnizO Word) (leibnizO Word)).
  Implicit Types interp : (D).

  Lemma AddSubLt_spec_determ r i dst arg1 arg2 regs regs' retv retv' :
    is_AddSubLt i dst arg1 arg2 ->
    AddSubLt_spec i r dst arg1 arg2 regs retv ->
    AddSubLt_spec i r dst arg1 arg2 regs' retv' ->
    (regs = regs' ∨ retv = FailedV) ∧ retv = retv'.
  Proof.
    intros isASL Hspec1 Hspec2.
    inversion Hspec1; inversion Hspec2; subst; simplify_eq; split; auto.
    - inv H4; congruence.
    - inv H4; congruence.
    - inv H0; congruence.
  Qed.

  Lemma add_sub_lt_case (W : WORLD) (r : prodO (leibnizO Reg) (leibnizO Reg)) (p : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst : RegName) (r1 r2: Z + RegName) (P:D):
    (∀ w : Word, <[PC:=w]> r.1 = <[PC:=w]> r.2)
    → p = RX ∨ p = RWX ∨ (p = RWLX /\ g = Directed)
    → (∀ x : RegName, is_Some (r.1 !! x) ∧ is_Some (r.2 !! x))
    → isCorrectPC (inr (p, g, b, e, a))
    → (b <= a)%a ∧ (a < e)%a
    → (∀ Wv : WORLD * prodO (leibnizO Word) (leibnizO Word), Persistent (P Wv.1 Wv.2))
    → (if machine_base.pwl p then region_state_pwl_mono W a else region_state_nwl W a g)
    → std W !! a = Some ρ
    → ρ ≠ Revoked
    → (∀ g : gmap Addr (Word * Word), ρ ≠ Monostatic g)
    → (∀ w, ρ ≠ Uninitialized w)
    → (decodeInstrW w = Add dst r1 r2 \/
       decodeInstrW w = Sub dst r1 r2 \/
       decodeInstrW w = Lt dst r1 r2)
    → spec_ctx
    -∗ □ ▷ (∀ (a0 : WORLD) (a1 : prodO (leibnizO Reg) (leibnizO Reg)) (a2 : Perm) (a3 : Locality) (a4 a5 a6 : Addr),
              full_map a1 ∧ (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → fixpoint interp1 a0 (a1.1 !r! r1, a1.2 !r! r1))
              -∗ registers_mapsto (<[PC:=inr (a2, a3, a4, a5, a6)]> a1.1)
                 -∗ spec_registers_mapsto (<[PC:=inr (a2, a3, a4, a5, a6)]> a1.2)
                    -∗ region a0
                       -∗ sts_full_world a0
                          -∗ na_own logrel_nais ⊤
                             -∗ ⤇ Seq (Instr Executable)
                                -∗ ⌜a2 = RX ∨ a2 = RWX ∨ a2 = RWLX ∧ a3 = Directed⌝
                                   → □ region_conditions a0 a2 a3 a4 a5 -∗ interp_conf a0)
    -∗ region_conditions W p g b e
    -∗ (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → fixpoint interp1 W (r.1 !r! r1, r.2 !r! r1))
    -∗ rel a (λ Wv, P Wv.1 Wv.2)
    -∗ rcond P interp
    -∗ □ (if decide (writeAllowed_in_r_a (<[PC:=inr (p, g, b, e, a)]> r.1) a) then wcond P interp else emp)
    -∗ (▷ (if decide (ρ = Monotemporary)
           then future_pub_a_mono a (λ Wv, P Wv.1 Wv.2) w w
           else future_priv_mono (λ Wv, P Wv.1 Wv.2) w w))
    -∗ ▷ P W (w,w)
    -∗ sts_full_world W
    -∗ na_own logrel_nais ⊤
    -∗ open_region a W
    -∗ sts_state_std a ρ
    -∗ a ↦ₐ w
    -∗ a ↣ₐ w
    -∗ PC ↦ᵣ inr (p, g, b, e, a)
    -∗ ([∗ map] k↦y ∈ delete PC (<[PC:=inr (p, g, b, e, a)]> r.1), k ↦ᵣ y)
    -∗ PC ↣ᵣ inr (p, g, b, e, a)
    -∗ ([∗ map] k↦y ∈ delete PC (<[PC:=inr (p, g, b, e, a)]> r.1), k ↣ᵣ y)
    -∗ ⤇ Seq (Instr Executable)
    -∗
        WP Instr Executable
        {{ v, WP Seq (of_val v)
        {{ v0, ⌜v0 = HaltedV⌝
               → ∃ (r1 : Reg * Reg) W',
                   ⤇ Instr Halted
                   ∗ full_map r1
                     ∗ registers_mapsto r1.1
                       ∗ spec_registers_mapsto r1.2
                         ∗ ⌜related_sts_priv_world W W'⌝ ∗ na_own logrel_nais ⊤ ∗ sts_full_world W' ∗ region W' }} }}.
  Proof.
    intros Heqregs Hp Hsome i Hbae Hpers Hpwl Hregion Hnotrevoked Hnotmonostatic Hnotuninitialized Hi.
    iIntros "#Hspec #IH #Hinv #Hreg #Hinva #Hrcond #Hwcond Hmono Hw Hsts Hown".
    iIntros "Hr Hstate Ha Ha' HPC Hmap HsPC Hsmap Hj".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iDestruct ((big_sepM_delete _ _ PC) with "[HsPC Hsmap]") as "Hsmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_AddSubLt with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; eauto. destruct Hsome with rr;auto. }
    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".

    iMod (step_AddSubLt _ [SeqCtx] with "[$Ha' $Hsmap $Hj $Hspec]") as (retv' regs'') "(Hs' & Hs & Ha' & Hsmap) /=";eauto.
    { rewrite lookup_insert. eauto. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; eauto. destruct Hsome with rr;auto. }
    iDestruct "Hs'" as %HSpec'.

    specialize (AddSubLt_spec_determ _ _ _ _ _ _ _ _ _ Hi HSpec HSpec') as [Heq ->].

    destruct HSpec; cycle 1.
    { iApply wp_pure_step_later; auto. iNext.
      iApply wp_value; auto. iIntros; discriminate. }
    { incrementPC_inv; simplify_map_eq.
      destruct Heq as [<- | Hcontr];[|inversion Hcontr].
      iApply wp_pure_step_later; auto. iNext.
      iMod (do_step_pure _ [] with "[$Hspec $Hs]") as "Hs /=";auto.
      assert (dst <> PC) as HdstPC by (intros ->; simplify_map_eq).
      simplify_map_eq.
      iDestruct (region_close with "[$Hstate $Hr $Ha $Ha' $Hmono Hw]") as "Hr"; eauto.
      { destruct ρ;auto;[|specialize (Hnotmonostatic g)|specialize (Hnotuninitialized p)];contradiction. }
      iApply ("IH" $! _ (<[dst:=_]> (<[PC:=_]> r.1),<[dst:=_]> (<[PC:=_]> r.1)) with "[] [Hmap] [Hsmap] [$Hr] [$Hsts] [$Hown] [$Hs]");
        try iClear "IH"; eauto.
      iSplit;eauto.
      { iPureIntro. intros. cbn. split; repeat (rewrite lookup_insert_is_Some'; right);destruct Hsome with x5;auto. }

      iIntros (ri Hri). rewrite /(RegLocate _ ri) insert_commute // lookup_insert_ne //; [].
      destruct (decide (ri = dst)); simplify_map_eq.
      { repeat rewrite fixpoint_interp1_eq; auto. }
      { iDestruct ("Hreg" $! _ Hri) as "Hregr1".
        rewrite /RegLocate.
        rewrite -(lookup_insert_ne r.2 PC _ (inl 0%Z))// -Heqregs lookup_insert_ne//.  } }

  Qed.

End fundamental.
