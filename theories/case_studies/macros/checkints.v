From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules proofmode.
From cap_machine Require Import is_word_type lea_to_base.

Section Checkints.
  Context
      {MP: MachineParameters}
  .


  Definition checkints_loop_instrs (r r1 r2 : RegName) : list Word :=
    encodeInstrsW [Load r1 r]
      ++ is_int_instrs r1 r2
      ++ encodeInstrsW
      [ (* is an integer *)
        Lea r 1;
        GetA r1 r;
        GetE r2 r;
        Lt r1 r1 r2;
        (* if r1 -> 0 then a + 1 >= e, and we continue,
        otherwise we jump back to the beginning of the loop *)
        Jnz (- ((length (is_int_instrs r1 r2))+5))%Z r1
      ].

  Definition checkints_instrs (r r1 r2 : RegName) : list Word :=
      lea_to_base_instrs r r1 r2
      ++ encodeInstrsW [
        GetB r1 r;
        GetE r2 r;
        Lt r1 r1 r2;
        Sub r1 r1 1; (* invert result for the jump *)
        Jnz (length (checkints_loop_instrs r r1 r2) + 1) r1]
      ++ checkints_loop_instrs r r1 r2
      ++ encodeInstrsW [
        Mov r1 0;
        Mov r2 0].

  Definition checkints_loop_offset : Z :=
    Eval vm_compute in
      length ( lea_to_base_instrs PC PC PC)
      + length (
            encodeInstrsW [
                GetB PC PC;
                GetE PC PC;
                Lt PC PC PC;
                Sub PC PC 1; (* invert result for the jump *)
                Jnz (length (checkints_loop_instrs PC PC PC) + 1) PC])
  .
End Checkints.

Section Checkints_spec.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ}
      {MP: MachineParameters}
  .

  Lemma checkints_loop_spec
    (r r1 r2 : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (w1 w2 : Word) (l : list Addr) (ws : list Word)
    (p : Perm) (g : Locality) (b e a : Addr)
    (φ : language.val cap_lang → iPropI Σ) :

    let checkints_loop := (checkints_loop_instrs r r1 r2) in
    let a_last := (pc_a ^+ length (checkints_loop_instrs r r1 r2))%a in
    executeAllowed pc_p = true →
    SubBounds pc_b pc_e pc_a a_last →
    l ≡ₚ (finz.seq_between b e) ->
    (b <= a < e)%a ->
    readAllowed p = true ->
    Forall (λ w,
              (∃ k, ws !! k = Some w ∧ (∃ a', l !! k = Some a' ∧ (b <= a' < a)%a ))
              ->
              ∃ z, w = WInt z) ws ->
    r ≠ cnull ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    ▷ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
    ∗ ▷ r ↦ᵣ (WCap p g b e a)
    ∗ ▷ r1 ↦ᵣ w1
    ∗ ▷ r2 ↦ᵣ w2
    ∗ ▷ codefrag pc_a checkints_loop
    ∗ ▷ ( [∗ list] a;v ∈ l;ws, a ↦ₐ v )
    ∗ ▷ ( PC ↦ᵣ WCap pc_p pc_g pc_b pc_e a_last
         ∗ r ↦ᵣ WCap p g b e (finz.max b e)
         ∗ r1 ↦ᵣ WInt 0%Z
         ∗ r2 ↦ᵣ WInt e%Z
         ∗ ( [∗ list] a;v ∈ l;ws, a ↦ₐ v )
         ∗ ⌜ Forall (λ w, ∃ z, w = WInt z) ws ⌝
         ∗ codefrag pc_a checkints_loop
         -∗ WP Seq (Instr Executable) {{ φ }}
        )
    ∗ □ (▷ (φ FailedV))
    ⊢ WP Seq (Instr Executable) {{ v, φ v }}.
  Proof.
    intros checkints a_last ; subst checkints a_last.
    iIntros (Hvpc Hcont Hl Hae Hra Hall Hrcnull Hr1cnull Hr2cnull)
      "(>HPC & >Hr & >Hr1 & >Hr2 & >Hcode & >Hmem & Hφ & #Hfailed)".
    iLöb as "IH" forall ( a Hae Hall w1 w2).
    iDestruct (big_sepL2_length with "Hcode") as %Hlength.
    iDestruct (big_sepL2_length with "Hmem") as %Hlength_mem.
    codefrag_facts "Hcode".
    iEval (cbn) in "HPC".

    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    assert (a ∈ l) as Ha.
    { setoid_rewrite Hl; by rewrite elem_of_finz_seq_between. }
    rewrite elem_of_list_lookup in Ha; destruct Ha as [ka Ha].
    pose proof Ha as Ha'.
    apply take_drop_middle in Ha'; symmetry in Ha'.
    set (la1 := take ka l).
    set (la2 := drop (S ka) l).
    (* rewrite Hla in Hlength_mem. *)
    assert (exists lw1 w lw2, ws = lw1 ++ w :: lw2
                         ∧ length lw1 = length la1
                         ∧ length lw2 = length la2
           ) as (lw1 & w & lw2 & Hlw & Hlw1 & Hlw2).
    {
      (* rewrite elem_of_list_lookup in Ha'; destruct Ha' as [ka Ha]. *)
      assert (is_Some (ws !! ka)) as [wa Hwa].
      { exists (ws !!! ka).
        apply list_lookup_lookup_total_lt.
        rewrite -Hlength_mem.
        eapply lookup_lt_Some; eauto.
      }
      pose proof Hwa as Hwa'.
      apply take_drop_middle in Hwa'.
      exists (take ka ws), wa, ((drop (S ka)) ws).
      split; first done.
      split.
      + subst la1.
        rewrite length_take_le; last (eapply Nat.lt_le_incl, lookup_lt_Some; eauto).
        rewrite length_take_le; last (eapply Nat.lt_le_incl, lookup_lt_Some; eauto).
        done.
      + subst la2.
        rewrite !length_drop.
        rewrite Hlength_mem.
        done.
    }
    rewrite Ha' Hlw.
    iDestruct ( big_sepL2_app' with "Hmem") as "[Hmem1 Hmem]"; auto.
    iDestruct ( big_sepL2_cons with "Hmem") as "[Ha Hmem2]"; auto.
    iInstr "Hcode".
    { split; auto; solve_addr. }
    iDestruct ( big_sepL2_cons (λ _ a v, a ↦ₐ v)%I with "[$Ha $Hmem2]") as "Hmem"; auto.
    iDestruct ( big_sepL2_app (λ _ a v, a ↦ₐ v)%I with "[$Hmem1] [$Hmem]") as "Hmem"; auto.
    rewrite - Ha' - Hlw.
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 1 "Hcode" as a_checkint Ha_checkint "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (is_int_spec with "[- $HPC $Hr1 $Hr2 $Hcode]"); eauto.
    iSplitR "Hfailed"; last (iNext; iApply "Hfailed").
    iNext; iIntros "(HPC & Hr1 & %Hz & Hr2 & Hcode)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 2 "Hcode" as a_cond Ha_cond "Hcode" "Hcont"; iHide "Hcont" as hcont ; clear Ha_checkint a_checkint.
    iInstr "Hcode".
    { transitivity (Some (a^+1)%a); auto; solve_addr. }
    iInstr "Hcode".
    iInstr "Hcode".
    iInstr "Hcode".
    destruct (decide ((a + 1%nat)%Z < e)%Z) as [Hae' | Hae']; cycle 1.
    - replace (a ^+ 1)%a with e by solve_addr.
      replace (e <? e)%Z with false by solve_addr.
      iInstr "Hcode".
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".
      replace (finz.max b e) with e by solve_addr.
      replace (a_cond ^+ 5)%a with (pc_a ^+ length (checkints_loop_instrs r r1 r2))%a by solve_addr.
      iApply "Hφ"; iFrame; eauto.
      iPureIntro.
      apply Forall_forall.
      intros v Hv.
      rewrite Forall_forall in Hall.
      apply elem_of_list_lookup in Hv as [k Hv].
      destruct (decide (k = ka)) as [-> | Hkeq]; cycle 1.
      + eapply Hall; eauto.
        {  by apply elem_of_list_lookup_2 in Hv. }
        eexists k; split; first done.
        assert (is_Some (l !! k)) as [f Hk].
        { apply lookup_lt_is_Some_2.
          eapply lookup_lt_Some in Hv; eauto.
          rewrite Hlength_mem.
          done.
        }
        assert (f ≠ a).
        { intros ->.
          apply Hkeq.
          eapply NoDup_lookup; eauto.
          setoid_rewrite Hl.
          apply finz_seq_between_NoDup.
        }
        exists f; split; auto.
        apply elem_of_list_lookup_2 in Hk.
        setoid_rewrite Hl in Hk.
        replace e with (a ^+1)%a in Hk; last solve_addr.
        apply elem_of_finz_seq_between in Hk.
        solve_addr.
      + destruct Hz as (z & Hz); cbn in *.
        assert ( w = WInt z) ; simplify_eq.
        { destruct w ; destruct_perm p; done. }
        rewrite list_lookup_middle in Hv; simplify_eq; first (eexists ; done).
        rewrite Hlw1; subst la1.
        rewrite length_take_le; last (eapply Nat.lt_le_incl, lookup_lt_Some; eauto).
        done.
    - replace ((a ^+ 1)%a <? e)%Z with true by solve_addr.
      iInstr "Hcode".
      { transitivity (Some pc_a); auto; solve_addr. }
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".
      iApply ("IH" with "[] [] [$] [$] [$] [$] [$] [$] [$]"); eauto.
      { iPureIntro; solve_addr. }
      { iPureIntro.
        apply Forall_forall.
        rewrite Forall_forall in Hall.
        intros v Hv Hk.
        destruct Hk as (k & Hwk & ak & Hak & Hak_bounds).
        destruct (decide (ak = a)) as [-> | Ha_ak].
        + assert (k = ka); simplify_eq.
          {
            eapply NoDup_lookup; eauto.
            setoid_rewrite Hl.
            apply finz_seq_between_NoDup.
          }
          destruct Hz as (z & Hz); cbn in *.
          assert ( w = WInt z) ; simplify_eq.
          { destruct w ; destruct_perm p; done. }
          rewrite list_lookup_middle in Hwk; simplify_eq; first (eexists ; done).
          rewrite Hlw1; subst la1.
          rewrite length_take_le; last (eapply Nat.lt_le_incl, lookup_lt_Some; eauto).
          done.
        + apply Hall; eauto.
          exists k; split; auto.
          exists ak; split; auto.
          solve_addr.
      }
  Qed.

  Lemma checkints_spec
    (r r1 r2 : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (w1 w2 : Word) (l : list Addr) (ws : list Word)
    (p : Perm) (g : Locality) (b e a : Addr)
    (φ : language.val cap_lang → iPropI Σ) :

    let checkints := (checkints_instrs r r1 r2) in
    let a_last := (pc_a ^+ length checkints)%a in
    executeAllowed pc_p = true →
    SubBounds pc_b pc_e pc_a a_last →
    l ≡ₚ (finz.seq_between b e) ->
    readAllowed p = true ->
    r ≠ cnull ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    ▷ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
    ∗ ▷ r ↦ᵣ (WCap p g b e a)
    ∗ ▷ r1 ↦ᵣ w1
    ∗ ▷ r2 ↦ᵣ w2
    ∗ ▷ codefrag pc_a checkints
    ∗ ▷ ( [∗ list] a;v ∈ l;ws, a ↦ₐ v )
    ∗ ▷ ( PC ↦ᵣ WCap pc_p pc_g pc_b pc_e a_last
         ∗ r ↦ᵣ WCap p g b e (finz.max b e)
         ∗ r1 ↦ᵣ WInt 0%Z
         ∗ r2 ↦ᵣ WInt 0%Z
         ∗ ( [∗ list] a;v ∈ l;ws, a ↦ₐ v )
         ∗ ⌜ Forall (λ w, ∃ z, w = WInt z) ws ⌝
         ∗ codefrag pc_a checkints
         ∗ £ 2
         -∗ WP Seq (Instr Executable) {{ φ }}
        )
    ∗ □ (▷ φ FailedV)
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    intros checkints a_last ; subst checkints a_last.
    iIntros (Hvpc Hcont Hl Hra Hrcnull Hr1cnull Hr2cnull)
      "(>HPC & >Hr & >Hr1 & >Hr2 & >Hcode & >Hmem & Hφ & #Hfailed)".
    iDestruct (big_sepL2_length with "Hcode") as %Hlength.
    iDestruct (big_sepL2_length with "Hmem") as %Hlength_mem
    ; setoid_rewrite Hl in Hlength_mem.
    codefrag_facts "Hcode".
    rename H into HcontRegion; clear H0.
    rewrite /checkints_instrs.

    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (lea_to_base_spec with "[- $HPC $Hr $Hr1 $Hr2 $Hcode]"); eauto.
    iNext; iIntros "(HPC & Hr & Hr1 & Hr2 & Hcode)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 1 "Hcode" as a_init Ha_init "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iInstr "Hcode" with "Hlc".
    iInstr "Hcode" with "Hlc".
    iInstr "Hcode".
    iInstr "Hcode".
    destruct (decide (b < e)%a) as [Hbe|Hbe]; cycle 1.
    { pose proof Hbe as Hbe'.
      apply Z.ltb_nlt in Hbe; rewrite Hbe ; cbn.
      replace (0 - 1%nat)%Z with (-1)%Z by lia.
      iInstr "Hcode".
      { transitivity (Some (a_init ^+ 16)%a); auto; solve_addr. }
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".
      focus_block 3 "Hcode" as a_end Ha_end "Hcode" "Hcont"; iHide "Hcont" as hcont; clear Ha_init a_init.
      iInstr "Hcode".
      iInstr "Hcode".
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".
      replace (a_end ^+ 2)%a with (pc_a ^+ 24%nat)%a by solve_addr.
      replace (finz.max b e) with b by solve_addr.
      iApply "Hφ"; iFrame; eauto.
      rewrite finz_seq_between_length finz_dist_0 in Hlength_mem; last solve_addr.
      symmetry in Hlength_mem. apply nil_length_inv in Hlength_mem; simplify_eq.
      done.
    }

    apply Z.ltb_lt in Hbe; rewrite Hbe; cbn.
    replace (1 - 1%nat)%Z with 0%Z by lia.
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".
    focus_block 2 "Hcode" as a_loop Ha_loop "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear Ha_init a_init.
    iApply (checkints_loop_spec with "[- $HPC $Hr $Hr1 $Hr2 $Hcode $Hmem]"); eauto.
    { solve_addr. }
    { apply Forall_forall.
      intros v Hv (k & Hkv & (ka & Hka & Hka_bounds)).
      solve_addr.
    }
    iSplitR "Hfailed"; last (iModIntro ; iNext ; iApply "Hfailed").
    iNext; iIntros "(HPC & Hr & Hr1 & Hr2 & Hmem & % & Hcode)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 3 "Hcode" as a_end Ha_end "Hcode" "Hcont"; iHide "Hcont" as hcont; clear Ha_loop a_loop.
    iInstr "Hcode".
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".
    replace (a_end ^+ 2)%a with (pc_a ^+ 24%nat)%a by solve_addr.
    iApply "Hφ"; iFrame; eauto.
  Qed.

End Checkints_spec.
