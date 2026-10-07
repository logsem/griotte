From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Export logrel_binary.

(** Pure lemmas used to relate the two runs. *)

Lemma load_word_int_inv (p : Perm) (w : Word) (z : Z) :
  load_word p w = WInt z → w = WInt z.
Proof.
  rewrite /load_word.
  destruct w as [ | [ | ] | | ]; destruct (isDL p), (isDRO p); cbn; done.
Qed.

(** If the loaded instruction words are related and the implementation word
    decodes to an instruction other than [Fail], then both words are equal. *)
Lemma load_word_decode_eq `{MachineParameters} (p : Perm) (w1 w2 : Word) :
  (load_word p w1 = load_word p w2
   ∨ ∃ o sb1 sb2, load_word p w1 = WSealed o sb1 ∧ load_word p w2 = WSealed o sb2) →
  decodeInstrW w1 ≠ Fail →
  w1 = w2.
Proof.
  intros Hload Hdec.
  destruct w1 as [z | | | ]; cbn in Hdec; try done.
  destruct Hload as [Hload | (o & sb1 & sb2 & Hload & _)].
  - rewrite {1}/load_word in Hload.
    destruct (isDL p), (isDRO p); cbn in Hload; symmetry in Hload;
      by apply load_word_int_inv in Hload.
  - rewrite /load_word in Hload.
    destruct (isDL p), (isDRO p); cbn in Hload; done.
Qed.

Lemma incrementPC_gen_PC_eq (regs1 regs2 regs1' : Reg) (n : Z) :
  regs1 !! PC = regs2 !! PC →
  incrementPC_gen regs1 n = Some regs1' →
  incrementPC_gen regs2 n = None →
  False.
Proof. rewrite /incrementPC_gen; intros ->; by repeat case_match. Qed.

Lemma insert_reg_lookup_PC (regs : Reg) (r : RegName) (w : Word) :
  r ≠ PC → <[r:=w]ᵣ> regs !! PC = regs !! PC.
Proof. intros. rewrite /insert_reg lookup_insert_ne //. Qed.

(** Incrementing the PC only depends on the PC: a successful increment
    transfers to any register file with the same PC. *)
Lemma incrementPC_gen_transfer (regs1 regs2 regs1' : Reg) (n : Z) :
  regs1 !! PC = regs2 !! PC →
  incrementPC_gen regs1 n = Some regs1' →
  ∃ wpc, regs1' = <[PC:=wpc]> regs1 ∧ incrementPC_gen regs2 n = Some (<[PC:=wpc]> regs2).
Proof.
  rewrite /incrementPC_gen; intros <-.
  repeat case_match; intros; simplify_eq; eauto.
Qed.

Lemma insert_reg_PC_eq (regs1 regs2 : Reg) (r : RegName) (w : Word) :
  regs1 !! PC = regs2 !! PC →
  <[r:=w]ᵣ> regs1 !! PC = <[r:=w]ᵣ> regs2 !! PC.
Proof.
  intros HPC; rewrite /insert_reg.
  destruct (decide (r = PC)) as [->|]; simplify_map_eq; done.
Qed.

Lemma incrementPC_gen_build (regs : Reg) p g b e a a' n :
  regs !! PC = Some (WCap p g b e a) →
  (a + n)%a = Some a' →
  incrementPC_gen regs n = Some (<[PC:=WCap p g b e a']> regs).
Proof. rewrite /incrementPC_gen; intros -> ->; done. Qed.

(** Rebuild, in the specification run, the PC increment performed by the
    implementation run, from the lookup [HPC] of the PC and the new address [Ha]. *)
Ltac transfer_incrementPC HPC Ha :=
  lazymatch type of HPC with _ !! PC = Some (WCap ?p ?g ?b ?e ?a) =>
  lazymatch type of Ha with (_ + ?n)%a = Some ?a' =>
    apply (incrementPC_gen_build _ p g b e a a' n); [ | exact Ha ];
    rewrite -HPC;
    first [ by simplify_map_eq
          | apply insert_reg_PC_eq; by simplify_map_eq
          | rewrite !insert_reg_lookup_PC //; by simplify_map_eq ]
  end end.

Lemma insert_reg_PC (regs : Reg) (w : Word) :
  <[PC:=w]ᵣ> regs = <[PC:=w]> regs.
Proof. rewrite /insert_reg /=; by case_decide. Qed.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO (Word * Word)) -n> iPropO Σ).
  Implicit Types interp : (V).

  Definition validPCperm (p : Perm) (g : Locality) :=
    executeAllowed p = true ∧ (isWL p = true -> g = Local).

  (** Induction hypothesis of the fundamental theorem: related program
      counters (on the diagonal) are safe to execute. *)
  Definition ftlr_IH: iProp Σ :=
    (□ ▷ (∀ (W_ih : WORLD) (C_ih : CmptName) (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName)
            (r1_ih r2_ih : Reg)
            (p_ih : Perm) (g_ih : Locality) (b_ih e_ih a_ih : Addr),
            spec_ctx
            -∗ interp_reg interp W_ih C_ih (r1_ih, r2_ih)
            -∗ registers_pointsto (<[PC:= WCap p_ih g_ih b_ih e_ih a_ih]> r1_ih)
            -∗ spec_registers_pointsto (<[PC:= WCap p_ih g_ih b_ih e_ih a_ih]> r2_ih)
            -∗ ⤇ Seq (Instr Executable)
            -∗ world_interp W_ih C_ih
            -∗ interp_continuation stk Ws Cs
            -∗ ⌜frame_match Ws Cs stk W_ih C_ih⌝
            -∗ na_own cerise_nais ⊤
            -∗ cstack_frag (map fst stk)
            -∗ cstack_frag_spec (map snd stk)
            -∗ □ interp W_ih C_ih (WCap p_ih g_ih b_ih e_ih a_ih, WCap p_ih g_ih b_ih e_ih a_ih)
            -∗ interp_conf W_ih C_ih))%I.

  (** Postcondition of the instruction cases. *)
  Definition ftlr_post (v : val) : iProp Σ :=
    WP Seq (griotte_lang.of_val v)
      {{ v0, ⌜v0 = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }}%I.

  Definition ftlr_instr_base (W : WORLD) (C : CmptName) (regs1 regs2 : Reg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : Word) (ρ : region_type) (P : V) (Pinstr : Prop)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName)
    : Prop :=
    validPCperm p g
    → isCorrectPC (WCap p g b e a)
    → (b <= a)%a ∧ (a < e)%a
    → PermFlowsTo p p'
    → (persistent_cond P)
    → (if isWL p then region_state_pwl W a else region_state_nwl W a g)
    → std W !! a = Some ρ
    → ρ ≠ Revoked
    → Pinstr
    -> ftlr_IH
    -∗ spec_ctx
    -∗ interp W C (WCap p g b e a, WCap p g b e a)
    -∗ interp_reg interp W C (regs1, regs2)
    -∗ rel C a p' (safeC P)
    -∗ □ (if decide (readAllowed_a_in_regs (<[PC:=WCap p g b e a]> regs1) a)
            then ▷ (rcond P C p' interp)
            else emp)
    -∗ □ (if decide (writeAllowed_a_in_regs (<[PC:=(WCap p g b e a)]> regs1) a)
          then ▷ wcond P C interp
          else emp)
    -∗ monoReq W C a p' P
    -∗ ▷ WorldRes W C a p' (safeC P) (w, w) ρ
    -∗ interp_continuation stk Ws Cs
    -∗ ⌜frame_match Ws Cs stk W C⌝
    -∗ world_interp_open W C [a]
    -∗ na_own cerise_nais ⊤
    -∗ cstack_frag (map fst stk)
    -∗ cstack_frag_spec (map snd stk)
    -∗ sts_state_std C a ρ
    -∗ ⤇ Seq (Instr Executable)
    -∗ ([∗ map] k↦y ∈ <[PC:=WCap p g b e a]> regs1, k ↦ᵣ y)
    -∗ ([∗ map] k↦y ∈ <[PC:=WCap p g b e a]> regs2, k ↣ᵣ y)
    -∗ WP Instr Executable {{ v, ftlr_post v }}.

  Definition ftlr_instr (W : WORLD) (C : CmptName) (regs1 regs2 : Reg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : Word) (i: instr) (ρ : region_type) (P : V)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName)
    : Prop :=
    ftlr_instr_base W C regs1 regs2 p p' g b e a w ρ P (decodeInstrW w = i) stk Ws Cs.

  (** ** Helper lemmas on related register files *)

  Global Instance interp_reg_persistent W C (regs : Reg * Reg) :
    Persistent (interp_reg interp W C regs).
  Proof. rewrite /interp_reg /full_map /=; apply _. Qed.

  Lemma interp_reg_full_map_1 W C regs1 regs2 :
    interp_reg interp W C (regs1, regs2) -∗ ⌜∀ r, is_Some (regs1 !! r)⌝.
  Proof. iIntros "(%H & _ & _)"; done. Qed.

  Lemma interp_reg_full_map_2 W C regs1 regs2 :
    interp_reg interp W C (regs1, regs2) -∗ ⌜∀ r, is_Some (regs2 !! r)⌝.
  Proof. iIntros "(_ & %H & _)"; done. Qed.

  Lemma interp_reg_insert W C regs1 regs2 r w1 w2 :
    interp_reg interp W C (regs1, regs2) -∗
    (⌜r ≠ PC⌝ → ⌜r ≠ cnull⌝ → interp W C (w1, w2)) -∗
    interp_reg interp W C (<[r:=w1]ᵣ> regs1, <[r:=w2]ᵣ> regs2).
  Proof.
    iIntros "#(%Hfull1 & %Hfull2 & Hreg) #Hw".
    rewrite /insert_reg.
    iSplit; [|iSplit].
    - iPureIntro; intros r'; apply lookup_insert_is_Some'; eauto.
    - iPureIntro; intros r'; apply lookup_insert_is_Some'; eauto.
    - iIntros (r' v1 v2 Hr' Hv1 Hv2); cbn in *.
      destruct (decide (r = r')) as [<-|Hne].
      + rewrite !lookup_insert_eq in Hv1 Hv2; simplify_eq.
        destruct (decide (r = cnull)); simplify_eq; first iApply interp_int.
        by iApply "Hw".
      + rewrite !lookup_insert_ne // in Hv1 Hv2.
        by iApply "Hreg".
  Qed.

  Lemma interp_reg_insert_raw W C regs1 regs2 r w1 w2 :
    interp_reg interp W C (regs1, regs2) -∗
    (⌜r ≠ PC⌝ → interp W C (w1, w2)) -∗
    interp_reg interp W C (<[r:=w1]> regs1, <[r:=w2]> regs2).
  Proof.
    iIntros "#(%Hfull1 & %Hfull2 & Hreg) #Hw".
    iSplit; [|iSplit].
    - iPureIntro; intros r'; apply lookup_insert_is_Some'; eauto.
    - iPureIntro; intros r'; apply lookup_insert_is_Some'; eauto.
    - iIntros (r' v1 v2 Hr' Hv1 Hv2); cbn in *.
      destruct (decide (r = r')) as [<-|Hne].
      + rewrite !lookup_insert_eq in Hv1 Hv2; simplify_eq.
        by iApply "Hw".
      + rewrite !lookup_insert_ne // in Hv1 Hv2.
        by iApply "Hreg".
  Qed.

  Lemma interp_reg_insert_PC W C regs1 regs2 w1 w2 :
    interp_reg interp W C (regs1, regs2) -∗
    interp_reg interp W C (<[PC:=w1]> regs1, <[PC:=w2]> regs2).
  Proof.
    iIntros "#H".
    iApply (interp_reg_insert_raw with "H").
    by iIntros (?).
  Qed.

  (** The operands read in related register files (where the PC holds
      the same word) are related. *)
  Lemma interp_reg_lookup W C regs1 regs2 wpc r v1 v2 :
    <[PC:=wpc]> regs1 !!ᵣ r = Some v1 →
    <[PC:=wpc]> regs2 !!ᵣ r = Some v2 →
    interp W C (wpc, wpc) -∗
    interp_reg interp W C (regs1, regs2) -∗
    interp W C (v1, v2).
  Proof.
    iIntros (Hv1 Hv2) "#Hpc #(_ & _ & Hreg)".
    rewrite /lookup_reg in Hv1 Hv2.
    destruct (decide (r = cnull)) as [->|Hnull].
    { destruct (<[PC:=wpc]> regs1 !! cnull), (<[PC:=wpc]> regs2 !! cnull); cbn in *; simplify_eq.
      iApply interp_int. }
    destruct (decide (r = PC)) as [->|HPC].
    { rewrite !lookup_insert_eq in Hv1 Hv2; cbn in *; simplify_eq; done. }
    rewrite !lookup_insert_ne // in Hv1 Hv2.
    destruct (regs1 !! r) as [w1|] eqn:H1; rewrite H1 /= in Hv1; last done.
    destruct (regs2 !! r) as [w2|] eqn:H2; rewrite H2 /= in Hv2; last done.
    simplify_eq.
    by iApply "Hreg".
  Qed.

  Lemma interp_reg_lookup_Some W C regs1 regs2 wpc r :
    interp_reg interp W C (regs1, regs2) -∗
    ⌜∃ v, <[PC:=wpc]> regs2 !!ᵣ r = Some v⌝.
  Proof.
    iIntros "(_ & %Hfull & _)"; iPureIntro.
    apply is_Some_lookup_reg.
    apply lookup_insert_is_Some'; eauto.
  Qed.

  Lemma interp_word_of_argument W C regs1 regs2 wpc src v1 v2 :
    word_of_argument (<[PC:=wpc]> regs1) src = Some v1 →
    word_of_argument (<[PC:=wpc]> regs2) src = Some v2 →
    interp W C (wpc, wpc) -∗
    interp_reg interp W C (regs1, regs2) -∗
    interp W C (v1, v2).
  Proof.
    iIntros (Hv1 Hv2) "#Hpc #Hreg".
    destruct src as [z|r]; cbn in *; simplify_eq.
    - iApply interp_int.
    - by iApply (interp_reg_lookup with "Hpc Hreg").
  Qed.

  Lemma interp_reg_word_of_argument_Some W C regs1 regs2 wpc src :
    interp_reg interp W C (regs1, regs2) -∗
    ⌜∃ v, word_of_argument (<[PC:=wpc]> regs2) src = Some v⌝.
  Proof.
    iIntros "#Hreg".
    destruct src as [z|r]; cbn; first by eauto.
    iApply (interp_reg_lookup_Some with "Hreg").
  Qed.

  (** Related words agree on [z_of_argument]. *)
  Lemma interp_z_of_argument W C regs1 regs2 wpc src :
    interp W C (wpc, wpc) -∗
    interp_reg interp W C (regs1, regs2) -∗
    ⌜z_of_argument (<[PC:=wpc]> regs1) src = z_of_argument (<[PC:=wpc]> regs2) src⌝.
  Proof.
    iIntros "#Hpc #Hreg".
    destruct src as [z|r]; cbn; first done.
    iDestruct (interp_reg_full_map_1 with "Hreg") as %Hfull1.
    iDestruct (interp_reg_lookup_Some _ _ _ _ wpc r with "Hreg") as %[v2 Hv2].
    assert (is_Some (<[PC:=wpc]> regs1 !!ᵣ r)) as [v1 Hv1].
    { apply is_Some_lookup_reg, lookup_insert_is_Some'; eauto. }
    iDestruct (interp_reg_lookup with "Hpc Hreg") as "Hv"; [exact Hv1|exact Hv2|].
    rewrite Hv1 Hv2.
    iDestruct (interp_eq_unless_sealed with "Hv") as %[->|(?&?&?&->&->)]; done.
  Qed.

  Lemma interp_reg_lookup_same W C regs1 regs2 wpc r v1 :
    <[PC:=wpc]> regs1 !!ᵣ r = Some v1 →
    is_sealed v1 = false →
    interp W C (wpc, wpc) -∗
    interp_reg interp W C (regs1, regs2) -∗
    ⌜<[PC:=wpc]> regs2 !!ᵣ r = Some v1⌝.
  Proof.
    iIntros (Hv1 Hsealed) "#Hpc #Hreg".
    iDestruct (interp_reg_lookup_Some _ _ _ _ wpc r with "Hreg") as %[v2 Hv2].
    iDestruct (interp_reg_lookup with "Hpc Hreg") as "Hv"; [exact Hv1|exact Hv2|].
    by iDestruct (interp_eq_not_sealed with "Hv") as %<-.
  Qed.

  Lemma interp_nonZero W C v1 v2 :
    interp W C (v1, v2) -∗ ⌜nonZero v1 = nonZero v2⌝.
  Proof.
    iIntros "Hv".
    by iDestruct (interp_eq_unless_sealed with "Hv") as %[->|(?&?&?&->&->)].
  Qed.

End fundamental.

(** The implementation run failed: the postcondition holds trivially. *)
Ltac ftlr_impl_fail :=
  iApply wp_pure_step_later; auto; iNext; iIntros "_";
  iApply wp_value;
  let H := fresh "Hcontr" in iIntros (H); inversion H.
