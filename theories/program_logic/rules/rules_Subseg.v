From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base.
From griotte Require Import rules_regs capability_monotonicity_base.
#[local] Open Scope capability_scope.

(** * Subseg

    Subseg has no WP rule of its own: [iInstr] steps it with the register
    rules of [rules_regs.v], from its register steps in closed form below.
    Two rules with a witness remain: the heap root of a new base, and the
    rebase on an identifier. *)

(* Discharges [subseg_root_free] on a literal register map. *)
Ltac solve_subseg_root_free :=
  let Hd := fresh "Hd" in let Ha1 := fresh "Ha1" in let Ha2 := fresh "Ha2" in
  let Ht := fresh "Ht" in let Hlt := fresh "Hlt" in
  intros ? ? ? ? ? ? ? ? Hd Ha1 Ha2 Ht Hlt;
  rewrite /laddr_of_argument /lz_of_argument ?/llookup_reg in Ha1, Ha2, Hd;
  simplify_map_eq;
  first [ done | solve_addr | congruence
        | match goal with H : None = None → _ |- _ => by apply H end ].

Section subseg_next_ok.
  Context `{MP : MachineParameters}.

  (** An identifier-less source narrowed to a tagged, non-empty heap result
      needs its new base outside the heap. *)
  Definition subseg_root_free (regs : LReg) (src : RegName) arg1 arg2 : Prop :=
    ∀ t p g b e a a1 a2,
      regs !!ₗ src = Some (WCap t p g b e a @@? None) →
      laddr_of_argument regs arg1 = Some a1 →
      laddr_of_argument regs arg2 = Some a2 →
      (t && isWithin a1 a2 b e && (a1 <=? a2)%a) = true →
      (a1 < a2)%a →
      is_heap_address a1 = false.

  (** Subseg of a capability with representable endpoints writes the new
      bounds, the tag kept only within the old bounds. *)
  Lemma subseg_agree_cap pl lpc regs dst src ρ1 ρ2 (t : bool) p g b e a π n1 n2 a1 a2 :
    regs !!ₗ src = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs ρ1 = Some n1 →
    lz_of_argument regs ρ2 = Some n2 →
    z_to_addr n1 = Some a1 →
    z_to_addr n2 = Some a2 →
    regs_next_agree exec_opt (Subseg dst src ρ1 ρ2) pl lpc regs dst
      (WCap (t && isWithin a1 a2 b e && (a1 <=? a2)%a) p g a1 a2 a @@? π) 1 (λ S, S src).
  Proof.
    intros Hsrc H1 H2 Ha1 Ha2 φ S _ Hcopy.
    rewrite /= (regs_copy_llookup _ _ _ _ _ Hcopy Hsrc) /= (regs_copy_z _ _ _ _ _ Hcopy H1)
      (regs_copy_z _ _ _ _ _ Hcopy H2) /= Ha1 Ha2 /regs_effect.
    by destruct (S src).
  Qed.

  Lemma subseg_next_ok_cap pl lpc regs dst src ρ1 ρ2 (t : bool) p g b e a π n1 n2 a1 a2 :
    regs !!ₗ src = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs ρ1 = Some n1 →
    lz_of_argument regs ρ2 = Some n2 →
    z_to_addr n1 = Some a1 →
    z_to_addr n2 = Some a2 →
    subseg_root_free regs src ρ1 ρ2 →
    regs_next_ok (Subseg dst src ρ1 ρ2) pl lpc regs dst
      (WCap (t && isWithin a1 a2 b e && (a1 <=? a2)%a) p g a1 a2 a @@? π) 1.
  Proof.
    intros Hsrc H1 H2 Ha1 Ha2 Hfree. exists (λ S, S src).
    split; last by eapply subseg_agree_cap.
    assert (regs !! src = Some (WCap t p g b e a @@? π)) as Hsrc'.
    { rewrite /llookup_reg in Hsrc. by case_decide. }
    apply (lsource_reg _ _ _ _ _ Hsrc'); [| done |].
    - destruct (t && isWithin a1 a2 b e && (a1 <=? a2)%a) eqn:Htag; last by apply wle_untagged.
      apply andb_true_iff in Htag as [ [-> Hwithin]%andb_true_iff Hle%Z.leb_le].
      apply isWithin_implies in Hwithin. cbn.
      apply wle_cap; [done | apply PermFlowsToReflexive | apply LocalityFlowsToReflexive
                     | solve_addr | solve_addr | right; solve_addr].
    - intros Hπ Htag. right. cbn in Hπ; subst π. rewrite /heap_authority_base /heap_cap_base /=.
      case_decide as Hlt; last done.
      rewrite (Hfree t p g b e a a1 a2 Hsrc); [done | | | done | done];
        rewrite /laddr_of_argument ?H1 ?H2 //.
  Qed.

  (** A result within the old bounds keeps the tag: the facts of the
      dedicated rules. *)
  Lemma subseg_next_ok_cap_valid pl lpc regs dst src ρ1 ρ2 (t : bool) p g b e a π n1 n2 a1 a2 :
    regs !!ₗ src = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs ρ1 = Some n1 →
    lz_of_argument regs ρ2 = Some n2 →
    z_to_addr n1 = Some a1 →
    z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (a1 <= a2)%a →
    (π = None → (a1 < a2)%a → is_heap_address a1 = false) →
    regs_next_ok (Subseg dst src ρ1 ρ2) pl lpc regs dst (WCap t p g a1 a2 a @@? π) 1.
  Proof.
    intros Hsrc H1 H2 Ha1 Ha2 Hwb Hle Hroot.
    assert ((a1 <=? a2)%a = true) as Hle' by solve_addr.
    pose proof (subseg_next_ok_cap pl lpc regs dst src ρ1 ρ2 t p g b e a π n1 n2 a1 a2
                  Hsrc H1 H2 Ha1 Ha2) as Hok.
    rewrite Hwb Hle' !andb_true_r in Hok. apply Hok.
    intros t' p' g' b' e' a' a1' a2' Hsrc' Ha1' Ha2' _ Hlt.
    rewrite Hsrc in Hsrc'. simplify_eq.
    rewrite /laddr_of_argument H1 Ha1 in Ha1'.
    rewrite /laddr_of_argument H2 Ha2 in Ha2'.
    simplify_eq.
    by apply Hroot.
  Qed.

  (** Both endpoints from the same operand: an empty result. *)
  Lemma subseg_next_ok_cap_same pl lpc regs dst src ρ (t : bool) p g b e a π n1 a1 :
    regs !!ₗ src = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs ρ = Some n1 →
    z_to_addr n1 = Some a1 →
    isWithin a1 a1 b e = true →
    regs_next_ok (Subseg dst src ρ ρ) pl lpc regs dst (WCap t p g a1 a1 a @@? π) 1.
  Proof.
    intros Hsrc H1 Ha1 Hwb.
    eapply subseg_next_ok_cap_valid;
      [exact Hsrc | exact H1 | exact H1 | exact Ha1 | exact Ha1 | exact Hwb | solve_addr |].
    intros _ Hlt. exfalso. solve_addr.
  Qed.

  (** [Subseg dst dst dst ρ2]: the base is the address of the capability
      itself (CHERIoT's [csetbounds]). *)
  Lemma subseg_next_ok_cap_base pl lpc regs dst ρ2 (t : bool) p g b e a π n2 a2 :
    regs !!ₗ dst = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs ρ2 = Some n2 →
    z_to_addr n2 = Some a2 →
    isWithin a a2 b e = true →
    (a <= a2)%a →
    (π = None → (a < a2)%a → is_heap_address a = false) →
    regs_next_ok (Subseg dst dst (inr dst) ρ2) pl lpc regs dst (WCap t p g a a2 a @@? π) 1.
  Proof.
    intros Hd H2 Ha2 Hwb Hle Hroot.
    eapply subseg_next_ok_cap_valid; [exact Hd | | exact H2 | apply finz_of_z_to_z | done..].
    by rewrite /lz_of_argument Hd.
  Qed.

  Lemma subseg_next_ok_cap_untagged pl lpc regs dst src ρ1 ρ2 (t : bool) p g b e a π n1 n2 :
    regs !!ₗ src = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs ρ1 = Some n1 →
    lz_of_argument regs ρ2 = Some n2 →
    z_to_addr n1 = None ∨ z_to_addr n2 = None →
    regs_next_ok (Subseg dst src ρ1 ρ2) pl lpc regs dst (Cap⁻ p g b e a @@? π) 1.
  Proof.
    intros Hsrc H1 H2 Hnone. exists (λ _, true). split; first by apply lsource_untagged.
    intros φ S _ Hcopy.
    rewrite /= (regs_copy_llookup _ _ _ _ _ Hcopy Hsrc) /= (regs_copy_z _ _ _ _ _ Hcopy H1)
      (regs_copy_z _ _ _ _ _ Hcopy H2) /= /regs_effect ?and_tag_true.
    destruct Hnone as [-> | ->]; first done. by destruct (z_to_addr n1).
  Qed.

  Lemma subseg_next_ok_sr pl lpc regs dst src ρ1 ρ2 (t : bool) p g b e a π n1 n2 o1 o2 :
    regs !!ₗ src = Some (WSealRange t p g b e a @@? π) →
    lz_of_argument regs ρ1 = Some n1 →
    lz_of_argument regs ρ2 = Some n2 →
    z_to_otype n1 = Some o1 →
    z_to_otype n2 = Some o2 →
    regs_next_ok (Subseg dst src ρ1 ρ2) pl lpc regs dst
      (WSealRange (t && isWithin o1 o2 b e) p g o1 o2 a @@? π) 1.
  Proof.
    intros Hsrc H1 H2 Ho1 Ho2. exists (λ S, S src). split.
    - apply (lsource_derive _ _ _ _ _ Hsrc); cbn; [done | by destruct t | done].
    - intros φ S _ Hcopy.
      rewrite /= (regs_copy_llookup _ _ _ _ _ Hcopy Hsrc) /= (regs_copy_z _ _ _ _ _ Hcopy H1)
        (regs_copy_z _ _ _ _ _ Hcopy H2) /= Ho1 Ho2 /regs_effect.
      by destruct (S src).
  Qed.

  (** A result within the old bounds keeps the tag. *)
  Lemma subseg_next_ok_sr_valid pl lpc regs dst src ρ1 ρ2 (t : bool) p g b e a π n1 n2 o1 o2 :
    regs !!ₗ src = Some (WSealRange t p g b e a @@? π) →
    lz_of_argument regs ρ1 = Some n1 →
    lz_of_argument regs ρ2 = Some n2 →
    z_to_otype n1 = Some o1 →
    z_to_otype n2 = Some o2 →
    isWithin o1 o2 b e = true →
    regs_next_ok (Subseg dst src ρ1 ρ2) pl lpc regs dst (WSealRange t p g o1 o2 a @@? π) 1.
  Proof.
    intros Hsrc H1 H2 Ho1 Ho2 Hwb.
    pose proof (subseg_next_ok_sr pl lpc regs dst src ρ1 ρ2 t p g b e a π n1 n2 o1 o2
                  Hsrc H1 H2 Ho1 Ho2) as Hok.
    by rewrite Hwb andb_true_r in Hok.
  Qed.

  Lemma subseg_next_ok_sr_same pl lpc regs dst src ρ (t : bool) p g b e a π n1 o1 :
    regs !!ₗ src = Some (WSealRange t p g b e a @@? π) →
    lz_of_argument regs ρ = Some n1 →
    z_to_otype n1 = Some o1 →
    isWithin o1 o1 b e = true →
    regs_next_ok (Subseg dst src ρ ρ) pl lpc regs dst (WSealRange t p g o1 o1 a @@? π) 1.
  Proof.
    intros Hsrc H1 Ho1 Hwb.
    by eapply subseg_next_ok_sr_valid; [exact Hsrc | exact H1 | exact H1 | exact Ho1 | exact Ho1 |].
  Qed.

  Lemma subseg_next_ok_sr_untagged pl lpc regs dst src ρ1 ρ2 (t : bool) p g b e a π n1 n2 :
    regs !!ₗ src = Some (WSealRange t p g b e a @@? π) →
    lz_of_argument regs ρ1 = Some n1 →
    lz_of_argument regs ρ2 = Some n2 →
    z_to_otype n1 = None ∨ z_to_otype n2 = None →
    regs_next_ok (Subseg dst src ρ1 ρ2) pl lpc regs dst (SealRange⁻ p g b e a @@? π) 1.
  Proof.
    intros Hsrc H1 H2 Hnone. exists (λ _, true). split; first by apply lsource_untagged.
    intros φ S _ Hcopy.
    rewrite /= (regs_copy_llookup _ _ _ _ _ Hcopy Hsrc) /= (regs_copy_z _ _ _ _ _ Hcopy H1)
      (regs_copy_z _ _ _ _ _ Hcopy H2) /= /regs_effect ?and_tag_true.
    destruct Hnone as [-> | ->]; first done. by destruct (z_to_otype n1).
  Qed.

  (** An integer is unchanged; a sealed word or a sentry loses its tag. *)
  Lemma subseg_next_ok_other pl lpc regs dst src ρ1 ρ2 v :
    regs !!ₗ src = Some v →
    is_mutable_range v.(lw) = false →
    regs_next_ok (Subseg dst src ρ1 ρ2) pl lpc regs dst (lclear_tag v) 1.
  Proof.
    intros Hsrc Hmutable. exists (λ _, true). split.
    { apply lsource_untagged, get_tag_clear_tag. }
    intros φ S _ Hcopy.
    rewrite /= (regs_copy_llookup _ _ _ _ _ Hcopy Hsrc) /regs_effect ?and_tag_true.
    destruct v as [w π]; cbn in Hmutable |- *.
    destruct w as [| [] | | ? [] ]; try discriminate Hmutable; by destruct (S src).
  Qed.

  (** *** Sources with a witness *)

  (** A word below a source register whose new heap authority base, if
      any, is [a1], a heap root of the claim map. *)
  Lemma subseg_root_source regs lpc src v0 v a1 :
    regs !! src = Some v0 →
    v.(lw) ⊑ v0.(lw) →
    v.(lprov) = v0.(lprov) →
    (∀ b', heap_authority_base v.(lw) = Some b' → b' = a1) →
    lsource_witness_ok (λ _ C, C !! a1 = Some HeapRoot) regs lpc
      (λ _, v) (λ S, S src) (λ v', v' = v).
  Proof.
    intros Hsrc Hle Hprov Hbase R C st S Hreg Ha1 Hregs _ _.
    cbn beta in Ha1 |- *.
    destruct (Hregs src v0 Hsrc) as [Hok Hphys].
    split_and!; [| by eapply reg_phys_word_le_and_tag | done].
    destruct (get_tag v.(lw)) eqn:Htag; last by apply reg_word_ok_untagged.
    destruct v as [w π]; cbn in Hle, Hprov, Hbase, Htag; subst π.
    apply reg_word_ok_shrink; [done | by apply word_le_shrinks | done |].
    intros _ _ b' Hab. by rewrite (Hbase b' Hab).
  Qed.

  (** An identifier-less, non-executable capability narrowed to exactly the
      range of a live or painting identifier [ι] takes [ι]; the registry
      entry of [ι] comes from the witness. *)
  Lemma subseg_rebase_source regs lpc src p g b e a a1 a2 ι s :
    regs !! src = Some (Cap p g b e a @@? None) →
    isWithin a1 a2 b e = true →
    (a1 <= a2)%a →
    s = ALive ∨ s = APainting →
    executeAllowed p = false →
    lsource_witness_ok (λ R _, ∃ γ, R !! ι = Some (a1, a2, γ, s)) regs lpc
      (λ _, Cap p g a1 a2 a @@ ι) (λ S, S src) (λ v, v = Cap p g a1 a2 a @@ ι).
  Proof.
    intros Hsrc Hwb Hle Hs Hpx R C st S _ [γ HRι] Hregs _ _.
    destruct (Hregs src _ Hsrc) as [_ Hrel]. cbn beta.
    split_and!; [| | done].
    { eapply reg_word_ok_rebase; [exact HRι | by destruct Hs as [-> | ->] | exact Hpx]. }
    revert Hrel. destruct (S src); intros Hrel; rewrite ?and_tag_true ?and_tag_false in Hrel |- *.
    - apply reg_phys_exact. intros ι' x _ Hι Hx. cbn in Hι. simplify_eq.
      cbn. by intros [-> | ->]; destruct Hs.
    - (* The source is an empty heap capability without authority, and so
         is the result. *)
      destruct Hrel as [ [Heq | [_ [ [(? & ? & ? & _) _] | [Hna [base Hh] ] ] ] ] _];
        cbn in *; try discriminate.
      split; last done. right. split; first done. right.
      assert (is_heap_address b = true) as Hbh.
      { rewrite /heap_cap_base /= in Hh. by destruct (is_heap_address b). }
      assert (¬ (b < e)%a) as Hnlt.
      { intros Hlt. apply Hna. split; first done. exists b.
        apply heap_authority_base_memory_cap_bounds. eauto. }
      apply isWithin_implies in Hwb.
      assert (a1 = b) as -> by solve_addr. assert (a2 = b) as -> by solve_addr.
      split.
      + intros [_ [b' Hab] ].
        apply heap_authority_base_memory_cap_bounds in Hab as (? & [= <- <-] & ? & _).
        solve_addr.
      + rewrite /heap_cap_base /= Hbh. eauto.
  Qed.
End subseg_next_ok.

(* The tag as a value ([subseg_next_ok_cap], [subseg_next_ok_sr]) is not a
   hint: on literal operands it would be found before the forms that keep
   the tag, whose facts the clients prove; a client names it with
   [iInstr "H" using subseg_next_ok_cap]. *)
#[export] Hint Resolve subseg_next_ok_cap_same | 0 : regs_next_ok_db.
#[export] Hint Resolve subseg_next_ok_cap_same | 0 : regs_next_ok_lax_db.
#[export] Hint Resolve subseg_next_ok_cap_valid | 1 : regs_next_ok_db.
#[export] Hint Resolve subseg_next_ok_cap_valid | 1 : regs_next_ok_lax_db.
#[export] Hint Resolve subseg_next_ok_sr_same | 0 : regs_next_ok_db.
#[export] Hint Resolve subseg_next_ok_sr_same | 0 : regs_next_ok_lax_db.
#[export] Hint Resolve subseg_next_ok_sr_valid | 1 : regs_next_ok_db.
#[export] Hint Resolve subseg_next_ok_sr_valid | 1 : regs_next_ok_lax_db.
#[export] Hint Resolve subseg_next_ok_cap_untagged | 5 : regs_next_ok_db.
#[export] Hint Resolve subseg_next_ok_sr_untagged | 5 : regs_next_ok_db.
#[export] Hint Resolve subseg_next_ok_other | 5 : regs_next_ok_db.

(** ** The rules with a witness *)

Section subseg_witness_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types r : RegName.
  Implicit Types w : LWord.
  Implicit Types reg : gmap RegName LWord.
  Implicit Types ms : gmap Addr LWord.

  (** The rebase: an identifier-less source narrowed to exactly the range of
      a non-dead identifier [ι] takes [ι]. The source is not executable,
      since an identified word never is. The allocate step
      ([rules_registry]) gives [alloc_obj] and the status token. *)
  Lemma wp_subseg_rebase E pc_p pc_g pc_b pc_e pc_a pc_π w dst r1 r2 p g b e a w1 n1 w2 n2 a1 a2 pc_a'
      ι q s dq :
    decodeInstrW w.(lw) = Subseg dst dst (inr r1) (inr r2) →
    IsLInt w1 n1 →
    IsLInt w2 n2 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (a1 <= a2)%a →
    s = ALive ∨ s = APainting →
    executeAllowed p = false →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ Cap p g b e a @@? None
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ w2
        ∗ alloc_obj ι a1 a2
        ∗ ι ↦st{q} s }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r1 ↦ᵣ w1
          ∗ r2 ↦ᵣ w2
          ∗ dst ↦ᵣ (Cap p g a1 a2 a) @@ ι
          ∗ alloc_obj ι a1 a2
          ∗ ι ↦st{q} s
      }}}.
  Proof.
    iIntros (Hinstr Hw1 Hw2 Hvpc Hn1 Hn2 Hwb Hle Hs Hpx Hpc_a' Hcnull Hcnull' Hcnull'' Φ)
      "(>HPC & >Hpc_a & >Hdst & >Hr1 & >Hr2 & #Hobj & Htok) HΦ".
    destruct (IsLInt_inv _ _ Hw1) as [π1 ->].
    destruct (IsLInt_inv _ _ Hw2) as [π2 ->].
    assert ((a1 <=? a2)%a = true) as Hle' by solve_addr.
    iDestruct (map_of_regs_3 with "Hr1 Hr2 Hdst") as "[Hmap (%Hne12 & %Hne1d & %Hne2d)]".
    set (regs := <[r1 := WInt n1 @@? π1]> (<[r2 := WInt n2 @@? π2]>
                   (<[dst := Cap p g b e a @@? None]> (∅ : LReg)))).
    assert (regs !! dst = Some (Cap p g b e a @@? None)) as Hd.
    { rewrite /regs. by simplify_map_eq. }
    assert (lz_of_argument regs (inr r1) = Some n1) as Hz1.
    { rewrite /lz_of_argument llookup_reg_not_cnull // /regs. by simplify_map_eq. }
    assert (lz_of_argument regs (inr r2) = Some n2) as Hz2.
    { rewrite /lz_of_argument llookup_reg_not_cnull // /regs. by simplify_map_eq. }
    pose proof (subseg_agree_cap pc_p (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst dst
                  (inr r1) (inr r2) true p g b e a None n1 n2 a1 a2
                  ltac:(by rewrite llookup_reg_not_cnull) Hz1 Hz2 Hn1 Hn2) as Hagree.
    rewrite Hwb Hle' in Hagree.
    (* The agreement reads only the physical word: the identifier [ι] of the
       written word is not in it. *)
    iApply (wp_regs_step _ _ _ _ _ _ _ _ _ _ regs dst (λ _, Cap p g a1 a2 a @@ ι) 1 (λ S, S dst)
              (λ v, v = Cap p g a1 a2 a @@ ι) (alloc_obj ι a1 a2 ∗ ι ↦st{q} s)
              (λ R _, ∃ γ, R !! ι = Some (a1, a2, γ, s))
              with "[$HPC $Hpc_a $Hobj $Htok $Hmap]");
      [done | rewrite /regs_instr_ok; by apply sw_of_none | done
      | by eapply subseg_rebase_source | exact Hagree
      | right; rewrite /regs; set_solver+ | |].
    { iIntros (R C) "HR _ [#Hobj' Htok']".
      iDestruct (reg_lookup_obj with "HR Hobj'") as %(γ & s' & HRι).
      iDestruct (reg_lookup_own with "HR Htok'") as %(b' & e' & γ' & HRι').
      rewrite HRι in HRι'. simplify_eq. iPureIntro. by eexists. }
    iIntros "!>" (lpc' regs' retv) "(%Hout & HPC & Hpc_a & [_ Htok] & Hmap)".
    rewrite /regs_outcome (incrementPC_gen_add true _ _ _ _ _ _ _ _ Hpc_a') in Hout.
    destruct Hout as (-> & -> & v & -> & ->).
    rewrite linsert_reg_not_cnull //. subst regs.
    iRegsMap "Hmap"; eauto. iApply "HΦ". iFrame "∗ #".
  Qed.
End subseg_witness_rules.
