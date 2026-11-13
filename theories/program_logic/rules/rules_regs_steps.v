From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base.
From griotte Require Import machine_base rules_regs capability_monotonicity_base
  rules_Get.

(** * The register steps in closed form

    The instructions below have no WP rule of their own: [iInstr] steps them
    with the k-ary register rules of [rules_regs.v], from their register
    steps in closed form, lemmas concluding [regs_next_ok] or
    [regs_jump_agree], each registered in [regs_next_ok_db] (and its case
    lemmas in [regs_next_ok_lax_db]) on the lines after it. *)

(** ** Mov

    Mov has no WP rule of its own: [iInstr] steps it with the register rules
    of [rules_regs.v], from its register step in closed form below. *)

Section mov_next_ok.
  Context `{MP : MachineParameters}.

  (** Mov writes its argument: untagged for an immediate, derived from the
      register otherwise. *)
  Lemma mov_next_ok p lpc regs dst ρ v :
    lword_of_argument regs ρ = Some v → regs_next_ok (Mov dst ρ) p lpc regs dst v 1.
  Proof.
    intros Hv. destruct ρ as [z | r]; cbn in Hv.
    - simplify_eq. exists (λ _, true). split; first by apply lsource_untagged.
      intros φ S _ _. by rewrite /regs_effect and_tag_true.
    - exists (λ S, S r). split.
      + destruct v as [w π]. by apply (lsource_derive _ _ _ _ _ Hv).
      + intros φ S _ Hc. by rewrite /= (regs_copy_llookup _ _ _ _ _ Hc Hv) /regs_effect.
  Qed.

  Lemma mov_next_ok_z p lpc regs dst z :
    regs_next_ok (Mov dst (inl z)) p lpc regs dst (WInt z @@? None) 1.
  Proof. by apply mov_next_ok. Qed.

  Lemma mov_next_ok_reg p lpc regs dst r v :
    regs !!ₗ r = Some v → regs_next_ok (Mov dst (inr r)) p lpc regs dst v 1.
  Proof. exact (mov_next_ok p lpc regs dst (inr r) v). Qed.
End mov_next_ok.

#[export] Hint Resolve mov_next_ok_z | 0 : regs_next_ok_db.
#[export] Hint Resolve mov_next_ok_reg | 0 : regs_next_ok_db.

(** ** BinOp

    The register step of a BinOp in closed form; the operation is
    [binop_denote]. *)

Section binop_definitions.
  Context `{MP: MachineParameters}.

  Definition binop_denote (i: instr) (n1 n2: Z): Z :=
    match i with
    | machine_instructions.Add _ _ _ => (n1 + n2)%Z
    | Sub _ _ _ => (n1 - n2)%Z
    | Mul _ _ _ => (n1 * n2)%Z
    | LAnd _ _ _ => (Z.land n1 n2)
    | LOr _ _ _ => (Z.lor n1 n2)
    | LShiftL _ _ _ => (n1 ≪ n2)%Z
    | LShiftR _ _ _ => (n1 ≫ n2)%Z
    | Lt _ _ _ => (Z.b2z (n1 <? n2)%Z)
    | Le _ _ _ => (Z.b2z (n1 <=? n2)%Z)
    | _ => 0%Z
    end.

  Definition is_BinOp (i: instr) (r: RegName) (arg1 arg2: Z + RegName) :=
    i = machine_instructions.Add r arg1 arg2 ∨
    i = Sub r arg1 arg2 ∨
    i = Mul r arg1 arg2 ∨
    i = LAnd r arg1 arg2 ∨
    i = LOr r arg1 arg2 ∨
    i = LShiftL r arg1 arg2 ∨
    i = LShiftR r arg1 arg2 ∨
    i = Lt r arg1 arg2 ∨
    i = Le r arg1 arg2.

End binop_definitions.

(* Hints to automate proofs of is_BinOp *)
Lemma is_BinOp_Add dst arg1 arg2 :
  is_BinOp (Add dst arg1 arg2) dst arg1 arg2.
Proof. intros; unfold is_BinOp; naive_solver. Qed.
Lemma is_BinOp_Sub dst arg1 arg2 :
  is_BinOp (Sub dst arg1 arg2) dst arg1 arg2.
Proof. intros; unfold is_BinOp; naive_solver. Qed.
Lemma is_BinOp_Mul dst arg1 arg2 :
  is_BinOp (Mul dst arg1 arg2) dst arg1 arg2.
Proof. intros; unfold is_BinOp; naive_solver. Qed.
Lemma is_BinOp_LAnd dst arg1 arg2 :
  is_BinOp (LAnd dst arg1 arg2) dst arg1 arg2.
Proof. intros; unfold is_BinOp; naive_solver. Qed.
Lemma is_BinOp_LOr dst arg1 arg2 :
  is_BinOp (LOr dst arg1 arg2) dst arg1 arg2.
Proof. intros; unfold is_BinOp; naive_solver. Qed.
Lemma is_BinOp_LShiftL dst arg1 arg2 :
  is_BinOp (LShiftL dst arg1 arg2) dst arg1 arg2.
Proof. intros; unfold is_BinOp; naive_solver. Qed.
Lemma is_BinOp_LShiftR dst arg1 arg2 :
  is_BinOp (LShiftR dst arg1 arg2) dst arg1 arg2.
Proof. intros; unfold is_BinOp; naive_solver. Qed.
Lemma is_BinOp_Lt dst arg1 arg2 :
  is_BinOp (Lt dst arg1 arg2) dst arg1 arg2.
Proof. intros; unfold is_BinOp; naive_solver. Qed.
Lemma is_BinOp_Le dst arg1 arg2 :
  is_BinOp (Le dst arg1 arg2) dst arg1 arg2.
Proof. intros; unfold is_BinOp; naive_solver. Qed.

#[export] Hint Resolve is_BinOp_Add : core.
#[export] Hint Resolve is_BinOp_Sub : core.
#[export] Hint Resolve is_BinOp_Mul : core.
#[export] Hint Resolve is_BinOp_LAnd : core.
#[export] Hint Resolve is_BinOp_LOr : core.
#[export] Hint Resolve is_BinOp_LShiftL : core.
#[export] Hint Resolve is_BinOp_LShiftR : core.
#[export] Hint Resolve is_BinOp_Lt : core.
#[export] Hint Resolve is_BinOp_Le : core.

Section binop_next_ok.
  Context `{MP : MachineParameters}.

  (** A BinOp writes the denotation of its operands, untagged. A register
      operand gives the address of its word ([lz_of_argument]): an integer,
      or the address of a capability. *)
  Lemma binop_next_ok i p lpc regs dst ρ1 ρ2 n1 n2 :
    is_BinOp i dst ρ1 ρ2 →
    lz_of_argument regs ρ1 = Some n1 →
    lz_of_argument regs ρ2 = Some n2 →
    regs_next_ok i p lpc regs dst (WInt (binop_denote i n1 n2) @@? None) 1.
  Proof.
    intros Hi Hn1 Hn2. exists (λ _, true). split; first by apply lsource_untagged.
    intros φ S _ Hcopy. destruct_or! Hi; subst i;
      by rewrite /= (regs_copy_z _ _ _ _ _ Hcopy Hn1) (regs_copy_z _ _ _ _ _ Hcopy Hn2)
        /= /regs_effect.
  Qed.
End binop_next_ok.

#[export] Hint Resolve binop_next_ok | 0 : regs_next_ok_db.

(** ** Get

    The register steps of the Get instructions in closed form; the
    operation is [get_denote], and GetTag keeps its rules with a
    witness in [rules_Get.v]. *)

Section get_next_ok.
  Context `{MP : MachineParameters}.

  (** A Get other than GetTag reads the same result on a stripped copy. *)
  Lemma get_denote_and_tag_not_gettag i dst src s (w : Word) :
    is_Get i dst src → i ≠ GetTag dst src → get_denote i (and_tag s w) = get_denote i w.
  Proof.
    intros Hi Hnot. rewrite get_denote_and_tag.
    destruct_or! Hi; subst i; first [done | by destruct Hnot].
  Qed.

  (** A Get other than GetTag writes the denotation of its source,
      untagged. *)
  Lemma get_next_ok i dst src p lpc regs v z :
    is_Get i dst src → i ≠ GetTag dst src →
    regs !!ₗ src = Some v → get_denote i v.(lw) = Some z →
    regs_next_ok i p lpc regs dst (WInt z @@? None) 1.
  Proof.
    intros Hi Hnot Hsrc Hz. exists (λ _, true). split; first by apply lsource_untagged.
    intros [pc r sr m st td] S _ Hcopy.
    rewrite /regs_effect (exec_opt_Get i dst src _ _ _ _ _ _ _ _ Hi
                            (regs_copy_llookup _ _ _ _ _ Hcopy Hsrc)).
    by rewrite (get_denote_and_tag_not_gettag i dst src _ _ Hi Hnot) Hz and_tag_true.
  Qed.

  (** GetTag of an untagged word writes 0. *)
  Lemma gettag_next_ok_untagged dst src p lpc regs v :
    regs !!ₗ src = Some v → get_tag v.(lw) = false →
    regs_next_ok (GetTag dst src) p lpc regs dst (WInt 0 @@? None) 1.
  Proof.
    intros Hsrc Ht. exists (λ _, true). split; first by apply lsource_untagged.
    intros [pc r sr m st td] S _ Hcopy.
    rewrite /regs_effect (exec_opt_Get (GetTag dst src) dst src _ _ _ _ _ _ _ _
                            (is_Get_GetTag dst src) (regs_copy_llookup _ _ _ _ _ Hcopy Hsrc)).
    by rewrite gettag_get_denote get_tag_and_tag Ht andb_false_r and_tag_true.
  Qed.

  (** GetTag to [cnull] writes nothing. *)
  Lemma gettag_jump_agree_to_cnull src p lpc regs v :
    regs !!ₗ src = Some v → regs_jump_agree (GetTag cnull src) p lpc regs 1.
  Proof.
    intros Hsrc [pc r sr m st td] S _ Hcopy.
    rewrite /regs_effect (exec_opt_Get (GetTag cnull src) cnull src _ _ _ _ _ _ _ _
                            (is_Get_GetTag cnull src) (regs_copy_llookup _ _ _ _ _ Hcopy Hsrc)).
    rewrite gettag_get_denote. cbv iota. by rewrite update_reg_cnull.
  Qed.
End get_next_ok.

#[export] Hint Extern 0 (_ ≠ GetTag _ _) => discriminate : regs_next_ok_db.
#[export] Hint Resolve gettag_next_ok_untagged | 0 : regs_next_ok_db.
#[export] Hint Resolve gettag_jump_agree_to_cnull | 0 : regs_next_ok_db.
#[export] Hint Resolve get_next_ok | 5 : regs_next_ok_db.

(** ** ClearTag

    ClearTag has no WP rule of its own: [iInstr] steps it with the register
    rules of [rules_regs.v], from its register step in closed form below. *)

Section cleartag_next_ok.
  Context `{MP : MachineParameters}.

  (** ClearTag writes its source untagged, with its identifier. *)
  Lemma cleartag_next_ok dst src p lpc regs v :
    regs !!ₗ src = Some v → regs_next_ok (ClearTag dst src) p lpc regs dst (lclear_tag v) 1.
  Proof.
    intros Hsrc. exists (λ _, true).
    split; first (apply lsource_untagged; apply get_tag_clear_tag).
    intros φ S _ Hcopy.
    by rewrite /= (regs_copy_llookup _ _ _ _ _ Hcopy Hsrc) /= clear_tag_and_tag
      /regs_effect and_tag_true.
  Qed.
End cleartag_next_ok.

#[export] Hint Resolve cleartag_next_ok | 0 : regs_next_ok_db.

(** ** Auipcc

    Auipcc has no WP rule of its own: [iInstr] steps it with the register
    rules of [rules_regs.v], from its register steps in closed form below. *)

Section auipcc_next_ok.
  Context `{MP : MachineParameters}.

  (** Auipcc writes the PC at an offset address: below the PC, with its
      identifier. *)
  Lemma auipcc_next_ok p0 regs dst imm p g b e a π a' :
    (a + imm)%a = Some a' →
    regs_next_ok (Auipcc dst imm) p0 (Cap p g b e a @@? π) regs dst (Cap p g b e a' @@? π) 1.
  Proof.
    intros Ha'. exists (λ _, true). split.
    - apply lsource_pc; [| done | by intros _ _; left].
      apply capability_monotonicity_base.wle_cap; [done | reflexivity | reflexivity | solve_addr | solve_addr | by left].
    - intros φ S Hpc _. cbn [exec_opt]. rewrite Hpc. cbn [lw]. rewrite Ha'.
      by rewrite /regs_effect and_tag_true.
  Qed.

  (** On an address overflow, the PC untagged. *)
  Lemma auipcc_next_ok_untagged p0 regs dst imm p g b e a π :
    (a + imm)%a = None →
    regs_next_ok (Auipcc dst imm) p0 (Cap p g b e a @@? π) regs dst (Cap⁻ p g b e a @@? π) 1.
  Proof.
    intros Ha'. exists (λ _, true). split; first by apply lsource_untagged.
    intros φ S Hpc _. cbn [exec_opt]. rewrite Hpc. cbn [lw]. rewrite Ha'.
    by rewrite /regs_effect and_tag_true.
  Qed.
End auipcc_next_ok.

#[export] Hint Resolve auipcc_next_ok | 0 : regs_next_ok_db.
#[export] Hint Resolve auipcc_next_ok_untagged | 1 : regs_next_ok_db.
#[export] Hint Resolve auipcc_next_ok : regs_next_ok_lax_db.

(** ** Lea

    Lea has no WP rule of its own: [iInstr] steps it with the register rules
    of [rules_regs.v], from its register steps in closed form below. *)

Section lea_next_ok.
  Context `{MP : MachineParameters}.

  (** The word a Lea writes: for a capability or a sealing range, the moved
      cursor, or the untagged original if the cursor overflows; the moved
      integer; the untagged original otherwise. *)
  Definition lea_result (v : LWord) (z : Z) : option LWord :=
    match v.(lw) with
    | WCap t p g b e a =>
        Some (match (a + z)%a with
              | Some a' => WCap t p g b e a'
              | None => Cap⁻ p g b e a
              end @@? v.(lprov))
    | WSealRange t p g b e a =>
        Some (match (a + z)%ot with
              | Some a' => WSealRange t p g b e a'
              | None => SealRange⁻ p g b e a
              end @@? v.(lprov))
    | WInt n => Some (WInt (n + z) @@? v.(lprov))
    | _ => Some (lclear_tag v)
    end.

  (** [lea_result] is defined on every word. *)
  Lemma lea_result_is_Some (w : LWord) (z : Z) : is_Some (lea_result w z).
  Proof. rewrite /lea_result. repeat case_match; eauto. Qed.

  (** Lea writes [lea_result] of its source, derived from the source. *)
  Lemma lea_next_ok p0 lpc regs dst src ρ v z v' :
    regs !!ₗ src = Some v →
    lz_of_argument regs ρ = Some z →
    lea_result v z = Some v' →
    regs_next_ok (Lea dst src ρ) p0 lpc regs dst v' 1.
  Proof.
    intros Hsrc Hz Hres. exists (λ S, S src). destruct v as [w π].
    rewrite /lea_result /= in Hres. split.
    - destruct w as [n | [t p g b e a | t p g b e a] | k t p g b e a | o [] ]; cbn in Hres;
        simplify_eq; repeat case_match; simplify_eq; rewrite ?/lclear_tag ?/lift_word;
        apply (lsource_derive _ _ _ _ _ Hsrc); cbn; auto; done.
    - intros φ S _ Hc.
      rewrite /= (regs_copy_z _ _ _ _ _ Hc Hz) /= (regs_copy_llookup _ _ _ _ _ Hc Hsrc).
      rewrite /regs_effect.
      destruct (S src); destruct w as [n | [t p g b e a | t p g b e a] | k t p g b e a | o [] ];
        cbn in Hres |- *; simplify_eq; repeat case_match; simplify_eq; done.
  Qed.

  Lemma lea_next_ok_cap p0 lpc regs dst src ρ t p g b e a π z a' :
    regs !!ₗ src = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs ρ = Some z →
    (a + z)%a = Some a' →
    regs_next_ok (Lea dst src ρ) p0 lpc regs dst (WCap t p g b e a' @@? π) 1.
  Proof.
    intros Hsrc Hz Ha'. eapply lea_next_ok; [exact Hsrc | exact Hz |].
    by rewrite /lea_result /= Ha'.
  Qed.

  Lemma lea_next_ok_cap_untagged p0 lpc regs dst src ρ t p g b e a π z :
    regs !!ₗ src = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs ρ = Some z →
    (a + z)%a = None →
    regs_next_ok (Lea dst src ρ) p0 lpc regs dst (Cap⁻ p g b e a @@? π) 1.
  Proof.
    intros Hsrc Hz Ha'. eapply lea_next_ok; [exact Hsrc | exact Hz |].
    by rewrite /lea_result /= Ha'.
  Qed.

  Lemma lea_next_ok_sr p0 lpc regs dst src ρ t p g b e a π z a' :
    regs !!ₗ src = Some (WSealRange t p g b e a @@? π) →
    lz_of_argument regs ρ = Some z →
    (a + z)%ot = Some a' →
    regs_next_ok (Lea dst src ρ) p0 lpc regs dst (WSealRange t p g b e a' @@? π) 1.
  Proof.
    intros Hsrc Hz Ha'. eapply lea_next_ok; [exact Hsrc | exact Hz |].
    by rewrite /lea_result /= Ha'.
  Qed.

  Lemma lea_next_ok_sr_untagged p0 lpc regs dst src ρ t p g b e a π z :
    regs !!ₗ src = Some (WSealRange t p g b e a @@? π) →
    lz_of_argument regs ρ = Some z →
    (a + z)%ot = None →
    regs_next_ok (Lea dst src ρ) p0 lpc regs dst (SealRange⁻ p g b e a @@? π) 1.
  Proof.
    intros Hsrc Hz Ha'. eapply lea_next_ok; [exact Hsrc | exact Hz |].
    by rewrite /lea_result /= Ha'.
  Qed.

  Lemma lea_next_ok_int p0 lpc regs dst src ρ n π z :
    regs !!ₗ src = Some (WInt n @@? π) →
    lz_of_argument regs ρ = Some z →
    regs_next_ok (Lea dst src ρ) p0 lpc regs dst (WInt (n + z) @@? π) 1.
  Proof. intros Hsrc Hz. by eapply lea_next_ok. Qed.
End lea_next_ok.

#[export] Hint Resolve lea_next_ok_cap | 0 : regs_next_ok_db.
#[export] Hint Resolve lea_next_ok_cap : regs_next_ok_lax_db.
#[export] Hint Resolve lea_next_ok_cap_untagged | 0 : regs_next_ok_db.
#[export] Hint Resolve lea_next_ok_sr | 0 : regs_next_ok_db.
#[export] Hint Resolve lea_next_ok_sr : regs_next_ok_lax_db.
#[export] Hint Resolve lea_next_ok_sr_untagged | 0 : regs_next_ok_db.
#[export] Hint Resolve lea_next_ok_int | 0 : regs_next_ok_db.
(* Any word, through [lea_result]: the fact from the context. *)
#[export] Hint Resolve lea_next_ok | 5 : regs_next_ok_db.
#[export] Hint Extern 0 (lea_result _ _ = Some _) => eassumption : regs_next_ok_db.

(** ** SetA

    SetA has no WP rule of its own: [iInstr] steps it with the register rules
    of [rules_regs.v], from its register steps in closed form below. *)

Section seta_next_ok.
  Context `{MP : MachineParameters}.

  (** The word a SetA writes: for a capability or a sealing range, the cursor
      set to the address, or the untagged original if the address is out of
      range; the address itself for an integer; the untagged original
      otherwise. *)
  Definition seta_result (v : LWord) (n : Z) : option LWord :=
    match v.(lw) with
    | WCap t p g b e a =>
        Some (match z_to_addr n with
              | Some a' => WCap t p g b e a'
              | None => Cap⁻ p g b e a
              end @@? v.(lprov))
    | WSealRange t p g b e a =>
        Some (match z_to_otype n with
              | Some a' => WSealRange t p g b e a'
              | None => SealRange⁻ p g b e a
              end @@? v.(lprov))
    | WInt _ => Some (WInt n @@? v.(lprov))
    | _ => Some (lclear_tag v)
    end.

  (** Setting the address to [n] moves the cursor by the difference to [n]. *)
  Lemma seta_result_lea_result (w : LWord) (n : Z) :
    seta_result w n = lea_result w (n - get_a w.(lw)).
  Proof.
    destruct w as [w π]. rewrite /seta_result /lea_result /=.
    destruct_word w; cbn; rewrite ?finz_incr_of_z; repeat f_equal; lia.
  Qed.

  (** SetA writes [seta_result] of its source, derived from the source. *)
  Lemma seta_next_ok p0 lpc regs dst src ρ v n v' :
    regs !!ₗ src = Some v →
    lz_of_argument regs ρ = Some n →
    seta_result v n = Some v' →
    regs_next_ok (SetA dst src ρ) p0 lpc regs dst v' 1.
  Proof.
    intros Hsrc Hn Hres. exists (λ S, S src). destruct v as [w π].
    rewrite /seta_result /= in Hres. split.
    - destruct w as [m | [t p g b e a | t p g b e a] | k t p g b e a | o [] ]; cbn in Hres;
        simplify_eq; repeat case_match; simplify_eq; rewrite ?/lclear_tag ?/lift_word;
        apply (lsource_derive _ _ _ _ _ Hsrc); cbn; auto; done.
    - intros φ S _ Hc.
      rewrite /= (regs_copy_z _ _ _ _ _ Hc Hn) /= (regs_copy_llookup _ _ _ _ _ Hc Hsrc).
      rewrite /regs_effect.
      destruct (S src); destruct w as [m | [t p g b e a | t p g b e a] | k t p g b e a | o [] ];
        cbn in Hres |- *; simplify_eq; repeat case_match; simplify_eq; done.
  Qed.

  Lemma seta_next_ok_cap p0 lpc regs dst src ρ t p g b e a π n a' :
    regs !!ₗ src = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs ρ = Some n →
    z_to_addr n = Some a' →
    regs_next_ok (SetA dst src ρ) p0 lpc regs dst (WCap t p g b e a' @@? π) 1.
  Proof.
    intros Hsrc Hn Ha'. eapply seta_next_ok; [exact Hsrc | exact Hn |].
    by rewrite /seta_result /= Ha'.
  Qed.

  Lemma seta_next_ok_cap_untagged p0 lpc regs dst src ρ t p g b e a π n :
    regs !!ₗ src = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs ρ = Some n →
    z_to_addr n = None →
    regs_next_ok (SetA dst src ρ) p0 lpc regs dst (Cap⁻ p g b e a @@? π) 1.
  Proof.
    intros Hsrc Hn Ha'. eapply seta_next_ok; [exact Hsrc | exact Hn |].
    by rewrite /seta_result /= Ha'.
  Qed.

  Lemma seta_next_ok_sr p0 lpc regs dst src ρ t p g b e a π n a' :
    regs !!ₗ src = Some (WSealRange t p g b e a @@? π) →
    lz_of_argument regs ρ = Some n →
    z_to_otype n = Some a' →
    regs_next_ok (SetA dst src ρ) p0 lpc regs dst (WSealRange t p g b e a' @@? π) 1.
  Proof.
    intros Hsrc Hn Ha'. eapply seta_next_ok; [exact Hsrc | exact Hn |].
    by rewrite /seta_result /= Ha'.
  Qed.

  Lemma seta_next_ok_sr_untagged p0 lpc regs dst src ρ t p g b e a π n :
    regs !!ₗ src = Some (WSealRange t p g b e a @@? π) →
    lz_of_argument regs ρ = Some n →
    z_to_otype n = None →
    regs_next_ok (SetA dst src ρ) p0 lpc regs dst (SealRange⁻ p g b e a @@? π) 1.
  Proof.
    intros Hsrc Hn Ha'. eapply seta_next_ok; [exact Hsrc | exact Hn |].
    by rewrite /seta_result /= Ha'.
  Qed.

  Lemma seta_next_ok_int p0 lpc regs dst src ρ m π n :
    regs !!ₗ src = Some (WInt m @@? π) →
    lz_of_argument regs ρ = Some n →
    regs_next_ok (SetA dst src ρ) p0 lpc regs dst (WInt n @@? π) 1.
  Proof. intros Hsrc Hn. by eapply seta_next_ok. Qed.
End seta_next_ok.

#[export] Hint Resolve seta_next_ok_cap | 0 : regs_next_ok_db.
#[export] Hint Resolve seta_next_ok_cap : regs_next_ok_lax_db.
#[export] Hint Resolve seta_next_ok_cap_untagged | 0 : regs_next_ok_db.
#[export] Hint Resolve seta_next_ok_sr | 0 : regs_next_ok_db.
#[export] Hint Resolve seta_next_ok_sr : regs_next_ok_lax_db.
#[export] Hint Resolve seta_next_ok_sr_untagged | 0 : regs_next_ok_db.
#[export] Hint Resolve seta_next_ok_int | 0 : regs_next_ok_db.
(* Any word, through [seta_result]: the fact from the context, directly or as
   a [lea_result]. *)
#[export] Hint Resolve seta_next_ok | 5 : regs_next_ok_db.
#[export] Hint Extern 0 (seta_result _ _ = Some _) =>
  first [eassumption | rewrite seta_result_lea_result; eassumption] : regs_next_ok_db.

(** ** Restrict

    Restrict has no WP rule of its own: [iInstr] steps it with the register
    rules of [rules_regs.v], from its register steps in closed form below. *)

Section restrict_next_ok.
  Context `{MP : MachineParameters}.

  (** A capability takes the decoded permission and locality, tagged if
      they flow to the old ones; derived from the source. *)
  Lemma restrict_next_ok_cap p0 lpc regs dst src ρ (t : bool) p g b e a π n p' g' :
    regs !!ₗ src = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs ρ = Some n →
    decodePermPair n = (p', g') →
    regs_next_ok (Restrict dst src ρ) p0 lpc regs dst
      (WCap (t && PermFlowsTo p' p && LocalityFlowsTo g' g) p' g' b e a @@? π) 1.
  Proof.
    intros Hsrc Hn Hdec. exists (λ S, S src). split.
    - apply (lsource_derive _ _ _ _ _ Hsrc); cbn.
      + done.
      + by intros [ [Ht _]%andb_prop _]%andb_prop.
      + intros [ [_ Hflows]%andb_prop _]%andb_prop Hexec.
        eapply (executeAllowed_flowsto p' p); [by rewrite Hflows | exact Hexec].
    - intros φ S _ Hcopy.
      rewrite /= (regs_copy_z _ _ _ _ _ Hcopy Hn) /= (regs_copy_llookup _ _ _ _ _ Hcopy Hsrc) /= Hdec.
      rewrite /regs_effect. by destruct (S src).
  Qed.

  (** A sealing range, likewise; a sealing range is never executable. *)
  Lemma restrict_next_ok_sr p0 lpc regs dst src ρ (t : bool) p g b e a π n p' g' :
    regs !!ₗ src = Some (WSealRange t p g b e a @@? π) →
    lz_of_argument regs ρ = Some n →
    decodeSealPermPair n = (p', g') →
    regs_next_ok (Restrict dst src ρ) p0 lpc regs dst
      (WSealRange (t && SealPermFlowsTo p' p && LocalityFlowsTo g' g) p' g' b e a @@? π) 1.
  Proof.
    intros Hsrc Hn Hdec. exists (λ S, S src). split.
    - apply (lsource_derive _ _ _ _ _ Hsrc); cbn.
      + done.
      + by intros [ [Ht _]%andb_prop _]%andb_prop.
      + by intros _ Hexec.
    - intros φ S _ Hcopy.
      rewrite /= (regs_copy_z _ _ _ _ _ Hcopy Hn) /= (regs_copy_llookup _ _ _ _ _ Hcopy Hsrc) /= Hdec.
      rewrite /regs_effect. by destruct (S src).
  Qed.

  (** An integer is unchanged; a sentry or a sealed word loses its tag. *)
  Lemma restrict_next_ok_other p0 lpc regs dst src ρ v n :
    regs !!ₗ src = Some v →
    lz_of_argument regs ρ = Some n →
    is_mutable_range v.(lw) = false →
    regs_next_ok (Restrict dst src ρ) p0 lpc regs dst (lclear_tag v) 1.
  Proof.
    intros Hsrc Hn Hmutable. exists (λ _, true). split.
    { apply lsource_untagged, get_tag_clear_tag. }
    intros φ S _ Hcopy.
    rewrite /= (regs_copy_z _ _ _ _ _ Hcopy Hn) /= (regs_copy_llookup _ _ _ _ _ Hcopy Hsrc)
      /regs_effect.
    destruct v as [ [| [] | | ? [] ] ?]; cbn in Hmutable |- *; try discriminate;
      by rewrite ?and_tag_true ?clear_tag_and_tag.
  Qed.

  (** When the flows hold, the tag is kept. *)
  Lemma restrict_next_ok_cap_flows p0 lpc regs dst src ρ (t : bool) p g b e a π n p' g' :
    regs !!ₗ src = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs ρ = Some n →
    (p', g') = decodePermPair n →
    PermFlowsTo p' p = true →
    LocalityFlowsTo g' g = true →
    regs_next_ok (Restrict dst src ρ) p0 lpc regs dst (WCap t p' g' b e a @@? π) 1.
  Proof.
    intros Hsrc Hn Hdec Hp Hg.
    pose proof (restrict_next_ok_cap p0 lpc regs dst src ρ t p g b e a π n p' g'
                  Hsrc Hn (eq_sym Hdec)) as Hok.
    by rewrite Hp Hg !andb_true_r in Hok.
  Qed.

  Lemma restrict_next_ok_sr_flows p0 lpc regs dst src ρ (t : bool) p g b e a π n p' g' :
    regs !!ₗ src = Some (WSealRange t p g b e a @@? π) →
    lz_of_argument regs ρ = Some n →
    (p', g') = decodeSealPermPair n →
    SealPermFlowsTo p' p = true →
    LocalityFlowsTo g' g = true →
    regs_next_ok (Restrict dst src ρ) p0 lpc regs dst (WSealRange t p' g' b e a @@? π) 1.
  Proof.
    intros Hsrc Hn Hdec Hp Hg.
    pose proof (restrict_next_ok_sr p0 lpc regs dst src ρ t p g b e a π n p' g'
                  Hsrc Hn (eq_sym Hdec)) as Hok.
    by rewrite Hp Hg !andb_true_r in Hok.
  Qed.
End restrict_next_ok.

(* The forms with the flows first: they give the word with its tag. The
   decoding of a permission is never computed: it comes from the context, or
   stays a side goal with the flows. *)
#[export] Hint Resolve restrict_next_ok_cap_flows | 0 : regs_next_ok_db.
#[export] Hint Resolve restrict_next_ok_cap_flows : regs_next_ok_lax_db.
#[export] Hint Resolve restrict_next_ok_sr_flows | 0 : regs_next_ok_db.
#[export] Hint Resolve restrict_next_ok_sr_flows : regs_next_ok_lax_db.
#[export] Hint Resolve restrict_next_ok_cap | 5 : regs_next_ok_db.
#[export] Hint Resolve restrict_next_ok_sr | 5 : regs_next_ok_db.
#[export] Hint Resolve restrict_next_ok_other | 5 : regs_next_ok_db.
#[export] Hint Extern 0 (decodePermPair _ = _) => eassumption : regs_next_ok_db.
#[export] Hint Extern 0 (_ = decodePermPair _) => eassumption : regs_next_ok_db.
#[export] Hint Extern 0 (decodeSealPermPair _ = _) => eassumption : regs_next_ok_db.
#[export] Hint Extern 0 (_ = decodeSealPermPair _) => eassumption : regs_next_ok_db.

(** ** Seal

    Seal has no WP rule of its own: [iInstr] steps it with the register rules
    of [rules_regs.v], from its register steps in closed form below. *)

Section seal_next_ok.
  Context `{MP : MachineParameters}.

  (** A sealing range and a sealable: the sealable sealed at the cursor,
      tagged if the range permits it; derived from the sealable. The sealing
      range is never stripped. *)
  Lemma seal_next_ok p0 lpc regs dst r1 r2 (ta : bool) p g b e a πs sb π :
    regs !!ₗ r1 = Some (WSealRange ta p g b e a @@? πs) →
    regs !!ₗ r2 = Some (WSealable sb @@? π) →
    regs_next_ok (Seal dst r1 r2) p0 lpc regs dst
      (WSealed a (and_tag_sealable (ta && get_tag_sealable sb && permit_seal p && withinBounds b e a) sb)
         @@? π) 1.
  Proof.
    intros H1 H2. exists (λ S, S r2). split.
    { apply (lsource_derive _ _ _ _ _ H2); destruct sb; cbn; try solve [auto];
        by intros [_ Ht]%andb_prop. }
    intros φ S _ Hcopy.
    rewrite /= (regs_copy_llookup _ _ _ _ _ Hcopy H1) (regs_copy_llookup _ _ _ _ _ Hcopy H2).
    destruct (S r1) eqn:Hs1.
    - rewrite /= /regs_effect.
      destruct (S r2), sb as [t' ? ? ? ? ? | t' ? ? ? ? ?], ta, t', (permit_seal p),
        (withinBounds b e a); done.
    - exfalso. rewrite /llookup_reg in H1. case_decide; first done.
      destruct (Hcopy r1 _ H1) as [_ Hstrip]. by destruct (Hstrip Hs1).
  Qed.

  (** The sealable is tagged and the range permits sealing at its cursor:
      the sealable sealed as it is. *)
  Lemma seal_next_ok_tagged p0 lpc regs dst r1 r2 p g b e a πs sb π :
    regs !!ₗ r1 = Some (SealRange p g b e a @@? πs) →
    regs !!ₗ r2 = Some (WSealable sb @@? π) →
    get_tag_sealable sb = true →
    permit_seal p = true →
    withinBounds b e a = true →
    regs_next_ok (Seal dst r1 r2) p0 lpc regs dst (WSealed a sb @@? π) 1.
  Proof.
    intros H1 H2 Htag Hperm Hwb.
    pose proof (seal_next_ok p0 lpc regs dst r1 r2 true p g b e a πs sb π H1 H2) as Hok.
    by rewrite Htag Hperm Hwb /= and_tag_sealable_true in Hok.
  Qed.

  (** Without a sealing range and a sealable, the sealee loses its tag. *)
  Lemma seal_next_ok_other p0 lpc regs dst r1 r2 v1 v2 :
    regs !!ₗ r1 = Some v1 →
    regs !!ₗ r2 = Some v2 →
    is_sealr v1.(lw) && is_sealb v2.(lw) = false →
    regs_next_ok (Seal dst r1 r2) p0 lpc regs dst (lclear_tag v2) 1.
  Proof.
    intros H1 H2 Hkind. exists (λ _, true). split.
    { apply lsource_untagged, get_tag_clear_tag. }
    intros φ S _ Hcopy.
    rewrite /= (regs_copy_llookup _ _ _ _ _ Hcopy H1) (regs_copy_llookup _ _ _ _ _ Hcopy H2)
      /regs_effect.
    destruct v1 as [ [| [] | | ? [] ] ?], v2 as [ [| [] | | ? [] ] ?]; cbn in Hkind |- *;
      try discriminate; by rewrite ?and_tag_true ?clear_tag_and_tag.
  Qed.
End seal_next_ok.

(* [seal_next_ok] is not a hint: on literal operands it has no fact to check
   and would give the word with its tag as a value; a client names it with
   [iInstr "H" using seal_next_ok]. *)
#[export] Hint Resolve seal_next_ok_tagged | 0 : regs_next_ok_db.
#[export] Hint Resolve seal_next_ok_tagged : regs_next_ok_lax_db.
#[export] Hint Resolve seal_next_ok_other | 5 : regs_next_ok_db.
#[export] Hint Extern 1 (is_sealr _ && is_sealb _ = false) =>
  first [ reflexivity | eassumption ] : regs_next_ok_db.

(** ** UnSeal

    UnSeal has no WP rule of its own: [iInstr] steps it with the register
    rules of [rules_regs.v], from its register steps in closed form below. *)

(** The word an UnSeal writes, on any operands: with a sealing range and a
    sealed word, the sealable unsealed, tagged if the range permits it;
    otherwise the second operand untagged. *)
Definition unseal_word (v1 v2 : LWord) : LWord :=
  match v1.(lw), v2.(lw) with
  | WSealRange ta p g b e a, WSealed o sb =>
      WSealable (and_tag_sealable (ta && get_tag_sealable sb && permit_unseal p && withinBounds b e o)
                   (unseal_sb g sb)) @@? v2.(lprov)
  | _, _ => lclear_tag v2
  end.

Lemma unseal_word_not_sealed v1 v2 :
  is_sealr v1.(lw) && is_sealed v2.(lw) = false → unseal_word v1 v2 = lclear_tag v2.
Proof.
  intros Hkind. destruct v1 as [w1 π1], v2 as [w2 π2]; cbn in Hkind.
  destruct w1 as [| [] | | ], w2; cbn in Hkind; try discriminate; done.
Qed.

Section unseal_next_ok.
  Context `{MP : MachineParameters}.

  (** Without a sealing range and a sealed word, the operand loses its
      tag. *)
  Lemma unseal_next_ok_other p0 lpc regs dst r1 r2 v1 v2 :
    regs !!ₗ r1 = Some v1 →
    regs !!ₗ r2 = Some v2 →
    is_sealr v1.(lw) && is_sealed v2.(lw) = false →
    regs_next_ok (UnSeal dst r1 r2) p0 lpc regs dst (lclear_tag v2) 1.
  Proof.
    intros H1 H2 Hkind. exists (λ _, true). split.
    { apply lsource_untagged, get_tag_clear_tag. }
    intros φ S _ Hcopy.
    rewrite /= (regs_copy_llookup _ _ _ _ _ Hcopy H1) (regs_copy_llookup _ _ _ _ _ Hcopy H2)
      /regs_effect.
    destruct v1 as [ [| [] | | ? [] ] ?], v2 as [ [| [] | | ? [] ] ?]; cbn in Hkind |- *;
      try discriminate; by rewrite ?and_tag_true ?clear_tag_and_tag.
  Qed.

  (** UnSeal writes [unseal_word] of its operands, derived from the sealed
      word. The sealing range is never stripped. *)
  Lemma unseal_next_ok p0 lpc regs dst r1 r2 v1 v2 :
    regs !!ₗ r1 = Some v1 →
    regs !!ₗ r2 = Some v2 →
    regs_next_ok (UnSeal dst r1 r2) p0 lpc regs dst (unseal_word v1 v2) 1.
  Proof.
    intros H1 H2. destruct (is_sealr v1.(lw) && is_sealed v2.(lw)) eqn:Hkind.
    2: { rewrite unseal_word_not_sealed //. by eapply unseal_next_ok_other. }
    destruct v1 as [ [| [|ta p g b e a] | | ] πs]; cbn in Hkind; try discriminate.
    destruct v2 as [ [| | | o sb] π]; cbn in Hkind; try discriminate.
    rewrite /unseal_word /=. exists (λ S, S r2). split.
    { apply (lsource_derive _ _ _ _ _ H2); destruct sb; cbn; try solve [auto];
        by intros [_ Ht]%andb_prop. }
    intros φ S _ Hcopy.
    rewrite /= (regs_copy_llookup _ _ _ _ _ Hcopy H1) (regs_copy_llookup _ _ _ _ _ Hcopy H2).
    destruct (S r1) eqn:Hs1.
    - rewrite /= /regs_effect.
      destruct (S r2), sb as [t' ? ? ? ? ? | t' ? ? ? ? ?], ta, t', (permit_unseal p),
        (withinBounds b e o); done.
    - exfalso. rewrite /llookup_reg in H1. case_decide; first done.
      destruct (Hcopy r1 _ H1) as [_ Hstrip]. by destruct (Hstrip Hs1).
  Qed.

  (** The sealable is tagged and the range permits unsealing its otype: the
      sealable unsealed, with its tag. *)
  Lemma unseal_next_ok_tagged p0 lpc regs dst r1 r2 p g b e a πs o sb π :
    regs !!ₗ r1 = Some (SealRange p g b e a @@? πs) →
    regs !!ₗ r2 = Some (WSealed o sb @@? π) →
    get_tag_sealable sb = true →
    permit_unseal p = true →
    withinBounds b e o = true →
    regs_next_ok (UnSeal dst r1 r2) p0 lpc regs dst (WSealable (unseal_sb g sb) @@? π) 1.
  Proof.
    intros H1 H2 Htag Hperm Hwb.
    pose proof (unseal_next_ok p0 lpc regs dst r1 r2 _ _ H1 H2) as Hok.
    by rewrite /unseal_word /= Htag Hperm Hwb /= and_tag_sealable_true in Hok.
  Qed.
End unseal_next_ok.

(* [unseal_next_ok] is not a hint: it has no fact to check and would give
   [unseal_word] where the tagged form gives the sealable; a client names it
   with [iInstr "H" using unseal_next_ok]. *)
#[export] Hint Resolve unseal_next_ok_tagged | 0 : regs_next_ok_db.
#[export] Hint Resolve unseal_next_ok_tagged : regs_next_ok_lax_db.
#[export] Hint Resolve unseal_next_ok_other | 5 : regs_next_ok_db.
#[export] Hint Extern 1 (is_sealr _ && is_sealed _ = false) =>
  first [ reflexivity | eassumption ] : regs_next_ok_db.

(** ** Jmp

    Jmp has no WP rule of its own: [iInstr] steps it with the register rules
    of [rules_regs.v] ([wp_regs_jump_0], [wp_regs_jump_1]), from its register
    step in closed form below. *)

Section jmp_jump_agree.
  Context `{MP : MachineParameters}.

  (** Jmp moves the PC by its operand and writes no register. *)
  Lemma jmp_jump_agree p lpc regs ρ imm :
    lz_of_argument regs ρ = Some imm → regs_jump_agree (Jmp ρ) p lpc regs imm.
  Proof.
    intros Himm φ S _ Hc. by rewrite /= (regs_copy_z _ _ _ _ _ Hc Himm) /= /regs_effect.
  Qed.
End jmp_jump_agree.

#[export] Hint Resolve jmp_jump_agree | 0 : regs_next_ok_db.

(** ** JCond

    The conditional jumps, which differ only by their comparison
    [jcond_test]. *)
Definition is_JCond (i : instr) (off arg1 arg2 : Z + RegName) :=
  i = Jeq off arg1 arg2 ∨
  i = Jne off arg1 arg2 ∨
  i = Jlt off arg1 arg2 ∨
  i = Jle off arg1 arg2.

(* Hints to automate proofs of is_JCond *)
Lemma is_JCond_Jeq off arg1 arg2 : is_JCond (Jeq off arg1 arg2) off arg1 arg2.
Proof. rewrite /is_JCond. naive_solver. Qed.
Lemma is_JCond_Jne off arg1 arg2 : is_JCond (Jne off arg1 arg2) off arg1 arg2.
Proof. rewrite /is_JCond. naive_solver. Qed.
Lemma is_JCond_Jlt off arg1 arg2 : is_JCond (Jlt off arg1 arg2) off arg1 arg2.
Proof. rewrite /is_JCond. naive_solver. Qed.
Lemma is_JCond_Jle off arg1 arg2 : is_JCond (Jle off arg1 arg2) off arg1 arg2.
Proof. rewrite /is_JCond. naive_solver. Qed.

#[export] Hint Resolve is_JCond_Jeq : core.
#[export] Hint Resolve is_JCond_Jne : core.
#[export] Hint Resolve is_JCond_Jlt : core.
#[export] Hint Resolve is_JCond_Jle : core.

(** The conditional jumps have no WP rule of their own: [iInstr] steps them
    with the register rules of [rules_regs.v] ([wp_regs_jump_0] to
    [wp_regs_jump_3]), from their register steps in closed form below. *)

Section jcond_jump_agree.
  Context `{MP : MachineParameters}.

  Lemma exec_opt_is_JCond i off arg1 arg2 p φ :
    is_JCond i off arg1 arg2 →
    exec_opt i p φ = exec_jcond (jcond_test i) off arg1 arg2 φ.
  Proof. intros HH. destruct_or! HH; subst i; reflexivity. Qed.

  (** A conditional jump whose test holds moves the PC by its offset. *)
  Lemma jcond_jump_agree_jmp i off ρ1 ρ2 p lpc regs n1 n2 imm :
    is_JCond i off ρ1 ρ2 →
    lz_of_argument regs ρ1 = Some n1 →
    lz_of_argument regs ρ2 = Some n2 →
    jcond_test i n1 n2 = true →
    lz_of_argument regs off = Some imm →
    regs_jump_agree i p lpc regs imm.
  Proof.
    intros Hi H1 H2 Ht Himm φ S _ Hc.
    rewrite (exec_opt_is_JCond _ _ _ _ _ _ Hi) /exec_jcond (regs_copy_z _ _ _ _ _ Hc H1)
      (regs_copy_z _ _ _ _ _ Hc H2) /= Ht (regs_copy_z _ _ _ _ _ Hc Himm) /=.
    by rewrite /regs_effect.
  Qed.

  (** A conditional jump whose test fails moves the PC to the next
      instruction. *)
  Lemma jcond_jump_agree_next i off ρ1 ρ2 p lpc regs n1 n2 :
    is_JCond i off ρ1 ρ2 →
    lz_of_argument regs ρ1 = Some n1 →
    lz_of_argument regs ρ2 = Some n2 →
    jcond_test i n1 n2 = false →
    regs_jump_agree i p lpc regs 1.
  Proof.
    intros Hi H1 H2 Ht φ S _ Hc.
    rewrite (exec_opt_is_JCond _ _ _ _ _ _ Hi) /exec_jcond (regs_copy_z _ _ _ _ _ Hc H1)
      (regs_copy_z _ _ _ _ _ Hc H2) /= Ht.
    done.
  Qed.

  (** The comparison of a register with zero, [Jne off r 0] and
      [Jeq off r 0]: on a register holding the integer [0], else on whether
      its word is zero ([nonZero]). *)
  Lemma jnez_jump_agree_next_int off r p lpc regs v :
    regs !!ₗ r = Some v →
    IsLInt v 0 →
    regs_jump_agree (Jne off (inr r) (inl 0%Z)) p lpc regs 1.
  Proof.
    intros Hr Hv.
    by eapply jcond_jump_agree_next; [ | eapply lz_of_argument_reg_int | apply lz_of_argument_z | ].
  Qed.

  Lemma jnez_jump_agree_next off r p lpc regs v :
    regs !!ₗ r = Some v →
    nonZero v.(lw) = false →
    regs_jump_agree (Jne off (inr r) (inl 0%Z)) p lpc regs 1.
  Proof.
    intros Hr Hz.
    by eapply jcond_jump_agree_next; [ | apply lz_of_argument_reg | apply lz_of_argument_z | ].
  Qed.

  Lemma jnez_jump_agree_jmp off r p lpc regs v imm :
    regs !!ₗ r = Some v →
    nonZero v.(lw) = true →
    lz_of_argument regs off = Some imm →
    regs_jump_agree (Jne off (inr r) (inl 0%Z)) p lpc regs imm.
  Proof.
    intros Hr Hnz Himm.
    by eapply jcond_jump_agree_jmp; [ | apply lz_of_argument_reg | apply lz_of_argument_z | | ].
  Qed.

  Lemma jeqz_jump_agree_jmp_int off r p lpc regs v imm :
    regs !!ₗ r = Some v →
    IsLInt v 0 →
    lz_of_argument regs off = Some imm →
    regs_jump_agree (Jeq off (inr r) (inl 0%Z)) p lpc regs imm.
  Proof.
    intros Hr Hv Himm.
    by eapply jcond_jump_agree_jmp;
      [ | eapply lz_of_argument_reg_int | apply lz_of_argument_z | | ].
  Qed.

  Lemma jeqz_jump_agree_jmp off r p lpc regs v imm :
    regs !!ₗ r = Some v →
    nonZero v.(lw) = false →
    lz_of_argument regs off = Some imm →
    regs_jump_agree (Jeq off (inr r) (inl 0%Z)) p lpc regs imm.
  Proof.
    intros Hr Hz Himm.
    by eapply jcond_jump_agree_jmp;
      [ | apply lz_of_argument_reg | apply lz_of_argument_z | cbn; by apply negb_false_iff | ].
  Qed.

  Lemma jeqz_jump_agree_next off r p lpc regs v :
    regs !!ₗ r = Some v →
    nonZero v.(lw) = true →
    regs_jump_agree (Jeq off (inr r) (inl 0%Z)) p lpc regs 1.
  Proof.
    intros Hr Hnz.
    by eapply jcond_jump_agree_next;
      [ | apply lz_of_argument_reg | apply lz_of_argument_z | cbn; by apply negb_true_iff ].
  Qed.
End jcond_jump_agree.

(* The comparison of a register with zero is stepped by its own lemmas
   below, the other forms by the general ones. The taken jump first: a test
   that fails is cheaper to reject on a known operand (zero) than on a
   symbolic one. *)
#[export] Hint Extern 0 (regs_jump_agree ?i _ _ _ _) =>
  lazymatch i with
  | Jne _ (inr _) (inl 0%Z) => fail
  | Jeq _ (inr _) (inl 0%Z) => fail
  | _ => simple eapply jcond_jump_agree_jmp
  end : regs_next_ok_db.
#[export] Hint Extern 1 (regs_jump_agree ?i _ _ _ _) =>
  lazymatch i with
  | Jne _ (inr _) (inl 0%Z) => fail
  | Jeq _ (inr _) (inl 0%Z) => fail
  | _ => simple eapply jcond_jump_agree_next
  end : regs_next_ok_db.
(* [Jne r 0] falls through on the integer [0] or a word known to be zero,
   else jumps; [Jeq r 0] the converse. The fact that the word is not zero is
   left to the client when the search does not decide it. *)
#[export] Hint Resolve jnez_jump_agree_next_int | 0 : regs_next_ok_db.
#[export] Hint Resolve jnez_jump_agree_next | 1 : regs_next_ok_db.
#[export] Hint Resolve jnez_jump_agree_jmp | 2 : regs_next_ok_db.
#[export] Hint Resolve jnez_jump_agree_jmp : regs_next_ok_lax_db.
#[export] Hint Resolve jeqz_jump_agree_jmp_int | 0 : regs_next_ok_db.
#[export] Hint Resolve jeqz_jump_agree_jmp | 1 : regs_next_ok_db.
#[export] Hint Resolve jeqz_jump_agree_next | 2 : regs_next_ok_db.
#[export] Hint Resolve jeqz_jump_agree_next : regs_next_ok_lax_db.

#[local] Open Scope capability_scope.

(** ** Subseg

    Subseg's rule with a witness, the rebase on an identifier, is in
    [rules_Subseg.v]. *)

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
