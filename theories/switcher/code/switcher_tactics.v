From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte Require Export code_blocks.
From griotte Require Export switcher.

(** * Code of the switcher

    Shared definitions about the code of the switcher, used by the
    block-group lemmas of the call and return routines. *)

(** The offset of the first instruction of block [n] of the switcher, from
    [a_switcher_call]. *)
Notation switcher_block_offset := (code_block_offset assembled_switcher).

(** The offset of the label [s] of the switcher from [a_switcher_call], its
    first instruction (the label [.Lswitch_csp_check]). *)
Notation switcher_label_offset s :=
  (asm_label_offset switcher_asm ".Lswitch_csp_check" s).

(** The index of the block of the switcher that defines the label [s]. *)
Notation switcher_block s := (asm_block switcher_asm s).

(** The PC capability of the switcher at offset [off] of the code. *)
Notation switcher_pc off :=
  (WCap true XSRW_ Local b_switcher e_switcher (a_switcher_call ^+ off)%a) (only parsing).

(** The PC capability of the switcher at its label [s]. *)
Notation switcher_label_pc s := (switcher_pc (switcher_label_offset s)) (only parsing).

(** The code of the switcher. *)
Notation switcher_code := (codefrag_pers a_switcher_call switcher_instrs) (only parsing).

(** Unfold the code of the switcher in [h], in order to focus on its blocks. *)
Ltac switcher_unfold_code h :=
  iEval (rewrite /switcher_instrs /assembled_switcher) in h;
  repeat (iEval (cbn [fmap list_fmap]) in h);
  repeat (iEval (cbn [concat]) in h).

(** Rewrite, in the goal, the abstracted start addresses [x] of the opened
    blocks of the switcher with their equations [x = a_switcher_call ^+ off]
    (see [switcher_focus_label]). *)
Ltac switcher_unabstract :=
  repeat match goal with
  | H : ?x = (a_switcher_call ^+ _)%a |- context [?x] => is_var x; rewrite !H
  end.

(** Prove [a = a_switcher_call ^+ off], an equality between addresses of
    the code of the switcher. The abstracted start addresses of the opened
    blocks are first replaced with their definitions. The offsets are closed
    terms, so the proof first runs in a context with only the layout of the
    switcher ([switcher_addr_eq_cleared]), and falls back to the full
    context. *)
Ltac switcher_addr_eq_cleared :=
  switcher_unabstract;
  solve [ let Hsize := fresh "Hsize" in
          let Hcall := fresh "Hcall" in
          pose proof switcher_size as Hsize;
          pose proof switcher_call_entry_point as Hcall;
          clear - Hsize Hcall; offsets_compute; solve_addr ].

Ltac switcher_addr_eq :=
  first [ switcher_addr_eq_cleared | switcher_unabstract; offsets_compute; solve_addr ].

(** Change the address of the PC to [a'], in the PC hypothesis only. Does
    nothing when the PC is already at [a'], syntactically. *)
Ltac switcher_set_pc a' :=
  try (unfold lword_of_word);
  match goal with |- context [ environments.Esnoc _ ?i (PC ↦ₚ (WCap _ _ _ _ _ ?a) @@? _)%I ] =>
    tryif constr_eq a a' then idtac else
      (let Heq := fresh "Heq_pc" in
       assert (a = a') as Heq by switcher_addr_eq;
       iEval (rewrite Heq) in i; clear Heq)
  end.

(** Change the PC to [a_switcher_call ^+ off]. Does nothing when the PC is
    already this address, syntactically. *)
Ltac switcher_change_pc off := switcher_set_pc (a_switcher_call ^+ off)%a.

(** Change the PC to the label [s] of the switcher. *)
Ltac switcher_change_pc_label s := switcher_change_pc (switcher_label_offset s).

(** Focus on block [n] of the switcher, whose first address is
    [a_switcher_call ^+ switcher_block_offset n]. The PC is moved to this
    address, when possible. The address of the block is computed in a
    context with only the hypothesis of the focus, which is then
    cleared. *)
Tactic Notation "switcher_focus_block" constr(n) constr(h)
    "as" constr(hi) constr(hcont) :=
  let n := eval vm_compute in n in
  let a := fresh "a_block" in
  let Ha := fresh "Ha_block" in
  focus_block_nochangePC n h as a Ha hi hcont;
  assert (a = (a_switcher_call ^+ switcher_block_offset n)%a) as ->
    by (clear - Ha; cbn in Ha; offsets_compute; solve_addr);
  clear Ha;
  try switcher_change_pc (switcher_block_offset n).

(** Focus on the block of the switcher that starts with the label [s]. The
    first address of the block is abstracted into the variable [a], with the
    equation [Ha : a = a_switcher_call ^+ switcher_label_offset s]: the label
    terms slow the instruction tactics down. The PC is moved to [a] when the
    equality of the addresses holds in the layout of the switcher only. *)
Ltac switcher_focus_label_as s h hi hcont a Ha :=
  let n := eval vm_compute in (switcher_block s) in
  let Hb := fresh "Ha_block" in
  focus_block_nochangePC n h as a Hb hi hcont;
  assert (a = (a_switcher_call ^+ switcher_label_offset s)%a) as Ha
    by (clear - Hb; cbn in Hb; offsets_compute; solve_addr);
  clear Hb;
  try (unfold lword_of_word);
  first
    [ match goal with
      |- context [ environments.Esnoc _ ?i (PC ↦ₚ (WCap _ _ _ _ _ ?a') @@? _)%I ] =>
        constr_eq a' (a_switcher_call ^+ switcher_label_offset s)%a;
        iEval (rewrite -Ha) in i
      end
    | match goal with
      |- context [ environments.Esnoc _ ?i (PC ↦ₚ (WCap _ _ _ _ _ ?a') @@? _)%I ] =>
        let Heq := fresh "Heq_pc" in
        assert (a' = a) as Heq by switcher_addr_eq_cleared;
        iEval (rewrite Heq) in i; clear Heq
      end
    | idtac ].

Tactic Notation "switcher_focus_label" constr(s) constr(h)
    "as" constr(hi) constr(hcont) :=
  let a := fresh "a_block" in
  let Ha := fresh "Heq_block" in
  switcher_focus_label_as s h hi hcont a Ha.

(** Hide the proposition of the Iris hypothesis [h], such as a large
    postcondition, in the local definition [x], to speed up the proof mode.
    A later modality in front of the proposition is left visible: the
    instructions strip it, which would otherwise unfold [x]. *)
Ltac switcher_hide h x :=
  lazymatch goal with
  | |- context [ environments.Esnoc _ (INamed h) (▷ ?P)%I ] => set (x := P)
  | |- context [ environments.Esnoc _ (INamed h) ?P ] => set (x := P)
  end.

Tactic Notation "switcher_hide" constr(h) "as" ident(x) := switcher_hide h x.

Section Switcher_Code.
  Context `{MP: MachineParameters} {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}.

  Lemma switcher_SubBounds :
    SubBounds b_switcher e_switcher a_switcher_call
      (a_switcher_call ^+ length switcher_instrs)%a.
  Proof.
    pose proof switcher_size.
    pose proof switcher_call_entry_point.
    solve_addr.
  Qed.

  Lemma switcher_return_offset :
    a_switcher_return =
      (a_switcher_call ^+ switcher_label_offset "switcher_after_compartment_call")%a.
  Proof.
    pose proof switcher_return_entry_point as Hret.
    pose proof switcher_call_entry_point as Hcall.
    pose proof switcher_size as Hsize.
    cbn in Hret, Hcall, Hsize.
    offsets_compute.
    solve_addr.
  Qed.

  (** A return through the switcher's return sentry passes the checks of
      [Jalr cnull cra]. *)
  Lemma jalr_target_ok_switcher_return_sentry mie :
    jalr_target_ok cnull cra
      (WSentry (ret_kind mie) true XSRW_ Local b_switcher e_switcher a_switcher_return) = true.
  Proof. by destruct mie. Qed.

End Switcher_Code.

(** Open the block of the switcher that starts with the label [s], from the
    persistent code of the switcher [h]: [hi] is the persistent code of the
    block, at the variable [a] (fresh by default), with the facts that
    [iInstr] needs and the equation [Ha : a = a_switcher_call ^+
    switcher_label_offset s] for the exits, and the PC is moved to [a], when
    possible. [h] is cleared: the unfolded code of the whole switcher slows
    the proof mode down. *)
Ltac switcher_open_label_as s h hi a Ha :=
  let Hsub := fresh "Hsub_switcher" in
  pose proof switcher_SubBounds as Hsub;
  switcher_unfold_code h;
  switcher_focus_label_as s h hi "Hswitcher_cont" a Ha;
  clear Hsub;
  iClear h; iClear "Hswitcher_cont".

Tactic Notation "switcher_open_label" constr(s) constr(h) "as" constr(hi)
    ident(a) ident(Ha) :=
  switcher_open_label_as s h hi a Ha.

Tactic Notation "switcher_open_label" constr(s) constr(h) "as" constr(hi) :=
  let a := fresh "a_block" in
  let Ha := fresh "Heq_block" in
  switcher_open_label_as s h hi a Ha.

(** Rewrite the PC in [h], at the label [s] inside the opened block of the
    switcher that starts with the label [sb], to the address [a ^+ k] of the
    block, where [iInstr] looks for the instruction. *)
Ltac switcher_pc_in_block sb s h :=
  let k := eval vm_compute in (switcher_label_offset s - switcher_label_offset sb)%Z in
  match goal with H : ?a = (a_switcher_call ^+ switcher_label_offset sb)%a |- _ =>
    is_var a;
    let Heq := fresh "Heq_pc" in
    assert ((a_switcher_call ^+ switcher_label_offset s)%a = (a ^+ k)%a) as Heq
      by switcher_addr_eq;
    iEval (rewrite Heq) in h; clear Heq
  end.

(** The offset of the label [s] from the label [sb] of the switcher,
    computed. *)
Ltac switcher_label_index sb s :=
  eval vm_compute in (switcher_label_offset s - switcher_label_offset sb)%Z.

(** Move the PC to the label [s] inside the opened block of the switcher
    that starts with the label [sb], written [a ^+ k] from the start [a] of
    the block, where [iInstr] looks for the instruction. The current address
    of the PC must be equal to [a ^+ k] without the labels, for example the
    end of a macro: the labels are not unfolded. *)
Ltac switcher_set_pc_in_block sb s :=
  let k := switcher_label_index sb s in
  match goal with H : ?a = (a_switcher_call ^+ switcher_label_offset sb)%a |- _ =>
    is_var a;
    try (unfold lword_of_word);
    match goal with
    |- context [ environments.Esnoc _ ?i (PC ↦ₚ (WCap _ _ _ _ _ ?a') @@? _)%I ] =>
      let Heq := fresh "Heq_pc" in
      assert (a' = (a ^+ k)%a) as Heq by (clear H; cbn; solve_addr);
      iEval (rewrite Heq) in i; clear Heq
    end
  end.

(** The address of the label [s] of the switcher, written [a ^+ k] from the
    start [a] of the opened block that starts with the label [sb]: the
    equation [Heq : a ^+ k = a_switcher_call ^+ switcher_label_offset s],
    with [k] computed from the labels, for an exit of the block to [s]. *)
Ltac switcher_label_in_block sb s Heq :=
  let k := switcher_label_index sb s in
  match goal with H : ?a = (a_switcher_call ^+ switcher_label_offset sb)%a |- _ =>
    is_var a;
    assert ((a ^+ k)%a = (a_switcher_call ^+ switcher_label_offset s)%a) as Heq
      by switcher_addr_eq
  end.

Tactic Notation "switcher_label_in_block" constr(sb) constr(s) "as" ident(Heq) :=
  switcher_label_in_block sb s Heq.

(** The same address, as the target of a jump from the opened block:
    [Hsome : (a + k)%a = Some (a_switcher_call ^+ switcher_label_offset s)]. *)
Ltac switcher_jump_in_block sb s Hsome :=
  let k := switcher_label_index sb s in
  match goal with H : ?a = (a_switcher_call ^+ switcher_label_offset sb)%a |- _ =>
    is_var a;
    assert ((a + k)%a = Some (a_switcher_call ^+ switcher_label_offset s)%a) as Hsome
      by switcher_addr_eq
  end.

Tactic Notation "switcher_jump_in_block" constr(sb) constr(s) "as" ident(Hsome) :=
  switcher_jump_in_block sb s Hsome.

(** The offset [off] of an address [a = a_switcher_call ^+ off] of the code
    of the switcher, written [a_switcher_call ^+ off], [a' ^+ k], or an
    abstracted start address of an opened block. *)
Ltac switcher_addr_offset a :=
  lazymatch a with
  | (a_switcher_call ^+ ?off)%a => off
  | (?a' ^+ ?k)%a => let off := switcher_addr_offset a' in constr:((off + k)%Z)
  | ?x => match goal with H : x = (a_switcher_call ^+ ?off)%a |- _ => off end
  end.

(** Rewrite the addresses of the capabilities of the switcher in the goal,
    such as the address [a ^+ k] of a faulting instruction inside the
    opened block at [a], to [a_switcher_call ^+ off], to state them with
    [switcher_pc]. The rewriting is done in the conclusion when possible,
    and in the whole goal otherwise. *)
Ltac switcher_merge_pc :=
  try (unfold lword_of_word);
  repeat match goal with
  | |- context [ WCap _ _ _ b_switcher e_switcher ?a ] =>
      lazymatch a with (a_switcher_call ^+ _)%a => fail | _ => idtac end;
      let off := switcher_addr_offset a in
      let Heq := fresh "Heq_pc" in
      assert (a = (a_switcher_call ^+ off)%a) as Heq by switcher_addr_eq;
      first [ iEval (rewrite Heq) | rewrite Heq ]; clear Heq
  end.
