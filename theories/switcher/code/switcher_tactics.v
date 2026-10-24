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

(** Prove [a = a_switcher_call ^+ off], an equality between addresses of
    the code of the switcher. The offsets are closed terms, so the proof
    first runs in a context with only the layout of the switcher, and falls
    back to the full context. *)
Ltac switcher_addr_eq :=
  first
    [ solve [ let Hsize := fresh "Hsize" in
              let Hcall := fresh "Hcall" in
              pose proof switcher_size as Hsize;
              pose proof switcher_call_entry_point as Hcall;
              clear - Hsize Hcall; offsets_compute; solve_addr ]
    | offsets_compute; solve_addr ].

(** Change the PC to [a_switcher_call ^+ off]. Does nothing when the PC is
    already this address, syntactically. *)
Ltac switcher_change_pc off :=
  try (unfold lword_of_word);
  match goal with |- context [ environments.Esnoc _ _ (PC ↦ₚ (WCap _ _ _ _ _ ?a) @@? _)%I ] =>
    let a' := constr:((a_switcher_call ^+ off)%a) in
    tryif constr_eq a a' then idtac else
      (let Heq := fresh "Heq_pc" in
       assert (a = a') as Heq by switcher_addr_eq;
       rewrite Heq; clear Heq)
  end.

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
    first address of the block is [a_switcher_call ^+ switcher_label_offset s],
    and the PC is moved to it, when possible. *)
Tactic Notation "switcher_focus_label" constr(s) constr(h)
    "as" constr(hi) constr(hcont) :=
  let n := eval vm_compute in (switcher_block s) in
  let a := fresh "a_block" in
  let Ha := fresh "Ha_block" in
  focus_block_nochangePC n h as a Ha hi hcont;
  assert (a = (a_switcher_call ^+ switcher_label_offset s)%a) as ->
    by (clear - Ha; cbn in Ha; offsets_compute; solve_addr);
  clear Ha;
  try switcher_change_pc_label s.

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
    block, at [a_switcher_call ^+ switcher_label_offset s], with the facts
    that [iInstr] needs, and the PC is moved to it, when possible. [h] is
    cleared: the unfolded code of the whole switcher slows the proof mode
    down. *)
Tactic Notation "switcher_open_label" constr(s) constr(h) "as" constr(hi) :=
  let Hsub := fresh "Hsub_switcher" in
  pose proof switcher_SubBounds as Hsub;
  switcher_unfold_code h;
  switcher_focus_label s h as hi "Hswitcher_cont";
  clear Hsub;
  iClear h; iClear "Hswitcher_cont".

(** Solve [(a + z)%a = Some ?a'], the target of a jump of the switcher to
    its label [s]: [?a'] is the address of [s]. *)
Ltac switcher_jump_label s :=
  transitivity (Some (a_switcher_call ^+ switcher_label_offset s)%a);
  [switcher_addr_eq | reflexivity].

(** Rewrite the addresses [a_switcher_call ^+ off ^+ k] of the goal to
    [a_switcher_call ^+ (off + k)], for instance the address of a faulting
    instruction inside a block, to state it with [switcher_pc]. *)
Ltac switcher_merge_pc :=
  repeat match goal with |- context [((a_switcher_call ^+ ?off) ^+ ?k)%a] =>
    rewrite (_ : ((a_switcher_call ^+ off) ^+ k)%a = (a_switcher_call ^+ (off + k))%a);
      [| switcher_addr_eq]
  end.
