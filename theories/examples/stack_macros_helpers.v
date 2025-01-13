From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
Require Import Eqdep_dec List.
From cap_machine Require Import cap_lang region contiguous.

Section helpers.

  (* ---------------------------- Helper Lemmas --------------------------------------- *)

  Definition isCorrectPC_range p g b e a0 an :=
    ∀ ai, (a0 <= ai)%a ∧ (ai < an)%a → isCorrectPC (inr (p, g, b, e, ai)).

  Lemma isCorrectPC_inrange p g b (e a0 an a: Addr) :
    isCorrectPC_range p g b e a0 an →
    (a0 <= a < an)%Z →
    isCorrectPC (inr (p, g, b, e, a)).
  Proof.
    unfold isCorrectPC_range. move=> /(_ a) HH ?. apply HH. eauto.
  Qed.

  Lemma isCorrectPC_contiguous_range p g b e a0 an a l :
    isCorrectPC_range p g b e a0 an →
    contiguous_between l a0 an →
    a ∈ l →
    isCorrectPC (inr (p, g, b, e, a)).
  Proof.
    intros Hr Hc Hin.
    eapply isCorrectPC_inrange; eauto.
    eapply contiguous_between_middle_bounds'; eauto.
  Qed.

  Lemma isCorrectPC_range_perm p g b e a0 an :
    isCorrectPC_range p g b e a0 an →
    (a0 < an)%a →
    p = RX ∨ p = RWX ∨ p = RWLX.
  Proof.
    intros Hr H0n.
    assert (isCorrectPC (inr (p, g, b, e, a0))) as HH by (apply Hr; solve_addr).
    inversion HH; auto.
  Qed.

  Lemma isCorrectPC_range_npE p g b e a0 an :
    isCorrectPC_range p g b e a0 an →
    (a0 < an)%a →
    p ≠ E.
  Proof.
    intros HH1 HH2.
    destruct (isCorrectPC_range_perm _ _ _ _ _ _ HH1 HH2) as [?| [?|?] ];
      congruence.
  Qed.

  Lemma isCorrectPC_range_restrict p g b e a0 an a0' an' :
    isCorrectPC_range p g b e a0 an →
    (a0 <= a0')%a ∧ (an' <= an)%a →
    isCorrectPC_range p g b e a0' an'.
  Proof.
    intros HR [? ?] a' [? ?]. apply HR. solve_addr.
  Qed.

  Lemma isCorrectPC_range_monotone p g b e a0 an a' a'':
    isCorrectPC_range p g b e a0 an →
    (a0 <= a')%a → (a'' <= an)%a →
    isCorrectPC_range p g b e a' a''.
  Proof.
    intros. intros a1 [Ha'1 Ha'2]. apply H. solve_addr.
  Qed.

  Lemma isCorrectPC_range_split :
    ∀ (p : Perm) (g : Locality) (b e a0 an a_link : Addr),
      isCorrectPC_range p g b e a0 an
      → (a0 <= a_link)%a → (a_link <= an)%a →
      isCorrectPC_range p g b e a0 a_link ∧ isCorrectPC_range p g b e a_link an.
  Proof.
    intros * HCorr ??. split; eapply isCorrectPC_range_monotone; eauto; solve_addr.
  Qed.
  
  Lemma pc_range_not_E  pc_p pc_g pc_b pc_e a_first a_last a_tail:
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last →
    contiguous_between (a_first :: a_tail) a_first a_last →
    pc_p ≠ E.
  Proof.
    intros Hvpc Hcont.
    apply isCorrectPC_range_perm in Hvpc as [Heq | [Heq | Heq] ]; subst; auto.
    apply (contiguous_between_middle_bounds _ 0 a_first) in Hcont as [_ Hlt]; auto.
  Qed.

  Lemma pc_range_perm  pc_p pc_g pc_b pc_e a_first a_last a_tail:
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last →
    contiguous_between (a_first :: a_tail) a_first a_last →
    pc_p = RX ∨ pc_p = RWX ∨ pc_p = RWLX.
  Proof.
    intros Hvpc Hcont.
    apply isCorrectPC_range_perm in Hvpc as [Heq | [Heq | Heq] ]; subst; auto.
    apply (contiguous_between_middle_bounds _ 0 a_first) in Hcont as [_ Hlt]; auto.
  Qed.

  Lemma pc_range_nonO  pc_p pc_g pc_b pc_e a_first a_last a_tail:
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last →
    contiguous_between (a_first :: a_tail) a_first a_last →
    pc_p ≠ O.
  Proof.
    intros Hcorr Hcont.
    assert (pc_p = RX ∨ pc_p = RWX ∨ pc_p = RWLX) as [-> | [-> | ->] ] by (eapply pc_range_perm; eauto); auto.
  Qed.

  Lemma pc_range_readA  pc_p pc_g pc_b pc_e a_first a_last a_tail:
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last →
    contiguous_between (a_first :: a_tail) a_first a_last →
    readAllowed pc_p = true.
  Proof.
    intros Hcorr Hcont.
    assert (pc_p = RX ∨ pc_p = RWX ∨ pc_p = RWLX) as [-> | [-> | ->] ] by (eapply pc_range_perm; eauto); auto.
  Qed.

End helpers.

(* -------------------------------- LTACS ------------------------------------------- *)

  (* Destructing -parts of- sequences of addresses *)
  Ltac prep_addr_core list n :=
    match eval compute in n with
    | 0 => idtac
    | _ => destruct list;[done|]; prep_addr_core list (pred n) end.

  Ltac prep_addr_list list Hcont n :=
    let l := fresh "l" in
    destruct list as [| list l];[done|];
    apply contiguous_between_cons_inv_first in Hcont as Heq; subst list;
    prep_addr_core l (pred n).

  Ltac destruct_addr_list list :=
    let l := fresh "l" in
    destruct list as [| list l];[done|];
    repeat (destruct l;[done|]); destruct l; [|done].

  Ltac prep_addr_list_full list Hcont :=
    destruct_addr_list list;
    apply contiguous_between_cons_inv_first in Hcont as Heq; subst list.

  (* Tactics for single instruction spec application *)
  Ltac iPrologue_pre :=
    match goal with
    | Hlen : length ?a = ?n |- _ =>
      let a' := fresh "a" in
      destruct a as [| a' a]; inversion Hlen; simpl
    end.

  Ltac iPrologue prog :=
    let str_destr := constr:(("[Hi " ++ prog ++ "]")%string) in
    iDestruct prog as str_destr;
    iApply (wp_bind (fill [SeqCtx])).

  Ltac iEpilogue prog :=
    iNext; iIntros prog; iSimpl;
    iApply wp_pure_step_later;auto;iNext.

  Ltac iEpilogueLoad z prog :=
    iNext; iIntros (z) prog; iSimpl;
    iApply wp_pure_step_later;auto;iNext.

  Ltac iCorrectPC i j :=
    eapply isCorrectPC_contiguous_range with (a0 := i) (an := j); eauto; [];
    cbn; solve [ repeat constructor ].

  Ltac iContiguous_next Ha index :=
    apply contiguous_of_contiguous_between in Ha;
    generalize (contiguous_spec _ Ha index); auto.

  Lemma lst_lkup_head `{A : Type} hd (tail : list A) :
    (hd :: tail) !! 0 = Some hd.
  Proof. done. Qed.
  Lemma lst_lkup_cons `{A : Type} hd (tail : list A) i:
    (hd :: tail) !! (i + 1) = tail !! i.
  Proof. rewrite -plus_n_Sm Nat.add_0_r. rewrite -lookup_tail. simpl. done. Qed.
  Ltac iContiguous_next_a Ha :=
    apply contiguous_of_contiguous_between in Ha;
    eapply (contiguous_spec _ Ha);
    [repeat first [ by apply lst_lkup_head | erewrite lst_lkup_cons ] | done].
  Ltac iCorrectPC_a :=
    match goal with
    | _ : isCorrectPC_range _ _ _ _ ?i ?j |- _ =>
      eapply isCorrectPC_contiguous_range with (a0 := i) (an := j); eauto; [];
      cbn; solve [ repeat constructor ]
    end.

  Ltac contiguous_between_clean Hcont :=
    repeat apply contiguous_between_weak in Hcont.

  (* Tactics in case of CPS spec *)
  Ltac derive_length Hprog Hprog_len :=
    iDestruct (big_sepL2_length with Hprog) as %Hprog_len; simpl in Hprog_len.
  Ltac split_program Hprog Hcont a_link :=
    let str_destr := constr:(("(Hcode & " ++ Hprog ++ " & #Hcontig)")%string) in
    let l_code := fresh "l_code" in
    let l_rest := fresh "l_rest" in
    iDestruct (contiguous_between_program_split with Hprog) as (l_code l_rest a_link)  str_destr;[apply Hcont|]; clear Hcont.
  Ltac split_PC_range Hvpc Hcont_code Hcont a_linka :=
    let Hvpc_code := fresh "Hvpc_code" in
    let Hvpc_rest := fresh "Hvpc_rest" in
    edestruct isCorrectPC_range_split with (a_link := a_linka) as [Hvpc_code Hvpc_rest];[exact Hvpc| apply (contiguous_between_bounds _ _ _ Hcont_code) | apply (contiguous_between_bounds _ _ _ Hcont)| ..]; clear Hvpc; rename Hvpc_rest into Hvpc.

  Ltac iPrologue_multi Hprog Hcont Hvpc a_link :=
    split_program Hprog Hcont a_link;
    let Hcont_code := fresh "Hcont_code" in
    let Hlink := fresh "Hlink" in
    let Hre := fresh "Hre" in
    iDestruct "Hcontig" as %(Hcont_code & Hcont & Hre & Hlink);
    rewrite -> Hre in *; clear Hre;
    let Hlength_code := fresh "Hlength_code" in
    derive_length "Hcode" Hlength_code;
    rewrite Hlength_code in Hlink; clear Hlength_code;
    let Hlength := fresh "Hlength" in
    derive_length Hprog Hlength;
    split_PC_range Hvpc Hcont_code Hcont a_link.

  Tactic Notation "iEpilogue_multi" constr(Hprog) hyp_list(Hclear) :=
    let Hfresh := fresh "Hfresh" in
    assert (Hfresh : True) by auto;
    iNext; iIntros Hprog; clear Hfresh Hclear.

  Ltac frame_conjunction Hyp :=
    repeat (iDestruct Hyp as "[Hi Hprog_done]"; iFrame "Hi"); iFrame; auto.

  (* Adding and removing pointso from a map *)

 Ltac extract_pointsto_map regs Hmap rname Hrdom Hreg :=
    let rval := fresh "v"rname in
    let Hsome := fresh "Hsome" in
    let str_destr := constr:(("[" ++ Hreg ++ " " ++ Hmap ++ "]")%string) in
    assert (is_Some (regs !! rname)) as [rval Hsome] by (apply Hrdom; repeat constructor);
    iDestruct (big_sepM_delete _ _ rname with Hmap) as str_destr; first by simplify_map_eq.
  Ltac solve_insert_dom :=
  rewrite -(not_elem_of_dom (D := (gset RegName)));
  match goal with
  | [ H : dom (gset RegName) _ = _ |- _ ] =>
    rewrite H end;
  set_solver+.

  Ltac insert_pointsto_map_dom Hmap Hreg:=
    let str_destr := constr:(("[ $" ++ Hmap ++ " $" ++ Hreg ++ "]")%string) in
    iDestruct (big_sepM_insert with str_destr) as Hmap;
    [(repeat rewrite lookup_insert_ne //;[]); solve_insert_dom | ].

  Ltac insert_pointsto_map_del Hmap Hreg :=
    let str_destr := constr:(("[ $" ++ Hmap ++ " $" ++ Hreg ++ "]")%string) in
    iDestruct (big_sepM_insert with str_destr) as Hmap;
    [by simplify_map_eq | repeat (rewrite -delete_insert_ne //;[]); try rewrite insert_delete].

   Ltac insert_pointsto_map Hmap Hreg :=
     first [insert_pointsto_map_del Hmap Hreg | insert_pointsto_map_dom Hmap Hreg].
