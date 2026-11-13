From iris.proofmode Require Import coq_tactics.
From iris.bi Require Import bi.
Import bi.
From griotte Require Import rules rules_regs rules_mem_access solve_pure machine_instructions.
From Ltac2 Require Import Ltac2 Option.
Set Default Proof Mode "Classic".

(* Normalize proved register aliases before choosing an explicit-resource rule.
   Prefer cnull as a representative and never decide an unknown equality. *)
Ltac instr_normalize_register_aliases :=
  repeat match goal with
  | H : @eq RegName ?r1 ?r2 |- _ =>
      tryif is_var r1 then
        lazymatch r2 with
        | context [r1] => fail
        | _ => progress rewrite -> H in *
        end
      else (
        is_var r2;
        lazymatch r1 with
        | context [r2] => fail
        | _ => progress rewrite <- H in *
        end)
  end.

(* Operand aliases share one owned entry. [cnull] needs no register
   resource. *)
(* Distinct full-ownership hypotheses already imply distinct registers. The
   explicit-resource rule proves this fact internally when consuming them. *)
Ltac instr_distinct_register_resources r1 r2 :=
  match goal with
  | |- context [ Esnoc _ ?h1 (?rr1 ↦ᵣ _)%I ] =>
    let checked := constr:(ltac:(constr_eq r1 rr1; exact I) : True) in
    match goal with
    | |- context [ Esnoc _ ?h2 (?rr2 ↦ᵣ _)%I ] =>
      let checked := constr:(ltac:(constr_eq r2 rr2; exact I) : True) in
      let checked := constr:(ltac:(tryif constr_eq h1 h2 then fail else exact I) : True) in
      constr:(false)
    end
  end.

(* Use proved aliases or distinct ownership; never instantiate register
   operands or split symbolic alias cases to choose a rule. *)
Ltac instr_same_register r1 r2 :=
  let r1' := eval cbv in r1 in
  let r2' := eval cbv in r2 in
  let checked := constr:(ltac:(without_evars r1'; without_evars r2'; exact I) : True) in
  match goal with
  | _ => let H := constr:(ltac:(constr_eq r1 r2; reflexivity) : r1 = r2) in constr:(true)
  | _ => let eq := eval vm_compute in (bool_decide (r1 = r2)) in
         lazymatch eq with true => constr:(true) | false => constr:(false) end
  | _ => let H := constr:(ltac:(first [congruence | solve_pure]) : r1 = r2) in constr:(true)
  | _ => let H := constr:(ltac:(first [congruence | solve_pure]) : r1 ≠ r2) in constr:(false)
  | _ => instr_distinct_register_resources r1 r2
  end.

Ltac instr_registers_contain regs r :=
  lazymatch regs with
  | (?rr, ?ww) :: ?tail =>
    let eq := instr_same_register rr r in
    lazymatch eq with true => constr:(true) | false => instr_registers_contain tail r end
  | _ => constr:(false)
  end.

(* PC has its own resource in every failure rule. Collect only the remaining
   distinct operands other than [cnull], binding each to its owned word
   before applying a rule. *)
Ltac instr_register_words rs :=
  lazymatch rs with
  | nil => constr:(@nil (RegName * LWord))
  | cnull :: ?rs => instr_register_words rs
  | ?r :: ?rs =>
    let tail := instr_register_words rs in
    let found := instr_registers_contain tail r in
    lazymatch found with
    | true => tail
    | false => match goal with
      | |- context [ Esnoc _ _ (?rr ↦ᵣ ?w)%I ] =>
        let eq := instr_same_register rr r in
        lazymatch eq with
        | true => constr:((rr, w) :: tail)
        end
      end
    end
  end.

Ltac instr_argument_registers arg rest :=
  let arg := eval cbv [regn cst] in arg in
  lazymatch arg with
  | inl _ => rest
  | inr ?r => constr:(r :: rest)
  end.

Ltac instr_failure_registers instr :=
  let instr := eval cbv [regn cst] in instr in
  let rs := lazymatch instr with
    | Lea ?dst ?src ?off => instr_argument_registers off constr:([dst; src])
    | SetA ?dst ?src ?addr => instr_argument_registers addr constr:([dst; src])
    | Restrict ?dst ?src ?perm => instr_argument_registers perm constr:([dst; src])
    | Subseg ?dst ?src ?s1 ?s2 =>
      let rest := instr_argument_registers s2 constr:([dst; src]) in
      instr_argument_registers s1 rest
    | Seal ?dst ?s1 ?s2 => constr:([dst; s1; s2])
    | UnSeal ?dst ?s1 ?s2 => constr:([dst; s1; s2])
    | CLoad ?dst ?src _ => constr:([dst; src])
    | Store ?dst ?src _ => instr_argument_registers src constr:([dst])
    | _ => eval vm_compute in (elements (regs_of instr))
    end in
  instr_register_words rs.

Ltac solve_instr_failure :=
  intros;
  (* A physical register is a copy of its logical word, its tag kept or
     cleared: consider both cases. *)
  repeat match goal with
  | H : _ !! _ = Some (and_tag ?s _) |- _ =>
      is_var s; destruct s; rewrite ?and_tag_true ?and_tag_false in H
  end;
  cbn [lw lword_of_word] in *;
  rewrite /exec /exec_opt /= /word_of_argument /z_of_argument /lookup_reg;
  rewrite ?finz_add_0 /=;
  repeat first [
    progress (rewrite finz_add_0 /=)
  | match goal with
    | H : ?lhs = ?rhs |- context [?lhs] => progress (rewrite H; cbn)
    end ];
  repeat match goal with
  | sb : Sealable |- context [clear_tag_sealable (unseal_sb _ ?x)] =>
      constr_eq sb x; destruct sb; cbn
  | sb : Sealable |- context [clear_tag_sealable ?x] =>
      constr_eq sb x; destruct sb; cbn
  end;
  try (rewrite /nextPC /advancePC /update_reg /reg /sreg /mem /= /insert_reg;
       rewrite ?lookup_insert /=; simplify_map_eq; rewrite ?lookup_insert /=);
  repeat first [
    progress (rewrite finz_add_0 /=)
  | match goal with
    | H : ?lhs = ?rhs |- context [?lhs] => progress (rewrite H; cbn)
    end ];
  try done;
  try solve_pure.

(* Instruction rules may introduce an output address evar. Choosing the
   canonical wrapped sum instantiates that output, never an instruction input. *)
Ltac instr_auto_z_literal z :=
  lazymatch z with
  | Z0 => constr:(I)
  | Zpos _ => constr:(I)
  | Zneg _ => constr:(I)
  end.

Ltac instr_auto_add_offsets x y :=
  match goal with
  | _ =>
      let _ := instr_auto_z_literal x in
      let _ := instr_auto_z_literal y in
      eval vm_compute in (x + y)%Z
  | _ =>
      lazymatch x with
      | (?prefix + ?last)%Z =>
          let _ := instr_auto_z_literal last in
          let _ := instr_auto_z_literal y in
          let sum := eval vm_compute in (last + y)%Z in
          lazymatch sum with
          | Z0 => prefix
          | _ => constr:((prefix + sum)%Z)
          end
      end
  | _ => constr:((x + y)%Z)
  end.

(* Subseg endpoints are integers obtained from addresses and arithmetic.
   Recover the base and offset, then reuse increment-result inference below. *)
Ltac instr_auto_address_offset bound n :=
  lazymatch n with
  | @finz.to_z bound ?a => constr:((a, 0%Z))
  | (?x + ?y)%Z =>
      let parts := instr_auto_address_offset bound x in
      lazymatch parts with (?a, ?off) =>
        let total := instr_auto_add_offsets off y in constr:((a, total))
      end
  | (?x - ?y)%Z =>
      let parts := instr_auto_address_offset bound x in
      lazymatch parts with (?a, ?off) =>
        let total := instr_auto_add_offsets off constr:((- y)%Z) in constr:((a, total))
      end
  end.

(* Keep the arithmetic context small on the fast path. In particular, hidden
   code continuations contain many irrelevant finz subterms. This is only a
   heuristic: the caller retries with the original context if it cannot close
   the goal. Do not change the general-purpose [solve_addr] tactic. *)
Ltac instr_auto_arithmetic_fact P :=
  lazymatch P with
  | InCtx ?P => instr_auto_arithmetic_fact P
  | ?P /\ ?Q => instr_auto_arithmetic_fact P; instr_auto_arithmetic_fact Q
  | ~ ?P => instr_auto_arithmetic_fact P
  | @eq Z _ _ => idtac
  | @eq nat _ _ => idtac
  | @eq (finz _) _ _ => idtac
  | @eq (option (finz _)) _ _ => idtac
  | Z.le _ _ => idtac
  | Z.lt _ _ => idtac
  | Nat.le _ _ => idtac
  | Nat.lt _ _ => idtac
  | SubBounds _ _ _ _ => idtac
  | ContiguousRegion _ _ => idtac
  | IncrFinZ _ _ _ => idtac
  | withinBounds _ _ _ = _ => idtac
  | isWithin _ _ _ _ = _ => idtac
  end.

Ltac2 instr_auto_arithmetic_context () :=
  List.iter (fun (h, _, _) =>
    ltac1:(h |-
      let P := type of h in
      first [instr_auto_arithmetic_fact P | clear h | idtac])
      (Ltac1.of_ident h)) (List.rev (Control.hyps ())).

(* The local definitions of addresses are inlined first: [solve_addr] keeps
   only the bounds of a local definition, not its body. *)
Ltac instr_auto_solve_addr :=
  repeat match goal with x := _ : finz _ |- _ => subst x end;
  first [solve [ltac2:(instr_auto_arithmetic_context ()); solve_addr]
        | solve_addr].

Ltac instr_auto_solve_addr_result :=
  lazymatch goal with
  | |- @finz.of_z ?bound (@finz.to_z ?bound ?a) = Some ?result =>
      is_evar result; unify result a; instr_auto_solve_addr
  | |- @finz.of_z ?bound ?n = Some ?result =>
      is_evar result; without_evars n;
      let parts := instr_auto_address_offset bound n in
      lazymatch parts with (?a, ?off) =>
        let Hincr := fresh "Hincr" in
        assert (@finz.incr bound a off = Some result) as Hincr by
          instr_auto_solve_addr_result;
        instr_auto_solve_addr
      end
  | |- (?a + ?off)%a = Some ?result =>
      is_evar result;
      first [
        lazymatch off with
        | ((@finz.to_z MemNum ?target) - (@finz.to_z MemNum a))%Z =>
            unify result target; instr_auto_solve_addr
        end
      |
        match goal with
        | H : (?base + ?prior)%a = Some a |- _ =>
            let total := instr_auto_add_offsets prior off in
            unify result (base ^+ total); instr_auto_solve_addr
        end
      | lazymatch a with
        | (?base ^+ ?prior) =>
            let total := instr_auto_add_offsets prior off in
            unify result (base ^+ total); instr_auto_solve_addr
        | _ => unify result (a ^+ off); instr_auto_solve_addr
        end ]
  | |- (?a + ?off)%ot = Some ?result =>
      is_evar result;
      first [
        lazymatch off with
        | ((@finz.to_z ONum ?target) - (@finz.to_z ONum a))%Z =>
            unify result target; instr_auto_solve_addr
        end
      |
        match goal with
        | H : (?base + ?prior)%ot = Some a |- _ =>
            let total := instr_auto_add_offsets prior off in
            unify result (base ^+ total); instr_auto_solve_addr
        end
      | lazymatch a with
        | (?base ^+ ?prior) =>
            let total := instr_auto_add_offsets prior off in
            unify result (base ^+ total); instr_auto_solve_addr
        | _ => unify result (a ^+ off); instr_auto_solve_addr
        end ]
  end.

Ltac instr_auto_solve_within_bounds :=
  rewrite /withinBounds;
  first [ltac2:(solve_pure_iinstr ()) | instr_auto_solve_addr |
    (apply andb_false_iff;
      first [left; instr_auto_solve_addr | right; instr_auto_solve_addr]) |
    (apply andb_true_iff; split; instr_auto_solve_addr)].

(* A known rejected factor suffices even when other authorization checks
   remain symbolic. This constructs a proof without splitting input values. *)
Ltac instr_auto_solve_bool :=
  first [assumption | reflexivity |
    lazymatch goal with
    | |- _ && _ = false =>
        apply andb_false_iff;
        first [left; instr_auto_solve_bool | right; instr_auto_solve_bool]
    | |- _ && _ = true =>
        apply andb_true_iff; split; instr_auto_solve_bool
    end].

(* A bounded access into a region disjoint from shadow memory is nonshadow.
   Backtrack over region hypotheses until their bounds cover the address. *)
Ltac instr_auto_solve_nonshadow_general :=
  match goal with
  | H : disjoint_from_shadow ?b ?e |- is_shadow_address ?a = false =>
      apply (disjoint_from_shadow_not_in b e a H);
      solve [assumption | instr_auto_solve_within_bounds]
  | H : disjoint_from_mmio ?b ?e |- is_shadow_address ?a = false =>
      apply (disjoint_from_shadow_not_in b e a (disjoint_from_mmio_shadow b e H));
      solve [assumption | instr_auto_solve_within_bounds]
  end.

Ltac instr_auto_addr_base a :=
  lazymatch a with
  | (?b ^+ _) => instr_auto_addr_base b
  | _ => a
  end.

Ltac instr_auto_solve_nonshadow :=
  first [solve [
    lazymatch goal with
    | |- is_shadow_address ?a = false =>
      let base := instr_auto_addr_base a in
      match goal with
      | H : disjoint_from_shadow ?b ?e |- _ =>
        constr_eq base b;
        apply (disjoint_from_shadow_not_in b e a H);
        solve [assumption | instr_auto_solve_within_bounds]
      | H : disjoint_from_mmio ?b ?e |- _ =>
        constr_eq base b;
        apply (disjoint_from_shadow_not_in b e a (disjoint_from_mmio_shadow b e H));
        solve [assumption | instr_auto_solve_within_bounds]
      end
    end]
  | instr_auto_solve_nonshadow_general].

Ltac instr_auto_solve_premise :=
  first [solve [instr_auto_solve_bool] |
    solve [lazymatch goal with
    | |- is_shadow_address _ = false => instr_auto_solve_nonshadow
    | |- withinBounds _ _ _ = _ => instr_auto_solve_within_bounds
    end] |
    ltac2:(solve_pure_iinstr ()) | instr_auto_solve_bool | solve_addr |
    instr_auto_solve_within_bounds | instr_auto_solve_nonshadow |
    (rewrite le_addr_withinBounds; solve_addr) |
    (split; first [ltac2:(solve_pure_iinstr ()) | solve_addr |
                   instr_auto_solve_within_bounds]) |
    (injection; intros; lia) | congruence |
    (rewrite ?decode_encode_permPair_inv ?decode_encode_SealPermPair_inv; done) |
    by simplify_map_eq].

Ltac instr_auto_simplify_exec :=
  repeat match goal with
  | |- context [if ?condition then _ else _] =>
      first [
        let H := constr:(ltac:(instr_auto_solve_premise) : condition = true) in
        rewrite H /=
      | let H := constr:(ltac:(instr_auto_solve_premise) : condition = false) in
        rewrite H /= ]
  end.

Ltac instr_auto_solve_success :=
  solve [instr_auto_solve_addr_result | instr_auto_solve_premise |
         apply addr_add_0].

Ltac instr_auto_solve_invalidation :=
  solve [instr_auto_solve_addr_result | instr_auto_solve_premise |
         reflexivity | apply addr_add_0].

Ltac instr_auto_solve_failure :=
  solve [solve_instr_failure; instr_auto_simplify_exec;
           try instr_auto_solve_premise |
         instr_auto_solve_addr_result | instr_auto_solve_premise].

(* Explicit invalidation leaves semantic premises to the caller, except that
   Subseg conversion-overflow rules require evidence before selection. *)
Ltac instr_guard_invalidation_premise :=
  lazymatch goal with
  | |- z_to_addr ?n1 = None ∨ z_to_addr ?n2 = None =>
      without_evars n1; without_evars n2;
      solve [solve_pure | left; solve_pure | right; solve_pure]
  | |- z_to_otype ?n1 = None ∨ z_to_otype ?n2 = None =>
      without_evars n1; without_evars n2;
      solve [solve_pure | left; solve_pure | right; solve_pure]
  | _ => idtac
  end.

(** * The register steps in closed form: premises and search

    The premises of an instruction's register step in closed form
    ([rules_regs.v], database [regs_next_ok_db]) on the literal register map
    of a k-ary rule, solved during the search for that lemma. A case of a
    family whose premise fails gives way to the next case. The settings are
    global: the database is searched in client proofs, which do not import
    this file. *)

(* A lookup in a literal register map, by [lookup_insert_eq] and
   [lookup_insert_ne] only: no [simplify_map_eq], slow in large contexts. *)
Ltac regs_lookup :=
  first [ apply lookup_insert_eq
        | apply lookup_singleton_eq
        | rewrite lookup_insert_ne;
          [ regs_lookup | first [assumption | by apply not_eq_sym] ] ].

(* A premise with a constructor pattern ([Some (WCap …)]) is checked
   syntactically against the head of the word found, so that a symbolic word
   is neither unfolded nor matched against a constructor. A word that
   computes to a constructor ([load_word p w] on a literal [w]) is checked on
   its head normal form. *)
Ltac lword_head_matches a b :=
  lazymatch a with
  | WInt _ => lazymatch b with WInt _ => idtac end
  | WSealable (SCap _ _ _ _ _ _) => lazymatch b with WSealable (SCap _ _ _ _ _ _) => idtac end
  | WSealable (SSealRange _ _ _ _ _ _) =>
      lazymatch b with WSealable (SSealRange _ _ _ _ _ _) => idtac end
  | WSentry _ _ _ _ _ _ _ => lazymatch b with WSentry _ _ _ _ _ _ _ => idtac end
  | WSealed _ _ => lazymatch b with WSealed _ _ => idtac end
  | _ => idtac
  end.

Ltac lword_shape_matches v w :=
  let a := eval cbn [lw] in v.(lw) in
  let b := eval cbn [lw] in w.(lw) in
  first [ lword_head_matches a b
        | let b' := eval hnf in b in lword_head_matches a b' ].

(* The owned word of an operand, read in the literal map. *)
Ltac regs_next_ok_lookup :=
  lazymatch goal with
  | |- ?regs !!ₗ ?r = Some ?v =>
      first
        [ apply llookup_reg_cnull
        | let Hr := fresh "Hr" in
          eassert (regs !!ₗ r = Some _) as Hr
            by (rewrite ?llookup_reg_not_cnull //; regs_lookup);
          lazymatch type of Hr with _ = Some ?w =>
            tryif is_evar v then idtac else lword_shape_matches v w
          end;
          exact Hr ]
  end.

#[global] Hint Extern 0 (_ !!ₗ _ = Some _) => regs_next_ok_lookup : regs_next_ok_db.

(* An address result: from the context, or by the [IncrFinZ] instances of
   [solve_pure], which the search also uses. Otherwise the lemma does not
   apply; the lax search ([solve_regs_next_ok_lax]) or [iInstr "H" using s]
   leaves the fact as a side goal. *)
#[global] Hint Extern 0 ((_ + _)%a = Some _) => eassumption : regs_next_ok_db.
#[global] Hint Extern 0 ((_ + _)%ot = Some _) => eassumption : regs_next_ok_db.
#[global] Hint Extern 0 (z_to_addr _ = Some _) => eassumption : regs_next_ok_db.
#[global] Hint Extern 0 ((_ + _)%a = None) => eassumption : regs_next_ok_db.
#[global] Hint Extern 0 ((_ + _)%ot = None) => eassumption : regs_next_ok_db.
#[global] Hint Extern 0 (z_to_addr _ = None) => eassumption : regs_next_ok_db.
#[global] Hint Extern 0 (z_to_otype _ = Some _) => eassumption : regs_next_ok_db.
#[global] Hint Extern 0 (z_to_otype _ = None) => eassumption : regs_next_ok_db.

(* An untagged word: a literal, or a fact of the context. *)
#[global] Hint Extern 1 (get_tag _ = false) =>
  first [ reflexivity
        | match goal with H : InCtx (get_tag _ = false) |- _ => exact H end ]
  : regs_next_ok_db.

(* Whether a word is zero: by computation, or a fact of the context. *)
#[global] Hint Extern 1 (nonZero _ = _) =>
  first [ reflexivity
        | match goal with H : InCtx (nonZero _ = _) |- _ => exact H end ]
  : regs_next_ok_db.

(* An integer, a sentry or a sealed word: a literal, or a fact of the
   context. *)
#[global] Hint Extern 1 (is_mutable_range _ = false) =>
  first [ reflexivity | eassumption ] : regs_next_ok_db.

(* Subseg: the premise of its tag as a value, on a literal register map, and
   endpoints out of range on literals. *)
#[global] Hint Extern 1 (subseg_root_free _ _ _ _) =>
  unfreeze_hyps; solve_subseg_root_free : regs_next_ok_db.
#[global] Hint Extern 1 (z_to_addr _ = None ∨ z_to_addr _ = None) =>
  first [ left; reflexivity | right; reflexivity ] : regs_next_ok_db.
#[global] Hint Extern 1 (z_to_otype _ = None ∨ z_to_otype _ = None) =>
  first [ left; reflexivity | right; reflexivity ] : regs_next_ok_db.
(* In the lax search, as in the strict one, an endpoint of Subseg is computed
   when its integer is an address ([solve_pure]); otherwise the fact is
   postponed. The heap premise is searched for even with unknown endpoints: a
   fact of the context then fixes them, and their facts are checked once they
   are known. A search that fails leaves the premise as a side goal. *)
#[global] Hint Extern 0 (z_to_addr _ = Some _) =>
  solve [typeclasses eauto 8 with regs_next_ok_db solve_pure typeclass_instances]
  : regs_next_ok_lax_db.
#[global] Hint Extern 0 (z_to_otype _ = Some _) =>
  solve [typeclasses eauto 8 with regs_next_ok_db solve_pure typeclass_instances]
  : regs_next_ok_lax_db.
#[global] Hint Extern 0 =>
  lazymatch goal with
  | |- (_ = None → _ → is_heap_address _ = false) =>
      solve [ intros [=]
            | match goal with H : InCtx (_ = None → _ → is_heap_address _ = false) |- _ =>
                exact H end
            | typeclasses eauto 8 with regs_next_ok_db solve_pure typeclass_instances ]
  end : regs_next_ok_lax_db.

(* The comparison of two known operands: from a hypothesis (also on the words,
   by [congruence]), or by [lia], or by [solve_addr] when addresses occur. *)
Ltac jcond_test_arith :=
  lazymatch goal with
  | |- Z.eqb _ _ = true => apply Z.eqb_eq
  | |- Z.eqb _ _ = false => apply Z.eqb_neq
  | |- Datatypes.negb (Z.eqb _ _) = true => apply negb_true_iff, Z.eqb_neq
  | |- Datatypes.negb (Z.eqb _ _) = false => apply negb_false_iff, Z.eqb_eq
  | |- Z.ltb _ _ = true => apply Z.ltb_lt
  | |- Z.ltb _ _ = false => apply Z.ltb_ge
  | |- Z.leb _ _ = true => apply Z.leb_le
  | |- Z.leb _ _ = false => apply Z.leb_gt
  end;
  first
    [ assumption
    | symmetry; assumption
    | apply not_eq_sym; assumption
    | congruence
    | lia
    | lazymatch goal with |- context [finz.to_z _] => solve_addr end ].

(* The test of a conditional jump on known operands: by computation, from a
   hypothesis (up to conversion), also as [nonZero w], or on the comparison
   once the addresses of literal words are computed. An integer word is read
   as its integer ([lz_of_argument_reg_int]): its address form is the same
   test, rejected at once. *)
Ltac solve_jcond_test :=
  lazymatch goal with
  | |- ?g => tryif has_evar g then fail "jcond_test: unknown operands" else idtac
  end;
  tryif (match goal with
         | |- context [get_a (lw ?v)] =>
             let w := eval cbn [lw] in (lw v) in lazymatch w with WInt _ => idtac end
         end)
  then fail "jcond_test: an integer word is read as an integer"
  else idtac;
  cbn [jcond_test];
  first
    [ reflexivity
    | assumption
    | lazymatch goal with
      | |- Datatypes.negb (Z.eqb (get_a ?w) 0) = ?b => change (nonZero w = b); assumption
      | |- Z.eqb (get_a ?w) 0 = true =>
          apply negb_false_iff; change (nonZero w = false); assumption
      | |- Z.eqb (get_a ?w) 0 = false =>
          apply negb_true_iff; change (nonZero w = true); assumption
      end
    | cbn [get_a get_a_sealable lw]; first [reflexivity | jcond_test_arith] ].

(* The test of a conditional jump, with the hypotheses of the client. *)
#[global] Hint Extern 0 (jcond_test _ _ _ = _) =>
  unfreeze_hyps; solve_jcond_test : regs_next_ok_db.

(* The search, under frozen hypotheses (as [solve_pure_iinstr]). *)
Ltac solve_regs_next_ok_frozen :=
  ltac2:(griotte_freeze_hyps_once ());
  typeclasses eauto 8 with regs_next_ok_db solve_pure typeclass_instances;
  unfreeze_hyps.

(* The distinctness premises of a k-ary rule. *)
Ltac regs_next_ok_intros :=
  repeat match goal with |- _ ≠ _ → _ => let Hne := fresh "Hne" in intros Hne end.

(* The instruction's register step in closed form, for the premise
   [regs_next_ok] or [regs_jump_agree] of a k-ary rule, under its
   distinctness premises. *)
Ltac solve_regs_next_ok :=
  regs_next_ok_intros; solve_regs_next_ok_frozen.

(* The lemma [s] named by the client: applied, directly or at [cnull],
   then the search closes what it can; the other premises of [s] stay as
   side goals, in their order. *)
Ltac regs_next_ok_using s :=
  regs_next_ok_intros;
  first [ eapply s | eapply regs_next_ok_cnull_jump; eapply s ];
  try solve_regs_next_ok_frozen.

(** The lax search in [regs_next_ok_lax_db]: a case lemma whose operand
    premises hold, its other premises postponed (shelved during the search,
    then returned as side goals in their order). *)

(* An operand premise, solved as in the strict search. *)
#[global] Hint Extern 0 (_ !!ₗ _ = Some _) => regs_next_ok_lookup : regs_next_ok_lax_db.
#[global] Hint Extern 0 (lz_of_argument _ _ = Some _) =>
  solve [typeclasses eauto 8 with regs_next_ok_db solve_pure typeclass_instances]
  : regs_next_ok_lax_db.

(* Any other premise of a case lemma is postponed. *)
Ltac regs_next_ok_postpone :=
  lazymatch goal with
  | |- regs_next_ok _ _ _ _ _ _ _ => fail
  | |- regs_jump_agree _ _ _ _ _ => fail
  | |- _ !!ₗ _ = Some _ => fail
  | |- lz_of_argument _ _ = Some _ => fail
  | |- _ => shelve
  end.

#[global] Hint Extern 100 => regs_next_ok_postpone : regs_next_ok_lax_db.

(* A postponed premise: an evar of the lemma is shelved again; a fact with no
   evar is tried once, from a hypothesis or by the strict search; the rest is
   a side goal. A fact with an evar is not searched: a hint could fix the evar
   to a value that the client does not want ([PermFlowsTo ?p p] by
   reflexivity, for instance). *)
Ltac regs_next_ok_postponed_premise :=
  lazymatch goal with
  | |- ?G =>
      lazymatch type of G with
      | Prop =>
          tryif has_evar G then idtac
          else (try solve [assumption | discriminate | solve_regs_next_ok_frozen])
      | _ => shelve
      end
  end.

Ltac solve_regs_next_ok_lax :=
  regs_next_ok_intros;
  ltac2:(griotte_freeze_hyps_once ());
  unshelve (typeclasses eauto 8 with regs_next_ok_lax_db);
  unfreeze_hyps;
  [ regs_next_ok_postponed_premise .. ].

(** * The memory steps in closed form: premises and search

    The membership and agreement of a memory instruction ([rules_mem_access.v],
    database [mem_agree_db]), and the word that a store writes, read in the
    literal register map of a k-ary rule. The settings are global, as for
    [regs_next_ok_db]. *)

(* The word of a store argument: an integer, or the owned word of a
   register. *)
#[global] Hint Extern 0 (store_lift_exact _ _ _) => apply store_lift_argument : mem_agree_db.
#[global] Hint Extern 0 (lword_of_argument _ (inl _) = Some _) => reflexivity : mem_agree_db.
#[global] Hint Extern 0 (lword_of_argument _ (inr _) = Some _) =>
  cbn [lword_of_argument]; regs_next_ok_lookup : mem_agree_db.

(* The permission and the bounds of an access, in the memory fallback of
   [iInstr]: tried only once their address is known, so that no hypothesis
   about another cell fixes the address ([instr_mem_fact_ready],
   [proofmode.v]). *)
Definition mem_access_fact (P : Prop) : Prop := P.

(* A stored integer is the integer itself. *)
Lemma lstore_word_int p z π : lstore_word p (WInt z @@? π) = WInt z @@? π.
Proof. by rewrite /lstore_word /lift_word /= store_word_untagged. Qed.

(* The search, under its distinctness premises and frozen hypotheses. *)
Ltac solve_mem_agree :=
  regs_next_ok_intros;
  ltac2:(griotte_freeze_hyps_once ());
  typeclasses eauto 8 with mem_agree_db;
  unfreeze_hyps.
