From iris.proofmode Require Import coq_tactics.
From iris.bi Require Import bi.
Import bi.
From griotte Require Import rules solve_pure machine_instructions.
From Ltac2 Require Import Ltac2 Option.
Set Default Proof Mode "Classic".

(* Normalize proved register aliases before choosing an explicit-resource rule.
   Prefer PC/cnull as representatives and never decide an unknown equality. *)
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

(* Operand aliases share one owned entry, including PC and cnull. Reading
   cnull still requires its physical register resource. *)
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
   distinct operands, binding each to its owned word before applying a rule. *)
Ltac instr_register_words rs :=
  lazymatch rs with
  | nil => constr:(@nil (RegName * Word))
  | ?r :: ?rs =>
    let tail := instr_register_words rs in
    let ispc := instr_same_register PC r in
    let found := lazymatch ispc with
      | true => constr:(true)
      | false => instr_registers_contain tail r
      end in
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
    | Lea ?dst ?src => instr_argument_registers src constr:([PC; dst])
    | Restrict ?dst ?src => instr_argument_registers src constr:([PC; dst])
    | Subseg ?dst ?s1 ?s2 =>
      let rest := instr_argument_registers s2 constr:([PC; dst]) in
      instr_argument_registers s1 rest
    | Seal ?dst ?s1 ?s2 => constr:([PC; dst; s1; s2])
    | UnSeal ?dst ?s1 ?s2 => constr:([PC; dst; s1; s2])
    | Load ?dst ?src _ => constr:([PC; dst; src])
    | Store ?dst ?src _ => instr_argument_registers src constr:([PC; dst])
    | _ => eval vm_compute in (elements ({[PC]} ∪ regs_of instr))
    end in
  instr_register_words rs.

Ltac solve_instr_failure :=
  intros;
  rewrite /exec /exec_opt /= /word_of_argument /z_of_argument /lookup_reg;
  rewrite ?finz_add_0 /=;
  repeat first [
    progress (rewrite finz_add_0 /=)
  | match goal with
    | H : ?lhs = ?rhs |- context [?lhs] => progress (rewrite H; cbn)
    end ];
  repeat match goal with
  | sb : Sealable |- context [clear_tag_sealable (machine_word.unseal _ ?x)] =>
      constr_eq sb x; destruct sb; cbn
  | sb : Sealable |- context [clear_tag_sealable ?x] =>
      constr_eq sb x; destruct sb; cbn
  end;
  try (rewrite /updatePC /updatePC_gen /update_reg /reg /sreg /mem /= /insert_reg;
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

Ltac instr_auto_solve_addr_result :=
  lazymatch goal with
  | |- @finz.of_z ?bound (@finz.to_z ?bound ?a) = Some ?result =>
      is_evar result; unify result a; solve_addr
  | |- @finz.of_z ?bound ?n = Some ?result =>
      is_evar result; without_evars n;
      let parts := instr_auto_address_offset bound n in
      lazymatch parts with (?a, ?off) =>
        let Hincr := fresh "Hincr" in
        assert (@finz.incr bound a off = Some result) as Hincr by
          instr_auto_solve_addr_result;
        solve_addr
      end
  | |- (?a + ?off)%a = Some ?result =>
      is_evar result;
      first [
        lazymatch off with
        | ((@finz.to_z MemNum ?target) - (@finz.to_z MemNum a))%Z =>
            unify result target; solve_addr
        end
      |
        match goal with
        | H : (?base + ?prior)%a = Some a |- _ =>
            let total := instr_auto_add_offsets prior off in
            unify result (base ^+ total)%a; solve_addr
        end
      | lazymatch a with
        | (?base ^+ ?prior)%a =>
            let total := instr_auto_add_offsets prior off in
            unify result (base ^+ total)%a; solve_addr
        | _ => unify result (a ^+ off)%a; solve_addr
        end ]
  | |- (?a + ?off)%ot = Some ?result =>
      is_evar result;
      first [
        lazymatch off with
        | ((@finz.to_z ONum ?target) - (@finz.to_z ONum a))%Z =>
            unify result target; solve_addr
        end
      |
        match goal with
        | H : (?base + ?prior)%ot = Some a |- _ =>
            let total := instr_auto_add_offsets prior off in
            unify result (base ^+ total)%ot; solve_addr
        end
      | lazymatch a with
        | (?base ^+ ?prior)%ot =>
            let total := instr_auto_add_offsets prior off in
            unify result (base ^+ total)%ot; solve_addr
        | _ => unify result (a ^+ off)%ot; solve_addr
        end ]
  end.

Ltac instr_auto_solve_within_bounds :=
  rewrite /withinBounds;
  first [ltac2:(solve_pure_iinstr ()) | solve_addr |
    (apply andb_false_iff; first [left; solve_addr | right; solve_addr]) |
    (apply andb_true_iff; split; solve_addr)].

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

Ltac instr_auto_solve_premise :=
  first [ltac2:(solve_pure_iinstr ()) | instr_auto_solve_bool | solve_addr |
    instr_auto_solve_within_bounds |
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
