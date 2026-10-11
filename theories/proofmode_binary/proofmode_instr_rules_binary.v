From iris.proofmode Require Import coq_tactics.
From iris.bi Require Import bi.
Import bi.
From griotte Require Import rules_binary solve_pure machine_instructions
  proofmode_instr_support.
From Ltac2 Require Import Ltac2 Option.
Set Default Proof Mode "Classic".

(** * Rule selection for spec-side instruction steps

    Spec counterpart of [proofmode_instr_rules.v]: the same syntactic dispatch
    on the instruction, selecting the [step_*] rules of [rules_binary].
    Instructions without a derived spec rule fall through to the final error
    case. *)

(** Spec counterparts of the register-collection tactics of
    [proofmode_instr_support.v], on spec register points-to predicates. *)
Ltac instr_distinct_register_resources_spec r1 r2 :=
  match goal with
  | |- context [ Esnoc _ ?h1 (?rr1 ↣ᵣ _)%I ] =>
    let checked := constr:(ltac:(constr_eq r1 rr1; exact I) : True) in
    match goal with
    | |- context [ Esnoc _ ?h2 (?rr2 ↣ᵣ _)%I ] =>
      let checked := constr:(ltac:(constr_eq r2 rr2; exact I) : True) in
      let checked := constr:(ltac:(tryif constr_eq h1 h2 then fail else exact I) : True) in
      constr:(false)
    end
  end.

Ltac instr_same_register_spec r1 r2 :=
  let r1' := eval cbv in r1 in
  let r2' := eval cbv in r2 in
  let checked := constr:(ltac:(without_evars r1'; without_evars r2'; exact I) : True) in
  match goal with
  | _ => let H := constr:(ltac:(constr_eq r1 r2; reflexivity) : r1 = r2) in constr:(true)
  | _ => let eq := eval vm_compute in (bool_decide (r1 = r2)) in
         lazymatch eq with true => constr:(true) | false => constr:(false) end
  | _ => let H := constr:(ltac:(first [congruence | solve_pure]) : r1 = r2) in constr:(true)
  | _ => let H := constr:(ltac:(first [congruence | solve_pure]) : r1 ≠ r2) in constr:(false)
  | _ => instr_distinct_register_resources_spec r1 r2
  end.

Ltac instr_registers_contain_spec regs r :=
  lazymatch regs with
  | (?rr, ?ww) :: ?tail =>
    let eq := instr_same_register_spec rr r in
    lazymatch eq with true => constr:(true) | false => instr_registers_contain_spec tail r end
  | _ => constr:(false)
  end.

Ltac instr_register_words_spec rs :=
  lazymatch rs with
  | nil => constr:(@nil (RegName * Word))
  | ?r :: ?rs =>
    let tail := instr_register_words_spec rs in
    let ispc := instr_same_register_spec PC r in
    let found := lazymatch ispc with
      | true => constr:(true)
      | false => instr_registers_contain_spec tail r
      end in
    lazymatch found with
    | true => tail
    | false => match goal with
      | |- context [ Esnoc _ _ (?rr ↣ᵣ ?w)%I ] =>
        let eq := instr_same_register_spec rr r in
        lazymatch eq with
        | true => constr:((rr, w) :: tail)
        end
      end
    end
  end.

Ltac instr_failure_registers_spec instr :=
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
  instr_register_words_spec rs.

Ltac dispatch_spec_Get r1 r2 cont :=
  let p := constr:((r1, r2)) in
  lazymatch p with
  | (_, PC) => cont (@step_Get_PC_success)
  | (?r, ?r) => cont (@step_Get_same_success)
  | _ => cont (@step_Get_success)
  end.

Ltac dispatch_spec_BinOp r1 x1 x2 cont :=
  let p := constr:((r1, x1, x2)) in
  lazymatch p with
  | (?r, (inr ?r), (inr ?r)) => cont (@step_binop_success_dst_dst)
  | (?dst, (inr ?r), (inr ?dst)) => cont (@step_binop_success_r_dst)
  | (?dst, (inr ?dst), (inr ?r)) => cont (@step_binop_success_dst_r)
  | (?dst, (inl _), (inr ?dst)) => cont (@step_binop_success_z_dst)
  | (?dst, (inr ?dst), (inl _)) => cont (@step_binop_success_dst_z)
  | (?dst, (inr ?r), (inr ?r)) => cont (@step_binop_success_r_r_same)
  | (?dst, (inr ?r), (inl _)) => cont (@step_binop_success_r_z)
  | (?dst, (inl _), (inr _)) =>
    (cont (@step_binop_success_z_r) ||
     cont (@step_binop_fail_z_r))
  | (?dst, (inr _), (inr _)) => cont (@step_binop_success_r_r)
  | (?dst, (inl _), (inl _)) => cont (@step_binop_success_z_z)
  end.

Ltac dispatch_spec_instr_rule instr cont :=
  let instr := eval unfold register_file.regn, register_file.cst in instr in
  lazymatch instr with
  (* Mov *)
  | Mov PC (inr PC) => cont (@step_move_success_reg_samePC)
  | Mov PC (inr _) => cont (@step_move_success_reg_toPC)
  | Mov _ (inr PC) => cont (@step_move_success_reg_fromPC)
  | Mov ?r (inr ?r) => cont (@step_move_success_reg_same)
  | Mov _ (inr _) => cont (@step_move_success_reg)
  | Mov _ (inl _) => cont (@step_move_success_z_gen)
  (* Get *)
  | GetL ?r1 ?r2 => dispatch_spec_Get r1 r2 cont
  | GetP ?r1 ?r2 => dispatch_spec_Get r1 r2 cont
  | GetB ?r1 ?r2 => dispatch_spec_Get r1 r2 cont
  | GetE ?r1 ?r2 => dispatch_spec_Get r1 r2 cont
  | GetA ?r1 ?r2 => dispatch_spec_Get r1 r2 cont
  | GetOType ?r1 ?r2 => dispatch_spec_Get r1 r2 cont
  | GetWType ?r1 ?r2 => dispatch_spec_Get r1 r2 cont
  | GetTag PC PC => cont (@step_GetTag_PC_failure)
  | GetTag PC cnull => cont (@step_GetTag_cnull_toPC)
  | GetTag PC _ => cont (@step_GetTag_toPC_failure)
  | GetTag cnull cnull => cont (@step_GetTag_cnull)
  | GetTag cnull PC => cont (@step_GetTag_PC_to_cnull)
  | GetTag cnull _ => cont (@step_GetTag_to_cnull)
  | GetTag _ cnull => cont (@step_GetTag_from_cnull)
  | GetTag ?r1 ?r2 => dispatch_spec_Get r1 r2 cont
  (* ClearTag *)
  | ClearTag PC PC => cont (@step_ClearTag_PC)
  | ClearTag PC cnull => cont (@step_ClearTag_cnull_toPC)
  | ClearTag PC _ =>
    (cont (@step_ClearTag_toPC) || cont (@step_ClearTag_toPC_failure))
  | ClearTag cnull cnull => cont (@step_ClearTag_cnull)
  | ClearTag cnull PC => cont (@step_ClearTag_PC_to_cnull)
  | ClearTag cnull _ => cont (@step_ClearTag_to_cnull)
  | ClearTag _ cnull => cont (@step_ClearTag_from_cnull)
  | ClearTag _ PC => cont (@step_ClearTag_fromPC)
  | ClearTag ?r ?r => cont (@step_ClearTag_same_success)
  | ClearTag _ _ => cont (@step_ClearTag_success)
  (* BinOp *)
  | Add ?x1 ?x2 ?x3 => dispatch_spec_BinOp x1 x2 x3 cont
  | Sub ?x1 ?x2 ?x3 => dispatch_spec_BinOp x1 x2 x3 cont
  | Mul ?x1 ?x2 ?x3 => dispatch_spec_BinOp x1 x2 x3 cont
  | LAnd ?x1 ?x2 ?x3 => dispatch_spec_BinOp x1 x2 x3 cont
  | LOr ?x1 ?x2 ?x3 => dispatch_spec_BinOp x1 x2 x3 cont
  | LShiftL ?x1 ?x2 ?x3 => dispatch_spec_BinOp x1 x2 x3 cont
  | LShiftR ?x1 ?x2 ?x3 => dispatch_spec_BinOp x1 x2 x3 cont
  | Lt ?x1 ?x2 ?x3 => dispatch_spec_BinOp x1 x2 x3 cont
  (* Lea *)
  | Lea PC (inr _) => cont (@step_lea_success_reg_PC)
  | Lea PC (inl _) => cont (@step_lea_success_z_PC)
  | Lea _ (inr _) => (cont (@step_lea_success_reg) || cont (@step_lea_success_reg_sr))
  | Lea _ (inl _) => (cont (@step_lea_success_z) || cont (@step_lea_success_z_sr))
  (* Load *)
  | Load PC PC _ => cont (@step_load_success_PC_PC_imm)
  | Load PC _ 0 => cont (@step_load_success_PC)
  | Load _ PC 0 => cont (@step_load_success_fromPC)
  | Load ?r ?r 0 =>
    (cont (fun MP Σ invG specg E r1 pc_p pc_g pc_b pc_e pc_a w w' =>
       @step_load_success_same_notinstr MP Σ invG specg E r1 pc_p pc_g pc_b pc_e pc_a w w' (WInt 0)) ||
     cont (@step_load_success_same_frominstr))
  | Load _ _ 0 =>
    (cont (@step_load_success_notinstr) ||
     cont (@step_load_success_frominstr))
  (* Store *)
  | Store PC (inl _) 0 => cont (@step_store_success_z_PC)
  | Store PC (inr PC) 0 =>
    cont (fun MP Σ invG specg E pc_p pc_g pc_b pc_e pc_a pc_a' w =>
      @step_store_success_reg_PC_same_store_word MP Σ invG specg E pc_p pc_g pc_b pc_e pc_a pc_a' w (WInt 0))
  | Store PC (inr _) 0 => cont (@step_store_success_reg_PC_store_word)
  | Store _ (inl _) 0 =>
    (cont (fun MP Σ invG specg E pc_p pc_g pc_b pc_e pc_a pc_a' w dst z =>
       @step_store_success_same MP Σ invG specg E pc_p pc_g pc_b pc_e pc_a pc_a' w dst z (WInt 0)) ||
     cont (@step_store_success_z))
  | Store _ (inr PC) 0 =>
    (cont (@step_store_success_reg_fromPC_same_a_store_word_imm) ||
     cont (@step_store_success_reg_fromPC_store_word_imm))
  | Store ?r (inr ?r) 0 =>
    (cont (@step_store_success_reg_same'_store_word) ||
     cont (@step_store_success_reg_same_store_word))
  | Store _ (inr _) 0 =>
    (cont (@step_store_success_reg_same_a_store_word) ||
     cont (@step_store_success_reg_store_word))
  (* Immediate accesses use the effective address in their memory resources. *)
  | Load PC _ _ => cont (@step_load_success_PC_imm)
  | Load _ PC _ =>
    (cont (@step_load_success_fromPC_notinstr_imm) ||
     cont (@step_load_success_fromPC_frominstr_imm))
  | Load ?r ?r _ =>
    (cont (@step_load_success_same_notinstr_imm) ||
     cont (@step_load_success_same_frominstr_imm))
  | Load _ _ _ =>
    (cont (@step_load_success_notinstr_imm) ||
     cont (@step_load_success_frominstr_imm))
  | Store PC (inl _) _ =>
    (cont (@step_store_success_z_PC_same_a_imm) ||
     cont (@step_store_success_z_PC_imm))
  | Store PC (inr PC) _ =>
    (cont (@step_store_success_reg_PC_same_same_a_store_word_imm) ||
     cont (@step_store_success_reg_PC_same_store_word_imm))
  | Store PC (inr _) _ =>
    (cont (@step_store_success_reg_PC_same_a_store_word_imm) ||
     cont (@step_store_success_reg_PC_store_word_imm))
  | Store _ (inl _) _ =>
    (cont (@step_store_success_same_imm) ||
     cont (@step_store_success_z_imm))
  | Store _ (inr PC) _ =>
    (cont (@step_store_success_reg_fromPC_same_a_store_word_imm) ||
     cont (@step_store_success_reg_fromPC_store_word_imm))
  | Store ?r (inr ?r) _ =>
    (cont (@step_store_success_reg_same'_store_word_imm) ||
     cont (@step_store_success_reg_same_store_word_imm))
  | Store _ (inr _) _ =>
    (cont (@step_store_success_reg_same_a_store_word_imm) ||
     cont (@step_store_success_reg_store_word_imm))
  (* Jnz *)
  | Jnz (inl _) PC => cont (@step_jnz_success_jmpPC_z)
  | Jnz (inr _) PC => cont (@step_jnz_success_jmpPC_reg)
  | Jnz (inl _) _ => (cont (@step_jnz_success_next_z) || cont (@step_jnz_success_jmp_z))
  | Jnz (inr ?r) ?r => cont (@step_jnz_success_jmp_same)
  | Jnz (inr _) _ => (cont (@step_jnz_success_next_reg) || cont (@step_jnz_success_jmp_reg))
  (* Jmp *)
  | Jmp (inl _) => cont (@step_jmp_success_z)
  | Jmp (inr _) => cont (@step_jmp_success_reg)
  (* Jalr *)
  | Jalr _ PC => cont (@step_jalr_successPC)
  | Jalr cnull _ => cont (@step_jalr_success_cnull)
  | Jalr ?r ?r => cont (@step_jalr_success_rdst)
  | Jalr _ _ => cont (@step_jalr_success)
  (* Subseg *)
  | Subseg PC _ _ => fail "No spec rule for Subseg on PC:" instr
  | Subseg _ (inr ?r) (inr ?r) => fail "No spec rule for Subseg with equal bounds registers:" instr
  | Subseg _ (inr _) (inr _) => (cont (@step_subseg_success) || cont (@step_subseg_success_sr))
  (* Restrict *)
  | Restrict PC (inr _) => cont (@step_restrict_success_reg_PC)
  | Restrict _ (inr _) => cont (@step_restrict_success_reg)
  | Restrict PC (inl _) => cont (@step_restrict_success_z_PC)
  | Restrict _ (inl _) => cont (@step_restrict_success_z)
  (* Seal *)
  | Seal _ _ _ => fail "No spec rule for Seal:" instr
  (* UnSeal *)
  | UnSeal PC _ _ => fail "No spec rule for UnSeal on PC:" instr
  | UnSeal ?r _ ?r => cont (@step_unseal_r2)
  | UnSeal ?r ?r _ => fail "No spec rule for UnSeal with dst = src1:" instr
  | UnSeal _ _ _ => cont (@step_unseal_success)
  (* ReadSR *)
  | ReadSR PC _ => cont (@step_readsr_success_toPC)
  | ReadSR _ _ => cont (@step_readsr_success)
  (* WriteSR *)
  | WriteSR _ PC => cont (@step_writesr_success_fromPC)
  | WriteSR _ _ => cont (@step_writesr_success)
  (* Fail *)
  | Fail => cont (@step_fail)
  (* Halt *)
  | Halt => cont (@step_halt)
  (* not found *)
  | _ => fail "No suitable spec rule found for instruction" instr
  end.

(** Runtime failure: the generic [step_instr_failed_N] rules, as for the
    implementation side ([dispatch_instr_failure]). *)
Ltac dispatch_spec_generic_failure instr cont :=
  let regs := instr_failure_registers_spec instr in
  lazymatch goal with
  | |- context [ Esnoc _ _ (PC ↣ᵣ WCap true ?p ?g ?b ?e ?a)%I ] =>
    lazymatch regs with
    | [] => cont (fun E => @step_instr_failed_0 _ _ _ _ E p g b e a
                            (encodeInstrW instr) instr)
    | [(?r1, ?w1)] => cont (fun E => @step_instr_failed_1 _ _ _ _ E p g b e a
                                     (encodeInstrW instr) instr r1 w1)
    | [(?r1, ?w1); (?r2, ?w2)] =>
        cont (fun E => @step_instr_failed_2 _ _ _ _ E p g b e a
                         (encodeInstrW instr) instr r1 w1 r2 w2)
    | [(?r1, ?w1); (?r2, ?w2); (?r3, ?w3)] =>
        cont (fun E => @step_instr_failed_3 _ _ _ _ E p g b e a
                         (encodeInstrW instr) instr r1 w1 r2 w2 r3 w3)
    end
  end.

Ltac dispatch_spec_instr_failure instr cont :=
  first [ dispatch_spec_generic_failure instr cont
        | fail "No immediate-failure spec provider found for instruction" instr ].

(** Invalidation: spec counterpart of [dispatch_instr_invalidation]. *)
Ltac dispatch_spec_instr_invalidation instr cont :=
  let instr := eval cbv [regn cst] in instr in
  lazymatch instr with
  (* Lea: reuse the existing overflow rules. *)
  | Lea PC (inr _) => cont (@step_lea_overflow_reg_PC)
  | Lea PC (inl _) => cont (@step_lea_overflow_z_PC)
  | Lea _ (inr _) => (cont (@step_lea_overflow_reg) || cont (@step_lea_overflow_reg_sr))
  | Lea _ (inl _) => (cont (@step_lea_overflow_z) || cont (@step_lea_overflow_z_sr))
  (* Restrict *)
  | Restrict PC (inr _) => cont (@step_restrict_invalidated_reg_PC)
  | Restrict PC (inl _) => cont (@step_restrict_invalidated_z_PC)
  | Restrict _ (inr _) =>
      (cont (@step_restrict_invalidated_reg) || cont (@step_restrict_invalidated_reg_sr))
  | Restrict _ (inl _) =>
      (cont (@step_restrict_invalidated_z) || cont (@step_restrict_invalidated_z_sr))
  (* Subseg: conversion overflow has priority over representable rejection. *)
  | Subseg PC (inr ?r) (inr ?r) =>
      (cont (@step_subseg_unrepresentable_pc_same) ||
       cont (@step_subseg_invalidated_pc_same))
  | Subseg PC (inr _) (inr _) =>
      (cont (@step_subseg_unrepresentable_pc) ||
       cont (@step_subseg_invalidated_pc))
  | Subseg PC (inl _) (inr _) =>
      (cont (@step_subseg_unrepresentable_pc_l) ||
       cont (@step_subseg_invalidated_pc_l))
  | Subseg PC (inr _) (inl _) =>
      (cont (@step_subseg_unrepresentable_pc_r) ||
       cont (@step_subseg_invalidated_pc_r))
  | Subseg PC (inl _) (inl _) =>
      (cont (@step_subseg_unrepresentable_pc_lr) ||
       cont (@step_subseg_invalidated_pc_lr))
  | Subseg _ (inr ?r) (inr ?r) =>
      (cont (@step_subseg_unrepresentable_same) ||
       cont (@step_subseg_unrepresentable_same_sr) ||
       cont (@step_subseg_invalidated_same) ||
       cont (@step_subseg_invalidated_same_sr))
  | Subseg _ (inr _) (inr _) =>
      (cont (@step_subseg_unrepresentable) ||
       cont (@step_subseg_unrepresentable_sr) ||
       cont (@step_subseg_invalidated) ||
       cont (@step_subseg_invalidated_sr))
  | Subseg _ (inl _) (inr _) =>
      (cont (@step_subseg_unrepresentable_l) ||
       cont (@step_subseg_unrepresentable_l_sr) ||
       cont (@step_subseg_invalidated_l) ||
       cont (@step_subseg_invalidated_l_sr))
  | Subseg _ (inr _) (inl _) =>
      (cont (@step_subseg_unrepresentable_r) ||
       cont (@step_subseg_unrepresentable_r_sr) ||
       cont (@step_subseg_invalidated_r) ||
       cont (@step_subseg_invalidated_r_sr))
  | Subseg _ (inl _) (inl _) =>
      (cont (@step_subseg_unrepresentable_lr) ||
       cont (@step_subseg_unrepresentable_lr_sr) ||
       cont (@step_subseg_invalidated_lr) ||
       cont (@step_subseg_invalidated_lr_sr))
  (* Seal *)
  | Seal ?r ?r PC => cont (@step_seal_invalidated_PC_eq)
  | Seal _ _ PC => cont (@step_seal_invalidated_PC)
  | Seal ?r ?r ?r => cont (@step_seal_invalidated_all)
  | Seal _ ?r ?r => cont (@step_seal_invalidated_same)
  | Seal ?r ?r _ => cont (@step_seal_invalidated_r1)
  | Seal ?r _ ?r => cont (@step_seal_invalidated_r2)
  | Seal _ _ _ => cont (@step_seal_invalidated)
  (* UnSeal *)
  | UnSeal PC _ _ => cont (@step_unseal_invalidated_PC)
  | UnSeal ?r ?r _ => cont (@step_unseal_invalidated_r1)
  | UnSeal ?r _ ?r => cont (@step_unseal_invalidated_r2)
  | UnSeal _ _ _ => cont (@step_unseal_invalidated)
  | _ => fail "No invalidation spec rule found for instruction" instr
  end.
