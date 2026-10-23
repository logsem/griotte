From iris.proofmode Require Import coq_tactics.
From iris.bi Require Import bi.
Import bi.
From griotte Require Import rules solve_pure machine_instructions
  proofmode_instr_support.
From Ltac2 Require Import Ltac2 Option.
Set Default Proof Mode "Classic".

Ltac dispatch_Get r1 r2 cont :=
  let p := constr:((r1, r2)) in
  lazymatch p with
  | (?r, ?r) => cont (@wp_Get_same_success)
  | _ => cont (@wp_Get_success)
  end.

Ltac dispatch_BinOp r1 x1 x2 cont :=
  let p := constr:((r1, x1, x2)) in
  lazymatch p with
  | (?r, (inr ?r), (inr ?r)) => cont (@wp_binop_success_dst_dst)
  | (?dst, (inr ?r), (inr ?dst)) => cont (@wp_binop_success_r_dst)
  | (?dst, (inr ?dst), (inr ?r)) => cont (@wp_binop_success_dst_r)
  | (?dst, (inl _), (inr ?dst)) => cont (@wp_binop_success_z_dst)
  | (?dst, (inr ?dst), (inl _)) => cont (@wp_binop_success_dst_z)
  | (?dst, (inr ?r), (inr ?r)) => cont (@wp_binop_success_r_r_same)
  | (?dst, (inr ?r), (inl _)) => cont (@wp_binop_success_r_z)
  | (?dst, (inl _), (inr _)) => cont (@wp_binop_success_z_r)
  | (?dst, (inr _), (inr _)) => cont (@wp_binop_success_r_r)
  | (?dst, (inl _), (inl _)) => cont (@wp_binop_success_z_z)
  end.

(* A conditional jump: the rule of the taken jump, else the rule of the
   fall-through. Each commits its comparison ([instr_commit_lint]). *)
Ltac dispatch_JCond off x1 x2 cont :=
  let p := constr:((off, x1, x2)) in
  lazymatch p with
  | (inl _, inr ?r, inr ?r) =>
      (cont (@wp_jcond_success_jmp_r_r_same) || cont (@wp_jcond_success_next_r_r_same))
  | (inl _, inr _, inr _) =>
      (cont (@wp_jcond_success_jmp_r_r) || cont (@wp_jcond_success_next_r_r))
  | (inl _, inr _, inl _) =>
      (cont (@wp_jcond_success_jmp_r_z) || cont (@wp_jcond_success_next_r_z))
  | (inl _, inl _, inr _) =>
      (cont (@wp_jcond_success_jmp_z_r) || cont (@wp_jcond_success_next_z_r))
  end.

Ltac dispatch_instr_rule instr cont :=
  let instr := eval unfold register_file.regn, register_file.cst in instr in
  lazymatch instr with
  (* Mov *)
  | Mov ?r (inr ?r) => cont (@wp_move_success_reg_same)
  | Mov _ (inr _) => cont (@wp_move_success_reg)
  | Mov _ (inl _) => cont (@wp_move_success_z_gen)
  (* Get *)
  | GetL ?r1 ?r2 => dispatch_Get r1 r2 cont
  | GetP ?r1 ?r2 => dispatch_Get r1 r2 cont
  | GetB ?r1 ?r2 => dispatch_Get r1 r2 cont
  | GetE ?r1 ?r2 => dispatch_Get r1 r2 cont
  | GetA ?r1 ?r2 => dispatch_Get r1 r2 cont
  | GetOType ?r1 ?r2 => dispatch_Get r1 r2 cont
  | GetWType ?r1 ?r2 => dispatch_Get r1 r2 cont
  | GetTag cnull cnull => cont (@wp_GetTag_cnull)
  | GetTag cnull _ => cont (@wp_GetTag_to_cnull)
  | GetTag _ cnull => cont (@wp_GetTag_from_cnull)
  | GetTag _ _ => cont (@wp_gettag_success)
  (* ClearTag *)
  | ClearTag cnull cnull => cont (@wp_ClearTag_cnull)
  | ClearTag cnull _ => cont (@wp_ClearTag_to_cnull)
  | ClearTag _ cnull => cont (@wp_ClearTag_from_cnull)
  | ClearTag ?r ?r => cont (@wp_ClearTag_same_success)
  | ClearTag _ _ => cont (@wp_ClearTag_success)
  (* BinOp *)
  | Add ?x1 ?x2 ?x3 => dispatch_BinOp x1 x2 x3 cont
  | Sub ?x1 ?x2 ?x3 => dispatch_BinOp x1 x2 x3 cont
  | Mul ?x1 ?x2 ?x3 => dispatch_BinOp x1 x2 x3 cont
  | LAnd ?x1 ?x2 ?x3 => dispatch_BinOp x1 x2 x3 cont
  | LOr ?x1 ?x2 ?x3 => dispatch_BinOp x1 x2 x3 cont
  | LShiftL ?x1 ?x2 ?x3 => dispatch_BinOp x1 x2 x3 cont
  | LShiftR ?x1 ?x2 ?x3 => dispatch_BinOp x1 x2 x3 cont
  | Lt ?x1 ?x2 ?x3 => dispatch_BinOp x1 x2 x3 cont
  | Le ?x1 ?x2 ?x3 => dispatch_BinOp x1 x2 x3 cont
  (* SetA *)
  | SetA ?r ?r (inr _) => (cont (@wp_seta_success_reg) || cont (@wp_seta_success_reg_int))
  | SetA ?r ?r (inl _) => (cont (@wp_seta_success_z) || cont (@wp_seta_success_z_int))
  | SetA _ _ (inr _) =>
    (cont (@wp_seta_success_reg_src) || cont (@wp_seta_success_reg_int_src))
  | SetA _ _ (inl _) =>
    (cont (@wp_seta_success_z_src) || cont (@wp_seta_success_z_int_src))
  (* Lea *)
  | Lea _ (inr _) => (cont (@wp_lea_success_reg) || cont (@wp_lea_success_reg_sr))
  | Lea _ (inl _) =>
    (cont (@wp_lea_success_z) || cont (@wp_lea_success_z_sr) || cont (@wp_lea_success_z_int))
  (* CLoad *)
  | CLoad ?r ?r 0 =>
    (cont (fun MP Σ ceriseg E r1 pc_p pc_g pc_b pc_e pc_a pc_π w w' =>
       @wp_load_success_same_notinstr MP Σ ceriseg E r1 pc_p pc_g pc_b pc_e pc_a pc_π w w' (WInt 0 @@? None)) ||
     cont (@wp_load_success_same_frominstr))
  | CLoad _ _ 0 =>
    (cont (@wp_load_success_notinstr) ||
     cont (@wp_load_success_frominstr))
  (* Store *)
  | Store _ (inl _) 0 =>
    (cont (fun MP Σ ceriseg E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst z =>
       @wp_store_success_same MP Σ ceriseg E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst z (WInt 0 @@? None)) ||
     cont (@wp_store_success_z))
  | Store ?r (inr ?r) 0 =>
    (cont (@wp_store_success_reg_same'_store_word) ||
     cont (@wp_store_success_reg_same_store_word))
  | Store _ (inr _) 0 =>
    (cont (@wp_store_success_reg_same_a_store_word) ||
     cont (@wp_store_success_reg_store_word))
  (* Immediate accesses use the effective address in their memory resources. *)
  | CLoad ?r ?r _ =>
    (cont (@wp_load_success_same_notinstr_imm) ||
     cont (@wp_load_success_same_frominstr_imm))
  | CLoad _ _ _ =>
    (cont (@wp_load_success_notinstr_imm) ||
     cont (@wp_load_success_frominstr_imm))
  (* Store *)
  | Store _ (inl _) _ =>
    (cont (@wp_store_success_same_imm) ||
     cont (@wp_store_success_z_imm))
  | Store ?r (inr ?r) _ =>
    (cont (@wp_store_success_reg_same'_store_word_imm) ||
     cont (@wp_store_success_reg_same_store_word_imm))
  | Store _ (inr _) _ =>
    (cont (@wp_store_success_reg_same_a_store_word_imm) ||
     cont (@wp_store_success_reg_store_word_imm))
  (* Conditional jumps; [Jne off r 0] and [Jeq off r 0] first *)
  | Jne (inl _) (inr _) (inl 0%Z) =>
    (cont (@wp_jnez_success_next_z) || cont (@wp_jnez_success_jmp_z))
  | Jeq (inl _) (inr _) (inl 0%Z) =>
    (cont (@wp_jeqz_success_jmp_z) || cont (@wp_jeqz_success_next_z))
  | Jeq ?o ?x1 ?x2 => dispatch_JCond o x1 x2 cont
  | Jne ?o ?x1 ?x2 => dispatch_JCond o x1 x2 cont
  | Jlt ?o ?x1 ?x2 => dispatch_JCond o x1 x2 cont
  | Jle ?o ?x1 ?x2 => dispatch_JCond o x1 x2 cont
  (* Jmp *)
  | Jmp (inl _) => cont (@wp_jmp_success_z)
  | Jmp (inr _) => cont (@wp_jmp_success_reg)
  (* Jalr *)
  | Jalr cnull _ => cont (@wp_jalr_success_cnull)
  | Jalr cra cra => cont (@wp_jalr_success_call_same)
  | Jalr cra _ => cont (@wp_jalr_success_call)
  | Jalr ?r ?r => cont (@wp_jalr_success_rdst)
  | Jalr _ _ => cont (@wp_jalr_success)
  (* Subseg *)
  | Subseg _ (inr ?r) (inr ?r) => (cont (@wp_subseg_success_same) || cont (@wp_subseg_success_same_sr)) (* TODO: improve using register values? *)
  | Subseg _ (inr _) (inr _) =>
    (cont (@wp_subseg_success) || cont (@wp_subseg_success_sr) || cont (@wp_subseg_success_root))
  | Subseg _ (inl _) (inr _) => (cont (@wp_subseg_success_l) || cont (@wp_subseg_success_l_sr))
  | Subseg _ (inr _) (inl _) => (cont (@wp_subseg_success_r) || cont (@wp_subseg_success_r_sr))
  | Subseg _ (inl _) (inl _) => (cont (@wp_subseg_success_lr) || cont (@wp_subseg_success_lr_sr))
  (* Restrict *)
  | Restrict _ (inr _) => cont (@wp_restrict_success_reg)
  | Restrict _ (inl _) => cont (@wp_restrict_success_z)
  (* Seal *)
  | Seal ?r _ ?r => cont (@wp_seal_r2)
  | Seal ?r ?r _ => cont (@wp_seal_r1)
  | Seal _ _ _ => cont (@wp_seal_success)
  (* UnSeal *)
  | UnSeal ?r _ ?r => cont (@wp_unseal_r2)
  | UnSeal ?r ?r _ => cont (@wp_unseal_r1)
  | UnSeal _ _ _ => cont (@wp_unseal_success)
  (* SpecialRW: readsr, writesr, csrw with an immediate, swaps *)
  | SpecialRW _ _ (inr cnull) => cont (@wp_readsr_success)
  | SpecialRW cnull _ (inr _) => cont (@wp_writesr_success)
  | SpecialRW cnull _ (inl _) => cont (@wp_specialrw_imm_success)
  | SpecialRW ?r _ (inr ?r) => cont (@wp_specialrw_swap)
  | SpecialRW _ _ (inr _) => cont (@wp_specialrw_success)
  (* SetMIE: csrsi and csrci on mstatus *)
  | SetMIE _ => cont (@wp_setmie_success)
  (* Mret *)
  | Mret => cont (@wp_mret_success)
  (* auipcc *)
  | Auipcc _ _ => (cont (@wp_auipcc_success) || cont (@wp_auipcc_overflow))
  (* Fail *)
  | Fail => cont (@wp_fail)
  (* Halt *)
  | Halt => cont (@wp_halt)
  (* not found *)
  | _ => fail "No suitable rule found for instruction" instr
  end.

Ltac dispatch_generic_failure instr cont :=
  let regs := instr_failure_registers instr in
  lazymatch goal with
  | |- context [ Esnoc _ _ (PC ↦ₚ WCap true ?p ?g ?b ?e ?a @@? ?π)%I ] =>
    lazymatch regs with
    | [] => cont (fun E => @wp_instr_faulted_0 _ _ _ E p g b e a π
                            (encodeInstrW instr @@? None) instr)
    | [(?r1, ?w1)] => cont (fun E => @wp_instr_faulted_1 _ _ _ E p g b e a π
                                     (encodeInstrW instr @@? None) instr r1 w1)
    | [(?r1, ?w1); (?r2, ?w2)] =>
        cont (fun E => @wp_instr_faulted_2 _ _ _ E p g b e a π
                         (encodeInstrW instr @@? None) instr r1 w1 r2 w2)
    | [(?r1, ?w1); (?r2, ?w2); (?r3, ?w3)] =>
        cont (fun E => @wp_instr_faulted_3 _ _ _ E p g b e a π
                         (encodeInstrW instr @@? None) instr r1 w1 r2 w2 r3 w3)
    end
  end.

(* Jalr fails on its target before it writes anything. *)
Ltac dispatch_jalr_failure instr cont :=
  let instr := eval unfold register_file.regn, register_file.cst in instr in
  lazymatch instr with
  | Jalr cnull _ => cont (@wp_jalr_fail_target_cnull)
  | Jalr ?r ?r => cont (@wp_jalr_fail_target_same)
  | Jalr _ _ => cont (@wp_jalr_fail_target)
  end.

Ltac dispatch_instr_failure instr cont :=
  first [ dispatch_jalr_failure instr cont
        | dispatch_generic_failure instr cont
        | fail "No immediate-failure provider found for instruction" instr ].

(* Like ordinary success dispatch, invalidation selects explicit-resource
   lemmas. Add an instruction case and its necessary alias/operand variants;
   resource preparation and side-condition handling belong to the caller. *)
Ltac dispatch_instr_invalidation instr cont :=
  let instr := eval cbv [regn cst] in instr in
  lazymatch instr with
  (* SetA: an address out of range *)
  | SetA ?r ?r (inr _) => cont (@wp_seta_invalid_reg)
  | SetA ?r ?r (inl _) => cont (@wp_seta_invalid_z)
  | SetA _ _ (inr _) => cont (@wp_seta_invalid_reg_src)
  | SetA _ _ (inl _) => cont (@wp_seta_invalid_z_src)
  (* Lea: reuse the existing overflow rules. *)
  | Lea _ (inr _) => (cont (@wp_lea_overflow_reg) || cont (@wp_lea_overflow_reg_sr))
  | Lea _ (inl _) => (cont (@wp_lea_overflow_z) || cont (@wp_lea_overflow_z_sr))
  (* Restrict *)
  | Restrict _ (inr _) =>
      (cont (@wp_restrict_invalidated_reg) || cont (@wp_restrict_invalidated_reg_sr))
  | Restrict _ (inl _) =>
      (cont (@wp_restrict_invalidated_z) || cont (@wp_restrict_invalidated_z_sr))
  (* Subseg: conversion overflow has priority over representable rejection.
     The explicit-mode caller requires overflow evidence before committing. *)
  | Subseg _ (inr ?r) (inr ?r) =>
      (cont (@wp_subseg_unrepresentable_same) ||
       cont (@wp_subseg_unrepresentable_same_sr) ||
       cont (@wp_subseg_invalidated_same) ||
       cont (@wp_subseg_invalidated_same_sr))
  | Subseg _ (inr _) (inr _) =>
      (cont (@wp_subseg_unrepresentable) ||
       cont (@wp_subseg_unrepresentable_sr) ||
       cont (@wp_subseg_invalidated) ||
       cont (@wp_subseg_invalidated_sr))
  | Subseg _ (inl _) (inr _) =>
      (cont (@wp_subseg_unrepresentable_l) ||
       cont (@wp_subseg_unrepresentable_l_sr) ||
       cont (@wp_subseg_invalidated_l) ||
       cont (@wp_subseg_invalidated_l_sr))
  | Subseg _ (inr _) (inl _) =>
      (cont (@wp_subseg_unrepresentable_r) ||
       cont (@wp_subseg_unrepresentable_r_sr) ||
       cont (@wp_subseg_invalidated_r) ||
       cont (@wp_subseg_invalidated_r_sr))
  | Subseg _ (inl _) (inl _) =>
      (cont (@wp_subseg_unrepresentable_lr) ||
       cont (@wp_subseg_unrepresentable_lr_sr) ||
       cont (@wp_subseg_invalidated_lr) ||
       cont (@wp_subseg_invalidated_lr_sr))
  (* Seal *)
  | Seal ?r ?r ?r => cont (@wp_seal_invalidated_all)
  | Seal _ ?r ?r => cont (@wp_seal_invalidated_same)
  | Seal ?r ?r _ => cont (@wp_seal_invalidated_r1)
  | Seal ?r _ ?r => cont (@wp_seal_invalidated_r2)
  | Seal _ _ _ => cont (@wp_seal_invalidated)
  (* UnSeal *)
  | UnSeal ?r ?r _ => cont (@wp_unseal_invalidated_r1)
  | UnSeal ?r _ ?r => cont (@wp_unseal_invalidated_r2)
  | UnSeal _ _ _ => cont (@wp_unseal_invalidated)
  | _ => fail "No invalidation rule found for instruction" instr
  end.
