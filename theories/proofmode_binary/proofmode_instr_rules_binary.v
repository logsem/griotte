From griotte Require Import rules_binary machine_instructions.
From Ltac2 Require Import Ltac2 Option.
Set Default Proof Mode "Classic".

(** * Rule selection for spec-side instruction steps

    Spec counterpart of [proofmode_instr_rules.v]: the same syntactic dispatch
    on the instruction, selecting the [step_*] rules of [rules_binary].
    Instructions without a derived spec rule fall through to the final error
    case. *)

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
  | Load PC _ => fail "No spec rule for this instruction:" instr
  | Load _ PC => cont (@step_load_success_fromPC)
  | Load ?r ?r =>
    (cont (@step_load_success_same_notinstr) ||
     cont (@step_load_success_same_frominstr))
  | Load _ _ =>
    (cont (@step_load_success_notinstr) ||
     cont (@step_load_success_frominstr))
  (* Store *)
  | Store PC _ => fail "No spec rule for Store through PC:" instr
  | Store _ (inl _) =>
    (cont (@step_store_success_same) ||
     cont (@step_store_success_z))
  | Store ?r (inr ?r) =>
    (cont (@step_store_success_reg_same') ||
     cont (@step_store_success_reg_same))
  | Store _ (inr _) =>
    (cont (@step_store_success_reg_same_a) ||
     cont (@step_store_success_reg))
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
