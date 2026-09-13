From iris.proofmode Require Import coq_tactics.
From iris.bi Require Import bi.
Import bi.
From griotte Require Import rules instr_outcome_rules solve_pure machine_instructions.
From Ltac2 Require Import Ltac2 Option.
Set Default Proof Mode "Classic".

Ltac dispatch_Get r1 r2 cont :=
  let p := constr:((r1, r2)) in
  lazymatch p with
  | (_, PC) => cont (@wp_Get_PC_success)
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
  | (?dst, (inl _), (inr _)) =>
    (cont (@wp_binop_success_z_r) ||
     cont (@wp_binop_fail_z_r))
  | (?dst, (inr _), (inr _)) => cont (@wp_binop_success_r_r)
  | (?dst, (inl _), (inl _)) => cont (@wp_binop_success_z_z)
  end.

Ltac dispatch_instr_rule instr cont :=
  let instr := eval unfold register_file.regn, register_file.cst in instr in
  lazymatch instr with
  (* Mov *)
  | Mov PC (inr PC) => cont (@wp_move_success_reg_samePC)
  | Mov PC (inr _) => cont (@wp_move_success_reg_toPC)
  | Mov _ (inr PC) => cont (@wp_move_success_reg_fromPC)
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
  | GetTag PC PC => cont (@wp_GetTag_PC_failure)
  | GetTag PC cnull => cont (@wp_GetTag_cnull_toPC)
  | GetTag PC _ => cont (@wp_GetTag_toPC_failure)
  | GetTag cnull cnull => cont (@wp_GetTag_cnull)
  | GetTag cnull PC => cont (@wp_GetTag_PC_to_cnull)
  | GetTag cnull _ => cont (@wp_GetTag_to_cnull)
  | GetTag _ cnull => cont (@wp_GetTag_from_cnull)
  | GetTag ?r1 ?r2 => dispatch_Get r1 r2 cont
  (* ClearTag *)
  | ClearTag PC PC => cont (@wp_ClearTag_PC)
  | ClearTag PC cnull => cont (@wp_ClearTag_cnull_toPC)
  | ClearTag PC _ =>
    (cont (@wp_ClearTag_toPC) || cont (@wp_ClearTag_toPC_failure))
  | ClearTag cnull cnull => cont (@wp_ClearTag_cnull)
  | ClearTag cnull PC => cont (@wp_ClearTag_PC_to_cnull)
  | ClearTag cnull _ => cont (@wp_ClearTag_to_cnull)
  | ClearTag _ cnull => cont (@wp_ClearTag_from_cnull)
  | ClearTag _ PC => cont (@wp_ClearTag_fromPC)
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
  (* Lea *)
  | Lea PC (inr _) => cont (@wp_lea_success_reg_PC)
  | Lea PC (inl _) => cont (@wp_lea_success_z_PC)
  | Lea _ (inr _) => (cont (@wp_lea_success_reg) || cont (@wp_lea_success_reg_sr))
  | Lea _ (inl _) => (cont (@wp_lea_success_z) || cont (@wp_lea_success_z_sr))
  (* Load *)
  | Load PC _ => cont (@wp_load_success_PC)
  | Load _ PC => cont (@wp_load_success_fromPC)
  | Load ?r ?r =>
    (cont (@wp_load_success_same_notinstr) ||
     cont (@wp_load_success_same_frominstr))
  | Load _ _ =>
    (cont (@wp_load_success_notinstr) ||
     cont (@wp_load_success_frominstr))
  (* Store *)
  | Store PC (inl _) => cont (@wp_store_success_z_PC)
  | Store PC (inr PC) => cont (@wp_store_success_reg_PC_same_store_word)
  | Store PC (inr _) => cont (@wp_store_success_reg_PC_store_word)
  | Store _ (inl _) =>
    (cont (@wp_store_success_same) ||
     cont (@wp_store_success_z))
  (* | Store _ (inr PC) => *)
  (*   (cont (@wp_store_success_reg_frominstr_same) || *)
  (*    cont (@wp_store_success_reg_frominstr)) *)
  | Store ?r (inr ?r) =>
    (cont (@wp_store_success_reg_same'_store_word) ||
     cont (@wp_store_success_reg_same_store_word))
  | Store _ (inr _) =>
    (cont (@wp_store_success_reg_same_a_store_word) ||
     cont (@wp_store_success_reg_store_word))
  (* Jnz *)
  (* | Jnz PC PC => cont (@wp_jnz_success_jmpPC) *) (* FAIL *)
  | Jnz (inl _) PC => cont (@wp_jnz_success_jmpPC_z)
  | Jnz (inr _) PC => cont (@wp_jnz_success_jmpPC_reg)
  | Jnz (inl _) _ => (cont (@wp_jnz_success_next_z) || cont (@wp_jnz_success_jmp_z) )
  | Jnz (inr ?r) ?r => cont (@wp_jnz_success_jmp_same)
  | Jnz (inl _) _ => (cont (@wp_jnz_success_next_reg) || cont (@wp_jnz_success_jmp_reg) )
  (* Jmp *)
  | Jmp (inl _) => cont (@wp_jmp_success_z)
  | Jmp (inr _) => cont (@wp_jmp_success_reg)
  (* | Jmp (inr PC) => cont (@wp_jmp_success_z) *) (* FAIL *)
  (* Jalr *)
  | Jalr _ PC => cont (@wp_jalr_successPC)
  | Jalr cnull _ => cont (@wp_jalr_success_cnull)
  | Jalr ?r ?r => cont (@wp_jalr_success_rdst)
  | Jalr _ _ => cont (@wp_jalr_success)
  (* Subseg *)
  | Subseg PC (inr ?r) (inr ?r) => cont (@wp_subseg_success_pc_same)
  | Subseg PC (inr _) (inr _) => cont (@wp_subseg_success_pc)
  | Subseg PC (inl _) (inr _) => cont (@wp_subseg_success_pc_l)
  | Subseg PC (inr _) (inl _) => cont (@wp_subseg_success_pc_r)
  | Subseg PC (inl _) (inl _) => cont (@wp_subseg_success_pc_lr)
  | Subseg _ (inr ?r) (inr ?r) => (cont (@wp_subseg_success_same) || cont (@wp_subseg_success_same_sr)) (* TODO: improve using register values? *)
  | Subseg _ (inr _) (inr _) => (cont (@wp_subseg_success) || cont (@wp_subseg_success_sr))
  | Subseg _ (inl _) (inr _) => (cont (@wp_subseg_success_l) || cont (@wp_subseg_success_l_sr))
  | Subseg _ (inr _) (inl _) => (cont (@wp_subseg_success_r) || cont (@wp_subseg_success_r_sr))
  | Subseg _ (inl _) (inl _) => (cont (@wp_subseg_success_lr) || cont (@wp_subseg_success_lr_sr))
  (* Restrict *)
  | Restrict PC (inr _) => cont (@wp_restrict_success_reg_PC)
  | Restrict _ (inr _) => cont (@wp_restrict_success_reg)
  | Restrict PC (inl _) => cont (@wp_restrict_success_z_PC)
  | Restrict _ (inl _) => cont (@wp_restrict_success_z)
  (* Seal *)
  | Seal ?r ?r PC => cont (@wp_seal_PC_eq)
  | Seal _ _ PC => cont (@wp_seal_PC)
  | Seal ?r _ ?r => cont (@wp_seal_r2)
  | Seal ?r ?r _ => cont (@wp_seal_r1)
  | Seal _ _ _ => cont (@wp_seal_success)
  (* UnSeal *)
  | UnSeal PC _ _ => cont (@wp_unseal_PC)
  | UnSeal ?r _ ?r => cont (@wp_unseal_r2)
  | UnSeal ?r ?r _ => cont (@wp_unseal_r1)
  | UnSeal _ _ _ => cont (@wp_unseal_success)
  (* readsr *)
  | ReadSR PC _ => cont (@wp_readsr_success_toPC)
  | ReadSR _ _ => cont (@wp_readsr_success)
  (* writesr *)
  | WriteSR _ PC => cont (@wp_writesr_success_fromPC)
  | WriteSR _ _ => cont (@wp_writesr_success)
  (* Fail *)
  | Fail => cont (@wp_fail)
  (* Halt *)
  | Halt => cont (@wp_halt)
  (* not found *)
  | _ => fail "No suitable rule found for instruction" instr
  end.

(* Concrete maps share one owned entry for operand aliases, including PC and
   cnull. Reading cnull still requires its physical register resource. *)
(* Equality is an input to dispatch: never instantiate register operands or
   split symbolic alias cases to choose a rule. *)
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
  end.

Ltac instr_map_contains regs r :=
  lazymatch regs with
  | <[?rr := ?ww]> ?tail =>
    let eq := instr_same_register rr r in
    lazymatch eq with true => constr:(true) | false => instr_map_contains tail r end
  | _ => constr:(false)
  end.

Ltac instr_register_map rs :=
  lazymatch rs with
  | nil => constr:(∅ : Reg)
  | ?r :: ?rs =>
    let tail := instr_register_map rs in
    let found := instr_map_contains tail r in
    lazymatch found with
    | true => tail
    | false => match goal with
      | |- context [ Esnoc _ _ (?rr ↦ᵣ ?w)%I ] =>
        let eq := instr_same_register rr r in
        lazymatch eq with
        | true => constr:(<[rr := w]> tail : Reg)
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

Ltac instr_map instr :=
  let instr := eval cbv [regn cst] in instr in
  let rs := lazymatch instr with
    | Lea ?dst ?src => instr_argument_registers src constr:([PC; dst])
    | Restrict ?dst ?src => instr_argument_registers src constr:([PC; dst])
    | Subseg ?dst ?s1 ?s2 =>
      let rest := instr_argument_registers s2 constr:([PC; dst]) in
      instr_argument_registers s1 rest
    | Seal ?dst ?s1 ?s2 => constr:([PC; dst; s1; s2])
    | UnSeal ?dst ?s1 ?s2 => constr:([PC; dst; s1; s2])
    | Load ?dst ?src => constr:([PC; dst; src])
    | Store ?dst ?src => instr_argument_registers src constr:([PC; dst])
    | _ => eval vm_compute in (elements ({[PC]} ∪ regs_of instr))
    end in
  instr_register_map rs.

Ltac instr_expand_map_rule rule cont :=
  let expanded := constr:(ltac:(
    let H := fresh "Hrule" in
    pose proof rule as H;
    repeat match type of H with
    | context [big_sepM ?P (<[?rr := ?ww]> ?mm)] =>
      let Pnone := constr:(mm !! rr = None) in
      let Hnone := constr:(ltac:(rewrite ?lookup_insert ?lookup_empty;
                                 repeat case_decide; simplify_eq; done) : Pnone) in
      setoid_rewrite (big_sepM_insert P mm rr ww Hnone) in H
    end;
    try setoid_rewrite big_sepM_empty in H;
    try setoid_rewrite sep_emp in H;
    exact H)) in
  cont expanded.

Ltac dispatch_instr_failure instr cont :=
  let regs := instr_map instr in
  lazymatch goal with
  | |- context [ Esnoc _ _ (PC ↦ᵣ WCap true ?p ?g ?b ?e ?a)%I ] =>
    let rule := constr:(fun E => @wp_instr_failed _ _ _ E p g b e a
                         (encodeInstrW instr) instr regs) in
    instr_expand_map_rule rule cont
  end.

(* Read and update the concrete ownership map without unfolding word metadata. *)
Ltac instr_map_word regs r :=
  lazymatch regs with
  | <[?rr := ?ww]> ?tail =>
    let eq := instr_same_register rr r in
    lazymatch eq with true => ww | false => instr_map_word tail r end
  end.

Ltac instr_read regs r :=
  let null := instr_same_register r cnull in
  lazymatch null with true => constr:(WInt 0) | false => instr_map_word regs r end.

Ltac instr_argument regs arg :=
  let arg := eval cbv [regn cst] in arg in
  lazymatch arg with
  | inl ?n => n
  | inr ?r => let w := instr_read regs r in
              lazymatch w with WInt ?n => n end
  end.

Ltac instr_map_update regs r w :=
  lazymatch regs with
  | <[?rr := ?ww]> ?tail =>
    let eq := instr_same_register rr r in
    lazymatch eq with
    | true => constr:(<[rr := w]> tail : Reg)
    | false => let rest := instr_map_update tail r w in
               constr:(<[rr := ww]> rest : Reg)
    end
  end.

Ltac instr_result regs dst word :=
  let null := instr_same_register dst cnull in
  let written := lazymatch null with true => constr:(WInt 0) | false => word end in
  let updated := instr_map_update regs dst written in
  let pc := instr_map_word updated PC in
  lazymatch pc with
  | WCap ?t ?p ?g ?b ?e ?a =>
    instr_map_update updated PC (WCap t p g b e (a ^+ 1)%a)
  | _ => fail "The invalidated result cannot advance PC; use iInstr_fail"
  end.

Ltac instr_decode_cap n :=
  lazymatch n with
  | encodePermPair ?pair => pair
  | _ => match goal with
         | H : decodePermPair n = ?pair |- _ => pair
         | H : ?pair = decodePermPair n |- _ => pair
         | _ => constr:((fst (decodePermPair n), snd (decodePermPair n)))
         end
  end.

Ltac instr_decode_sr n :=
  lazymatch n with
  | encodeSealPermPair ?pair => pair
  | _ => match goal with
         | H : decodeSealPermPair n = ?pair |- _ => pair
         | H : ?pair = decodeSealPermPair n |- _ => pair
         | _ => constr:((fst (decodeSealPermPair n), snd (decodeSealPermPair n)))
         end
  end.

Ltac instr_endpoint convert n fallback :=
  lazymatch n with
  | finz.to_z ?a => a
  | _ => match goal with H : convert n = Some ?a |- _ => a
                         | _ => fallback end
  end.

Ltac dispatch_instr_invalidation instr cont :=
  let instr := eval cbv [regn cst] in instr in
  let regs := instr_map instr in
  let pc := instr_map_word regs PC in
  lazymatch pc with WCap true ?pp ?pg ?pb ?pe ?pa =>
  lazymatch instr with
  | Lea ?dst ?src =>
    let wd := instr_read regs dst in
    let n := instr_argument regs src in
    lazymatch wd with
    | WCap ?t ?p ?g ?b ?e ?a =>
      let result := instr_result regs dst (WCap false p g b e a) in
      let rule := constr:(fun E => @wp_lea_invalidated_cap _ _ _ E pp pg pb pe pa
                        (encodeInstrW instr) dst src regs result t p g b e a n) in
      instr_expand_map_rule rule cont
    | WSealRange ?t ?p ?g ?b ?e ?a =>
      let result := instr_result regs dst (WSealRange false p g b e a) in
      let rule := constr:(fun E => @wp_lea_invalidated_sr _ _ _ E pp pg pb pe pa
                        (encodeInstrW instr) dst src regs result t p g b e a n) in
      instr_expand_map_rule rule cont
    end
  | Restrict ?dst ?src =>
    let wd := instr_read regs dst in
    let n := instr_argument regs src in
    lazymatch wd with
    | WCap ?t ?p ?g ?b ?e ?a =>
      let pair := instr_decode_cap n in
      let p' := eval cbn in (fst pair) in
      let g' := eval cbn in (snd pair) in
      let result := instr_result regs dst (WCap false p' g' b e a) in
      let rule := constr:(fun E => @wp_restrict_invalidated_cap _ _ _ E pp pg pb pe pa
                        (encodeInstrW instr) dst src regs result t p g b e a n p' g') in
      instr_expand_map_rule rule cont
    | WSealRange ?t ?p ?g ?b ?e ?a =>
      let pair := instr_decode_sr n in
      let p' := eval cbn in (fst pair) in
      let g' := eval cbn in (snd pair) in
      let result := instr_result regs dst (WSealRange false p' g' b e a) in
      let rule := constr:(fun E => @wp_restrict_invalidated_sr _ _ _ E pp pg pb pe pa
                        (encodeInstrW instr) dst src regs result t p g b e a n p' g') in
      instr_expand_map_rule rule cont
    end
  | Seal ?dst ?src1 ?src2 =>
    let w1 := instr_read regs src1 in
    let w2 := instr_read regs src2 in
    lazymatch w1 with WSealRange ?t ?p ?g ?b ?e ?a =>
    lazymatch w2 with WSealable ?sb =>
      let result := instr_result regs dst (WSealed a (clear_tag_sealable sb)) in
      let rule := constr:(fun E => @wp_seal_invalidated _ _ _ E pp pg pb pe pa
                        (encodeInstrW instr) dst src1 src2 regs result t p g b e a sb) in
      instr_expand_map_rule rule cont
    end end
  | UnSeal ?dst ?src1 ?src2 =>
    let w1 := instr_read regs src1 in
    let w2 := instr_read regs src2 in
    lazymatch w1 with WSealRange ?t ?p ?g ?b ?e ?a =>
    lazymatch w2 with WSealed ?a' ?sb =>
      let word := eval cbn [clear_tag_sealable] in (WSealable (clear_tag_sealable sb)) in
      let result := instr_result regs dst word in
      let rule := constr:(fun E => @wp_unseal_invalidated _ _ _ E pp pg pb pe pa
                        (encodeInstrW instr) dst src1 src2 regs result t p g b e a a' sb) in
      instr_expand_map_rule rule cont
    end end
  | Subseg ?dst ?src1 ?src2 =>
    let wd := instr_read regs dst in
    let n1 := instr_argument regs src1 in
    let n2 := instr_argument regs src2 in
    lazymatch wd with
    | WCap ?t ?p ?g ?b ?e ?a =>
      first [
        let overflow := constr:(ltac:(first [left; solve_pure | right; solve_pure | assumption]) :
                                  z_to_addr n1 = None ∨ z_to_addr n2 = None) in
        let result := instr_result regs dst (WCap false p g b e a) in
        let rule := constr:(fun E => @wp_subseg_unrepresentable_cap _ _ _ E pp pg pb pe pa
                          (encodeInstrW instr) dst src1 src2 regs result t p g b e a n1 n2) in
        instr_expand_map_rule rule cont
      | let a1 := instr_endpoint constr:(z_to_addr) n1 ((0 ^+ n1)%a) in
        let a2 := instr_endpoint constr:(z_to_addr) n2 ((0 ^+ n2)%a) in
        let result := instr_result regs dst (WCap false p g a1 a2 a) in
        let rule := constr:(fun E => @wp_subseg_invalidated_cap _ _ _ E pp pg pb pe pa
                          (encodeInstrW instr) dst src1 src2 regs result t p g b e a n1 n2 a1 a2) in
        instr_expand_map_rule rule cont ]
    | WSealRange ?t ?p ?g ?b ?e ?a =>
      first [
        let overflow := constr:(ltac:(first [left; solve_pure | right; solve_pure | assumption]) :
                                  z_to_otype n1 = None ∨ z_to_otype n2 = None) in
        let result := instr_result regs dst (WSealRange false p g b e a) in
        let rule := constr:(fun E => @wp_subseg_unrepresentable_sr _ _ _ E pp pg pb pe pa
                          (encodeInstrW instr) dst src1 src2 regs result t p g b e a n1 n2) in
        instr_expand_map_rule rule cont
      | let a1 := instr_endpoint constr:(z_to_otype) n1 ((0 ^+ n1)%ot) in
        let a2 := instr_endpoint constr:(z_to_otype) n2 ((0 ^+ n2)%ot) in
        let result := instr_result regs dst (WSealRange false p g a1 a2 a) in
        let rule := constr:(fun E => @wp_subseg_invalidated_sr _ _ _ E pp pg pb pe pa
                          (encodeInstrW instr) dst src1 src2 regs result t p g b e a n1 n2 a1 a2) in
        instr_expand_map_rule rule cont ]
    end
  | _ => fail "iInstr_invalidate supports Lea, Restrict, Subseg, Seal, and UnSeal"
  end end.

Ltac solve_instr_map :=
  first [solve_pure | done | solve [left; solve_pure | right; solve_pure] |
    (rewrite ?decode_encode_permPair_inv ?decode_encode_SealPermPair_inv; done) |
    (rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver) |
    (rewrite /z_of_argument /lookup_reg ?lookup_insert ?lookup_empty;
     repeat case_decide; simplify_eq; done) |
    (rewrite /incrementPC /incrementPC_gen /insert_reg ?lookup_insert;
     repeat case_decide; simplify_eq; cbn [clear_tag_sealable];
     match goal with |- context [ (?a + 1)%a ] =>
       let Pincr := constr:((a + 1)%a = Some (a ^+ 1)%a) in
       let H := constr:(ltac:(solve_pure) : Pincr) in
       rewrite H /=
     end; apply f_equal; apply map_eq; intros;
     rewrite !lookup_insert; repeat case_decide; simplify_eq; done)].

Ltac instr_known_registers entries owned full Hincl :=
  lazymatch entries with
  | <[?r := ?w]> ?tail =>
    let Hlookup := fresh "Hreg" in
    assert (full !! r = Some w) as Hlookup by
      (apply (lookup_weaken owned full r w); [rewrite ?lookup_insert ?lookup_empty; repeat case_decide; simplify_eq; done | exact Hincl]);
    instr_known_registers tail owned full Hincl
  | _ => idtac
  end.

Ltac solve_instr_failure :=
  intros;
  match goal with
  | Hincl : ?owned ⊆ ?full |- _ =>
    instr_known_registers owned owned full Hincl
  end;
  rewrite /exec /exec_opt /= /word_of_argument /z_of_argument /lookup_reg;
  repeat match goal with
  | H : ?lhs = ?rhs |- context [?lhs] => progress (rewrite H; cbn)
  end;
  try (rewrite /updatePC /updatePC_gen /update_reg /reg /sreg /mem /= /insert_reg;
       rewrite ?lookup_insert /=; simplify_map_eq; rewrite ?lookup_insert /=);
  repeat match goal with
  | H : ?lhs = ?rhs |- context [?lhs] => progress (rewrite H; cbn)
  end;
  try done;
  try solve_pure.
