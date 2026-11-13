From iris.proofmode Require Import coq_tactics.
From iris.bi Require Import bi.
Import bi.
From griotte Require Import rules rules_regs solve_pure machine_instructions
  proofmode_instr_support.
From Ltac2 Require Import Ltac2 Option.
Set Default Proof Mode "Classic".

(** * The register steps in closed form

    An instruction with no dedicated case is stepped with a k-ary rule of
    [rules_regs.v]: [wp_regs_next_1] to [wp_regs_next_4] when its
    destination is owned, [wp_regs_jump_0] to [wp_regs_jump_3]
    when it is [cnull] or absent. The premise of the rule ([regs_next_ok]
    or [regs_jump_agree]) is the instruction's register step in closed
    form, found in the hint database [regs_next_ok_db]
    ([solve_regs_next_ok]), else a case lemma of [regs_next_ok_lax_db]
    whose undecided facts are left as side goals ([solve_regs_next_ok_lax]),
    or named by the client
    ([iInstr "H" using s], [proofmode.v]). The operands are read from the
    instruction term. *)

(* The register operands of [t], from its application spine: every argument
   of type [RegName] and every [inr r], in argument order, and the first
   argument of type [RegName] (the destination), if any. *)
Ltac instr_spine_operands t dst acc :=
  lazymatch t with
  | ?f ?x =>
      lazymatch type of x with
      | RegName =>
          let d := constr:(@Some RegName x) in
          let a := constr:(x :: acc) in
          instr_spine_operands f d a
      | (Z + RegName)%type =>
          lazymatch x with
          | inr ?r => let a := constr:(r :: acc) in instr_spine_operands f dst a
          | _ => instr_spine_operands f dst acc
          end
      | _ => instr_spine_operands f dst acc
      end
  | _ => constr:((dst, acc))
  end.

Ltac instr_spine_registers instr :=
  let d := constr:(@None RegName) in
  let a := constr:(@nil RegName) in
  instr_spine_operands instr d a.

(* The entry of the register [r] in a list of owned registers. *)
Ltac regs_find r regs :=
  lazymatch regs with
  | (?r', ?w) :: ?tail =>
      let eq := instr_same_register r' r in
      lazymatch eq with true => constr:((r', w)) | false => regs_find r tail end
  end.

(* The list of owned registers without the register [r]. *)
Ltac regs_remove r regs :=
  lazymatch regs with
  | nil => regs
  | (?r', ?w) :: ?tail =>
      let eq := instr_same_register r' r in
      lazymatch eq with
      | true => tail
      | false => let tail' := regs_remove r tail in constr:((r', w) :: tail')
      end
  end.

(* The search in [regs_next_ok_db], else the lax search in
   [regs_next_ok_lax_db], or the lemma [s] named by the client. *)
Ltac regs_next_ok_solver s instr :=
  lazymatch s with
  | tt =>
      first
        [ solve_regs_next_ok
        | solve_regs_next_ok_lax
        | fail "No lemma in regs_next_ok_db closes" instr
               "(name one with: iInstr ""H"" using <lemma>)" ]
  | _ => regs_next_ok_using s
  end.

(* The owned entry of [d] in [rs], if any. *)
Ltac regs_find_opt d rs :=
  match constr:(tt) with
  | _ => let e := regs_find d rs in constr:(Some e)
  | _ => constr:(@None (RegName * LWord))
  end.

(* Whether the owned destination [d] is known not to be [cnull], as the
   side goals of a rule are solved ([solve_pure_iinstr]). *)
Ltac regs_dst_not_cnull d :=
  match goal with
  | _ =>
      let _ := constr:(ltac:(solve [ltac2:(solve_pure_iinstr ())]) : d ≠ cnull) in
      constr:(true)
  | _ => constr:(false)
  end.

(* The k-ary register rule for the operands of [instr], its premise
   [regs_next_ok] (owned destination) or [regs_jump_agree] (destination
   [cnull], or none) proved first by the search in [regs_next_ok_db], or
   from the lemma [s] when it is not [tt]. *)
Ltac dispatch_next_ok_using s instr cont :=
  let instr' := eval unfold register_file.regn, register_file.cst in instr in
  let ops := instr_spine_registers instr' in
  lazymatch ops with (?dsto, ?rs) =>
  let regs := instr_register_words rs in
  let dst_entry := lazymatch dsto with
    | Some ?d => regs_find_opt d regs
    | None => constr:(@None (RegName * LWord))
    end in
  lazymatch goal with
  | |- context [ Esnoc _ _ (PC ↦ₚ Cap ?p ?g ?b ?e ?a @@? ?π)%I ] =>
    let Hsw := fresh "Hsw" in
    let Hok := fresh "Hregs_next_ok" in
    assert (∀ th, regs_instr_ok th instr') as Hsw
      by (let th := fresh "th" in intros th; rewrite /regs_instr_ok; by apply sw_of_none);
    lazymatch dst_entry with
    | Some (?dst, ?wd) =>
      let rest := regs_remove dst regs in
      (* A destination not known to differ from [cnull] keeps its word
         there: the rules [wp_regs_next_k_any_dst]. *)
      let dst_known := regs_dst_not_cnull dst in
      lazymatch rest with
      | [] =>
        eassert (regs_next_ok instr' p (Cap p g b e a @@? π) {[dst := wd]} dst _ 1) as Hok;
        [ regs_next_ok_solver s instr'
        | rewrite ?MkLWord_eta in Hok;
          lazymatch type of Hok with regs_next_ok _ _ _ _ _ ?v _ =>
            lazymatch dst_known with
            | true =>
              cont (fun E pc_a' dq Hdec Hvpc Hpc_a' Hdst =>
                      @wp_regs_next_1 _ _ _ _ _ E p g b e a π pc_a'
                        (encodeInstrW instr' @@? None) dq instr' dst wd v
                        Hdec (Hsw _) Hvpc Hpc_a' Hdst Hok)
            | false =>
              cont (fun E pc_a' dq Hdec Hvpc Hpc_a' =>
                      @wp_regs_next_1_any_dst _ _ _ _ _ E p g b e a π pc_a'
                        (encodeInstrW instr' @@? None) dq instr' dst wd v
                        Hdec (Hsw _) Hvpc Hpc_a' Hok)
            end
          end ]
      | [(?r2, ?w2)] =>
        eassert (dst ≠ r2 →
                 regs_next_ok instr' p (Cap p g b e a @@? π) (<[dst := wd]> (<[r2 := w2]> ∅))
                   dst _ 1) as Hok;
        [ regs_next_ok_solver s instr'
        | rewrite ?MkLWord_eta in Hok;
          lazymatch type of Hok with _ → regs_next_ok _ _ _ _ _ ?v _ =>
            lazymatch dst_known with
            | true =>
              cont (fun E pc_a' dq Hdec Hvpc Hpc_a' Hdst =>
                      @wp_regs_next_2 _ _ _ _ _ E p g b e a π pc_a'
                        (encodeInstrW instr' @@? None) dq instr' dst wd r2 w2 v
                        Hdec (Hsw _) Hvpc Hpc_a' Hdst Hok)
            | false =>
              cont (fun E pc_a' dq Hdec Hvpc Hpc_a' =>
                      @wp_regs_next_2_any_dst _ _ _ _ _ E p g b e a π pc_a'
                        (encodeInstrW instr' @@? None) dq instr' dst wd r2 w2 v
                        Hdec (Hsw _) Hvpc Hpc_a' Hok)
            end
          end ]
      | [(?r2, ?w2); (?r3, ?w3)] =>
        eassert (dst ≠ r2 → dst ≠ r3 → r2 ≠ r3 →
                 regs_next_ok instr' p (Cap p g b e a @@? π)
                   (<[dst := wd]> (<[r2 := w2]> (<[r3 := w3]> ∅))) dst _ 1) as Hok;
        [ regs_next_ok_solver s instr'
        | rewrite ?MkLWord_eta in Hok;
          lazymatch type of Hok with _ → _ → _ → regs_next_ok _ _ _ _ _ ?v _ =>
            lazymatch dst_known with
            | true =>
              cont (fun E pc_a' dq Hdec Hvpc Hpc_a' Hdst =>
                      @wp_regs_next_3 _ _ _ _ _ E p g b e a π pc_a'
                        (encodeInstrW instr' @@? None) dq instr' dst wd r2 w2 r3 w3 v
                        Hdec (Hsw _) Hvpc Hpc_a' Hdst Hok)
            | false =>
              cont (fun E pc_a' dq Hdec Hvpc Hpc_a' =>
                      @wp_regs_next_3_any_dst _ _ _ _ _ E p g b e a π pc_a'
                        (encodeInstrW instr' @@? None) dq instr' dst wd r2 w2 r3 w3 v
                        Hdec (Hsw _) Hvpc Hpc_a' Hok)
            end
          end ]
      | [(?r2, ?w2); (?r3, ?w3); (?r4, ?w4)] =>
        eassert (dst ≠ r2 → dst ≠ r3 → dst ≠ r4 → r2 ≠ r3 → r2 ≠ r4 → r3 ≠ r4 →
                 regs_next_ok instr' p (Cap p g b e a @@? π)
                   (<[dst := wd]> (<[r2 := w2]> (<[r3 := w3]> (<[r4 := w4]> ∅)))) dst _ 1)
          as Hok;
        [ regs_next_ok_solver s instr'
        | rewrite ?MkLWord_eta in Hok;
          lazymatch type of Hok with _ → _ → _ → _ → _ → _ → regs_next_ok _ _ _ _ _ ?v _ =>
            cont (fun E pc_a' dq Hdec Hvpc Hpc_a' Hdst =>
                    @wp_regs_next_4 _ _ _ _ _ E p g b e a π pc_a'
                      (encodeInstrW instr' @@? None) dq instr' dst wd r2 w2 r3 w3 r4 w4 v
                      Hdec (Hsw _) Hvpc Hpc_a' Hdst Hok)
          end ]
      end
    | None =>
      lazymatch regs with
      | [] =>
        eassert (regs_jump_agree instr' p (Cap p g b e a @@? π) ∅ _) as Hok;
        [ regs_next_ok_solver s instr'
        | lazymatch type of Hok with regs_jump_agree _ _ _ _ ?n =>
            cont (fun E pc_a' dq Hdec Hvpc Hpc_a' =>
                    @wp_regs_jump_0 _ _ _ _ _ E p g b e a π
                      (encodeInstrW instr' @@? None) dq instr' n (Cap p g b e pc_a' @@? π)
                      Hdec (Hsw _) Hvpc
                      (incrementPC_gen_add true p g b e a pc_a' π n Hpc_a') Hok)
          end ]
      | [(?r1, ?w1)] =>
        eassert (regs_jump_agree instr' p (Cap p g b e a @@? π) {[r1 := w1]} _) as Hok;
        [ regs_next_ok_solver s instr'
        | lazymatch type of Hok with regs_jump_agree _ _ _ _ ?n =>
            cont (fun E pc_a' dq Hdec Hvpc Hpc_a' =>
                    @wp_regs_jump_1 _ _ _ _ _ E p g b e a π
                      (encodeInstrW instr' @@? None) dq instr' r1 w1 n
                      (Cap p g b e pc_a' @@? π) Hdec (Hsw _) Hvpc
                      (incrementPC_gen_add true p g b e a pc_a' π n Hpc_a') Hok)
          end ]
      | [(?r1, ?w1); (?r2, ?w2)] =>
        eassert (r1 ≠ r2 →
                 regs_jump_agree instr' p (Cap p g b e a @@? π)
                   (<[r1 := w1]> (<[r2 := w2]> ∅)) _) as Hok;
        [ regs_next_ok_solver s instr'
        | lazymatch type of Hok with _ → regs_jump_agree _ _ _ _ ?n =>
            cont (fun E pc_a' dq Hdec Hvpc Hpc_a' =>
                    @wp_regs_jump_2 _ _ _ _ _ E p g b e a π
                      (encodeInstrW instr' @@? None) dq instr' r1 w1 r2 w2 n
                      (Cap p g b e pc_a' @@? π) Hdec (Hsw _) Hvpc
                      (incrementPC_gen_add true p g b e a pc_a' π n Hpc_a') Hok)
          end ]
      | [(?r1, ?w1); (?r2, ?w2); (?r3, ?w3)] =>
        eassert (r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 →
                 regs_jump_agree instr' p (Cap p g b e a @@? π)
                   (<[r1 := w1]> (<[r2 := w2]> (<[r3 := w3]> ∅))) _) as Hok;
        [ regs_next_ok_solver s instr'
        | lazymatch type of Hok with _ → _ → _ → regs_jump_agree _ _ _ _ ?n =>
            cont (fun E pc_a' dq Hdec Hvpc Hpc_a' =>
                    @wp_regs_jump_3 _ _ _ _ _ E p g b e a π
                      (encodeInstrW instr' @@? None) dq instr' r1 w1 r2 w2 r3 w3 n
                      (Cap p g b e pc_a' @@? π) Hdec (Hsw _) Hvpc
                      (incrementPC_gen_add true p g b e a pc_a' π n Hpc_a') Hok)
          end ]
      end
    end;
    try clear Hok; try clear Hsw
  end end.

Ltac dispatch_next_ok instr cont := dispatch_next_ok_using constr:(tt) instr cont.

Ltac dispatch_instr_rule instr cont :=
  let instr := eval unfold register_file.regn, register_file.cst in instr in
  lazymatch instr with
  (* GetTag: the rule with the dereference witness; the cnull forms through
     the register steps in closed form *)
  | GetTag cnull _ => dispatch_next_ok instr cont
  | GetTag _ cnull => dispatch_next_ok instr cont
  | GetTag _ _ => cont (@wp_gettag_success)
  (* CLoad *)
  | CLoad ?r ?r 0 =>
    (cont (fun MP Σ ceriseg th CL E r1 pc_p pc_g pc_b pc_e pc_a pc_π w w' =>
       @wp_load_success_same_notinstr MP Σ ceriseg th CL E r1 pc_p pc_g pc_b pc_e pc_a pc_π w w'
         (WInt 0 @@? None)) ||
     cont (@wp_load_success_same_frominstr))
  | CLoad _ _ 0 =>
    (cont (@wp_load_success_notinstr) ||
     cont (@wp_load_success_frominstr))
  (* Store *)
  | Store _ (inl _) 0 =>
    (cont (fun MP Σ ceriseg th CL E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst z =>
       @wp_store_success_same MP Σ ceriseg th CL E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst z
         (WInt 0 @@? None)) ||
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
  (* Jalr *)
  (* Jalr: the rules at the core link, else the posture forms at a link with
     a routing law (the posture moves with the MIE fragment and [held]). *)
  | Jalr cnull _ =>
    (cont (@wp_jalr_success_cnull) || cont (@wp_jalr_success_cnull_posture))
  | Jalr cra cra =>
    (cont (@wp_jalr_success_call_same) || cont (@wp_jalr_success_call_same_posture))
  | Jalr cra _ => (cont (@wp_jalr_success_call) || cont (@wp_jalr_success_call_posture))
  | Jalr ?r ?r => cont (@wp_jalr_success_rdst)
  | Jalr _ _ => cont (@wp_jalr_success)
  (* SpecialRW on mtdc, before the generic cases: its own ghost state. A
     write transfers the clause of the mtdc token: the ghost value comes
     back to the home value, is kept, leaves the home value, or moves
     between other values, in this order (see [instr_commit_lint]). *)
  | SpecialRW _ mtdc (inr cnull) => cont (@wp_readsr_mtdc)
  | SpecialRW cnull mtdc (inr _) =>
    (cont (@wp_writesr_mtdc_close) || cont (@wp_writesr_mtdc_keep) ||
     cont (@wp_writesr_mtdc_open) || cont (@wp_writesr_mtdc_ex))
  | SpecialRW cnull mtdc (inl _) =>
    (cont (@wp_specialrw_imm_mtdc_close) || cont (@wp_specialrw_imm_mtdc_keep) ||
     cont (@wp_specialrw_imm_mtdc_open) || cont (@wp_specialrw_imm_mtdc_ex))
  | SpecialRW ?r mtdc (inr ?r) =>
    (cont (@wp_specialrw_swap_mtdc_close) || cont (@wp_specialrw_swap_mtdc_keep) ||
     cont (@wp_specialrw_swap_mtdc_open) || cont (@wp_specialrw_swap_mtdc_ex))
  (* SpecialRW: readsr, writesr, csrw with an immediate, swaps *)
  | SpecialRW _ _ (inr cnull) => cont (@wp_readsr_success)
  | SpecialRW cnull _ (inr _) => cont (@wp_writesr_success)
  | SpecialRW cnull _ (inl _) => cont (@wp_specialrw_imm_success)
  | SpecialRW ?r _ (inr ?r) => cont (@wp_specialrw_swap)
  | SpecialRW _ _ (inr _) => cont (@wp_specialrw_success)
  (* SetMIE: csrsi and csrci on mstatus *)
  | SetMIE _ => (cont (@wp_setmie_success) || cont (@wp_setmie_success_posture))
  (* Mret *)
  | Mret => cont (@wp_mret_success)
  (* Ecall: the exception entry, at the core link *)
  | Ecall => cont (@wp_ecall)
  (* Fail *)
  | Fail => cont (@wp_fail)
  (* Halt *)
  | Halt => cont (@wp_halt)
  (* The register steps in closed form, else not found *)
  | _ =>
    first
      [ dispatch_next_ok instr cont
      | fail "No suitable rule found for instruction" instr ]
  end.

Ltac dispatch_generic_failure instr cont :=
  let regs := instr_failure_registers instr in
  lazymatch goal with
  | |- context [ Esnoc _ _ (PC ↦ₚ Cap ?p ?g ?b ?e ?a @@? ?π)%I ] =>
    lazymatch regs with
    | [] => cont (fun E => @wp_instr_faulted_0 _ _ _ _ _ E p g b e a π
                            (encodeInstrW instr @@? None) instr)
    | [(?r1, ?w1)] => cont (fun E => @wp_instr_faulted_1 _ _ _ _ _ E p g b e a π
                                     (encodeInstrW instr @@? None) instr r1 w1)
    | [(?r1, ?w1); (?r2, ?w2)] =>
        cont (fun E => @wp_instr_faulted_2 _ _ _ _ _ E p g b e a π
                         (encodeInstrW instr @@? None) instr r1 w1 r2 w2)
    | [(?r1, ?w1); (?r2, ?w2); (?r3, ?w3)] =>
        cont (fun E => @wp_instr_faulted_3 _ _ _ _ _ E p g b e a π
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
  | _ => fail "No invalidation rule found for instruction" instr
  end.
