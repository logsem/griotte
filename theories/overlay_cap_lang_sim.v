From cap_machine.overlay Require Import base lang.
From cap_machine Require Import cap_lang simulation linking region machine_run.
From cap_machine.rules Require rules_base.
From stdpp Require Import base gmap fin_maps list.
From Coq Require Import Eqdep_dec.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section overlay_to_cap_lang.

  (* TODO: update solve_addr *)
  Lemma ltb_addr_spec:
    forall a1 a2,
      ltb_addr a1 a2 = true <-> (a1 < a2)%a.
  Proof.
    intros; unfold ltb_addr, lt_addr. eapply Z.ltb_lt.
  Qed.

  Lemma leb_addr_spec:
    forall a1 a2,
      leb_addr a1 a2 = true <-> (a1 <= a2)%a.
  Proof.
    intros; unfold leb_addr, le_addr. eapply Z.leb_le.
  Qed.

  Lemma all_registers_correct:
    forall r, r ∈ all_registers.
  Proof.
    rewrite /all_registers.
    destruct r.
    - do 32 (apply elem_of_cons; right).
        by apply elem_of_list_singleton.
    - induction n.
      + apply elem_of_cons; left.
        apply f_equal. apply eq_proofs_unicity. decide equality.
      + apply elem_of_list_lookup_2 with (S n).
        repeat (destruct n;
                first (simpl;do 2 f_equal;apply eq_proofs_unicity;decide equality)).
        simpl in *. inversion fin.
  Qed.

  Lemma all_registers_s_correct:
    forall r, r ∈ (@list_to_set _ (gset RegName) _ _ _ all_registers).
  Proof.
    intros; rewrite elem_of_list_to_set.
    apply all_registers_correct.
  Qed.

  Definition translate_word (w: base.Word): Word :=
    match w with
    | inl n => inl n
    | inr c => match c with
              | Regular c => inr c
              | Stk d p b e a => inr (p, Directed, b, e, a)
              | Ret b e a => inr (E, Directed, b, e, a)
              end
    end.

  Lemma isCorrectPC_translate_word:
    forall w,
      lang.isCorrectPC w ->
      isCorrectPC (translate_word w).
  Proof.
    intros; inv H; simpl; econstructor; eauto.
  Qed.

  Lemma decodeInstrW_translate_word `{MachineParameters}:
    forall w,
      decodeInstrW' w = decodeInstrW (translate_word w).
  Proof.
    destruct w; simpl; auto.
    destruct c; simpl; auto.
  Qed.

  Lemma translate_word_cap:
    forall c,
      exists c', translate_word (inr c) = inr c'.
  Proof.
    simpl; destruct c; eauto.
  Qed.

  Definition compile (c: overlay_component): machine_component :=
    match c with
    | Lib _ _ _ _ (ms, imp, exp) => Lib _ _ _ _ (@fmap (gmap Addr) _ base.Word Word translate_word ms, imp, fmap translate_word exp)
    | Main _ _ _ _ (ms, imp, exp) c_main => Main _ _ _ _ (@fmap (gmap Addr) _ base.Word Word translate_word ms, imp, fmap translate_word exp) (translate_word c_main)
    end.

  Variables b_stk e_stk: Addr.
  Variable stk_pos: (b_stk < e_stk)%a.
  Context `{MachineParameters}.

  Inductive sim_flag: lang.ConfFlag -> ConfFlag -> Prop :=
  | sim_flag_exec:
      sim_flag lang.Executable Executable
  | sim_flag_halted:
      sim_flag lang.Halted Halted
  | sim_flag_failed:
      sim_flag lang.Failed Failed
  | sim_flag_next:
      sim_flag lang.NextI NextI.

  Lemma sim_flag_determ:
    forall f1 f2 f2',
      sim_flag f1 f2 ->
      sim_flag f1 f2' ->
      f2 = f2'.
  Proof.
    intros; inv H0; inv H1; auto.
  Qed.

  Inductive sim_expr: lang.expr -> expr -> Prop :=
  | sim_expr_instr_failed:
      sim_expr (lang.Instr lang.Failed) (Instr Failed)
  | sim_expr_instr_halted:
      sim_expr (lang.Instr lang.Halted) (Instr Halted)
  | sim_expr_seq:
      forall f1 f2,
        sim_flag f1 f2 ->
        sim_expr (lang.Seq (lang.Instr f1)) (Seq (Instr f2)).

  Lemma sim_expr_determ:
    forall e1 e2 e2',
      sim_expr e1 e2 ->
      sim_expr e1 e2' ->
      e2 = e2'.
  Proof.
    intros e1 e2 e2' A B; inv A; inv B; auto.
    f_equal. f_equal. eapply sim_flag_determ; eauto.
  Qed.

  Lemma cons_is_app:
    forall K (a: lang.ectx_item), a :: K = K ++ [a].
  Proof.
    induction K.
    - reflexivity.
    - simpl. intros; destruct a, a0.
      rewrite IHK. reflexivity.
  Qed.

  Lemma sim_expr_exec_inv:
    forall K,
      sim_expr (fill K (lang.Instr lang.Executable)) (@ectx_language.fill cap_ectx_lang (map (fun _ => SeqCtx) K) (Instr Executable)) ->
      K = [lang.SeqCtx].
  Proof.
    destruct K.
    - simpl; inversion 1.
    - rewrite (cons_is_app K e) /fill /= map_app !ectxi_language.fill_app.
      destruct e; simpl. inversion 1.
      destruct K; [reflexivity|].
      exfalso. rewrite (cons_is_app K e) /fill /= ectxi_language.fill_app in H1.
      destruct e; simpl in H1. inv H1.
  Qed.

  Lemma sim_expr_next_inv:
    forall K,
      sim_expr (fill K (lang.Instr lang.NextI)) (@ectx_language.fill cap_ectx_lang (map (fun _ => SeqCtx) K) (Instr NextI)) ->
      K = [lang.SeqCtx].
  Proof.
    destruct K.
    - simpl; inversion 1.
    - rewrite (cons_is_app K e) /fill /= map_app !ectxi_language.fill_app.
      destruct e; simpl. inversion 1.
      destruct K; [reflexivity|].
      exfalso. rewrite (cons_is_app K e) /fill /= ectxi_language.fill_app in H1.
      destruct e; simpl in H1. inv H1.
  Qed.

  Lemma fill_inv_instr:
    forall K cf e1,
      ectxi_language.fill K e1 = lang.Instr cf ->
      K = [] /\ e1 = lang.Instr cf.
  Proof.
    destruct K; [simpl; auto|].
    rewrite (cons_is_app K e) /fill /=.
    intros. rewrite ectxi_language.fill_app in H0.
    destruct e; simpl in H0; inv H0.
  Qed.

  Lemma z_of_argument_inv_Some:
    forall reg arg n,
      lang.z_of_argument reg arg = Some n ->
      (arg = inl n) \/ (exists r, arg = inr r /\ reg !! r = Some (inl n)).
  Proof.
    destruct arg; simpl; intros.
    - inv H0; left; auto.
    - right; exists r; split; auto.
      destruct (reg !! r); inv H0; auto.
      destruct s; inv H2; auto.
  Qed.

  Lemma z_of_argument_inv_None:
    forall reg arg,
      (forall r, is_Some (reg !! r)) ->
      lang.z_of_argument reg arg = None ->
      (exists r c, arg = inr r /\ reg !! r = Some (inr c)).
  Proof.
    destruct arg; simpl; intros; try congruence.
    exists r. generalize (H0 r); intro A.
    destruct (reg !! r); inv H1.
    destruct s; inv H3; eauto.
    inv A; congruence.
  Qed.

  Definition incrementPC (regs: base.Reg) : option base.Reg :=
    match regs !! PC with
    | Some (inr (Regular ((p, g), b, e, a))) =>
      match (a + 1)%a with
      | Some a' =>
        match p with
        | E | URWLX | URWX | URWL | URW => None
        | _ => Some (<[ PC := inr (Regular ((p, g), b, e, a')) ]> regs)
        end
      | None => None
      end
    | Some (inr (Stk d p b e a)) =>
      match (a + 1)%a with
      | Some a' =>
        match p with
        | E | URWLX | URWX | URWL | URW => None
        | _ => Some (<[ PC := inr (Stk d p b e a') ]> regs)
        end
      | None => None
      end
    | _ => None
    end.

  Lemma incrementPC_is_Some:
    forall r1 r2,
      incrementPC r1 = Some r2 ->
      forall x, is_Some (r1 !! x) <-> is_Some (r2 !! x).
  Proof.
    rewrite /incrementPC. intros.
    destruct (r1 !! PC) eqn:X; [|inv H0].
    destruct s; inv H0.
    destruct c; inv H2.
    - destruct c as [ [ [ [p' g'] b'] e'] a'].
      destruct (a' + 1)%a; inv H1.
      destruct (reg_eq_dec x PC).
      + subst x. destruct p'; try congruence; inv H2; rewrite lookup_insert X; split; intro; eauto.
      + destruct p'; try congruence; inv H2; rewrite lookup_insert_ne; auto.
    - destruct (a1 + 1)%a; inv H1.
      destruct (reg_eq_dec x PC).
      + subst x. destruct p; try congruence; inv H2; rewrite lookup_insert X; split; intro; eauto.
      + destruct p; try congruence; inv H2; rewrite lookup_insert_ne; auto.
  Qed.

  Lemma incrementPC_inv_Some:
    forall r1 r2,
      incrementPC r1 = Some r2 ->
      match r1 !! PC with
      | Some (inr (Regular (p, g, b, e, a))) => exists a', (a + 1)%a = Some a' /\ r2 = <[PC := inr (Regular (p, g, b, e, a'))]> r1 /\ (p <> E /\ p <> URWLX /\ p <> URWX /\ p <> URWL /\ p <> URW)
      | Some (inr (Stk d p b e a)) => exists a', (a + 1)%a = Some a' /\ r2 = <[PC := inr (Stk d p b e a')]> r1  /\ (p <> E /\ p <> URWLX /\ p <> URWX /\ p <> URWL /\ p <> URW)
      | _ => False
      end.
  Proof.
    intros. rewrite /incrementPC in H0.
    destruct (r1 !! PC) as [wpc|] eqn:HPC; [|congruence].
    destruct wpc; [congruence|].
    destruct c.
    - destruct c as [ [ [ [p g] b] e] a].
      destruct (a + 1)%a; [|congruence].
      destruct p; inv H0; eexists; repeat split; eauto.
    - destruct (a1 + 1)%a; [|congruence].
      destruct p; inv H0; eexists; repeat split; eauto.
    - congruence.
  Qed.

  Lemma incrementPC_fail_updatePC regs h stk cs :
   incrementPC regs = None ->
   lang.updatePC (regs, h, stk, cs) = (lang.Failed, (regs, h, stk, cs)).
  Proof.
   rewrite /incrementPC /lang.updatePC /base.RegLocate /=.
   destruct (regs !! PC) as [X|]; auto.
   destruct X; auto. destruct c as [ [ [ [ [p g] b] e] a] | ? | ?]; auto.
   destruct (a + 1)%a; auto; destruct p; try congruence; auto.
   destruct (a1 + 1)%a; auto; destruct p; try congruence; auto.
  Qed.

  Lemma incrementPC_success_updatePC regs regs' h stk cs :
    incrementPC regs = Some regs' ->
    lang.updatePC (regs, h, stk, cs) = (lang.NextI, (regs', h, stk, cs)).
  Proof.
    rewrite /incrementPC /lang.updatePC /update_reg /base.RegLocate /=.
    destruct (regs !! PC) as [X|] eqn:?; auto; try congruence; [].
    destruct X; try congruence. destruct c as [ [ [ [ [p g] b] e] a] | ? | ?]; try congruence.
    destruct (a + 1)%a eqn:?; [| congruence]. destruct p; try congruence; inversion 1; subst regs';
    do 6 eexists; repeat split; auto.
    destruct (a1 + 1)%a eqn:?; [| congruence]. destruct p; try congruence; inversion 1; subst regs';
    do 6 eexists; repeat split; auto.
  Qed.

  Notation incrementPC' := rules_base.incrementPC.

  Lemma incrementPC_success_incrementPC' regs1 regs1' regs2 w:
    regs1 !! PC = Some w ->
    regs2 !! PC = Some (translate_word w) ->
    incrementPC regs1 = Some regs1' ->
    exists regs2', incrementPC' regs2 = Some regs2'.
  Proof.
    intros Hw Hw'. rewrite /incrementPC /incrementPC' Hw Hw'.
    destruct w; try congruence.
    destruct c as [ [ [ [ [p g] b] e] a] | ? | ?]; try congruence.
    - simpl; destruct (a + 1)%a eqn:?; [| congruence]. destruct p; try congruence; eauto.
    - simpl; destruct (a1 + 1)%a eqn:?; [| congruence]. destruct p; try congruence; eauto.
  Qed.

  Lemma incrementPC_fail_incrementPC' regs1 regs2 w:
    regs1 !! PC = Some w ->
    regs2 !! PC = Some (translate_word w) ->
    incrementPC regs1 = None ->
    incrementPC' regs2 = None.
  Proof.
    intros Hw Hw'. rewrite /incrementPC /incrementPC' Hw Hw'.
    destruct w; simpl; auto.
    destruct c as [ [ [ [ [p g] b] e] a1] | ? | ?]; simpl; auto;
    destruct (a1 + 1)%a; try congruence; auto; destruct p; try congruence; auto.
  Qed.

  Definition word_of_argument (regs: base.Reg) (a: Z + RegName): base.Word :=
    match a with
    | inl n => inl n
    | inr r => base.RegLocate regs r
    end.

  Fixpoint flag_of_expr (e: lang.expr) :=
    match e with
    | lang.Instr f => f
    | lang.Seq e => flag_of_expr e
    end.

  Definition can_step (e: lang.expr): Prop :=
    flag_of_expr e = lang.Executable \/ flag_of_expr e = lang.NextI.

  Lemma can_step_fill:
    forall K e, can_step (fill K e) = can_step e.
  Proof.
    induction K; simpl; auto.
    intros. destruct a. simpl.
    rewrite IHK. rewrite /can_step /=. reflexivity.
  Qed.

  Definition activation_code: list base.Word :=
    [ inl (encodeInstr (Mov (R 1 eq_refl) (inr PC)))
    ; inl (encodeInstr (Lea (R 1 eq_refl) (inl (-1)%Z)))
    ; inl (encodeInstr (Load call.r_stk (R 1 eq_refl)))]
    ++ List.map inl call.pop_env_instrs
    ++ [ inl (encodeInstr (LoadU PC call.r_stk (inl (- 1)%Z)))].

  Lemma activation_code_length:
    length activation_code = 66.
  Proof.
    rewrite /activation_code !app_length map_length call.pop_env_instrs_length /=.
    reflexivity.
  Qed.

  Definition is_return (stk: base.Mem) a e: Prop :=
    forall i,
      i < 66 ->
      exists ai, (a + i)%a = Some ai /\
                 (ai < e)%a /\
                 activation_code !! i = stk !! ai.

  Definition interp (w: base.Word) (h: base.Mem) (stk: base.Mem) (cs: list Stackframe): Prop :=
    match w with
    | inl n => True
    | inr (Regular _) => lang.pwlW w = false /\ lang.can_address_only w (dom _ h)
    | inr (Stk d p b e a) => d = length cs /\ (e <= e_stk)%a /\ (forall d' stk', stack d' cs = Some stk' -> forall a', is_Some (stk' !! a') -> (a' < b)%a) /\ forall x, (b <= x < addr_reg.min e (lang.canReadUpTo w))%a -> exists w, stk !! x = Some w
    | inr (Ret b e a) => match cs with
                         | [] => False
                         | (reg', stk')::cs' =>
                            exists e_stk' a_stk,
                              reg' !! call.r_stk = Some (inr (Stk (length cs') URWLX b e_stk' ^(a_stk + 1)%a)) /\
                              (a_stk + 33)%a = Some a /\
                              (exists pcp pcg pcb pce pca, reg' !! PC = Some (inr (Regular (pcp, pcg, pcb, pce, pca))) /\ (pcp = RX \/ pcp = RWX \/ pcp = RWLX) /\
                              exists pcam1, stk' !! a_stk = Some (inr (Regular (pcp, pcg, pcb, pce, pcam1))) /\ (pcam1 + 1)%a = Some pca) /\
                              (b <= a_stk < e)%a /\
                              (e <= e_stk')%a /\
                              (e_stk <= e_stk)%a /\
                              (forall i, i < 31 -> exists ri, ((list_difference all_registers [PC; call.r_stk]) !! i) = Some ri /\ stk' !! ^(a_stk + (S i))%a = reg' !! ri) /\
                              stk' !! ^(a_stk + 32)%a = Some (inr (Stk (length cs') URWLX b e_stk' ^(a_stk + 32)%a)) /\
                              is_return stk' a e
                         end
    end.

  Lemma interp_updatePcPerm_regular:
    forall c h stk cs,
      interp (inr (Regular c)) h stk cs ->
      forall stk' cs', interp (lang.updatePcPerm (inr (Regular c))) h stk' cs'.
  Proof.
    destruct c as [ [ [ [p g] b] e] a]; intros.
    simpl. simpl in H0. destruct p; auto.
  Qed.

  Lemma interp_call_preserved:
    forall w h stk cs,
      is_safe w ->
      interp w h stk cs ->
      forall new_stk reg' stk',
        interp w h new_stk ((reg', stk')::cs).
  Proof.
    destruct w; auto.
    destruct c; simpl; intros; auto.
    - inv H0.
    - inv H0.
  Qed.

  Lemma interp_heap_extend:
    forall w x y h stk cs,
      interp w h stk cs ->
      interp w (<[x:=y]> h) stk cs.
  Proof.
    intros. destruct w; auto.
    destruct c; auto.
    simpl in H0. simpl. destruct H0.
    split; auto.
    destruct c as [ [ [ [p g] b] e] a].
    intros. apply H1 in H2. set_solver.
  Qed.

  Lemma interp_stack_extend:
    forall w x y h stk cs,
      interp w h stk cs ->
      interp w h (<[x:=y]> stk) cs.
  Proof.
    intros. destruct w; auto.
    destruct c; auto.
    simpl in H0. simpl. destruct H0 as [? [? [? ?] ] ].
    do 3 (split; auto).
    intros. apply H3 in H4.
    destruct (addr_eq_dec x x0); [subst x0; rewrite lookup_insert; eauto|rewrite lookup_insert_ne; auto].
  Qed.

  (* w is legally stored at address a *)
  Definition canBeStored (w: base.Word) (a: Addr): Prop :=
    lang.canStoreU URWLX a w = true.

  Inductive sim_cs: bool -> base.Mem -> list Stackframe -> machine_base.Mem -> Prop :=
  | sim_cs_nil:
      forall b h m,
        sim_cs b h [] m
  | sim_cs_cons_true:
      forall reg stk cs h m
        (Hregsdef: forall r, exists w, reg !! r = Some w /\ interp w h stk cs)
        (Hstkdisjheap: forall a, is_Some (stk !! a) -> (a < e_stk)%a)
        (Hstksim: forall a w, stk !! a = Some w -> m !! a = Some (translate_word w) /\ interp w h stk cs /\ canBeStored w a)
        (Hcs: sim_cs true h cs m),
        sim_cs true h ((reg, stk)::cs) m
 | sim_cs_cons_false:
      (* false indicates topmost frame *)
      forall reg stk cs h m
        (Hregsdef: forall r, exists w, reg !! r = Some w /\ interp w h stk cs)
        (Hstkdisjheap: forall a, is_Some (stk !! a) -> (a < e_stk)%a)
        (Hstksim: forall a w, stk !! a = Some w -> m !! a = Some (translate_word w) /\ interp w h stk cs /\ canBeStored w a)
        (Hcs: sim_cs true h cs m),
        sim_cs false h ((reg, stk)::cs) m.

  Lemma sim_cs_heap_extend:
    forall cs h m a wa,
      (e_stk <= a)%a ->
      sim_cs true h cs m ->
      sim_cs true (<[a:=wa]> h) cs (<[a:=translate_word wa]> m).
  Proof.
    induction cs; intros; auto.
    - econstructor.
    - inv H1. econstructor; eauto.
      + intros. destruct (Hregsdef r) as [wr [Hwr ?] ].
        eexists; split; eauto. apply interp_heap_extend; auto.
      + intros. generalize (Hstkdisjheap a ltac:(eexists; apply H1)). intro D.
        generalize (Hstksim _ _ H1). intro T.
        destruct T as [? [? ?] ].
        split; [|split; [apply interp_heap_extend; auto|auto] ].
        rewrite lookup_insert_ne; auto.
        clear -H0 D; solve_addr.
  Qed.

  Lemma stack_cons_length:
    forall cs reg stk,
      stack (length cs) ((reg, stk)::cs) = Some stk.
  Proof.
    intros; rewrite /stack /=; fold stack.
    match goal with |- (match ?A with | left _ => _ | right _ => _ end) = Some ?D => destruct A end; auto. elim n. reflexivity.
  Qed.

  Lemma stack_cons_length_ne:
    forall d cs reg stk,
      d <> length cs ->
      stack d ((reg, stk)::cs) = stack d cs.
  Proof.
    intros; rewrite /stack /=; fold stack.
    unfold Stackframe. destruct (nat_eq_dec d (length cs)); auto. congruence.
  Qed.

  Lemma stack_is_Some:
    forall cs d,
      is_Some (stack d cs) <-> d < length cs.
  Proof.
    induction cs; intros.
    - simpl. split; [inversion 1; discriminate|lia].
    - simpl. destruct (nat_eq_dec d (length cs)).
      + subst d. split; [lia|eauto].
      + rewrite IHcs. lia.
  Qed.

  Lemma sim_cs_stack_extend:
    forall cs h m a wa,
      (forall d stk', stack d cs = Some stk' -> forall a', is_Some (stk' !! a') -> (a' < a)%a) ->
      sim_cs true h cs m ->
      sim_cs true h cs (<[a:=translate_word wa]> m).
  Proof.
    induction cs; intros; auto.
    - econstructor.
    - inv H1. econstructor; eauto.
      + intros. generalize (Hstksim _ _ H1).
        rewrite lookup_insert_ne; auto.
        generalize (H0 (length cs) stk ltac:(rewrite stack_cons_length; auto) a ltac:(eexists; eauto)).
        clear; solve_addr.
      + eapply IHcs; eauto.
        intros. eapply H0; eauto.
        erewrite stack_cons_length_ne; eauto.
        generalize (proj1 (stack_is_Some _ _) ltac:(eexists; apply H1)).
        unfold Stackframe in *; lia.
  Qed.

  Inductive invariants: language.cfg overlay_lang -> language.cfg cap_lang -> Prop :=
  | invariants_intro:
      forall e1 e2 reg1 reg2 h stk cs mem2
        (Hstkdisj: forall d1 d2, d1 < d2 -> forall stk1 stk2, stack d1 ((reg1, stk)::cs) = Some stk1 -> stack d2 ((reg1, stk)::cs) = Some stk2 -> forall a1 a2, is_Some (stk1 !! a1) -> is_Some (stk2 !! a2) -> (a1 < a2)%a)
        (Hcswf: sim_cs false h ((reg1, stk)::cs) mem2)
        (Hsregs: forall r w, reg1 !! r = Some w -> reg2 !! r = Some (translate_word w))
        (Hsh: forall a w, h !! a = Some w -> mem2 !! a = Some (translate_word w) /\ lang.pwlW w = false /\ lang.is_global w = true /\ lang.can_address_only w (dom _ h))
        (Hdisj: forall a, a ∈ dom (gset _) h -> (e_stk <= a)%a),
      invariants ([e1], (reg1, h, stk, cs)) ([e2], (reg2, mem2)).

  Inductive sim: language.cfg overlay_lang -> language.cfg cap_lang -> Prop :=
  | sim_intro:
      forall e1 e2 reg1 reg2 h stk cs mem2
        (Hsexpr: sim_expr e1 e2)
        (Hinvs: can_step e1 -> invariants ([e1], (reg1, h, stk, cs)) ([e2], (reg2, mem2))),
        sim ([e1], (reg1, h, stk, cs)) ([e2], (reg2, mem2)).

  Lemma Hregsdef_preserve_word_of_arg reg h stk cs
    (Hregsdef: forall r, exists w, reg !! r = Some w /\ interp w h stk cs):
    forall src dst r,
      exists w, <[dst := word_of_argument reg src]> reg !! r = Some w /\ interp w h stk cs.
  Proof.
    intros. destruct (reg_eq_dec dst r); [|rewrite lookup_insert_ne; eauto].
    subst r. rewrite lookup_insert. eexists; split; eauto.
    destruct src; simpl; auto. rewrite /base.RegLocate.
    destruct (Hregsdef r) as [wr [A B] ]. rewrite A; auto.
  Qed.

  Lemma Hsregs_preserve_word_of_arg (reg1: base.Reg) (reg2: Reg) dst src
    (Hsregs: forall (r: RegName) w, reg1 !! r = Some w -> reg2 !! r = Some (translate_word w)):
    forall r w, (<[dst:=word_of_argument reg1 src]> reg1) !! r = Some w -> (<[dst:=translate_word (word_of_argument reg1 src)]> reg2 )!! r = Some (translate_word w).
  Proof.
    intros. destruct (reg_eq_dec dst r); [|rewrite lookup_insert_ne; rewrite lookup_insert_ne in H0; auto].
    subst r; rewrite lookup_insert; rewrite lookup_insert in H0.
    inv H0; auto.
  Qed.

  Definition addr_of_argument' reg r :=
    match lang.z_of_argument reg r with
    | Some n => z_to_addr n
    | None => None
    end.

  Lemma can_address_only_heap_extend:
    forall w (h: base.Mem) x y,
      lang.can_address_only w (dom (gset Addr) h) ->
      lang.can_address_only w (dom (gset Addr) (<[x := y]> h)).
  Proof.
    intros. destruct w; simpl; auto.
    destruct c; simpl in H0; auto.
    destruct c as [ [ [ [p g] b] e] a].
    intros. apply H0 in H1. set_solver.
  Qed.

  Lemma canStore_canStoreU_URWLX:
    forall p a w,
      lang.canStore p a w = true ->
      lang.canStoreU URWLX a w = true.
  Proof.
    destruct w; simpl; intros; auto.
    destruct c; auto.
    + destruct c as [ [ [ [pp gg] bb] ee] aa].
      destruct gg; auto.
      apply andb_true_iff in H0. destruct H0; auto.
    + apply andb_true_iff in H0. destruct H0; auto.
    + apply andb_true_iff in H0. destruct H0; auto.
  Qed.

  Lemma canStoreU_canStoreU_URWLX:
    forall p a w,
      lang.canStoreU p a w = true ->
      lang.canStoreU URWLX a w = true.
  Proof.
    destruct w; simpl; intros; auto.
    destruct c; auto.
    + destruct c as [ [ [ [pp gg] bb] ee] aa].
      destruct gg; auto.
      apply andb_true_iff in H0. destruct H0; auto.
    + apply andb_true_iff in H0. destruct H0; auto.
    + apply andb_true_iff in H0. destruct H0; auto.
  Qed.

  Lemma exec_sim:
    forall K reg1 reg1' reg2 reg2' h h' stk stk' cs cs' mem2 mem2' p g b e a c1 c2
      (Hsexpr: sim_expr (fill K (lang.Instr lang.Executable)) (@ectx_language.fill cap_ectx_lang (map (fun _ => SeqCtx) K) (Instr Executable)))
      (Hstkdisj: forall d1 d2, d1 < d2 -> forall stk1 stk2, stack d1 ((reg1, stk)::cs) = Some stk1 -> stack d2 ((reg1, stk)::cs) = Some stk2 -> forall a1 a2, is_Some (stk1 !! a1) -> is_Some (stk2 !! a2) -> (a1 < a2)%a)
      (Hcswf: sim_cs false h ((reg1, stk)::cs) mem2)
      (Hsregs: forall r w, reg1 !! r = Some w -> reg2 !! r = Some (translate_word w))
      (Hsh: forall a w, h !! a = Some w -> mem2 !! a = Some (translate_word w) /\ lang.pwlW w = false /\ lang.is_global w = true /\ lang.can_address_only w (dom _ h))
      (Hdisj: forall a, a ∈ dom (gset _) h -> (e_stk <= a)%a)
      (HnisJmp: ∀ r : RegName, decodeInstrW' (base.MemLocate h a) ≠ Jmp r)
      (HnisJnz: ∀ r1 r2 : RegName, decodeInstrW' (base.MemLocate h a) ≠ Jnz r1 r2)
      (HisCorrectPC: lang.isCorrectPC (inr (Regular (p, g, b, e, a)))),
      reg1 !! PC = Some (inr (Regular (p, g, b, e, a))) ->
      lang.exec (decodeInstrW' (base.MemLocate h a)) (reg1, h, stk, cs) = (c1, (reg1', h', stk', cs')) ->
      exec (decodeInstrW (mem2 !m! a)) (reg2, mem2) = (c2, (reg2', mem2')) ->
      sim ([ectxi_language.fill K (lang.Instr c1)], (reg1', h', stk', cs')) ([ectxi_language.fill (map (fun _ => SeqCtx) K) (Instr c2)], (reg2', mem2')).
  Proof.
    rewrite /MemLocate /base.MemLocate. intros.
    inv Hcswf. generalize (Hregsdef PC).
    intros [wpc [HPC HinterpPC] ].
    rewrite HPC in H0; inv H0. simpl in HinterpPC.
    destruct HinterpPC as [HnpwlPC Hisdef].
    inv HisCorrectPC. generalize (Hisdef _ H4); intros Hha.
    eapply elem_of_dom in Hha. destruct Hha as [wa Ha].
    rewrite Ha in H1. generalize (Hsh _ _ Ha).
    intros [Ha' [HnpwlW [Hisglobal Hcan_address] ] ].
    rewrite Ha' in H2. rewrite -decodeInstrW_translate_word in H2.
    rewrite Ha in HnisJmp, HnisJnz.
    destruct (decodeInstrW' wa) eqn:Hinstr.
    - (* Jmp *)
      exfalso; eapply HnisJmp; reflexivity.
    - (* Jnz *)
      exfalso; eapply HnisJnz; reflexivity.
    - (* Mov *)
      simpl in H1, H2.
      assert (match incrementPC (<[dst := word_of_argument reg1 src]> reg1) with Some r => c1 = lang.NextI /\ c2 = NextI /\ reg1' = r /\ h' = h /\ stk' = stk /\ cs' = cs /\ mem2' = mem2 /\ incrementPC' (<[dst := translate_word (word_of_argument reg1 src)]> reg2) = Some reg2' | _ => c1 = lang.Failed /\ c2 = Failed end).
      { destruct (incrementPC (<[dst:=word_of_argument reg1 src]> reg1)) as [reg1''|] eqn:Hincrement1.
        - generalize (@incrementPC_success_updatePC _ _ h stk cs Hincrement1).
          intro A. assert (X: (c1, (reg1', h', stk', cs')) = (lang.NextI, (reg1'', h, stk, cs))).
          { rewrite -A -H1. destruct src; simpl in A; rewrite A; auto. }
          inv X. assert (Hww: exists ww, <[dst:=word_of_argument reg1 src]> reg1 !! PC = Some ww).
          { destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert; eauto|].
            rewrite lookup_insert_ne; auto. rewrite HPC; eauto. }
          destruct Hww as [ww Hww].
          assert (Hww': (<[dst:=translate_word (word_of_argument reg1 src)]> reg2) !! PC = Some (translate_word ww)).
          { destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hww; inv Hww; rewrite lookup_insert //|].
            rewrite lookup_insert_ne; auto.
            rewrite lookup_insert_ne in Hww; auto. }
          generalize (@incrementPC_success_incrementPC' _ _ _ _ Hww Hww' Hincrement1).
          intros [regs2'' Y].
          generalize (@rules_base.incrementPC_success_updatePC _ mem2 _ Y).
          intros [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
          assert (XX: (c2, (reg2', mem2')) = (NextI, (regs2'', mem2))).
          { rewrite Z4 -Z3 - H2. destruct src; simpl; auto.
            replace (reg2 !r! r) with (translate_word (base.RegLocate reg1 r)); auto.
            rewrite /base.RegLocate /RegLocate.
            destruct (Hregsdef r) as [rw [X1 X2] ].
            rewrite X1. rewrite (Hsregs _ _ X1) //. }
          inv XX. repeat split; auto.
        - generalize (@incrementPC_fail_updatePC _ h stk cs Hincrement1).
          intro X. split.
          + destruct src; simpl in H1; rewrite H1 in X; inv X; auto.
          + assert (Hww: exists ww, <[dst:=word_of_argument reg1 src]> reg1 !! PC = Some ww).
            { destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert; eauto|].
              rewrite lookup_insert_ne; auto. rewrite HPC; eauto. }
            destruct Hww as [ww Hww].
            assert (Hww': (<[dst:=translate_word (word_of_argument reg1 src)]> reg2) !! PC = Some (translate_word ww)).
            { destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hww; inv Hww; rewrite lookup_insert //|].
              rewrite lookup_insert_ne; auto.
              rewrite lookup_insert_ne in Hww; auto. }
            generalize (@incrementPC_fail_incrementPC' _ _ _ Hww Hww' Hincrement1). intro Y.
            generalize (rules_base.incrementPC_fail_updatePC _ mem2 Y).
            intro Z. destruct src; simpl in H2; simpl in Z; [rewrite H2 in Z; inv Z; auto|].
            replace (reg2 !r! r) with (translate_word (base.RegLocate reg1 r)) in H2; [rewrite H2 in Z; inv Z; auto|].
            rewrite /base.RegLocate /RegLocate.
            destruct (Hregsdef r) as [rw [X1 X2] ].
            rewrite X1. rewrite (Hsregs _ _ X1) //. }
      destruct (incrementPC (<[dst:=word_of_argument reg1 src]> reg1)) as [reg1''|] eqn:Hincrement; cycle 1.
      + destruct H0 as [-> ->].
        econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          simpl. repeat econstructor.
        * rewrite can_step_fill /can_step /=; intros [A | A]; discriminate.
      + destruct H0 as [-> [-> [-> [<- [<- [<- [<- Hincrement'] ] ] ]  ] ] ].
        econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          simpl. repeat econstructor.
        * intros _. econstructor; eauto.
          -- econstructor; eauto.
             generalize (Hregsdef_preserve_word_of_arg Hregsdef src dst). intros AA.
             generalize (incrementPC_inv_Some Hincrement). intro X1.
             generalize (rules_base.incrementPC_Some_inv _ _ Hincrement').
             intros [p'' [g'' [b'' [e'' [a'' [a''' [Y1 [Y2 [Y3 Y4] ] ] ] ] ] ] ] ].
             destruct (<[dst:=word_of_argument reg1 src]> reg1 !! PC) as [wpc|] eqn:X2; [|elim X1].
             destruct wpc as [?|cap]; [elim X1|].
             destruct cap as [ [ [ [ [p1 g1] b1] e1] a1] | ? | ?]; [| | elim X1].
             ** destruct X1 as [a1' [Ha1' [X1 X1'] ] ].
                rewrite X1. intro. destruct (reg_eq_dec PC r).
                { subst r; rewrite lookup_insert; eexists; split; eauto.
                  simpl. destruct (AA PC) as [wpc [ZA ZB] ].
                  rewrite X2 in ZA; inv ZA. apply ZB. }
                { rewrite lookup_insert_ne; auto. }
             ** destruct X1 as [a2' [Ha2' [X1 X1'] ] ].
                rewrite X1. intro. destruct (reg_eq_dec PC r).
                { subst r; rewrite lookup_insert; eexists; split; eauto.
                  simpl. destruct (AA PC) as [wpc [ZA ZB] ].
                  rewrite X2 in ZA; inv ZA. simpl in ZB.
                  destruct ZB as [ZB1 [ZB3 [ZB4 ZB2] ] ]; split; auto.
                  split; auto. split; auto.
                  intros. apply ZB2. destruct X1' as [? [? [? [? ?] ] ] ].
                  destruct p0; auto; congruence. }
                { rewrite lookup_insert_ne; auto. }
          -- generalize (@Hsregs_preserve_word_of_arg _ _ dst src Hsregs). intros Hsregs'.
             generalize (incrementPC_inv_Some Hincrement). intro X1.
             generalize (rules_base.incrementPC_Some_inv _ _ Hincrement').
             intros [p'' [g'' [b'' [e'' [a'' [a''' [Y1 [Y2 [Y3 Y4] ] ] ] ] ] ] ] ].
             destruct (<[dst:=word_of_argument reg1 src]> reg1 !! PC) as [wpc|] eqn:X2; [|elim X1].
             destruct wpc as [?|cap]; [elim X1|].
             destruct cap as [ [ [ [ [p1 g1] b1] e1] a1] | ? | ?]; [| | elim X1].
             ++ destruct X1 as [a1' [Ha1' [X1 X1'] ] ].
                rewrite X1. intro. destruct (reg_eq_dec PC r).
                { subst r; rewrite lookup_insert.
                  subst reg2'. rewrite lookup_insert.
                  inversion 1. simpl.
                  generalize (Hsregs' _ _ X2). rewrite Y1. simpl. inversion 1; subst.
                  rewrite Y2 in Ha1'; inv Ha1'; auto. }
                { subst reg2'. rewrite !(lookup_insert_ne _ PC); auto. }
             ++ destruct X1 as [a1' [Ha1' [X1 X1'] ] ].
                rewrite X1. intro. destruct (reg_eq_dec PC r).
                { subst r; rewrite lookup_insert.
                  subst reg2'. rewrite lookup_insert.
                  inversion 1. simpl.
                  generalize (Hsregs' _ _ X2). rewrite Y1. simpl. inversion 1; subst.
                  rewrite Y2 in Ha1'; inv Ha1'; auto. }
                { subst reg2'. rewrite !(lookup_insert_ne _ PC); auto. }
    - (* Load *)
      assert (AA: match reg1 !! src with
                  | Some (inr (Regular (pp, gg, bb, ee, aa))) =>
                    if (readAllowed pp) &&  (withinBounds (pp, gg, bb, ee, aa)) then
                      exists wsrc, h !! aa = Some wsrc /\ interp wsrc h stk cs /\
                        match incrementPC (<[dst:=wsrc]> reg1) with
                        | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=translate_word wsrc]> reg2) = Some reg2' /\ mem2' = mem2
                        | None => c1 = lang.Failed /\ c2 = Failed
                        end
                    else c1 = lang.Failed /\ c2 = Failed
                  | Some (inr (Stk dd pp bb ee aa)) =>
                    if (readAllowed pp) && (withinBounds (pp, Directed, bb, ee, aa)) then
                      exists xstk, stack dd ((reg1, stk)::cs) = Some xstk /\ exists wsrc, xstk !! aa = Some wsrc /\ interp wsrc h stk cs /\
                          match incrementPC (<[dst:=wsrc]> reg1) with
                          | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=translate_word wsrc]> reg2) = Some reg2' /\ mem2' = mem2
                          | None => c1 = lang.Failed /\ c2 = Failed
                          end
                    else c1 = lang.Failed /\ c2 = Failed
                  | _ => c1 = lang.Failed /\ c2 = Failed
                  end).
      { destruct (Hregsdef src) as [wsrc [Hwsrc Hinterpsrc] ].
        generalize (Hsregs _ _ Hwsrc); intros Hwsrc'.
        rewrite Hwsrc. destruct wsrc.
        - rewrite /= /base.RegLocate Hwsrc in H1.
          rewrite /= /RegLocate Hwsrc' in H2.
          inv H1; inv H2; auto.
        - destruct (translate_word_cap c) as [c' Hc'].
          rewrite Hc' in Hwsrc'.
          destruct c; [|inv Hc'|inv Hc'; rewrite /= /base.RegLocate Hwsrc in H1; rewrite /= /RegLocate Hwsrc' /= in H2; inv H1; inv H2; auto].
          + destruct c as [ [ [ [pp gg] bb] ee] aa]. inv Hc'.
            rewrite /= /base.RegLocate Hwsrc /base.update_reg /= in H1.
            rewrite /= /RegLocate Hwsrc' /update_reg /= in H2.
            simpl. destruct (readAllowed pp && ((bb <=? aa)%a && (aa <? ee)%a)) eqn:Hcond; cycle 1.
            * inv H1; inv H2; auto.
            * rewrite /base.MemLocate /= in H1.
              rewrite /MemLocate /= in H2.
              destruct Hinterpsrc as [Hpwl Hcan_read].
              eapply andb_true_iff in Hcond. destruct Hcond as [Hcond1 Hcond2].
              eapply andb_true_iff in Hcond2. destruct Hcond2 as [Hcond2 Hcond3].
              apply leb_addr_spec in Hcond2. apply ltb_addr_spec in Hcond3.
              generalize (Hcan_read aa ltac:(clear -Hcond2 Hcond3; solve_addr)).
              intro Hin. eapply elem_of_dom in Hin. destruct Hin as [waa Haa].
              exists waa; split; auto. generalize (Hsh _ _ Haa).
              intros [Haa' [T1 [T2 T3] ] ]. split; [destruct waa; simpl; auto; destruct c; inv T2; auto|].
              rewrite Haa in H1. rewrite Haa' in H2.
              assert (exists w, (<[dst:=waa]> reg1) !! PC = Some w /\ (<[dst:=translate_word waa]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
              { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert /=; eauto|].
                rewrite !lookup_insert_ne //.
                eexists; rewrite HPC; split; auto. }
              destruct (incrementPC (<[dst:=waa]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
              { erewrite incrementPC_fail_updatePC in H1; eauto.
                inv H1; split; auto.
                eapply incrementPC_fail_incrementPC' in Hincrement1; eauto.
                erewrite rules_base.incrementPC_fail_updatePC in H2; eauto.
                inv H2; auto. }
              erewrite incrementPC_success_updatePC in H1; eauto.
              eapply incrementPC_success_incrementPC' in Hincrement1; eauto.
              destruct Hincrement1 as [reg2'' Hincrement2].
              rewrite Hincrement2.
              eapply rules_base.incrementPC_success_updatePC in Hincrement2.
              destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
              instantiate (1 := mem2) in Z3.
              rewrite Z3 -Z4 in H2. inv H1; inv H2; repeat split; auto.
          + rewrite /= /base.RegLocate Hwsrc /base.update_reg /= in H1.
            rewrite /= /RegLocate Hwsrc' /update_reg /= in H2.
            simpl. destruct (readAllowed p0 && ((a0 <=? a2)%a && (a2 <? a1)%a)) eqn:Hcond; cycle 1.
            * inv H1; inv H2; auto.
            * simpl in Hinterpsrc. destruct Hinterpsrc as [Hn [Hbound1 [HQW Hdom] ] ].
              match goal with |- context [(if ?X then _ else _)  = _] => destruct X as [_|ZZ]; [|elim ZZ; auto] end.
              eexists; split; eauto.
              rewrite /base.MemLocate /= in H1.
              rewrite /MemLocate /= in H2.
              eapply andb_true_iff in Hcond. destruct Hcond as [Hcond1 Hcond2].
              eapply andb_true_iff in Hcond2. destruct Hcond2 as [Hcond2 Hcond3].
              apply leb_addr_spec in Hcond2. apply ltb_addr_spec in Hcond3.
              generalize (Hdom a2 ltac:(clear -Hcond1 Hcond2 Hcond3; destruct p0; simpl in Hcond1; try congruence; solve_addr)).
              intros [waa Haa].
              rewrite Haa. rewrite Haa in H1.
              destruct (Hstksim _ _ Haa) as [Haa' [T1 T2] ]. rewrite Haa' in H2.
              eexists; split; eauto. split; auto.
              assert (exists w, (<[dst:=waa]> reg1) !! PC = Some w /\ (<[dst:=translate_word waa]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
              { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert /=; eauto|].
                rewrite !lookup_insert_ne //.
                eexists; rewrite HPC; split; auto. }
              destruct (incrementPC (<[dst:=waa]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
              { erewrite incrementPC_fail_updatePC in H1; eauto.
                inv H1; split; auto.
                eapply incrementPC_fail_incrementPC' in Hincrement1; eauto.
                erewrite rules_base.incrementPC_fail_updatePC in H2; eauto.
                inv H2; auto. }
              erewrite incrementPC_success_updatePC in H1; eauto.
              eapply incrementPC_success_incrementPC' in Hincrement1; eauto.
              destruct Hincrement1 as [reg2'' Hincrement2].
              rewrite Hincrement2.
              eapply rules_base.incrementPC_success_updatePC in Hincrement2.
              destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
              instantiate (1 := mem2) in Z3.
              rewrite Z3 -Z4 in H2. inv H1; inv H2; repeat split; auto. }
      destruct (Hregsdef src) as [wsrc [Hwsrc Hinterp1] ].
      generalize (Hsregs _ _ Hwsrc); intros Hwsrc'.
      rewrite Hwsrc in AA. clear H1 H2.
      destruct wsrc.
      { destruct AA as [-> ->]. econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          simpl. repeat econstructor.
        * rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
      destruct c; cycle 2.
      { destruct AA as [-> ->]. econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          simpl. repeat econstructor.
        * rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
      { destruct c as [ [ [ [pp gg] bb] ee] aa].
        destruct (readAllowed pp && withinBounds (pp, gg, bb, ee, aa)) eqn:Hconds; cycle 1.
        { destruct AA as [-> ->]. econstructor.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            simpl. repeat econstructor.
          * rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
        destruct AA as [waa [Haa [Hinterpaa AA] ] ].
        destruct (incrementPC (<[dst:=waa]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        { destruct AA as [-> ->]. econstructor.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            simpl. repeat econstructor.
          * rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
        destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
        econstructor; eauto.
        - eapply sim_expr_exec_inv in Hsexpr. subst K.
          simpl. repeat econstructor.
        - eapply incrementPC_inv_Some in Hincrement1.
          destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|].
          + destruct waa; [elim Hincrement1|].
            destruct c; [| |elim Hincrement1].
            * destruct c as [ [ [ [px gx] bx] ex] ax].
              destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite lookup_insert in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              inv HXX. rewrite Hap1 in Hap1'; inv Hap1'.
              rewrite !insert_insert.
              intros _. econstructor; eauto.
              { econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto]. }
              { intros rr; destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|rewrite !lookup_insert_ne; auto]. }
            * intros. destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite lookup_insert in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              inv HXX. rewrite Hap1 in Hap1'; inv Hap1'.
              rewrite !insert_insert.
              constructor; eauto.
              { econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; eauto].
                eexists; split; eauto.
                simpl. destruct Hinterpaa as [? [? [? ?] ] ].
                do 3 (split; auto).
                intros; eapply H5. simpl.
                destruct X2 as [? [? [? [? ?] ] ] ].
                destruct ppp; try congruence; auto. }
              { intros rr; destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|rewrite !lookup_insert_ne; auto]. }
          + rewrite lookup_insert_ne in Hincrement1; auto.
            intros _. rewrite HPC in Hincrement1.
            destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
            eapply rules_base.incrementPC_Some_inv in Hincrement2.
            destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
            rewrite lookup_insert_ne in HXX; auto.
            generalize (Hsregs _ _ HPC). rewrite HXX.
            intro DD; inv DD. rewrite Hap1 in Hap1'; inv Hap1'.
            econstructor; eauto.
            * econstructor; eauto. intros rr.
              destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite (lookup_insert_ne _ PC); auto].
              { eexists; split; eauto. generalize (Hregsdef PC).
                intros [wpc [Hwpc HinterpPC] ]. rewrite HPC in Hwpc; inv Hwpc.
                auto. }
              destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
            * intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto| rewrite !(lookup_insert_ne _ PC); auto].
              destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert; inversion 1; auto| rewrite !lookup_insert_ne; auto]. }
      { destruct (readAllowed p0 && withinBounds (p0, Directed, a0, a1, a2)) eqn:Hconds; cycle 1.
        { destruct AA as [-> ->]. econstructor.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            simpl. repeat econstructor.
          * rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
        destruct AA as [xstk [Hxstk [waa [Haa [Hinterpaa AA] ] ] ] ].
        destruct (incrementPC (<[dst:=waa]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        { destruct AA as [-> ->]. econstructor.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            simpl. repeat econstructor.
          * rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
        destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
        econstructor; eauto.
        - eapply sim_expr_exec_inv in Hsexpr. subst K.
          simpl. repeat econstructor.
        - eapply incrementPC_inv_Some in Hincrement1.
          destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|].
          + destruct waa; [elim Hincrement1|].
            destruct c; [| |elim Hincrement1].
            * destruct c as [ [ [ [px gx] bx] ex] ax].
              destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite lookup_insert in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              inv HXX. rewrite Hap1 in Hap1'; inv Hap1'.
              rewrite !insert_insert.
              intros _. econstructor; eauto.
              { econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto]. }
              { intros rr; destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|rewrite !lookup_insert_ne; auto]. }
            * intros. destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite lookup_insert in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              inv HXX. rewrite Hap1 in Hap1'; inv Hap1'.
              rewrite !insert_insert.
              constructor; eauto.
              { econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; eauto].
                eexists; split; eauto.
                simpl. destruct Hinterpaa as [? [? [? ?] ] ].
                do 3 (split; auto).
                intros; eapply H5. simpl.
                destruct X2 as [? [? [? [? ?] ] ] ].
                destruct ppp; try congruence; auto. }
              { intros rr; destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|rewrite !lookup_insert_ne; auto]. }
          + rewrite lookup_insert_ne in Hincrement1; auto.
            intros _. rewrite HPC in Hincrement1.
            destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
            eapply rules_base.incrementPC_Some_inv in Hincrement2.
            destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
            rewrite lookup_insert_ne in HXX; auto.
            generalize (Hsregs _ _ HPC). rewrite HXX.
            intro DD; inv DD. rewrite Hap1 in Hap1'; inv Hap1'.
            econstructor; eauto.
            * econstructor; eauto. intros rr.
              destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite (lookup_insert_ne _ PC); auto].
              { eexists; split; eauto. generalize (Hregsdef PC).
                intros [wpc [Hwpc HinterpPC] ]. rewrite HPC in Hwpc; inv Hwpc.
                auto. }
              destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
            * intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto| rewrite !(lookup_insert_ne _ PC); auto].
              destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert; inversion 1; auto| rewrite !lookup_insert_ne; auto]. }
    - (* Store *)
      destruct (Hregsdef dst) as [wdst [Hwdst Hinterpdst] ].
      generalize (Hsregs _ _ Hwdst). intros Hwdst'.
      assert (exists wsrc, word_of_argument reg1 src = wsrc /\ interp wsrc h stk cs) as [wsrc [Hwsrc Hinterpsrc] ].
      { destruct src; [simpl; eexists; split; eauto; simpl; auto|].
        destruct (Hregsdef r) as [? [? ?] ]. simpl.
        rewrite /base.RegLocate H0. eauto. }
      assert (rules_base.word_of_argument reg2 src = Some (translate_word wsrc)) as Hwsrc'.
      { destruct src; [inv Hwsrc; simpl; auto|].
        destruct (Hregsdef r) as [? [? ?] ]. rewrite /= /base.RegLocate H0 in Hwsrc.
        inv Hwsrc; eapply Hsregs; eauto. }
      assert (AA: match wdst with
                  | inr (Regular (pp, gg, bb, ee, aa)) =>
                    if (writeAllowed pp) && ((bb <=? aa)%a && (aa <? ee)%a) && (lang.canStore pp aa wsrc) then
                      match incrementPC reg1 with
                      | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = (<[aa:=wsrc]> h) /\ stk' = stk /\ cs' = cs /\ incrementPC' reg2 = Some reg2' /\ mem2' = (<[aa:=translate_word wsrc]> mem2)
                      | None => c1 = lang.Failed /\ c2 = Failed
                      end
                    else c1 = lang.Failed /\ c2 = Failed
                  | inr (Stk dd pp bb ee aa) =>
                    if (writeAllowed pp) && ((bb <=? aa)%a && (aa <? ee)%a) && (lang.canStore pp aa wsrc) then
                      match incrementPC reg1 with
                      | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ (stk' = if nat_eq_dec dd (length cs) then <[aa:=wsrc]> stk else stk) /\ (if nat_eq_dec dd (length cs) then cs' = cs else update_callstack cs dd aa wsrc = Some cs') /\ incrementPC' reg2 = Some reg2' /\ mem2' = (<[aa:=translate_word wsrc]> mem2)
                      | None => c1 = lang.Failed /\ c2 = Failed
                      end
                    else c1 = lang.Failed /\ c2 = Failed
                  | _ => c1 = lang.Failed /\ c2 = Failed
                  end).
      { rewrite /= /base.RegLocate Hwdst in H1.
        rewrite /= /RegLocate Hwdst' in H2.
        assert (match wdst with
         | inl _ => (lang.Failed, (reg1, h, stk, cs))
         | inr c =>
             match c with
             | Regular c0 =>
                 let (p0, a) := c0 in
                 let (p1, e) := p0 in
                 let (p2, b) := p1 in
                 let (p, _) := p2 in
                 if writeAllowed p && ((b <=? a)%a && (a <? e)%a) && lang.canStore p a wsrc
                 then
                  lang.updatePC
                    (base.update_mem (reg1, h, stk, cs) a wsrc)
                 else (lang.Failed, (reg1, h, stk, cs))
             | Stk d p b e a =>
                if writeAllowed p && ((b <=? a)%a && (a <? e)%a) && lang.canStore p a wsrc then
                 if nat_eq_dec d (length cs)
                 then lang.updatePC (update_stk (reg1, h, stk, cs) a wsrc)
                 else
                  match update_stack (reg1, h, stk, cs) d a wsrc with
                  | Some φ' => lang.updatePC φ'
                  | None => (lang.Failed, (reg1, h, stk, cs))
                  end
                else (lang.Failed, (reg1, h, stk, cs))
             | Ret _ _ _ => (lang.Failed, (reg1, h, stk, cs))
             end
         end = (c1, (reg1', h', stk', cs')) /\ match translate_word wdst with
         | inl _ => (Failed, (reg2, mem2))
         | inr c =>
             let (p0, a) := c in
             let (p1, e) := p0 in
             let (p2, b) := p1 in
             let (p, _) := p2 in
             if writeAllowed p && ((b <=? a)%a && (a <? e)%a) && canStore p a (translate_word wsrc)
             then updatePC (update_mem (reg2, mem2) a (translate_word wsrc))
             else (Failed, (reg2, mem2))
         end = (c2, (reg2', mem2'))) as [X1 X2].
        { destruct src; [inv Hwsrc; inv Hwsrc'; simpl in H2; simpl; auto|].
          - destruct wdst; simpl in H2; simpl; auto.
            destruct c; simpl; simpl in H2; try (rewrite andb_true_r); auto.
            destruct c as [ [ [ [pp gg] bb] ee] aa]; rewrite andb_true_r; auto.
          - simpl in Hwsrc; simpl in Hwsrc'.
            rewrite /base.RegLocate in Hwsrc. rewrite Hwsrc in H1.
            rewrite /RegLocate in Hwsrc'. rewrite Hwsrc' in H2. auto. }
        clear H1 H2.
        destruct wdst; [simpl in X2; inv X1; inv X2; auto|].
        destruct c; [|simpl in X2|simpl in X2; inv X1; inv X2; auto].
        - destruct c as [ [ [ [pp gg] bb] ee] aa].
          simpl in X2. assert (YY: lang.canStore pp aa wsrc = canStore pp aa (translate_word wsrc)).
          { clear. destruct wsrc; auto. destruct c; auto. }
          rewrite -YY in X2. destruct (writeAllowed pp && ((bb <=? aa)%a && (aa <? ee)%a) && lang.canStore pp aa wsrc) eqn:Hconds; [|inv X1; inv X2; auto].
          rewrite /base.update_mem /= in X1.
          rewrite /update_mem /= in X2.
          generalize (Hsregs _ _ HPC). intros HPC'.
          destruct (incrementPC reg1) as [reg1''|] eqn:Hincrement1.
          { erewrite incrementPC_success_updatePC in X1; eauto.
            eapply incrementPC_success_incrementPC' in HPC; eauto.
            destruct HPC as [reg2'' HX].
            rewrite HX.
            eapply rules_base.incrementPC_success_updatePC in HX.
            destruct HX as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
            instantiate (1 := (<[aa:=translate_word wsrc]> mem2)) in Z3.
            rewrite Z3 -Z4 in X2. inv X1; inv X2; repeat split; auto. }
          { erewrite incrementPC_fail_updatePC in X1; eauto.
            inv X1; split; auto.
            eapply incrementPC_fail_incrementPC' in HPC; eauto.
            erewrite rules_base.incrementPC_fail_updatePC in X2; eauto.
            inv X2; auto. }
        - assert (YY: lang.canStore p0 a2 wsrc = canStore p0 a2 (translate_word wsrc)).
          { clear. destruct wsrc; auto. destruct c; auto. }
          rewrite -YY in X2. destruct (writeAllowed p0 && ((a0 <=? a2)%a && (a2 <? a1)%a) && lang.canStore p0 a2 wsrc) eqn:Hconds; [|inv X1; inv X2; auto].
          rewrite /base.update_mem /= in X1.
          rewrite /update_mem /= in X2.
          generalize (Hsregs _ _ HPC). intros HPC'.
          destruct (incrementPC reg1) as [reg1''|] eqn:Hincrement1.
          { simpl in Hinterpdst. destruct Hinterpdst as [TT Hinterpdst].
            destruct (nat_eq_dec n (length cs)) as [_|RR]; [|elim RR; auto].
            rewrite /update_stk /= in X1.
            erewrite incrementPC_success_updatePC in X1; eauto.
            eapply incrementPC_success_incrementPC' in HPC; eauto.
            destruct HPC as [reg2'' HX].
            rewrite HX.
            eapply rules_base.incrementPC_success_updatePC in HX.
            destruct HX as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
            instantiate (1 := <[a2:=translate_word wsrc]> mem2) in Z3.
            rewrite Z3 -Z4 in X2. inv X1; inv X2; repeat split; auto. }
          { simpl in Hinterpdst. destruct Hinterpdst as [TT Hinterpdst].
            destruct (nat_eq_dec n (length cs)) as [_|RR]; [|elim RR; auto].
            rewrite /update_stk /= in X1.
            erewrite incrementPC_fail_updatePC in X1; eauto.
            inv X1; split; auto.
            eapply incrementPC_fail_incrementPC' in HPC; eauto.
            erewrite rules_base.incrementPC_fail_updatePC in X2; eauto.
            inv X2; auto. } }
      destruct wdst.
      { destruct AA as [-> ->]. econstructor.
        - eapply sim_expr_exec_inv in Hsexpr. subst K.
          simpl. repeat econstructor.
        - rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
      destruct c; cycle 2.
      { destruct AA as [-> ->]. econstructor.
        - eapply sim_expr_exec_inv in Hsexpr. subst K.
          simpl. repeat econstructor.
        - rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
      { destruct c as [ [ [ [pp gg] bb] ee] aa].
        destruct (writeAllowed pp && ((bb <=? aa)%a && (aa <? ee)%a) && lang.canStore pp aa wsrc) eqn:Hconds; cycle 1.
        { destruct AA as [-> ->]. econstructor.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            simpl. repeat econstructor.
          - rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
        erewrite !andb_true_iff in Hconds. destruct Hconds as [ [Hcond1 Hcond2] Hcond3].
        erewrite leb_addr_spec in Hcond2. erewrite ltb_addr_spec in Hcond2.
        destruct (incrementPC reg1) as [reg1''|] eqn:Hincrement1; cycle 1.
        { destruct AA as [-> ->]. econstructor.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            simpl. repeat econstructor.
          - rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
        destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
        econstructor; eauto.
        - eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        - intros _. eapply incrementPC_inv_Some in Hincrement1.
          rewrite HPC in Hincrement1. destruct Hincrement1 as [ap1 [Hap1 [-> TT] ] ].
          eapply rules_base.incrementPC_Some_inv in Hincrement2.
          rewrite (Hsregs _ _ HPC) /= in Hincrement2.
          destruct Hincrement2 as [? [? [? [? [? [? [XXX [Hap1' [-> XY] ] ] ] ] ] ] ] ]; inv XXX.
          rewrite Hap1 in Hap1'; inv Hap1'.
          econstructor; eauto.
          + econstructor; eauto.
            * intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
              { destruct (Hregsdef PC) as [wpc [Hwpc HinterpPC] ].
                rewrite HPC in Hwpc; inv Hwpc.
                simpl in HinterpPC; destruct HinterpPC.
                eexists; split; eauto. simpl; split; auto.
                intros. apply H3 in H5. clear -H5; set_solver. }
              destruct (Hregsdef rr) as [wrr [Hwrr Hinterprr] ].
              eexists; split; eauto. apply interp_heap_extend; auto.
            * intros. generalize (Hstkdisjheap a ltac:(eexists; apply H0)).
              simpl in Hinterpdst. destruct Hinterpdst as [? ?].
              generalize (H5 aa ltac:(clear -Hcond2; solve_addr)).
              intros. apply Hdisj in H6.
              assert (aa <> a) by (clear -H6 H7; solve_addr).
              rewrite !lookup_insert_ne; auto. apply Hstksim in H0.
              destruct H0 as [? [? ?] ]; do 2 (split; auto).
              apply interp_heap_extend; auto.
            * eapply sim_cs_heap_extend; auto.
              simpl in Hinterpdst. destruct Hinterpdst as [? ?].
              generalize (H3 aa ltac:(clear -Hcond2; solve_addr)).
              intro F. apply Hdisj in F. auto.
          + intro rr; destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto| rewrite !lookup_insert_ne; auto].
          + intro ax. destruct (addr_eq_dec aa ax); [subst ax; rewrite !lookup_insert|rewrite !lookup_insert_ne; auto].
            * inversion 1; split; auto.
              destruct (word_of_argument reg1 src); auto.
              simpl in Hinterpdst. simpl in Hcond3.
              destruct Hinterpdst as [Q W].
              assert (E: pwl pp = false) by (clear -Q; destruct pp; try congruence; auto).
              rewrite E andb_false_l in Hcond3.
              destruct c; try congruence.
              destruct c as [ [ [ [px gx] bx] ex] ax].
              destruct gx; try congruence.
              simpl. simpl in Hinterpsrc.
              destruct Hinterpsrc. do 2 (split; auto).
              intros. apply H6 in H7. clear -H7; set_solver.
            * intros. apply Hsh in H0. destruct H0 as [R [T [Y U] ] ].
              do 3 (split; auto). apply can_address_only_heap_extend; auto.
          + intros. assert (a = aa \/ a ∈ dom (gset Addr) h) by (clear -H0; set_solver).
            destruct H3; [subst a|apply Hdisj; auto].
            simpl in Hinterpdst. destruct Hinterpdst as [? ?].
            generalize (H5 aa ltac:(clear -Hcond2; solve_addr)).
            intro F. apply Hdisj in F. auto. }
      { destruct (writeAllowed p0 && ((a0 <=? a2)%a && (a2 <? a1)%a) && lang.canStore p0 a2 wsrc) eqn:Hconds; cycle 1.
        { destruct AA as [-> ->]. econstructor.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            simpl. repeat econstructor.
          - rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
        erewrite !andb_true_iff in Hconds. destruct Hconds as [ [Hcond1 Hcond2] Hcond3].
        erewrite leb_addr_spec in Hcond2. erewrite ltb_addr_spec in Hcond2.
        destruct (incrementPC reg1) as [reg1''|] eqn:Hincrement1; cycle 1.
        { destruct AA as [-> ->]. econstructor.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            simpl. repeat econstructor.
          - rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
        destruct (nat_eq_dec n (length cs)) as [_|G]; [|elim G; destruct Hinterpdst; auto].
        destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
        econstructor; eauto.
        - eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        - intros _. eapply incrementPC_inv_Some in Hincrement1.
          rewrite HPC in Hincrement1. destruct Hincrement1 as [ap1 [Hap1 [-> TT] ] ].
          eapply rules_base.incrementPC_Some_inv in Hincrement2.
          rewrite (Hsregs _ _ HPC) /= in Hincrement2.
          destruct Hincrement2 as [? [? [? [? [? [? [XXX [Hap1' [-> XY] ] ] ] ] ] ] ] ]; inv XXX.
          rewrite Hap1 in Hap1'; inv Hap1'.
          econstructor; eauto.
          + simpl in Hinterpdst. intros d1 d2 Hlt.
            destruct (nat_eq_dec d2 (length cs)).
            * subst d2. rewrite stack_cons_length.
              intros. inv H3.
              destruct (addr_eq_dec a2 a4).
              { subst a4. destruct Hinterpdst as [? [? [XZ ?] ] ].
                simpl in H0.
                match goal with H: context [(if ?S then _ else _) = Some stk1] |- _ => destruct S as [G|_]; [clear -G Hlt; unfold Stackframe in G; lia|] end.
                eapply XZ in H5; eauto.
                clear -H5 Hcond2; solve_addr. }
              rewrite lookup_insert_ne in H6; auto.
              eapply Hstkdisj; eauto; [|rewrite stack_cons_length; auto].
              simpl. simpl in H0. unfold Stackframe in *.
              destruct (nat_eq_dec d1 (length cs)); [lia|auto].
            * intros. rewrite (stack_cons_length_ne) in H3; eauto.
              generalize (proj1 (stack_is_Some _ _) ltac:(eexists; apply H3)).
              intros XT. rewrite (stack_cons_length_ne) in H0; eauto; [|unfold Stackframe in *; lia].
              eapply (Hstkdisj d1 d2 Hlt); eauto; rewrite stack_cons_length_ne; eauto.
              unfold Stackframe in *. lia.
          + econstructor; eauto.
            * intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
              { destruct (Hregsdef PC) as [wpc [Hwpc HinterpPC] ].
                rewrite HPC in Hwpc; inv Hwpc.
                simpl in HinterpPC; destruct HinterpPC.
                eexists; split; eauto. simpl; split; auto. }
              destruct (Hregsdef rr) as [wrr [Hwrr Hinterprr] ].
              eexists; split; eauto. apply interp_stack_extend; auto.
            * simpl in Hinterpdst. destruct Hinterpdst as [? [GG ?] ].
              clear -Hstkdisjheap Hcond2 GG.
              intro ax. destruct (addr_eq_dec a2 ax); [subst ax; intros; solve_addr|rewrite lookup_insert_ne; auto].
            * intros ax. destruct (addr_eq_dec a2 ax); [subst ax; rewrite !lookup_insert|rewrite !(lookup_insert_ne _ a2); auto].
              { inversion 1; split; auto.
                split; [apply interp_stack_extend; auto|].
                rewrite /canBeStored /=. eapply canStore_canStoreU_URWLX; eauto. }
              intros. apply Hstksim in H0. destruct H0 as [? [? ?] ].
              do 2 (split; auto). apply interp_stack_extend; auto.
            * assert (XQC: forall d xstk, stack d cs = Some xstk -> forall ax, is_Some (xstk !! ax) -> (ax < a2)%a).
              { destruct Hinterpdst as [W1 [W2 [W3 W4] ] ].
                intros. eapply W3 in H3; eauto. clear -H3 Hcond2; solve_addr. }
              eapply sim_cs_stack_extend; eauto.
          + intro rr; destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto| rewrite !lookup_insert_ne; auto].
          + intros. rewrite lookup_insert_ne; auto.
            assert (is_Some (h !! a)) by (eexists; eauto).
            apply elem_of_dom in H3.
            generalize (Hdisj _ H3). intro T.
            destruct Hinterpdst as [W1 [W2 ?] ].
            clear -Hcond2 T W2. solve_addr. }
    - (* Lt *)
      assert (match (lang.z_of_argument reg1 r1, lang.z_of_argument reg1 r2) with
              | (Some n1, Some n2) =>
                match incrementPC (<[dst:=inl (Z.b2z (n1 <? n2)%Z)]> reg1) with
                | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inl (Z.b2z (n1 <? n2)%Z)]> reg2) = Some reg2' /\ mem2' = mem2
                | None => c1 = lang.Failed /\ c2 = Failed
                end
              | (_, _) => c1 = lang.Failed /\ c2 = Failed
      end).
      { assert (Hregsome1: forall r, is_Some (reg1 !!r)).
        { intros. destruct (Hregsdef r) as [rw [-> _] ]. eauto. }
        destruct (lang.z_of_argument reg1 r1) as [n1|] eqn:Hr1.
        - destruct (lang.z_of_argument reg1 r2) as [n2|] eqn:Hr2.
          + eapply z_of_argument_inv_Some in Hr1.
            eapply z_of_argument_inv_Some in Hr2.
            assert (XX: lang.exec (Lt dst r1 r2) (reg1, h, stk, cs) = lang.updatePC (<[dst:=inl (Z.b2z (n1 <? n2)%Z)]> reg1, h, stk, cs)).
            { rewrite /lang.exec /=. destruct Hr1 as [-> | [r1' [-> Hr1eq] ] ].
              - destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ].
                + reflexivity.
                + rewrite /base.RegLocate Hr2eq //.
              - rewrite /base.RegLocate Hr1eq.
                destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ]; [reflexivity| rewrite Hr2eq //]. }
            rewrite XX in H1; clear XX.
            assert (XX: exec (Lt dst r1 r2) (reg2, mem2) = updatePC (<[dst:=inl (Z.b2z (n1 <? n2)%Z)]> reg2, mem2)).
            { rewrite /exec /=. destruct Hr1 as [-> | [r1' [-> Hr1eq] ] ].
              - destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ]; [reflexivity|].
                rewrite /RegLocate (Hsregs _ _ Hr2eq) //.
              - rewrite /RegLocate (Hsregs _ _ Hr1eq) /=.
                destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ]; [reflexivity|].
                rewrite (Hsregs _ _ Hr2eq) //. }
            rewrite XX in H2; clear XX.
            rewrite /base.update_reg /= in H1.
            assert (exists w, (<[dst:=inl (Z.b2z (n1 <? n2)%Z)]> reg1) !! PC = Some w /\ (<[dst:=inl (Z.b2z (n1 <? n2)%Z)]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
            { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert /=; eauto|].
              rewrite !lookup_insert_ne //.
              eexists; rewrite HPC; split; auto. }
            destruct (incrementPC (<[dst:=inl (Z.b2z (n1 <? n2)%Z)]> reg1)) as [reg1''|] eqn:HX.
            * erewrite incrementPC_success_updatePC in H1; eauto.
              eapply incrementPC_success_incrementPC' in HX; eauto.
              destruct HX as [reg2'' HX].
              rewrite HX.
              eapply rules_base.incrementPC_success_updatePC in HX.
              destruct HX as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
              instantiate (1 := mem2) in Z3.
              rewrite Z3 -Z4 in H2. inv H1; inv H2; repeat split; auto.
            * erewrite incrementPC_fail_updatePC in H1; eauto.
              inv H1; split; auto.
              eapply incrementPC_fail_incrementPC' in HX; eauto.
              erewrite rules_base.incrementPC_fail_updatePC in H2; eauto.
              inv H2; auto.
          + simpl in H1, H2.
            eapply z_of_argument_inv_None in Hr2; eauto.
            destruct Hr2 as [r2' [cap2 [-> Hr2eq] ] ].
            rewrite /base.RegLocate Hr2eq in H1.
            destruct (translate_word_cap cap2) as [cap2' Hcap2'].
            generalize (Hsregs _ _ Hr2eq). rewrite Hcap2'; intros Hr2eq'.
            rewrite /RegLocate Hr2eq' in H2.
            destruct r1; [inv H1; inv H2; split; auto|].
            destruct (reg1 !! r) as [w1|]; destruct (reg2 !! r) as [w2|]; try (destruct w1); try (destruct w2); inv H1; inv H2; split; auto.
        - simpl in H1, H2.
          eapply z_of_argument_inv_None in Hr1; eauto.
          destruct Hr1 as [r1' [cap1 [-> Hr1eq] ] ].
          rewrite /base.RegLocate Hr1eq in H1.
          destruct (translate_word_cap cap1) as [cap1' Hcap1'].
          generalize (Hsregs _ _ Hr1eq). rewrite Hcap1'; intros Hr1eq'.
          rewrite /RegLocate Hr1eq' in H2.
          destruct r2; inv H1; inv H2; auto. }
      destruct (lang.z_of_argument reg1 r1) as [n1|] eqn:Hn1; cycle 1.
      + destruct H0 as [-> ->]. econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          simpl. repeat econstructor.
        * rewrite can_step_fill /can_step /=; intros [A | A]; discriminate.
      + destruct (lang.z_of_argument reg1 r2) as [n2|] eqn:Hn2; cycle 1.
        * destruct H0 as [-> ->]. econstructor.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            simpl. repeat econstructor. }
          { rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
        * destruct (incrementPC (<[dst:=inl (Z.b2z (n1 <? n2)%Z)]> reg1)) as [reg1''|] eqn:Hincrement; cycle 1.
          { destruct H0 as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              simpl. repeat econstructor.
            - rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
          { destruct H0 as [-> [-> [-> [-> [-> [-> [Hincrement' ->] ] ] ] ] ] ].
            econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              simpl. repeat econstructor.
            - intros _. eapply incrementPC_inv_Some in Hincrement.
              destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in  Hincrement; elim Hincrement|].
              rewrite lookup_insert_ne // in Hincrement.
              rewrite HPC in Hincrement. destruct Hincrement as [ap1 [Hap1 [-> XX] ] ] .
              eapply rules_base.incrementPC_Some_inv in Hincrement'.
              rewrite lookup_insert_ne // in Hincrement'.
              rewrite (Hsregs _ _ HPC) /= in Hincrement'.
              destruct Hincrement' as [? [? [? [? [? [? [XXX [Hap1' [-> XY] ] ] ] ] ] ] ] ]; inv XXX.
              rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              + econstructor; eauto. intros.
                destruct (reg_eq_dec PC r).
                * subst r; rewrite lookup_insert. eexists; split; eauto.
                  simpl; auto.
                * rewrite lookup_insert_ne //. destruct (reg_eq_dec dst r).
                  { subst r; rewrite lookup_insert. eexists; split; eauto.
                    simpl; auto. }
                  { rewrite lookup_insert_ne //. }
              + intros r; destruct (reg_eq_dec PC r); [subst r|].
                * rewrite !lookup_insert; inversion 1; simpl; auto.
                * rewrite !(lookup_insert_ne _ PC) //. destruct (reg_eq_dec dst r); [subst r|].
                  { rewrite !lookup_insert; inversion 1; simpl; auto. }
                  { rewrite !lookup_insert_ne //. auto. } }
    - (* Add *)
      assert (match (lang.z_of_argument reg1 r1, lang.z_of_argument reg1 r2) with
              | (Some n1, Some n2) =>
                match incrementPC (<[dst:=inl (n1 + n2)%Z]> reg1) with
                | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inl (n1 + n2)%Z]> reg2) = Some reg2' /\ mem2' = mem2
                | None => c1 = lang.Failed /\ c2 = Failed
                end
              | (_, _) => c1 = lang.Failed /\ c2 = Failed
      end).
      { assert (Hregsome1: forall r, is_Some (reg1 !!r)).
        { intros. destruct (Hregsdef r) as [rw [-> _] ]. eauto. }
        destruct (lang.z_of_argument reg1 r1) as [n1|] eqn:Hr1.
        - destruct (lang.z_of_argument reg1 r2) as [n2|] eqn:Hr2.
          + eapply z_of_argument_inv_Some in Hr1.
            eapply z_of_argument_inv_Some in Hr2.
            assert (XX: lang.exec (machine_base.Add dst r1 r2) (reg1, h, stk, cs) = lang.updatePC (<[dst:=inl ((n1 + n2)%Z)]> reg1, h, stk, cs)).
            { rewrite /lang.exec /=. destruct Hr1 as [-> | [r1' [-> Hr1eq] ] ].
              - destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ].
                + reflexivity.
                + rewrite /base.RegLocate Hr2eq //.
              - rewrite /base.RegLocate Hr1eq.
                destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ]; [reflexivity| rewrite Hr2eq //]. }
            rewrite XX in H1; clear XX.
            assert (XX: exec (machine_base.Add dst r1 r2) (reg2, mem2) = updatePC (<[dst:=inl ((n1 + n2)%Z)]> reg2, mem2)).
            { rewrite /exec /=. destruct Hr1 as [-> | [r1' [-> Hr1eq] ] ].
              - destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ]; [reflexivity|].
                rewrite /RegLocate (Hsregs _ _ Hr2eq) //.
              - rewrite /RegLocate (Hsregs _ _ Hr1eq) /=.
                destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ]; [reflexivity|].
                rewrite (Hsregs _ _ Hr2eq) //. }
            rewrite XX in H2; clear XX.
            rewrite /base.update_reg /= in H1.
            assert (exists w, (<[dst:=inl ((n1 + n2)%Z)]> reg1) !! PC = Some w /\ (<[dst:=inl ((n1 + n2)%Z)]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
            { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert /=; eauto|].
              rewrite !lookup_insert_ne //.
              eexists; rewrite HPC; split; auto. }
            destruct (incrementPC (<[dst:=inl ((n1 + n2)%Z)]> reg1)) as [reg1''|] eqn:HX.
            * erewrite incrementPC_success_updatePC in H1; eauto.
              eapply incrementPC_success_incrementPC' in HX; eauto.
              destruct HX as [reg2'' HX].
              rewrite HX.
              eapply rules_base.incrementPC_success_updatePC in HX.
              destruct HX as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
              instantiate (1 := mem2) in Z3.
              rewrite Z3 -Z4 in H2. inv H1; inv H2; repeat split; auto.
            * erewrite incrementPC_fail_updatePC in H1; eauto.
              inv H1; split; auto.
              eapply incrementPC_fail_incrementPC' in HX; eauto.
              erewrite rules_base.incrementPC_fail_updatePC in H2; eauto.
              inv H2; auto.
          + simpl in H1, H2.
            eapply z_of_argument_inv_None in Hr2; eauto.
            destruct Hr2 as [r2' [cap2 [-> Hr2eq] ] ].
            rewrite /base.RegLocate Hr2eq in H1.
            destruct (translate_word_cap cap2) as [cap2' Hcap2'].
            generalize (Hsregs _ _ Hr2eq). rewrite Hcap2'; intros Hr2eq'.
            rewrite /RegLocate Hr2eq' in H2.
            destruct r1; [inv H1; inv H2; split; auto|].
            destruct (reg1 !! r) as [w1|]; destruct (reg2 !! r) as [w2|]; try (destruct w1); try (destruct w2); inv H1; inv H2; split; auto.
        - simpl in H1, H2.
          eapply z_of_argument_inv_None in Hr1; eauto.
          destruct Hr1 as [r1' [cap1 [-> Hr1eq] ] ].
          rewrite /base.RegLocate Hr1eq in H1.
          destruct (translate_word_cap cap1) as [cap1' Hcap1'].
          generalize (Hsregs _ _ Hr1eq). rewrite Hcap1'; intros Hr1eq'.
          rewrite /RegLocate Hr1eq' in H2.
          destruct r2; inv H1; inv H2; auto. }
      destruct (lang.z_of_argument reg1 r1) as [n1|] eqn:Hn1; cycle 1.
      + destruct H0 as [-> ->]. econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          simpl. repeat econstructor.
        * rewrite can_step_fill /can_step /=; intros [A | A]; discriminate.
      + destruct (lang.z_of_argument reg1 r2) as [n2|] eqn:Hn2; cycle 1.
        * destruct H0 as [-> ->]. econstructor.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            simpl. repeat econstructor. }
          { rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
        * destruct (incrementPC (<[dst:=inl ((n1 + n2)%Z)]> reg1)) as [reg1''|] eqn:Hincrement; cycle 1.
          { destruct H0 as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              simpl. repeat econstructor.
            - rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
          { destruct H0 as [-> [-> [-> [-> [-> [-> [Hincrement' ->] ] ] ] ] ] ].
            econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              simpl. repeat econstructor.
            - intros _. eapply incrementPC_inv_Some in Hincrement.
              destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in  Hincrement; elim Hincrement|].
              rewrite lookup_insert_ne // in Hincrement.
              rewrite HPC in Hincrement. destruct Hincrement as [ap1 [Hap1 [-> XX] ] ] .
              eapply rules_base.incrementPC_Some_inv in Hincrement'.
              rewrite lookup_insert_ne // in Hincrement'.
              rewrite (Hsregs _ _ HPC) /= in Hincrement'.
              destruct Hincrement' as [? [? [? [? [? [? [XXX [Hap1' [-> XY] ] ] ] ] ] ] ] ]; inv XXX.
              rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              + econstructor; eauto. intros.
                destruct (reg_eq_dec PC r).
                * subst r; rewrite lookup_insert. eexists; split; eauto.
                  simpl; auto.
                * rewrite lookup_insert_ne //. destruct (reg_eq_dec dst r).
                  { subst r; rewrite lookup_insert. eexists; split; eauto.
                    simpl; auto. }
                  { rewrite lookup_insert_ne //. }
              + intros r; destruct (reg_eq_dec PC r); [subst r|].
                * rewrite !lookup_insert; inversion 1; simpl; auto.
                * rewrite !(lookup_insert_ne _ PC) //. destruct (reg_eq_dec dst r); [subst r|].
                  { rewrite !lookup_insert; inversion 1; simpl; auto. }
                  { rewrite !lookup_insert_ne //. auto. } }
    - (* Sub *)
      assert (match (lang.z_of_argument reg1 r1, lang.z_of_argument reg1 r2) with
              | (Some n1, Some n2) =>
                match incrementPC (<[dst:=inl ((n1 - n2)%Z)]> reg1) with
                | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inl ((n1 - n2)%Z)]> reg2) = Some reg2' /\ mem2' = mem2
                | None => c1 = lang.Failed /\ c2 = Failed
                end
              | (_, _) => c1 = lang.Failed /\ c2 = Failed
      end).
      { assert (Hregsome1: forall r, is_Some (reg1 !!r)).
        { intros. destruct (Hregsdef r) as [rw [-> _] ]. eauto. }
        destruct (lang.z_of_argument reg1 r1) as [n1|] eqn:Hr1.
        - destruct (lang.z_of_argument reg1 r2) as [n2|] eqn:Hr2.
          + eapply z_of_argument_inv_Some in Hr1.
            eapply z_of_argument_inv_Some in Hr2.
            assert (XX: lang.exec (Sub dst r1 r2) (reg1, h, stk, cs) = lang.updatePC (<[dst:=inl ((n1 - n2)%Z)]> reg1, h, stk, cs)).
            { rewrite /lang.exec /=. destruct Hr1 as [-> | [r1' [-> Hr1eq] ] ].
              - destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ].
                + reflexivity.
                + rewrite /base.RegLocate Hr2eq //.
              - rewrite /base.RegLocate Hr1eq.
                destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ]; [reflexivity| rewrite Hr2eq //]. }
            rewrite XX in H1; clear XX.
            assert (XX: exec (Sub dst r1 r2) (reg2, mem2) = updatePC (<[dst:=inl ((n1 - n2)%Z)]> reg2, mem2)).
            { rewrite /exec /=. destruct Hr1 as [-> | [r1' [-> Hr1eq] ] ].
              - destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ]; [reflexivity|].
                rewrite /RegLocate (Hsregs _ _ Hr2eq) //.
              - rewrite /RegLocate (Hsregs _ _ Hr1eq) /=.
                destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ]; [reflexivity|].
                rewrite (Hsregs _ _ Hr2eq) //. }
            rewrite XX in H2; clear XX.
            rewrite /base.update_reg /= in H1.
            assert (exists w, (<[dst:=inl ((n1 - n2)%Z)]> reg1) !! PC = Some w /\ (<[dst:=inl ((n1 - n2)%Z)]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
            { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert /=; eauto|].
              rewrite !lookup_insert_ne //.
              eexists; rewrite HPC; split; auto. }
            destruct (incrementPC (<[dst:=inl ((n1 - n2)%Z)]> reg1)) as [reg1''|] eqn:HX.
            * erewrite incrementPC_success_updatePC in H1; eauto.
              eapply incrementPC_success_incrementPC' in HX; eauto.
              destruct HX as [reg2'' HX].
              rewrite HX.
              eapply rules_base.incrementPC_success_updatePC in HX.
              destruct HX as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
              instantiate (1 := mem2) in Z3.
              rewrite Z3 -Z4 in H2. inv H1; inv H2; repeat split; auto.
            * erewrite incrementPC_fail_updatePC in H1; eauto.
              inv H1; split; auto.
              eapply incrementPC_fail_incrementPC' in HX; eauto.
              erewrite rules_base.incrementPC_fail_updatePC in H2; eauto.
              inv H2; auto.
          + simpl in H1, H2.
            eapply z_of_argument_inv_None in Hr2; eauto.
            destruct Hr2 as [r2' [cap2 [-> Hr2eq] ] ].
            rewrite /base.RegLocate Hr2eq in H1.
            destruct (translate_word_cap cap2) as [cap2' Hcap2'].
            generalize (Hsregs _ _ Hr2eq). rewrite Hcap2'; intros Hr2eq'.
            rewrite /RegLocate Hr2eq' in H2.
            destruct r1; [inv H1; inv H2; split; auto|].
            destruct (reg1 !! r) as [w1|]; destruct (reg2 !! r) as [w2|]; try (destruct w1); try (destruct w2); inv H1; inv H2; split; auto.
        - simpl in H1, H2.
          eapply z_of_argument_inv_None in Hr1; eauto.
          destruct Hr1 as [r1' [cap1 [-> Hr1eq] ] ].
          rewrite /base.RegLocate Hr1eq in H1.
          destruct (translate_word_cap cap1) as [cap1' Hcap1'].
          generalize (Hsregs _ _ Hr1eq). rewrite Hcap1'; intros Hr1eq'.
          rewrite /RegLocate Hr1eq' in H2.
          destruct r2; inv H1; inv H2; auto. }
      destruct (lang.z_of_argument reg1 r1) as [n1|] eqn:Hn1; cycle 1.
      + destruct H0 as [-> ->]. econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          simpl. repeat econstructor.
        * rewrite can_step_fill /can_step /=; intros [A | A]; discriminate.
      + destruct (lang.z_of_argument reg1 r2) as [n2|] eqn:Hn2; cycle 1.
        * destruct H0 as [-> ->]. econstructor.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            simpl. repeat econstructor. }
          { rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
        * destruct (incrementPC (<[dst:=inl ((n1 - n2)%Z)]> reg1)) as [reg1''|] eqn:Hincrement; cycle 1.
          { destruct H0 as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              simpl. repeat econstructor.
            - rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
          { destruct H0 as [-> [-> [-> [-> [-> [-> [Hincrement' ->] ] ] ] ] ] ].
            econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              simpl. repeat econstructor.
            - intros _. eapply incrementPC_inv_Some in Hincrement.
              destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in  Hincrement; elim Hincrement|].
              rewrite lookup_insert_ne // in Hincrement.
              rewrite HPC in Hincrement. destruct Hincrement as [ap1 [Hap1 [-> XX] ] ] .
              eapply rules_base.incrementPC_Some_inv in Hincrement'.
              rewrite lookup_insert_ne // in Hincrement'.
              rewrite (Hsregs _ _ HPC) /= in Hincrement'.
              destruct Hincrement' as [? [? [? [? [? [? [XXX [Hap1' [-> XY] ] ] ] ] ] ] ] ]; inv XXX.
              rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              + econstructor; eauto. intros.
                destruct (reg_eq_dec PC r).
                * subst r; rewrite lookup_insert. eexists; split; eauto.
                  simpl; auto.
                * rewrite lookup_insert_ne //. destruct (reg_eq_dec dst r).
                  { subst r; rewrite lookup_insert. eexists; split; eauto.
                    simpl; auto. }
                  { rewrite lookup_insert_ne //. }
              + intros r; destruct (reg_eq_dec PC r); [subst r|].
                * rewrite !lookup_insert; inversion 1; simpl; auto.
                * rewrite !(lookup_insert_ne _ PC) //. destruct (reg_eq_dec dst r); [subst r|].
                  { rewrite !lookup_insert; inversion 1; simpl; auto. }
                  { rewrite !lookup_insert_ne //. auto. } }
    - (* Lea *)
      assert (AA: match lang.z_of_argument reg1 r with
                  | None => c1 = lang.Failed /\ c2 = Failed
                  | Some n => match reg1 !! dst with
                              | Some (inr (Regular (pp, gg, bb, ee, aa))) =>
                                if perm_eq_dec pp E then c1 = lang.Failed /\ c2 = Failed else
                                match (aa + n)%a with
                                       | None => c1 = lang.Failed /\ c2 = Failed
                                       | Some aa' => if isU pp then if Addr_le_dec aa' aa then
                                                    match incrementPC (<[dst:=inr (Regular (pp, gg, bb, ee, aa'))]> reg1)
                                                    with Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inr (pp, gg, bb, ee, aa')]> reg2) = Some reg2' /\ mem2' = mem2
                                                    | _ => c1 = lang.Failed /\ c2 = Failed
                                                    end
                                                    else c1 = lang.Failed /\ c2 = Failed else
                                                    match incrementPC (<[dst:=inr (Regular (pp, gg, bb, ee, aa'))]> reg1)
                                                    with Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inr (pp, gg, bb, ee, aa')]> reg2) = Some reg2' /\ mem2' = mem2
                                                    | _ => c1 = lang.Failed /\ c2 = Failed
                                                    end
                                       end
                              | Some (inr (Stk dd pp bb ee aa)) =>
                                if perm_eq_dec pp E then c1 = lang.Failed /\ c2 = Failed else
                                match (aa + n)%a with
                                       | None => c1 = lang.Failed /\ c2 = Failed
                                       | Some aa' => if isU pp then if Addr_le_dec aa' aa then
                                                    match incrementPC (<[dst:=inr (Stk dd pp bb ee aa')]> reg1)
                                                    with Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inr (pp, Directed, bb, ee, aa')]> reg2) = Some reg2' /\ mem2' = mem2
                                                    | _ => c1 = lang.Failed /\ c2 = Failed
                                                    end
                                                    else c1 = lang.Failed /\ c2 = Failed else
                                                    match incrementPC (<[dst:=inr (Stk dd pp bb ee aa')]> reg1)
                                                    with Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inr (pp, Directed, bb, ee, aa')]> reg2) = Some reg2' /\ mem2' = mem2
                                                    | _ => c1 = lang.Failed /\ c2 = Failed
                                                    end
                                       end
                              | _ => c1 = lang.Failed /\ c2 = Failed
                              end
                  end).
      { destruct (Hregsdef dst) as [wdst [Hwdst _] ].
        generalize (Hsregs _ _ Hwdst). intros Hwdst'.
        destruct (lang.z_of_argument reg1 r) as [nn|] eqn:Harg1; cycle 1.
        - simpl in H1, H2. destruct r; simpl in Harg1; try congruence.
          destruct (Hregsdef r) as [wr [Hwr _] ].
          rewrite Hwr in Harg1. destruct wr; simpl in Harg1; try congruence.
          rewrite /base.RegLocate Hwdst Hwr in H1.
          generalize (Hsregs _ _ Hwr). intros Hwr'.
          destruct (translate_word_cap c) as [c' Hc']; rewrite Hc' in Hwr'.
          rewrite /RegLocate Hwdst' Hwr' /= in H2.
          destruct wdst; [simpl in H1, H2; inv H1; inv H2; auto|].
          destruct (translate_word_cap c0) as [c0' Hc0']; rewrite Hc0' in H2.
          destruct c0 as [ [ [ [ [? ?] ?] ?] ?] | ? | ?]; simpl in Hc0'; inv Hc0'.
          + destruct p0; inv H1; inv H2; auto.
          + destruct p0; inv H1; inv H2; auto.
          + inv H1; inv H2; auto.
        - rewrite Hwdst. destruct wdst.
          + simpl in H1, H2. rewrite /base.RegLocate Hwdst in H1.
            rewrite /RegLocate Hwdst' /= in H2.
            destruct r; inv H1; inv H2; auto.
          + rewrite /= /base.RegLocate Hwdst /= in H1.
            assert (X1: match c with | Regular c0 => let (p0, a) := c0 in let (p1, e) := p0 in let (p2, b) := p1 in let (p, g) := p2 in match p with | E => (lang.Failed, (reg1, h, stk, cs)) | URW | URWL | URWX | URWLX => match (a + nn)%a with | Some a' => if Addr_le_dec a' a then lang.updatePC (base.update_reg (reg1, h, stk, cs) dst (inr (Regular (p, g, b, e, a')))) else (lang.Failed, (reg1, h, stk, cs)) | None => (lang.Failed, (reg1, h, stk, cs)) end | _ => match (a + nn)%a with | Some a' => lang.updatePC (base.update_reg (reg1, h, stk, cs) dst (inr (Regular (p, g, b, e, a')))) | None => (lang.Failed, (reg1, h, stk, cs)) end end | Stk d p b e a => match p with | E => (lang.Failed, (reg1, h, stk, cs)) | URW | URWL | URWX | URWLX => match (a + nn)%a with | Some a' => if Addr_le_dec a' a then  lang.updatePC (base.update_reg (reg1, h, stk, cs) dst (inr (Stk d p b e a'))) else (lang.Failed, (reg1, h, stk, cs)) | None => (lang.Failed, (reg1, h, stk, cs)) end | _ => match (a + nn)%a with | Some a' => lang.updatePC (base.update_reg (reg1, h, stk, cs) dst (inr (Stk d p b e a'))) | None => (lang.Failed, (reg1, h, stk, cs)) end end | Ret _ _ _ => (lang.Failed, (reg1, h, stk, cs)) end = (c1, (reg1', h', stk', cs'))).
            { destruct r; simpl in Harg1.
              - inv Harg1; rewrite -H1. reflexivity.
              - destruct (Hregsdef r) as [wr [Hwr _] ].
                rewrite Hwr in Harg1. destruct wr; inv Harg1.
                rewrite Hwr in H1. auto. }
            clear H1. destruct (translate_word_cap c) as [c' Hc'].
            rewrite Hc' in Hwdst'. rewrite /= /RegLocate Hwdst' /= in H2.
            assert (X2: let (p0, a) := c' in let (p1, e) := p0 in let (p2, b) := p1 in let (p, g) := p2 in match p with | E => (Failed, (reg2, mem2)) | URW | URWL | URWX | URWLX => match (a + nn)%a with | Some a' => if Addr_le_dec a' a then updatePC (update_reg (reg2, mem2) dst (inr (p, g, b, e, a'))) else (Failed, (reg2, mem2)) | None => (Failed, (reg2, mem2)) end | _ => match (a + nn)%a with | Some a' => updatePC (update_reg (reg2, mem2) dst (inr (p, g, b, e, a'))) | None => (Failed, (reg2, mem2)) end end = (c2, (reg2', mem2'))).
            { destruct r; simpl in Harg1.
              - inv Harg1; rewrite -H2. destruct c' as [ [ [ [pp gg] bb] ee] aa].
                auto.
              - destruct (Hregsdef r) as [wr [Hwr _] ].
                rewrite Hwr in Harg1. destruct wr; inv Harg1.
                generalize (Hsregs _ _ Hwr). intros Hwr'.
                rewrite Hwr' /= in H2; auto. rewrite -H2.
                destruct c' as [ [ [ [pp gg] bb] ee] aa]; auto. }
            clear H2.
            destruct c; cycle 2.
            * destruct c' as [ [ [ [pp gg] bb] ee] aa].
              simpl in Hc'; inv Hc'. inv X1; inv X2; auto.
            * destruct c as [ [ [ [pp gg] bb] ee] aa].
              simpl in Hc'; inv Hc'. destruct (perm_eq_dec pp E).
              { subst pp. inv X1; inv X2; auto. }
              destruct (aa + nn)%a as [aa'|] eqn:Haa'; cycle 1.
              { destruct pp; inv X1; inv X2; auto. }
              destruct (isU pp) eqn:HisU.
              { destruct (Addr_le_dec aa' aa).
                - assert (exists w, (<[dst:=inr (Regular (pp, gg, bb, ee, aa'))]> reg1) !! PC = Some w /\ (<[dst:=inr (pp, gg, bb, ee, aa')]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
                  { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
                    rewrite !lookup_insert_ne //. eauto. }
                  destruct (incrementPC (<[dst:=inr (Regular (pp, gg, bb, ee, aa'))]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
                  + generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
                    intros Hincrement2. rewrite /base.update_reg /= in X1.
                    erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in X1.
                    rewrite /update_reg /= in X2.
                    erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in X2.
                    destruct pp; try congruence; inv X1; inv X2; auto.
                  + destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
                    rewrite /base.update_reg /= in X1. rewrite /update_reg /= in X2.
                    erewrite incrementPC_success_updatePC in X1; eauto.
                    rewrite Hincrement2.
                    eapply rules_base.incrementPC_success_updatePC in Hincrement2.
                    destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
                    instantiate (1 := mem2) in Z3.
                    rewrite Z3 -Z4 in X2. destruct pp; try congruence; inv X1; inv X2; repeat split; auto.
                - destruct pp; simpl in HisU; try congruence; inv X1; inv X2; auto. }
              assert (exists w, (<[dst:=inr (Regular (pp, gg, bb, ee, aa'))]> reg1) !! PC = Some w /\ (<[dst:=inr (pp, gg, bb, ee, aa')]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
              { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
                rewrite !lookup_insert_ne //. eauto. }
              rewrite /base.update_reg /= in X1. rewrite /update_reg /= in X2.
              destruct (incrementPC (<[dst:=inr (Regular (pp, gg, bb, ee, aa'))]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
              { generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
                intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in X1.
                erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in X2.
                destruct pp; simpl in HisU; try congruence; inv X1; inv X2; auto. }
              destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
              erewrite incrementPC_success_updatePC in X1; eauto.
              rewrite Hincrement2.
              eapply rules_base.incrementPC_success_updatePC in Hincrement2.
              destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
              instantiate (1 := mem2) in Z3.
              rewrite Z3 -Z4 in X2. destruct pp; simpl in HisU; try congruence; inv X1; inv X2; repeat split; auto.
            * simpl in Hc'; inv Hc'. destruct (perm_eq_dec p0 E).
              { subst p0. inv X1; inv X2; auto. }
              destruct (a2 + nn)%a as [aa'|] eqn:Haa'; cycle 1.
              { destruct p0; inv X1; inv X2; auto. }
              destruct (isU p0) eqn:HisU.
              { destruct (Addr_le_dec aa' a2).
                - assert (exists w, (<[dst:=inr (Stk n p0 a0 a1 aa')]> reg1) !! PC = Some w /\ (<[dst:=inr (p0, Directed, a0, a1, aa')]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
                  { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
                    rewrite !lookup_insert_ne //. eauto. }
                  destruct (incrementPC (<[dst:=inr (Stk n p0 a0 a1 aa')]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
                  + generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
                    intros Hincrement2. rewrite /base.update_reg /= in X1.
                    erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in X1.
                    rewrite /update_reg /= in X2.
                    erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in X2.
                    destruct p0; try congruence; inv X1; inv X2; auto.
                  + destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
                    rewrite /base.update_reg /= in X1. rewrite /update_reg /= in X2.
                    erewrite incrementPC_success_updatePC in X1; eauto.
                    rewrite Hincrement2.
                    eapply rules_base.incrementPC_success_updatePC in Hincrement2.
                    destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
                    instantiate (1 := mem2) in Z3.
                    rewrite Z3 -Z4 in X2. destruct p0; try congruence; inv X1; inv X2; repeat split; auto.
                - destruct p0; simpl in HisU; try congruence; inv X1; inv X2; auto. }
              assert (exists w, (<[dst:=inr (Stk n p0 a0 a1 aa')]> reg1) !! PC = Some w /\ (<[dst:=inr (p0, Directed, a0, a1, aa')]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
              { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
                rewrite !lookup_insert_ne //. eauto. }
              rewrite /base.update_reg /= in X1. rewrite /update_reg /= in X2.
              destruct (incrementPC (<[dst:=inr (Stk n p0 a0 a1 aa')]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
              { generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
                intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in X1.
                erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in X2.
                destruct p0; simpl in HisU; try congruence; inv X1; inv X2; auto. }
              destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
              erewrite incrementPC_success_updatePC in X1; eauto.
              rewrite Hincrement2.
              eapply rules_base.incrementPC_success_updatePC in Hincrement2.
              destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
              instantiate (1 := mem2) in Z3.
              rewrite Z3 -Z4 in X2. destruct p0; simpl in HisU; try congruence; inv X1; inv X2; repeat split; auto. }
      destruct (lang.z_of_argument reg1 r) as [nn|] eqn:Harg1; cycle 1.
      { destruct AA as [-> ->]. econstructor.
        - eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
      destruct (Hregsdef dst) as [wdst [Hwdst _] ].
      rewrite Hwdst in AA. destruct wdst.
      { destruct AA as [-> ->]. econstructor.
        - eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
      destruct c; cycle 2.
      { destruct AA as [-> ->]. econstructor.
        - eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
      + destruct c as [ [ [ [pp gg] bb] ee] aa].
        destruct (perm_eq_dec pp E); [subst pp|].
        { destruct AA as [-> ->]. econstructor.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (aa + nn)%a as [aa'|] eqn:Haa'; cycle 1.
        { destruct AA as [-> ->]. econstructor.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (incrementPC (<[dst:=inr (Regular (pp, gg, bb, ee, aa'))]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        { assert (c1 = lang.Failed ∧ c2 = Failed) as [-> ->] by (destruct (isU pp); destruct (Addr_le_dec aa' aa); auto).
          econstructor.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (isU pp) eqn:HisU; cycle 1.
        { destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          * intros _.
            eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|].
            { destruct (Hregsdef PC) as [wPC [HPC' HinterpPC] ].
              rewrite HPC in HPC'; inv HPC'.
              destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite lookup_insert in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              inv HXX. rewrite Hap1 in Hap1'; inv Hap1'.
              rewrite !insert_insert.
              econstructor; eauto.
              - econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|].
                + eexists; split; simpl; eauto.
                  repeat split; simpl; auto.
                  destruct ppp; simpl in HisU; try congruence.
                  rewrite Hwdst in HPC; inv HPC. auto.
                + rewrite lookup_insert_ne //.
              - intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
                rewrite !(lookup_insert_ne _ PC) //. auto. }
            { destruct (Hregsdef PC) as [wPC [HPC' HinterpPC] ].
              rewrite HPC in HPC'; inv HPC'.
              destruct (Hregsdef dst) as [wdst' [Hwdst' Hinterpdst] ].
              rewrite Hwdst in Hwdst'; inv Hwdst'.
              rewrite lookup_insert_ne in Hincrement1; auto.
              rewrite HPC in Hincrement1. destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite lookup_insert_ne in Hincrement2; auto.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              generalize (Hsregs _ _ HPC). intros HPC'.
              rewrite HPC' in HXX; inv HXX. rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              - econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|].
                + eexists; split; simpl; eauto.
                + rewrite lookup_insert_ne //. destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert|].
                  * eexists; split; simpl; eauto.
                  * rewrite lookup_insert_ne //.
              - intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
                rewrite !(lookup_insert_ne _ PC); auto.
                destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
                rewrite !lookup_insert_ne; auto. } }
        destruct (Addr_le_dec aa' aa); cycle 1.
        { destruct AA as [-> ->]. econstructor.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        { destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          * intros _.
            eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|].
            { destruct (Hregsdef PC) as [wPC [HPC' HinterpPC] ].
              rewrite HPC in HPC'; inv HPC'.
              destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite lookup_insert in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              inv HXX. rewrite Hap1 in Hap1'; inv Hap1'.
              rewrite !insert_insert.
              econstructor; eauto.
              - econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|].
                + eexists; split; simpl; eauto.
                  repeat split; simpl; auto.
                  destruct ppp; simpl in HisU; try congruence.
                  rewrite Hwdst in HPC; inv HPC. auto.
                + rewrite lookup_insert_ne //.
              - intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
                rewrite !(lookup_insert_ne _ PC) //. auto. }
            { destruct (Hregsdef PC) as [wPC [HPC' HinterpPC] ].
              rewrite HPC in HPC'; inv HPC'.
              destruct (Hregsdef dst) as [wdst' [Hwdst' Hinterpdst] ].
              rewrite Hwdst in Hwdst'; inv Hwdst'.
              rewrite lookup_insert_ne in Hincrement1; auto.
              rewrite HPC in Hincrement1. destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite lookup_insert_ne in Hincrement2; auto.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              generalize (Hsregs _ _ HPC). intros HPC'.
              rewrite HPC' in HXX; inv HXX. rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              - econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|].
                + eexists; split; simpl; eauto.
                + rewrite lookup_insert_ne //. destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert|].
                  * eexists; split; simpl; eauto.
                  * rewrite lookup_insert_ne //.
              - intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
                rewrite !(lookup_insert_ne _ PC); auto.
                destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
                rewrite !lookup_insert_ne; auto. } }
      + destruct (perm_eq_dec p0 E); [subst p0|].
        { destruct AA as [-> ->]. econstructor.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (a2 + nn)%a as [aa'|] eqn:Haa'; cycle 1.
        { destruct AA as [-> ->]. econstructor.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (incrementPC (<[dst:=inr (Stk n p0 a0 a1 aa')]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        { assert (c1 = lang.Failed ∧ c2 = Failed) as [-> ->] by (destruct (isU p0); destruct (Addr_le_dec aa' a2); auto).
          econstructor.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (isU p0) eqn:HisU; cycle 1.
        { destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          * intros _.
            eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|].
            { rewrite HPC in Hwdst; inv Hwdst. }
            { destruct (Hregsdef PC) as [wPC [HPC' HinterpPC] ].
              rewrite HPC in HPC'; inv HPC'.
              destruct (Hregsdef dst) as [wdst' [Hwdst' Hinterpdst] ].
              rewrite Hwdst in Hwdst'; inv Hwdst'.
              rewrite lookup_insert_ne in Hincrement1; auto.
              rewrite HPC in Hincrement1. destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite lookup_insert_ne in Hincrement2; auto.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              generalize (Hsregs _ _ HPC). intros HPC'.
              rewrite HPC' in HXX; inv HXX. rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              - econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|].
                + eexists; split; simpl; eauto.
                + rewrite lookup_insert_ne //. destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert|].
                  * eexists; split; simpl; eauto.
                    simpl in Hinterpdst. destruct Hinterpdst as [? [? [? ?] ] ].
                    do 3 (split; auto). simpl. intros; apply H6; auto.
                    destruct p0; simpl in HisU; try congruence; auto.
                  * rewrite lookup_insert_ne //.
              - intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
                rewrite !(lookup_insert_ne _ PC); auto.
                destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
                rewrite !lookup_insert_ne; auto. } }
        destruct (Addr_le_dec aa' a2); cycle 1.
        { destruct AA as [-> ->]. econstructor.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        { destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          * intros _.
            eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|].
            { rewrite HPC in Hwdst; inv Hwdst. }
            { destruct (Hregsdef PC) as [wPC [HPC' HinterpPC] ].
              rewrite HPC in HPC'; inv HPC'.
              destruct (Hregsdef dst) as [wdst' [Hwdst' Hinterpdst] ].
              rewrite Hwdst in Hwdst'; inv Hwdst'.
              rewrite lookup_insert_ne in Hincrement1; auto.
              rewrite HPC in Hincrement1. destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite lookup_insert_ne in Hincrement2; auto.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              generalize (Hsregs _ _ HPC). intros HPC'.
              rewrite HPC' in HXX; inv HXX. rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              - econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|].
                + eexists; split; simpl; eauto.
                + rewrite lookup_insert_ne //. destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert|].
                  * eexists; split; simpl; eauto.
                    destruct Hinterpdst as [? [? [? ?] ] ].
                    do 3 (split; auto). simpl; intros; eapply H6.
                    simpl. clear -HisU H7 l; destruct p0; try congruence; auto; solve_addr.
                  * rewrite lookup_insert_ne //.
              - intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
                rewrite !(lookup_insert_ne _ PC); auto.
                destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
                rewrite !lookup_insert_ne; auto. } }
    - (* Restrict *)
      assert (AA: match reg1 !! dst with
                  | Some (inr (Regular (pp, gg, bb, ee, aa))) =>
                    if perm_eq_dec pp E then c1 = lang.Failed /\ c2 = Failed else
                    match lang.z_of_argument reg1 r with
                    | Some nn => if PermPairFlowsTo (decodePermPair nn) (pp, gg) then
                      match incrementPC (<[dst:=inr (Regular ((decodePermPair nn), bb, ee, aa))]> reg1) with
                      | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inr ((decodePermPair nn), bb, ee, aa)]> reg2) = Some reg2' /\ mem2' = mem2
                      | None => c1 = lang.Failed /\ c2 = Failed
                      end
                    else c1 = lang.Failed /\ c2 = Failed
                    | None => c1 = lang.Failed /\ c2 = Failed
                    end
                  | Some (inr (Stk dd pp bb ee aa)) =>
                    if perm_eq_dec pp E then c1 = lang.Failed /\ c2 = Failed else
                    match lang.z_of_argument reg1 r with
                    | Some nn => if PermPairFlowsTo (decodePermPair nn) (pp, Directed) then
                      match incrementPC (<[dst:=inr (Stk dd (decodePermPair nn).1 bb ee aa)]> reg1) with
                      | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inr ((decodePermPair nn), bb, ee, aa)]> reg2) = Some reg2' /\ mem2' = mem2
                      | None => c1 = lang.Failed /\ c2 = Failed
                      end
                    else c1 = lang.Failed /\ c2 = Failed
                    | None => c1 = lang.Failed /\ c2 = Failed
                    end
                  | _ => c1 = lang.Failed /\ c2 = Failed
                  end).
      { destruct (Hregsdef dst) as [wdst [Hwdst _] ].
        rewrite Hwdst. generalize (Hsregs _ _ Hwdst). intros Hwdst'.
        destruct wdst; [simpl in H1, H2; rewrite /base.RegLocate Hwdst in H1; rewrite /RegLocate Hwdst' /= in H2; destruct r; inv H1; inv H2; auto|].
        destruct c; cycle 2.
        { simpl in H1, H2; rewrite /base.RegLocate Hwdst in H1; rewrite /RegLocate Hwdst' /= in H2.
          destruct r; inv H1; inv H2; auto. destruct (reg2 !! r); inv H1; auto.
          destruct s; inv H2; auto. }
        { destruct c as [ [ [ [pp gg] bb] ee] aa].
          destruct (perm_eq_dec pp E).
          - subst pp. simpl in H1, H2; rewrite /base.RegLocate Hwdst in H1; rewrite /RegLocate Hwdst' /= in H2.
            destruct r; [inv H1; inv H2; auto|].
            destruct (reg1 !! r); destruct (reg2 !! r); try (destruct s); try (destruct s0); inv H1; inv H2; auto.
          - destruct (lang.z_of_argument reg1 r) as [nn|] eqn:Hnn; cycle 1.
            + simpl in H1, H2; rewrite /base.RegLocate Hwdst in H1; rewrite /RegLocate Hwdst' /= in H2.
              destruct r; simpl in Hnn; [inv Hnn|].
              destruct (Hregsdef r) as [wr [Hwr _] ].
              rewrite Hwr in Hnn. destruct wr; inv Hnn.
              generalize (Hsregs _ _ Hwr). intros Hwr'.
              destruct (translate_word_cap c) as [c' Hc'].
              rewrite Hc' in Hwr'. rewrite Hwr in H1.
              rewrite Hwr' in H2. inv H1; inv H2; auto.
            + simpl in H1, H2; rewrite /base.RegLocate Hwdst in H1; rewrite /RegLocate Hwdst' /= in H2.
              assert ((if PermPairFlowsTo (decodePermPair nn) (pp, gg) then lang.updatePC (base.update_reg (reg1, h, stk, cs) dst (inr (Regular (decodePermPair nn, bb, ee, aa)))) else (lang.Failed, (reg1, h, stk, cs))) = (c1, (reg1', h', stk', cs')) /\ (if PermPairFlowsTo (decodePermPair nn) (pp, gg) then updatePC (update_reg (reg2, mem2) dst (inr (decodePermPair nn, bb, ee, aa))) else (Failed, (reg2, mem2))) = (c2, (reg2', mem2'))) as [X1 X2].
              { destruct r; [inv Hnn; destruct pp; try congruence; auto|].
                destruct (Hregsdef r) as [wr [Hwr _] ].
                rewrite /= Hwr in Hnn. destruct wr; inv Hnn.
                generalize (Hsregs _ _ Hwr); intro Hwr'.
                rewrite Hwr /= in H1. rewrite Hwr' /= in H2.
                destruct pp; try congruence; auto. }
              clear H1 H2.
              destruct (PermPairFlowsTo (decodePermPair nn) (pp, gg)) eqn:Hflowsto; cycle 1.
              * inv X1; inv X2; auto.
              * assert (exists w, (<[dst:=inr (Regular (decodePermPair nn, bb, ee, aa))]> reg1) !! PC = Some w /\ (<[dst:=inr ((decodePermPair nn, bb, ee, aa))]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
                { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
                  rewrite !lookup_insert_ne //. eauto. }
                rewrite /base.update_reg in X1.
                rewrite /update_reg in X2.
                destruct (incrementPC (<[dst:=inr (Regular (decodePermPair nn, bb, ee, aa))]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
                { generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
                  intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in X1.
                  erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in X2.
                  inv X1; inv X2; auto. }
                destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
                erewrite incrementPC_success_updatePC in X1; eauto.
                rewrite Hincrement2.
                eapply rules_base.incrementPC_success_updatePC in Hincrement2.
                destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
                instantiate (1 := mem2) in Z3.
                rewrite Z3 -Z4 in X2. inv X1; inv X2; repeat split; auto. }
        { destruct (perm_eq_dec p0 E).
          - subst p0. simpl in H1, H2; rewrite /base.RegLocate Hwdst in H1; rewrite /RegLocate Hwdst' /= in H2.
            destruct r; [inv H1; inv H2; auto|].
            destruct (reg1 !! r); destruct (reg2 !! r); try (destruct s); try (destruct s0); inv H1; inv H2; auto.
          - destruct (lang.z_of_argument reg1 r) as [nn|] eqn:Hnn; cycle 1.
            + simpl in H1, H2; rewrite /base.RegLocate Hwdst in H1; rewrite /RegLocate Hwdst' /= in H2.
              destruct r; simpl in Hnn; [inv Hnn|].
              destruct (Hregsdef r) as [wr [Hwr _] ].
              rewrite Hwr in Hnn. destruct wr; inv Hnn.
              generalize (Hsregs _ _ Hwr). intros Hwr'.
              destruct (translate_word_cap c) as [c' Hc'].
              rewrite Hc' in Hwr'. rewrite Hwr in H1.
              rewrite Hwr' in H2. inv H1; inv H2; auto.
            + simpl in H1, H2; rewrite /base.RegLocate Hwdst in H1; rewrite /RegLocate Hwdst' /= in H2.
              assert ((if PermPairFlowsTo (decodePermPair nn) (p0, Directed) then lang.updatePC (base.update_reg (reg1, h, stk, cs) dst (inr (Stk n (decodePermPair nn).1 a0 a1 a2))) else (lang.Failed, (reg1, h, stk, cs))) = (c1, (reg1', h', stk', cs')) /\ (if PermPairFlowsTo (decodePermPair nn) (p0, Directed) then updatePC (update_reg (reg2, mem2) dst (inr (decodePermPair nn, a0, a1, a2))) else (Failed, (reg2, mem2))) = (c2, (reg2', mem2'))) as [X1 X2].
              { destruct r; [inv Hnn; destruct p0; try congruence; auto|].
                destruct (Hregsdef r) as [wr [Hwr _] ].
                rewrite /= Hwr in Hnn. destruct wr; inv Hnn.
                generalize (Hsregs _ _ Hwr); intro Hwr'.
                rewrite Hwr /= in H1. rewrite Hwr' /= in H2.
                destruct p0; try congruence; auto. }
              clear H1 H2.
              destruct (PermPairFlowsTo (decodePermPair nn) (p0, Directed)) eqn:Hflowsto; cycle 1.
              * inv X1; inv X2; auto.
              * assert (decodePermPair nn = ((decodePermPair nn).1, Directed)) as XYZ.
                { rewrite /PermPairFlowsTo /= in Hflowsto.
                  destruct (decodePermPair nn) as [x y].
                  simpl; f_equal. simpl in Hflowsto.
                  eapply andb_true_iff in Hflowsto.
                  destruct Hflowsto as [? GG].
                  destruct y; simpl in GG; try congruence; auto. }
                assert (exists w, (<[dst:=inr (Stk n (decodePermPair nn).1 a0 a1 a2)]> reg1) !! PC = Some w /\ (<[dst:=inr ((decodePermPair nn, a0, a1, a2))]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
                { rewrite XYZ /=.
                  destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert /=; eexists; split; eauto; simpl|].
                  rewrite !lookup_insert_ne //. eauto. }
                rewrite /base.update_reg /= in X1.
                rewrite /update_reg /= in X2.
                destruct (incrementPC (<[dst:=inr (Stk n (decodePermPair nn).1 a0 a1 a2)]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
                { generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
                  intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in X1.
                  erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in X2.
                  inv X1; inv X2; auto. }
                destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
                erewrite incrementPC_success_updatePC in X1; eauto.
                rewrite Hincrement2.
                eapply rules_base.incrementPC_success_updatePC in Hincrement2.
                destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
                instantiate (1 := mem2) in Z3.
                rewrite Z3 -Z4 in X2. inv X1; inv X2; repeat split; auto. } }
      clear H1 H2. destruct (Hregsdef dst) as [wdst [Hwdst Hinterpdst] ].
      rewrite Hwdst in AA.
      destruct wdst.
      + destruct AA as [-> ->]. econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate.
      + destruct (translate_word_cap c) as [c' Hc'].
        generalize (Hsregs _ _ Hwdst). intro Hwdst'.
        destruct c; cycle 2.
        * destruct AA as [-> ->]. econstructor.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        * destruct c as [ [ [ [pp gg] bb] ee] aa].
          destruct (perm_eq_dec pp E).
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (lang.z_of_argument reg1 r) as [nn|] eqn:Harg1; cycle 1.
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (PermPairFlowsTo (decodePermPair nn) (pp, gg)) eqn:Hflowsto; cycle 1.
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (incrementPC (<[dst:=inr (Regular (decodePermPair nn, bb, ee, aa))]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          eapply incrementPC_inv_Some in Hincrement1.
          destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|].
          { destruct (decodePermPair nn) as [px gx].
            destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
            eapply rules_base.incrementPC_Some_inv in Hincrement2.
            destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
            rewrite lookup_insert in Z1. rewrite insert_insert in Z3. inv Z1.
            rewrite Hap1 in Z2; inv Z2.
            destruct (Hregsdef PC) as [wpc [Hwpc HinterpPC] ].
            rewrite HPC in Hwpc; inv Hwpc. simpl in HinterpPC.
            econstructor; eauto.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - intros _. econstructor; eauto.
              + rewrite insert_insert. econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|].
                * eexists; split; simpl; eauto.
                  rewrite HPC in Hwdst; inv Hwdst.
                  destruct HinterpPC.
                  repeat split; simpl; auto.
                  rewrite /PermPairFlowsTo /= in Hflowsto.
                  eapply andb_true_iff in Hflowsto. destruct Hflowsto.
                  destruct X1 as [? [? [? [? ?] ] ] ].
                  destruct pp; destruct p'; simpl in H2; try congruence; auto.
                * rewrite lookup_insert_ne //.
              + rewrite insert_insert. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|].
                rewrite !lookup_insert_ne; auto. }
          { rewrite lookup_insert_ne in Hincrement1; auto.
            rewrite HPC in Hincrement1. destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
            eapply rules_base.incrementPC_Some_inv in Hincrement2.
            destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
            rewrite lookup_insert_ne in Z1; auto.
            generalize (Hsregs _ _ HPC). intros HPC'.
            rewrite HPC' in Z1; inv Z1.
            rewrite Hap1 in Z2; inv Z2.
            econstructor; eauto.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - intros _. econstructor; eauto.
              + econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
                * eexists; split; eauto. destruct (Hregsdef PC) as [wpc [Hwpc HinterpPC] ].
                  rewrite HPC in Hwpc; inv Hwpc; auto.
                * destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
                  eexists; split; eauto. simpl. simpl in Hinterpdst.
                  destruct (decodePermPair nn) as [px gx] eqn:Hpermpair.
                  destruct Hinterpdst. split; auto.
                  destruct pp; destruct px; simpl in H0; simpl in Hflowsto; try congruence; auto.
              + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto| rewrite !(lookup_insert_ne _ PC); auto].
                destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert; inversion 1; auto| rewrite !lookup_insert_ne; auto]. }
        * destruct (perm_eq_dec p0 E).
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (lang.z_of_argument reg1 r) as [nn|] eqn:Harg1; cycle 1.
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (PermPairFlowsTo (decodePermPair nn) (p0, Directed)) eqn:Hflowsto; cycle 1.
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (incrementPC (<[dst:=inr (Stk n (decodePermPair nn).1 a0 a1 a2)]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          eapply incrementPC_inv_Some in Hincrement1.
          destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|].
          { rewrite HPC in Hwdst; inv Hwdst. }
          { rewrite lookup_insert_ne in Hincrement1; auto.
            rewrite HPC in Hincrement1. destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
            eapply rules_base.incrementPC_Some_inv in Hincrement2.
            destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
            rewrite lookup_insert_ne in Z1; auto.
            generalize (Hsregs _ _ HPC). intros HPC'.
            rewrite HPC' in Z1; inv Z1.
            rewrite Hap1 in Z2; inv Z2.
            econstructor; eauto.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - intros _. econstructor; eauto.
              + econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
                * eexists; split; eauto. destruct (Hregsdef PC) as [wpc [Hwpc HinterpPC] ].
                  rewrite HPC in Hwpc; inv Hwpc; auto.
                * destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
                  eexists; split; eauto. simpl. simpl in Hinterpdst.
                  destruct (decodePermPair nn) as [px gx] eqn:Hpermpair.
                  destruct Hinterpdst as [? [? [? ?] ] ]. split; auto.
                  split; auto. split; auto. simpl. intros; apply H3.
                  rewrite /PermPairFlowsTo /= in Hflowsto.
                  eapply andb_true_iff in Hflowsto; destruct Hflowsto.
                  clear -H6 H5; destruct px; destruct p0; simpl in H6; try congruence; solve_addr.
              + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto| rewrite !(lookup_insert_ne _ PC); auto].
                destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert; inversion 1; auto| rewrite !lookup_insert_ne; auto].
                simpl. destruct (decodePermPair) as [px gx]; simpl; repeat f_equal.
                rewrite /PermPairFlowsTo /= in Hflowsto. apply andb_true_iff in Hflowsto.
                destruct Hflowsto. destruct gx; simpl in H3; try congruence; auto. }
    - (* Subseg *)
      assert (AA: match reg1 !! dst with
                  | Some (inr (Regular (pp, gg, bb, ee, aa))) =>
                    if perm_eq_dec pp E then c1 = lang.Failed /\ c2 = Failed
                    else match addr_of_argument' reg1 r1 with
                         | Some aa1 => match addr_of_argument' reg1 r2 with
                                       | Some aa2 =>
                                        if isWithin aa1 aa2 bb ee then
                                        match incrementPC (<[dst:=inr (Regular (pp, gg, aa1, aa2, aa))]> reg1) with
                                        | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inr (pp, gg, aa1, aa2, aa)]> reg2) = Some reg2' /\ mem2' = mem2
                                        | _ => c1 = lang.Failed /\ c2 = Failed
                                        end
                                        else c1 = lang.Failed /\ c2 = Failed
                                       | _ => c1 = lang.Failed /\ c2 = Failed
                                       end
                         | _ => c1 = lang.Failed /\ c2 = Failed
                         end
                  | Some (inr (Stk dd pp bb ee aa)) =>
                    if perm_eq_dec pp E then c1 = lang.Failed /\ c2 = Failed
                    else match addr_of_argument' reg1 r1 with
                         | Some aa1 => match addr_of_argument' reg1 r2 with
                                       | Some aa2 =>
                                        if isWithin aa1 aa2 bb ee then
                                        match incrementPC (<[dst:=inr (Stk dd pp aa1 aa2 aa)]> reg1) with
                                        | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inr (pp, Directed, aa1, aa2, aa)]> reg2) = Some reg2' /\ mem2' = mem2
                                        | _ => c1 = lang.Failed /\ c2 = Failed
                                        end
                                        else c1 = lang.Failed /\ c2 = Failed
                                       | _ => c1 = lang.Failed /\ c2 = Failed
                                       end
                         | _ => c1 = lang.Failed /\ c2 = Failed
                         end
                  | _ => c1 = lang.Failed /\ c2 = Failed
                  end).
      { destruct (Hregsdef dst) as [wdst [Hwdst _] ].
        rewrite Hwdst. generalize (Hsregs _ _ Hwdst). intros Hwdst'.
        rewrite /= /base.RegLocate Hwdst in H1.
        rewrite /= /RegLocate Hwdst' in H2.
        destruct wdst; [simpl in H1, H2; destruct r1; destruct r2; inv H1; inv H2; auto|].
        destruct (translate_word_cap c) as [c' Hc']. rewrite Hc' in H2.
        destruct (addr_of_argument' reg1 r1) as [aa1|] eqn:Haa1; cycle 1.
        - destruct r1; rewrite /addr_of_argument' /= in Haa1.
          + rewrite Haa1 in H1, H2.
            destruct c; [destruct c as [ [ [ [pp gg] bb] ee] aa]; inv Hc'; destruct r2; destruct (perm_eq_dec pp E); destruct pp; try (destruct (reg1 !! r)); try (destruct (reg2 !! r)); try (destruct s); try (destruct s0); inv H1; inv H2; auto| |inv Hc'; destruct r2; inv H1; inv H2; auto].
            inv Hc'. destruct (perm_eq_dec p0 E); destruct p0; destruct r2; try (destruct (reg1 !! r)); try (destruct (reg2 !! r)); try (destruct s); try (destruct s0); inv H1; inv H2; auto.
          + destruct (Hregsdef r) as [wr [Hwr _] ]; rewrite Hwr in Haa1.
            generalize (Hsregs _ _ Hwr). intros Hwr'.
            rewrite Hwr in H1. rewrite Hwr' in H2.
            destruct wr as [nn|cc]; [rewrite Haa1 in H1|destruct (translate_word_cap cc) as [cc' Hcc']; rewrite Hcc' in H2].
            * rewrite /= Haa1 in H2. destruct r2.
              { destruct c; [destruct c as [ [ [ [pp gg] bb] ee] aa]; inv Hc'; destruct (perm_eq_dec pp E); destruct pp; inv H1; inv H2; auto| |inv Hc'; inv H1; inv H2; auto].
                inv Hc'. destruct (perm_eq_dec p0 E); destruct p0; inv H1; inv H2; auto. }
              { destruct (Hregsdef r0) as [wr0 [Hwr0 _] ].
                generalize (Hsregs _ _ Hwr0). intros Hwr0'.
                rewrite Hwr0 in H1. rewrite Hwr0' in H2.
                destruct c; [destruct c as [ [ [ [pp gg] bb] ee] aa]; inv Hc'; destruct (perm_eq_dec pp E); destruct pp; try congruence; destruct wr0; try (destruct c); inv H1; inv H2; auto| |inv Hc'; inv H1; inv H2; auto].
                inv Hc'. destruct (perm_eq_dec p0 E); destruct p0; try congruence; destruct wr0; try (destruct c); inv H1; inv H2; auto. }
            * destruct c; [|inv Hc'; destruct (perm_eq_dec p0 E); destruct p0; destruct r2; inv H1; inv H2; auto|inv Hc'; destruct r2; inv H1; inv H2; auto].
              destruct c as [ [ [ [pp gg] bb] ee] aa]; inv Hc'.
              destruct (perm_eq_dec pp E); destruct pp; destruct r2; inv H1; inv H2; auto.
        - destruct (addr_of_argument' reg1 r2) as [aa2|] eqn:Haa2; cycle 1.
          + match goal with |- ?G => assert (XY: c1 = lang.Failed ∧ c2 = Failed -> G); [|apply XY; clear XY] end.
            { intro. destruct c; auto.
              destruct c as [ [ [ [pp gg] bb] ee] aa]; destruct (perm_eq_dec pp E); auto.
              destruct (perm_eq_dec p0 E); auto. }
            destruct r2; rewrite /addr_of_argument' /= in Haa2.
            * rewrite Haa2 in H1. rewrite Haa2 in H2.
              destruct r1; [rewrite /addr_of_argument' /= in Haa1; rewrite Haa1 in H1; rewrite Haa1 in H2|].
              { destruct c; [|inv Hc'; destruct p0; inv H1; inv H2; auto|inv Hc'; inv H1; inv H2; auto].
                destruct c as [ [ [ [pp gg] bb] ee] aa]; inv Hc'; destruct pp; inv H1; inv H2; auto. }
              { destruct (Hregsdef r) as [wr [Hwr _] ].
                rewrite /addr_of_argument' /= Hwr in Haa1.
                destruct wr as [nn1|]; [|inv Haa1].
                generalize (Hsregs _ _ Hwr); intros Hwr'.
                rewrite Hwr Haa1 in H1. rewrite Hwr' /= Haa1 in H2.
                destruct c; [|inv Hc'; destruct p0; inv H1; inv H2; auto|inv Hc'; inv H1; inv H2; auto].
                destruct c as [ [ [ [pp gg] bb] ee] aa]; inv Hc'; destruct pp; inv H1; inv H2; auto. }
            * destruct (Hregsdef r) as [wr [Hwr _] ].
              generalize (Hsregs _ _ Hwr). intros Hwr'.
              rewrite Hwr in Haa2. destruct wr as [nn2|]; cycle 1.
              { destruct (translate_word_cap c0) as [c0' Hc0'].
                rewrite Hc0' in Hwr'.
                rewrite Hwr /= in H1. rewrite Hwr' /= in H2.
                destruct r1.
                - destruct c; [|inv Hc'; destruct p0; inv H1; inv H2; auto|inv Hc'; inv H1; inv H2; auto].
                  destruct c as [ [ [ [pp gg] bb] ee] aa]; inv Hc'; destruct pp; inv H1; inv H2; auto.
                - destruct (Hregsdef r0) as [wr0 [Hwr0 _] ].
                  rewrite /addr_of_argument' /= Hwr0 in Haa1.
                  destruct wr0 as [nn1|]; [|inv Haa1].
                  generalize (Hsregs _ _ Hwr0). intros Hwr0'.
                  rewrite Hwr0 in H1. rewrite Hwr0' in H2.
                  destruct c; [|inv Hc'; destruct p0; inv H1; inv H2; auto|inv Hc'; inv H1; inv H2; auto].
                  destruct c as [ [ [ [pp gg] bb] ee] aa]; inv Hc'; destruct pp; inv H1; inv H2; auto. }
              { rewrite Hwr Haa2 in H1. rewrite Hwr' /= Haa2 in H2.
                destruct r1; rewrite /addr_of_argument' /= in Haa1; [rewrite Haa1 in H1; rewrite Haa1 in H2|].
                - destruct c; [|inv Hc'; destruct p0; inv H1; inv H2; auto|inv Hc'; inv H1; inv H2; auto].
                  destruct c as [ [ [ [pp gg] bb] ee] aa]; inv Hc'; destruct pp; inv H1; inv H2; auto.
                - destruct (Hregsdef r0) as [wr0 [Hwr0 _] ].
                  rewrite /addr_of_argument' /= Hwr0 in Haa1.
                  destruct wr0 as [nn1|]; [|inv Haa1].
                  generalize (Hsregs _ _ Hwr0). intros Hwr0'.
                  rewrite Hwr0 Haa1 in H1. rewrite Hwr0' /= Haa1 in H2.
                  destruct c; [|inv Hc'; destruct p0; inv H1; inv H2; auto|inv Hc'; inv H1; inv H2; auto].
                  destruct c as [ [ [ [pp gg] bb] ee] aa]; inv Hc'; destruct pp; inv H1; inv H2; auto. }
          + rewrite /base.update_reg /= in H1.
            rewrite /update_reg /= in H2.
            assert (match c with | Regular (pp, gg, bb, ee, aa) => if perm_eq_dec pp E then (lang.Failed, (reg1, h, stk, cs)) else if lang.isWithin aa1 aa2 bb ee then lang.updatePC (<[dst:=inr (Regular (pp, gg, aa1, aa2, aa))]> reg1, h, stk, cs) else (lang.Failed, (reg1, h, stk, cs)) | Stk dd pp bb ee aa => if perm_eq_dec pp E then (lang.Failed, (reg1, h, stk, cs)) else if lang.isWithin aa1 aa2 bb ee then lang.updatePC (<[dst:=inr (Stk dd pp aa1 aa2 aa)]> reg1, h, stk, cs) else (lang.Failed, (reg1, h, stk, cs)) | Ret _ _ _ => (lang.Failed, (reg1, h, stk, cs)) end = (c1, (reg1', h', stk', cs')) /\ match c' with (pp, gg, bb, ee, aa) => if perm_eq_dec pp E then (Failed, (reg2, mem2)) else if isWithin aa1 aa2 bb ee then updatePC (<[dst:=inr (pp, gg, aa1, aa2, aa)]> reg2, mem2) else (Failed, (reg2, mem2)) end = (c2, (reg2', mem2'))) as [X1 X2]; [|clear H1 H2].
            { destruct r1; destruct r2; rewrite /addr_of_argument' /= in Haa1, Haa2.
              - rewrite Haa1 in H1, H2. rewrite Haa2 in H1, H2.
                destruct c; [|inv Hc'; destruct p0; inv H1; inv H2; auto|inv Hc'; inv H1; inv H2; auto].
                destruct c as [ [ [ [pp gg] bb] ee] aa]; inv Hc'; destruct pp; inv H1; inv H2; auto.
              - destruct (Hregsdef r) as [wr [Hwr _] ].
                generalize (Hsregs _ _ Hwr). intros Hwr'.
                rewrite Hwr in Haa2. destruct wr; [|inv Haa2].
                rewrite Hwr Haa1 Haa2 in H1. rewrite Hwr' /= Haa1 Haa2 in H2.
                destruct c; [|inv Hc'; destruct p0; inv H1; inv H2; auto|inv Hc'; inv H1; inv H2; auto].
                destruct c as [ [ [ [pp gg] bb] ee] aa]; inv Hc'; destruct pp; inv H1; inv H2; auto.
              - destruct (Hregsdef r) as [wr [Hwr _] ].
                generalize (Hsregs _ _ Hwr). intros Hwr'.
                rewrite Hwr in Haa1. destruct wr; [|inv Haa1].
                rewrite Hwr Haa1 Haa2 in H1. rewrite Hwr' /= Haa1 Haa2 in H2.
                destruct c; [|inv Hc'; destruct p0; inv H1; inv H2; auto|inv Hc'; inv H1; inv H2; auto].
                destruct c as [ [ [ [pp gg] bb] ee] aa]; inv Hc'; destruct pp; inv H1; inv H2; auto.
              - destruct (Hregsdef r) as [wr [Hwr _] ].
                generalize (Hsregs _ _ Hwr). intros Hwr'.
                rewrite Hwr in Haa1. destruct wr; [|inv Haa1].
                destruct (Hregsdef r0) as [wr0 [Hwr0 _] ].
                generalize (Hsregs _ _ Hwr0). intros Hwr0'.
                rewrite Hwr0 in Haa2. destruct wr0; [|inv Haa2].
                rewrite Hwr Hwr0 Haa1 Haa2 in H1. rewrite Hwr' Hwr0' /= Haa1 Haa2 in H2.
                destruct c; [|inv Hc'; destruct p0; inv H1; inv H2; auto|inv Hc'; inv H1; inv H2; auto].
                destruct c as [ [ [ [pp gg] bb] ee] aa]; inv Hc'; destruct pp; inv H1; inv H2; auto. }
            destruct c; [|inv Hc'|inv Hc'; inv X1; inv X2; auto].
            * destruct c as [ [ [ [pp gg] bb] ee] aa]; inv Hc'; destruct (perm_eq_dec pp E); [inv X1; inv X2; auto|].
              replace lang.isWithin with isWithin in X1 by reflexivity.
              destruct (isWithin aa1 aa2 bb ee) eqn:HisWithin; [|inv X1; inv X2; auto].
              assert (exists w, (<[dst:=inr (Regular (pp, gg, aa1, aa2, aa))]> reg1) !! PC = Some w /\ (<[dst:=inr (pp, gg, aa1, aa2, aa)]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
              { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
                rewrite !lookup_insert_ne //. eauto. }
              destruct (incrementPC (<[dst:=inr (Regular (pp, gg, aa1, aa2, aa))]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
              { generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
                intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in X1.
                erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in X2.
                inv X1; inv X2; auto. }
              { destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
                erewrite incrementPC_success_updatePC in X1; eauto.
                rewrite Hincrement2.
                eapply rules_base.incrementPC_success_updatePC in Hincrement2.
                destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
                instantiate (1 := mem2) in Z3.
                rewrite Z3 -Z4 in X2. inv X1; inv X2; repeat split; auto. }
            * destruct (perm_eq_dec p0 E); [inv X1; inv X2; auto|].
              replace lang.isWithin with isWithin in X1 by reflexivity.
              destruct (isWithin aa1 aa2 a0 a1) eqn:HisWithin; [|inv X1; inv X2; auto].
              assert (exists w, (<[dst:=inr (Stk n p0 aa1 aa2 a2)]> reg1) !! PC = Some w /\ (<[dst:=inr (p0, Directed, aa1, aa2, a2)]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
              { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
                rewrite !lookup_insert_ne //. eauto. }
              destruct (incrementPC (<[dst:=inr (Stk n p0 aa1 aa2 a2)]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
              { generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
                intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in X1.
                erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in X2.
                inv X1; inv X2; auto. }
              { destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
                erewrite incrementPC_success_updatePC in X1; eauto.
                rewrite Hincrement2.
                eapply rules_base.incrementPC_success_updatePC in Hincrement2.
                destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
                instantiate (1 := mem2) in Z3.
                rewrite Z3 -Z4 in X2. inv X1; inv X2; repeat split; auto. } }
      destruct (Hregsdef dst) as [wdst [Hwdst Hinterpdst] ].
      rewrite Hwdst in AA. destruct wdst as [|cdst].
      + destruct AA as [-> ->]. econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate.
      + destruct cdst; cycle 2.
        * destruct AA as [-> ->]. econstructor.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        * generalize (Hsregs _ _ Hwdst). intros Hwdst'.
          destruct c as [ [ [ [pp gg] bb] ee] aa].
          destruct (perm_eq_dec pp E).
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (addr_of_argument' reg1 r1) as [aa1|] eqn:Haa1; cycle 1.
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (addr_of_argument' reg1 r2) as [aa2|] eqn:Haa2; cycle 1.
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (isWithin aa1 aa2 bb ee) eqn:HisWithin; cycle 1.
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (incrementPC (<[dst:=inr (Regular (pp, gg, aa1, aa2, aa))]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          destruct (Hregsdef PC) as [wpc [Hwpc HinterpPC] ].
          rewrite HPC in Hwpc; inv Hwpc.
          generalize (Hsregs _ _ HPC); intros HPC'.
          econstructor; eauto.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { intros _.
            eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|rewrite lookup_insert_ne in Hincrement1; auto].
            - rewrite HPC in Hwdst; inv Hwdst.
              destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              rewrite insert_insert.
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite lookup_insert in Hincrement2.
              destruct Hincrement2 as [? [? [? [? [? [aa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              inv HXX. rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              + econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
                eexists; split; eauto. simpl.
                simpl in HinterpPC. destruct HinterpPC as [? XXX].
                split; auto. intros. eapply XXX.
                apply andb_true_iff in HisWithin.
                clear -H3 HisWithin. destruct HisWithin.
                apply leb_addr_spec in H0. apply leb_addr_spec in H.
                solve_addr.
              + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert| rewrite !(lookup_insert_ne _ PC); auto].
                inversion 1; auto.
            - rewrite HPC in Hincrement1. destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite lookup_insert_ne in Hincrement2; auto.
              destruct Hincrement2 as [? [? [? [? [? [aa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              rewrite HPC' in HXX; inv HXX.
              rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              + econstructor; eauto.
                intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert| rewrite lookup_insert_ne; auto].
                * eexists; split; eauto.
                * destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne;auto].
                  eexists; split; eauto.
                  destruct Hinterpdst as [QQ WW].
                  split; auto. red; intros. apply WW.
                  apply andb_true_iff in HisWithin.
                  clear -HisWithin H0. destruct HisWithin.
                  apply leb_addr_spec in H. apply leb_addr_spec in H1.
                  solve_addr.
              + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert| rewrite !(lookup_insert_ne _ PC); auto].
                * inversion 1; auto.
                * destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert|rewrite !(lookup_insert_ne _ dst); auto].
                  inversion 1; auto. }
        * destruct (perm_eq_dec p0 E).
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (addr_of_argument' reg1 r1) as [aa1|] eqn:Haa1; cycle 1.
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (addr_of_argument' reg1 r2) as [aa2|] eqn:Haa2; cycle 1.
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (isWithin aa1 aa2 a0 a1) eqn:HisWithin; cycle 1.
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (incrementPC (<[dst:=inr (Stk n p0 aa1 aa2 a2)]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          destruct (Hregsdef PC) as [wpc [Hwpc HinterpPC] ].
          rewrite HPC in Hwpc; inv Hwpc.
          generalize (Hsregs _ _ HPC); intros HPC'.
          econstructor; eauto.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { intros _.
            eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|rewrite lookup_insert_ne in Hincrement1; auto].
            - rewrite HPC in Hwdst; inv Hwdst.
            - rewrite HPC in Hincrement1. destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite lookup_insert_ne in Hincrement2; auto.
              destruct Hincrement2 as [? [? [? [? [? [aa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              rewrite HPC' in HXX; inv HXX.
              rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              + econstructor; eauto.
                intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert| rewrite lookup_insert_ne; auto].
                * eexists; split; eauto.
                * destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne;auto].
                  eexists; split; eauto.
                  destruct Hinterpdst as [QQ [WW [TT ZZ] ] ].
                  split; auto. apply andb_true_iff in HisWithin.
                  destruct HisWithin. apply leb_addr_spec in H0.
                  apply leb_addr_spec in H3.
                  split; [clear -H3 WW; solve_addr|].
                  split; auto.
                  { intros. eapply TT in H6; eauto.
                    clear -H0 H6; solve_addr. }
                  { intros. apply ZZ.
                    assert ((addr_reg.min aa2 (lang.canReadUpTo (inr (Stk n p0 aa1 aa2 a2))) <= addr_reg.min a1 (lang.canReadUpTo (inr (Stk n p0 a0 a1 a2))))%a).
                    { clear -H3. destruct p0; simpl; solve_addr. }
                    clear -H5 H0 H6. solve_addr. }
              + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert| rewrite !(lookup_insert_ne _ PC); auto].
                * inversion 1; auto.
                * destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert|rewrite !(lookup_insert_ne _ dst); auto].
                  inversion 1; auto. }
    - (* IsPtr *)
      assert (AA: exists n, match incrementPC (<[dst:=inl n]> reg1) with
                              | Some reg1'' =>
                                c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inl n]> reg2) = Some reg2' /\ mem2' = mem2
                              | _ => c1 = lang.Failed /\ c2 = Failed
                              end).
      { simpl in H1, H2. destruct (Hregsdef r) as [wr [Hwr _] ].
        rewrite /base.RegLocate Hwr in H1.
        rewrite /RegLocate (Hsregs _ _ Hwr) in H2.
        set (nn := match wr with inl _ => 0%Z | inr _ => 1%Z end).
        exists nn. assert (X1: lang.updatePC (<[dst:=inl nn]> reg1, h, stk, cs) = (c1, (reg1', h', stk', cs'))) by (destruct wr; auto).
        assert (X2: updatePC (<[dst:=inl nn]> reg2, mem2) = (c2, (reg2', mem2'))) by (destruct wr; auto; destruct (translate_word_cap c) as [c' Hc']; rewrite Hc' in H2; auto).
        clear H1 H2. assert (exists w, (<[dst:=inl nn]> reg1) !! PC = Some w /\ (<[dst:=inl nn]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
        { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
          rewrite !lookup_insert_ne //. eauto. }
        destruct (incrementPC (<[dst:=inl nn]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        - generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
          intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in X1.
          erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in X2.
          inv X1; inv X2; auto.
        - destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
          erewrite incrementPC_success_updatePC in X1; eauto.
          rewrite Hincrement2.
          eapply rules_base.incrementPC_success_updatePC in Hincrement2.
          destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
          instantiate (1 := mem2) in Z3.
          rewrite Z3 -Z4 in X2. inv X1; inv X2; repeat split; auto. }
      destruct AA as [nn AA]. destruct (incrementPC (<[dst:=inl nn]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        + destruct AA as [-> ->]. econstructor.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate.
        + destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          * intros _.
            eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1; elim Hincrement1|].
            rewrite lookup_insert_ne // HPC in Hincrement1.
            destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
            eapply rules_base.incrementPC_Some_inv in Hincrement2.
            destruct Hincrement2 as [pp [gg [bb [ee [aa [aa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
            rewrite lookup_insert_ne // in HXX.
            rewrite (Hsregs _ _ HPC) /= in HXX. inv HXX.
            rewrite Hap1 in Hap1'; inv Hap1'.
            econstructor; eauto.
            { econstructor; eauto. intros rr.
              destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|].
              - eexists; split; simpl; eauto.
                repeat split; simpl; auto.
              - rewrite lookup_insert_ne //.
                destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert; eexists; split; eauto; simpl; auto|].
                rewrite lookup_insert_ne //; auto. }
            { intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
              rewrite !(lookup_insert_ne _ PC) //.
              eapply (@Hsregs_preserve_word_of_arg reg1 reg2 dst (inl nn)); auto. }
    - (* GetL *)
      assert (AA: match reg1 !! r with
                  | Some (inr _) =>
                    exists n, match incrementPC (<[dst:=inl n]> reg1) with
                              | Some reg1'' =>
                                c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inl n]> reg2) = Some reg2' /\ mem2' = mem2
                              | _ => c1 = lang.Failed /\ c2 = Failed
                              end
                  | _ => c1 = lang.Failed /\ c2 = Failed
                  end).
      { simpl in H1, H2. destruct (Hregsdef r) as [wr [Hwr _] ].
        rewrite Hwr. rewrite /base.RegLocate Hwr in H1.
        rewrite /RegLocate (Hsregs _ _ Hwr) in H2.
        destruct wr; [inv H1; inv H2; auto|].
        destruct (translate_word_cap c) as [c' Hc'].
        rewrite Hc' in H2. set (nn := match c with Ret _ _ _ | Stk _ _ _ _ _ => encodeLoc Directed | Regular (_, l, _, _, _) => encodeLoc l end).
        exists nn. assert (X1: lang.updatePC (<[dst:=inl nn]> reg1, h, stk, cs) = (c1, (reg1', h', stk', cs'))).
        { rewrite -H1 /base.update_reg /=.
          subst nn; destruct c; auto.
          destruct c as [ [ [ [pp gg] bb] ee] aa]; auto. }
        clear H1. assert (X2: updatePC (<[dst:=inl nn]> reg2, mem2) = (c2, (reg2', mem2'))).
        { rewrite -H2 /update_reg /=.
          subst nn. destruct c; inv Hc'; auto.
          destruct c' as [ [ [ [pp gg] bb] ee] aa]; auto. }
        clear H2. assert (exists w, (<[dst:=inl nn]> reg1) !! PC = Some w /\ (<[dst:=inl nn]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
        { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
          rewrite !lookup_insert_ne //. eauto. }
        destruct (incrementPC (<[dst:=inl nn]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        - generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
          intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in X1.
          erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in X2.
          inv X1; inv X2; auto.
        - destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
          erewrite incrementPC_success_updatePC in X1; eauto.
          rewrite Hincrement2.
          eapply rules_base.incrementPC_success_updatePC in Hincrement2.
          destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
          instantiate (1 := mem2) in Z3.
          rewrite Z3 -Z4 in X2. inv X1; inv X2; repeat split; auto. }
      destruct (Hregsdef r) as [wr [Hwr Hinterpwr] ].
      rewrite Hwr in AA. destruct wr as [nr|cr].
      + destruct AA as [-> ->]. econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate.
      + destruct AA as [nn AA]. destruct (incrementPC (<[dst:=inl nn]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        * destruct AA as [-> ->]. econstructor.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        * destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { intros _.
            eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1; elim Hincrement1|].
            rewrite lookup_insert_ne // HPC in Hincrement1.
            destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
            eapply rules_base.incrementPC_Some_inv in Hincrement2.
            destruct Hincrement2 as [pp [gg [bb [ee [aa [aa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
            rewrite lookup_insert_ne // in HXX.
            rewrite (Hsregs _ _ HPC) /= in HXX. inv HXX.
            rewrite Hap1 in Hap1'; inv Hap1'.
            econstructor; eauto.
            + econstructor; eauto. intros rr.
              destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|].
              * eexists; split; simpl; eauto.
                repeat split; simpl; auto.
              * rewrite lookup_insert_ne //.
                destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert; eexists; split; eauto; simpl; auto|].
                rewrite lookup_insert_ne //; auto.
            + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
              rewrite !(lookup_insert_ne _ PC) //.
              eapply (@Hsregs_preserve_word_of_arg reg1 reg2 dst (inl nn)); auto. }
    - (* GetP *)
      assert (AA: match reg1 !! r with
                  | Some (inr _) =>
                    exists n, match incrementPC (<[dst:=inl n]> reg1) with
                              | Some reg1'' =>
                                c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inl n]> reg2) = Some reg2' /\ mem2' = mem2
                              | _ => c1 = lang.Failed /\ c2 = Failed
                              end
                  | _ => c1 = lang.Failed /\ c2 = Failed
                  end).
      { simpl in H1, H2. destruct (Hregsdef r) as [wr [Hwr _] ].
        rewrite Hwr. rewrite /base.RegLocate Hwr in H1.
        rewrite /RegLocate (Hsregs _ _ Hwr) in H2.
        destruct wr; [inv H1; inv H2; auto|].
        destruct (translate_word_cap c) as [c' Hc'].
        rewrite Hc' in H2. set (nn := match c with Ret _ _ _ => encodePerm E | Stk _ p _ _ _ | Regular (p, _, _, _, _) => encodePerm p end).
        exists nn. assert (X1: lang.updatePC (<[dst:=inl nn]> reg1, h, stk, cs) = (c1, (reg1', h', stk', cs'))).
        { rewrite -H1 /base.update_reg /=.
          subst nn; destruct c; auto.
          destruct c as [ [ [ [pp gg] bb] ee] aa]; auto. }
        clear H1. assert (X2: updatePC (<[dst:=inl nn]> reg2, mem2) = (c2, (reg2', mem2'))).
        { rewrite -H2 /update_reg /=.
          subst nn. destruct c; inv Hc'; auto.
          destruct c' as [ [ [ [pp gg] bb] ee] aa]; auto. }
        clear H2. assert (exists w, (<[dst:=inl nn]> reg1) !! PC = Some w /\ (<[dst:=inl nn]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
        { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
          rewrite !lookup_insert_ne //. eauto. }
        destruct (incrementPC (<[dst:=inl nn]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        - generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
          intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in X1.
          erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in X2.
          inv X1; inv X2; auto.
        - destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
          erewrite incrementPC_success_updatePC in X1; eauto.
          rewrite Hincrement2.
          eapply rules_base.incrementPC_success_updatePC in Hincrement2.
          destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
          instantiate (1 := mem2) in Z3.
          rewrite Z3 -Z4 in X2. inv X1; inv X2; repeat split; auto. }
      destruct (Hregsdef r) as [wr [Hwr Hinterpwr] ].
      rewrite Hwr in AA. destruct wr as [nr|cr].
      + destruct AA as [-> ->]. econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate.
      + destruct AA as [nn AA]. destruct (incrementPC (<[dst:=inl nn]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        * destruct AA as [-> ->]. econstructor.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        * destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { intros _.
            eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1; elim Hincrement1|].
            rewrite lookup_insert_ne // HPC in Hincrement1.
            destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
            eapply rules_base.incrementPC_Some_inv in Hincrement2.
            destruct Hincrement2 as [pp [gg [bb [ee [aa [aa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
            rewrite lookup_insert_ne // in HXX.
            rewrite (Hsregs _ _ HPC) /= in HXX. inv HXX.
            rewrite Hap1 in Hap1'; inv Hap1'.
            econstructor; eauto.
            + econstructor; eauto. intros rr.
              destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|].
              * eexists; split; simpl; eauto.
                repeat split; simpl; auto.
              * rewrite lookup_insert_ne //.
                destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert; eexists; split; eauto; simpl; auto|].
                rewrite lookup_insert_ne //; auto.
            + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
              rewrite !(lookup_insert_ne _ PC) //.
              eapply (@Hsregs_preserve_word_of_arg reg1 reg2 dst (inl nn)); auto. }
    - (* GetB *)
      assert (AA: match reg1 !! r with
                  | Some (inr _) =>
                    exists n, match incrementPC (<[dst:=inl n]> reg1) with
                              | Some reg1'' =>
                                c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inl n]> reg2) = Some reg2' /\ mem2' = mem2
                              | _ => c1 = lang.Failed /\ c2 = Failed
                              end
                  | _ => c1 = lang.Failed /\ c2 = Failed
                  end).
      { simpl in H1, H2. destruct (Hregsdef r) as [wr [Hwr _] ].
        rewrite Hwr. rewrite /base.RegLocate Hwr in H1.
        rewrite /RegLocate (Hsregs _ _ Hwr) in H2.
        destruct wr; [inv H1; inv H2; auto|].
        destruct (translate_word_cap c) as [c' Hc'].
        rewrite Hc' in H2. set (nn := match c with Ret b _ _ | Stk _ _ b _ _ | Regular (_, _, b, _, _) => z_of b end).
        exists nn. assert (X1: lang.updatePC (<[dst:=inl nn]> reg1, h, stk, cs) = (c1, (reg1', h', stk', cs'))).
        { rewrite -H1 /base.update_reg /=.
          subst nn; destruct c; auto; [| destruct a0; auto..].
          destruct c as [ [ [ [pp gg] bb] ee] aa]; auto.
          destruct bb; auto. }
        clear H1. assert (X2: updatePC (<[dst:=inl nn]> reg2, mem2) = (c2, (reg2', mem2'))).
        { rewrite -H2 /update_reg /=.
          subst nn. destruct c; inv Hc'; auto; [| destruct a0; auto..].
          destruct c' as [ [ [ [pp gg] bb] ee] aa]; auto.
          destruct bb; auto. }
        clear H2. assert (exists w, (<[dst:=inl nn]> reg1) !! PC = Some w /\ (<[dst:=inl nn]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
        { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
          rewrite !lookup_insert_ne //. eauto. }
        destruct (incrementPC (<[dst:=inl nn]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        - generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
          intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in X1.
          erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in X2.
          inv X1; inv X2; auto.
        - destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
          erewrite incrementPC_success_updatePC in X1; eauto.
          rewrite Hincrement2.
          eapply rules_base.incrementPC_success_updatePC in Hincrement2.
          destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
          instantiate (1 := mem2) in Z3.
          rewrite Z3 -Z4 in X2. inv X1; inv X2; repeat split; auto. }
      destruct (Hregsdef r) as [wr [Hwr Hinterpwr] ].
      rewrite Hwr in AA. destruct wr as [nr|cr].
      + destruct AA as [-> ->]. econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate.
      + destruct AA as [nn AA]. destruct (incrementPC (<[dst:=inl nn]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        * destruct AA as [-> ->]. econstructor.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        * destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { intros _.
            eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1; elim Hincrement1|].
            rewrite lookup_insert_ne // HPC in Hincrement1.
            destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
            eapply rules_base.incrementPC_Some_inv in Hincrement2.
            destruct Hincrement2 as [pp [gg [bb [ee [aa [aa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
            rewrite lookup_insert_ne // in HXX.
            rewrite (Hsregs _ _ HPC) /= in HXX. inv HXX.
            rewrite Hap1 in Hap1'; inv Hap1'.
            econstructor; eauto.
            + econstructor; eauto. intros rr.
              destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|].
              * eexists; split; simpl; eauto.
                repeat split; simpl; auto.
              * rewrite lookup_insert_ne //.
                destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert; eexists; split; eauto; simpl; auto|].
                rewrite lookup_insert_ne //; auto.
            + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
              rewrite !(lookup_insert_ne _ PC) //.
              eapply (@Hsregs_preserve_word_of_arg reg1 reg2 dst (inl nn)); auto. }
    - (* GetE *)
      assert (AA: match reg1 !! r with
                  | Some (inr _) =>
                    exists n, match incrementPC (<[dst:=inl n]> reg1) with
                              | Some reg1'' =>
                                c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inl n]> reg2) = Some reg2' /\ mem2' = mem2
                              | _ => c1 = lang.Failed /\ c2 = Failed
                              end
                  | _ => c1 = lang.Failed /\ c2 = Failed
                  end).
      { simpl in H1, H2. destruct (Hregsdef r) as [wr [Hwr _] ].
        rewrite Hwr. rewrite /base.RegLocate Hwr in H1.
        rewrite /RegLocate (Hsregs _ _ Hwr) in H2.
        destruct wr; [inv H1; inv H2; auto|].
        destruct (translate_word_cap c) as [c' Hc'].
        rewrite Hc' in H2. set (nn := match c with Ret _ e _ | Stk _ _ _ e _ | Regular (_, _, _, e, _) => z_of e end).
        exists nn. assert (X1: lang.updatePC (<[dst:=inl nn]> reg1, h, stk, cs) = (c1, (reg1', h', stk', cs'))).
        { rewrite -H1 /base.update_reg /=.
          subst nn; destruct c; auto; [| destruct a1; auto..].
          destruct c as [ [ [ [pp gg] bb] ee] aa]; auto.
          destruct ee; auto. }
        clear H1. assert (X2: updatePC (<[dst:=inl nn]> reg2, mem2) = (c2, (reg2', mem2'))).
        { rewrite -H2 /update_reg /=.
          subst nn. destruct c; inv Hc'; auto; [| destruct a1; auto..].
          destruct c' as [ [ [ [pp gg] bb] ee] aa]; auto.
          destruct ee; auto. }
        clear H2. assert (exists w, (<[dst:=inl nn]> reg1) !! PC = Some w /\ (<[dst:=inl nn]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
        { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
          rewrite !lookup_insert_ne //. eauto. }
        destruct (incrementPC (<[dst:=inl nn]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        - generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
          intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in X1.
          erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in X2.
          inv X1; inv X2; auto.
        - destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
          erewrite incrementPC_success_updatePC in X1; eauto.
          rewrite Hincrement2.
          eapply rules_base.incrementPC_success_updatePC in Hincrement2.
          destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
          instantiate (1 := mem2) in Z3.
          rewrite Z3 -Z4 in X2. inv X1; inv X2; repeat split; auto. }
      destruct (Hregsdef r) as [wr [Hwr Hinterpwr] ].
      rewrite Hwr in AA. destruct wr as [nr|cr].
      + destruct AA as [-> ->]. econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate.
      + destruct AA as [nn AA]. destruct (incrementPC (<[dst:=inl nn]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        * destruct AA as [-> ->]. econstructor.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        * destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { intros _.
            eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1; elim Hincrement1|].
            rewrite lookup_insert_ne // HPC in Hincrement1.
            destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
            eapply rules_base.incrementPC_Some_inv in Hincrement2.
            destruct Hincrement2 as [pp [gg [bb [ee [aa [aa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
            rewrite lookup_insert_ne // in HXX.
            rewrite (Hsregs _ _ HPC) /= in HXX. inv HXX.
            rewrite Hap1 in Hap1'; inv Hap1'.
            econstructor; eauto.
            + econstructor; eauto. intros rr.
              destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|].
              * eexists; split; simpl; eauto.
                repeat split; simpl; auto.
              * rewrite lookup_insert_ne //.
                destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert; eexists; split; eauto; simpl; auto|].
                rewrite lookup_insert_ne //; auto.
            + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
              rewrite !(lookup_insert_ne _ PC) //.
              eapply (@Hsregs_preserve_word_of_arg reg1 reg2 dst (inl nn)); auto. }
    - (* GetA *)
      assert (AA: match reg1 !! r with
                  | Some (inr _) =>
                    exists n, match incrementPC (<[dst:=inl n]> reg1) with
                              | Some reg1'' =>
                                c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inl n]> reg2) = Some reg2' /\ mem2' = mem2
                              | _ => c1 = lang.Failed /\ c2 = Failed
                              end
                  | _ => c1 = lang.Failed /\ c2 = Failed
                  end).
      { simpl in H1, H2. destruct (Hregsdef r) as [wr [Hwr _] ].
        rewrite Hwr. rewrite /base.RegLocate Hwr in H1.
        rewrite /RegLocate (Hsregs _ _ Hwr) in H2.
        destruct wr; [inv H1; inv H2; auto|].
        destruct (translate_word_cap c) as [c' Hc'].
        rewrite Hc' in H2. set (nn := match c with Ret _ _ a | Stk _ _ _ _ a | Regular (_, _, _, _, a) => z_of a end).
        exists nn. assert (X1: lang.updatePC (<[dst:=inl nn]> reg1, h, stk, cs) = (c1, (reg1', h', stk', cs'))).
        { rewrite -H1 /base.update_reg /=.
          subst nn; destruct c; auto; [| destruct a2; auto..].
          destruct c as [ [ [ [pp gg] bb] ee] aa]; auto.
          destruct aa; auto. }
        clear H1. assert (X2: updatePC (<[dst:=inl nn]> reg2, mem2) = (c2, (reg2', mem2'))).
        { rewrite -H2 /update_reg /=.
          subst nn. destruct c; inv Hc'; auto; [| destruct a2; auto..].
          destruct c' as [ [ [ [pp gg] bb] ee] aa]; auto.
          destruct aa; auto. }
        clear H2. assert (exists w, (<[dst:=inl nn]> reg1) !! PC = Some w /\ (<[dst:=inl nn]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
        { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
          rewrite !lookup_insert_ne //. eauto. }
        destruct (incrementPC (<[dst:=inl nn]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        - generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
          intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in X1.
          erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in X2.
          inv X1; inv X2; auto.
        - destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
          erewrite incrementPC_success_updatePC in X1; eauto.
          rewrite Hincrement2.
          eapply rules_base.incrementPC_success_updatePC in Hincrement2.
          destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
          instantiate (1 := mem2) in Z3.
          rewrite Z3 -Z4 in X2. inv X1; inv X2; repeat split; auto. }
      destruct (Hregsdef r) as [wr [Hwr Hinterpwr] ].
      rewrite Hwr in AA. destruct wr as [nr|cr].
      + destruct AA as [-> ->]. econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate.
      + destruct AA as [nn AA]. destruct (incrementPC (<[dst:=inl nn]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        * destruct AA as [-> ->]. econstructor.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        * destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { intros _.
            eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1; elim Hincrement1|].
            rewrite lookup_insert_ne // HPC in Hincrement1.
            destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
            eapply rules_base.incrementPC_Some_inv in Hincrement2.
            destruct Hincrement2 as [pp [gg [bb [ee [aa [aa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
            rewrite lookup_insert_ne // in HXX.
            rewrite (Hsregs _ _ HPC) /= in HXX. inv HXX.
            rewrite Hap1 in Hap1'; inv Hap1'.
            econstructor; eauto.
            + econstructor; eauto. intros rr.
              destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|].
              * eexists; split; simpl; eauto.
                repeat split; simpl; auto.
              * rewrite lookup_insert_ne //.
                destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert; eexists; split; eauto; simpl; auto|].
                rewrite lookup_insert_ne //; auto.
            + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
              rewrite !(lookup_insert_ne _ PC) //.
              eapply (@Hsregs_preserve_word_of_arg reg1 reg2 dst (inl nn)); auto. }
    - (* Fail *)
      simpl in H1, H2. inv H1; inv H2.
      econstructor.
      + eapply sim_expr_exec_inv in Hsexpr. subst K.
        simpl. repeat econstructor.
      + rewrite can_step_fill /can_step /=; intros [A | A]; discriminate.
    - (* Halt *)
      simpl in H1, H2. inv H1; inv H2.
      econstructor.
      + eapply sim_expr_exec_inv in Hsexpr. subst K.
        simpl. repeat econstructor.
      + rewrite can_step_fill /can_step /=; intros [A | A]; discriminate.
    - (* LoadU *)
      destruct (Hregsdef src) as [wsrc [Hwsrc Hinterpsrc] ].
      generalize (Hsregs _ _ Hwsrc). intros Hwsrc'.
      assert (AA: match wsrc with
                  | inr (Regular (pp, gg, bb, ee, aa)) =>
                    if isU pp then
                      match lang.z_of_argument reg1 offs with
                      | Some noffs =>
                        match verify_access (LoadU_access bb ee aa noffs) with
                        | Some aa' =>
                          exists waa, h !! aa' = Some waa /\ interp waa h stk cs /\ match incrementPC (<[dst:=waa]> reg1) with
                            | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=translate_word waa]> reg2) = Some reg2' /\ mem2' = mem2
                            | None => c1 = lang.Failed /\ c2 = Failed
                            end
                        | None => c1 = lang.Failed /\ c2 = Failed
                        end
                      | None => c1 = lang.Failed /\ c2 = Failed
                      end
                    else c1 = lang.Failed /\ c2 = Failed
                  | inr (Stk dd pp bb ee aa) =>
                    if isU pp then
                      match lang.z_of_argument reg1 offs with
                      | Some noffs =>
                        match verify_access (LoadU_access bb ee aa noffs) with
                        | Some aa' =>
                          exists xstk, stack dd ((reg1, stk)::cs) = Some xstk /\
                          exists waa, xstk !! aa' = Some waa /\ interp waa h stk cs /\ match incrementPC (<[dst:=waa]> reg1) with
                            | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=translate_word waa]> reg2) = Some reg2' /\ mem2' = mem2
                            | None => c1 = lang.Failed /\ c2 = Failed
                            end
                        | None => c1 = lang.Failed /\ c2 = Failed
                        end
                      | None => c1 = lang.Failed /\ c2 = Failed
                      end
                    else c1 = lang.Failed /\ c2 = Failed
                  | _ => c1 = lang.Failed /\ c2 = Failed
                  end).
      { destruct wsrc; [rewrite /= /base.RegLocate Hwsrc /= in H1; rewrite /= /RegLocate Hwsrc' /= in H2; inv H1; inv H2; auto|].
        destruct c; [|simpl in Hwsrc'|simpl in Hwsrc'; rewrite /= /base.RegLocate Hwsrc /= in H1; rewrite /= /RegLocate Hwsrc' /= in H2; inv H1; inv H2; auto].
        - destruct c as [ [ [ [px gx] bx] ex] ax].
          rewrite /= /base.RegLocate Hwsrc /= in H1; rewrite /= /RegLocate Hwsrc' /= in H2.
          destruct (isU px) eqn:HisU; [|inv H1; inv H2; auto].
          assert (UU: z_of_argument reg2 offs = lang.z_of_argument reg1 offs).
          { destruct offs; simpl; auto.
            destruct (Hregsdef r) as [wr [Hwr _] ].
            generalize (Hsregs _ _ Hwr). intros Hwr'.
            rewrite Hwr Hwr'. destruct wr; [simpl; auto|].
            destruct (translate_word_cap c) as [c' ->]. auto. }
          rewrite UU in H2.
          destruct (lang.z_of_argument reg1 offs) as [noffs|] eqn:Hoffs; [|inv H1; inv H2; auto].
          fold verify_access in H1.
          destruct (verify_access (LoadU_access bx ex ax noffs)) as [aa'|] eqn:Hverify; cycle 1.
          { simpl in Hverify. rewrite Hverify in H1, H2; inv H1; inv H2; auto. }
          simpl in Hverify; rewrite Hverify in H1, H2.
          rewrite /base.MemLocate in H1.
          rewrite /MemLocate in H2.
          assert ((ax + noffs)%a = Some aa' /\ (bx <= aa')%a /\ (aa' < ax)%a /\ (ax <= ex)%a) as [Haa' [Hcond1 [Hcond2 Hcond3] ] ].
          { clear -Hverify. destruct ((ax + noffs)%a); [|inv Hverify].
            destruct (Addr_le_dec bx a); [|inv Hverify].
            destruct (Addr_lt_dec a ax); [|inv Hverify].
            destruct (Addr_le_dec ax ex); inv Hverify; auto. }
          destruct Hinterpsrc as [T1 T2].
          generalize (T2 aa' ltac:(clear -Hcond1 Hcond2 Hcond3; solve_addr)).
          intro Hwaa'. apply elem_of_dom in Hwaa'.
          destruct Hwaa' as [waa' Hwaa'].
          destruct (Hsh _ _ Hwaa') as [Hwaa'' [U1 [U2 U3] ] ].
          rewrite Hwaa'. eexists; split; auto.
          split; auto.
          { destruct waa'; simpl; auto.
            destruct c; simpl in U2; try congruence. auto. }
          rewrite Hwaa' /base.update_reg /= in H1.
          rewrite Hwaa'' /update_reg /= in H2.
          assert (exists w, (<[dst:=waa']> reg1) !! PC = Some w /\ (<[dst:=translate_word waa']> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
          { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
            rewrite !lookup_insert_ne //. eauto. }
          destruct (incrementPC (<[dst:=waa']> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
          { generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
            intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in H1.
            erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in H2.
            inv H1; inv H2; auto. }
          { destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
            erewrite incrementPC_success_updatePC in H1; eauto.
            rewrite Hincrement2.
            eapply rules_base.incrementPC_success_updatePC in Hincrement2.
            destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
            instantiate (1 := mem2) in Z3.
            rewrite Z3 -Z4 in H2. inv H1; inv H2; repeat split; auto. }
        - rewrite /= /base.RegLocate Hwsrc /= in H1; rewrite /= /RegLocate Hwsrc' /= in H2.
          destruct (isU p0) eqn:HisU; [|inv H1; inv H2; auto].
          assert (UU: z_of_argument reg2 offs = lang.z_of_argument reg1 offs).
          { destruct offs; simpl; auto.
            destruct (Hregsdef r) as [wr [Hwr _] ].
            generalize (Hsregs _ _ Hwr). intros Hwr'.
            rewrite Hwr Hwr'. destruct wr; [simpl; auto|].
            destruct (translate_word_cap c) as [c' ->]. auto. }
          rewrite UU in H2.
          destruct (lang.z_of_argument reg1 offs) as [noffs|] eqn:Hoffs; [|inv H1; inv H2; auto].
          destruct (verify_access (LoadU_access a0 a1 a2 noffs)) as [aa'|] eqn:Hverify; cycle 1.
          { simpl in Hverify. rewrite Hverify in H1, H2; inv H1; inv H2; auto. }
          simpl in Hverify; rewrite Hverify in H1, H2.
          rewrite /base.MemLocate in H1.
          rewrite /MemLocate in H2.
          assert ((a2 + noffs)%a = Some aa' /\ (a0 <= aa')%a /\ (aa' < a2)%a /\ (a2 <= a1)%a) as [Haa' [Hcond1 [Hcond2 Hcond3] ] ].
          { clear -Hverify. destruct ((a2 + noffs)%a); [|inv Hverify].
            destruct (Addr_le_dec a0 a); [|inv Hverify].
            destruct (Addr_lt_dec a a2); [|inv Hverify].
            destruct (Addr_le_dec a2 a1); inv Hverify; auto. }
          destruct Hinterpsrc as [T1 [T2 [T4 T3] ] ].
          simpl.
          match goal with |- context [(if ?Q then _ else _) = _] => destruct Q as [_|KK]; [auto|elim KK; auto] end.
          exists stk. split; auto.
          destruct (T3 aa' ltac:(simpl; clear -Hcond1 Hcond2 Hcond3 HisU; destruct p0; simpl in HisU; try congruence; simpl; solve_addr)) as [waa' Hwaa'].
          destruct (Hstksim _ _ Hwaa') as [Hwaa'' [U1 U2] ].
          rewrite Hwaa'. eexists; split; auto.
          split; auto.
          rewrite Hwaa' /base.update_reg /= in H1.
          rewrite Hwaa'' /update_reg /= in H2.
          assert (exists w, (<[dst:=waa']> reg1) !! PC = Some w /\ (<[dst:=translate_word waa']> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
          { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
            rewrite !lookup_insert_ne //. eauto. }
          destruct (incrementPC (<[dst:=waa']> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
          { generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
            intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in H1.
            erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in H2.
            inv H1; inv H2; auto. }
          { destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
            erewrite incrementPC_success_updatePC in H1; eauto.
            rewrite Hincrement2.
            eapply rules_base.incrementPC_success_updatePC in Hincrement2.
            destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
            instantiate (1 := mem2) in Z3.
            rewrite Z3 -Z4 in H2. inv H1; inv H2; repeat split; auto. } }
      clear H1 H2. destruct wsrc.
      { destruct AA as [-> ->]. econstructor; eauto.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
      destruct c; cycle 2.
      { destruct AA as [-> ->]. econstructor; eauto.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
      { destruct c as [ [ [ [pp gg] bb] ee] aa].
        destruct (isU pp) eqn:HisU; cycle 1.
        { destruct AA as [-> ->]. econstructor; eauto.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (lang.z_of_argument reg1 offs) as [noffs|] eqn:Hoffs; cycle 1.
        { destruct AA as [-> ->]. econstructor; eauto.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (verify_access (LoadU_access bb ee aa noffs)) as [aa'|] eqn:Haa'; cycle 1.
        { destruct AA as [-> ->]. econstructor; eauto.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct AA as [waa [Hwaa [Hinterpaa AA] ] ].
        destruct (incrementPC (<[dst:=waa]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        { destruct AA as [-> ->]. econstructor; eauto.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
        econstructor; eauto.
        { eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor. }
        { intros _. eapply incrementPC_inv_Some in Hincrement1.
          destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|].
          - destruct waa; [elim Hincrement1|].
            destruct c; [| |elim Hincrement1].
            * destruct c as [ [ [ [px gx] bx] ex] ax].
              destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite lookup_insert in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              inv HXX. rewrite Hap1 in Hap1'; inv Hap1'.
              rewrite !insert_insert.
              econstructor; eauto.
              { econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto]. }
              { intros rr; destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|rewrite !lookup_insert_ne; auto]. }
            * intros. destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite lookup_insert in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              inv HXX. rewrite Hap1 in Hap1'; inv Hap1'.
              rewrite !insert_insert.
              constructor; eauto.
              { econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; eauto].
                eexists; split; eauto.
                simpl. destruct Hinterpaa as [? [? [HH ?] ] ].
                do 3 (split; auto).
                intros; eapply H2. simpl.
                destruct X2 as [? [? [? [? ?] ] ] ].
                destruct ppp; try congruence; auto. }
              { intros rr; destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|rewrite !lookup_insert_ne; auto]. }
          - rewrite lookup_insert_ne in Hincrement1; auto.
            rewrite HPC in Hincrement1.
            destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
            eapply rules_base.incrementPC_Some_inv in Hincrement2.
            destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
            rewrite lookup_insert_ne in HXX; auto.
            generalize (Hsregs _ _ HPC). rewrite HXX.
            intro DD; inv DD. rewrite Hap1 in Hap1'; inv Hap1'.
            econstructor; eauto.
            * econstructor; eauto. intros rr.
              destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite (lookup_insert_ne _ PC); auto].
              { eexists; split; eauto. generalize (Hregsdef PC).
                intros [wpc [Hwpc HinterpPC] ]. rewrite HPC in Hwpc; inv Hwpc.
                auto. }
              destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
            * intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto| rewrite !(lookup_insert_ne _ PC); auto].
              destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert; inversion 1; auto| rewrite !lookup_insert_ne; auto]. } }
      { destruct (isU p0) eqn:HisU; cycle 1.
        { destruct AA as [-> ->]. econstructor; eauto.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (lang.z_of_argument reg1 offs) as [noffs|] eqn:Hoffs; cycle 1.
        { destruct AA as [-> ->]. econstructor; eauto.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (verify_access (LoadU_access a0 a1 a2 noffs)) as [aa'|] eqn:Haa'; cycle 1.
        { destruct AA as [-> ->]. econstructor; eauto.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct AA as [xstk [Hxstk [waa [Hwaa [Hinterpaa AA] ] ] ] ].
        destruct (incrementPC (<[dst:=waa]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        { destruct AA as [-> ->]. econstructor; eauto.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
        econstructor; eauto.
        { eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor. }
        { intros _. eapply incrementPC_inv_Some in Hincrement1.
          destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|].
          - destruct waa; [elim Hincrement1|].
            destruct c; [| |elim Hincrement1].
            * destruct c as [ [ [ [px gx] bx] ex] ax].
              destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite lookup_insert in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              inv HXX. rewrite Hap1 in Hap1'; inv Hap1'.
              rewrite !insert_insert.
              econstructor; eauto.
              { econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto]. }
              { intros rr; destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|rewrite !lookup_insert_ne; auto]. }
            * intros. destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite lookup_insert in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              inv HXX. rewrite Hap1 in Hap1'; inv Hap1'.
              rewrite !insert_insert.
              constructor; eauto.
              { econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; eauto].
                eexists; split; eauto.
                simpl. destruct Hinterpaa as [? [? [HH ?] ] ].
                do 3 (split; auto).
                intros; eapply H2. simpl.
                destruct X2 as [? [? [? [? ?] ] ] ].
                destruct ppp; try congruence; auto. }
              { intros rr; destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|rewrite !lookup_insert_ne; auto]. }
          - rewrite lookup_insert_ne in Hincrement1; auto.
            rewrite HPC in Hincrement1.
            destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
            eapply rules_base.incrementPC_Some_inv in Hincrement2.
            destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
            rewrite lookup_insert_ne in HXX; auto.
            generalize (Hsregs _ _ HPC). rewrite HXX.
            intro DD; inv DD. rewrite Hap1 in Hap1'; inv Hap1'.
            econstructor; eauto.
            * econstructor; eauto. intros rr.
              destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite (lookup_insert_ne _ PC); auto].
              { eexists; split; eauto. generalize (Hregsdef PC).
                intros [wpc [Hwpc HinterpPC] ]. rewrite HPC in Hwpc; inv Hwpc.
                auto. }
              destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
            * intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto| rewrite !(lookup_insert_ne _ PC); auto].
              destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert; inversion 1; auto| rewrite !lookup_insert_ne; auto]. } }
    - (* StoreU *)
      destruct (Hregsdef dst) as [wdst [Hwdst Hinterpdst] ].
      generalize (Hsregs _ _ Hwdst). intros Hwdst'.
      assert (exists wsrc, word_of_argument reg1 src = wsrc /\ interp wsrc h stk cs /\ rules_base.word_of_argument reg2 src = Some (translate_word wsrc)) as [wsrc [Hwsrc [Hinterpwsrc Hwsrc'] ] ].
      { destruct src; simpl; [eexists; split; eauto; simpl; eauto|].
        destruct (Hregsdef r) as [wr [Hwr Hinterpwr] ].
        generalize (Hsregs _ _ Hwr); intros Hwr'.
        rewrite /base.RegLocate Hwr. eexists; split; eauto. }
      assert (AA: match wdst with
                  | inr (Regular (pp, gg, bb, ee, aa)) =>
                    match lang.z_of_argument reg1 offs with
                    | Some noffs =>
                      match verify_access (StoreU_access bb ee aa noffs) with
                      | Some aa' =>
                        if isU pp && lang.canStoreU pp aa' wsrc then
                          if addr_eq_dec aa aa'
                          then exists aa'', (aa + 1)%a = Some aa'' /\
                            match incrementPC (<[dst:=inr (Regular (pp, gg, bb, ee, aa''))]> reg1) with
                            | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = (<[aa':=wsrc]> h) /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inr (pp, gg, bb, ee, aa'')]> reg2) = Some reg2' /\ mem2' = (<[aa':=translate_word wsrc]> mem2)
                            | _ => c1 = lang.Failed /\ c2 = Failed
                            end
                          else
                            match incrementPC reg1 with
                            | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = (<[aa':=wsrc]> h) /\ stk' = stk /\ cs' = cs /\ incrementPC' reg2 = Some reg2' /\ mem2' = (<[aa':=translate_word wsrc]> mem2)
                            | _ => c1 = lang.Failed /\ c2 = Failed
                            end
                        else c1 = lang.Failed /\ c2 = Failed
                      | _ => c1 = lang.Failed /\ c2 = Failed
                      end
                    | _ => c1 = lang.Failed /\ c2 = Failed
                    end
                  | inr (Stk dd pp bb ee aa) =>
                    match lang.z_of_argument reg1 offs with
                    | Some noffs =>
                      match verify_access (StoreU_access bb ee aa noffs) with
                      | Some aa' =>
                        if isU pp && lang.canStoreU pp aa' wsrc then
                          if addr_eq_dec aa aa'
                          then exists aa'', (aa + 1)%a = Some aa'' /\
                            match incrementPC (<[dst:=inr (Stk dd pp bb ee aa'')]> reg1) with
                            | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = (<[aa':=wsrc]> stk) /\ cs' = cs /\ incrementPC' (<[dst:=inr (pp, Directed, bb, ee, aa'')]> reg2) = Some reg2' /\ mem2' = (<[aa':=translate_word wsrc]> mem2)
                            | _ => c1 = lang.Failed /\ c2 = Failed
                            end
                          else
                            match incrementPC reg1 with
                            | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = (<[aa':=wsrc]> stk) /\ cs' = cs /\ incrementPC' reg2 = Some reg2' /\ mem2' = (<[aa':=translate_word wsrc]> mem2)
                            | _ => c1 = lang.Failed /\ c2 = Failed
                            end
                        else c1 = lang.Failed /\ c2 = Failed
                      | _ => c1 = lang.Failed /\ c2 = Failed
                      end
                    | _ => c1 = lang.Failed /\ c2 = Failed
                    end
                  | _ => c1 = lang.Failed /\ c2 = Failed
                  end).
      { rewrite /= /base.RegLocate Hwdst in H1.
        rewrite /= /RegLocate Hwdst' in H2.
        destruct wdst; [inv H1; inv H2; auto|].
        destruct c; simpl in H2; [| | repeat (match goal with H: context [match ?X with _ => _ end = (c2, _)] |- _ => destruct X end); inv H1; inv H2; auto].
        { destruct c as [ [ [ [pp gg] bb] ee] aa].
          assert (UU: z_of_argument reg2 offs = lang.z_of_argument reg1 offs).
          { destruct offs; simpl; auto.
            destruct (Hregsdef r) as [wr [Hwr _] ].
            generalize (Hsregs _ _ Hwr). intros Hwr'.
            rewrite Hwr Hwr'. destruct wr; [simpl; auto|].
            destruct (translate_word_cap c) as [c' ->]. auto. }
          rewrite UU in H2.
          destruct (lang.z_of_argument reg1 offs) as [noffs|] eqn:Hnoffs; [|inv H1; inv H2; auto].
          destruct (verify_access (StoreU_access bb ee aa noffs)) as [aa'|] eqn:Hconds; cycle 1.
          { rewrite /verify_access /= in Hconds. rewrite Hconds in H1, H2.
            inv H1; inv H2; auto. }
          rewrite /verify_access /= in Hconds. rewrite Hconds in H1, H2.
          rewrite /word_of_argument in Hwsrc. rewrite Hwsrc in H1.
          replace (match src with | inl n => inl n | inr rsrc => match reg2 !! rsrc with | Some w => w | None => inl 0%Z end end) with (translate_word wsrc) in H2.
          2:{ rewrite /rules_base.word_of_argument in Hwsrc'.
              destruct src; [inv Hwsrc'; auto| rewrite Hwsrc'; auto]. }
          assert (OO: lang.canStoreU pp aa' wsrc = canStoreU pp aa' (translate_word wsrc)).
          { destruct wsrc; simpl; auto.
            destruct c; auto. }
          rewrite -OO in H2.
          destruct (isU pp && lang.canStoreU pp aa' wsrc) eqn:Hconds'; [|inv H1; inv H2; auto].
          destruct (addr_eq_dec aa aa').
          - eexists ^(aa + 1)%a. subst aa'.
            destruct (proj1 (verify_access_spec (StoreU_access _ _ _ _) aa) Hconds) as [Hconds1 [Hconds2 [Hconds3 Hconds4] ] ].
            split; [clear -Hconds4; solve_addr|].
            replace (aa + 1)%a with (Some ^(aa + 1)%a) in H1 by (clear -Hconds4; solve_addr).
            replace (aa + 1)%a with (Some ^(aa + 1)%a) in H2 by (clear -Hconds4; solve_addr).
            rewrite /base.update_reg /base.update_mem /= in H1.
            rewrite /update_reg /update_mem /= in H2.
            assert (exists w, (<[dst:=inr (Regular (pp, gg, bb, ee, ^(aa + 1)%a))]> reg1) !! PC = Some w /\ (<[dst:=inr (pp, gg, bb, ee, ^(aa + 1)%a)]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
            { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
            rewrite !lookup_insert_ne //. eauto. }
            destruct (incrementPC (<[dst:=inr (Regular (pp, gg, bb, ee, ^(aa + 1)%a))]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
            { generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
              intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in H1.
              erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in H2.
              inv H1; inv H2; auto. }
            destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
            erewrite incrementPC_success_updatePC in H1; eauto.
            rewrite Hincrement2.
            eapply rules_base.incrementPC_success_updatePC in Hincrement2.
            destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
            instantiate (1 := <[aa:=translate_word wsrc]> mem2) in Z3.
            rewrite Z3 -Z4 in H2. inv H1; inv H2; repeat split; auto.
          - rewrite /base.update_reg /base.update_mem /= in H1.
            rewrite /update_reg /update_mem /= in H2.
            generalize (Hsregs _ _ HPC). intros HPC'.
            destruct (incrementPC reg1) as [reg1''|] eqn:Hincrement1; cycle 1.
            { generalize (incrementPC_fail_incrementPC' HPC HPC' Hincrement1).
              intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in H1.
              erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in H2.
              inv H1; inv H2; auto. }
            destruct (incrementPC_success_incrementPC' HPC HPC' Hincrement1) as [reg2'' Hincrement2].
            erewrite incrementPC_success_updatePC in H1; eauto.
            rewrite Hincrement2.
            eapply rules_base.incrementPC_success_updatePC in Hincrement2.
            destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
            instantiate (1 := <[aa':=translate_word wsrc]> mem2) in Z3.
            rewrite Z3 -Z4 in H2. inv H1; inv H2; repeat split; auto. }
        { assert (UU: z_of_argument reg2 offs = lang.z_of_argument reg1 offs).
          { destruct offs; simpl; auto.
            destruct (Hregsdef r) as [wr [Hwr _] ].
            generalize (Hsregs _ _ Hwr). intros Hwr'.
            rewrite Hwr Hwr'. destruct wr; [simpl; auto|].
            destruct (translate_word_cap c) as [c' ->]. auto. }
          rewrite UU in H2.
          destruct (lang.z_of_argument reg1 offs) as [noffs|] eqn:Hnoffs; [|inv H1; inv H2; auto].
          destruct (verify_access (StoreU_access a0 a1 a2 noffs)) as [aa'|] eqn:Hconds; cycle 1.
          { rewrite /verify_access /= in Hconds. rewrite Hconds in H1, H2.
            inv H1; inv H2; auto. }
          rewrite /verify_access /= in Hconds. rewrite Hconds in H1, H2.
          rewrite /word_of_argument in Hwsrc. rewrite Hwsrc in H1.
          replace (match src with | inl n => inl n | inr rsrc => match reg2 !! rsrc with | Some w => w | None => inl 0%Z end end) with (translate_word wsrc) in H2.
          2:{ rewrite /rules_base.word_of_argument in Hwsrc'.
              destruct src; [inv Hwsrc'; auto| rewrite Hwsrc'; auto]. }
          assert (OO: lang.canStoreU p0 aa' wsrc = canStoreU p0 aa' (translate_word wsrc)).
          { destruct wsrc; simpl; auto.
            destruct c; auto. }
          rewrite -OO in H2.
          destruct (isU p0 && lang.canStoreU p0 aa' wsrc) eqn:Hconds'; [|inv H1; inv H2; auto].
          destruct (addr_eq_dec a2 aa').
          - eexists ^(a2 + 1)%a. subst aa'.
            destruct (proj1 (verify_access_spec (StoreU_access _ _ _ _) a2) Hconds) as [Hconds1 [Hconds2 [Hconds3 Hconds4] ] ].
            split; [clear -Hconds4; solve_addr|].
            replace (a2 + 1)%a with (Some ^(a2 + 1)%a) in H1 by (clear -Hconds4; solve_addr).
            replace (a2 + 1)%a with (Some ^(a2 + 1)%a) in H2 by (clear -Hconds4; solve_addr).
            rewrite /base.update_reg /base.update_mem /= in H1.
            rewrite /update_reg /update_mem /= in H2.
            assert (exists w, (<[dst:=inr (Stk n p0 a0 a1 ^(a2 + 1)%a)]> reg1) !! PC = Some w /\ (<[dst:=inr (p0, Directed, a0, a1, ^(a2 + 1)%a)]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
            { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
            rewrite !lookup_insert_ne //. eauto. }
            unfold Stackframe in *. destruct (nat_eq_dec n (length cs)) as [_|KK]; [|elim KK; destruct Hinterpdst; auto].
            destruct (incrementPC (<[dst:=inr (Stk n p0 a0 a1 ^(a2 + 1)%a)]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
            { generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
              intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in H1.
              erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in H2.
              inv H1; inv H2; auto. }
            destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
            erewrite incrementPC_success_updatePC in H1; eauto.
            rewrite Hincrement2.
            eapply rules_base.incrementPC_success_updatePC in Hincrement2.
            destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
            instantiate (1 := <[a2:=translate_word wsrc]> mem2) in Z3.
            rewrite Z3 -Z4 in H2. inv H1; inv H2; repeat split; auto.
          - rewrite /base.update_reg /base.update_mem /update_stk /= in H1.
            rewrite /update_reg /update_mem /= in H2.
            unfold Stackframe in *. destruct (nat_eq_dec n (length cs)) as [_|KK]; [|elim KK; destruct Hinterpdst; auto].
            generalize (Hsregs _ _ HPC). intros HPC'.
            destruct (incrementPC reg1) as [reg1''|] eqn:Hincrement1; cycle 1.
            { generalize (incrementPC_fail_incrementPC' HPC HPC' Hincrement1).
              intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in H1.
              erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in H2.
              inv H1; inv H2; auto. }
            destruct (incrementPC_success_incrementPC' HPC HPC' Hincrement1) as [reg2'' Hincrement2].
            erewrite incrementPC_success_updatePC in H1; eauto.
            rewrite Hincrement2.
            eapply rules_base.incrementPC_success_updatePC in Hincrement2.
            destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
            instantiate (1 := <[aa':=translate_word wsrc]> mem2) in Z3.
            rewrite Z3 -Z4 in H2. inv H1; inv H2; repeat split; auto. } }
      clear H1 H2. destruct wdst.
      { destruct AA as [-> ->]. econstructor; eauto.
        - eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
      destruct c; cycle 2.
      { destruct AA as [-> ->]. econstructor; eauto.
        - eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
      { destruct c as [ [ [ [pp gg] bb] ee] aa].
        destruct (lang.z_of_argument reg1 offs) as [noffs|] eqn:Hnoffs; cycle 1.
        { destruct AA as [-> ->]. econstructor; eauto.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (verify_access (StoreU_access bb ee aa noffs)) as [aa'|] eqn:Hconds; cycle 1.
        { destruct AA as [-> ->]. econstructor; eauto.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (proj1 (verify_access_spec (StoreU_access _ _ _ _) _) Hconds) as [Hconds1 [Hconds2 [Hconds3 Hconds4] ] ].
        destruct (isU pp && lang.canStoreU pp aa' wsrc) eqn:Hconds'; cycle 1.
        { destruct AA as [-> ->]. econstructor; eauto.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (addr_eq_dec aa aa').
        { subst aa'. destruct AA as [aa'' [Haa'' AA] ].
          destruct (incrementPC (<[dst:=inr (Regular (pp, gg, bb, ee, aa''))]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
          { destruct AA as [-> ->]. econstructor; eauto.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { intros _. eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|].
            - rewrite HPC in Hwdst; inv Hwdst.
              destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              rewrite insert_insert.
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              rewrite lookup_insert in HXX; inv HXX.
              rewrite Hap1 in Hap1'; inv Hap1'.
              rewrite insert_insert.
              econstructor; eauto.
              + econstructor; eauto.
                * intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
                  { eexists; split; auto. simpl.
                    split; auto. intros. apply Hisdef in H0.
                    clear -H0; set_solver. }
                  destruct (Hregsdef rr) as [wr [Hwr Hinterpwr] ].
                  eexists; split; eauto. apply interp_heap_extend; auto.
                * intros ax wx Hwx. destruct (Hstksim ax wx Hwx) as [? [? ?] ].
                  rewrite lookup_insert_ne; [do 2 (split; auto)|].
                  apply interp_heap_extend; auto.
                  generalize (Hstkdisjheap _ ltac:(eexists; apply Hwx)).
                  destruct Hinterpdst. generalize (H5 aa ltac:(clear -Hconds2 Hconds4; solve_addr)).
                  intros Q. apply Hdisj in Q. clear -Q; solve_addr.
                * eapply sim_cs_heap_extend; eauto.
              + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|rewrite !lookup_insert_ne; auto].
              + intros ax. destruct (addr_eq_dec aa ax); [subst ax; rewrite !lookup_insert|rewrite !lookup_insert_ne; auto].
                * inversion 1; split; auto.
                  destruct (word_of_argument reg1 src); auto.
                  simpl in Hinterpdst.
                  destruct Hinterpdst as [Q W].
                  apply andb_true_iff in Hconds'.
                  destruct Hconds' as [Hcond1 Hcond2].
                  rewrite /lang.canStoreU Q in Hcond2.
                  rewrite andb_false_l in Hcond2.
                  destruct c; try congruence.
                  destruct c as [ [ [ [px gx] bx] ex] ax].
                  destruct gx; try congruence.
                  simpl. simpl in Hinterpwsrc.
                  destruct Hinterpwsrc. do 2 (split; auto).
                  intros. apply H3 in H5. clear -H5; set_solver.
                * intros. apply Hsh in H0. destruct H0 as [R [T [Y U] ] ].
                  do 3 (split; auto). apply can_address_only_heap_extend; auto.
              + intros. assert (a = aa \/ a ∈ dom (gset Addr) h) by (clear -H0; set_solver).
                destruct H1; [subst a|apply Hdisj; auto].
                simpl in Hinterpdst. destruct Hinterpdst as [? ?].
                generalize (H2 aa ltac:(clear -Hconds2 Hconds4; solve_addr)).
                intro F. apply Hdisj in F. auto.
            - rewrite lookup_insert_ne in Hincrement1; auto.
              rewrite HPC in Hincrement1. destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              rewrite lookup_insert_ne in HXX; auto.
              generalize (Hsregs _ _ HPC). intros HPC'.
              rewrite HPC' in HXX; inv HXX.
              rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              + econstructor; eauto.
                * intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
                  { eexists; split; auto. simpl.
                    split; auto. intros. apply Hisdef in H0.
                    clear -H0; set_solver. }
                  destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
                  { eexists; split; auto. eapply interp_heap_extend.
                    auto. }
                  destruct (Hregsdef rr) as [wr [Hwr Hinterpwr] ].
                  eexists; split; eauto. apply interp_heap_extend; auto.
                * intros ax wx Hwx. destruct (Hstksim ax wx Hwx) as [? [? ?] ].
                  rewrite lookup_insert_ne; [do 2 (split; auto)|].
                  apply interp_heap_extend; auto.
                  generalize (Hstkdisjheap _ ltac:(eexists; apply Hwx)).
                  destruct Hinterpdst. generalize (H5 aa ltac:(clear -Hconds2 Hconds4; solve_addr)).
                  intros Q. apply Hdisj in Q. clear -Q; solve_addr.
                * eapply sim_cs_heap_extend; eauto.
                  destruct (Hinterpdst). apply Hdisj.
                  apply H1. clear -Hconds2 Hconds4; solve_addr.
              + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|rewrite !(lookup_insert_ne _ PC); auto].
                destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|rewrite !lookup_insert_ne; auto].
              + intros ax. destruct (addr_eq_dec aa ax); [subst ax; rewrite !lookup_insert|rewrite !lookup_insert_ne; auto].
                * inversion 1; split; auto.
                  destruct (word_of_argument reg1 src); auto.
                  simpl in Hinterpdst.
                  destruct Hinterpdst as [Q W].
                  apply andb_true_iff in Hconds'.
                  destruct Hconds' as [Hcond1 Hcond2].
                  rewrite /lang.canStoreU Q in Hcond2.
                  rewrite andb_false_l in Hcond2.
                  destruct c; try congruence.
                  destruct c as [ [ [ [px gx] bx] ex] ax].
                  destruct gx; try congruence.
                  simpl. simpl in Hinterpwsrc.
                  destruct Hinterpwsrc. do 2 (split; auto).
                  intros. apply H3 in H5. clear -H5; set_solver.
                * intros. apply Hsh in H0. destruct H0 as [R [T [Y U] ] ].
                  do 3 (split; auto). apply can_address_only_heap_extend; auto.
              + intros. assert (a = aa \/ a ∈ dom (gset Addr) h) by (clear -H0; set_solver).
                destruct H1; [subst a|apply Hdisj; auto].
                simpl in Hinterpdst. destruct Hinterpdst as [? ?].
                generalize (H2 aa ltac:(clear -Hconds2 Hconds4; solve_addr)).
                intro F. apply Hdisj in F. auto. } }
        { destruct (incrementPC reg1) as [reg1''|] eqn:Hincrement1; cycle 1.
          { destruct AA as [-> ->]. econstructor; eauto.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { intros _. eapply incrementPC_inv_Some in Hincrement1.
            rewrite HPC in Hincrement1.
            destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
            eapply rules_base.incrementPC_Some_inv in Hincrement2.
            destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
            generalize (Hsregs _ _ HPC). intros HPC'.
            rewrite HPC' in HXX; inv HXX.
            rewrite Hap1 in Hap1'; inv Hap1'.
            econstructor; eauto.
            + econstructor; eauto.
              * intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
                { eexists; split; auto. simpl.
                  split; auto. intros. apply Hisdef in H0.
                  clear -H0; set_solver. }
                destruct (Hregsdef rr) as [wr [Hwr Hinterpwr] ].
                eexists; split; eauto. apply interp_heap_extend; auto.
              * intros ax wx Hwx. destruct (Hstksim ax wx Hwx) as [? [? ?] ].
                rewrite lookup_insert_ne; [do 2 (split; auto)|].
                apply interp_heap_extend; auto.
                generalize (Hstkdisjheap _ ltac:(eexists; apply Hwx)).
                destruct Hinterpdst. generalize (H5 aa' ltac:(clear -Hconds2 Hconds3 Hconds4; solve_addr)).
                intros Q. apply Hdisj in Q. clear -Q; solve_addr.
              * eapply sim_cs_heap_extend; eauto.
                destruct (Hinterpdst). apply Hdisj.
                apply H1. clear -Hconds2 Hconds3 Hconds4; solve_addr.
              + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|rewrite !(lookup_insert_ne _ PC); auto].
              + intros ax. destruct (addr_eq_dec aa' ax); [subst ax; rewrite !lookup_insert|rewrite !lookup_insert_ne; auto].
                * inversion 1; split; auto.
                  destruct (word_of_argument reg1 src); auto.
                  simpl in Hinterpdst.
                  destruct Hinterpdst as [Q W].
                  apply andb_true_iff in Hconds'.
                  destruct Hconds' as [Hcond1 Hcond2].
                  rewrite /lang.canStoreU Q in Hcond2.
                  rewrite andb_false_l in Hcond2.
                  destruct c; try congruence.
                  destruct c as [ [ [ [px gx] bx] ex] ax].
                  destruct gx; try congruence.
                  simpl. simpl in Hinterpwsrc.
                  destruct Hinterpwsrc. do 2 (split; auto).
                  intros. apply H3 in H5. clear -H5; set_solver.
                * intros. apply Hsh in H0. destruct H0 as [R [T [Y U] ] ].
                  do 3 (split; auto). apply can_address_only_heap_extend; auto.
              + intros. assert (a = aa' \/ a ∈ dom (gset Addr) h) by (clear -H0; set_solver).
                destruct H1; [subst a|apply Hdisj; auto].
                simpl in Hinterpdst. destruct Hinterpdst as [? ?].
                generalize (H2 aa' ltac:(clear -Hconds2 Hconds3 Hconds4; solve_addr)).
                intro F. apply Hdisj in F. auto. } } }
      { destruct (lang.z_of_argument reg1 offs) as [noffs|] eqn:Hnoffs; cycle 1.
        { destruct AA as [-> ->]. econstructor; eauto.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (verify_access (StoreU_access a0 a1 a2 noffs)) as [aa'|] eqn:Hconds; cycle 1.
        { destruct AA as [-> ->]. econstructor; eauto.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (proj1 (verify_access_spec (StoreU_access _ _ _ _) _) Hconds) as [Hconds1 [Hconds2 [Hconds3 Hconds4] ] ].
        destruct (isU p0 && lang.canStoreU p0 aa' wsrc) eqn:Hconds'; cycle 1.
        { destruct AA as [-> ->]. econstructor; eauto.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (addr_eq_dec a2 aa').
        { subst aa'. destruct AA as [aa'' [Haa'' AA] ].
          destruct (incrementPC (<[dst:=inr (Stk n p0 a0 a1 aa'')]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
          { destruct AA as [-> ->]. econstructor; eauto.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { intros _. eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|].
            - rewrite HPC in Hwdst; inv Hwdst.
            - rewrite lookup_insert_ne in Hincrement1; auto.
              rewrite HPC in Hincrement1. destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              rewrite lookup_insert_ne in HXX; auto.
              generalize (Hsregs _ _ HPC). intros HPC'.
              rewrite HPC' in HXX; inv HXX.
              rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              + simpl in Hinterpdst. intros d1 d2 Hlt.
                destruct (nat_eq_dec d2 (length cs)).
                * subst d2. rewrite stack_cons_length.
                  intros. inv H1.
                  destruct (addr_eq_dec a2 a4).
                  { subst a4. destruct Hinterpdst as [? [? [XZ ?] ] ].
                    simpl in H0.
                    match goal with H: context [(if ?S then _ else _) = Some stk1] |- _ => destruct S as [G|_]; [clear -G Hlt; unfold Stackframe in G; lia|] end.
                    eapply XZ in H2; eauto.
                    clear -H2 Hconds2; solve_addr. }
                  rewrite lookup_insert_ne in H3; auto.
                  eapply Hstkdisj; eauto; [|rewrite stack_cons_length; auto].
                  simpl. simpl in H0. unfold Stackframe in *.
                  destruct (nat_eq_dec d1 (length cs)); [lia|auto].
                * intros. rewrite (stack_cons_length_ne) in H1; eauto.
                  generalize (proj1 (stack_is_Some _ _) ltac:(eexists; apply H1)).
                  intros XT. rewrite (stack_cons_length_ne) in H0; eauto; [|unfold Stackframe in *; lia].
                  eapply (Hstkdisj d1 d2 Hlt); eauto; rewrite stack_cons_length_ne; eauto.
                  unfold Stackframe in *. lia.
              + econstructor; eauto.
                * intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
                  { destruct (Hregsdef PC) as [wpc [Hwpc HinterpPC] ].
                    rewrite HPC in Hwpc; inv Hwpc.
                    simpl in HinterpPC; destruct HinterpPC.
                    eexists; split; eauto. simpl; split; auto. }
                  destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert|rewrite lookup_insert_ne; auto].
                  { eexists; split; auto.
                    simpl. destruct Hinterpdst as [W1 [W2 [W3 W4] ] ].
                    do 3 (split; auto).
                    intros ax QQ.
                    destruct (addr_eq_dec a2 ax); [subst ax; rewrite lookup_insert; eauto|rewrite lookup_insert_ne; auto].
                    apply W4. simpl.
                    clear -QQ n2 Haa''. destruct p0; solve_addr. }
                  destruct (Hregsdef rr) as [wrr [Hwrr Hinterprr] ].
                  eexists; split; eauto. apply interp_stack_extend; auto.
                * simpl in Hinterpdst. destruct Hinterpdst as [? [GG ?] ].
                  clear -Hstkdisjheap Hconds4 GG.
                  intro ax. destruct (addr_eq_dec a2 ax); [subst ax; intros; solve_addr|rewrite lookup_insert_ne; auto].
                * intros ax. destruct (addr_eq_dec a2 ax); [subst ax; rewrite !lookup_insert|rewrite !(lookup_insert_ne _ a2); auto].
                  { inversion 1; split; auto.
                    split; [apply interp_stack_extend; auto|].
                    rewrite /canBeStored /=. apply andb_true_iff in Hconds'.
                    destruct Hconds'. eapply canStoreU_canStoreU_URWLX; eauto. }
                  intros. apply Hstksim in H0. destruct H0 as [? [? ?] ].
                  do 2 (split; auto). apply interp_stack_extend; auto.
                * assert (XQC: forall d xstk, stack d cs = Some xstk -> forall ax, is_Some (xstk !! ax) -> (ax < a2)%a).
                  { destruct Hinterpdst as [W1 [W2 [W3 W4] ] ].
                    intros. eapply W3 in H1; eauto. clear -H1 Hconds2; solve_addr. }
                  eapply sim_cs_stack_extend; eauto.
              + intro rr; destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|rewrite !(lookup_insert_ne _ PC); auto].
                destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|rewrite !lookup_insert_ne; auto].
              + intros. rewrite lookup_insert_ne; auto.
                assert (is_Some (h !! a)) by (eexists; eauto).
                apply elem_of_dom in H1.
                generalize (Hdisj _ H1). intro T.
                destruct Hinterpdst as [W1 [W2 ?] ].
                clear -Hconds4 T W2. solve_addr. } }
        { destruct (incrementPC reg1) as [reg1''|] eqn:Hincrement1; cycle 1.
          { destruct AA as [-> ->]. econstructor; eauto.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { intros _. eapply incrementPC_inv_Some in Hincrement1.
            rewrite HPC in Hincrement1.
            destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
            eapply rules_base.incrementPC_Some_inv in Hincrement2.
            destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
            generalize (Hsregs _ _ HPC). intros HPC'.
            rewrite HPC' in HXX; inv HXX.
            rewrite Hap1 in Hap1'; inv Hap1'.
            econstructor; eauto.
            + simpl in Hinterpdst. intros d1 d2 Hlt.
                destruct (nat_eq_dec d2 (length cs)).
                * subst d2. rewrite stack_cons_length.
                  intros. inv H1.
                  destruct (addr_eq_dec aa' a4).
                  { subst a4. destruct Hinterpdst as [? [? [XZ ?] ] ].
                    simpl in H0.
                    match goal with H: context [(if ?S then _ else _) = Some stk1] |- _ => destruct S as [G|_]; [clear -G Hlt; unfold Stackframe in G; lia|] end.
                    eapply XZ in H2; eauto.
                    clear -H2 Hconds2; solve_addr. }
                  rewrite lookup_insert_ne in H3; auto.
                  eapply Hstkdisj; eauto; [|rewrite stack_cons_length; auto].
                  simpl. simpl in H0. unfold Stackframe in *.
                  destruct (nat_eq_dec d1 (length cs)); [lia|auto].
                * intros. rewrite (stack_cons_length_ne) in H1; eauto.
                  generalize (proj1 (stack_is_Some _ _) ltac:(eexists; apply H1)).
                  intros XT. rewrite (stack_cons_length_ne) in H0; eauto; [|unfold Stackframe in *; lia].
                  eapply (Hstkdisj d1 d2 Hlt); eauto; rewrite stack_cons_length_ne; eauto.
                  unfold Stackframe in *. lia.
              + econstructor; eauto.
                * intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
                  { destruct (Hregsdef PC) as [wpc [Hwpc HinterpPC] ].
                    rewrite HPC in Hwpc; inv Hwpc.
                    simpl in HinterpPC; destruct HinterpPC.
                    eexists; split; eauto. simpl; split; auto. }
                  destruct (Hregsdef rr) as [wrr [Hwrr Hinterprr] ].
                  eexists; split; eauto. apply interp_stack_extend; auto.
                * simpl in Hinterpdst. destruct Hinterpdst as [? [GG ?] ].
                  clear -Hstkdisjheap Hconds1 Hconds2 Hconds3 Hconds4 GG.
                  intro ax. destruct (addr_eq_dec aa' ax); [subst ax; intros; solve_addr|rewrite lookup_insert_ne; auto].
                * intros ax. destruct (addr_eq_dec aa' ax); [subst ax; rewrite !lookup_insert|rewrite !(lookup_insert_ne _ aa'); auto].
                  { inversion 1; split; auto.
                    split; [apply interp_stack_extend; auto|].
                    rewrite /canBeStored /=. apply andb_true_iff in Hconds'.
                    destruct Hconds'. eapply canStoreU_canStoreU_URWLX; eauto. }
                  intros. apply Hstksim in H0. destruct H0 as [? [? ?] ].
                  do 2 (split; auto). apply interp_stack_extend; auto.
                * assert (XQC: forall d xstk, stack d cs = Some xstk -> forall ax, is_Some (xstk !! ax) -> (ax < aa')%a).
                  { destruct Hinterpdst as [W1 [W2 [W3 W4] ] ].
                    intros. eapply W3 in H1; eauto. clear -H1 Hconds2; solve_addr. }
                  eapply sim_cs_stack_extend; eauto.
              + intro rr; destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|rewrite !(lookup_insert_ne _ PC); auto].
              + intros. rewrite lookup_insert_ne; auto.
                assert (is_Some (h !! a)) by (eexists; eauto).
                apply elem_of_dom in H1.
                generalize (Hdisj _ H1). intro T.
                destruct Hinterpdst as [W1 [W2 ?] ].
                clear -Hconds1 Hconds2 Hconds3 Hconds4 T W2. solve_addr. } } }
    - (* PromoteU *)
      assert (AA: match reg1 !! dst with
                  | Some (inr (Regular (pp, gg, bb, ee, aa))) =>
                    if perm_eq_dec pp E then c1 = lang.Failed /\ c2 = Failed else
                    match incrementPC (<[dst:=inr (Regular (promote_perm pp, gg, bb, addr_reg.min aa ee, aa))]> reg1) with
                    | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inr (promote_perm pp, gg, bb, addr_reg.min aa ee, aa)]> reg2) = Some reg2' /\ mem2' = mem2
                    | None => c1 = lang.Failed /\ c2 = Failed
                    end
                  | Some (inr (Stk dd pp bb ee aa)) =>
                    if perm_eq_dec pp E then c1 = lang.Failed /\ c2 = Failed else
                    match incrementPC (<[dst:=inr (Stk dd (promote_perm pp) bb (addr_reg.min aa ee) aa)]> reg1) with
                    | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inr (promote_perm pp, Directed, bb, addr_reg.min aa ee, aa)]> reg2) = Some reg2' /\ mem2' = mem2
                    | None => c1 = lang.Failed /\ c2 = Failed
                    end
                  | _ => c1 = lang.Failed /\ c2 = Failed
                  end).
      { destruct (Hregsdef dst) as [wdst [Hwdst _] ].
        rewrite Hwdst. generalize (Hsregs _ _ Hwdst). intros Hwdst'.
        rewrite /= /base.RegLocate Hwdst in H1.
        rewrite /= /RegLocate Hwdst' in H2.
        destruct wdst; [simpl in H2; inv H1; inv H2; auto|].
        destruct (translate_word_cap c) as [c' Hc'].
        rewrite Hc' in H2. destruct c; [|inv Hc'|inv Hc'; inv H1; inv H2; auto].
        - destruct c as [ [ [ [pp gg] bb] ee] aa]. inv Hc'.
          destruct (perm_eq_dec pp E); [inv H1; inv H2; auto|].
          rewrite /base.update_reg /= in H1.
          rewrite /update_reg /= in H2.
          assert (exists w, (<[dst:=inr (Regular (promote_perm pp, gg, bb, addr_reg.min aa ee, aa))]> reg1) !! PC = Some w /\ (<[dst:=inr (promote_perm pp, gg, bb, addr_reg.min aa ee, aa)]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
          { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
            rewrite !lookup_insert_ne //. eauto. }
          destruct (incrementPC (<[dst:=inr (Regular (promote_perm pp, gg, bb, addr_reg.min aa ee, aa))]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
          + generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
            intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in H1.
            erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in H2.
            inv H1; inv H2; auto.
          + destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
            erewrite incrementPC_success_updatePC in H1; eauto.
            rewrite Hincrement2.
            eapply rules_base.incrementPC_success_updatePC in Hincrement2.
            destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
            instantiate (1 := mem2) in Z3.
            rewrite Z3 -Z4 in H2. inv H1; inv H2; repeat split; auto.
        - destruct (perm_eq_dec p0 E); [inv H1; inv H2; auto|].
          rewrite /base.update_reg /= in H1.
          rewrite /update_reg /= in H2.
          assert (exists w, (<[dst:=inr (Stk n (promote_perm p0) a0 (addr_reg.min a2 a1) a2)]> reg1) !! PC = Some w /\ (<[dst:=inr (promote_perm p0, Directed, a0, addr_reg.min a2 a1, a2)]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
          { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
            rewrite !lookup_insert_ne //. eauto. }
          destruct (incrementPC (<[dst:=inr (Stk n (promote_perm p0) a0 (addr_reg.min a2 a1) a2)]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
          + generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
            intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in H1.
            erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in H2.
            inv H1; inv H2; auto.
          + destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
            erewrite incrementPC_success_updatePC in H1; eauto.
            rewrite Hincrement2.
            eapply rules_base.incrementPC_success_updatePC in Hincrement2.
            destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
            instantiate (1 := mem2) in Z3.
            rewrite Z3 -Z4 in H2. inv H1; inv H2; repeat split; auto. }
      clear H1 H2. destruct (Hregsdef dst) as [wdst [Hwdst Hinterpdst] ].
      generalize (Hsregs _ _ Hwdst); intros Hwdst'.
      rewrite Hwdst in AA.
      destruct (Hregsdef PC) as [wPC [HwPC HinterpPC] ].
      rewrite HPC in HwPC; inv HwPC.
      generalize (Hsregs _ _ HPC); intros HPC'.
      destruct wdst.
      + destruct AA as [-> ->]. econstructor; eauto.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate.
      + destruct c; cycle 2.
        * destruct AA as [-> ->]. econstructor; eauto.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        * destruct c as [ [ [ [pp gg] bb] ee] aa].
          destruct (perm_eq_dec pp E).
          { destruct AA as [-> ->]. econstructor; eauto.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (incrementPC (<[dst:=inr (Regular (promote_perm pp, gg, bb, addr_reg.min aa ee, aa))]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
          { destruct AA as [-> ->]. econstructor; eauto.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { intros _. eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|].
            - rewrite HPC in Hwdst; inv Hwdst.
              destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              rewrite insert_insert.
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              rewrite lookup_insert in HXX. inv HXX.
              econstructor; eauto.
              + econstructor; eauto. intros rr; destruct (reg_eq_dec PC rr); [|rewrite lookup_insert_ne; auto].
                subst rr; rewrite lookup_insert.
                eexists; split; eauto. simpl.
                destruct HinterpPC.
                split; [destruct H8 as [-> | [-> | ->] ]; simpl; auto|].
                intros; apply H1.
                clear -H2; solve_addr.
              + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert|rewrite !(lookup_insert_ne _ PC); auto].
                inversion 1; simpl; auto. rewrite Hap1 in Hap1'; inv Hap1'; auto.
            - rewrite lookup_insert_ne // HPC in Hincrement1.
              destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              rewrite lookup_insert_ne // in HXX.
              rewrite (Hsregs _ _ HPC) /= in HXX. inv HXX.
              rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              + econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|].
                * eexists; split; simpl; eauto.
                * rewrite lookup_insert_ne //.
                  destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
                  eexists; split; eauto. destruct Hinterpdst; simpl; auto.
                  simpl in H0. split; [destruct pp; simpl in H0; simpl; try congruence; auto|].
                  intros. eapply H1; clear -H2; solve_addr.
              + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
                rewrite !(lookup_insert_ne _ PC) //.
                destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert|rewrite !lookup_insert_ne; auto].
                inversion 1; auto. }
        * destruct (perm_eq_dec p0 E).
          { destruct AA as [-> ->]. econstructor; eauto.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (incrementPC (<[dst:=inr (Stk n (promote_perm p0) a0 (addr_reg.min a2 a1) a2)]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
          { destruct AA as [-> ->]. econstructor; eauto.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { intros _. eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|].
            - rewrite HPC in Hwdst; inv Hwdst.
            - rewrite lookup_insert_ne // HPC in Hincrement1.
              destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              rewrite lookup_insert_ne // in HXX.
              rewrite (Hsregs _ _ HPC) /= in HXX. inv HXX.
              rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              + econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|].
                * eexists; split; simpl; eauto.
                * rewrite lookup_insert_ne //.
                  destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
                  eexists; split; eauto. destruct Hinterpdst as [? [? [HH ?] ] ]; simpl; auto.
                  split; auto. split; [clear -H1; solve_addr|].
                  split; auto.
                  intros; eapply H2. simpl. clear -H3.
                  destruct p0; simpl in H3; solve_addr.
              + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
                rewrite !(lookup_insert_ne _ PC) //.
                destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert|rewrite !lookup_insert_ne; auto].
                inversion 1; auto. }
  Qed.

  Lemma foldl_pop_instrs_acc:
    forall rlist acc,
      foldl (λ (b : list Z) (r : RegName), call.pop_instrs r ++ b) acc rlist =
      (foldl (λ (b : list Z) (r : RegName), call.pop_instrs r ++ b) [] rlist) ++ acc.
  Proof.
    induction rlist; intros.
    - reflexivity.
    - simpl in IHrlist. simpl foldl. rewrite IHrlist.
      rewrite (IHrlist ([encodeInstr (LoadU a call.r_stk (inl (-1)%Z)); encodeInstr (Lea call.r_stk (inl (-1)%Z))])).
      rewrite -app_assoc /=. reflexivity.
  Qed.

  Lemma foldl_pop_instrs_cons:
    forall rlist r,
      foldl (λ (b : list Z) (r : RegName), call.pop_instrs r ++ b) [] (r :: rlist) =
      (foldl (λ (b : list Z) (r : RegName), call.pop_instrs r ++ b) [] rlist) ++ (call.pop_instrs r).
  Proof.
    intros. simpl foldl. rewrite foldl_pop_instrs_acc. reflexivity.
  Qed.

  Lemma foldl_pop_instrs_length:
    forall rlist,
      length (foldl (λ (b : list Z) (r : RegName), call.pop_instrs r ++ b) [] rlist) = 2 * length rlist.
  Proof.
    induction rlist.
    - reflexivity.
    - rewrite foldl_pop_instrs_cons app_length IHrlist.
      simpl. lia.
  Qed.

  Lemma all_registers_NoDup :
    NoDup all_registers.
  Proof.
    rewrite /all_registers.
    repeat (
      apply NoDup_cons_2;
      first (repeat (rewrite not_elem_of_cons; split; [done|]); apply not_elem_of_nil)
    ).
    by apply NoDup_nil.
  Qed.

  Lemma pop_env_instrs_spec:
    forall rlist br er ar ar_final bstk estk astk astk_final reg mem (reg': base.Reg)
    (Hstkfinal: (astk + (- (length rlist)))%a = Some (astk_final))
    (Hlowstk: (bstk <= astk_final)%a)
    (Hhistk: (astk < estk)%a)
    (Harfinal: (ar + (2 * (length rlist)))%a = Some (ar_final))
    (Hlowar: (br <= ar)%a)
    (Hhiar: (ar_final < er)%a)
    (Hnotin: PC ∉ rlist /\ call.r_stk ∉ rlist)
    (Hinstrs: forall i,
                i < 2 * (length rlist) ->
                exists ai, (ar + i)%a = Some ai /\
                mem !! ai = (translate_word <$> (inl <$> (foldl (fun b r => (call.pop_instrs r) ++ b) [] rlist))) !! i)
    (Hcontents: forall i,
                  i < length rlist ->
                  exists ai, (astk + - (S i))%a = Some ai /\
                  exists r, rlist !! (length rlist - S i) = Some r /\
                  exists rwi, mem !! ai = Some (translate_word rwi) /\
                  reg' !! r = Some rwi),
    rtc erased_step
      ([Seq (Instr Executable)], (<[PC:=inr (RX, Directed, br, er, ar)]> (<[call.r_stk:=inr (URWLX, Directed, bstk, estk, astk)]> reg), mem))
      ([Seq (Instr Executable)], (<[PC:=inr (RX, Directed, br, er, ar_final)]> (<[call.r_stk:=inr (URWLX, Directed, bstk, estk, astk_final)]> (foldr (fun r reg => <[r:= translate_word (base.RegLocate reg' r)]> reg) reg rlist)), mem)).
  Proof.
    induction rlist; intros.
    - simpl. simpl in Hstkfinal. assert (astk = astk_final) as <- by (clear -Hstkfinal; solve_addr).
      simpl in Harfinal. assert (ar = ar_final) as <- by (clear -Harfinal; solve_addr).
      apply rtc_refl.
    - eapply rtc_transitive.
      + eapply IHrlist; auto.
        * instantiate (1 := ^(astk + - length rlist)%a).
          clear -Hstkfinal. solve_addr.
        * clear -Hstkfinal Hlowstk; solve_addr.
        * instantiate (1 := ^(ar + 2 * length rlist)%a).
          clear -Harfinal. solve_addr.
        * clear -Harfinal Hhiar; solve_addr.
        * destruct Hnotin as [Hnotin1 Hnotin2].
          eapply not_elem_of_cons in Hnotin1.
          eapply not_elem_of_cons in Hnotin2.
          destruct Hnotin1, Hnotin2. split; auto.
        * rewrite foldl_pop_instrs_cons in Hinstrs.
          intros. generalize (Hinstrs i ltac:(clear -H0; simpl; lia)).
          intros [ai [Hai HA] ]. exists ai; split; auto.
          rewrite !fmap_app in HA.
          rewrite lookup_app_l in HA; auto.
          rewrite !fmap_length. rewrite foldl_pop_instrs_length; auto.
        * intros. generalize (Hcontents i ltac:(clear -H0; simpl; lia)).
          intros [ai [Hai [r [HA [rwi HB] ] ] ] ]. exists ai; split; auto.
          exists r. rewrite lookup_cons_ne_0 in HA; [|simpl; lia].
          replace (length (a :: rlist) - S i) with (S (length rlist - S i)) in HA by (simpl; lia).
          simpl in HA. split; auto.
          exists rwi; eauto.
      + destruct (Hinstrs (2 * length rlist) ltac:(simpl; lia)) as [ar' [Har' Hinstr0] ].
        destruct (Hinstrs (2 * length rlist + 1) ltac:(simpl; lia)) as [arp1 [Harp1 Hinstr1] ].
        destruct (Hcontents (length rlist) ltac:(simpl; lia)) as [astkm1 [Hastkm1 [r0 [Hr0 [rw0 [Hrw0 Hrw0'] ] ] ] ] ].
        simpl. replace (length (a :: rlist) - S (length rlist)) with 0 in Hr0 by (simpl; lia).
        simpl in Hr0; inv Hr0.
        rewrite /(base.RegLocate _ r0) Hrw0'.
        eapply rtc_l.
        * econstructor. econstructor; eauto.
          { f_equal; eauto. instantiate (1 := []).
            instantiate (2 := []). reflexivity. }
          { instantiate (1 := []). econstructor; try reflexivity.
            instantiate (2 := [SeqCtx]). reflexivity.
            econstructor. eapply step_exec_instr; simpl; auto.
            rewrite /RegLocate lookup_insert; reflexivity.
            rewrite /RegLocate lookup_insert. econstructor; eauto.
            clear -Hlowar Hhiar Harfinal. solve_addr. }
        * simpl. assert (^(ar + 2 * length rlist)%a = ar') as -> by (clear -Har'; solve_addr).
          rewrite foldl_pop_instrs_cons !fmap_app in Hinstr0.
          rewrite lookup_app_r in Hinstr0; [|rewrite !fmap_length foldl_pop_instrs_length; lia].
          rewrite !fmap_length foldl_pop_instrs_length in Hinstr0.
          replace (2 * length rlist - 2 * length rlist) with 0 in Hinstr0 by lia.
          simpl in Hinstr0.
          rewrite /MemLocate Hinstr0 /= decode_encode_instr_inv /=.
          rewrite /RegLocate lookup_insert_ne //.
          rewrite lookup_insert /=.
          assert ((^(astk + - length rlist) + -1)%a = Some astkm1) as -> by (clear -Hastkm1; solve_addr).
          destruct (Addr_le_dec bstk astkm1) as [_|X]; [|clear -X Hastkm1 Hstkfinal Hlowstk; solve_addr].
          destruct (Addr_lt_dec astkm1 ^(astk + - length rlist)%a) as [_|X]; [|clear -X Hastkm1; solve_addr].
          destruct (Addr_le_dec ^(astk + - length rlist)%a estk) as [_|X]; [|clear -X Hhistk Hastkm1; solve_addr].
          rewrite /update_reg /= /MemLocate Hrw0.
          assert (HnPCr0: r0 <> PC).
          { destruct Hnotin as [Hnotin1 _]. apply not_elem_of_cons in Hnotin1.
            destruct Hnotin1; auto. }
          assert (Hnrstkr0: r0 <> call.r_stk).
          { destruct Hnotin as [_ Hnotin1]. apply not_elem_of_cons in Hnotin1.
            destruct Hnotin1; auto. }
          rewrite /updatePC /= /RegLocate (lookup_insert_ne _ r0 PC) //.
          rewrite lookup_insert.
          assert ((ar' + 1)%a = Some arp1) as -> by (clear -Har' Harp1; solve_addr).
          rewrite /update_reg /=.
          eapply rtc_l.
          { econstructor. econstructor; eauto.
            { f_equal; eauto. instantiate (1 := []).
              instantiate (2 := []). reflexivity. }
            { instantiate (1 := []). econstructor; try reflexivity.
              instantiate (2 := []). reflexivity. econstructor. } }
          simpl. eapply rtc_l.
          { econstructor. econstructor; eauto.
            { f_equal; eauto. instantiate (1 := []).
              instantiate (2 := []). reflexivity. }
            { instantiate (1 := []). econstructor; try reflexivity.
              instantiate (2 := [SeqCtx]). reflexivity.
              econstructor. eapply step_exec_instr; simpl; auto.
              rewrite /RegLocate lookup_insert; reflexivity.
              rewrite /RegLocate lookup_insert. econstructor; eauto.
              clear -Hlowar Hhiar Harfinal Harp1. solve_addr. } }
          simpl. rewrite foldl_pop_instrs_cons !fmap_app in Hinstr1.
          rewrite lookup_app_r in Hinstr1; [|rewrite !fmap_length foldl_pop_instrs_length; lia].
          rewrite !fmap_length foldl_pop_instrs_length in Hinstr1.
          replace (2 * length rlist + 1 - 2 * length rlist) with 1 in Hinstr1 by lia.
          simpl in Hinstr1.
          rewrite /MemLocate Hinstr1 /= decode_encode_instr_inv /=.
          rewrite /RegLocate (lookup_insert_ne _ PC call.r_stk) //.
          rewrite (lookup_insert_ne _ r0 call.r_stk) //.
          rewrite (lookup_insert_ne _ PC call.r_stk) //.
          rewrite lookup_insert. assert ((^(astk + - length rlist) + -1)%a = Some astkm1) as -> by (clear -Hastkm1; solve_addr).
          destruct (Addr_le_dec astkm1 ^(astk + - length rlist)%a) as [_|X]; [|clear -X Hstkfinal Hlowstk Hastkm1; solve_addr].
          rewrite /update_reg /= /updatePC /= /RegLocate (lookup_insert_ne _ call.r_stk PC) //.
          rewrite lookup_insert.
          assert ((arp1 + 1)%a = Some ar_final) as -> by (clear -Harp1 Harfinal; solve_addr).
          rewrite /update_reg /=.
          rewrite (insert_commute _ call.r_stk PC) //.
          rewrite insert_insert.
          rewrite (insert_commute _ r0 PC) //.
          rewrite (insert_commute _ call.r_stk PC) //.
          rewrite insert_insert.
          rewrite (insert_commute _ r0 call.r_stk) //.
          rewrite insert_insert.
          replace astkm1 with astk_final by (clear -Hastkm1 Hstkfinal; solve_addr).
          eapply rtc_once. econstructor. econstructor; eauto.
          { f_equal; eauto. instantiate (1 := []).
            instantiate (2 := []). reflexivity. }
          { reflexivity. }
          econstructor. instantiate (2:=[]); auto.
          reflexivity. econstructor.
  Qed.

  Lemma foldr_insert_spec:
    forall rlist nregs reg r,
      NoDup rlist ->
      (In r rlist ->
      (foldr (λ (r : RegName) (reg : Reg), <[r:=translate_word (base.RegLocate nregs r)]> reg) reg rlist) !! r = Some (translate_word (base.RegLocate nregs r))) /\
      (~ In r rlist ->
      (foldr (λ (r : RegName) (reg : Reg), <[r:=translate_word (base.RegLocate nregs r)]> reg) reg rlist) !! r = reg !! r).
  Proof.
    induction rlist; intros.
    - split; [inversion 1|intro; reflexivity].
    - split.
      + intro X; inv X.
        * simpl. rewrite lookup_insert //.
        * simpl. inv H0. eapply elem_of_list_In in H1.
          rewrite lookup_insert_ne; [|intro; subst a; apply H4; auto].
          destruct (IHrlist nregs reg r H5) as [A B].
          eapply A; eapply elem_of_list_In; auto.
      + intros. simpl. rewrite lookup_insert_ne; [|intro; subst r; eapply H1; left; auto].
        inv H0. destruct (IHrlist nregs reg r H5) as [A B].
        eapply B. intro; eapply H1; right; auto.
  Qed.

  Definition push_words_no_check (m: machine_base.Mem) (a: Addr) (ws: list Word) :=
    foldl (fun '(a, m) w => (^(a + 1)%a, <[a:=w]> m)) (a, m) ws.

  Lemma push_words_no_check_cons m a w ws:
    push_words_no_check m a (w::ws) = push_words_no_check (<[a:=w]> m) ^(a + 1)%a ws.
  Proof. reflexivity. Qed.

  Lemma canStoreU_translate_word:
    forall p a w,
      lang.canStoreU p a w = canStoreU p a (translate_word w).
  Proof.
    destruct w; simpl; auto. destruct c; auto.
  Qed.

  Lemma push_env_instrs_spec:
    forall wlist pr gr br er ar ar_final bstk estk astk astk_final reg mem reg1
    (HisCorrectPC: isCorrectPC (inr (pr, gr, br, er, ar)))
    (Hstkdisj: (estk <= br)%a)
    (Hstkfinal: (astk + (length wlist))%a = Some (astk_final))
    (Hlowstk: (bstk <= astk)%a)
    (Hhistk: (astk_final <= estk)%a)
    (Harfinal: (ar + (length wlist))%a = Some (ar_final))
    (Hlowar: (br <= ar)%a)
    (Hhiar: (ar_final < er)%a)
    (Hinstrs: forall i,
                i < (length wlist) ->
                exists ai, (ar + i)%a = Some ai /\
                mem !! ai = (translate_word <$> (call.push_instrs wlist)) !! i)
    (Hregsdef: ∀ r, r <> PC -> r <> call.r_stk -> ∃ w, reg1 !! r = Some w)
    (Hsregs: ∀ r w, r <> PC -> r <> call.r_stk -> reg1 !! r = Some w → reg !! r = Some (translate_word w))
    (Hcanstore: forall i wi, wlist !! i = Some wi -> lang.canStoreU URWLX (^(astk + Z.of_nat i)%a) (word_of_argument reg1 wi) = true)
    (Hnotin: inr PC ∉ wlist /\ inr call.r_stk ∉ wlist),
    rtc erased_step
      ([Seq (Instr Executable)], (<[PC:=inr (pr, gr, br, er, ar)]> (<[call.r_stk:=inr (URWLX, Directed, bstk, estk, astk)]> reg), mem))
      ([Seq (Instr Executable)], (<[PC:=inr (pr, gr, br, er, ar_final)]> (<[call.r_stk:=inr (URWLX, Directed, bstk, estk, astk_final)]> reg), (push_words_no_check mem astk (map (fun w => translate_word (word_of_argument reg1 w)) wlist)).2)).
  Proof.
    induction wlist; intros.
    - simpl. simpl in Hstkfinal, Harfinal.
      replace astk_final with astk by (clear -Hstkfinal; solve_addr).
      replace ar_final with ar by (clear -Harfinal; solve_addr).
      eapply rtc_refl.
    - simpl map. rewrite push_words_no_check_cons.
      eapply rtc_transitive with (y := ([Seq (Instr Executable)], (<[PC:=inr (pr, gr, br, er, ^(ar + 1)%a)]> (<[call.r_stk:=inr (URWLX, Directed, bstk, estk, ^(astk + 1)%a)]> reg), <[astk:=translate_word (word_of_argument reg1 a)]> mem))).
      + eapply rtc_l.
        * econstructor. econstructor; eauto.
          { instantiate (2 := []). instantiate (3 := []). reflexivity. }
          { econstructor; eauto.
            - instantiate (2 := [SeqCtx]). reflexivity.
            - econstructor. eapply step_exec_instr.
              + simpl. rewrite /RegLocate lookup_insert //.
              + rewrite /= /RegLocate lookup_insert //.
              + rewrite /= /MemLocate. destruct (Hinstrs 0 ltac:(simpl; lia)) as [a0 [Ha0 Hinstr0] ].
                assert (a0 = ar) as -> by (clear -Ha0; solve_addr).
                rewrite Hinstr0 /=. rewrite decode_encode_instr_inv. reflexivity.
              + rewrite /= /RegLocate lookup_insert_ne; [|auto].
                rewrite lookup_insert. assert ((astk + 0)%a = Some astk) as -> by (clear; solve_addr).
                destruct (Addr_le_dec bstk astk) as [_|X]; [|elim X; auto].
                destruct (Addr_le_dec astk astk) as [_|X]; [|elim X; clear; solve_addr].
                destruct (Addr_lt_dec astk estk) as [_|X]; [|elim X; clear -Hstkfinal Hhistk; simpl in Hstkfinal; solve_addr].
                simpl. destruct (addr_eq_dec astk astk) as [_|X]; [|elim X; reflexivity].
                assert ((astk + 1)%a = Some ^(astk + 1)%a) as -> by (clear - Hstkfinal; solve_addr).
                rewrite /update_reg /update_mem /=.
                generalize (Hcanstore 0 a eq_refl).
                intros Hacanstore. replace (^(astk + 0%nat)%a) with astk in Hacanstore by (clear; solve_addr). rewrite canStoreU_translate_word in Hacanstore.
                assert (match a with | inl n => inl n | inr rsrc => match <[PC:=inr (pr, gr, br, er, ar)]> (<[call.r_stk:=inr (URWLX, Directed, bstk, estk, astk)]> reg) !! rsrc with | Some w => w | None => inl 0%Z end end = (translate_word (word_of_argument reg1 a))) as ->.
                { destruct a; [reflexivity|].
                  destruct Hnotin as [Hnotin1 Hnotin2].
                  eapply not_elem_of_cons in Hnotin1. destruct Hnotin1 as [Hnotin1 Hnotin1'].
                  eapply not_elem_of_cons in Hnotin2. destruct Hnotin2 as [Hnotin2 Hnotin2'].
                  rewrite lookup_insert_ne; [|intro; apply Hnotin1; subst; auto].
                  rewrite lookup_insert_ne; [|intro; apply Hnotin2; subst; auto].
                  destruct (Hregsdef r ltac:(intro; apply Hnotin1; subst; auto) ltac:(intro; apply Hnotin2; subst; auto)) as [wr Hwr].
                  rewrite (Hsregs r _ ltac:(intro; apply Hnotin1; subst; auto) ltac:(intro; apply Hnotin2; subst; auto) Hwr).
                  simpl. rewrite /base.RegLocate Hwr //. }
                rewrite Hacanstore. rewrite (insert_commute _ call.r_stk PC); [|auto].
                rewrite insert_insert /updatePC /= /RegLocate lookup_insert /=.
                assert ((ar + 1)%a = Some ^(ar + 1)%a) as -> by (clear -Harfinal; simpl in Harfinal; solve_addr).
                inv HisCorrectPC. destruct H6 as [-> | [-> | ->] ]; auto. }
        * eapply rtc_once; simpl. rewrite /update_reg /= insert_insert.
          econstructor. econstructor; eauto.
          { instantiate (2 := []). instantiate (3 := []). reflexivity. }
          { reflexivity. }
          { econstructor.
            - instantiate (2 := []). reflexivity.
            - reflexivity.
            - econstructor. }
      + eapply IHwlist; eauto.
        * inv HisCorrectPC; econstructor; eauto.
          clear -H2 Harfinal Hhiar. simpl in Harfinal; solve_addr.
        * clear -Hstkfinal. simpl in Hstkfinal. solve_addr.
        * clear -Hlowstk; solve_addr.
        * clear -Harfinal; simpl in Harfinal. solve_addr.
        * clear -Hlowar; solve_addr.
        * clear -Hstkfinal Hinstrs Hstkdisj Hlowar Hhistk. simpl in Hstkfinal, Hinstrs.
          intros i Hi. destruct (Hinstrs (S i) ltac:(lia)) as [ai [Hai Hinstri] ].
          exists ai. split; [clear -Hai; solve_addr|].
          simpl in Hinstri. rewrite lookup_insert_ne; auto.
          solve_addr.
        * intros i wi Hwi. generalize (Hcanstore (S i) wi Hwi).
          replace ^(astk + S i)%a with ^(^(astk + 1) + i)%a; auto.
          clear -Hstkfinal; simpl in Hstkfinal; solve_addr.
        * destruct Hnotin as [Hnotin1 Hnotin2].
          apply not_elem_of_cons in Hnotin1. destruct Hnotin1 as [Hnotin1 Hnotin1'].
          apply not_elem_of_cons in Hnotin2. destruct Hnotin2 as [Hnotin2 Hnotin2'].
          split; auto.
  Qed.

  Lemma exec_sim_stk:
    forall K reg1 reg1' reg2 reg2' m h h' stk stk' cs cs' mem2 mem2' d p b e a c1 c2
      (Hsexpr: sim_expr (fill K (lang.Instr lang.Executable)) (@ectx_language.fill cap_ectx_lang (map (fun _ => SeqCtx) K) (Instr Executable)))
      (Hstkdisj: forall d1 d2, d1 < d2 -> forall stk1 stk2, stack d1 ((reg1, stk)::cs) = Some stk1 -> stack d2 ((reg1, stk)::cs) = Some stk2 -> forall a1 a2, is_Some (stk1 !! a1) -> is_Some (stk2 !! a2) -> (a1 < a2)%a)
      (Hcswf: sim_cs false h ((reg1, stk)::cs) mem2)
      (Hsregs: forall r w, reg1 !! r = Some w -> reg2 !! r = Some (translate_word w))
      (Hsh: forall a w, h !! a = Some w -> mem2 !! a = Some (translate_word w) /\ lang.pwlW w = false /\ lang.is_global w = true /\ lang.can_address_only w (dom _ h))
      (Hdisj: forall a, a ∈ dom (gset _) h -> (e_stk <= a)%a)
      (HnisJmp: ∀ r : RegName, decodeInstrW' (base.MemLocate m a) ≠ Jmp r)
      (HnisJnz: ∀ r1 r2 : RegName, decodeInstrW' (base.MemLocate m a) ≠ Jnz r1 r2)
      (HisCorrectPC: lang.isCorrectPC (inr (Stk d p b e a)))
      (HQWE: stack d ((reg1, stk)::cs) = Some m),
      reg1 !! PC = Some (inr (Stk d p b e a)) ->
      lang.exec (decodeInstrW' (base.MemLocate m a)) (reg1, h, stk, cs) = (c1, (reg1', h', stk', cs')) ->
      exec (decodeInstrW (mem2 !m! a)) (reg2, mem2) = (c2, (reg2', mem2')) ->
      sim ([ectxi_language.fill K (lang.Instr c1)], (reg1', h', stk', cs')) ([ectxi_language.fill (map (fun _ => SeqCtx) K) (Instr c2)], (reg2', mem2')).
  Proof.
    rewrite /MemLocate /base.MemLocate. intros.
    inv Hcswf. generalize (Hregsdef PC).
    intros [wpc [HPC HinterpPC] ].
    rewrite HPC in H0; inv H0.
    assert (Hisdef: forall x, (b <= x < e)%a -> exists w, m !! x = Some w).
    { destruct HinterpPC as [W1 [W2 [W3 W4] ] ].
      subst d; rewrite stack_cons_length in HQWE.
      inv HQWE. intros. apply W4. simpl.
      inv HisCorrectPC. clear -H0 H9; destruct H9 as [-> | [-> | ->] ]; solve_addr. }
    inv HisCorrectPC. generalize (Hisdef _ H4); intros Hha.
    destruct Hha as [wa Ha]. rewrite Ha in H1.
    assert (Hstksim': forall a w, m !! a = Some w -> mem2 !! a = Some (translate_word w) /\ interp w h m cs /\ canBeStored w a).
    { destruct HinterpPC as [? ?]; subst d.
      rewrite stack_cons_length in HQWE; inv HQWE. auto. }
    generalize (Hstksim' _ _ Ha).
    intros [Ha' [HIa HCSa] ].
    rewrite Ha' in H2. rewrite -decodeInstrW_translate_word in H2.
    rewrite Ha in HnisJmp, HnisJnz.
    destruct (decodeInstrW' wa) eqn:Hinstr.
    - (* Jmp *)
      exfalso; eapply HnisJmp; reflexivity.
    - (* Jnz *)
      exfalso; eapply HnisJnz; reflexivity.
    - (* Mov *)
      simpl in H1, H2.
      assert (match incrementPC (<[dst := word_of_argument reg1 src]> reg1) with Some r => c1 = lang.NextI /\ c2 = NextI /\ reg1' = r /\ h' = h /\ stk' = stk /\ cs' = cs /\ mem2' = mem2 /\ incrementPC' (<[dst := translate_word (word_of_argument reg1 src)]> reg2) = Some reg2' | _ => c1 = lang.Failed /\ c2 = Failed end).
      { destruct (incrementPC (<[dst:=word_of_argument reg1 src]> reg1)) as [reg1''|] eqn:Hincrement1.
        - generalize (@incrementPC_success_updatePC _ _ h stk cs Hincrement1).
          intro A. assert (X: (c1, (reg1', h', stk', cs')) = (lang.NextI, (reg1'', h, stk, cs))).
          { rewrite -A -H1. destruct src; simpl in A; rewrite A; auto. }
          inv X. assert (Hww: exists ww, <[dst:=word_of_argument reg1 src]> reg1 !! PC = Some ww).
          { destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert; eauto|].
            rewrite lookup_insert_ne; auto. rewrite HPC; eauto. }
          destruct Hww as [ww Hww].
          assert (Hww': (<[dst:=translate_word (word_of_argument reg1 src)]> reg2) !! PC = Some (translate_word ww)).
          { destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hww; inv Hww; rewrite lookup_insert //|].
            rewrite lookup_insert_ne; auto.
            rewrite lookup_insert_ne in Hww; auto. }
          generalize (@incrementPC_success_incrementPC' _ _ _ _ Hww Hww' Hincrement1).
          intros [regs2'' Y].
          generalize (@rules_base.incrementPC_success_updatePC _ mem2 _ Y).
          intros [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
          assert (XX: (c2, (reg2', mem2')) = (NextI, (regs2'', mem2))).
          { rewrite Z4 -Z3 - H2. destruct src; simpl; auto.
            replace (reg2 !r! r) with (translate_word (base.RegLocate reg1 r)); auto.
            rewrite /base.RegLocate /RegLocate.
            destruct (Hregsdef r) as [rw [X1 X2] ].
            rewrite X1. rewrite (Hsregs _ _ X1) //. }
          inv XX. repeat split; auto.
        - generalize (@incrementPC_fail_updatePC _ h stk cs Hincrement1).
          intro X. split.
          + destruct src; simpl in H1; rewrite H1 in X; inv X; auto.
          + assert (Hww: exists ww, <[dst:=word_of_argument reg1 src]> reg1 !! PC = Some ww).
            { destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert; eauto|].
              rewrite lookup_insert_ne; auto. rewrite HPC; eauto. }
            destruct Hww as [ww Hww].
            assert (Hww': (<[dst:=translate_word (word_of_argument reg1 src)]> reg2) !! PC = Some (translate_word ww)).
            { destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hww; inv Hww; rewrite lookup_insert //|].
              rewrite lookup_insert_ne; auto.
              rewrite lookup_insert_ne in Hww; auto. }
            generalize (@incrementPC_fail_incrementPC' _ _ _ Hww Hww' Hincrement1). intro Y.
            generalize (rules_base.incrementPC_fail_updatePC _ mem2 Y).
            intro Z. destruct src; simpl in H2; simpl in Z; [rewrite H2 in Z; inv Z; auto|].
            replace (reg2 !r! r) with (translate_word (base.RegLocate reg1 r)) in H2; [rewrite H2 in Z; inv Z; auto|].
            rewrite /base.RegLocate /RegLocate.
            destruct (Hregsdef r) as [rw [X1 X2] ].
            rewrite X1. rewrite (Hsregs _ _ X1) //. }
      destruct (incrementPC (<[dst:=word_of_argument reg1 src]> reg1)) as [reg1''|] eqn:Hincrement; cycle 1.
      + destruct H0 as [-> ->].
        econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          simpl. repeat econstructor.
        * rewrite can_step_fill /can_step /=; intros [A | A]; discriminate.
      + destruct H0 as [-> [-> [-> [<- [<- [<- [<- Hincrement'] ] ] ]  ] ] ].
        econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          simpl. repeat econstructor.
        * intros _. econstructor; eauto.
          -- econstructor; eauto.
             generalize (Hregsdef_preserve_word_of_arg Hregsdef src dst). intros AA.
             generalize (incrementPC_inv_Some Hincrement). intro X1.
             generalize (rules_base.incrementPC_Some_inv _ _ Hincrement').
             intros [p'' [g'' [b'' [e'' [a'' [a''' [Y1 [Y2 [Y3 Y4] ] ] ] ] ] ] ] ].
             destruct (<[dst:=word_of_argument reg1 src]> reg1 !! PC) as [wpc|] eqn:X2; [|elim X1].
             destruct wpc as [?|cap]; [elim X1|].
             destruct cap as [ [ [ [ [p1 g1] b1] e1] a1] | ? | ?]; [| | elim X1].
             ** destruct X1 as [a1' [Ha1' [X1 X1'] ] ].
                rewrite X1. intro. destruct (reg_eq_dec PC r).
                { subst r; rewrite lookup_insert; eexists; split; eauto.
                  simpl. destruct (AA PC) as [wpc [ZA ZB] ].
                  rewrite X2 in ZA; inv ZA. apply ZB. }
                { rewrite lookup_insert_ne; auto. }
             ** destruct X1 as [a2' [Ha2' [X1 X1'] ] ].
                rewrite X1. intro. destruct (reg_eq_dec PC r).
                { subst r; rewrite lookup_insert; eexists; split; eauto.
                  simpl. destruct (AA PC) as [wpc [ZA ZB] ].
                  rewrite X2 in ZA; inv ZA. simpl in ZB.
                  destruct ZB as [ZB1 [ZB3 [ZB4 ZB2] ] ]; split; auto.
                  split; auto. split; auto.
                  intros. apply ZB2. destruct X1' as [? [? [? [? ?] ] ] ].
                  destruct p0; auto; congruence. }
                { rewrite lookup_insert_ne; auto. }
          -- generalize (@Hsregs_preserve_word_of_arg _ _ dst src Hsregs). intros Hsregs'.
             generalize (incrementPC_inv_Some Hincrement). intro X1.
             generalize (rules_base.incrementPC_Some_inv _ _ Hincrement').
             intros [p'' [g'' [b'' [e'' [a'' [a''' [Y1 [Y2 [Y3 Y4] ] ] ] ] ] ] ] ].
             destruct (<[dst:=word_of_argument reg1 src]> reg1 !! PC) as [wpc|] eqn:X2; [|elim X1].
             destruct wpc as [?|cap]; [elim X1|].
             destruct cap as [ [ [ [ [p1 g1] b1] e1] a1] | ? | ?]; [| | elim X1].
             ++ destruct X1 as [a1' [Ha1' [X1 X1'] ] ].
                rewrite X1. intro. destruct (reg_eq_dec PC r).
                { subst r; rewrite lookup_insert.
                  subst reg2'. rewrite lookup_insert.
                  inversion 1. simpl.
                  generalize (Hsregs' _ _ X2). rewrite Y1. simpl. inversion 1; subst.
                  rewrite Y2 in Ha1'; inv Ha1'; auto. }
                { subst reg2'. rewrite !(lookup_insert_ne _ PC); auto. }
             ++ destruct X1 as [a1' [Ha1' [X1 X1'] ] ].
                rewrite X1. intro. destruct (reg_eq_dec PC r).
                { subst r; rewrite lookup_insert.
                  subst reg2'. rewrite lookup_insert.
                  inversion 1. simpl.
                  generalize (Hsregs' _ _ X2). rewrite Y1. simpl. inversion 1; subst.
                  rewrite Y2 in Ha1'; inv Ha1'; auto. }
                { subst reg2'. rewrite !(lookup_insert_ne _ PC); auto. }
    - (* Load *)
      assert (AA: match reg1 !! src with
                  | Some (inr (Regular (pp, gg, bb, ee, aa))) =>
                    if (readAllowed pp) &&  (withinBounds (pp, gg, bb, ee, aa)) then
                      exists wsrc, h !! aa = Some wsrc /\ interp wsrc h stk cs /\
                        match incrementPC (<[dst:=wsrc]> reg1) with
                        | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=translate_word wsrc]> reg2) = Some reg2' /\ mem2' = mem2
                        | None => c1 = lang.Failed /\ c2 = Failed
                        end
                    else c1 = lang.Failed /\ c2 = Failed
                  | Some (inr (Stk dd pp bb ee aa)) =>
                    if (readAllowed pp) && (withinBounds (pp, Directed, bb, ee, aa)) then
                      exists xstk, stack dd ((reg1, stk)::cs) = Some xstk /\ exists wsrc, xstk !! aa = Some wsrc /\ interp wsrc h stk cs /\
                          match incrementPC (<[dst:=wsrc]> reg1) with
                          | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=translate_word wsrc]> reg2) = Some reg2' /\ mem2' = mem2
                          | None => c1 = lang.Failed /\ c2 = Failed
                          end
                    else c1 = lang.Failed /\ c2 = Failed
                  | _ => c1 = lang.Failed /\ c2 = Failed
                  end).
      { destruct (Hregsdef src) as [wsrc [Hwsrc Hinterpsrc] ].
        generalize (Hsregs _ _ Hwsrc); intros Hwsrc'.
        rewrite Hwsrc. destruct wsrc.
        - rewrite /= /base.RegLocate Hwsrc in H1.
          rewrite /= /RegLocate Hwsrc' in H2.
          inv H1; inv H2; auto.
        - destruct (translate_word_cap c) as [c' Hc'].
          rewrite Hc' in Hwsrc'.
          destruct c; [|inv Hc'|inv Hc'; rewrite /= /base.RegLocate Hwsrc in H1; rewrite /= /RegLocate Hwsrc' /= in H2; inv H1; inv H2; auto].
          + destruct c as [ [ [ [pp gg] bb] ee] aa]. inv Hc'.
            rewrite /= /base.RegLocate Hwsrc /base.update_reg /= in H1.
            rewrite /= /RegLocate Hwsrc' /update_reg /= in H2.
            simpl. destruct (readAllowed pp && ((bb <=? aa)%a && (aa <? ee)%a)) eqn:Hcond; cycle 1.
            * inv H1; inv H2; auto.
            * rewrite /base.MemLocate /= in H1.
              rewrite /MemLocate /= in H2.
              destruct Hinterpsrc as [Hpwl Hcan_read].
              eapply andb_true_iff in Hcond. destruct Hcond as [Hcond1 Hcond2].
              eapply andb_true_iff in Hcond2. destruct Hcond2 as [Hcond2 Hcond3].
              apply leb_addr_spec in Hcond2. apply ltb_addr_spec in Hcond3.
              generalize (Hcan_read aa ltac:(clear -Hcond2 Hcond3; solve_addr)).
              intro Hin. eapply elem_of_dom in Hin. destruct Hin as [waa Haa].
              exists waa; split; auto. generalize (Hsh _ _ Haa).
              intros [Haa' [T1 [T2 T3] ] ]. split; [destruct waa; simpl; auto; destruct c; inv T2; auto|].
              rewrite Haa in H1. rewrite Haa' in H2.
              assert (exists w, (<[dst:=waa]> reg1) !! PC = Some w /\ (<[dst:=translate_word waa]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
              { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert /=; eauto|].
                rewrite !lookup_insert_ne //.
                eexists; rewrite HPC; split; auto. }
              destruct (incrementPC (<[dst:=waa]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
              { erewrite incrementPC_fail_updatePC in H1; eauto.
                inv H1; split; auto.
                eapply incrementPC_fail_incrementPC' in Hincrement1; eauto.
                erewrite rules_base.incrementPC_fail_updatePC in H2; eauto.
                inv H2; auto. }
              erewrite incrementPC_success_updatePC in H1; eauto.
              eapply incrementPC_success_incrementPC' in Hincrement1; eauto.
              destruct Hincrement1 as [reg2'' Hincrement2].
              rewrite Hincrement2.
              eapply rules_base.incrementPC_success_updatePC in Hincrement2.
              destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
              instantiate (1 := mem2) in Z3.
              rewrite Z3 -Z4 in H2. inv H1; inv H2; repeat split; auto.
          + rewrite /= /base.RegLocate Hwsrc /base.update_reg /= in H1.
            rewrite /= /RegLocate Hwsrc' /update_reg /= in H2.
            simpl. destruct (readAllowed p0 && ((a0 <=? a2)%a && (a2 <? a1)%a)) eqn:Hcond; cycle 1.
            * inv H1; inv H2; auto.
            * simpl in Hinterpsrc. destruct Hinterpsrc as [Hn [Hbound1 [HQW Hdom] ] ].
              match goal with |- context [(if ?X then _ else _)  = _] => destruct X as [_|ZZ]; [|elim ZZ; auto] end.
              eexists; split; eauto.
              rewrite /base.MemLocate /= in H1.
              rewrite /MemLocate /= in H2.
              eapply andb_true_iff in Hcond. destruct Hcond as [Hcond1 Hcond2].
              eapply andb_true_iff in Hcond2. destruct Hcond2 as [Hcond2 Hcond3].
              apply leb_addr_spec in Hcond2. apply ltb_addr_spec in Hcond3.
              generalize (Hdom a2 ltac:(clear -Hcond1 Hcond2 Hcond3; destruct p0; simpl in Hcond1; try congruence; solve_addr)).
              intros [waa Haa].
              rewrite Haa. rewrite Haa in H1.
              destruct (Hstksim _ _ Haa) as [Haa' [T1 T2] ]. rewrite Haa' in H2.
              eexists; split; eauto. split; auto.
              assert (exists w, (<[dst:=waa]> reg1) !! PC = Some w /\ (<[dst:=translate_word waa]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
              { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert /=; eauto|].
                rewrite !lookup_insert_ne //.
                eexists; rewrite HPC; split; auto. }
              destruct (incrementPC (<[dst:=waa]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
              { erewrite incrementPC_fail_updatePC in H1; eauto.
                inv H1; split; auto.
                eapply incrementPC_fail_incrementPC' in Hincrement1; eauto.
                erewrite rules_base.incrementPC_fail_updatePC in H2; eauto.
                inv H2; auto. }
              erewrite incrementPC_success_updatePC in H1; eauto.
              eapply incrementPC_success_incrementPC' in Hincrement1; eauto.
              destruct Hincrement1 as [reg2'' Hincrement2].
              rewrite Hincrement2.
              eapply rules_base.incrementPC_success_updatePC in Hincrement2.
              destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
              instantiate (1 := mem2) in Z3.
              rewrite Z3 -Z4 in H2. inv H1; inv H2; repeat split; auto. }
      destruct (Hregsdef src) as [wsrc [Hwsrc Hinterp1] ].
      generalize (Hsregs _ _ Hwsrc); intros Hwsrc'.
      rewrite Hwsrc in AA. clear H1 H2.
      destruct wsrc.
      { destruct AA as [-> ->]. econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          simpl. repeat econstructor.
        * rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
      destruct c; cycle 2.
      { destruct AA as [-> ->]. econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          simpl. repeat econstructor.
        * rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
      { destruct c as [ [ [ [pp gg] bb] ee] aa].
        destruct (readAllowed pp && withinBounds (pp, gg, bb, ee, aa)) eqn:Hconds; cycle 1.
        { destruct AA as [-> ->]. econstructor.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            simpl. repeat econstructor.
          * rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
        destruct AA as [waa [Haa [Hinterpaa AA] ] ].
        destruct (incrementPC (<[dst:=waa]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        { destruct AA as [-> ->]. econstructor.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            simpl. repeat econstructor.
          * rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
        destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
        econstructor; eauto.
        - eapply sim_expr_exec_inv in Hsexpr. subst K.
          simpl. repeat econstructor.
        - eapply incrementPC_inv_Some in Hincrement1.
          destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|].
          + destruct waa; [elim Hincrement1|].
            destruct c; [| |elim Hincrement1].
            * destruct c as [ [ [ [px gx] bx] ex] ax].
              destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite lookup_insert in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              inv HXX. rewrite Hap1 in Hap1'; inv Hap1'.
              rewrite !insert_insert.
              intros _. econstructor; eauto.
              { econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto]. }
              { intros rr; destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|rewrite !lookup_insert_ne; auto]. }
            * intros. destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite lookup_insert in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              inv HXX. rewrite Hap1 in Hap1'; inv Hap1'.
              rewrite !insert_insert.
              constructor; eauto.
              { econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; eauto].
                eexists; split; eauto.
                simpl. destruct Hinterpaa as [? [? [? ?] ] ].
                do 3 (split; auto).
                intros; eapply H5. simpl.
                destruct X2 as [? [? [? [? ?] ] ] ].
                destruct ppp; try congruence; auto. }
              { intros rr; destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|rewrite !lookup_insert_ne; auto]. }
          + rewrite lookup_insert_ne in Hincrement1; auto.
            intros _. rewrite HPC in Hincrement1.
            destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
            eapply rules_base.incrementPC_Some_inv in Hincrement2.
            destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
            rewrite lookup_insert_ne in HXX; auto.
            generalize (Hsregs _ _ HPC). rewrite HXX.
            intro DD; inv DD. rewrite Hap1 in Hap1'; inv Hap1'.
            econstructor; eauto.
            * econstructor; eauto. intros rr.
              destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite (lookup_insert_ne _ PC); auto].
              { eexists; split; eauto.
                simpl in HinterpPC. destruct H8 as [-> | [-> | ->] ]; auto. }
              destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
            * intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto| rewrite !(lookup_insert_ne _ PC); auto].
              destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert; inversion 1; auto| rewrite !lookup_insert_ne; auto]. }
      { destruct (readAllowed p0 && withinBounds (p0, Directed, a0, a1, a2)) eqn:Hconds; cycle 1.
        { destruct AA as [-> ->]. econstructor.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            simpl. repeat econstructor.
          * rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
        destruct AA as [xstk [Hxstk [waa [Haa [Hinterpaa AA] ] ] ] ].
        destruct (incrementPC (<[dst:=waa]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        { destruct AA as [-> ->]. econstructor.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            simpl. repeat econstructor.
          * rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
        destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
        econstructor; eauto.
        - eapply sim_expr_exec_inv in Hsexpr. subst K.
          simpl. repeat econstructor.
        - eapply incrementPC_inv_Some in Hincrement1.
          destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|].
          + destruct waa; [elim Hincrement1|].
            destruct c; [| |elim Hincrement1].
            * destruct c as [ [ [ [px gx] bx] ex] ax].
              destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite lookup_insert in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              inv HXX. rewrite Hap1 in Hap1'; inv Hap1'.
              rewrite !insert_insert.
              intros _. econstructor; eauto.
              { econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto]. }
              { intros rr; destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|rewrite !lookup_insert_ne; auto]. }
            * intros. destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite lookup_insert in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              inv HXX. rewrite Hap1 in Hap1'; inv Hap1'.
              rewrite !insert_insert.
              constructor; eauto.
              { econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; eauto].
                eexists; split; eauto.
                simpl. destruct Hinterpaa as [? [? [? ?] ] ].
                do 3 (split; auto).
                intros; eapply H5. simpl.
                destruct X2 as [? [? [? [? ?] ] ] ].
                destruct ppp; try congruence; auto. }
              { intros rr; destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|rewrite !lookup_insert_ne; auto]. }
          + rewrite lookup_insert_ne in Hincrement1; auto.
            intros _. rewrite HPC in Hincrement1.
            destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
            eapply rules_base.incrementPC_Some_inv in Hincrement2.
            destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
            rewrite lookup_insert_ne in HXX; auto.
            generalize (Hsregs _ _ HPC). rewrite HXX.
            intro DD; inv DD. rewrite Hap1 in Hap1'; inv Hap1'.
            econstructor; eauto.
            * econstructor; eauto. intros rr.
              destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite (lookup_insert_ne _ PC); auto].
              { eexists; split; eauto. simpl in HinterpPC. simpl.
                destruct H8 as [-> | [-> | ->] ]; auto. }
              destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
            * intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto| rewrite !(lookup_insert_ne _ PC); auto].
              destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert; inversion 1; auto| rewrite !lookup_insert_ne; auto]. }
    - (* Store *)
      destruct (Hregsdef dst) as [wdst [Hwdst Hinterpdst] ].
      generalize (Hsregs _ _ Hwdst). intros Hwdst'.
      assert (exists wsrc, word_of_argument reg1 src = wsrc /\ interp wsrc h stk cs) as [wsrc [Hwsrc Hinterpsrc] ].
      { destruct src; [simpl; eexists; split; eauto; simpl; auto|].
        destruct (Hregsdef r) as [? [? ?] ]. simpl.
        rewrite /base.RegLocate H0. eauto. }
      assert (rules_base.word_of_argument reg2 src = Some (translate_word wsrc)) as Hwsrc'.
      { destruct src; [inv Hwsrc; simpl; auto|].
        destruct (Hregsdef r) as [? [? ?] ]. rewrite /= /base.RegLocate H0 in Hwsrc.
        inv Hwsrc; eapply Hsregs; eauto. }
      assert (AA: match wdst with
                  | inr (Regular (pp, gg, bb, ee, aa)) =>
                    if (writeAllowed pp) && ((bb <=? aa)%a && (aa <? ee)%a) && (lang.canStore pp aa wsrc) then
                      match incrementPC reg1 with
                      | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = (<[aa:=wsrc]> h) /\ stk' = stk /\ cs' = cs /\ incrementPC' reg2 = Some reg2' /\ mem2' = (<[aa:=translate_word wsrc]> mem2)
                      | None => c1 = lang.Failed /\ c2 = Failed
                      end
                    else c1 = lang.Failed /\ c2 = Failed
                  | inr (Stk dd pp bb ee aa) =>
                    if (writeAllowed pp) && ((bb <=? aa)%a && (aa <? ee)%a) && (lang.canStore pp aa wsrc) then
                      match incrementPC reg1 with
                      | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ (stk' = if nat_eq_dec dd (length cs) then <[aa:=wsrc]> stk else stk) /\ (if nat_eq_dec dd (length cs) then cs' = cs else update_callstack cs dd aa wsrc = Some cs') /\ incrementPC' reg2 = Some reg2' /\ mem2' = (<[aa:=translate_word wsrc]> mem2)
                      | None => c1 = lang.Failed /\ c2 = Failed
                      end
                    else c1 = lang.Failed /\ c2 = Failed
                  | _ => c1 = lang.Failed /\ c2 = Failed
                  end).
      { rewrite /= /base.RegLocate Hwdst in H1.
        rewrite /= /RegLocate Hwdst' in H2.
        assert (match wdst with
         | inl _ => (lang.Failed, (reg1, h, stk, cs))
         | inr c =>
             match c with
             | Regular c0 =>
                 let (p0, a) := c0 in
                 let (p1, e) := p0 in
                 let (p2, b) := p1 in
                 let (p, _) := p2 in
                 if writeAllowed p && ((b <=? a)%a && (a <? e)%a) && lang.canStore p a wsrc
                 then
                  lang.updatePC
                    (base.update_mem (reg1, h, stk, cs) a wsrc)
                 else (lang.Failed, (reg1, h, stk, cs))
             | Stk d p b e a =>
                if writeAllowed p && ((b <=? a)%a && (a <? e)%a) && lang.canStore p a wsrc then
                 if nat_eq_dec d (length cs)
                 then lang.updatePC (update_stk (reg1, h, stk, cs) a wsrc)
                 else
                  match update_stack (reg1, h, stk, cs) d a wsrc with
                  | Some φ' => lang.updatePC φ'
                  | None => (lang.Failed, (reg1, h, stk, cs))
                  end
                else (lang.Failed, (reg1, h, stk, cs))
             | Ret _ _ _ => (lang.Failed, (reg1, h, stk, cs))
             end
         end = (c1, (reg1', h', stk', cs')) /\ match translate_word wdst with
         | inl _ => (Failed, (reg2, mem2))
         | inr c =>
             let (p0, a) := c in
             let (p1, e) := p0 in
             let (p2, b) := p1 in
             let (p, _) := p2 in
             if writeAllowed p && ((b <=? a)%a && (a <? e)%a) && canStore p a (translate_word wsrc)
             then updatePC (update_mem (reg2, mem2) a (translate_word wsrc))
             else (Failed, (reg2, mem2))
         end = (c2, (reg2', mem2'))) as [X1 X2].
        { destruct src; [inv Hwsrc; inv Hwsrc'; simpl in H2; simpl; auto|].
          - destruct wdst; simpl in H2; simpl; auto.
            destruct c; simpl; simpl in H2; try (rewrite andb_true_r); auto.
            destruct c as [ [ [ [pp gg] bb] ee] aa]; rewrite andb_true_r; auto.
          - simpl in Hwsrc; simpl in Hwsrc'.
            rewrite /base.RegLocate in Hwsrc. rewrite Hwsrc in H1.
            rewrite /RegLocate in Hwsrc'. rewrite Hwsrc' in H2. auto. }
        clear H1 H2.
        destruct wdst; [simpl in X2; inv X1; inv X2; auto|].
        destruct c; [|simpl in X2|simpl in X2; inv X1; inv X2; auto].
        - destruct c as [ [ [ [pp gg] bb] ee] aa].
          simpl in X2. assert (YY: lang.canStore pp aa wsrc = canStore pp aa (translate_word wsrc)).
          { clear. destruct wsrc; auto. destruct c; auto. }
          rewrite -YY in X2. destruct (writeAllowed pp && ((bb <=? aa)%a && (aa <? ee)%a) && lang.canStore pp aa wsrc) eqn:Hconds; [|inv X1; inv X2; auto].
          rewrite /base.update_mem /= in X1.
          rewrite /update_mem /= in X2.
          generalize (Hsregs _ _ HPC). intros HPC'.
          destruct (incrementPC reg1) as [reg1''|] eqn:Hincrement1.
          { erewrite incrementPC_success_updatePC in X1; eauto.
            eapply incrementPC_success_incrementPC' in HPC; eauto.
            destruct HPC as [reg2'' HX].
            rewrite HX.
            eapply rules_base.incrementPC_success_updatePC in HX.
            destruct HX as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
            instantiate (1 := (<[aa:=translate_word wsrc]> mem2)) in Z3.
            rewrite Z3 -Z4 in X2. inv X1; inv X2; repeat split; auto. }
          { erewrite incrementPC_fail_updatePC in X1; eauto.
            inv X1; split; auto.
            eapply incrementPC_fail_incrementPC' in HPC; eauto.
            erewrite rules_base.incrementPC_fail_updatePC in X2; eauto.
            inv X2; auto. }
        - assert (YY: lang.canStore p0 a2 wsrc = canStore p0 a2 (translate_word wsrc)).
          { clear. destruct wsrc; auto. destruct c; auto. }
          rewrite -YY in X2. destruct (writeAllowed p0 && ((a0 <=? a2)%a && (a2 <? a1)%a) && lang.canStore p0 a2 wsrc) eqn:Hconds; [|inv X1; inv X2; auto].
          rewrite /base.update_mem /= in X1.
          rewrite /update_mem /= in X2.
          generalize (Hsregs _ _ HPC). intros HPC'.
          destruct (incrementPC reg1) as [reg1''|] eqn:Hincrement1.
          { simpl in Hinterpdst. destruct Hinterpdst as [TT Hinterpdst].
            destruct (nat_eq_dec n (length cs)) as [_|RR]; [|elim RR; auto].
            rewrite /update_stk /= in X1.
            erewrite incrementPC_success_updatePC in X1; eauto.
            eapply incrementPC_success_incrementPC' in HPC; eauto.
            destruct HPC as [reg2'' HX].
            rewrite HX.
            eapply rules_base.incrementPC_success_updatePC in HX.
            destruct HX as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
            instantiate (1 := <[a2:=translate_word wsrc]> mem2) in Z3.
            rewrite Z3 -Z4 in X2. inv X1; inv X2; repeat split; auto. }
          { simpl in Hinterpdst. destruct Hinterpdst as [TT Hinterpdst].
            destruct (nat_eq_dec n (length cs)) as [_|RR]; [|elim RR; auto].
            rewrite /update_stk /= in X1.
            erewrite incrementPC_fail_updatePC in X1; eauto.
            inv X1; split; auto.
            eapply incrementPC_fail_incrementPC' in HPC; eauto.
            erewrite rules_base.incrementPC_fail_updatePC in X2; eauto.
            inv X2; auto. } }
      destruct wdst.
      { destruct AA as [-> ->]. econstructor.
        - eapply sim_expr_exec_inv in Hsexpr. subst K.
          simpl. repeat econstructor.
        - rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
      destruct c; cycle 2.
      { destruct AA as [-> ->]. econstructor.
        - eapply sim_expr_exec_inv in Hsexpr. subst K.
          simpl. repeat econstructor.
        - rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
      { destruct c as [ [ [ [pp gg] bb] ee] aa].
        destruct (writeAllowed pp && ((bb <=? aa)%a && (aa <? ee)%a) && lang.canStore pp aa wsrc) eqn:Hconds; cycle 1.
        { destruct AA as [-> ->]. econstructor.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            simpl. repeat econstructor.
          - rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
        erewrite !andb_true_iff in Hconds. destruct Hconds as [ [Hcond1 Hcond2] Hcond3].
        erewrite leb_addr_spec in Hcond2. erewrite ltb_addr_spec in Hcond2.
        destruct (incrementPC reg1) as [reg1''|] eqn:Hincrement1; cycle 1.
        { destruct AA as [-> ->]. econstructor.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            simpl. repeat econstructor.
          - rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
        destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
        econstructor; eauto.
        - eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        - intros _. eapply incrementPC_inv_Some in Hincrement1.
          rewrite HPC in Hincrement1. destruct Hincrement1 as [ap1 [Hap1 [-> TT] ] ].
          eapply rules_base.incrementPC_Some_inv in Hincrement2.
          rewrite (Hsregs _ _ HPC) /= in Hincrement2.
          destruct Hincrement2 as [? [? [? [? [? [? [XXX [Hap1' [-> XY] ] ] ] ] ] ] ] ]; inv XXX.
          rewrite Hap1 in Hap1'; inv Hap1'.
          econstructor; eauto.
          + econstructor; eauto.
            * intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
              { eexists; split; auto. eapply interp_heap_extend.
                simpl in HinterpPC. simpl. destruct H8 as [-> | [-> | ->] ]; auto. }
              destruct (Hregsdef rr) as [wrr [Hwrr Hinterprr] ].
              eexists; split; eauto. apply interp_heap_extend; auto.
            * intros. generalize (Hstkdisjheap a ltac:(eexists; apply H0)).
              simpl in Hinterpdst. destruct Hinterpdst as [? ?].
              generalize (H5 aa ltac:(clear -Hcond2; solve_addr)).
              intros. apply Hdisj in H6.
              assert (aa <> a) by (clear -H6 H7; solve_addr).
              rewrite !lookup_insert_ne; auto. apply Hstksim in H0.
              destruct H0 as [? [? ?] ]; do 2 (split; auto).
              apply interp_heap_extend; auto.
            * eapply sim_cs_heap_extend; auto.
              simpl in Hinterpdst. destruct Hinterpdst as [? ?].
              generalize (H3 aa ltac:(clear -Hcond2; solve_addr)).
              intro F. apply Hdisj in F. auto.
          + intro rr; destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto| rewrite !lookup_insert_ne; auto].
          + intro ax. destruct (addr_eq_dec aa ax); [subst ax; rewrite !lookup_insert|rewrite !lookup_insert_ne; auto].
            * inversion 1; split; auto.
              destruct (word_of_argument reg1 src); auto.
              simpl in Hinterpdst. simpl in Hcond3.
              destruct Hinterpdst as [Q W].
              assert (E: pwl pp = false) by (clear -Q; destruct pp; try congruence; auto).
              rewrite E andb_false_l in Hcond3.
              destruct c; try congruence.
              destruct c as [ [ [ [px gx] bx] ex] ax].
              destruct gx; try congruence.
              simpl. simpl in Hinterpsrc.
              destruct Hinterpsrc. do 2 (split; auto).
              intros. apply H6 in H7. clear -H7; set_solver.
            * intros. apply Hsh in H0. destruct H0 as [R [T [Y U] ] ].
              do 3 (split; auto). apply can_address_only_heap_extend; auto.
          + intros. assert (a = aa \/ a ∈ dom (gset Addr) h) by (clear -H0; set_solver).
            destruct H3; [subst a|apply Hdisj; auto].
            simpl in Hinterpdst. destruct Hinterpdst as [? ?].
            generalize (H5 aa ltac:(clear -Hcond2; solve_addr)).
            intro F. apply Hdisj in F. auto. }
      { destruct (writeAllowed p0 && ((a0 <=? a2)%a && (a2 <? a1)%a) && lang.canStore p0 a2 wsrc) eqn:Hconds; cycle 1.
        { destruct AA as [-> ->]. econstructor.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            simpl. repeat econstructor.
          - rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
        erewrite !andb_true_iff in Hconds. destruct Hconds as [ [Hcond1 Hcond2] Hcond3].
        erewrite leb_addr_spec in Hcond2. erewrite ltb_addr_spec in Hcond2.
        destruct (incrementPC reg1) as [reg1''|] eqn:Hincrement1; cycle 1.
        { destruct AA as [-> ->]. econstructor.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            simpl. repeat econstructor.
          - rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
        destruct (nat_eq_dec n (length cs)) as [_|G]; [|elim G; destruct Hinterpdst; auto].
        destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
        econstructor; eauto.
        - eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        - intros _. eapply incrementPC_inv_Some in Hincrement1.
          rewrite HPC in Hincrement1. destruct Hincrement1 as [ap1 [Hap1 [-> TT] ] ].
          eapply rules_base.incrementPC_Some_inv in Hincrement2.
          rewrite (Hsregs _ _ HPC) /= in Hincrement2.
          destruct Hincrement2 as [? [? [? [? [? [? [XXX [Hap1' [-> XY] ] ] ] ] ] ] ] ]; inv XXX.
          rewrite Hap1 in Hap1'; inv Hap1'.
          econstructor; eauto.
          + simpl in Hinterpdst. intros d1 d2 Hlt.
            destruct (nat_eq_dec d2 (length cs)).
            * subst d2. rewrite stack_cons_length.
              intros. inv H3.
              destruct (addr_eq_dec a2 a4).
              { subst a4. destruct Hinterpdst as [? [? [XZ ?] ] ].
                simpl in H0.
                match goal with H: context [(if ?S then _ else _) = Some stk1] |- _ => destruct S as [G|_]; [clear -G Hlt; unfold Stackframe in G; lia|] end.
                eapply XZ in H5; eauto.
                clear -H5 Hcond2; solve_addr. }
              rewrite lookup_insert_ne in H6; auto.
              eapply Hstkdisj; eauto; [|rewrite stack_cons_length; auto].
              simpl. simpl in H0. unfold Stackframe in *.
              destruct (nat_eq_dec d1 (length cs)); [lia|auto].
            * intros. rewrite (stack_cons_length_ne) in H3; eauto.
              generalize (proj1 (stack_is_Some _ _) ltac:(eexists; apply H3)).
              intros XT. rewrite (stack_cons_length_ne) in H0; eauto; [|unfold Stackframe in *; lia].
              eapply (Hstkdisj d1 d2 Hlt); eauto; rewrite stack_cons_length_ne; eauto.
              unfold Stackframe in *. lia.
          + econstructor; eauto.
            * intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
              { eexists; split; auto. apply interp_stack_extend.
                simpl. simpl in HinterpPC. destruct H8 as [-> | [-> | ->] ]; auto. }
              destruct (Hregsdef rr) as [wrr [Hwrr Hinterprr] ].
              eexists; split; eauto. apply interp_stack_extend; auto.
            * simpl in Hinterpdst. destruct Hinterpdst as [? [GG ?] ].
              clear -Hstkdisjheap Hcond2 GG.
              intro ax. destruct (addr_eq_dec a2 ax); [subst ax; intros; solve_addr|rewrite lookup_insert_ne; auto].
            * intros ax. destruct (addr_eq_dec a2 ax); [subst ax; rewrite !lookup_insert|rewrite !(lookup_insert_ne _ a2); auto].
              { inversion 1; split; auto.
                split; [apply interp_stack_extend; auto|].
                rewrite /canBeStored /=. eapply canStore_canStoreU_URWLX; eauto. }
              intros. apply Hstksim in H0. destruct H0 as [? [? ?] ].
              do 2 (split; auto). apply interp_stack_extend; auto.
            * assert (XQC: forall d xstk, stack d cs = Some xstk -> forall ax, is_Some (xstk !! ax) -> (ax < a2)%a).
              { destruct Hinterpdst as [W1 [W2 [W3 W4] ] ].
                intros. eapply W3 in H3; eauto. clear -H3 Hcond2; solve_addr. }
              eapply sim_cs_stack_extend; eauto.
          + intro rr; destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto| rewrite !lookup_insert_ne; auto].
          + intros. rewrite lookup_insert_ne; auto.
            assert (is_Some (h !! a)) by (eexists; eauto).
            apply elem_of_dom in H3.
            generalize (Hdisj _ H3). intro T.
            destruct Hinterpdst as [W1 [W2 ?] ].
            clear -Hcond2 T W2. solve_addr. }
    - (* Lt *)
      assert (match (lang.z_of_argument reg1 r1, lang.z_of_argument reg1 r2) with
              | (Some n1, Some n2) =>
                match incrementPC (<[dst:=inl (Z.b2z (n1 <? n2)%Z)]> reg1) with
                | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inl (Z.b2z (n1 <? n2)%Z)]> reg2) = Some reg2' /\ mem2' = mem2
                | None => c1 = lang.Failed /\ c2 = Failed
                end
              | (_, _) => c1 = lang.Failed /\ c2 = Failed
      end).
      { assert (Hregsome1: forall r, is_Some (reg1 !!r)).
        { intros. destruct (Hregsdef r) as [rw [-> _] ]. eauto. }
        destruct (lang.z_of_argument reg1 r1) as [n1|] eqn:Hr1.
        - destruct (lang.z_of_argument reg1 r2) as [n2|] eqn:Hr2.
          + eapply z_of_argument_inv_Some in Hr1.
            eapply z_of_argument_inv_Some in Hr2.
            assert (XX: lang.exec (Lt dst r1 r2) (reg1, h, stk, cs) = lang.updatePC (<[dst:=inl (Z.b2z (n1 <? n2)%Z)]> reg1, h, stk, cs)).
            { rewrite /lang.exec /=. destruct Hr1 as [-> | [r1' [-> Hr1eq] ] ].
              - destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ].
                + reflexivity.
                + rewrite /base.RegLocate Hr2eq //.
              - rewrite /base.RegLocate Hr1eq.
                destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ]; [reflexivity| rewrite Hr2eq //]. }
            rewrite XX in H1; clear XX.
            assert (XX: exec (Lt dst r1 r2) (reg2, mem2) = updatePC (<[dst:=inl (Z.b2z (n1 <? n2)%Z)]> reg2, mem2)).
            { rewrite /exec /=. destruct Hr1 as [-> | [r1' [-> Hr1eq] ] ].
              - destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ]; [reflexivity|].
                rewrite /RegLocate (Hsregs _ _ Hr2eq) //.
              - rewrite /RegLocate (Hsregs _ _ Hr1eq) /=.
                destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ]; [reflexivity|].
                rewrite (Hsregs _ _ Hr2eq) //. }
            rewrite XX in H2; clear XX.
            rewrite /base.update_reg /= in H1.
            assert (exists w, (<[dst:=inl (Z.b2z (n1 <? n2)%Z)]> reg1) !! PC = Some w /\ (<[dst:=inl (Z.b2z (n1 <? n2)%Z)]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
            { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert /=; eauto|].
              rewrite !lookup_insert_ne //.
              eexists; rewrite HPC; split; auto. }
            destruct (incrementPC (<[dst:=inl (Z.b2z (n1 <? n2)%Z)]> reg1)) as [reg1''|] eqn:HX.
            * erewrite incrementPC_success_updatePC in H1; eauto.
              eapply incrementPC_success_incrementPC' in HX; eauto.
              destruct HX as [reg2'' HX].
              rewrite HX.
              eapply rules_base.incrementPC_success_updatePC in HX.
              destruct HX as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
              instantiate (1 := mem2) in Z3.
              rewrite Z3 -Z4 in H2. inv H1; inv H2; repeat split; auto.
            * erewrite incrementPC_fail_updatePC in H1; eauto.
              inv H1; split; auto.
              eapply incrementPC_fail_incrementPC' in HX; eauto.
              erewrite rules_base.incrementPC_fail_updatePC in H2; eauto.
              inv H2; auto.
          + simpl in H1, H2.
            eapply z_of_argument_inv_None in Hr2; eauto.
            destruct Hr2 as [r2' [cap2 [-> Hr2eq] ] ].
            rewrite /base.RegLocate Hr2eq in H1.
            destruct (translate_word_cap cap2) as [cap2' Hcap2'].
            generalize (Hsregs _ _ Hr2eq). rewrite Hcap2'; intros Hr2eq'.
            rewrite /RegLocate Hr2eq' in H2.
            destruct r1; [inv H1; inv H2; split; auto|].
            destruct (reg1 !! r) as [w1|]; destruct (reg2 !! r) as [w2|]; try (destruct w1); try (destruct w2); inv H1; inv H2; split; auto.
        - simpl in H1, H2.
          eapply z_of_argument_inv_None in Hr1; eauto.
          destruct Hr1 as [r1' [cap1 [-> Hr1eq] ] ].
          rewrite /base.RegLocate Hr1eq in H1.
          destruct (translate_word_cap cap1) as [cap1' Hcap1'].
          generalize (Hsregs _ _ Hr1eq). rewrite Hcap1'; intros Hr1eq'.
          rewrite /RegLocate Hr1eq' in H2.
          destruct r2; inv H1; inv H2; auto. }
      destruct (lang.z_of_argument reg1 r1) as [n1|] eqn:Hn1; cycle 1.
      + destruct H0 as [-> ->]. econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          simpl. repeat econstructor.
        * rewrite can_step_fill /can_step /=; intros [A | A]; discriminate.
      + destruct (lang.z_of_argument reg1 r2) as [n2|] eqn:Hn2; cycle 1.
        * destruct H0 as [-> ->]. econstructor.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            simpl. repeat econstructor. }
          { rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
        * destruct (incrementPC (<[dst:=inl (Z.b2z (n1 <? n2)%Z)]> reg1)) as [reg1''|] eqn:Hincrement; cycle 1.
          { destruct H0 as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              simpl. repeat econstructor.
            - rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
          { destruct H0 as [-> [-> [-> [-> [-> [-> [Hincrement' ->] ] ] ] ] ] ].
            econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              simpl. repeat econstructor.
            - intros _. eapply incrementPC_inv_Some in Hincrement.
              destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in  Hincrement; elim Hincrement|].
              rewrite lookup_insert_ne // in Hincrement.
              rewrite HPC in Hincrement. destruct Hincrement as [ap1 [Hap1 [-> XX] ] ] .
              eapply rules_base.incrementPC_Some_inv in Hincrement'.
              rewrite lookup_insert_ne // in Hincrement'.
              rewrite (Hsregs _ _ HPC) /= in Hincrement'.
              destruct Hincrement' as [? [? [? [? [? [? [XXX [Hap1' [-> XY] ] ] ] ] ] ] ] ]; inv XXX.
              rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              + econstructor; eauto. intros.
                destruct (reg_eq_dec PC r).
                * subst r; rewrite lookup_insert. eexists; split; eauto.
                  simpl. simpl in HinterpPC. destruct H8 as [-> | [-> | ->] ]; auto.
                * rewrite lookup_insert_ne //. destruct (reg_eq_dec dst r).
                  { subst r; rewrite lookup_insert. eexists; split; eauto.
                    simpl; auto. }
                  { rewrite lookup_insert_ne //. }
              + intros r; destruct (reg_eq_dec PC r); [subst r|].
                * rewrite !lookup_insert; inversion 1; simpl; auto.
                * rewrite !(lookup_insert_ne _ PC) //. destruct (reg_eq_dec dst r); [subst r|].
                  { rewrite !lookup_insert; inversion 1; simpl; auto. }
                  { rewrite !lookup_insert_ne //. auto. } }
    - (* Add *)
      assert (match (lang.z_of_argument reg1 r1, lang.z_of_argument reg1 r2) with
              | (Some n1, Some n2) =>
                match incrementPC (<[dst:=inl (n1 + n2)%Z]> reg1) with
                | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inl (n1 + n2)%Z]> reg2) = Some reg2' /\ mem2' = mem2
                | None => c1 = lang.Failed /\ c2 = Failed
                end
              | (_, _) => c1 = lang.Failed /\ c2 = Failed
      end).
      { assert (Hregsome1: forall r, is_Some (reg1 !!r)).
        { intros. destruct (Hregsdef r) as [rw [-> _] ]. eauto. }
        destruct (lang.z_of_argument reg1 r1) as [n1|] eqn:Hr1.
        - destruct (lang.z_of_argument reg1 r2) as [n2|] eqn:Hr2.
          + eapply z_of_argument_inv_Some in Hr1.
            eapply z_of_argument_inv_Some in Hr2.
            assert (XX: lang.exec (machine_base.Add dst r1 r2) (reg1, h, stk, cs) = lang.updatePC (<[dst:=inl ((n1 + n2)%Z)]> reg1, h, stk, cs)).
            { rewrite /lang.exec /=. destruct Hr1 as [-> | [r1' [-> Hr1eq] ] ].
              - destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ].
                + reflexivity.
                + rewrite /base.RegLocate Hr2eq //.
              - rewrite /base.RegLocate Hr1eq.
                destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ]; [reflexivity| rewrite Hr2eq //]. }
            rewrite XX in H1; clear XX.
            assert (XX: exec (machine_base.Add dst r1 r2) (reg2, mem2) = updatePC (<[dst:=inl ((n1 + n2)%Z)]> reg2, mem2)).
            { rewrite /exec /=. destruct Hr1 as [-> | [r1' [-> Hr1eq] ] ].
              - destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ]; [reflexivity|].
                rewrite /RegLocate (Hsregs _ _ Hr2eq) //.
              - rewrite /RegLocate (Hsregs _ _ Hr1eq) /=.
                destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ]; [reflexivity|].
                rewrite (Hsregs _ _ Hr2eq) //. }
            rewrite XX in H2; clear XX.
            rewrite /base.update_reg /= in H1.
            assert (exists w, (<[dst:=inl ((n1 + n2)%Z)]> reg1) !! PC = Some w /\ (<[dst:=inl ((n1 + n2)%Z)]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
            { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert /=; eauto|].
              rewrite !lookup_insert_ne //.
              eexists; rewrite HPC; split; auto. }
            destruct (incrementPC (<[dst:=inl ((n1 + n2)%Z)]> reg1)) as [reg1''|] eqn:HX.
            * erewrite incrementPC_success_updatePC in H1; eauto.
              eapply incrementPC_success_incrementPC' in HX; eauto.
              destruct HX as [reg2'' HX].
              rewrite HX.
              eapply rules_base.incrementPC_success_updatePC in HX.
              destruct HX as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
              instantiate (1 := mem2) in Z3.
              rewrite Z3 -Z4 in H2. inv H1; inv H2; repeat split; auto.
            * erewrite incrementPC_fail_updatePC in H1; eauto.
              inv H1; split; auto.
              eapply incrementPC_fail_incrementPC' in HX; eauto.
              erewrite rules_base.incrementPC_fail_updatePC in H2; eauto.
              inv H2; auto.
          + simpl in H1, H2.
            eapply z_of_argument_inv_None in Hr2; eauto.
            destruct Hr2 as [r2' [cap2 [-> Hr2eq] ] ].
            rewrite /base.RegLocate Hr2eq in H1.
            destruct (translate_word_cap cap2) as [cap2' Hcap2'].
            generalize (Hsregs _ _ Hr2eq). rewrite Hcap2'; intros Hr2eq'.
            rewrite /RegLocate Hr2eq' in H2.
            destruct r1; [inv H1; inv H2; split; auto|].
            destruct (reg1 !! r) as [w1|]; destruct (reg2 !! r) as [w2|]; try (destruct w1); try (destruct w2); inv H1; inv H2; split; auto.
        - simpl in H1, H2.
          eapply z_of_argument_inv_None in Hr1; eauto.
          destruct Hr1 as [r1' [cap1 [-> Hr1eq] ] ].
          rewrite /base.RegLocate Hr1eq in H1.
          destruct (translate_word_cap cap1) as [cap1' Hcap1'].
          generalize (Hsregs _ _ Hr1eq). rewrite Hcap1'; intros Hr1eq'.
          rewrite /RegLocate Hr1eq' in H2.
          destruct r2; inv H1; inv H2; auto. }
      destruct (lang.z_of_argument reg1 r1) as [n1|] eqn:Hn1; cycle 1.
      + destruct H0 as [-> ->]. econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          simpl. repeat econstructor.
        * rewrite can_step_fill /can_step /=; intros [A | A]; discriminate.
      + destruct (lang.z_of_argument reg1 r2) as [n2|] eqn:Hn2; cycle 1.
        * destruct H0 as [-> ->]. econstructor.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            simpl. repeat econstructor. }
          { rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
        * destruct (incrementPC (<[dst:=inl ((n1 + n2)%Z)]> reg1)) as [reg1''|] eqn:Hincrement; cycle 1.
          { destruct H0 as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              simpl. repeat econstructor.
            - rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
          { destruct H0 as [-> [-> [-> [-> [-> [-> [Hincrement' ->] ] ] ] ] ] ].
            econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              simpl. repeat econstructor.
            - intros _. eapply incrementPC_inv_Some in Hincrement.
              destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in  Hincrement; elim Hincrement|].
              rewrite lookup_insert_ne // in Hincrement.
              rewrite HPC in Hincrement. destruct Hincrement as [ap1 [Hap1 [-> XX] ] ] .
              eapply rules_base.incrementPC_Some_inv in Hincrement'.
              rewrite lookup_insert_ne // in Hincrement'.
              rewrite (Hsregs _ _ HPC) /= in Hincrement'.
              destruct Hincrement' as [? [? [? [? [? [? [XXX [Hap1' [-> XY] ] ] ] ] ] ] ] ]; inv XXX.
              rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              + econstructor; eauto. intros.
                destruct (reg_eq_dec PC r).
                * subst r; rewrite lookup_insert. eexists; split; eauto.
                  simpl. simpl in HinterpPC. destruct H8 as [-> | [-> | ->] ]; auto.
                * rewrite lookup_insert_ne //. destruct (reg_eq_dec dst r).
                  { subst r; rewrite lookup_insert. eexists; split; eauto.
                    simpl; auto. }
                  { rewrite lookup_insert_ne //. }
              + intros r; destruct (reg_eq_dec PC r); [subst r|].
                * rewrite !lookup_insert; inversion 1; simpl; auto.
                * rewrite !(lookup_insert_ne _ PC) //. destruct (reg_eq_dec dst r); [subst r|].
                  { rewrite !lookup_insert; inversion 1; simpl; auto. }
                  { rewrite !lookup_insert_ne //. auto. } }
    - (* Sub *)
      assert (match (lang.z_of_argument reg1 r1, lang.z_of_argument reg1 r2) with
              | (Some n1, Some n2) =>
                match incrementPC (<[dst:=inl ((n1 - n2)%Z)]> reg1) with
                | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inl ((n1 - n2)%Z)]> reg2) = Some reg2' /\ mem2' = mem2
                | None => c1 = lang.Failed /\ c2 = Failed
                end
              | (_, _) => c1 = lang.Failed /\ c2 = Failed
      end).
      { assert (Hregsome1: forall r, is_Some (reg1 !!r)).
        { intros. destruct (Hregsdef r) as [rw [-> _] ]. eauto. }
        destruct (lang.z_of_argument reg1 r1) as [n1|] eqn:Hr1.
        - destruct (lang.z_of_argument reg1 r2) as [n2|] eqn:Hr2.
          + eapply z_of_argument_inv_Some in Hr1.
            eapply z_of_argument_inv_Some in Hr2.
            assert (XX: lang.exec (Sub dst r1 r2) (reg1, h, stk, cs) = lang.updatePC (<[dst:=inl ((n1 - n2)%Z)]> reg1, h, stk, cs)).
            { rewrite /lang.exec /=. destruct Hr1 as [-> | [r1' [-> Hr1eq] ] ].
              - destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ].
                + reflexivity.
                + rewrite /base.RegLocate Hr2eq //.
              - rewrite /base.RegLocate Hr1eq.
                destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ]; [reflexivity| rewrite Hr2eq //]. }
            rewrite XX in H1; clear XX.
            assert (XX: exec (Sub dst r1 r2) (reg2, mem2) = updatePC (<[dst:=inl ((n1 - n2)%Z)]> reg2, mem2)).
            { rewrite /exec /=. destruct Hr1 as [-> | [r1' [-> Hr1eq] ] ].
              - destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ]; [reflexivity|].
                rewrite /RegLocate (Hsregs _ _ Hr2eq) //.
              - rewrite /RegLocate (Hsregs _ _ Hr1eq) /=.
                destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ]; [reflexivity|].
                rewrite (Hsregs _ _ Hr2eq) //. }
            rewrite XX in H2; clear XX.
            rewrite /base.update_reg /= in H1.
            assert (exists w, (<[dst:=inl ((n1 - n2)%Z)]> reg1) !! PC = Some w /\ (<[dst:=inl ((n1 - n2)%Z)]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
            { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert /=; eauto|].
              rewrite !lookup_insert_ne //.
              eexists; rewrite HPC; split; auto. }
            destruct (incrementPC (<[dst:=inl ((n1 - n2)%Z)]> reg1)) as [reg1''|] eqn:HX.
            * erewrite incrementPC_success_updatePC in H1; eauto.
              eapply incrementPC_success_incrementPC' in HX; eauto.
              destruct HX as [reg2'' HX].
              rewrite HX.
              eapply rules_base.incrementPC_success_updatePC in HX.
              destruct HX as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
              instantiate (1 := mem2) in Z3.
              rewrite Z3 -Z4 in H2. inv H1; inv H2; repeat split; auto.
            * erewrite incrementPC_fail_updatePC in H1; eauto.
              inv H1; split; auto.
              eapply incrementPC_fail_incrementPC' in HX; eauto.
              erewrite rules_base.incrementPC_fail_updatePC in H2; eauto.
              inv H2; auto.
          + simpl in H1, H2.
            eapply z_of_argument_inv_None in Hr2; eauto.
            destruct Hr2 as [r2' [cap2 [-> Hr2eq] ] ].
            rewrite /base.RegLocate Hr2eq in H1.
            destruct (translate_word_cap cap2) as [cap2' Hcap2'].
            generalize (Hsregs _ _ Hr2eq). rewrite Hcap2'; intros Hr2eq'.
            rewrite /RegLocate Hr2eq' in H2.
            destruct r1; [inv H1; inv H2; split; auto|].
            destruct (reg1 !! r) as [w1|]; destruct (reg2 !! r) as [w2|]; try (destruct w1); try (destruct w2); inv H1; inv H2; split; auto.
        - simpl in H1, H2.
          eapply z_of_argument_inv_None in Hr1; eauto.
          destruct Hr1 as [r1' [cap1 [-> Hr1eq] ] ].
          rewrite /base.RegLocate Hr1eq in H1.
          destruct (translate_word_cap cap1) as [cap1' Hcap1'].
          generalize (Hsregs _ _ Hr1eq). rewrite Hcap1'; intros Hr1eq'.
          rewrite /RegLocate Hr1eq' in H2.
          destruct r2; inv H1; inv H2; auto. }
      destruct (lang.z_of_argument reg1 r1) as [n1|] eqn:Hn1; cycle 1.
      + destruct H0 as [-> ->]. econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          simpl. repeat econstructor.
        * rewrite can_step_fill /can_step /=; intros [A | A]; discriminate.
      + destruct (lang.z_of_argument reg1 r2) as [n2|] eqn:Hn2; cycle 1.
        * destruct H0 as [-> ->]. econstructor.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            simpl. repeat econstructor. }
          { rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
        * destruct (incrementPC (<[dst:=inl ((n1 - n2)%Z)]> reg1)) as [reg1''|] eqn:Hincrement; cycle 1.
          { destruct H0 as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              simpl. repeat econstructor.
            - rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
          { destruct H0 as [-> [-> [-> [-> [-> [-> [Hincrement' ->] ] ] ] ] ] ].
            econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              simpl. repeat econstructor.
            - intros _. eapply incrementPC_inv_Some in Hincrement.
              destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in  Hincrement; elim Hincrement|].
              rewrite lookup_insert_ne // in Hincrement.
              rewrite HPC in Hincrement. destruct Hincrement as [ap1 [Hap1 [-> XX] ] ] .
              eapply rules_base.incrementPC_Some_inv in Hincrement'.
              rewrite lookup_insert_ne // in Hincrement'.
              rewrite (Hsregs _ _ HPC) /= in Hincrement'.
              destruct Hincrement' as [? [? [? [? [? [? [XXX [Hap1' [-> XY] ] ] ] ] ] ] ] ]; inv XXX.
              rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              + econstructor; eauto. intros.
                destruct (reg_eq_dec PC r).
                * subst r; rewrite lookup_insert. eexists; split; eauto.
                  simpl. simpl in HinterpPC. destruct H8 as [-> | [-> | ->] ]; auto.
                * rewrite lookup_insert_ne //. destruct (reg_eq_dec dst r).
                  { subst r; rewrite lookup_insert. eexists; split; eauto.
                    simpl; auto. }
                  { rewrite lookup_insert_ne //. }
              + intros r; destruct (reg_eq_dec PC r); [subst r|].
                * rewrite !lookup_insert; inversion 1; simpl; auto.
                * rewrite !(lookup_insert_ne _ PC) //. destruct (reg_eq_dec dst r); [subst r|].
                  { rewrite !lookup_insert; inversion 1; simpl; auto. }
                  { rewrite !lookup_insert_ne //. auto. } }
    - (* Lea *)
      assert (AA: match lang.z_of_argument reg1 r with
                  | None => c1 = lang.Failed /\ c2 = Failed
                  | Some n => match reg1 !! dst with
                              | Some (inr (Regular (pp, gg, bb, ee, aa))) =>
                                if perm_eq_dec pp E then c1 = lang.Failed /\ c2 = Failed else
                                match (aa + n)%a with
                                       | None => c1 = lang.Failed /\ c2 = Failed
                                       | Some aa' => if isU pp then if Addr_le_dec aa' aa then
                                                    match incrementPC (<[dst:=inr (Regular (pp, gg, bb, ee, aa'))]> reg1)
                                                    with Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inr (pp, gg, bb, ee, aa')]> reg2) = Some reg2' /\ mem2' = mem2
                                                    | _ => c1 = lang.Failed /\ c2 = Failed
                                                    end
                                                    else c1 = lang.Failed /\ c2 = Failed else
                                                    match incrementPC (<[dst:=inr (Regular (pp, gg, bb, ee, aa'))]> reg1)
                                                    with Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inr (pp, gg, bb, ee, aa')]> reg2) = Some reg2' /\ mem2' = mem2
                                                    | _ => c1 = lang.Failed /\ c2 = Failed
                                                    end
                                       end
                              | Some (inr (Stk dd pp bb ee aa)) =>
                                if perm_eq_dec pp E then c1 = lang.Failed /\ c2 = Failed else
                                match (aa + n)%a with
                                       | None => c1 = lang.Failed /\ c2 = Failed
                                       | Some aa' => if isU pp then if Addr_le_dec aa' aa then
                                                    match incrementPC (<[dst:=inr (Stk dd pp bb ee aa')]> reg1)
                                                    with Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inr (pp, Directed, bb, ee, aa')]> reg2) = Some reg2' /\ mem2' = mem2
                                                    | _ => c1 = lang.Failed /\ c2 = Failed
                                                    end
                                                    else c1 = lang.Failed /\ c2 = Failed else
                                                    match incrementPC (<[dst:=inr (Stk dd pp bb ee aa')]> reg1)
                                                    with Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inr (pp, Directed, bb, ee, aa')]> reg2) = Some reg2' /\ mem2' = mem2
                                                    | _ => c1 = lang.Failed /\ c2 = Failed
                                                    end
                                       end
                              | _ => c1 = lang.Failed /\ c2 = Failed
                              end
                  end).
      { destruct (Hregsdef dst) as [wdst [Hwdst _] ].
        generalize (Hsregs _ _ Hwdst). intros Hwdst'.
        destruct (lang.z_of_argument reg1 r) as [nn|] eqn:Harg1; cycle 1.
        - simpl in H1, H2. destruct r; simpl in Harg1; try congruence.
          destruct (Hregsdef r) as [wr [Hwr _] ].
          rewrite Hwr in Harg1. destruct wr; simpl in Harg1; try congruence.
          rewrite /base.RegLocate Hwdst Hwr in H1.
          generalize (Hsregs _ _ Hwr). intros Hwr'.
          destruct (translate_word_cap c) as [c' Hc']; rewrite Hc' in Hwr'.
          rewrite /RegLocate Hwdst' Hwr' /= in H2.
          destruct wdst; [simpl in H1, H2; inv H1; inv H2; auto|].
          destruct (translate_word_cap c0) as [c0' Hc0']; rewrite Hc0' in H2.
          destruct c0 as [ [ [ [ [? ?] ?] ?] ?] | ? | ?]; simpl in Hc0'; inv Hc0'.
          + destruct p0; inv H1; inv H2; auto.
          + destruct p0; inv H1; inv H2; auto.
          + inv H1; inv H2; auto.
        - rewrite Hwdst. destruct wdst.
          + simpl in H1, H2. rewrite /base.RegLocate Hwdst in H1.
            rewrite /RegLocate Hwdst' /= in H2.
            destruct r; inv H1; inv H2; auto.
          + rewrite /= /base.RegLocate Hwdst /= in H1.
            assert (X1: match c with | Regular c0 => let (p0, a) := c0 in let (p1, e) := p0 in let (p2, b) := p1 in let (p, g) := p2 in match p with | E => (lang.Failed, (reg1, h, stk, cs)) | URW | URWL | URWX | URWLX => match (a + nn)%a with | Some a' => if Addr_le_dec a' a then lang.updatePC (base.update_reg (reg1, h, stk, cs) dst (inr (Regular (p, g, b, e, a')))) else (lang.Failed, (reg1, h, stk, cs)) | None => (lang.Failed, (reg1, h, stk, cs)) end | _ => match (a + nn)%a with | Some a' => lang.updatePC (base.update_reg (reg1, h, stk, cs) dst (inr (Regular (p, g, b, e, a')))) | None => (lang.Failed, (reg1, h, stk, cs)) end end | Stk d p b e a => match p with | E => (lang.Failed, (reg1, h, stk, cs)) | URW | URWL | URWX | URWLX => match (a + nn)%a with | Some a' => if Addr_le_dec a' a then  lang.updatePC (base.update_reg (reg1, h, stk, cs) dst (inr (Stk d p b e a'))) else (lang.Failed, (reg1, h, stk, cs)) | None => (lang.Failed, (reg1, h, stk, cs)) end | _ => match (a + nn)%a with | Some a' => lang.updatePC (base.update_reg (reg1, h, stk, cs) dst (inr (Stk d p b e a'))) | None => (lang.Failed, (reg1, h, stk, cs)) end end | Ret _ _ _ => (lang.Failed, (reg1, h, stk, cs)) end = (c1, (reg1', h', stk', cs'))).
            { destruct r; simpl in Harg1.
              - inv Harg1; rewrite -H1. reflexivity.
              - destruct (Hregsdef r) as [wr [Hwr _] ].
                rewrite Hwr in Harg1. destruct wr; inv Harg1.
                rewrite Hwr in H1. auto. }
            clear H1. destruct (translate_word_cap c) as [c' Hc'].
            rewrite Hc' in Hwdst'. rewrite /= /RegLocate Hwdst' /= in H2.
            assert (X2: let (p0, a) := c' in let (p1, e) := p0 in let (p2, b) := p1 in let (p, g) := p2 in match p with | E => (Failed, (reg2, mem2)) | URW | URWL | URWX | URWLX => match (a + nn)%a with | Some a' => if Addr_le_dec a' a then updatePC (update_reg (reg2, mem2) dst (inr (p, g, b, e, a'))) else (Failed, (reg2, mem2)) | None => (Failed, (reg2, mem2)) end | _ => match (a + nn)%a with | Some a' => updatePC (update_reg (reg2, mem2) dst (inr (p, g, b, e, a'))) | None => (Failed, (reg2, mem2)) end end = (c2, (reg2', mem2'))).
            { destruct r; simpl in Harg1.
              - inv Harg1; rewrite -H2. destruct c' as [ [ [ [pp gg] bb] ee] aa].
                auto.
              - destruct (Hregsdef r) as [wr [Hwr _] ].
                rewrite Hwr in Harg1. destruct wr; inv Harg1.
                generalize (Hsregs _ _ Hwr). intros Hwr'.
                rewrite Hwr' /= in H2; auto. rewrite -H2.
                destruct c' as [ [ [ [pp gg] bb] ee] aa]; auto. }
            clear H2.
            destruct c; cycle 2.
            * destruct c' as [ [ [ [pp gg] bb] ee] aa].
              simpl in Hc'; inv Hc'. inv X1; inv X2; auto.
            * destruct c as [ [ [ [pp gg] bb] ee] aa].
              simpl in Hc'; inv Hc'. destruct (perm_eq_dec pp E).
              { subst pp. inv X1; inv X2; auto. }
              destruct (aa + nn)%a as [aa'|] eqn:Haa'; cycle 1.
              { destruct pp; inv X1; inv X2; auto. }
              destruct (isU pp) eqn:HisU.
              { destruct (Addr_le_dec aa' aa).
                - assert (exists w, (<[dst:=inr (Regular (pp, gg, bb, ee, aa'))]> reg1) !! PC = Some w /\ (<[dst:=inr (pp, gg, bb, ee, aa')]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
                  { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
                    rewrite !lookup_insert_ne //. eauto. }
                  destruct (incrementPC (<[dst:=inr (Regular (pp, gg, bb, ee, aa'))]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
                  + generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
                    intros Hincrement2. rewrite /base.update_reg /= in X1.
                    erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in X1.
                    rewrite /update_reg /= in X2.
                    erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in X2.
                    destruct pp; try congruence; inv X1; inv X2; auto.
                  + destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
                    rewrite /base.update_reg /= in X1. rewrite /update_reg /= in X2.
                    erewrite incrementPC_success_updatePC in X1; eauto.
                    rewrite Hincrement2.
                    eapply rules_base.incrementPC_success_updatePC in Hincrement2.
                    destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
                    instantiate (1 := mem2) in Z3.
                    rewrite Z3 -Z4 in X2. destruct pp; try congruence; inv X1; inv X2; repeat split; auto.
                - destruct pp; simpl in HisU; try congruence; inv X1; inv X2; auto. }
              assert (exists w, (<[dst:=inr (Regular (pp, gg, bb, ee, aa'))]> reg1) !! PC = Some w /\ (<[dst:=inr (pp, gg, bb, ee, aa')]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
              { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
                rewrite !lookup_insert_ne //. eauto. }
              rewrite /base.update_reg /= in X1. rewrite /update_reg /= in X2.
              destruct (incrementPC (<[dst:=inr (Regular (pp, gg, bb, ee, aa'))]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
              { generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
                intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in X1.
                erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in X2.
                destruct pp; simpl in HisU; try congruence; inv X1; inv X2; auto. }
              destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
              erewrite incrementPC_success_updatePC in X1; eauto.
              rewrite Hincrement2.
              eapply rules_base.incrementPC_success_updatePC in Hincrement2.
              destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
              instantiate (1 := mem2) in Z3.
              rewrite Z3 -Z4 in X2. destruct pp; simpl in HisU; try congruence; inv X1; inv X2; repeat split; auto.
            * simpl in Hc'; inv Hc'. destruct (perm_eq_dec p0 E).
              { subst p0. inv X1; inv X2; auto. }
              destruct (a2 + nn)%a as [aa'|] eqn:Haa'; cycle 1.
              { destruct p0; inv X1; inv X2; auto. }
              destruct (isU p0) eqn:HisU.
              { destruct (Addr_le_dec aa' a2).
                - assert (exists w, (<[dst:=inr (Stk n p0 a0 a1 aa')]> reg1) !! PC = Some w /\ (<[dst:=inr (p0, Directed, a0, a1, aa')]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
                  { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
                    rewrite !lookup_insert_ne //. eauto. }
                  destruct (incrementPC (<[dst:=inr (Stk n p0 a0 a1 aa')]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
                  + generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
                    intros Hincrement2. rewrite /base.update_reg /= in X1.
                    erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in X1.
                    rewrite /update_reg /= in X2.
                    erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in X2.
                    destruct p0; try congruence; inv X1; inv X2; auto.
                  + destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
                    rewrite /base.update_reg /= in X1. rewrite /update_reg /= in X2.
                    erewrite incrementPC_success_updatePC in X1; eauto.
                    rewrite Hincrement2.
                    eapply rules_base.incrementPC_success_updatePC in Hincrement2.
                    destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
                    instantiate (1 := mem2) in Z3.
                    rewrite Z3 -Z4 in X2. destruct p0; try congruence; inv X1; inv X2; repeat split; auto.
                - destruct p0; simpl in HisU; try congruence; inv X1; inv X2; auto. }
              assert (exists w, (<[dst:=inr (Stk n p0 a0 a1 aa')]> reg1) !! PC = Some w /\ (<[dst:=inr (p0, Directed, a0, a1, aa')]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
              { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
                rewrite !lookup_insert_ne //. eauto. }
              rewrite /base.update_reg /= in X1. rewrite /update_reg /= in X2.
              destruct (incrementPC (<[dst:=inr (Stk n p0 a0 a1 aa')]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
              { generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
                intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in X1.
                erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in X2.
                destruct p0; simpl in HisU; try congruence; inv X1; inv X2; auto. }
              destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
              erewrite incrementPC_success_updatePC in X1; eauto.
              rewrite Hincrement2.
              eapply rules_base.incrementPC_success_updatePC in Hincrement2.
              destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
              instantiate (1 := mem2) in Z3.
              rewrite Z3 -Z4 in X2. destruct p0; simpl in HisU; try congruence; inv X1; inv X2; repeat split; auto. }
      destruct (lang.z_of_argument reg1 r) as [nn|] eqn:Harg1; cycle 1.
      { destruct AA as [-> ->]. econstructor.
        - eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
      destruct (Hregsdef dst) as [wdst [Hwdst _] ].
      rewrite Hwdst in AA. destruct wdst.
      { destruct AA as [-> ->]. econstructor.
        - eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
      destruct c; cycle 2.
      { destruct AA as [-> ->]. econstructor.
        - eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
      + destruct c as [ [ [ [pp gg] bb] ee] aa].
        destruct (perm_eq_dec pp E); [subst pp|].
        { destruct AA as [-> ->]. econstructor.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (aa + nn)%a as [aa'|] eqn:Haa'; cycle 1.
        { destruct AA as [-> ->]. econstructor.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (incrementPC (<[dst:=inr (Regular (pp, gg, bb, ee, aa'))]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        { assert (c1 = lang.Failed ∧ c2 = Failed) as [-> ->] by (destruct (isU pp); destruct (Addr_le_dec aa' aa); auto).
          econstructor.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (isU pp) eqn:HisU; cycle 1.
        { destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          * intros _.
            eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|].
            { rewrite Hwdst in HPC; inv HPC. }
            { destruct (Hregsdef dst) as [wdst' [Hwdst' Hinterpdst] ].
              rewrite Hwdst in Hwdst'; inv Hwdst'.
              rewrite lookup_insert_ne in Hincrement1; auto.
              rewrite HPC in Hincrement1. destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite lookup_insert_ne in Hincrement2; auto.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              generalize (Hsregs _ _ HPC). intros HPC'.
              rewrite HPC' in HXX; inv HXX. rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              - econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|].
                + eexists; split; simpl; eauto.
                  destruct H8 as [-> | [-> | ->] ]; auto.
                + rewrite lookup_insert_ne //. destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert|].
                  * eexists; split; simpl; eauto.
                  * rewrite lookup_insert_ne //.
              - intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
                rewrite !(lookup_insert_ne _ PC); auto.
                destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
                rewrite !lookup_insert_ne; auto. } }
        destruct (Addr_le_dec aa' aa); cycle 1.
        { destruct AA as [-> ->]. econstructor.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        { destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          * intros _.
            eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|].
            { rewrite HPC in Hwdst; inv Hwdst. }
            { destruct (Hregsdef dst) as [wdst' [Hwdst' Hinterpdst] ].
              rewrite Hwdst in Hwdst'; inv Hwdst'.
              rewrite lookup_insert_ne in Hincrement1; auto.
              rewrite HPC in Hincrement1. destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite lookup_insert_ne in Hincrement2; auto.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              generalize (Hsregs _ _ HPC). intros HPC'.
              rewrite HPC' in HXX; inv HXX. rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              - econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|].
                + eexists; split; simpl; eauto.
                  destruct H8 as [-> | [-> | ->] ]; auto.
                + rewrite lookup_insert_ne //. destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert|].
                  * eexists; split; simpl; eauto.
                  * rewrite lookup_insert_ne //.
              - intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
                rewrite !(lookup_insert_ne _ PC); auto.
                destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
                rewrite !lookup_insert_ne; auto. } }
      + destruct (perm_eq_dec p0 E); [subst p0|].
        { destruct AA as [-> ->]. econstructor.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (a2 + nn)%a as [aa'|] eqn:Haa'; cycle 1.
        { destruct AA as [-> ->]. econstructor.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (incrementPC (<[dst:=inr (Stk n p0 a0 a1 aa')]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        { assert (c1 = lang.Failed ∧ c2 = Failed) as [-> ->] by (destruct (isU p0); destruct (Addr_le_dec aa' a2); auto).
          econstructor.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (isU p0) eqn:HisU; cycle 1.
        { destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          * intros _.
            eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|].
            { rewrite HPC in Hwdst; inv Hwdst.
              destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite insert_insert. rewrite lookup_insert in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              inv HXX. rewrite Hap1 in Hap1'. inv Hap1'.
              econstructor; eauto.
              - econstructor; eauto.
                intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
                eexists; split; auto.
                destruct H8 as [-> | [-> | ->] ]; auto.
              - rewrite insert_insert. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert|rewrite !lookup_insert_ne; auto].
                inversion 1; auto. }
            { destruct (Hregsdef dst) as [wdst' [Hwdst' Hinterpdst] ].
              rewrite Hwdst in Hwdst'; inv Hwdst'.
              rewrite lookup_insert_ne in Hincrement1; auto.
              rewrite HPC in Hincrement1. destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite lookup_insert_ne in Hincrement2; auto.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              generalize (Hsregs _ _ HPC). intros HPC'.
              rewrite HPC' in HXX; inv HXX. rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              - econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|].
                + eexists; split; simpl; eauto.
                  destruct H8 as [-> | [-> | ->] ]; auto.
                + rewrite lookup_insert_ne //. destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert|].
                  * eexists; split; simpl; eauto.
                    simpl in Hinterpdst. destruct Hinterpdst as [? [? [? ?] ] ].
                    do 3 (split; auto). simpl. intros; apply H6; auto.
                    destruct p0; simpl in HisU; try congruence; auto.
                  * rewrite lookup_insert_ne //.
              - intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
                rewrite !(lookup_insert_ne _ PC); auto.
                destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
                rewrite !lookup_insert_ne; auto. } }
        destruct (Addr_le_dec aa' a2); cycle 1.
        { destruct AA as [-> ->]. econstructor.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        { destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          * intros _.
            eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|].
            { rewrite HPC in Hwdst; inv Hwdst.
              destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              generalize (Hsregs _ _ HPC). intros HPC'.
              rewrite !insert_insert.
              rewrite lookup_insert in HXX; inv HXX.
              rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              - econstructor; eauto.
                intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
                eexists; split; auto.
                destruct H8 as [-> | [-> | ->] ]; auto.
              - intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert|rewrite !lookup_insert_ne; auto].
                inversion 1; auto. }
            { destruct (Hregsdef dst) as [wdst' [Hwdst' Hinterpdst] ].
              rewrite Hwdst in Hwdst'; inv Hwdst'.
              rewrite lookup_insert_ne in Hincrement1; auto.
              rewrite HPC in Hincrement1. destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite lookup_insert_ne in Hincrement2; auto.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              generalize (Hsregs _ _ HPC). intros HPC'.
              rewrite HPC' in HXX; inv HXX. rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              - econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|].
                + eexists; split; simpl; eauto.
                  destruct H8 as [-> | [-> | ->] ]; auto.
                + rewrite lookup_insert_ne //. destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert|].
                  * eexists; split; simpl; eauto.
                    destruct Hinterpdst as [? [? [? ?] ] ].
                    do 3 (split; auto). simpl; intros; eapply H6.
                    simpl. clear -HisU H7 l; destruct p0; try congruence; auto; solve_addr.
                  * rewrite lookup_insert_ne //.
              - intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
                rewrite !(lookup_insert_ne _ PC); auto.
                destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
                rewrite !lookup_insert_ne; auto. } }
    - (* Restrict *)
      assert (AA: match reg1 !! dst with
                  | Some (inr (Regular (pp, gg, bb, ee, aa))) =>
                    if perm_eq_dec pp E then c1 = lang.Failed /\ c2 = Failed else
                    match lang.z_of_argument reg1 r with
                    | Some nn => if PermPairFlowsTo (decodePermPair nn) (pp, gg) then
                      match incrementPC (<[dst:=inr (Regular ((decodePermPair nn), bb, ee, aa))]> reg1) with
                      | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inr ((decodePermPair nn), bb, ee, aa)]> reg2) = Some reg2' /\ mem2' = mem2
                      | None => c1 = lang.Failed /\ c2 = Failed
                      end
                    else c1 = lang.Failed /\ c2 = Failed
                    | None => c1 = lang.Failed /\ c2 = Failed
                    end
                  | Some (inr (Stk dd pp bb ee aa)) =>
                    if perm_eq_dec pp E then c1 = lang.Failed /\ c2 = Failed else
                    match lang.z_of_argument reg1 r with
                    | Some nn => if PermPairFlowsTo (decodePermPair nn) (pp, Directed) then
                      match incrementPC (<[dst:=inr (Stk dd (decodePermPair nn).1 bb ee aa)]> reg1) with
                      | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inr ((decodePermPair nn), bb, ee, aa)]> reg2) = Some reg2' /\ mem2' = mem2
                      | None => c1 = lang.Failed /\ c2 = Failed
                      end
                    else c1 = lang.Failed /\ c2 = Failed
                    | None => c1 = lang.Failed /\ c2 = Failed
                    end
                  | _ => c1 = lang.Failed /\ c2 = Failed
                  end).
      { destruct (Hregsdef dst) as [wdst [Hwdst _] ].
        rewrite Hwdst. generalize (Hsregs _ _ Hwdst). intros Hwdst'.
        destruct wdst; [simpl in H1, H2; rewrite /base.RegLocate Hwdst in H1; rewrite /RegLocate Hwdst' /= in H2; destruct r; inv H1; inv H2; auto|].
        destruct c; cycle 2.
        { simpl in H1, H2; rewrite /base.RegLocate Hwdst in H1; rewrite /RegLocate Hwdst' /= in H2.
          destruct r; inv H1; inv H2; auto. destruct (reg2 !! r); inv H1; auto.
          destruct s; inv H2; auto. }
        { destruct c as [ [ [ [pp gg] bb] ee] aa].
          destruct (perm_eq_dec pp E).
          - subst pp. simpl in H1, H2; rewrite /base.RegLocate Hwdst in H1; rewrite /RegLocate Hwdst' /= in H2.
            destruct r; [inv H1; inv H2; auto|].
            destruct (reg1 !! r); destruct (reg2 !! r); try (destruct s); try (destruct s0); inv H1; inv H2; auto.
          - destruct (lang.z_of_argument reg1 r) as [nn|] eqn:Hnn; cycle 1.
            + simpl in H1, H2; rewrite /base.RegLocate Hwdst in H1; rewrite /RegLocate Hwdst' /= in H2.
              destruct r; simpl in Hnn; [inv Hnn|].
              destruct (Hregsdef r) as [wr [Hwr _] ].
              rewrite Hwr in Hnn. destruct wr; inv Hnn.
              generalize (Hsregs _ _ Hwr). intros Hwr'.
              destruct (translate_word_cap c) as [c' Hc'].
              rewrite Hc' in Hwr'. rewrite Hwr in H1.
              rewrite Hwr' in H2. inv H1; inv H2; auto.
            + simpl in H1, H2; rewrite /base.RegLocate Hwdst in H1; rewrite /RegLocate Hwdst' /= in H2.
              assert ((if PermPairFlowsTo (decodePermPair nn) (pp, gg) then lang.updatePC (base.update_reg (reg1, h, stk, cs) dst (inr (Regular (decodePermPair nn, bb, ee, aa)))) else (lang.Failed, (reg1, h, stk, cs))) = (c1, (reg1', h', stk', cs')) /\ (if PermPairFlowsTo (decodePermPair nn) (pp, gg) then updatePC (update_reg (reg2, mem2) dst (inr (decodePermPair nn, bb, ee, aa))) else (Failed, (reg2, mem2))) = (c2, (reg2', mem2'))) as [X1 X2].
              { destruct r; [inv Hnn; destruct pp; try congruence; auto|].
                destruct (Hregsdef r) as [wr [Hwr _] ].
                rewrite /= Hwr in Hnn. destruct wr; inv Hnn.
                generalize (Hsregs _ _ Hwr); intro Hwr'.
                rewrite Hwr /= in H1. rewrite Hwr' /= in H2.
                destruct pp; try congruence; auto. }
              clear H1 H2.
              destruct (PermPairFlowsTo (decodePermPair nn) (pp, gg)) eqn:Hflowsto; cycle 1.
              * inv X1; inv X2; auto.
              * assert (exists w, (<[dst:=inr (Regular (decodePermPair nn, bb, ee, aa))]> reg1) !! PC = Some w /\ (<[dst:=inr ((decodePermPair nn, bb, ee, aa))]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
                { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
                  rewrite !lookup_insert_ne //. eauto. }
                rewrite /base.update_reg in X1.
                rewrite /update_reg in X2.
                destruct (incrementPC (<[dst:=inr (Regular (decodePermPair nn, bb, ee, aa))]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
                { generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
                  intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in X1.
                  erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in X2.
                  inv X1; inv X2; auto. }
                destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
                erewrite incrementPC_success_updatePC in X1; eauto.
                rewrite Hincrement2.
                eapply rules_base.incrementPC_success_updatePC in Hincrement2.
                destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
                instantiate (1 := mem2) in Z3.
                rewrite Z3 -Z4 in X2. inv X1; inv X2; repeat split; auto. }
        { destruct (perm_eq_dec p0 E).
          - subst p0. simpl in H1, H2; rewrite /base.RegLocate Hwdst in H1; rewrite /RegLocate Hwdst' /= in H2.
            destruct r; [inv H1; inv H2; auto|].
            destruct (reg1 !! r); destruct (reg2 !! r); try (destruct s); try (destruct s0); inv H1; inv H2; auto.
          - destruct (lang.z_of_argument reg1 r) as [nn|] eqn:Hnn; cycle 1.
            + simpl in H1, H2; rewrite /base.RegLocate Hwdst in H1; rewrite /RegLocate Hwdst' /= in H2.
              destruct r; simpl in Hnn; [inv Hnn|].
              destruct (Hregsdef r) as [wr [Hwr _] ].
              rewrite Hwr in Hnn. destruct wr; inv Hnn.
              generalize (Hsregs _ _ Hwr). intros Hwr'.
              destruct (translate_word_cap c) as [c' Hc'].
              rewrite Hc' in Hwr'. rewrite Hwr in H1.
              rewrite Hwr' in H2. inv H1; inv H2; auto.
            + simpl in H1, H2; rewrite /base.RegLocate Hwdst in H1; rewrite /RegLocate Hwdst' /= in H2.
              assert ((if PermPairFlowsTo (decodePermPair nn) (p0, Directed) then lang.updatePC (base.update_reg (reg1, h, stk, cs) dst (inr (Stk n (decodePermPair nn).1 a0 a1 a2))) else (lang.Failed, (reg1, h, stk, cs))) = (c1, (reg1', h', stk', cs')) /\ (if PermPairFlowsTo (decodePermPair nn) (p0, Directed) then updatePC (update_reg (reg2, mem2) dst (inr (decodePermPair nn, a0, a1, a2))) else (Failed, (reg2, mem2))) = (c2, (reg2', mem2'))) as [X1 X2].
              { destruct r; [inv Hnn; destruct p0; try congruence; auto|].
                destruct (Hregsdef r) as [wr [Hwr _] ].
                rewrite /= Hwr in Hnn. destruct wr; inv Hnn.
                generalize (Hsregs _ _ Hwr); intro Hwr'.
                rewrite Hwr /= in H1. rewrite Hwr' /= in H2.
                destruct p0; try congruence; auto. }
              clear H1 H2.
              destruct (PermPairFlowsTo (decodePermPair nn) (p0, Directed)) eqn:Hflowsto; cycle 1.
              * inv X1; inv X2; auto.
              * assert (decodePermPair nn = ((decodePermPair nn).1, Directed)) as XYZ.
                { rewrite /PermPairFlowsTo /= in Hflowsto.
                  destruct (decodePermPair nn) as [x y].
                  simpl; f_equal. simpl in Hflowsto.
                  eapply andb_true_iff in Hflowsto.
                  destruct Hflowsto as [? GG].
                  destruct y; simpl in GG; try congruence; auto. }
                assert (exists w, (<[dst:=inr (Stk n (decodePermPair nn).1 a0 a1 a2)]> reg1) !! PC = Some w /\ (<[dst:=inr ((decodePermPair nn, a0, a1, a2))]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
                { rewrite XYZ /=.
                  destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert /=; eexists; split; eauto; simpl|].
                  rewrite !lookup_insert_ne //. eauto. }
                rewrite /base.update_reg /= in X1.
                rewrite /update_reg /= in X2.
                destruct (incrementPC (<[dst:=inr (Stk n (decodePermPair nn).1 a0 a1 a2)]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
                { generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
                  intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in X1.
                  erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in X2.
                  inv X1; inv X2; auto. }
                destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
                erewrite incrementPC_success_updatePC in X1; eauto.
                rewrite Hincrement2.
                eapply rules_base.incrementPC_success_updatePC in Hincrement2.
                destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
                instantiate (1 := mem2) in Z3.
                rewrite Z3 -Z4 in X2. inv X1; inv X2; repeat split; auto. } }
      clear H1 H2. destruct (Hregsdef dst) as [wdst [Hwdst Hinterpdst] ].
      rewrite Hwdst in AA.
      destruct wdst.
      + destruct AA as [-> ->]. econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate.
      + destruct (translate_word_cap c) as [c' Hc'].
        generalize (Hsregs _ _ Hwdst). intro Hwdst'.
        destruct c; cycle 2.
        * destruct AA as [-> ->]. econstructor.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        * destruct c as [ [ [ [pp gg] bb] ee] aa].
          destruct (perm_eq_dec pp E).
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (lang.z_of_argument reg1 r) as [nn|] eqn:Harg1; cycle 1.
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (PermPairFlowsTo (decodePermPair nn) (pp, gg)) eqn:Hflowsto; cycle 1.
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (incrementPC (<[dst:=inr (Regular (decodePermPair nn, bb, ee, aa))]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          eapply incrementPC_inv_Some in Hincrement1.
          destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|].
          { destruct (decodePermPair nn) as [px gx].
            destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
            eapply rules_base.incrementPC_Some_inv in Hincrement2.
            destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
            rewrite lookup_insert in Z1. rewrite insert_insert in Z3. inv Z1.
            rewrite Hap1 in Z2; inv Z2.
            econstructor; eauto.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - intros _. econstructor; eauto.
              + rewrite insert_insert. econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|].
                * rewrite HPC in Hwdst; inv Hwdst.
                * rewrite lookup_insert_ne //.
              + rewrite insert_insert. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|].
                rewrite !lookup_insert_ne; auto. }
          { rewrite lookup_insert_ne in Hincrement1; auto.
            rewrite HPC in Hincrement1. destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
            eapply rules_base.incrementPC_Some_inv in Hincrement2.
            destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
            rewrite lookup_insert_ne in Z1; auto.
            generalize (Hsregs _ _ HPC). intros HPC'.
            rewrite HPC' in Z1; inv Z1.
            rewrite Hap1 in Z2; inv Z2.
            econstructor; eauto.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - intros _. econstructor; eauto.
              + econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
                * eexists; split; eauto.
                  destruct H8 as [-> | [-> | ->] ]; auto.
                * destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
                  eexists; split; eauto. simpl. simpl in Hinterpdst.
                  destruct (decodePermPair nn) as [px gx] eqn:Hpermpair.
                  destruct Hinterpdst. split; auto.
                  destruct pp; destruct px; simpl in H0; simpl in Hflowsto; try congruence; auto.
              + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto| rewrite !(lookup_insert_ne _ PC); auto].
                destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert; inversion 1; auto| rewrite !lookup_insert_ne; auto]. }
        * destruct (perm_eq_dec p0 E).
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (lang.z_of_argument reg1 r) as [nn|] eqn:Harg1; cycle 1.
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (PermPairFlowsTo (decodePermPair nn) (p0, Directed)) eqn:Hflowsto; cycle 1.
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (incrementPC (<[dst:=inr (Stk n (decodePermPair nn).1 a0 a1 a2)]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          eapply incrementPC_inv_Some in Hincrement1.
          destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|].
          { rewrite HPC in Hwdst; inv Hwdst.
            destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
            eapply rules_base.incrementPC_Some_inv in Hincrement2.
            destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
            rewrite lookup_insert in Z1. inv Z1.
            rewrite Hap1 in Z2; inv Z2.
            rewrite !insert_insert.
            econstructor; eauto.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - intros _. econstructor; eauto.
              + econstructor; eauto.
                intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
                eexists; split; auto.
                destruct (decodePermPair nn) as [px gx] eqn:Hpermpair.
                destruct HinterpPC as [? [? [? ?] ] ]. split; auto.
                split; auto. split; auto. simpl. intros; apply H5.
                rewrite /PermPairFlowsTo /= in Hflowsto.
                eapply andb_true_iff in Hflowsto; destruct Hflowsto.
                clear -H6 H7 H4 Hap1 H8; destruct px; destruct H8 as [-> | [-> | ->] ]; simpl in H7; simpl; try congruence; try solve_addr.
              + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert|rewrite !lookup_insert_ne; auto].
                inversion 1; simpl; auto. rewrite H1 /=.
                rewrite H1 /= in Hflowsto.
                eapply andb_true_iff in Hflowsto; destruct Hflowsto.
                simpl in H5. destruct g'; simpl in H5; try congruence. }
          { rewrite lookup_insert_ne in Hincrement1; auto.
            rewrite HPC in Hincrement1. destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
            eapply rules_base.incrementPC_Some_inv in Hincrement2.
            destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
            rewrite lookup_insert_ne in Z1; auto.
            generalize (Hsregs _ _ HPC). intros HPC'.
            rewrite HPC' in Z1; inv Z1.
            rewrite Hap1 in Z2; inv Z2.
            econstructor; eauto.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - intros _. econstructor; eauto.
              + econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
                * eexists; split; eauto.
                  destruct H8 as [-> | [-> | ->] ]; auto.
                * destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
                  eexists; split; eauto. simpl. simpl in Hinterpdst.
                  destruct (decodePermPair nn) as [px gx] eqn:Hpermpair.
                  destruct Hinterpdst as [? [? [? ?] ] ]. split; auto.
                  split; auto. split; auto. simpl. intros; apply H3.
                  rewrite /PermPairFlowsTo /= in Hflowsto.
                  eapply andb_true_iff in Hflowsto; destruct Hflowsto.
                  clear -H6 H5; destruct px; destruct p0; simpl in H6; try congruence; solve_addr.
              + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto| rewrite !(lookup_insert_ne _ PC); auto].
                destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert; inversion 1; auto| rewrite !lookup_insert_ne; auto].
                simpl. destruct (decodePermPair) as [px gx]; simpl; repeat f_equal.
                rewrite /PermPairFlowsTo /= in Hflowsto. apply andb_true_iff in Hflowsto.
                destruct Hflowsto. destruct gx; simpl in H3; try congruence; auto. }
    - (* Subseg *)
      assert (AA: match reg1 !! dst with
                  | Some (inr (Regular (pp, gg, bb, ee, aa))) =>
                    if perm_eq_dec pp E then c1 = lang.Failed /\ c2 = Failed
                    else match addr_of_argument' reg1 r1 with
                         | Some aa1 => match addr_of_argument' reg1 r2 with
                                       | Some aa2 =>
                                        if isWithin aa1 aa2 bb ee then
                                        match incrementPC (<[dst:=inr (Regular (pp, gg, aa1, aa2, aa))]> reg1) with
                                        | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inr (pp, gg, aa1, aa2, aa)]> reg2) = Some reg2' /\ mem2' = mem2
                                        | _ => c1 = lang.Failed /\ c2 = Failed
                                        end
                                        else c1 = lang.Failed /\ c2 = Failed
                                       | _ => c1 = lang.Failed /\ c2 = Failed
                                       end
                         | _ => c1 = lang.Failed /\ c2 = Failed
                         end
                  | Some (inr (Stk dd pp bb ee aa)) =>
                    if perm_eq_dec pp E then c1 = lang.Failed /\ c2 = Failed
                    else match addr_of_argument' reg1 r1 with
                         | Some aa1 => match addr_of_argument' reg1 r2 with
                                       | Some aa2 =>
                                        if isWithin aa1 aa2 bb ee then
                                        match incrementPC (<[dst:=inr (Stk dd pp aa1 aa2 aa)]> reg1) with
                                        | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inr (pp, Directed, aa1, aa2, aa)]> reg2) = Some reg2' /\ mem2' = mem2
                                        | _ => c1 = lang.Failed /\ c2 = Failed
                                        end
                                        else c1 = lang.Failed /\ c2 = Failed
                                       | _ => c1 = lang.Failed /\ c2 = Failed
                                       end
                         | _ => c1 = lang.Failed /\ c2 = Failed
                         end
                  | _ => c1 = lang.Failed /\ c2 = Failed
                  end).
      { destruct (Hregsdef dst) as [wdst [Hwdst _] ].
        rewrite Hwdst. generalize (Hsregs _ _ Hwdst). intros Hwdst'.
        rewrite /= /base.RegLocate Hwdst in H1.
        rewrite /= /RegLocate Hwdst' in H2.
        destruct wdst; [simpl in H1, H2; destruct r1; destruct r2; inv H1; inv H2; auto|].
        destruct (translate_word_cap c) as [c' Hc']. rewrite Hc' in H2.
        destruct (addr_of_argument' reg1 r1) as [aa1|] eqn:Haa1; cycle 1.
        - destruct r1; rewrite /addr_of_argument' /= in Haa1.
          + rewrite Haa1 in H1, H2.
            destruct c; [destruct c as [ [ [ [pp gg] bb] ee] aa]; inv Hc'; destruct r2; destruct (perm_eq_dec pp E); destruct pp; try (destruct (reg1 !! r)); try (destruct (reg2 !! r)); try (destruct s); try (destruct s0); inv H1; inv H2; auto| |inv Hc'; destruct r2; inv H1; inv H2; auto].
            inv Hc'. destruct (perm_eq_dec p0 E); destruct p0; destruct r2; try (destruct (reg1 !! r)); try (destruct (reg2 !! r)); try (destruct s); try (destruct s0); inv H1; inv H2; auto.
          + destruct (Hregsdef r) as [wr [Hwr _] ]; rewrite Hwr in Haa1.
            generalize (Hsregs _ _ Hwr). intros Hwr'.
            rewrite Hwr in H1. rewrite Hwr' in H2.
            destruct wr as [nn|cc]; [rewrite Haa1 in H1|destruct (translate_word_cap cc) as [cc' Hcc']; rewrite Hcc' in H2].
            * rewrite /= Haa1 in H2. destruct r2.
              { destruct c; [destruct c as [ [ [ [pp gg] bb] ee] aa]; inv Hc'; destruct (perm_eq_dec pp E); destruct pp; inv H1; inv H2; auto| |inv Hc'; inv H1; inv H2; auto].
                inv Hc'. destruct (perm_eq_dec p0 E); destruct p0; inv H1; inv H2; auto. }
              { destruct (Hregsdef r0) as [wr0 [Hwr0 _] ].
                generalize (Hsregs _ _ Hwr0). intros Hwr0'.
                rewrite Hwr0 in H1. rewrite Hwr0' in H2.
                destruct c; [destruct c as [ [ [ [pp gg] bb] ee] aa]; inv Hc'; destruct (perm_eq_dec pp E); destruct pp; try congruence; destruct wr0; try (destruct c); inv H1; inv H2; auto| |inv Hc'; inv H1; inv H2; auto].
                inv Hc'. destruct (perm_eq_dec p0 E); destruct p0; try congruence; destruct wr0; try (destruct c); inv H1; inv H2; auto. }
            * destruct c; [|inv Hc'; destruct (perm_eq_dec p0 E); destruct p0; destruct r2; inv H1; inv H2; auto|inv Hc'; destruct r2; inv H1; inv H2; auto].
              destruct c as [ [ [ [pp gg] bb] ee] aa]; inv Hc'.
              destruct (perm_eq_dec pp E); destruct pp; destruct r2; inv H1; inv H2; auto.
        - destruct (addr_of_argument' reg1 r2) as [aa2|] eqn:Haa2; cycle 1.
          + match goal with |- ?G => assert (XY: c1 = lang.Failed ∧ c2 = Failed -> G); [|apply XY; clear XY] end.
            { intro. destruct c; auto.
              destruct c as [ [ [ [pp gg] bb] ee] aa]; destruct (perm_eq_dec pp E); auto.
              destruct (perm_eq_dec p0 E); auto. }
            destruct r2; rewrite /addr_of_argument' /= in Haa2.
            * rewrite Haa2 in H1. rewrite Haa2 in H2.
              destruct r1; [rewrite /addr_of_argument' /= in Haa1; rewrite Haa1 in H1; rewrite Haa1 in H2|].
              { destruct c; [|inv Hc'; destruct p0; inv H1; inv H2; auto|inv Hc'; inv H1; inv H2; auto].
                destruct c as [ [ [ [pp gg] bb] ee] aa]; inv Hc'; destruct pp; inv H1; inv H2; auto. }
              { destruct (Hregsdef r) as [wr [Hwr _] ].
                rewrite /addr_of_argument' /= Hwr in Haa1.
                destruct wr as [nn1|]; [|inv Haa1].
                generalize (Hsregs _ _ Hwr); intros Hwr'.
                rewrite Hwr Haa1 in H1. rewrite Hwr' /= Haa1 in H2.
                destruct c; [|inv Hc'; destruct p0; inv H1; inv H2; auto|inv Hc'; inv H1; inv H2; auto].
                destruct c as [ [ [ [pp gg] bb] ee] aa]; inv Hc'; destruct pp; inv H1; inv H2; auto. }
            * destruct (Hregsdef r) as [wr [Hwr _] ].
              generalize (Hsregs _ _ Hwr). intros Hwr'.
              rewrite Hwr in Haa2. destruct wr as [nn2|]; cycle 1.
              { destruct (translate_word_cap c0) as [c0' Hc0'].
                rewrite Hc0' in Hwr'.
                rewrite Hwr /= in H1. rewrite Hwr' /= in H2.
                destruct r1.
                - destruct c; [|inv Hc'; destruct p0; inv H1; inv H2; auto|inv Hc'; inv H1; inv H2; auto].
                  destruct c as [ [ [ [pp gg] bb] ee] aa]; inv Hc'; destruct pp; inv H1; inv H2; auto.
                - destruct (Hregsdef r0) as [wr0 [Hwr0 _] ].
                  rewrite /addr_of_argument' /= Hwr0 in Haa1.
                  destruct wr0 as [nn1|]; [|inv Haa1].
                  generalize (Hsregs _ _ Hwr0). intros Hwr0'.
                  rewrite Hwr0 in H1. rewrite Hwr0' in H2.
                  destruct c; [|inv Hc'; destruct p0; inv H1; inv H2; auto|inv Hc'; inv H1; inv H2; auto].
                  destruct c as [ [ [ [pp gg] bb] ee] aa]; inv Hc'; destruct pp; inv H1; inv H2; auto. }
              { rewrite Hwr Haa2 in H1. rewrite Hwr' /= Haa2 in H2.
                destruct r1; rewrite /addr_of_argument' /= in Haa1; [rewrite Haa1 in H1; rewrite Haa1 in H2|].
                - destruct c; [|inv Hc'; destruct p0; inv H1; inv H2; auto|inv Hc'; inv H1; inv H2; auto].
                  destruct c as [ [ [ [pp gg] bb] ee] aa]; inv Hc'; destruct pp; inv H1; inv H2; auto.
                - destruct (Hregsdef r0) as [wr0 [Hwr0 _] ].
                  rewrite /addr_of_argument' /= Hwr0 in Haa1.
                  destruct wr0 as [nn1|]; [|inv Haa1].
                  generalize (Hsregs _ _ Hwr0). intros Hwr0'.
                  rewrite Hwr0 Haa1 in H1. rewrite Hwr0' /= Haa1 in H2.
                  destruct c; [|inv Hc'; destruct p0; inv H1; inv H2; auto|inv Hc'; inv H1; inv H2; auto].
                  destruct c as [ [ [ [pp gg] bb] ee] aa]; inv Hc'; destruct pp; inv H1; inv H2; auto. }
          + rewrite /base.update_reg /= in H1.
            rewrite /update_reg /= in H2.
            assert (match c with | Regular (pp, gg, bb, ee, aa) => if perm_eq_dec pp E then (lang.Failed, (reg1, h, stk, cs)) else if lang.isWithin aa1 aa2 bb ee then lang.updatePC (<[dst:=inr (Regular (pp, gg, aa1, aa2, aa))]> reg1, h, stk, cs) else (lang.Failed, (reg1, h, stk, cs)) | Stk dd pp bb ee aa => if perm_eq_dec pp E then (lang.Failed, (reg1, h, stk, cs)) else if lang.isWithin aa1 aa2 bb ee then lang.updatePC (<[dst:=inr (Stk dd pp aa1 aa2 aa)]> reg1, h, stk, cs) else (lang.Failed, (reg1, h, stk, cs)) | Ret _ _ _ => (lang.Failed, (reg1, h, stk, cs)) end = (c1, (reg1', h', stk', cs')) /\ match c' with (pp, gg, bb, ee, aa) => if perm_eq_dec pp E then (Failed, (reg2, mem2)) else if isWithin aa1 aa2 bb ee then updatePC (<[dst:=inr (pp, gg, aa1, aa2, aa)]> reg2, mem2) else (Failed, (reg2, mem2)) end = (c2, (reg2', mem2'))) as [X1 X2]; [|clear H1 H2].
            { destruct r1; destruct r2; rewrite /addr_of_argument' /= in Haa1, Haa2.
              - rewrite Haa1 in H1, H2. rewrite Haa2 in H1, H2.
                destruct c; [|inv Hc'; destruct p0; inv H1; inv H2; auto|inv Hc'; inv H1; inv H2; auto].
                destruct c as [ [ [ [pp gg] bb] ee] aa]; inv Hc'; destruct pp; inv H1; inv H2; auto.
              - destruct (Hregsdef r) as [wr [Hwr _] ].
                generalize (Hsregs _ _ Hwr). intros Hwr'.
                rewrite Hwr in Haa2. destruct wr; [|inv Haa2].
                rewrite Hwr Haa1 Haa2 in H1. rewrite Hwr' /= Haa1 Haa2 in H2.
                destruct c; [|inv Hc'; destruct p0; inv H1; inv H2; auto|inv Hc'; inv H1; inv H2; auto].
                destruct c as [ [ [ [pp gg] bb] ee] aa]; inv Hc'; destruct pp; inv H1; inv H2; auto.
              - destruct (Hregsdef r) as [wr [Hwr _] ].
                generalize (Hsregs _ _ Hwr). intros Hwr'.
                rewrite Hwr in Haa1. destruct wr; [|inv Haa1].
                rewrite Hwr Haa1 Haa2 in H1. rewrite Hwr' /= Haa1 Haa2 in H2.
                destruct c; [|inv Hc'; destruct p0; inv H1; inv H2; auto|inv Hc'; inv H1; inv H2; auto].
                destruct c as [ [ [ [pp gg] bb] ee] aa]; inv Hc'; destruct pp; inv H1; inv H2; auto.
              - destruct (Hregsdef r) as [wr [Hwr _] ].
                generalize (Hsregs _ _ Hwr). intros Hwr'.
                rewrite Hwr in Haa1. destruct wr; [|inv Haa1].
                destruct (Hregsdef r0) as [wr0 [Hwr0 _] ].
                generalize (Hsregs _ _ Hwr0). intros Hwr0'.
                rewrite Hwr0 in Haa2. destruct wr0; [|inv Haa2].
                rewrite Hwr Hwr0 Haa1 Haa2 in H1. rewrite Hwr' Hwr0' /= Haa1 Haa2 in H2.
                destruct c; [|inv Hc'; destruct p0; inv H1; inv H2; auto|inv Hc'; inv H1; inv H2; auto].
                destruct c as [ [ [ [pp gg] bb] ee] aa]; inv Hc'; destruct pp; inv H1; inv H2; auto. }
            destruct c; [|inv Hc'|inv Hc'; inv X1; inv X2; auto].
            * destruct c as [ [ [ [pp gg] bb] ee] aa]; inv Hc'; destruct (perm_eq_dec pp E); [inv X1; inv X2; auto|].
              replace lang.isWithin with isWithin in X1 by reflexivity.
              destruct (isWithin aa1 aa2 bb ee) eqn:HisWithin; [|inv X1; inv X2; auto].
              assert (exists w, (<[dst:=inr (Regular (pp, gg, aa1, aa2, aa))]> reg1) !! PC = Some w /\ (<[dst:=inr (pp, gg, aa1, aa2, aa)]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
              { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
                rewrite !lookup_insert_ne //. eauto. }
              destruct (incrementPC (<[dst:=inr (Regular (pp, gg, aa1, aa2, aa))]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
              { generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
                intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in X1.
                erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in X2.
                inv X1; inv X2; auto. }
              { destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
                erewrite incrementPC_success_updatePC in X1; eauto.
                rewrite Hincrement2.
                eapply rules_base.incrementPC_success_updatePC in Hincrement2.
                destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
                instantiate (1 := mem2) in Z3.
                rewrite Z3 -Z4 in X2. inv X1; inv X2; repeat split; auto. }
            * destruct (perm_eq_dec p0 E); [inv X1; inv X2; auto|].
              replace lang.isWithin with isWithin in X1 by reflexivity.
              destruct (isWithin aa1 aa2 a0 a1) eqn:HisWithin; [|inv X1; inv X2; auto].
              assert (exists w, (<[dst:=inr (Stk n p0 aa1 aa2 a2)]> reg1) !! PC = Some w /\ (<[dst:=inr (p0, Directed, aa1, aa2, a2)]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
              { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
                rewrite !lookup_insert_ne //. eauto. }
              destruct (incrementPC (<[dst:=inr (Stk n p0 aa1 aa2 a2)]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
              { generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
                intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in X1.
                erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in X2.
                inv X1; inv X2; auto. }
              { destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
                erewrite incrementPC_success_updatePC in X1; eauto.
                rewrite Hincrement2.
                eapply rules_base.incrementPC_success_updatePC in Hincrement2.
                destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
                instantiate (1 := mem2) in Z3.
                rewrite Z3 -Z4 in X2. inv X1; inv X2; repeat split; auto. } }
      destruct (Hregsdef dst) as [wdst [Hwdst Hinterpdst] ].
      rewrite Hwdst in AA. destruct wdst as [|cdst].
      + destruct AA as [-> ->]. econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate.
      + destruct cdst; cycle 2.
        * destruct AA as [-> ->]. econstructor.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        * generalize (Hsregs _ _ Hwdst). intros Hwdst'.
          destruct c as [ [ [ [pp gg] bb] ee] aa].
          destruct (perm_eq_dec pp E).
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (addr_of_argument' reg1 r1) as [aa1|] eqn:Haa1; cycle 1.
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (addr_of_argument' reg1 r2) as [aa2|] eqn:Haa2; cycle 1.
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (isWithin aa1 aa2 bb ee) eqn:HisWithin; cycle 1.
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (incrementPC (<[dst:=inr (Regular (pp, gg, aa1, aa2, aa))]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          generalize (Hsregs _ _ HPC); intros HPC'.
          econstructor; eauto.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { intros _.
            eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|rewrite lookup_insert_ne in Hincrement1; auto].
            - rewrite HPC in Hwdst; inv Hwdst.
            - rewrite HPC in Hincrement1. destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite lookup_insert_ne in Hincrement2; auto.
              destruct Hincrement2 as [? [? [? [? [? [aa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              rewrite HPC' in HXX; inv HXX.
              rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              + econstructor; eauto.
                intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert| rewrite lookup_insert_ne; auto].
                * eexists; split; eauto.
                  destruct H8 as [-> | [-> | ->] ]; auto.
                * destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne;auto].
                  eexists; split; eauto.
                  destruct Hinterpdst as [QQ WW].
                  split; auto. red; intros. apply WW.
                  apply andb_true_iff in HisWithin.
                  clear -HisWithin H0. destruct HisWithin.
                  apply leb_addr_spec in H. apply leb_addr_spec in H1.
                  solve_addr.
              + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert| rewrite !(lookup_insert_ne _ PC); auto].
                * inversion 1; auto.
                * destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert|rewrite !(lookup_insert_ne _ dst); auto].
                  inversion 1; auto. }
        * destruct (perm_eq_dec p0 E).
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (addr_of_argument' reg1 r1) as [aa1|] eqn:Haa1; cycle 1.
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (addr_of_argument' reg1 r2) as [aa2|] eqn:Haa2; cycle 1.
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (isWithin aa1 aa2 a0 a1) eqn:HisWithin; cycle 1.
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (incrementPC (<[dst:=inr (Stk n p0 aa1 aa2 a2)]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
          { destruct AA as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          generalize (Hsregs _ _ HPC); intros HPC'.
          econstructor; eauto.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { intros _.
            eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|rewrite lookup_insert_ne in Hincrement1; auto].
            - rewrite HPC in Hwdst; inv Hwdst.
              destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              destruct Hincrement2 as [? [? [? [? [? [aa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              rewrite !insert_insert.
              rewrite lookup_insert in HXX; inv HXX.
              rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              + econstructor; eauto.
                intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
                eexists; split; auto.
                simpl; simpl in HinterpPC.
                destruct HinterpPC as [? [? [? ?] ] ].
                split; auto. apply andb_true_iff in HisWithin.
                destruct HisWithin as [GG1 GG2]. apply leb_addr_spec in GG1.
                apply leb_addr_spec in GG2.
                split; [clear -GG2 H3; solve_addr|].
                split; [intros d' stk' QQ1 a' QQ2; eapply H5 in QQ2; eauto; clear -QQ2 GG1; solve_addr|].
                intros. apply H6.
                clear -H7 GG1 GG2 H8; destruct H8 as [-> | [-> | ->] ]; solve_addr.
              + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto| rewrite !lookup_insert_ne; auto].
            - rewrite HPC in Hincrement1. destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite lookup_insert_ne in Hincrement2; auto.
              destruct Hincrement2 as [? [? [? [? [? [aa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              rewrite HPC' in HXX; inv HXX.
              rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              + econstructor; eauto.
                intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert| rewrite lookup_insert_ne; auto].
                * eexists; split; eauto.
                  destruct H8 as [-> | [-> | ->] ]; auto.
                * destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne;auto].
                  eexists; split; eauto.
                  destruct Hinterpdst as [QQ [WW [TT ZZ] ] ].
                  split; auto. apply andb_true_iff in HisWithin.
                  destruct HisWithin. apply leb_addr_spec in H0.
                  apply leb_addr_spec in H3.
                  split; [clear -H3 WW; solve_addr|].
                  split; auto.
                  { intros. eapply TT in H6; eauto.
                    clear -H0 H6; solve_addr. }
                  { intros. apply ZZ.
                    assert ((addr_reg.min aa2 (lang.canReadUpTo (inr (Stk n p0 aa1 aa2 a2))) <= addr_reg.min a1 (lang.canReadUpTo (inr (Stk n p0 a0 a1 a2))))%a).
                    { clear -H3. destruct p0; simpl; solve_addr. }
                    clear -H5 H0 H6. solve_addr. }
              + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert| rewrite !(lookup_insert_ne _ PC); auto].
                * inversion 1; auto.
                * destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert|rewrite !(lookup_insert_ne _ dst); auto].
                  inversion 1; auto. }
    - (* IsPtr *)
      assert (AA: exists n, match incrementPC (<[dst:=inl n]> reg1) with
                              | Some reg1'' =>
                                c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inl n]> reg2) = Some reg2' /\ mem2' = mem2
                              | _ => c1 = lang.Failed /\ c2 = Failed
                              end).
      { simpl in H1, H2. destruct (Hregsdef r) as [wr [Hwr _] ].
        rewrite /base.RegLocate Hwr in H1.
        rewrite /RegLocate (Hsregs _ _ Hwr) in H2.
        set (nn := match wr with inl _ => 0%Z | inr _ => 1%Z end).
        exists nn. assert (X1: lang.updatePC (<[dst:=inl nn]> reg1, h, stk, cs) = (c1, (reg1', h', stk', cs'))) by (destruct wr; auto).
        assert (X2: updatePC (<[dst:=inl nn]> reg2, mem2) = (c2, (reg2', mem2'))) by (destruct wr; auto; destruct (translate_word_cap c) as [c' Hc']; rewrite Hc' in H2; auto).
        clear H1 H2. assert (exists w, (<[dst:=inl nn]> reg1) !! PC = Some w /\ (<[dst:=inl nn]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
        { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
          rewrite !lookup_insert_ne //. eauto. }
        destruct (incrementPC (<[dst:=inl nn]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        - generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
          intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in X1.
          erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in X2.
          inv X1; inv X2; auto.
        - destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
          erewrite incrementPC_success_updatePC in X1; eauto.
          rewrite Hincrement2.
          eapply rules_base.incrementPC_success_updatePC in Hincrement2.
          destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
          instantiate (1 := mem2) in Z3.
          rewrite Z3 -Z4 in X2. inv X1; inv X2; repeat split; auto. }
      destruct AA as [nn AA]. destruct (incrementPC (<[dst:=inl nn]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        + destruct AA as [-> ->]. econstructor.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate.
        + destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          * intros _.
            eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1; elim Hincrement1|].
            rewrite lookup_insert_ne // HPC in Hincrement1.
            destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
            eapply rules_base.incrementPC_Some_inv in Hincrement2.
            destruct Hincrement2 as [pp [gg [bb [ee [aa [aa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
            rewrite lookup_insert_ne // in HXX.
            rewrite (Hsregs _ _ HPC) /= in HXX. inv HXX.
            rewrite Hap1 in Hap1'; inv Hap1'.
            econstructor; eauto.
            { econstructor; eauto. intros rr.
              destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|].
              - eexists; split; simpl; eauto.
                destruct H8 as [-> | [-> | ->] ]; auto.
              - rewrite lookup_insert_ne //.
                destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert; eexists; split; eauto; simpl; auto|].
                rewrite lookup_insert_ne //; auto. }
            { intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
              rewrite !(lookup_insert_ne _ PC) //.
              eapply (@Hsregs_preserve_word_of_arg reg1 reg2 dst (inl nn)); auto. }
    - (* GetL *)
      assert (AA: match reg1 !! r with
                  | Some (inr _) =>
                    exists n, match incrementPC (<[dst:=inl n]> reg1) with
                              | Some reg1'' =>
                                c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inl n]> reg2) = Some reg2' /\ mem2' = mem2
                              | _ => c1 = lang.Failed /\ c2 = Failed
                              end
                  | _ => c1 = lang.Failed /\ c2 = Failed
                  end).
      { simpl in H1, H2. destruct (Hregsdef r) as [wr [Hwr _] ].
        rewrite Hwr. rewrite /base.RegLocate Hwr in H1.
        rewrite /RegLocate (Hsregs _ _ Hwr) in H2.
        destruct wr; [inv H1; inv H2; auto|].
        destruct (translate_word_cap c) as [c' Hc'].
        rewrite Hc' in H2. set (nn := match c with Ret _ _ _ | Stk _ _ _ _ _ => encodeLoc Directed | Regular (_, l, _, _, _) => encodeLoc l end).
        exists nn. assert (X1: lang.updatePC (<[dst:=inl nn]> reg1, h, stk, cs) = (c1, (reg1', h', stk', cs'))).
        { rewrite -H1 /base.update_reg /=.
          subst nn; destruct c; auto.
          destruct c as [ [ [ [pp gg] bb] ee] aa]; auto. }
        clear H1. assert (X2: updatePC (<[dst:=inl nn]> reg2, mem2) = (c2, (reg2', mem2'))).
        { rewrite -H2 /update_reg /=.
          subst nn. destruct c; inv Hc'; auto.
          destruct c' as [ [ [ [pp gg] bb] ee] aa]; auto. }
        clear H2. assert (exists w, (<[dst:=inl nn]> reg1) !! PC = Some w /\ (<[dst:=inl nn]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
        { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
          rewrite !lookup_insert_ne //. eauto. }
        destruct (incrementPC (<[dst:=inl nn]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        - generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
          intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in X1.
          erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in X2.
          inv X1; inv X2; auto.
        - destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
          erewrite incrementPC_success_updatePC in X1; eauto.
          rewrite Hincrement2.
          eapply rules_base.incrementPC_success_updatePC in Hincrement2.
          destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
          instantiate (1 := mem2) in Z3.
          rewrite Z3 -Z4 in X2. inv X1; inv X2; repeat split; auto. }
      destruct (Hregsdef r) as [wr [Hwr Hinterpwr] ].
      rewrite Hwr in AA. destruct wr as [nr|cr].
      + destruct AA as [-> ->]. econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate.
      + destruct AA as [nn AA]. destruct (incrementPC (<[dst:=inl nn]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        * destruct AA as [-> ->]. econstructor.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        * destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { intros _.
            eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1; elim Hincrement1|].
            rewrite lookup_insert_ne // HPC in Hincrement1.
            destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
            eapply rules_base.incrementPC_Some_inv in Hincrement2.
            destruct Hincrement2 as [pp [gg [bb [ee [aa [aa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
            rewrite lookup_insert_ne // in HXX.
            rewrite (Hsregs _ _ HPC) /= in HXX. inv HXX.
            rewrite Hap1 in Hap1'; inv Hap1'.
            econstructor; eauto.
            + econstructor; eauto. intros rr.
              destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|].
              * eexists; split; simpl; eauto.
                destruct H8 as [-> | [-> | ->] ]; auto.
              * rewrite lookup_insert_ne //.
                destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert; eexists; split; eauto; simpl; auto|].
                rewrite lookup_insert_ne //; auto.
            + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
              rewrite !(lookup_insert_ne _ PC) //.
              eapply (@Hsregs_preserve_word_of_arg reg1 reg2 dst (inl nn)); auto. }
    - (* GetP *)
      assert (AA: match reg1 !! r with
                  | Some (inr _) =>
                    exists n, match incrementPC (<[dst:=inl n]> reg1) with
                              | Some reg1'' =>
                                c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inl n]> reg2) = Some reg2' /\ mem2' = mem2
                              | _ => c1 = lang.Failed /\ c2 = Failed
                              end
                  | _ => c1 = lang.Failed /\ c2 = Failed
                  end).
      { simpl in H1, H2. destruct (Hregsdef r) as [wr [Hwr _] ].
        rewrite Hwr. rewrite /base.RegLocate Hwr in H1.
        rewrite /RegLocate (Hsregs _ _ Hwr) in H2.
        destruct wr; [inv H1; inv H2; auto|].
        destruct (translate_word_cap c) as [c' Hc'].
        rewrite Hc' in H2. set (nn := match c with Ret _ _ _ => encodePerm E | Stk _ p _ _ _ | Regular (p, _, _, _, _) => encodePerm p end).
        exists nn. assert (X1: lang.updatePC (<[dst:=inl nn]> reg1, h, stk, cs) = (c1, (reg1', h', stk', cs'))).
        { rewrite -H1 /base.update_reg /=.
          subst nn; destruct c; auto.
          destruct c as [ [ [ [pp gg] bb] ee] aa]; auto. }
        clear H1. assert (X2: updatePC (<[dst:=inl nn]> reg2, mem2) = (c2, (reg2', mem2'))).
        { rewrite -H2 /update_reg /=.
          subst nn. destruct c; inv Hc'; auto.
          destruct c' as [ [ [ [pp gg] bb] ee] aa]; auto. }
        clear H2. assert (exists w, (<[dst:=inl nn]> reg1) !! PC = Some w /\ (<[dst:=inl nn]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
        { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
          rewrite !lookup_insert_ne //. eauto. }
        destruct (incrementPC (<[dst:=inl nn]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        - generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
          intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in X1.
          erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in X2.
          inv X1; inv X2; auto.
        - destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
          erewrite incrementPC_success_updatePC in X1; eauto.
          rewrite Hincrement2.
          eapply rules_base.incrementPC_success_updatePC in Hincrement2.
          destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
          instantiate (1 := mem2) in Z3.
          rewrite Z3 -Z4 in X2. inv X1; inv X2; repeat split; auto. }
      destruct (Hregsdef r) as [wr [Hwr Hinterpwr] ].
      rewrite Hwr in AA. destruct wr as [nr|cr].
      + destruct AA as [-> ->]. econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate.
      + destruct AA as [nn AA]. destruct (incrementPC (<[dst:=inl nn]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        * destruct AA as [-> ->]. econstructor.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        * destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { intros _.
            eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1; elim Hincrement1|].
            rewrite lookup_insert_ne // HPC in Hincrement1.
            destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
            eapply rules_base.incrementPC_Some_inv in Hincrement2.
            destruct Hincrement2 as [pp [gg [bb [ee [aa [aa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
            rewrite lookup_insert_ne // in HXX.
            rewrite (Hsregs _ _ HPC) /= in HXX. inv HXX.
            rewrite Hap1 in Hap1'; inv Hap1'.
            econstructor; eauto.
            + econstructor; eauto. intros rr.
              destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|].
              * eexists; split; simpl; eauto.
                destruct H8 as [-> | [-> | ->] ]; auto.
              * rewrite lookup_insert_ne //.
                destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert; eexists; split; eauto; simpl; auto|].
                rewrite lookup_insert_ne //; auto.
            + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
              rewrite !(lookup_insert_ne _ PC) //.
              eapply (@Hsregs_preserve_word_of_arg reg1 reg2 dst (inl nn)); auto. }
    - (* GetB *)
      assert (AA: match reg1 !! r with
                  | Some (inr _) =>
                    exists n, match incrementPC (<[dst:=inl n]> reg1) with
                              | Some reg1'' =>
                                c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inl n]> reg2) = Some reg2' /\ mem2' = mem2
                              | _ => c1 = lang.Failed /\ c2 = Failed
                              end
                  | _ => c1 = lang.Failed /\ c2 = Failed
                  end).
      { simpl in H1, H2. destruct (Hregsdef r) as [wr [Hwr _] ].
        rewrite Hwr. rewrite /base.RegLocate Hwr in H1.
        rewrite /RegLocate (Hsregs _ _ Hwr) in H2.
        destruct wr; [inv H1; inv H2; auto|].
        destruct (translate_word_cap c) as [c' Hc'].
        rewrite Hc' in H2. set (nn := match c with Ret b _ _ | Stk _ _ b _ _ | Regular (_, _, b, _, _) => z_of b end).
        exists nn. assert (X1: lang.updatePC (<[dst:=inl nn]> reg1, h, stk, cs) = (c1, (reg1', h', stk', cs'))).
        { rewrite -H1 /base.update_reg /=.
          subst nn; destruct c; auto; [| destruct a0; auto..].
          destruct c as [ [ [ [pp gg] bb] ee] aa]; auto.
          destruct bb; auto. }
        clear H1. assert (X2: updatePC (<[dst:=inl nn]> reg2, mem2) = (c2, (reg2', mem2'))).
        { rewrite -H2 /update_reg /=.
          subst nn. destruct c; inv Hc'; auto; [| destruct a0; auto..].
          destruct c' as [ [ [ [pp gg] bb] ee] aa]; auto.
          destruct bb; auto. }
        clear H2. assert (exists w, (<[dst:=inl nn]> reg1) !! PC = Some w /\ (<[dst:=inl nn]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
        { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
          rewrite !lookup_insert_ne //. eauto. }
        destruct (incrementPC (<[dst:=inl nn]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        - generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
          intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in X1.
          erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in X2.
          inv X1; inv X2; auto.
        - destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
          erewrite incrementPC_success_updatePC in X1; eauto.
          rewrite Hincrement2.
          eapply rules_base.incrementPC_success_updatePC in Hincrement2.
          destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
          instantiate (1 := mem2) in Z3.
          rewrite Z3 -Z4 in X2. inv X1; inv X2; repeat split; auto. }
      destruct (Hregsdef r) as [wr [Hwr Hinterpwr] ].
      rewrite Hwr in AA. destruct wr as [nr|cr].
      + destruct AA as [-> ->]. econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate.
      + destruct AA as [nn AA]. destruct (incrementPC (<[dst:=inl nn]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        * destruct AA as [-> ->]. econstructor.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        * destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { intros _.
            eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1; elim Hincrement1|].
            rewrite lookup_insert_ne // HPC in Hincrement1.
            destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
            eapply rules_base.incrementPC_Some_inv in Hincrement2.
            destruct Hincrement2 as [pp [gg [bb [ee [aa [aa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
            rewrite lookup_insert_ne // in HXX.
            rewrite (Hsregs _ _ HPC) /= in HXX. inv HXX.
            rewrite Hap1 in Hap1'; inv Hap1'.
            econstructor; eauto.
            + econstructor; eauto. intros rr.
              destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|].
              * eexists; split; simpl; eauto.
                destruct H8 as [-> | [-> | ->] ]; auto.
              * rewrite lookup_insert_ne //.
                destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert; eexists; split; eauto; simpl; auto|].
                rewrite lookup_insert_ne //; auto.
            + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
              rewrite !(lookup_insert_ne _ PC) //.
              eapply (@Hsregs_preserve_word_of_arg reg1 reg2 dst (inl nn)); auto. }
    - (* GetE *)
      assert (AA: match reg1 !! r with
                  | Some (inr _) =>
                    exists n, match incrementPC (<[dst:=inl n]> reg1) with
                              | Some reg1'' =>
                                c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inl n]> reg2) = Some reg2' /\ mem2' = mem2
                              | _ => c1 = lang.Failed /\ c2 = Failed
                              end
                  | _ => c1 = lang.Failed /\ c2 = Failed
                  end).
      { simpl in H1, H2. destruct (Hregsdef r) as [wr [Hwr _] ].
        rewrite Hwr. rewrite /base.RegLocate Hwr in H1.
        rewrite /RegLocate (Hsregs _ _ Hwr) in H2.
        destruct wr; [inv H1; inv H2; auto|].
        destruct (translate_word_cap c) as [c' Hc'].
        rewrite Hc' in H2. set (nn := match c with Ret _ e _ | Stk _ _ _ e _ | Regular (_, _, _, e, _) => z_of e end).
        exists nn. assert (X1: lang.updatePC (<[dst:=inl nn]> reg1, h, stk, cs) = (c1, (reg1', h', stk', cs'))).
        { rewrite -H1 /base.update_reg /=.
          subst nn; destruct c; auto; [| destruct a1; auto..].
          destruct c as [ [ [ [pp gg] bb] ee] aa]; auto.
          destruct ee; auto. }
        clear H1. assert (X2: updatePC (<[dst:=inl nn]> reg2, mem2) = (c2, (reg2', mem2'))).
        { rewrite -H2 /update_reg /=.
          subst nn. destruct c; inv Hc'; auto; [| destruct a1; auto..].
          destruct c' as [ [ [ [pp gg] bb] ee] aa]; auto.
          destruct ee; auto. }
        clear H2. assert (exists w, (<[dst:=inl nn]> reg1) !! PC = Some w /\ (<[dst:=inl nn]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
        { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
          rewrite !lookup_insert_ne //. eauto. }
        destruct (incrementPC (<[dst:=inl nn]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        - generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
          intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in X1.
          erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in X2.
          inv X1; inv X2; auto.
        - destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
          erewrite incrementPC_success_updatePC in X1; eauto.
          rewrite Hincrement2.
          eapply rules_base.incrementPC_success_updatePC in Hincrement2.
          destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
          instantiate (1 := mem2) in Z3.
          rewrite Z3 -Z4 in X2. inv X1; inv X2; repeat split; auto. }
      destruct (Hregsdef r) as [wr [Hwr Hinterpwr] ].
      rewrite Hwr in AA. destruct wr as [nr|cr].
      + destruct AA as [-> ->]. econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate.
      + destruct AA as [nn AA]. destruct (incrementPC (<[dst:=inl nn]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        * destruct AA as [-> ->]. econstructor.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        * destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { intros _.
            eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1; elim Hincrement1|].
            rewrite lookup_insert_ne // HPC in Hincrement1.
            destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
            eapply rules_base.incrementPC_Some_inv in Hincrement2.
            destruct Hincrement2 as [pp [gg [bb [ee [aa [aa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
            rewrite lookup_insert_ne // in HXX.
            rewrite (Hsregs _ _ HPC) /= in HXX. inv HXX.
            rewrite Hap1 in Hap1'; inv Hap1'.
            econstructor; eauto.
            + econstructor; eauto. intros rr.
              destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|].
              * eexists; split; simpl; eauto.
                destruct H8 as [-> | [-> | ->] ]; auto.
              * rewrite lookup_insert_ne //.
                destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert; eexists; split; eauto; simpl; auto|].
                rewrite lookup_insert_ne //; auto.
            + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
              rewrite !(lookup_insert_ne _ PC) //.
              eapply (@Hsregs_preserve_word_of_arg reg1 reg2 dst (inl nn)); auto. }
    - (* GetA *)
      assert (AA: match reg1 !! r with
                  | Some (inr _) =>
                    exists n, match incrementPC (<[dst:=inl n]> reg1) with
                              | Some reg1'' =>
                                c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inl n]> reg2) = Some reg2' /\ mem2' = mem2
                              | _ => c1 = lang.Failed /\ c2 = Failed
                              end
                  | _ => c1 = lang.Failed /\ c2 = Failed
                  end).
      { simpl in H1, H2. destruct (Hregsdef r) as [wr [Hwr _] ].
        rewrite Hwr. rewrite /base.RegLocate Hwr in H1.
        rewrite /RegLocate (Hsregs _ _ Hwr) in H2.
        destruct wr; [inv H1; inv H2; auto|].
        destruct (translate_word_cap c) as [c' Hc'].
        rewrite Hc' in H2. set (nn := match c with Ret _ _ a | Stk _ _ _ _ a | Regular (_, _, _, _, a) => z_of a end).
        exists nn. assert (X1: lang.updatePC (<[dst:=inl nn]> reg1, h, stk, cs) = (c1, (reg1', h', stk', cs'))).
        { rewrite -H1 /base.update_reg /=.
          subst nn; destruct c; auto; [| destruct a2; auto..].
          destruct c as [ [ [ [pp gg] bb] ee] aa]; auto.
          destruct aa; auto. }
        clear H1. assert (X2: updatePC (<[dst:=inl nn]> reg2, mem2) = (c2, (reg2', mem2'))).
        { rewrite -H2 /update_reg /=.
          subst nn. destruct c; inv Hc'; auto; [| destruct a2; auto..].
          destruct c' as [ [ [ [pp gg] bb] ee] aa]; auto.
          destruct aa; auto. }
        clear H2. assert (exists w, (<[dst:=inl nn]> reg1) !! PC = Some w /\ (<[dst:=inl nn]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
        { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
          rewrite !lookup_insert_ne //. eauto. }
        destruct (incrementPC (<[dst:=inl nn]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        - generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
          intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in X1.
          erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in X2.
          inv X1; inv X2; auto.
        - destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
          erewrite incrementPC_success_updatePC in X1; eauto.
          rewrite Hincrement2.
          eapply rules_base.incrementPC_success_updatePC in Hincrement2.
          destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
          instantiate (1 := mem2) in Z3.
          rewrite Z3 -Z4 in X2. inv X1; inv X2; repeat split; auto. }
      destruct (Hregsdef r) as [wr [Hwr Hinterpwr] ].
      rewrite Hwr in AA. destruct wr as [nr|cr].
      + destruct AA as [-> ->]. econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate.
      + destruct AA as [nn AA]. destruct (incrementPC (<[dst:=inl nn]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        * destruct AA as [-> ->]. econstructor.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        * destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { intros _.
            eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1; elim Hincrement1|].
            rewrite lookup_insert_ne // HPC in Hincrement1.
            destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
            eapply rules_base.incrementPC_Some_inv in Hincrement2.
            destruct Hincrement2 as [pp [gg [bb [ee [aa [aa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
            rewrite lookup_insert_ne // in HXX.
            rewrite (Hsregs _ _ HPC) /= in HXX. inv HXX.
            rewrite Hap1 in Hap1'; inv Hap1'.
            econstructor; eauto.
            + econstructor; eauto. intros rr.
              destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|].
              * eexists; split; simpl; eauto.
                destruct H8 as [-> | [-> | ->] ]; auto.
              * rewrite lookup_insert_ne //.
                destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert; eexists; split; eauto; simpl; auto|].
                rewrite lookup_insert_ne //; auto.
            + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
              rewrite !(lookup_insert_ne _ PC) //.
              eapply (@Hsregs_preserve_word_of_arg reg1 reg2 dst (inl nn)); auto. }
    - (* Fail *)
      simpl in H1, H2. inv H1; inv H2.
      econstructor.
      + eapply sim_expr_exec_inv in Hsexpr. subst K.
        simpl. repeat econstructor.
      + rewrite can_step_fill /can_step /=; intros [A | A]; discriminate.
    - (* Halt *)
      simpl in H1, H2. inv H1; inv H2.
      econstructor.
      + eapply sim_expr_exec_inv in Hsexpr. subst K.
        simpl. repeat econstructor.
      + rewrite can_step_fill /can_step /=; intros [A | A]; discriminate.
    - (* LoadU *)
      destruct (Hregsdef src) as [wsrc [Hwsrc Hinterpsrc] ].
      generalize (Hsregs _ _ Hwsrc). intros Hwsrc'.
      assert (AA: match wsrc with
                  | inr (Regular (pp, gg, bb, ee, aa)) =>
                    if isU pp then
                      match lang.z_of_argument reg1 offs with
                      | Some noffs =>
                        match verify_access (LoadU_access bb ee aa noffs) with
                        | Some aa' =>
                          exists waa, h !! aa' = Some waa /\ interp waa h stk cs /\ match incrementPC (<[dst:=waa]> reg1) with
                            | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=translate_word waa]> reg2) = Some reg2' /\ mem2' = mem2
                            | None => c1 = lang.Failed /\ c2 = Failed
                            end
                        | None => c1 = lang.Failed /\ c2 = Failed
                        end
                      | None => c1 = lang.Failed /\ c2 = Failed
                      end
                    else c1 = lang.Failed /\ c2 = Failed
                  | inr (Stk dd pp bb ee aa) =>
                    if isU pp then
                      match lang.z_of_argument reg1 offs with
                      | Some noffs =>
                        match verify_access (LoadU_access bb ee aa noffs) with
                        | Some aa' =>
                          exists xstk, stack dd ((reg1, stk)::cs) = Some xstk /\
                          exists waa, xstk !! aa' = Some waa /\ interp waa h stk cs /\ match incrementPC (<[dst:=waa]> reg1) with
                            | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=translate_word waa]> reg2) = Some reg2' /\ mem2' = mem2
                            | None => c1 = lang.Failed /\ c2 = Failed
                            end
                        | None => c1 = lang.Failed /\ c2 = Failed
                        end
                      | None => c1 = lang.Failed /\ c2 = Failed
                      end
                    else c1 = lang.Failed /\ c2 = Failed
                  | _ => c1 = lang.Failed /\ c2 = Failed
                  end).
      { destruct wsrc; [rewrite /= /base.RegLocate Hwsrc /= in H1; rewrite /= /RegLocate Hwsrc' /= in H2; inv H1; inv H2; auto|].
        destruct c; [|simpl in Hwsrc'|simpl in Hwsrc'; rewrite /= /base.RegLocate Hwsrc /= in H1; rewrite /= /RegLocate Hwsrc' /= in H2; inv H1; inv H2; auto].
        - destruct c as [ [ [ [px gx] bx] ex] ax].
          rewrite /= /base.RegLocate Hwsrc /= in H1; rewrite /= /RegLocate Hwsrc' /= in H2.
          destruct (isU px) eqn:HisU; [|inv H1; inv H2; auto].
          assert (UU: z_of_argument reg2 offs = lang.z_of_argument reg1 offs).
          { destruct offs; simpl; auto.
            destruct (Hregsdef r) as [wr [Hwr _] ].
            generalize (Hsregs _ _ Hwr). intros Hwr'.
            rewrite Hwr Hwr'. destruct wr; [simpl; auto|].
            destruct (translate_word_cap c) as [c' ->]. auto. }
          rewrite UU in H2.
          destruct (lang.z_of_argument reg1 offs) as [noffs|] eqn:Hoffs; [|inv H1; inv H2; auto].
          fold verify_access in H1.
          destruct (verify_access (LoadU_access bx ex ax noffs)) as [aa'|] eqn:Hverify; cycle 1.
          { simpl in Hverify. rewrite Hverify in H1, H2; inv H1; inv H2; auto. }
          simpl in Hverify; rewrite Hverify in H1, H2.
          rewrite /base.MemLocate in H1.
          rewrite /MemLocate in H2.
          assert ((ax + noffs)%a = Some aa' /\ (bx <= aa')%a /\ (aa' < ax)%a /\ (ax <= ex)%a) as [Haa' [Hcond1 [Hcond2 Hcond3] ] ].
          { clear -Hverify. destruct ((ax + noffs)%a); [|inv Hverify].
            destruct (Addr_le_dec bx a); [|inv Hverify].
            destruct (Addr_lt_dec a ax); [|inv Hverify].
            destruct (Addr_le_dec ax ex); inv Hverify; auto. }
          destruct Hinterpsrc as [T1 T2].
          generalize (T2 aa' ltac:(clear -Hcond1 Hcond2 Hcond3; solve_addr)).
          intro Hwaa'. apply elem_of_dom in Hwaa'.
          destruct Hwaa' as [waa' Hwaa'].
          destruct (Hsh _ _ Hwaa') as [Hwaa'' [U1 [U2 U3] ] ].
          rewrite Hwaa'. eexists; split; auto.
          split; auto.
          { destruct waa'; simpl; auto.
            destruct c; simpl in U2; try congruence. auto. }
          rewrite Hwaa' /base.update_reg /= in H1.
          rewrite Hwaa'' /update_reg /= in H2.
          assert (exists w, (<[dst:=waa']> reg1) !! PC = Some w /\ (<[dst:=translate_word waa']> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
          { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
            rewrite !lookup_insert_ne //. eauto. }
          destruct (incrementPC (<[dst:=waa']> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
          { generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
            intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in H1.
            erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in H2.
            inv H1; inv H2; auto. }
          { destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
            erewrite incrementPC_success_updatePC in H1; eauto.
            rewrite Hincrement2.
            eapply rules_base.incrementPC_success_updatePC in Hincrement2.
            destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
            instantiate (1 := mem2) in Z3.
            rewrite Z3 -Z4 in H2. inv H1; inv H2; repeat split; auto. }
        - rewrite /= /base.RegLocate Hwsrc /= in H1; rewrite /= /RegLocate Hwsrc' /= in H2.
          destruct (isU p0) eqn:HisU; [|inv H1; inv H2; auto].
          assert (UU: z_of_argument reg2 offs = lang.z_of_argument reg1 offs).
          { destruct offs; simpl; auto.
            destruct (Hregsdef r) as [wr [Hwr _] ].
            generalize (Hsregs _ _ Hwr). intros Hwr'.
            rewrite Hwr Hwr'. destruct wr; [simpl; auto|].
            destruct (translate_word_cap c) as [c' ->]. auto. }
          rewrite UU in H2.
          destruct (lang.z_of_argument reg1 offs) as [noffs|] eqn:Hoffs; [|inv H1; inv H2; auto].
          destruct (verify_access (LoadU_access a0 a1 a2 noffs)) as [aa'|] eqn:Hverify; cycle 1.
          { simpl in Hverify. rewrite Hverify in H1, H2; inv H1; inv H2; auto. }
          simpl in Hverify; rewrite Hverify in H1, H2.
          rewrite /base.MemLocate in H1.
          rewrite /MemLocate in H2.
          assert ((a2 + noffs)%a = Some aa' /\ (a0 <= aa')%a /\ (aa' < a2)%a /\ (a2 <= a1)%a) as [Haa' [Hcond1 [Hcond2 Hcond3] ] ].
          { clear -Hverify. destruct ((a2 + noffs)%a); [|inv Hverify].
            destruct (Addr_le_dec a0 a); [|inv Hverify].
            destruct (Addr_lt_dec a a2); [|inv Hverify].
            destruct (Addr_le_dec a2 a1); inv Hverify; auto. }
          destruct Hinterpsrc as [T1 [T2 [T4 T3] ] ].
          simpl.
          match goal with |- context [(if ?Q then _ else _) = _] => destruct Q as [_|KK]; [auto|elim KK; auto] end.
          exists stk. split; auto.
          destruct (T3 aa' ltac:(simpl; clear -Hcond1 Hcond2 Hcond3 HisU; destruct p0; simpl in HisU; try congruence; simpl; solve_addr)) as [waa' Hwaa'].
          destruct (Hstksim _ _ Hwaa') as [Hwaa'' [U1 U2] ].
          rewrite Hwaa'. eexists; split; auto.
          split; auto.
          rewrite Hwaa' /base.update_reg /= in H1.
          rewrite Hwaa'' /update_reg /= in H2.
          assert (exists w, (<[dst:=waa']> reg1) !! PC = Some w /\ (<[dst:=translate_word waa']> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
          { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
            rewrite !lookup_insert_ne //. eauto. }
          destruct (incrementPC (<[dst:=waa']> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
          { generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
            intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in H1.
            erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in H2.
            inv H1; inv H2; auto. }
          { destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
            erewrite incrementPC_success_updatePC in H1; eauto.
            rewrite Hincrement2.
            eapply rules_base.incrementPC_success_updatePC in Hincrement2.
            destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
            instantiate (1 := mem2) in Z3.
            rewrite Z3 -Z4 in H2. inv H1; inv H2; repeat split; auto. } }
      clear H1 H2. destruct wsrc.
      { destruct AA as [-> ->]. econstructor; eauto.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
      destruct c; cycle 2.
      { destruct AA as [-> ->]. econstructor; eauto.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
      { destruct c as [ [ [ [pp gg] bb] ee] aa].
        destruct (isU pp) eqn:HisU; cycle 1.
        { destruct AA as [-> ->]. econstructor; eauto.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (lang.z_of_argument reg1 offs) as [noffs|] eqn:Hoffs; cycle 1.
        { destruct AA as [-> ->]. econstructor; eauto.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (verify_access (LoadU_access bb ee aa noffs)) as [aa'|] eqn:Haa'; cycle 1.
        { destruct AA as [-> ->]. econstructor; eauto.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct AA as [waa [Hwaa [Hinterpaa AA] ] ].
        destruct (incrementPC (<[dst:=waa]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        { destruct AA as [-> ->]. econstructor; eauto.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
        econstructor; eauto.
        { eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor. }
        { intros _. eapply incrementPC_inv_Some in Hincrement1.
          destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|].
          - destruct waa; [elim Hincrement1|].
            destruct c; [| |elim Hincrement1].
            * destruct c as [ [ [ [px gx] bx] ex] ax].
              destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite lookup_insert in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              inv HXX. rewrite Hap1 in Hap1'; inv Hap1'.
              rewrite !insert_insert.
              econstructor; eauto.
              { econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto]. }
              { intros rr; destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|rewrite !lookup_insert_ne; auto]. }
            * intros. destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite lookup_insert in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              inv HXX. rewrite Hap1 in Hap1'; inv Hap1'.
              rewrite !insert_insert.
              constructor; eauto.
              { econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; eauto].
                eexists; split; eauto.
                simpl. destruct Hinterpaa as [? [? [HH ?] ] ].
                do 3 (split; auto).
                intros; eapply H2. simpl.
                destruct X2 as [? [? [? [? ?] ] ] ].
                destruct ppp; try congruence; auto. }
              { intros rr; destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|rewrite !lookup_insert_ne; auto]. }
          - rewrite lookup_insert_ne in Hincrement1; auto.
            rewrite HPC in Hincrement1.
            destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
            eapply rules_base.incrementPC_Some_inv in Hincrement2.
            destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
            rewrite lookup_insert_ne in HXX; auto.
            generalize (Hsregs _ _ HPC). rewrite HXX.
            intro DD; inv DD. rewrite Hap1 in Hap1'; inv Hap1'.
            econstructor; eauto.
            * econstructor; eauto. intros rr.
              destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite (lookup_insert_ne _ PC); auto].
              { eexists; split; eauto.
                destruct H8 as [-> | [-> | ->] ]; auto. }
              destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
            * intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto| rewrite !(lookup_insert_ne _ PC); auto].
              destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert; inversion 1; auto| rewrite !lookup_insert_ne; auto]. } }
      { destruct (isU p0) eqn:HisU; cycle 1.
        { destruct AA as [-> ->]. econstructor; eauto.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (lang.z_of_argument reg1 offs) as [noffs|] eqn:Hoffs; cycle 1.
        { destruct AA as [-> ->]. econstructor; eauto.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (verify_access (LoadU_access a0 a1 a2 noffs)) as [aa'|] eqn:Haa'; cycle 1.
        { destruct AA as [-> ->]. econstructor; eauto.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct AA as [xstk [Hxstk [waa [Hwaa [Hinterpaa AA] ] ] ] ].
        destruct (incrementPC (<[dst:=waa]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
        { destruct AA as [-> ->]. econstructor; eauto.
          * eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
        econstructor; eauto.
        { eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor. }
        { intros _. eapply incrementPC_inv_Some in Hincrement1.
          destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|].
          - destruct waa; [elim Hincrement1|].
            destruct c; [| |elim Hincrement1].
            * destruct c as [ [ [ [px gx] bx] ex] ax].
              destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite lookup_insert in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              inv HXX. rewrite Hap1 in Hap1'; inv Hap1'.
              rewrite !insert_insert.
              econstructor; eauto.
              { econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto]. }
              { intros rr; destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|rewrite !lookup_insert_ne; auto]. }
            * intros. destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              rewrite lookup_insert in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              inv HXX. rewrite Hap1 in Hap1'; inv Hap1'.
              rewrite !insert_insert.
              constructor; eauto.
              { econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; eauto].
                eexists; split; eauto.
                simpl. destruct Hinterpaa as [? [? [HH ?] ] ].
                do 3 (split; auto).
                intros; eapply H2. simpl.
                destruct X2 as [? [? [? [? ?] ] ] ].
                destruct ppp; try congruence; auto. }
              { intros rr; destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|rewrite !lookup_insert_ne; auto]. }
          - rewrite lookup_insert_ne in Hincrement1; auto.
            rewrite HPC in Hincrement1.
            destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
            eapply rules_base.incrementPC_Some_inv in Hincrement2.
            destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
            rewrite lookup_insert_ne in HXX; auto.
            generalize (Hsregs _ _ HPC). rewrite HXX.
            intro DD; inv DD. rewrite Hap1 in Hap1'; inv Hap1'.
            econstructor; eauto.
            * econstructor; eauto. intros rr.
              destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite (lookup_insert_ne _ PC); auto].
              { eexists; split; eauto.
                destruct H8 as [-> | [-> | ->] ]; auto. }
              destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
            * intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto| rewrite !(lookup_insert_ne _ PC); auto].
              destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert; inversion 1; auto| rewrite !lookup_insert_ne; auto]. } }
    - (* StoreU *)
      destruct (Hregsdef dst) as [wdst [Hwdst Hinterpdst] ].
      generalize (Hsregs _ _ Hwdst). intros Hwdst'.
      assert (exists wsrc, word_of_argument reg1 src = wsrc /\ interp wsrc h stk cs /\ rules_base.word_of_argument reg2 src = Some (translate_word wsrc)) as [wsrc [Hwsrc [Hinterpwsrc Hwsrc'] ] ].
      { destruct src; simpl; [eexists; split; eauto; simpl; eauto|].
        destruct (Hregsdef r) as [wr [Hwr Hinterpwr] ].
        generalize (Hsregs _ _ Hwr); intros Hwr'.
        rewrite /base.RegLocate Hwr. eexists; split; eauto. }
      assert (AA: match wdst with
                  | inr (Regular (pp, gg, bb, ee, aa)) =>
                    match lang.z_of_argument reg1 offs with
                    | Some noffs =>
                      match verify_access (StoreU_access bb ee aa noffs) with
                      | Some aa' =>
                        if isU pp && lang.canStoreU pp aa' wsrc then
                          if addr_eq_dec aa aa'
                          then exists aa'', (aa + 1)%a = Some aa'' /\
                            match incrementPC (<[dst:=inr (Regular (pp, gg, bb, ee, aa''))]> reg1) with
                            | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = (<[aa':=wsrc]> h) /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inr (pp, gg, bb, ee, aa'')]> reg2) = Some reg2' /\ mem2' = (<[aa':=translate_word wsrc]> mem2)
                            | _ => c1 = lang.Failed /\ c2 = Failed
                            end
                          else
                            match incrementPC reg1 with
                            | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = (<[aa':=wsrc]> h) /\ stk' = stk /\ cs' = cs /\ incrementPC' reg2 = Some reg2' /\ mem2' = (<[aa':=translate_word wsrc]> mem2)
                            | _ => c1 = lang.Failed /\ c2 = Failed
                            end
                        else c1 = lang.Failed /\ c2 = Failed
                      | _ => c1 = lang.Failed /\ c2 = Failed
                      end
                    | _ => c1 = lang.Failed /\ c2 = Failed
                    end
                  | inr (Stk dd pp bb ee aa) =>
                    match lang.z_of_argument reg1 offs with
                    | Some noffs =>
                      match verify_access (StoreU_access bb ee aa noffs) with
                      | Some aa' =>
                        if isU pp && lang.canStoreU pp aa' wsrc then
                          if addr_eq_dec aa aa'
                          then exists aa'', (aa + 1)%a = Some aa'' /\
                            match incrementPC (<[dst:=inr (Stk dd pp bb ee aa'')]> reg1) with
                            | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = (<[aa':=wsrc]> stk) /\ cs' = cs /\ incrementPC' (<[dst:=inr (pp, Directed, bb, ee, aa'')]> reg2) = Some reg2' /\ mem2' = (<[aa':=translate_word wsrc]> mem2)
                            | _ => c1 = lang.Failed /\ c2 = Failed
                            end
                          else
                            match incrementPC reg1 with
                            | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = (<[aa':=wsrc]> stk) /\ cs' = cs /\ incrementPC' reg2 = Some reg2' /\ mem2' = (<[aa':=translate_word wsrc]> mem2)
                            | _ => c1 = lang.Failed /\ c2 = Failed
                            end
                        else c1 = lang.Failed /\ c2 = Failed
                      | _ => c1 = lang.Failed /\ c2 = Failed
                      end
                    | _ => c1 = lang.Failed /\ c2 = Failed
                    end
                  | _ => c1 = lang.Failed /\ c2 = Failed
                  end).
      { rewrite /= /base.RegLocate Hwdst in H1.
        rewrite /= /RegLocate Hwdst' in H2.
        destruct wdst; [inv H1; inv H2; auto|].
        destruct c; simpl in H2; [| | repeat (match goal with H: context [match ?X with _ => _ end = (c2, _)] |- _ => destruct X end); inv H1; inv H2; auto].
        { destruct c as [ [ [ [pp gg] bb] ee] aa].
          assert (UU: z_of_argument reg2 offs = lang.z_of_argument reg1 offs).
          { destruct offs; simpl; auto.
            destruct (Hregsdef r) as [wr [Hwr _] ].
            generalize (Hsregs _ _ Hwr). intros Hwr'.
            rewrite Hwr Hwr'. destruct wr; [simpl; auto|].
            destruct (translate_word_cap c) as [c' ->]. auto. }
          rewrite UU in H2.
          destruct (lang.z_of_argument reg1 offs) as [noffs|] eqn:Hnoffs; [|inv H1; inv H2; auto].
          destruct (verify_access (StoreU_access bb ee aa noffs)) as [aa'|] eqn:Hconds; cycle 1.
          { rewrite /verify_access /= in Hconds. rewrite Hconds in H1, H2.
            inv H1; inv H2; auto. }
          rewrite /verify_access /= in Hconds. rewrite Hconds in H1, H2.
          rewrite /word_of_argument in Hwsrc. rewrite Hwsrc in H1.
          replace (match src with | inl n => inl n | inr rsrc => match reg2 !! rsrc with | Some w => w | None => inl 0%Z end end) with (translate_word wsrc) in H2.
          2:{ rewrite /rules_base.word_of_argument in Hwsrc'.
              destruct src; [inv Hwsrc'; auto| rewrite Hwsrc'; auto]. }
          assert (OO: lang.canStoreU pp aa' wsrc = canStoreU pp aa' (translate_word wsrc)).
          { destruct wsrc; simpl; auto.
            destruct c; auto. }
          rewrite -OO in H2.
          destruct (isU pp && lang.canStoreU pp aa' wsrc) eqn:Hconds'; [|inv H1; inv H2; auto].
          destruct (addr_eq_dec aa aa').
          - eexists ^(aa + 1)%a. subst aa'.
            destruct (proj1 (verify_access_spec (StoreU_access _ _ _ _) aa) Hconds) as [Hconds1 [Hconds2 [Hconds3 Hconds4] ] ].
            split; [clear -Hconds4; solve_addr|].
            replace (aa + 1)%a with (Some ^(aa + 1)%a) in H1 by (clear -Hconds4; solve_addr).
            replace (aa + 1)%a with (Some ^(aa + 1)%a) in H2 by (clear -Hconds4; solve_addr).
            rewrite /base.update_reg /base.update_mem /= in H1.
            rewrite /update_reg /update_mem /= in H2.
            assert (exists w, (<[dst:=inr (Regular (pp, gg, bb, ee, ^(aa + 1)%a))]> reg1) !! PC = Some w /\ (<[dst:=inr (pp, gg, bb, ee, ^(aa + 1)%a)]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
            { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
            rewrite !lookup_insert_ne //. eauto. }
            destruct (incrementPC (<[dst:=inr (Regular (pp, gg, bb, ee, ^(aa + 1)%a))]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
            { generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
              intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in H1.
              erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in H2.
              inv H1; inv H2; auto. }
            destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
            erewrite incrementPC_success_updatePC in H1; eauto.
            rewrite Hincrement2.
            eapply rules_base.incrementPC_success_updatePC in Hincrement2.
            destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
            instantiate (1 := <[aa:=translate_word wsrc]> mem2) in Z3.
            rewrite Z3 -Z4 in H2. inv H1; inv H2; repeat split; auto.
          - rewrite /base.update_reg /base.update_mem /= in H1.
            rewrite /update_reg /update_mem /= in H2.
            generalize (Hsregs _ _ HPC). intros HPC'.
            destruct (incrementPC reg1) as [reg1''|] eqn:Hincrement1; cycle 1.
            { generalize (incrementPC_fail_incrementPC' HPC HPC' Hincrement1).
              intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in H1.
              erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in H2.
              inv H1; inv H2; auto. }
            destruct (incrementPC_success_incrementPC' HPC HPC' Hincrement1) as [reg2'' Hincrement2].
            erewrite incrementPC_success_updatePC in H1; eauto.
            rewrite Hincrement2.
            eapply rules_base.incrementPC_success_updatePC in Hincrement2.
            destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
            instantiate (1 := <[aa':=translate_word wsrc]> mem2) in Z3.
            rewrite Z3 -Z4 in H2. inv H1; inv H2; repeat split; auto. }
        { assert (UU: z_of_argument reg2 offs = lang.z_of_argument reg1 offs).
          { destruct offs; simpl; auto.
            destruct (Hregsdef r) as [wr [Hwr _] ].
            generalize (Hsregs _ _ Hwr). intros Hwr'.
            rewrite Hwr Hwr'. destruct wr; [simpl; auto|].
            destruct (translate_word_cap c) as [c' ->]. auto. }
          rewrite UU in H2.
          destruct (lang.z_of_argument reg1 offs) as [noffs|] eqn:Hnoffs; [|inv H1; inv H2; auto].
          destruct (verify_access (StoreU_access a0 a1 a2 noffs)) as [aa'|] eqn:Hconds; cycle 1.
          { rewrite /verify_access /= in Hconds. rewrite Hconds in H1, H2.
            inv H1; inv H2; auto. }
          rewrite /verify_access /= in Hconds. rewrite Hconds in H1, H2.
          rewrite /word_of_argument in Hwsrc. rewrite Hwsrc in H1.
          replace (match src with | inl n => inl n | inr rsrc => match reg2 !! rsrc with | Some w => w | None => inl 0%Z end end) with (translate_word wsrc) in H2.
          2:{ rewrite /rules_base.word_of_argument in Hwsrc'.
              destruct src; [inv Hwsrc'; auto| rewrite Hwsrc'; auto]. }
          assert (OO: lang.canStoreU p0 aa' wsrc = canStoreU p0 aa' (translate_word wsrc)).
          { destruct wsrc; simpl; auto.
            destruct c; auto. }
          rewrite -OO in H2.
          destruct (isU p0 && lang.canStoreU p0 aa' wsrc) eqn:Hconds'; [|inv H1; inv H2; auto].
          destruct (addr_eq_dec a2 aa').
          - eexists ^(a2 + 1)%a. subst aa'.
            destruct (proj1 (verify_access_spec (StoreU_access _ _ _ _) a2) Hconds) as [Hconds1 [Hconds2 [Hconds3 Hconds4] ] ].
            split; [clear -Hconds4; solve_addr|].
            replace (a2 + 1)%a with (Some ^(a2 + 1)%a) in H1 by (clear -Hconds4; solve_addr).
            replace (a2 + 1)%a with (Some ^(a2 + 1)%a) in H2 by (clear -Hconds4; solve_addr).
            rewrite /base.update_reg /base.update_mem /= in H1.
            rewrite /update_reg /update_mem /= in H2.
            assert (exists w, (<[dst:=inr (Stk n p0 a0 a1 ^(a2 + 1)%a)]> reg1) !! PC = Some w /\ (<[dst:=inr (p0, Directed, a0, a1, ^(a2 + 1)%a)]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
            { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
            rewrite !lookup_insert_ne //. eauto. }
            unfold Stackframe in *. destruct (nat_eq_dec n (length cs)) as [_|KK]; [|elim KK; destruct Hinterpdst; auto].
            destruct (incrementPC (<[dst:=inr (Stk n p0 a0 a1 ^(a2 + 1)%a)]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
            { generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
              intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in H1.
              erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in H2.
              inv H1; inv H2; auto. }
            destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
            erewrite incrementPC_success_updatePC in H1; eauto.
            rewrite Hincrement2.
            eapply rules_base.incrementPC_success_updatePC in Hincrement2.
            destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
            instantiate (1 := <[a2:=translate_word wsrc]> mem2) in Z3.
            rewrite Z3 -Z4 in H2. inv H1; inv H2; repeat split; auto.
          - rewrite /base.update_reg /base.update_mem /update_stk /= in H1.
            rewrite /update_reg /update_mem /= in H2.
            unfold Stackframe in *. destruct (nat_eq_dec n (length cs)) as [_|KK]; [|elim KK; destruct Hinterpdst; auto].
            generalize (Hsregs _ _ HPC). intros HPC'.
            destruct (incrementPC reg1) as [reg1''|] eqn:Hincrement1; cycle 1.
            { generalize (incrementPC_fail_incrementPC' HPC HPC' Hincrement1).
              intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in H1.
              erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in H2.
              inv H1; inv H2; auto. }
            destruct (incrementPC_success_incrementPC' HPC HPC' Hincrement1) as [reg2'' Hincrement2].
            erewrite incrementPC_success_updatePC in H1; eauto.
            rewrite Hincrement2.
            eapply rules_base.incrementPC_success_updatePC in Hincrement2.
            destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
            instantiate (1 := <[aa':=translate_word wsrc]> mem2) in Z3.
            rewrite Z3 -Z4 in H2. inv H1; inv H2; repeat split; auto. } }
      clear H1 H2. destruct wdst.
      { destruct AA as [-> ->]. econstructor; eauto.
        - eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
      destruct c; cycle 2.
      { destruct AA as [-> ->]. econstructor; eauto.
        - eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
      { destruct c as [ [ [ [pp gg] bb] ee] aa].
        destruct (lang.z_of_argument reg1 offs) as [noffs|] eqn:Hnoffs; cycle 1.
        { destruct AA as [-> ->]. econstructor; eauto.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (verify_access (StoreU_access bb ee aa noffs)) as [aa'|] eqn:Hconds; cycle 1.
        { destruct AA as [-> ->]. econstructor; eauto.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (proj1 (verify_access_spec (StoreU_access _ _ _ _) _) Hconds) as [Hconds1 [Hconds2 [Hconds3 Hconds4] ] ].
        destruct (isU pp && lang.canStoreU pp aa' wsrc) eqn:Hconds'; cycle 1.
        { destruct AA as [-> ->]. econstructor; eauto.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (addr_eq_dec aa aa').
        { subst aa'. destruct AA as [aa'' [Haa'' AA] ].
          destruct (incrementPC (<[dst:=inr (Regular (pp, gg, bb, ee, aa''))]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
          { destruct AA as [-> ->]. econstructor; eauto.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { intros _. eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|].
            - rewrite HPC in Hwdst; inv Hwdst.
            - rewrite lookup_insert_ne in Hincrement1; auto.
              rewrite HPC in Hincrement1. destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              rewrite lookup_insert_ne in HXX; auto.
              generalize (Hsregs _ _ HPC). intros HPC'.
              rewrite HPC' in HXX; inv HXX.
              rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              + econstructor; eauto.
                * intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
                  { eexists; split; auto. simpl.
                    destruct H8 as [-> | [-> | ->] ]; auto. }
                  destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
                  { eexists; split; auto. eapply interp_heap_extend.
                    auto. }
                  destruct (Hregsdef rr) as [wr [Hwr Hinterpwr] ].
                  eexists; split; eauto. apply interp_heap_extend; auto.
                * intros ax wx Hwx. destruct (Hstksim ax wx Hwx) as [? [? ?] ].
                  rewrite lookup_insert_ne; [do 2 (split; auto)|].
                  apply interp_heap_extend; auto.
                  generalize (Hstkdisjheap _ ltac:(eexists; apply Hwx)).
                  destruct Hinterpdst. generalize (H5 aa ltac:(clear -Hconds2 Hconds4; solve_addr)).
                  intros Q. apply Hdisj in Q. clear -Q; solve_addr.
                * eapply sim_cs_heap_extend; eauto.
                  destruct (Hinterpdst). apply Hdisj.
                  apply H1. clear -Hconds2 Hconds4; solve_addr.
              + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|rewrite !(lookup_insert_ne _ PC); auto].
                destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|rewrite !lookup_insert_ne; auto].
              + intros ax. destruct (addr_eq_dec aa ax); [subst ax; rewrite !lookup_insert|rewrite !lookup_insert_ne; auto].
                * inversion 1; split; auto.
                  destruct (word_of_argument reg1 src); auto.
                  simpl in Hinterpdst.
                  destruct Hinterpdst as [Q W].
                  apply andb_true_iff in Hconds'.
                  destruct Hconds' as [Hcond1 Hcond2].
                  rewrite /lang.canStoreU Q in Hcond2.
                  rewrite andb_false_l in Hcond2.
                  destruct c; try congruence.
                  destruct c as [ [ [ [px gx] bx] ex] ax].
                  destruct gx; try congruence.
                  simpl. simpl in Hinterpwsrc.
                  destruct Hinterpwsrc. do 2 (split; auto).
                  intros. apply H3 in H5. clear -H5; set_solver.
                * intros. apply Hsh in H0. destruct H0 as [R [T [Y U] ] ].
                  do 3 (split; auto). apply can_address_only_heap_extend; auto.
              + intros. assert (a = aa \/ a ∈ dom (gset Addr) h) by (clear -H0; set_solver).
                destruct H1; [subst a|apply Hdisj; auto].
                simpl in Hinterpdst. destruct Hinterpdst as [? ?].
                generalize (H2 aa ltac:(clear -Hconds2 Hconds4; solve_addr)).
                intro F. apply Hdisj in F. auto. } }
        { destruct (incrementPC reg1) as [reg1''|] eqn:Hincrement1; cycle 1.
          { destruct AA as [-> ->]. econstructor; eauto.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { intros _. eapply incrementPC_inv_Some in Hincrement1.
            rewrite HPC in Hincrement1.
            destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
            eapply rules_base.incrementPC_Some_inv in Hincrement2.
            destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
            generalize (Hsregs _ _ HPC). intros HPC'.
            rewrite HPC' in HXX; inv HXX.
            rewrite Hap1 in Hap1'; inv Hap1'.
            econstructor; eauto.
            + econstructor; eauto.
              * intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
                { eexists; split; auto. simpl.
                  destruct H8 as [-> | [-> | ->] ]; auto. }
                destruct (Hregsdef rr) as [wr [Hwr Hinterpwr] ].
                eexists; split; eauto. apply interp_heap_extend; auto.
              * intros ax wx Hwx. destruct (Hstksim ax wx Hwx) as [? [? ?] ].
                rewrite lookup_insert_ne; [do 2 (split; auto)|].
                apply interp_heap_extend; auto.
                generalize (Hstkdisjheap _ ltac:(eexists; apply Hwx)).
                destruct Hinterpdst. generalize (H5 aa' ltac:(clear -Hconds2 Hconds3 Hconds4; solve_addr)).
                intros Q. apply Hdisj in Q. clear -Q; solve_addr.
              * eapply sim_cs_heap_extend; eauto.
                destruct (Hinterpdst). apply Hdisj.
                apply H1. clear -Hconds2 Hconds3 Hconds4; solve_addr.
              + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|rewrite !(lookup_insert_ne _ PC); auto].
              + intros ax. destruct (addr_eq_dec aa' ax); [subst ax; rewrite !lookup_insert|rewrite !lookup_insert_ne; auto].
                * inversion 1; split; auto.
                  destruct (word_of_argument reg1 src); auto.
                  simpl in Hinterpdst.
                  destruct Hinterpdst as [Q W].
                  apply andb_true_iff in Hconds'.
                  destruct Hconds' as [Hcond1 Hcond2].
                  rewrite /lang.canStoreU Q in Hcond2.
                  rewrite andb_false_l in Hcond2.
                  destruct c; try congruence.
                  destruct c as [ [ [ [px gx] bx] ex] ax].
                  destruct gx; try congruence.
                  simpl. simpl in Hinterpwsrc.
                  destruct Hinterpwsrc. do 2 (split; auto).
                  intros. apply H3 in H5. clear -H5; set_solver.
                * intros. apply Hsh in H0. destruct H0 as [R [T [Y U] ] ].
                  do 3 (split; auto). apply can_address_only_heap_extend; auto.
              + intros. assert (a = aa' \/ a ∈ dom (gset Addr) h) by (clear -H0; set_solver).
                destruct H1; [subst a|apply Hdisj; auto].
                simpl in Hinterpdst. destruct Hinterpdst as [? ?].
                generalize (H2 aa' ltac:(clear -Hconds2 Hconds3 Hconds4; solve_addr)).
                intro F. apply Hdisj in F. auto. } } }
      { destruct (lang.z_of_argument reg1 offs) as [noffs|] eqn:Hnoffs; cycle 1.
        { destruct AA as [-> ->]. econstructor; eauto.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (verify_access (StoreU_access a0 a1 a2 noffs)) as [aa'|] eqn:Hconds; cycle 1.
        { destruct AA as [-> ->]. econstructor; eauto.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (proj1 (verify_access_spec (StoreU_access _ _ _ _) _) Hconds) as [Hconds1 [Hconds2 [Hconds3 Hconds4] ] ].
        destruct (isU p0 && lang.canStoreU p0 aa' wsrc) eqn:Hconds'; cycle 1.
        { destruct AA as [-> ->]. econstructor; eauto.
          - eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor.
          - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        destruct (addr_eq_dec a2 aa').
        { subst aa'. destruct AA as [aa'' [Haa'' AA] ].
          destruct (incrementPC (<[dst:=inr (Stk n p0 a0 a1 aa'')]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
          { destruct AA as [-> ->]. econstructor; eauto.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { intros _. eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|].
            - rewrite HPC in Hwdst; inv Hwdst.
              destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              generalize (Hsregs _ _ HPC). intros HPC'.
              rewrite lookup_insert in HXX; inv HXX.
              rewrite Hap1 in Hap1'; inv Hap1'.
              rewrite !insert_insert.
              econstructor; eauto.
              + simpl in HinterpPC. intros d1 d2 Hlt.
                destruct (nat_eq_dec d2 (length cs)).
                * subst d2. rewrite stack_cons_length.
                  intros. inv H1.
                  destruct (addr_eq_dec a2 a0).
                  { subst a0. destruct Hinterpdst as [? [? [XZ ?] ] ].
                    simpl in H0.
                    match goal with H: context [(if ?S then _ else _) = Some stk1] |- _ => destruct S as [G|_]; [clear -G Hlt; unfold Stackframe in G; lia|] end.
                    eapply XZ in H2; eauto.
                    clear -H2 Hconds2; solve_addr. }
                  rewrite lookup_insert_ne in H3; auto.
                  eapply Hstkdisj; eauto; [|rewrite stack_cons_length; auto].
                  simpl. simpl in H0. unfold Stackframe in *.
                  destruct (nat_eq_dec d1 (length cs)); [lia|auto].
                * intros. rewrite (stack_cons_length_ne) in H1; eauto.
                  generalize (proj1 (stack_is_Some _ _) ltac:(eexists; apply H1)).
                  intros XT. rewrite (stack_cons_length_ne) in H0; eauto; [|unfold Stackframe in *; lia].
                  eapply (Hstkdisj d1 d2 Hlt); eauto; rewrite stack_cons_length_ne; eauto.
                  unfold Stackframe in *. lia.
              + econstructor; eauto.
                * intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
                  { eexists; split; eauto.
                    apply interp_stack_extend.
                    destruct H8 as [-> | [-> | ->] ]; auto. }
                  destruct (Hregsdef rr) as [wrr [Hwrr Hinterprr] ].
                  eexists; split; eauto. apply interp_stack_extend; auto.
                * simpl in Hinterpdst. destruct Hinterpdst as [? [GG ?] ].
                  clear -Hstkdisjheap Hconds4 GG.
                  intro ax. destruct (addr_eq_dec a2 ax); [subst ax; intros; solve_addr|rewrite lookup_insert_ne; auto].
                * intros ax. destruct (addr_eq_dec a2 ax); [subst ax; rewrite !lookup_insert|rewrite !(lookup_insert_ne _ a2); auto].
                  { inversion 1; split; auto.
                    split; [apply interp_stack_extend; auto|].
                    rewrite /canBeStored /=. apply andb_true_iff in Hconds'.
                    destruct Hconds'. eapply canStoreU_canStoreU_URWLX; eauto. }
                  intros. apply Hstksim in H0. destruct H0 as [? [? ?] ].
                  do 2 (split; auto). apply interp_stack_extend; auto.
                * assert (XQC: forall d xstk, stack d cs = Some xstk -> forall ax, is_Some (xstk !! ax) -> (ax < a2)%a).
                  { destruct Hinterpdst as [W1 [W2 [W3 W4] ] ].
                    intros. eapply W3 in H1; eauto. clear -H1 Hconds2; solve_addr. }
                  eapply sim_cs_stack_extend; eauto.
              + intro rr; destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|rewrite !(lookup_insert_ne _ PC); auto].
              + intros. rewrite lookup_insert_ne; auto.
                assert (is_Some (h !! a)) by (eexists; eauto).
                apply elem_of_dom in H1.
                generalize (Hdisj _ H1). intro T.
                destruct Hinterpdst as [W1 [W2 ?] ].
                clear -Hconds4 T W2. solve_addr.
            - rewrite lookup_insert_ne in Hincrement1; auto.
              rewrite HPC in Hincrement1. destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              rewrite lookup_insert_ne in HXX; auto.
              generalize (Hsregs _ _ HPC). intros HPC'.
              rewrite HPC' in HXX; inv HXX.
              rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              + simpl in Hinterpdst. intros d1 d2 Hlt.
                destruct (nat_eq_dec d2 (length cs)).
                * subst d2. rewrite stack_cons_length.
                  intros. inv H1.
                  destruct (addr_eq_dec a2 a4).
                  { subst a4. destruct Hinterpdst as [? [? [XZ ?] ] ].
                    simpl in H0.
                    match goal with H: context [(if ?S then _ else _) = Some stk1] |- _ => destruct S as [G|_]; [clear -G Hlt; unfold Stackframe in G; lia|] end.
                    eapply XZ in H2; eauto.
                    clear -H2 Hconds2; solve_addr. }
                  rewrite lookup_insert_ne in H3; auto.
                  eapply Hstkdisj; eauto; [|rewrite stack_cons_length; auto].
                  simpl. simpl in H0. unfold Stackframe in *.
                  destruct (nat_eq_dec d1 (length cs)); [lia|auto].
                * intros. rewrite (stack_cons_length_ne) in H1; eauto.
                  generalize (proj1 (stack_is_Some _ _) ltac:(eexists; apply H1)).
                  intros XT. rewrite (stack_cons_length_ne) in H0; eauto; [|unfold Stackframe in *; lia].
                  eapply (Hstkdisj d1 d2 Hlt); eauto; rewrite stack_cons_length_ne; eauto.
                  unfold Stackframe in *. lia.
              + econstructor; eauto.
                * intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
                  { eexists; split; eauto.
                    apply interp_stack_extend.
                    destruct H8 as [-> | [-> | ->] ]; auto. }
                  destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert|rewrite lookup_insert_ne; auto].
                  { eexists; split; auto.
                    simpl. destruct Hinterpdst as [W1 [W2 [W3 W4] ] ].
                    do 3 (split; auto).
                    intros ax QQ.
                    destruct (addr_eq_dec a2 ax); [subst ax; rewrite lookup_insert; eauto|rewrite lookup_insert_ne; auto].
                    apply W4. simpl.
                    clear -QQ n2 Haa''. destruct p0; solve_addr. }
                  destruct (Hregsdef rr) as [wrr [Hwrr Hinterprr] ].
                  eexists; split; eauto. apply interp_stack_extend; auto.
                * simpl in Hinterpdst. destruct Hinterpdst as [? [GG ?] ].
                  clear -Hstkdisjheap Hconds4 GG.
                  intro ax. destruct (addr_eq_dec a2 ax); [subst ax; intros; solve_addr|rewrite lookup_insert_ne; auto].
                * intros ax. destruct (addr_eq_dec a2 ax); [subst ax; rewrite !lookup_insert|rewrite !(lookup_insert_ne _ a2); auto].
                  { inversion 1; split; auto.
                    split; [apply interp_stack_extend; auto|].
                    rewrite /canBeStored /=. apply andb_true_iff in Hconds'.
                    destruct Hconds'. eapply canStoreU_canStoreU_URWLX; eauto. }
                  intros. apply Hstksim in H0. destruct H0 as [? [? ?] ].
                  do 2 (split; auto). apply interp_stack_extend; auto.
                * assert (XQC: forall d xstk, stack d cs = Some xstk -> forall ax, is_Some (xstk !! ax) -> (ax < a2)%a).
                  { destruct Hinterpdst as [W1 [W2 [W3 W4] ] ].
                    intros. eapply W3 in H1; eauto. clear -H1 Hconds2; solve_addr. }
                  eapply sim_cs_stack_extend; eauto.
              + intro rr; destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|rewrite !(lookup_insert_ne _ PC); auto].
                destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|rewrite !lookup_insert_ne; auto].
              + intros. rewrite lookup_insert_ne; auto.
                assert (is_Some (h !! a)) by (eexists; eauto).
                apply elem_of_dom in H1.
                generalize (Hdisj _ H1). intro T.
                destruct Hinterpdst as [W1 [W2 ?] ].
                clear -Hconds4 T W2. solve_addr. } }
        { destruct (incrementPC reg1) as [reg1''|] eqn:Hincrement1; cycle 1.
          { destruct AA as [-> ->]. econstructor; eauto.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { intros _. eapply incrementPC_inv_Some in Hincrement1.
            rewrite HPC in Hincrement1.
            destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
            eapply rules_base.incrementPC_Some_inv in Hincrement2.
            destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
            generalize (Hsregs _ _ HPC). intros HPC'.
            rewrite HPC' in HXX; inv HXX.
            rewrite Hap1 in Hap1'; inv Hap1'.
            econstructor; eauto.
            + simpl in Hinterpdst. intros d1 d2 Hlt.
                destruct (nat_eq_dec d2 (length cs)).
                * subst d2. rewrite stack_cons_length.
                  intros. inv H1.
                  destruct (addr_eq_dec aa' a4).
                  { subst a4. destruct Hinterpdst as [? [? [XZ ?] ] ].
                    simpl in H0.
                    match goal with H: context [(if ?S then _ else _) = Some stk1] |- _ => destruct S as [G|_]; [clear -G Hlt; unfold Stackframe in G; lia|] end.
                    eapply XZ in H2; eauto.
                    clear -H2 Hconds2; solve_addr. }
                  rewrite lookup_insert_ne in H3; auto.
                  eapply Hstkdisj; eauto; [|rewrite stack_cons_length; auto].
                  simpl. simpl in H0. unfold Stackframe in *.
                  destruct (nat_eq_dec d1 (length cs)); [lia|auto].
                * intros. rewrite (stack_cons_length_ne) in H1; eauto.
                  generalize (proj1 (stack_is_Some _ _) ltac:(eexists; apply H1)).
                  intros XT. rewrite (stack_cons_length_ne) in H0; eauto; [|unfold Stackframe in *; lia].
                  eapply (Hstkdisj d1 d2 Hlt); eauto; rewrite stack_cons_length_ne; eauto.
                  unfold Stackframe in *. lia.
              + econstructor; eauto.
                * intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
                  { eexists; split; eauto.
                    apply interp_stack_extend.
                    destruct H8 as [-> | [-> | ->] ]; auto. }
                  destruct (Hregsdef rr) as [wrr [Hwrr Hinterprr] ].
                  eexists; split; eauto. apply interp_stack_extend; auto.
                * simpl in Hinterpdst. destruct Hinterpdst as [? [GG ?] ].
                  clear -Hstkdisjheap Hconds1 Hconds2 Hconds3 Hconds4 GG.
                  intro ax. destruct (addr_eq_dec aa' ax); [subst ax; intros; solve_addr|rewrite lookup_insert_ne; auto].
                * intros ax. destruct (addr_eq_dec aa' ax); [subst ax; rewrite !lookup_insert|rewrite !(lookup_insert_ne _ aa'); auto].
                  { inversion 1; split; auto.
                    split; [apply interp_stack_extend; auto|].
                    rewrite /canBeStored /=. apply andb_true_iff in Hconds'.
                    destruct Hconds'. eapply canStoreU_canStoreU_URWLX; eauto. }
                  intros. apply Hstksim in H0. destruct H0 as [? [? ?] ].
                  do 2 (split; auto). apply interp_stack_extend; auto.
                * assert (XQC: forall d xstk, stack d cs = Some xstk -> forall ax, is_Some (xstk !! ax) -> (ax < aa')%a).
                  { destruct Hinterpdst as [W1 [W2 [W3 W4] ] ].
                    intros. eapply W3 in H1; eauto. clear -H1 Hconds2; solve_addr. }
                  eapply sim_cs_stack_extend; eauto.
              + intro rr; destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; auto|rewrite !(lookup_insert_ne _ PC); auto].
              + intros. rewrite lookup_insert_ne; auto.
                assert (is_Some (h !! a)) by (eexists; eauto).
                apply elem_of_dom in H1.
                generalize (Hdisj _ H1). intro T.
                destruct Hinterpdst as [W1 [W2 ?] ].
                clear -Hconds1 Hconds2 Hconds3 Hconds4 T W2. solve_addr. } } }
    - (* PromoteU *)
      assert (AA: match reg1 !! dst with
                  | Some (inr (Regular (pp, gg, bb, ee, aa))) =>
                    if perm_eq_dec pp E then c1 = lang.Failed /\ c2 = Failed else
                    match incrementPC (<[dst:=inr (Regular (promote_perm pp, gg, bb, addr_reg.min aa ee, aa))]> reg1) with
                    | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inr (promote_perm pp, gg, bb, addr_reg.min aa ee, aa)]> reg2) = Some reg2' /\ mem2' = mem2
                    | None => c1 = lang.Failed /\ c2 = Failed
                    end
                  | Some (inr (Stk dd pp bb ee aa)) =>
                    if perm_eq_dec pp E then c1 = lang.Failed /\ c2 = Failed else
                    match incrementPC (<[dst:=inr (Stk dd (promote_perm pp) bb (addr_reg.min aa ee) aa)]> reg1) with
                    | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inr (promote_perm pp, Directed, bb, addr_reg.min aa ee, aa)]> reg2) = Some reg2' /\ mem2' = mem2
                    | None => c1 = lang.Failed /\ c2 = Failed
                    end
                  | _ => c1 = lang.Failed /\ c2 = Failed
                  end).
      { destruct (Hregsdef dst) as [wdst [Hwdst _] ].
        rewrite Hwdst. generalize (Hsregs _ _ Hwdst). intros Hwdst'.
        rewrite /= /base.RegLocate Hwdst in H1.
        rewrite /= /RegLocate Hwdst' in H2.
        destruct wdst; [simpl in H2; inv H1; inv H2; auto|].
        destruct (translate_word_cap c) as [c' Hc'].
        rewrite Hc' in H2. destruct c; [|inv Hc'|inv Hc'; inv H1; inv H2; auto].
        - destruct c as [ [ [ [pp gg] bb] ee] aa]. inv Hc'.
          destruct (perm_eq_dec pp E); [inv H1; inv H2; auto|].
          rewrite /base.update_reg /= in H1.
          rewrite /update_reg /= in H2.
          assert (exists w, (<[dst:=inr (Regular (promote_perm pp, gg, bb, addr_reg.min aa ee, aa))]> reg1) !! PC = Some w /\ (<[dst:=inr (promote_perm pp, gg, bb, addr_reg.min aa ee, aa)]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
          { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
            rewrite !lookup_insert_ne //. eauto. }
          destruct (incrementPC (<[dst:=inr (Regular (promote_perm pp, gg, bb, addr_reg.min aa ee, aa))]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
          + generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
            intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in H1.
            erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in H2.
            inv H1; inv H2; auto.
          + destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
            erewrite incrementPC_success_updatePC in H1; eauto.
            rewrite Hincrement2.
            eapply rules_base.incrementPC_success_updatePC in Hincrement2.
            destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
            instantiate (1 := mem2) in Z3.
            rewrite Z3 -Z4 in H2. inv H1; inv H2; repeat split; auto.
        - destruct (perm_eq_dec p0 E); [inv H1; inv H2; auto|].
          rewrite /base.update_reg /= in H1.
          rewrite /update_reg /= in H2.
          assert (exists w, (<[dst:=inr (Stk n (promote_perm p0) a0 (addr_reg.min a2 a1) a2)]> reg1) !! PC = Some w /\ (<[dst:=inr (promote_perm p0, Directed, a0, addr_reg.min a2 a1, a2)]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
          { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert; eauto|].
            rewrite !lookup_insert_ne //. eauto. }
          destruct (incrementPC (<[dst:=inr (Stk n (promote_perm p0) a0 (addr_reg.min a2 a1) a2)]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
          + generalize (incrementPC_fail_incrementPC' HY HZ Hincrement1).
            intros Hincrement2. erewrite (incrementPC_fail_updatePC _ _ _ Hincrement1) in H1.
            erewrite (rules_base.incrementPC_fail_updatePC _ _ Hincrement2) in H2.
            inv H1; inv H2; auto.
          + destruct (incrementPC_success_incrementPC' HY HZ Hincrement1) as [reg2'' Hincrement2].
            erewrite incrementPC_success_updatePC in H1; eauto.
            rewrite Hincrement2.
            eapply rules_base.incrementPC_success_updatePC in Hincrement2.
            destruct Hincrement2 as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
            instantiate (1 := mem2) in Z3.
            rewrite Z3 -Z4 in H2. inv H1; inv H2; repeat split; auto. }
      clear H1 H2. destruct (Hregsdef dst) as [wdst [Hwdst Hinterpdst] ].
      generalize (Hsregs _ _ Hwdst); intros Hwdst'.
      rewrite Hwdst in AA.
      generalize (Hsregs _ _ HPC); intros HPC'.
      destruct wdst.
      + destruct AA as [-> ->]. econstructor; eauto.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          repeat econstructor.
        * rewrite can_step_fill /can_step /=. intros [A | A]; discriminate.
      + destruct c; cycle 2.
        * destruct AA as [-> ->]. econstructor; eauto.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
        * destruct c as [ [ [ [pp gg] bb] ee] aa].
          destruct (perm_eq_dec pp E).
          { destruct AA as [-> ->]. econstructor; eauto.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (incrementPC (<[dst:=inr (Regular (promote_perm pp, gg, bb, addr_reg.min aa ee, aa))]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
          { destruct AA as [-> ->]. econstructor; eauto.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { intros _. eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|].
            - rewrite HPC in Hwdst; inv Hwdst.
            - rewrite lookup_insert_ne // HPC in Hincrement1.
              destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              rewrite lookup_insert_ne // in HXX.
              rewrite (Hsregs _ _ HPC) /= in HXX. inv HXX.
              rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              + econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|].
                * eexists; split; simpl; eauto.
                  destruct H8 as [-> | [-> | ->] ]; auto.
                * rewrite lookup_insert_ne //.
                  destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
                  eexists; split; eauto. destruct Hinterpdst; simpl; auto.
                  simpl in H0. split; [destruct pp; simpl in H0; simpl; try congruence; auto|].
                  intros. eapply H1; clear -H2; solve_addr.
              + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
                rewrite !(lookup_insert_ne _ PC) //.
                destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert|rewrite !lookup_insert_ne; auto].
                inversion 1; auto. }
        * destruct (perm_eq_dec p0 E).
          { destruct AA as [-> ->]. econstructor; eauto.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct (incrementPC (<[dst:=inr (Stk n (promote_perm p0) a0 (addr_reg.min a2 a1) a2)]> reg1)) as [reg1''|] eqn:Hincrement1; cycle 1.
          { destruct AA as [-> ->]. econstructor; eauto.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              repeat econstructor.
            - rewrite can_step_fill /can_step /=. intros [A | A]; discriminate. }
          destruct AA as [-> [-> [-> [-> [-> [-> [Hincrement2 ->] ] ] ] ] ] ].
          econstructor; eauto.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            repeat econstructor. }
          { intros _. eapply incrementPC_inv_Some in Hincrement1.
            destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hincrement1|].
            - rewrite HPC in Hwdst; inv Hwdst.
              destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              rewrite lookup_insert in HXX. inv HXX.
              rewrite Hap1 in Hap1'; inv Hap1'.
              rewrite !insert_insert.
              econstructor; eauto.
              + econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
                * eexists; split; simpl; eauto.
                  simpl. destruct HinterpPC as [? [? [HH ?] ] ]; simpl; auto.
                  split; auto. split; [clear -H1; solve_addr|].
                  split; auto.
                  intros; eapply H2. simpl. clear -H3.
                  destruct p0; simpl in H3; solve_addr.
              + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
                rewrite !(lookup_insert_ne _ PC) //. auto.
            - rewrite lookup_insert_ne // HPC in Hincrement1.
              destruct Hincrement1 as [ap1 [Hap1 [-> X1] ] ].
              eapply rules_base.incrementPC_Some_inv in Hincrement2.
              destruct Hincrement2 as [ppp [ggg [bbb [eee [aaa [aaa' [HXX [Hap1' [-> X2] ] ] ] ] ] ] ] ].
              rewrite lookup_insert_ne // in HXX.
              rewrite (Hsregs _ _ HPC) /= in HXX. inv HXX.
              rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              + econstructor; eauto. intros rr.
                destruct (reg_eq_dec PC rr); [subst rr; rewrite lookup_insert|].
                * eexists; split; simpl; eauto.
                  destruct H8 as [-> | [-> | ->] ]; auto.
                * rewrite lookup_insert_ne //.
                  destruct (reg_eq_dec dst rr); [subst rr; rewrite lookup_insert|rewrite lookup_insert_ne; auto].
                  eexists; split; eauto. destruct Hinterpdst as [? [? [HH ?] ] ]; simpl; auto.
                  split; auto. split; [clear -H1; solve_addr|].
                  split; auto.
                  intros; eapply H2. simpl. clear -H3.
                  destruct p0; simpl in H3; solve_addr.
              + intros rr. destruct (reg_eq_dec PC rr); [subst rr; rewrite !lookup_insert; inversion 1; simpl; auto|].
                rewrite !(lookup_insert_ne _ PC) //.
                destruct (reg_eq_dec dst rr); [subst rr; rewrite !lookup_insert|rewrite !lookup_insert_ne; auto].
                inversion 1; auto. }
  Qed.

  Lemma push_words_cons:
    forall w words m a m',
      push_words m a (w::words) = Some m' ->
      push_words m a (w::words) = push_words (<[a:=w]> m) ^(a + 1)%a words.
  Proof.
    intros. rewrite H0.
    rewrite /push_words /= in H0.
    destruct (lang.canStoreU URWLX a w).
    - rewrite -H0. reflexivity.
    - match goal with H: context [match ?X with _ => _ end] |- _ => assert (X = None) end.
      { clear. induction words.
        - reflexivity.
        - simpl. auto. }
      rewrite H1 in H0. inv H0.
  Qed.

  Lemma push_words_canStoreU:
    forall words m a m',
      push_words m a words = Some m' ->
      forall (i: nat) w, words !! i = Some w ->
        lang.canStoreU URWLX ^(a + i)%a w = true.
  Proof.
    induction words; intros.
    - simpl. rewrite lookup_nil in H1. inv H1.
    - destruct i.
      + simpl in H1. inv H1.
        replace ^(a0 + 0%nat)%a with a0 by (clear; solve_addr).
        rewrite /push_words /= in H0.
        destruct (lang.canStoreU URWLX a0 w); auto.
        match goal with H: context [match ?X with _ => _ end] |- _ => assert (X = None) end.
        { clear. induction words.
          - reflexivity.
          - simpl. auto. }
        rewrite H1 in H0; inv H0.
      + simpl in H1. erewrite push_words_cons in H0; eauto.
        replace ^(a0 + S i)%a with ^(^(a0 + 1) + i)%a by solve_addr.
        eapply IHwords; eauto.
  Qed.

  Lemma push_words_no_check_spec:
    forall l m a hi (Hhi: (^(a + length l) < hi)%a),
      forall a',
        ((a' < a)%a \/ (^(a + length l)%a <= a')%a) ->
        (push_words_no_check m a l).2 !! a' = m !! a'.
  Proof.
    induction l; intros.
    - simpl. reflexivity.
    - rewrite push_words_no_check_cons.
      erewrite IHl.
      + rewrite lookup_insert_ne; auto.
        destruct H0 as [X|X]; clear -X Hhi; simpl in X; try solve_addr.
      + instantiate (1 := hi).
        clear -Hhi; solve_addr.
      + destruct H0; [left; clear -H0; solve_addr|right; clear -H0 Hhi; solve_addr].
  Qed.

  Lemma push_words_lookup_spec:
    forall wlist m a e m',
      (^(a + length wlist)%a < e)%a ->
      push_words m a wlist = Some m' ->
      (forall (i: nat), i < length wlist ->
        m' !! ^(a + i)%a = wlist !! i) /\
      (forall a', ((a' < a)%a \/ (^(a + length wlist) <= a')%a) ->
        m' !! a' = m !! a').
  Proof.
    induction wlist; split.
    - intros. inv H2.
    - rewrite /push_words /= in H1. inv H1.
      intros. reflexivity.
    - intros. generalize (push_words_cons H1). intros X.
      destruct i.
      + simpl. rewrite X in H1. eapply IHwlist in H1; [|instantiate (1 := e); clear -H0; solve_addr].
        destruct H1. assert (^(a0 + 0%nat)%a = a0) as -> by (clear; solve_addr).
        rewrite H3; [rewrite lookup_insert //|left; clear - H0; solve_addr].
      + rewrite X in H1. assert (^(a0 + S i)%a = ^(^(a0 + 1) + i)%a) as -> by (clear -H0; solve_addr).
        eapply IHwlist in H1; [|instantiate (1 := e); clear -H0; solve_addr].
        simpl. destruct H1. apply H1. simpl in H2; lia.
    - intros. generalize (push_words_cons H1). intros X. rewrite X in H1.
      eapply IHwlist in H1; [|instantiate (1 := e); clear -H0; solve_addr].
      destruct H1. rewrite H3; [|destruct H2; [left; clear -H2; solve_addr|right; clear-H0 H2; solve_addr] ].
      rewrite lookup_insert_ne; auto. destruct H2; clear -H0 H2; solve_addr.
  Qed.

  Lemma push_words_no_check_in:
    forall l m a hi (Hhi: (^(a + length l) < hi)%a),
      forall i, i < length l ->
        (push_words_no_check m a l).2 !! ^(a + i)%a = l !! i.
  Proof.
    induction l; intros.
    - simpl in H0. exfalso. lia.
    - rewrite push_words_no_check_cons.
      destruct i.
      + simpl. erewrite push_words_no_check_spec.
        * replace ^(a0 + 0%nat)%a with a0 by solve_addr.
          rewrite lookup_insert //.
        * instantiate (1 := hi); clear -Hhi; solve_addr.
        * left. clear -Hhi; solve_addr.
      + simpl. erewrite <- IHl.
        * f_equal; auto. clear -Hhi; solve_addr.
        * instantiate (1 := hi). clear -Hhi; solve_addr.
        * simpl in H0; lia.
  Qed.

  Lemma rclear_spec:
    forall rlist pr gr br er ar ar_final reg mem
    (HisCorrectPC: isCorrectPC (inr (pr, gr, br, er, ar)))
    (Harfinal: (ar + (length rlist))%a = Some (ar_final))
    (Hlowar: (br <= ar)%a)
    (Hhiar: (ar_final < er)%a)
    (Hinstrs: forall i,
                i < (length rlist) ->
                exists ai, (ar + i)%a = Some ai /\
                mem !! ai = (translate_word <$> (call.rclear_instrs rlist)) !! i)
    (Hnotin: PC ∉ rlist),
    rtc erased_step
      ([Seq (Instr Executable)], (<[PC:=inr (pr, gr, br, er, ar)]> reg, mem))
      ([Seq (Instr Executable)], (<[PC:=inr (pr, gr, br, er, ar_final)]> (foldl (fun reg r => <[r:= inl 0%Z]> reg) reg rlist), mem)).
  Proof.
    induction rlist; intros.
    - simpl. simpl in Harfinal.
      assert (ar_final = ar) as -> by (clear -Harfinal; solve_addr).
      eapply rtc_refl.
    - simpl. eapply not_elem_of_cons in Hnotin.
      destruct Hnotin as [Hnotin1 Hnotin2].
      eapply rtc_transitive.
      + eapply rtc_transitive; eapply rtc_once.
        * econstructor. econstructor; eauto.
          { instantiate (2 := []). instantiate (3 := []). reflexivity. }
          { econstructor; eauto.
            - instantiate (2 := [SeqCtx]); reflexivity.
            - econstructor. eapply step_exec_instr.
              + rewrite /RegLocate /= lookup_insert //.
              + rewrite /RegLocate /= lookup_insert //.
              + rewrite /MemLocate /=. generalize (Hinstrs 0 ltac:(simpl; lia)).
                intros [a0 [Ha0 Hinstr0] ].
                assert (a0 = ar) as -> by (clear -Ha0; solve_addr).
                clear Ha0. rewrite Hinstr0. simpl.
                rewrite decode_encode_instr_inv. auto.
              + rewrite /= /update_reg /updatePC /RegLocate /= lookup_insert_ne; [|auto].
                rewrite lookup_insert.
                assert ((ar + 1)%a = Some ^(ar + 1)%a) as -> by (clear -Harfinal; solve_addr).
                inv HisCorrectPC. destruct H6 as [-> | [-> | ->] ]; auto. }
        * simpl; rewrite /update_reg /= (insert_commute _ a PC); auto.
          rewrite insert_insert. econstructor. econstructor; eauto.
          { instantiate (2:=[]); instantiate (3:=[]); reflexivity. }
          { econstructor; eauto.
            - instantiate (2 := []); reflexivity.
            - econstructor. }
      + simpl. simpl in Harfinal. eapply IHrlist; auto.
        * inv HisCorrectPC; econstructor; eauto.
          clear -Harfinal Hhiar H2; solve_addr.
        * clear -Harfinal; solve_addr.
        * clear -Hlowar; solve_addr.
        * intros i Hilt. generalize (Hinstrs (S i) ltac:(clear -Hilt; simpl; lia)).
          intros [ai [Hai Hinstri] ].
          exists ai. split; [clear -Hai Hilt Harfinal; solve_addr|].
          rewrite Hinstri; reflexivity.
  Qed.

  Lemma rclear_commute:
    forall rlist (reg: Reg) r w,
    r ∉ rlist ->
    (foldl (fun reg r => <[r:= inl 0%Z]> reg) (<[r:=w]> reg) rlist) = <[r:=w]> (foldl (fun reg r => <[r:= inl 0%Z]> reg) reg rlist).
  Proof.
    induction rlist; intros.
    - simpl. auto.
    - simpl. eapply not_elem_of_cons in H0.
      destruct H0. rewrite (insert_commute _ a r); auto.
  Qed.

  Lemma rclear_commute_erase:
    forall rlist (reg: Reg) r w,
    r ∈ rlist ->
    (foldl (fun reg r => <[r:= inl 0%Z]> reg) (<[r:=w]> reg) rlist) = (foldl (fun reg r => <[r:= inl 0%Z]> reg) reg rlist).
  Proof.
    induction rlist; intros.
    - inv H0.
    - simpl. destruct (reg_eq_dec r a).
      + subst r; rewrite insert_insert //.
      + eapply elem_of_cons in H0. destruct H0 as [-> | H0]; [elim n; auto|].
        rewrite insert_commute; auto.
  Qed.

  Lemma rclear_lookup_not_in:
    forall rlist (reg: Reg) r,
    r ∉ rlist ->
    (foldl (fun reg r => <[r:= inl 0%Z]> reg) reg rlist) !! r = reg !! r.
  Proof.
    induction rlist; intros.
    - simpl; auto.
    - eapply not_elem_of_cons in H0. destruct H0.
      simpl. rewrite IHrlist; auto.
      rewrite lookup_insert_ne; auto.
  Qed.

  Lemma rclear_lookup_in:
    forall rlist (reg: Reg) r,
    r ∈ rlist ->
    (foldl (fun reg r => <[r:= inl 0%Z]> reg) reg rlist) !! r = Some (inl 0%Z).
  Proof.
    induction rlist; intros.
    - inv H0.
    - eapply elem_of_cons in H0. destruct (elem_of_list_dec r rlist).
      + simpl. eapply IHrlist; auto.
      + destruct H0 as [H0|?]; [|elim n; auto].
        subst r. simpl. rewrite rclear_commute; auto.
        rewrite lookup_insert //.
  Qed.

  Inductive sim_val: lang.val -> val -> Prop :=
  | sim_val_halted:
      sim_val lang.HaltedV HaltedV
  | sim_val_failed:
      sim_val lang.FailedV FailedV
  | sim_val_next:
      sim_val lang.NextIV NextIV.

  Lemma sim_cs_call_preserve:
    forall cs h mem mem' bound
      (Hstkgood: forall a, (a < bound)%a -> mem' !! a = mem !! a)
      (Hcslt: forall d stk, stack d cs = Some stk -> forall a, is_Some (stk !! a) -> (a < bound)%a),
    sim_cs true h cs mem ->
    sim_cs true h cs mem'.
  Proof.
    induction cs; intros.
    - eapply sim_cs_nil.
    - inv H0; econstructor; eauto.
      + intros. generalize (Hstksim _ _ H0).
        intros. destruct H1 as [? [? ?] ].
        split; auto. rewrite Hstkgood; auto.
        eapply Hcslt; [|eexists; exact H0].
        instantiate (1 := length cs).
        rewrite stack_cons_length //.
      + eapply IHcs; eauto.
        intros. generalize (proj1 (stack_is_Some _ _) ltac:(eexists; eapply H0)).
        intros. eapply (Hcslt d); eauto.
        rewrite /stack. destruct (nat_eq_dec d (length cs)); [lia|].
        fold stack; auto.
  Qed.

  Lemma all_registers_list_difference_length:
    length (list_difference all_registers [PC; call.r_stk]) = 31.
  Proof. reflexivity. Qed.

  Lemma exec_call:
   forall
      (c: overlay_component)
      (H0: is_program e_stk nat nat_eq_dec nat_countable base.Word lang.can_address_only lang.pwlW lang.is_global c)
      (reg1: base.Reg)
      (h stk: base.Mem)
      (cs: list Stackframe)
      (reg2: Reg)
      (mem2: Mem)
      (σ2: language.state overlay_lang)
      (Hstkdisj: ∀ d1 d2 : nat,
                  d1 < d2
                  → ∀ stk1 stk2 : base.Mem,
                      stack d1 ((reg1, stk) :: cs) = Some stk1
                      → stack d2 ((reg1, stk) :: cs) = Some stk2
                        → ∀ a1 a2 : Addr,
                            is_Some (stk1 !! a1) → is_Some (stk2 !! a2) → (a1 < a2)%a)
      (Hcswf: sim_cs false h ((reg1, stk) :: cs) mem2)
      (Hsregs: ∀ (r : RegName) (w : base.Word),
                reg1 !! r = Some w → reg2 !! r = Some (translate_word w))
      (Hsh: ∀ (a : Addr) (w : base.Word),
              h !! a = Some w
              → mem2 !! a = Some (translate_word w)
                ∧ lang.pwlW w = false
                  ∧ lang.is_global w = true ∧ lang.can_address_only w (dom (gset Addr) h))
      (Hdisj: ∀ a : Addr, a ∈ dom (gset Addr) h → (e_stk <= a)%a)
      (p: Perm)
      (g: Locality)
      (b e a: Addr)
      (rf: RegName)
      (rargs: list RegName)
      (H5: base.RegLocate reg1 PC = inr (Regular (p, g, b, e, a)))
      (H6: lang.isCorrectPC (base.RegLocate reg1 PC))
      (H7: is_call reg1 rf rargs (base.mem (reg1, h, stk, cs)) a e)
      (H8: depth_of (base.RegLocate reg1 call.r_stk) =
          Some (length (callstack (reg1, h, stk, cs))))
      (H9: exec_call (reg1, h, stk, cs) rf rargs p g b e a = (lang.NextI, σ2)),
      ∃ s2' : cfg cap_lang,
        tc erased_step ([Seq (Instr Executable)], (reg2, mem2)) s2'
        ∧ sim ([fill [lang.SeqCtx] (lang.Instr lang.NextI)], σ2) s2'.
  Proof. Local Opaque all_registers.
    intros.
    simpl in H5, H6. rewrite /base.mem /base.reg in H7.
    rewrite /base.reg /= in H8.
    set (d := length cs). inv Hcswf.
    destruct (Hregsdef call.r_stk) as [wstk [Hwstk Hinterpwstk] ].
    rewrite /base.RegLocate Hwstk in H8.
    destruct wstk; simpl in H8; try congruence.
    destruct c0; try congruence. inv H8.
    destruct H7 as [pca' [HrfnePC [Hrfnerstk [Hner0 [Hner1 [Hner2 [Hpcaeq' [Hpcalt' [Hcode Hreasonable] ] ] ] ] ] ] ] ].
    eapply not_elem_of_cons in HrfnePC. destruct HrfnePC as [HrfnePC HrfnePC'].
    eapply not_elem_of_cons in Hrfnerstk. destruct Hrfnerstk as [Hrfnerstk Hrfnerstk'].
    rewrite /base.RegLocate in H5.
    destruct (Hregsdef PC) as [wpc [HPC HinterpPC] ].
    rewrite HPC in H5; inv H5.
    generalize (Hsregs _ _ HPC). intros HPC'.
    rewrite /base.RegLocate HPC in H6.
    assert (Hgnotmono: g <> Directed).
    { intro X; rewrite /exec_call X in H9. inv H9. }
    rewrite /exec_call /base.RegLocate Hwstk in H9.
    assert (Hstkrange1: (a0 < a2)%a).
    { destruct (Addr_lt_dec a0 a2); destruct g; auto; try congruence;
      destruct p0; inv H9. }
    assert (p0 = URWLX) as ->.
    { destruct g; try congruence; destruct p0; auto; inv H9. }
    destruct (Addr_lt_dec a0 a2) as [_|X]; [|elim X; auto].
    destruct ((a2 + (100 + length rargs))%a) as [astkend|] eqn:Hastkend; [|destruct g; try congruence; inv H9].
    rewrite call.call_instrs_length in H9; auto.
    replace ((a + (141 + length rargs)%nat)%a) with (Some pca') in H9 by (clear -Hpcaeq'; solve_addr).
    destruct (Addr_le_dec astkend a1) as [Hrange2|?]; [|destruct g; try congruence; inv H9].
    rewrite /base.stk in H9.
    match goal with H: context [push_words stk a2 ?X]|- _ => set (saved_words := X) end.
    fold saved_words in H9.
    destruct (push_words stk a2 saved_words) as [saved_stk|] eqn:Hsaved_stk; [|destruct g; inv H9].
    match goal with H: context [push_words _ _ ?X]|- _ => set (wretargs := X) end.
    fold wretargs in H9.
    destruct (push_words ∅ ^(a2 + 99)%a wretargs) as [new_stk|] eqn:Hnew_stk; [|destruct g; inv H9].
    rewrite /base.mem /base.reg /callstack in H9.
    destruct (Hregsdef rf) as [wrf [Hwrf Hinterpwrf] ].
    rewrite Hwrf in H9. assert ((lang.NextI,
        (<[PC:=lang.updatePcPerm wrf]>
           (<[call.r_stk:=inr
                            (Stk (length cs + 1) URWLX ^
                               (a2 + 99)%a a1 ^(Some astkend)%a)]>
              (<[rf:=wrf]>
                 (gset_to_gmap (inl 0%Z) (list_to_set all_registers)))),
        h, new_stk,
        (<[PC:=inr (Regular (p, g, b, e, pca'))]>
           (<[call.r_stk:=inr (Stk (length cs) URWLX a0 a1 ^(a2 + 1)%a)]>
              reg1), clear_stk saved_stk ^(a2 + 99)%a) :: cs)) = (lang.NextI, σ2)) by (destruct g; try congruence; auto).
    clear H9. revert H1; intro H9.
    simpl. destruct (push_words_no_check (<[a2:=inl 0%Z]> mem2) ^(a2 + 1)%a (map (λ w : Z + RegName, translate_word (word_of_argument reg1 w)) (map inr (list_difference all_registers [PC; call.r_stk])))) as [aa mem2'] eqn:Hpush1.
    destruct ((push_words_no_check (<[^(a2 + 32)%a:=inr (URWLX, Directed, a0, a1, ^(a2 + 32)%a)]> mem2') ^(a2 + 33)%a (map (λ w : Z + RegName, translate_word (word_of_argument reg1 w)) ([inl (encodeInstr (Mov (R 1 eq_refl) (inr PC))); inl (encodeInstr (Lea (R 1 eq_refl) (inl (-1)%Z))); inl (encodeInstr (Load call.r_stk (R 1 eq_refl)))] ++ map inl call.pop_env_instrs ++ [inl (encodeInstr (LoadU PC call.r_stk (inl (-1)%Z)))])))) as [ab mem2''] eqn:Hpush2.
    destruct (push_words_no_check (<[^(a2 + 99)%a:=inr (E, Directed, a0, ^(a2 + 99)%a, ^(a2 + 33)%a)]> (<[a2:=inr (p, g, b, e, ^(a + (140 + length rargs))%a)]> mem2'')) ^(a2 + 100)%a (map (λ r : RegName, translate_word (base.RegLocate reg1 r)) rargs)) as [ac mem2'''] eqn:Hpush3.
    set (final_state := ([Seq (Instr NextI)], (<[PC:=updatePcPerm (translate_word wrf)]> (<[call.r_stk:=inr (URWLX, Directed, ^(a2 + 99)%a, a1, ^(Some astkend)%a)]> (<[rf:=translate_word wrf]> (gset_to_gmap (inl 0%Z) (list_to_set all_registers)))), mem2'''))).
    exists final_state. split.
    { eapply tc_rtc_r.
      - eapply tc_once. econstructor. econstructor.
        + instantiate (2 := []). instantiate (3 := []). rewrite app_nil_l. reflexivity.
        + reflexivity.
        + econstructor; eauto.
          * instantiate (2 := [SeqCtx]); reflexivity.
          * econstructor. eapply step_exec_instr.
            { rewrite /RegLocate HPC' /= //. }
            { rewrite /RegLocate HPC' /= //. inv H6; econstructor; eauto. }
            { destruct (Hcode 0 ltac:(lia)) as [ap0 [Hap0 Hinstr0] ].
              assert (ap0 = a) as -> by (clear -Hap0; solve_addr).
              simpl in Hinstr0. symmetry in Hinstr0.
              generalize (Hsh _ _ Hinstr0). intros [Hinstr0' _].
              rewrite /MemLocate Hinstr0' /= decode_encode_instr_inv //. }
            { simpl. generalize (Hsregs _ _ Hwstk). intros Hwstk'.
              rewrite /RegLocate Hwstk' /=.
              replace (a2 + 0)%a with (Some a2) by (clear; solve_addr).
              destruct (Addr_le_dec a0 a2) as [_|X]; [|elim X; clear -Hstkrange1; solve_addr].
              destruct (Addr_le_dec a2 a2) as [_|X]; [|elim X; clear; solve_addr].
              destruct (Addr_lt_dec a2 a1) as [_|X]; [|elim X; clear -Hastkend Hrange2; solve_addr].
              destruct (addr_eq_dec a2 a2) as [_|X]; [|elim X; clear; solve_addr].
              assert ((a2 + 1)%a = Some ^(a2 + 1)%a) as -> by (clear -Hastkend; solve_addr).
              rewrite /update_mem /update_reg /updatePC /=.
              rewrite /RegLocate lookup_insert_ne; [|auto].
              rewrite HPC' /=. replace ((a + 1)%a) with (Some ^(a + 1)%a) by (clear -Hpcaeq'; solve_addr).
              inv H6. destruct H8 as [-> | [-> | ->] ]; auto. }
      - simpl. eapply rtc_l.
        { econstructor. econstructor; eauto.
          - instantiate (2 := []). instantiate (3 := []). rewrite app_nil_l. reflexivity.
          - econstructor; eauto.
            + instantiate (2 := []). reflexivity.
            + econstructor. }
        assert (Ha1b: (a1 <= b)%a).
        { simpl in HinterpPC. destruct HinterpPC as [A B].
          generalize (B b ltac:(clear -H6; inv H6; solve_addr)). intro C.
          generalize (Hdisj _ C). intros.
          simpl in Hinterpwstk. destruct Hinterpwstk as [? [X ?] ].
          clear -X H1; solve_addr. }
        rewrite /update_reg /=. eapply rtc_transitive.
        { eapply rtc_transitive.
          - eapply push_env_instrs_spec with (reg1 := reg1) (wlist := map inr (list_difference all_registers [PC; call.r_stk])); auto.
            + eapply isCorrectPC_translate_word in H6.
              simpl in H6. inv H6. econstructor; eauto.
              clear -Hpcaeq' Hpcalt' H3. solve_addr.
            + rewrite map_length /=.
              instantiate (1 := ^(a2 + 32)%a).
              rewrite all_registers_list_difference_length.
              clear -Hastkend; solve_addr.
            + clear -Hstkrange1; solve_addr.
            + clear -Hastkend Hrange2; solve_addr.
            + rewrite map_length /=.
              instantiate (1 := ^(a + 32)%a).
              rewrite all_registers_list_difference_length.
              clear -Hpcaeq' Hpcalt'. solve_addr.
            + inv H6. clear -H3; solve_addr.
            + clear -Hpcaeq' Hpcalt'. solve_addr.
            + intros i Hi. rewrite map_length /= in Hi.
              rewrite all_registers_list_difference_length in Hi.
              generalize (Hcode (S i) ltac:(clear -Hi; lia)).
              intros [ai [Hai Hinstri] ].
              exists ai. split.
              * clear -Hai Hpcaeq'; solve_addr.
              * rewrite /call.call_instrs lookup_app_l in Hinstri; [|rewrite call.call_instrs_prologue_length; lia].
                rewrite /call.call_instrs_prologue lookup_app_r in Hinstri; [|simpl; lia].
                simpl length in Hinstri.
                replace (S i - 1) with i in Hinstri by lia.
                rewrite lookup_app_l in Hinstri; [|rewrite call.push_env_instrs_length; lia].
                unfold call.push_env_instrs in Hinstri.
                rewrite list_lookup_fmap. rewrite Hinstri.
                rewrite list_lookup_lookup_total_lt in Hinstri; [|rewrite map_length /=; auto].
                destruct (Hsh ai _ ltac:(eauto)) as [X1 X2].
                rewrite -Hinstri lookup_insert_ne.
                rewrite X1 //.
                generalize (Hdisj ai ltac:(eapply elem_of_dom; eexists; eauto)).
                simpl in Hinterpwstk. destruct Hinterpwstk as [? [X ?] ].
                clear -Hastkend Hrange2 X. solve_addr.
            + intros. destruct (Hregsdef r) as [wrr [Hwrr ?] ]. eauto.
            + intros. generalize (lookup_lt_Some _ _ _ H1). intros D.
              rewrite map_length /= in D.
              generalize (push_words_canStoreU Hsaved_stk). intros X.
              replace ^(^(a2 + 1) + i)%a with ^(a2 + S i)%a by (clear; solve_addr).
              eapply (X (S i) (word_of_argument reg1 wi)).
              unfold saved_words. rewrite lookup_app_r; [|simpl; lia].
              simpl length. replace (S i - 1) with i by lia.
              rewrite /base.reg.
              rewrite lookup_app_l; [|rewrite map_length /=; auto].
              erewrite list_lookup_fmap in H1.
              erewrite list_lookup_fmap.
              destruct (list_difference all_registers [PC; call.r_stk] !! i).
              { inv H1. simpl. auto. }
              { inv H1. }
            + split.
              * intro X. eapply elem_of_list_fmap in X.
                destruct X as [y [Hy1 Hy] ]. inv Hy1.
                eapply elem_of_list_difference in Hy. destruct Hy.
                eapply H2. eapply elem_of_cons. left; auto.
              * intro X. eapply elem_of_list_fmap in X.
                destruct X as [y [Hy1 Hy] ]. inv Hy1.
                eapply elem_of_list_difference in Hy. destruct Hy.
                eapply H2. eapply elem_of_cons. right.
                eapply elem_of_list_singleton. auto.
          - eapply rtc_refl. }
        rewrite Hpush1 /=.
        eapply rtc_transitive.
        { eapply rtc_l; [|eapply rtc_once].
          - econstructor. econstructor; eauto.
            + instantiate (2 := []). instantiate (3 := []). reflexivity.
            + econstructor; eauto.
              * instantiate (2 := [SeqCtx]). reflexivity.
              * econstructor. eapply step_exec_instr.
                { rewrite /RegLocate lookup_insert //. }
                { rewrite /RegLocate lookup_insert. inv H6; econstructor; eauto.
                  clear -H3 Hpcaeq' Hpcalt'. solve_addr. }
                { rewrite /cap_lang.mem /MemLocate /=.
                  assert (mem2' !! ^(a + 32)%a = (<[a2:=inl 0%Z]> mem2) !! ^(a + 32)%a).
                  { replace mem2' with (aa, mem2').2 by reflexivity.
                    rewrite -Hpush1. eapply push_words_no_check_spec.
                    - rewrite map_length /=. instantiate (1 := a1).
                      rewrite map_length all_registers_list_difference_length.
                      clear -Hastkend Hrange2. solve_addr.
                    - right; rewrite !map_length all_registers_list_difference_length.
                      clear -Hastkend Hrange2 Ha1b H6. inv H6; solve_addr. }
                  rewrite H1 lookup_insert_ne; [|clear -Hastkend Hrange2 Ha1b H6; inv H6; solve_addr].
                  destruct (Hcode 32 ltac:(lia)) as [ap32 [Hap32 Hinstr32] ].
                  rewrite /call.call_instrs lookup_app_l in Hinstr32; [|rewrite call.call_instrs_prologue_length; lia].
                  rewrite /call.call_instrs_prologue lookup_app_r in Hinstr32; [|simpl; lia].
                  rewrite lookup_app_r in Hinstr32; [|rewrite call.push_env_instrs_length; simpl; lia].
                  rewrite call.push_env_instrs_length lookup_app_l in Hinstr32; [|simpl; lia].
                  simpl in Hinstr32. destruct (Hsh _ _ ltac:(symmetry; apply Hinstr32)) as [Hinstr32' _].
                  assert (ap32 = ^(a + 32)%a) as -> by (clear -Hap32; solve_addr).
                  rewrite Hinstr32'. simpl. rewrite decode_encode_instr_inv. reflexivity. }
                { rewrite /exec /RegLocate (lookup_insert_ne _ PC call.r_stk); [|auto].
                  rewrite lookup_insert /z_of_argument.
                  assert (verify_access (StoreU_access a0 a1 ^(a2 + 32)%a 0) = Some ^(a2 + 32)%a) as ->.
                  { rewrite /=. assert ((^(a2 + 32) + 0)%a = Some ^(a2 + 32)%a) as -> by (clear; solve_addr).
                    destruct (Addr_le_dec ^(a2 + 32)%a ^(a2 + 32)%a) as [_|X]; [|elim X; clear; solve_addr].
                    destruct (Addr_le_dec a0 ^(a2 + 32)%a) as [_|X]; [|elim X; clear -Hstkrange1; solve_addr].
                    destruct (Addr_lt_dec ^(a2 + 32)%a a1) as [_|X]; auto.
                    elim X. clear -Hrange2 Hastkend. solve_addr. }
                  destruct (addr_eq_dec ^(a2 + 32)%a ^(a2 + 32)%a) as [_|X]; [|elim X; reflexivity].
                  rewrite /isU /canStoreU /pwlU /canReadUpTo /andb.
                  rewrite (proj2 (leb_addr_spec _ _)); [|clear; solve_addr].
                  assert ((^(a2 + 32) + 1)%a = Some ^(a2 + 33)%a) as -> by (clear -Hastkend; solve_addr).
                  rewrite /update_reg /update_mem /reg /cap_lang.mem /fst /snd.
                  rewrite (insert_commute _ call.r_stk PC); [|auto].
                  rewrite insert_insert /updatePC /RegLocate lookup_insert.
                  assert ((^(a + 32) + 1)%a = Some ^(a + 33)%a) as -> by (clear -Hpcaeq' Hpcalt'; solve_addr).
                  rewrite /update_reg /cap_lang.mem /snd insert_insert.
                  inv H6. destruct H8 as [-> | [-> | ->] ]; auto. }
          - simpl app. econstructor. econstructor; eauto.
            + instantiate (2 := []). instantiate (3 := []). reflexivity.
            + econstructor; eauto.
              * instantiate (2 := []). reflexivity.
              * econstructor. }
        simpl app. eapply rtc_transitive.
        { eapply push_env_instrs_spec with (wlist := [inl (encodeInstr (Mov (R 1 eq_refl) (inr PC))); inl (encodeInstr (Lea (R 1 eq_refl) (inl (- 1)%Z))); inl (encodeInstr (Load call.r_stk (R 1 eq_refl)))] ++ List.map inl call.pop_env_instrs ++ [ inl (encodeInstr (LoadU PC call.r_stk (inl (- 1)%Z)))]); auto.
          - inv H6; econstructor; eauto.
            clear -H3 Hpcaeq' Hpcalt'; solve_addr.
          - rewrite !app_length map_length call.pop_env_instrs_length /=.
            instantiate (1 := ^(a2 + 99)%a).
            clear -Hastkend Hstkrange1. solve_addr.
          - clear -Hstkrange1; solve_addr.
          - clear -Hastkend Hrange2; solve_addr.
          - rewrite !app_length map_length call.pop_env_instrs_length /=.
            instantiate (1 := ^(a + 99)%a).
            clear -Hpcaeq' Hpcalt'; solve_addr.
          - inv H6; clear -H3; solve_addr.
          - inv H6; clear -H3 Hpcaeq' Hpcalt'; solve_addr.
          - intros i Hilt.
            rewrite !app_length map_length call.pop_env_instrs_length /= in Hilt.
            generalize (Hcode (33 + i) ltac:(clear -Hilt; lia)). intros [ai [Hai Hinstri] ].
            exists ai. split; [clear -Hai Hpcaeq'; solve_addr|].
            rewrite /call.call_instrs lookup_app_l in Hinstri; [|rewrite call.call_instrs_prologue_length; lia].
            rewrite /call.call_instrs_prologue 2!app_assoc lookup_app_r in Hinstri; [|rewrite !app_length call.push_env_instrs_length /=; lia].
            rewrite !app_length call.push_env_instrs_length in Hinstri.
            simpl length in Hinstri. replace ((33 + i - (1 + 31 + 1))) with i in Hinstri by lia.
            rewrite lookup_app_l in Hinstri; [|rewrite call.push_instrs_length !app_length map_length call.pop_env_instrs_length /=; lia].
            rewrite list_lookup_fmap Hinstri.
            assert (WW: is_Some (h !! ai)).
            { rewrite -Hinstri. apply lookup_lt_is_Some_2.
              rewrite call.push_instrs_length !app_length map_length call.pop_env_instrs_length /=; auto. }
            destruct WW as [wwai Hwwai].
            rewrite lookup_insert_ne; [|clear -Hai Hastkend Hstkrange1 H6 Ha1b Hrange2; inv H6; solve_addr].
            replace (mem2') with (aa, mem2').2 by reflexivity.
            rewrite -Hpush1. erewrite push_words_no_check_spec.
            + rewrite lookup_insert_ne; [|clear -Hai Hastkend Hstkrange1 H6 Ha1b Hrange2; inv H6; solve_addr].
              rewrite -Hinstri. generalize (Hsh _ _ Hwwai).
              intros [-> _]. rewrite Hinstri Hwwai. reflexivity.
            + instantiate (1 := a1).
              rewrite !map_length all_registers_list_difference_length.
              clear -Hastkend Hrange2. solve_addr.
            + right. rewrite !map_length all_registers_list_difference_length.
              clear -Hai Hastkend Hstkrange1 H6 Ha1b Hrange2; inv H6; solve_addr.
          - instantiate (1 := reg1). intros r _ _.
            destruct (Hregsdef r) as [xz [? _] ]; eauto.
          - intros; eapply Hsregs; eauto.
          - intros. assert (exists wni, wi = inl wni) as [wni ->]; simpl; auto.
            clear -H1; destruct (nat_lt_dec i 3).
            { rewrite lookup_app_l in H1; [|simpl; auto].
              destruct i; [simpl in H1; inv H1; eauto|].
              destruct i; [simpl in H1; inv H1; eauto|].
              destruct i; simpl in H1; inv H1; eauto. }
            destruct (nat_lt_dec i 65).
            { rewrite lookup_app_r in H1; [|simpl; lia].
              rewrite lookup_app_l in H1; [|rewrite map_length call.pop_env_instrs_length /=; lia].
              erewrite list_lookup_fmap in H1.
              simpl length in H1. destruct (call.pop_env_instrs !! (i - 3)); inv H1; eauto. }
            rewrite lookup_app_r in H1; [|simpl; lia].
            rewrite lookup_app_r in H1; [|rewrite map_length call.pop_env_instrs_length /=; lia].
            eapply elem_of_list_lookup_2 in H1.
            eapply elem_of_cons in H1.
            destruct H1 as [X|X]; inv X; eauto.
          - assert (forall i (wi: Z + RegName), ([inl (encodeInstr (Mov (R 1 eq_refl) (inr PC))); inl (encodeInstr (Lea (R 1 eq_refl) (inl (-1)%Z))); inl (encodeInstr (Load call.r_stk (R 1 eq_refl)))] ++ map inl call.pop_env_instrs ++ [inl (encodeInstr (LoadU PC call.r_stk (inl (-1)%Z)))]) !! i = Some wi -> exists wni, wi = inl wni).
            { intros i wi H1.
              clear -H1; destruct (nat_lt_dec i 3).
              { rewrite lookup_app_l in H1; [|simpl; auto].
                destruct i; [simpl in H1; inv H1; eauto|].
                destruct i; [simpl in H1; inv H1; eauto|].
                destruct i; simpl in H1; inv H1; eauto. }
              destruct (nat_lt_dec i 65).
              { rewrite lookup_app_r in H1; [|simpl; lia].
                rewrite lookup_app_l in H1; [|rewrite map_length call.pop_env_instrs_length /=; lia].
                erewrite list_lookup_fmap in H1.
                simpl length in H1. destruct (call.pop_env_instrs !! (i - 3)); inv H1; eauto. }
              rewrite lookup_app_r in H1; [|simpl; lia].
              rewrite lookup_app_r in H1; [|rewrite map_length call.pop_env_instrs_length /=; lia].
              eapply elem_of_list_lookup_2 in H1.
              eapply elem_of_cons in H1.
              destruct H1 as [X|X]; inv X; eauto. }
            split; intro X; eapply elem_of_list_lookup in X; destruct X as [i X]; eapply H1 in X; destruct X as [? X]; inv X. }
         rewrite Hpush2. simpl.
         assert (Hmem2'': forall xa, (a1 <= xa)%a -> mem2'' !! xa = mem2 !! xa).
         { intros xa Hxa. replace mem2'' with (ab, mem2'').2 by reflexivity.
           rewrite -Hpush2. erewrite push_words_no_check_spec; [|rewrite !map_length !app_length map_length call.pop_env_instrs_length /=..].
           2: { instantiate (1 := a1). clear -Hastkend Hrange2. solve_addr. }
           2: { right. clear -Hastkend Hrange2 Hxa. solve_addr. }
           rewrite lookup_insert_ne; [|clear -Hastkend Hrange2 Hxa; solve_addr].
           replace mem2' with (aa, mem2').2 by reflexivity.
           rewrite -Hpush1. erewrite push_words_no_check_spec; [|rewrite !map_length /=..].
           2: { instantiate (1 := a1). clear -Hastkend Hrange2.
                rewrite all_registers_list_difference_length. solve_addr. }
           2: { right. clear -Hastkend Hrange2 Hxa.
                rewrite all_registers_list_difference_length. solve_addr. }
           rewrite lookup_insert_ne; [auto|clear -Hastkend Hrange2 Hxa; solve_addr]. }
         eapply rtc_transitive.
         { eapply rtc_l; [|eapply rtc_once].
           - econstructor. econstructor; eauto.
             + instantiate (2 := []); instantiate (3 := []); reflexivity.
             + econstructor; eauto.
               * instantiate (2 := [SeqCtx]); reflexivity.
               * econstructor. eapply step_exec_instr.
                 { rewrite /RegLocate /= lookup_insert //. }
                 { rewrite /RegLocate /= lookup_insert. inv H6; econstructor; eauto.
                   clear -H3 Hpcaeq' Hpcalt'; solve_addr. }
                 { rewrite /MemLocate /=. erewrite Hmem2''; [|clear -Hastkend Hrange2 Ha1b H6; inv H6; solve_addr].
                   generalize (Hcode 99 ltac:(lia)). intros [ap99 [Hap99 Hinstr99] ].
                   rewrite /call.call_instrs lookup_app_l in Hinstr99; [|rewrite call.call_instrs_prologue_length; lia].
                   rewrite /call.call_instrs_prologue 3!app_assoc lookup_app_r in Hinstr99; [|rewrite !app_length map_length !call.push_instrs_length !app_length !map_length call.pop_env_instrs_length all_registers_list_difference_length /=; lia].
                   rewrite !app_length map_length !call.push_instrs_length !app_length !map_length call.pop_env_instrs_length all_registers_list_difference_length /= in Hinstr99.
                   generalize (Hsh _ _ ltac:(symmetry; apply Hinstr99)).
                   intros [Hinstr99' _]. assert (ap99 = ^(a + 99)%a) as -> by (clear -Hap99; solve_addr).
                   rewrite Hinstr99'.
                   rewrite /= decode_encode_instr_inv //. }
                 { rewrite /exec /= /RegLocate lookup_insert /update_reg /updatePC /=.
                   rewrite /RegLocate lookup_insert_ne; [|auto].
                   rewrite lookup_insert /update_reg /= (insert_commute _ (R 1 _) PC); [|auto].
                   assert ((^(a + 99) + 1)%a = Some (^(a + 100)%a)) as -> by (clear -Hpcaeq'; solve_addr).
                   rewrite insert_insert.
                   inv H6. destruct H8 as [-> | [-> | ->] ]; auto. }
           - simpl. econstructor. econstructor; eauto.
             + instantiate (2 := []). instantiate (3 := []). reflexivity.
             + econstructor; eauto.
               * instantiate (2 := []). reflexivity.
               * econstructor. }
         simpl. eapply rtc_transitive.
         { eapply rtc_l; [|eapply rtc_once].
           - econstructor. econstructor; eauto.
             + instantiate (2 := []); instantiate (3 := []); reflexivity.
             + econstructor; eauto.
               * instantiate (2 := [SeqCtx]); reflexivity.
               * econstructor. eapply step_exec_instr.
                 { rewrite /RegLocate /= lookup_insert //. }
                 { rewrite /RegLocate /= lookup_insert. inv H6; econstructor; eauto.
                   clear -H3 Hpcaeq' Hpcalt'; solve_addr. }
                 { rewrite /MemLocate /=. erewrite Hmem2''; [|clear -Hastkend Hrange2 Ha1b H6; inv H6; solve_addr].
                   generalize (Hcode 100 ltac:(lia)). intros [ap99 [Hap99 Hinstr99] ].
                   rewrite /call.call_instrs lookup_app_l in Hinstr99; [|rewrite call.call_instrs_prologue_length; lia].
                   rewrite /call.call_instrs_prologue 3!app_assoc lookup_app_r in Hinstr99; [|rewrite !app_length map_length !call.push_instrs_length !app_length !map_length call.pop_env_instrs_length all_registers_list_difference_length /=; lia].
                   rewrite !app_length map_length !call.push_instrs_length !app_length !map_length call.pop_env_instrs_length /= in Hinstr99.
                   generalize (Hsh _ _ ltac:(symmetry; apply Hinstr99)).
                   intros [Hinstr99' _]. assert (ap99 = ^(a + 100)%a) as -> by (clear -Hap99; solve_addr).
                   rewrite Hinstr99'.
                   rewrite /= decode_encode_instr_inv //. }
                 { rewrite /exec /= /RegLocate lookup_insert_ne; [|auto].
                   rewrite lookup_insert /update_reg /=.
                   assert ((^(a + 99) + (41 + length rargs))%a = Some ^(a + (140 + length rargs))%a) as -> by (clear -Hpcaeq'; solve_addr).
                   rewrite (insert_commute _ (R 1 _) PC); [|auto].
                   rewrite insert_insert.
                   rewrite /updatePC /RegLocate lookup_insert /=.
                   assert ((^(a + 100) + 1)%a = Some (^(a + 101)%a)) as -> by (clear -Hpcaeq'; solve_addr).
                   rewrite /update_reg insert_insert /=.
                   inv H6. destruct H8 as [-> | [-> | ->] ]; auto. }
           - simpl. econstructor. econstructor; eauto.
             + instantiate (2 := []). instantiate (3 := []). reflexivity.
             + econstructor; eauto.
               * instantiate (2 := []). reflexivity.
               * econstructor. }
         simpl. eapply rtc_transitive.
         { eapply rtc_l; [|eapply rtc_once].
           - econstructor. econstructor; eauto.
             + instantiate (2 := []); instantiate (3 := []); reflexivity.
             + econstructor; eauto.
               * instantiate (2 := [SeqCtx]); reflexivity.
               * econstructor. eapply step_exec_instr.
                 { rewrite /RegLocate /= lookup_insert //. }
                 { rewrite /RegLocate /= lookup_insert. inv H6; econstructor; eauto.
                   clear -H3 Hpcaeq' Hpcalt'; solve_addr. }
                 { rewrite /MemLocate /=. erewrite Hmem2''; [|clear -Hastkend Hrange2 Ha1b H6; inv H6; solve_addr].
                   generalize (Hcode 101 ltac:(lia)). intros [ap99 [Hap99 Hinstr99] ].
                   rewrite /call.call_instrs lookup_app_l in Hinstr99; [|rewrite call.call_instrs_prologue_length; lia].
                   rewrite /call.call_instrs_prologue 3!app_assoc lookup_app_r in Hinstr99; [|rewrite !app_length map_length !call.push_instrs_length !app_length !map_length call.pop_env_instrs_length all_registers_list_difference_length /=; lia].
                   rewrite !app_length map_length !call.push_instrs_length !app_length !map_length call.pop_env_instrs_length /= in Hinstr99.
                   generalize (Hsh _ _ ltac:(symmetry; apply Hinstr99)).
                   intros [Hinstr99' _]. assert (ap99 = ^(a + 101)%a) as -> by (clear -Hap99; solve_addr).
                   rewrite Hinstr99'.
                   rewrite /= decode_encode_instr_inv //. }
                 { rewrite /exec /= /RegLocate lookup_insert_ne; [|auto].
                   rewrite lookup_insert_ne; [|auto].
                   rewrite lookup_insert /=.
                   assert ((^(a2 + 99) + -99)%a = Some a2) as -> by (clear -Hastkend; solve_addr).
                   destruct (Addr_le_dec a0 a2) as [_|X]; [|elim X; clear -Hstkrange1; solve_addr].
                   destruct (Addr_le_dec a2 ^(a2 + 99)%a) as [_|X]; [|elim X; clear; solve_addr].
                   destruct (Addr_lt_dec ^(a2 + 99)%a a1) as [_|X]; [|elim X; clear -Hastkend Hrange2; solve_addr].
                   rewrite lookup_insert_ne; [|auto].
                   rewrite lookup_insert /=.
                   destruct (addr_eq_dec ^(a2 + 99)%a a2) as [X|_]; [exfalso; clear -X Hastkend; solve_addr|].
                   rewrite /update_mem /updatePC /RegLocate /= lookup_insert /=.
                   assert ((^(a + 101) + 1)%a = Some ^(a + 102)%a) as -> by (clear - Hpcaeq'; solve_addr).
                   rewrite /update_reg insert_insert /=.
                   destruct g; try congruence; inv H6; destruct H8 as [-> | [-> | ->] ]; auto. }
           - simpl. econstructor. econstructor; eauto.
             + instantiate (2 := []). instantiate (3 := []). reflexivity.
             + econstructor; eauto.
               * instantiate (2 := []). reflexivity.
               * econstructor. }
         simpl. assert (Hcode2: forall i, i < 39 + length rargs -> mem2'' !! (^(a + (102 + i))%a) = translate_word <$> ([inl (encodeInstr (Mov (R 0 eq_refl) (inr call.r_stk))); inl (encodeInstr (PromoteU (R 0 eq_refl))); inl (encodeInstr (Lea (R 0 eq_refl) (inl (-66)%Z))); inl (encodeInstr (Restrict (R 0 eq_refl) (inl (encodePermPair (E, Directed)))))] ++ [inl (encodeInstr (GetA (R 1 eq_refl) call.r_stk)); inl (encodeInstr (GetE (R 2 eq_refl) call.r_stk)); inl (encodeInstr (Subseg call.r_stk (inr (R 1 eq_refl)) (inr (R 2 eq_refl))))] ++ call.push_instrs [inr (R 0 eq_refl)] ++ call.push_instrs (map inr rargs) ++ call.rclear_instrs (list_difference all_registers [PC; rf; call.r_stk]) ++ [inl (encodeInstr (Jmp rf))]) !! i).
              { intros. erewrite Hmem2''.
                - generalize (Hcode (102 + i) ltac:(lia)).
                  intros [ai [Hai Hinstri] ].
                  assert (ai = ^(a + (102 + i))%a) as -> by (clear -Hai; solve_addr).
                  rewrite /call.call_instrs lookup_app_r in Hinstri; [|rewrite call.call_instrs_prologue_length; lia].
                  replace (102 + i - length (call.call_instrs_prologue rargs)) with i in Hinstri by (rewrite call.call_instrs_prologue_length; lia).
                  rewrite Hinstri. rewrite list_lookup_lookup_total_lt in Hinstri; [|rewrite !app_length !call.push_instrs_length map_length call.rclear_instrs_length call.all_registers_list_difference_length /=; auto; lia].
                  generalize (Hsh _ _ ltac:(symmetry; apply Hinstri)).
                  intros [Hinstri' _]. rewrite -Hinstri Hinstri'; reflexivity.
                - clear -Hastkend Hrange2 Ha1b H6; inv H6; solve_addr. }
              eapply rtc_transitive.
              { eapply rtc_transitive; eapply rtc_once.
                - econstructor. econstructor; eauto.
                  + instantiate (2 := []); instantiate (3 := []). reflexivity.
                  + econstructor; eauto.
                    * instantiate (2 := [SeqCtx]); reflexivity.
                    * econstructor. eapply step_exec_instr; simpl.
                      { rewrite /RegLocate lookup_insert //. }
                      { rewrite /RegLocate lookup_insert; econstructor; inv H6; auto.
                        clear -H3 Hpcaeq' Hpcalt'; solve_addr. }
                      { rewrite /MemLocate lookup_insert_ne; [|clear -Hastkend Hrange2 Ha1b H6; inv H6; solve_addr].
                        rewrite (Hcode2 0 ltac:(lia)) /= decode_encode_instr_inv //. }
                      { rewrite /exec /update_reg /= /RegLocate lookup_insert_ne; [|auto].
                        rewrite lookup_insert_ne; [|auto].
                        rewrite lookup_insert /updatePC /= /RegLocate lookup_insert_ne; [|auto].
                        rewrite lookup_insert. assert ((^(a + 102) + 1)%a = Some (^(a + 103))%a) as -> by (clear -Hpcaeq' Hpcalt'; solve_addr).
                        rewrite /update_reg /=. rewrite (insert_commute _ (R 0 _) PC); [|auto].
                        rewrite insert_insert. inv H6.
                        destruct H8 as [-> | [-> | ->] ]; auto. }
                - simpl. econstructor. econstructor; eauto.
                  + instantiate (2 := []). instantiate (3 := []). reflexivity.
                  + econstructor; eauto.
                    * instantiate (2 := []); reflexivity.
                    * econstructor. }
              simpl. eapply rtc_transitive.
              { eapply rtc_transitive; eapply rtc_once.
                - econstructor. econstructor; eauto.
                  + instantiate (2 := []); instantiate (3 := []). reflexivity.
                  + econstructor; eauto.
                    * instantiate (2 := [SeqCtx]); reflexivity.
                    * econstructor. eapply step_exec_instr; simpl.
                      { rewrite /RegLocate lookup_insert //. }
                      { rewrite /RegLocate lookup_insert; econstructor; inv H6; auto.
                        clear -H3 Hpcaeq' Hpcalt'; solve_addr. }
                      { rewrite /MemLocate lookup_insert_ne; [|clear -Hastkend Hrange2 Ha1b H6; inv H6; solve_addr].
                        rewrite (Hcode2 1 ltac:(lia)) /= decode_encode_instr_inv //. }
                      { rewrite /exec /update_reg /= /RegLocate lookup_insert_ne; [|auto].
                        rewrite lookup_insert /updatePC /= /RegLocate lookup_insert_ne; [|auto].
                        rewrite lookup_insert. assert ((^(a + 103) + 1)%a = Some (^(a + 104))%a) as -> by (clear -Hpcaeq' Hpcalt'; solve_addr).
                        rewrite /update_reg /=. rewrite (insert_commute _ (R 0 _) PC); [|auto].
                        rewrite !insert_insert. inv H6.
                        destruct H8 as [-> | [-> | ->] ]; auto. }
                - simpl. econstructor. econstructor; eauto.
                  + instantiate (2 := []). instantiate (3 := []). reflexivity.
                  + econstructor; eauto.
                    * instantiate (2 := []); reflexivity.
                    * econstructor. }
              simpl. eapply rtc_transitive.
              { eapply rtc_transitive; eapply rtc_once.
                - econstructor. econstructor; eauto.
                  + instantiate (2 := []); instantiate (3 := []). reflexivity.
                  + econstructor; eauto.
                    * instantiate (2 := [SeqCtx]); reflexivity.
                    * econstructor. eapply step_exec_instr; simpl.
                      { rewrite /RegLocate lookup_insert //. }
                      { rewrite /RegLocate lookup_insert; econstructor; inv H6; auto.
                        clear -H3 Hpcaeq' Hpcalt'; solve_addr. }
                      { rewrite /MemLocate lookup_insert_ne; [|clear -Hastkend Hrange2 Ha1b H6; inv H6; solve_addr].
                        rewrite (Hcode2 2 ltac:(lia)) /= decode_encode_instr_inv //. }
                      { rewrite /exec /update_reg /= /RegLocate lookup_insert_ne; [|auto].
                        rewrite lookup_insert /updatePC /= /RegLocate.
                        assert ((^(a2 + 99) + -66)%a = Some ^(a2 + 33)%a) as -> by (clear -Hastkend; solve_addr).
                        rewrite (lookup_insert_ne _ (R 0 _) PC); [|auto].
                        rewrite lookup_insert. assert ((^(a + 104) + 1)%a = Some (^(a + 105))%a) as -> by (clear -Hpcaeq' Hpcalt'; solve_addr).
                        rewrite /update_reg /=. rewrite (insert_commute _ (R 0 _) PC); [|auto].
                        rewrite !insert_insert. inv H6.
                        destruct H8 as [-> | [-> | ->] ]; auto. }
                - simpl. econstructor. econstructor; eauto.
                  + instantiate (2 := []). instantiate (3 := []). reflexivity.
                  + econstructor; eauto.
                    * instantiate (2 := []); reflexivity.
                    * econstructor. }
              simpl. eapply rtc_transitive.
              { eapply rtc_transitive; eapply rtc_once.
                - econstructor. econstructor; eauto.
                  + instantiate (2 := []); instantiate (3 := []). reflexivity.
                  + econstructor; eauto.
                    * instantiate (2 := [SeqCtx]); reflexivity.
                    * econstructor. eapply step_exec_instr; simpl.
                      { rewrite /RegLocate lookup_insert //. }
                      { rewrite /RegLocate lookup_insert; econstructor; inv H6; auto.
                        clear -H3 Hpcaeq' Hpcalt'; solve_addr. }
                      { rewrite /MemLocate lookup_insert_ne; [|clear -Hastkend Hrange2 Ha1b H6; inv H6; solve_addr].
                        rewrite (Hcode2 3 ltac:(lia)) /= decode_encode_instr_inv //. }
                      { rewrite /exec /update_reg /= /RegLocate lookup_insert_ne; [|auto].
                        rewrite lookup_insert /updatePC /= /RegLocate.
                        rewrite decode_encode_permPair_inv /=.
                        rewrite (lookup_insert_ne _ (R 0 _) PC); [|auto].
                        rewrite lookup_insert. assert ((^(a + 105) + 1)%a = Some (^(a + 106))%a) as -> by (clear -Hpcaeq' Hpcalt'; solve_addr).
                        rewrite /update_reg /=. rewrite (insert_commute _ (R 0 _) PC); [|auto].
                        rewrite !insert_insert. inv H6.
                        destruct H8 as [-> | [-> | ->] ]; auto. }
                - simpl. assert (addr_reg.min ^(a2 + 99)%a a1 = ^(a2 + 99)%a) as -> by (clear -Hastkend Hrange2; solve_addr).
                  econstructor. econstructor; eauto.
                  + instantiate (2 := []). instantiate (3 := []). reflexivity.
                  + econstructor; eauto.
                    * instantiate (2 := []); reflexivity.
                    * econstructor. }
              simpl. eapply rtc_transitive.
              { eapply rtc_transitive; eapply rtc_once.
                - econstructor. econstructor; eauto.
                  + instantiate (2 := []); instantiate (3 := []). reflexivity.
                  + econstructor; eauto.
                    * instantiate (2 := [SeqCtx]); reflexivity.
                    * econstructor. eapply step_exec_instr; simpl.
                      { rewrite /RegLocate lookup_insert //. }
                      { rewrite /RegLocate lookup_insert; econstructor; inv H6; auto.
                        clear -H3 Hpcaeq' Hpcalt'; solve_addr. }
                      { rewrite /MemLocate lookup_insert_ne; [|clear -Hastkend Hrange2 Ha1b H6; inv H6; solve_addr].
                        rewrite (Hcode2 4 ltac:(lia)) /= decode_encode_instr_inv //. }
                      { rewrite /exec /update_reg /= /RegLocate lookup_insert_ne; [|auto].
                        rewrite lookup_insert_ne; [|auto].
                        rewrite lookup_insert_ne; [|auto].
                        rewrite lookup_insert. case_eq ^(a2 + 99)%a; intros.
                        assert (z = (^(a2 + 99)%a)%Z) by (rewrite H1; reflexivity).
                        subst z; rewrite -H1. clear H1 fin pos.
                        rewrite /updatePC /RegLocate lookup_insert_ne; [|auto].
                        rewrite lookup_insert.
                        assert ((^(a + 106) + 1)%a = Some (^(a + 107))%a) as -> by (clear -Hpcaeq' Hpcalt'; solve_addr).
                        rewrite /update_reg /=. rewrite (insert_commute _ (R 1 _) PC); [|auto].
                        rewrite (insert_commute _ (R 1 _) (R 0 _)); [|auto].
                        rewrite !insert_insert. inv H6.
                        destruct H8 as [-> | [-> | ->] ]; auto. }
                - simpl. econstructor. econstructor; eauto.
                  + instantiate (2 := []). instantiate (3 := []). reflexivity.
                  + econstructor; eauto.
                    * instantiate (2 := []); reflexivity.
                    * econstructor. }
              simpl. eapply rtc_transitive.
              { eapply rtc_transitive; eapply rtc_once.
                - econstructor. econstructor; eauto.
                  + instantiate (2 := []); instantiate (3 := []). reflexivity.
                  + econstructor; eauto.
                    * instantiate (2 := [SeqCtx]); reflexivity.
                    * econstructor. eapply step_exec_instr; simpl.
                      { rewrite /RegLocate lookup_insert //. }
                      { rewrite /RegLocate lookup_insert; econstructor; inv H6; auto.
                        clear -H3 Hpcaeq' Hpcalt'; solve_addr. }
                      { rewrite /MemLocate lookup_insert_ne; [|clear -Hastkend Hrange2 Ha1b H6; inv H6; solve_addr].
                        rewrite (Hcode2 5 ltac:(lia)) /= decode_encode_instr_inv //. }
                      { rewrite /exec /update_reg /= /RegLocate lookup_insert_ne; [|auto].
                        rewrite lookup_insert_ne; [|auto].
                        rewrite lookup_insert_ne; [|auto].
                        rewrite lookup_insert. case_eq a1; intros.
                        assert (z = a1%Z) by (rewrite H1; reflexivity).
                        subst z; rewrite -H1. clear H1 fin pos.
                        rewrite /updatePC /RegLocate lookup_insert_ne; [|auto].
                        rewrite lookup_insert.
                        assert ((^(a + 107) + 1)%a = Some (^(a + 108))%a) as -> by (clear -Hpcaeq' Hpcalt'; solve_addr).
                        rewrite /update_reg /=. rewrite (insert_commute _ (R 2 _) PC); [|auto].
                        rewrite !insert_insert. inv H6.
                        destruct H8 as [-> | [-> | ->] ]; auto. }
                - simpl. econstructor. econstructor; eauto.
                  + instantiate (2 := []). instantiate (3 := []). reflexivity.
                  + econstructor; eauto.
                    * instantiate (2 := []); reflexivity.
                    * econstructor. }
              simpl. eapply rtc_transitive.
              { eapply rtc_transitive; eapply rtc_once.
                - econstructor. econstructor; eauto.
                  + instantiate (2 := []); instantiate (3 := []). reflexivity.
                  + econstructor; eauto.
                    * instantiate (2 := [SeqCtx]); reflexivity.
                    * econstructor. eapply step_exec_instr; simpl.
                      { rewrite /RegLocate lookup_insert //. }
                      { rewrite /RegLocate lookup_insert; econstructor; inv H6; auto.
                        clear -H3 Hpcaeq' Hpcalt'; solve_addr. }
                      { rewrite /MemLocate lookup_insert_ne; [|clear -Hastkend Hrange2 Ha1b H6; inv H6; solve_addr].
                        rewrite (Hcode2 6 ltac:(lia)) /= decode_encode_instr_inv //. }
                      { rewrite /exec /update_reg /= /RegLocate lookup_insert_ne; [|auto].
                        rewrite lookup_insert_ne; [|auto].
                        rewrite lookup_insert_ne; [|auto].
                        rewrite lookup_insert_ne; [|auto].
                        rewrite lookup_insert.
                        rewrite lookup_insert_ne; [|auto].
                        rewrite lookup_insert_ne; [|auto].
                        rewrite lookup_insert_ne; [|auto].
                        rewrite lookup_insert.
                        rewrite lookup_insert_ne; [|auto].
                        rewrite lookup_insert.
                        rewrite !z_to_addr_z_of.
                        rewrite /isWithin. assert ((a0 <=? ^(a2 + 99))%a = true) as -> by (eapply leb_addr_spec; clear -Hstkrange1; solve_addr).
                        assert ((a1 <=? a1)%a = true) as -> by (eapply leb_addr_spec; clear; solve_addr).
                        rewrite /updatePC /= /RegLocate lookup_insert_ne; [|auto].
                        rewrite lookup_insert /=.
                        assert ((^(a + 108) + 1)%a = Some (^(a + 109))%a) as -> by (clear -Hpcaeq' Hpcalt'; solve_addr).
                        rewrite /update_reg /=. rewrite (insert_commute _ call.r_stk PC); [|auto].
                        rewrite insert_insert. inv H6.
                        destruct H8 as [-> | [-> | ->] ]; auto. }
                - simpl. econstructor. econstructor; eauto.
                  + instantiate (2 := []). instantiate (3 := []). reflexivity.
                  + econstructor; eauto.
                    * instantiate (2 := []); reflexivity.
                    * econstructor. }
              simpl. eapply rtc_transitive.
              { eapply rtc_transitive; eapply rtc_once.
                - econstructor. econstructor; eauto.
                  + instantiate (2 := []); instantiate (3 := []). reflexivity.
                  + econstructor; eauto.
                    * instantiate (2 := [SeqCtx]); reflexivity.
                    * econstructor. eapply step_exec_instr; simpl.
                      { rewrite /RegLocate lookup_insert //. }
                      { rewrite /RegLocate lookup_insert; econstructor; inv H6; auto.
                        clear -H3 Hpcaeq' Hpcalt'; solve_addr. }
                      { rewrite /MemLocate lookup_insert_ne; [|clear -Hastkend Hrange2 Ha1b H6; inv H6; solve_addr].
                        rewrite (Hcode2 7 ltac:(lia)) /= decode_encode_instr_inv //. }
                      { rewrite /exec /update_reg /= /RegLocate lookup_insert_ne; [|auto].
                        rewrite lookup_insert /=.
                        assert ((^(a2 + 99) + 0)%a = Some ^(a2 + 99)%a) as -> by (clear; solve_addr).
                        destruct (Addr_le_dec ^(a2 + 99)%a ^(a2 + 99)%a) as [_|X]; [|elim X; clear; solve_addr].
                        destruct (Addr_lt_dec ^(a2 + 99)%a a1) as [_|X]; [|elim X; clear -X Hastkend Hrange2; solve_addr].
                        do 3 (rewrite lookup_insert_ne; [|auto]).
                        rewrite lookup_insert /=.
                        assert ((^(a2 + 99) <=? ^(a2 + 99))%a = true) as -> by (eapply leb_addr_spec; clear; solve_addr).
                        destruct (addr_eq_dec ^(a2 + 99)%a ^(a2 + 99)%a) as [_|X]; [|elim X; clear; solve_addr].
                        assert ((^(a2 + 99) + 1)%a = Some ^(a2 + 100)%a) as -> by (clear -Hastkend; solve_addr).
                        rewrite /updatePC /= /RegLocate lookup_insert_ne; [|auto].
                        rewrite lookup_insert /=.
                        assert ((^(a + 109) + 1)%a = Some (^(a + 110))%a) as -> by (clear -Hpcaeq' Hpcalt'; solve_addr).
                        rewrite /update_reg /=. rewrite (insert_commute _ call.r_stk PC); [|auto].
                        rewrite !insert_insert. inv H6.
                        destruct H8 as [-> | [-> | ->] ]; auto. }
                - simpl. econstructor. econstructor; eauto.
                  + instantiate (2 := []). instantiate (3 := []). reflexivity.
                  + econstructor; eauto.
                    * instantiate (2 := []); reflexivity.
                    * econstructor. }
              simpl. rewrite (insert_commute _ (R 1 _) call.r_stk) //.
              rewrite (insert_commute _ (R 0 _) call.r_stk) //.
              rewrite (insert_commute _ (R 2 _) call.r_stk) // insert_insert.
              eapply rtc_transitive.
              { eapply rtc_transitive.
                - eapply push_env_instrs_spec with (wlist := inr <$> rargs); auto.
                  + econstructor; inv H6; eauto.
                    clear -Hpcaeq' Hpcalt' H3; solve_addr.
                  + rewrite map_length. instantiate (1 := ^(a2 + (100 + length rargs))%a).
                    clear -Hastkend; solve_addr.
                  + clear; solve_addr.
                  + clear -Hastkend Hrange2. solve_addr.
                  + rewrite map_length. instantiate (1 := ^(a + (110 + length rargs))%a).
                    clear -Hpcaeq'; solve_addr.
                  + inv H6; clear -H3; solve_addr.
                  + inv H6; clear -Hpcalt' Hpcaeq' H3; solve_addr.
                  + rewrite map_length; intros.
                    generalize (Hcode2 (8 + i) ltac:(lia)).
                    assert (^(a + (102 + (8 + i)%nat))%a = ^(a + (110 + i))%a) as -> by (clear -Hpcaeq' Hpcalt'; solve_addr).
                    intros Hinstri. exists (^(a + (110 + i))%a).
                    split; [clear -H1 Hpcalt' Hpcaeq'; solve_addr|].
                    rewrite lookup_app_r in Hinstri; [|simpl; lia].
                    simpl length in Hinstri.
                    rewrite lookup_app_r in Hinstri; [|simpl; lia].
                    simpl length in Hinstri.
                    rewrite lookup_app_r in Hinstri; [|simpl; lia].
                    simpl length in Hinstri.
                    replace (8 + i - 4 - 3 - 1) with i in Hinstri by lia.
                    rewrite lookup_app_l in Hinstri; [|rewrite call.push_instrs_length map_length; auto].
                    rewrite list_lookup_fmap -Hinstri.
                    rewrite lookup_insert_ne; [|clear -Hastkend Hrange2 H6 Ha1b; inv H6; solve_addr].
                    rewrite lookup_insert_ne; [|clear -Hastkend Hrange2 H6 Ha1b; inv H6; solve_addr].
                    reflexivity.
                  + instantiate (1 := <[R 2 eq_refl:=inl (z_of a1)]> (<[R 0 eq_refl:=(inr (Stk (length cs) E a0 ^(a2 + 99)%a ^(a2 + 33)%a))]> (<[R 1 eq_refl:=inl (z_of (^(a2 + 99)%a))]> reg1))).
                    intros. destruct (Hregsdef r) as [? [? _] ]; eauto.
                    match goal with |- context [<[?r1:=_]> _ !! ?r2] => destruct (reg_eq_dec r1 r2) as [X|] end; [rewrite X lookup_insert; eauto| rewrite lookup_insert_ne //].
                    match goal with |- context [<[?r1:=_]> _ !! ?r2] => destruct (reg_eq_dec r1 r2) as [X|] end; [rewrite X lookup_insert; eauto| rewrite lookup_insert_ne //].
                    match goal with |- context [<[?r1:=_]> _ !! ?r2] => destruct (reg_eq_dec r1 r2) as [X|] end; [rewrite X lookup_insert; eauto| rewrite lookup_insert_ne; eauto].
                  + intros. match goal with |- context [<[?r1:=_]> _ !! ?r2] => destruct (reg_eq_dec r1 r2) as [X|] end; [subst r; rewrite lookup_insert; rewrite lookup_insert in H3; inv H3; auto| rewrite lookup_insert_ne //; rewrite lookup_insert_ne // in H3].
                    match goal with |- context [<[?r1:=_]> _ !! ?r2] => destruct (reg_eq_dec r1 r2) as [X|] end; [subst r; rewrite lookup_insert; rewrite lookup_insert in H3; inv H3; auto| rewrite lookup_insert_ne //; rewrite lookup_insert_ne // in H3].
                    match goal with |- context [<[?r1:=_]> _ !! ?r2] => destruct (reg_eq_dec r1 r2) as [X|] end; [subst r; rewrite lookup_insert; rewrite lookup_insert in H3; inv H3; auto| rewrite lookup_insert_ne //; rewrite lookup_insert_ne // in H3].
                    apply (Hsregs _ _ H3).
                  + intros. rewrite list_lookup_fmap in H1.
                    destruct (rargs !! i) as [ri|] eqn:Hri; inv H1.
                    simpl. generalize (elem_of_list_lookup_2 _ _ _ Hri). intros Hri'.
                    rewrite /base.RegLocate lookup_insert_ne; [|intro X; subst ri; eapply Hner2; eapply elem_of_cons; right; eapply Hri'].
                    rewrite /base.RegLocate lookup_insert_ne; [|intro X; subst ri; eapply Hner0; eapply elem_of_cons; right; eapply Hri'].
                    rewrite /base.RegLocate lookup_insert_ne; [|intro X; subst ri; eapply Hner1; eapply elem_of_cons; right; eapply Hri'].
                    generalize (push_words_canStoreU Hnew_stk).
                    intros X. generalize (X (S i) (base.RegLocate reg1 ri) ltac:(rewrite /wretargs lookup_app_r; [simpl; rewrite list_lookup_fmap; replace (i - 0) with i by lia; rewrite Hri /= /base.RegLocate //|simpl; lia])).
                    rewrite /base.RegLocate.
                    eapply lookup_lt_Some in Hri.
                    replace (^(^(a2 + 99) + S i)%a) with (^(^(a2 + 100) + i)%a) by (clear -Hri Hastkend Hrange2; solve_addr). auto.
                  + split; intro Z; eapply elem_of_list_fmap in Z; destruct Z as [? [Y Z] ]; inv Y; [elim HrfnePC'; auto|elim Hrfnerstk'; auto].
                - match goal with |- context [map ?f ?l] => assert (map f l = map (fun r => translate_word (base.RegLocate reg1 r)) rargs) as -> end.
                  { eapply list_eq_same_length.
                    - rewrite map_length //.
                    - rewrite !map_length //.
                    - intros. rewrite !list_lookup_fmap in H2, H3.
                      destruct (rargs !! i) as [ri|] eqn:Hri; inv H2; inv H3.
                      generalize (elem_of_list_lookup_2 _ _ _ Hri). intros Hri'.
                      rewrite /base.RegLocate lookup_insert_ne; [|intro X; subst ri; eapply Hner2; eapply elem_of_cons; right; eapply Hri'].
                      rewrite /base.RegLocate lookup_insert_ne; [|intro X; subst ri; eapply Hner0; eapply elem_of_cons; right; eapply Hri'].
                      rewrite /base.RegLocate lookup_insert_ne; [|intro X; subst ri; eapply Hner1; eapply elem_of_cons; right; eapply Hri'].
                      reflexivity. }
                  eapply rtc_refl. }
              eapply rtc_transitive.
              { eapply rtc_transitive.
                - eapply rclear_spec with (rlist := (list_difference all_registers [PC; rf; call.r_stk])).
                  + inv H6; econstructor; eauto; clear -H3 Hpcalt' Hpcaeq'; solve_addr.
                  + rewrite call.all_registers_list_difference_length; auto.
                    instantiate (1 := ^(a + (140 + length rargs))%a).
                    clear -Hpcaeq'; solve_addr.
                  + inv H6; clear -H3; solve_addr.
                  + clear -Hpcaeq' Hpcalt'; solve_addr.
                  + rewrite call.all_registers_list_difference_length; auto.
                    intros i Hilt. exists ^(a + (102 + (8 + length rargs + i)))%a.
                    split; [clear -Hpcaeq' Hilt Hpcalt'; solve_addr|].
                    generalize (Hcode2 (8 + length rargs + i) ltac:(clear -Hilt; lia)).
                    intros Hinstri. rewrite lookup_app_r in Hinstri; [|simpl; lia].
                    rewrite lookup_app_r in Hinstri; [|simpl; lia].
                    rewrite lookup_app_r in Hinstri; [|simpl; lia].
                    rewrite lookup_app_r in Hinstri; [|rewrite call.push_instrs_length map_length; simpl; lia].
                    rewrite call.push_instrs_length !map_length in Hinstri; simpl length in Hinstri.
                    rewrite lookup_app_l in Hinstri; [|rewrite call.rclear_instrs_length call.all_registers_list_difference_length; auto; lia].
                    replace (8 + length rargs + i - 4 - 3 - 1 - length rargs) with i in Hinstri; [|lia].
                    rewrite list_lookup_fmap -Hinstri.
                    erewrite push_words_no_check_spec.
                    * rewrite lookup_insert_ne; [|clear -Hastkend Hrange2 Ha1b H6; inv H6; solve_addr].
                      rewrite lookup_insert_ne; [|clear -Hastkend Hrange2 Ha1b H6; inv H6; solve_addr].
                      repeat f_equal. lia.
                    * rewrite map_length. instantiate (1 := e).
                      clear -Hastkend Hrange2 Ha1b H6; inv H6; solve_addr.
                    * right. rewrite map_length.
                      clear -Hastkend Hrange2 Ha1b H6; inv H6; solve_addr.
                  + eapply not_elem_of_list.
                    eapply elem_of_cons; left; auto.
                - rewrite rclear_commute; [|eapply not_elem_of_list; do 2 (eapply elem_of_cons; right); eapply elem_of_cons; left; auto].
                  eapply not_elem_of_cons in Hner0; destruct Hner0 as [Hner0 Hner0'].
                  eapply not_elem_of_cons in Hner1; destruct Hner1 as [Hner1 Hner1'].
                  eapply not_elem_of_cons in Hner2; destruct Hner2 as [Hner2 Hner2'].
                  rewrite rclear_commute_erase; [|eapply elem_of_list_difference; split; [eapply all_registers_correct|do 3 (eapply not_elem_of_cons; split; auto); eapply not_elem_of_nil] ].
                  rewrite rclear_commute_erase; [|eapply elem_of_list_difference; split; [eapply all_registers_correct|do 3 (eapply not_elem_of_cons; split; auto); eapply not_elem_of_nil] ].
                  rewrite rclear_commute_erase; [|eapply elem_of_list_difference; split; [eapply all_registers_correct|do 3 (eapply not_elem_of_cons; split; auto); eapply not_elem_of_nil] ].
                  eapply rtc_refl. }
              eapply rtc_transitive.
              { eapply rtc_once. econstructor; econstructor; eauto.
                - instantiate (2 := []). instantiate (3 := []). reflexivity.
                - econstructor; eauto.
                  + instantiate (2 := [SeqCtx]). reflexivity.
                  + econstructor. eapply step_exec_instr.
                    { rewrite /RegLocate lookup_insert //. }
                    { rewrite /RegLocate lookup_insert.
                      inv H6; econstructor; eauto.
                      clear -H3 Hpcaeq' Hpcalt'; solve_addr. }
                    { rewrite /MemLocate /=. erewrite push_words_no_check_spec.
                      - rewrite lookup_insert_ne; [|clear -Hastkend Hrange2 Ha1b H6; inv H6; solve_addr].
                        rewrite lookup_insert_ne; [|clear -Hastkend Hrange2 Ha1b H6; inv H6; solve_addr].
                        generalize (Hcode2 (38 + length rargs) ltac:(lia)).
                        intros Hinstri. rewrite lookup_app_r in Hinstri; [|simpl; lia].
                        rewrite lookup_app_r in Hinstri; [|simpl; lia].
                        rewrite lookup_app_r in Hinstri; [|simpl; lia].
                        rewrite lookup_app_r in Hinstri; [|rewrite call.push_instrs_length map_length; simpl; lia].
                        rewrite call.push_instrs_length !map_length in Hinstri; simpl length in Hinstri.
                        rewrite lookup_app_r in Hinstri; [|rewrite call.rclear_instrs_length call.all_registers_list_difference_length; auto; lia].
                        rewrite call.rclear_instrs_length call.all_registers_list_difference_length in Hinstri; [|auto|auto].
                        replace (38 + length rargs - 4 - 3 - 1 - length rargs - 30) with 0 in Hinstri by lia.
                        assert (^(a + (102 + (38 + length rargs)%nat))%a = ^(a + (140 + length rargs))%a) as <- by (clear -Hpcalt' Hpcaeq'; solve_addr).
                        rewrite Hinstri; simpl. eapply decode_encode_instr_inv.
                      - rewrite map_length. instantiate (1 := e).
                        clear -Hastkend Hrange2 Ha1b H6; inv H6; solve_addr.
                      - right. rewrite map_length.
                        clear -Hastkend Hrange2 Ha1b H6; inv H6; solve_addr. }
                    { rewrite /exec /update_reg /RegLocate /reg /cap_lang.mem lookup_insert_ne; [|auto].
                      rewrite lookup_insert_ne; [|auto].
                      rewrite rclear_lookup_not_in; [|eapply not_elem_of_list; apply elem_of_cons; right; eapply elem_of_cons; left; auto].
                      rewrite insert_insert /snd.
                      rewrite (Hsregs _ _ Hwrf). auto. } }
              simpl app. rewrite Hpush3 /snd /final_state.
              assert (<[PC:=updatePcPerm (translate_word wrf)]> (<[call.r_stk:=inr (URWLX, Directed, ^(a2 + 99)%a, a1, ^(a2 + (100 + length rargs))%a)]> (foldl (λ (reg : Reg) (r : RegName), <[r:=inl 0%Z]> reg) reg2 (list_difference all_registers [PC; rf; call.r_stk]))) = <[PC:=updatePcPerm (translate_word wrf)]> (<[call.r_stk:=inr (URWLX, Directed, ^(a2 + 99)%a, a1, ^(Some astkend)%a)]> (<[rf:=translate_word wrf]> (gset_to_gmap (inl 0%Z) (list_to_set all_registers))))) as YZ.
              { eapply map_eq; intros r.
                destruct (reg_eq_dec r PC); [subst r; rewrite !lookup_insert //|rewrite !(lookup_insert_ne _ PC r); auto].
                destruct (reg_eq_dec r call.r_stk); [subst r; rewrite !lookup_insert Hastkend //|].
                rewrite !(lookup_insert_ne _ call.r_stk r); auto.
                destruct (reg_eq_dec rf r); [subst r|].
                - rewrite lookup_insert rclear_lookup_not_in; [|eapply not_elem_of_list; eapply elem_of_cons; right; eapply elem_of_cons; left; auto].
                  apply (Hsregs _ _ Hwrf).
                - rewrite lookup_insert_ne; auto.
                  rewrite rclear_lookup_in; [|eapply elem_of_list_difference; split; [eapply all_registers_correct|do 3 (eapply not_elem_of_cons; split; auto); eapply not_elem_of_nil] ].
                  rewrite (proj2 (lookup_gset_to_gmap_Some ((inl 0%Z): Word) (list_to_set all_registers) r (inl 0%Z))) //.
                  split; auto. eapply elem_of_list_to_set. apply all_registers_correct. }
              rewrite YZ. eapply rtc_refl. }
          { rewrite /final_state.
            assert (σ2 = (<[PC:=lang.updatePcPerm wrf]> (<[call.r_stk:=inr (Stk (length cs + 1) URWLX ^(a2 + 99)%a a1 ^(Some astkend)%a)]> (<[rf:=wrf]> (gset_to_gmap (inl 0%Z) (list_to_set all_registers)))), h, new_stk, (<[PC:=inr (Regular (p, g, b, e, pca'))]> (<[call.r_stk:=inr (Stk (length cs) URWLX a0 a1 ^(a2 + 1)%a)]> reg1), clear_stk saved_stk ^(a2 + 99)%a) :: cs)) as -> by (inv H9; auto).
            assert (Ha1b: (a1 <= b)%a).
            { simpl in HinterpPC. destruct HinterpPC as [A B].
              generalize (B b ltac:(clear -H6; inv H6; solve_addr)). intro C.
              generalize (Hdisj _ C). intros.
              simpl in Hinterpwstk. destruct Hinterpwstk as [? [X ?] ].
              clear -X H1; solve_addr. }
            econstructor.
            - repeat econstructor.
            - intros _. econstructor.
              + intros. simpl in H2; destruct (nat_eq_dec d1 (S (length cs))).
                * inv H2. generalize (proj1 (stack_is_Some _ _) ltac:(eexists; eapply H3)).
                  simpl. intro X; clear -H1 X; lia.
                * simpl in H3; destruct (nat_eq_dec d2 (S (length cs))).
                  { assert (stk2 = new_stk) as -> by (inv H3; auto).
                    destruct (nat_eq_dec d1 (length cs)).
                    - assert (forall A (x y: A), Some x = Some y -> x = y) as ihatecoq by (inversion 1; auto).
                      eapply ihatecoq in H2; subst stk1. clear ihatecoq.
                      assert (Hlower: (a3 < ^(a2 + 99)%a)%a).
                      { destruct (Addr_lt_dec a3 ^(a2 + 99)%a); auto.
                        destruct (lang.clear_stk_spec saved_stk ^(a2 + 99)%a) as [X _].
                        generalize (X a3 ltac:(clear -n0; solve_addr)).
                        destruct H4. rewrite H2. congruence. }
                      assert (Hhigher: (^(a2 + 99)%a <= a4)%a).
                      { destruct (Addr_le_dec ^(a2 + 99)%a a4); auto.
                        assert (Hwretargslen: length wretargs = 1 + length rargs).
                        { rewrite /wretargs app_length map_length //. }
                        generalize (@push_words_lookup_spec wretargs ∅ ^(a2 + 99)%a e new_stk ltac:(clear -Hastkend Hrange2 H6 Ha1b Hwretargslen; rewrite Hwretargslen; inv H6; solve_addr) Hnew_stk).
                        intros [_ XY]. destruct H5. generalize (XY a4 ltac:(left; clear -n0; solve_addr)).
                        rewrite H2. rewrite lookup_empty. congruence. }
                        clear -Hlower Hhigher; solve_addr.
                    - destruct Hinterpwstk as [_ [ZZ [TY YZ] ] ].
                      generalize (YZ a0 ltac:(simpl; clear -Hstkrange1 Hastkend Hrange2; solve_addr)).
                      intros YY.
                      generalize (Hstkdisj d1 (length cs) ltac:(lia) stk1 stk ltac:(rewrite /stack; destruct (nat_eq_dec d1 (length cs)); [elim n0; auto|]; auto) ltac:(rewrite /stack; destruct (nat_eq_dec (length cs) (length cs)); [reflexivity|congruence]) a3 a0 H4 YY).
                      assert (Hhigher: (^(a2 + 99)%a <= a4)%a).
                      { destruct (Addr_le_dec ^(a2 + 99)%a a4); auto.
                        assert (Hwretargslen: length wretargs = 1 + length rargs).
                        { rewrite /wretargs app_length map_length //. }
                        generalize (@push_words_lookup_spec wretargs ∅ ^(a2 + 99)%a e new_stk ltac:(clear -Hastkend Hrange2 H6 Ha1b Hwretargslen; rewrite Hwretargslen; inv H6; solve_addr) Hnew_stk).
                        intros [_ XY]. destruct H5. generalize (XY a4 ltac:(left; clear -n1; solve_addr)).
                        rewrite H5. rewrite lookup_empty. congruence. }
                        clear -Hhigher Hstkrange1; solve_addr. }
                  { destruct (nat_eq_dec d2 (length cs)).
                    - destruct (nat_eq_dec d1 (length cs)); [lia|].
                      assert (forall A (x y: A), Some x = Some y -> x = y) as ihatecoq by (inversion 1; auto).
                      eapply ihatecoq in H3. subst stk2. clear ihatecoq.
                      destruct H5. destruct (clear_stk_spec saved_stk ^(a2 + 99)%a) as [XX XY].
                      assert (a4 < ^(a2 + 99)%a)%a.
                      { destruct (Addr_lt_dec a4 ^(a2 + 99)%a); auto.
                        rewrite XX in H3; [|clear -n2; solve_addr]. inv H3. }
                      rewrite (XY _ H5) in H3.
                      assert (Hsaved_word_len: length saved_words = 99).
                      { rewrite /saved_words !app_length !map_length call.pop_env_instrs_length /= //. }
                      assert (FF: (^(a2 + length saved_words) < ^(a2 + 100)%a)%a).
                      { rewrite Hsaved_word_len. destruct (a2 + 99%nat)%a eqn:GG.
                        - destruct (a2 + 100)%a eqn:HH; [clear -GG HH; solve_addr|].
                          simpl. inv H6. clear -GG Hastkend H10 Ha1b Hrange2.
                          solve_addr.
                        - inv H6. clear -GG Hastkend H10 Ha1b Hrange2.
                          solve_addr. }
                      generalize (@push_words_lookup_spec saved_words stk a2 _ saved_stk FF Hsaved_stk).
                      intros [GG HH]. rewrite Hsaved_word_len in GG, HH.
                      destruct (Addr_lt_dec a4 a2).
                      + rewrite (HH a4 ltac:(left; auto)) in H3.
                        apply (Hstkdisj d1 d2 H1 stk1 stk ltac:(rewrite /stack; destruct (nat_eq_dec d1 (length cs)); [elim n1; auto|]; auto) ltac:(rewrite /stack; destruct (nat_eq_dec d2 (length cs)); [reflexivity|congruence]) a3 a4 H4 ltac:(eexists; eapply H3)).
                      + destruct Hinterpwstk as [_ [ZZ [TY YZ] ] ].
                        generalize (YZ a0 ltac:(simpl; clear -Hstkrange1 Hastkend Hrange2; solve_addr)).
                        intros YY.
                        generalize (Hstkdisj d1 (length cs) ltac:(lia) stk1 stk ltac:(rewrite /stack; destruct (nat_eq_dec d1 (length cs)); [elim n1; auto|]; auto) ltac:(rewrite /stack; destruct (nat_eq_dec (length cs) (length cs)); [reflexivity|congruence]) a3 a0 H4 YY).
                        clear -n2 Hstkrange1. solve_addr.
                    - eapply Hstkdisj; eauto.
                      + assert (d2 < length cs) by (eapply stack_is_Some; eauto).
                        simpl; destruct (nat_eq_dec d1 (length cs)); [lia|]. auto.
                      + simpl; destruct (nat_eq_dec d2 (length cs)); [lia|]. auto. }
              + econstructor; eauto.
                * intros. destruct (reg_eq_dec PC r); [subst r; rewrite lookup_insert| rewrite lookup_insert_ne //].
                  { eexists; split; [reflexivity|].
                    assert (Hwrf_reasonable: is_safe wrf).
                    { generalize (Hreasonable rf ltac:(eapply elem_of_cons; left; auto)).
                      rewrite /base.RegLocate Hwrf //. }
                    destruct wrf; simpl in Hwrf_reasonable; [simpl; auto|].
                    destruct c0; [|inv Hwrf_reasonable..].
                    eapply interp_updatePcPerm_regular; eauto. }
                  destruct (reg_eq_dec call.r_stk r); [subst r; rewrite lookup_insert|rewrite lookup_insert_ne //].
                  { eexists; split; [reflexivity|]. simpl.
                    split; [lia|]. split; [destruct Hinterpwstk as [? [? [QQ ?] ] ]; auto|].
                    split; [destruct Hinterpwstk as [? [? [QQ ?] ] ]; auto|].
                    { intros. destruct (nat_eq_dec d' (length cs)).
                      - subst d'. assert (stk' = clear_stk saved_stk ^(a2 + 99)%a).
                        clear -H4. congruence.
                        clear H4. subst stk'.
                        destruct (clear_stk_spec saved_stk ^(a2 + 99)%a) as [R1 R2].
                        destruct (Addr_lt_dec a' ^(a2 + 99)%a); auto.
                        erewrite R1 in H5. destruct H5; congruence.
                        clear -n0; solve_addr.
                      - eapply QQ in H5; eauto. clear -Hstkrange1 H5; solve_addr. }
                    intros. assert (Hwretargslen: length wretargs = 1 + length rargs) by (rewrite /wretargs app_length map_length //).
                    generalize (@push_words_lookup_spec wretargs ∅ ^(a2 + 99)%a e new_stk ltac:(clear -Hastkend Hrange2 H6 Ha1b Hwretargslen; rewrite Hwretargslen; inv H6; solve_addr) Hnew_stk).
                    intros [YY PP].
                    assert (x = ^(^(a2 + 99)%a + (Z.to_nat (z_of x - z_of ^(a2 + 99)%a)))%a) as ->.
                    { clear -H1; solve_addr. }
                    erewrite YY; [|rewrite Hwretargslen; clear -H1 Hastkend; solve_addr].
                    erewrite list_lookup_lookup_total_lt; eauto.
                    rewrite Hwretargslen; clear -H1 Hastkend; solve_addr. }
                  destruct (reg_eq_dec rf r); [subst r; rewrite lookup_insert|rewrite lookup_insert_ne //].
                  { eexists; split; [reflexivity|].
                    eapply interp_call_preserved; eauto.
                    generalize (Hreasonable rf ltac:(eapply elem_of_cons; left; auto)).
                    rewrite /base.RegLocate Hwrf //. }
                  exists (inl 0%Z); split; [|simpl; auto].
                  eapply lookup_gset_to_gmap_Some; split; auto.
                  eapply elem_of_list_to_set. eapply all_registers_correct.
                * assert (Hwretargslen: length wretargs = 1 + length rargs) by (rewrite /wretargs app_length map_length //).
                  generalize (@push_words_lookup_spec wretargs ∅ ^(a2 + 99)%a e new_stk ltac:(clear -Hastkend Hrange2 H6 Ha1b Hwretargslen; rewrite Hwretargslen; inv H6; solve_addr) Hnew_stk).
                  intros [YY YZ].
                  intros. destruct Hinterpwstk as [W1 [W2 W3] ].
                  destruct (Addr_le_dec ^(^(a2 + 99)%a + length wretargs)%a a3).
                  { rewrite YZ in H1; auto. rewrite lookup_empty in H1.
                    destruct H1; congruence. }
                  rewrite Hwretargslen in n. clear -Hastkend Hrange2 W2 n.
                  solve_addr.
                * assert (Hwretargslen: length wretargs = 1 + length rargs) by (rewrite /wretargs app_length map_length //).
                  generalize (@push_words_lookup_spec wretargs ∅ ^(a2 + 99)%a e new_stk ltac:(clear -Hastkend Hrange2 H6 Ha1b Hwretargslen; rewrite Hwretargslen; inv H6; solve_addr) Hnew_stk).
                  intros [YY YZ].
                  intros. destruct (Addr_lt_dec a3 ^(a2 + 99)%a).
                  { erewrite YZ in H1; auto. rewrite lookup_empty in H1; inv H1. }
                  destruct (Addr_le_dec ^(^(a2 + 99) + length wretargs)%a a3).
                  { erewrite YZ in H1; auto. rewrite lookup_empty in H1; inv H1. }
                  assert (a3 = ^(^(a2 + 99)%a + (Z.to_nat (z_of a3 - z_of ^(a2 + 99)%a)))%a) as ZZ.
                  { clear -n n0; solve_addr. }
                  assert (a3 < astkend)%a.
                  { rewrite Hwretargslen in n0; clear -n0 Hastkend Hrange2 H6. inv H6. solve_addr. }
                  clear n0.
                  assert (Z.to_nat (a3 - ^(a2 + 99)%a) < length wretargs).
                  { rewrite Hwretargslen; clear -Hrange2 H6 n H2 Hastkend; inv H6. solve_addr. }
                  rewrite ZZ in H1. rewrite YY in H1; auto.
                  destruct (Z.to_nat (a3 - ^(a2 + 99)%a)).
                  { simpl in H1. inv H1. split.
                    - replace (^(^(a2 + 99) + 0%nat)%a) with ^(a2 + 99)%a by (clear; solve_addr).
                      replace mem2''' with (ac, mem2''').2 by reflexivity.
                      rewrite -Hpush3. erewrite push_words_no_check_spec; [rewrite lookup_insert /= //| rewrite map_length..].
                      + instantiate (1 := e). clear -Hastkend H6 Ha1b Hrange2; inv H6; solve_addr.
                      + left. clear -Hastkend H6 Ha1b Hrange2; inv H6; solve_addr.
                    - split; [|rewrite /canBeStored /lang.canStoreU /=; clear; eapply leb_addr_spec; solve_addr].
                      rewrite /interp. eexists. eexists.
                      split; [rewrite lookup_insert_ne; auto; rewrite lookup_insert; reflexivity|].
                      split; [clear -Hastkend; solve_addr|].
                      split; [do 5 eexists; split; [rewrite lookup_insert; reflexivity|]|].
                      + split; [inv H6; auto|]. destruct (clear_stk_spec saved_stk ^(a2 + 99)%a) as [A B].
                        rewrite B; [|clear -Hastkend; solve_addr].
                        assert (^(a2 +length saved_words) < astkend)%a.
                        { rewrite /saved_words !app_length !map_length call.pop_env_instrs_length all_registers_list_difference_length /=.
                          clear -Hastkend. solve_addr. }
                        generalize (@push_words_lookup_spec saved_words stk a2 _ saved_stk H1 Hsaved_stk).
                        intros [AA BB].
                        assert (a2 = ^(a2 + 0)%a) as -> by (clear; solve_addr).
                        rewrite (AA 0 ltac:(rewrite /saved_words !app_length !map_length call.pop_env_instrs_length /=; lia)). simpl.
                        eexists; split; [reflexivity|]. clear -Hpcalt' Hpcaeq'; solve_addr.
                      + split; [clear -Hstkrange1 Hastkend; solve_addr|].
                        split; [clear -Hastkend Hrange2; solve_addr|].
                        split; [clear; solve_addr|].
                        split.
                        { intros. assert (∃ ri : RegName, list_difference all_registers [PC; call.r_stk] !! i = Some ri) as [ri Hri] by (eapply lookup_lt_is_Some_2; eauto).
                          eexists. split; eauto.
                          rewrite lookup_insert_ne; [|intro; subst ri; eapply elem_of_list_lookup_2 in Hri; eapply elem_of_list_difference in Hri; destruct Hri as [_ Hri]; eapply Hri; eapply elem_of_cons; left; auto].
                          rewrite lookup_insert_ne; [|intro; subst ri; eapply elem_of_list_lookup_2 in Hri; eapply elem_of_list_difference in Hri; destruct Hri as [_ Hri]; eapply Hri; eapply elem_of_cons; right; eapply elem_of_cons; left; auto].
                          destruct (clear_stk_spec saved_stk ^(a2 + 99)%a) as [QQ WW].
                          erewrite WW; [|clear -H1 Hastkend; solve_addr].
                          assert (^(a2 + length saved_words) < astkend)%a.
                          { rewrite /saved_words !app_length !map_length call.pop_env_instrs_length all_registers_list_difference_length /=.
                            clear -Hastkend. solve_addr. }
                          generalize (@push_words_lookup_spec saved_words stk a2 _ saved_stk H4 Hsaved_stk). intros [AA BB].
                          assert (UU: length saved_words = 99) by (rewrite /saved_words !app_length !map_length call.pop_env_instrs_length /= //).
                          rewrite UU in AA.
                          rewrite AA; [|clear -H1; lia].
                          rewrite /saved_words lookup_app_r; [|simpl; lia].
                          rewrite lookup_app_l; [|rewrite map_length all_registers_list_difference_length /=; lia].
                          simpl length. replace (S i - 1) with i by lia.
                          erewrite list_lookup_fmap. rewrite Hri /=.
                          destruct (Hregsdef ri) as [? [X _] ]. rewrite !X. reflexivity. }
                          destruct (clear_stk_spec saved_stk ^(a2 + 99)%a) as [QQ WW].
                          erewrite WW; [|clear -Hastkend; solve_addr].
                          assert (^(a2 + length saved_words) < astkend)%a.
                          { rewrite /saved_words !app_length !map_length call.pop_env_instrs_length all_registers_list_difference_length /=.
                            clear -Hastkend. solve_addr. }
                          generalize (@push_words_lookup_spec saved_words stk a2 _ saved_stk H1 Hsaved_stk). intros [AA BB].
                          assert (UU: length saved_words = 99) by (rewrite /saved_words !app_length !map_length call.pop_env_instrs_length /= //).
                          rewrite UU in AA.
                          rewrite (AA 32 ltac:(lia)). rewrite /saved_words lookup_app_r; [|clear; simpl; lia].
                          rewrite lookup_app_r; [|rewrite map_length all_registers_list_difference_length /=; lia].
                          rewrite map_length all_registers_list_difference_length lookup_app_l; [|simpl; lia].
                          split; [simpl; auto|].
                          rewrite /is_return. intros.
                          exists ^(^(a2 + 33) + i)%a.
                          split; [clear -Hastkend H4; solve_addr|].
                          split; [clear -Hastkend H4; solve_addr|].
                          rewrite WW; [|clear -Hastkend H4; solve_addr].
                          assert (^(^(a2 + 33) + i)%a = ^(a2 + (Z.to_nat (33 + i)))%a) as -> by (clear -Hastkend H4; solve_addr).
                          rewrite AA; [|lia].
                          rewrite /saved_words (lookup_app_r [inr _]); [|simpl; lia].
                          rewrite (lookup_app_r (map _ _)); [|rewrite map_length all_registers_list_difference_length /=; lia].
                          rewrite (lookup_app_r [inr _]); [|rewrite map_length all_registers_list_difference_length /=; lia].
                          rewrite map_length. assert ((Z.to_nat (33 + i) - length [inr (Regular (p, g, b, e, ^(pca' + -1)%a))] - length (list_difference all_registers [PC; call.r_stk]) - length [inr (Stk (length cs) URWLX a0 a1 ^(a2 + 32)%a)]) = i) as -> by (rewrite all_registers_list_difference_length /=; lia).
                          reflexivity. }
                  { generalize H1; intro CC.
                    rewrite app_length map_length /= in H3.
                    assert (Hn0: n0 < length rargs) by lia. clear H3.
                    simpl in H1. assert (Hrn0: exists rn0, rargs !! n0 = Some rn0) by (eapply lookup_lt_is_Some_2; eauto).
                    destruct Hrn0 as [rn0 Hrn0]. rewrite list_lookup_fmap Hrn0 /= in H1.
                    replace mem2''' with (ac, mem2''').2 by reflexivity.
                    rewrite -Hpush3. assert (a3 = ^(^(a2 + 100)%a + n0)%a) as -> by (clear -ZZ Hastkend Hn0; solve_addr).
                    erewrite push_words_no_check_in; [| rewrite map_length; instantiate (1 := e); clear -Hastkend H6 Ha1b Hrange2; inv H6; solve_addr| rewrite map_length; auto].
                    rewrite list_lookup_fmap Hrn0 /=.
                    rewrite /base.RegLocate.
                    split; [inv H1; auto|].
                    generalize (Hregsdef rn0). intros [w0 [Hw0 Hw0'] ].
                    rewrite Hw0 in H1; inv H1.
                    assert (Hreasonablew0: is_safe w).
                    { eapply elem_of_list_lookup_2 in Hrn0.
                      generalize (Hreasonable rn0 ltac:(eapply elem_of_cons; right; auto)).
                      rewrite /base.RegLocate Hw0 //. }
                    split; [eapply (interp_call_preserved Hreasonablew0 Hw0'); eauto|].
                    generalize (push_words_canStoreU Hnew_stk CC).
                    rewrite -ZZ. auto. }
                * econstructor; eauto.
                  { intros r. destruct (reg_eq_dec PC r); [subst r; rewrite lookup_insert|rewrite lookup_insert_ne //].
                    - eexists; split; [eauto|]. simpl. auto.
                    - destruct (reg_eq_dec call.r_stk r); [subst r; rewrite lookup_insert|rewrite lookup_insert_ne //].
                      + eexists; split; eauto. simpl.
                        destruct Hinterpwstk as [? [? [EE DD] ] ].
                        split; auto. split; auto. split; auto.
                        intros. simpl in DD. destruct (addr_eq_dec x a2).
                        * subst x. destruct (clear_stk_spec saved_stk ^(a2 + 99)%a) as [QQ WW].
                          rewrite WW; [|clear -Hastkend; solve_addr].
                          assert (SS: (^(a2 + length saved_words) < astkend)%a).
                          { rewrite /saved_words !app_length !map_length call.pop_env_instrs_length all_registers_list_difference_length /=.
                            clear -Hastkend. solve_addr. }
                          generalize (@push_words_lookup_spec saved_words stk a2 _ saved_stk SS Hsaved_stk). intros [AA BB].
                          replace a2 with ^(a2 + 0)%a by (clear; solve_addr).
                          rewrite (AA 0); [|rewrite /saved_words !app_length map_length /=; lia].
                          simpl. eauto.
                        * destruct (clear_stk_spec saved_stk ^(a2 + 99)%a) as [QQ WW].
                          rewrite WW; [|clear -Hastkend H3 n0; solve_addr].
                          assert (SS: (^(a2 + length saved_words) < astkend)%a).
                          { rewrite /saved_words !app_length !map_length call.pop_env_instrs_length all_registers_list_difference_length /=.
                            clear -Hastkend. solve_addr. }
                          generalize (@push_words_lookup_spec saved_words stk a2 _ saved_stk SS Hsaved_stk). intros [AA BB].
                          rewrite BB; [|left; clear -H3 n0; solve_addr].
                          eapply DD. clear -H3 n0; solve_addr.
                      + destruct (Hregsdef r) as [wr [Hr Hinterpr] ].
                        eexists; split; eauto.
                        assert (exists i, (list_difference all_registers [PC; call.r_stk]) !! i = Some r) as [i Hi].
                        { eapply elem_of_list_lookup. eapply elem_of_list_difference.
                          split; [apply all_registers_correct|].
                          eapply not_elem_of_cons; split; auto.
                          eapply not_elem_of_cons; split; auto.
                          apply not_elem_of_nil. }
                        generalize Hi; intros EE. eapply lookup_lt_Some in EE.
                        assert (JJ: saved_words !! (S i) = Some wr).
                        { rewrite /saved_words lookup_app_r; [|simpl; lia].
                          rewrite lookup_app_l; [|rewrite map_length /=; simpl in EE; lia].
                          simpl length. replace (S i - 1) with i by lia.
                          erewrite list_lookup_fmap. rewrite Hi /= Hr //. }
                        generalize (push_words_canStoreU Hsaved_stk JJ).
                        simpl in EE. intro FF.
                        destruct wr; simpl; auto.
                        destruct c0; simpl; simpl in Hinterpr; auto.
                        destruct Hinterpr as [? [? [CC ?] ] ].
                        do 3 (split; auto). intros x XX.
                        generalize (H3 x XX). intros [wx Hwx].
                        simpl in FF. destruct (clear_stk_spec saved_stk ^(a2 + 99)%a) as [QQ WW].
                        apply leb_addr_spec in FF. rewrite all_registers_list_difference_length in EE.
                        rewrite WW; [|clear -FF EE XX Hastkend Hrange2; solve_addr].
                        assert (SS: (^(a2 + length saved_words) < astkend)%a).
                        { rewrite /saved_words !app_length !map_length call.pop_env_instrs_length all_registers_list_difference_length /=.
                          clear -Hastkend. solve_addr. }
                        generalize (@push_words_lookup_spec saved_words stk a2 _ saved_stk SS Hsaved_stk). intros [AA BB].
                        destruct (Addr_lt_dec x a2) as [UU | UU].
                        * rewrite BB; auto.
                        * assert (exists j, j < length saved_words /\ x = ^(a2 + j)%a).
                          { rewrite /saved_words !app_length !map_length call.pop_env_instrs_length /=.
                            exists (Z.to_nat (z_of x - z_of a2)).
                            clear -FF EE XX Hastkend Hrange2 UU; split; solve_addr. }
                          destruct H4 as [j [HH GG] ].
                          rewrite GG (AA j HH).
                          rewrite list_lookup_lookup_total_lt; eauto. }
                  { intros. destruct (clear_stk_spec saved_stk ^(a2 + 99)%a) as [QQ WW].
                    destruct Hinterpwstk as [X1 [X2 [X3 X4] ] ].
                    destruct (Addr_lt_dec a3 ^(a2 + 99)%a) as [FF|FF].
                    - clear -X2 FF Hastkend Hrange2. solve_addr.
                    - rewrite QQ in H1. destruct H1; congruence.
                      clear -FF; solve_addr. }
                  { intros. destruct (clear_stk_spec saved_stk ^(a2 + 99)%a) as [QQ WW].
                    destruct (Addr_lt_dec a3 ^(a2 + 99)%a) as [FF|FF]; [|rewrite QQ in H1; [inv H1|clear -FF; solve_addr] ].
                    rewrite WW in H1; auto.
                    assert (SS: (^(a2 + length saved_words) < astkend)%a).
                    { rewrite /saved_words !app_length !map_length call.pop_env_instrs_length all_registers_list_difference_length /=.
                      clear -Hastkend. solve_addr. }
                    generalize (@push_words_lookup_spec saved_words stk a2 _ saved_stk SS Hsaved_stk). intros [AA BB].
                    replace mem2''' with (ac, mem2''').2 by reflexivity.
                    rewrite -Hpush3. rewrite /saved_words !app_length !map_length call.pop_env_instrs_length /= in BB.
                    destruct (Addr_lt_dec a3 a2) as [FF'|FF'].
                    { rewrite BB in H1; [|left; auto].
                      erewrite push_words_no_check_spec; [|rewrite map_length; instantiate (1 := e); clear -Hastkend H6 Ha1b Hrange2; inv H6; solve_addr| rewrite map_length; clear -FF; left; solve_addr].
                      rewrite lookup_insert_ne; [|clear -FF; solve_addr].
                      rewrite lookup_insert_ne; [|clear -FF'; solve_addr].
                      replace mem2'' with (ab, mem2'').2 by reflexivity.
                      rewrite -Hpush2. erewrite push_words_no_check_spec; [|rewrite  !map_length !app_length map_length call.pop_env_instrs_length /=; instantiate (1 := e); clear -Hastkend H6 Ha1b Hrange2; inv H6; solve_addr|clear -FF'; left; solve_addr].
                      rewrite lookup_insert_ne; [|clear -FF'; solve_addr].
                      replace mem2' with (aa, mem2').2 by reflexivity.
                      rewrite -Hpush1. erewrite push_words_no_check_spec; [|rewrite  !map_length all_registers_list_difference_length /=; instantiate (1 := e); clear -Hastkend H6 Ha1b Hrange2; inv H6; solve_addr|clear -FF'; left; solve_addr].
                      rewrite lookup_insert_ne; [|clear -FF'; solve_addr].
                      destruct (Hstksim _ _ H1) as [Q [W E] ].
                      do 2 (split; auto).
                      destruct w; auto.
                      destruct c0; simpl in W; simpl; auto.
                      destruct W as [W1 [W2 [W4 W3] ] ]. do 3 (split; auto).
                      intros x T. generalize (W3 _ T); intros [wx T'].
                      rewrite /canBeStored /= in E. apply leb_addr_spec in E.
                      rewrite WW; [|clear -FF E T; solve_addr].
                      rewrite BB; [|clear -FF' E T; solve_addr]. eauto. }
                    { assert (GG: exists j, j < 99 /\ a3 = ^(a2 + j)%a).
                      { exists (Z.to_nat (z_of a3 - z_of a2)).
                        clear -FF FF' Hastkend Hrange2; split; solve_addr. }
                      destruct GG as [j [GG1 GG2] ].
                      erewrite push_words_no_check_spec; [|rewrite map_length; instantiate (1 := e); clear -Hastkend H6 Ha1b Hrange2; inv H6; solve_addr| rewrite map_length; clear -FF; left; solve_addr].
                      rewrite lookup_insert_ne; [|clear -FF; solve_addr].
                      destruct (addr_eq_dec a2 a3) as [DD|DD]; [subst a3; rewrite -DD lookup_insert|rewrite lookup_insert_ne; auto].
                      - rewrite AA in H1; [|rewrite /saved_words !app_length !map_length call.pop_env_instrs_length /= //].
                        assert (j = 0) as -> by (clear -DD GG1 Hastkend Hrange2; solve_addr).
                        simpl in H1. inv H1.
                        split; [simpl; f_equal; f_equal; f_equal; auto; clear -Hpcaeq' Hpcalt'; solve_addr|].
                        split; [|rewrite /canBeStored /=; destruct g; try congruence; auto].
                        apply HinterpPC.
                      - rewrite GG2 AA in H1; [|rewrite /saved_words !app_length !map_length call.pop_env_instrs_length /= //].
                        destruct (lt_dec j 33) as [AQ|AQ].
                        + replace mem2'' with (ab, mem2'').2 by reflexivity.
                          rewrite -Hpush2. erewrite push_words_no_check_spec; [|rewrite  !map_length !app_length map_length call.pop_env_instrs_length /=; instantiate (1 := e); clear -Hastkend H6 Ha1b Hrange2; inv H6; solve_addr|clear -GG2 AQ Hastkend; left; solve_addr].
                          destruct (nat_eq_dec j 32).
                          * subst j. rewrite GG2 lookup_insert.
                            simpl in H1. inv H1.
                            split; auto. split; [|rewrite /canBeStored !lookup_app_r /=; [apply leb_addr_spec; clear; rewrite map_length all_registers_list_difference_length /=; solve_addr|rewrite map_length all_registers_list_difference_length;lia] ].
                            simpl. destruct Hinterpwstk as [? [? [II ?] ] ].
                            do 3 (split; auto). simpl in H3.
                            intros x Hx. destruct (Addr_lt_dec x a2) as [PP|PP].
                            { rewrite WW; [|clear -PP; solve_addr].
                              rewrite BB; [|left; auto]. eapply H3. clear -Hx PP; solve_addr. }
                            rewrite lookup_app_r map_length all_registers_list_difference_length /= in Hx; [|lia].
                            rewrite WW; [|clear -Hx; solve_addr].
                            assert (exists j, j < 32 /\ x = ^(a2 + j)%a) as [j [Hjt Hxj] ].
                            { exists (Z.to_nat (z_of x - z_of a2)).
                              clear -PP Hx; split; solve_addr. }
                            rewrite Hxj AA; [|rewrite /saved_words !app_length !map_length call.pop_env_instrs_length /=; lia].
                            rewrite list_lookup_lookup_total_lt; eauto.
                            rewrite /saved_words !app_length !map_length call.pop_env_instrs_length /=; clear -Hjt; lia.
                          * rewrite lookup_insert_ne; [|clear -n GG2 Hastkend; solve_addr].
                            replace mem2' with (aa, mem2').2 by reflexivity.
                            rewrite -Hpush1. destruct (nat_eq_dec j 0); [subst j|].
                            { elim DD; rewrite GG2; clear; solve_addr. }
                            assert (GG3: a3 = ^(^(a2 + 1)%a + (j - 1)%nat)%a).
                            { clear -GG2 n0 Hastkend; solve_addr. }
                            rewrite GG3. erewrite push_words_no_check_in with (a := ^(a2 + 1)%a) (i := j - 1); [|rewrite !map_length all_registers_list_difference_length /=; instantiate (1 := e); clear -Hastkend H6 Ha1b Hrange2; inv H6; solve_addr| rewrite !map_length all_registers_list_difference_length /=; clear -AQ n; lia].
                            generalize (push_words_canStoreU Hsaved_stk H1). intro Hcan.
                            rewrite /saved_words lookup_app_r in H1; [|simpl; clear -n0; lia].
                            rewrite lookup_app_l in H1; [|rewrite map_length all_registers_list_difference_length /=; clear -AQ n; lia].
                            simpl length in H1. erewrite !list_lookup_fmap.
                            erewrite list_lookup_fmap in H1.
                            destruct (list_difference all_registers [PC; call.r_stk] !! (j - 1)) as [r|] eqn:Hr; inv H1.
                            simpl. split; auto. split; [|rewrite /canBeStored /=; rewrite GG3 in Hcan; auto].
                            destruct (Hregsdef r) as [wr [Hwr Hinterpwr] ].
                            rewrite Hwr. destruct wr; auto.
                            destruct c0; simpl in Hinterpwr; simpl; auto.
                            destruct Hinterpwr as [F1 [F2 [F4 F3] ] ].
                            do 3 (split; auto). rewrite Hwr /= in Hcan.
                            apply leb_addr_spec in Hcan. intros x Hx.
                            rewrite WW; [|clear -Hx Hcan AQ Hastkend; solve_addr].
                            destruct (Addr_lt_dec x a2) as [RR|RR].
                            { rewrite BB; [|left; auto].
                              eapply F3; auto. }
                            assert (exists k, k < j /\ x = ^(a2 + k)%a) as [k [Hk ->] ].
                            { exists (Z.to_nat (z_of x - z_of a2)). clear -Hx Hcan Hastkend AQ RR; split; solve_addr. }
                            rewrite AA; [|rewrite /saved_words !app_length !map_length call.pop_env_instrs_length /=; clear -Hk AQ; lia].
                            rewrite list_lookup_lookup_total_lt; [|rewrite /saved_words !app_length !map_length call.pop_env_instrs_length /=; clear -Hk AQ; lia]. eauto.
                        + replace mem2'' with (ab, mem2'').2 by reflexivity.
                          rewrite - Hpush2. assert (exists k, k < 66 /\ a3 = ^(^(a2 + 33)%a + k)%a /\ j = 33 + k) as [k [GG3 [GG4 GG5] ] ].
                          { exists (Z.to_nat (z_of a3 - z_of ^(a2 + 33)%a)).
                            clear -GG1 GG2 AQ Hastkend; split; [|split]; solve_addr. }
                          rewrite GG4. erewrite push_words_no_check_in; [|rewrite !map_length !app_length map_length call.pop_env_instrs_length /=; instantiate (1 := e); clear -Hastkend H6 Ha1b Hrange2 GG3; inv H6; solve_addr| rewrite map_length !app_length map_length call.pop_env_instrs_length /=; exact GG3].
                          rewrite /saved_words lookup_app_r in H1; [|simpl; clear -AQ; lia].
                          rewrite lookup_app_r in H1; [|rewrite map_length all_registers_list_difference_length /=; clear -AQ; lia].
                          rewrite map_length all_registers_list_difference_length lookup_app_r in H1; [|simpl; clear -AQ; lia].
                          simpl length in H1. replace (j - 1 - 31 - 1) with k in H1 by (clear -GG5; lia).
                          rewrite 2!map_app map_map.
                          match goal with H1: ?X !! k = Some w |- context [?Y !! k] => assert (map translate_word X = Y) as <- end.
                          { reflexivity. }
                          erewrite list_lookup_fmap. rewrite H1. split; auto.
                          assert (exists nw, w = inl nw) as [nw ->]; [|split; simpl; auto; rewrite /canBeStored /= //].
                          { match goal with H1: ?X !! k = Some w |- _ => assert (@list_filter (Z + base.Cap) (fun w => match w with inl _ => True | _ => False end) ltac:(destruct x; [left; auto|right; intro Z; elim Z; auto]) X = X) by reflexivity end.
                            rewrite -H2 in H1. eapply elem_of_list_lookup_2 in H1.
                            eapply elem_of_list_filter in H1. destruct H1 as [Q _].
                            destruct w; eauto. elim Q; auto. } } }
                  { assert (Hhgood: forall a, is_Some (h !! a) -> mem2''' !! a = mem2 !! a).
                    { intros x Hx. eapply elem_of_dom in Hx.
                      generalize (Hdisj _ Hx). intros Hxx.
                      replace mem2''' with (ac, mem2''').2 by reflexivity.
                      rewrite -Hpush3. destruct (Hinterpwstk) as [_ [Hstkbound ?] ].
                      erewrite push_words_no_check_spec; [|instantiate (1:=e); rewrite map_length; clear -Hastkend Hrange2 Ha1b H6; inv H6; solve_addr |right; rewrite map_length; clear -Hastkend Hrange2 Hxx Hstkbound; solve_addr].
                      rewrite lookup_insert_ne; [|clear -Hastkend Hrange2 Hxx Hstkbound; solve_addr].
                      rewrite lookup_insert_ne; [|clear -Hastkend Hrange2 Hxx Hstkbound; solve_addr].
                      replace mem2'' with (ab, mem2'').2 by reflexivity.
                      rewrite -Hpush2. erewrite push_words_no_check_spec; [|instantiate (1:=e); rewrite map_length !app_length map_length call.pop_env_instrs_length /=; clear -Hastkend Hrange2 Ha1b H6; inv H6; solve_addr |right; rewrite map_length !app_length map_length call.pop_env_instrs_length /=; clear -Hastkend Hrange2 Hxx Hstkbound; solve_addr].
                      rewrite lookup_insert_ne; [|clear -Hastkend Hrange2 Hxx Hstkbound; solve_addr].
                      replace mem2' with (aa, mem2').2 by reflexivity.
                      rewrite -Hpush1. erewrite push_words_no_check_spec; [|instantiate (1:=e); rewrite !map_length all_registers_list_difference_length /=; clear -Hastkend Hrange2 Ha1b H6; inv H6; solve_addr |right; rewrite !map_length all_registers_list_difference_length /=; clear -Hastkend Hrange2 Hxx Hstkbound; solve_addr].
                      rewrite lookup_insert_ne; [|clear -Hastkend Hrange2 Hxx Hstkbound; solve_addr].
                      reflexivity. }
                    assert (Hcslt: forall dx stkx, stack dx cs = Some stkx -> forall x, is_Some (stkx !! x) -> (x < a0)%a).
                    { intros. generalize (proj1 (stack_is_Some _ _) ltac:(eexists; apply H1)).
                      intros Hxlt.
                      apply (Hstkdisj dx (length cs) Hxlt stkx stk ltac:(rewrite /stack; destruct (nat_eq_dec dx (length cs)); [lia|fold stack; rewrite H1; auto]) ltac:(rewrite /stack; destruct (nat_eq_dec (length cs) (length cs)); [|lia]; auto) x a0 H2).
                      destruct Hinterpwstk as [? [? XX] ]. eapply XX.
                      simpl. clear -Hstkrange1 Hastkend Hrange2. solve_addr. }
                    assert (Hstkgood: forall a, (a < a0)%a -> mem2''' !! a = mem2 !! a).
                    { intros x Hx. replace mem2''' with (ac, mem2''').2 by reflexivity.
                      rewrite -Hpush3. erewrite push_words_no_check_spec; [|instantiate (1:=e); rewrite map_length; clear -Hastkend Hrange2 Ha1b H6; inv H6; solve_addr |left; clear -Hx Hstkrange1; solve_addr].
                      rewrite lookup_insert_ne; [|clear -Hx Hstkrange1; solve_addr].
                      rewrite lookup_insert_ne; [|clear -Hx Hstkrange1; solve_addr].
                      replace mem2'' with (ab, mem2'').2 by reflexivity.
                      rewrite -Hpush2. erewrite push_words_no_check_spec; [|instantiate (1:=e); rewrite map_length !app_length map_length call.pop_env_instrs_length /=; clear -Hastkend Hrange2 Ha1b H6; inv H6; solve_addr |left; clear -Hx Hstkrange1; solve_addr].
                      rewrite lookup_insert_ne; [|clear -Hx Hstkrange1; solve_addr].
                      replace mem2' with (aa, mem2').2 by reflexivity.
                      rewrite -Hpush1. erewrite push_words_no_check_spec; [|instantiate (1:=e); rewrite !map_length all_registers_list_difference_length /=; clear -Hastkend Hrange2 Ha1b H6; inv H6; solve_addr |left; clear -Hx Hstkrange1; solve_addr].
                      rewrite lookup_insert_ne; [|clear -Hx Hstkrange1; solve_addr].
                      reflexivity. }
                    eapply sim_cs_call_preserve; eauto. }
              + intros. destruct (reg_eq_dec PC r); [subst r| rewrite lookup_insert_ne // in H1; rewrite lookup_insert_ne //].
                { rewrite lookup_insert in H1; rewrite lookup_insert.
                  assert (Hwrf_reasonable: is_safe wrf).
                  { generalize (Hreasonable rf ltac:(eapply elem_of_cons; left; auto)).
                    rewrite /base.RegLocate Hwrf //. }
                  inv H1. destruct wrf; simpl; auto. destruct c0; inv Hwrf_reasonable; auto.
                  destruct c0 as [ [ [ [pp gg] bb] ee] qq]. destruct pp; simpl; auto. }
                destruct (reg_eq_dec call.r_stk r); [subst r| rewrite lookup_insert_ne // in H1; rewrite lookup_insert_ne //].
                { rewrite lookup_insert; rewrite lookup_insert in H1.
                  inv H1; simpl; auto. }
                destruct (reg_eq_dec rf r); [subst r; rewrite lookup_insert; rewrite lookup_insert in H1; inv H1; simpl; auto| rewrite lookup_insert_ne // in H1; rewrite lookup_insert_ne //].
                eapply lookup_gset_to_gmap_Some in H1. destruct H1.
                eapply lookup_gset_to_gmap_Some; split; auto. inv H2; auto.
              + assert (Hhgood: forall a, is_Some (h !! a) -> mem2''' !! a = mem2 !! a).
                { intros x Hx. apply elem_of_dom in Hx.
                  generalize (Hdisj _ Hx). intros Hxx.
                  replace mem2''' with (ac, mem2''').2 by reflexivity.
                  rewrite -Hpush3. destruct (Hinterpwstk) as [_ [Hstkbound ?] ].
                  erewrite push_words_no_check_spec; [|instantiate (1:=e); rewrite map_length; clear -Hastkend Hrange2 Ha1b H6; inv H6; solve_addr |right; rewrite map_length; clear -Hastkend Hrange2 Hxx Hstkbound; solve_addr].
                  rewrite lookup_insert_ne; [|clear -Hastkend Hrange2 Hxx Hstkbound; solve_addr].
                  rewrite lookup_insert_ne; [|clear -Hastkend Hrange2 Hxx Hstkbound; solve_addr].
                  replace mem2'' with (ab, mem2'').2 by reflexivity.
                  rewrite -Hpush2. erewrite push_words_no_check_spec; [|instantiate (1:=e); rewrite map_length !app_length map_length call.pop_env_instrs_length /=; clear -Hastkend Hrange2 Ha1b H6; inv H6; solve_addr |right; rewrite map_length !app_length map_length call.pop_env_instrs_length /=; clear -Hastkend Hrange2 Hxx Hstkbound; solve_addr].
                  rewrite lookup_insert_ne; [|clear -Hastkend Hrange2 Hxx Hstkbound; solve_addr].
                  replace mem2' with (aa, mem2').2 by reflexivity.
                  rewrite -Hpush1. erewrite push_words_no_check_spec; [|instantiate (1:=e); rewrite !map_length all_registers_list_difference_length /=; clear -Hastkend Hrange2 Ha1b H6; inv H6; solve_addr |right; rewrite !map_length all_registers_list_difference_length /=; clear -Hastkend Hrange2 Hxx Hstkbound; solve_addr].
                  rewrite lookup_insert_ne; [|clear -Hastkend Hrange2 Hxx Hstkbound; solve_addr].
                  reflexivity. }
                intros. rewrite (Hhgood _ ltac:(eexists; apply H1)). auto.
              + auto. }
  Qed.

Local Transparent all_registers.
  Lemma overlay_to_cap_lang_fsim:
    forall (c: overlay_component),
      is_program e_stk _ _ _ _ lang.can_address_only lang.pwlW lang.is_global c ->
      @forward_simulation_tc overlay_lang cap_lang (lang.initial_state b_stk e_stk c) (initial_state call.r_stk b_stk e_stk (compile c)) sim sim_val.
  Proof.
    intros. econstructor.
    - inv H0. cbn -[list_to_set].
      econstructor.
      + repeat econstructor.
      + intros. econstructor.
        { intros; destruct d1.
          * simpl in H2. inv H2.
            rewrite lookup_empty in H4. inv H4. congruence.
          * simpl in H2. congruence. }
        { intros. econstructor.
          * intros. destruct (reg_eq_dec r call.r_stk).
            { subst r. rewrite lookup_insert. eauto.
              eexists; split; eauto. simpl. split; auto.
              split; [solve_addr|].
              split; [intros; try congruence|].
              intros. solve_addr. }
            { rewrite lookup_insert_ne; auto.
              destruct (reg_eq_dec r PC).
              - subst r. rewrite lookup_insert.
                eexists; split; eauto. inv Hwfcomp.
                destruct Hw_main as [A [B C] ]. simpl in A.
                destruct w_main; simpl; auto.
                destruct c; simpl in A.
                + destruct c as [ [ [ [p g] b] e] a].
                  simpl in B. auto.
                + elim A.
                + elim A.
              - rewrite lookup_insert_ne; auto.
                exists (inl 0%Z). split; [|simpl; auto].
                rewrite lookup_gset_to_gmap_Some. split; auto.
                eapply all_registers_s_correct. }
          * intros. rewrite lookup_empty in H1. destruct H1; congruence.
          * intros. rewrite lookup_empty in H1. inv H1.
          * econstructor. }
        { intros. destruct (reg_eq_dec r call.r_stk).
          * subst r. rewrite lookup_insert in H1.
            inv H1. rewrite lookup_insert. reflexivity.
          * rewrite lookup_insert_ne in H1; auto.
            rewrite lookup_insert_ne; auto.
            destruct (reg_eq_dec r PC).
            { subst r. rewrite lookup_insert in H1.
              rewrite lookup_insert. inv H1. reflexivity. }
            { rewrite lookup_insert_ne in H1; auto.
              rewrite lookup_insert_ne; auto.
              rewrite lookup_gset_to_gmap_Some.
              eapply lookup_gset_to_gmap_Some in H1.
              destruct H1 as [A B]; inv B.
              split; auto. } }
        { intros. rewrite lookup_fmap H1 /=. split; auto.
          inv Hwfcomp. inv Hwf_pre. generalize (Hnpwl _ _ H1).
          intros [A [B C] ]; repeat split; auto. }
        { intros. inv Hwfcomp. inv Hwf_pre. eapply Hdisjstk; auto. }
    - intros. inv H1. inv H2. inv H1.
      assert (e0 = e1 /\ t1 = [] /\ t2 = []).
      { destruct t1, t2; simpl in H2; inv H2; auto.
        - symmetry in H5. apply app_eq_nil in H5.
          destruct H5 as [A B]; inv B.
        - symmetry in H5. apply app_eq_nil in H5.
          destruct H5 as [A B]; inv B. }
      destruct H1 as [A [B C] ]; subst e0; subst t1; subst t2.
      inv H2. rewrite !app_nil_l.
      inv H4. inv Hsexpr.
      { symmetry in H2; eapply fill_inv_instr in H2.
        destruct H2; subst K; subst e1'.
        inv H3. }
      { symmetry in H2; eapply fill_inv_instr in H2.
        destruct H2; subst K; subst e1'.
        inv H3. }
      inv H3.
      + (* General exec case*)
        assert (K = [lang.SeqCtx] /\ f1 = lang.Executable) as [-> ->].
        { destruct K; [simpl in H1; inv H1|]. rewrite cons_is_app in H1.
          destruct e; rewrite ectxi_language.fill_app /= in H1.
          inv H1. symmetry in H5; eapply fill_inv_instr in H5.
          destruct H5 as [-> ?]. inv H1; auto. }
        specialize (Hinvs ltac:(rewrite can_step_fill /can_step /=; auto)).
        inv Hinvs. clear H1. inv H2. inv H4.
        * (* not correct PC *)
          simpl in H3. eexists. split.
          { eapply tc_once. exists []. econstructor; eauto.
            { f_equal; eauto. instantiate (1 := []).
              instantiate (2 := []). reflexivity. }
            econstructor; eauto. instantiate (2 := [SeqCtx]).
            reflexivity. econstructor.
            eapply step_exec_fail. simpl; intro HA.
            rewrite /RegLocate in HA.
            inv HA. destruct (reg2 !! PC) as [pcw2|] eqn:X; try congruence.
            subst pcw2. rewrite /base.RegLocate in H3. inv Hcswf.
            destruct (Hregsdef PC) as [pcw1 [Y Y'] ]. rewrite Y in H3.
            generalize (Hsregs PC _ Y). rewrite X; intros Z; inv Z.
            destruct pcw1; simpl in H5; try congruence.
            destruct c0.
            + inv H5. eapply H3. econstructor; eauto.
            + inv H5. eapply H3. econstructor; eauto.
            + inv H5. destruct H4 as [? | [? | ?] ]; congruence. }
          { simpl. econstructor; eauto.
            - repeat econstructor.
            - rewrite /can_step /=. intros [?|?]; discriminate. }
        * (* not correct PC stack *)
          simpl in H5. rewrite /base.RegLocate in H5.
          destruct (reg1 !! PC) as [pcw1|] eqn:X; try congruence. subst pcw1.
          inv Hcswf. destruct (Hregsdef PC) as [pcw1 [HA HB] ].
          rewrite X in HA; inv HA. simpl in HB. destruct HB.
          simpl in H6. destruct (nat_eq_dec d (@length Stackframe cs)); try congruence.
        * (* Regular exec *)
          simpl in H5, H6. rewrite H5 in H6. simpl.
          assert ((exists r, decodeInstrW' (base.MemLocate h a) = Jmp r) \/ (forall r, decodeInstrW' (base.MemLocate h a) <> Jmp r)).
          { clear. destruct (decodeInstrW' (base.MemLocate h a)); eauto. }
          destruct H1 as [HisJmp | HnisJmp].
          { (* Jmp case *)
            destruct HisJmp as [rjmp HisJmp].
            inv Hcswf. destruct (Hregsdef rjmp) as [wrjmp [HA Hinterp] ].
            assert (Hne: (exists br er ar, wrjmp = inr (Ret br er ar)) \/ (forall br er ar, wrjmp <> inr (Ret br er ar))).
            { destruct wrjmp; auto. destruct c0; eauto. }
            destruct Hne as [ [br [er [ar ->] ] ] |Hne]; cycle 1.
            - (* Regular jmp *)
              set res := exec (decodeInstrW (mem2 !m! a)) (reg2, mem2).
              exists ([Seq (Instr res.1)], res.2).
              split.
              + eapply tc_once. econstructor. econstructor; eauto.
                * f_equal; eauto. instantiate (1 := []).
                  instantiate (2 := []). reflexivity.
                * instantiate (1 := res.2).
                  instantiate (1 := []). reflexivity.
                * econstructor; eauto. instantiate (2 := [SeqCtx]).
                  reflexivity. reflexivity.
                  rewrite /base.RegLocate in H5.
                  destruct (reg1 !! PC) eqn:HPC; [|congruence].
                  subst s. generalize (Hsregs _ _ HPC); simpl.
                  intros HPC'. econstructor; simpl; eauto.
                  econstructor; simpl; eauto.
                  { rewrite /RegLocate HPC'. reflexivity. }
                  { rewrite /RegLocate HPC'. generalize (isCorrectPC_translate_word H6).
                    simpl; auto. }
              + rewrite HisJmp. rewrite /base.MemLocate in HisJmp.
                destruct (Hregsdef PC) as [wpc [HPC HinterpPC] ].
                rewrite /base.RegLocate HPC in H5. inv H5.
                generalize (Hsregs _ _ HPC). intro HPC'.
                simpl in HinterpPC. destruct HinterpPC as [HnpwlU Hdom].
                generalize (Hdom a ltac:(inv H6; auto)); intros Haa.
                eapply elem_of_dom in Haa. destruct Haa as [wa Hha].
                rewrite Hha in HisJmp. generalize (Hsh _ _ Hha).
                intros [Hma [HnpwlW [Hisglob Hcan_address] ] ].
                subst res. rewrite /MemLocate Hma -decodeInstrW_translate_word // HisJmp.
                generalize (Hsregs _ _ HA). intros HB.
                rewrite /= /RegLocate /base.RegLocate HA HB /=.
                destruct wrjmp as [njmp | cap] eqn:Hwrjmp; simpl.
                * econstructor.
                  { repeat econstructor. }
                  { intros. econstructor; eauto.
                    - econstructor; eauto.
                      replace (inl njmp) with (word_of_argument reg1 (inr rjmp)) by (simpl; rewrite /base.RegLocate HA //).
                      eapply Hregsdef_preserve_word_of_arg; eauto.
                    - replace (inl njmp) with (word_of_argument reg1 (inr rjmp)) by (simpl; rewrite /base.RegLocate HA //).
                      replace (inl njmp) with (translate_word (word_of_argument reg1 (inr rjmp))) by (simpl; rewrite /base.RegLocate HA //).
                      eapply Hsregs_preserve_word_of_arg; eauto. }
                * destruct cap; [| | congruence].
                  { destruct c0 as [ [ [ [p1 g1] b1] e1] a1].
                    destruct (perm_eq_dec p1 E).
                    - subst p1; simpl. econstructor; eauto.
                      + repeat econstructor.
                      + intros. econstructor; eauto.
                        * econstructor; eauto.
                          simpl. intros. destruct (reg_eq_dec PC r).
                          { subst r; rewrite lookup_insert.
                            eexists; split; eauto. }
                          { rewrite lookup_insert_ne; auto. }
                        * simpl. intros r w. destruct (reg_eq_dec PC r).
                          { subst r; rewrite !lookup_insert; inversion 1; simpl; auto. }
                          { rewrite !lookup_insert_ne //. auto. }
                    - rewrite updatePcPerm_cap_non_E; auto. simpl.
                      econstructor; eauto.
                      + repeat econstructor.
                      + intros. econstructor; eauto.
                        * econstructor; eauto.
                          simpl. intros. destruct (reg_eq_dec PC r).
                          { subst r; rewrite lookup_insert.
                            destruct p1; try congruence; eexists; split; eauto. }
                          { rewrite lookup_insert_ne; auto. }
                        * simpl. intros r w. destruct (reg_eq_dec PC r).
                          { destruct p1; try congruence; subst r; rewrite !lookup_insert; inversion 1; simpl; auto. }
                          { rewrite !lookup_insert_ne //. auto. } }
                  { destruct (perm_eq_dec p0 E).
                    - subst p0; simpl. econstructor; eauto.
                      + repeat econstructor.
                      + intros. econstructor; eauto.
                        * econstructor; eauto.
                          simpl. intros. destruct (reg_eq_dec PC r).
                          { subst r; rewrite lookup_insert.
                            eexists; split; eauto. }
                          { rewrite lookup_insert_ne; auto. }
                        * simpl. intros r w. destruct (reg_eq_dec PC r).
                          { subst r; rewrite !lookup_insert; inversion 1; simpl; auto. }
                          { rewrite !lookup_insert_ne //. auto. }
                    - rewrite updatePcPerm_cap_non_E; auto. simpl.
                      econstructor; eauto.
                      + repeat econstructor.
                      + intros. econstructor; eauto.
                        * econstructor; eauto.
                          simpl. intros. destruct (reg_eq_dec PC r).
                          { subst r; rewrite lookup_insert.
                            destruct p0; try congruence; eexists; split; eauto. }
                          { rewrite lookup_insert_ne; auto. }
                        * simpl. intros r w. destruct (reg_eq_dec PC r).
                          { destruct p0; try congruence; subst r; rewrite !lookup_insert; inversion 1; simpl; auto. }
                          { rewrite !lookup_insert_ne //. auto. } }
            - (* Return jump *)
              rewrite /base.RegLocate in H5.
              destruct (Hregsdef PC) as [wpc [HPC HinterpPC] ].
              rewrite HPC in H5; inv H5. generalize (Hsregs _ _ HPC); simpl.
              intros HPC'. simpl in Hinterp; destruct cs as [| [nregs nstk] cs']; [elim Hinterp|].
              destruct Hinterp as [ne_stk [na_stk [Hr_stk [Haris [ (pcp & pcg & pcb & pce & pca & HnewPC & Hcanexec & pcam1 & HnewPC' & Hpcam1eq) [Hrange [Hrange' [XE [XA [XB XC] ] ] ] ] ] ] ] ] ].
              simpl in HinterpPC. destruct HinterpPC as [HnpwlU Hdom].
              eexists ([Seq (Instr NextI)], (fmap translate_word nregs, mem2)).
              rewrite HisJmp. rewrite /lang.exec /base.RegLocate HA /=.
              split.
              + eapply tc_rtc_r.
                * eapply tc_once. econstructor. econstructor; eauto.
                  { f_equal; eauto. instantiate (1 := []).
                    instantiate (2 := []). reflexivity. }
                  { instantiate (1 := []). econstructor; try reflexivity.
                    instantiate (2 := [SeqCtx]). reflexivity.
                    econstructor. eapply step_exec_instr; simpl; auto.
                    rewrite /RegLocate HPC'; reflexivity.
                    rewrite /RegLocate HPC'. inv H6; econstructor; eauto. }
                * simpl. generalize (Hdom a ltac:(inv H6; auto)); intros Haa.
                  eapply elem_of_dom in Haa. destruct Haa as [wa Hha].
                  rewrite /base.MemLocate Hha in HisJmp. generalize (Hsh _ _ Hha).
                  intros [Hma [HnpwlW [Hisglob Hcan_address] ] ].
                  rewrite /MemLocate Hma -decodeInstrW_translate_word // HisJmp.
                  rewrite /= /RegLocate. generalize (Hsregs _ _ HA).
                  intros HA'. rewrite HA'. simpl. eapply rtc_l.
                  { exists []. eapply step_atomic with (t1:=[]).
                    1,2: reflexivity. cbn.
                    eapply ectx_language.Ectx_step with (K:=[]).
                    1,2: reflexivity. cbn. econstructor. }
                  simpl. rewrite /is_return in XC.
                  rewrite /update_reg /=.
                  assert (XD: forall i, i < 66 -> is_Some (activation_code !! i)).
                  { intros. apply lookup_lt_is_Some.
                    rewrite activation_code_length //. }
                  assert (XC': forall i, i < 66 -> exists ai, (ar + i)%a = Some ai /\ (ai < er)%a /\ (translate_word <$> activation_code) !! i = mem2 !! ai).
                  { intros. generalize (XC i H1). intros [ai [A [B C] ] ].
                    exists ai. split; auto. split; auto.
                    rewrite list_lookup_fmap C.
                    assert (exists wai, nstk !! ai = Some wai) as [wai Hwai].
                    { destruct (XD _ H1) as [wai Hwai].
                      rewrite Hwai in C; eauto. }
                    inv Hcs. generalize (Hstksim0 _ _ Hwai). rewrite Hwai.
                    simpl. intros [? [? ?] ]. congruence. }
                  eapply rtc_l.
                  { exists []. eapply step_atomic with (t1:=[]).
                    1,2: reflexivity. cbn.
                    eapply ectx_language.Ectx_step with (K:=[SeqCtx]).
                    1,2: reflexivity. econstructor. eapply step_exec_instr; eauto.
                    - rewrite /= /RegLocate lookup_insert; eauto.
                    - rewrite /= /RegLocate lookup_insert. econstructor; auto.
                      destruct (XC 0 ltac:(lia)) as [ar' [Har' [XX _] ] ].
                      clear -Hrange Haris Har' XX. solve_addr. }
                  simpl. generalize (XC' 0 ltac:(lia)). intros [ar' [XX [_ XY] ] ].
                  assert (ar = ar') by (clear -XX; solve_addr). subst ar'; clear XX.
                  rewrite list_lookup_fmap in XY. rewrite /activation_code /= in XY.
                  rewrite /MemLocate -XY /=. clear XY.
                  destruct (XC' 1 ltac:(lia)) as [arp1 [Harp1 [Hlow1 Hcode1] ] ].
                  rewrite decode_encode_instr_inv /= /RegLocate lookup_insert /update_reg /updatePC /RegLocate !(lookup_insert_ne _ (R 1 _) PC) // /= !lookup_insert Harp1 /update_reg /=.
                  eapply rtc_l.
                  { exists []. eapply step_atomic with (t1:=[]).
                    1,2: reflexivity. cbn.
                    eapply ectx_language.Ectx_step with (K:=[]).
                    1,2: reflexivity. cbn. econstructor. }
                  simpl. eapply rtc_l.
                  { exists []. eapply step_atomic with (t1:=[]).
                    1,2: reflexivity. cbn.
                    eapply ectx_language.Ectx_step with (K:=[SeqCtx]).
                    1,2: reflexivity. econstructor. eapply step_exec_instr; eauto.
                    - rewrite /= /RegLocate lookup_insert; eauto.
                    - rewrite /= /RegLocate lookup_insert. econstructor; auto.
                      clear -Hlow1 Hrange Harp1 Hlow1 Haris. solve_addr. }
                  simpl. rewrite list_lookup_fmap /= in Hcode1.
                  rewrite /MemLocate -Hcode1 /= decode_encode_instr_inv /= /RegLocate !(lookup_insert_ne _ PC (R 1 _)) // !lookup_insert.
                  assert (Harm1eq: (ar + -1)%a = Some (^(na_stk + 32)%a)).
                  { clear -Haris Hrange. solve_addr. }
                  rewrite Harm1eq /update_reg /=.
                  destruct (XC' 2 ltac:(lia)) as [arp2 [Harp2 [Hlow2 Hcode2] ] ].
                  assert ((arp1 + 1)%a = Some arp2) by (clear -Harp1 Harp2; solve_addr).
                  rewrite /updatePC /RegLocate /= (lookup_insert_ne _ (R 1 _) PC) // lookup_insert H1 /update_reg /=. clear H1.
                  eapply rtc_l.
                  { exists []. eapply step_atomic with (t1:=[]).
                    1,2: reflexivity. cbn.
                    eapply ectx_language.Ectx_step with (K:=[]).
                    1,2: reflexivity. cbn. econstructor. }
                  simpl. eapply rtc_l.
                  { exists []. eapply step_atomic with (t1:=[]).
                    1,2: reflexivity. cbn.
                    eapply ectx_language.Ectx_step with (K:=[SeqCtx]).
                    1,2: reflexivity. econstructor. eapply step_exec_instr; eauto.
                    - rewrite /= /RegLocate lookup_insert; eauto.
                    - rewrite /= /RegLocate lookup_insert. econstructor; auto.
                      clear -Hlow2 Hrange Harp2 Haris. solve_addr. }
                  simpl. rewrite list_lookup_fmap /= in Hcode2.
                  rewrite /MemLocate -Hcode2 /= decode_encode_instr_inv /= /RegLocate !(lookup_insert_ne _ PC (R 1 _)) // !lookup_insert.
                  rewrite andb_true_l.
                  assert ((br <=? ^(na_stk + 32))%a && (^(na_stk + 32) <? er)%a = true) as ->.
                  { clear -Hrange Harm1eq Haris Harp1 Hlow1. apply andb_true_iff.
                    split. apply leb_addr_spec. solve_addr.
                    apply ltb_addr_spec. solve_addr. }
                  rewrite /update_reg /=. inv Hcs.
                  generalize (Hstksim0 _ _ XB). simpl. intros [YA [ [_ YB] _] ].
                  rewrite /MemLocate YA /=.
                  destruct (XC' 3 ltac:(lia)) as [arp3 [Harp3 [Hlow3 Hcode3] ] ].
                  assert ((arp2 + 1)%a = Some arp3) by (clear -Harp2 Harp3; solve_addr).
                  rewrite /updatePC /RegLocate /= (lookup_insert_ne _ call.r_stk) // lookup_insert /= H1 /update_reg /=. clear H1.
                  eapply rtc_l.
                  { exists []. eapply step_atomic with (t1:=[]).
                    1,2: reflexivity. cbn.
                    eapply ectx_language.Ectx_step with (K:=[]).
                    1,2: reflexivity. cbn. econstructor. }
                  simpl. rewrite -!(insert_commute _ PC (R 1 _)) //.
                  rewrite -!(insert_commute _ PC call.r_stk) //.
                  rewrite !insert_insert. eapply rtc_transitive.
                  { eapply pop_env_instrs_spec with (rlist := list_difference all_registers [PC; call.r_stk]).
                    - replace (length (list_difference all_registers [PC; call.r_stk])) with 31 by reflexivity.
                      instantiate (1 := ^(na_stk + 1)%a).
                      clear -Haris. solve_addr.
                    - clear -Hrange. solve_addr.
                    - clear -Hrange Hrange' Harm1eq Harp1 Hlow1. solve_addr.
                    - instantiate (1 := ^(ar + 65)%a).
                      simpl length. destruct (XC 65 ltac:(lia)) as [arp65 [? _] ].
                      clear -H1 Harp3. solve_addr.
                    - clear -Hrange Harp3 Haris. solve_addr.
                    - destruct (XC 65 ltac:(lia)) as [arp65 [X [Y _] ] ].
                      clear -X Y; solve_addr.
                    - split; eapply not_elem_of_list; [left|right;left].
                    - simpl length. simpl Nat.mul.
                      intros i Hilt. generalize (XC' (3 + i) ltac:(lia)).
                      intros [ai [Hai [Hailt Hcodei] ] ].
                      exists ai. split; [clear -Harp3 Hai; solve_addr|].
                      rewrite /activation_code in Hcodei.
                      rewrite fmap_app lookup_app_r in Hcodei; [|simpl; lia].
                      rewrite fmap_app lookup_app_l in Hcodei; [|rewrite !fmap_length map_length call.pop_env_instrs_length /=; lia].
                      simpl length in Hcodei. replace (3 + i - 3) with i in Hcodei by lia.
                      rewrite -Hcodei. reflexivity.
                    - simpl length. intros i Hilt.
                      generalize (XA (31 - S i) ltac:(clear -Hilt; lia)).
                      intros [ri [Hri Hstkri] ].
                      exists (^(na_stk + S (31 - S i))%a).
                      split; [clear -Haris Hrange Hilt; solve_addr|].
                      exists ri; split; auto.
                      destruct (Hregsdef0 ri) as [rwi [Hrwi Hinterprwi] ].
                      exists rwi. split; eauto.
                      rewrite Hrwi in Hstkri.
                      generalize (Hstksim0 _ _ Hstkri). intros [? ?]; auto. }
                  eapply rtc_l.
                  { econstructor. econstructor; eauto.
                    - instantiate (2 := []). instantiate (3 := []).
                      reflexivity.
                    - econstructor.
                      + instantiate (2 := [SeqCtx]). reflexivity.
                      + reflexivity.
                      + econstructor. eapply step_exec_instr; eauto.
                        * rewrite /RegLocate lookup_insert //.
                        * rewrite /RegLocate lookup_insert.
                          econstructor; auto. destruct (XC' 65 ltac:(lia)) as [arp65 [Harp65 [Hlt65 ?] ] ].
                          clear -Hrange Harp65 Hlt65 Haris. solve_addr. }
                  rewrite !app_nil_l.
                  set (rlist := list_difference all_registers [PC; call.r_stk]).
                  rewrite /cap_lang.mem /MemLocate.
                  destruct (XC' 65 ltac:(lia)) as [arp65 [Harp65 [Hlt65 Hcode65] ] ].
                  replace (^(ar + 65)%a) with arp65 by (clear -Harp65; solve_addr).
                  rewrite /activation_code !fmap_app in Hcode65.
                  rewrite lookup_app_r in Hcode65; [|simpl; lia].
                  rewrite lookup_app_r in Hcode65; [|simpl; lia].
                  simpl in Hcode65. rewrite -Hcode65.
                  rewrite /decodeInstrW decode_encode_instr_inv.
                  rewrite /exec /reg /RegLocate.
                  rewrite (lookup_insert_ne _ PC) //.
                  rewrite lookup_insert. rewrite /isU /z_of_argument.
                  rewrite /verify_access.
                  assert ((^(na_stk + 1) + -1)%a = Some na_stk) as -> by (clear -Hrange; solve_addr).
                  destruct (Addr_le_dec br na_stk) as [_|X]; [|exfalso; clear -X Hrange; solve_addr].
                  destruct (Addr_lt_dec na_stk ^(na_stk + 1)%a) as [_|X]; [|exfalso; clear -X Hrange; solve_addr].
                  destruct (Addr_le_dec ^(na_stk + 1)%a ne_stk) as [_|X]; [|exfalso; clear -X Hrange Hrange'; solve_addr].
                  rewrite /update_reg /cap_lang.mem /reg /MemLocate.
                  generalize (Hstksim0 _ _ HnewPC'). intros [AA [AB AC] ].
                  rewrite AA.
                  assert (ZZ: (foldr (λ (r : RegName) (reg : Reg), <[r:=translate_word (base.RegLocate nregs r)]> reg) (<[R 1 eq_refl:=inr (RX, Directed, br, er, ^(na_stk + 32)%a)]> reg2) rlist) = <[PC := reg2 !r! PC]> (<[call.r_stk := reg2 !r! call.r_stk]> (translate_word <$> nregs))).
                  { eapply map_eq. intros.
                    assert (Hdup: NoDup rlist).
                    { subst rlist. apply NoDup_list_difference.
                      apply all_registers_NoDup. }
                    destruct (in_dec reg_eq_dec i rlist).
                    - rewrite (proj1 (foldr_insert_spec _ _ i Hdup) i0).
                      eapply elem_of_list_In in i0.
                      eapply elem_of_list_difference in i0.
                      destruct i0 as [Hin Hnin].
                      rewrite lookup_insert_ne; [|intro; subst i; eapply Hnin; left].
                      rewrite lookup_insert_ne; [|intro; subst i; eapply Hnin; right; left].
                      destruct (Hregsdef0 i) as [wi [Hwi _] ].
                      rewrite lookup_fmap /base.RegLocate Hwi; reflexivity.
                    - rewrite (proj2 (foldr_insert_spec _ _ i Hdup) n).
                      destruct (reg_eq_dec PC i); [subst i; rewrite lookup_insert lookup_insert_ne /RegLocate // HPC' //|].
                      rewrite (lookup_insert_ne _ PC) //.
                      destruct (reg_eq_dec call.r_stk i); [subst i; rewrite lookup_insert lookup_insert_ne /RegLocate //|].
                      destruct (Hregsdef call.r_stk) as [ww [XX _] ].
                      rewrite (Hsregs _ _ XX); auto.
                      exfalso. eapply n. eapply elem_of_list_In.
                      eapply elem_of_list_difference.
                      split. apply all_registers_correct.
                      intro. eapply elem_of_cons in H1.
                      destruct H1; [apply n0; auto|].
                      eapply elem_of_cons in H1. destruct H1; [apply n1; auto|].
                      eapply not_elem_of_nil; eauto. }
                  rewrite ZZ. rewrite insert_insert.
                  rewrite (insert_commute _ call.r_stk PC) //.
                  rewrite !insert_insert /=.
                  assert (YY: updatePC (<[PC:=inr (pcp, pcg, pcb, pce, pcam1)]> (<[call.r_stk:=inr (URWLX, Directed, br, ne_stk, ^(na_stk + 1)%a)]> (translate_word <$> nregs)), mem2) = (NextI, update_reg (<[PC:=inr (pcp, pcg, pcb, pce, pcam1)]> (<[call.r_stk:=inr (URWLX, Directed, br, ne_stk, ^(na_stk + 1)%a)]> (translate_word <$> nregs)), mem2) PC (inr (pcp, pcg, pcb, pce, pca)))).
                  { rewrite /updatePC /RegLocate lookup_insert /= Hpcam1eq.
                    destruct Hcanexec as [-> | [-> | ->] ]; auto. }
                  rewrite YY /update_reg /=.
                  rewrite insert_insert.
                  assert (XX: <[PC:=inr (pcp, pcg, pcb, pce, pca)]> (<[call.r_stk:=inr (URWLX, Directed, br, ne_stk, ^(na_stk + 1)%a)]> (translate_word <$> nregs)) = translate_word <$> nregs).
                  { eapply map_eq. intros.
                    destruct (reg_eq_dec i PC); [subst i|].
                    - rewrite lookup_insert lookup_fmap HnewPC /= //.
                    - rewrite lookup_insert_ne; auto.
                      destruct (reg_eq_dec i call.r_stk); [subst i|].
                      + rewrite lookup_insert lookup_fmap Hr_stk /= //.
                      + rewrite lookup_insert_ne; auto. }
                  rewrite XX. econstructor.
            + econstructor.
              * repeat econstructor.
              * intros _. econstructor; eauto.
                { intros. eapply Hstkdisj; eauto.
                  - generalize (proj1 (stack_is_Some _ _) ltac:(eexists; exact H2)); simpl; intros Hd1.
                    destruct (nat_eq_dec d1 (S (length cs'))); [lia|].
                    exact H2.
                  - generalize (proj1 (stack_is_Some _ _) ltac:(eexists; exact H3)); simpl; intros Hd2.
                    destruct (nat_eq_dec d2 (S (length cs'))); [lia|].
                    exact H3. }
                { inv Hcs; econstructor; eauto. }
                { intros r w X; rewrite lookup_fmap X /= //. } }
          assert ((exists r1 r2, decodeInstrW' (base.MemLocate h a) = Jnz r1 r2) \/ (forall r1 r2, decodeInstrW' (base.MemLocate h a) <> Jnz r1 r2)).
          { clear. destruct (decodeInstrW' (base.MemLocate h a)); eauto. }
          destruct H1 as [HisJnz | HnisJnz].
          { destruct HisJnz as [rjnz [rcond HisJnz] ].
            inv Hcswf. destruct (Hregsdef rjnz) as [wrjnz [HA Hinterp] ].
            destruct (Hregsdef rcond) as [wcond [HA' Hinterp_cond] ].
            assert (Hne: (exists br er ar, wrjnz = inr (Ret br er ar)) \/ (forall br er ar, wrjnz <> inr (Ret br er ar))).
            { destruct wrjnz; auto. destruct c0; eauto. }
            destruct Hne as [ [br [er [ar ->] ] ] |Hne]; cycle 1.
            - (* Regular jnz *)
              set res := exec (decodeInstrW (mem2 !m! a)) (reg2, mem2).
              exists ([@ectx_language.fill cap_ectx_lang [SeqCtx] (Instr res.1)], res.2).
              split.
              + eapply tc_once. econstructor. econstructor; eauto.
                * f_equal; eauto. instantiate (1 := []).
                instantiate (2 := []). reflexivity.
                * instantiate (1 := res.2).
                  instantiate (1 := []). reflexivity.
                * econstructor; eauto. econstructor.
                  rewrite /base.RegLocate in H5.
                  destruct (reg1 !! PC) eqn:HPC; [|congruence].
                  subst s. generalize (Hsregs _ _ HPC); simpl.
                  intros HPC'. econstructor; simpl; eauto.
                  econstructor; simpl; eauto.
                  { rewrite /RegLocate HPC'. reflexivity. }
                  { rewrite /RegLocate HPC'. generalize (isCorrectPC_translate_word H6).
                    simpl; auto. }
              + rewrite HisJnz. rewrite /base.MemLocate in HisJnz.
                destruct (Hregsdef PC) as [wpc [HPC HinterpPC] ].
                rewrite /base.RegLocate HPC in H5. inv H5.
                generalize (Hsregs _ _ HPC). intro HPC'.
                generalize (Hsregs _ _ HA'). intro HA''.
                simpl in HinterpPC. destruct HinterpPC as [HnpwlU Hdom].
                generalize (Hdom a ltac:(inv H6; auto)); intros Haa.
                eapply elem_of_dom in Haa. destruct Haa as [wa Hha].
                rewrite Hha in HisJnz. generalize (Hsh _ _ Hha).
                intros [Hma [HnpwlW [Hisglob Hcan_address] ] ].
                subst res. rewrite /MemLocate Hma -decodeInstrW_translate_word // HisJnz.
                generalize (Hsregs _ _ HA). intros HB.
                rewrite /= /RegLocate /base.RegLocate HA HA' HA'' HB /=.
                replace (nonZero (translate_word wcond)) with (lang.nonZero wcond); cycle 1.
                { destruct wcond; [reflexivity|]. destruct c0; reflexivity. }
                destruct (lang.nonZero wcond); simpl.
                * destruct wrjnz as [njmp | cap] eqn:Hwrjmp; simpl.
                  { econstructor.
                    { repeat econstructor. }
                    { intros. econstructor; eauto.
                      - econstructor; eauto.
                        replace (inl njmp) with (word_of_argument reg1 (inr rjnz)) by (simpl; rewrite /base.RegLocate HA //).
                        eapply Hregsdef_preserve_word_of_arg; eauto.
                      - replace (inl njmp) with (word_of_argument reg1 (inr rjnz)) by (simpl; rewrite /base.RegLocate HA //).
                        replace (inl njmp) with (translate_word (word_of_argument reg1 (inr rjnz))) by (simpl; rewrite /base.RegLocate HA //).
                        eapply Hsregs_preserve_word_of_arg; eauto. } }
                  { destruct cap; [| | congruence].
                    { destruct c0 as [ [ [ [p1 g1] b1] e1] a1].
                      destruct (perm_eq_dec p1 E).
                      - subst p1; simpl. econstructor; eauto.
                        + repeat econstructor.
                        + intros. econstructor; eauto.
                          * econstructor; eauto.
                            simpl. intros. destruct (reg_eq_dec PC r).
                            { subst r; rewrite lookup_insert.
                              eexists; split; eauto. }
                            { rewrite lookup_insert_ne; auto. }
                          * simpl. intros r w. destruct (reg_eq_dec PC r).
                            { subst r; rewrite !lookup_insert; inversion 1; simpl; auto. }
                            { rewrite !lookup_insert_ne //. auto. }
                      - rewrite updatePcPerm_cap_non_E; auto. simpl.
                        econstructor; eauto.
                        + repeat econstructor.
                        + intros. econstructor; eauto.
                          * econstructor; eauto.
                            simpl. intros. destruct (reg_eq_dec PC r).
                            { subst r; rewrite lookup_insert.
                              destruct p1; try congruence; eexists; split; eauto. }
                            { rewrite lookup_insert_ne; auto. }
                          * simpl. intros r w. destruct (reg_eq_dec PC r).
                            { destruct p1; try congruence; subst r; rewrite !lookup_insert; inversion 1; simpl; auto. }
                            { rewrite !lookup_insert_ne //. auto. } }
                    { destruct (perm_eq_dec p0 E).
                      - subst p0; simpl. econstructor; eauto.
                        + repeat econstructor.
                        + intros. econstructor; eauto.
                          * econstructor; eauto.
                            simpl. intros. destruct (reg_eq_dec PC r).
                            { subst r; rewrite lookup_insert.
                              eexists; split; eauto. }
                            { rewrite lookup_insert_ne; auto. }
                          * simpl. intros r w. destruct (reg_eq_dec PC r).
                            { subst r; rewrite !lookup_insert; inversion 1; simpl; auto. }
                            { rewrite !lookup_insert_ne //. auto. }
                      - rewrite updatePcPerm_cap_non_E; auto. simpl.
                        econstructor; eauto.
                        + repeat econstructor.
                        + intros. econstructor; eauto.
                          * econstructor; eauto.
                            simpl. intros. destruct (reg_eq_dec PC r).
                            { subst r; rewrite lookup_insert.
                              destruct p0; try congruence; eexists; split; eauto. }
                            { rewrite lookup_insert_ne; auto. }
                          * simpl. intros r w. destruct (reg_eq_dec PC r).
                            { destruct p0; try congruence; subst r; rewrite !lookup_insert; inversion 1; simpl; auto. }
                            { rewrite !lookup_insert_ne //. auto. } } }
                * destruct (a + 1)%a eqn:Hap1.
                  { assert (lang.updatePC (reg1, h, stk, cs) = (lang.NextI, (<[PC := inr (Regular (p, g, b, e, a0))]>reg1, h, stk, cs))) as ->.
                    { rewrite /lang.updatePC /= /base.RegLocate HPC /= Hap1 /=.
                      inv H6; destruct p; simpl; naive_solver. }
                    assert (updatePC (reg2, mem2) = (NextI, (<[PC := inr (p, g, b, e, a0)]> reg2, mem2))) as ->.
                    { rewrite /updatePC /= /RegLocate HPC' /= Hap1 /=.
                      inv H6; destruct p; simpl; naive_solver. }
                    simpl. econstructor.
                    - repeat econstructor.
                    - intros. econstructor; eauto.
                      + econstructor; eauto.
                        intros r; destruct (reg_eq_dec r PC).
                        * subst r; rewrite lookup_insert; eexists; split; auto.
                          simpl. auto.
                        * rewrite lookup_insert_ne; auto.
                      + intros r w. destruct (reg_eq_dec r PC).
                        * subst r; rewrite !lookup_insert; auto.
                          inversion 1; simpl; auto.
                        * rewrite !lookup_insert_ne; auto. }
                  { rewrite /lang.updatePC /updatePC /= /base.RegLocate /RegLocate HPC HPC' /= Hap1 /=.
                    simpl. econstructor.
                    - repeat econstructor.
                    - rewrite /can_step /=. intros [X | X]; discriminate. }
            - (* Return jnz *)
              rewrite HisJnz. rewrite /base.MemLocate in HisJnz.
              destruct (Hregsdef PC) as [wpc [HPC HinterpPC] ].
              rewrite /base.RegLocate HPC in H5. inv H5.
              generalize (Hsregs _ _ HPC). intro HPC'.
              generalize (Hsregs _ _ HA'). intro HA''.
              simpl in HinterpPC. destruct HinterpPC as [HnpwlU Hdom].
              generalize (Hdom a ltac:(inv H6; auto)); intros Haa.
              eapply elem_of_dom in Haa. destruct Haa as [wa Hha].
              rewrite Hha in HisJnz. generalize (Hsh _ _ Hha).
              intros [Hma [HnpwlW [Hisglob Hcan_address] ] ].
              generalize (Hsregs _ _ HA). intros HB.
              assert (Hnz: nonZero (translate_word wcond) = lang.nonZero wcond).
              { destruct wcond; simpl; auto. destruct c0; simpl; auto. }
              destruct (lang.nonZero wcond) eqn:Hnzcond; cycle 1.
              + set res := exec (decodeInstrW (mem2 !m! a)) (reg2, mem2).
                exists ([@ectx_language.fill cap_ectx_lang [SeqCtx] (Instr res.1)], res.2). split.
                * eapply tc_once. econstructor. econstructor; eauto.
                  -- f_equal; eauto. instantiate (1 := []).
                     instantiate (2 := []). reflexivity.
                  -- instantiate (1 := res.2).
                     instantiate (1 := []). reflexivity.
                  -- econstructor; eauto. econstructor.
                     econstructor; simpl; eauto.
                     econstructor; simpl; eauto.
                     ++ rewrite /RegLocate HPC'; eauto.
                     ++ rewrite /RegLocate HPC'. generalize (isCorrectPC_translate_word H6).
                        simpl; auto.
                * subst res. rewrite /MemLocate Hma -decodeInstrW_translate_word HisJnz.
                  rewrite /= /base.RegLocate /RegLocate HA' HA'' Hnzcond Hnz /=.
                  destruct (a + 1)%a eqn:Hap1.
                  { assert (lang.updatePC (reg1, h, stk, cs) = (lang.NextI, (<[PC := inr (Regular (p, g, b, e, a0))]>reg1, h, stk, cs))) as ->.
                    { rewrite /lang.updatePC /= /base.RegLocate HPC /= Hap1 /=.
                      inv H6; destruct p; simpl; naive_solver. }
                    assert (updatePC (reg2, mem2) = (NextI, (<[PC := inr (p, g, b, e, a0)]> reg2, mem2))) as ->.
                    { rewrite /updatePC /= /RegLocate HPC' /= Hap1 /=.
                      inv H6; destruct p; simpl; naive_solver. }
                    simpl. econstructor.
                    - repeat econstructor.
                    - intros. econstructor; eauto.
                      + econstructor; eauto.
                        intros r; destruct (reg_eq_dec r PC).
                        * subst r; rewrite lookup_insert; eexists; split; auto.
                          simpl. auto.
                        * rewrite lookup_insert_ne; auto.
                      + intros r w. destruct (reg_eq_dec r PC).
                        * subst r; rewrite !lookup_insert; auto.
                          inversion 1; simpl; auto.
                        * rewrite !lookup_insert_ne; auto. }
                  { rewrite /lang.updatePC /updatePC /= /base.RegLocate /RegLocate HPC HPC' /= Hap1 /=.
                    simpl. econstructor.
                    - repeat econstructor.
                    - rewrite /can_step /=. intros [X | X]; discriminate. }
              + (* Actual return case *)
                simpl in Hinterp; destruct cs as [| [nregs nstk] cs']; [elim Hinterp|].
                destruct Hinterp as [ne_stk [na_stk [Hr_stk [Haris [ (pcp & pcg & pcb & pce & pca & HnewPC & Hcanexec & pcam1 & HnewPC' & Hpcam1eq) [Hrange [Hrange' [XE [XA [XB XC] ] ] ] ] ] ] ] ] ].
                eexists ([Seq (Instr NextI)], (fmap translate_word nregs, mem2)).
                rewrite /lang.exec /base.RegLocate HA /=.
                split.
                { eapply tc_rtc_r.
                  * eapply tc_once. econstructor. econstructor; eauto.
                    { f_equal; eauto. instantiate (1 := []).
                      instantiate (2 := []). reflexivity. }
                    { instantiate (1 := []). econstructor; try reflexivity.
                      instantiate (2 := [SeqCtx]). reflexivity.
                      econstructor. eapply step_exec_instr; simpl; auto.
                      rewrite /RegLocate HPC'; reflexivity.
                      rewrite /RegLocate HPC'. inv H6; econstructor; eauto. }
                  * rewrite /MemLocate Hma -decodeInstrW_translate_word // HisJnz.
                    rewrite /= /RegLocate. generalize (Hsregs _ _ HA).
                    intros HA1'. rewrite HA1'. simpl. eapply rtc_l.
                    { exists []. eapply step_atomic with (t1:=[]).
                      1,2: reflexivity. cbn.
                      eapply ectx_language.Ectx_step with (K:=[]).
                      1,2: reflexivity. cbn. rewrite HA'' Hnz. econstructor. }
                    simpl. rewrite /is_return in XC.
                    rewrite /update_reg /=.
                    assert (XD: forall i, i < 66 -> is_Some (activation_code !! i)).
                    { intros. apply lookup_lt_is_Some.
                      rewrite activation_code_length //. }
                    assert (XC': forall i, i < 66 -> exists ai, (ar + i)%a = Some ai /\ (ai < er)%a /\ (translate_word <$> activation_code) !! i = mem2 !! ai).
                    { intros. generalize (XC i H1). intros [ai [A [B C] ] ].
                      exists ai. split; auto. split; auto.
                      rewrite list_lookup_fmap C.
                      assert (exists wai, nstk !! ai = Some wai) as [wai Hwai].
                      { destruct (XD _ H1) as [wai Hwai].
                        rewrite Hwai in C; eauto. }
                      inv Hcs. generalize (Hstksim0 _ _ Hwai). rewrite Hwai.
                      simpl. intros [? [? ?] ]. congruence. }
                    eapply rtc_l.
                    { exists []. eapply step_atomic with (t1:=[]).
                      1,2: reflexivity. cbn.
                      eapply ectx_language.Ectx_step with (K:=[SeqCtx]).
                      1,2: reflexivity. econstructor. eapply step_exec_instr; eauto.
                      - rewrite /= /RegLocate lookup_insert; eauto.
                      - rewrite /= /RegLocate lookup_insert. econstructor; auto.
                        destruct (XC 0 ltac:(lia)) as [ar' [Har' [XX _] ] ].
                        clear -Hrange Haris Har' XX. solve_addr. }
                    simpl. generalize (XC' 0 ltac:(lia)). intros [ar' [XX [_ XY] ] ].
                    assert (ar = ar') by (clear -XX; solve_addr). subst ar'; clear XX.
                    rewrite list_lookup_fmap in XY. rewrite /activation_code /= in XY.
                    rewrite /MemLocate -XY /=. clear XY.
                    destruct (XC' 1 ltac:(lia)) as [arp1 [Harp1 [Hlow1 Hcode1] ] ].
                    rewrite decode_encode_instr_inv /= /RegLocate lookup_insert /update_reg /updatePC /RegLocate !(lookup_insert_ne _ (R 1 _) PC) // /= !lookup_insert Harp1 /update_reg /=.
                    eapply rtc_l.
                    { exists []. eapply step_atomic with (t1:=[]).
                      1,2: reflexivity. cbn.
                      eapply ectx_language.Ectx_step with (K:=[]).
                      1,2: reflexivity. cbn. econstructor. }
                    simpl. eapply rtc_l.
                    { exists []. eapply step_atomic with (t1:=[]).
                      1,2: reflexivity. cbn.
                      eapply ectx_language.Ectx_step with (K:=[SeqCtx]).
                      1,2: reflexivity. econstructor. eapply step_exec_instr; eauto.
                      - rewrite /= /RegLocate lookup_insert; eauto.
                      - rewrite /= /RegLocate lookup_insert. econstructor; auto.
                        clear -Hlow1 Hrange Harp1 Hlow1 Haris. solve_addr. }
                    simpl. rewrite list_lookup_fmap /= in Hcode1.
                    rewrite /MemLocate -Hcode1 /= decode_encode_instr_inv /= /RegLocate !(lookup_insert_ne _ PC (R 1 _)) // !lookup_insert.
                    assert (Harm1eq: (ar + -1)%a = Some (^(na_stk + 32)%a)).
                    { clear -Haris Hrange. solve_addr. }
                    rewrite Harm1eq /update_reg /=.
                    destruct (XC' 2 ltac:(lia)) as [arp2 [Harp2 [Hlow2 Hcode2] ] ].
                    assert ((arp1 + 1)%a = Some arp2) by (clear -Harp1 Harp2; solve_addr).
                    rewrite /updatePC /RegLocate /= (lookup_insert_ne _ (R 1 _) PC) // lookup_insert H1 /update_reg /=. clear H1.
                    eapply rtc_l.
                    { exists []. eapply step_atomic with (t1:=[]).
                      1,2: reflexivity. cbn.
                      eapply ectx_language.Ectx_step with (K:=[]).
                      1,2: reflexivity. cbn. econstructor. }
                    simpl. eapply rtc_l.
                    { exists []. eapply step_atomic with (t1:=[]).
                      1,2: reflexivity. cbn.
                      eapply ectx_language.Ectx_step with (K:=[SeqCtx]).
                      1,2: reflexivity. econstructor. eapply step_exec_instr; eauto.
                      - rewrite /= /RegLocate lookup_insert; eauto.
                      - rewrite /= /RegLocate lookup_insert. econstructor; auto.
                        clear -Hlow2 Hrange Harp2 Haris. solve_addr. }
                    simpl. rewrite list_lookup_fmap /= in Hcode2.
                    rewrite /MemLocate -Hcode2 /= decode_encode_instr_inv /= /RegLocate !(lookup_insert_ne _ PC (R 1 _)) // !lookup_insert.
                    rewrite andb_true_l.
                    assert ((br <=? ^(na_stk + 32))%a && (^(na_stk + 32) <? er)%a = true) as ->.
                    { clear -Hrange Harm1eq Haris Harp1 Hlow1. apply andb_true_iff.
                      split. apply leb_addr_spec. solve_addr.
                      apply ltb_addr_spec. solve_addr. }
                    rewrite /update_reg /=. inv Hcs.
                    generalize (Hstksim0 _ _ XB). simpl. intros [YA [ [_ YB] _] ].
                    rewrite /MemLocate YA /=.
                    destruct (XC' 3 ltac:(lia)) as [arp3 [Harp3 [Hlow3 Hcode3] ] ].
                    assert ((arp2 + 1)%a = Some arp3) by (clear -Harp2 Harp3; solve_addr).
                    rewrite /updatePC /RegLocate /= (lookup_insert_ne _ call.r_stk) // lookup_insert /= H1 /update_reg /=. clear H1.
                    eapply rtc_l.
                    { exists []. eapply step_atomic with (t1:=[]).
                      1,2: reflexivity. cbn.
                      eapply ectx_language.Ectx_step with (K:=[]).
                      1,2: reflexivity. cbn. econstructor. }
                    simpl. rewrite -!(insert_commute _ PC (R 1 _)) //.
                    rewrite -!(insert_commute _ PC call.r_stk) //.
                    rewrite !insert_insert. eapply rtc_transitive.
                    { eapply pop_env_instrs_spec with (rlist := list_difference all_registers [PC; call.r_stk]).
                      - replace (length (list_difference all_registers [PC; call.r_stk])) with 31 by reflexivity.
                        instantiate (1 := ^(na_stk + 1)%a).
                        clear -Haris. solve_addr.
                      - clear -Hrange. solve_addr.
                      - clear -Hrange Hrange' Harm1eq Harp1 Hlow1. solve_addr.
                      - instantiate (1 := ^(ar + 65)%a).
                        simpl length. destruct (XC 65 ltac:(lia)) as [arp65 [? _] ].
                        clear -H1 Harp3. solve_addr.
                      - clear -Hrange Harp3 Haris. solve_addr.
                      - destruct (XC 65 ltac:(lia)) as [arp65 [X [Y _] ] ].
                        clear -X Y; solve_addr.
                      - split; eapply not_elem_of_list; [left|right;left].
                      - simpl length. simpl Nat.mul.
                        intros i Hilt. generalize (XC' (3 + i) ltac:(lia)).
                        intros [ai [Hai [Hailt Hcodei] ] ].
                        exists ai. split; [clear -Harp3 Hai; solve_addr|].
                        rewrite /activation_code in Hcodei.
                        rewrite fmap_app lookup_app_r in Hcodei; [|simpl; lia].
                        rewrite fmap_app lookup_app_l in Hcodei; [|rewrite !fmap_length map_length call.pop_env_instrs_length /=; lia].
                        simpl length in Hcodei. replace (3 + i - 3) with i in Hcodei by lia.
                        rewrite -Hcodei. reflexivity.
                      - simpl length. intros i Hilt.
                        generalize (XA (31 - S i) ltac:(clear -Hilt; lia)).
                        intros [ri [Hri Hstkri] ].
                        exists (^(na_stk + S (31 - S i))%a).
                        split; [clear -Haris Hrange Hilt; solve_addr|].
                        exists ri; split; auto.
                        destruct (Hregsdef0 ri) as [rwi [Hrwi Hinterprwi] ].
                        exists rwi. split; eauto.
                        rewrite Hrwi in Hstkri.
                        generalize (Hstksim0 _ _ Hstkri). intros [? ?]; auto. }
                    eapply rtc_l.
                    { econstructor. econstructor; eauto.
                      - instantiate (2 := []). instantiate (3 := []).
                        reflexivity.
                      - econstructor.
                        + instantiate (2 := [SeqCtx]). reflexivity.
                        + reflexivity.
                        + econstructor. eapply step_exec_instr; eauto.
                          * rewrite /RegLocate lookup_insert //.
                          * rewrite /RegLocate lookup_insert.
                            econstructor; auto. destruct (XC' 65 ltac:(lia)) as [arp65 [Harp65 [Hlt65 ?] ] ].
                            clear -Hrange Harp65 Hlt65 Haris. solve_addr. }
                    rewrite !app_nil_l.
                    set (rlist := list_difference all_registers [PC; call.r_stk]).
                    rewrite /cap_lang.mem /MemLocate.
                    destruct (XC' 65 ltac:(lia)) as [arp65 [Harp65 [Hlt65 Hcode65] ] ].
                    replace (^(ar + 65)%a) with arp65 by (clear -Harp65; solve_addr).
                    rewrite /activation_code !fmap_app in Hcode65.
                    rewrite lookup_app_r in Hcode65; [|simpl; lia].
                    rewrite lookup_app_r in Hcode65; [|simpl; lia].
                    simpl in Hcode65. rewrite -Hcode65.
                    rewrite /decodeInstrW decode_encode_instr_inv.
                    rewrite /exec /reg /RegLocate.
                    rewrite (lookup_insert_ne _ PC) //.
                    rewrite lookup_insert. rewrite /isU /z_of_argument.
                    rewrite /verify_access.
                    assert ((^(na_stk + 1) + -1)%a = Some na_stk) as -> by (clear -Hrange; solve_addr).
                    destruct (Addr_le_dec br na_stk) as [_|X]; [|exfalso; clear -X Hrange; solve_addr].
                    destruct (Addr_lt_dec na_stk ^(na_stk + 1)%a) as [_|X]; [|exfalso; clear -X Hrange; solve_addr].
                    destruct (Addr_le_dec ^(na_stk + 1)%a ne_stk) as [_|X]; [|exfalso; clear -X Hrange Hrange'; solve_addr].
                    rewrite /update_reg /cap_lang.mem /reg /MemLocate.
                    generalize (Hstksim0 _ _ HnewPC'). intros [AA [AB AC] ].
                    rewrite AA.
                    assert (ZZ: (foldr (λ (r : RegName) (reg : Reg), <[r:=translate_word (base.RegLocate nregs r)]> reg) (<[R 1 eq_refl:=inr (RX, Directed, br, er, ^(na_stk + 32)%a)]> reg2) rlist) = <[PC := reg2 !r! PC]> (<[call.r_stk := reg2 !r! call.r_stk]> (translate_word <$> nregs))).
                    { eapply map_eq. intros.
                      assert (Hdup: NoDup rlist).
                      { subst rlist. apply NoDup_list_difference.
                        apply all_registers_NoDup. }
                      destruct (in_dec reg_eq_dec i rlist).
                      - rewrite (proj1 (foldr_insert_spec _ _ i Hdup) i0).
                        eapply elem_of_list_In in i0.
                        eapply elem_of_list_difference in i0.
                        destruct i0 as [Hin Hnin].
                        rewrite lookup_insert_ne; [|intro; subst i; eapply Hnin; left].
                        rewrite lookup_insert_ne; [|intro; subst i; eapply Hnin; right; left].
                        destruct (Hregsdef0 i) as [wi [Hwi _] ].
                        rewrite lookup_fmap /base.RegLocate Hwi; reflexivity.
                      - rewrite (proj2 (foldr_insert_spec _ _ i Hdup) n).
                        destruct (reg_eq_dec PC i); [subst i; rewrite lookup_insert lookup_insert_ne /RegLocate // HPC' //|].
                        rewrite (lookup_insert_ne _ PC) //.
                        destruct (reg_eq_dec call.r_stk i); [subst i; rewrite lookup_insert lookup_insert_ne /RegLocate //|].
                        destruct (Hregsdef call.r_stk) as [ww [XX _] ].
                        rewrite (Hsregs _ _ XX); auto.
                        exfalso. eapply n. eapply elem_of_list_In.
                        eapply elem_of_list_difference.
                        split. apply all_registers_correct.
                        intro. eapply elem_of_cons in H1.
                        destruct H1; [apply n0; auto|].
                        eapply elem_of_cons in H1. destruct H1; [apply n1; auto|].
                        eapply not_elem_of_nil; eauto. }
                    rewrite ZZ. rewrite insert_insert.
                    rewrite (insert_commute _ call.r_stk PC) //.
                    rewrite !insert_insert /=.
                    assert (YY: updatePC (<[PC:=inr (pcp, pcg, pcb, pce, pcam1)]> (<[call.r_stk:=inr (URWLX, Directed, br, ne_stk, ^(na_stk + 1)%a)]> (translate_word <$> nregs)), mem2) = (NextI, update_reg (<[PC:=inr (pcp, pcg, pcb, pce, pcam1)]> (<[call.r_stk:=inr (URWLX, Directed, br, ne_stk, ^(na_stk + 1)%a)]> (translate_word <$> nregs)), mem2) PC (inr (pcp, pcg, pcb, pce, pca)))).
                    { rewrite /updatePC /RegLocate lookup_insert /= Hpcam1eq.
                      destruct Hcanexec as [-> | [-> | ->] ]; auto. }
                    rewrite YY /update_reg /=.
                    rewrite insert_insert.
                    assert (XX: <[PC:=inr (pcp, pcg, pcb, pce, pca)]> (<[call.r_stk:=inr (URWLX, Directed, br, ne_stk, ^(na_stk + 1)%a)]> (translate_word <$> nregs)) = translate_word <$> nregs).
                    { eapply map_eq. intros.
                      destruct (reg_eq_dec i PC); [subst i|].
                      - rewrite lookup_insert lookup_fmap HnewPC /= //.
                      - rewrite lookup_insert_ne; auto.
                        destruct (reg_eq_dec i call.r_stk); [subst i|].
                        + rewrite lookup_insert lookup_fmap Hr_stk /= //.
                        + rewrite lookup_insert_ne; auto. }
                    rewrite XX. econstructor. }
              { rewrite HA' Hnzcond.
                econstructor.
                * repeat econstructor.
                * intros _. econstructor; eauto.
                  { intros. eapply Hstkdisj; eauto.
                    - generalize (proj1 (stack_is_Some _ _) ltac:(eexists; exact H2)); simpl; intros Hd1.
                      destruct (nat_eq_dec d1 (S (length cs'))); [lia|].
                      exact H2.
                    - generalize (proj1 (stack_is_Some _ _) ltac:(eexists; exact H3)); simpl; intros Hd2.
                      destruct (nat_eq_dec d2 (S (length cs'))); [lia|].
                      exact H3. }
                  { inv Hcs; econstructor; eauto. }
                  { intros r w X; rewrite lookup_fmap X /= //. } } }
          (* Not Jmp nor Jnz so we know we only need one step *)
          set res := exec (decodeInstrW (mem2 !m! a)) (reg2, mem2).
          exists ([@ectx_language.fill cap_ectx_lang [SeqCtx] (Instr res.1)], res.2).
          split.
          { eapply tc_once. econstructor. econstructor; eauto.
            - f_equal; eauto. instantiate (1 := []).
              instantiate (2 := []). reflexivity.
            - instantiate (1 := res.2).
              instantiate (1 := []). reflexivity.
            - econstructor; eauto. econstructor.
              rewrite /base.RegLocate in H5.
              destruct (reg1 !! PC) eqn:HPC; [|congruence].
              subst s. generalize (Hsregs _ _ HPC); simpl.
              intros HPC'. econstructor; simpl; eauto.
              econstructor; simpl; eauto.
              + rewrite /RegLocate HPC'. reflexivity.
              + rewrite /RegLocate HPC'. generalize (isCorrectPC_translate_word H6).
                simpl; auto. }
          { destruct (lang.exec (decodeInstrW' (base.MemLocate h a)) (reg1, h, stk, cs)) as [c1 [ [ [reg1' h'] stk'] cs'] ] eqn:Hexec. simpl.
            destruct res as [c2 [reg2' mem2'] ] eqn:Hexec'. subst res. simpl.
            rewrite /base.RegLocate in H5.
            destruct (reg1 !! PC) eqn:HPC; [|congruence]. subst s.
            eapply exec_sim with (K := [lang.SeqCtx]); eauto.
            repeat econstructor. }
        * (* Regular stack exec *)
          simpl in H5, H6. rewrite H5 in H6. simpl.
          revert H7. intro HQWE.
          assert ((exists r, decodeInstrW' (base.MemLocate m a) = Jmp r) \/ (forall r, decodeInstrW' (base.MemLocate m a) <> Jmp r)).
          { clear. destruct (decodeInstrW' (base.MemLocate m a)); eauto. }
          destruct H1 as [HisJmp | HnisJmp].
          { (* Jmp case *)
            destruct HisJmp as [rjmp HisJmp].
            inv Hcswf. destruct (Hregsdef rjmp) as [wrjmp [HA Hinterp] ].
            assert (Hne: (exists br er ar, wrjmp = inr (Ret br er ar)) \/ (forall br er ar, wrjmp <> inr (Ret br er ar))).
            { destruct wrjmp; auto. destruct c0; eauto. }
            destruct Hne as [ [br [er [ar ->] ] ] |Hne]; cycle 1.
            - (* Stack jmp *)
              set res := exec (decodeInstrW (mem2 !m! a)) (reg2, mem2).
              exists ([Seq (Instr res.1)], res.2).
              split.
              + eapply tc_once. econstructor. econstructor; eauto.
                * f_equal; eauto. instantiate (1 := []).
                  instantiate (2 := []). reflexivity.
                * instantiate (1 := res.2).
                  instantiate (1 := []). reflexivity.
                * econstructor; eauto. instantiate (2 := [SeqCtx]).
                  reflexivity. reflexivity.
                  rewrite /base.RegLocate in H5.
                  destruct (reg1 !! PC) eqn:HPC; [|congruence].
                  subst s. generalize (Hsregs _ _ HPC); simpl.
                  intros HPC'. econstructor; simpl; eauto.
                  econstructor; simpl; eauto.
                  { rewrite /RegLocate HPC'. reflexivity. }
                  { rewrite /RegLocate HPC'. generalize (isCorrectPC_translate_word H6).
                    simpl; auto. }
              + rewrite HisJmp. rewrite /base.MemLocate in HisJmp.
                destruct (Hregsdef PC) as [wpc [HPC HinterpPC] ].
                rewrite /base.RegLocate HPC in H5. inv H5.
                generalize (Hsregs _ _ HPC). intro HPC'.
                assert (Hdom: forall x, (b <= x < e)%a -> exists w, m !! x = Some w).
                { destruct HinterpPC as [W1 [W2 [W3 W4] ] ].
                  subst d; rewrite stack_cons_length in HQWE.
                  inv HQWE. intros. apply W4. simpl.
                  inv H6. clear -H1 H9; destruct H9 as [-> | [-> | ->] ]; solve_addr. }
                generalize (Hdom a ltac:(inv H6; auto)); intros Haa.
                destruct Haa as [wa Hha].
                rewrite Hha in HisJmp.
                assert (Hstksim': forall a w, m !! a = Some w -> mem2 !! a = Some (translate_word w) /\ interp w h m cs /\ canBeStored w a).
                { destruct HinterpPC as [? ?]. subst d.
                  rewrite stack_cons_length in HQWE; inv HQWE; auto. }
                generalize (Hstksim' _ _ Hha).
                intros [Hma [HIa HCSa] ].
                subst res. rewrite /MemLocate Hma -decodeInstrW_translate_word // HisJmp.
                generalize (Hsregs _ _ HA). intros HB.
                rewrite /= /RegLocate /base.RegLocate HA HB /=.
                destruct wrjmp as [njmp | cap] eqn:Hwrjmp; simpl.
                * econstructor.
                  { repeat econstructor. }
                  { intros. econstructor; eauto.
                    - econstructor; eauto.
                      replace (inl njmp) with (word_of_argument reg1 (inr rjmp)) by (simpl; rewrite /base.RegLocate HA //).
                      eapply Hregsdef_preserve_word_of_arg; eauto.
                    - replace (inl njmp) with (word_of_argument reg1 (inr rjmp)) by (simpl; rewrite /base.RegLocate HA //).
                      replace (inl njmp) with (translate_word (word_of_argument reg1 (inr rjmp))) by (simpl; rewrite /base.RegLocate HA //).
                      eapply Hsregs_preserve_word_of_arg; eauto. }
                * destruct cap; [| | congruence].
                  { destruct c0 as [ [ [ [p1 g1] b1] e1] a1].
                    destruct (perm_eq_dec p1 E).
                    - subst p1; simpl. econstructor; eauto.
                      + repeat econstructor.
                      + intros. econstructor; eauto.
                        * econstructor; eauto.
                          simpl. intros. destruct (reg_eq_dec PC r).
                          { subst r; rewrite lookup_insert.
                            eexists; split; eauto. }
                          { rewrite lookup_insert_ne; auto. }
                        * simpl. intros r w. destruct (reg_eq_dec PC r).
                          { subst r; rewrite !lookup_insert; inversion 1; simpl; auto. }
                          { rewrite !lookup_insert_ne //. auto. }
                    - rewrite updatePcPerm_cap_non_E; auto. simpl.
                      econstructor; eauto.
                      + repeat econstructor.
                      + intros. econstructor; eauto.
                        * econstructor; eauto.
                          simpl. intros. destruct (reg_eq_dec PC r).
                          { subst r; rewrite lookup_insert.
                            destruct p1; try congruence; eexists; split; eauto. }
                          { rewrite lookup_insert_ne; auto. }
                        * simpl. intros r w. destruct (reg_eq_dec PC r).
                          { destruct p1; try congruence; subst r; rewrite !lookup_insert; inversion 1; simpl; auto. }
                          { rewrite !lookup_insert_ne //. auto. } }
                  { destruct (perm_eq_dec p0 E).
                    - subst p0; simpl. econstructor; eauto.
                      + repeat econstructor.
                      + intros. econstructor; eauto.
                        * econstructor; eauto.
                          simpl. intros. destruct (reg_eq_dec PC r).
                          { subst r; rewrite lookup_insert.
                            eexists; split; eauto. }
                          { rewrite lookup_insert_ne; auto. }
                        * simpl. intros r w. destruct (reg_eq_dec PC r).
                          { subst r; rewrite !lookup_insert; inversion 1; simpl; auto. }
                          { rewrite !lookup_insert_ne //. auto. }
                    - rewrite updatePcPerm_cap_non_E; auto. simpl.
                      econstructor; eauto.
                      + repeat econstructor.
                      + intros. econstructor; eauto.
                        * econstructor; eauto.
                          simpl. intros. destruct (reg_eq_dec PC r).
                          { subst r; rewrite lookup_insert.
                            destruct p0; try congruence; eexists; split; eauto. }
                          { rewrite lookup_insert_ne; auto. }
                        * simpl. intros r w. destruct (reg_eq_dec PC r).
                          { destruct p0; try congruence; subst r; rewrite !lookup_insert; inversion 1; simpl; auto. }
                          { rewrite !lookup_insert_ne //. auto. } }
            - (* Return jump *)
              rewrite /base.RegLocate in H5.
              destruct (Hregsdef PC) as [wpc [HPC HinterpPC] ].
              rewrite HPC in H5; inv H5. generalize (Hsregs _ _ HPC); simpl.
              intros HPC'. simpl in Hinterp; destruct cs as [| [nregs nstk] cs']; [elim Hinterp|].
              destruct Hinterp as [ne_stk [na_stk [Hr_stk [Haris [ (pcp & pcg & pcb & pce & pca & HnewPC & Hcanexec & pcam1 & HnewPC' & Hpcam1eq) [Hrange [Hrange' [XE [XA [XB XC] ] ] ] ] ] ] ] ] ].
              assert (Hdom: forall x, (b <= x < e)%a -> exists w, m !! x = Some w).
              { destruct HinterpPC as [W1 [W2 [W3 W4] ] ].
                subst d; rewrite stack_cons_length in HQWE.
                inv HQWE. intros. apply W4. simpl.
                inv H6. clear -H1 H9; destruct H9 as [-> | [-> | ->] ]; solve_addr. }
              eexists ([Seq (Instr NextI)], (fmap translate_word nregs, mem2)).
              rewrite HisJmp. rewrite /lang.exec /base.RegLocate HA /=.
              split.
              + eapply tc_rtc_r.
                * eapply tc_once. econstructor. econstructor; eauto.
                  { f_equal; eauto. instantiate (1 := []).
                    instantiate (2 := []). reflexivity. }
                  { instantiate (1 := []). econstructor; try reflexivity.
                    instantiate (2 := [SeqCtx]). reflexivity.
                    econstructor. eapply step_exec_instr; simpl; auto.
                    rewrite /RegLocate HPC'; reflexivity.
                    rewrite /RegLocate HPC'. inv H6; econstructor; eauto. }
                * simpl. generalize (Hdom a ltac:(inv H6; auto)); intros Haa.
                  destruct Haa as [wa Hha].
                  rewrite /base.MemLocate Hha in HisJmp.
                  assert (Hstksim': forall a w, m !! a = Some w -> mem2 !! a = Some (translate_word w) /\ interp w h m ((nregs, nstk) :: cs') /\ canBeStored w a).
                  { destruct HinterpPC as [? ?]. subst d.
                    rewrite stack_cons_length in HQWE; inv HQWE; auto. }
                  generalize (Hstksim' _ _ Hha).
                  intros [Hma [HIa HCSa] ].
                  rewrite /MemLocate Hma -decodeInstrW_translate_word // HisJmp.
                  rewrite /= /RegLocate. generalize (Hsregs _ _ HA).
                  intros HA'. rewrite HA'. simpl. eapply rtc_l.
                  { exists []. eapply step_atomic with (t1:=[]).
                    1,2: reflexivity. cbn.
                    eapply ectx_language.Ectx_step with (K:=[]).
                    1,2: reflexivity. cbn. econstructor. }
                  simpl. rewrite /is_return in XC.
                  rewrite /update_reg /=.
                  assert (XD: forall i, i < 66 -> is_Some (activation_code !! i)).
                  { intros. apply lookup_lt_is_Some.
                    rewrite activation_code_length //. }
                  assert (XC': forall i, i < 66 -> exists ai, (ar + i)%a = Some ai /\ (ai < er)%a /\ (translate_word <$> activation_code) !! i = mem2 !! ai).
                  { intros. generalize (XC i H1). intros [ai [A [B C] ] ].
                    exists ai. split; auto. split; auto.
                    rewrite list_lookup_fmap C.
                    assert (exists wai, nstk !! ai = Some wai) as [wai Hwai].
                    { destruct (XD _ H1) as [wai Hwai].
                      rewrite Hwai in C; eauto. }
                    inv Hcs. generalize (Hstksim0 _ _ Hwai). rewrite Hwai.
                    simpl. intros [? [? ?] ]. congruence. }
                  eapply rtc_l.
                  { exists []. eapply step_atomic with (t1:=[]).
                    1,2: reflexivity. cbn.
                    eapply ectx_language.Ectx_step with (K:=[SeqCtx]).
                    1,2: reflexivity. econstructor. eapply step_exec_instr; eauto.
                    - rewrite /= /RegLocate lookup_insert; eauto.
                    - rewrite /= /RegLocate lookup_insert. econstructor; auto.
                      destruct (XC 0 ltac:(lia)) as [ar' [Har' [XX _] ] ].
                      clear -Hrange Haris Har' XX. solve_addr. }
                  simpl. generalize (XC' 0 ltac:(lia)). intros [ar' [XX [_ XY] ] ].
                  assert (ar = ar') by (clear -XX; solve_addr). subst ar'; clear XX.
                  rewrite list_lookup_fmap in XY. rewrite /activation_code /= in XY.
                  rewrite /MemLocate -XY /=. clear XY.
                  destruct (XC' 1 ltac:(lia)) as [arp1 [Harp1 [Hlow1 Hcode1] ] ].
                  rewrite decode_encode_instr_inv /= /RegLocate lookup_insert /update_reg /updatePC /RegLocate !(lookup_insert_ne _ (R 1 _) PC) // /= !lookup_insert Harp1 /update_reg /=.
                  eapply rtc_l.
                  { exists []. eapply step_atomic with (t1:=[]).
                    1,2: reflexivity. cbn.
                    eapply ectx_language.Ectx_step with (K:=[]).
                    1,2: reflexivity. cbn. econstructor. }
                  simpl. eapply rtc_l.
                  { exists []. eapply step_atomic with (t1:=[]).
                    1,2: reflexivity. cbn.
                    eapply ectx_language.Ectx_step with (K:=[SeqCtx]).
                    1,2: reflexivity. econstructor. eapply step_exec_instr; eauto.
                    - rewrite /= /RegLocate lookup_insert; eauto.
                    - rewrite /= /RegLocate lookup_insert. econstructor; auto.
                      clear -Hlow1 Hrange Harp1 Hlow1 Haris. solve_addr. }
                  simpl. rewrite list_lookup_fmap /= in Hcode1.
                  rewrite /MemLocate -Hcode1 /= decode_encode_instr_inv /= /RegLocate !(lookup_insert_ne _ PC (R 1 _)) // !lookup_insert.
                  assert (Harm1eq: (ar + -1)%a = Some (^(na_stk + 32)%a)).
                  { clear -Haris Hrange. solve_addr. }
                  rewrite Harm1eq /update_reg /=.
                  destruct (XC' 2 ltac:(lia)) as [arp2 [Harp2 [Hlow2 Hcode2] ] ].
                  assert ((arp1 + 1)%a = Some arp2) by (clear -Harp1 Harp2; solve_addr).
                  rewrite /updatePC /RegLocate /= (lookup_insert_ne _ (R 1 _) PC) // lookup_insert H1 /update_reg /=. clear H1.
                  eapply rtc_l.
                  { exists []. eapply step_atomic with (t1:=[]).
                    1,2: reflexivity. cbn.
                    eapply ectx_language.Ectx_step with (K:=[]).
                    1,2: reflexivity. cbn. econstructor. }
                  simpl. eapply rtc_l.
                  { exists []. eapply step_atomic with (t1:=[]).
                    1,2: reflexivity. cbn.
                    eapply ectx_language.Ectx_step with (K:=[SeqCtx]).
                    1,2: reflexivity. econstructor. eapply step_exec_instr; eauto.
                    - rewrite /= /RegLocate lookup_insert; eauto.
                    - rewrite /= /RegLocate lookup_insert. econstructor; auto.
                      clear -Hlow2 Hrange Harp2 Haris. solve_addr. }
                  simpl. rewrite list_lookup_fmap /= in Hcode2.
                  rewrite /MemLocate -Hcode2 /= decode_encode_instr_inv /= /RegLocate !(lookup_insert_ne _ PC (R 1 _)) // !lookup_insert.
                  rewrite andb_true_l.
                  assert ((br <=? ^(na_stk + 32))%a && (^(na_stk + 32) <? er)%a = true) as ->.
                  { clear -Hrange Harm1eq Haris Harp1 Hlow1. apply andb_true_iff.
                    split. apply leb_addr_spec. solve_addr.
                    apply ltb_addr_spec. solve_addr. }
                  rewrite /update_reg /=. inv Hcs.
                  generalize (Hstksim0 _ _ XB). simpl. intros [YA [ [_ YB] _] ].
                  rewrite /MemLocate YA /=.
                  destruct (XC' 3 ltac:(lia)) as [arp3 [Harp3 [Hlow3 Hcode3] ] ].
                  assert ((arp2 + 1)%a = Some arp3) by (clear -Harp2 Harp3; solve_addr).
                  rewrite /updatePC /RegLocate /= (lookup_insert_ne _ call.r_stk) // lookup_insert /= H1 /update_reg /=. clear H1.
                  eapply rtc_l.
                  { exists []. eapply step_atomic with (t1:=[]).
                    1,2: reflexivity. cbn.
                    eapply ectx_language.Ectx_step with (K:=[]).
                    1,2: reflexivity. cbn. econstructor. }
                  simpl. rewrite -!(insert_commute _ PC (R 1 _)) //.
                  rewrite -!(insert_commute _ PC call.r_stk) //.
                  rewrite !insert_insert. eapply rtc_transitive.
                  { eapply pop_env_instrs_spec with (rlist := list_difference all_registers [PC; call.r_stk]).
                    - replace (length (list_difference all_registers [PC; call.r_stk])) with 31 by reflexivity.
                      instantiate (1 := ^(na_stk + 1)%a).
                      clear -Haris. solve_addr.
                    - clear -Hrange. solve_addr.
                    - clear -Hrange Hrange' Harm1eq Harp1 Hlow1. solve_addr.
                    - instantiate (1 := ^(ar + 65)%a).
                      simpl length. destruct (XC 65 ltac:(lia)) as [arp65 [? _] ].
                      clear -H1 Harp3. solve_addr.
                    - clear -Hrange Harp3 Haris. solve_addr.
                    - destruct (XC 65 ltac:(lia)) as [arp65 [X [Y _] ] ].
                      clear -X Y; solve_addr.
                    - split; eapply not_elem_of_list; [left|right;left].
                    - simpl length. simpl Nat.mul.
                      intros i Hilt. generalize (XC' (3 + i) ltac:(lia)).
                      intros [ai [Hai [Hailt Hcodei] ] ].
                      exists ai. split; [clear -Harp3 Hai; solve_addr|].
                      rewrite /activation_code in Hcodei.
                      rewrite fmap_app lookup_app_r in Hcodei; [|simpl; lia].
                      rewrite fmap_app lookup_app_l in Hcodei; [|rewrite !fmap_length map_length call.pop_env_instrs_length /=; lia].
                      simpl length in Hcodei. replace (3 + i - 3) with i in Hcodei by lia.
                      rewrite -Hcodei. reflexivity.
                    - simpl length. intros i Hilt.
                      generalize (XA (31 - S i) ltac:(clear -Hilt; lia)).
                      intros [ri [Hri Hstkri] ].
                      exists (^(na_stk + S (31 - S i))%a).
                      split; [clear -Haris Hrange Hilt; solve_addr|].
                      exists ri; split; auto.
                      destruct (Hregsdef0 ri) as [rwi [Hrwi Hinterprwi] ].
                      exists rwi. split; eauto.
                      rewrite Hrwi in Hstkri.
                      generalize (Hstksim0 _ _ Hstkri). intros [? ?]; auto. }
                  eapply rtc_l.
                  { econstructor. econstructor; eauto.
                    - instantiate (2 := []). instantiate (3 := []).
                      reflexivity.
                    - econstructor.
                      + instantiate (2 := [SeqCtx]). reflexivity.
                      + reflexivity.
                      + econstructor. eapply step_exec_instr; eauto.
                        * rewrite /RegLocate lookup_insert //.
                        * rewrite /RegLocate lookup_insert.
                          econstructor; auto. destruct (XC' 65 ltac:(lia)) as [arp65 [Harp65 [Hlt65 ?] ] ].
                          clear -Hrange Harp65 Hlt65 Haris. solve_addr. }
                  rewrite !app_nil_l.
                  set (rlist := list_difference all_registers [PC; call.r_stk]).
                  rewrite /cap_lang.mem /MemLocate.
                  destruct (XC' 65 ltac:(lia)) as [arp65 [Harp65 [Hlt65 Hcode65] ] ].
                  replace (^(ar + 65)%a) with arp65 by (clear -Harp65; solve_addr).
                  rewrite /activation_code !fmap_app in Hcode65.
                  rewrite lookup_app_r in Hcode65; [|simpl; lia].
                  rewrite lookup_app_r in Hcode65; [|simpl; lia].
                  simpl in Hcode65. rewrite -Hcode65.
                  rewrite /decodeInstrW decode_encode_instr_inv.
                  rewrite /exec /reg /RegLocate.
                  rewrite (lookup_insert_ne _ PC) //.
                  rewrite lookup_insert. rewrite /isU /z_of_argument.
                  rewrite /verify_access.
                  assert ((^(na_stk + 1) + -1)%a = Some na_stk) as -> by (clear -Hrange; solve_addr).
                  destruct (Addr_le_dec br na_stk) as [_|X]; [|exfalso; clear -X Hrange; solve_addr].
                  destruct (Addr_lt_dec na_stk ^(na_stk + 1)%a) as [_|X]; [|exfalso; clear -X Hrange; solve_addr].
                  destruct (Addr_le_dec ^(na_stk + 1)%a ne_stk) as [_|X]; [|exfalso; clear -X Hrange Hrange'; solve_addr].
                  rewrite /update_reg /cap_lang.mem /reg /MemLocate.
                  generalize (Hstksim0 _ _ HnewPC'). intros [AA [AB AC] ].
                  rewrite AA.
                  assert (ZZ: (foldr (λ (r : RegName) (reg : Reg), <[r:=translate_word (base.RegLocate nregs r)]> reg) (<[R 1 eq_refl:=inr (RX, Directed, br, er, ^(na_stk + 32)%a)]> reg2) rlist) = <[PC := reg2 !r! PC]> (<[call.r_stk := reg2 !r! call.r_stk]> (translate_word <$> nregs))).
                  { eapply map_eq. intros.
                    assert (Hdup: NoDup rlist).
                    { subst rlist. apply NoDup_list_difference.
                      apply all_registers_NoDup. }
                    destruct (in_dec reg_eq_dec i rlist).
                    - rewrite (proj1 (foldr_insert_spec _ _ i Hdup) i0).
                      eapply elem_of_list_In in i0.
                      eapply elem_of_list_difference in i0.
                      destruct i0 as [Hin Hnin].
                      rewrite lookup_insert_ne; [|intro; subst i; eapply Hnin; left].
                      rewrite lookup_insert_ne; [|intro; subst i; eapply Hnin; right; left].
                      destruct (Hregsdef0 i) as [wi [Hwi _] ].
                      rewrite lookup_fmap /base.RegLocate Hwi; reflexivity.
                    - rewrite (proj2 (foldr_insert_spec _ _ i Hdup) n).
                      destruct (reg_eq_dec PC i); [subst i; rewrite lookup_insert lookup_insert_ne /RegLocate // HPC' //|].
                      rewrite (lookup_insert_ne _ PC) //.
                      destruct (reg_eq_dec call.r_stk i); [subst i; rewrite lookup_insert lookup_insert_ne /RegLocate //|].
                      destruct (Hregsdef call.r_stk) as [ww [XX _] ].
                      rewrite (Hsregs _ _ XX); auto.
                      exfalso. eapply n. eapply elem_of_list_In.
                      eapply elem_of_list_difference.
                      split. apply all_registers_correct.
                      intro. eapply elem_of_cons in H1.
                      destruct H1; [apply n0; auto|].
                      eapply elem_of_cons in H1. destruct H1; [apply n1; auto|].
                      eapply not_elem_of_nil; eauto. }
                  rewrite ZZ. rewrite insert_insert.
                  rewrite (insert_commute _ call.r_stk PC) //.
                  rewrite !insert_insert /=.
                  assert (YY: updatePC (<[PC:=inr (pcp, pcg, pcb, pce, pcam1)]> (<[call.r_stk:=inr (URWLX, Directed, br, ne_stk, ^(na_stk + 1)%a)]> (translate_word <$> nregs)), mem2) = (NextI, update_reg (<[PC:=inr (pcp, pcg, pcb, pce, pcam1)]> (<[call.r_stk:=inr (URWLX, Directed, br, ne_stk, ^(na_stk + 1)%a)]> (translate_word <$> nregs)), mem2) PC (inr (pcp, pcg, pcb, pce, pca)))).
                  { rewrite /updatePC /RegLocate lookup_insert /= Hpcam1eq.
                    destruct Hcanexec as [-> | [-> | ->] ]; auto. }
                  rewrite YY /update_reg /=.
                  rewrite insert_insert.
                  assert (XX: <[PC:=inr (pcp, pcg, pcb, pce, pca)]> (<[call.r_stk:=inr (URWLX, Directed, br, ne_stk, ^(na_stk + 1)%a)]> (translate_word <$> nregs)) = translate_word <$> nregs).
                  { eapply map_eq. intros.
                    destruct (reg_eq_dec i PC); [subst i|].
                    - rewrite lookup_insert lookup_fmap HnewPC /= //.
                    - rewrite lookup_insert_ne; auto.
                      destruct (reg_eq_dec i call.r_stk); [subst i|].
                      + rewrite lookup_insert lookup_fmap Hr_stk /= //.
                      + rewrite lookup_insert_ne; auto. }
                  rewrite XX. econstructor.
            + econstructor.
              * repeat econstructor.
              * intros _. econstructor; eauto.
                { intros. eapply Hstkdisj; eauto.
                  - generalize (proj1 (stack_is_Some _ _) ltac:(eexists; exact H2)); simpl; intros Hd1.
                    destruct (nat_eq_dec d1 (S (length cs'))); [lia|].
                    exact H2.
                  - generalize (proj1 (stack_is_Some _ _) ltac:(eexists; exact H3)); simpl; intros Hd2.
                    destruct (nat_eq_dec d2 (S (length cs'))); [lia|].
                    exact H3. }
                { inv Hcs; econstructor; eauto. }
                { intros r w X; rewrite lookup_fmap X /= //. } }
          assert ((exists r1 r2, decodeInstrW' (base.MemLocate m a) = Jnz r1 r2) \/ (forall r1 r2, decodeInstrW' (base.MemLocate m a) <> Jnz r1 r2)).
          { clear. destruct (decodeInstrW' (base.MemLocate m a)); eauto. }
          destruct H1 as [HisJnz | HnisJnz].
          { destruct HisJnz as [rjnz [rcond HisJnz] ].
            inv Hcswf. destruct (Hregsdef rjnz) as [wrjnz [HA Hinterp] ].
            destruct (Hregsdef rcond) as [wcond [HA' Hinterp_cond] ].
            assert (Hne: (exists br er ar, wrjnz = inr (Ret br er ar)) \/ (forall br er ar, wrjnz <> inr (Ret br er ar))).
            { destruct wrjnz; auto. destruct c0; eauto. }
            destruct Hne as [ [br [er [ar ->] ] ] |Hne]; cycle 1.
            - (* Regular jnz *)
              set res := exec (decodeInstrW (mem2 !m! a)) (reg2, mem2).
              exists ([@ectx_language.fill cap_ectx_lang [SeqCtx] (Instr res.1)], res.2).
              split.
              + eapply tc_once. econstructor. econstructor; eauto.
                * f_equal; eauto. instantiate (1 := []).
                instantiate (2 := []). reflexivity.
                * instantiate (1 := res.2).
                  instantiate (1 := []). reflexivity.
                * econstructor; eauto. econstructor.
                  rewrite /base.RegLocate in H5.
                  destruct (reg1 !! PC) eqn:HPC; [|congruence].
                  subst s. generalize (Hsregs _ _ HPC); simpl.
                  intros HPC'. econstructor; simpl; eauto.
                  econstructor; simpl; eauto.
                  { rewrite /RegLocate HPC'. reflexivity. }
                  { rewrite /RegLocate HPC'. generalize (isCorrectPC_translate_word H6).
                    simpl; auto. }
              + rewrite HisJnz. rewrite /base.MemLocate in HisJnz.
                destruct (Hregsdef PC) as [wpc [HPC HinterpPC] ].
                rewrite /base.RegLocate HPC in H5. inv H5.
                generalize (Hsregs _ _ HPC). intro HPC'.
                generalize (Hsregs _ _ HA'). intro HA''.
                assert (Hdom: forall x, (b <= x < e)%a -> exists w, m !! x = Some w).
                { destruct HinterpPC as [W1 [W2 [W3 W4] ] ].
                  subst d; rewrite stack_cons_length in HQWE.
                  inv HQWE. intros. apply W4. simpl.
                  inv H6. clear -H1 H9; destruct H9 as [-> | [-> | ->] ]; solve_addr. }
                generalize (Hdom a ltac:(inv H6; auto)); intros Haa.
                destruct Haa as [wa Hha].
                assert (Hstksim': forall a w, m !! a = Some w -> mem2 !! a = Some (translate_word w) /\ interp w h m cs /\ canBeStored w a).
                { destruct HinterpPC as [? ?]. subst d.
                  rewrite stack_cons_length in HQWE; inv HQWE; auto. }
                rewrite Hha in HisJnz. generalize (Hstksim' _ _ Hha).
                intros [Hma [HIa HCSa] ].
                subst res. rewrite /MemLocate Hma -decodeInstrW_translate_word // HisJnz.
                generalize (Hsregs _ _ HA). intros HB.
                rewrite /= /RegLocate /base.RegLocate HA HA' HA'' HB /=.
                replace (nonZero (translate_word wcond)) with (lang.nonZero wcond); cycle 1.
                { destruct wcond; [reflexivity|]. destruct c0; reflexivity. }
                destruct (lang.nonZero wcond); simpl.
                * destruct wrjnz as [njmp | cap] eqn:Hwrjmp; simpl.
                  { econstructor.
                    { repeat econstructor. }
                    { intros. econstructor; eauto.
                      - econstructor; eauto.
                        replace (inl njmp) with (word_of_argument reg1 (inr rjnz)) by (simpl; rewrite /base.RegLocate HA //).
                        eapply Hregsdef_preserve_word_of_arg; eauto.
                      - replace (inl njmp) with (word_of_argument reg1 (inr rjnz)) by (simpl; rewrite /base.RegLocate HA //).
                        replace (inl njmp) with (translate_word (word_of_argument reg1 (inr rjnz))) by (simpl; rewrite /base.RegLocate HA //).
                        eapply Hsregs_preserve_word_of_arg; eauto. } }
                  { destruct cap; [| | congruence].
                    { destruct c0 as [ [ [ [p1 g1] b1] e1] a1].
                      destruct (perm_eq_dec p1 E).
                      - subst p1; simpl. econstructor; eauto.
                        + repeat econstructor.
                        + intros. econstructor; eauto.
                          * econstructor; eauto.
                            simpl. intros. destruct (reg_eq_dec PC r).
                            { subst r; rewrite lookup_insert.
                              eexists; split; eauto. }
                            { rewrite lookup_insert_ne; auto. }
                          * simpl. intros r w. destruct (reg_eq_dec PC r).
                            { subst r; rewrite !lookup_insert; inversion 1; simpl; auto. }
                            { rewrite !lookup_insert_ne //. auto. }
                      - rewrite updatePcPerm_cap_non_E; auto. simpl.
                        econstructor; eauto.
                        + repeat econstructor.
                        + intros. econstructor; eauto.
                          * econstructor; eauto.
                            simpl. intros. destruct (reg_eq_dec PC r).
                            { subst r; rewrite lookup_insert.
                              destruct p1; try congruence; eexists; split; eauto. }
                            { rewrite lookup_insert_ne; auto. }
                          * simpl. intros r w. destruct (reg_eq_dec PC r).
                            { destruct p1; try congruence; subst r; rewrite !lookup_insert; inversion 1; simpl; auto. }
                            { rewrite !lookup_insert_ne //. auto. } }
                    { destruct (perm_eq_dec p0 E).
                      - subst p0; simpl. econstructor; eauto.
                        + repeat econstructor.
                        + intros. econstructor; eauto.
                          * econstructor; eauto.
                            simpl. intros. destruct (reg_eq_dec PC r).
                            { subst r; rewrite lookup_insert.
                              eexists; split; eauto. }
                            { rewrite lookup_insert_ne; auto. }
                          * simpl. intros r w. destruct (reg_eq_dec PC r).
                            { subst r; rewrite !lookup_insert; inversion 1; simpl; auto. }
                            { rewrite !lookup_insert_ne //. auto. }
                      - rewrite updatePcPerm_cap_non_E; auto. simpl.
                        econstructor; eauto.
                        + repeat econstructor.
                        + intros. econstructor; eauto.
                          * econstructor; eauto.
                            simpl. intros. destruct (reg_eq_dec PC r).
                            { subst r; rewrite lookup_insert.
                              destruct p0; try congruence; eexists; split; eauto. }
                            { rewrite lookup_insert_ne; auto. }
                          * simpl. intros r w. destruct (reg_eq_dec PC r).
                            { destruct p0; try congruence; subst r; rewrite !lookup_insert; inversion 1; simpl; auto. }
                            { rewrite !lookup_insert_ne //. auto. } } }
                * destruct (a + 1)%a eqn:Hap1.
                  { assert (lang.updatePC (reg1, h, stk, cs) = (lang.NextI, (<[PC := inr (Stk d p b e a0)]>reg1, h, stk, cs))) as ->.
                    { rewrite /lang.updatePC /= /base.RegLocate HPC /= Hap1 /=.
                      inv H6; destruct p; simpl; naive_solver. }
                    assert (updatePC (reg2, mem2) = (NextI, (<[PC := inr (p, Directed, b, e, a0)]> reg2, mem2))) as ->.
                    { rewrite /updatePC /= /RegLocate HPC' /= Hap1 /=.
                      inv H6; destruct p; simpl; naive_solver. }
                    simpl. econstructor.
                    - repeat econstructor.
                    - intros. econstructor; eauto.
                      + econstructor; eauto.
                        intros r; destruct (reg_eq_dec r PC).
                        * subst r; rewrite lookup_insert; eexists; split; auto.
                          simpl in HinterpPC. simpl.
                          inv H6. destruct H9 as [-> | [-> | ->] ]; auto.
                        * rewrite lookup_insert_ne; auto.
                      + intros r w. destruct (reg_eq_dec r PC).
                        * subst r; rewrite !lookup_insert; auto.
                          inversion 1; simpl; auto.
                        * rewrite !lookup_insert_ne; auto. }
                  { rewrite /lang.updatePC /updatePC /= /base.RegLocate /RegLocate HPC HPC' /= Hap1 /=.
                    simpl. econstructor.
                    - repeat econstructor.
                    - rewrite /can_step /=. intros [X | X]; discriminate. }
            - (* Return jnz *)
              rewrite HisJnz. rewrite /base.MemLocate in HisJnz.
              destruct (Hregsdef PC) as [wpc [HPC HinterpPC] ].
              rewrite /base.RegLocate HPC in H5. inv H5.
              generalize (Hsregs _ _ HPC). intro HPC'.
              generalize (Hsregs _ _ HA'). intro HA''.
              assert (Hdom: forall x, (b <= x < e)%a -> exists w, m !! x = Some w).
              { destruct HinterpPC as [W1 [W2 [W3 W4] ] ].
                subst d; rewrite stack_cons_length in HQWE.
                inv HQWE. intros. apply W4. simpl.
                inv H6. clear -H1 H9; destruct H9 as [-> | [-> | ->] ]; solve_addr. }
              generalize (Hdom a ltac:(inv H6; auto)); intros Haa.
              destruct Haa as [wa Hha].
              assert (Hstksim': forall a w, m !! a = Some w -> mem2 !! a = Some (translate_word w) /\ interp w h m cs /\ canBeStored w a).
              { destruct HinterpPC as [? ?]. subst d.
                rewrite stack_cons_length in HQWE; inv HQWE; auto. }
              generalize (Hstksim' _ _ Hha). rewrite Hha in HisJnz.
              intros [Hma [HIa HCSa] ].
              generalize (Hsregs _ _ HA). intros HB.
              assert (Hnz: nonZero (translate_word wcond) = lang.nonZero wcond).
              { destruct wcond; simpl; auto. destruct c0; simpl; auto. }
              destruct (lang.nonZero wcond) eqn:Hnzcond; cycle 1.
              + set res := exec (decodeInstrW (mem2 !m! a)) (reg2, mem2).
                exists ([@ectx_language.fill cap_ectx_lang [SeqCtx] (Instr res.1)], res.2). split.
                * eapply tc_once. econstructor. econstructor; eauto.
                  -- f_equal; eauto. instantiate (1 := []).
                     instantiate (2 := []). reflexivity.
                  -- instantiate (1 := res.2).
                     instantiate (1 := []). reflexivity.
                  -- econstructor; eauto. econstructor.
                     econstructor; simpl; eauto.
                     econstructor; simpl; eauto.
                     ++ rewrite /RegLocate HPC'; eauto.
                     ++ rewrite /RegLocate HPC'. generalize (isCorrectPC_translate_word H6).
                        simpl; auto.
                * subst res. rewrite /MemLocate Hma -decodeInstrW_translate_word HisJnz.
                  rewrite /= /base.RegLocate /RegLocate HA' HA'' Hnzcond Hnz /=.
                  destruct (a + 1)%a eqn:Hap1.
                  { assert (lang.updatePC (reg1, h, stk, cs) = (lang.NextI, (<[PC := inr (Stk d p b e a0)]>reg1, h, stk, cs))) as ->.
                    { rewrite /lang.updatePC /= /base.RegLocate HPC /= Hap1 /=.
                      inv H6; destruct p; simpl; naive_solver. }
                    assert (updatePC (reg2, mem2) = (NextI, (<[PC := inr (p, Directed, b, e, a0)]> reg2, mem2))) as ->.
                    { rewrite /updatePC /= /RegLocate HPC' /= Hap1 /=.
                      inv H6; destruct p; simpl; naive_solver. }
                    simpl. econstructor.
                    - repeat econstructor.
                    - intros. econstructor; eauto.
                      + econstructor; eauto.
                        intros r; destruct (reg_eq_dec r PC).
                        * subst r; rewrite lookup_insert; eexists; split; auto.
                          simpl in HinterpPC. simpl.
                          inv H6. destruct H9 as [-> | [-> | ->] ]; auto.
                        * rewrite lookup_insert_ne; auto.
                      + intros r w. destruct (reg_eq_dec r PC).
                        * subst r; rewrite !lookup_insert; auto.
                          inversion 1; simpl; auto.
                        * rewrite !lookup_insert_ne; auto. }
                  { rewrite /lang.updatePC /updatePC /= /base.RegLocate /RegLocate HPC HPC' /= Hap1 /=.
                    simpl. econstructor.
                    - repeat econstructor.
                    - rewrite /can_step /=. intros [X | X]; discriminate. }
              + (* Actual return case *)
                simpl in Hinterp; destruct cs as [| [nregs nstk] cs']; [elim Hinterp|].
                destruct Hinterp as [ne_stk [na_stk [Hr_stk [Haris [ (pcp & pcg & pcb & pce & pca & HnewPC & Hcanexec & pcam1 & HnewPC' & Hpcam1eq) [Hrange [Hrange' [XE [XA [XB XC] ] ] ] ] ] ] ] ] ].
                eexists ([Seq (Instr NextI)], (fmap translate_word nregs, mem2)).
                rewrite /lang.exec /base.RegLocate HA /=.
                split.
                { eapply tc_rtc_r.
                  * eapply tc_once. econstructor. econstructor; eauto.
                    { f_equal; eauto. instantiate (1 := []).
                      instantiate (2 := []). reflexivity. }
                    { instantiate (1 := []). econstructor; try reflexivity.
                      instantiate (2 := [SeqCtx]). reflexivity.
                      econstructor. eapply step_exec_instr; simpl; auto.
                      rewrite /RegLocate HPC'; reflexivity.
                      rewrite /RegLocate HPC'. inv H6; econstructor; eauto. }
                  * rewrite /MemLocate Hma -decodeInstrW_translate_word // HisJnz.
                    rewrite /= /RegLocate. generalize (Hsregs _ _ HA).
                    intros HA1'. rewrite HA1'. simpl. eapply rtc_l.
                    { exists []. eapply step_atomic with (t1:=[]).
                      1,2: reflexivity. cbn.
                      eapply ectx_language.Ectx_step with (K:=[]).
                      1,2: reflexivity. cbn. rewrite HA'' Hnz. econstructor. }
                    simpl. rewrite /is_return in XC.
                    rewrite /update_reg /=.
                    assert (XD: forall i, i < 66 -> is_Some (activation_code !! i)).
                    { intros. apply lookup_lt_is_Some.
                      rewrite activation_code_length //. }
                    assert (XC': forall i, i < 66 -> exists ai, (ar + i)%a = Some ai /\ (ai < er)%a /\ (translate_word <$> activation_code) !! i = mem2 !! ai).
                    { intros. generalize (XC i H1). intros [ai [A [B C] ] ].
                      exists ai. split; auto. split; auto.
                      rewrite list_lookup_fmap C.
                      assert (exists wai, nstk !! ai = Some wai) as [wai Hwai].
                      { destruct (XD _ H1) as [wai Hwai].
                        rewrite Hwai in C; eauto. }
                      inv Hcs. generalize (Hstksim0 _ _ Hwai). rewrite Hwai.
                      simpl. intros [? [? ?] ]. congruence. }
                    eapply rtc_l.
                    { exists []. eapply step_atomic with (t1:=[]).
                      1,2: reflexivity. cbn.
                      eapply ectx_language.Ectx_step with (K:=[SeqCtx]).
                      1,2: reflexivity. econstructor. eapply step_exec_instr; eauto.
                      - rewrite /= /RegLocate lookup_insert; eauto.
                      - rewrite /= /RegLocate lookup_insert. econstructor; auto.
                        destruct (XC 0 ltac:(lia)) as [ar' [Har' [XX _] ] ].
                        clear -Hrange Haris Har' XX. solve_addr. }
                    simpl. generalize (XC' 0 ltac:(lia)). intros [ar' [XX [_ XY] ] ].
                    assert (ar = ar') by (clear -XX; solve_addr). subst ar'; clear XX.
                    rewrite list_lookup_fmap in XY. rewrite /activation_code /= in XY.
                    rewrite /MemLocate -XY /=. clear XY.
                    destruct (XC' 1 ltac:(lia)) as [arp1 [Harp1 [Hlow1 Hcode1] ] ].
                    rewrite decode_encode_instr_inv /= /RegLocate lookup_insert /update_reg /updatePC /RegLocate !(lookup_insert_ne _ (R 1 _) PC) // /= !lookup_insert Harp1 /update_reg /=.
                    eapply rtc_l.
                    { exists []. eapply step_atomic with (t1:=[]).
                      1,2: reflexivity. cbn.
                      eapply ectx_language.Ectx_step with (K:=[]).
                      1,2: reflexivity. cbn. econstructor. }
                    simpl. eapply rtc_l.
                    { exists []. eapply step_atomic with (t1:=[]).
                      1,2: reflexivity. cbn.
                      eapply ectx_language.Ectx_step with (K:=[SeqCtx]).
                      1,2: reflexivity. econstructor. eapply step_exec_instr; eauto.
                      - rewrite /= /RegLocate lookup_insert; eauto.
                      - rewrite /= /RegLocate lookup_insert. econstructor; auto.
                        clear -Hlow1 Hrange Harp1 Hlow1 Haris. solve_addr. }
                    simpl. rewrite list_lookup_fmap /= in Hcode1.
                    rewrite /MemLocate -Hcode1 /= decode_encode_instr_inv /= /RegLocate !(lookup_insert_ne _ PC (R 1 _)) // !lookup_insert.
                    assert (Harm1eq: (ar + -1)%a = Some (^(na_stk + 32)%a)).
                    { clear -Haris Hrange. solve_addr. }
                    rewrite Harm1eq /update_reg /=.
                    destruct (XC' 2 ltac:(lia)) as [arp2 [Harp2 [Hlow2 Hcode2] ] ].
                    assert ((arp1 + 1)%a = Some arp2) by (clear -Harp1 Harp2; solve_addr).
                    rewrite /updatePC /RegLocate /= (lookup_insert_ne _ (R 1 _) PC) // lookup_insert H1 /update_reg /=. clear H1.
                    eapply rtc_l.
                    { exists []. eapply step_atomic with (t1:=[]).
                      1,2: reflexivity. cbn.
                      eapply ectx_language.Ectx_step with (K:=[]).
                      1,2: reflexivity. cbn. econstructor. }
                    simpl. eapply rtc_l.
                    { exists []. eapply step_atomic with (t1:=[]).
                      1,2: reflexivity. cbn.
                      eapply ectx_language.Ectx_step with (K:=[SeqCtx]).
                      1,2: reflexivity. econstructor. eapply step_exec_instr; eauto.
                      - rewrite /= /RegLocate lookup_insert; eauto.
                      - rewrite /= /RegLocate lookup_insert. econstructor; auto.
                        clear -Hlow2 Hrange Harp2 Haris. solve_addr. }
                    simpl. rewrite list_lookup_fmap /= in Hcode2.
                    rewrite /MemLocate -Hcode2 /= decode_encode_instr_inv /= /RegLocate !(lookup_insert_ne _ PC (R 1 _)) // !lookup_insert.
                    rewrite andb_true_l.
                    assert ((br <=? ^(na_stk + 32))%a && (^(na_stk + 32) <? er)%a = true) as ->.
                    { clear -Hrange Harm1eq Haris Harp1 Hlow1. apply andb_true_iff.
                      split. apply leb_addr_spec. solve_addr.
                      apply ltb_addr_spec. solve_addr. }
                    rewrite /update_reg /=. inv Hcs.
                    generalize (Hstksim0 _ _ XB). simpl. intros [YA [ [_ YB] _] ].
                    rewrite /MemLocate YA /=.
                    destruct (XC' 3 ltac:(lia)) as [arp3 [Harp3 [Hlow3 Hcode3] ] ].
                    assert ((arp2 + 1)%a = Some arp3) by (clear -Harp2 Harp3; solve_addr).
                    rewrite /updatePC /RegLocate /= (lookup_insert_ne _ call.r_stk) // lookup_insert /= H1 /update_reg /=. clear H1.
                    eapply rtc_l.
                    { exists []. eapply step_atomic with (t1:=[]).
                      1,2: reflexivity. cbn.
                      eapply ectx_language.Ectx_step with (K:=[]).
                      1,2: reflexivity. cbn. econstructor. }
                    simpl. rewrite -!(insert_commute _ PC (R 1 _)) //.
                    rewrite -!(insert_commute _ PC call.r_stk) //.
                    rewrite !insert_insert. eapply rtc_transitive.
                    { eapply pop_env_instrs_spec with (rlist := list_difference all_registers [PC; call.r_stk]).
                      - replace (length (list_difference all_registers [PC; call.r_stk])) with 31 by reflexivity.
                        instantiate (1 := ^(na_stk + 1)%a).
                        clear -Haris. solve_addr.
                      - clear -Hrange. solve_addr.
                      - clear -Hrange Hrange' Harm1eq Harp1 Hlow1. solve_addr.
                      - instantiate (1 := ^(ar + 65)%a).
                        simpl length. destruct (XC 65 ltac:(lia)) as [arp65 [? _] ].
                        clear -H1 Harp3. solve_addr.
                      - clear -Hrange Harp3 Haris. solve_addr.
                      - destruct (XC 65 ltac:(lia)) as [arp65 [X [Y _] ] ].
                        clear -X Y; solve_addr.
                      - split; eapply not_elem_of_list; [left|right;left].
                      - simpl length. simpl Nat.mul.
                        intros i Hilt. generalize (XC' (3 + i) ltac:(lia)).
                        intros [ai [Hai [Hailt Hcodei] ] ].
                        exists ai. split; [clear -Harp3 Hai; solve_addr|].
                        rewrite /activation_code in Hcodei.
                        rewrite fmap_app lookup_app_r in Hcodei; [|simpl; lia].
                        rewrite fmap_app lookup_app_l in Hcodei; [|rewrite !fmap_length map_length call.pop_env_instrs_length /=; lia].
                        simpl length in Hcodei. replace (3 + i - 3) with i in Hcodei by lia.
                        rewrite -Hcodei. reflexivity.
                      - simpl length. intros i Hilt.
                        generalize (XA (31 - S i) ltac:(clear -Hilt; lia)).
                        intros [ri [Hri Hstkri] ].
                        exists (^(na_stk + S (31 - S i))%a).
                        split; [clear -Haris Hrange Hilt; solve_addr|].
                        exists ri; split; auto.
                        destruct (Hregsdef0 ri) as [rwi [Hrwi Hinterprwi] ].
                        exists rwi. split; eauto.
                        rewrite Hrwi in Hstkri.
                        generalize (Hstksim0 _ _ Hstkri). intros [? ?]; auto. }
                    eapply rtc_l.
                    { econstructor. econstructor; eauto.
                      - instantiate (2 := []). instantiate (3 := []).
                        reflexivity.
                      - econstructor.
                        + instantiate (2 := [SeqCtx]). reflexivity.
                        + reflexivity.
                        + econstructor. eapply step_exec_instr; eauto.
                          * rewrite /RegLocate lookup_insert //.
                          * rewrite /RegLocate lookup_insert.
                            econstructor; auto. destruct (XC' 65 ltac:(lia)) as [arp65 [Harp65 [Hlt65 ?] ] ].
                            clear -Hrange Harp65 Hlt65 Haris. solve_addr. }
                    rewrite !app_nil_l.
                    set (rlist := list_difference all_registers [PC; call.r_stk]).
                    rewrite /cap_lang.mem /MemLocate.
                    destruct (XC' 65 ltac:(lia)) as [arp65 [Harp65 [Hlt65 Hcode65] ] ].
                    replace (^(ar + 65)%a) with arp65 by (clear -Harp65; solve_addr).
                    rewrite /activation_code !fmap_app in Hcode65.
                    rewrite lookup_app_r in Hcode65; [|simpl; lia].
                    rewrite lookup_app_r in Hcode65; [|simpl; lia].
                    simpl in Hcode65. rewrite -Hcode65.
                    rewrite /decodeInstrW decode_encode_instr_inv.
                    rewrite /exec /reg /RegLocate.
                    rewrite (lookup_insert_ne _ PC) //.
                    rewrite lookup_insert. rewrite /isU /z_of_argument.
                    rewrite /verify_access.
                    assert ((^(na_stk + 1) + -1)%a = Some na_stk) as -> by (clear -Hrange; solve_addr).
                    destruct (Addr_le_dec br na_stk) as [_|X]; [|exfalso; clear -X Hrange; solve_addr].
                    destruct (Addr_lt_dec na_stk ^(na_stk + 1)%a) as [_|X]; [|exfalso; clear -X Hrange; solve_addr].
                    destruct (Addr_le_dec ^(na_stk + 1)%a ne_stk) as [_|X]; [|exfalso; clear -X Hrange Hrange'; solve_addr].
                    rewrite /update_reg /cap_lang.mem /reg /MemLocate.
                    generalize (Hstksim0 _ _ HnewPC'). intros [AA [AB AC] ].
                    rewrite AA.
                    assert (ZZ: (foldr (λ (r : RegName) (reg : Reg), <[r:=translate_word (base.RegLocate nregs r)]> reg) (<[R 1 eq_refl:=inr (RX, Directed, br, er, ^(na_stk + 32)%a)]> reg2) rlist) = <[PC := reg2 !r! PC]> (<[call.r_stk := reg2 !r! call.r_stk]> (translate_word <$> nregs))).
                    { eapply map_eq. intros.
                      assert (Hdup: NoDup rlist).
                      { subst rlist. apply NoDup_list_difference.
                        apply all_registers_NoDup. }
                      destruct (in_dec reg_eq_dec i rlist).
                      - rewrite (proj1 (foldr_insert_spec _ _ i Hdup) i0).
                        eapply elem_of_list_In in i0.
                        eapply elem_of_list_difference in i0.
                        destruct i0 as [Hin Hnin].
                        rewrite lookup_insert_ne; [|intro; subst i; eapply Hnin; left].
                        rewrite lookup_insert_ne; [|intro; subst i; eapply Hnin; right; left].
                        destruct (Hregsdef0 i) as [wi [Hwi _] ].
                        rewrite lookup_fmap /base.RegLocate Hwi; reflexivity.
                      - rewrite (proj2 (foldr_insert_spec _ _ i Hdup) n).
                        destruct (reg_eq_dec PC i); [subst i; rewrite lookup_insert lookup_insert_ne /RegLocate // HPC' //|].
                        rewrite (lookup_insert_ne _ PC) //.
                        destruct (reg_eq_dec call.r_stk i); [subst i; rewrite lookup_insert lookup_insert_ne /RegLocate //|].
                        destruct (Hregsdef call.r_stk) as [ww [XX _] ].
                        rewrite (Hsregs _ _ XX); auto.
                        exfalso. eapply n. eapply elem_of_list_In.
                        eapply elem_of_list_difference.
                        split. apply all_registers_correct.
                        intro. eapply elem_of_cons in H1.
                        destruct H1; [apply n0; auto|].
                        eapply elem_of_cons in H1. destruct H1; [apply n1; auto|].
                        eapply not_elem_of_nil; eauto. }
                    rewrite ZZ. rewrite insert_insert.
                    rewrite (insert_commute _ call.r_stk PC) //.
                    rewrite !insert_insert /=.
                    assert (YY: updatePC (<[PC:=inr (pcp, pcg, pcb, pce, pcam1)]> (<[call.r_stk:=inr (URWLX, Directed, br, ne_stk, ^(na_stk + 1)%a)]> (translate_word <$> nregs)), mem2) = (NextI, update_reg (<[PC:=inr (pcp, pcg, pcb, pce, pcam1)]> (<[call.r_stk:=inr (URWLX, Directed, br, ne_stk, ^(na_stk + 1)%a)]> (translate_word <$> nregs)), mem2) PC (inr (pcp, pcg, pcb, pce, pca)))).
                    { rewrite /updatePC /RegLocate lookup_insert /= Hpcam1eq.
                      destruct Hcanexec as [-> | [-> | ->] ]; auto. }
                    rewrite YY /update_reg /=.
                    rewrite insert_insert.
                    assert (XX: <[PC:=inr (pcp, pcg, pcb, pce, pca)]> (<[call.r_stk:=inr (URWLX, Directed, br, ne_stk, ^(na_stk + 1)%a)]> (translate_word <$> nregs)) = translate_word <$> nregs).
                    { eapply map_eq. intros.
                      destruct (reg_eq_dec i PC); [subst i|].
                      - rewrite lookup_insert lookup_fmap HnewPC /= //.
                      - rewrite lookup_insert_ne; auto.
                        destruct (reg_eq_dec i call.r_stk); [subst i|].
                        + rewrite lookup_insert lookup_fmap Hr_stk /= //.
                        + rewrite lookup_insert_ne; auto. }
                    rewrite XX. econstructor. }
              { rewrite HA' Hnzcond.
                econstructor.
                * repeat econstructor.
                * intros _. econstructor; eauto.
                  { intros. eapply Hstkdisj; eauto.
                    - generalize (proj1 (stack_is_Some _ _) ltac:(eexists; exact H2)); simpl; intros Hd1.
                      destruct (nat_eq_dec d1 (S (length cs'))); [lia|].
                      exact H2.
                    - generalize (proj1 (stack_is_Some _ _) ltac:(eexists; exact H3)); simpl; intros Hd2.
                      destruct (nat_eq_dec d2 (S (length cs'))); [lia|].
                      exact H3. }
                  { inv Hcs; econstructor; eauto. }
                  { intros r w X; rewrite lookup_fmap X /= //. } } }
          (* Not Jmp nor Jnz so we know we only need one step *)
          set res := exec (decodeInstrW (mem2 !m! a)) (reg2, mem2).
          exists ([@ectx_language.fill cap_ectx_lang [SeqCtx] (Instr res.1)], res.2).
          split.
          { eapply tc_once. econstructor. econstructor; eauto.
            - f_equal; eauto. instantiate (1 := []).
              instantiate (2 := []). reflexivity.
            - instantiate (1 := res.2).
              instantiate (1 := []). reflexivity.
            - econstructor; eauto. econstructor.
              rewrite /base.RegLocate in H5.
              destruct (reg1 !! PC) eqn:HPC; [|congruence].
              subst s. generalize (Hsregs _ _ HPC); simpl.
              intros HPC'. econstructor; simpl; eauto.
              econstructor; simpl; eauto.
              + rewrite /RegLocate HPC'. reflexivity.
              + rewrite /RegLocate HPC'. generalize (isCorrectPC_translate_word H6).
                simpl; auto. }
          { destruct (lang.exec (decodeInstrW' (base.MemLocate m a)) (reg1, h, stk, cs)) as [c1 [ [ [reg1' h'] stk'] cs'] ] eqn:Hexec. simpl.
            destruct res as [c2 [reg2' mem2'] ] eqn:Hexec'. subst res. simpl.
            rewrite /base.RegLocate in H5.
            destruct (reg1 !! PC) eqn:HPC; [|congruence]. subst s.
            simpl in HQWE.
            eapply exec_sim_stk with (K := [lang.SeqCtx]); eauto.
            repeat econstructor. }
        * (* Regular call *)
          eapply exec_call; eauto.
      + (* NextI case *)
        assert (K = [] /\ f1 = lang.NextI) as [-> ->].
        { destruct K; [simpl in H1; inv H1; auto|]. rewrite cons_is_app in H1.
          destruct e; rewrite ectxi_language.fill_app /= in H1.
          inv H1. symmetry in H4; eapply fill_inv_instr in H4.
          destruct H4 as [-> ?]. inv H1; auto. }
        inv H2. clear H1.
        exists ([@ectx_language.fill cap_ectx_lang [] (Seq (Instr Executable))], (reg2, mem2)). split.
        * eapply tc_once. econstructor. econstructor; eauto.
          { f_equal; eauto. instantiate (1 := []).
            instantiate (2 := []). reflexivity. }
          { instantiate (1 := (reg2, mem2)).
            instantiate (1 := []). reflexivity. }
          { econstructor; eauto.
            econstructor. econstructor. }
        * specialize (Hinvs ltac:(rewrite can_step_fill /can_step /=; auto)).
          inv Hinvs. econstructor; eauto.
          { repeat econstructor. }
          { intros. econstructor; eauto. }
      + (* Halted case *)
        assert (K = [] /\ f1 = lang.Halted) as [-> ->].
        { destruct K; [simpl in H1; inv H1; auto|]. rewrite cons_is_app in H1.
          destruct e; rewrite ectxi_language.fill_app /= in H1.
          inv H1. symmetry in H4; eapply fill_inv_instr in H4.
          destruct H4 as [-> ?]. inv H1; auto. }
        inv H2. clear H1.
        exists ([@ectx_language.fill cap_ectx_lang [] (Instr Halted)], (reg2, mem2)). split.
        * eapply tc_once. econstructor. econstructor; eauto.
          { f_equal; eauto. instantiate (1 := []).
            instantiate (2 := []). reflexivity. }
          { instantiate (1 := (reg2, mem2)).
            instantiate (1 := []). reflexivity. }
          { econstructor; eauto.
            econstructor. econstructor. }
        * econstructor; eauto.
          { repeat econstructor. }
          { rewrite can_step_fill /can_step /=. intros [? | ?]; discriminate. }
      + (* Failed case *)
        assert (K = [] /\ f1 = lang.Failed) as [-> ->].
        { destruct K; [simpl in H1; inv H1; auto|]. rewrite cons_is_app in H1.
          destruct e; rewrite ectxi_language.fill_app /= in H1.
          inv H1. symmetry in H4; eapply fill_inv_instr in H4.
          destruct H4 as [-> ?]. inv H1; auto. }
        inv H2. clear H1.
        exists ([@ectx_language.fill cap_ectx_lang [] (Instr Failed)], (reg2, mem2)). split.
        * eapply tc_once. econstructor. econstructor; eauto.
          { f_equal; eauto. instantiate (1 := []).
            instantiate (2 := []). reflexivity. }
          { instantiate (1 := (reg2, mem2)).
            instantiate (1 := []). reflexivity. }
          { econstructor; eauto.
            econstructor. econstructor. }
        * econstructor; eauto.
          { repeat econstructor. }
          { rewrite can_step_fill /can_step /=; intros [? | ?]; discriminate. }
    - intros. inv H1. destruct H3 as [A B].
      inv H2. simpl in A. inv A. destruct x; simpl in B; [|congruence].
      inv Hsexpr; inv B; eexists; split; econstructor; simpl; split; reflexivity.
  Qed.

End overlay_to_cap_lang.
