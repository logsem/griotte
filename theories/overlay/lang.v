From iris.algebra Require Import base.
From iris.program_logic Require Import language ectx_language ectxi_language.
From stdpp Require Import gmap fin_maps list finite.
From cap_machine Require Export addr_reg machine_base machine_parameters linking.
From cap_machine.overlay Require Import base call.
(* From Equations Require Import Equations. *)

Inductive ConfFlag : Type :=
| Executable
| Halted
| Failed
| NextI.

Definition Conf: Type := ConfFlag * ExecConf.

Definition updatePC (φ: ExecConf): Conf :=
  match RegLocate (reg φ) PC with
  | inr (Regular ((p, g), b, e, a)) =>
    match (a + 1)%a with
    | Some a' =>
      match p with
      | E | URWLX | URWX | URWL | URW => (Failed, φ)
      | _ => let φ' := (update_reg φ PC (inr (Regular ((p, g), b, e, a')))) in (NextI, φ')
      end
    | None => (Failed, φ)
    end
  | inr (Stk d p b e a) =>
    match (a + 1)%a with
    | Some a' =>
      match p with
      | E | URWLX | URWX | URWL | URW => (Failed, φ)
      | _ => let φ' := (update_reg φ PC (inr (Stk d p b e a'))) in
                  (NextI, φ')
      end
    | None => (Failed, φ)
    end
  | _ => (Failed, φ)
  end.

Definition updatePcPerm (w: base.Word): base.Word :=
  match w with
  | inr (Regular ((E, g), b, e, a)) => inr (Regular ((RX, g), b, e, a))
  | inr (Stk d E b e a) => inr (Stk d RX b e a)
  | _ => w
  end.

Fixpoint stack (d: nat) (cs: list Stackframe) :=
  match cs with
  | sf::cs => if nat_eq_dec d (length cs) then Some (snd sf) else stack d cs
  | [] => None
  end.

Definition nonZero (w: base.Word): bool :=
  match w with
  | inr _ => true
  | inl n => Zneq_bool n 0
  end.

Definition canReadUpTo (w: base.Word): Addr :=
  match w with
  | inl _ => za
  | inr (Regular ((p, g), b, e, a)) => match p with
                                      | O => za
                                      | RO | RW | RWL | RX | RWX | RWLX | E => e
                                      | URW | URWL | URWX | URWLX => a
                                      end
  | inr (Stk d p b e a) => match p with
                          | O => za
                          | RO | RW | RWL | RX | RWX | RWLX | E => e
                          | URW | URWL | URWX | URWLX => a
                          end
  | inr (Ret b e a) => e
  end.

Definition canStore (p: Perm) (a: Addr) (w: base.Word): bool :=
  match w with
  | inl _ => true
  | inr (Regular ((_, g), _, _, _)) => match g with
                                      | Global => true
                                      | Local => pwl p
                                      | Directed => pwl p && leb_addr (canReadUpTo w) a
                                      end
  | inr (Stk _ _ _ _ _) | inr (Ret _ _ _) => pwl p && leb_addr (canReadUpTo w) a
  end.

Definition canStoreU (p: Perm) (a: Addr) (w: base.Word): bool :=
  match w with
  | inl _ => true
  | inr (Regular ((_, g), _, _, _)) => match g with
                                      | Global => true
                                      | Local => pwlU p
                                      | Directed => pwlU p && leb_addr (canReadUpTo w) a
                                      end
  | inr (Stk _ _ _ _ _) | inr (Ret _ _ _) => pwlU p && leb_addr (canReadUpTo w) a
  end.

Definition isWithin (n1 n2 b e: Addr) : bool :=
  ((b <=? n1) && (n2 <=? e))%a.

Inductive access_kind: Type :=
| LoadU_access (b e a: Addr) (offs: Z): access_kind
| StoreU_access (b e a: Addr) (offs: Z): access_kind.

Definition verify_access (a: access_kind): option Addr :=
  match a with
  | LoadU_access b e a offs =>
    match (a + offs)%a with
    | None => None
    | Some a' => if Addr_le_dec b a' then
                  if Addr_lt_dec a' a then
                    if Addr_le_dec a e then
                      Some a' else None else None else None
    end
  | StoreU_access b e a offs =>
    match (a + offs)%a with
    | None => None
    | Some a' => if Addr_le_dec b a' then
                  if Addr_le_dec a' a then
                    if Addr_lt_dec a e then
                      Some a' else None else None else None
    end
  end.

Definition z_of_argument (regs: base.Reg) (a: Z + RegName) : option Z :=
  match a with
  | inl z => Some z
  | inr r =>
    match regs !! r with
    | Some (inl z) => Some z
    | _ => None
    end
  end.

Inductive isCorrectPC: base.Word → Prop :=
| isCorrectPC_intro:
    forall p g (b e a : Addr),
      (b <= a < e)%a →
      p = RX \/ p = RWX \/ p = RWLX →
      isCorrectPC (inr (Regular ((p, g), b, e, a)))
| isCorrectPC_intro':
    forall d p (b e a : Addr),
      (b <= a < e)%a →
      p = RX \/ p = RWX \/ p = RWLX →
      isCorrectPC (inr (Stk d p b e a)).

Lemma isCorrectPC_dec:
  forall w, { isCorrectPC w } + { not (isCorrectPC w) }.
Proof.
  destruct w.
  - right. red; intros H. inversion H.
  - destruct c.
    + destruct c as ((((p & g) & b) & e) & a).
      case_eq (match p with RX | RWX | RWLX => true | _ => false end); intros.
      * destruct (Addr_le_dec b a).
        { destruct (Addr_lt_dec a e).
          { left. econstructor; simpl; eauto. by auto.
            destruct p; naive_solver. }
          { right. red; intro HH. inversion HH; subst. solve_addr. } }
        { right. red; intros HH; inversion HH; subst. solve_addr. }
      * right. red; intros HH; inversion HH; subst. naive_solver.
    + case_eq (match p with RX | RWX | RWLX => true | _ => false end); intros.
      * destruct (Addr_le_dec a a1).
        { destruct (Addr_lt_dec a1 a0).
          { left. econstructor; simpl; eauto. by auto.
            destruct p; naive_solver. }
          { right. red; intro HH. inversion HH; subst. solve_addr. } }
        { right. red; intros HH; inversion HH; subst. solve_addr. }
      * right. red; intros HH; inversion HH; subst. naive_solver.
    + right. red; intros H. inversion H.
Qed.

(* TODO: move into stdpp_extra, already upstreamed to stdpp *)
Section surjective_finite.
  Context {A} `{Finite A, EqDecision B} (f : A → B).
  Context `{!Surj (=) f}.

  Program Instance surjective_finite: Finite B :=
    {| enum := remove_dups (f <$> enum A) |}.
  Next Obligation. apply NoDup_remove_dups. Qed.
  Next Obligation.
    intros. rewrite elem_of_remove_dups elem_of_list_fmap.
    destruct (surj f x). eauto using elem_of_enum.
  Qed.
End surjective_finite.

Section opsem.
  Context `{MachineParameters}.

  Definition exec (i: instr) (φ: ExecConf): Conf :=
    match i with
    | Fail => (Failed, φ)
    | Halt => (Halted, φ)
    | Jmp r =>
      match (RegLocate (reg φ) r) with
      | inr (Ret b e a) => match (callstack φ) with
                           | [] => (Failed, φ)
                           | ((reg', m') :: cs) => (NextI, (reg', mem φ, m', cs))
                           end
      | _ => let φ' := (update_reg φ PC (updatePcPerm (RegLocate (reg φ) r))) in (NextI, φ')
      end
    | Jnz r1 r2 =>
      if nonZero (RegLocate (reg φ) r2) then
        match (RegLocate (reg φ) r1) with
        | inr (Ret b e a) => match (callstack φ) with
                             | [] => (Failed, φ)
                             | ((reg', m') :: cs) => (NextI, (reg', mem φ, m', cs))
                             end
        | _ => let φ' := (update_reg φ PC (updatePcPerm (RegLocate (reg φ) r1))) in (NextI, φ')
        end
      else updatePC φ
    | Load dst src =>
      match RegLocate (reg φ) src with
      | inl n => (Failed, φ)
      | inr (Regular ((p, g), b, e, a)) =>
        (* Fails for U cap *)
        if readAllowed p && withinBounds ((p, g), b, e, a) then updatePC (update_reg φ dst (MemLocate (mem φ) a))
        else (Failed, φ)
      | inr (Ret b e a) => (Failed, φ)
      | inr (Stk d p b e a) =>
        if readAllowed p && withinBounds ((p, Directed), b, e, a) then
          match stack d ((reg φ, stk φ)::(callstack φ)) with
          | None => (Failed, φ)
          | Some m => updatePC (update_reg φ dst (MemLocate m a))
          end
        else (Failed, φ)
      end
    | Store dst (inr src) =>
      match RegLocate (reg φ) dst with
      | inl n => (Failed, φ)
      | inr (Regular ((p, g), b, e, a)) =>
        (* Fails for U cap *)
        if writeAllowed p && withinBounds ((p, g), b, e, a) && canStore p a (RegLocate (reg φ) src) then
          updatePC (update_mem φ a (RegLocate (reg φ) src))
        else (Failed, φ)
      | inr (Ret b e a) => (Failed, φ)
      | inr (Stk d p b e a) =>
        if writeAllowed p && withinBounds ((p, Directed), b, e, a) && canStore p a (RegLocate (reg φ) src) then
        if nat_eq_dec d (length (callstack φ)) then
          updatePC (update_stk φ a (RegLocate (reg φ) src))
        else match update_stack φ d a (RegLocate (reg φ) src) with
             | None => (Failed, φ)
             | Some φ' => updatePC φ'
             end
        else (Failed, φ)
      end
    | Store dst (inl n) =>
      match RegLocate (reg φ) dst with
      | inl n => (Failed, φ)
      | inr (Regular ((p, g), b, e, a)) =>
        (* Fails for U cap *)
        if writeAllowed p && withinBounds ((p, g), b, e, a) then updatePC (update_mem φ a (inl n)) else (Failed, φ)
      | inr (Ret b e a) => (Failed, φ)
      | inr (Stk d p b e a) =>
        if writeAllowed p && withinBounds ((p, Directed), b, e, a) then
        if nat_eq_dec d (length (callstack φ)) then
          updatePC (update_stk φ a (inl n))
        else match update_stack φ d a (inl n) with
             | None => (Failed, φ)
             | Some φ' => updatePC φ'
             end
        else (Failed, φ)
      end
    | Mov dst (inl n) => updatePC (update_reg φ dst (inl n))
    | Mov dst (inr src) => updatePC (update_reg φ dst (RegLocate (reg φ) src))
    | Lea dst (inl n) =>
      match RegLocate (reg φ) dst with
      | inl _ => (Failed, φ)
      | inr (Regular ((p, g), b, e, a)) =>
        match p with
        | E => (Failed, φ)
        (* Make sure that we can only decrease pointer for uninitialized capabilities *)
        | URW | URWL | URWX | URWLX => match (a + n)%a with
                                      | Some a' => if Addr_le_dec a' a then
                                                    let c := Regular ((p, g), b, e, a') in
                                                    updatePC (update_reg φ dst (inr c))
                                                  else (Failed, φ)
                                      | None => (Failed, φ)
                                      end
        | _ => match (a + n)%a with
               | Some a' => let c := Regular ((p, g), b, e, a') in
                            updatePC (update_reg φ dst (inr c))
               | None => (Failed, φ)
               end
        end
      | inr (Ret b e a) => (Failed, φ)
      | inr (Stk d p b e a) =>
        match p with
        | E => (Failed, φ)
        (* Make sure that we can only decrease pointer for uninitialized capabilities *)
        | URW | URWL | URWX | URWLX => match (a + n)%a with
                                      | Some a' => if Addr_le_dec a' a then
                                                    let c := Stk d p b e a' in
                                                    updatePC (update_reg φ dst (inr c))
                                                  else (Failed, φ)
                                      | None => (Failed, φ)
                                      end
        | _ => match (a + n)%a with
               | Some a' => let c := Stk d p b e a' in
                            updatePC (update_reg φ dst (inr c))
               | None => (Failed, φ)
               end
        end
      end
    | Lea dst (inr r) =>
      match RegLocate (reg φ) dst with
      | inl _ => (Failed, φ)
      | inr (Regular ((p, g), b, e, a)) =>
        match p with
        | E => (Failed, φ)
        (* Make sure that we can only decrease pointer for uninitialized capabilities *)
        | URW | URWL | URWX | URWLX => match RegLocate (reg φ) r with
                                      | inr _ => (Failed, φ)
                                      | inl n => match (a + n)%a with
                                                | Some a' => if Addr_le_dec a' a then
                                                              let c := Regular ((p, g), b, e, a') in
                                                              updatePC (update_reg φ dst (inr c))
                                                            else (Failed, φ)
                                                | None => (Failed, φ)
                                                end
                                      end
        | _ => match RegLocate (reg φ) r with
              | inr _ => (Failed, φ)
              | inl n => match (a + n)%a with
                        | Some a' => let c := Regular ((p, g), b, e, a') in
                                    updatePC (update_reg φ dst (inr c))
                        | None => (Failed, φ)
                        end
              end
        end
      | inr (Ret b e a) => (Failed, φ)
      | inr (Stk d p b e a) =>
        match p with
        | E => (Failed, φ)
        (* Make sure that we can only decrease pointer for uninitialized capabilities *)
        | URW | URWL | URWX | URWLX => match RegLocate (reg φ) r with
                                      | inr _ => (Failed, φ)
                                      | inl n => match (a + n)%a with
                                                | Some a' => if Addr_le_dec a' a then
                                                              let c := Stk d p b e a' in
                                                              updatePC (update_reg φ dst (inr c))
                                                            else (Failed, φ)
                                                | None => (Failed, φ)
                                                end
                                      end
        | _ => match RegLocate (reg φ) r with
              | inr _ => (Failed, φ)
              | inl n => match (a + n)%a with
                        | Some a' => let c := Stk d p b e a' in
                                    updatePC (update_reg φ dst (inr c))
                        | None => (Failed, φ)
                        end
              end
        end
      end
    | Restrict dst (inl n) =>
      match RegLocate (reg φ) dst with
      | inl _ => (Failed, φ)
      | inr (Regular (permPair, b, e, a)) =>
        match permPair with
        | (E, _) => (Failed, φ)
        | _ => if PermPairFlowsTo (decodePermPair n) permPair then
                updatePC (update_reg φ dst (inr (Regular (decodePermPair n, b, e, a))))
              else (Failed, φ)
        end
      | inr (Ret _ _ _) => (Failed, φ)
      | inr (Stk d p b e a) =>
        match p with
        | E => (Failed, φ)
        | _ => if PermPairFlowsTo (decodePermPair n) (p, Directed) then
                                updatePC (update_reg φ dst (inr (Stk d (fst (decodePermPair n)) b e a)))
              else (Failed, φ)
        end
      end
    | Restrict dst (inr r) =>
      match RegLocate (reg φ) dst with
      | inl _ => (Failed, φ)
      | inr (Regular (permPair, b, e, a)) =>
        match RegLocate (reg φ) r with
        | inr _ => (Failed, φ)
        | inl n =>
          match permPair with
          | (E, _) => (Failed, φ)
          | _ => if PermPairFlowsTo (decodePermPair n) permPair then
                  updatePC (update_reg φ dst (inr (Regular (decodePermPair n, b, e, a))))
                else (Failed, φ)
          end
        end
      | inr (Ret _ _ _) => (Failed, φ)
      | inr (Stk d p b e a) =>
        match RegLocate (reg φ) r with
        | inr _ => (Failed, φ)
        | inl n =>
          match p with
          | E => (Failed, φ)
          | _ => if PermPairFlowsTo (decodePermPair n) (p, Directed) then
                  updatePC (update_reg φ dst (inr (Stk d (fst (decodePermPair n)) b e a)))
                else (Failed, φ)
          end
        end
      end
    | Add dst (inr r1) (inr r2) =>
      match RegLocate (reg φ) r1 with
      | inr _ => (Failed, φ)
      | inl n1 => match RegLocate (reg φ) r2 with
                 | inr _ => (Failed, φ)
                 | inl n2 => updatePC (update_reg φ dst (inl (n1 + n2)%Z))
                 end
      end
    | Add dst (inl n1) (inr r2) =>
      match RegLocate (reg φ) r2 with
      | inr _ => (Failed, φ)
      | inl n2 => updatePC (update_reg φ dst (inl (n1 + n2)%Z))
      end
    | Add dst (inr r1) (inl n2) =>
      match RegLocate (reg φ) r1 with
      | inr _ => (Failed, φ)
      | inl n1 => updatePC (update_reg φ dst (inl (n1 + n2)%Z))
      end
    | Add dst (inl n1) (inl n2) =>
      updatePC (update_reg φ dst (inl (n1 + n2)%Z))
    | Sub dst (inr r1) (inr r2) =>
      match RegLocate (reg φ) r1 with
      | inr _ => (Failed, φ)
      | inl n1 => match RegLocate (reg φ) r2 with
                 | inr _ => (Failed, φ)
                 | inl n2 => updatePC (update_reg φ dst (inl (n1 - n2)%Z))
                 end
      end
    | Sub dst (inl n1) (inr r2) =>
      match RegLocate (reg φ) r2 with
      | inr _ => (Failed, φ)
      | inl n2 => updatePC (update_reg φ dst (inl (n1 - n2)%Z))
      end
    | Sub dst (inr r1) (inl n2) =>
      match RegLocate (reg φ) r1 with
      | inr _ => (Failed, φ)
      | inl n1 => updatePC (update_reg φ dst (inl (n1 - n2)%Z))
      end
    | Sub dst (inl n1) (inl n2) =>
      updatePC (update_reg φ dst (inl (n1 - n2)%Z))
    | Lt dst (inr r1) (inr r2) =>
      match RegLocate (reg φ) r1 with
      | inr _ => (Failed, φ)
      | inl n1 => match RegLocate (reg φ) r2 with
                 | inr _ => (Failed, φ)
                 | inl n2 => updatePC (update_reg φ dst (inl (Z.b2z (Z.ltb n1 n2))))
                 end
      end
    | Lt dst (inl n1) (inr r2) =>
      match RegLocate (reg φ) r2 with
      | inr _ => (Failed, φ)
      | inl n2 => updatePC (update_reg φ dst (inl (Z.b2z (Z.ltb n1 n2))))
      end
    | Lt dst (inr r1) (inl n2) =>
      match RegLocate (reg φ) r1 with
      | inr _ => (Failed, φ)
      | inl n1 => updatePC (update_reg φ dst (inl (Z.b2z (Z.ltb n1 n2))))
      end
    | Lt dst (inl n1) (inl n2) =>
      updatePC (update_reg φ dst (inl (Z.b2z (Z.ltb n1 n2))))
    | Subseg dst (inr r1) (inr r2) =>
      match RegLocate (reg φ) dst with
      | inl _ => (Failed, φ)
      | inr (Regular ((p, g), b, e, a)) =>
        match p with
        | E => (Failed, φ)
        | _ =>
          match RegLocate (reg φ) r1 with
          | inr _ => (Failed, φ)
          | inl n1 =>
            match RegLocate (reg φ) r2 with
            | inr _ => (Failed, φ)
            | inl n2 =>
              match z_to_addr n1, z_to_addr n2 with
              | Some a1, Some a2 =>
                if isWithin a1 a2 b e then
                  updatePC (update_reg φ dst (inr (Regular ((p, g), a1, a2, a))))
                else (Failed, φ)
              | _,_ => (Failed, φ)
              end
            end
          end
        end
      | inr (Ret _ _ _) => (Failed, φ)
      | inr (Stk d p b e a) =>
        match p with
        | E => (Failed, φ)
        | _ =>
          match RegLocate (reg φ) r1 with
          | inr _ => (Failed, φ)
          | inl n1 =>
            match RegLocate (reg φ) r2 with
            | inr _ => (Failed, φ)
            | inl n2 =>
              match z_to_addr n1, z_to_addr n2 with
              | Some a1, Some a2 =>
                if isWithin a1 a2 b e then
                  updatePC (update_reg φ dst (inr (Stk d p a1 a2 a)))
                else (Failed, φ)
              | _,_ => (Failed, φ)
              end
            end
          end
        end
      end
    | Subseg dst (inl n1) (inr r2) =>
      match RegLocate (reg φ) dst with
      | inl _ => (Failed, φ)
      | inr (Regular ((p, g), b, e, a)) =>
        match p with
        | E => (Failed, φ)
        | _ =>
          match RegLocate (reg φ) r2 with
          | inr _ => (Failed, φ)
          | inl n2 =>
            match z_to_addr n1, z_to_addr n2 with
            | Some a1, Some a2 =>
              if isWithin a1 a2 b e then
                updatePC (update_reg φ dst (inr (Regular ((p, g), a1, a2, a))))
                     else (Failed, φ)
            | _,_ => (Failed, φ)
            end
          end
        end
      | inr (Ret _ _ _) => (Failed, φ)
      | inr (Stk d p b e a) =>
        match p with
        | E => (Failed, φ)
        | _ =>
          match RegLocate (reg φ) r2 with
          | inr _ => (Failed, φ)
          | inl n2 =>
            match z_to_addr n1, z_to_addr n2 with
            | Some a1, Some a2 =>
              if isWithin a1 a2 b e then
                updatePC (update_reg φ dst (inr (Stk d p a1 a2 a)))
                     else (Failed, φ)
            | _,_ => (Failed, φ)
            end
          end
        end
      end
    | Subseg dst (inr r1) (inl n2) =>
      match RegLocate (reg φ) dst with
      | inl _ => (Failed, φ)
      | inr (Regular ((p, g), b, e, a)) =>
        match p with
        | E => (Failed, φ)
        | _ =>
          match RegLocate (reg φ) r1 with
          | inr _ => (Failed, φ)
          | inl n1 =>
            match z_to_addr n1, z_to_addr n2 with
            | Some a1, Some a2 =>
              if isWithin a1 a2 b e then
                updatePC (update_reg φ dst (inr (Regular ((p, g), a1, a2, a))))
              else (Failed, φ)
            | _,_ => (Failed, φ)
            end
          end
        end
      | inr (Ret _ _ _) => (Failed, φ)
      | inr (Stk d p b e a) =>
        match p with
        | E => (Failed, φ)
        | _ =>
          match RegLocate (reg φ) r1 with
          | inr _ => (Failed, φ)
          | inl n1 =>
            match z_to_addr n1, z_to_addr n2 with
            | Some a1, Some a2 =>
              if isWithin a1 a2 b e then
                updatePC (update_reg φ dst (inr (Stk d p a1 a2 a)))
              else (Failed, φ)
            | _,_ => (Failed, φ)
            end
          end
        end
      end
    | Subseg dst (inl n1) (inl n2) =>
      match RegLocate (reg φ) dst with
      | inl _ => (Failed, φ)
      | inr (Regular ((p, g), b, e, a)) =>
        match p with
        | E => (Failed, φ)
        | _ =>
          match z_to_addr n1, z_to_addr n2 with
          | Some a1, Some a2 =>
            if isWithin a1 a2 b e then
              updatePC (update_reg φ dst (inr (Regular ((p, g), a1, a2, a))))
            else (Failed, φ)
          | _,_ => (Failed, φ)
          end
        end
      | inr (Ret _ _ _) => (Failed, φ)
      | inr (Stk d p b e a) =>
        match p with
        | E => (Failed, φ)
        | _ =>
          match z_to_addr n1, z_to_addr n2 with
          | Some a1, Some a2 =>
            if isWithin a1 a2 b e then
              updatePC (update_reg φ dst (inr (Stk d p a1 a2 a)))
            else (Failed, φ)
          | _,_ => (Failed, φ)
          end
        end
      end
    | GetA dst r =>
      match RegLocate (reg φ) r with
      | inl _ => (Failed, φ)
      | inr (Regular (_, _, _, a)) | inr (Ret _ _ a) | inr (Stk _ _ _ _ a) =>
        match a with
        | A a' _ _ => updatePC (update_reg φ dst (inl a'))
        end
      end
    | GetB dst r =>
      match RegLocate (reg φ) r with
      | inl _ => (Failed, φ)
      | inr (Regular (_, b, _, _)) | inr (Ret b _ _) | inr (Stk _ _ b _ _) =>
        match b with
        | A b' _ _ => updatePC (update_reg φ dst (inl b'))
        end
      end
    | GetE dst r =>
      match RegLocate (reg φ) r with
      | inl _ => (Failed, φ)
      | inr (Regular (_, _, e, _)) | inr (Ret _ e _) | inr (Stk _ _ _ e _) =>
        match e with
        | A e' _ _ => updatePC (update_reg φ dst (inl e'))
        end
      end
    | GetP dst r =>
      match RegLocate (reg φ) r with
      | inl _ => (Failed, φ)
      | inr (Regular ((p, _), _, _, _))
      | inr (Stk _ p _ _ _) =>
        updatePC (update_reg φ dst (inl (encodePerm p)))
      | inr (Ret _ _ _) =>
        updatePC (update_reg φ dst (inl (encodePerm E)))
      end
    | GetL dst r =>
      match RegLocate (reg φ) r with
      | inl _ => (Failed, φ)
      | inr (Regular ((_, g), _, _, _)) => updatePC (update_reg φ dst (inl (encodeLoc g)))
      | inr (Stk _ _ _ _ _)
      | inr (Ret _ _ _) =>
        updatePC (update_reg φ dst (inl (encodeLoc Directed)))
      end
    | IsPtr dst r =>
      match RegLocate (reg φ) r with
      | inl _ => updatePC (update_reg φ dst (inl 0%Z))
      | inr _ => updatePC (update_reg φ dst (inl 1%Z))
      end
    | LoadU rdst rsrc offs =>
      match RegLocate (reg φ) rsrc with
      | inl _ => (Failed, φ)
      | inr (Regular ((p, g), b, e, a)) =>
        if isU p then
          match z_of_argument (reg φ) offs with
          | None => (Failed, φ)
          | Some noffs => match verify_access (LoadU_access b e a noffs) with
                         | None => (Failed, φ)
                         | Some a' => updatePC (update_reg φ rdst (MemLocate (mem φ) a'))
                         end
          end
        else (Failed, φ)
      | inr (Ret _ _ _) => (Failed, φ)
      | inr (Stk d p b e a) =>
        if isU p then
          match z_of_argument (reg φ) offs with
          | None => (Failed, φ)
          | Some noffs => match verify_access (LoadU_access b e a noffs) with
                         | None => (Failed, φ)
                         | Some a' => match stack d ((reg φ, stk φ)::(callstack φ)) with
                                     | None => (Failed, φ)
                                     | Some m => updatePC (update_reg φ rdst (MemLocate m a'))
                                     end
                         end
          end
        else (Failed, φ)
      end
    | StoreU dst offs src =>
      let w := match src with
               | inl n => inl n
               | inr rsrc => (RegLocate (reg φ) rsrc)
               end in
      match RegLocate (reg φ) dst with
      | inl _ => (Failed, φ)
      | inr (Regular ((p, g), b, e, a)) =>
        match z_of_argument (reg φ) offs with
        | None => (Failed, φ)
        | Some noffs => match verify_access (StoreU_access b e a noffs) with
                       | None => (Failed, φ)
                       | Some a' => if isU p && canStoreU p a' w then
                                     if addr_eq_dec a a' then
                                       match (a + 1)%a with
                                       | Some a => updatePC (update_reg (update_mem φ a' w) dst (inr (Regular ((p, g), b, e, a))))
                                       | None => (Failed, φ)
                                       end
                                     else updatePC (update_mem φ a' w)
                                   else (Failed, φ)
                       end
        end
      | inr (Ret _ _ _) => (Failed, φ)
      | inr (Stk d p b e a) =>
        match z_of_argument (reg φ) offs with
        | None => (Failed, φ)
        | Some noffs => match verify_access (StoreU_access b e a noffs) with
                       | None => (Failed, φ)
                       | Some a' => if isU p && canStoreU p a' w then
                                     if addr_eq_dec a a' then
                                       match (a + 1)%a with
                                       | Some a =>
                                         if nat_eq_dec d (length (callstack φ)) then
                                           updatePC (update_reg (update_stk φ a' w) dst (inr (Stk d p b e a)))
                                         else match update_stack φ d a' w with
                                              | None => (Failed, φ)
                                              | Some φ' => updatePC (update_reg φ' dst (inr (Stk d p b e a)))
                                              end
                                       | None => (Failed, φ)
                                       end
                                     else if nat_eq_dec d (length (callstack φ))
                                         then
                                           updatePC (update_stk φ a' w)
                                         else match update_stack φ d a' w with
                                              | None => (Failed, φ)
                                              | Some φ' => updatePC φ'
                                              end
                                   else (Failed, φ)
                       end
        end
      end
    | PromoteU dst =>
      match RegLocate (reg φ) dst with
      | inr (Regular ((p, g), b, e, a)) =>
        if perm_eq_dec p E then (Failed, φ)
        else updatePC (update_reg φ dst (inr (Regular ((promote_perm p, g), b, min a e, a))))
      | inr (Ret _ _ _) => (Failed, φ)
      | inr (Stk d p b e a) =>
        if perm_eq_dec p E then (Failed, φ)
        else updatePC (update_reg φ dst (inr (Stk d (promote_perm p) b (min a e) a)))
      | inl _ => (Failed, φ)
      end
    end.

  Definition clear_regs (reg: base.Reg) (l: list RegName) :=
    foldr (fun r reg => <[r := inl 0%Z]> reg) reg l.

  Fixpoint exec_instrs (l: list instr) (φ: ExecConf): option ExecConf :=
    match l with
    | [] => Some φ
    | i::l => match exec i φ with
              | (NextI, φ) => exec_instrs l φ
              | _ => None
              end
    end.

  Definition addPC (w: base.Word) (n: nat) :=
    match w with
    | inr (Regular (p, l, b, e, a)) =>
      match (a + n)%a with
      | Some a' => inr (Regular (p, l, b, e, a'))
      | None => w
      end
    | inr (Stk d p b e a) =>
      match (a + n)%a with
      | Some a' => inr (Stk d p b e a')
      | None => w
      end
    | _ => w
    end.

  (* Remove all words over some bounds *)
  Fixpoint clear_stk_aux (m: base.Mem) (a: Addr) (n: nat) :=
    match n with
    | 0 => delete a m
    | S n => match (a + 1)%a with
             | None => delete a m
             | Some a' => clear_stk_aux (delete a m) a' n
             end
    end.

  Lemma clear_stk_aux_spec:
    forall n m a,
      (forall a' k, k <= n -> (a + k)%a = Some a' -> (clear_stk_aux m a n) !! a' = None) /\
      (forall a', (a' < a)%a -> (clear_stk_aux m a n) !! a' = m !! a').
  Proof.
    induction n; intros.
    - split; intros.
      + assert (k = 0) as -> by lia.
        rewrite addr_add_0 in H1.
        inversion H1. simpl. rewrite lookup_delete //.
      + simpl. rewrite lookup_delete_ne //. solve_addr.
    - split; intros.
      + destruct (nat_eq_dec k (S n)).
        * subst k. simpl. generalize (incr_addr_spec a 1).
          intros [[a'' [HA [HB [HC HD]]]] | [HA HB]].
          { rewrite HA. assert ((a'' + n)%a = Some a') by solve_addr.
            destruct (IHn (delete a m) a'') as [X Y].
            eapply (X a' n ltac:(lia) H2). }
          { exfalso. solve_addr. }
        * simpl. destruct (a + 1)%a as [a''|] eqn:Ha''.
          { destruct (nat_eq_dec k 0).
            - subst k. rewrite addr_add_0 in H1. inversion H1.
              subst a'. destruct (IHn (delete a m) a'') as [X Y].
              rewrite (Y a ltac:(solve_addr)).
              rewrite lookup_delete //.
            - destruct (IHn (delete a m) a'') as [X Y].
              rewrite (X a' (k - 1) ltac:(lia) ltac:(solve_addr)) //. }
          { assert (k = 0) as -> by solve_addr.
            rewrite addr_add_0 in H1; inversion H1; subst a'.
            rewrite lookup_delete //. }
      + simpl. destruct (a + 1)%a as [a''|] eqn:Ha''.
        * destruct (IHn (delete a m) a'') as [X Y].
          rewrite (Y a' ltac:(solve_addr)).
          rewrite lookup_delete_ne //. solve_addr.
        * rewrite lookup_delete_ne //. solve_addr.
  Qed.

  Definition clear_stk (m: base.Mem) (a: Addr) :=
    clear_stk_aux m a (Z.to_nat MemNum).

  Lemma clear_stk_spec:
    forall m a,
      (forall a', (a <= a')%a -> (clear_stk m a) !! a' = None) /\
      (forall a', (a' < a)%a -> (clear_stk m a) !! a' = m !! a').
  Proof.
    intros.
    generalize (clear_stk_aux_spec (Z.to_nat MemNum) m a). intros [A B].
    split; intros.
    - assert ((a + (a' - a)%Z)%a = Some a') by solve_addr.
      assert (Z.to_nat (a' - a)%Z <= (Z.to_nat MemNum)) by solve_addr.
      eapply A; eauto. solve_addr.
    - eapply B; eauto.
  Qed.

  Definition decodeInstrW' (w: base.Word) :=
    match w with
    | inl n => decodeInstrW (inl n)
    | inr _ => Fail
    end.

  (* Definition measure (w: base.Word): nat := *)
  (*   match w with *)
  (*   | inr (Stk d p b e a) => Z.to_nat (canReadUpTo w) *)
  (*   | _ => 0 *)
  (*   end. *)

  (* Inductive legal: list Stackframe -> Prop := *)
  (* | legal_nil: *)
  (*     legal [] *)
  (* | legal_cons: *)
  (*     forall reg stk cs *)
  (*     (Hcons_legal: map_Forall (fun a w => canReadUpTo w <= a)%a stk) *)
  (*     (Hlegal: legal cs), *)
  (*     legal ((reg, stk)::cs). *)

  (* Lemma is_legal_dec cs: *)
  (*   Decision (legal cs). *)
  (* Proof. *)
  (*   induction cs. *)
  (*   - left; constructor. *)
  (*   - destruct IHcs. *)
  (*     + destruct a as [reg stk]. *)
  (*       assert (forall a w, Decision ((fun a w => canReadUpTo w <= a)%a a w)). *)
  (*       { intros. apply (Addr_le_dec (canReadUpTo w) a). } *)
  (*       destruct (map_Forall_dec (fun a w => canReadUpTo w <= a)%a stk). *)
  (*       * left; econstructor; eauto. *)
  (*       * right. intro Y. inversion Y; subst; clear Y. *)
  (*         apply n; auto. *)
  (*     + right. intro Y. apply n. inversion Y; auto. *)
  (* Qed. *)

  (* Fixpoint region_addrs_aux (b: Addr) (n: nat): list Addr := *)
  (*   match n with *)
  (*   | 0 => nil *)
  (*   | S n => b :: (region_addrs_aux (^(b + 1)%a) n) *)
  (*   end. *)

  (* Definition region_size : Addr → Addr → nat := *)
  (*   λ b e, Z.to_nat (e - b). *)

  (* Definition region_addrs (b e: Addr): list Addr := *)
  (*   region_addrs_aux b (region_size b e). *)

  (* Equations is_safe_generalized (cs: list Stackframe) (w: base.Word): bool by wf (measure w) lt := *)
  (* is_safe_generalized cs (inr (Stk d p b e a)) := *)
  (*   if is_legal_dec cs then *)
  (*     if nat_eq_dec d (length cs) then true *)
  (*     else match cs !! d with *)
  (*          | None => false *)
  (*          | Some (reg, stk) => *)
  (*            match reg !! r_stk with *)
  (*            | Some (inr (Stk d' p' b' e' a')) => *)
  (*              if Addr_lt_dec e a' then *)
  (*                foldl (fun b a => match stk !! a with | Some w => b && (is_safe_generalized cs w) | _ => false end) true (region_addrs b (addr_reg.min e (canReadUpTo (inr (Stk d p b e a))))) *)
  (*              else false *)
  (*            | _ => false *)
  (*            end *)
  (*          end *)
  (*   else false; *)
  (* is_safe_generalized _ _ := true. *)
  (* Next Obligation. *)
  (* (* (* Cannot prove the obligation because Coq forgets that w is within (region_addrs b (addr_reg.min e (canReadUpTo w))) *) *) *)

  Definition is_safe (w: base.Word): Prop :=
    match w with
    | inl _ => True
    | inr (Stk d p b e a) => False
    | inr (Ret b e a) => False
    | inr (Regular _) => True
    end.

  Lemma is_safe_dec:
    forall w, Decision (is_safe w).
  Proof.
    destruct w.
    - left; simpl; auto.
    - destruct c.
      + left; simpl; auto.
      + right; simpl; auto.
      + right; simpl; auto.
  Qed.

  Definition is_call (regs: base.Reg) rf rargs (m: base.Mem) a e: Prop :=
    exists a',
      PC ∉ rf::rargs /\
      r_stk ∉ rf::rargs /\
      (R 0 eq_refl) ∉ rf::rargs /\
      (R 1 eq_refl) ∉ rf::rargs /\
      (R 2 eq_refl) ∉ rf::rargs /\
      (a + (141 + length rargs))%a = Some a' /\
      (a' < e)%a /\
      (forall i, (i < (141 + length rargs))%nat ->
            exists a_i, (a + i)%a = Some a_i /\ (call_instrs rf rargs) !! i = m !! a_i) /\
      (forall r, r ∈ rf::rargs -> is_safe (regs !r! r)).

  Lemma is_call_determ:
    forall regs rf1 rf2 rargs1 rargs2 m a e,
    is_call regs rf1 rargs1 m a e ->
    is_call regs rf2 rargs2 m a e ->
    rf1 = rf2 /\ rargs1 = rargs2.
  Proof.
    Local Opaque app. (* Hack so Qed terminates *)
    intros. destruct H0 as [a' [HA1 [HA2 [HA3 [HA4 [HA5 [HA6 [HA7 [HA8 HA9]]]]]]]]].
    destruct H1 as [a'' [HB1 [HB2 [HB3 [HB4 [HB5 [HB6 [HB7 [HB8 HB9]]]]]]]]].
    eapply not_elem_of_cons in HA1. destruct HA1 as [HA1 HA1'].
    eapply not_elem_of_cons in HA2. destruct HA2 as [HA2 HA2'].
    eapply not_elem_of_cons in HB1. destruct HB1 as [HB1 HB1'].
    eapply not_elem_of_cons in HB2. destruct HB2 as [HB2 HB2'].
    assert (Hleneq: length rargs1 = length rargs2).
    { destruct (HA8 100 ltac:(lia)) as [a_i [Ha_i Hinstr]].
      destruct (HB8 100 ltac:(lia)) as [a_i' [Ha_i' Hinstr']].
      rewrite Ha_i' in Ha_i; inversion Ha_i; subst.
      unfold call_instrs in Hinstr, Hinstr'.
      rewrite (@lookup_app_l (base.Word) (call_instrs_prologue rargs1) _ 100) in Hinstr; [|rewrite call_instrs_prologue_length; lia].
      rewrite lookup_app_l in Hinstr'; [|rewrite call_instrs_prologue_length; lia].
      rewrite /call_instrs_prologue lookup_app_r in Hinstr; [|simpl; lia].
      rewrite /= lookup_app_r in Hinstr; [|rewrite push_env_instrs_length; lia].
      rewrite /= lookup_app_r in Hinstr; [|simpl; lia].
      rewrite /= lookup_app_r in Hinstr; [|rewrite push_instrs_length !app_length map_length pop_env_instrs_length /=; lia].
      rewrite push_instrs_length !app_length map_length pop_env_instrs_length /= in Hinstr.
      rewrite lookup_app_l /= in Hinstr; [|simpl; lia].
      rewrite /call_instrs_prologue lookup_app_r in Hinstr'; [|simpl; lia].
      rewrite /= lookup_app_r in Hinstr'; [|rewrite push_env_instrs_length; lia].
      rewrite /= lookup_app_r in Hinstr'; [|simpl; lia].
      rewrite /= lookup_app_r in Hinstr'; [|rewrite push_instrs_length !app_length map_length pop_env_instrs_length /=; lia].
      rewrite push_instrs_length !app_length map_length pop_env_instrs_length /= in Hinstr'.
      rewrite lookup_app_l /= in Hinstr'; [|simpl; lia].
      rewrite -Hinstr' in Hinstr. inversion Hinstr.
      eapply encode_instr_inj in H1. inversion H1. lia. }
    split.
    { destruct (HA8 (140 + length rargs1) ltac:(lia)) as [a_i [Ha_i Hinstr]].
      destruct (HB8 (140 + length rargs1) ltac:(lia)) as [a_i' [Ha_i' Hinstr']].
      rewrite Ha_i' in Ha_i; inversion Ha_i; subst.
      rewrite /call_instrs in Hinstr, Hinstr'.
      rewrite lookup_app_r in Hinstr; [|rewrite call_instrs_prologue_length; lia].
      rewrite lookup_app_r in Hinstr'; [|rewrite call_instrs_prologue_length; lia].
      rewrite call_instrs_prologue_length lookup_app_r in Hinstr; [|simpl; lia].
      rewrite lookup_app_r in Hinstr; [|simpl; lia].
      simpl length in Hinstr.
      rewrite lookup_app_r in Hinstr; [|rewrite push_instrs_length /=; lia].
      rewrite push_instrs_length in Hinstr. simpl length in Hinstr.
      rewrite lookup_app_r in Hinstr; [|rewrite push_instrs_length map_length; lia].
      rewrite lookup_app_r in Hinstr; [|rewrite rclear_instrs_length all_registers_list_difference_length // push_instrs_length map_length; lia].
      rewrite rclear_instrs_length all_registers_list_difference_length // push_instrs_length map_length in Hinstr.
      rewrite call_instrs_prologue_length lookup_app_r in Hinstr'; [|simpl; lia].
      rewrite lookup_app_r in Hinstr'; [|simpl; lia].
      simpl length in Hinstr'.
      rewrite lookup_app_r in Hinstr'; [|rewrite push_instrs_length /=; lia].
      rewrite push_instrs_length in Hinstr'. simpl length in Hinstr'.
      rewrite lookup_app_r in Hinstr'; [|rewrite push_instrs_length map_length; lia].
      rewrite lookup_app_r in Hinstr'; [|rewrite rclear_instrs_length all_registers_list_difference_length // push_instrs_length map_length; lia].
      rewrite rclear_instrs_length all_registers_list_difference_length // push_instrs_length map_length in Hinstr'.
      replace (140 + length rargs1 - 102 - 4 - 3 - 1 - length rargs1 - 30) with 0 in Hinstr by lia.
      replace (140 + length rargs1 - 102 - 4 - 3 - 1 - length rargs2 - 30) with 0 in Hinstr' by lia.
      simpl in Hinstr, Hinstr'. rewrite -Hinstr' in Hinstr. inversion Hinstr.
      eapply encode_instr_inj in H1. inversion H1; auto. }
    destruct (nat_eq_dec (length rargs1) 0).
    { eapply nil_length_inv in e0. subst rargs1.
      destruct rargs2; auto. simpl in Hleneq. inversion Hleneq. }
    assert (Hpush_regs_eq: forall i, i < length rargs1 -> (push_instrs (map (fun r => inr r) rargs1)) !! i = (push_instrs (map (fun r => inr r) rargs2)) !! i).
    { intros. destruct (HA8 (110 + i) ltac:(lia)) as [a_i [Ha_i Hinstr]].
      destruct (HB8 (110 + i) ltac:(lia)) as [a_i' [Ha_i' Hinstr']].
      rewrite Ha_i' in Ha_i; inversion Ha_i; subst.
      rewrite /call_instrs in Hinstr, Hinstr'.
      rewrite lookup_app_r in Hinstr; [|rewrite call_instrs_prologue_length; lia].
      rewrite lookup_app_r in Hinstr'; [|rewrite call_instrs_prologue_length; lia].
      rewrite call_instrs_prologue_length in Hinstr.
      rewrite call_instrs_prologue_length in Hinstr'.
      rewrite lookup_app_r in Hinstr; [|simpl; lia].
      rewrite lookup_app_r in Hinstr'; [|simpl; lia].
      simpl length in Hinstr, Hinstr'.
      rewrite lookup_app_r in Hinstr; [|simpl; lia].
      rewrite lookup_app_r in Hinstr'; [|simpl; lia].
      simpl length in Hinstr, Hinstr'.
      rewrite lookup_app_r in Hinstr; [|simpl; lia].
      rewrite lookup_app_r in Hinstr'; [|simpl; lia].
      simpl length in Hinstr, Hinstr'.
      rewrite lookup_app_l in Hinstr; [|rewrite push_instrs_length map_length; lia].
      rewrite lookup_app_l in Hinstr'; [|rewrite push_instrs_length map_length; lia].
      replace (110 + i - 102 - 4 - 3 - 1) with i in Hinstr by lia.
      replace (110 + i - 102 - 4 - 3 - 1) with i in Hinstr' by lia.
      rewrite -Hinstr' in Hinstr; inversion Hinstr. auto. }
    assert (Hpush_regs_eq': push_instrs (map (λ r : RegName, inr r) rargs1) = push_instrs (map (λ r : RegName, inr r) rargs2)).
    { eapply list_eq_same_length; [eauto|rewrite !push_instrs_length !map_length //|].
      rewrite push_instrs_length map_length -Hleneq. intros.
      rewrite (Hpush_regs_eq _ H0) in H1. rewrite H1 in H2; inversion H2; auto. }
    clear Hpush_regs_eq. eapply push_instrs_inj in Hpush_regs_eq'.
    eapply fmap_inj in Hpush_regs_eq'; auto.
    inversion 1; auto.
  Qed.

  (* Pushing a list of words starting at address a *)
  Definition push_words (stk: base.Mem) (a: Addr) (ws: list base.Word) :=
    match (foldl (fun oastk w => match oastk with None => None | Some (a, stk) => if canStoreU URWLX a w then Some (^(a + 1)%a, <[a:=w]> stk) else None end) (Some (a, stk)) ws) with
    | Some (_, stk) => Some stk
    | None => None
    end.

  Definition exec_call (φ: ExecConf) (rf: RegName) (rargs: list RegName) pcp pcg (pcb pce pca: Addr): Conf :=
    match pcg with
    | Directed => (Failed, φ) (* Can't store PC if it's monotone because we currently assume heap is above stack *)
    | _ =>
    match (reg φ) !r! r_stk with
    | inr (Stk d URWLX b e a) =>
      if (Addr_lt_dec b a) then
      (* We know that d = length (callstack φ) *)
      match (a + (100 + length rargs))%a with
      | Some a' => match (pca + (length (call_instrs rf rargs)))%a with
                   | Some pca' =>
                     if (Addr_le_dec a' e) then
                     let saved_regs := <[PC := inr (Regular (pcp, pcg, pcb, pce, pca'))]> (<[r_stk := inr (Stk d URWLX b e ^(a + 1)%a)]> (reg φ)) in
                     match push_words (stk φ) a ([inr (Regular (pcp, pcg, pcb, pce, ^(pca' + -1)%a))] ++ (map (fun r => ((reg φ) !r! r)) (list_difference all_registers [PC; r_stk])) ++ [inr (Stk d URWLX b e ^(a + 32)%a)] ++ ([inl (encodeInstr (Mov (R 1 eq_refl) (inr PC))); inl (encodeInstr (Lea (R 1 eq_refl) (inl (- 1)%Z))); inl (encodeInstr (Load r_stk (R 1 eq_refl)))] ++ List.map inl pop_env_instrs ++ [inl (encodeInstr (LoadU PC r_stk (inl (- 1)%Z)))])) with
                     | Some saved_stk =>
                       match push_words ∅ ^(a + 99)%a ([inr (Ret b ^(a + 99)%a ^(a + 33)%a)] ++ (map (fun r => ((reg φ) !r! r)) rargs)) with
                       | Some new_stk => (NextI, (<[PC := updatePcPerm ((reg φ !r! rf))]> (<[r_stk := inr (Stk (d + 1) URWLX ^(a + 99)%a e ^(a + (100 + length rargs))%a)]> (<[rf := (reg φ) !r! rf]> (gset_to_gmap (inl 0%Z) (list_to_set all_registers)))), mem φ, new_stk, (saved_regs, clear_stk saved_stk ^(a + 99)%a)::callstack φ))
                       | None => (Failed, φ)
                       end
                     | None => (Failed, φ)
                     end
                     else (Failed, φ)
                   | None => (Failed, φ)
                   end
      | None => (Failed, φ) (* Not enough space to push everything on the stack *)
      end
      else (Failed, φ)
    | _ =>
      (* Won't be able to store the return capability if not URWLX *)
      (Failed, φ)
    end
    end.

  Definition depth_of (w: base.Word): option nat :=
    match w with
    | inr (Stk d _ _ _ _) => Some d
    | _ => None
    end.

  Inductive step: Conf → Conf → Prop :=
  | step_exec_fail:
      forall φ,
        not (isCorrectPC ((reg φ) !r! PC)) →
        step (Executable, φ) (Failed, φ)
  | step_exec_fail': (* This should never happen *)
      forall φ d p b e a,
        RegLocate (reg φ) PC = inr (Stk d p b e a) ->
        stack d ((reg φ, stk φ)::(callstack φ)) = None ->
        step (Executable, φ) (Failed, φ)
  | step_exec_instr:
      forall φ p g b e a i c,
        RegLocate (reg φ) PC = inr (Regular ((p, g), b, e, a)) ->
        isCorrectPC ((reg φ) !r! PC) →
        decodeInstrW' ((mem φ) !m! a) = i →
        exec i φ = c →
        (~ exists rf rargs, is_call (reg φ) rf rargs (mem φ) a e /\ (exec_call φ rf rargs p g b e a).1 = NextI) \/ (match depth_of ((reg φ) !r! r_stk) with Some d => d <> length (callstack φ) | None => True end) ->
        step (Executable, φ) (c.1, c.2)
  | step_exec_instr':
      forall φ d p b e a i c m,
        RegLocate (reg φ) PC = inr (Stk d p b e a) ->
        isCorrectPC ((reg φ) !r! PC) →
        stack d ((reg φ, stk φ)::(callstack φ)) = Some m ->
        decodeInstrW' (m !m! a) = i →
        exec i φ = c →
        step (Executable, φ) (c.1, c.2)
  | step_exec_call:
      forall φ p g b e a φ' rf rargs,
        RegLocate (reg φ) PC = inr (Regular ((p, g), b, e, a)) ->
        isCorrectPC ((reg φ) !r! PC) →
        is_call (reg φ) rf rargs (mem φ) a e ->
        depth_of ((reg φ) !r! r_stk) = Some (length (callstack φ)) ->
        exec_call φ rf rargs p g b e a  = (NextI, φ') ->
        step (Executable, φ) (NextI, φ').

  (* TODO: move into stdpp_extra and maybe upstream *)
  Global Instance lists_finite {A} `{Finite A} n:
    Finite { l : list A | length l <=? n = true }.
  Proof.
    induction n.
    - refine {| enum := [[]↾eq_refl]; NoDup_enum := _; elem_of_enum := _ |}.
      + repeat econstructor. intro. inversion H1.
      + intros. destruct x. destruct x.
        * apply elem_of_list_singleton. by apply (sig_eq_pi _).
        * simpl in e. inversion e.
    - assert (Hf1: forall (l: list A), (length l <=? n) = true -> (length l <=? S n) = true) by (intros l Hl; erewrite Nat.leb_le in Hl; rewrite Nat.leb_le; lia).
      assert (Hf2: forall (l: list A), length l = S n -> (length l <=? S n) = true) by (intros; rewrite Nat.leb_le; lia).
      set (f := fun (x: sum {l : list A | (length l <=? n) = true} {l : list A | length l = S n}) => match x return {l : list A | (length l <=? S n) = true} with | inl (l ↾ p) => l ↾ (Hf1 l p) | inr (l ↾ p) => l ↾ (Hf2 l p) end).
      eapply @surjective_finite with (f := f).
      + eapply sum_finite.
      + intro y. destruct y as [l Hl].
        destruct (Nat.eq_dec (length l) (S n)).
        * exists (inr (l ↾ e)). simpl. by apply (sig_eq_pi _).
        * generalize (proj1 (Nat.leb_le _ _) Hl); intros Hl'.
          assert (Hl'': length l <= n) by lia.
          exists (inl (l ↾ (proj2 (Nat.leb_le _ _) Hl''))).
          simpl. by apply (sig_eq_pi _).
  Qed.

  (* TODO: move into stdpp_extra and maybe upstream *)
  Lemma sig_exists_dec {A} {P Q: A -> Prop} `{Finite { x : A | Q x }}:
    (forall x, P x -> Q x) ->
    (∀ x : A, Decision (P x)) ->
    Decision (∃ x : A, P x).
  Proof.
    intros. generalize (exists_dec (fun x => P (proj1_sig x))).
    intros. destruct H2.
    - left. destruct e. eauto.
    - right. intro. eapply n.
      destruct H2. generalize (H1 _ H2). intros.
      exists (exist _ x H3). simpl. auto.
  Qed.

  Lemma is_call_dec:
    forall regs m a e,
      Decision (exists rf rargs, is_call regs rf rargs m a e).
  Proof.
    intros. eapply exists_dec. intros rf.
    eapply @sig_exists_dec with (Q := fun l => length l <=? Z.to_nat (e - a)%Z = true).
    - eapply _.
    - intros. destruct H0 as [a' [HPC [Hstk [HA [HB [HC [HD [HE HF]]]]]]]].
      revert HD HE. clear. intros HD HE.
      eapply Nat.leb_le. solve_addr.
    - intros rargs. destruct (elem_of_list_dec PC (rf::rargs)).
      { right. intro X. destruct X as [a' [HPC [Hstk [HA [HB [HC [HD [HE HF]]]]]]]].
        eapply HPC; auto. }
      destruct (elem_of_list_dec r_stk (rf::rargs)).
      { right. intro X. destruct X as [a' [HPC [Hstk [HA [HB [HC [HD [HE HF]]]]]]]].
        eapply Hstk; auto. }
      eapply not_elem_of_cons in n; destruct n as [n Hn].
      eapply not_elem_of_cons in n0; destruct n0 as [n0 Hn0].
      destruct (elem_of_list_dec (R 0 eq_refl) (rf::rargs)).
      { right. intro X. destruct X as [a' [HPC [Hstk [HA [HB [HC [HD [HE HF]]]]]]]].
        eapply HA; auto. }
      destruct (elem_of_list_dec (R 1 eq_refl) (rf::rargs)).
      { right. intro X. destruct X as [a' [HPC [Hstk [HA [HB [HC [HD [HE HF]]]]]]]].
        eapply HB; auto. }
      destruct (elem_of_list_dec (R 2 eq_refl) (rf::rargs)).
      { right. intro X. destruct X as [a' [HPC [Hstk [HA [HB [HC [HD [HE HF]]]]]]]].
        eapply HC; auto. }
      destruct ((a + (141 + length rargs))%a) as [a'|] eqn:Ha'.
      2: { right. intro X. destruct X as [a' [HPC [Hstk [HA [HB [HC [HD [HE HF]]]]]]]].
           congruence. }
      destruct (Addr_lt_dec a' e).
      2: { right. intro X. destruct X as [a'' [HPC [Hstk [HA [HB [HC [HD [HE HF]]]]]]]].
           rewrite HD in Ha'; inversion Ha'; subst.
           eapply n4; auto. }
      assert (Decision (∀ (i : fin (141 + length rargs)), ∃ a_i : Addr, (a + fin_to_nat i)%a = Some a_i ∧ call_instrs rf rargs !! (fin_to_nat i) = m !! a_i)).
      { eapply forall_dec. intros. destruct (a + x)%a as [a_i|] eqn:Ha_i.
        - case_eq ((call_instrs rf rargs) !! (fin_to_nat x)); intros.
          + destruct (m !! a_i) as [w'|] eqn:Hw'.
            * destruct (base.word_eq_dec w w').
              { subst w; left; eauto. }
              { right. intros [a_i' [A B]].
                inversion A; subst a_i'; clear A.
                rewrite B in H0; inversion H0; subst. congruence. }
            * right. intros [a_i' [A B]].
              inversion A; subst a_i'; clear A.
              rewrite B in H0; inversion H0; subst. congruence.
          + exfalso. rewrite list_lookup_lookup_total_lt in H0; [congruence|].
            rewrite call_instrs_length; auto. eapply fin_to_nat_lt.
        - right; intros [a_i' [A B]].
          inversion A. }
      assert (Decision (∀ r : RegName, r ∈ rf::rargs → is_safe (regs !r! r))).
      { clear. induction (rf::rargs).
        - left. intros. inversion H.
        - destruct (is_safe_dec (regs !r! a)).
          + destruct IHl.
            * left. intros. eapply elem_of_cons in H.
              destruct H; [subst a|]; auto.
            * right. red; intros. eapply n.
              intros. eapply H. right. auto.
          + right. red; intros. eapply n.
            eapply H. left. }
      destruct H0.
      2: { right. intro X. destruct X as [a'' [HPC [Hstk [HA [HB [HC [HD [HE [HF HG]]]]]]]]].
           eapply n4. intros. eapply (HF (fin_to_nat i)).
           generalize (fin_to_nat_lt i). lia. }
      destruct H1.
      { left. exists a'. repeat split; eauto; [eapply not_elem_of_cons; auto|eapply not_elem_of_cons; auto|].
        intros. assert (i0 < (141 + length rargs)) by lia.
        generalize (e0 (nat_to_fin H1)). rewrite fin_to_nat_to_fin. auto. }
      right. intro X. destruct X as [a'' [HPC [Hstk [HA [HB [HC [HD [HE [HF HG]]]]]]]]].
      eapply n4; auto.
  Qed.

  Lemma normal_always_step:
    forall φ, exists cf φ', step (Executable, φ) (cf, φ').
  Proof.
    intros. destruct (isCorrectPC_dec (RegLocate (reg φ) PC)).
    - inversion i; subst.
      + destruct (is_call_dec (reg φ) (mem φ) a e) as [Hiscall|Hiscall].
        * destruct Hiscall as [rf [rargs Hiscall]].
          destruct (depth_of (RegLocate (reg φ) r_stk)) eqn:X.
          { destruct (nat_eq_dec n (length (callstack φ))).
            - subst n.
              + destruct (exec_call φ rf rargs p g b e a) as [cf φ'] eqn:Hexec.
                assert (cf = NextI \/ cf <> NextI) as [->|Hne] by (destruct cf; auto).
                * do 2 eexists. eapply step_exec_call; eauto.
                * do 2 eexists; eapply step_exec_instr; eauto.
                  left. intro Y. destruct Y as [rf' [rargs' [HY HZ]]].
                  generalize (is_call_determ _ _ _ _ _ _ _ _ HY Hiscall).
                  intros [-> ->]. rewrite Hexec /= in HZ. elim Hne; auto.
            - do 2 eexists; eapply step_exec_instr; eauto.
              right; rewrite X /=; auto. }
          { do 2 eexists; eapply step_exec_instr; eauto.
            right; rewrite X /=; auto. }
        * do 2 eexists; eapply step_exec_instr; eauto.
          left. intro X. eapply Hiscall. destruct X as [rf [rargs [Hiscall' ?]]].
          eauto.
      + destruct (stack d ((reg φ, stk φ)::(callstack φ))) as [m|] eqn:Hstk.
        * do 2 eexists; eapply step_exec_instr'; eauto.
        * do 2 eexists. eapply step_exec_fail'; eauto.
    - exists Failed, φ. constructor 1; eauto.
  Qed.

  Lemma step_deterministic:
    forall c1 c2 c2' σ1 σ2 σ2',
      step (c1, σ1) (c2, σ2) →
      step (c1, σ1) (c2', σ2') →
      c2 = c2' ∧ σ2 = σ2'.
  Proof.
    Ltac inv H := inversion H; clear H; subst.
    intros * H1 H2; split; inv H1; inv H2; auto; try congruence.
    - rewrite H4 in H6; inv H6.
      destruct H10 as [X | X]; [elim X; eexists; eexists; split; eauto; rewrite H11; eauto|rewrite H9 in X; elim X; eauto].
    - rewrite H4 in H6; inv H6.
      destruct H13 as [X | X]; [elim X; eexists; eexists; split; eauto; rewrite H10; eauto|rewrite H9 in X; elim X; eauto].
    - rewrite H4 in H6; inv H6.
      destruct H10 as [X | X]; [elim X; eexists; eexists; split; eauto; rewrite H11; eauto|rewrite H9 in X; elim X; eauto].
    - rewrite H4 in H6; inv H6.
      destruct H13 as [X | X]; [elim X; eexists; eexists; split; eauto; rewrite H10; eauto|rewrite H9 in X; elim X; eauto].
    - rewrite H4 in H6; inv H6.
      destruct (is_call_determ _ _ _ _ _ _ _ _ H8 H11) as [<- <-].
      rewrite H10 in H13; inv H13; auto.
  Qed.

  Inductive val: Type :=
  | HaltedV: val
  | FailedV: val
  | NextIV: val.

  Inductive expr: Type :=
  | Instr (c : ConfFlag)
  | Seq (e : expr).
  Definition state : Type := ExecConf.

  Definition of_val (v: val): expr :=
    match v with
    | HaltedV => Instr Halted
    | FailedV => Instr Failed
    | NextIV => Instr NextI
    end.

  Definition to_val (e: expr): option val :=
    match e with
    | Instr c =>
      match c with
      | Executable => None
      | Halted => Some HaltedV
      | Failed => Some FailedV
      | NextI => Some NextIV
      end
    | Seq _ => None
    end.

  Lemma of_to_val:
    forall e v, to_val e = Some v →
           of_val v = e.
  Proof.
    intros * HH. destruct e; try destruct c; simpl in HH; inv HH; auto.
  Qed.

  Lemma to_of_val:
    forall v, to_val (of_val v) = Some v.
  Proof. destruct v; reflexivity. Qed.

  (** Evaluation context *)
  Inductive ectx_item :=
  | SeqCtx.

  Notation ectx := (list ectx_item).

  Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
    match Ki with
    | SeqCtx => Seq e
    end.

  Inductive prim_step: expr → state → list Empty_set → expr → state → list expr → Prop :=
  | PS_no_fork_instr σ e' σ' :
      step (Executable, σ) (e', σ') → prim_step (Instr Executable) σ [] (Instr e') σ' []
  | PS_no_fork_seq σ : prim_step (Seq (Instr NextI)) σ [] (Seq (Instr Executable)) σ []
  | PS_no_fork_halt σ : prim_step (Seq (Instr Halted)) σ [] (Instr Halted) σ []
  | PS_no_fork_fail σ : prim_step (Seq (Instr Failed)) σ [] (Instr Failed) σ [].

  Lemma val_stuck:
    forall e σ o e' σ' efs,
      prim_step e σ o e' σ' efs →
      to_val e = None.
  Proof. intros * HH. by inversion HH. Qed.

  Lemma prim_step_exec_inv σ1 l1 e2 σ2 efs :
    prim_step (Instr Executable) σ1 l1 e2 σ2 efs →
    l1 = [] ∧ efs = [] ∧
    exists (c: ConfFlag),
      e2 = Instr c ∧
      step (Executable, σ1) (c, σ2).
  Proof. inversion 1; subst; split; eauto. Qed.

  Lemma prim_step_and_step_exec σ1 e2 σ2 l1 e2' σ2' efs :
    step (Executable, σ1) (e2, σ2) →
    prim_step (Instr Executable) σ1 l1 e2' σ2' efs →
    l1 = [] ∧ e2' = (Instr e2) ∧ σ2' = σ2 ∧ efs = [].
  Proof.
    intros* Hstep Hpstep. inversion Hpstep as [? ? ? Hstep' | | |]; subst.
    generalize (step_deterministic _ _ _ _ _ _ Hstep Hstep'). intros [-> ->].
    auto.
  Qed.

  Lemma overlay_lang_determ e1 σ1 κ κ' e2 e2' σ2 σ2' efs efs' :
    prim_step e1 σ1 κ e2 σ2 efs →
    prim_step e1 σ1 κ' e2' σ2' efs' →
    κ = κ' ∧ e2 = e2' ∧ σ2 = σ2' ∧ efs = efs'.
  Proof.
    intros Hs1 Hs2. inv Hs1; inv Hs2. all: auto.
    generalize (step_deterministic _ _ _ _ _ _ H0 H1).
    intros [? ?]; subst. auto.
  Qed.

  Lemma fill_item_val Ki e :
    is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
  Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

  Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
  Proof. destruct Ki; intros ???; simplify_eq; auto with f_equal. Qed.

  Lemma head_ctx_step_val Ki e σ1 κ e2 σ2 ef :
    prim_step (fill_item Ki e) σ1 κ e2 σ2 ef → is_Some (to_val e).
  Proof. destruct Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

  Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    to_val e1 = None → to_val e2 = None →
    fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
  Proof.
    destruct Ki1, Ki2; intros; try discriminate; simplify_eq;
    repeat match goal with
           | HH : to_val (of_val _) = None |- _ => by rewrite to_of_val in HH
           end; auto.
  Qed.

  Lemma overlay_lang_mixin : EctxiLanguageMixin of_val to_val fill_item prim_step.
  Proof.
    constructor;
    apply _ || eauto using to_of_val, of_to_val, val_stuck,
           fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
  Qed.

  Definition is_atomic (e : expr) : Prop :=
    match e with
    | Instr _ => True
    | _ => False
    end.

  Lemma updatePC_atomic φ :
    ∃ φ', updatePC φ = (Failed,φ') ∨ (updatePC φ = (NextI,φ')) ∨
          (updatePC φ = (Halted,φ')).
  Proof.
    rewrite /updatePC; repeat case_match; eauto.
  Qed.

  Lemma instr_atomic i φ :
    ∃ φ', (exec i φ = (Failed, φ')) ∨ (exec i φ = (NextI, φ')) ∨
          (exec i φ = (Halted, φ')).
  Proof.
    unfold exec; repeat case_match; eauto; try (eapply updatePC_atomic; eauto).
  Qed.

End opsem.

Canonical Structure overlay_ectxi_lang `{MachineParameters} := EctxiLanguage overlay_lang_mixin.
Canonical Structure overlay_ectx_lang `{MachineParameters} := EctxLanguageOfEctxi overlay_ectxi_lang.
Canonical Structure overlay_lang `{MachineParameters} := LanguageOfEctx overlay_ectx_lang.

Hint Extern 20 (PureExec _ _ _) => progress simpl : typeclass_instances.

Hint Extern 5 (IntoVal _ _) => eapply of_to_val; fast_done : typeclass_instances.
Hint Extern 10 (IntoVal _ _) =>
  rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

Hint Extern 5 (AsVal _) => eexists; eapply of_to_val; fast_done : typeclass_instances.
Hint Extern 10 (AsVal _) =>
eexists; rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

Local Hint Resolve language.val_irreducible.
Local Hint Resolve to_of_val.
Local Hint Unfold language.irreducible.

Global Instance dec_pc c : Decision (isCorrectPC c).
Proof. apply isCorrectPC_dec. Qed.

(* There is probably a more general instance to be stated there...*)
Instance Reflexive_ofe_equiv_Word : (Reflexive (ofe_equiv (leibnizO base.Word))).
Proof. intro; reflexivity. Qed.

(****)

Lemma updatePC_not_executable `{MachineParameters}:
  forall φ,
    (updatePC φ).1 <> Executable.
Proof.
  intros; unfold updatePC.
  repeat match goal with
           |- context [match ?X with | _ => _ end] => destruct X
         end; simpl; auto.
Qed.

Lemma exec_not_executable `{MachineParameters}:
  forall i φ,
    (exec i φ).1 <> Executable.
Proof.
  intros. destruct i; simpl; auto;
            repeat match goal with
                     |- context [match ?X with | _ => _ end] => destruct X
                   end; simpl; auto; apply updatePC_not_executable.
Qed.

Lemma exec_call_not_executable `{MachineParameters}:
  forall σ rf rargs p g b e a,
    (exec_call σ rf rargs p g b e a).1 <> Executable.
Proof.
  intros. rewrite /exec_call.
  repeat match goal with
           |- context [match ?X with | _ => _ end] => destruct X
  end; simpl; auto.
Qed.

Global Instance is_atomic_correct `{MachineParameters} s (e : expr) : is_atomic e → Atomic s e.
Proof.
  intros Ha; apply strongly_atomic_atomic, ectx_language_atomic.
  - destruct e.
    + destruct c; rewrite /Atomic; intros ????? Hstep;
        inversion Hstep.
      match goal with HH : step _ _ |- _ => inversion HH end; subst; simpl; eauto.
      * case_eq (exec (decodeInstrW' (mem σ !m! a)) σ); intros.
        destruct c; eauto.
        generalize (exec_not_executable (decodeInstrW' (mem σ !m! a)) σ).
        rewrite H1. simpl; congruence.
      * case_eq (exec (decodeInstrW' (m !m! a)) σ); intros.
        destruct c; eauto.
        generalize (exec_not_executable (decodeInstrW' (m !m! a)) σ).
        rewrite H1. simpl; congruence.
    + inversion Ha.
  - intros K e' -> Hval%eq_None_not_Some.
    induction K using rev_ind; first done.
    simpl in Ha; rewrite fill_app in Ha; simpl in Ha.
    destruct Hval. apply (fill_val K e'); simpl in *.
    destruct x; naive_solver.
Qed.

Ltac solve_atomic :=
  apply is_atomic_correct; simpl; repeat split;
    rewrite ?to_of_val; eapply mk_is_Some; fast_done.

Hint Extern 0 (Atomic _ _) => solve_atomic.
Hint Extern 0 (Atomic _ _) => solve_atomic : typeclass_instances.

Lemma head_reducible_from_step `{MachineParameters} σ1 e2 σ2 :
  step (Executable, σ1) (e2, σ2) →
  head_reducible (Instr Executable) σ1.
Proof. intros * HH. rewrite /head_reducible /head_step //=.
       eexists [], (Instr _), σ2, []. by constructor.
Qed.

Lemma normal_always_head_reducible `{MachineParameters} σ :
  head_reducible (Instr Executable) σ.
Proof.
  generalize (normal_always_step σ); intros (?&?&?).
  eapply head_reducible_from_step. eauto.
Qed.

Definition overlay_component: Type := component nat _ _ overlay.base.Word.

Definition initial_state `{MachineParameters} (b_stk e_stk: Addr) (c: overlay_component): cfg overlay_lang :=
  match c with
  | Lib _ _ _ _ pre_comp => ([Seq (Instr Executable)], (∅, ∅, ∅, [])) (* dummy value *)
  | Main _ _ _ _ (ms, _, _) c_main => ([Seq (Instr Executable)], (<[r_stk := inr (Stk 0 URWLX b_stk e_stk b_stk)]> (<[PC := c_main]> (gset_to_gmap (inl 0%Z) (list_to_set all_registers))), ms, ∅, []))
  end.

Definition can_address_only (w: base.Word) (addrs: gset Addr): Prop :=
  match w with
  | inl _ => True
  | inr (Regular (_, _, b, e, _)) =>
    forall a, (b <= a < e)%a -> a ∈ addrs
  | _ => False
  end.

Definition pwlW (w: base.Word): bool :=
  match w with
  | inl _ => false
  | inr (Regular (p, _, _, _, _)) => pwlU p
  | inr (Stk _ p _ _ _) => pwlU p
  | inr (Ret _ _ _) => false
  end.

Definition is_global (w: base.Word): bool :=
  match w with
  | inl _ => true
  | inr (Regular (_, l, _, _, _)) =>
    match l with
    | Global => true
    | _ => false
    end
  | inr _ => false
  end.
