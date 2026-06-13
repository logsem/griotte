From griotte Require Export stdpp_extra.
From griotte Require Export machine_base machine_parameters machine_instructions.

Definition ExecConf := (Reg * SReg * Mem)%type.

Inductive ConfFlag : Type :=
| Executable
| Halted
| Failed
| NextI.

Definition Conf: Type := ConfFlag * ExecConf.

Definition reg (ϕ: ExecConf) := (fst (fst ϕ)).
Definition sreg (ϕ: ExecConf) := (snd (fst ϕ)).
Definition mem (ϕ: ExecConf) := snd ϕ.

Definition update_reg (φ: ExecConf) (r: RegName) (w: Word): ExecConf :=
  (<[r:=w]ᵣ>(reg φ), sreg φ, mem φ).
Definition update_sreg (φ: ExecConf) (sr: SRegName) (w: Word): ExecConf :=
  (reg φ, <[sr:=w]>(sreg φ), mem φ).
Definition update_mem (φ: ExecConf) (a: Addr) (w: Word): ExecConf :=
  (reg φ, sreg φ, <[a:=w]>(mem φ)).


(* Note that the `None` values here also undo any previous changes that were tentatively made in the same step. This is more consistent across the board. *)
Definition updatePC_gen (φ: ExecConf) (imm : Z): option Conf :=
  match (reg φ) !! PC with
  | Some (WCap p g b e a) =>
    match (a + imm)%a with
    | Some a' => let φ' := (update_reg φ PC (WCap p g b e a')) in
                Some (NextI, φ')
    | None => None
    end
  | _ => None
  end.

Definition updatePC (φ: ExecConf): option Conf := updatePC_gen φ 1.


Definition z_of_argument (regs: Reg) (a: Z + RegName) : option Z :=
  match a with
  | inl z => Some z
  | inr r =>
    match regs !!ᵣ r with
    | Some (WInt z) => Some z
    | _ => None
    end
  end.

Definition word_of_argument (regs: Reg) (a: Z + RegName): option Word :=
  match a with
  | inl n => Some (WInt n)
  | inr r => regs !!ᵣ r
  end.

Definition addr_of_argument regs src :=
  match z_of_argument regs src with
  | Some n => z_to_addr n
  | None => None
  end.

Definition otype_of_argument regs src : option OType :=
  match z_of_argument regs src with
  | Some n => (z_to_otype n) : option OType
  | None => None : option OType
  end.

Section opsem.
  Context `{MachineParameters}.

  Definition exec_opt (i: instr) (plevel : Perm) (φ: ExecConf): option Conf :=
    match i with
    | Fail => Some (Failed, φ)
    | Halt => Some (Halted, φ)
    | Jmp rimm =>
        imm ← z_of_argument (reg φ) rimm;
        updatePC_gen φ imm
    | Jnz rimm rcond =>
        wcond ← (reg φ) !!ᵣ rcond;
        if nonZero wcond
        then imm ← z_of_argument (reg φ) rimm;
             updatePC_gen φ imm
        else updatePC φ
    | Jalr rdst rsrc =>
        (* Note: allow jumping to integers, sealing ranges etc; machine will crash later *)
        wrsrc ← (reg φ) !!ᵣ rsrc;
        wpc ← (reg φ) !! PC;
        match wpc with
        | (WCap p g b e a) =>
            match (a + 1)%a with
            | Some a' =>
                let φ_next := (update_reg φ PC (updatePcPerm wrsrc)) in
                let φ_dst := (update_reg φ_next rdst (WSentry p g b e a')) in
                Some (NextI, φ_dst)
            | None => None
            end
        | _ => None
        end
    | Load dst src =>
      wsrc ← (reg φ) !!ᵣ src;
      match wsrc with
      | WCap p g b e a =>
        if readAllowed p && withinBounds b e a then
          asrc ← (mem φ) !! a;
          updatePC (update_reg φ dst (load_word p asrc))
        else None
      | _ => None
      end
    | Store dst ρ =>
      tostore ← word_of_argument (reg φ) ρ;
      wdst ← (reg φ) !!ᵣ dst;
      match wdst with
      | WCap p g b e a =>
        if writeAllowed p && withinBounds b e a && canStore p tostore then
          updatePC (update_mem φ a tostore)
        else None
      | _ => None
      end
    | Mov dst ρ =>
      tomov ← word_of_argument (reg φ) ρ;
      updatePC (update_reg φ dst tomov)
    | Lea dst ρ =>
      n ← z_of_argument (reg φ) ρ;
      wdst ← (reg φ) !!ᵣ dst;
      match wdst with
      | WCap p g b e a =>
          match (a + n)%a with
          | Some a' => updatePC (update_reg φ dst (WCap p g b e a'))
          | None => None
          end
      | WSealRange p g b e a =>
         match (a + n)%ot with
          | Some a' => updatePC (update_reg φ dst (WSealRange p g b e a'))
          | None => None
          end
      | _ => None
      end
    | Restrict dst ρ =>
      n ← z_of_argument (reg φ) ρ ;
      wdst ← (reg φ) !!ᵣ dst;
      match wdst with
      | WCap p g b e a =>
          let (p',g') := decodePermPair n in
          if PermFlowsTo p' p && LocalityFlowsTo g' g then
            updatePC (update_reg φ dst (WCap p' g' b e a))
          else None
      | WSealRange p g b e a =>
            let (p',g') := decodeSealPermPair n in
            if SealPermFlowsTo p' p && LocalityFlowsTo g' g  then
              updatePC (update_reg φ dst (WSealRange p' g' b e a))
            else None
      | _ => None
      end
    | machine_instructions.Add dst ρ1 ρ2 =>
    n1 ← z_of_argument (reg φ) ρ1;
    n2 ← z_of_argument (reg φ) ρ2;
    updatePC (update_reg φ dst (WInt (n1 + n2)%Z))
    | Sub dst ρ1 ρ2 =>
    n1 ← z_of_argument (reg φ) ρ1;
    n2 ← z_of_argument (reg φ) ρ2;
    updatePC (update_reg φ dst (WInt (n1 - n2)%Z))
    | Mul dst ρ1 ρ2 =>
    n1 ← z_of_argument (reg φ) ρ1;
    n2 ← z_of_argument (reg φ) ρ2;
    updatePC (update_reg φ dst (WInt (n1 * n2)%Z))
    | LAnd dst ρ1 ρ2 =>
    n1 ← z_of_argument (reg φ) ρ1;
    n2 ← z_of_argument (reg φ) ρ2;
    updatePC (update_reg φ dst (WInt (Z.land n1 n2)))
    | LOr dst ρ1 ρ2 =>
    n1 ← z_of_argument (reg φ) ρ1;
    n2 ← z_of_argument (reg φ) ρ2;
    updatePC (update_reg φ dst (WInt (Z.lor n1 n2)))
    | LShiftL dst ρ1 ρ2 =>
    n1 ← z_of_argument (reg φ) ρ1;
    n2 ← z_of_argument (reg φ) ρ2;
    updatePC (update_reg φ dst (WInt (n1 ≪ n2)%Z))
    | LShiftR dst ρ1 ρ2 =>
    n1 ← z_of_argument (reg φ) ρ1;
    n2 ← z_of_argument (reg φ) ρ2;
    updatePC (update_reg φ dst (WInt (n1 ≫ n2)%Z))
    | Lt dst ρ1 ρ2 =>
    n1 ← z_of_argument (reg φ) ρ1;
    n2 ← z_of_argument (reg φ) ρ2;
    updatePC (update_reg φ dst (WInt (Z.b2z (Z.ltb n1 n2))))
  | Subseg dst ρ1 ρ2 =>
    wdst ← (reg φ) !!ᵣ dst;
    match wdst with
    | WCap p g b e a =>
      a1 ← addr_of_argument (reg φ) ρ1;
      a2 ← addr_of_argument (reg φ) ρ2;
      if isWithin a1 a2 b e then
        updatePC (update_reg φ dst (WCap p g a1 a2 a))
      else None
    | WSealRange p g b e a =>
      o1 ← otype_of_argument (reg φ) ρ1;
      o2 ← otype_of_argument (reg φ) ρ2;
      if isWithin o1 o2 b e then
        updatePC (update_reg φ dst (WSealRange p g o1 o2 a))
      else None
    | _ => None
    end
  | GetA dst r =>
    wr ← (reg φ) !!ᵣ r;
    match wr with
    | WCap _ _ _ _ a
    | WSentry _ _ _ _ a
    | WSealRange _ _ _ _ a => updatePC (update_reg φ dst (WInt a))
    | _ => None
    end
  | GetB dst r =>
    wr ← (reg φ) !!ᵣ r;
    match wr with
    | WCap _ _ b _ _
    | WSentry _ _ b _ _
    | WSealRange _ _ b _ _ => updatePC (update_reg φ dst (WInt b))
    | _ => None
    end
  | GetE dst r =>
    wr ← (reg φ) !!ᵣ r;
    match wr with
    | WCap _ _ _ e _
    | WSentry _ _ _ e _
    | WSealRange _ _ _ e _ => updatePC (update_reg φ dst (WInt e))
    | _ => None
    end
  | GetP dst r =>
    wr ← (reg φ) !!ᵣ r;
    match wr with
    | WCap p _ _ _ _
    | WSentry p _ _ _ _ => updatePC (update_reg φ dst (WInt (encodePerm p)))
    | WSealRange p _ _ _ _ => updatePC (update_reg φ dst (WInt (encodeSealPerms p)))
    | _ => None
    end
  | GetL dst r =>
    wr ← (reg φ) !!ᵣ r;
    match wr with
    | WCap _ l _ _ _
    | WSentry _ l _ _ _
    | WSealRange _ l _ _ _ => updatePC (update_reg φ dst (WInt (encodeLoc l)))
    | _ => None
    end

  | GetOType dst r =>
    wr ← (reg φ) !!ᵣ r;
    match wr with
    | WSealed o _ => updatePC (update_reg φ dst (WInt o))
    (* NOTE if not a sealed, return -1 in any other case ? What if not a sealable ? *)
    | _ => updatePC (update_reg φ dst (WInt (-1)))
    end

  | GetWType dst r =>
    wr ← (reg φ) !!ᵣ r; updatePC (update_reg φ dst (WInt (encodeWordType wr)))

  | Seal dst r1 r2 =>
    wr1 ← (reg φ) !!ᵣ r1;
    wr2 ← (reg φ) !!ᵣ r2;
    match wr1,wr2 with
    | WSealRange p g b e a, WSealable sb =>
      if permit_seal p && withinBounds b e a then updatePC (update_reg φ dst (WSealed a sb))
      else None
    | _, _ => None
    end
  | UnSeal dst r1 r2 =>
    wr1 ← (reg φ) !!ᵣ r1;
    wr2 ← (reg φ) !!ᵣ r2;
    match wr1, wr2 with
    | WSealRange p g b e a, WSealed a' sb =>
        if decide (permit_unseal p = true ∧ withinBounds b e a = true ∧ a' = a) then updatePC (update_reg φ dst (WSealable sb))
        else None
    | _,_ => None
    end
  | ReadSR dst src =>
      if has_sreg_access plevel
      then tomov ← (sreg φ) !! src; updatePC (update_reg φ dst tomov)
      else None
  | WriteSR dst src =>
      if has_sreg_access plevel
      then tomov ← (reg φ) !!ᵣ src; updatePC (update_sreg φ dst tomov)
      else None
  end.

  Definition exec (i: instr) (plevel : Perm) (φ: ExecConf) : Conf :=
     match exec_opt i plevel φ with | None => (Failed, φ) | Some conf => conf end .

  Lemma exec_opt_exec_some :
    forall φ i plevel c,
      exec_opt i plevel φ = Some c →
      exec i plevel φ = c.
  Proof. unfold exec. by intros * ->. Qed.

  Lemma exec_opt_exec_none :
    forall φ i plevel,
      exec_opt i plevel φ = None →
      exec i plevel φ = (Failed, φ).
  Proof. unfold exec. by intros * ->. Qed.

  Inductive step: Conf → Conf → Prop :=
  | step_exec_regfail:
      forall φ,
        (reg φ) !! PC = None →
        step (Executable, φ) (Failed, φ)
  | step_exec_corrfail:
      forall φ wreg,
        (reg φ) !! PC = Some wreg →
        not (isCorrectPC wreg) →
        step (Executable, φ) (Failed, φ)
  | step_exec_memfail:
      forall φ p g b e a,
        (reg φ) !! PC = Some (WCap p g b e a) →
        (mem φ) !! a = None →
        step (Executable, φ) (Failed, φ)
  | step_exec_instr:
      forall φ p g b e a i c wa,
        (reg φ) !! PC = Some (WCap p g b e a) → (* only works for caps *)
        (mem φ) !! a = Some wa →
        isCorrectPC (WCap p g b e a) →
        decodeInstrW wa = i →
        exec i p φ = c →
        step (Executable, φ) (c.1, c.2).

End opsem.
