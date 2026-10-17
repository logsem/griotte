From griotte Require Export stdpp_extra machine_utils_extra.
From griotte Require Export machine_base machine_parameters machine_instructions.

(* The machine configuration: the PC, the general registers, the system
   registers, the memory and the shadow table. *)
Definition ExecConf := (Word * Reg * SReg * Mem * ShadowTbl)%type.

Inductive ConfFlag : Type :=
| Executable
| Halted
| Failed
| NextI.

Definition Conf: Type := ConfFlag * ExecConf.

Definition pcc (ϕ: ExecConf) := (fst (fst (fst (fst ϕ)))).
Definition reg (ϕ: ExecConf) := (snd (fst (fst (fst ϕ)))).
Definition sreg (ϕ: ExecConf) := (snd (fst (fst ϕ))).
Definition mem (ϕ: ExecConf) := (snd (fst ϕ)).
Definition shadowtbl (ϕ: ExecConf) := snd ϕ.

Definition update_pcc (φ: ExecConf) (w: Word): ExecConf :=
  (w, reg φ, sreg φ, mem φ, shadowtbl φ).
Definition update_reg (φ: ExecConf) (r: RegName) (w: Word): ExecConf :=
  (pcc φ, <[r:=w]ᵣ>(reg φ), sreg φ, mem φ, shadowtbl φ).
Definition update_sreg (φ: ExecConf) (sr: SRegName) (w: Word): ExecConf :=
  (pcc φ, reg φ, <[sr:=w]>(sreg φ), mem φ, shadowtbl φ).
Definition update_mem (φ: ExecConf) (a: Addr) (w: Word): ExecConf :=
  (pcc φ, reg φ, sreg φ, <[a:=w]>(mem φ), shadowtbl φ).
Definition update_shadowtbl (φ: ExecConf) (a: Addr) (s: AllocStatus): ExecConf :=
  (pcc φ, reg φ, sreg φ, mem φ, <[a:=s]> (shadowtbl φ)).

(* Note that the `None` values here also undo any previous changes that were tentatively made in the same step. This is more consistent across the board. *)
Definition updatePC_gen (φ: ExecConf) (imm : Z): option Conf :=
  match pcc φ with
  | WCap t p g b e a =>
    match (a + imm)%a with
    | Some a' => let φ' := (update_pcc φ (WCap t p g b e a')) in
                Some (NextI, φ')
    | None => None
    end
  | _ => None
  end.

Definition updatePC (φ: ExecConf): option Conf := updatePC_gen φ 1.


(* An integer operand reads the address of a register word, as in
   cheriot-sail. *)
Definition z_of_argument (regs: Reg) (a: Z + RegName) : option Z :=
  match a with
  | inl z => Some z
  | inr r =>
    match regs !!ᵣ r with
    | Some w => Some (get_a w)
    | None => None
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

(** * System registers *)

Definition interrupt_status_bit (b : InterruptStatus) : bool :=
  match b with InterruptEnabled => true | InterruptDisabled => false end.

Definition interrupt_status_of_bit (bit : bool) : InterruptStatus :=
  if bit then InterruptEnabled else InterruptDisabled.

(** mstatus holds MIE and MPIE; its other bits read as 0. *)
Definition mstatus_enc (mie mpie : InterruptStatus) : Z :=
  (Z.shiftl (Z.b2z (interrupt_status_bit mie)) MIE_BIT +
   Z.shiftl (Z.b2z (interrupt_status_bit mpie)) MPIE_BIT)%Z.

Definition mie_of (z : Z) : InterruptStatus := interrupt_status_of_bit (Z.testbit z MIE_BIT).
Definition mpie_of (z : Z) : InterruptStatus := interrupt_status_of_bit (Z.testbit z MPIE_BIT).

Lemma mie_of_mstatus_enc mie mpie : mie_of (mstatus_enc mie mpie) = mie.
Proof. by destruct mie, mpie. Qed.

Lemma mpie_of_mstatus_enc mie mpie : mpie_of (mstatus_enc mie mpie) = mpie.
Proof. by destruct mie, mpie. Qed.

Lemma mstatus_enc_inj mie mpie mie' mpie' :
  mstatus_enc mie mpie = mstatus_enc mie' mpie' → mie = mie' ∧ mpie = mpie'.
Proof. by destruct mie, mpie, mie', mpie'. Qed.

(** The link Jalr writes to [rdst], for the return address [a] in the PC
    [WCap t p g b e _]: a return sentry when [rdst] is [cra], whose kind
    restores the interrupt status [mie] of the caller, and otherwise the
    unsealed capability. *)
Definition jalr_link (rdst : RegName) (mie : InterruptStatus)
    (t : bool) (p : Perm) (g : Locality) (b e a : Addr) : Word :=
  if decide (rdst = cra) then WSentry (ret_kind mie) t p g b e a else WCap t p g b e a.

(** mstatus after a jump to [w], from its value [z] before the jump: a
    sentry that sets the interrupt status sets MIE, MPIE is unchanged. *)
Definition jalr_mstatus (w : Word) (z : Z) : option Z :=
  (λ mie, mstatus_enc mie (mpie_of z)) <$> jalr_target_mie w.

(** A write to MTCC or MEPCC clears the tag of a word that is sealed (a
    sentry included) or not executable, as cheriot-sail's [CSpecialRW]. Word
    addresses have no alignment constraint. *)
Definition legalise_pc (w : Word) : Word :=
  if is_sealb w && executable_word w then w else clear_tag w.

(** The value a system register stores when [w] is written to it: MTCC and
    MEPCC are legalised, MTDC stores [w], and the CSRs store the integer view
    of [w], mstatus keeping only its MIE and MPIE bits. *)
Definition legalise (sr : SRegName) (w : Word) : Word :=
  match sr with
  | MTCC | MEPCC => legalise_pc w
  | MTDC => w
  | MSTATUS => WInt (mstatus_enc (mie_of (get_a w)) (mpie_of (get_a w)))
  | MCAUSE | MTVAL => WInt (get_a w)
  end.

(** The system registers that hold a PC: [mret] and trap entry jump to them
    without checks. *)
Definition is_pc_sreg (sr : SRegName) : bool :=
  match sr with MTCC | MEPCC => true | _ => false end.

Lemma legalise_pc_pc_ok w : pc_ok (legalise_pc w).
Proof.
  rewrite /legalise_pc /pc_ok.
  destruct (is_sealb w) eqn:Hs, (executable_word w) eqn:Hx; cbn;
    rewrite ?get_tag_clear_tag; naive_solver.
Qed.

Lemma legalise_mtcc_pc_ok w : pc_ok (legalise MTCC w).
Proof. apply legalise_pc_pc_ok. Qed.

Lemma legalise_mepcc_pc_ok w : pc_ok (legalise MEPCC w).
Proof. apply legalise_pc_pc_ok. Qed.

Lemma legalise_pc_sreg_pc_ok sr w : is_pc_sreg sr = true → pc_ok (legalise sr w).
Proof. destruct sr; try done; intros _; apply legalise_pc_pc_ok. Qed.

Lemma legalise_pc_ok_id w : pc_ok w → legalise_pc w = w.
Proof.
  rewrite /legalise_pc /pc_ok. intros Hok.
  destruct (get_tag w) eqn:Ht.
  - by destruct (Hok eq_refl) as [-> ->].
  - destruct (is_sealb w && executable_word w); first done.
    destruct w as [| [] | | ? []]; cbn in *; by subst.
Qed.

Lemma legalise_mstatus w :
  legalise MSTATUS w = WInt (mstatus_enc (mie_of (get_a w)) (mpie_of (get_a w))).
Proof. done. Qed.

Lemma legalise_mstatus_enc mie mpie :
  legalise MSTATUS (WInt (mstatus_enc mie mpie)) = WInt (mstatus_enc mie mpie).
Proof. by rewrite legalise_mstatus /= mie_of_mstatus_enc mpie_of_mstatus_enc. Qed.

Lemma legalise_clear_tag sr w : legalise sr (clear_tag w) = clear_tag (legalise sr w).
Proof.
  destruct sr; cbn; rewrite ?get_a_clear_tag //.
  all: rewrite /legalise_pc; destruct w as [| [] | | ? []]; cbn; by repeat case_match.
Qed.

Lemma legalise_idemp sr w : legalise sr (legalise sr w) = legalise sr w.
Proof.
  destruct sr; cbn; try done.
  1,2: rewrite /legalise_pc; destruct w as [| [] | | ? []]; cbn;
       repeat case_match; cbn in *; congruence.
  by rewrite mie_of_mstatus_enc mpie_of_mstatus_enc.
Qed.

Section opsem.
  Context `{MachineParameters}.
  Definition get_shadow_address (a : Addr) : Addr := a.

  (** The revoker's atomic sweep clears the tag of exactly the words that the
      CLoad filter strips: those whose heap base is quarantined. *)
  Definition sweep_word (shadow : ShadowTbl) (w : Word) : Word :=
    match heap_cap_base w with
    | Some base =>
        match shadow !! base with
        | Some ShadowQuarantined => clear_tag w
        | _ => w
        end
    | None => w
    end.

  Definition sweep_mem (shadow : ShadowTbl) (m : Mem) : Mem :=
    sweep_word shadow <$> m.

  Definition revoker_sweep (φ : ExecConf) : ExecConf :=
    (pcc φ, reg φ, sreg φ, sweep_mem (shadowtbl φ) (mem φ), shadowtbl φ).

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
        wrsrc ← (reg φ) !!ᵣ rsrc;
        (* The checks on the target, in the order of cheriot-sail: the tag,
           the sealing by the form of the instruction, the execute
           permission. A failed check writes neither the PC, nor the link
           register, nor mstatus. *)
        if negb (get_tag wrsrc) then None
        else if negb (jalr_sealing_ok rdst rsrc wrsrc) then None
        else if negb (executable_word wrsrc) then None
        else
        wst ← (sreg φ) !! MSTATUS;
        match pcc φ with
        | (WCap t p g b e a) =>
            match (a + 1)%a with
            | Some a' =>
                let φ_next := (update_pcc φ (updatePcPerm wrsrc)) in
                (* A [cnull] destination drops the link; the link's kind is
                   taken from MIE before the jump. *)
                let φ_dst :=
                  if decide (rdst = cnull) then φ_next
                  else update_reg φ_next rdst
                         (jalr_link rdst (mie_of (get_a wst)) t p g b e a') in
                (* A sentry that sets the interrupt status writes MIE. *)
                let φ_st :=
                  match jalr_mstatus wrsrc (get_a wst) with
                  | Some z => update_sreg φ_dst MSTATUS (WInt z)
                  | None => φ_dst
                  end in
                Some (NextI, φ_st)
            | None => None
            end
        | _ => None
        end
    | CLoad dst src imm =>
      wsrc ← (reg φ) !!ᵣ src;
      match wsrc with
      | WCap true p g b e a =>
        ea ← (a + imm)%a;
        if readAllowed p && withinBounds b e ea then
          if (is_shadow_address ea)
          then
            heap_a ← shadow_to_heap ea;
            status ← (shadowtbl φ) !! heap_a;
            updatePC (update_reg φ dst (WInt (encodeAllocStatus status)))
          else if (is_revoker_address ea)
          then
            (* The revoker reads as zero. *)
            updatePC (update_reg φ dst (WInt 0))
          else
            asrc ← (mem φ) !! ea;
            match heap_cap_base asrc with
            | Some base =>
                status ← (shadowtbl φ) !! base;
                let loaded_word :=
                  match status with
                  | ShadowLive => load_word p asrc
                  | ShadowQuarantined => clear_tag (load_word p asrc)
                  end
                in
                updatePC (update_reg φ dst loaded_word)
            | _ => updatePC (update_reg φ dst (load_word p asrc))
            end
        else None
      | _ => None
      end
    | Store dst ρ imm =>
      tostore ← word_of_argument (reg φ) ρ;
      wdst ← (reg φ) !!ᵣ dst;
      match wdst with
      | WCap true p g b e a =>
        ea ← (a + imm)%a;
        if writeAllowed p && withinBounds b e ea then
          if (is_shadow_address ea)
          then
            heap_a ← shadow_to_heap ea;
            (* Integer stores decode to an allocation status. *)
            match tostore with
            | WInt z => updatePC (update_shadowtbl φ heap_a (decodeAllocStatus z))
            | _ => None
            end
          else if (is_revoker_address ea)
          then
            (* Any store to the revoker sweeps memory; the value is ignored. *)
            updatePC (revoker_sweep φ)
          else
            updatePC (update_mem φ ea (store_word p tostore))
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
      | WCap t p g b e a =>
          match (a + n)%a with
          | Some a' => updatePC (update_reg φ dst (WCap t p g b e a'))
          | None => updatePC (update_reg φ dst (WCap false p g b e a))
          end
      | WSealRange t p g b e a =>
         match (a + n)%ot with
          | Some a' => updatePC (update_reg φ dst (WSealRange t p g b e a'))
          | None => updatePC (update_reg φ dst (WSealRange false p g b e a))
          end
      | WInt z => updatePC (update_reg φ dst (WInt (z + n)%Z))
      (* A sealed word or a sentry loses its tag; its address is unchanged. *)
      | _ => updatePC (update_reg φ dst (clear_tag wdst))
      end
    | Restrict dst ρ =>
      n ← z_of_argument (reg φ) ρ ;
      wdst ← (reg φ) !!ᵣ dst;
      match wdst with
      | WCap t p g b e a =>
          let (p',g') := decodePermPair n in
          let new_tag := t && PermFlowsTo p' p && LocalityFlowsTo g' g in
          updatePC (update_reg φ dst (WCap new_tag p' g' b e a))
      | WSealRange t p g b e a =>
          let (p',g') := decodeSealPermPair n in
          let new_tag := t && SealPermFlowsTo p' p && LocalityFlowsTo g' g in
          updatePC (update_reg φ dst (WSealRange new_tag p' g' b e a))
      (* An integer is unchanged; a sealed word or a sentry loses its tag,
         its permissions unchanged. *)
      | _ => updatePC (update_reg φ dst (clear_tag wdst))
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
    | WCap t p g b e a =>
      n1 ← z_of_argument (reg φ) ρ1;
      n2 ← z_of_argument (reg φ) ρ2;
      match z_to_addr n1, z_to_addr n2 with
      | Some a1, Some a2 =>
        let new_tag := t && isWithin a1 a2 b e && (a1 <=? a2)%a in
        updatePC (update_reg φ dst (WCap new_tag p g a1 a2 a))
      | _, _ => updatePC (update_reg φ dst (WCap false p g b e a))
      end
    | WSealRange t p g b e a =>
      n1 ← z_of_argument (reg φ) ρ1;
      n2 ← z_of_argument (reg φ) ρ2;
      match z_to_otype n1, z_to_otype n2 with
      | Some o1, Some o2 =>
        let new_tag := t && isWithin o1 o2 b e in
        updatePC (update_reg φ dst (WSealRange new_tag p g o1 o2 a))
      | _, _ => updatePC (update_reg φ dst (WSealRange false p g b e a))
      end
    (* An integer is unchanged; a sealed word or a sentry loses its tag, its
       bounds unchanged. *)
    | _ => updatePC (update_reg φ dst (clear_tag wdst))
    end
  | GetA dst r =>
    wr ← (reg φ) !!ᵣ r;
    updatePC (update_reg φ dst (WInt (get_a wr)))
  | GetB dst r =>
    wr ← (reg φ) !!ᵣ r;
    updatePC (update_reg φ dst (WInt (get_b wr)))
  | GetE dst r =>
    wr ← (reg φ) !!ᵣ r;
    updatePC (update_reg φ dst (WInt (get_e wr)))
  | GetP dst r =>
    wr ← (reg φ) !!ᵣ r;
    updatePC (update_reg φ dst (WInt (encodePermSum (get_p wr))))
  | GetL dst r =>
    wr ← (reg φ) !!ᵣ r;
    updatePC (update_reg φ dst (WInt (encodeLoc (get_l wr))))

  | GetOType dst r =>
    wr ← (reg φ) !!ᵣ r;
    match wr with
    | WSealed o _ => updatePC (update_reg φ dst (WInt o))
    (* NOTE if not a sealed, return -1 in any other case ? What if not a sealable ? *)
    | _ => updatePC (update_reg φ dst (WInt (-1)))
    end

  | GetWType dst r =>
    wr ← (reg φ) !!ᵣ r; updatePC (update_reg φ dst (WInt (encodeWordType wr)))

  | GetTag dst src =>
    wsrc ← (reg φ) !!ᵣ src;
    updatePC (update_reg φ dst (WInt (Z.b2z (get_tag wsrc))))

  | ClearTag dst src =>
    wsrc ← (reg φ) !!ᵣ src;
    updatePC (update_reg φ dst (clear_tag wsrc))

  | Seal dst r1 r2 =>
    wr1 ← (reg φ) !!ᵣ r1;
    wr2 ← (reg φ) !!ᵣ r2;
    match wr1,wr2 with
    | WSealRange ta p g b e a, WSealable sb =>
      let new_tag := ta && get_tag_sealable sb && permit_seal p && withinBounds b e a in
      let sb' := if new_tag then sb else clear_tag_sealable sb in
      updatePC (update_reg φ dst (WSealed a sb'))
    (* Without a sealing range and a sealable, the sealee loses its tag and is
       not sealed. *)
    | _, _ => updatePC (update_reg φ dst (clear_tag wr2))
    end
  | UnSeal dst r1 r2 =>
    wr1 ← (reg φ) !!ᵣ r1;
    wr2 ← (reg φ) !!ᵣ r2;
    match wr1, wr2 with
    | WSealRange ta p g b e a, WSealed a' sb =>
      let new_tag := ta && get_tag_sealable sb && permit_unseal p && withinBounds b e a' in
      let sb' := if new_tag then unseal_sb g sb else clear_tag_sealable (unseal_sb g sb) in
      updatePC (update_reg φ dst (WSealable sb'))
    (* Without a sealing range and a sealed word, the operand loses its tag
       and is not unsealed. *)
    | _,_ => updatePC (update_reg φ dst (clear_tag wr2))
    end
  | SpecialRW dst sr src =>
      (* The source is read before [dst] is written, so [dst = src] swaps.
         The source [inr cnull] does not write [sr]; the destination [cnull]
         drops the old value of [sr]. *)
      if has_sreg_access plevel
      then
        wold ← (sreg φ) !! sr;
        φ' ← match src with
             | inr r =>
                 if decide (r = cnull) then Some φ
                 else wsrc ← (reg φ) !!ᵣ r; Some (update_sreg φ sr (legalise sr wsrc))
             | inl z => Some (update_sreg φ sr (legalise sr (WInt z)))
             end;
        updatePC (if decide (dst = cnull) then φ' else update_reg φ' dst wold)
      else None
  | SetMIE b =>
      (* MIE receives [b]; MPIE is unchanged. *)
      if has_sreg_access plevel
      then
        wst ← (sreg φ) !! MSTATUS;
        updatePC (update_sreg φ MSTATUS (WInt (mstatus_enc b (mpie_of (get_a wst)))))
      else None
  | Mret =>
      (* The PC receives MEPCC without checks: MEPCC is legalised when
         written. MIE receives MPIE, and MPIE becomes enabled. *)
      if has_sreg_access plevel
      then
        wepcc ← (sreg φ) !! MEPCC;
        wst ← (sreg φ) !! MSTATUS;
        Some (NextI, update_sreg (update_pcc φ wepcc) MSTATUS
                       (WInt (mstatus_enc (mpie_of (get_a wst)) InterruptEnabled)))
      else None
  | Auipcc dst imm =>
      (* As Lea on the PC: the tag is cleared on an address overflow. *)
      match pcc φ with
      | WCap t p g b e a =>
          match (a + imm)%a with
          | Some a' => updatePC (update_reg φ dst (WCap t p g b e a'))
          | None => updatePC (update_reg φ dst (WCap false p g b e a))
          end
      | _ => None
      end
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

(* TODO I don't think that we need to check whether PC
   is in the heap memory or not, at least it's not the case
   in cheriot-sail *)
  Inductive step: Conf → Conf → Prop :=
  | step_exec_corrfail:
      forall φ,
        not (isCorrectPC (pcc φ)) →
        step (Executable, φ) (Failed, φ)
  | step_exec_memfail:
      forall φ p g b e a,
        pcc φ = WCap true p g b e a →
        (mem φ) !! a = None →
        step (Executable, φ) (Failed, φ)
  | step_exec_instr:
      forall φ p g b e a i c wa,
        pcc φ = WCap true p g b e a → (* only works for caps *)
        (mem φ) !! a = Some wa →
        isCorrectPC (WCap true p g b e a) →
        decodeInstrW wa = i →
        exec i p φ = c →
        step (Executable, φ) (c.1, c.2).


End opsem.
