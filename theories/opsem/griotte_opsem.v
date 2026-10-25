From griotte Require Export stdpp_extra machine_utils_extra.
From griotte Require Export machine_base machine_parameters machine_instructions trap_fault.

(* The machine configuration: the PC, the general registers, the system
   registers, the memory and the shadow table. *)
Definition ExecConf := (Word * Reg * SReg * Mem * ShadowTbl)%type.

Inductive ConfFlag : Type :=
| Executable
| Halted
| Faulted
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

(** Field updates, written on the right of the configuration so that a
    chain of updates reads in order, one per line: [φ .[r :=ᵣ w]] is
    [update_reg φ r w]. *)
Notation "φ .[ 'PC' := w ]" := (update_pcc φ w)
  (at level 2, left associativity, format "φ  '/' .[ 'PC'  :=  w ]").
Notation "φ .[ r :=ᵣ w ]" := (update_reg φ r w)
  (at level 2, left associativity, format "φ  '/' .[ r  :=ᵣ  w ]").
Notation "φ .[ sr :=ₛᵣ w ]" := (update_sreg φ sr w)
  (at level 2, left associativity, format "φ  '/' .[ sr  :=ₛᵣ  w ]").
Notation "φ .[ a :=ₐ w ]" := (update_mem φ a w)
  (at level 2, left associativity, format "φ  '/' .[ a  :=ₐ  w ]").
Notation "φ .[ a :=ₛ s ]" := (update_shadowtbl φ a s)
  (at level 2, left associativity, format "φ  '/' .[ a  :=ₛ  s ]").

(** Pipeline: [x |> f] is [f x]. *)
Notation "x |> f" := (f x) (at level 61, left associativity, only parsing).

(** Check: [when b then X] is [X] if [b] holds, and fails otherwise. *)
Notation "'when' b 'then' X" := (if b then X else None)
  (at level 200, X at level 200, only parsing).

(* Note that the `None` values here also undo any previous changes that were tentatively made in the same step. This is more consistent across the board. *)
Definition advancePC (φ: ExecConf) (imm : Z): option Conf :=
  match pcc φ with
  | WCap t p g b e a =>
    match (a + imm)%a with
    | Some a' => let φ' := φ .[PC := WCap t p g b e a'] in
                Some (NextI, φ')
    | None => None
    end
  | _ => None
  end.

Definition nextPC (φ: ExecConf): option Conf := advancePC φ 1.


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

(** The comparison of a conditional jump, on the integer views of its
    operands (signed). *)
Definition jcond_test (i : instr) (n1 n2 : Z) : bool :=
  match i with
  | Jeq _ _ _ => Z.eqb n1 n2
  | Jne _ _ _ => negb (Z.eqb n1 n2)
  | Jlt _ _ _ => Z.ltb n1 n2
  | Jle _ _ _ => Z.leb n1 n2
  | _ => false
  end.

(** A conditional jump: the comparison [test] of [ρ1] and [ρ2] decides
    between a jump by [off], relative to the PC, and the next instruction. *)
Definition exec_jcond (test : Z → Z → bool) (off ρ1 ρ2 : Z + RegName)
  (φ : ExecConf) : option Conf :=
  n1 ← z_of_argument (reg φ) ρ1;
  n2 ← z_of_argument (reg φ) ρ2;
  if test n1 n2
  then imm ← z_of_argument (reg φ) off;
       advancePC φ imm
  else nextPC φ.

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

(** A boolean test for [isCorrectPC]. *)
Definition isCorrectPCb (w: Word): bool :=
  match w with
  | WCap true p g b e a =>
    (b <=? a)%a && (a <? e)%a && executeAllowed p
  | _ => false
  end.

Lemma isCorrectPCb_isCorrectPC w :
  isCorrectPCb w = true ↔ isCorrectPC w.
Proof.
  rewrite /isCorrectPCb. destruct_word w.
  1,3,4,5 : split; try congruence; inversion 1.
  destruct t; last (split; [congruence | inversion 1]).
  rewrite !andb_true_iff !Z.leb_le !Z.ltb_lt.
  split.
  - intros [? ?]. constructor; [solve_addr | naive_solver].
  - inversion 1; subst. split; [solve_addr | naive_solver].
Qed.

Lemma isCorrectPCb_nisCorrectPC w :
  isCorrectPCb w = false ↔ ¬ isCorrectPC w.
Proof.
  destruct (isCorrectPCb w) eqn:HH.
  - apply isCorrectPCb_isCorrectPC in HH. split; congruence.
  - split; auto. intros _. intros ?%isCorrectPCb_isCorrectPC. congruence.
Qed.

(** The word MEPCC receives on exception entry from the PC [w], as
    cheriot-sail: a tagged PC that is not a correct PC (a fetch fault) loses
    its tag; any other PC is kept as it is. *)
Definition mepcc_of_pc (w : Word) : Word :=
  if get_tag w && negb (isCorrectPCb w) then clear_tag w else w.

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
    | Fail => Some (Faulted, φ)
    | Halt => Some (Halted, φ)
    | Jmp rimm =>
        imm ← z_of_argument (reg φ) rimm;
        advancePC φ imm
    | Jeq off ρ1 ρ2 => exec_jcond (jcond_test i) off ρ1 ρ2 φ
    | Jne off ρ1 ρ2 => exec_jcond (jcond_test i) off ρ1 ρ2 φ
    | Jlt off ρ1 ρ2 => exec_jcond (jcond_test i) off ρ1 ρ2 φ
    | Jle off ρ1 ρ2 => exec_jcond (jcond_test i) off ρ1 ρ2 φ
    | Jalr rdst rsrc =>
        wrsrc ← (reg φ) !!ᵣ rsrc;
        (* The checks on the target, in the order of cheriot-sail: the tag,
           the sealing by the form of the instruction, the execute
           permission. A failed check writes neither the PC, nor the link
           register, nor mstatus. *)
        when get_tag wrsrc then
        when jalr_sealing_ok rdst rsrc wrsrc then
        when executable_word wrsrc then
        wst ← (sreg φ) !! MSTATUS;
        match pcc φ with
        | (WCap t p g b e a) =>
            match (a + 1)%a with
            | Some a' =>
                let φ_next := φ .[PC := updatePcPerm wrsrc] in
                (* A [cnull] destination drops the link; the link's kind is
                   taken from MIE before the jump. *)
                let φ_dst :=
                  if decide (rdst = cnull) then φ_next
                  else φ_next
                         .[rdst :=ᵣ jalr_link rdst (mie_of (get_a wst)) t p g b e a'] in
                (* A sentry that sets the interrupt status writes MIE. *)
                let φ_st :=
                  match jalr_mstatus wrsrc (get_a wst) with
                  | Some z => φ_dst .[MSTATUS :=ₛᵣ WInt z]
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
        when readAllowed p && withinBounds b e ea then
          if (is_shadow_address ea)
          then
            heap_a ← shadow_to_heap ea;
            status ← (shadowtbl φ) !! heap_a;
            φ .[dst :=ᵣ WInt (encodeAllocStatus status)] |> nextPC
          else if (is_revoker_address ea)
          then
            (* The revoker reads as zero. *)
            φ .[dst :=ᵣ WInt 0] |> nextPC
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
                φ .[dst :=ᵣ loaded_word] |> nextPC
            | _ => φ .[dst :=ᵣ load_word p asrc] |> nextPC
            end
      | _ => None
      end
    | Store dst ρ imm =>
      tostore ← word_of_argument (reg φ) ρ;
      wdst ← (reg φ) !!ᵣ dst;
      match wdst with
      | WCap true p g b e a =>
        ea ← (a + imm)%a;
        when writeAllowed p && withinBounds b e ea then
          if (is_shadow_address ea)
          then
            heap_a ← shadow_to_heap ea;
            (* Integer stores decode to an allocation status. *)
            match tostore with
            | WInt z => φ .[heap_a :=ₛ decodeAllocStatus z] |> nextPC
            | _ => None
            end
          else if (is_revoker_address ea)
          then
            (* Any store to the revoker sweeps memory; the value is ignored. *)
            revoker_sweep φ |> nextPC
          else
            (* A store to an address absent from memory faults, after the
               capability checks. *)
            match (mem φ) !! ea with
            | Some _ => φ .[ea :=ₐ store_word p tostore] |> nextPC
            | None => None
            end
      | _ => None
      end
    | Mov dst ρ =>
      tomov ← word_of_argument (reg φ) ρ;
      φ .[dst :=ᵣ tomov] |> nextPC
    | Lea dst src ρ =>
      n ← z_of_argument (reg φ) ρ;
      wsrc ← (reg φ) !!ᵣ src;
      match wsrc with
      | WCap t p g b e a =>
          match (a + n)%a with
          | Some a' => φ .[dst :=ᵣ WCap t p g b e a'] |> nextPC
          | None => φ .[dst :=ᵣ WCap false p g b e a] |> nextPC
          end
      | WSealRange t p g b e a =>
         match (a + n)%ot with
          | Some a' => φ .[dst :=ᵣ WSealRange t p g b e a'] |> nextPC
          | None => φ .[dst :=ᵣ WSealRange false p g b e a] |> nextPC
          end
      | WInt z => φ .[dst :=ᵣ WInt (z + n)%Z] |> nextPC
      (* A sealed word or a sentry loses its tag; its address is unchanged. *)
      | _ => φ .[dst :=ᵣ clear_tag wsrc] |> nextPC
      end
    | SetA dst src ρ =>
      n ← z_of_argument (reg φ) ρ;
      wsrc ← (reg φ) !!ᵣ src;
      match wsrc with
      | WCap t p g b e a =>
          match z_to_addr n with
          | Some a' => φ .[dst :=ᵣ WCap t p g b e a'] |> nextPC
          | None => φ .[dst :=ᵣ WCap false p g b e a] |> nextPC
          end
      | WSealRange t p g b e a =>
          match z_to_otype n with
          | Some a' => φ .[dst :=ᵣ WSealRange t p g b e a'] |> nextPC
          | None => φ .[dst :=ᵣ WSealRange false p g b e a] |> nextPC
          end
      | WInt _ => φ .[dst :=ᵣ WInt n] |> nextPC
      (* A sealed word or a sentry loses its tag; its address is unchanged. *)
      | _ => φ .[dst :=ᵣ clear_tag wsrc] |> nextPC
      end
    | Restrict dst src ρ =>
      n ← z_of_argument (reg φ) ρ ;
      wsrc ← (reg φ) !!ᵣ src;
      match wsrc with
      | WCap t p g b e a =>
          let (p',g') := decodePermPair n in
          let new_tag := t && PermFlowsTo p' p && LocalityFlowsTo g' g in
          φ .[dst :=ᵣ WCap new_tag p' g' b e a] |> nextPC
      | WSealRange t p g b e a =>
          let (p',g') := decodeSealPermPair n in
          let new_tag := t && SealPermFlowsTo p' p && LocalityFlowsTo g' g in
          φ .[dst :=ᵣ WSealRange new_tag p' g' b e a] |> nextPC
      (* An integer is unchanged; a sealed word or a sentry loses its tag,
         its permissions unchanged. *)
      | _ => φ .[dst :=ᵣ clear_tag wsrc] |> nextPC
      end
    | machine_instructions.Add dst ρ1 ρ2 =>
    n1 ← z_of_argument (reg φ) ρ1;
    n2 ← z_of_argument (reg φ) ρ2;
    φ .[dst :=ᵣ WInt (n1 + n2)%Z] |> nextPC
    | Sub dst ρ1 ρ2 =>
    n1 ← z_of_argument (reg φ) ρ1;
    n2 ← z_of_argument (reg φ) ρ2;
    φ .[dst :=ᵣ WInt (n1 - n2)%Z] |> nextPC
    | Mul dst ρ1 ρ2 =>
    n1 ← z_of_argument (reg φ) ρ1;
    n2 ← z_of_argument (reg φ) ρ2;
    φ .[dst :=ᵣ WInt (n1 * n2)%Z] |> nextPC
    | LAnd dst ρ1 ρ2 =>
    n1 ← z_of_argument (reg φ) ρ1;
    n2 ← z_of_argument (reg φ) ρ2;
    φ .[dst :=ᵣ WInt (Z.land n1 n2)] |> nextPC
    | LOr dst ρ1 ρ2 =>
    n1 ← z_of_argument (reg φ) ρ1;
    n2 ← z_of_argument (reg φ) ρ2;
    φ .[dst :=ᵣ WInt (Z.lor n1 n2)] |> nextPC
    | LShiftL dst ρ1 ρ2 =>
    n1 ← z_of_argument (reg φ) ρ1;
    n2 ← z_of_argument (reg φ) ρ2;
    φ .[dst :=ᵣ WInt (n1 ≪ n2)%Z] |> nextPC
    | LShiftR dst ρ1 ρ2 =>
    n1 ← z_of_argument (reg φ) ρ1;
    n2 ← z_of_argument (reg φ) ρ2;
    φ .[dst :=ᵣ WInt (n1 ≫ n2)%Z] |> nextPC
    | Lt dst ρ1 ρ2 =>
    n1 ← z_of_argument (reg φ) ρ1;
    n2 ← z_of_argument (reg φ) ρ2;
    φ .[dst :=ᵣ WInt (Z.b2z (Z.ltb n1 n2))] |> nextPC
    | Le dst ρ1 ρ2 =>
    n1 ← z_of_argument (reg φ) ρ1;
    n2 ← z_of_argument (reg φ) ρ2;
    φ .[dst :=ᵣ WInt (Z.b2z (Z.leb n1 n2))] |> nextPC
  | Subseg dst src ρ1 ρ2 =>
    wsrc ← (reg φ) !!ᵣ src;
    match wsrc with
    | WCap t p g b e a =>
      n1 ← z_of_argument (reg φ) ρ1;
      n2 ← z_of_argument (reg φ) ρ2;
      match z_to_addr n1, z_to_addr n2 with
      | Some a1, Some a2 =>
        let new_tag := t && isWithin a1 a2 b e && (a1 <=? a2)%a in
        φ .[dst :=ᵣ WCap new_tag p g a1 a2 a] |> nextPC
      | _, _ => φ .[dst :=ᵣ WCap false p g b e a] |> nextPC
      end
    | WSealRange t p g b e a =>
      n1 ← z_of_argument (reg φ) ρ1;
      n2 ← z_of_argument (reg φ) ρ2;
      match z_to_otype n1, z_to_otype n2 with
      | Some o1, Some o2 =>
        let new_tag := t && isWithin o1 o2 b e in
        φ .[dst :=ᵣ WSealRange new_tag p g o1 o2 a] |> nextPC
      | _, _ => φ .[dst :=ᵣ WSealRange false p g b e a] |> nextPC
      end
    (* An integer is unchanged; a sealed word or a sentry loses its tag, its
       bounds unchanged. *)
    | _ => φ .[dst :=ᵣ clear_tag wsrc] |> nextPC
    end
  | GetA dst r =>
    wr ← (reg φ) !!ᵣ r;
    φ .[dst :=ᵣ WInt (get_a wr)] |> nextPC
  | GetB dst r =>
    wr ← (reg φ) !!ᵣ r;
    φ .[dst :=ᵣ WInt (get_b wr)] |> nextPC
  | GetE dst r =>
    wr ← (reg φ) !!ᵣ r;
    φ .[dst :=ᵣ WInt (get_e wr)] |> nextPC
  | GetLen dst r =>
    wr ← (reg φ) !!ᵣ r;
    φ .[dst :=ᵣ WInt (get_e wr - get_b wr)] |> nextPC
  | GetP dst r =>
    wr ← (reg φ) !!ᵣ r;
    φ .[dst :=ᵣ WInt (encodePermSum (get_p wr))] |> nextPC
  | GetL dst r =>
    wr ← (reg φ) !!ᵣ r;
    φ .[dst :=ᵣ WInt (encodeLoc (get_l wr))] |> nextPC

  | GetOType dst r =>
    wr ← (reg φ) !!ᵣ r;
    match wr with
    | WSealed o _ => φ .[dst :=ᵣ WInt o] |> nextPC
    (* NOTE if not a sealed, return -1 in any other case ? What if not a sealable ? *)
    | _ => φ .[dst :=ᵣ WInt (-1)] |> nextPC
    end

  | GetWType dst r =>
    wr ← (reg φ) !!ᵣ r; φ .[dst :=ᵣ WInt (encodeWordType wr)] |> nextPC

  | GetTag dst src =>
    wsrc ← (reg φ) !!ᵣ src;
    φ .[dst :=ᵣ WInt (Z.b2z (get_tag wsrc))] |> nextPC

  | ClearTag dst src =>
    wsrc ← (reg φ) !!ᵣ src;
    φ .[dst :=ᵣ clear_tag wsrc] |> nextPC

  | Seal dst r1 r2 =>
    wr1 ← (reg φ) !!ᵣ r1;
    wr2 ← (reg φ) !!ᵣ r2;
    match wr1,wr2 with
    | WSealRange ta p g b e a, WSealable sb =>
      let new_tag := ta && get_tag_sealable sb && permit_seal p && withinBounds b e a in
      let sb' := if new_tag then sb else clear_tag_sealable sb in
      φ .[dst :=ᵣ WSealed a sb'] |> nextPC
    (* Without a sealing range and a sealable, the sealee loses its tag and is
       not sealed. *)
    | _, _ => φ .[dst :=ᵣ clear_tag wr2] |> nextPC
    end
  | UnSeal dst r1 r2 =>
    wr1 ← (reg φ) !!ᵣ r1;
    wr2 ← (reg φ) !!ᵣ r2;
    match wr1, wr2 with
    | WSealRange ta p g b e a, WSealed a' sb =>
      let new_tag := ta && get_tag_sealable sb && permit_unseal p && withinBounds b e a' in
      let sb' := if new_tag then unseal_sb g sb else clear_tag_sealable (unseal_sb g sb) in
      φ .[dst :=ᵣ WSealable sb'] |> nextPC
    (* Without a sealing range and a sealed word, the operand loses its tag
       and is not unsealed. *)
    | _,_ => φ .[dst :=ᵣ clear_tag wr2] |> nextPC
    end
  | SpecialRW dst sr src =>
      (* The source is read before [dst] is written, so [dst = src] swaps.
         The source [inr cnull] does not write [sr]; the destination [cnull]
         drops the old value of [sr]. *)
      when has_sreg_access plevel then
        wold ← (sreg φ) !! sr;
        φ' ← match src with
             | inr r =>
                 if decide (r = cnull) then Some φ
                 else wsrc ← (reg φ) !!ᵣ r; Some (φ .[sr :=ₛᵣ legalise sr wsrc])
             | inl z => Some (φ .[sr :=ₛᵣ legalise sr (WInt z)])
             end;
        (if decide (dst = cnull) then φ' else φ' .[dst :=ᵣ wold]) |> nextPC
  | SetMIE b =>
      (* MIE receives [b]; MPIE is unchanged. *)
      when has_sreg_access plevel then
        wst ← (sreg φ) !! MSTATUS;
        φ .[MSTATUS :=ₛᵣ WInt (mstatus_enc b (mpie_of (get_a wst)))] |> nextPC
  | Mret =>
      (* The PC receives MEPCC without checks: MEPCC is legalised when
         written. MIE receives MPIE, and MPIE becomes enabled. *)
      when has_sreg_access plevel then
        wepcc ← (sreg φ) !! MEPCC;
        wst ← (sreg φ) !! MSTATUS;
        Some (NextI,
          φ .[PC      := wepcc]
            .[MSTATUS :=ₛᵣ WInt (mstatus_enc (mpie_of (get_a wst)) InterruptEnabled)])
  | Auipcc dst imm =>
      (* As Lea on the PC: the tag is cleared on an address overflow. *)
      match pcc φ with
      | WCap t p g b e a =>
          match (a + imm)%a with
          | Some a' => φ .[dst :=ᵣ WCap t p g b e a'] |> nextPC
          | None => φ .[dst :=ᵣ WCap false p g b e a] |> nextPC
          end
      | _ => None
      end
  end.

  Definition exec (i: instr) (plevel : Perm) (φ: ExecConf) : Conf :=
     match exec_opt i plevel φ with | None => (Faulted, φ) | Some conf => conf end .

  Lemma exec_opt_exec_some :
    forall φ i plevel c,
      exec_opt i plevel φ = Some c →
      exec i plevel φ = c.
  Proof. unfold exec. by intros * ->. Qed.

  Lemma exec_opt_exec_none :
    forall φ i plevel,
      exec_opt i plevel φ = None →
      exec i plevel φ = (Faulted, φ).
  Proof. unfold exec. by intros * ->. Qed.

(* TODO I don't think that we need to check whether PC
   is in the heap memory or not, at least it's not the case
   in cheriot-sail *)
  Inductive step: Conf → Conf → Prop :=
  | step_exec_corrfail:
      forall φ,
        not (isCorrectPC (pcc φ)) →
        step (Executable, φ) (Faulted, φ)
  | step_exec_memfail:
      forall φ p g b e a,
        pcc φ = WCap true p g b e a →
        (mem φ) !! a = None →
        step (Executable, φ) (Faulted, φ)
  | step_exec_instr:
      forall φ p g b e a i c wa,
        pcc φ = WCap true p g b e a → (* only works for caps *)
        (mem φ) !! a = Some wa →
        isCorrectPC (WCap true p g b e a) →
        decodeInstrW wa = i →
        exec i p φ = c →
        step (Executable, φ) (c.1, c.2).

  (** * Trap entry *)

  (** Exception causes, with the names and values of CHERIoT's
      [sdk/include/priv/riscv.h]. *)
  Definition MCAUSE_INST_ACCESS_FAULT : Z := 1.
  Definition MCAUSE_ILLEGAL_INSTRUCTION : Z := 2.
  Definition MCAUSE_LOAD_ACCESS_FAULT : Z := 5.
  Definition MCAUSE_STORE_ACCESS_FAULT : Z := 7.
  Definition MCAUSE_CHERI : Z := 28.

  (** The value that trap entry writes to mtval for a fault that has none
      (an illegal instruction: cheriot-sail's default, without the
      instruction bits). *)
  Definition MTVAL_NONE : Z := 0.

  (** The default fault, for a fault that the PC checks do not explain and
      that no instruction check reports: a bounds violation on the PC. It is
      the fault of a jump out of the address space, which cheriot-sail
      reports at the next fetch; the other cases are unreachable from a
      correct PC (an absent register, a PC that cannot advance). *)
  Definition fault_default : fault := FaultCheri BoundsViolation CheriPCC.

  (** The checks of the capability [w] in register [r] that authorises a
      data access at offset [imm], in cheriot-sail's order: the tag, the
      sealing, the permission ([perm_ok], else the code [perm_code]; a
      sealing range has none), and the bounds (an address overflow is out
      of bounds). It gives the fault, or the effective address. *)
  Definition data_cap_check (perm_ok : Perm → bool) (perm_code : cheri_cause_code)
    (r : RegName) (w : Word) (imm : Z) : fault + Addr :=
    match w with
    | WCap true p _ b e a =>
        if perm_ok p then
          match (a + imm)%a with
          | Some ea =>
              if withinBounds b e ea then inr ea
              else inl (FaultCheri BoundsViolation (CheriGPR r))
          | None => inl (FaultCheri BoundsViolation (CheriGPR r))
          end
        else inl (FaultCheri perm_code (CheriGPR r))
    | WSealRange true _ _ _ _ _ => inl (FaultCheri perm_code (CheriGPR r))
    | WSentry _ true _ _ _ _ _
    | WSealed _ (SCap true _ _ _ _ _) | WSealed _ (SSealRange true _ _ _ _ _) =>
        inl (FaultCheri SealViolation (CheriGPR r))
    | _ => inl (FaultCheri TagViolation (CheriGPR r))
    end.

  (** The fault of [CLoad _ src imm], in cheriot-sail's order of checks: the
      checks of the capability in [src], and then an access fault at the
      effective address if it is absent from memory or misses the shadow
      table: a shadow address whose heap address has no shadow entry, or a
      loaded heap capability whose base has no shadow entry. *)
  Definition load_fault (φ : ExecConf) (src : RegName) (imm : Z) : fault :=
    match reg φ !!ᵣ src with
    | Some w =>
        match data_cap_check readAllowed PermitLoadViolation src w imm with
        | inl f => f
        | inr ea =>
            if is_shadow_address ea then
              match shadow_to_heap ea with
              | Some heap_a =>
                  match shadowtbl φ !! heap_a with
                  | None => FaultLoadAccess ea
                  | Some _ => fault_default
                  end
              | None => fault_default
              end
            else if is_revoker_address ea then fault_default
            else
              match mem φ !! ea with
              | None => FaultLoadAccess ea
              | Some w =>
                  match heap_cap_base w with
                  | Some base =>
                      match shadowtbl φ !! base with
                      | None => FaultLoadAccess ea
                      | Some _ => fault_default
                      end
                  | None => fault_default
                  end
              end
        end
    | None => fault_default
    end.

  (** The fault of [Store dst ρ imm], in cheriot-sail's order of checks: the
      checks of the capability in [dst], and then an access fault at the
      effective address if it is absent from memory, or if a non-integer is
      stored to a shadow address. *)
  Definition store_fault (φ : ExecConf) (dst : RegName) (ρ : Z + RegName) (imm : Z) : fault :=
    match word_of_argument (reg φ) ρ, reg φ !!ᵣ dst with
    | Some tostore, Some w =>
        match data_cap_check writeAllowed PermitStoreViolation dst w imm with
        | inl f => f
        | inr ea =>
            if is_shadow_address ea then
              match tostore with
              | WInt _ => fault_default
              | _ => FaultStoreAccess ea
              end
            else if is_revoker_address ea then fault_default
            else
              match mem φ !! ea with
              | None => FaultStoreAccess ea
              | Some _ => fault_default
              end
        end
    | _, _ => fault_default
    end.

  (** The fault of [Jalr rdst rsrc], in cheriot-sail's order of checks on
      the target in [rsrc]: the tag, the sealing by the form of the
      instruction, the execute permission. *)
  Definition jalr_fault (φ : ExecConf) (rdst rsrc : RegName) : fault :=
    match reg φ !!ᵣ rsrc with
    | Some w =>
        if negb (get_tag w) then FaultCheri TagViolation (CheriGPR rsrc)
        else if negb (jalr_sealing_ok rdst rsrc w) then FaultCheri SealViolation (CheriGPR rsrc)
        else if negb (executable_word w) then FaultCheri PermitExecuteViolation (CheriGPR rsrc)
        else fault_default
    | None => fault_default
    end.

  (** The register that a system register access without the permission to
      access system registers reports: the special capability register, or
      the PC for a CSR. *)
  Definition sreg_cheri_reg (sr : SRegName) : cheri_reg :=
    match sr with
    | MTCC => CheriMTCC
    | MTDC => CheriMTDC
    | MEPCC => CheriMEPCC
    | MSTATUS | MCAUSE | MTVAL => CheriPCC
    end.

  (** The fault of the instruction [i], executed with the PC permission
      [plevel]: [Fail] is an illegal instruction, a load or a store fails
      the checks of its capability or is an access fault, [Jalr] fails the
      checks of its target, and an access to a system register without the
      permission reports the register. Any other fault is the default
      one. *)
  Definition instr_fault (i : instr) (plevel : Perm) (φ : ExecConf) : fault :=
    let no_sreg_access sr :=
      if has_sreg_access plevel then fault_default
      else FaultCheri PermitAccessSystemRegistersViolation sr in
    match i with
    | Fail => FaultIllegal
    | CLoad _ src imm => load_fault φ src imm
    | Store dst ρ imm => store_fault φ dst ρ imm
    | Jalr rdst rsrc => jalr_fault φ rdst rsrc
    | SpecialRW _ sr _ => no_sreg_access (sreg_cheri_reg sr)
    | SetMIE _ | Mret => no_sreg_access CheriPCC
    | _ => fault_default
    end.

  (** The fault in the state [φ], from the fetch and the decoded instruction
      at PC: the checks of the PC in cheriot-sail's order (the tag, the
      sealing, the execute permission, the bounds) are CHERI faults on the
      PC, a fetch from an address absent from memory is an access fault. *)
  Definition trap_fault (φ : ExecConf) : fault :=
    match pcc φ with
    | WCap true p _ _ _ a =>
        if isCorrectPCb (pcc φ) then
          match mem φ !! a with
          | None => FaultInstAccess a
          | Some wa => instr_fault (decodeInstrW wa) p φ
          end
        else if executeAllowed p then FaultCheri BoundsViolation CheriPCC
        else FaultCheri PermitExecuteViolation CheriPCC
    | WSealRange true _ _ _ _ _ => FaultCheri PermitExecuteViolation CheriPCC
    | WSentry _ true _ _ _ _ _
    | WSealed _ (SCap true _ _ _ _ _) | WSealed _ (SSealRange true _ _ _ _ _) =>
        FaultCheri SealViolation CheriPCC
    | _ => FaultCheri TagViolation CheriPCC
    end.

  (** The cause and the value of a fault, as cheriot-sail writes them to
      mcause and mtval. *)
  Definition fault_mcause (f : fault) : Z :=
    match f with
    | FaultCheri _ _ => MCAUSE_CHERI
    | FaultIllegal => MCAUSE_ILLEGAL_INSTRUCTION
    | FaultInstAccess _ => MCAUSE_INST_ACCESS_FAULT
    | FaultLoadAccess _ => MCAUSE_LOAD_ACCESS_FAULT
    | FaultStoreAccess _ => MCAUSE_STORE_ACCESS_FAULT
    end.

  Definition fault_mtval (f : fault) : Z :=
    match f with
    | FaultCheri c r => encode_mtval c r
    | FaultIllegal => MTVAL_NONE
    | FaultInstAccess a | FaultLoadAccess a | FaultStoreAccess a => a
    end.

  (** The cause and the value of a fault in the state [φ]. *)
  Definition trap_cause (φ : ExecConf) : Z := fault_mcause (trap_fault φ).
  Definition trap_tval (φ : ExecConf) : Z := fault_mtval (trap_fault φ).

  (** The value of a system register; an absent one reads as [WInt 0]. *)
  Definition sreg_word (φ : ExecConf) (sr : SRegName) : Word :=
    default (WInt 0) (sreg φ !! sr).

  (** Exception entry with cause [cv.1] and value [cv.2], as cheriot-sail:
      MEPCC receives the PC, untagged if it is not a correct PC
      ([mepcc_of_pc]), MPIE receives MIE, MIE is disabled, mcause and mtval
      receive the cause and the value, and the PC receives MTCC without checks
      (MTCC is legalised when written). *)
  Definition enter_exc (cv : Z * Z) (φ : ExecConf) : ExecConf :=
    let mie := mie_of (get_a (sreg_word φ MSTATUS)) in
    φ .[MEPCC   :=ₛᵣ mepcc_of_pc (pcc φ)]
      .[MSTATUS :=ₛᵣ WInt (mstatus_enc InterruptDisabled mie)]
      .[MCAUSE  :=ₛᵣ WInt cv.1]
      .[MTVAL   :=ₛᵣ WInt cv.2]
      .[PC      := sreg_word φ MTCC].

  (** After a fault, the machine stops instead of entering the exception
      handler when neither the PC nor MTCC is tagged. A fault with an untagged
      PC is a fetch fault, and cheriot-sail's fetch check stops there, writing
      nothing, when MTCC is untagged: the entry would install the untagged
      MTCC in the PC, which would fault again. *)
  Definition trap_halts (φ : ExecConf) : bool :=
    negb (get_tag (pcc φ)) && negb (get_tag (sreg_word φ MTCC)).

End opsem.
