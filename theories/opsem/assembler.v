From stdpp Require Export strings gmap.
From griotte Require Export -(coercions) machine_base.

Module Asm_Griotte.

  (** To use the assembler, import `Asm_Griotte`.
      Define the assembly code: `xxx_asm : list asm_code`,
      assemble it and check it with
      ```
      Definition assembled_xxx := Eval compute in (assemble xxx_asm).
      Lemma xxx_assembles : asm_ok (assemble_check xxx_asm).
      Proof. asm_check. Qed.
      ```
      The check fails with the assembler's message on an undefined label, a
      label or symbol defined twice, or a symbol between two instructions
      ([assemble] returns [[]] on such an error).
      Label expressions resolve at the position of their instruction.

      If your code is supposed to be defined by blocks,
      ie, `xxx_asm := xxx1_asm ++ xxx2_asm`,
      define instead `xxx_asm := [xxx1_asm; xxx2_asm]`
      and assemble it by blocks:
      ```
      Definition assembled_xxx := Eval compute in (assemble_block xxx_asm).
      Lemma xxx_assembles : asm_ok (assemble_block_check xxx_asm).
      Proof. asm_check. Qed.
      Definition xxx_instrs : list Word := concat (encodeInstrsW <$> assembled_xxx).
      ```

      Assemble with [compute], not [vm_compute]: [compute] respects the
      opacity of the register names (`csp`, `cs0`, ...), so they stay folded
      in the assembled code and register parameters are preserved, while
      [vm_compute] unfolds them (https://github.com/rocq-prover/rocq/issues/4476).

      A macro is a function returning asm code, inlined in the programs that
      use it. If it defines labels, make it a local block, so that its labels
      are resolved inside it and do not clash with other instances:
      ```
      Definition xxx_asm (r : RegName) : list asm_code :=
        macro: [ ... ; #"loop"; ... ; jnez "loop" r; ... ].
      Definition xxx (r : RegName) : list instr :=
        Eval compute in assemble (xxx_asm r).
      Lemma xxx_assembles r : asm_ok (assemble_check (xxx_asm r)).
      Proof. asm_check. Qed.
      ```
      A macro without local labels can refer to the labels and symbols of
      the enclosing program (e.g. the import symbols named by [fetch_asm]).

      [label_offset l s] is the offset of the label or symbol [s] of [l],
      and [label_offset_from l from s] the offset of [s] from [from]. For a
      program by blocks [P], they apply to [concat P], and the lemmas
      [label_offset_code_block] and [label_offset_code_instr] (in
      [code_blocks]) relate the offset of a label to the offsets of the
      blocks of the assembled code. A specification can state its PC as
      `(pc_b + label_offset (concat xxx_asm) ".Lname")%a = Some pc_a`; on
      closed arguments, [offsets_compute] computes the offsets.
   *)

  (*** Assembly Language with Labels *)
  Inductive asm_expr : Type :=
  | Asm_lbl (s : string)
  | Asm_z (z : Z)
  | Asm_plus (e1 e2 : asm_expr)
  | Asm_minus (e1 e2 : asm_expr).

  (** The operand of an instruction that takes an immediate or a register.
      It is a definition of its own so that the asm coercions into it do not
      clash with the coercions into [Z + RegName] of [register_file]. *)
  Definition asm_arg : Type := (asm_expr + RegName)%type.

  Inductive asm_instr: Type :=
  | Jmp (rimm: asm_arg)
  | Jeq (off : asm_arg) (r1 r2 : asm_arg)
  | Jne (off : asm_arg) (r1 r2 : asm_arg)
  | Jlt (off : asm_arg) (r1 r2 : asm_arg)
  | Jle (off : asm_arg) (r1 r2 : asm_arg)
  | Jalr (rdst: RegName) (rsrc: RegName)
  | Mov (dst: RegName) (src: asm_arg)
  | CLoad (dst src: RegName) (imm: asm_expr)
  | Store (dst: RegName) (src: asm_arg) (imm: asm_expr)
  | Lt (dst: RegName) (r1 r2: asm_arg)
  | Le (dst: RegName) (r1 r2: asm_arg)
  | Add (dst: RegName) (r1 r2: asm_arg)
  | Sub (dst: RegName) (r1 r2: asm_arg)
  | Mul (dst: RegName) (r1 r2: asm_arg)
  | LAnd (dst: RegName) (r1 r2: asm_arg)
  | LOr (dst: RegName) (r1 r2: asm_arg)
  | LShiftL (dst: RegName) (r1 r2: asm_arg)
  | LShiftR (dst: RegName) (r1 r2: asm_arg)
  | Lea (dst src : RegName) (off : asm_arg)
  | SetA (dst src : RegName) (addr : asm_arg)
  | Restrict (dst src : RegName) (perm : asm_arg)
  | Subseg (dst src : RegName) (b e : asm_arg)
  | GetB (dst r: RegName)
  | GetE (dst r: RegName)
  | GetLen (dst r: RegName)
  | GetA (dst r: RegName)
  | GetP (dst r: RegName)
  | GetL (dst r: RegName)
  | GetWType (dst r : RegName)
  | GetOType (dst r: RegName)
  | Seal (dst : RegName) (r1 r2: RegName)
  | UnSeal (dst : RegName) (r1 r2: RegName)
  | SpecialRW (dst: RegName) (sr: SRegName) (src: asm_arg)
  | SetMIE (b: InterruptStatus)
  (* [csrsi]/[csrci] on [sr] with [mask]: only [mstatus] with the MIE mask
     assembles, to [SetMIE b]. *)
  | CsrMIE (b: InterruptStatus) (sr: SRegName) (mask: asm_expr)
  | Mret
  | Fail
  | Halt
  | GetTag (dst src: RegName)
  | ClearTag (dst src: RegName)
  | Auipcc (dst: RegName) (imm: asm_expr).

  (** [ASM_Symbol s] names a data word reserved by the loader at the current
      address: it occupies one word but emits no instruction. Symbols may only
      form a data prefix before the code or a data suffix after it (see
      [asm_symbols_check]), so that the assembled instructions stay
      contiguous.

      [ASM_Local l] is the code [l] with its own scope: the labels and
      symbols defined in [l] are visible only in [l], where they shadow
      those of the enclosing code, while [l] sees the names of the enclosing
      code. A macro with labels is a local block, so that it can be
      instantiated several times in a program. *)
  Inductive asm_code : Type :=
  | ASM_Label (s : string)
  | ASM_Symbol (s : string)
  | ASM_Instr (w : asm_instr)
  | ASM_Local (l : list asm_code).

  (** The number of words of a piece of code: its instructions and symbols. *)
  Fixpoint asm_code_words (c : asm_code) : nat :=
    match c with
    | ASM_Label _ => 0
    | ASM_Symbol _ | ASM_Instr _ => 1
    | ASM_Local l =>
        (fix words (l : list asm_code) : nat :=
           match l with
           | [] => 0
           | c :: l => asm_code_words c + words l
           end) l
    end.

  Fixpoint asm_words (l : list asm_code) : nat :=
    match l with
    | [] => 0
    | c :: l => asm_code_words c + asm_words l
    end.

  (** The code with its local blocks inlined. *)
  Fixpoint asm_code_flatten (c : asm_code) : list asm_code :=
    match c with
    | ASM_Local l =>
        (fix flatten (l : list asm_code) : list asm_code :=
           match l with
           | [] => []
           | c :: l => asm_code_flatten c ++ flatten l
           end) l
    | c => [c]
    end.

  Fixpoint asm_flatten (l : list asm_code) : list asm_code :=
    match l with
    | [] => []
    | c :: l => asm_code_flatten c ++ asm_flatten l
    end.

  (*** Assembler results. *)
  (** The result of assembling: the value, or an error message naming the
      offending label, symbol or instruction. *)
  Inductive asm_result (A : Type) : Type :=
  | Ok (a : A)
  | Err (msg : string).
  Arguments Ok {A} a.
  Arguments Err {A} msg.

  #[global] Instance asm_result_ret : MRet asm_result := λ A a, Ok a.
  #[global] Instance asm_result_bind : MBind asm_result :=
    λ A B f r, match r with Ok a => f a | Err msg => Err msg end.

  (** The value of a result, or [d] on an error. *)
  Definition asm_get {A} (d : A) (r : asm_result A) : A :=
    match r with Ok a => a | Err _ => d end.

  (*** Checked environment. *)
  (** The environment maps each label and symbol to its word offset. It is
      an association list rather than a [gmap]: [compute] reduces lookups in
      it quickly, while reducing [gmap] operations on [string] keys is slow. *)
  Definition asm_env_map : Type := list (string * nat).

  Fixpoint asm_lookup (s : string) (env : asm_env_map) : option nat :=
    match env with
    | [] => None
    | (s', n) :: env => if String.eqb s s' then Some n else asm_lookup s env
    end.

  (** The offset of each label and symbol of [l] (outside its local blocks)
      in the code without labels, where the first word of [l] is at offset
      [n]. A name defined twice is an error. *)
  Fixpoint asm_env_aux (l : list asm_code) (n : nat) (env : asm_env_map)
    : asm_result (asm_env_map) :=
    match l with
    | [] => Ok env
    | ASM_Label s :: l =>
        match asm_lookup s env with
        | Some _ => Err ("duplicate label: " ++ s)%string
        | None => asm_env_aux l n ((s, n) :: env)
        end
    | ASM_Symbol s :: l =>
        match asm_lookup s env with
        | Some _ => Err ("duplicate symbol: " ++ s)%string
        | None => asm_env_aux l (S n) ((s, n) :: env)
        end
    | ASM_Instr _ :: l => asm_env_aux l (S n) env
    | ASM_Local l' :: l => asm_env_aux l (n + asm_code_words (ASM_Local l')) env
    end.

  Definition asm_env (l : list asm_code) : asm_result (asm_env_map) :=
    asm_env_aux l 0 [].

  (** Symbols form a data prefix before the code and a data suffix after it,
      never between two instructions. [sym] is [None] before the first
      instruction or while no symbol follows the code, and the last symbol
      after the code otherwise. *)
  Fixpoint asm_symbols_check_aux (in_code : bool) (sym : option string) (l : list asm_code)
    : asm_result unit :=
    match l with
    | [] => Ok tt
    | ASM_Label _ :: l => asm_symbols_check_aux in_code sym l
    | ASM_Symbol s :: l =>
        if in_code
        then asm_symbols_check_aux true (Some s) l
        else asm_symbols_check_aux false None l
    | ASM_Instr _ :: l =>
        match sym with
        | Some s => Err ("symbol between instructions: " ++ s)%string
        | None => asm_symbols_check_aux true None l
        end
    | ASM_Local _ :: l => asm_symbols_check_aux in_code sym l
    end.

  (** The check applies to the code with its local blocks inlined. *)
  Definition asm_symbols_check (l : list asm_code) : asm_result unit :=
    asm_symbols_check_aux false None (asm_flatten l).

  (** Evaluates an expression at the word offset [n] of the code: a label
      denotes its offset relative to [n]. *)
  Fixpoint asm_eval (expr : asm_expr) (env : asm_env_map) (n : nat) : asm_result Z :=
    match expr with
    | Asm_lbl lbl =>
        match asm_lookup lbl env with
        | Some z => Ok (Z.of_nat z - Z.of_nat n)%Z
        | None => Err ("undefined label: " ++ lbl)%string
        end
    | Asm_z z => Ok z
    | Asm_plus e1 e2 =>
        z1 ← asm_eval e1 env n;
        z2 ← asm_eval e2 env n;
        Ok (z1 + z2)%Z
    | Asm_minus e1 e2 =>
        z1 ← asm_eval e1 env n;
        z2 ← asm_eval e2 env n;
        Ok (z1 - z2)%Z
    end.

  (*** Code assembler. *)
  Definition assemble_arg (arg : asm_expr + RegName) (env : asm_env_map) (n : nat)
    : asm_result (Z + RegName) :=
    match arg with
    | inr r => Ok (inr r)
    | inl expr => z ← asm_eval expr env n; Ok (inl z)
    end.

  Definition assemble_instr (i : asm_instr) (env : asm_env_map) (n : nat)
    : asm_result instr :=
    match i with
    | Jmp rimm =>
        rimm' ← assemble_arg rimm env n;
        Ok (machine_instructions.Jmp rimm')
    | Jeq off r1 r2 =>
        off' ← assemble_arg off env n;
        w1 ← assemble_arg r1 env n;
        w2 ← assemble_arg r2 env n;
        Ok (machine_instructions.Jeq off' w1 w2)
    | Jne off r1 r2 =>
        off' ← assemble_arg off env n;
        w1 ← assemble_arg r1 env n;
        w2 ← assemble_arg r2 env n;
        Ok (machine_instructions.Jne off' w1 w2)
    | Jlt off r1 r2 =>
        off' ← assemble_arg off env n;
        w1 ← assemble_arg r1 env n;
        w2 ← assemble_arg r2 env n;
        Ok (machine_instructions.Jlt off' w1 w2)
    | Jle off r1 r2 =>
        off' ← assemble_arg off env n;
        w1 ← assemble_arg r1 env n;
        w2 ← assemble_arg r2 env n;
        Ok (machine_instructions.Jle off' w1 w2)
    | Jalr rdst rsrc =>
        Ok (machine_instructions.Jalr rdst rsrc)
    | Mov dst src  =>
        src ← assemble_arg src env n;
        Ok (machine_instructions.Mov dst src)
    | CLoad dst src imm =>
        off ← asm_eval imm env n;
        Ok (machine_instructions.CLoad dst src off)
    | Store dst src imm =>
        src ← assemble_arg src env n;
        off ← asm_eval imm env n;
        Ok (machine_instructions.Store dst src off)
    | Lt dst r1 r2 =>
        w1 ← assemble_arg r1 env n;
        w2 ← assemble_arg r2 env n;
        Ok (machine_instructions.Lt dst w1 w2)
    | Le dst r1 r2 =>
        w1 ← assemble_arg r1 env n;
        w2 ← assemble_arg r2 env n;
        Ok (machine_instructions.Le dst w1 w2)
    | Add dst r1 r2 =>
        w1 ← assemble_arg r1 env n;
        w2 ← assemble_arg r2 env n;
        Ok (machine_instructions.Add dst w1 w2)
    | Sub dst r1 r2 =>
        w1 ← assemble_arg r1 env n;
        w2 ← assemble_arg r2 env n;
        Ok (machine_instructions.Sub dst w1 w2)
    | Mul dst r1 r2 =>
        w1 ← assemble_arg r1 env n;
        w2 ← assemble_arg r2 env n;
        Ok (machine_instructions.Mul dst w1 w2)
    | LAnd dst r1 r2 =>
        w1 ← assemble_arg r1 env n;
        w2 ← assemble_arg r2 env n;
        Ok (machine_instructions.LAnd dst w1 w2)
    | LOr dst r1 r2 =>
        w1 ← assemble_arg r1 env n;
        w2 ← assemble_arg r2 env n;
        Ok (machine_instructions.LOr dst w1 w2)
    | LShiftL dst r1 r2 =>
        w1 ← assemble_arg r1 env n;
        w2 ← assemble_arg r2 env n;
        Ok (machine_instructions.LShiftL dst w1 w2)
    | LShiftR dst r1 r2 =>
        w1 ← assemble_arg r1 env n;
        w2 ← assemble_arg r2 env n;
        Ok (machine_instructions.LShiftR dst w1 w2)
    | Lea dst src r =>
        w ← assemble_arg r env n;
        Ok (machine_instructions.Lea dst src w)
    | SetA dst src addr =>
        w ← assemble_arg addr env n;
        Ok (machine_instructions.SetA dst src w)
    | Restrict dst src r =>
        w ← assemble_arg r env n;
        Ok (machine_instructions.Restrict dst src w)
    | Subseg dst src r1 r2 =>
        w1 ← assemble_arg r1 env n;
        w2 ← assemble_arg r2 env n;
        Ok (machine_instructions.Subseg dst src w1 w2)
    | GetB dst src =>
        Ok (machine_instructions.GetB dst src)
    | GetE dst src =>
        Ok (machine_instructions.GetE dst src)
    | GetLen dst src =>
        Ok (machine_instructions.GetLen dst src)
    | GetA dst src =>
        Ok (machine_instructions.GetA dst src)
    | GetP dst src =>
        Ok (machine_instructions.GetP dst src)
    | GetL dst src =>
        Ok (machine_instructions.GetL dst src)
    | GetTag dst src =>
        Ok (machine_instructions.GetTag dst src)
    | ClearTag dst src =>
        Ok (machine_instructions.ClearTag dst src)
    | GetWType dst src =>
        Ok (machine_instructions.GetWType dst src)
    | GetOType dst src =>
        Ok (machine_instructions.GetOType dst src)
    | Seal dst r1 r2 =>
        Ok (machine_instructions.Seal dst r1 r2)
    | UnSeal dst r1 r2 =>
        Ok (machine_instructions.UnSeal dst r1 r2)
    | SpecialRW dst sr src =>
        src ← assemble_arg src env n;
        Ok (machine_instructions.SpecialRW dst sr src)
    | SetMIE b =>
        Ok (machine_instructions.SetMIE b)
    | CsrMIE b sr mask =>
        z ← asm_eval mask env n;
        if decide (sr = MSTATUS ∧ z = Z.shiftl 1 MIE_BIT)
        then Ok (machine_instructions.SetMIE b)
        else Err "csrsi/csrci: only mstatus with the MIE mask 0x8"%string
    | Mret =>
        Ok machine_instructions.Mret
    | Fail=>
        Ok (machine_instructions.Fail)
    | Halt=>
        Ok (machine_instructions.Halt)
    | Auipcc dst imm =>
        off ← asm_eval imm env n;
        Ok (machine_instructions.Auipcc dst off)
    end.

  (** Assembles a piece of code, whose first word is at offset [n]. A local
      block is assembled with its own names in front of [env]. *)
  Fixpoint assemble_code_item (c : asm_code) (env : asm_env_map) (n : nat)
    : asm_result (list instr) :=
    match c with
    | ASM_Label _ | ASM_Symbol _ => Ok []
    | ASM_Instr i => i' ← assemble_instr i env n; Ok [i']
    | ASM_Local l =>
        env' ← asm_env_aux l n [];
        (fix assemble_local (l : list asm_code) (n : nat) : asm_result (list instr) :=
           match l with
           | [] => Ok []
           | c :: l =>
               c' ← assemble_code_item c (env' ++ env) n;
               l' ← assemble_local l (n + asm_code_words c);
               Ok (c' ++ l')
           end) l n
    end.

  (** Assembles [l], whose first word is at offset [n]. *)
  Fixpoint assemble_code (l : list asm_code) (env : asm_env_map) (n : nat)
    : asm_result (list instr) :=
    match l with
    | [] => Ok []
    | c :: l =>
        c' ← assemble_code_item c env n;
        l' ← assemble_code l env (n + asm_code_words c);
        Ok (c' ++ l')
    end.

  Fixpoint assemble_blocks (l : list (list asm_code)) (env : asm_env_map) (n : nat)
    : asm_result (list (list instr)) :=
    match l with
    | [] => Ok []
    | b :: l =>
        b' ← assemble_code b env n;
        l' ← assemble_blocks l env (n + asm_words b);
        Ok (b' :: l')
    end.

  (** Checked assembler for plain code. *)
  Definition assemble_check (l : list asm_code) : asm_result (list instr) :=
    asm_symbols_check l;;
    env ← asm_env l;
    assemble_code l env 0.

  (** Checked assembler for a list of blocks, with the environment of their
      concatenation. Each block keeps its own list of instructions, so that
      the blocks can be specified separately. *)
  Definition assemble_block_check (l : list (list asm_code))
    : asm_result (list (list instr)) :=
    asm_symbols_check (concat l);;
    env ← asm_env (concat l);
    assemble_blocks l env 0.

  (** Assemblers returning the code, [[]] on an error. Each assembled
      definition comes with a check (see [asm_check]) that fails on an
      error. *)
  Definition assemble (l : list asm_code) : list instr :=
    asm_get [] (assemble_check l).

  Definition assemble_block (l : list (list asm_code)) : list (list instr) :=
    asm_get [] (assemble_block_check l).

  (** The offset of the label or symbol [s] of [l] (outside its local
      blocks) in the code without labels, [0] if it is undefined. *)
  Definition label_offset (l : list asm_code) (s : string) : nat :=
    match asm_env l with
    | Ok env => default 0 (asm_lookup s env)
    | Err _ => 0
    end.

  (** The offset of the label or symbol [s] of [l] from the label or symbol
      [from] of [l]. For a program by blocks [P], the labels are those of
      [concat P]. On closed arguments, it computes by [vm_compute] (see
      [offsets_compute]). *)
  Definition label_offset_from (l : list asm_code) (from s : string) : Z :=
    (Z.of_nat (label_offset l s) - Z.of_nat (label_offset l from))%Z.

  (*** Successful results. *)
  (** [asm_ok r] holds when [r] is not an error; on an error it reduces to
      the uninhabited [asm_error msg], so that [asm_check] reports [msg]. *)
  Inductive asm_error (msg : string) : Prop := .

  Definition asm_ok {A} (r : asm_result A) : Prop :=
    match r with
    | Ok _ => True
    | Err msg => asm_error msg
    end.

  (** Whether [l] defines the label or symbol [s] (outside its local
      blocks). *)
  Definition asm_defines (s : string) (l : list asm_code) : bool :=
    existsb (λ c, match c with
                  | ASM_Label s' | ASM_Symbol s' => String.eqb s s'
                  | _ => false
                  end) l.

  (** The index of the block of [P] that defines the label or symbol [s]
      ([length P] if none does). On closed arguments, it computes by
      [vm_compute] (see [focus_block]). *)
  Fixpoint label_block (P : list (list asm_code)) (s : string) : nat :=
    match P with
    | [] => 0
    | b :: P => if asm_defines s b then 0 else S (label_block P s)
    end.

  (*** Offsets of the labels. *)
  (** The number of instructions and the number of symbols of a piece of
      code: its words are its instructions and its symbols. *)
  Fixpoint asm_code_instrs (c : asm_code) : nat :=
    match c with
    | ASM_Instr _ => 1
    | ASM_Label _ | ASM_Symbol _ => 0
    | ASM_Local l =>
        (fix instrs (l : list asm_code) : nat :=
           match l with
           | [] => 0
           | c :: l => asm_code_instrs c + instrs l
           end) l
    end.

  Fixpoint asm_instrs (l : list asm_code) : nat :=
    match l with
    | [] => 0
    | c :: l => asm_code_instrs c + asm_instrs l
    end.

  Fixpoint asm_code_symbols (c : asm_code) : nat :=
    match c with
    | ASM_Symbol _ => 1
    | ASM_Label _ | ASM_Instr _ => 0
    | ASM_Local l =>
        (fix symbols (l : list asm_code) : nat :=
           match l with
           | [] => 0
           | c :: l => asm_code_symbols c + symbols l
           end) l
    end.

  Fixpoint asm_symbols (l : list asm_code) : nat :=
    match l with
    | [] => 0
    | c :: l => asm_code_symbols c + asm_symbols l
    end.

  (** Induction on [asm_code], through the local blocks. *)
  Section asm_code_induction.
    Context (P : asm_code → Prop).
    Context (Hlabel : ∀ s, P (ASM_Label s)) (Hsymbol : ∀ s, P (ASM_Symbol s))
      (Hinstr : ∀ i, P (ASM_Instr i)) (Hlocal : ∀ l, Forall P l → P (ASM_Local l)).

    Fixpoint asm_code_ind' (c : asm_code) : P c :=
      match c with
      | ASM_Label s => Hlabel s
      | ASM_Symbol s => Hsymbol s
      | ASM_Instr i => Hinstr i
      | ASM_Local l =>
          Hlocal l
            ((fix go (l : list asm_code) : Forall P l :=
                match l with
                | [] => @List.Forall_nil _ P
                | c :: l => @List.Forall_cons _ P c l (asm_code_ind' c) (go l)
                end) l)
      end.
  End asm_code_induction.

  Lemma asm_code_words_local l : asm_code_words (ASM_Local l) = asm_words l.
  Proof. induction l as [|c l IH]; [done|]. cbn in *. by rewrite IH. Qed.
  Lemma asm_code_instrs_local l : asm_code_instrs (ASM_Local l) = asm_instrs l.
  Proof. induction l as [|c l IH]; [done|]. cbn in *. by rewrite IH. Qed.
  Lemma asm_code_symbols_local l : asm_code_symbols (ASM_Local l) = asm_symbols l.
  Proof. induction l as [|c l IH]; [done|]. cbn in *. by rewrite IH. Qed.

  Lemma asm_words_app l1 l2 : asm_words (l1 ++ l2) = asm_words l1 + asm_words l2.
  Proof. induction l1; cbn; lia. Qed.
  Lemma asm_instrs_app l1 l2 : asm_instrs (l1 ++ l2) = asm_instrs l1 + asm_instrs l2.
  Proof. induction l1; cbn; lia. Qed.
  Lemma asm_symbols_app l1 l2 : asm_symbols (l1 ++ l2) = asm_symbols l1 + asm_symbols l2.
  Proof. induction l1; cbn; lia. Qed.

  Lemma asm_code_words_split c :
    asm_code_words c = asm_code_instrs c + asm_code_symbols c.
  Proof.
    induction c as [| | |l Hl] using asm_code_ind'; try done.
    rewrite asm_code_words_local asm_code_instrs_local asm_code_symbols_local.
    induction Hl as [|c l Hc _ IH]; cbn; lia.
  Qed.

  Lemma asm_words_split l : asm_words l = asm_instrs l + asm_symbols l.
  Proof. induction l as [|c l IH]; cbn; [done|]. rewrite asm_code_words_split. lia. Qed.

  Lemma assemble_code_item_local l env n :
    assemble_code_item (ASM_Local l) env n =
      (env' ← asm_env_aux l n []; assemble_code l (env' ++ env) n).
  Proof.
    cbn [assemble_code_item]. destruct (asm_env_aux l n []) as [env'|msg]; [|done].
    cbn. generalize n. induction l as [|c l IH]; intros m; [done|]. cbn.
    destruct (assemble_code_item c (env' ++ env) m); cbn; [|done].
    by rewrite IH.
  Qed.

  (** The assembled code has one instruction per instruction of the code. *)
  Lemma assemble_code_item_length c env n ins :
    assemble_code_item c env n = Ok ins → length ins = asm_code_instrs c.
  Proof.
    revert env n ins.
    induction c as [s|s|i|l Hl] using asm_code_ind'; intros env n ins.
    - by intros [= <-].
    - by intros [= <-].
    - cbn. destruct (assemble_instr i env n); cbn; [by intros [= <-]|done].
    - rewrite assemble_code_item_local asm_code_instrs_local.
      destruct (asm_env_aux l n []) as [env'|]; cbn; [|done].
      generalize (env' ++ env). clear env. revert n ins.
      induction Hl as [|c l Hc _ IH]; intros n ins env; cbn; [by intros [= <-]|].
      destruct (assemble_code_item c env n) as [c'|] eqn:Hc'; cbn; [|done].
      destruct (assemble_code l env (n + asm_code_words c)) as [l'|] eqn:Hl'; cbn; [|done].
      intros [= <-]. rewrite length_app (Hc _ _ _ Hc') (IH _ _ _ Hl'). done.
  Qed.

  Lemma assemble_code_length l env n ins :
    assemble_code l env n = Ok ins → length ins = asm_instrs l.
  Proof.
    revert n ins. induction l as [|c l IH]; intros n ins; cbn; [by intros [= <-]|].
    destruct (assemble_code_item c env n) as [c'|] eqn:Hc'; cbn; [|done].
    destruct (assemble_code l env (n + asm_code_words c)) as [l'|] eqn:Hl'; cbn; [|done].
    intros [= <-]. rewrite length_app (assemble_code_item_length _ _ _ _ Hc') (IH _ _ Hl'). done.
  Qed.

  Lemma assemble_blocks_length P env n bs :
    assemble_blocks P env n = Ok bs → length <$> bs = asm_instrs <$> P.
  Proof.
    revert n bs. induction P as [|b P IH]; intros n bs; cbn; [by intros [= <-]|].
    destruct (assemble_code b env n) as [b'|] eqn:Hb; cbn; [|done].
    destruct (assemble_blocks P env (n + asm_words b)) as [P'|] eqn:HP; cbn; [|done].
    intros [= <-]. cbn. by rewrite (assemble_code_length _ _ _ _ Hb) (IH _ _ HP).
  Qed.

  Lemma asm_env_aux_app l1 l2 n env :
    asm_env_aux (l1 ++ l2) n env =
      (env1 ← asm_env_aux l1 n env; asm_env_aux l2 (n + asm_words l1) env1).
  Proof.
    revert n env. induction l1 as [|c l1 IH]; intros n env; cbn.
    { by rewrite Nat.add_0_r. }
    destruct c as [s|s|i|l]; cbn.
    - destruct (asm_lookup s env); [done|]. by rewrite IH.
    - destruct (asm_lookup s env); [done|]. rewrite IH.
      destruct (asm_env_aux l1 (S n) _); cbn; [|done]. f_equal. lia.
    - rewrite IH. destruct (asm_env_aux l1 (S n) env); cbn; [|done]. f_equal. lia.
    - rewrite IH. destruct (asm_env_aux l1 _ env); cbn; [|done]. f_equal. lia.
  Qed.

  Lemma asm_env_aux_lookup l n env env' s k :
    asm_env_aux l n env = Ok env' →
    asm_lookup s env = Some k →
    asm_lookup s env' = Some k.
  Proof.
    revert n env. induction l as [|c l IH]; intros n env; cbn.
    { by intros [= <-]. }
    destruct c as [s'|s'|i|l']; intros Henv Hs.
    - destruct (asm_lookup s' env) eqn:Hs'; [done|]. eapply IH; [done|]. cbn.
      destruct (String.eqb_spec s s'); [subst; congruence|done].
    - destruct (asm_lookup s' env) eqn:Hs'; [done|]. eapply IH; [done|]. cbn.
      destruct (String.eqb_spec s s'); [subst; congruence|done].
    - by eapply IH.
    - by eapply IH.
  Qed.

  (** A label of the top level of the code is at the number of words that
      precede it. *)
  Lemma label_offset_app l1 s l2 :
    asm_ok (asm_env (l1 ++ ASM_Label s :: l2)) →
    label_offset (l1 ++ ASM_Label s :: l2) s = asm_words l1.
  Proof.
    rewrite /label_offset /asm_env asm_env_aux_app.
    destruct (asm_env_aux l1 0 []) as [env1|msg]; cbn; [|by intros []].
    destruct (asm_lookup s env1); [by intros []|].
    destruct (asm_env_aux l2 _ _) as [env'|msg] eqn:Henv; [|by intros []]. intros _.
    erewrite asm_env_aux_lookup; [done|done|]. cbn. by rewrite String.eqb_refl.
  Qed.

  Lemma assemble_block_check_ok P :
    asm_ok (assemble_block_check P) →
    asm_ok (asm_env (concat P)) ∧
    ∃ env, assemble_blocks P env 0 = Ok (assemble_block P).
  Proof.
    rewrite /assemble_block /assemble_block_check.
    destruct (asm_symbols_check (concat P)); cbn; [|by intros []].
    destruct (asm_env (concat P)) as [env|]; cbn; [|by intros []].
    destruct (assemble_blocks P env 0) eqn:HP; cbn; [|by intros []].
    intros _. split; [done|]. by exists env.
  Qed.

  (*** Assembly checks. *)
  (** Proves [asm_ok r] for a closed [r], or fails with the assembler's
      error message. Usage, for each assembled program:
      ```
      Lemma xxx_assembles : asm_ok (assemble_block_check xxx_asm).
      Proof. asm_check. Qed.
      ```
      Parameters of the code (registers, offsets) can be universally
      quantified: they do not affect labels. *)
  Ltac asm_check :=
    intros;
    vm_compute;
    lazymatch goal with
    | |- True => exact I
    | |- asm_error ?msg => fail 0 "assembler error:" msg
    | |- ?g => fail 0 "asm_check: unexpected goal" g
    end.

  (*** Notations for ASM language *)
  Declare Scope Asm_scope.
  Delimit Scope Asm_scope with asm.

  (** The language introduces a number of coercions *)
  Notation "e1 + e2" := (Asm_plus e1 e2) : Asm_scope .
  Notation "e1 - e2" := (Asm_minus e1 e2) : Asm_scope .
  Definition asmexprz : Z → asm_expr%type := (fun z => Asm_z z).
  Coercion asmexprz : Z >-> asm_expr.
  Definition asmexprlbl : string → asm_expr%type := (fun s => Asm_lbl s).
  Coercion asmexprlbl : string >-> asm_expr.
  Definition asmz : Z → asm_arg := (fun z => inl (Asm_z z)).
  Coercion asmz : Z >-> asm_arg.
  Definition asms : string → asm_arg := (fun s => inl (Asm_lbl s)).
  Coercion asms : string >-> asm_arg.
  Definition asmi : asm_instr → asm_code%type := ASM_Instr.
  Coercion asmi : asm_instr >-> asm_code.
  Definition asmr : RegName → asm_arg := inr.
  Coercion asmr : RegName >-> asm_arg.
  Definition asme : asm_expr → asm_arg := inl.
  Coercion asme : asm_expr >-> asm_arg.

  Definition jmp r := (ASM_Instr (Jmp r)).
  (** Conditional jumps by [off] on a comparison of [r1] and [r2]; [jgt]
      and [jge] swap the operands of [jlt] and [jle]; [jnez off r] and
      [jeqz off r] compare [r] with 0. *)
  Definition jeq off r1 r2 := (ASM_Instr (Jeq off r1 r2)).
  Definition jne off r1 r2 := (ASM_Instr (Jne off r1 r2)).
  Definition jlt off r1 r2 := (ASM_Instr (Jlt off r1 r2)).
  Definition jle off r1 r2 := (ASM_Instr (Jle off r1 r2)).
  Definition jgt off r1 r2 := (ASM_Instr (Jlt off r2 r1)).
  Definition jge off r1 r2 := (ASM_Instr (Jle off r2 r1)).
  Definition jnez off (r : RegName) := (ASM_Instr (Jne off (asmr r) (asmz 0))).
  Definition jeqz off (r : RegName) := (ASM_Instr (Jeq off (asmr r) (asmz 0))).
  Definition jalr rdst rsrc := (ASM_Instr (Jalr rdst rsrc)).

  Definition mov dst src  := (ASM_Instr (Mov dst src)).
  (** Offsets are signed displacements measured in address units. Label expressions use
      the same instruction-relative resolution as the other immediates. *)
  Definition load_imm dst src imm := ASM_Instr (CLoad dst src imm).
  Definition store_imm dst src imm := ASM_Instr (Store dst src imm).
  Definition load dst src := load_imm dst src (Asm_z 0).
  Definition store dst src := store_imm dst src (Asm_z 0).
  Definition lt dst r1 r2 := (ASM_Instr (Lt dst r1 r2)).
  Definition le dst r1 r2 := (ASM_Instr (Le dst r1 r2)).
  Definition add dst r1 r2 := (ASM_Instr (Add dst r1 r2)).
  Definition sub dst r1 r2 := (ASM_Instr (Sub dst r1 r2)).
  Definition mul dst r1 r2 := (ASM_Instr (Mul dst r1 r2)).
  Definition land dst r1 r2 := (ASM_Instr (LAnd dst r1 r2)).
  Definition lor dst r1 r2 := (ASM_Instr (LOr dst r1 r2)).
  Definition lshiftl dst r1 r2 := (ASM_Instr (LShiftL dst r1 r2)).
  Definition lshiftr dst r1 r2 := (ASM_Instr (LShiftR dst r1 r2)).
  Definition lea dst src off := (ASM_Instr (Lea dst src off)).
  Definition seta dst src addr := (ASM_Instr (SetA dst src addr)).
  Definition restrict dst src perm := (ASM_Instr (Restrict dst src perm)).
  Definition subseg dst src b e := (ASM_Instr (Subseg dst src b e)).
  Definition getb dst src := (ASM_Instr (GetB dst src)).
  Definition gete dst src := (ASM_Instr (GetE dst src)).
  Definition getlen dst src := (ASM_Instr (GetLen dst src)).
  Definition geta dst src := (ASM_Instr (GetA dst src)).
  Definition getp dst src := (ASM_Instr (GetP dst src)).
  Definition getl dst src := (ASM_Instr (GetL dst src)).
  Definition gettag dst src := (ASM_Instr (GetTag dst src)).
  Definition cleartag dst src := (ASM_Instr (ClearTag dst src)).
  (** [auipcc dst imm]: [dst] receives the PC with its address offset by
      [imm]. Label expressions resolve as the other immediates. *)
  Definition auipcc dst imm := (ASM_Instr (Auipcc dst imm)).
  Definition getwtype dst src := (ASM_Instr (GetWType dst src)).
  Definition getotype dst src := (ASM_Instr (GetOType dst src)).
  Definition seal dst r1 r2 := (ASM_Instr (Seal dst r1 r2)).
  Definition unseal dst r1 r2 := (ASM_Instr (UnSeal dst r1 r2)).
  (** [specialrw dst sr src] swaps [src] into the system register [sr] and
      its old value into [dst]. The source [cnull] does not write [sr], and
      the destination [cnull] drops the old value. *)
  Definition specialrw dst sr src := (ASM_Instr (SpecialRW dst sr src)).
  (** [readsr dst sr]: [dst] receives [sr], which is unchanged. *)
  Definition readsr dst sr := specialrw dst sr (asmr cnull).
  (** [writesr sr src]: [sr] receives [src], legalised. *)
  Definition writesr sr (src : RegName) := specialrw cnull sr (asmr src).
  (** The CSR forms. [csrw sr src] also takes an immediate; with the source
      [cnull] it does not write [sr]: write the immediate [0] instead. *)
  Definition csrr dst sr := readsr dst sr.
  Definition csrw sr src := specialrw cnull sr src.
  (** [setmie b]: the MIE bit of mstatus receives [b]. *)
  Definition setmie b := (ASM_Instr (SetMIE b)).
  (** [csrsi sr mask] and [csrci sr mask] set and clear the bits [mask] of
      [sr]. Only [csrsi mstatus 0x8] and [csrci mstatus 0x8], which enable and
      disable interrupts, assemble; any other operand is an assembler error. *)
  Definition csrsi sr mask := (ASM_Instr (CsrMIE InterruptEnabled sr mask)).
  Definition csrci sr mask := (ASM_Instr (CsrMIE InterruptDisabled sr mask)).
  (** [mret]: returns from an exception (see [Mret]). It shadows stdpp's
      monadic [mret] where this module is imported. *)
  Definition mret := (ASM_Instr Mret).
  Definition fail:= (ASM_Instr Fail).
  Definition halt:= (ASM_Instr Halt).

  Definition ret:= (ASM_Instr (Jalr cnull cra)).

  Notation "# s" := (ASM_Label s) (at level 50).
  Notation "#@ s" := (ASM_Symbol s) (at level 50).
  (** [macro: [ c1; …; cn ]] is a local block: the labels defined in it are
      visible only inside it. [macro: ( l )] takes any list expression. *)
  Notation "'macro:' [ x ; .. ; y ]" := ([ASM_Local (cons x .. (cons y nil) ..)])
    (at level 0, x at level 200, y at level 200).
  Notation "'macro:' ( l )" := ([ASM_Local l]) (at level 0, l at level 200).

End Asm_Griotte.
