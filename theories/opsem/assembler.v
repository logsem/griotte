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

      If you use labels in a macro that is supposed to be re-used,
      resolve them in the macro to avoid label conflicts.
      So, first define your asm macro with labels:
      `xxx_asm_pre r`, then compute its label environment (with
      [vm_compute]: it contains no register) and resolve the labels with
      ```
      Definition xxx_asm_env :=
        Eval vm_compute in (compute_asm_code_env (xxx_asm_pre cnull)).2.
      Definition xxx_asm r :=
        Eval compute in (resolve_labels_macros (xxx_asm_pre r) xxx_asm_env).
      ```
      and check `xxx_asm_pre r` with [assemble_check].
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
  | Jnz (rimm : asm_arg) (rcond: RegName)
  | Jalr (rdst: RegName) (rsrc: RegName)
  | Mov (dst: RegName) (src: asm_arg)
  | CLoad (dst src: RegName) (imm: asm_expr)
  | Store (dst: RegName) (src: asm_arg) (imm: asm_expr)
  | Lt (dst: RegName) (r1 r2: asm_arg)
  | Add (dst: RegName) (r1 r2: asm_arg)
  | Sub (dst: RegName) (r1 r2: asm_arg)
  | Mul (dst: RegName) (r1 r2: asm_arg)
  | LAnd (dst: RegName) (r1 r2: asm_arg)
  | LOr (dst: RegName) (r1 r2: asm_arg)
  | LShiftL (dst: RegName) (r1 r2: asm_arg)
  | LShiftR (dst: RegName) (r1 r2: asm_arg)
  | Lea (dst: RegName) (r: asm_arg)
  | Restrict (dst: RegName) (r: asm_arg)
  | Subseg (dst: RegName) (r1 r2: asm_arg)
  | GetB (dst r: RegName)
  | GetE (dst r: RegName)
  | GetA (dst r: RegName)
  | GetP (dst r: RegName)
  | GetL (dst r: RegName)
  | GetWType (dst r : RegName)
  | GetOType (dst r: RegName)
  | Seal (dst : RegName) (r1 r2: RegName)
  | UnSeal (dst : RegName) (r1 r2: RegName)
  | ReadSR (dst: RegName) (src: SRegName)
  | WriteSR (dst: SRegName) (src: RegName)
  | Fail
  | Halt
  | GetTag (dst src: RegName)
  | ClearTag (dst src: RegName)
  | Auipcc (dst: RegName) (imm: asm_expr).

  (** [ASM_Symbol s] names a data word reserved by the loader at the current
      address: it occupies one word but emits no instruction. Symbols may only
      form a data prefix before the code or a data suffix after it (see
      [asm_symbols_check]), so that the assembled instructions stay
      contiguous. *)
  Inductive asm_code : Type :=
  | ASM_Label (s : string)
  | ASM_Symbol (s : string)
  | ASM_Instr (w : asm_instr).

  (*** ASM environment *)

  (** Computes the environment of the program.
      The environment consists on:
      - the current line in the assembly code (includes the labels);
      - the current line of the labels in the assembly code (excludes the labels);
      - a map which, for each labels, associates its offset in the code without labels (so after assembling).
   *)
  Definition compute_asm_code_env (l: list asm_code) : (nat * nat * gmap string nat) :=
    foldl
      (fun (acc : (nat * nat * gmap string nat)) (a : asm_code)  =>
         let '(n,nlbl,env) := acc in
         match a with
         | ASM_Label string => (n+1,nlbl+1, <[string := n-nlbl]> env)
         | ASM_Symbol string => (n+1,nlbl, <[string := n-nlbl]> env)
         | ASM_Instr _ => (n+1,nlbl,env)
         end
      )
      (0, 0, ∅)
      l
  .

  (** Computes the ASM expression with the current environment.
      Because jumps are relative, we keep track of the current line with [current_n].
   *)
  Fixpoint eval_asm_expr (expr : asm_expr) (env : gmap string nat) (current_n : nat) : option Z :=
    match expr with
    | Asm_lbl lbl => z ← env !! lbl; Some ( (Z.of_nat z) - (Z.of_nat current_n) )%Z
    | Asm_z z => Some z
    | Asm_plus e1 e2 =>
        z1 ← (eval_asm_expr e1 env current_n);
        z2 ← (eval_asm_expr e2 env current_n);
        Some (z1 + z2)%Z
    | Asm_minus e1 e2 =>
        z1 ← (eval_asm_expr e1 env current_n);
        z2 ← (eval_asm_expr e2 env current_n);
        Some (z1 - z2)%Z
    end.

  (*** Label solver. *)
  (** The label solver simply resolves and eliminate the labels.
      It can be used to pre-assemble a block with labels,
      and avoid label conflict when used outside.
   *)

  Definition resolve_labels_arg
    (arg : asm_expr + RegName)
    (env : gmap string nat)
    (current_n : nat)
    : option (asm_expr+RegName) :=
    match arg with
    | inr r => Some (inr r)
    | inl expr => z ← eval_asm_expr expr env current_n ; Some (inl (Asm_z z))
    end.

  Definition resolve_labels_instr (i: asm_instr) (env : gmap string nat) (current_n : nat) : option asm_instr :=
    match i with
    | Jmp rimm =>
        rimm' ← resolve_labels_arg rimm env current_n;
        Some (Jmp rimm')
    | Jnz rimm rcond =>
        rimm' ← resolve_labels_arg rimm env current_n;
        Some (Jnz rimm' rcond)
    | Jalr rdst rsrc =>
        Some (Jalr rdst rsrc)
    | Mov dst src  =>
        src ← resolve_labels_arg src env current_n;
        Some (Mov dst src)
    | CLoad dst src imm =>
        off ← eval_asm_expr imm env current_n;
        Some (CLoad dst src (Asm_z off))
    | Store dst src imm =>
        src ← resolve_labels_arg src env current_n;
        off ← eval_asm_expr imm env current_n;
        Some (Store dst src (Asm_z off))
    | Lt dst r1 r2 =>
        w1 ← resolve_labels_arg r1 env current_n;
        w2 ← resolve_labels_arg r2 env current_n;
        Some (Lt dst w1 w2)
    | Add dst r1 r2 =>
        w1 ← resolve_labels_arg r1 env current_n;
        w2 ← resolve_labels_arg r2 env current_n;
        Some (Add dst w1 w2)
    | Sub dst r1 r2 =>
        w1 ← resolve_labels_arg r1 env current_n;
        w2 ← resolve_labels_arg r2 env current_n;
        Some (Sub dst w1 w2)
    | Mul dst r1 r2 =>
        w1 ← resolve_labels_arg r1 env current_n;
        w2 ← resolve_labels_arg r2 env current_n;
        Some (Mul dst w1 w2)
    | LAnd dst r1 r2 =>
        w1 ← resolve_labels_arg r1 env current_n;
        w2 ← resolve_labels_arg r2 env current_n;
        Some (LAnd dst w1 w2)
    | LOr dst r1 r2 =>
        w1 ← resolve_labels_arg r1 env current_n;
        w2 ← resolve_labels_arg r2 env current_n;
        Some (LOr dst w1 w2)
    | LShiftL dst r1 r2 =>
        w1 ← resolve_labels_arg r1 env current_n;
        w2 ← resolve_labels_arg r2 env current_n;
        Some (LShiftL dst w1 w2)
    | LShiftR dst r1 r2 =>
        w1 ← resolve_labels_arg r1 env current_n;
        w2 ← resolve_labels_arg r2 env current_n;
        Some (LShiftR dst w1 w2)
    | Lea dst r =>
        w ← resolve_labels_arg r env current_n;
        Some (Lea dst w)
    | Restrict dst r =>
        w ← resolve_labels_arg r env current_n;
        Some (Restrict dst w)
    | Subseg dst r1 r2 =>
        w1 ← resolve_labels_arg r1 env current_n;
        w2 ← resolve_labels_arg r2 env current_n;
        Some (Subseg dst w1 w2)
    | GetB dst src =>
        Some (GetB dst src)
    | GetE dst src =>
        Some (GetE dst src)
    | GetA dst src =>
        Some (GetA dst src)
    | GetP dst src =>
        Some (GetP dst src)
    | GetL dst src =>
        Some (GetL dst src)
    | GetTag dst src =>
        Some (GetTag dst src)
    | ClearTag dst src =>
        Some (ClearTag dst src)
    | GetWType dst src =>
        Some (GetWType dst src)
    | GetOType dst src =>
        Some (GetOType dst src)
    | Seal dst r1 r2 =>
        Some (Seal dst r1 r2)
    | UnSeal dst r1 r2 =>
        Some (UnSeal dst r1 r2)
    | ReadSR dst src =>
        Some (ReadSR dst src)
    | WriteSR dst src =>
        Some (WriteSR dst src)
    | Fail=>
        Some (Fail)
    | Halt=>
        Some (Halt)
    | Auipcc dst imm =>
        off ← eval_asm_expr imm env current_n;
        Some (Auipcc dst (Asm_z off))
    end.

  Definition resolve_labels_aux
    (l: list asm_code) (env : gmap string nat) (init_n : nat) : option ( (list asm_code) * nat) :=
    foldl
      (fun (acc : option ( (list asm_code) * nat)) (a : asm_code)  =>
         match a with
         | ASM_Label string => acc
         | ASM_Symbol string =>
             '(generated_code,current_n) ← acc;
             Some (generated_code, current_n + 1)
         | ASM_Instr i =>
             '(generated_code,current_n) ← acc;
             i' ← resolve_labels_instr i env current_n;
             let next_current := current_n + 1 in
             Some ((ASM_Instr i')::generated_code, next_current )
         end
      )
      (Some ([], init_n))
      l
  .

  (** Label solver for a macros, providing the environment.
      Useful if computing the label with [compute] is too expensive. *)
  Definition resolve_labels_macros (l : list asm_code) (env : gmap string nat) : list asm_code :=
    let resolved_labels := resolve_labels_aux l env 0 in
    match resolved_labels with
    | Some (asm_code, _) => reverse asm_code
    | None => []
    end.

  (** Label solver of a plain code. *)
  Definition resolve_labels (l : list asm_code) : list asm_code :=
    let env := (compute_asm_code_env l).2 in
    resolve_labels_macros l env.

  Definition resolve_labels_block_aux
    (l : list (list asm_code) ) (env : gmap string nat) : option ((list (list asm_code)) * nat) :=
    foldl
      ( fun (acc : option ((list (list asm_code)) * nat)) (prog : list asm_code) =>
          '(generated_code,current_n) ← acc;
          '(prog',next_current) ← resolve_labels_aux prog env current_n;
          Some ( (reverse prog')::generated_code, next_current)
      )
      (Some ([], 0))
      l.

  (** Label solver of a list of code. *)
  Definition resolve_labels_block
    (l : list (list asm_code) ) (env : gmap string nat) : (list (list asm_code)) :=
    match resolve_labels_block_aux l env with
    | Some (asm_codes, _) => reverse asm_codes
    | None => []
    end.

  (*** Assembler results. *)
  (** The result of assembling: the value, or an error message naming the
      offending label, symbol or instruction. *)
  Inductive asm_result (A : Type) : Type :=
  | Ok (a : A)
  | Err (msg : string).
  Arguments Ok {A} a.
  Arguments Err {A} msg.

  Global Instance asm_result_ret : MRet asm_result := λ A a, Ok a.
  Global Instance asm_result_bind : MBind asm_result :=
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

  (** The offset of each label and symbol in the code without labels.
      A name defined twice is an error. *)
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
    end.

  Definition asm_symbols_check (l : list asm_code) : asm_result unit :=
    asm_symbols_check_aux false None l.

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
    | Jnz rimm rcond =>
        rimm' ← assemble_arg rimm env n;
        Ok (machine_instructions.Jnz rimm' rcond)
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
    | Lea dst r =>
        w ← assemble_arg r env n;
        Ok (machine_instructions.Lea dst w)
    | Restrict dst r =>
        w ← assemble_arg r env n;
        Ok (machine_instructions.Restrict dst w)
    | Subseg dst r1 r2 =>
        w1 ← assemble_arg r1 env n;
        w2 ← assemble_arg r2 env n;
        Ok (machine_instructions.Subseg dst w1 w2)
    | GetB dst src =>
        Ok (machine_instructions.GetB dst src)
    | GetE dst src =>
        Ok (machine_instructions.GetE dst src)
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
    | ReadSR dst src =>
        Ok (machine_instructions.ReadSR dst src)
    | WriteSR dst src =>
        Ok (machine_instructions.WriteSR dst src)
    | Fail=>
        Ok (machine_instructions.Fail)
    | Halt=>
        Ok (machine_instructions.Halt)
    | Auipcc dst imm =>
        off ← asm_eval imm env n;
        Ok (machine_instructions.Auipcc dst off)
    end.

  (** Assembles [l], whose first word is at offset [n]. *)
  Fixpoint assemble_code (l : list asm_code) (env : asm_env_map) (n : nat)
    : asm_result (list instr) :=
    match l with
    | [] => Ok []
    | ASM_Label _ :: l => assemble_code l env n
    | ASM_Symbol _ :: l => assemble_code l env (S n)
    | ASM_Instr i :: l =>
        i' ← assemble_instr i env n;
        l' ← assemble_code l env (S n);
        Ok (i' :: l')
    end.

  (** The number of words of [l]: its instructions and symbols. *)
  Fixpoint asm_words (l : list asm_code) : nat :=
    match l with
    | [] => 0
    | ASM_Label _ :: l => asm_words l
    | _ :: l => S (asm_words l)
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

  (** Checked assembler for plain code, given its environment [env] (as
      computed by [asm_env]). *)
  Definition assemble_env_check (env : asm_result (asm_env_map)) (l : list asm_code)
    : asm_result (list instr) :=
    asm_symbols_check l;;
    env ← env;
    assemble_code l env 0.

  (** Checked assembler for a list of blocks, given the environment [env] of
      their concatenation. Each block keeps its own list of instructions, so
      that the blocks can be specified separately. *)
  Definition assemble_block_env_check
    (env : asm_result (asm_env_map)) (l : list (list asm_code))
    : asm_result (list (list instr)) :=
    asm_symbols_check (concat l);;
    env ← env;
    assemble_blocks l env 0.

  Definition assemble_check (l : list asm_code) : asm_result (list instr) :=
    assemble_env_check (asm_env l) l.

  Definition assemble_block_check (l : list (list asm_code)) : asm_result (list (list instr)) :=
    assemble_block_env_check (asm_env (concat l)) l.

  (** Assemblers returning the code, [[]] on an error. Each assembled
      definition comes with a check (see [asm_check]) that fails on an
      error. *)
  Definition assemble (l : list asm_code) : list instr :=
    asm_get [] (assemble_check l).

  Definition assemble_block (l : list (list asm_code)) : list (list instr) :=
    asm_get [] (assemble_block_check l).

  Definition assemble_env (env : asm_result (asm_env_map)) (l : list asm_code)
    : list instr :=
    asm_get [] (assemble_env_check env l).

  Definition assemble_block_env (env : asm_result (asm_env_map)) (l : list (list asm_code))
    : list (list instr) :=
    asm_get [] (assemble_block_env_check env l).

  (*** Assembly checks. *)
  (** [asm_ok r] holds when [r] is not an error; on an error it reduces to
      the uninhabited [asm_error msg], so that [asm_check] reports [msg]. *)
  Inductive asm_error (msg : string) : Prop := .

  Definition asm_ok {A} (r : asm_result A) : Prop :=
    match r with
    | Ok _ => True
    | Err msg => asm_error msg
    end.

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
  Definition jnz rimm rcond := (ASM_Instr (Jnz rimm rcond)).
  Definition jalr rdst rsrc := (ASM_Instr (Jalr rdst rsrc)).

  Definition mov dst src  := (ASM_Instr (Mov dst src)).
  (** Offsets are signed displacements measured in address units. Label expressions use
      the same instruction-relative resolution as the other immediates. *)
  Definition load_imm dst src imm := ASM_Instr (CLoad dst src imm).
  Definition store_imm dst src imm := ASM_Instr (Store dst src imm).
  Definition load dst src := load_imm dst src (Asm_z 0).
  Definition store dst src := store_imm dst src (Asm_z 0).
  Definition lt dst r1 r2 := (ASM_Instr (Lt dst r1 r2)).
  Definition add dst r1 r2 := (ASM_Instr (Add dst r1 r2)).
  Definition sub dst r1 r2 := (ASM_Instr (Sub dst r1 r2)).
  Definition mul dst r1 r2 := (ASM_Instr (Mul dst r1 r2)).
  Definition land dst r1 r2 := (ASM_Instr (LAnd dst r1 r2)).
  Definition lor dst r1 r2 := (ASM_Instr (LOr dst r1 r2)).
  Definition lshiftl dst r1 r2 := (ASM_Instr (LShiftL dst r1 r2)).
  Definition lshiftr dst r1 r2 := (ASM_Instr (LShiftR dst r1 r2)).
  Definition lea dst r := (ASM_Instr (Lea dst r)).
  Definition restrict dst r := (ASM_Instr (Restrict dst r)).
  Definition subseg dst r1 r2 := (ASM_Instr (Subseg dst r1 r2)).
  Definition getb dst src := (ASM_Instr (GetB dst src)).
  Definition gete dst src := (ASM_Instr (GetE dst src)).
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
  Definition readsr dst src := (ASM_Instr (ReadSR dst src)).
  Definition writesr dst src := (ASM_Instr (WriteSR dst src)).
  Definition fail:= (ASM_Instr Fail).
  Definition halt:= (ASM_Instr Halt).

  Definition ret:= (ASM_Instr (Jalr cnull cra)).

  Notation "# s" := (ASM_Label s) (at level 50).
  Notation "#@ s" := (ASM_Symbol s) (at level 50).

End Asm_Griotte.
