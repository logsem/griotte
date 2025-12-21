From stdpp Require Export strings gmap.
From cap_machine Require Export -(coercions) addr_reg machine_base.

Module Asm_Griotte.

  (** To use the assembler, import `Asm_Griotte`.
      Define the assembly code: `xxx_asm : list asm_code`,
      and assemble it with
      ```
      Definition assembled_xxx' := Eval vm_compute in (assemble xxx_asm).
      Definition assembled_xxx  := Eval cbv in (revert_regs_code assembled_xxx').
      ```

      If your code is supposed to be defined by blocks,
      ie, `xxx_asm := xxx1_asm ++ xxx2_asm`,
      define instead `xxx_asm := [xxx1_asm; xxx2_asm]`
      and assemble it by blocks:
      ```
      Definition assembled_xxx' := Eval vm_compute in (assemble_block xxx_asm).
      Definition assembled_xxx  := Eval cbv in (revert_regs_code_block assembled_xxx').
      Definition xxx_instrs : list Word := concat (encodeInstrsW <$> assembled_xxx).
      ```

      If you use labels in a macro that is supposed to be re-used,
      use [resolve_labels] to avoid label conflict.
      So, first define your asm macro with labels:
      `xxx_asm_pre`, then resolve the labels with
      ```
      Definition xxx_asm := Eval vcompute in (resolve_labels xxx_asm_pre).
      ```
      Finally, [vm_compute] defies Opaque, so if your code is parameterised with
      register name, use [compute] instead.
   *)

  (*** Assembly Language with Labels *)
  Inductive asm_expr : Type :=
  | Asm_lbl (s : string)
  | Asm_z (z : Z)
  | Asm_plus (e1 e2 : asm_expr)
  | Asm_minus (e1 e2 : asm_expr).

  Inductive asm_instr: Type :=
  | Jmp (rimm: asm_expr + RegName)
  | Jnz (rimm : asm_expr + RegName) (rcond: RegName)
  | Jalr (rdst: RegName) (rsrc: RegName)
  | JmpCap (rsrc: RegName) (* XXX: temporary, remove when support for cnull *)
  | Mov (dst: RegName) (src: asm_expr + RegName)
  | Load (dst src: RegName)
  | Store (dst: RegName) (src: asm_expr + RegName)
  | Lt (dst: RegName) (r1 r2: asm_expr + RegName)
  | Add (dst: RegName) (r1 r2: asm_expr + RegName)
  | Sub (dst: RegName) (r1 r2: asm_expr + RegName)
  | Mul (dst: RegName) (r1 r2: asm_expr + RegName)
  | LAnd (dst: RegName) (r1 r2: asm_expr + RegName)
  | LOr (dst: RegName) (r1 r2: asm_expr + RegName)
  | LShiftL (dst: RegName) (r1 r2: asm_expr + RegName)
  | LShiftR (dst: RegName) (r1 r2: asm_expr + RegName)
  | Lea (dst: RegName) (r: asm_expr + RegName)
  | Restrict (dst: RegName) (r: asm_expr + RegName)
  | Subseg (dst: RegName) (r1 r2: asm_expr + RegName)
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
  | Halt.

  Inductive asm_code : Type :=
  | ASM_Label (s : string)
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
    | JmpCap rsrc =>
        Some (JmpCap rsrc)
    | Mov dst src  =>
        src ← resolve_labels_arg src env current_n;
        Some (Mov dst src)
    | Load dst src =>
        Some (Load dst src)
    | Store dst src =>
        src ← resolve_labels_arg src env current_n;
        Some (Store dst src)
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
    end.

  Definition resolve_labels_aux
    (l: list asm_code) (env : gmap string nat) (init_n : nat) : option ( (list asm_code) * nat) :=
    foldl
      (fun (acc : option ( (list asm_code) * nat)) (a : asm_code)  =>
         match a with
         | ASM_Label string => acc
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
          '(prog',_) ← resolve_labels_aux prog env current_n;
          let next_current : nat := current_n + (length prog') in
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

  (*** Code assembler. *)
  Definition assemble_arg (arg : asm_expr + RegName) (env : gmap string nat)
    : option (Z+RegName) :=
    match arg with
    | inr r => Some (inr r)
    | inl expr => z ← eval_asm_expr expr env 0 ; Some (inl z)
    end.

  Definition assemble_instr (i: asm_instr) (env : gmap string nat) : option instr :=
    match i with
    | Jmp rimm =>
        rimm' ← assemble_arg rimm env;
        Some (machine_base.Jmp rimm')
    | Jnz rimm rcond =>
        rimm' ← assemble_arg rimm env;
        Some (machine_base.Jnz rimm' rcond)
    | Jalr rdst rsrc =>
        Some (machine_base.Jalr rdst rsrc)
    | JmpCap rsrc =>
        Some (machine_base.JmpCap rsrc)
    | Mov dst src  =>
        src ← assemble_arg src env;
        Some (machine_base.Mov dst src)
    | Load dst src =>
        Some (machine_base.Load dst src)
    | Store dst src =>
        src ← assemble_arg src env;
        Some (machine_base.Store dst src)
    | Lt dst r1 r2 =>
        w1 ← assemble_arg r1 env;
        w2 ← assemble_arg r2 env;
        Some (machine_base.Lt dst w1 w2)
    | Add dst r1 r2 =>
        w1 ← assemble_arg r1 env;
        w2 ← assemble_arg r2 env;
        Some (machine_base.Add dst w1 w2)
    | Sub dst r1 r2 =>
        w1 ← assemble_arg r1 env;
        w2 ← assemble_arg r2 env;
        Some (machine_base.Sub dst w1 w2)
    | Mul dst r1 r2 =>
        w1 ← assemble_arg r1 env;
        w2 ← assemble_arg r2 env;
        Some (machine_base.Mul dst w1 w2)
    | LAnd dst r1 r2 =>
        w1 ← assemble_arg r1 env;
        w2 ← assemble_arg r2 env;
        Some (machine_base.LAnd dst w1 w2)
    | LOr dst r1 r2 =>
        w1 ← assemble_arg r1 env;
        w2 ← assemble_arg r2 env;
        Some (machine_base.LOr dst w1 w2)
    | LShiftL dst r1 r2 =>
        w1 ← assemble_arg r1 env;
        w2 ← assemble_arg r2 env;
        Some (machine_base.LShiftL dst w1 w2)
    | LShiftR dst r1 r2 =>
        w1 ← assemble_arg r1 env;
        w2 ← assemble_arg r2 env;
        Some (machine_base.LShiftR dst w1 w2)
    | Lea dst r =>
        w ← assemble_arg r env;
        Some (machine_base.Lea dst w)
    | Restrict dst r =>
        w ← assemble_arg r env;
        Some (machine_base.Restrict dst w)
    | Subseg dst r1 r2 =>
        w1 ← assemble_arg r1 env;
        w2 ← assemble_arg r2 env;
        Some (machine_base.Subseg dst w1 w2)
    | GetB dst src =>
        Some (machine_base.GetB dst src)
    | GetE dst src =>
        Some (machine_base.GetE dst src)
    | GetA dst src =>
        Some (machine_base.GetA dst src)
    | GetP dst src =>
        Some (machine_base.GetP dst src)
    | GetL dst src =>
        Some (machine_base.GetL dst src)
    | GetWType dst src =>
        Some (machine_base.GetWType dst src)
    | GetOType dst src =>
        Some (machine_base.GetOType dst src)
    | Seal dst r1 r2 =>
        Some (machine_base.Seal dst r1 r2)
    | UnSeal dst r1 r2 =>
        Some (machine_base.UnSeal dst r1 r2)
    | ReadSR dst src =>
        Some (machine_base.ReadSR dst src)
    | WriteSR dst src =>
        Some (machine_base.WriteSR dst src)
    | Fail=>
        Some (machine_base.Fail)
    | Halt=>
        Some (machine_base.Halt)
    end.

  Definition assemble_aux (l: list asm_code) (env : gmap string nat) : option (list instr) :=
    foldr
      (fun (a : asm_code) (acc : option (list instr)) =>
         match a with
         | ASM_Label string => acc
         | ASM_Instr i =>
             i' ← assemble_instr i env ;
             acc' ← acc;
             Some (i'::acc')
         end
      )
      (Some [])
      l
  .

  (** Assembler for plain code. *)
  Definition assemble (l : list asm_code) : list instr :=
    default [] (assemble_aux l (compute_asm_code_env l).2).

  (** Assembler for a list of code.
      Used to avoid the original code written with blocks (ie. including macros)
      to be concatenated and forget the blocks (which forbids modularity).
   *)
  Definition assemble_block (l : list (list asm_code)) : list (list instr) :=
    let full_code := concat l in
    let env := (compute_asm_code_env full_code).2 in
    let no_labels_l := resolve_labels_block l env in
    (fun prog => default [] (assemble_aux prog env) ) <$> no_labels_l.

  (*** Revert registers. *)
  (** It is recommended to assemble the code with [compute] when possible,
      and with [vm_compute] if [compute] is too slow.
      (See in the explanation)
      The problem is that [vm_compute] defies Rocq Opaque
      (https://github.com/rocq-prover/rocq/issues/4476).
      So, when the code is assembled with [vm_compute],
      the registers names (`csp`, `cs0`, ... ) are converted back
      into their initial definitions (`R 3 eq_refl`, ...),
      which breaks some of the automation.

      [revert_regs_code] (and [revert_regs_code_block])
      simply reverts the unfolded registers into their name.

      The downside is that it does not work well with parameters.
   *)
  Definition revert_regs (r : RegName) : RegName :=
    match r with
    | PC => PC
    | addr_reg.R n H =>
        match n with
        | 0 => cnull
        | 1 => cra
        | 2 => csp
        | 3 => cgp
        | 4 => ctp
        | 5 => ct0
        | 6 => ct1
        | 7 => ct2
        | 8 => cs0
        | 9 => cs1
        | 10 => ca0
        | 11 => ca1
        | 12 => ca2
        | 13 => ca3
        | 14 => ca4
        | 15 => ca5
        | 16 => ca6
        | 17 => ca7
        | 18 => cs2
        | 19 => cs3
        | 20 => cs4
        | 21 => cs5
        | 22 => cs6
        | 23 => cs7
        | 24 => cs8
        | 25 => cs9
        | 26 => cs10
        | 27 => cs11
        | 28 => ct3
        | 29 => ct4
        | 30 => ct5
        | 31 => ct6
        | _ => addr_reg.R n H
        end
    end.

  Definition revert_regs_arg (arg : Z+RegName) : (Z+RegName) :=
    match arg with
    | inl z => inl z
    | inr r => inr (revert_regs r)
    end.

  Definition revert_regs_instr (i : instr) : instr :=
    match i with
    | machine_base.Jmp rimm =>
        let rimm := revert_regs_arg rimm in
        (machine_base.Jmp rimm)
    | machine_base.Jnz rimm rcond =>
        let rimm := revert_regs_arg rimm in
        let rcond := revert_regs rcond in
        (machine_base.Jnz rimm rcond)
    | machine_base.Jalr rdst rsrc =>
        let rdst := revert_regs rdst in
        let rsrc := revert_regs rsrc in
        (machine_base.Jalr rdst rsrc)
    | machine_base.JmpCap rsrc =>
        let rsrc := revert_regs rsrc in
        (machine_base.JmpCap rsrc)
    | machine_base.Mov dst src  =>
        let dst := revert_regs dst in
        let src := revert_regs_arg src in
        (machine_base.Mov dst src)
    | machine_base.Load dst src =>
        let dst := revert_regs dst in
        let src := revert_regs src in
        (machine_base.Load dst src)
    | machine_base.Store dst src =>
        let dst := revert_regs dst in
        let src := revert_regs_arg src in
        (machine_base.Store dst src)
    | machine_base.Lt dst r1 r2 =>
        let dst := revert_regs dst in
        let r1 := revert_regs_arg r1 in
        let r2 := revert_regs_arg r2 in
        (machine_base.Lt dst r1 r2)
    | machine_base.Add dst r1 r2 =>
        let dst := revert_regs dst in
        let r1 := revert_regs_arg r1 in
        let r2 := revert_regs_arg r2 in
        (machine_base.Add dst r1 r2)
    | machine_base.Sub dst r1 r2 =>
        let dst := revert_regs dst in
        let r1 := revert_regs_arg r1 in
        let r2 := revert_regs_arg r2 in
        (machine_base.Sub dst r1 r2)
    | machine_base.Mul dst r1 r2 =>
        let dst := revert_regs dst in
        let r1 := revert_regs_arg r1 in
        let r2 := revert_regs_arg r2 in
        (machine_base.Mul dst r1 r2)
    | machine_base.LAnd dst r1 r2 =>
        let dst := revert_regs dst in
        let r1 := revert_regs_arg r1 in
        let r2 := revert_regs_arg r2 in
        (machine_base.LAnd dst r1 r2)
    | machine_base.LOr dst r1 r2 =>
        let dst := revert_regs dst in
        let r1 := revert_regs_arg r1 in
        let r2 := revert_regs_arg r2 in
        (machine_base.LOr dst r1 r2)
    | machine_base.LShiftL dst r1 r2 =>
        let dst := revert_regs dst in
        let r1 := revert_regs_arg r1 in
        let r2 := revert_regs_arg r2 in
        (machine_base.LShiftL dst r1 r2)
    | machine_base.LShiftR dst r1 r2 =>
        let dst := revert_regs dst in
        let r1 := revert_regs_arg r1 in
        let r2 := revert_regs_arg r2 in
        (machine_base.LShiftR dst r1 r2)
    | machine_base.Lea dst r =>
        let dst := revert_regs dst in
        let r := revert_regs_arg r in
        (machine_base.Lea dst r)
    | machine_base.Restrict dst r =>
        let dst := revert_regs dst in
        let r := revert_regs_arg r in
        (machine_base.Restrict dst r)
    | machine_base.Subseg dst r1 r2 =>
        let dst := revert_regs dst in
        let r1 := revert_regs_arg r1 in
        let r2 := revert_regs_arg r2 in
        (machine_base.Subseg dst r1 r2)
    | machine_base.GetB dst src =>
        let dst := revert_regs dst in
        let src := revert_regs src in
        (machine_base.GetB dst src)
    | machine_base.GetE dst src =>
        let dst := revert_regs dst in
        let src := revert_regs src in
        (machine_base.GetE dst src)
    | machine_base.GetA dst src =>
        let dst := revert_regs dst in
        let src := revert_regs src in
        (machine_base.GetA dst src)
    | machine_base.GetP dst src =>
        let dst := revert_regs dst in
        let src := revert_regs src in
        (machine_base.GetP dst src)
    | machine_base.GetL dst src =>
        let dst := revert_regs dst in
        let src := revert_regs src in
        (machine_base.GetL dst src)
    | machine_base.GetWType dst src =>
        let dst := revert_regs dst in
        let src := revert_regs src in
        (machine_base.GetWType dst src)
    | machine_base.GetOType dst src =>
        let dst := revert_regs dst in
        let src := revert_regs src in
        (machine_base.GetOType dst src)
    | machine_base.Seal dst r1 r2 =>
        let dst := revert_regs dst in
        let r1 := revert_regs r1 in
        let r2 := revert_regs r2 in
        (machine_base.Seal dst r1 r2)
    | machine_base.UnSeal dst r1 r2 =>
        let dst := revert_regs dst in
        let r1 := revert_regs r1 in
        let r2 := revert_regs r2 in
        (machine_base.UnSeal dst r1 r2)
    | machine_base.ReadSR dst src =>
        let dst := revert_regs dst in
        (machine_base.ReadSR dst src)
    | machine_base.WriteSR dst src =>
        let src := revert_regs src in
        (machine_base.WriteSR dst src)
    | machine_base.Fail=>
        (machine_base.Fail)
    | machine_base.Halt=>
        (machine_base.Halt)
    end.

  Definition revert_regs_code (assembled_code : list instr) : list instr :=
    fmap revert_regs_instr assembled_code.
  Definition revert_regs_code_block (assembled_code : list (list instr) ) : list (list instr) :=
    fmap revert_regs_code assembled_code.

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
  Definition asmz : Z → (asm_expr+RegName)%type := (fun z => inl (Asm_z z)).
  Coercion asmz : Z >-> sum.
  Definition asms : string → (asm_expr+RegName)%type := (fun s => inl (Asm_lbl s)).
  Coercion asms : string >-> sum.
  Definition asmi : asm_instr → asm_code%type := ASM_Instr.
  Coercion asmi : asm_instr >-> asm_code.
  Definition asmr : RegName → (asm_expr+RegName)%type := inr.
  Coercion asmr : RegName >-> sum.
  Definition asme : asm_expr → (asm_expr+RegName)%type := inl.
  Coercion asme : asm_expr >-> sum.

  Definition jmp r := (ASM_Instr (Jmp r)).
  Definition jnz rimm rcond := (ASM_Instr (Jnz rimm rcond)).
  Definition jalr rdst rsrc := (ASM_Instr (Jalr rdst rsrc)).

  Definition jmpcap rsrc := (ASM_Instr (JmpCap rsrc)). (* XXX: temporary, remove when support for cnull *)
  Definition mov dst src  := (ASM_Instr (Mov dst src)).
  Definition load dst src := (ASM_Instr (Load dst src)).
  Definition store dst src := (ASM_Instr (Store dst src)).
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
  Definition getwtype dst src := (ASM_Instr (GetWType dst src)).
  Definition getotype dst src := (ASM_Instr (GetOType dst src)).
  Definition seal dst r1 r2 := (ASM_Instr (Seal dst r1 r2)).
  Definition unseal dst r1 r2 := (ASM_Instr (UnSeal dst r1 r2)).
  Definition readsr dst src := (ASM_Instr (ReadSR dst src)).
  Definition writesr dst src := (ASM_Instr (WriteSR dst src)).
  Definition fail:= (ASM_Instr Fail).
  Definition halt:= (ASM_Instr Halt).
  Notation "# s" := (ASM_Label s) (at level 50).

End Asm_Griotte.
