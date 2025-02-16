From stdpp Require Export strings gmap.
From cap_machine Require Export -(coercions) addr_reg machine_base.

Module Asm_Cerise.

  Inductive asm_expr : Type :=
  | Asm_lbl (s : string)
  | Asm_z (z : Z)
  | Asm_plus (e1 e2 : asm_expr)
  | Asm_minus (e1 e2 : asm_expr).

  Inductive asm_instr: Type :=
  | Jmp (rimm: asm_expr + RegName)
  | Jnz (rimm : asm_expr + RegName) (rcond: RegName)
  | Jalr (rdst: RegName) (rsrc: RegName)
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

  Definition eval_asm_code (l: list asm_code) : (nat * nat * gmap string nat) :=
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

  Fixpoint eval_asm_expr (expr : asm_expr) (env : gmap string nat) : option Z :=
    match expr with
    | Asm_lbl lbl => z ← env !! lbl; Some (Z.of_nat z)
    | Asm_z z => Some z
    | Asm_plus e1 e2 =>
        z1 ← (eval_asm_expr e1 env);
        z2 ← (eval_asm_expr e2 env);
        Some (z1 + z2)%Z
    | Asm_minus e1 e2 =>
        z1 ← (eval_asm_expr e1 env);
        z2 ← (eval_asm_expr e2 env);
        Some (z1 - z2)%Z
    end.

  Definition assemble_arg (arg : asm_expr + RegName) (env : gmap string nat)
    : option (Z+RegName) :=
    match arg with
    | inr r => Some (inr r)
    | inl expr => z ← eval_asm_expr expr env ; Some (inl z)
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

  Definition assemble (l : list asm_code) : list instr :=
    match assemble_aux l (eval_asm_code l).2 with
    | Some l' => l'
    | None => []
    end.

  Definition revert_regs (r : RegName) : RegName :=
    match r with
    | PC => PC
    | addr_reg.R n _ =>
        match n with
        | 0 => r_t0
        | 1 => r_t1
        | 2 => r_t2
        | 3 => r_t3
        | 4 => r_t4
        | 5 => r_t5
        | 6 => r_t6
        | 7 => r_t7
        | 8 => r_t8
        | 9 => r_t9
        | 10 => r_t10
        | 11 => r_t11
        | 12 => r_t12
        | 13 => r_t13
        | 14 => r_t14
        | 15 => r_t15
        | 16 => r_t16
        | 17 => r_t17
        | 18 => r_t18
        | 19 => r_t19
        | 20 => r_t20
        | 21 => r_t21
        | 22 => r_t22
        | 23 => r_t23
        | 24 => r_t24
        | 25 => r_t25
        | 26 => r_t26
        | 27 => r_t27
        | 28 => r_t28
        | 29 => r_t29
        | 30 => r_t30
        | 31 => r_t31
        | _ => r_t0
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

  Declare Scope Asm_scope.
  Delimit Scope Asm_scope with asm.

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

End Asm_Cerise.
