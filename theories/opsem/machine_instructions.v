From griotte Require Import registers.

Inductive instr: Type :=
| Jmp (rimm: Z + RegName)
(* Conditional jumps: compare the integer views of [r1] and [r2] (signed),
   and jump by [off] relative to the PC if the comparison holds. *)
| Jeq (off : Z + RegName) (r1 r2 : Z + RegName)
| Jne (off : Z + RegName) (r1 r2 : Z + RegName)
| Jlt (off : Z + RegName) (r1 r2 : Z + RegName)
| Jle (off : Z + RegName) (r1 r2 : Z + RegName)
| Jalr (rdst: RegName) (rsrc: RegName) (* jumps to wsrc, rdst receives return cap *)
| Mov (dst: RegName) (src: Z + RegName)
| CLoad (dst src: RegName) (imm: Z)
| Store (dst: RegName) (src: Z + RegName) (imm: Z)
| Lt (dst: RegName) (r1 r2: Z + RegName)
| Le (dst: RegName) (r1 r2: Z + RegName)
| Add (dst: RegName) (r1 r2: Z + RegName)
| Sub (dst: RegName) (r1 r2: Z + RegName)
| Mul (dst: RegName) (r1 r2: Z + RegName)
| LAnd (dst: RegName) (r1 r2: Z + RegName)
| LOr (dst: RegName) (r1 r2: Z + RegName)
| LShiftL (dst: RegName) (r1 r2: Z + RegName)
| LShiftR (dst: RegName) (r1 r2: Z + RegName)
| Lea (dst: RegName) (r: Z + RegName)
(* The word of [src] with its address set to [addr], written to [dst]. *)
| SetA (dst src : RegName) (addr : Z + RegName)
| Restrict (dst: RegName) (r: Z + RegName)
| Subseg (dst: RegName) (r1 r2: Z + RegName)
| GetB (dst r: RegName)
| GetE (dst r: RegName)
| GetA (dst r: RegName)
| GetP (dst r: RegName)
| GetL (dst r: RegName)
| GetWType (dst r : RegName) (* structural word category, independent of validity *)
| GetOType (dst r: RegName)
| Seal (dst : RegName) (r1 r2: RegName)
| UnSeal (dst : RegName) (r1 r2: RegName)
(* Swaps a system register: [dst] receives the old value of [sr], and [sr]
   receives the legalised value of [src]. The source [inr cnull] leaves [sr]
   unchanged, and the destination [cnull] drops the old value. *)
| SpecialRW (dst: RegName) (sr: SRegName) (src: Z + RegName)
(* Sets the MIE bit of mstatus to [b], keeping MPIE. *)
| SetMIE (b: InterruptStatus)
(* Returns from an exception: the PC receives MEPCC, MIE receives MPIE, and
   MPIE becomes enabled. *)
| Mret
| Fail
| Halt
| GetTag (dst src: RegName)
| ClearTag (dst src: RegName)
(* The PC capability with its address offset by [imm]. *)
| Auipcc (dst: RegName) (imm: Z).

#[global] Instance instr_eq_dec : EqDecision instr.
Proof. solve_decision. Defined.

#[global] Instance instr_countable : Countable instr.
Proof.

  set (enc := fun e =>
      match e with
      | Jmp r => GenNode 0 [GenLeaf (inr r)]
      | Mov dst src => GenNode 2 [GenLeaf (inl (inl dst)); GenLeaf (inr src)]
      | CLoad dst src imm => GenNode 3 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl src)); GenLeaf (inr (inl imm))]
      | Store dst src imm => GenNode 4 [GenLeaf (inl (inl dst)); GenLeaf (inr src); GenLeaf (inr (inl imm))]
      | Lt dst r1 r2 => GenNode 5 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)]
      | Add dst r1 r2 => GenNode 6 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)]
      | Sub dst r1 r2 => GenNode 7 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)]
      | Lea dst r => GenNode 8 [GenLeaf (inl (inl dst)); GenLeaf (inr r)]
      | Restrict dst r => GenNode 9 [GenLeaf (inl (inl dst)); GenLeaf (inr r)]
      | Subseg dst r1 r2 => GenNode 10 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)]
      | GetB dst r => GenNode 11 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r))]
      | GetE dst r => GenNode 12 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r))]
      | GetA dst r => GenNode 13 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r))]
      | GetP dst r => GenNode 14 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r))]
      | GetL dst r => GenNode 15 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r))]

      | GetOType dst r => GenNode 16 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r))]
      | GetWType dst r => GenNode 17 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r))]

      | Seal dst r1 r2 => GenNode 18 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r1)); GenLeaf (inl (inl r2))]
      | UnSeal dst r1 r2 => GenNode 19 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r1)); GenLeaf (inl (inl r2))]
      | SpecialRW dst sr src => GenNode 20 [GenLeaf (inl (inl dst)); GenLeaf (inl (inr sr)); GenLeaf (inr src)]
      | SetMIE InterruptEnabled => GenNode 21 []
      | SetMIE InterruptDisabled => GenNode 33 []
      | Mret => GenNode 34 []
      | Fail => GenNode 22 []
      | Halt => GenNode 23 []
      | Mul dst r1 r2 => GenNode 24 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)]
      | LAnd dst r1 r2 => GenNode 25 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)]
      | LOr dst r1 r2 => GenNode 26 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)]
      | LShiftL dst r1 r2 => GenNode 27 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)]
      | LShiftR dst r1 r2 => GenNode 28 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)]
      | Jalr dst src => GenNode 29 [GenLeaf (inl (inl dst));GenLeaf (inl (inl src))]
      | GetTag dst src => GenNode 30 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl src))]
      | ClearTag dst src => GenNode 31 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl src))]
      | Auipcc dst imm => GenNode 32 [GenLeaf (inl (inl dst)); GenLeaf (inr (inl imm))]
      | Le dst r1 r2 => GenNode 35 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)]
      | Jeq off r1 r2 => GenNode 36 [GenLeaf (inr off); GenLeaf (inr r1); GenLeaf (inr r2)]
      | Jne off r1 r2 => GenNode 37 [GenLeaf (inr off); GenLeaf (inr r1); GenLeaf (inr r2)]
      | Jlt off r1 r2 => GenNode 38 [GenLeaf (inr off); GenLeaf (inr r1); GenLeaf (inr r2)]
      | Jle off r1 r2 => GenNode 39 [GenLeaf (inr off); GenLeaf (inr r1); GenLeaf (inr r2)]
      | SetA dst src addr => GenNode 40 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl src)); GenLeaf (inr addr)]
      end).
  set (dec := fun e =>
      match e with
      | GenNode 0 [GenLeaf (inr r) ] => Jmp r
      | GenNode 2 [GenLeaf (inl (inl dst)); GenLeaf (inr src)] => Mov dst src
      | GenNode 3 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl src)); GenLeaf (inr (inl imm))] => CLoad dst src imm
      | GenNode 4 [GenLeaf (inl (inl dst)); GenLeaf (inr src); GenLeaf (inr (inl imm))] => Store dst src imm
      | GenNode 5 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)] => Lt dst r1 r2
      | GenNode 6 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)] => Add dst r1 r2
      | GenNode 7 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)] => Sub dst r1 r2
      | GenNode 8 [GenLeaf (inl (inl dst)); GenLeaf (inr r)] => Lea dst r
      | GenNode 9 [GenLeaf (inl (inl dst)); GenLeaf (inr r)] => Restrict dst r
      | GenNode 10 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)] => Subseg dst r1 r2
      | GenNode 11 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r))] => GetB dst r
      | GenNode 12 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r))] => GetE dst r
      | GenNode 13 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r))] => GetA dst r
      | GenNode 14 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r))] => GetP dst r
      | GenNode 15 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r))] => GetL dst r

      | GenNode 16 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r))] => GetOType dst r
      | GenNode 17 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r))] => GetWType dst r

      | GenNode 18 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r1)); GenLeaf (inl (inl r2))] => Seal dst r1 r2
      | GenNode 19 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r1)); GenLeaf (inl (inl r2))] => UnSeal dst r1 r2
      | GenNode 20 [GenLeaf (inl (inl dst)); GenLeaf (inl (inr sr)); GenLeaf (inr src)] => SpecialRW dst sr src
      | GenNode 21 [] => SetMIE InterruptEnabled
      | GenNode 33 [] => SetMIE InterruptDisabled
      | GenNode 34 [] => Mret
      | GenNode 22 [] => Fail
      | GenNode 23 [] => Halt
      | GenNode 24 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)] => Mul dst r1 r2
      | GenNode 25 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)] => LAnd dst r1 r2
      | GenNode 26 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)] => LOr dst r1 r2
      | GenNode 27 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)] => LShiftL dst r1 r2
      | GenNode 28 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)] => LShiftR dst r1 r2
      | GenNode 29 [GenLeaf (inl (inl dst));GenLeaf (inl (inl src))] => Jalr dst src
      | GenNode 30 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl src))] => GetTag dst src
      | GenNode 31 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl src))] => ClearTag dst src
      | GenNode 32 [GenLeaf (inl (inl dst)); GenLeaf (inr (inl imm))] => Auipcc dst imm
      | GenNode 35 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)] => Le dst r1 r2
      | GenNode 36 [GenLeaf (inr off); GenLeaf (inr r1); GenLeaf (inr r2)] => Jeq off r1 r2
      | GenNode 37 [GenLeaf (inr off); GenLeaf (inr r1); GenLeaf (inr r2)] => Jne off r1 r2
      | GenNode 38 [GenLeaf (inr off); GenLeaf (inr r1); GenLeaf (inr r2)] => Jlt off r1 r2
      | GenNode 39 [GenLeaf (inr off); GenLeaf (inr r1); GenLeaf (inr r2)] => Jle off r1 r2
      | GenNode 40 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl src)); GenLeaf (inr addr)] => SetA dst src addr
      | _ => Fail (* dummy *)
      end).
  refine (inj_countable' enc dec _).
  intros i. destruct i; try match goal with b : InterruptStatus |- _ => destruct b end; done.
Defined.
