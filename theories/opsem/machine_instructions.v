From griotte Require Import registers.

Inductive instr: Type :=
| Jmp (rimm: Z + RegName)
| Jnz (rimm : Z + RegName) (rcond: RegName)
| Jalr (rdst: RegName) (rsrc: RegName) (* jumps to wsrc, rdst receives return cap *)
| Mov (dst: RegName) (src: Z + RegName)
| Load (dst src: RegName)
| Store (dst: RegName) (src: Z + RegName)
| Lt (dst: RegName) (r1 r2: Z + RegName)
| Add (dst: RegName) (r1 r2: Z + RegName)
| Sub (dst: RegName) (r1 r2: Z + RegName)
| Mul (dst: RegName) (r1 r2: Z + RegName)
| LAnd (dst: RegName) (r1 r2: Z + RegName)
| LOr (dst: RegName) (r1 r2: Z + RegName)
| LShiftL (dst: RegName) (r1 r2: Z + RegName)
| LShiftR (dst: RegName) (r1 r2: Z + RegName)
| Lea (dst: RegName) (r: Z + RegName)
| Restrict (dst: RegName) (r: Z + RegName)
| Subseg (dst: RegName) (r1 r2: Z + RegName)
| GetB (dst r: RegName)
| GetE (dst r: RegName)
| GetA (dst r: RegName)
| GetP (dst r: RegName)
| GetL (dst r: RegName)
| GetWType (dst r : RegName) (* combine IsCap, GetTag, and GetSealed all together into a unique encoding *)
| GetOType (dst r: RegName)
| Seal (dst : RegName) (r1 r2: RegName)
| UnSeal (dst : RegName) (r1 r2: RegName)
(* Separate SpecialRW into 2 instructions *)
| ReadSR (dst: RegName) (src: SRegName)
| WriteSR (dst: SRegName) (src: RegName)
| Fail
| Halt.

Global Instance instr_eq_dec : EqDecision instr.
Proof. solve_decision. Defined.

Global Instance instr_countable : Countable instr.
Proof.

  set (enc := fun e =>
      match e with
      | Jmp r => GenNode 0 [GenLeaf (inr r)]
      | Jnz r1 r2 => GenNode 1 [GenLeaf (inr r1); GenLeaf (inl (inl r2))]
      | Mov dst src => GenNode 2 [GenLeaf (inl (inl dst)); GenLeaf (inr src)]
      | Load dst src => GenNode 3 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl src))]
      | Store dst src => GenNode 4 [GenLeaf (inl (inl dst)); GenLeaf (inr src)]
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
      | ReadSR dst src => GenNode 20 [GenLeaf (inl (inl dst)); GenLeaf (inl (inr src))]
      | WriteSR dst src => GenNode 21 [GenLeaf (inl (inr dst)); GenLeaf (inl (inl src))]
      | Fail => GenNode 22 []
      | Halt => GenNode 23 []
      | Mul dst r1 r2 => GenNode 24 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)]
      | LAnd dst r1 r2 => GenNode 25 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)]
      | LOr dst r1 r2 => GenNode 26 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)]
      | LShiftL dst r1 r2 => GenNode 27 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)]
      | LShiftR dst r1 r2 => GenNode 28 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)]
      | Jalr dst src => GenNode 29 [GenLeaf (inl (inl dst));GenLeaf (inl (inl src))]
      end).
  set (dec := fun e =>
      match e with
      | GenNode 0 [GenLeaf (inr r) ] => Jmp r
      | GenNode 1 [GenLeaf (inr r1); GenLeaf (inl (inl r2))] => Jnz r1 r2
      | GenNode 2 [GenLeaf (inl (inl dst)); GenLeaf (inr src)] => Mov dst src
      | GenNode 3 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl src))] => Load dst src
      | GenNode 4 [GenLeaf (inl (inl dst)); GenLeaf (inr src)] => Store dst src
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
      | GenNode 20 [GenLeaf (inl (inl dst)); GenLeaf (inl (inr src))] => ReadSR dst src
      | GenNode 21 [GenLeaf (inl (inr dst)); GenLeaf (inl (inl src))] => WriteSR dst src
      | GenNode 22 [] => Fail
      | GenNode 23 [] => Halt
      | GenNode 24 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)] => Mul dst r1 r2
      | GenNode 25 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)] => LAnd dst r1 r2
      | GenNode 26 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)] => LOr dst r1 r2
      | GenNode 27 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)] => LShiftL dst r1 r2
      | GenNode 28 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)] => LShiftR dst r1 r2
      | GenNode 29 [GenLeaf (inl (inl dst));GenLeaf (inl (inl src))] => Jalr dst src
      | _ => Fail (* dummy *)
      end).
  refine (inj_countable' enc dec _).
  intros i. destruct i; simpl; done.
Defined.
