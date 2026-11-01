From griotte Require Import machine_base.

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
