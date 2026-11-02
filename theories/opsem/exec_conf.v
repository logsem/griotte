From griotte Require Import machine_base mmio_shadow mmio_timer.

(* The machine configuration: the PC, the general registers, the system
   registers, the memory, the shadow table and the time devices. *)
Record ExecConf := MkExecConf {
  pcc : Word;
  reg : Reg;
  sreg : SReg;
  mem : Mem;
  shadowtbl : ShadowTbl;
  timedevs : TimeDevs;
}.

#[global] Instance ExecConf_inhabited : Inhabited ExecConf :=
  populate (MkExecConf inhabitant inhabitant inhabitant inhabitant inhabitant inhabitant).

Inductive ConfFlag : Type :=
| Executable
| Halted
| Faulted
| NextI.

Definition Conf: Type := ConfFlag * ExecConf.

Definition update_pcc (φ: ExecConf) (w: Word): ExecConf :=
  {| pcc := w; reg := reg φ; sreg := sreg φ; mem := mem φ;
     shadowtbl := shadowtbl φ; timedevs := timedevs φ |}.
Definition update_reg (φ: ExecConf) (r: RegName) (w: Word): ExecConf :=
  {| pcc := pcc φ; reg := <[r:=w]ᵣ>(reg φ); sreg := sreg φ; mem := mem φ;
     shadowtbl := shadowtbl φ; timedevs := timedevs φ |}.
Definition update_sreg (φ: ExecConf) (sr: SRegName) (w: Word): ExecConf :=
  {| pcc := pcc φ; reg := reg φ; sreg := <[sr:=w]>(sreg φ); mem := mem φ;
     shadowtbl := shadowtbl φ; timedevs := timedevs φ |}.
Definition update_mem (φ: ExecConf) (a: Addr) (w: Word): ExecConf :=
  {| pcc := pcc φ; reg := reg φ; sreg := sreg φ; mem := <[a:=w]>(mem φ);
     shadowtbl := shadowtbl φ; timedevs := timedevs φ |}.
Definition update_shadowtbl (φ: ExecConf) (a: Addr) (s: AllocStatus): ExecConf :=
  {| pcc := pcc φ; reg := reg φ; sreg := sreg φ; mem := mem φ;
     shadowtbl := <[a:=s]> (shadowtbl φ); timedevs := timedevs φ |}.
(** The shadow table replaced by [sh], as a store to the shadow region gives
    it. *)
Definition set_shadowtbl (φ: ExecConf) (sh: ShadowTbl): ExecConf :=
  {| pcc := pcc φ; reg := reg φ; sreg := sreg φ; mem := mem φ; shadowtbl := sh;
     timedevs := timedevs φ |}.
(** The time devices replaced by [td], as a store to [mtimecmp] or a tick
    gives them. *)
Definition set_timedevs (φ: ExecConf) (td: TimeDevs): ExecConf :=
  {| pcc := pcc φ; reg := reg φ; sreg := sreg φ; mem := mem φ;
     shadowtbl := shadowtbl φ; timedevs := td |}.

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
Notation "φ .[ 'TD' := td ]" := (set_timedevs φ td)
  (at level 2, left associativity, format "φ  '/' .[ 'TD'  :=  td ]").

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
