From stdpp Require Import gmap strings.
From griotte Require Import machine_base.
From griotte Require Import compartment_layout.
Set Mangle Names.

(** * Firmwares: the abstract description of a firmware image

    Compartments are named, and the words the loader computes (sentries,
    sealed export entries, capabilities to static sealed objects) are given
    by what they refer to. [firmware_ok] translates a firmware into a
    condition on an image and an initial machine state. *)

(** An import, or another word written by the loader. *)
Inductive fw_word : Type :=
| FW (w : Word)                       (* a literal word *)
| ISwitcherCall                       (* the switcher call sentry *)
| IAssert                             (* the assert sentry *)
| IExport (c : string) (k : nat)      (* entry [k] of the export table of [c], sealed *)
| ISealedStatic (o : OType) (k : nat).
    (* the [k]-th static sealed object of the compartment itself, sealed
       with [o]; a compartment only refers to its own static sealed
       objects *)

(** The globals of a trusted compartment, by chunks: literal words, or a
    word written by the loader. *)
Inductive fw_chunk : Type :=
| FWs (ws : list Word)
| FWord (w : fw_word).

(** An export: its offset from the base of the PCC, its number of
    arguments and its interrupt posture. *)
Record fw_export : Type := MkFwExport {
  fe_offset : nat;
  fe_nargs : nat;
  fe_posture : InterruptStatus;
}.

(** The contents of a compartment. A trusted compartment has known code,
    globals and exports. The code, the globals and the export offsets of an
    untrusted compartment are arbitrary; [owner] names the logical
    compartment it belongs to. *)
Inductive fw_body : Type :=
| TrustedBody (code : list Word) (data : list fw_chunk) (exports : list fw_export)
| UntrustedBody (owner : string) (nexports : nat).

Record fw_cmpt : Type := MkFwCmpt {
  fc_name : string;
  fc_imports : list fw_word;
  fc_static_sealed : list Word;
  fc_body : fw_body;
}.

(** A thread starts at export [ft_entry] of compartment [ft_cmpt], with a
    zeroed stack of [ft_stack_size] words and a trusted stack with room for
    [ft_tstack_frames] frames besides the entry frame. *)
Record fw_thread : Type := MkFwThread {
  ft_cmpt : string;
  ft_entry : nat;
  ft_stack_size : nat;
  ft_tstack_frames : nat;
}.

(** A firmware: the compartments in image order, the threads, the sealing
    types handed to trusted code, and the heap roots (the bases of the heap
    capabilities the loader hands out, e.g. to the allocator). *)
Record firmware : Type := MkFirmware {
  fw_cmpts : list fw_cmpt;
  fw_threads : list fw_thread;
  fw_otypes : list OType;
  fw_heap_roots : list Addr;
}.

(** ** Annotation markers

    Transparent identities: [section] gives a heading to a group of
    conditions, [note] a comment to a word, a memory region or a condition.
    They are unfolded in the audited predicate. *)

Definition section (title : string) (P : Prop) : Prop := P.
Definition note {A} (comment : string) (x : A) : A := x.

(** ** Helpers mentioned by the predicates

    Small definitions that stay folded in the predicates, and that the
    reader of a predicate reads with it. *)

(** The words [ws] at the addresses [b], [b + 1], …. *)
Definition mem_region (b : Addr) (ws : list Word) : Mem :=
  list_to_map (zip (finz.seq b (length ws)) ws).

(** The ranges [[b, e)] are pairwise disjoint. *)
Definition ranges_disjoint (rs : list (Addr * Addr)) : Prop :=
  ## ((λ r, finz.seq_between r.1 r.2) <$> rs).

(** An integer word. *)
Definition is_int (w : Word) : Prop := is_z w.

(** A sealing type [o] with room for itself: [o + 1] exists. *)
Definition otype_valid (o : OType) : Prop := (o < o ^+ 1)%ot.

#[global] Instance otype_valid_dec o : Decision (otype_valid o).
Proof. rewrite /otype_valid. solve [apply _ | unfold finz.lt; apply _]. Defined.

(** An initial global of an untrusted compartment: an integer, or a
    capability, at most read-write, within the globals [[b, e)]. *)
Definition initial_data_word (b e : Addr) (w : Word) : Prop :=
  is_z w ∨ in_region w b e.

(** ** Lookups in a firmware *)

Definition default_fw_cmpt : fw_cmpt := MkFwCmpt "" [] [] (UntrustedBody "" 0).

Fixpoint fw_cmpt_of (l : list fw_cmpt) (n : string) : fw_cmpt :=
  match l with
  | [] => default_fw_cmpt
  | fc :: l => if String.eqb n (fc_name fc) then fc else fw_cmpt_of l n
  end.
