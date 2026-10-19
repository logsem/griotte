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
| IExport (c : string) (e : string)   (* the entry of the export [e] of [c], sealed *)
| ISealedStatic (o : OType) (s : string).
    (* the static sealed object named [s] of the compartment itself,
       sealed with [o]; a compartment only refers to its own static sealed
       objects *)

(** The globals of a trusted compartment, by chunks: literal words, or a
    word written by the loader. *)
Inductive fw_chunk : Type :=
| FWs (ws : list Word)
| FWord (w : fw_word).

(** An export of a trusted compartment: its name, its offset from the base
    of the PCC, its number of arguments and its interrupt posture. Imports
    and threads refer to exports by name. *)
Record fw_export : Type := MkFwExport {
  fe_name : string;
  fe_offset : nat;
  fe_nargs : nat;
  fe_posture : InterruptStatus;
}.

(** An export of an untrusted compartment: its name and its number of
    arguments; its offset is arbitrary. *)
Record fw_untrusted_export : Type := MkFwUntrustedExport {
  ue_name : string;
  ue_nargs : nat;
}.

(** A trusted compartment has known code, globals and exports. *)
Record fw_trusted : Type := MkFwTrusted {
  tb_code : list Word;
  tb_data : list fw_chunk;
  tb_exports : list fw_export;
}.

(** The code, the globals and the export offsets of an untrusted
    compartment are arbitrary; [ub_owner] names the logical compartment it
    belongs to. *)
Record fw_untrusted : Type := MkFwUntrusted {
  ub_owner : string;
  ub_exports : list fw_untrusted_export;
}.

(** The contents of a compartment. *)
Inductive fw_body : Type :=
| TrustedBody (b : fw_trusted)
| UntrustedBody (b : fw_untrusted).

(** A static sealed object: its name and its word. Imports refer to the
    static sealed objects of their compartment by name. *)
Record fw_static : Type := MkFwStatic {
  ss_name : string;
  ss_word : Word;
}.

Record fw_cmpt : Type := MkFwCmpt {
  fc_name : string;
  fc_imports : list fw_word;
  fc_static_sealed : list fw_static;
  fc_body : fw_body;
}.

(** A thread starts at the export named [ft_entry] of compartment
    [ft_cmpt], with a zeroed stack of [ft_stack_size] words and a trusted
    stack with room for [ft_tstack_frames] frames besides the entry
    frame. *)
Record fw_thread : Type := MkFwThread {
  ft_cmpt : string;
  ft_entry : string;
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

Definition default_fw_cmpt : fw_cmpt := MkFwCmpt "" [] [] (UntrustedBody (MkFwUntrusted "" [])).

Fixpoint fw_cmpt_of (l : list fw_cmpt) (n : string) : fw_cmpt :=
  match l with
  | [] => default_fw_cmpt
  | fc :: l => if String.eqb n (fc_name fc) then fc else fw_cmpt_of l n
  end.

(** The position of the first element of [l] named [e]. *)
Fixpoint fw_index_of {A} (name : A → string) (e : string) (l : list A) : option nat :=
  match l with
  | [] => None
  | x :: l =>
      if String.eqb e (name x) then Some 0
      else match fw_index_of name e l with Some k => Some (S k) | None => None end
  end.

(** The position of the export named [e] of the compartment [n] in its
    export table. *)
Definition fw_body_export_index (b : fw_body) (e : string) : option nat :=
  match b with
  | TrustedBody b => fw_index_of fe_name e (tb_exports b)
  | UntrustedBody b => fw_index_of ue_name e (ub_exports b)
  end.

Definition fw_export_index (fw : firmware) (n e : string) : option nat :=
  fw_body_export_index (fc_body (fw_cmpt_of (fw_cmpts fw) n)) e.

(** The export named [e] of a trusted compartment. *)
Fixpoint fw_find_export (e : string) (l : list fw_export) : option fw_export :=
  match l with
  | [] => None
  | x :: l => if String.eqb e (fe_name x) then Some x else fw_find_export e l
  end.
