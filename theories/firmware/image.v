From stdpp Require Import strings.
From griotte Require Import machine_base.
Set Mangle Names.

(** * Firmware images: the memory layout

    The addresses of every section of a firmware image and the words the
    loader placed in the sections whose contents vary between compartments.
    An image carries no well-formedness proof: the conditions on it are
    stated by [img_wf] in [firmware_ok], so that they can be printed. *)

(** A compartment: its PCC range (import table, then code), its CGP range
    (globals), its static sealed objects and its export table (the PCC and
    CGP capabilities, then the entries). *)
Record img_cmpt : Type := MkImgCmpt {
  cmpt_b_pcc : Addr;
  cmpt_a_code : Addr;
  cmpt_e_pcc : Addr;
  cmpt_b_cgp : Addr;
  cmpt_e_cgp : Addr;
  cmpt_b_static_sealed : Addr;
  cmpt_e_static_sealed : Addr;
  cmpt_exp_tbl_pcc : Addr;
  cmpt_exp_tbl_cgp : Addr;
  cmpt_exp_tbl_entries_start : Addr;
  cmpt_exp_tbl_entries_end : Addr;
  cmpt_imports : list Word;
  cmpt_code : list Word;
  cmpt_data : list Word;
  cmpt_static_sealed : list Word;
  cmpt_exp_tbl_entries : list Word;
}.

(** A thread: its stack and its trusted stack. *)
Record img_thread : Type := MkImgThread {
  b_stack : Addr;
  e_stack : Addr;
  b_trusted_stack : Addr;
  e_trusted_stack : Addr;
}.

(** The switcher: its code range, starting with its sealing key, its two
    entry points and the sealing type of the export entries. *)
Record img_switcher : Type := MkImgSwitcher {
  b_switcher : Addr;
  e_switcher : Addr;
  a_switcher_call : Addr;
  a_switcher_return : Addr;
  ot_switcher : OType;
}.

(** The assert library: its code, the capability to its flag, and the flag. *)
Record img_assert : Type := MkImgAssert {
  b_assert : Addr;
  e_assert : Addr;
  cap_assert : Addr;
  flag_assert : Addr;
}.

(** An image: the compartments by name, in the order of the firmware. *)
Record fw_image : Type := MkFwImage {
  img_sw : img_switcher;
  img_asrt : img_assert;
  img_cmpts : list (string * img_cmpt);
  img_threads : list img_thread;
}.

(** ** Lookups, with a default for absent names *)

Definition za0 : Addr := za.

Definition default_img_cmpt : img_cmpt :=
  MkImgCmpt za0 za0 za0 za0 za0 za0 za0 za0 za0 za0 za0 [] [] [] [] [].

Definition default_img_thread : img_thread := MkImgThread za0 za0 za0 za0.

Fixpoint assoc {A} (n : string) (l : list (string * A)) (d : A) : A :=
  match l with
  | [] => d
  | (n', x) :: l => if String.eqb n n' then x else assoc n l d
  end.

Definition cmpt_of (img : fw_image) (n : string) : img_cmpt :=
  assoc n (img_cmpts img) default_img_cmpt.

Fixpoint fw_nth {A} (k : nat) (l : list A) (d : A) : A :=
  match l, k with
  | [], _ => d
  | x :: _, 0 => x
  | _ :: l, S k => fw_nth k l d
  end.

Definition thread_of (img : fw_image) (i : nat) : img_thread :=
  fw_nth i (img_threads img) default_img_thread.
