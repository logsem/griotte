From Stdlib Require Import Extraction ExtrOcamlBasic.
From stdpp Require Import gmap.
From griotte Require Import machine_parameters machine_base griotte_lang machine_run.

(** A small, typed API keeps clients independent of stdpp's extracted [gmap]
    representation and hides the map type-class arguments. *)
Definition reg_empty : Reg := ∅.
Definition sreg_empty : SReg := ∅.
Definition mem_empty : Mem := ∅.

Definition reg_lookup (rs : Reg) (r : RegName) : option Word :=
  rs !! r.
Definition sreg_lookup (srs : SReg) (sr : SRegName) : option Word :=
  srs !! sr.
Definition mem_lookup (m : Mem) (a : Addr) : option Word :=
  m !! a.

Definition reg_insert (rs : Reg) (r : RegName) (w : Word) : Reg :=
  <[r := w]> rs.
Definition sreg_insert (srs : SReg) (sr : SRegName) (w : Word) : SReg :=
  <[sr := w]> srs.
Definition mem_insert (m : Mem) (a : Addr) (w : Word) : Mem :=
  <[a := w]> m.

Definition reg_elements (rs : Reg) : list (RegName * Word) := map_to_list rs.
Definition sreg_elements (srs : SReg) : list (SRegName * Word) := map_to_list srs.
Definition mem_elements (m : Mem) : list (Addr * Word) := map_to_list m.

(** Prototype extraction entry point.  The generated module deliberately
    retains [MachineParameters] as a runtime record: the concrete encoding is
    supplied by the OCaml adapter and is therefore part of the trusted base. *)
Extraction Language OCaml.
Set Extraction KeepSingleton.
Set Extraction File Comment
"GENERATED FILE -- DO NOT EDIT.

ExtrOcamlBasic maps basic Rocq datatypes to OCaml; otherwise there are no
custom extraction mappings, and gmap is stdpp's extracted trie. Extraction
erases proofs and refinements, so OCaml can construct out-of-bounds finz and R
values. It also erases the laws of MachineParameters: the OCaml-supplied
encoding functions and adapter must satisfy those laws and are trusted.
Generated Obj.magic casts rely on the extractor and on well-formed inputs.".

Extraction "griotte_extracted.ml"
  machine_step
  reg_empty sreg_empty mem_empty
  reg_lookup sreg_lookup mem_lookup
  reg_insert sreg_insert mem_insert
  reg_elements sreg_elements mem_elements.
