From Stdlib Require Import Extraction ExtrOcamlBasic.
From stdpp Require Import gmap.
Require Import machine_step.

(** A small, typed API keeps clients independent of stdpp's extracted [gmap]
    representation and hides the map type-class arguments. *)
Definition reg_empty : Reg := ∅.
Definition sreg_empty : SReg := ∅.
Definition mem_empty : Mem := ∅.
Definition reg_lookup (rs : Reg) (r : RegName) : option Word := rs !! r.
Definition sreg_lookup (srs : SReg) (sr : SRegName) : option Word := srs !! sr.
Definition mem_lookup (m : Mem) (a : Addr) : option Word := m !! a.
Definition reg_insert (rs : Reg) (r : RegName) (w : Word) : Reg := <[r := w]> rs.
Definition sreg_insert (srs : SReg) (sr : SRegName) (w : Word) : SReg := <[sr := w]> srs.
Definition mem_insert (m : Mem) (a : Addr) (w : Word) : Mem := <[a := w]> m.
Definition reg_elements (rs : Reg) : list (RegName * Word) := map_to_list rs.
Definition sreg_elements (srs : SReg) : list (SRegName * Word) := map_to_list srs.
Definition mem_elements (m : Mem) : list (Addr * Word) := map_to_list m.

Extraction Language OCaml.
Set Extraction KeepSingleton.
Set Extraction File Comment
"GENERATED FILE -- DO NOT EDIT.".

Extraction "griotte_extracted.ml"
  machine_step.machine_step
  reg_empty sreg_empty mem_empty
  reg_lookup sreg_lookup mem_lookup
  reg_insert sreg_insert mem_insert
  reg_elements sreg_elements mem_elements.
