From Stdlib Require Import ZArith.

(** The layout of an export table, counted in words: the PCC and the CGP
    of the compartment, the offsets of its stackful and stackless error
    handlers ([0xffff] for none; one word each, where CHERIoT has 16-bit
    fields), then the export entries. *)
Definition ExportTable_offset_pcc : Z := 0%Z.
Definition ExportTable_offset_cgp : Z := 1%Z.
Definition ExportTable_offset_errorHandler : Z := 2%Z.
Definition ExportTable_offset_errorHandlerStackless : Z := 3%Z.
Definition ExportTable_offset_entries : Z := 4%Z.

(** The handler offset of a compartment that declares no handler. *)
Definition ExportTable_no_handler : Z := 0xffff%Z.
