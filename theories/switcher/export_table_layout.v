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

(** CHERIoT's [SPILL_SLOT_*]: the slots of the spill area where the call
    path of the switcher saves the caller's registers, counted in words. *)
(** The slot of the caller's [cs0] in the spill area (in words). *)
Definition SpillSlot_cs0 : Z := 0%Z.
(** The slot of the caller's [cs1] in the spill area (in words). *)
Definition SpillSlot_cs1 : Z := 1%Z.
(** The slot of the caller's [cgp] in the spill area (in words). *)
Definition SpillSlot_cgp : Z := 2%Z.
(** The slot of the caller's return address [cra] in the spill area (in words). *)
Definition SpillSlot_pcc : Z := 3%Z.
(** The size of the spill area (in words). *)
Definition SpillSlot_size : Z := 4%Z.
