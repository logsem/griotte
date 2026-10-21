From griotte Require Import machine_parameters assembler switcher fetch.

(** The code shared by the allocators: their constants, the loops over the
    heap and the shadow table, and the code segments that both entries run
    identically. Each allocator assembles its entries from its own blocks
    and these segments; the segments contain their own labels, and the
    entries jump to [.malloc_invalid], [.malloc_no_memory] and
    [.free_invalid], which they define.

    The layout of an allocator compartment is also shared: it does not depend
    on the code. *)

Section AllocatorCommonCode.
  Import Asm_Griotte.
  Context `{MP : MachineParameters}.
  #[local] Coercion Z.of_nat : nat >-> Z.

  Definition ALLOC_OK : Z := 0.

  Definition ALLOC_INVALID : Z := -1.

  Definition ALLOC_NO_MEMORY : Z := -2.

  Definition allocator_shadow_import_off : Z := 0.

  Definition allocator_unsealing_key_import_off : Z := 1.

  Definition allocator_revoker_import_off : Z := 2.

  (** The imports are a data prefix of the code, named by symbols in the order
      of [allocator_imports]: an allocator program starts with
      [allocator_import_symbols_asm], and the fetches load the imports
      relative to the PC. The code starts after them, at the entry [.Lmalloc]
      of [malloc]. *)
  Definition allocator_import_symbols_asm : list asm_code :=
    [ #@".Limport_shadow";
      #@".Limport_unsealing_key";
      #@".Limport_revoker";
      #".Lmalloc"
    ].

  (** Prefix the first block of an allocator program [l] with the import
      symbols. *)
  Definition allocator_with_imports (l : list (list asm_code)) : list (list asm_code) :=
    match l with
    | [] => []
    | b :: l => (allocator_import_symbols_asm ++ b) :: l
    end.

  Definition allocator_header_words : Z := 3.

  (** These loops are local blocks: their labels are resolved inside them, so
      their assembled code is independent of its placement. Both require a
      nonempty range. *)

  Definition allocator_zero_asm (rptr rend rtmp : RegName) : list asm_code :=
    macro: [ #".allocator_zero";
         store rptr 0;
         lea rptr 1;
         geta rtmp rptr;
         sub rtmp rend rtmp;
         jnz (".allocator_zero")%asm rtmp
       ].

  Definition allocator_zero (rptr rend rtmp : RegName) :=
    Eval compute in assemble (allocator_zero_asm rptr rend rtmp).
  Lemma allocator_zero_assembles (rptr rend rtmp : RegName) :
    asm_ok (assemble_check (allocator_zero_asm rptr rend rtmp)).
  Proof. asm_check. Qed.

  Definition allocator_zero_instrs (rptr rend rtmp : RegName) : list Word :=
    encodeInstrsW (allocator_zero rptr rend rtmp).

  (** Paint a positive number of consecutive shadow entries, advancing the
      pointer and consuming the count. *)

  Definition allocator_paint_asm (rptr rcount : RegName) (status : AllocStatus)
    : list asm_code :=
    macro: [ #".allocator_paint";
         store rptr (encodeAllocStatus status);
         lea rptr 1;
         sub rcount rcount 1;
         jnz (".allocator_paint")%asm rcount
       ].

  Definition allocator_paint (rptr rcount : RegName) (status : AllocStatus) :=
    Eval compute in assemble (allocator_paint_asm rptr rcount status).
  Lemma allocator_paint_assembles (rptr rcount : RegName) (status : AllocStatus) :
    asm_ok (assemble_check (allocator_paint_asm rptr rcount status)).
  Proof. asm_check. Qed.

  Definition allocator_paint_instrs (rptr rcount : RegName) (status : AllocStatus)
    : list Word := encodeInstrsW (allocator_paint rptr rcount status).

  (** Register clearing belongs to the switcher return path. *)

  Definition allocator_return_asm : list asm_code := [jalr cnull cra].

  (** The shadow segment of [malloc]: [ca2] holds the payload capability with
      its cursor at the payload base, [ct0] the full heap capability with its
      cursor at the new header, [ct1] the payload base, [ct2] its end and
      [ctp] the shadow capability, fetched from the imports by the block
      before the segment. The memory is zeroed before its shadow entries are
      written. *)

  Definition allocator_malloc_shadow_asm : list (list asm_code) :=
    [ allocator_zero_asm ca2 ct2 ca3;
      [ (* Translate the header address by its offset within the heap. *)
        getb ca3 ct0;
        sub ca3 ct1 ca3;
        sub ca3 ca3 allocator_header_words;
        lea ctp ca3;
        mov ca2 allocator_header_words
      ];
      (* Paint the three header words quarantined, as CHERIoT does: [free]
         recognizes a payload base as the first unpainted word after a
         painted one. *)
      allocator_paint_asm ctp ca2 ShadowQuarantined;
      [ sub ca2 ct2 ct1 ];
      allocator_paint_asm ctp ca2 ShadowLive
    ].

  Definition assembled_allocator_malloc_shadow :=
    Eval compute in assemble_block allocator_malloc_shadow_asm.
  Lemma allocator_malloc_shadow_assembles :
    asm_ok (assemble_block_check allocator_malloc_shadow_asm).
  Proof. asm_check. Qed.

  Definition allocator_malloc_shadow_instrs_n (n : nat) : list Word :=
    encodeInstrsW (default [] (assembled_allocator_malloc_shadow !! n)).

  (** The exits of [malloc]: the rejection of an invalid size, the rejection
      of an exhausted heap, and the return. *)

  Definition allocator_malloc_exit_asm : list (list asm_code) :=
    [ [ #".malloc_invalid";
        mov ca0 ALLOC_INVALID;
        mov ca1 0;
        jmp (".malloc_return")%asm
      ];
      [ #".malloc_no_memory";
        mov ca0 ALLOC_NO_MEMORY;
        mov ca1 0
      ];
      ASM_Label ".malloc_return" :: allocator_return_asm
    ].

  Definition assembled_allocator_malloc_exit :=
    Eval compute in assemble_block allocator_malloc_exit_asm.
  Lemma allocator_malloc_exit_assembles :
    asm_ok (assemble_block_check allocator_malloc_exit_asm).
  Proof. asm_check. Qed.

  Definition allocator_malloc_exit_instrs_n (n : nat) : list Word :=
    encodeInstrsW (default [] (assembled_allocator_malloc_exit !! n)).

  (** The tail of [free], once the request is known to be an allocation:
      [ctp] holds the shadow capability with its cursor at the payload base,
      [ca2] the payload size, [ct1] the payload base, [ct2] its end and [ca3]
      the revoker capability, fetched from the imports by the block before the
      segment. It
      paints the payload quarantined, revokes it and unpaints it. It also
      holds the rejection of an invalid request, and the return. *)

  Definition allocator_free_tail_asm : list (list asm_code) :=
    [ allocator_paint_asm ctp ca2 ShadowQuarantined;
      [ #".free_success";
        (* Clear the argument registers: no register then holds a capability
           to the freed allocation. *)
        mov ca0 ALLOC_OK;
        mov ca1 0
      ];
      [ (* The offset back to the payload base and the count, computed first
           so that [ca4] and [ca2] hold integers during the sweep. *)
        sub ca4 ct1 ct2;
        sub ca2 ct2 ct1;
        (* Sweep memory: every capability to the painted payload loses its tag. *)
        store ca3 0;
        (* Rewind the shadow cursor to the payload base. *)
        lea ctp ca4
      ];
      (* The revoked payload leaves quarantine: unpaint it. *)
      allocator_paint_asm ctp ca2 ShadowLive;
      [ jmp (".free_return")%asm ];
      [ #".free_invalid";
        mov ca0 ALLOC_INVALID;
        mov ca1 0
      ];
      ASM_Label ".free_return" :: allocator_return_asm
    ].

  Definition assembled_allocator_free_tail :=
    Eval compute in assemble_block allocator_free_tail_asm.
  Lemma allocator_free_tail_assembles :
    asm_ok (assemble_block_check allocator_free_tail_asm).
  Proof. asm_check. Qed.

  Definition allocator_free_tail_instrs_n (n : nat) : list Word :=
    encodeInstrsW (default [] (assembled_allocator_free_tail !! n)).

  Definition allocator_data : list Word :=
    [WCap true RW Global heap_b heap_e (heap_b ^+ 1)%a].

  Class allocatorLayout : Type := mkAllocatorLayout {
    AllocOtype : OType;
    allocator_pcc_b : Addr;
    allocator_code_b : Addr;
    allocator_pcc_e : Addr;
    allocator_cgp_b : Addr;
    allocator_cgp_e : Addr;
    allocator_exp_tbl_b : Addr;
    allocator_exp_tbl_e : Addr;
  }.

  Definition allocator_revoker_cap : Word :=
    WCap true RW Global revoker_addr (revoker_addr ^+ 1)%a revoker_addr.

  Definition allocator_imports `{allocatorLayout} : list Word :=
    [WCap true RW Global shadow_b shadow_e shadow_b;
     WSealRange true (false, true) Global AllocOtype
       (AllocOtype ^+ 1)%ot AllocOtype;
     allocator_revoker_cap].

  Lemma allocator_imports_length `{allocatorLayout} : length allocator_imports = 3.
  Proof. reflexivity. Qed.

  (** The offset of the entry of [malloc] from the start of the PCC. *)
  Definition allocator_malloc_pcc_off : nat :=
    Eval vm_compute in label_offset allocator_import_symbols_asm ".Lmalloc".

  (** The indices of the exports [malloc] and [free], in the order of the
      firmware, and the offsets of their entries in the export table. *)
  Definition allocator_entry_malloc : nat := 0.
  Definition allocator_entry_free : nat := 1.

  Definition allocator_malloc_exp_tbl_off : Z := ExportTable_offset_entry allocator_entry_malloc.

  Definition allocator_free_exp_tbl_off : Z := ExportTable_offset_entry allocator_entry_free.

  (** The well-formedness of a layout that does not depend on the code. Each
      allocator's [allocatorLayoutWf] provides it. *)

  Class allocatorCommonLayoutWf `{allocatorLayout} : Prop := mkAllocatorCommonLayoutWf {
    allocator_common_otype_size : (AllocOtype < AllocOtype ^+ 1)%ot;
    allocator_common_revoker_size : (revoker_addr < revoker_addr ^+ 1)%a;
    allocator_common_translation_affine : forall a,
      heap_to_shadow a = translate_region heap_b heap_e shadow_b a;
    allocator_common_size_imports :
      (allocator_pcc_b + length allocator_imports)%a = Some allocator_code_b;
    allocator_common_size_data :
      (allocator_cgp_b + length allocator_data)%a = Some allocator_cgp_e;
    allocator_common_regions_disjoint :
      ## [finz.seq_between allocator_pcc_b allocator_pcc_e;
          finz.seq_between allocator_cgp_b allocator_cgp_e;
          finz.seq_between allocator_exp_tbl_b allocator_exp_tbl_e;
          finz.seq_between heap_b heap_e;
          finz.seq_between shadow_b shadow_e];
  }.

  Definition allocator_malloc_pcc_addr `{allocatorLayout} : Addr :=
    (allocator_pcc_b ^+ allocator_malloc_pcc_off)%a.

  (** These export descriptors can be sealed with the switcher's ordinary
      entry key. There is no allocator-specific seal or authorization token. *)

  Definition allocator_malloc `{allocatorLayout} (g : Locality) : Sealable :=
    SCap true RO g allocator_exp_tbl_b allocator_exp_tbl_e
      (allocator_exp_tbl_b ^+ allocator_malloc_exp_tbl_off)%a.

  Definition allocator_free `{allocatorLayout} (g : Locality) : Sealable :=
    SCap true RO g allocator_exp_tbl_b allocator_exp_tbl_e
      (allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off)%a.

End AllocatorCommonCode.
