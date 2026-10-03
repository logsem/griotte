From griotte Require Import machine_parameters assembler switcher fetch.

(** A compartment providing a bump allocator and range quarantine.
    The data capability retains authority over the whole heap; its cursor
    records the first unused address. The first heap address is never allocated
    or quarantined, so loading this capability always sees a clear shadow bit.

    [malloc] takes a positive number of words in [ca0]. It zeroes the new
    allocation, clears its shadow entries, and returns an exactly bounded
    [RW Global] capability in [ca0]. Each allocation has three protected header
    words before its payload: the original end and two reserved addresses,
    initialized to zero. [free] traverses these headers from the first one
    and requires both supplied bounds to match an original payload. It paints
    the payload quarantined, stores to the revoker, which untags every stale
    capability to it in memory, and unpaints the payload. Neither operation
    reuses memory.

    Both entries return normally through [cra] with a single result in [ca0]
    and zero in [ca1], following the CHERIoT convention: as for
    [heap_allocate], [malloc] returns a tagged capability on success and an
    untagged error code otherwise, so callers check the tag. [free] returns
    [ALLOC_OK] on success and [ALLOC_INVALID] otherwise.
    Invalid requests leave memory, the shadow table, and the bump pointer
    unchanged. The compartment preserves [cgp], [csp], [cra], [cs0], [cs1]
    and clobbers its scratch registers. The switcher handles register clearing. *)

Section Allocator.
  Import Asm_Griotte.
  Context `{MP : MachineParameters}.
  Local Coercion Z.of_nat : nat >-> Z.

  Definition ALLOC_OK : Z := 0.

  Definition ALLOC_INVALID : Z := -1.

  Definition ALLOC_NO_MEMORY : Z := -2.

  Definition allocator_shadow_import_off : Z := 0.

  Definition allocator_unsealing_key_import_off : Z := 1.

  Definition allocator_revoker_import_off : Z := 2.

  Definition allocator_header_words : Z := 3.

  (** These loops resolve their local labels before being embedded into a
      larger block, so their assembled code is independent of its placement.
      Both require a nonempty range. *)

  Definition allocator_zero_asm_pre (rptr rend rtmp : RegName) : list asm_code :=
    [ #".allocator_zero";
      store rptr 0;
      lea rptr 1;
      geta rtmp rptr;
      sub rtmp rend rtmp;
      jnz (".allocator_zero")%asm rtmp
    ].
  (* VM reduction preserves the register parameters: these macros contain no
     fixed register names that would need [revert_regs_code]. *)

  Definition allocator_zero_asm_env (rptr rend rtmp : RegName) :=
    Eval vm_compute in (compute_asm_code_env (allocator_zero_asm_pre rptr rend rtmp)).2.

  Definition allocator_zero_asm (rptr rend rtmp : RegName) :=
    Eval vm_compute in resolve_labels_macros (allocator_zero_asm_pre rptr rend rtmp)
                      (allocator_zero_asm_env rptr rend rtmp).

  Definition allocator_zero (rptr rend rtmp : RegName) :=
    Eval vm_compute in assemble (allocator_zero_asm rptr rend rtmp).

  Definition allocator_zero_instrs (rptr rend rtmp : RegName) : list Word :=
    encodeInstrsW (allocator_zero rptr rend rtmp).

  (** Paint a positive number of consecutive shadow entries, advancing the
      pointer and consuming the count. *)

  Definition allocator_paint_asm_pre (rptr rcount : RegName) (status : AllocStatus)
    : list asm_code :=
    [ #".allocator_paint";
      store rptr (encodeAllocStatus status);
      lea rptr 1;
      sub rcount rcount 1;
      jnz (".allocator_paint")%asm rcount
    ].

  Definition allocator_paint_asm_env (rptr rcount : RegName) (status : AllocStatus) :=
    Eval vm_compute in (compute_asm_code_env (allocator_paint_asm_pre rptr rcount status)).2.

  Definition allocator_paint_asm (rptr rcount : RegName) (status : AllocStatus) :=
    Eval vm_compute in resolve_labels_macros (allocator_paint_asm_pre rptr rcount status)
                      (allocator_paint_asm_env rptr rcount status).

  Definition allocator_paint (rptr rcount : RegName) (status : AllocStatus) :=
    Eval vm_compute in assemble (allocator_paint_asm rptr rcount status).

  Definition allocator_paint_instrs (rptr rcount : RegName) (status : AllocStatus)
    : list Word := encodeInstrsW (allocator_paint rptr rcount status).

  (** Register clearing belongs to the switcher return path. *)

  Definition allocator_return_asm : list asm_code := [jalr cnull cra].

  (** [ct0] holds the full heap capability with its cursor at the new header,
      [ct1] the payload base, [ct2] its end, and [ct4] the result capability.
      Capacity includes all three header words. Bounds are checked
      using integer subtraction before any capability address is advanced.
      The memory is zeroed before its shadow entries are cleared, and the
      bump pointer is published only after both loops complete. *)
  (* CHERI-C-style overview (schematic; addresses and sizes count machine words).
     HEADER_WORDS is 3; [integer] denotes the machine's mathematical integers.
     [set_address] changes only a capability's cursor; [set_bounds(c, n)]
     bounds it to the n words starting at that cursor. [base], [end], and
     [address] inspect capability fields. Shadow access uses the private import.

     malloc(request) {
       if (!is_integer(request) || integer(request) <= 0)
         return ALLOC_INVALID;

       integer n = integer(request);
       word_t *__capability root = *bump_slot;
       address_t h = address(root);
       if ((integer)end(root) - (integer)h - HEADER_WORDS < n)
         return ALLOC_NO_MEMORY;

       address_t b = h + HEADER_WORDS;
       address_t e = b + n;
       word_t *__capability payload = set_bounds(set_address(root, b), n);
       root[0] = e;                    // Header: original payload end.
       root[1] = 0;                    // Header: first reserved address.
       root[2] = 0;                    // Header: second reserved address.
       for (integer i = 0; i < n; ++i)
         payload[i] = 0;
       paint_shadow(b, e, ShadowLive);
       *bump_slot = set_address(root, e);
       return payload;
     }
  *)

  Definition allocator_malloc_asm : list (list asm_code) :=
    [ [ (* Reject noninteger and nonpositive sizes before touching the heap. *)
        getwtype ct3 ca0;
        sub ct3 ct3 (encodeWordType wt_int);
        jnz (".malloc_invalid")%asm ct3;
        lt ct3 0 ca0;
        jnz (".malloc_size_ok")%asm ct3;
        jmp (".malloc_invalid")%asm
      ];
      [ #".malloc_size_ok";
        (* Leave room for all three header words before checking the payload size.
           A negative remaining capacity also takes the no-memory branch. *)
        load ct0 cgp;
        geta ct1 ct0;
        gete ct2 ct0;
        sub ct3 ct2 ct1;
        sub ct3 ct3 allocator_header_words;
        lt ct3 ct3 ca0;
        jnz (".malloc_no_memory")%asm ct3;
        (* Bound the returned capability to the payload, excluding its header. *)
        add ct1 ct1 allocator_header_words;
        add ct2 ct1 ca0;
        mov ct4 ct0;
        lea ct4 allocator_header_words;
        subseg ct4 ct1 ct2;
        (* Record the immutable end and initialize the reserved address.
           Header addresses retain their initially clear shadow bits. *)
        store ct0 ct2;
        store_imm ct0 0 1;
        store_imm ct0 0 2;
        mov ca2 ct4
      ];
      allocator_zero_asm ca2 ct2 ct3;
      fetch_asm allocator_shadow_import_off ctp ct3 ca2;
      [ (* Translate the allocation base by its offset within the heap. *)
        getb ct3 ct0;
        sub ct3 ct1 ct3;
        lea ctp ct3;
        sub ca2 ct2 ct1
      ];
      allocator_paint_asm ctp ca2 ShadowLive;
      [ (* Skip the header and payload, publishing only after initialization. *)
        lea ct0 allocator_header_words;
        lea ct0 ca0;
        store cgp ct0;
        mov ca0 ct4;
        mov ca1 0;
        jmp (".malloc_return")%asm
      ];
      [ #".malloc_invalid";
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

  Definition assembled_allocator_malloc' :=
    Eval vm_compute in assemble_block allocator_malloc_asm.

  Definition assembled_allocator_malloc :=
    Eval cbv in revert_regs_code_block assembled_allocator_malloc'.

  Definition assembled_allocator_malloc_n (n : nat) : list instr :=
    default [] (assembled_allocator_malloc !! n).

  Definition allocator_malloc_instrs_n (n : nat) : list Word :=
    encodeInstrsW (assembled_allocator_malloc_n n).

  Definition allocator_malloc_instrs : list Word :=
    concat (encodeInstrsW <$> assembled_allocator_malloc).

  (** [free] accepts a tagged ordinary capability whose base and end exactly
      match an original payload. Starting after the reserved root address, it
      walks protected headers by their recorded ends, stopping at the bump
      pointer. It never interprets payload contents as headers. Its cursor
      and permissions do not determine which allocation is freed.
      Null and narrowed capabilities are invalid. A repeated free is
      invalid too: after revocation no tagged capability to the payload
      remains, so the argument fails the tag check.

      Painting affects later capability loads, not values already held in
      registers. After painting, the argument registers are cleared and the
      revoker sweeps memory, so no tagged capability to the payload remains;
      the payload is then unpainted. The memory itself is not cleared. *)
  (* CHERI-C-style overview, using the word-addressed helpers above.
     The root retains authority over headers and payloads. Returned allocation
     capabilities cover only payloads, so callers cannot modify the header chain.

     free(request) {
       if (!is_tagged_ordinary_capability(request))
         return ALLOC_INVALID;

       word_t *__capability root = *bump_slot;
       address_t next = address(root);
       address_t b = base(request), e = end(request);
       if (!(base(root) < b && b < e && e <= next))
         return ALLOC_INVALID;

       address_t h = base(root) + 1;    // Skip the permanently reserved root address.
       while (h < next) {
         word_t *__capability header = set_address(root, h);
         address_t recorded_end = header[0];
         if (b == h + HEADER_WORDS) {
           if (e != recorded_end)
             return ALLOC_INVALID;
           if (read_shadow(b) != ShadowLive)
             return ALLOC_INVALID;  // Defence in depth: payloads are unpainted.
           paint_shadow(b, e, ShadowQuarantined);
           *revoker = 0;              // Sweep: untag every capability to the payload.
           paint_shadow(b, e, ShadowLive);
           return ALLOC_OK;
         }
         h = recorded_end;             // Follow the protected chain, not payloads.
       }
       return ALLOC_INVALID;
     }
  *)

  Definition allocator_free_asm : list (list asm_code) :=
    [ [ (* Reject every non-capability word, including null. *)
        getwtype ct3 ca0;
        sub ct3 ct3 (encodeWordType wt_cap);
        jnz (".free_invalid")%asm ct3
      ];
      [ gettag ct3 ca0;
        sub ct3 ct3 1;
        jnz (".free_invalid")%asm ct3;
        (* Check bounds against the allocated prefix, ignoring the cursor. *)
        load ct0 cgp;
        getb ct1 ca0;
        gete ct2 ca0;
        getb ct3 ct0;
        lt ct3 ct3 ct1;
        jnz (".free_base_ok")%asm ct3;
        jmp (".free_invalid")%asm;
        #".free_base_ok";
        lt ct3 ct1 ct2;
        jnz (".free_nonempty")%asm ct3;
        jmp (".free_invalid")%asm;
        #".free_nonempty";
        geta ct3 ct0;
        lt ct3 ct3 ct2;
        jnz (".free_invalid")%asm ct3
      ];
      [ (* Rederive the first header from the trusted heap root. [ct0] keeps
           the bump cursor; [ct4] traverses headers with full heap bounds. *)
        mov ct4 ct0;
        getb ct3 ct0;
        geta ca2 ct0;
        sub ct3 ct3 ca2;
        add ct3 ct3 1;
        lea ct4 ct3
      ];
      [ #".free_search";
        (* An empty chain, or reaching its end, means no allocation matched. *)
        geta ct3 ct4;
        geta ca2 ct0;
        lt ct3 ct3 ca2;
        jnz (".free_header")%asm ct3;
        jmp (".free_invalid")%asm
      ];
      [ #".free_header";
        (* Both payload bounds must match; the reserved addresses are unused. *)
        load ca2 ct4;
        geta ct3 ct4;
        add ct3 ct3 allocator_header_words;
        sub ct3 ct3 ct1;
        jnz (".free_next")%asm ct3;
        sub ct3 ca2 ct2;
        jnz (".free_invalid")%asm ct3;
        jmp (".free_found")%asm
      ];
      [ #".free_next";
        (* The recorded end is the next header address, including after free.
           No caller-supplied address or payload word controls this step. *)
        geta ct3 ct4;
        sub ct3 ca2 ct3;
        lea ct4 ct3;
        jmp (".free_search")%asm
      ];
      ASM_Label ".free_found" :: fetch_asm allocator_shadow_import_off ctp ct3 ca2;
      [ (* Translate the matched payload base to its shadow entry. *)
        getb ct3 ct0;
        sub ct3 ct1 ct3;
        lea ctp ct3;
        (* Defence in depth: every payload is unpainted at entry (live ones,
           and revoked ones after the unpaint), so this check cannot fail
           once the header matches. Compare against the machine's encoding
           rather than assuming live is zero. *)
        load ct3 ctp;
        sub ct3 ct3 (encodeAllocStatus ShadowLive);
        jnz (".free_invalid")%asm ct3;
        (* Paint only the complete payload; its header remains accessible. *)
        sub ca2 ct2 ct1
      ];
      allocator_paint_asm ctp ca2 ShadowQuarantined;
      [ #".free_success";
        (* Clear the argument registers: no register then holds a capability
           to the freed allocation. *)
        mov ca0 ALLOC_OK;
        mov ca1 0
      ];
      fetch_asm allocator_revoker_import_off ct3 ct4 ca2;
      [ (* Sweep memory: every capability to the painted payload loses its tag. *)
        store ct3 0;
        (* Rewind the shadow cursor to the payload base and reset the count. *)
        sub ct4 ct1 ct2;
        lea ctp ct4;
        sub ca2 ct2 ct1
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

  Definition assembled_allocator_free' :=
    Eval vm_compute in assemble_block allocator_free_asm.

  Definition assembled_allocator_free :=
    Eval cbv in revert_regs_code_block assembled_allocator_free'.

  Definition assembled_allocator_free_n (n : nat) : list instr :=
    default [] (assembled_allocator_free !! n).

  Definition allocator_free_instrs_n (n : nat) : list Word :=
    encodeInstrsW (assembled_allocator_free_n n).

  Definition allocator_free_instrs : list Word :=
    concat (encodeInstrsW <$> assembled_allocator_free).

  Definition allocator_code : list Word :=
    allocator_malloc_instrs ++ allocator_free_instrs.

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

  Definition allocator_malloc_nargs : nat := 1.

  Definition allocator_free_nargs : nat := 1.

  Definition allocator_malloc_pcc_off : nat := 3.

  Definition allocator_free_pcc_off : nat :=
    allocator_malloc_pcc_off + length allocator_malloc_instrs.

  Definition allocator_malloc_exp_tbl_off : nat := 2.

  Definition allocator_free_exp_tbl_off : nat := 3.

  Definition allocator_export_table_entries : list Word :=
    [WInt (encode_entry_point allocator_malloc_nargs allocator_malloc_pcc_off);
     WInt (encode_entry_point allocator_free_nargs allocator_free_pcc_off)].

  (** This executable implementation uses affine translation, without
      restricting other instances of the parameterized machine model.
      Initialization must provide the whole heap and its clear shadow table;
      in particular, the reserved root bit must remain clear. *)

  Class allocatorLayoutWf `{allocatorLayout} : Prop := mkAllocatorLayoutWf {
    allocator_otype_size : (AllocOtype < AllocOtype ^+ 1)%ot;
    allocator_revoker_size : (revoker_addr < revoker_addr ^+ 1)%a;
    allocator_translation_affine : forall a,
      heap_to_shadow a = translate_region heap_b heap_e shadow_b a;
    allocator_size_imports :
      (allocator_pcc_b + length allocator_imports)%a = Some allocator_code_b;
    allocator_size_code :
      (allocator_code_b + length allocator_code)%a = Some allocator_pcc_e;
    allocator_size_data :
      (allocator_cgp_b + length allocator_data)%a = Some allocator_cgp_e;
    allocator_size_exports :
      (allocator_exp_tbl_b + (2 + length allocator_export_table_entries))%a =
      Some allocator_exp_tbl_e;
    allocator_regions_disjoint :
      ## [finz.seq_between allocator_pcc_b allocator_pcc_e;
          finz.seq_between allocator_cgp_b allocator_cgp_e;
          finz.seq_between allocator_exp_tbl_b allocator_exp_tbl_e;
          finz.seq_between heap_b heap_e;
          finz.seq_between shadow_b shadow_e];
  }.

  Definition allocator_export_table `{allocatorLayout} : list Word :=
    [WCap true RX Global allocator_pcc_b allocator_pcc_e allocator_pcc_b;
     WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b]
      ++ allocator_export_table_entries.

  (** Compartment memory contains imports followed by code, the bump
      capability, and the export table. Heap contents and the initially
      clear shadow table are supplied separately by the enclosing system. *)

  Definition allocator_initial_memory `{allocatorLayout} : Mem :=
    list_to_map (zip (finz.seq_between allocator_pcc_b allocator_pcc_e)
      (allocator_imports ++ allocator_code)) ∪
    list_to_map (zip (finz.seq_between allocator_cgp_b allocator_cgp_e)
      allocator_data) ∪
    list_to_map (zip (finz.seq_between allocator_exp_tbl_b allocator_exp_tbl_e)
      allocator_export_table).

  Definition allocator_malloc_pcc_addr `{allocatorLayout} : Addr :=
    (allocator_pcc_b ^+ allocator_malloc_pcc_off)%a.

  Definition allocator_free_pcc_addr `{allocatorLayout} : Addr :=
    (allocator_pcc_b ^+ allocator_free_pcc_off)%a.

  (** These export descriptors can be sealed with the switcher's ordinary
      entry key. There is no allocator-specific seal or authorization token. *)

  Definition allocator_malloc `{allocatorLayout} (g : Locality) : Sealable :=
    SCap true RO g allocator_exp_tbl_b allocator_exp_tbl_e
      (allocator_exp_tbl_b ^+ allocator_malloc_exp_tbl_off)%a.

  Definition allocator_free `{allocatorLayout} (g : Locality) : Sealable :=
    SCap true RO g allocator_exp_tbl_b allocator_exp_tbl_e
      (allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off)%a.

End Allocator.
