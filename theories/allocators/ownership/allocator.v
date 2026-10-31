From griotte Require Import machine_parameters assembler switcher fetch.
From griotte.allocators.common Require Export allocator_common_code.

(** A compartment providing a bump allocator and range quarantine.
    The data capability retains authority over the whole heap; its cursor
    records the first unused address. The first heap address is never allocated
    or quarantined, so loading this capability always sees a clear shadow bit.

    Both entries take an allocator capability in [ca0], in the style of
    CHERIoT-RTOS: a capability sealed with [AllocOtype] (see
    [allocator_capability]) pointing to a static word that holds its owner
    identifier. Only the allocator can unseal it, with its imported unsealing
    key. A malformed allocator capability is not checked dynamically: the
    machine traps on [unseal] or on the following [load], as in the KVS.

    [malloc] takes a positive number of words in [ca1]. It zeroes the new
    allocation, clears its shadow entries, and returns an exactly bounded
    [RW Global] capability in [ca0]. Each allocation has three protected header
    words before its payload: the original end, the owner identifier of the
    allocator capability, and a reserved address initialized to zero; their
    shadow entries are painted. [free] takes the capability to free in [ca1].
    It checks the header locally, as CHERIoT does: the supplied base must be
    the first unpainted word after a painted header, the supplied end must
    match the end recorded in that header, and the owner identifier of the
    allocator capability must match the owner recorded there. It paints
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

(* Notes for specifications. [allocator_owner_asm] runs first in both entries
   and leaves the owner identifier in [ctp]; [free]
   then moves it to [ca0], since [ctp] later holds the shadow capability. The
   only new invalid path is an owner mismatch in [free]; a non-integer owner
   word traps on the comparison. Invariants must ensure that every capability
   sealed with [AllocOtype] reachable by callers is an [allocator_capability]
   on a read-only owner word, that the unsealing key does not leak, and that
   the second header word of every allocation stores its owner. *)

Section Allocator.
  Import Asm_Griotte.
  Context `{MP : MachineParameters}.
  #[local] Coercion Z.of_nat : nat >-> Z.

  (** Load the owner identifier of the allocator capability [rsealed] into
      [rdst], using the imported unsealing key. An allocator capability that
      is not sealed traps on [unseal]; one sealed with another otype unseals
      to an untagged capability and traps on [load]. *)

  Definition allocator_owner_asm (rdst rsealed : RegName) : list asm_code :=
    fetch_asm ".Limport_unsealing_key" rdst ++
    [ unseal rdst rdst rsealed;
      load rdst rdst
    ].

  (** The assembled macro, where [off] is the resolved offset of the unsealing
      key from the address of the fetch. *)
  Definition allocator_owner (off : Z) (rdst rsealed : RegName) : list instr :=
    fetch off rdst ++
    [ machine_instructions.UnSeal rdst rdst rsealed;
      machine_instructions.CLoad rdst rdst 0 ].

  Definition allocator_owner_instrs (off : Z) (rdst rsealed : RegName) : list Word :=
    encodeInstrsW (allocator_owner off rdst rsealed).

  (** [ctp] holds the owner identifier until it is stored in the header,
      [ca1] the requested size,
      [ct0] the full heap capability with its cursor at the new header,
      [ct1] the payload base, [ct2] its end, and [ca4] the result capability.
      Capacity includes all three header words. Bounds are checked
      using integer subtraction before any capability address is advanced.
      The memory is zeroed before its shadow entries are cleared, and the
      bump pointer is published only after both loops complete. *)
  (* CHERI-C-style overview (schematic; addresses and sizes count machine words).
     HEADER_WORDS is 3; [integer] denotes the machine's mathematical integers.
     [set_address] changes only a capability's cursor; [set_bounds(c, n)]
     bounds it to the n words starting at that cursor. [base], [end], and
     [address] inspect capability fields. Shadow access uses the private import.

     malloc(sealed_alloc, request) {
       owner_t owner = *token_unseal(alloc_key, sealed_alloc); // Traps if invalid.
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
       root[1] = owner;                // Header: owner identifier.
       root[2] = 0;                    // Header: reserved address.
       for (integer i = 0; i < n; ++i)
         payload[i] = 0;
       paint_shadow(h, b, ShadowQuarantined);  // Header words.
       paint_shadow(b, e, ShadowLive);
       *bump_slot = set_address(root, e);
       return payload;
     }
  *)

  Definition allocator_malloc_asm : list (list asm_code) :=
    [ #".Lmalloc_owner" :: allocator_owner_asm ctp ca0;
      [ (* Reject noninteger and nonpositive sizes before touching the heap. *)
        getwtype ca3 ca1;
        sub ca3 ca3 (encodeWordType wt_int);
        jnez (".malloc_invalid")%asm ca3;
        lt ca3 0 ca1;
        jnez (".malloc_size_ok")%asm ca3;
        jmp (".malloc_invalid")%asm
      ];
      [ #".malloc_size_ok";
        (* Leave room for all three header words before checking the payload size.
           A negative remaining capacity also takes the no-memory branch. *)
        load ct0 cgp;
        geta ct1 ct0;
        gete ct2 ct0;
        sub ca3 ct2 ct1;
        sub ca3 ca3 allocator_header_words;
        lt ca3 ca3 ca1;
        jnez (".malloc_no_memory")%asm ca3;
        (* Bound the returned capability to the payload, excluding its header. *)
        add ct1 ct1 allocator_header_words;
        add ct2 ct1 ca1;
        mov ca4 ct0;
        lea ca4 ca4 allocator_header_words;
        subseg ca4 ca4 ct1 ct2;
        (* Record the immutable end and owner, and initialize the reserved
           address. The header's shadow entries are painted below. *)
        store ct0 ct2;
        store_imm ct0 ctp 1;
        store_imm ct0 0 2;
        mov ca2 ca4
      ] ++
      (* The shadow capability, for the shadow segment. *)
      fetch_asm ".Limport_shadow" ctp
    ] ++ allocator_malloc_shadow_asm ++
    [ [ (* Skip the header and payload, publishing only after initialization. *)
        lea ct0 ct0 allocator_header_words;
        lea ct0 ct0 ca1;
        store cgp ct0;
        mov ca0 ca4;
        mov ca1 0;
        jmp (".malloc_return")%asm
      ]
    ] ++ allocator_malloc_exit_asm.

  (** [free] accepts, in [ca1], a tagged ordinary capability whose base and
      end exactly match an original payload, whose header records the owner
      identifier of the allocator capability in [ca0]. The owner block
      unseals it, and the owner identifier then replaces it in [ca0].
      Header words are painted and payloads, the reserved root address and
      the unused suffix are not, so a base
      whose previous word is painted and which is itself unpainted is a
      payload base; its header is the three words below it. The check never
      interprets payload contents as headers. Its cursor and permissions do
      not determine which allocation is freed.
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

     free(sealed_alloc, request) {
       owner_t owner = *token_unseal(alloc_key, sealed_alloc); // Traps if invalid.
       if (!is_tagged_ordinary_capability(request))
         return ALLOC_INVALID;

       word_t *__capability root = *bump_slot;
       address_t next = address(root);
       address_t b = base(request), e = end(request);
       if (!(base(root) < b && b < e && e <= next))
         return ALLOC_INVALID;

       // Local header check: the last header word is painted, the base is not.
       if (read_shadow(b - 1) != ShadowQuarantined)
         return ALLOC_INVALID;
       if (read_shadow(b) != ShadowLive)
         return ALLOC_INVALID;
       word_t *__capability header = set_address(root, b - HEADER_WORDS);
       if (e != header[0])           // The recorded payload end.
         return ALLOC_INVALID;
       if (header[1] != owner)
         return ALLOC_INVALID;       // Owned by another allocator capability.
       paint_shadow(b, e, ShadowQuarantined);
       *revoker = 0;                 // Sweep: untag every capability to the payload.
       paint_shadow(b, e, ShadowLive);
       return ALLOC_OK;
     }
  *)

  Definition allocator_free_asm : list (list asm_code) :=
    [ #".Lfree_owner" :: allocator_owner_asm ctp ca0;
      [ (* Keep the owner in [ca0]: [ctp] receives the shadow capability. *)
        mov ca0 ctp;
        (* Reject every non-capability word, including null. *)
        getwtype ca3 ca1;
        sub ca3 ca3 (encodeWordType wt_cap);
        jnez (".free_invalid")%asm ca3
      ];
      [ gettag ca3 ca1;
        sub ca3 ca3 1;
        jnez (".free_invalid")%asm ca3;
        (* Check bounds against the allocated prefix, ignoring the cursor. *)
        load ct0 cgp;
        getb ct1 ca1;
        gete ct2 ca1;
        getb ca3 ct0;
        lt ca3 ca3 ct1;
        jnez (".free_base_ok")%asm ca3;
        jmp (".free_invalid")%asm;
        #".free_base_ok";
        lt ca3 ct1 ct2;
        jnez (".free_nonempty")%asm ca3;
        jmp (".free_invalid")%asm;
        #".free_nonempty";
        geta ca3 ct0;
        lt ca3 ca3 ct2;
        jnez (".free_invalid")%asm ca3
      ];
      fetch_asm ".Limport_shadow" ctp;
      [ (* Translate the word below the payload base to its shadow entry. *)
        getb ca3 ct0;
        sub ca3 ct1 ca3;
        sub ca3 ca3 1;
        lea ctp ctp ca3;
        (* The last header word is painted. Compare against the machine's
           encoding rather than assuming quarantined is one. *)
        load ca3 ctp;
        sub ca3 ca3 (encodeAllocStatus ShadowQuarantined);
        jnez (".free_invalid")%asm ca3;
        (* The payload base is unpainted. *)
        lea ctp ctp 1;
        load ca3 ctp;
        sub ca3 ca3 (encodeAllocStatus ShadowLive);
        jnez (".free_invalid")%asm ca3;
        (* Rederive the header from the trusted heap root, never by [Subseg],
           and compare the recorded end. *)
        mov ca4 ct0;
        geta ca3 ct0;
        sub ca3 ct1 ca3;
        sub ca3 ca3 allocator_header_words;
        lea ca4 ca4 ca3;
        load ca2 ca4;
        sub ca3 ca2 ct2;
        jnez (".free_invalid")%asm ca3;
        (* The recorded owner is the owner of the allocator capability. *)
        load_imm ca3 ca4 1;
        sub ca3 ca3 ca0;
        jnez (".free_invalid")%asm ca3;
        (* Paint only the complete payload; its header remains accessible. *)
        sub ca2 ct2 ct1
      ] ++
      (* The revoker capability, for the tail. *)
      fetch_asm ".Limport_revoker" ca3
    ] ++ allocator_free_tail_asm.

  (** [malloc] and [free] form one program, after the imports. *)
  Definition allocator_asm : list (list asm_code) :=
    allocator_with_imports (allocator_malloc_asm ++ allocator_free_asm).

  Definition assembled_allocator :=
    Eval compute in assemble_block allocator_asm.
  Lemma allocator_assembles : asm_ok (assemble_block_check allocator_asm).
  Proof. asm_check. Qed.

  Definition assembled_allocator_malloc :=
    Eval compute in take (length allocator_malloc_asm) assembled_allocator.

  Definition assembled_allocator_malloc_n (n : nat) : list instr :=
    default [] (assembled_allocator_malloc !! n).

  Definition allocator_malloc_instrs_n (n : nat) : list Word :=
    encodeInstrsW (assembled_allocator_malloc_n n).

  Definition allocator_malloc_instrs : list Word :=
    concat (encodeInstrsW <$> assembled_allocator_malloc).

  Definition assembled_allocator_free :=
    Eval compute in drop (length allocator_malloc_asm) assembled_allocator.

  Definition assembled_allocator_free_n (n : nat) : list instr :=
    default [] (assembled_allocator_free !! n).

  Definition allocator_free_instrs_n (n : nat) : list Word :=
    encodeInstrsW (assembled_allocator_free_n n).

  Definition allocator_free_instrs : list Word :=
    concat (encodeInstrsW <$> assembled_allocator_free).

  (** The offsets of the fetches of the unsealing key by [allocator_owner_asm]
      at the start of each entry (the labels [.L<entry>_owner]), from the
      address of the fetch. *)
  Definition allocator_malloc_owner_off : Z :=
    Eval vm_compute in
      label_offset_from (concat allocator_asm) ".Lmalloc_owner" ".Limport_unsealing_key".

  Definition allocator_free_owner_off : Z :=
    Eval vm_compute in
      label_offset_from (concat allocator_asm) ".Lfree_owner" ".Limport_unsealing_key".

  Definition allocator_code : list Word :=
    allocator_malloc_instrs ++ allocator_free_instrs.

  Definition allocator_malloc_nargs : nat := 2.

  Definition allocator_free_nargs : nat := 2.

  (** The minimum stack sizes of [malloc] and [free]: neither uses its
      stack. *)
  Definition allocator_malloc_min_stack : nat := 0.

  Definition allocator_free_min_stack : nat := 0.

  (** The offset of the entry of [free] from the start of the PCC. *)
  Definition allocator_free_pcc_off : nat :=
    Eval vm_compute in label_offset (concat allocator_asm) ".Lfree_owner".

  Lemma allocator_free_pcc_off_eq :
    allocator_free_pcc_off = allocator_malloc_pcc_off + length allocator_malloc_instrs.
  Proof. reflexivity. Qed.

  Definition allocator_export_table_entries : list Word :=
    [WInt (encode_entry_point InterruptEnabled allocator_malloc_nargs allocator_malloc_min_stack
             allocator_malloc_pcc_off);
     WInt (encode_entry_point InterruptEnabled allocator_free_nargs allocator_free_min_stack
             allocator_free_pcc_off)].

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
      (allocator_exp_tbl_b + (ExportTable_offset_entries + length allocator_export_table_entries))%a =
      Some allocator_exp_tbl_e;
    allocator_regions_disjoint :
      ## [finz.seq_between allocator_pcc_b allocator_pcc_e;
          finz.seq_between allocator_cgp_b allocator_cgp_e;
          finz.seq_between allocator_exp_tbl_b allocator_exp_tbl_e;
          finz.seq_between heap_b heap_e;
          finz.seq_between shadow_b shadow_e];
  }.

  #[global] Instance allocator_layout_common_wf `{allocatorLayout} `{!allocatorLayoutWf} :
    allocatorCommonLayoutWf.
  Proof.
    constructor.
    - exact allocator_otype_size.
    - exact allocator_revoker_size.
    - exact allocator_translation_affine.
    - exact allocator_size_imports.
    - exact allocator_size_data.
    - exact allocator_regions_disjoint.
  Qed.

  Definition allocator_free_pcc_addr `{allocatorLayout} : Addr :=
    (allocator_pcc_b ^+ allocator_free_pcc_off).

  (** An allocator capability: a read-only capability on the static word [a],
      which holds the owner identifier, sealed with the allocator's otype. *)

  Definition allocator_capability_scap (g : Locality) (a : Addr) : Sealable :=
    SCap true RO g a (a ^+ 1) a.

  Definition allocator_capability `{allocatorLayout} (g : Locality) (a : Addr) : Word :=
    WSealed AllocOtype (allocator_capability_scap g a).

End Allocator.
