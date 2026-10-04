From griotte Require Import machine_parameters assembler fetch assert switcher.
From griotte.allocator Require Import allocator.

Section Heap_Temporal_Safety.
  Import Asm_Griotte.
  Context `{MP : MachineParameters}.
  Local Coercion Z.of_nat : nat >-> Z.

  (** Heap temporal safety, without address reuse:

      p = 0;
      buf = malloc(sealed_alloc, 1);
      if (malloc failed) halt;
      saved_buf = buf;
      buf[0] = 0;
      adv(buf);
      buf = saved_buf;             // this load consults the shadow table
      buf[0] = &p;
      if (free(sealed_alloc, buf) failed) halt;
      adv(0);
      assert(p == 0);
      halt;

      [sealed_alloc] is the imported allocator capability of this
      compartment ([allocator_capability]): it points to a read-only word in
      the compartment's static sealed region holding [hts_main_owner_id].
      It is never shared with the adversary; [free] only succeeds with an
      allocator capability whose owner matches the allocation header. The
      adversary has its own allocator capability, with owner
      [hts_adv_owner_id]: it can allocate and free its own buffers, but
      freeing [buf] returns ALLOC_INVALID, so it cannot quarantine [buf].
      Only [buf] is shared. [p] is the only word of the compartment's CGP
      data. [saved_buf] is a stack slot, the first word of main's stack: it
      lies below the frame that the switcher pushes and hands to the callees,
      so no callee can reach it.
      There is no claim operation and no tag check: [buf] is still live when
      it is reloaded, since only main can free it, and no adversary executes
      between this load and our call to free.
      Quarantine clears tags on subsequent capability loads, not on values
      already in registers. The switcher clears the adversary's registers
      when it returns, so a retained alias must later be loaded again. *)

  Definition hts_switcher_offset : Z := 0.
  Definition hts_assert_offset : Z := 1.
  Definition hts_adv_offset : Z := 2.
  Definition hts_malloc_offset : Z := 3.
  Definition hts_free_offset : Z := 4.
  Definition hts_alloc_cap_offset : Z := 5.

  (** Owner identifiers of the allocator capabilities of main and of the
      adversary. They differ, so the adversary cannot free main's buffer. *)
  Definition hts_main_owner_id : Z := 1.
  Definition hts_adv_owner_id : Z := 2.

  (** Each assembler block is also available to the local instruction proofs.
      Labels identify branch destinations and do not occupy machine memory. *)
  Definition hts_main_asm : list (list asm_code) :=
    [
      [
        (* p = 0; buf = malloc(sealed_alloc, 1); *)
        store_imm cgp (0)%asm 0;
        mov ca1 (1)%asm
      ];
      fetch_asm hts_alloc_cap_offset ca0 ct0 ct2;
      fetch_asm hts_switcher_offset ctp ct0 ct2;
      fetch_asm hts_malloc_offset ct1 ct0 ct2;
      [
        jalr cra ctp
      ];
      [
        (* if (malloc failed) halt; the result is tagged only on success:
           allocator errors and switcher failures return an integer in ca0. *)
        gettag ct0 ca0;
        jnz (".hts_malloc_result_end")%asm ct0;
        halt;
        #".hts_malloc_result_end"
      ];
      [
        (* saved_buf = buf (stack slot below the callee frame); buf[0] = 0; *)
        store_imm csp ca0 0;
        lea csp 1;
        store_imm ca0 (0)%asm 0
      ];
      fetch_asm hts_switcher_offset ctp ct0 ct2;
      fetch_asm hts_adv_offset ct1 ct0 ct2;
      [
        (* adv(buf); *)
        jalr cra ctp
      ];
      [
        (* buf = saved_buf; the load consults the shadow table. *)
        load_imm ca0 csp (-1)%Z
      ];
      [
        (* buf[0] = &p; cgp covers exactly p. *)
        store_imm ca0 cgp 0;
        (* The buffer to free is the second argument. *)
        mov ca1 ca0
      ];
      fetch_asm hts_alloc_cap_offset ca0 ct0 ct2;
      fetch_asm hts_switcher_offset ctp ct0 ct2;
      fetch_asm hts_free_offset ct1 ct0 ct2;
      [
        (* free(sealed_alloc, buf); halt if free or the switcher fails. *)
        jalr cra ctp
      ];
      [
        (* ca0 is ALLOC_OK = 0 only after a successful free. A nonzero value
           is a switcher failure: buf is then still live and holds &p, so we
           must halt. *)
        jnz (".hts_free_result_bad")%asm ca0;
        jmp (".hts_free_result_end")%asm;
        #".hts_free_result_bad";
        halt;
        #".hts_free_result_end"
      ];
      [
        (* adv(0); the dangling buffer is no longer passed. *)
        mov ca0 (0)%asm
      ];
      fetch_asm hts_switcher_offset ctp ct0 ct2;
      fetch_asm hts_adv_offset ct1 ct0 ct2;
      [
        jalr cra ctp
      ];
      [
        (* assert(p == 0); *)
        load_imm ct0 cgp 0;
        mov ct1 (0)%asm
      ];
      concat (assert_asm hts_assert_offset ct2 ct3 ct4);
      [
        (* halt; *)
        halt
      ]
    ].

  Definition assembled_hts_main' :=
    Eval vm_compute in assemble_block hts_main_asm.
  Definition assembled_hts_main :=
    Eval cbv in revert_regs_code_block assembled_hts_main'.
  Definition assembled_hts_main_n (n : nat) : list instr :=
    default [] (assembled_hts_main !! n).
  Definition hts_main_instrs_n (n : nat) : list Word :=
    encodeInstrsW (assembled_hts_main_n n).
  Definition hts_main_code : list Word :=
    concat (encodeInstrsW <$> assembled_hts_main).

  Definition hts_main_data : list Word := [WInt 0].

  (** The owner word of the allocator capability. It lives in the static
      sealed region, outside the heap and the compartment's data, and is
      only reachable through the sealed capability. *)
  Definition hts_main_static_sealed : list Word := [WInt hts_main_owner_id].

  (** [owner_a] is the address of the owner word, the first address of the
      main compartment's static sealed region. *)
  Definition hts_main_imports `{!switcherLayout} `{!assertLayout}
      `{!allocatorLayout} (owner_a : Addr) (adv_f : Sealable) : list Word :=
    [WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call;
     WSentry true RX Global b_assert e_assert b_assert;
     WSealed ot_switcher adv_f;
     WSealed ot_switcher (allocator_malloc Global);
     WSealed ot_switcher (allocator_free Global);
     allocator_capability Global owner_a].

  (** The adversary's owner word, in its own static sealed region. *)
  Definition hts_adv_static_sealed : list Word := [WInt hts_adv_owner_id].

  (** [owner_a] is the address of the adversary's owner word. *)
  Definition hts_adv_imports `{!switcherLayout} `{!allocatorLayout}
      (owner_a : Addr) : list Word :=
    [WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call;
     WSealed ot_switcher (allocator_malloc Global);
     WSealed ot_switcher (allocator_free Global);
     allocator_capability Global owner_a].

End Heap_Temporal_Safety.
