From griotte Require Import machine_parameters assembler fetch assert switcher.
From griotte.allocator Require Import allocator.

Section Heap_Temporal_Safety.
  Import Asm_Griotte.
  Context `{MP : MachineParameters}.
  Local Coercion Z.of_nat : nat >-> Z.

  (** Heap temporal safety, without address reuse:

      p = 0;
      buf = malloc(1);
      if (malloc failed) halt;
      saved_buf = buf;
      buf[0] = 0;
      adv(buf);
      buf = saved_buf;             // this load consults the shadow table
      if (!tag(buf)) halt;         // adv may have called free(buf)
      buf[0] = &p;
      if (free(buf) failed) halt;
      adv(0);
      assert(p == 0);
      halt;

      Only [buf] is shared. Both [p] and [saved_buf] are private CGP cells.
      There is no claim operation: the tag check handles early quarantine,
      and no adversary executes between this check and our call to free.
      Quarantine clears tags on subsequent capability loads, not on values
      already in registers. The switcher clears the adversary's registers
      when it returns, so a retained alias must later be loaded again. *)

  Definition hts_switcher_offset : Z := 0.
  Definition hts_assert_offset : Z := 1.
  Definition hts_adv_offset : Z := 2.
  Definition hts_malloc_offset : Z := 3.
  Definition hts_free_offset : Z := 4.

  (** Each assembler block is also available to the local instruction proofs.
      Labels identify branch destinations and do not occupy machine memory. *)
  Definition hts_main_asm : list (list asm_code) :=
    [
      [
        (* p = 0; buf = malloc(1); *)
        store_imm cgp (0)%asm 0;
        mov ca0 (1)%asm
      ];
      fetch_asm hts_switcher_offset ctp ct0 ct2;
      fetch_asm hts_malloc_offset ct1 ct0 ct2;
      [
        jalr cra ctp
      ];
      [
        (* if (malloc failed) halt; a switcher failure has ca1 = 0,
           so also check the result's type and tag. *)
        jnz (".hts_malloc_status_bad")%asm ca1;
        jmp (".hts_malloc_type")%asm;
        #".hts_malloc_status_bad";
        halt;
        #".hts_malloc_type";
        getwtype ct0 ca0;
        sub ct0 ct0 (encodeWordType wt_cap)%asm;
        jnz (".hts_malloc_type_bad")%asm ct0;
        jmp (".hts_malloc_tag")%asm;
        #".hts_malloc_type_bad";
        halt;
        #".hts_malloc_tag";
        gettag ct0 ca0;
        jnz (".hts_malloc_result_end")%asm ct0;
        halt;
        #".hts_malloc_result_end"
      ];
      [
        (* saved_buf = buf; buf[0] = 0; *)
        store_imm cgp ca0 1;
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
        load_imm ca0 cgp 1
      ];
      [
        (* if (!tag(buf)) halt; the adversary may have freed it. *)
        gettag ct0 ca0;
        jnz (".hts_check_buffer_end")%asm ct0;
        halt;
        #".hts_check_buffer_end"
      ];
      [
        (* buf[0] = &p; narrow cgp to its private first cell. *)
        mov ct0 cgp;
        getb ct1 ct0;
        add ct2 ct1 (1)%asm;
        subseg ct0 ct1 ct2;
        store_imm ca0 ct0 0
      ];
      fetch_asm hts_switcher_offset ctp ct0 ct2;
      fetch_asm hts_free_offset ct1 ct0 ct2;
      [
        (* free(buf); halt if free or the switcher fails. *)
        jalr cra ctp
      ];
      [
        (* Both result words are zero only after a successful free. *)
        jnz (".hts_free_result_bad")%asm ca0;
        jmp (".hts_free_status")%asm;
        #".hts_free_result_bad";
        halt;
        #".hts_free_status";
        jnz (".hts_free_status_bad")%asm ca1;
        jmp (".hts_free_result_end")%asm;
        #".hts_free_status_bad";
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

  Definition hts_main_data : list Word := [WInt 0; WInt 0].

  Definition hts_main_imports `{!switcherLayout} `{!assertLayout}
      `{!allocatorLayout} (adv_f : Sealable) : list Word :=
    [WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call;
     WSentry true RX Global b_assert e_assert b_assert;
     WSealed ot_switcher adv_f;
     WSealed ot_switcher (allocator_malloc Global);
     WSealed ot_switcher (allocator_free Global)].

End Heap_Temporal_Safety.
