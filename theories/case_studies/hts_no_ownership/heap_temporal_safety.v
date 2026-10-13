From griotte Require Import machine_parameters assembler fetch assert switcher.
From griotte.allocators.no_ownership Require Import allocator.

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

      Only [buf] is shared. [p] is the only word of the compartment's CGP
      data. [saved_buf] is a stack slot, the first word of main's stack: it
      lies below the frame that the switcher pushes and hands to the callees,
      so no callee can reach it.
      There is no claim operation: the tag check handles early quarantine,
      and no adversary executes between this check and our call to free.
      Quarantine clears tags on subsequent capability loads, not on values
      already in registers. The switcher clears the adversary's registers
      when it returns, so a retained alias must later be loaded again. *)

  (** Each assembler block is also available to the local instruction proofs.
      Labels identify branch destinations and do not occupy machine memory.
      The data symbols [#@] name the entries of the import table, which
      precedes the code. *)
  Definition hts_main_asm : list (list asm_code) :=
    [
      [
        (* the imports *)
        #@".Limport_switcher";
        #@".Limport_assert";
        #@".Limport_adv";
        #@".Limport_malloc";
        #@".Limport_free";
        #".Lhts_main";

        (* p = 0; buf = malloc(1); *)
        store_imm cgp (0)%asm 0;
        mov ca0 (1)%asm
      ];
      #".Lhts_fetch_switcher_malloc" ::
      fetch_asm ".Limport_switcher" ctp;
      #".Lhts_fetch_malloc" ::
      fetch_asm ".Limport_malloc" ct1;
      [
        #".Lhts_call_malloc";
        jalr cra ctp
      ];
      [
        #".Lhts_malloc_result";
        (* if (malloc failed) halt; the result is tagged only on success:
           allocator errors and switcher failures return an integer in ca0. *)
        gettag ct0 ca0;
        jnz (".hts_malloc_result_end")%asm ct0;
        halt;
        #".hts_malloc_result_end"
      ];
      [
        #".Lhts_share";
        (* saved_buf = buf (stack slot below the callee frame); buf[0] = 0; *)
        store_imm csp ca0 0;
        lea csp 1;
        store_imm ca0 (0)%asm 0
      ];
      #".Lhts_fetch_switcher_adv_1" ::
      fetch_asm ".Limport_switcher" ctp;
      #".Lhts_fetch_adv_1" ::
      fetch_asm ".Limport_adv" ct1;
      [
        #".Lhts_call_adv_1";
        (* adv(buf); *)
        jalr cra ctp
      ];
      [
        #".Lhts_reload";
        (* buf = saved_buf; the load consults the shadow table. *)
        load_imm ca0 csp (-1)%Z
      ];
      [
        #".Lhts_check_buffer";
        (* if (!tag(buf)) halt; the adversary may have freed it. *)
        gettag ct0 ca0;
        jnz (".hts_check_buffer_end")%asm ct0;
        halt;
        #".hts_check_buffer_end"
      ];
      [
        #".Lhts_store_private";
        (* buf[0] = &p; cgp covers exactly p. *)
        store_imm ca0 cgp 0
      ];
      #".Lhts_fetch_switcher_free" ::
      fetch_asm ".Limport_switcher" ctp;
      #".Lhts_fetch_free" ::
      fetch_asm ".Limport_free" ct1;
      [
        #".Lhts_call_free";
        (* free(buf); halt if free or the switcher fails. *)
        jalr cra ctp
      ];
      [
        #".Lhts_free_result";
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
        #".Lhts_zero_arg";
        (* adv(0); the dangling buffer is no longer passed. *)
        mov ca0 (0)%asm
      ];
      #".Lhts_fetch_switcher_adv_2" ::
      fetch_asm ".Limport_switcher" ctp;
      #".Lhts_fetch_adv_2" ::
      fetch_asm ".Limport_adv" ct1;
      [
        #".Lhts_call_adv_2";
        jalr cra ctp
      ];
      [
        #".Lhts_prep_assert";
        (* assert(p == 0); *)
        load_imm ct0 cgp 0;
        mov ct1 (0)%asm
      ];
      #".Lhts_assert" ::
      assert_asm ".Limport_assert" ct2 ca2;
      [
        #".Lhts_halt";
        (* halt; *)
        halt
      ]
    ].

  Definition assembled_hts_main :=
    Eval compute in assemble_block hts_main_asm.
  Lemma hts_main_assembles : asm_ok (assemble_block_check hts_main_asm).
  Proof. asm_check. Qed.
  Definition assembled_hts_main_n (n : nat) : list instr :=
    default [] (assembled_hts_main !! n).
  Definition hts_main_instrs_n (n : nat) : list Word :=
    encodeInstrsW (assembled_hts_main_n n).
  (** The code of [main], as the chain of its blocks. *)
  Definition hts_main_code : list Word :=
    hts_main_instrs_n 0 ++
    hts_main_instrs_n 1 ++
    hts_main_instrs_n 2 ++
    hts_main_instrs_n 3 ++
    hts_main_instrs_n 4 ++
    hts_main_instrs_n 5 ++
    hts_main_instrs_n 6 ++
    hts_main_instrs_n 7 ++
    hts_main_instrs_n 8 ++
    hts_main_instrs_n 9 ++
    hts_main_instrs_n 10 ++
    hts_main_instrs_n 11 ++
    hts_main_instrs_n 12 ++
    hts_main_instrs_n 13 ++
    hts_main_instrs_n 14 ++
    hts_main_instrs_n 15 ++
    hts_main_instrs_n 16 ++
    hts_main_instrs_n 17 ++
    hts_main_instrs_n 18 ++
    hts_main_instrs_n 19 ++
    hts_main_instrs_n 20 ++
    hts_main_instrs_n 21 ++
    hts_main_instrs_n 22.

  Lemma hts_main_code_assembled :
    hts_main_code = concat (encodeInstrsW <$> assembled_hts_main).
  Proof. reflexivity. Qed.

  Definition hts_main_data : list Word := [WInt 0].

  Definition hts_main_imports `{!switcherLayout} `{!assertLayout}
      `{!allocatorLayout} (adv_f : Sealable) : list Word :=
    [WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call;
     WSentry true RX Global b_assert e_assert b_assert;
     WSealed ot_switcher adv_f;
     WSealed ot_switcher (allocator_malloc Global);
     WSealed ot_switcher (allocator_free Global)].

End Heap_Temporal_Safety.
