From griotte Require Import machine_parameters griotte_opsem assembler fetch assert switcher.

(** * The error-handling example

    Three compartments: [main] (trusted, the thread starts there), [stats]
    (trusted, with a stackful error handler) and [adv] (untrusted, imports
    [stats_read]). The CHERIoT code:

    ```
// stats.cc: compartment "stats" (trusted, with an error handler)
static bool locked;

int __cheri_compartment("stats") stats_read(int *ptr)
{
	if (locked)
		return -EBUSY;
	locked = true;
	int v  = *ptr; // may fault: the caller's pointer
	locked = false;
	return v;
}

extern "C" ErrorRecoveryBehaviour
compartment_error_handler(ErrorState *frame, size_t mcause, size_t mtval)
{
	if (mcause == priv::MCAUSE_CHERI)
	{
		auto [code, reg] = CHERI::extract_cheri_mtval(mtval);
		if (code == CHERI::CauseCode::BoundsViolation &&
		    reg >= CHERI::RegisterNumber::CRA && reg <= CHERI::RegisterNumber::CA5)
		{
			// registers[i] is x(i+1): the word at offset reg of the ErrorState
			CHERI::Capability<void> c{frame->registers[int(reg) - 1]};
			// The retried load reads the base: it must not be in *frame,
			// which holds the saved context (and the globals of stats).
			ptraddr_t frameBase = reinterpret_cast<ptraddr_t>(frame);
			if (c.length() > 0 &&
			    (c.base() < frameBase || c.base() >= frameBase + sizeof(ErrorState)))
			{
				c.address() = c.base();             // back within bounds
				frame->registers[int(reg) - 1] = c; // the PC is unchanged:
				return ErrorRecoveryBehaviour::InstallContext; // retry
			}
		}
	}
	locked = false;
	return ErrorRecoveryBehaviour::ForceUnwind;
}

// main.cc: compartment "main" (trusted, thread start)
int __cheri_compartment("adv") adv(); // untrusted, imports stats_read

static constexpr int X_INIT = 42;
static int x = X_INIT;

void __cheri_compartment("main") run()
{
	adv();
	assert(stats_read(&x + 1) == X_INIT);                      // repaired, retried
	assert(stats_read(__builtin_cheri_tag_clear(&x)) == -ECOMPARTMENTFAIL); // unwound
	assert(stats_read(&x) == X_INIT);                          // the lock was released
}
    ```

    The handler reads the exact cause of the fault and the register that
    caused it. On a bounds violation on a general register whose saved
    capability has non-empty bounds and a base outside the [ErrorState],
    it moves that capability's address to its base and retries the
    faulting load. A base inside the [ErrorState] would make the retried
    load read the saved context, which holds the globals capability of
    [stats]: such a fault is unwound, like any other. On any other fault,
    it releases the lock and asks for the unwind: the caller gets
    [-ECOMPARTMENTFAIL]. Without the handler, a bad pointer would leave
    the lock held, and every later call would return [-EBUSY]. *)

(** ** [stats] *)
Section Stats.
  Import Asm_Griotte.
  #[local] Open Scope Z_scope.
  Context `{MP: MachineParameters}.

  (** CHERIoT's errno value, stored negated, as it is returned (like
      [ECOMPARTMENTFAIL] in [switcher]). *)
  Definition EBUSY : Z := -16.

  (** CHERIoT's [ErrorRecoveryBehaviour], the return values of an error
      handler. *)
  Definition InstallContext : Z := 0.
  Definition ForceUnwind : Z := 1.

  (** [stats_read(ptr)]: [ptr] in [ca0]; the lock is the first global, at
      [cgp]. Returns the value in [ca0], and 0 in [ca1]; the return path of
      the switcher clears the other registers. The load at [.Lread_load] is
      the fault site: the handler retries it, or asks for the unwind. *)
  Definition stats_read_asm : list (list asm_code) :=
    [ (* 0: the lock test *)
      [ #".Lstats_read";
        load ct0 cgp;
        jnez (".Lread_busy")%asm ct0 ];
      (* 1: take the lock *)
      [ #".Lread_lock";
        store cgp 1 ];
      (* 2: load through the caller's pointer, the fault site *)
      [ #".Lread_load";
        load ca0 ca0 ];
      (* 3: release the lock, return *)
      [ #".Lread_release";
        store cgp 0;
        mov ca1 0;
        ret ];
      (* 4: the lock is taken *)
      [ #".Lread_busy";
        mov ca0 EBUSY;
        mov ca1 0;
        ret ]
    ].

  (** The stackful error handler: [ca0] points to the [ErrorState] (word 0
      is the PC, words 1 to 15 the registers x1 to x15), [ca1] holds
      mcause and [ca2] mtval. Block 5 decodes the fault: a CHERI bounds
      violation on a register of the save area goes on to block 6, any
      other fault to block 8. Block 6 loads the saved capability of that
      register (the word at its index) and checks it: when its bounds are
      empty, or its base lies in the [ErrorState] (the [ErrorState_size]
      words from the cursor of [ca0]), it goes on to block 8. Otherwise
      block 7 moves its address to its base, stores it back and returns
      InstallContext: the faulting instruction runs again. Block 8
      releases the lock and returns ForceUnwind. *)
  Definition stats_handler_asm : list (list asm_code) :=
    [ (* 5: decode the cause and the register *)
      [ #".Lstats_handler";
        jne (".Lstats_handler_unwind")%asm ca1 MCAUSE_CHERI;
        land ct0 ca2 MTVAL_CODE_MASK;
        jne (".Lstats_handler_unwind")%asm ct0 (cause_code_num BoundsViolation);
        lshiftr ct0 ca2 MTVAL_REG_SHIFT;
        land ct0 ct0 MTVAL_REG_MASK;
        jlt (".Lstats_handler_unwind")%asm ct0 TrustedStack_offset_cra;
        jgt (".Lstats_handler_unwind")%asm ct0 TrustedStack_offset_ca5 ];
      (* 6: load the saved capability, check its bounds and its base *)
      [ #".Lstats_handler_check";
        lea ct1 ca0 ct0;
        load ct2 ct1;
        getlen ct0 ct2;
        jle (".Lstats_handler_unwind")%asm ct0 0;
        getb ct0 ct2;
        geta ctp ca0;
        jlt (".Lstats_handler_fix")%asm ct0 ctp;
        add ctp ctp ErrorState_size;
        jlt (".Lstats_handler_unwind")%asm ct0 ctp ];
      (* 7: repair the saved capability, retry *)
      [ #".Lstats_handler_fix";
        seta ct2 ct2 ct0;
        store ct1 ct2;
        mov ca0 InstallContext;
        ret ];
      (* 8: release the lock, unwind *)
      [ #".Lstats_handler_unwind";
        store cgp 0;
        mov ca0 ForceUnwind;
        ret ]
    ].

  Definition stats_asm : list (list asm_code) :=
    stats_read_asm ++ stats_handler_asm.

  (** The fields of the mtval encoding stay folded. *)
  Definition stats_assembled :=
    Eval cbv -[MTVAL_CODE_MASK MTVAL_REG_SHIFT MTVAL_REG_MASK cause_code_num mtval_encoding_mixin]
      in assemble_block stats_asm.
  Lemma stats_assembles : asm_ok (assemble_block_check stats_asm).
  Proof. asm_check. Qed.
  Definition stats_instrs_n (n : nat) : list Word :=
    encodeInstrsW (default [] (stats_assembled !! n)).

  Definition stats_read_code : list Word :=
    stats_instrs_n 0 ++
    stats_instrs_n 1 ++
    stats_instrs_n 2 ++
    stats_instrs_n 3 ++
    stats_instrs_n 4.

  Definition stats_handler_code : list Word :=
    stats_instrs_n 5 ++
    stats_instrs_n 6 ++
    stats_instrs_n 7 ++
    stats_instrs_n 8.

  Definition stats_code : list Word := stats_read_code ++ stats_handler_code.

  (** The lock, released. *)
  Definition stats_data : list Word := [WInt 0].

  #[local] Close Scope Z_scope.
  #[local] Coercion Z.of_nat : nat >-> Z.

  (** [stats] has no import: its code starts at the base of its PCC. *)
  Definition stats_read_nargs : nat := 1.
  (** The room for the [ErrorState] of the stackful handler. *)
  Definition stats_read_min_stack : nat := 16.
  (** The offset of the entry [.Lstats_read] from the start of the PCC. *)
  Definition stats_read_pcc_off : nat :=
    Eval vm_compute in label_offset (concat stats_asm) ".Lstats_read".
  Lemma stats_read_pcc_off_eq : stats_read_pcc_off = 0.
  Proof. reflexivity. Qed.
  (** The offset of the handler [.Lstats_handler] from the start of the
      PCC. *)
  Definition stats_handler_pcc_off : nat :=
    Eval vm_compute in label_offset (concat stats_asm) ".Lstats_handler".
  Lemma stats_handler_pcc_off_eq : stats_handler_pcc_off = length stats_read_code.
  Proof. reflexivity. Qed.

  Definition stats_exp_tbl_entry_read : Word :=
    WInt (encode_entry_point InterruptDisabled stats_read_nargs stats_read_min_stack
            stats_read_pcc_off).
  (** The index of the export [stats_read], in the order of the firmware. *)
  Definition stats_entry_read : nat := 0.
  Definition stats_read_exp_tbl_off : Z := ExportTable_offset_entry stats_entry_read.

  (** [stats] exports [stats_read] only. *)
  Definition stats_nb_exports : Z := 1.
  Definition length_stats_exports_tbl : Z := ExportTable_offset_entries + stats_nb_exports.

  (** The layout of [stats]: its PCC [[STATS_pcc_b, STATS_pcc_e)], with its
      code at [STATS_pcc_b'], its globals [[STATS_cgp_b, STATS_cgp_e)], the
      lock at [STATS_cgp_b], and its export table
      [[b_stats_exp_tbl, e_stats_exp_tbl)]. *)
  Class statsLayout : Type :=
    mkStatsLayout {
        STATS_pcc_b : Addr;
        STATS_pcc_b' : Addr;
        STATS_pcc_e : Addr;

        STATS_cgp_b : Addr;
        STATS_cgp_e : Addr;

        b_stats_exp_tbl : Addr;
        e_stats_exp_tbl : Addr;
      }.

  Class statsLayoutWf `{!statsLayout} : Type :=
    mkStatsLayoutWf {
        (* [stats] has no import: its code starts at the base of its PCC. *)
        STATS_size_imports : (STATS_pcc_b + 0)%a = Some STATS_pcc_b';

        STATS_size_code : (STATS_pcc_b' + length stats_code)%a = Some STATS_pcc_e;

        STATS_size_data : (STATS_cgp_b + length stats_data)%a = Some STATS_cgp_e;

        stats_exp_tbl_size : (b_stats_exp_tbl + length_stats_exports_tbl)%a = Some e_stats_exp_tbl;

        STATS_cgp_disjoint_from_shadow : disjoint_from_shadow STATS_cgp_b STATS_cgp_e;
        STATS_pcc_disjoint_from_shadow : disjoint_from_shadow STATS_pcc_b STATS_pcc_e;
        stats_exp_tbl_disjoint_from_shadow : disjoint_from_shadow b_stats_exp_tbl e_stats_exp_tbl;
        STATS_pcc_base_not_heap : is_heap_address STATS_pcc_b = false;
        STATS_cgp_base_not_heap : is_heap_address STATS_cgp_b = false;
        stats_export_base_not_heap : is_heap_address b_stats_exp_tbl = false
      }.

  Definition stats_read_exp_tbl_addr {STATS : statsLayout} : Addr :=
    (b_stats_exp_tbl ^+ stats_read_exp_tbl_off).
  (** The export of [stats_read], before its sealing by the switcher. *)
  Definition STATS_read {STATS : statsLayout} (g : Locality) : Sealable :=
    SCap true RO g b_stats_exp_tbl e_stats_exp_tbl stats_read_exp_tbl_addr.
End Stats.

(* [statsLayout] has no parameter: it takes no [Hint Mode]. *)
#[export] Hint Mode statsLayoutWf - + : typeclass_instances.

(** ** [main] *)
Section Main.
  Import Asm_Griotte.
  #[local] Open Scope Z_scope.
  Context `{MP: MachineParameters}.

  (** The initial value of the global [x]. *)
  Definition X_INIT : Z := 42.

  (** The main program. The data symbols [#@] name the entries of the
      import table, which precedes the code, in the order of
      [error_handling_main_imports]. The global [x] is at [cgp]. *)
  Definition error_handling_main_asm : list (list asm_code) :=
    [ (* 0: the imports; ctp -> switcher entry point *)
      [ #@".Limport_switcher";
        #@".Limport_assert";
        #@".Limport_adv";
        #@".Limport_stats_read";
        #".Lmain" ] ++
      fetch_asm ".Limport_switcher" ctp;
      (* 1: ct1 -> {adv.adv}_(ot_switcher) *)
      #".Lmain_fetch_adv" ::
      fetch_asm ".Limport_adv" ct1;
      (* 2: adv() *)
      [ #".Lmain_call_adv";
        mov cs0 cra; (* cs0 -> return-to-switcher *)
        jalr cra ctp ];
      (* 3: the capability of x, one past its end *)
      [ #".Lmain_ret_adv";
        lea ca0 cgp 1 ];
      (* 4: ctp -> switcher entry point *)
      #".Lmain_fetch_switcher_1" ::
      fetch_asm ".Limport_switcher" ctp;
      (* 5: ct1 -> {stats.stats_read}_(ot_switcher) *)
      #".Lmain_fetch_read_1" ::
      fetch_asm ".Limport_stats_read" ct1;
      (* 6: stats_read(&x + 1) *)
      [ #".Lmain_call_read_1";
        jalr cra ctp ];
      (* 7: return on trusted-stack exhaustion; prepare the assert *)
      [ #".Lmain_ret_read_1";
        jne 2 ca0 ENOTENOUGHTRUSTEDSTACK;
        jmp ".Lmain_return";
        mov ct0 ca0;
        mov ct1 X_INIT ];
      (* 8: assert (ret == X_INIT), that is ( ct0 = ct1 ) *)
      #".Lmain_assert_1" ::
      assert_asm ".Limport_assert" ct2 ca2;
      (* 9: the untagged capability of x *)
      [ #".Lmain_arg_2";
        cleartag ca0 cgp ];
      (* 10: ctp -> switcher entry point *)
      #".Lmain_fetch_switcher_2" ::
      fetch_asm ".Limport_switcher" ctp;
      (* 11: ct1 -> {stats.stats_read}_(ot_switcher) *)
      #".Lmain_fetch_read_2" ::
      fetch_asm ".Limport_stats_read" ct1;
      (* 12: stats_read(untagged &x) *)
      [ #".Lmain_call_read_2";
        jalr cra ctp ];
      (* 13: return on trusted-stack exhaustion; prepare the assert *)
      [ #".Lmain_ret_read_2";
        jne 2 ca0 ENOTENOUGHTRUSTEDSTACK;
        jmp ".Lmain_return";
        mov ct0 ca0;
        mov ct1 ECOMPARTMENTFAIL ];
      (* 14: assert (ret == ECOMPARTMENTFAIL), that is ( ct0 = ct1 ) *)
      #".Lmain_assert_2" ::
      assert_asm ".Limport_assert" ct2 ca2;
      (* 15: the capability of x *)
      [ #".Lmain_arg_3";
        mov ca0 cgp ];
      (* 16: ctp -> switcher entry point *)
      #".Lmain_fetch_switcher_3" ::
      fetch_asm ".Limport_switcher" ctp;
      (* 17: ct1 -> {stats.stats_read}_(ot_switcher) *)
      #".Lmain_fetch_read_3" ::
      fetch_asm ".Limport_stats_read" ct1;
      (* 18: stats_read(&x) *)
      [ #".Lmain_call_read_3";
        jalr cra ctp ];
      (* 19: return on trusted-stack exhaustion; prepare the assert *)
      [ #".Lmain_ret_read_3";
        jne 2 ca0 ENOTENOUGHTRUSTEDSTACK;
        jmp ".Lmain_return";
        mov ct0 ca0;
        mov ct1 X_INIT ];
      (* 20: assert (ret == X_INIT), that is ( ct0 = ct1 ) *)
      #".Lmain_assert_3" ::
      assert_asm ".Limport_assert" ct2 ca2;
      (* 21: return, the thread exits *)
      [ #".Lmain_return";
        mov cra cs0;
        ret ]
    ].

  Definition error_handling_main_assembled :=
    Eval compute in assemble_block error_handling_main_asm.
  Lemma error_handling_main_assembles :
    asm_ok (assemble_block_check error_handling_main_asm).
  Proof. asm_check. Qed.
  Definition error_handling_main_instrs_n (n : nat) : list Word :=
    encodeInstrsW (default [] (error_handling_main_assembled !! n)).

  (** Blocks 0-2: the call to [adv]. *)
  Definition error_handling_main_adv_phase_code : list Word :=
    error_handling_main_instrs_n 0 ++
    error_handling_main_instrs_n 1 ++
    error_handling_main_instrs_n 2.

  (** Blocks 3-8: the call to [stats_read] with the capability of [x] one
      past its end, which the handler repairs, and its assert. *)
  Definition error_handling_main_read_1_phase_code : list Word :=
    error_handling_main_instrs_n 3 ++
    error_handling_main_instrs_n 4 ++
    error_handling_main_instrs_n 5 ++
    error_handling_main_instrs_n 6 ++
    error_handling_main_instrs_n 7 ++
    error_handling_main_instrs_n 8.

  (** Blocks 9-14: the call to [stats_read] with the untagged capability
      of [x], which the handler unwinds, and its assert. *)
  Definition error_handling_main_read_2_phase_code : list Word :=
    error_handling_main_instrs_n 9 ++
    error_handling_main_instrs_n 10 ++
    error_handling_main_instrs_n 11 ++
    error_handling_main_instrs_n 12 ++
    error_handling_main_instrs_n 13 ++
    error_handling_main_instrs_n 14.

  (** Blocks 15-21: the call to [stats_read] with the capability of [x],
      its assert, and the return. *)
  Definition error_handling_main_read_3_phase_code : list Word :=
    error_handling_main_instrs_n 15 ++
    error_handling_main_instrs_n 16 ++
    error_handling_main_instrs_n 17 ++
    error_handling_main_instrs_n 18 ++
    error_handling_main_instrs_n 19 ++
    error_handling_main_instrs_n 20 ++
    error_handling_main_instrs_n 21.

  Definition error_handling_main_code : list Word :=
    error_handling_main_adv_phase_code ++
    error_handling_main_read_1_phase_code ++
    error_handling_main_read_2_phase_code ++
    error_handling_main_read_3_phase_code.

  (** The global [x]. *)
  Definition error_handling_main_data : list Word := [WInt X_INIT].

  #[local] Close Scope Z_scope.
  #[local] Coercion Z.of_nat : nat >-> Z.

  Definition error_handling_main_imports `{!switcherLayout} `{!assertLayout} `{!statsLayout}
    (adv_f : Sealable) : list Word :=
    [
      switcher_entry_call;
      assert_entry;
      WSealed ot_switcher adv_f;
      WSealed ot_switcher (STATS_read Global)
    ].

  Definition length_error_handling_main_imports `{!switcherLayout} `{!assertLayout}
    `{!statsLayout} :=
    length (error_handling_main_imports (SCap true RO Global za za za)).

  Definition error_handling_main_entry_nargs : nat := 0.
  (** The stack holds the spill of the switcher calls. *)
  Definition error_handling_main_entry_min_stack : nat := 22.
  (** The offset of the entry [.Lmain] from the start of the PCC. *)
  Definition error_handling_main_entry_pcc_off : nat :=
    Eval vm_compute in label_offset (concat error_handling_main_asm) ".Lmain".
  Lemma error_handling_main_entry_pcc_off_eq `{!switcherLayout} `{!assertLayout}
    `{!statsLayout} :
    error_handling_main_entry_pcc_off = length_error_handling_main_imports.
  Proof. reflexivity. Qed.
End Main.

(** The index of the export [adv] of the adversary, in the order of the
    firmware. *)
Definition error_handling_adv_entry : nat := 0.
