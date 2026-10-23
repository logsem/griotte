From griotte Require Import machine_parameters assembler fetch assert switcher.

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
	frame->registers[9] = reinterpret_cast<void *>(-EINVAL); // the load's result (a0)
	frame->pcc = static_cast<char *>(frame->pcc) + 4;        // skip the load
	return ErrorRecoveryBehaviour::InstallContext;
}

// main.cc: compartment "main" (trusted, thread start)
int __cheri_compartment("adv") adv(); // untrusted, imports stats_read

static int x = 5;

void __cheri_compartment("main") run()
{
	adv();
	assert(stats_read(static_cast<int *>(__builtin_cheri_tag_clear(&x))) == -EINVAL);
	assert(stats_read(&x) == 5); // the lock was released
}
    ```

    The handler skips the faulting load and sets its result to [-EINVAL];
    [stats_read] then releases the lock and returns [-EINVAL]. Without the
    handler, a bad pointer would leave the lock held, and every later call
    would return [-EBUSY]. *)

(** ** [stats] *)
Section Stats.
  Import Asm_Griotte.
  #[local] Open Scope Z_scope.
  Context `{MP: MachineParameters}.

  (** CHERIoT's errno values, stored negated, as they are returned (like
      [ECOMPARTMENTFAIL] in [switcher]). *)
  Definition EINVAL : Z := -22.
  Definition EBUSY : Z := -16.

  (** [stats_read(ptr)]: [ptr] in [ca0]; the lock is the first global, at
      [cgp]. Returns the value in [ca0], and 0 in [ca1]; the return path of
      the switcher clears the other registers. The load at [.Lread_load] is
      the fault site: the handler resumes at [.Lread_release]. *)
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
      is the PC, words 1 to 15 the registers x1 to x15). It sets the saved
      [a0] to [EINVAL], moves the saved PC past the faulting instruction
      (the saved PC is an untagged capability: [lea], not [add], which reads
      integers), and returns 0 (InstallContext). *)
  Definition stats_handler_asm : list asm_code :=
    [ #".Lstats_handler";
      store_imm ca0 EINVAL TrustedStack_offset_ca0;
      load ct0 ca0;
      lea ct0 ct0 1;
      store ca0 ct0;
      mov ca0 0;
      ret ].

  Definition stats_asm : list (list asm_code) :=
    stats_read_asm ++ [stats_handler_asm].

  Definition stats_assembled :=
    Eval compute in assemble_block stats_asm.
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

  Definition stats_handler_code : list Word := stats_instrs_n 5.

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
  (** The export of [stats_read], before its sealing by the switcher, for
      the export table of [stats] at [[b_exp_tbl, e_exp_tbl)]. *)
  Definition stats_read_export (b_exp_tbl e_exp_tbl : Addr) (g : Locality) : Sealable :=
    SCap true RO g b_exp_tbl e_exp_tbl (b_exp_tbl ^+ stats_read_exp_tbl_off)%a.
End Stats.

(** ** [main] *)
Section Main.
  Import Asm_Griotte.
  #[local] Open Scope Z_scope.
  Context `{MP: MachineParameters}.

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
        jalr cra ctp ];
      (* 3: the untagged capability of x *)
      [ #".Lmain_ret_adv";
        cleartag ca0 cgp ];
      (* 4: ctp -> switcher entry point *)
      #".Lmain_fetch_switcher_1" ::
      fetch_asm ".Limport_switcher" ctp;
      (* 5: ct1 -> {stats.stats_read}_(ot_switcher) *)
      #".Lmain_fetch_read_1" ::
      fetch_asm ".Limport_stats_read" ct1;
      (* 6: stats_read(untagged &x) *)
      [ #".Lmain_call_read_1";
        jalr cra ctp ];
      (* 7: halt on trusted-stack exhaustion; prepare the assert *)
      [ #".Lmain_ret_read_1";
        jne 2 ca0 ENOTENOUGHTRUSTEDSTACK;
        halt;
        mov ct0 ca0;
        mov ct1 EINVAL ];
      (* 8: assert (ret == EINVAL), that is ( ct0 = ct1 ) *)
      #".Lmain_assert_1" ::
      assert_asm ".Limport_assert" ct2 ca2;
      (* 9: the capability of x *)
      [ #".Lmain_arg_2";
        mov ca0 cgp ];
      (* 10: ctp -> switcher entry point *)
      #".Lmain_fetch_switcher_2" ::
      fetch_asm ".Limport_switcher" ctp;
      (* 11: ct1 -> {stats.stats_read}_(ot_switcher) *)
      #".Lmain_fetch_read_2" ::
      fetch_asm ".Limport_stats_read" ct1;
      (* 12: stats_read(&x) *)
      [ #".Lmain_call_read_2";
        jalr cra ctp ];
      (* 13: halt on trusted-stack exhaustion; prepare the assert *)
      [ #".Lmain_ret_read_2";
        jne 2 ca0 ENOTENOUGHTRUSTEDSTACK;
        halt;
        mov ct0 ca0;
        mov ct1 5 ];
      (* 14: assert (ret == 5), that is ( ct0 = ct1 ) *)
      #".Lmain_assert_2" ::
      assert_asm ".Limport_assert" ct2 ca2;
      (* 15 *)
      [ #".Lmain_halt";
        halt ]
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

  (** Blocks 3-8: the call to [stats_read] with an untagged capability, and
      its assert. *)
  Definition error_handling_main_read_1_phase_code : list Word :=
    error_handling_main_instrs_n 3 ++
    error_handling_main_instrs_n 4 ++
    error_handling_main_instrs_n 5 ++
    error_handling_main_instrs_n 6 ++
    error_handling_main_instrs_n 7 ++
    error_handling_main_instrs_n 8.

  (** Blocks 9-15: the call to [stats_read] with the capability of [x], its
      assert, and the halt. *)
  Definition error_handling_main_read_2_phase_code : list Word :=
    error_handling_main_instrs_n 9 ++
    error_handling_main_instrs_n 10 ++
    error_handling_main_instrs_n 11 ++
    error_handling_main_instrs_n 12 ++
    error_handling_main_instrs_n 13 ++
    error_handling_main_instrs_n 14 ++
    error_handling_main_instrs_n 15.

  Definition error_handling_main_code : list Word :=
    error_handling_main_adv_phase_code ++
    error_handling_main_read_1_phase_code ++
    error_handling_main_read_2_phase_code.

  (** The global [x]. *)
  Definition error_handling_main_data : list Word := [WInt 5].

  #[local] Close Scope Z_scope.
  #[local] Coercion Z.of_nat : nat >-> Z.

  Definition error_handling_main_imports `{!switcherLayout} `{!assertLayout}
    (adv_f stats_read : Sealable) : list Word :=
    [
      WSentry FwdDisable true XSRW_ Local b_switcher e_switcher a_switcher_call;
      WSentry Inherit true RX Global b_assert e_assert b_assert;
      WSealed ot_switcher adv_f;
      WSealed ot_switcher stats_read
    ].

  Definition length_error_handling_main_imports `{!switcherLayout} `{!assertLayout} :=
    length
      (error_handling_main_imports (SCap true RO Global za za za)
         (SCap true RO Global za za za)).

  Definition error_handling_main_entry_nargs : nat := 0.
  (** The stack holds the spill of the switcher calls. *)
  Definition error_handling_main_entry_min_stack : nat := 4.
  (** The offset of the entry [.Lmain] from the start of the PCC. *)
  Definition error_handling_main_entry_pcc_off : nat :=
    Eval vm_compute in label_offset (concat error_handling_main_asm) ".Lmain".
  Lemma error_handling_main_entry_pcc_off_eq `{!switcherLayout} `{!assertLayout} :
    error_handling_main_entry_pcc_off = length_error_handling_main_imports.
  Proof. reflexivity. Qed.
End Main.

(** The index of the export [entry] of [main] and of the export [adv] of the
    adversary, in the order of the firmware. *)
Definition error_handling_main_entry : nat := 0.
Definition error_handling_adv_entry : nat := 0.
