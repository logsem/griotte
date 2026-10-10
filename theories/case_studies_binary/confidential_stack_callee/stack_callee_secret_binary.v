From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte Require Import fetch switcher.

(** * Stack confidentiality: a trusted callee leaves a secret in its stack frame

    The trusted compartment [T] exports the entry point [T.f]. When it is
    called (through the switcher), [T.f] loads a secret from the private
    data of [T], writes it at the base of the stack frame given to it by the
    switcher, and returns to its caller through the switcher. The switcher
    clears the stack frame of [T.f] before giving control back to the
    caller, so the caller cannot observe the secret.

    The program starts in [T.run], which calls the untrusted entry point
    [B.adv] through the switcher, and halts when [B.adv] returns. The
    adversary [B] imports [T.f], and may call it any number of times.

    Both runs execute the same code; they only differ in the secret. *)

Section Stack_callee_secret.
  Context `{MP: MachineParameters}.

  (* Expect, in T.run:
     pc := (RX, Global, b_T, e_T, b_T_code )
     cgp := (RW, Global, b_data, e_data, b_data )
     csp := (RWL, Local, b_stk, e_stk, b_stk )

     b_T + 0 : WSentry XSRW_ b_switcher e_switcher a_cc_switcher
     b_T + 1 : WSealed ot_switcher B.adv

     b_data + 0 : secret
   *)
  Definition stack_callee_secret_code_run : list Word :=
    fetch_instrs 0 ctp ct0 ct1 (* ctp -> switcher entry point *)
    ++ fetch_instrs 1 ct1 ct0 cs0 (* ct1 -> {B.adv}_(ot_switcher) *)
    ++
    encodeInstrsW [
      (* call B.adv *)
      Jalr cra ctp;
      Halt
    ].

  (* Expect, in T.f:
     pc := (RX, Global, b_T, e_T, b_T_f )
     cgp := (RW, Global, b_data, e_data, b_data )
     csp := (RWL, Local, b_frame, e_stk, b_frame )
     cra := return-to-switcher entry point
   *)
  Definition stack_callee_secret_code_f : list Word :=
    encodeInstrsW [
      (* write the secret at the base of the stack frame of T.f *)
      Load ct0 cgp;
      Store csp ct0;
      (* return 0 *)
      Mov ca0 0%Z;
      Mov ca1 0%Z;
      Jalr cnull cra
    ].

  Definition stack_callee_secret_code : list Word :=
    stack_callee_secret_code_run ++ stack_callee_secret_code_f.

  Definition stack_callee_secret_data (secret : Z) : list Word := [WInt secret].

  Definition stack_callee_secret_imports `{!switcherLayout} (B_adv : Sealable) : list Word :=
    [
      WSentry XSRW_ Local b_switcher e_switcher a_switcher_call;
      WSealed ot_switcher B_adv
    ].

  Definition stack_callee_secret_B_adv_args : nat := 0.
  Definition stack_callee_secret_f_args : nat := 0.

  (** Offset of [T.f] from the beginning of the code region of [T]. *)
  Definition stack_callee_secret_f_offset `{!switcherLayout} : nat :=
    length (stack_callee_secret_imports (SCap RO Global za za za))
    + length stack_callee_secret_code_run.

  (** The entry of [T.f] in the export table of [T]. *)
  Definition stack_callee_secret_exp_tbl_entry_f `{!switcherLayout} : Word :=
    WInt (encode_entry_point
            (Z.of_nat stack_callee_secret_f_args)
            (Z.of_nat stack_callee_secret_f_offset)).

  Definition stack_callee_secret_export_table_entries `{!switcherLayout} : list Word :=
    [ stack_callee_secret_exp_tbl_entry_f ].

End Stack_callee_secret.
