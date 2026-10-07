From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte Require Import fetch switcher.

(** * Stack confidentiality: a secret below and above the stack pointer

    The trusted compartment [main] loads a secret from its private data, and
    writes it twice into its stack:
    - at [a_stk], the first word of its stack frame; the stack pointer is
      then moved one word up, so that this copy is kept in [main]'s frame,
      below the stack pointer at the call;
    - at [a_stk + 5], above the stack pointer at the call; the switcher
      spills four words at [a_stk + 1 .. a_stk + 4], so this stale copy is
      the first word of the stack frame given to the callee.
    Then [main] calls the untrusted entry point [B.f] through the switcher.
    The first copy is protected by the switcher restricting the callee's
    stack capability to the part above the stack pointer; the second copy
    is protected by the switcher clearing the callee's stack frame before
    jumping to the callee. After the call returns, [main] halts.

    Both runs execute the same code; they only differ in the secret. *)

Section Stack_secret_main.
  Context `{MP: MachineParameters}.

  (* Expect:
     pc := (RX, Global, b_main, e_main, b_main_code )
     cgp := (RW, Global, b_data, e_data, b_data )
     csp := (RWL, Local, b_stk, e_stk, b_stk )

     b_main + 0 : WSentry XSRW_ b_switcher e_switcher a_cc_switcher
     b_main + 1 : WSealed ot_switcher B.f

     b_data + 0 : secret
   *)
  Definition stack_secret_main_code : list Word :=
    encodeInstrsW [
      (* keep the secret in main's stack frame, at a_stk *)
      Load ct0 cgp;
      Store csp ct0;
      Lea csp 1%Z;
      (* leave a stale copy at a_stk + 5, above the 4 words spilled by the switcher *)
      Lea csp 4%Z;
      Store csp ct0;
      (* the stack pointer at the call is a_stk + 1 *)
      Lea csp (-4)%Z
    ]
    ++ fetch_instrs 0 ctp ct0 ct1 (* ctp -> switcher entry point *)
    ++ fetch_instrs 1 ct1 ct0 cs0 (* ct1 -> {B.f}_(ot_switcher) *)
    ++
    encodeInstrsW [
      (* call B.f *)
      Jalr cra ctp;
      Halt
    ].

  Definition stack_secret_main_data (secret : Z) : list Word := [WInt secret].

  Definition stack_secret_main_imports `{!switcherLayout} (B_f : Sealable) : list Word :=
    [
      WSentry XSRW_ Local b_switcher e_switcher a_switcher_call;
      WSealed ot_switcher B_f
    ].

  Definition stack_secret_B_f_args : nat := 0.

End Stack_secret_main.
