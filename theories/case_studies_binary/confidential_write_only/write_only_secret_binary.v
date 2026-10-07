From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte Require Import fetch switcher.

(** * Sharing a write-only capability to a secret

    The private data of the trusted compartment [main] consists of a single
    cell, which holds a secret. [main] restricts its capability [cgp] to
    this cell to the permission [WO], and calls the untrusted entry point
    [B.f] with the write-only capability as argument. [B] can overwrite the
    cell, but never read it. After the call returns, [main] halts.

    Both runs execute the same code; they only differ in the secret. *)

Section Write_only_secret_main.
  Context `{MP: MachineParameters}.

  (* Expect:
     pc := (RX, Global, b_main, e_main, b_main_code )
     cgp := (RW, Global, b_data, b_data + 1, b_data )

     b_main + 0 : WSentry XSRW_ b_switcher e_switcher a_cc_switcher
     b_main + 1 : WSealed ot_switcher B.f

     b_data + 0 : secret
   *)
  Definition write_only_secret_main_code : list Word :=
    let wo := encodePermPair (WO, Global) in
    encodeInstrsW [
      Mov ca0 cgp;     (* ca0 := (RW, Global, b_data, b_data + 1, b_data) *)
      Restrict ca0 wo  (* ca0 := (WO, Global, b_data, b_data + 1, b_data) *)
    ]
    ++ fetch_instrs 0 ctp ct0 ct1 (* ctp -> switcher entry point *)
    ++ fetch_instrs 1 ct1 ct0 cs0 (* ct1 -> {B.f}_(ot_switcher) *)
    ++
    encodeInstrsW [
      (* call B.f(ca0) *)
      Jalr cra ctp;
      Halt
    ].

  Definition write_only_secret_main_data (secret : Z) : list Word := [WInt secret].

  Definition write_only_secret_main_imports `{!switcherLayout} (B_f : Sealable) : list Word :=
    [
      WSentry XSRW_ Local b_switcher e_switcher a_switcher_call;
      WSealed ot_switcher B_f
    ].

  Definition write_only_secret_B_f_args : nat := 1.

End Write_only_secret_main.
