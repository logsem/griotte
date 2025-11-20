From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules proofmode.
From cap_machine Require Import fetch assert.

Section VAE_Main.
  Context `{MP: MachineParameters}.


  (*
    PSEUDO-CODE:

    init:
      set a := 0
      call B.adv VAE.akward
      halt

    awkward:
      set a := 0
      if (getotype arg_1 != ot_switcher) then halt else
      call g ()
      set a := 1
      call g ()
      assert (a == 1)
      return cra

   *)

  Definition VAE_main_code_init : list Word :=
    (* set a := 0 *)
    encodeInstrsW [Store cgp 0]
    (* call B.adv VAE.awkward *)
    ++ fetch_instrs 3 ca0 cs0 cs1 (* ca0 -> VAE_awkward entry point *)
    ++ fetch_instrs 0 ct0 cs0 cs1 (* ct0 -> switcher entry point *)
    ++ fetch_instrs 2 ct1 cs0 cs1 (* ct1 -> {B.f}_(ot_switcher)  *)
    ++
    encodeInstrsW [
      Jalr cra ct0; (* jmp to entry point *)
      Halt
    ].

  Definition VAE_main_code_f (ot_switcher : OType) : list Word :=
    (* set a := 0 *)
    encodeInstrsW [Store cgp 0]
    (* call g () *)
    ++ fetch_instrs 0 ct0 cs0 cs1 (* ct0 -> switcher entry point *)
    ++
    encodeInstrsW [
      Mov cs0 cra; (* stores return-to-switcher *)
      Mov cs1 ca0; (* stores arg_1 *)
      Jalr cs1 ct0 (* jmp to arg_1 *)
    ]
    (* set a := 1 *)
    ++ encodeInstrsW [Store cgp 1]
    (* call g () *)
    ++ fetch_instrs 0 ct0 cs0 cs1 (* ct0 -> switcher entry point *)
    ++
    encodeInstrsW [
      Mov cs0 cra; (* stores return-to-switcher *)
      Mov cs1 ca0; (* stores arg_1 *)
      Jalr cs1 ct0; (* jmp to arg_1 *)

      (* assert (a == 1) *)
      Load ct0 cgp; (* ct0 -> a *)
      Mov ct1 1%Z  (* ct1 -> 1 *)
    ]
    ++ assert_instrs 1 ct2 ct3 ct4 (* asserts that ( *ct0 = *ct1 ) *)
    (* return cra *)
    ++
    encodeInstrsW [
      Mov cra cs0; (* restores the return-to-switcher *)

      (* return a *)
      Mov ca0 0%Z;
      Mov ca1 0%Z;
      Mov cs0 0%Z;
      Mov cs1 0%Z;
      JmpCap cra
    ].

  Definition vae_main_code (ot_switcher : OType) : list Word
    := VAE_main_code_init ++ (VAE_main_code_f ot_switcher).

  Definition vae_main_data : list Word := [WInt 0].

  Definition vae_main_imports
    (b_switcher e_switcher a_cc_switcher : Addr) (ot_switcher : OType)
    (b_assert e_assert : Addr)
    (B_adv : Sealable)
    (b_vae_exp_tbl e_vae_exp_tbl a_vae_exp_tbl_awkward : Addr)
    : list Word :=
    [
      WSentry XSRW_ Local b_switcher e_switcher a_cc_switcher;
      WSentry RX Global b_assert e_assert b_assert;
      WSealed ot_switcher B_adv;
      WSealed ot_switcher (SCap RO Global b_vae_exp_tbl e_vae_exp_tbl a_vae_exp_tbl_awkward)
    ].

  Definition vae_export_table_entries : list Word :=
    [WInt (switcher.encode_entry_point 1 (length VAE_main_code_init))].

End VAE_Main.
