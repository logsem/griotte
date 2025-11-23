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
      call B.adv
      halt

    awkward:
      set a := 0
      call g ()
      set a := 1
      call g ()
      assert (a == 1)
      return
   *)

  Definition VAE_main_code_init : list Word :=
    (* set a := 0 *)
    encodeInstrsW [Store cgp 0]
    (* call B.adv VAE.awkward *)
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
      Mov ct1 ca0; (* place the arg_1 in ct1 *)
      Mov ca0 0;
      Mov ca1 0;
      Mov ca2 0;
      Mov ca3 0;
      Mov ca4 0;
      Mov ca5 0;
      Jalr cra ct0 (* jmp to arg_1 *)
    ]
    (* set a := 1 *)
    ++ encodeInstrsW [Store cgp 1; Mov cra cs0; Mov ca0 cs1]
    (* call g () *)
    ++ fetch_instrs 0 ct0 cs0 cs1 (* ct0 -> switcher entry point *)
    ++
    encodeInstrsW [
      Mov cs0 cra; (* stores return-to-switcher *)
      Mov ct1 ca0; (* stores arg_1 *)
      Mov ca0 0;
      Mov ca1 0;
      Jalr cra ct0; (* jmp to arg_1 *)

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
    : list Word :=
    [
      WSentry XSRW_ Local b_switcher e_switcher a_cc_switcher;
      WSentry RX Global b_assert e_assert b_assert;
      WSealed ot_switcher B_adv
    ].

  Definition length_vae_main_imports :=
    length
      (vae_main_imports za za za za_ot za za (SCap RO Global za za za)).

  Definition vae_exp_tbl_entry_awkward :=
    WInt (switcher.encode_entry_point 0
            (length_vae_main_imports + (length VAE_main_code_init))).

  Definition vae_entry_awkward_sb
    b_vae_exp_tbl e_vae_exp_tbl : Sealable :=
      SCap RO Global b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+2)%a.

  Definition vae_export_table_entries : list Word :=
    [ vae_exp_tbl_entry_awkward ].

End VAE_Main.
