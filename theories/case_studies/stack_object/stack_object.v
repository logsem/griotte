From cap_machine Require Import rules proofmode.
From cap_machine Require Import check_valid_stack_object fetch assert switcher.

Section SO_Main.
  Context `{MP: MachineParameters}.

  (** CHERIoT code for the stack objects example

      ```
void __cheri_compartment("known") f(char* in, Callback* g)
{
  // `*in` is a stack object from the caller
  int *y = 2;          // `*y` is hidden part of the stack
  char *z = [...];    // `*z` is public stack object
  g(z, in);           // call the adversary function `g`,
                      //   sharing both the stack object newly allocated
                      //   and the stack object formerly allocated
  assert ( y == 2 );  // check the integrity of `y`
	return;
}

int __cheri_compartment("known") run()
{
	// call unknown program
	adv();
	return 0;
}
      ```

   *)

  (** We must check:
      because `in` is a stack object from the caller,
      it might contain stack capabilities pointing to `f`'s stack frame,
      and in particular pointing to `y`.
      We need to check that `in` is fully initialised,
      and in our case, simply that it contains integers.

   *)

  (*
    PSEUDO-CODE:

    run:
      call B.adv
      halt

    f(in):
      // integrity check of `in`
      check_read(in, RWL);
      check_only_integer(in);
      y := push(2);
      o := allocate_stack_object( [0] );
      call(g, in, o) ;
      assert (y == 2) ;
      return
   *)

  Definition SO_main_code_run : list Word :=
    (* call B.adv LSE.awkward *)
    fetch_instrs 0 ct0 cs0 cs1 (* ct0 -> switcher entry point *)
    ++ fetch_instrs 2 ct1 cs0 cs1 (* ct1 -> {B.adv}_(ot_switcher)  *)
    ++
    encodeInstrsW [
      Jalr cra ct0; (* jmp to entry point *)
      Halt
    ].

  Definition so_secret : Z := 42.

  Definition SO_main_code_f : list Word :=
    (* ca0 := warg0 / ca1 := fun_g *)
    encodeInstrsW [
        Mov ct1 ca1 (* ct1 := fun_g *)
      ]
      (* TODO: macro [check_stack_object] instead *)
      (* we also need to explicitly check that it does not point upward *)
      (* ++ checkra_instrs ca0 cs0 cs1 *)
      (* ++ checkints_instrs ca0 cs0 cs1 *)
      ++ check_valid_stack_object_instrs ca0 cs0 cs1
      ++ encodeInstrsW [
        (* push (secret_val) on csp_b *)
        Store csp so_secret;
        Lea csp 1;
        (* allocate stack object *)
        Mov ca1 csp;
        GetA cs0 ca1;
        machine_base.Add cs1 cs0 1%Z;
        Subseg ca1 cs0 cs1;
        Store ca1 0%Z;  (* ca1 := (RWL, Local, csp_b+1, csp_b+2, csp_b+1) // csp_b+1 := 0 *)
        Lea csp 1%Z
      ]
      (* call g () *)
      ++ fetch_instrs 0 ct0 cs0 cs1 (* ct0 -> switcher entry point *)
      ++
      encodeInstrsW [
        Mov cs0 cra; (* cs0 -> return-to-switcher *)
        Mov cs1 ct1; (* cs1 -> fun_g *)
        Jalr cra ct0 (* jmp to g *)
      ]
      ++
      (* assert csp_b *)
      encodeInstrsW [
        Lea csp (-2)%Z;
        Load ct0 csp;      (* ct0 -> y *)
        Mov ct1 so_secret (* ct1 -> 2 *)
      ]
      ++ assert_instrs 1 ct2 ct3 ct4 (* asserts that ( *ct0 = *ct1 ) *)
      (* return cra *)
      ++
      encodeInstrsW [
        Mov cra cs0; (* cra -> return_to-switcher *)

        (* return a *)
        Mov ca0 0%Z;
        Mov ca1 0%Z;
        JmpCap cra
      ].

  Definition so_main_code : list Word
    := SO_main_code_run ++ SO_main_code_f.

  Definition so_main_data : list Word := [].

  Definition so_main_imports
    (b_switcher e_switcher a_cc_switcher : Addr) (ot_switcher : OType)
    (b_assert e_assert : Addr)
    (B_adv : Sealable)
    : list Word :=
    [
      WSentry XSRW_ Local b_switcher e_switcher a_cc_switcher;
      WSentry RX Global b_assert e_assert b_assert;
      WSealed ot_switcher B_adv
    ].

  Definition length_so_main_imports :=
    length
      (so_main_imports za za za za_ot za za (SCap RO Global za za za)).

  Definition so_exp_tbl_entry_f :=
    WInt (encode_entry_point 2
            (length_so_main_imports + (length SO_main_code_run))).

  Definition so_entry_f_sb
    b_so_exp_tbl e_so_exp_tbl : Sealable :=
      SCap RO Global b_so_exp_tbl e_so_exp_tbl (b_so_exp_tbl ^+2)%a.

  Definition so_export_table_entries : list Word :=
    [ so_exp_tbl_entry_f ].

End SO_Main.
