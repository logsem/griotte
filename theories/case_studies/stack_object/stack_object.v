From griotte Require Import rules proofmode.
From griotte Require Import fetch assert switcher.
From griotte Require Import checkra checkints check_no_overlap.

Section SO_Main.
  Context `{MP: MachineParameters}.

  (** CHERIoT code for the stack objects example

<<
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
>>

   *)

  (** We must check:
      because `in` is a stack object from the caller,
      it might contain stack capabilities pointing to `f`'s stack frame,
      and in particular pointing to `y`.
      We need to check that `in` is fully initialised,
      and in our case, simply that it contains integers.

   *)

  (** PSEUDO-CODE:

<<
    run:
      call B.adv
      halt

    f(in):
      // integrity check of `in`
      check_read(in);
      check_only_integer(in);
      y := push(2);
      o := allocate_stack_object( [0] );
      call(g, in, o) ;
      assert (y == 2) ;
      return
>>
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

  Definition so_f_alloc_instrs : list Word :=
    encodeInstrsW [
      (* push (secret_val) on csp_b *)
      Store csp so_secret;
      Lea csp 1;
      (* allocate stack object *)
      Mov ca1 csp;
      GetA cs0 ca1;
      machine_instructions.Add cs1 cs0 1%Z;
      Subseg ca1 cs0 cs1;
      Store ca1 0%Z;
      Lea csp 1%Z
    ].

  Definition so_f_call_instrs : list Word :=
    encodeInstrsW [
      Mov cs0 cra;
      Mov cs1 ct1;
      Jalr cra ct0
    ].

  Definition so_f_assert_prep_instrs : list Word :=
    encodeInstrsW [
      Lea csp (-2)%Z;
      Load ct0 csp;
      Mov ct1 so_secret
    ].

  Definition so_f_return_instrs : list Word :=
    encodeInstrsW [
      (* return a *)
      Mov cra cs0;
      Mov ca0 0%Z;
      Mov ca1 0%Z;
      Jalr cnull cra
    ].

  Definition SO_main_code_f : list Word :=
    (* ca0 := warg0 / ca1 := fun_g *)
    encodeInstrsW [
        Mov ct1 ca1 (* ct1 := fun_g *)
      ]
      ++ checkra_instrs ca0 cs0 cs1
      ++ check_no_overlap_instrs ca0 csp cs0 cs1
      ++ checkints_instrs ca0 cs0 cs1
      ++ so_f_alloc_instrs
      (* call g () *)
      ++ fetch_instrs 0 ct0 cs0 cs1 (* ct0 -> switcher entry point *)
      ++
      so_f_call_instrs
      ++
      (* assert csp_b *)
      so_f_assert_prep_instrs
      ++ assert_instrs 1 ct2 ct3 ct4 (* asserts that ( *ct0 = *ct1 ) *)
      (* return cra *)
      ++
      so_f_return_instrs.

  Definition so_main_code : list Word
    := SO_main_code_run ++ SO_main_code_f.

  Definition so_main_data : list Word := [].

  Definition so_main_imports `{!switcherLayout} `{!assertLayout}
    (B_adv : Sealable)
    : list Word :=
    [
      WSentry XSRW_ Local b_switcher e_switcher a_switcher_call;
      WSentry RX Global b_assert e_assert b_assert;
      WSealed ot_switcher B_adv
    ].

  Definition length_so_main_imports `{!switcherLayout} `{!assertLayout} :=
    length
      (so_main_imports (SCap RO Global za za za)).

  Definition so_exp_tbl_entry_f `{!switcherLayout} `{!assertLayout} :=
    WInt (encode_entry_point 2
            (length_so_main_imports + (length SO_main_code_run))).

  Definition so_entry_f_sb
    b_so_exp_tbl e_so_exp_tbl : Sealable :=
      SCap RO Global b_so_exp_tbl e_so_exp_tbl (b_so_exp_tbl ^+2)%a.

  Definition so_export_table_entries `{!switcherLayout} `{!assertLayout} : list Word :=
    [ so_exp_tbl_entry_f ].

End SO_Main.
