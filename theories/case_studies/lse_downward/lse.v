From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules proofmode.
From cap_machine Require Import fetch assert switcher.

Section LSE_Main.
  Context `{MP: MachineParameters}.

  (** CHERIoT code for the LSE downward example

      ```
int a = 2;

void __cheri_compartment("known") f(void)
{
  int *y;             // allocate an address on top of the stack frame
  *y = &a;            // push the (global) capability pointing to `a` on top of the stack frame
  assert ( a == 2 );  // check the integrity of `a`
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

  (** The LSE downward example relies on protection against dangling pointers.
      In short, a global capability points-to the CGP address `a` and contains 2.
      The function `f` ( a closure ) pushes the capability on top of the stack,
      and checks integrity of `a` (ie., it contains 2).

      The correctness of the example relies on the fact that,
      when `f` returns, its stack frame is popped
      (in CHERIoT, understand cleared by the switcher)
      and the content is not accessible by the caller anymore.
   *)

  (*
    PSEUDO-CODE:

    run:
      set a := 2
      call B.adv
      halt

    f:
      push (RW, Global, a, a+1, a)
      assert (a == 2)
      return
   *)

  Definition LSE_main_code_run : list Word :=
    (* set a := 2 *)
    encodeInstrsW [
        Store cgp 2
      ]
    (* call B.adv LSE.awkward *)
    ++ fetch_instrs 0 ct0 cs0 cs1 (* ct0 -> switcher entry point *)
    ++ fetch_instrs 2 ct1 cs0 cs1 (* ct1 -> {B.adv}_(ot_switcher)  *)
    ++
    encodeInstrsW [
      Jalr cra ct0; (* jmp to entry point *)
      Halt
    ].

  Definition LSE_main_code_f : list Word :=
    (* push a := (RW, Global, a, a+1, a) *)
    encodeInstrsW [
        GetB cs0 cgp;
        machine_base.Add cs1 cs0 1;
        Subseg cgp cs0 cs1; (* cgp := (RW, Global, a, a+1, a) *)
        (* csp = (RWL, Local, bstk, estk, bstk)  *)
        Store csp cgp; (* bstk -> (RW, Global, a, a+1, a) *)
        (* -- assert (a == 2) -- *)
        Load ct0 cgp;
        Mov ct1 2
      ]
      ++ assert_instrs 1 cgp cs0 cs1 (* asserts that ( *ct0 = *ct1 ) *)
      ++ encodeInstrsW [
        (* return 0 *)
        Mov ca0 0%Z;
        Mov ca1 0%Z;
        JmpCap cra
      ].

  Definition lse_main_code : list Word
    := LSE_main_code_run ++ LSE_main_code_f.

  Definition lse_main_data : list Word := [WInt 2].

  Definition lse_main_imports
    (b_switcher e_switcher a_cc_switcher : Addr) (ot_switcher : OType)
    (b_assert e_assert : Addr)
    (B_adv : Sealable)
    : list Word :=
    [
      WSentry XSRW_ Local b_switcher e_switcher a_cc_switcher;
      WSentry RX Global b_assert e_assert b_assert;
      WSealed ot_switcher B_adv
    ].

  Definition length_lse_main_imports :=
    length
      (lse_main_imports za za za za_ot za za (SCap RO Global za za za)).

  Definition lse_exp_tbl_entry_f :=
    WInt (encode_entry_point 0
            (length_lse_main_imports + (length LSE_main_code_run))).

  Definition lse_entry_f_sb
    b_lse_exp_tbl e_lse_exp_tbl : Sealable :=
      SCap RO Global b_lse_exp_tbl e_lse_exp_tbl (b_lse_exp_tbl ^+2)%a.

  Definition lse_export_table_entries : list Word :=
    [ lse_exp_tbl_entry_f ].

End LSE_Main.
