From griotte Require Import machine_parameters assembler fetch assert switcher.

Section LSE_Main.
  Import Asm_Griotte.
  Local Open Scope Z_scope.
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

  Definition lse_main_asm : list (list asm_code) :=
    [ (* run *)
      [ (* the imports *)
        #@".Limport_switcher";
        #@".Limport_assert";
        #@".Limport_B_adv";

        (* set a := 2 *)
        #".Llse_run";
        store cgp 2
      ];
      (* call B.adv LSE.awkward *)
      #".Llse_run_fetch_switcher" ::
      fetch_asm ".Limport_switcher" ct0; (* ct0 -> switcher entry point *)
      #".Llse_run_fetch_adv" ::
      fetch_asm ".Limport_B_adv" ct1; (* ct1 -> {B.adv}_(ot_switcher)  *)
      [ #".Llse_run_call";
        jalr cra ct0; (* jmp to entry point *)
        #".Llse_run_halt";
        halt
      ];
      (* f *)
      (* push a := (RW, Global, a, a+1, a) *)
      [ #".Llse_f";
        getb cs0 cgp;
        add cs1 cs0 1;
        subseg cgp cs0 cs1; (* cgp := (RW, Global, a, a+1, a) *)
        (* csp = (RWL, Local, bstk, estk, bstk)  *)
        store csp cgp; (* bstk -> (RW, Global, a, a+1, a) *)
        (* -- assert (a == 2) -- *)
        load ct0 cgp;
        mov ct1 2
      ];
      #".Llse_f_assert" ::
      assert_asm ".Limport_assert" cgp cs0; (* asserts that ( *ct0 = *ct1 ) *)
      [ (* return 0 *)
        #".Llse_f_return";
        mov ca0 0;
        mov ca1 0;
        ret
      ]
    ].

  Definition lse_main_assembled :=
    Eval compute in assemble_block lse_main_asm.
  Lemma lse_main_assembles : asm_ok (assemble_block_check lse_main_asm).
  Proof. asm_check. Qed.
  Definition lse_main_instrs_n (n : nat) : list Word :=
    encodeInstrsW (default [] (lse_main_assembled !! n)).

  Definition LSE_main_code_run : list Word :=
    lse_main_instrs_n 0 ++
    lse_main_instrs_n 1 ++
    lse_main_instrs_n 2 ++
    lse_main_instrs_n 3.

  Definition LSE_main_code_f : list Word :=
    lse_main_instrs_n 4 ++
    lse_main_instrs_n 5 ++
    lse_main_instrs_n 6.

  Local Close Scope Z_scope.
  Local Coercion Z.of_nat : nat >-> Z.

  Definition lse_main_code : list Word
    := LSE_main_code_run ++ LSE_main_code_f.

  Definition lse_main_data : list Word := [WInt 2].

  Definition lse_main_imports `{!switcherLayout} `{!assertLayout}
    (B_adv : Sealable)
    : list Word :=
    [
      WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call;
      WSentry true RX Global b_assert e_assert b_assert;
      WSealed ot_switcher B_adv
    ].

  Definition length_lse_main_imports `{!switcherLayout} `{!assertLayout} :=
    length
      (lse_main_imports (SCap true RO Global za za za)).

  Definition lse_exp_tbl_entry_f `{!switcherLayout} `{!assertLayout} :=
    WInt (encode_entry_point 0
            (length_lse_main_imports + (length LSE_main_code_run))).

  Definition lse_entry_f_sb
    b_lse_exp_tbl e_lse_exp_tbl : Sealable :=
      SCap true RO Global b_lse_exp_tbl e_lse_exp_tbl (b_lse_exp_tbl ^+2)%a.

  Definition lse_export_table_entries `{!switcherLayout} `{!assertLayout} : list Word :=
    [ lse_exp_tbl_entry_f ].

End LSE_Main.

(** The code of the concrete adversary of [lse_concrete], assembled here,
    away from the program logic's coercions. *)
Section lse_C_code.
  Context `{MP: MachineParameters}.
  Import Asm_Griotte.
  Local Open Scope Z_scope.

  Definition lse_C_asm : list asm_code :=
    [ #@".Limport_switcher";
      #@".Limport_main_f";
      store csp cra;
      lea csp 1 ] ++
    fetch_asm ".Limport_switcher" ct0 ++
    fetch_asm ".Limport_main_f" ct1 ++
    [ jalr cra ct0 ] ++
    fetch_asm ".Limport_switcher" ct0 ++
    fetch_asm ".Limport_main_f" ct1 ++
    [ jalr cra ct0;
      lea csp (-1);
      load cra csp;
      mov ca0 0;
      mov ca1 0;
      ret ].

  Definition lse_C_instrs : list instr :=
    Eval compute in assemble lse_C_asm.
  Lemma lse_C_assembles : asm_ok (assemble_check lse_C_asm).
  Proof. asm_check. Qed.
End lse_C_code.
