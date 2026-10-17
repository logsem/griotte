From griotte Require Import machine_parameters assembler fetch assert switcher check_no_overlap.
From griotte Require Import checkra checkints.

(** The code of the stack object example, [so_main_code], assembled by
    blocks from [so_main_asm]. *)
Section SO_Asm.
  Import Asm_Griotte.
  #[local] Open Scope Z_scope.
  Context `{MP: MachineParameters}.

  Definition so_secret : Z := 42.

  Definition so_main_asm : list (list asm_code) :=
    [ (* run *)
      (* the imports *)
      [ #@".Limport_switcher";
        #@".Limport_assert";
        #@".Limport_B_adv";
        #".Lso_run" ] ++
      fetch_asm ".Limport_switcher" ct0;
      #".Lso_run_fetch_adv" ::
      fetch_asm ".Limport_B_adv" ct1;
      [ #".Lso_run_call"; jalr cra ct0; #".Lso_run_halt"; halt ];
      (* f *)
      [ #".Lso_f"; mov ct1 ca1 ];
      #".Lso_f_checkra" ::
      checkra_asm ca0 cs0 cs1;
      #".Lso_f_check_no_overlap" ::
      check_no_overlap_asm ca0 csp cs0 cs1;
      #".Lso_f_checkints" ::
      checkints_asm ca0 cs0 cs1;
      [ #".Lso_f_alloc";
        store csp so_secret;
        lea csp 1;
        mov ca1 csp;
        geta cs0 ca1;
        add cs1 cs0 1;
        subseg ca1 cs0 cs1;
        store ca1 0;
        lea csp 1 ];
      #".Lso_f_fetch_switcher" ::
      fetch_asm ".Limport_switcher" ct0;
      [ #".Lso_f_call";
        mov cs0 cra;
        mov cs1 ct1;
        jalr cra ct0 ];
      [ #".Lso_f_after_call";
        lea csp (-2);
        load ct0 csp;
        mov ct1 so_secret ];
      #".Lso_f_assert" ::
      assert_asm ".Limport_assert" ct2 ca2;
      [ #".Lso_f_return";
        mov cra cs0;
        mov ca0 0;
        mov ca1 0;
        ret ]
    ].

  (** The encodings of word types and permissions, and [so_secret], stay
      folded in the assembled code, as in the code of the macros. *)
  Definition so_main_assembled :=
    Eval cbv -[encodeWordType word_encoding_mixin wt_cap wt_int
               encodePerm permission_encoding_mixin so_secret] in
      assemble_block so_main_asm.
  Lemma so_main_assembles : asm_ok (assemble_block_check so_main_asm).
  Proof. asm_check. Qed.
  Definition so_main_instrs_n (n : nat) : list Word :=
    encodeInstrsW (default [] (so_main_assembled !! n)).
End SO_Asm.

(** The code of the concrete adversary of [stack_object_concrete]. *)
Section SO_C_code.
  Import Asm_Griotte.
  #[local] Open Scope Z_scope.

  Definition so_C_asm : list asm_code :=
    [ #@".Limport_switcher";
      #@".Limport_main_f";
      #@".Limport_g";
      #"adv_entry";
      store csp cra;
      lea csp 1;
      mov ca0 csp;
      geta cs0 ca0;
      add cs1 cs0 1;
      subseg ca0 cs0 cs1;
      store ca0 0;
      lea csp 1 ] ++
    fetch_asm ".Limport_switcher" ct0 ++
    fetch_asm ".Limport_main_f" ct1 ++
    fetch_asm ".Limport_g" ca1 ++
    [ mov cs0 cra;
      mov cs1 ct1;
      jalr cra ct0;
      lea csp (-1);
      lea csp (-1);
      load cra csp;
      mov ca0 0;
      mov ca1 0;
      mov ct0 0;
      mov ct1 0;
      mov cs0 0;
      mov cs1 0;
      ret;

      #"g_entry";
      lea ca0 (-1);
      store ca0 7;
      store ca1 9;
      ret ].

  Definition so_C_instrs : list instr :=
    Eval compute in assemble so_C_asm.
  Lemma so_C_assembles : asm_ok (assemble_check so_C_asm).
  Proof. asm_check. Qed.

  (** The offsets of the two entry points from the start of the PCC. *)
  Definition so_C_adv_entry : nat :=
    Eval vm_compute in label_offset so_C_asm "adv_entry".
  Definition so_C_g_entry : nat :=
    Eval vm_compute in label_offset so_C_asm "g_entry".
End SO_C_code.

From griotte Require Import rules proofmode.

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
    so_main_instrs_n 0 ++
    so_main_instrs_n 1 ++
    so_main_instrs_n 2.

  Definition SO_main_code_f : list Word :=
    so_main_instrs_n 3 ++
    so_main_instrs_n 4 ++
    so_main_instrs_n 5 ++
    so_main_instrs_n 6 ++
    so_main_instrs_n 7 ++
    so_main_instrs_n 8 ++
    so_main_instrs_n 9 ++
    so_main_instrs_n 10 ++
    so_main_instrs_n 11 ++
    so_main_instrs_n 12.

  Definition so_main_code : list Word
    := SO_main_code_run ++ SO_main_code_f.

  Definition so_main_data : list Word := [].

  Definition so_main_imports `{!switcherLayout} `{!assertLayout}
    (B_adv : Sealable)
    : list Word :=
    [
      WSentry FwdDisable true XSRW_ Local b_switcher e_switcher a_switcher_call;
      WSentry Inherit true RX Global b_assert e_assert b_assert;
      WSealed ot_switcher B_adv
    ].

  Definition length_so_main_imports `{!switcherLayout} `{!assertLayout} :=
    length
      (so_main_imports (SCap true RO Global za za za)).

  Definition so_exp_tbl_entry_f `{!switcherLayout} `{!assertLayout} :=
    WInt (encode_entry_point 2
            (length_so_main_imports + (length SO_main_code_run))).

  Definition so_entry_f_sb
    b_so_exp_tbl e_so_exp_tbl : Sealable :=
      SCap true RO Global b_so_exp_tbl e_so_exp_tbl (b_so_exp_tbl ^+2)%a.

  Definition so_export_table_entries `{!switcherLayout} `{!assertLayout} : list Word :=
    [ so_exp_tbl_entry_f ].

End SO_Main.
