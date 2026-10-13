From griotte Require Import machine_parameters assembler fetch assert switcher check_no_overlap.

(** The assembly of [so_main_code], from which the offsets of its fetches
    of imports are derived. The macros [checkra_instrs],
    [check_no_overlap_instrs] and [checkints_instrs] are written in assembly
    here; [so_main_code_asm] checks that the assembly is the code. *)
Section SO_Asm.
  Import Asm_Griotte.
  Local Open Scope Z_scope.
  Context `{MP: MachineParameters}.

  Definition so_secret : Z := 42.

  Definition so_checkra_asm (r r1 r2 : RegName) : list asm_code :=
    [
      getwtype r1 r;
      sub r2 r1 (encodeWordType wt_cap);
      jnz 4 r2;
      getp r1 r;
      sub r2 r1 (encodePerm (O LG LM));
      jnz 2 r2;
      fail;
      sub r2 r1 (encodePerm (O DL LM));
      jnz 2 r2;
      fail;
      sub r2 r1 (encodePerm (O LG DRO));
      jnz 2 r2;
      fail;
      sub r2 r1 (encodePerm (O DL DRO));
      jnz 2 r2;
      fail;
      sub r2 r1 (encodePerm WO);
      jnz 2 r2;
      fail;
      sub r2 r1 (encodePerm WO_DL);
      jnz 2 r2;
      fail;
      sub r2 r1 (encodePerm WO_DRO);
      jnz 2 r2;
      fail;
      sub r2 r1 (encodePerm WO_DL_DRO);
      jnz 2 r2;
      fail;
      sub r2 r1 (encodePerm WLO);
      jnz 2 r2;
      fail;
      sub r2 r1 (encodePerm WLO_DL);
      jnz 2 r2;
      fail;
      sub r2 r1 (encodePerm WLO_DRO);
      jnz 2 r2;
      fail;
      sub r2 r1 (encodePerm WLO_DL_DRO);
      jnz 2 r2;
      fail;
      mov r1 0;
      mov r2 0
    ].

  Definition so_is_int_asm (r r1 : RegName) : list asm_code :=
    [ getwtype r1 r;
      sub r1 r1 (encodeWordType wt_int);
      jnz 2 r1;
      jmp 2;
      fail ].

  Definition so_checkints_asm (r r1 r2 : RegName) : list asm_code :=
    [ (* lea_to_base *)
      getb r1 r;
      geta r2 r;
      sub r1 r1 r2;
      lea r r1;
      mov r1 0;
      mov r2 0;
      getb r1 r;
      gete r2 r;
      lt r1 r1 r2;
      sub r1 r1 1; (* invert result for the jump *)
      jnz 12 r1;
      (* the loop *)
      load r1 r ] ++
    so_is_int_asm r1 r2 ++
    [ lea r 1;
      geta r1 r;
      gete r2 r;
      lt r1 r1 r2;
      jnz (-10) r1;
      mov r1 0;
      mov r2 0 ].

  Definition so_main_asm : list (list asm_code) :=
    [ (* run *)
      (* the imports *)
      [ #@".Limport_switcher";
        #@".Limport_assert";
        #@".Limport_B_adv" ] ++
      fetch_asm ".Limport_switcher" ct0;
      fetch_asm ".Limport_B_adv" ct1;
      [ jalr cra ct0; halt ];
      (* f *)
      [ mov ct1 ca1 ];
      so_checkra_asm ca0 cs0 cs1;
      check_no_overlap_asm ca0 csp cs0 cs1;
      so_checkints_asm ca0 cs0 cs1;
      [ store csp so_secret;
        lea csp 1;
        mov ca1 csp;
        geta cs0 ca1;
        add cs1 cs0 1;
        subseg ca1 cs0 cs1;
        store ca1 0;
        lea csp 1 ];
      fetch_asm ".Limport_switcher" ct0;
      [ mov cs0 cra;
        mov cs1 ct1;
        jalr cra ct0 ];
      [ lea csp (-2);
        load ct0 csp;
        mov ct1 so_secret ];
      assert_asm ".Limport_assert" ct2 ca2;
      [ mov cra cs0;
        mov ca0 0;
        mov ca1 0;
        ret ]
    ].

  Definition so_main_assembled :=
    Eval compute in assemble_block so_main_asm.
  Lemma so_main_assembles : asm_ok (assemble_block_check so_main_asm).
  Proof. asm_check. Qed.

  (** The offset of the fetch (or of the assert) of the block [n]. *)
  Definition so_fetch_offsets : list Z :=
    Eval vm_compute in fetch_offset <$> so_main_assembled.
  Definition so_fetch_offset (n : nat) : Z :=
    default 0 (so_fetch_offsets !! n).
End SO_Asm.

(** The code of the concrete adversary of [stack_object_concrete]. *)
Section SO_C_code.
  Import Asm_Griotte.
  Local Open Scope Z_scope.

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
    Eval vm_compute in default 0%nat ((compute_asm_code_env so_C_asm).2 !! "adv_entry").
  Definition so_C_g_entry : nat :=
    Eval vm_compute in default 0%nat ((compute_asm_code_env so_C_asm).2 !! "g_entry").
End SO_C_code.

From griotte Require Import rules proofmode.
From griotte Require Import checkra checkints.

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
    fetch_instrs (so_fetch_offset 0) ct0 (* ct0 -> switcher entry point *)
    ++ fetch_instrs (so_fetch_offset 1) ct1 (* ct1 -> {B.adv}_(ot_switcher)  *)
    ++
    encodeInstrsW [
      Jalr cra ct0; (* jmp to entry point *)
      Halt
    ].

  Definition so_f_alloc_instrs : list Word :=
    encodeInstrsW [
      (* push (secret_val) on csp_b *)
      Store csp so_secret 0;
      Lea csp 1;
      (* allocate stack object *)
      Mov ca1 csp;
      GetA cs0 ca1;
      machine_instructions.Add cs1 cs0 1%Z;
      Subseg ca1 cs0 cs1;
      Store ca1 0%Z 0;
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
      CLoad ct0 csp 0;
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
      ++ fetch_instrs (so_fetch_offset 8) ct0 (* ct0 -> switcher entry point *)
      ++
      so_f_call_instrs
      ++
      (* assert csp_b *)
      so_f_assert_prep_instrs
      ++ assert_instrs (so_fetch_offset 11) ct2 ca2 (* asserts that ( *ct0 = *ct1 ) *)
      (* return cra *)
      ++
      so_f_return_instrs.

  Definition so_main_code : list Word
    := SO_main_code_run ++ SO_main_code_f.

  (** The code is its assembly. *)
  Lemma so_main_code_asm :
    so_main_code = concat (encodeInstrsW <$> so_main_assembled).
  Proof. reflexivity. Qed.

  Definition so_main_data : list Word := [].

  Definition so_main_imports `{!switcherLayout} `{!assertLayout}
    (B_adv : Sealable)
    : list Word :=
    [
      WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call;
      WSentry true RX Global b_assert e_assert b_assert;
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
