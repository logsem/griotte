From griotte Require Import machine_parameters assembler fetch assert switcher.

Section DLE_Main.
  Import Asm_Griotte.
  #[local] Open Scope Z_scope.
  Context `{MP: MachineParameters}.


  (*
    PSEUDO-CODE:

    set a := (RW, Global, b, b+1, b)
    set b := 0
    call B.adv (RW-DL, Local, a, a+1, a)
    set b := 42
    call B.adv null
    assert (b==0)
    halt

   *)

  (* Expect:
     pc  := (RX, Global, b_main, e_main, b_main_code)
     cgp := (RW, Global, b, e, b)

     b_main + 0 : WSentry FwdDisable true XSRW_ b_switcher e_switcher a_cc_switcher
     b_main + 1 : WSentry Inherit true RX b_assert e_assert a_assert
     b_main + 2 : WSealed ot_switcher B.f

   *)
  (** [rw_dl] is the encoding of the permission and locality of the
      shared capability, kept abstract during the assembly. *)
  Definition dle_main_asm (rw_dl : Z) : list (list asm_code) :=
    [ [ (* the imports *)
        #@".Limport_switcher";
        #@".Limport_assert";
        #@".Limport_B_f";

        (* set b <- 0 *)
        #".Ldle_init";
        store cgp 0;        (* b <- 0 *)
        mov ct0 cgp;        (* ct0 := (RW, Global, b, e, b) *)

        (* set a <- (RW, Global, b, b+1, b) *)
        getb ct1 cgp;       (* ct1 := b *)
        add ct2 ct1 1;      (* ct2 := b+1 = a *)
        subseg ct0 ct1 ct2; (* ct0 := (RW, Global, b, b+1, b) *)

        lea cgp 1;          (* cgp := (RW, Global, b, e, b+1) *)
        store cgp ct0;      (* a <- (RW, Global, b, b+1, b) *)
        (* call B.f (RW-DL, Local, a, a+1, a) *)
        mov ca0 cgp;        (* ca0 := (RW, Global, b, e, b+1) = (RW, Global, b, e, a) *)
        lea cgp (-1);       (* cgp := (RW, Global, b, e, b) *)
        add ct1 ct2 1;      (* ct1 := a+1 *)
        subseg ca0 ct2 ct1; (* ca0 := (RW, Global, a, a+1, a) *)
        restrict ca0 rw_dl (* ca0 := (RO_DRO, Global, a, a+1, a) *)
      ];
      #".Ldle_fetch_switcher" ::
      fetch_asm ".Limport_switcher" ct0; (* ct0 -> switcher entry point *)
      #".Ldle_fetch_B_f" ::
      fetch_asm ".Limport_B_f" ct1; (* ct1 -> {B.f}_(ot_switcher)  *)
      [ (* Use cs0 and cs1 to save ct0 and ct1 through the call *)
        #".Ldle_call_B";
        mov cs0 ct0; (* cs0 -> switcher entry point *)
        mov cs1 ct1; (* cs1 -> {B.f}_(ot_switcher)  *)
        (* switcher_call to B.f *)
        jalr cra ct0;
        (* set b := 42 *)
        #".Ldle_overwrite";
        store cgp 42;      (* b <- 0 *)
        (* call B.adv null *)
        mov ca0 0;
        mov ct0 cs0; (* ct0 -> switcher entry point *)
        mov ct1 cs1; (* ct1 -> {B.f}_(ot_switcher)  *)
        (* switcher_call to B.f *)
        jalr cra ct0;
        (* assert (b==42) *)
        #".Ldle_check";
        load ct0 cgp; (* ct0 -> b *)
        mov ct1 42  (* ct1 -> 42 *)
      ];
      #".Ldle_assert" ::
      assert_asm ".Limport_assert" ct2 ca2; (* asserts that ( *ct0 = *ct1 ) *)
      [ (* halt *)
        #".Ldle_halt";
        halt
      ]
    ].

  Definition dle_main_assembled :=
    Eval compute in (λ rw_dl, assemble_block (dle_main_asm rw_dl)).
  Lemma dle_main_assembles rw_dl : asm_ok (assemble_block_check (dle_main_asm rw_dl)).
  Proof. asm_check. Qed.
  Definition dle_main_instrs_n (n : nat) : list Word :=
    encodeInstrsW (default [] (dle_main_assembled (encodePermPair (RW_DL, Local)) !! n)).

  Definition dle_main_code : list Word :=
    dle_main_instrs_n 0 ++
    dle_main_instrs_n 1 ++
    dle_main_instrs_n 2 ++
    dle_main_instrs_n 3 ++
    dle_main_instrs_n 4 ++
    dle_main_instrs_n 5.

  Definition dle_main_data : list Word := [WInt 0; WInt 0].

  Definition dle_main_imports `{!switcherLayout} `{!assertLayout}
    (B_f : Sealable) : list Word :=
    [
      WSentry FwdDisable true XSRW_ Local b_switcher e_switcher a_switcher_call;
      WSentry Inherit true RX Global b_assert e_assert b_assert;
      WSealed ot_switcher B_f
    ].

End DLE_Main.
