From griotte Require Import machine_parameters assembler fetch assert switcher.

Section DROE_Main.
  Import Asm_Griotte.
  #[local] Open Scope Z_scope.
  Context `{MP: MachineParameters}.


  (*
    PSEUDO-CODE:

      set b := 42
      set a := (RW, Global, b, b+1, b)
      call B.adv (RO_DRO, Global, a, a+1, a)
      assert (b == 42)
      return 0

   *)

  (* Expect:
     pc  := (RX, Global, b_main, e_main, b_main_code)
     cgp := (RW, Global, b, e, b)

     b_main + 0 : WSentry FwdDisable true XSRW_ b_switcher e_switcher a_cc_switcher
     b_main + 1 : WSentry Inherit true RX b_assert e_assert a_assert
     b_main + 2 : WSealed ot_switcher B.f


      data after initial setup:
      +----------------+ b
      |        42      |
      +----------------+ a
      | (RW,G,b,b+1,b) |
      +----------------+
      |       ...      |


   *)
  (** [ro_dro] is the encoding of the permission and locality of the
      shared capability, kept abstract during the assembly. *)
  Definition droe_main_asm (ro_dro : Z) : list (list asm_code) :=
    [ [ (* the imports *)
        #@".Limport_switcher";
        #@".Limport_assert";
        #@".Limport_B_f";

        (* set b <- 42 *)
        #".Ldroe_init";
        store cgp 42;       (* b <- 42 *)
        mov ct0 cgp;        (* ct0 := (RW, Global, b, e, b) *)

        (* set a <- (RW, Global, b, b+1, b) *)
        getb ct1 cgp;       (* ct1 := b *)
        add ct2 ct1 1;      (* ct2 := b+1 = a *)
        subseg ct0 ct1 ct2; (* ct0 := (RW, Global, b, b+1, b) *)

        lea cgp 1;          (* cgp := (RW, Global, b, e, b+1) *)
        store cgp ct0;      (* a <- (RW, Global, b, b+1, b) *)

        (* call B.f (RO_DRO, Global, a, a+1,a) *)
        mov ca0 cgp;        (* ca0 := (RW, Global, b, e, b+1) = (RW, Global, b, e, a) *)
        lea cgp (-1);       (* cgp := (RW, Global, b, e, b) *)
        add ct1 ct2 1;      (* ct1 := a+1 *)
        subseg ca0 ct2 ct1; (* ca0 := (RW, Global, a, a+1, a) *)
        restrict ca0 ro_dro (* ca0 := (RO_DRO, Global, a, a+1, a) *)
      ];
      #".Ldroe_fetch_switcher" ::
      fetch_asm ".Limport_switcher" ct0; (* ct0 -> switcher entry point *)
      #".Ldroe_fetch_B_f" ::
      fetch_asm ".Limport_B_f" ct1; (* ct1 -> {B.f}_(ot_switcher)  *)
      [ #".Ldroe_call_B";
        mov cs0 cra; (* stores the return-to-switcher *)
        (* clear the arguments *)
        jalr cra ct0;
        #".Ldroe_return";
        mov cra cs0; (* restores the return-to-switcher *)
        (* -- return from the call -- *)
        (* assert b == 42 *)
        load ct0 cgp; (* ct0 -> c *)
        mov ct1 42
      ];
      #".Ldroe_assert" ::
      assert_asm ".Limport_assert" ct2 ca2; (* asserts that ( *ct0 = *ct1 ) *)
      [ (* erase returned values from the call *)
        #".Ldroe_halt";
        mov ca0 0;
        mov ca1 0;
        halt
      ]
    ].

  Definition droe_main_assembled :=
    Eval compute in (λ ro_dro, assemble_block (droe_main_asm ro_dro)).
  Lemma droe_main_assembles ro_dro : asm_ok (assemble_block_check (droe_main_asm ro_dro)).
  Proof. asm_check. Qed.
  Definition droe_main_instrs_n (n : nat) : list Word :=
    encodeInstrsW (default [] (droe_main_assembled (encodePermPair (RO_DRO, Global)) !! n)).

  Definition droe_main_code : list Word :=
    droe_main_instrs_n 0 ++
    droe_main_instrs_n 1 ++
    droe_main_instrs_n 2 ++
    droe_main_instrs_n 3 ++
    droe_main_instrs_n 4 ++
    droe_main_instrs_n 5.

  Definition droe_main_data : list Word := [WInt 0; WInt 0].

  Definition droe_main_imports `{!switcherLayout} `{!assertLayout}
    (B_f : Sealable) : list Word :=
    [
      WSentry FwdDisable true XSRW_ Local b_switcher e_switcher a_switcher_call;
      WSentry Inherit true RX Global b_assert e_assert b_assert;
      WSealed ot_switcher B_f
    ].

End DROE_Main.
