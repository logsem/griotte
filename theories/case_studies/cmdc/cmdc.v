From griotte Require Import machine_parameters assembler fetch assert switcher.

Section CMDC_Main.
  Import Asm_Griotte.
  #[local] Open Scope Z_scope.
  Context `{MP: MachineParameters}.

  (* Expect:
     pc := (RX, Global, b_main, e_main, b_main_code )

     b_main + 0 : WSentry FwdDisable true XSRW_ b_switcher e_switcher a_cc_switcher
     b_main + 1 : WSentry Inherit true RX b_assert e_assert a_assert
     b_main + 2 : WSealed ot_switcher B.f
     b_main + 3 : WSealed ot_switcher C.g

   *)
  Definition cmdc_main_asm : list (list asm_code) :=
    [ [ (* the imports *)
        #@".Limport_switcher";
        #@".Limport_assert";
        #@".Limport_B_f";
        #@".Limport_C_g";

        (* set b <- 0 *)
        #".Lcmdc_init";
        store cgp 0;
        mov ca0 cgp;

        (* set c <- 0 *)
        lea cgp cgp 1;
        store cgp 0;

        (* call B.f b *)
        geta ct0 ca0;
        add ct1 ct0 1;
        subseg ca0 ca0 ct0 ct1 (* ca0 -> b *)
      ];
      #".Lcmdc_call_B" ::
      fetch_asm ".Limport_switcher" ctp; (* ctp -> switcher entry point *)
      #".Lcmdc_fetch_B_f" ::
      fetch_asm ".Limport_B_f" ct1; (* ct1 -> {B.f}_(ot_switcher)  *)
      [ #".Lcmdc_jump_B";
        jalr cra ctp;
        (* assert c == 0 *)
        #".Lcmdc_return_B";
        load ct0 cgp; (* ct0 -> c *)
        mov ct1 0
      ];
      #".Lcmdc_assert_B" ::
      assert_asm ".Limport_assert" ct2 ca2; (* asserts that ( *ct0 = *ct1 ) *)
      [ (* prepare for later *)
        #".Lcmdc_prep_C";
        mov ca0 cgp;
        mov ca1 0; (* erase returned values from the call *)

        (* set b <- 42 *)
        lea cgp cgp (-1);
        store cgp 42;

        (* call C.g c *)
        geta ct0 ca0;
        add ct1 ct0 1;
        subseg ca0 ca0 ct0 ct1 (* ca0 -> c *)
      ];
      #".Lcmdc_call_C" ::
      fetch_asm ".Limport_switcher" ctp; (* ctp -> switcher entry point *)
      #".Lcmdc_fetch_C_g" ::
      fetch_asm ".Limport_C_g" ct1; (* ct1 -> {C.g}_(ot_switcher)  *)
      [ #".Lcmdc_jump_C";
        jalr cra ctp;
        (* assert b == 42 *)
        #".Lcmdc_return_C";
        load ct0 cgp; (* ct0 -> c *)
        mov ct1 42
      ];
      #".Lcmdc_assert_C" ::
      assert_asm ".Limport_assert" ct2 ca2; (* asserts that ( *ct0 = *ct1 ) *)
      [ #".Lcmdc_halt"; halt ]
    ].

  Definition cmdc_main_assembled :=
    Eval compute in assemble_block cmdc_main_asm.
  Lemma cmdc_main_assembles : asm_ok (assemble_block_check cmdc_main_asm).
  Proof. asm_check. Qed.
  Definition cmdc_main_instrs_n (n : nat) : list Word :=
    encodeInstrsW (default [] (cmdc_main_assembled !! n)).

  Definition cmdc_main_code : list Word :=
    cmdc_main_instrs_n 0 ++
    cmdc_main_instrs_n 1 ++
    cmdc_main_instrs_n 2 ++
    cmdc_main_instrs_n 3 ++
    cmdc_main_instrs_n 4 ++
    cmdc_main_instrs_n 5 ++
    cmdc_main_instrs_n 6 ++
    cmdc_main_instrs_n 7 ++
    cmdc_main_instrs_n 8 ++
    cmdc_main_instrs_n 9 ++
    cmdc_main_instrs_n 10.

  Definition cmdc_main_data : list Word := [WInt 0; WInt 0].

  Definition cmdc_main_imports `{!switcherLayout} `{!assertLayout}
    (B_f C_g : Sealable) : list Word :=
    [
      WSentry FwdDisable true XSRW_ Local b_switcher e_switcher a_switcher_call;
      WSentry Inherit true RX Global b_assert e_assert b_assert;
      WSealed ot_switcher B_f;
      WSealed ot_switcher C_g
    ].

  Definition cmdc_B_f_args : nat := 1.
  Definition cmdc_C_g_args : nat := 1.

End CMDC_Main.

(** The indices of the exports [f] of [B] and [g] of [C], in the order of the
    firmware. *)
Definition cmdc_B_entry_f : nat := 0.
Definition cmdc_C_entry_g : nat := 0.
