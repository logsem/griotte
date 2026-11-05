From griotte Require Import machine_parameters assembler fetch assert switcher.

Section TI_K.
  Import Asm_Griotte.
  #[local] Open Scope Z_scope.
  Context `{MP: MachineParameters}.

  (*
    C CODE:

    void f(int* b);   (* in the compartment B *)
    int b;

    int run()
    {
      b = 0;
      f(restrict(&b, RW, Local));
      b = 42;
      assert (b == 42);
      return 0;
    }
   *)

  (* Expect:
     pc  := (RX, Global, b_K, e_K, b_K_code)
     cgp := (RW, Global, b, b+1, b)

     b_K + 0 : Sentry FwdDisable XSRW_ b_switcher e_switcher a_cc_switcher
     b_K + 1 : Sentry Inherit RX b_assert e_assert a_assert
     b_K + 2 : WSealed ot_switcher B.f
   *)
  (** [rw_local] is the encoding of the permission and locality of the
      lent capability, kept abstract during the assembly. *)
  Definition ti_K_asm (rw_local : Z) : list (list asm_code) :=
    [ [ (* the imports *)
        #@".Limport_switcher";
        #@".Limport_assert";
        #@".Limport_B_f";

        #".Lti_run";
        mov cs0 cra;            (* cs0 -> return-to-switcher *)
        (* b = 0 *)
        store cgp 0;
        (* f(restrict(&b, RW, Local)) *)
        mov ca0 cgp;
        geta ct0 ca0;
        add ct1 ct0 1;
        subseg ca0 ca0 ct0 ct1; (* ca0 := (RW, Global, b, b+1, b) *)
        restrict ca0 ca0 rw_local (* ca0 := (RW, Local, b, b+1, b) *)
      ];
      #".Lti_fetch_switcher" ::
      fetch_asm ".Limport_switcher" ctp; (* ctp -> switcher entry point *)
      #".Lti_fetch_B_f" ::
      fetch_asm ".Limport_B_f" ct1;      (* ct1 -> {B.f}_(ot_switcher) *)
      [ #".Lti_call_B";
        jalr cra ctp;
        (* b = 42 *)
        #".Lti_overwrite";
        store cgp 42;
        (* assert (b == 42) *)
        load ct0 cgp;           (* ct0 -> b *)
        mov ct1 42
      ];
      #".Lti_assert" ::
      assert_asm ".Limport_assert" ct2 ca2; (* asserts that ct0 = ct1 *)
      [ (* return 0 *)
        #".Lti_return";
        mov ca0 0;
        mov ca1 0;
        mov cra cs0;
        ret
      ]
    ].

  Definition ti_K_assembled :=
    Eval compute in (λ rw_local, assemble_block (ti_K_asm rw_local)).
  Lemma ti_K_assembles rw_local : asm_ok (assemble_block_check (ti_K_asm rw_local)).
  Proof. asm_check. Qed.
  Definition ti_K_instrs_n (n : nat) : list Word :=
    encodeInstrsW (default [] (ti_K_assembled (encodePermPair (RW, Local)) !! n)).

  Definition ti_K_code : list Word :=
    ti_K_instrs_n 0 ++
    ti_K_instrs_n 1 ++
    ti_K_instrs_n 2 ++
    ti_K_instrs_n 3 ++
    ti_K_instrs_n 4 ++
    ti_K_instrs_n 5.

  Definition ti_K_data : list Word := [WInt 0]. (* b *)

  Definition ti_K_imports `{!switcherLayout} `{!assertLayout}
    (B_f : Sealable) : list Word :=
    [
      switcher_entry_call;
      assert_entry;
      WSealed ot_switcher B_f
    ].

End TI_K.

(** The index of the export [f] of the adversary [B], in the order of the
    firmware. *)
Definition ti_B_entry_f : nat := 0.
