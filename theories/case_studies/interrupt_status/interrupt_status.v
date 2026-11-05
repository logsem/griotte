From griotte Require Import machine_parameters assembler fetch assert switcher.

Section IST_K.
  Import Asm_Griotte.
  #[local] Open Scope Z_scope.
  Context `{MP: MachineParameters}.

  (*
    C CODE:

    void f(int* b);   (* in the compartment B *)
    int b;

    [[cheriot::interrupt_state(disabled)]]
    int run()
    {
      b = 0;
      f(&b);
      b = 42;
      assert (b == 42);
      return 0;
    }
   *)

  (* Expect, with interrupts disabled:
     pc  := (RX, Global, b_K, e_K, b_K_code)
     cgp := (RW, Global, b, b+1, b)

     b_K + 0 : Sentry FwdDisable XSRW_ b_switcher e_switcher a_cc_switcher
     b_K + 1 : Sentry Inherit RX b_assert e_assert a_assert
     b_K + 2 : WSealed ot_switcher B.f
   *)
  Definition ist_K_asm : list (list asm_code) :=
    [ [ (* the imports *)
        #@".Limport_switcher";
        #@".Limport_assert";
        #@".Limport_B_f";

        #".Lstatus_run";
        mov cs0 cra;            (* cs0 -> return-to-switcher *)
        (* b = 0 *)
        store cgp 0;
        (* f(&b) *)
        mov ca0 cgp;
        geta ct0 ca0;
        add ct1 ct0 1;
        subseg ca0 ca0 ct0 ct1  (* ca0 := (RW, Global, b, b+1, b) *)
      ];
      #".Lstatus_fetch_switcher" ::
      fetch_asm ".Limport_switcher" ctp; (* ctp -> switcher entry point *)
      #".Lstatus_fetch_B_f" ::
      fetch_asm ".Limport_B_f" ct1;      (* ct1 -> {B.f}_(ot_switcher) *)
      [ #".Lstatus_call_B";
        jalr cra ctp;           (* back with interrupts disabled *)
        (* b = 42 *)
        #".Lstatus_overwrite";
        store cgp 42;
        (* assert (b == 42) *)
        load ct0 cgp;           (* ct0 -> b *)
        mov ct1 42
      ];
      #".Lstatus_assert" ::
      assert_asm ".Limport_assert" ct2 ca2; (* asserts that ct0 = ct1 *)
      [ (* return 0 *)
        #".Lstatus_return";
        mov ca0 0;
        mov ca1 0;
        mov cra cs0;
        ret
      ]
    ].

  Definition ist_K_assembled :=
    Eval compute in assemble_block ist_K_asm.
  Lemma ist_K_assembles : asm_ok (assemble_block_check ist_K_asm).
  Proof. asm_check. Qed.
  Definition ist_K_instrs_n (n : nat) : list Word :=
    encodeInstrsW (default [] (ist_K_assembled !! n)).

  Definition ist_K_code : list Word :=
    ist_K_instrs_n 0 ++
    ist_K_instrs_n 1 ++
    ist_K_instrs_n 2 ++
    ist_K_instrs_n 3 ++
    ist_K_instrs_n 4 ++
    ist_K_instrs_n 5.

  Definition ist_K_data : list Word := [WInt 0]. (* b *)

  Definition ist_K_imports `{!switcherLayout} `{!assertLayout}
    (B_f : Sealable) : list Word :=
    [
      switcher_entry_call;
      assert_entry;
      WSealed ot_switcher B_f
    ].

End IST_K.

(** The index of the export [f] of the adversary [B], in the order of the
    firmware. *)
Definition ist_B_entry_f : nat := 0.
