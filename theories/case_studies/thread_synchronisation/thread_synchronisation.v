From griotte Require Import machine_parameters assembler fetch assert switcher.

Section TSY_K.
  Import Asm_Griotte.
  #[local] Open Scope Z_scope.
  Context `{MP: MachineParameters}.

  (*
    C CODE:

    void f(int* b);   (* in the compartment B *)
    int b = 0;
    int flag = 0;

    int run1()
    {
      f(&b);
      flag = 1;
      return 0;
    }

    int run2()
    {
      while (flag == 0) { yield(); };
      b = 42;
      assert (b == 42);
      return 0;
    }
   *)

  (* Expect, at both entries, with interrupts enabled:
     pc  := (RX, Global, b_K, e_K, the entry)
     cgp := (RW, Global, b, b+2, b)     (b at b, flag at b+1)

     b_K + 0 : Sentry FwdDisable XSRW_ b_switcher e_switcher a_cc_switcher
     b_K + 1 : Sentry Inherit RX b_assert e_assert a_assert
     b_K + 2 : WSealed ot_switcher B.f
   *)
  Definition tsy_K_asm : list (list asm_code) :=
    [ [ (* the imports *)
        #@".Limport_switcher";
        #@".Limport_assert";
        #@".Limport_B_f";

        #".Lsync_run1";
        mov cs0 cra;            (* cs0 -> return-to-switcher *)
        (* f(&b) *)
        mov ca0 cgp;
        geta ct0 ca0;
        add ct1 ct0 1;
        subseg ca0 ca0 ct0 ct1  (* ca0 := (RW, Global, b, b+1, b) *)
      ];
      #".Lsync_fetch_switcher" ::
      fetch_asm ".Limport_switcher" ctp; (* ctp -> switcher entry point *)
      #".Lsync_fetch_B_f" ::
      fetch_asm ".Limport_B_f" ct1;      (* ct1 -> {B.f}_(ot_switcher) *)
      [ #".Lsync_call_B";
        jalr cra ctp;
        (* flag = 1 *)
        #".Lsync_flag";
        lea cgp cgp 1;          (* cgp -> flag *)
        store cgp 1;            (* hands the world of B over *)
        (* return 0 *)
        #".Lsync_run1_return";
        mov ca0 0;
        mov ca1 0;
        mov cra cs0;
        ret
      ];
      [ #".Lsync_run2";
        mov ct0 cgp;
        lea ct0 ct0 1;          (* ct0 -> flag *)
        (* while (flag == 0) { yield(); } *)
        #".Lsync_wait";
        load ct1 ct0;           (* takes the world of B when it reads 1 *)
        jnez (".Lsync_go")%asm ct1;
        ecall;                  (* yield() *)
        jmp (".Lsync_wait")%asm;
        (* b = 42 *)
        #".Lsync_go";
        store cgp 42;
        (* assert (b == 42) *)
        load ct0 cgp;           (* ct0 -> b *)
        mov ct1 42
      ];
      #".Lsync_assert" ::
      assert_asm ".Limport_assert" ct2 ca2; (* asserts that ct0 = ct1 *)
      [ (* return 0 *)
        #".Lsync_run2_return";
        mov ca0 0;
        mov ca1 0;
        ret
      ]
    ].

  Definition tsy_K_assembled :=
    Eval compute in assemble_block tsy_K_asm.
  Lemma tsy_K_assembles : asm_ok (assemble_block_check tsy_K_asm).
  Proof. asm_check. Qed.
  Definition tsy_K_instrs_n (n : nat) : list Word :=
    encodeInstrsW (default [] (tsy_K_assembled !! n)).

  Definition tsy_K_code : list Word :=
    tsy_K_instrs_n 0 ++
    tsy_K_instrs_n 1 ++
    tsy_K_instrs_n 2 ++
    tsy_K_instrs_n 3 ++
    tsy_K_instrs_n 4 ++
    tsy_K_instrs_n 5 ++
    tsy_K_instrs_n 6.

  Definition tsy_K_data : list Word := [WInt 0; WInt 0]. (* b; flag *)

  Definition tsy_K_imports `{!switcherLayout} `{!assertLayout}
    (B_f : Sealable) : list Word :=
    [
      switcher_entry_call;
      assert_entry;
      WSealed ot_switcher B_f
    ].

  (** The entry of [run2], from the base of the PCC: the label's offset,
      which counts the imports. *)
  Lemma tsy_run2_offset :
    Asm_Griotte.label_offset (concat tsy_K_asm) ".Lsync_run2" = 19%nat.
  Proof. reflexivity. Qed.
End TSY_K.

(** The index of the export [f] of the adversary [B]. *)
Definition tsy_B_entry_f : nat := 0.
