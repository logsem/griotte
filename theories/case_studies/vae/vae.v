From griotte Require Import machine_parameters assembler fetch assert switcher.

Section VAE_Main.
  Import Asm_Griotte.
  Local Open Scope Z_scope.
  Context `{MP: MachineParameters}.


  (*
    PSEUDO-CODE:

    init:
      set a := 0
      call B.adv
      halt

    awkward:
      set a := 0
      call g ()
      set a := 1
      call g ()
      assert (a == 1)
      return
   *)

  Definition vae_main_asm : list (list asm_code) :=
    [ (* init *)
      [ (* the imports *)
        #@".Limport_switcher";
        #@".Limport_assert";
        #@".Limport_B_adv";

        (* set a := 0 *)
        store cgp 0
      ];
      (* call B.adv VAE.awkward *)
      fetch_asm ".Limport_switcher" ct0; (* ct0 -> switcher entry point *)
      fetch_asm ".Limport_B_adv" ct1; (* ct1 -> {B.f}_(ot_switcher)  *)
      [ jalr cra ct0; (* jmp to entry point *)
        halt
      ];
      (* awkward *)
      (* set a := 0 *)
      [ store cgp 0 ];
      (* call g () *)
      fetch_asm ".Limport_switcher" ct0; (* ct0 -> switcher entry point *)
      [ mov cs0 cra; (* cs0 -> return-to-switcher *)
        mov cs1 ca0; (* cs1 -> fun_g *)
        mov ct1 ca0; (* ct1 -> fun_g *)
        mov ca0 0;
        jalr cra ct0 (* jmp to g *)
      ];
      (* set a := 1 *)
      [ store cgp 1;
        mov cra cs0; (* cra -> return_to-switcher *)
        mov ct1 cs1  (* ct1 -> fun_g *)
      ];
      (* call g () *)
      fetch_asm ".Limport_switcher" ct0; (* ct0 -> switcher entry point *)
      [ mov cs0 cra; (* cs0 -> return-to-switcher *)
        mov ca0 0;
        mov ca1 0;
        jalr cra ct0; (* jmp to arg_1 *)

        (* assert (a == 1) *)
        load ct0 cgp; (* ct0 -> a *)
        mov ct1 1  (* ct1 -> 1 *)
      ];
      assert_asm ".Limport_assert" ct2 ca2; (* asserts that ( *ct0 = *ct1 ) *)
      (* return cra *)
      [ mov cra cs0; (* cra -> return_to-switcher *)

        (* return a *)
        mov ca0 0;
        mov ca1 0;
        ret
      ]
    ].

  Definition vae_main_assembled :=
    Eval compute in assemble_block vae_main_asm.
  Lemma vae_main_assembles : asm_ok (assemble_block_check vae_main_asm).
  Proof. asm_check. Qed.
  Definition vae_main_instrs_n (n : nat) : list Word :=
    encodeInstrsW (default [] (vae_main_assembled !! n)).

  Definition VAE_main_code_init : list Word :=
    vae_main_instrs_n 0 ++
    vae_main_instrs_n 1 ++
    vae_main_instrs_n 2 ++
    vae_main_instrs_n 3.

  Definition VAE_main_code_f (ot_switcher : OType) : list Word :=
    vae_main_instrs_n 4 ++
    vae_main_instrs_n 5 ++
    vae_main_instrs_n 6 ++
    vae_main_instrs_n 7 ++
    vae_main_instrs_n 8 ++
    vae_main_instrs_n 9 ++
    vae_main_instrs_n 10 ++
    vae_main_instrs_n 11.

  Local Close Scope Z_scope.
  Local Coercion Z.of_nat : nat >-> Z.

  Definition vae_main_code `{!switcherLayout} : list Word
    := VAE_main_code_init ++ (VAE_main_code_f ot_switcher).

  Definition vae_main_data : list Word := [WInt 0].

  Definition vae_main_imports `{!switcherLayout} `{!assertLayout}
    (B_adv : Sealable)
    : list Word :=
    [
      WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call;
      WSentry true RX Global b_assert e_assert b_assert;
      WSealed ot_switcher B_adv
    ].

  Definition length_vae_main_imports `{!switcherLayout} `{!assertLayout} :=
    length
      (vae_main_imports (SCap true RO Global za za za)).

  Definition vae_exp_tbl_entry_awkward `{!switcherLayout} `{!assertLayout} :=
    WInt (encode_entry_point 1
            (length_vae_main_imports + (length VAE_main_code_init))).

  Definition vae_entry_awkward_sb
    b_vae_exp_tbl e_vae_exp_tbl : Sealable :=
      SCap true RO Global b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+2)%a.

  Definition vae_export_table_entries `{!switcherLayout} `{!assertLayout} : list Word :=
    [ vae_exp_tbl_entry_awkward ].

End VAE_Main.

(** The code of the concrete adversary of [vae_concrete], assembled here,
    away from the program logic's coercions. *)
Section vae_C_code.
  Import Asm_Griotte.
  Local Open Scope Z_scope.

  Definition vae_C_asm : list asm_code :=
    [ #@".Limport_switcher";
      #@".Limport_awkward";
      #@".Limport_g";
      #"adv_entry";
      store csp cra;
      lea csp 1 ] ++
    fetch_asm ".Limport_switcher" ct0 ++
    fetch_asm ".Limport_awkward" ct1 ++
    fetch_asm ".Limport_g" ca0 ++
    [ jalr cra ct0;
      lea csp (-1);
      load cra csp;
      mov ca0 0;
      ret;

      #"g_entry";
      load ct0 cgp;
      jnz ("g_ret")%asm ct0;
      store cgp 1;
      store csp cra;
      lea csp 1 ] ++
    fetch_asm ".Limport_switcher" ct0 ++
    fetch_asm ".Limport_awkward" ct1 ++
    fetch_asm ".Limport_g" ca0 ++
    [ jalr cra ct0;
      lea csp (-1);
      load cra csp;
      mov ca0 0;
      #"g_ret";
      ret ].

  Definition vae_C_instrs : list instr :=
    Eval compute in assemble vae_C_asm.
  Lemma vae_C_assembles : asm_ok (assemble_check vae_C_asm).
  Proof. asm_check. Qed.

  (** The offsets of the two entry points from the start of the PCC. *)
  Definition vae_C_adv_entry : nat :=
    Eval vm_compute in label_offset vae_C_asm "adv_entry".
  Definition vae_C_g_entry : nat :=
    Eval vm_compute in label_offset vae_C_asm "g_entry".
End vae_C_code.
