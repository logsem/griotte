From griotte Require Import machine_parameters assembler fetch switcher.

Section Counter_Main.
  Import Asm_Griotte.
  Local Open Scope Z_scope.
  Context `{MP: MachineParameters}.


  (*
    PSEUDO-CODE:

      get a
      set a := a + 1
      return a

   *)

  (* Expect:
     pc  := (RX, Global, b_main, e_main, b_main_code)
     cgp := (RW, Global, b, e, b)

     b_main + 0 : WSentry true XSRW_ b_switcher e_switcher a_cc_switcher
     b_main + 1 : WSealed ot_switcher C.f

      data:
      +----------------+ a
      |      v >= 0    |
      +----------------+
      |       ...      |


   *)
  Definition counter_main_asm : list (list asm_code) :=
    [ [ (* the imports *)
        #@".Limport_switcher";
        #@".Limport_C_f";

        (* get a *)
        load cs0 cgp;
        (* set a := a + 1 *)
        add cs0 cs0 1;
        store cgp cs0
        (* call C_f*)
      ];
      fetch_asm ".Limport_switcher" ct0; (* ct0 -> switcher entry point *)
      fetch_asm ".Limport_C_f" ct1; (* ct1 -> {B.f}_(ot_switcher)  *)
      [ mov cs0 cra; (* stores the return-to-switcher *)
        jalr cra ct0 (* jmp to entry point *)
      ];
      [ mov cra cs0; (* restores the return-to-switcher *)

        (* return a *)
        mov ca0 0;
        mov ca1 0;
        mov cs0 0;
        mov cs1 0;
        ret
      ]
    ].

  Definition counter_main_assembled' :=
    Eval vm_compute in assemble_block counter_main_asm.
  Definition counter_main_assembled :=
    Eval cbv in revert_regs_code_block counter_main_assembled'.
  Definition counter_main_instrs_n (n : nat) : list Word :=
    encodeInstrsW (default [] (counter_main_assembled !! n)).

  Definition counter_main_code : list Word :=
    counter_main_instrs_n 0 ++
    counter_main_instrs_n 1 ++
    counter_main_instrs_n 2 ++
    counter_main_instrs_n 3 ++
    counter_main_instrs_n 4.

  Definition counter_main_data : list Word := [WInt 0].

  Definition counter_main_imports `{!switcherLayout}
    (C_f : Sealable) : list Word :=
    [
      WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call;
      WSealed ot_switcher C_f
    ].

End Counter_Main.
