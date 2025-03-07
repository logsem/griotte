From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules proofmode.

Section Switcher.
  Context `{MP: MachineParameters}.

  (* Expects r1 := e_stk ; r2 := a_stk *)
  Definition clear_stack_instrs (r1 r2 : RegName) : list Word :=
    encodeInstrsW [
        Sub r1 r2 r1;
        Mov r2 csp;
        Jnz 2%Z r1;
        Jmp 5%Z;
        Store r2 0%Z;
        Lea r2 1%Z;
        Add r1 r1 1%Z;
        Jmp (-5)%Z
      ].

  Definition clear_registers_skip_instrs : list Word :=
    encodeInstrsW [
        Jmp ct2;
        Mov ca0 0%Z;
        Mov ca1 0%Z;
        Mov ca2 0%Z;
        Mov ca3 0%Z;
        Mov ca4 0%Z;
        Mov ca5 0%Z;
        Mov ct0 0%Z;
        Mov cnull 0%Z;
        Mov ctp 0%Z;
        Mov ct1 0%Z;
        Mov ct2 0%Z;
        Mov cs0 0%Z;
        Mov cs1 0%Z;
        Mov ca6 0%Z;
        Mov ca7 0%Z;
        Mov cs2 0%Z;
        Mov cs3 0%Z;
        Mov cs4 0%Z;
        Mov cs5 0%Z;
        Mov cs6 0%Z;
        Mov cs7 0%Z;
        Mov cs8 0%Z;
        Mov cs9 0%Z;
        Mov cs10 0%Z;
        Mov cs11 0%Z;
        Mov ct3 0%Z;
        Mov ct4 0%Z;
        Mov ct5 0%Z;
        Mov ct6 0%Z
      ].

  Definition clear_registers_instrs : list Word :=
    encodeInstrsW [
        Mov ct0 0%Z;
        Mov cnull 0%Z;
        Mov ctp 0%Z;
        Mov ct1 0%Z;
        Mov ct2 0%Z;
        Mov ct3 0%Z;
        Mov ct4 0%Z;
        Mov ct5 0%Z;
        Mov ct6 0%Z;
        Mov ca2 0%Z;
        Mov ca3 0%Z;
        Mov ca4 0%Z;
        Mov ca5 0%Z;
        Mov ca6 0%Z;
        Mov ca7 0%Z;
        Mov cs0 0%Z;
        Mov cs1 0%Z;
        Mov cs2 0%Z;
        Mov cs3 0%Z;
        Mov cs4 0%Z;
        Mov cs5 0%Z;
        Mov cs6 0%Z;
        Mov cs7 0%Z;
        Mov cs8 0%Z;
        Mov cs9 0%Z;
        Mov cs10 0%Z;
        Mov cs11 0%Z
      ].

  Definition switcher_instrs : list Word :=
    encodeInstrsW [
        (* Save the callee registers *)
        Store csp cs0;
        Lea csp 1%Z;
        Store csp cs1;
        Lea csp 1%Z;
        Store csp cra;
        Lea csp 1%Z;
        Store csp cgp;
        Lea csp 1%Z;

        (* Check permissions of the stack *)
        GetP ct2 csp;
        Mov ctp (encodePerm RWL);
        Sub ct2 ct2 ctp;
        Jnz 2%Z ct2;
        Jmp 2%Z;
        Fail;

        (* Save the caller's stack pointer in the trusted stack *)
        ReadSR ct2 mtdc;
        Lea ct2 1%Z;
        Store ct2 csp;
        WriteSR mtdc ct2;

      (* Zero out the callee's stack frame *)
        GetE cs0 csp;
        GetA cs1 csp;
        Subseg csp cs1 cs0
      ]
      ++ clear_stack_instrs cs0 cs1
      ++ encodeInstrsW [
        (* Fetch (unsealing capability and unseal entry point *)
        GetB cs1 PC;
        GetA cs0 PC;
        Sub cs1 cs1 cs0;
        Mov cs0 PC;
        Lea cs0 cs1;
        Lea cs0 (-2)%Z;
        Load cs0 cs0;
        UnSeal ct1 cs0 ct1;

        (* Load and decode entry point nargs and offset *)
        Load cs0 ct1;
        LAnd ct2 cs0 7%Z;
        LShiftR cs0 cs0 3%Z;

        (* Prepare callee's PCC in cra, and callee's CGP in cgp *)
        GetB cgp ct1;
        GetA cs1 ct1;
        Sub cs1 cgp cs1;
        Lea ct1 cs1;
        Load cra ct1;
        Lea ct1 1%Z;
        Load cgp ct1;
        Lea cra cs0;
        Add ct2 ct2 1%Z]
      (* clear registers, skipping arguments *)
      ++ clear_registers_skip_instrs
      ++ encodeInstrsW [

        (* Jump to callee *)
        Jalr cra cra;

        (* --- Callback --- *)
        (* Restores caller's stack frame *)
        ReadSR ctp mtdc;
        Load csp ctp;
        Lea ctp (-1)%Z;
        WriteSR mtdc ctp;

        (* Restores the caller's saved registers *)
        Load cgp csp;
        Lea csp (-1)%Z;
        Load ca2 csp;
        Lea csp (-1)%Z;
        Load cs1 csp;
        Lea csp (-1)%Z;
        Load cs0 csp;

        (* Zero out the callee stack frame *)
        GetE ct0 csp;
        GetA ct1 csp]
      ++ clear_stack_instrs ct0 ct1
      ++ encodeInstrsW[

        Sub ct0 ct1 ct0;
        Mov ct1 csp;
        Lea ct1 ct0;
        Jnz 2%Z ct0;
        Jmp 5%Z;
        Store ct1 0%Z;
        Lea ct1 1%Z;
        Add ct0 ct0 1%Z;
        Jmp (-5)%Z;

        (* Restores the return pointer to caller  *)
        Mov cra ca2]
      (* Clear registers *)
      ++ clear_registers_instrs
      ++ encodeInstrsW [
        (* Jump back to caller *)
        JmpCap cra
      ].

  Definition encode_entry_point (nargs entry_point_offset : Z) : Z :=
    let args := Z.land nargs 7 in
    let off := Z.shiftl entry_point_offset 3 in
    (Z.lor off args).

  Definition decode_entry_point (entry_point : Z) : (Z * Z) :=
    ( Z.land entry_point 7, Z.shiftr entry_point 3).

End Switcher.
