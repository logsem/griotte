From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules proofmode.
From cap_machine Require Export clear_stack clear_registers bitblast.

Section Switcher.
  Context `{MP: MachineParameters}.

  Definition switcher_call_instrs : list Word :=
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

        (* Check locality of the stack *)
        GetL ct2 csp;
        Mov ctp (encodeLoc Local);
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
        machine_base.Add ct2 ct2 1%Z]
      (* clear registers, skipping arguments *)
      ++ clear_registers_pre_call_skip_instrs
      ++ clear_registers_pre_call_instrs
      ++ encodeInstrsW [

        (* Jump to callee *)
        Jalr cra cra
      ].

  Definition switcher_return_instrs : list Word :=
    encodeInstrsW [

        (* --- Callback --- *)
        (* Restores caller's stack frame *)
        ReadSR ctp mtdc;
        Load csp ctp;
        Lea ctp (-1)%Z;
        WriteSR mtdc ctp;

        (* Restores the caller's saved registers *)
        Lea csp (-1)%Z;
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

        (* Sub ct0 ct1 ct0; *)
        (* Mov ct1 csp; *)
        (* Lea ct1 ct0; *)
        (* Jnz 2%Z ct0; *)
        (* Jmp 5%Z; *)
        (* Store ct1 0%Z; *)
        (* Lea ct1 1%Z; *)
        (* Add ct0 ct0 1%Z; *)
        (* Jmp (-5)%Z; *)

        (* Restores the return pointer to caller  *)
        Mov cra ca2]
      (* Clear registers *)
      ++ clear_registers_post_call_instrs
      ++ encodeInstrsW [
        (* Jump back to caller *)
        JmpCap cra
      ].

  Definition switcher_instrs : list Word :=
    switcher_call_instrs ++ switcher_return_instrs.


  Class switcherLayout : Type :=
    mkCmptSwitcher {
        b_switcher : Addr ;
        e_switcher : Addr ;
        a_switcher_call : Addr ;
        a_switcher_return : Addr ;

        ot_switcher : OType ;

        b_trusted_stack : Addr;
        e_trusted_stack : Addr;

        switcher_size :
        (a_switcher_call + length switcher_instrs)%a = Some e_switcher ;

        switcher_call_entry_point :
        (b_switcher + 1)%a = Some a_switcher_call ;

        switcher_return_entry_point :
        (b_switcher + (1 + length switcher_call_instrs) )%a = Some a_switcher_return ;
      }.

  Definition is_switcher_entry_point `{switcherLayout} (p : Perm) (g : Locality) (b e a : Addr) :=
    if (bool_decide (p = XSRW_)) && (bool_decide (g = Local))
    then
      if (b =? b_switcher)%a && (e =? e_switcher)%a
      then (if (a =? a_switcher_call)%a || (a =? a_switcher_return)%a then true else false)
      else false
    else false.

End Switcher.
