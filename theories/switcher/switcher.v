From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules proofmode bitblast.
From cap_machine Require Export clear_stack clear_registers.

Section Switcher.
  Context `{MP: MachineParameters}.

  Definition switcher_call_instrs : list Word :=
    encodeInstrsW [
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

        (* Save the callee registers *)
        Store csp cs0;
        Lea csp 1%Z;
        Store csp cs1;
        Lea csp 1%Z;
        Store csp cra;
        Lea csp 1%Z;
        Store csp cgp;
        Lea csp 1%Z;

        (* Check that the trusted stack has enough space *)
        ReadSR ct2 mtdc;
        GetA cs0 ct2;
        machine_base.Add cs0 cs0 1%Z;
        GetE ctp ct2;
        Lt ctp cs0 ctp; (* if (atstk+1 < etstk) then (ctp := 1) else (ctp := 0)*)
        Jnz 2%Z ctp;
        Fail;

        (* Save the caller's stack pointer in the trusted stack *)
        Lea ct2 1%Z;
        Store ct2 csp;
        WriteSR mtdc ct2;

      (* Chop off the stack *)
        GetE cs0 csp;
        GetA cs1 csp;
        Subseg csp cs1 cs0
      ]
      (* Zero out the callee's stack frame *)
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
        (* Restores the return pointer to caller  *)
        Mov cra ca2
      ]
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

  Definition is_switcher_entry_point `{switcherLayout} (w : Word) :=
    bool_decide
      (w = (WSentry XSRW_ Local b_switcher e_switcher a_switcher_call)
           ∨
      (w = (WSentry XSRW_ Local b_switcher e_switcher a_switcher_return)
      ))
  .

  Lemma is_switcher_entry_point_call `{switcherLayout} :
    is_switcher_entry_point (WSentry XSRW_ Local b_switcher e_switcher a_switcher_call) = true.
  Proof.
    rewrite /is_switcher_entry_point.
    rewrite bool_decide_eq_true_2; first done.
    by left.
  Qed.

  Lemma is_switcher_entry_point_return `{switcherLayout} :
    is_switcher_entry_point (WSentry XSRW_ Local b_switcher e_switcher a_switcher_return) = true.
  Proof.
    rewrite /is_switcher_entry_point.
    rewrite bool_decide_eq_true_2; first done.
    by right.
  Qed.

  Definition encode_entry_point (nargs entry_point_offset : Z) : Z :=
    let args := Z.land nargs 7 in
    let off := Z.shiftl entry_point_offset 3 in
    (Z.lor off args).

  Definition decode_entry_point (entry_point : Z) : (Z * Z) :=
    ( Z.land entry_point 7, Z.shiftr entry_point 3).

  Lemma encode_entry_point_eq_nargs nargs off_entry :
    (0 ≤ nargs ≤ 7)%Z -> ( (Z.land (encode_entry_point nargs off_entry) 7)) = nargs.
  Proof.
    intros.
    rewrite /encode_entry_point.
    bitblast.
    destruct (decide (nargs = 0)%Z); simplify_eq; first bitblast.
    destruct (decide (nargs = 1)%Z); simplify_eq; first bitblast.
    destruct (decide (nargs = 2)%Z); simplify_eq; first bitblast.
    destruct (decide (nargs = 3)%Z); simplify_eq; first bitblast.
    destruct (decide (nargs = 4)%Z); simplify_eq; first bitblast.
    destruct (decide (nargs = 5)%Z); simplify_eq; first bitblast.
    destruct (decide (nargs = 6)%Z); simplify_eq; first bitblast.
    destruct (decide (nargs = 7)%Z); simplify_eq; first bitblast.
    lia.
  Qed.

  Lemma encode_entry_point_eq_off nargs off_entry :
    ( (encode_entry_point nargs off_entry ≫ 3)%Z) = off_entry.
  Proof.
    intros.
    rewrite /encode_entry_point.
    bitblast.
  Qed.

End Switcher.
