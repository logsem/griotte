From cap_machine Require Import proofmode machine_parameters.
From cap_machine Require Import switcher.


Section CmptLayout.
  Context `{MP: MachineParameters}.

  Record cmptSwitcher : Type :=
    mkCmptSwitcher {

        b_switcher : Addr ;
        e_switcher : Addr ;
        a_switcher_cc : Addr ;
        ot_switcher : OType ;
        content_switcher : list Word;

        content_switcher_correct :
        content_switcher = (WSealRange (true,true) Global ot_switcher (ot_switcher^+1)%ot ot_switcher)::switcher_instrs;

        switcher_size :
          (b_switcher + length content_switcher)%a = Some e_switcher ;

        switcher_cc_entry_point :
          (b_switcher + 1)%a = Some a_switcher_cc ;

      }.

       codefrag b_assert (assert_subroutine_instrs rret rsrc1 rsrc2) ∗
       ⌜(b_assert + length (assert_subroutine_instrs rret rsrc1 rsrc2))%a = Some cap_addr⌝ ∗
       ⌜(cap_addr + 1)%a = Some e_assert⌝ ∗


  Record cmptAssert : Type :=
    mkCmptSwitcher {

        b_assert : Addr ;
        e_assert : Addr ;
        flag_assert : Addr ;
        content_assert : list Word;

        content_assert_correct :
        content_assert = assert_instrs++[WCap RW Global flag_assert (flag_assert ^+1)%a flag_assert];

        assert_code_size :
        (assert_start + length content_assert)%a = Some assert_cap;
        assert_size :
          (b_assert + length content_assert)%a = Some e_assert ;

        assert_cc_entry_point :
          (b_assert + 1)%a = Some a_assert_cc ;


        assert_size :
          (b_assert + length assert_instrs)%a = Some e_assert ;

        switcher_inbounds :
        ( (b_switcher ^+ 1)%a <= a_switcher_cc < e_switcher)%a ;

  (* (* assert library *) *)
  (* assert_start : Addr; *)
  (* assert_flag : Addr; *)
  (* assert_end : Addr; *)

  (* assert_code_size : *)
  (*   (assert_start + length assert_subroutine_instrs)%a = Some assert_cap; *)
  (* assert_cap_size : *)
  (*   (assert_cap + 1)%a = Some assert_flag; *)
  (* assert_flag_size : *)
  (*   (assert_flag + 1)%a = Some assert_end; *)


  (*       sealing_switcher_w : *)
  (*       sealing_switcher = *)
  (*       WSealRange (true,true) Global ot_switcher (ot_switcher^+1)%ot ot_switcher; *)
      }.


  Definition is_switcher_cc (w : Word) : Prop :=
    w = WCap E_XSR_ Global b_switcher e_switcher a_switcher_cc.

  Definition is_valid_adv_import (w : Word) : Prop :=
    is_sealed_with_o w ot_switcher \/ is_switcher_cc w.

  (* TODO add the in_region condition *)
  Definition is_valid_adv_data (b e : Addr) (w : Word)  : Prop :=
    is_z w = true.
  (* \/ in_region w b e. *)



  Context { ot_switcher: OType } { b_switcher e_switcher a_switcher_cc : Addr }.

Record cmpt : Type :=
  mkCmpt {
      cmpt_b_pcc : Addr;
      cmpt_a_code : Addr;
      cmpt_e_pcc : Addr;

      cmpt_b_data : Addr;
      cmpt_e_data : Addr;

      cmpt_imports : list Word;
      cmpt_code : list Word;
      cmpt_data : list Word;

      cmpt_import_size : (cmpt_b_pcc + length cmpt_imports)%a = Some cmpt_a_code;
      cmpt_code_size : (cmpt_a_code + length cmpt_code)%a = Some cmpt_e_pcc;
      cmpt_data_size : (cmpt_b_data + length cmpt_data)%a = Some cmpt_e_data;

      code_data_disjoint :
            (finz.seq_between cmpt_b_pcc cmpt_e_pcc)
              ## (finz.seq_between cmpt_b_data cmpt_e_data)
    }.


Record cmptAdv : Type :=
  mkCmptAdv {

      adv_cmpt : cmpt ;

      adv_cmpt_import_switcher_cc :
        (cmpt_imports adv_cmpt) !! 0 = Some (WCap E_XSR_ Global b_switcher e_switcher a_switcher_cc);
      adv_cmpt_importsWF :
        Forall is_valid_adv_import (cmpt_imports adv_cmpt) ;
      adv_cmpt_codeWF :
        Forall is_z (cmpt_code adv_cmpt) ;
      adv_cmpt_dataWF :
        Forall (is_valid_adv_data (cmpt_b_data adv_cmpt) (cmpt_e_data adv_cmpt)) (cmpt_data adv_cmpt) ;
    }.


Context { b_assert e_assert : Addr }.
Record cmptMain : Type :=
  mkCmptMain {

      main_cmpt : cmpt ;

      main_cmpt_import_switcher_cc :
        (cmpt_imports main_cmpt) !! 0 = Some (WCap E_XSR_ Global b_switcher e_switcher a_switcher_cc);
      main_cmpt_assert :
        (cmpt_imports main_cmpt) !! 1 = Some (WCap E_RX Global b_assert e_assert b_assert);

    }.




End CmptLayout.
