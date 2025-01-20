From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel.
From cap_machine.proofmode Require Import tactics_helpers map_simpl solve_pure.
From cap_machine Require Export iris_extra addr_reg_sample contiguous.

Section ReqPerm.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.


  (* -------------------------------------- REQPERM ----------------------------------- *)
  (* the following macro requires that a given registers contains a capability with a
     given (encoded) permission. If this is not the case, the macro goes to fail,
     otherwise it continues *)

  Definition reqperm_instrs r z :=
    [
    get_wtype r_t1 r;
    sub_r_z r_t1 r_t1 (encodeWordType wt_cap);
    move_r r_t2 PC;
    lea_z r_t2 11;
    jnz r_t2 r_t1; (* if is_int(r) then jmp LABEL*)
    getp r_t1 r;
    sub_r_z r_t1 r_t1 z;
    move_r r_t2 PC;
    lea_z r_t2 6;
    jnz r_t2 r_t1;
    move_r r_t2 PC;
    lea_z r_t2 4;
    jmp r_t2;
    fail_end;
    move_z r_t1 0;
    move_z r_t2 0].

  Definition reqperm r z a : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(reqperm_instrs r z), a_i ↦ₐ w_i)%I.

  Lemma reqperm_spec r perm a w pc_p pc_b pc_e a_first a_last φ :
    isCorrectPC_range pc_p pc_b pc_e a_first a_last ->
    contiguous_between a a_first a_last ->

      ▷ reqperm r (encodePerm perm) a
    ∗ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e a_first
    ∗ ▷ r ↦ᵣ w
    ∗ ▷ (∃ w, r_t1 ↦ᵣ w)
    ∗ ▷ (∃ w, r_t2 ↦ᵣ w)
    ∗ ▷ (if isPermWord w perm then
           ∃ b e a', ⌜w = WCap perm b e a'⌝ ∧
          (PC ↦ᵣ WCap pc_p pc_b pc_e a_last ∗ reqperm r (encodePerm perm) a ∗
            r ↦ᵣ WCap perm b e a' ∗ r_t1 ↦ᵣ WInt 0%Z ∗ r_t2 ↦ᵣ WInt 0%Z
            -∗ WP Seq (Instr Executable) {{ φ }})
        else φ FailedV)
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont) "(>Hprog & >HPC & >Hr & >Hr_t1 & >Hr_t2 & Hcont)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength. simpl in *.
    iDestruct ("Hr_t1") as (w1) "Hr_t1".
    iAssert (⌜r ≠ PC⌝)%I as %Hne.
    { destruct (decide (r = PC)); auto; subst. iDestruct (regname_dupl_false with "HPC Hr") as %Hcontr. done. }

    iPrologue "Hprog".
    apply contiguous_between_cons_inv_first in Hcont as Heq. subst.
    destruct a as [|a l];[done|].
    iApply (wp_Get_success with "[$HPC $Hi $Hr $Hr_t1]")
    ; [apply decode_encode_instrW_inv|solve_pure|iCorrectPC a_first a_last |iContiguous_next Hcont 0|auto..].

    iEpilogue "(HPC & Hi & Hr & Hr_t1)". iRename "Hi" into "Hprog_done".

    iPrologue "Hprog".
    destruct l;[done|].
    iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|auto|iContiguous_next Hcont 1|iCorrectPC a_first a_last|..].
    iEpilogue "(HPC & Hi & Hr_t1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    iSimpl in "Hr_t1".

    iPrologue "Hprog".
    destruct l;[done|].
    iDestruct "Hr_t2" as (w2) "Hr_t2".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 2|auto|..].
    iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".

    iPrologue "Hprog".
    do 12 (destruct l;[done|]).
    assert ((f + 11)%a = Some f10) as Hlea.
    { apply (contiguous_between_incr_addr_middle _ _ _ 2 11 f f10) in Hcont; auto. }
    assert (pc_p ≠ E) as HneE.
    { apply isCorrectPC_range_perm in Hvpc as [Heq | Heq ]; subst; auto.
      apply (contiguous_between_middle_bounds _ 0 a_first) in Hcont as [_ Hlt]; auto. }
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 3| exact |simpl;auto..].
    iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".

    destruct (is_cap w) eqn:Hcap ; cycle 1.
    {
      assert (isPermWord w perm = false) as ->. {destruct_word w; auto. inversion Hcap. }

      (* if w is not a capability we jump to the failure case *)
      iPrologue "Hprog".
      iApply (wp_jnz_success_jmp with "[$HPC $Hi $Hr_t2 $Hr_t1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|..].
      { intros Hcontr; clear -Hcap Hcontr.
        destruct w; [| (destruct sb; [by simpl in Hcap|]) |]
        ; unfold wt_cap in Hcontr
        ; injection Hcontr
        ; clear Hcontr; intro Hcontr
        ; apply Zminus_eq in Hcontr
        ; match goal with
          | H: encodeWordType ?x = encodeWordType ?y |- _ =>
              pose proof (encodeWordType_correct x y) as Hcontr2 ; cbn in Hcontr2
          end
        ; auto.
      }
      iEpilogue "(HPC & Hi & Hr_t2 & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
      do 8 (iDestruct "Hprog" as "[Hi Hprog]"; iCombine "Hi" "Hprog_done" as "Hprog_done").
      (* fail *)
      iPrologue "Hprog".
      assert (updatePcPerm (WCap pc_p pc_b pc_e f10) = (WCap pc_p pc_b pc_e f10)) as ->.
      { destruct pc_p; auto. congruence. }
      iApply (wp_fail with "[$HPC $Hi]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|].
      iEpilogue "(HPC & Hi)". iApply wp_value. iApply "Hcont".
    }

    (* now we know that w is a capability *)
    assert (∃ p b e a, w = WCap p b e a)  as (pc & bc & ec & ac & ->). {destruct_word w; inversion Hcap. eauto. }
    rewrite (_: (encodeWordType (WCap pc bc ec ac) - encodeWordType wt_cap)%Z = 0%Z); cycle 1.
    { rewrite (_ : (encodeWordType (WCap pc bc ec ac))%Z = (encodeWordType wt_cap)%Z)
      ; first lia. apply encodeWordType_correct_cap.
    }
    iPrologue "Hprog".
    iApply (wp_jnz_success_next with "[$HPC $Hi $Hr_t2 $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 4|..].
    iEpilogue "(HPC & Hi & Hr_t2 & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".

    iPrologue "Hprog".
    iApply (wp_Get_success with "[$HPC $Hi $Hr $Hr_t1]");
      [apply decode_encode_instrW_inv|auto|iCorrectPC a_first a_last|iContiguous_next Hcont 5|auto..].
    iEpilogue "(HPC & Hi & Hr & Hr_t1)". iCombine "Hi" "Hprog_done" as "Hprog_done".

    (* sub r_t1 r_t1 (encodeLoc Global) *)
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|auto|iContiguous_next Hcont 6|iCorrectPC a_first a_last|..].
    iEpilogue "(HPC & Hi & Hr_t1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    iSimpl in "Hr_t1".

    (* move r_t2 PC *)
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 7|auto|..].
    iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".

    (* lea r_t2 6 *)
    assert ((f4 + 6)%a = Some f10) as Hlea'.
    { apply (contiguous_between_incr_addr_middle _ _ _ 7 6 f4 f10) in Hcont; auto. }
    assert (pc_p ≠ E) as HneE'.
    { apply isCorrectPC_range_perm in Hvpc as [Heq | Heq ]; subst; auto.
      apply (contiguous_between_middle_bounds _ 0 a_first) in Hcont as [_ Hlt]; auto. }
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 8|apply Hlea'|auto..].
    iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    destruct (decide (encodePerm pc - encodePerm perm = 0))%Z as [e0|e0].
    - (* p is perm *)
      rewrite e0. assert (pc = perm);[apply encodePerm_inj;lia|subst].
      iSimpl in "Hcont". rewrite isPerm_refl. iDestruct "Hcont" as (b0 e1 a' Heq) "Hφ". inversion Heq; subst.
      iPrologue "Hprog".
      iApply (wp_jnz_success_next with "[$HPC $Hi $Hr_t2 $Hr_t1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 9|..].
      iEpilogue "(HPC & Hi & Hr_t2 & Hr_t1)";iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* move_r r_t2 PC *)
      iPrologue "Hprog".
      iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t2]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 10|auto|..].
      iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* lea r_t2 3 *)
      assert ((f7 + 4)%a = Some f11) as Hlea''.
      { apply (contiguous_between_incr_addr_middle _ _ _ 10 4 f7 f11) in Hcont; auto. }
      iPrologue "Hprog".
      iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t2]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 11|apply Hlea''|auto..].
      iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* jmp r_t2 *)
      iPrologue "Hprog".
      iApply (wp_jmp_success with "[$HPC $Hi $Hr_t2]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|..].
      iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
      assert (updatePcPerm (WCap pc_p pc_b pc_e f11) = (WCap pc_p pc_b pc_e f11)) as ->.
      { destruct pc_p; auto. congruence. }
      iDestruct "Hprog" as "[Hi Hprog]". iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* move r_t1 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z with "[$HPC $Hi $Hr_t1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 14|auto|..].
      iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* move r_t2 0 *)
      destruct l; [|done].
      iPrologue "Hprog".
      apply contiguous_between_last with (ai:=f12) in Hcont as Hnext;[|auto].
      iApply (wp_move_success_z with "[$HPC $Hi $Hr_t2]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|apply Hnext|auto|..].
      iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
      iApply "Hφ". iFrame "HPC Hr Hr_t1 Hr_t2".
      do 15 (iDestruct "Hprog_done" as "[Hi Hprog_done]"; iFrame "Hi").
      iFrame.
    - assert (pc ≠ perm) as HneP.
      { intros Hcontr. subst. lia. }
      iSimpl in "Hcont". rewrite isPerm_ne;[|auto].
      (* jnz r_t2 r_t1 *)
      iPrologue "Hprog".
      iApply (wp_jnz_success_jmp with "[$HPC $Hi $Hr_t2 $Hr_t1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|..].
      { intros Hcontr. inversion Hcontr. done. }
      iEpilogue "(HPC & Hi & Hr_t2 & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
      do 3 (iDestruct "Hprog" as "[Hi Hprog]"; iCombine "Hi" "Hprog_done" as "Hprog_done").
      (* fail *)
      iPrologue "Hprog".
      assert (updatePcPerm (WCap pc_p pc_b pc_e f10) = (WCap pc_p pc_b pc_e f10)) as ->.
      { destruct pc_p; auto. congruence. }
      iApply (wp_fail with "[$HPC $Hi]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|].
      iEpilogue "(HPC & Hi)". iApply wp_value. iApply "Hcont".
  Qed.

  (* --------------------------------------- REQSIZE ----------------------------------- *)
  (* This macro checks that the capability in r covers a memory range of size
     (i.e. e-b) greater than [minsize]. *)

  Definition reqsize_instrs r (minsize: Z) :=
    [getb r_t1 r;
     gete r_t2 r;
     sub_r_r r_t1 r_t2 r_t1;
     lt_z_r r_t1 minsize r_t1;
     move_r r_t2 PC;
     lea_z r_t2 4;
     jnz r_t2 r_t1;
     fail_end].

  Definition reqsize r minsize a : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(reqsize_instrs r minsize), a_i ↦ₐ w_i)%I.

  Lemma reqsize_spec r minsize a pc_p pc_b pc_e a_first a_last r_p r_b r_e r_a w1 w2 φ :
    isCorrectPC_range pc_p pc_b pc_e a_first a_last →
    contiguous_between a a_first a_last →

      ▷ reqsize r minsize a
    ∗ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e a_first
    ∗ ▷ r ↦ᵣ WCap r_p r_b r_e r_a
    ∗ ▷ r_t1 ↦ᵣ w1
    ∗ ▷ r_t2 ↦ᵣ w2
    ∗ ▷ (if (minsize <? (r_e - r_b)%a)%Z then
           (∃ w1 w2,
            reqsize r minsize a
            ∗ PC ↦ᵣ WCap pc_p pc_b pc_e a_last
            ∗ r ↦ᵣ WCap r_p r_b r_e r_a
            ∗ r_t1 ↦ᵣ w1
            ∗ r_t2 ↦ᵣ w2)
           -∗ WP Seq (Instr Executable) {{ φ }}
        else φ FailedV)
    ⊢
    WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont) "(>Hprog & >HPC & >Hr & >Hr1 & >Hr2 & Hcont)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength. simpl in *.
    iAssert (⌜r ≠ PC⌝)%I as %Hne.
    { iIntros (->). iApply (regname_dupl_false with "HPC Hr"). }
    destruct a as [| a l];[done|].
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont) as ->.
    assert (pc_p ≠ E).
    { eapply isCorrectPC_range_perm_non_E; eauto.
      generalize (contiguous_between_length _ _ _ Hcont). rewrite Hlength /=.
      clear; solve_addr. }
    (* getb r_t1 r *)
    destruct l as [| ? l];[done|].
    iPrologue "Hprog".
    iApply (wp_Get_success with "[$HPC $Hi $Hr $Hr1]");
      [apply decode_encode_instrW_inv|auto|iCorrectPC a_first a_last|iContiguous_next Hcont 0|auto..];
      simpl.
    iEpilogue "(HPC & Hi & Hr & Hr1)". iRename "Hi" into "Hprog_done".
    (* gete r_t2 r *)
    destruct l as [| ? l];[done|].
    iPrologue "Hprog".
    iApply (wp_Get_success with "[$HPC $Hi $Hr $Hr2]");
      [apply decode_encode_instrW_inv|auto|iCorrectPC a_first a_last|iContiguous_next Hcont 1|auto..];
      simpl.
    iEpilogue "(HPC & Hi & Hr & Hr2)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* sub_r_r r_t1 r_t2 r_t1 *)
    destruct l as [| ? l];[done|].
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_r_dst with "[$HPC $Hi $Hr2 $Hr1]");
      [apply decode_encode_instrW_inv|done|iContiguous_next Hcont 2|iCorrectPC a_first a_last|..];
      simpl.
    iEpilogue "(HPC & Hi & Hr2 & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lt_z_r r_t1 minsize r_t1 *)
    destruct l as [| ? l];[done|].
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_z_dst with "[$HPC $Hi $Hr1]");
      [apply decode_encode_instrW_inv|done|iContiguous_next Hcont 3|iCorrectPC a_first a_last|..];
      simpl.
    iEpilogue "(HPC & Hi & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move_r r_t2 PC *)
    destruct l as [| ? l];[done|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 4|auto..].
    iEpilogue "(HPC & Hi & Hr2)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea_z r_t2 4 *)
    destruct l as [| ? l];[done|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 5|try done..].
    { change 4%Z with (Z.of_nat (4%nat)).
      (* FIXME: a bit annoying to have to specify the index manually *)
      eapply (contiguous_between_middle_to_end _ _ _ 4); eauto. }
    iEpilogue "(HPC & Hi & Hr2)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* jnz r_t2 r_t1 *)
    destruct l as [| ? l];[done|].
    iPrologue "Hprog".
    destruct (minsize <? r_e - r_b)%Z eqn:Htest; simpl.
    { iApply (wp_jnz_success_jmp with "[$HPC $Hr2 $Hr1 $Hi]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|done|..].
      iEpilogue "(HPC & Hi & Hr2 & Hr1)". iApply "Hcont". iExists _,_.
      rewrite updatePcPerm_cap_non_E //. iFrame.
      iDestruct "Hprog_done" as "(?&?&?&?&?&?)". iFrame. }
    { iApply (wp_jnz_success_next with "[$HPC $Hr2 $Hr1 $Hi]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 6|..].
      iEpilogue "(HPC & Hi & Hr2 & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* fail_end *)
      iPrologue "Hprog".
      iApply (wp_fail with "[$HPC $Hi]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|..].
      iEpilogue "(HPC & Hi)". iApply wp_value. iApply "Hcont". }
  Qed.
End ReqPerm.
