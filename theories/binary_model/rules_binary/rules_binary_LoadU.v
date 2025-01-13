From cap_machine Require Export rules_LoadU rules_binary_base.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac.


Section cap_lang_spec_rules.
  Context `{cfgSG Σ, MachineParameters, invG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : cap_lang.state.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  Ltac option_locate_r_once_reg r reg :=
  match goal with
  | H : r !! reg = Some ?w |- _ => let Htmp := fresh in
                                rename H into Htmp ;
                                let Ha := fresh "H" r reg in
                                pose proof (regs_lookup_eq _ _ _ Htmp) as Ha; clear Htmp
  end.

  Ltac iFailStep_alt fail_type :=
    iMod (exprspec_mapsto_update _ _ (fill _ (Instr Failed)) with "Hown Hj") as "[Hown Hj]";
    iMod ("Hclose" with "[Hown]") as "_";
    [iNext;iExists _,_;iFrame;iPureIntro;eapply rtc_r;eauto;prim_step_from_exec|];
    try (iExists (FailedV),_; iFrame;iModIntro;iFailCore fail_type).

  Lemma step_loadU Ep K
     pc_p pc_g pc_b pc_e pc_a
     rdst rsrc offs w mem regs :
   decodeInstrW w = LoadU rdst rsrc offs →
   isCorrectPC (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
   regs !! PC = Some (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
   regs_of (LoadU rdst rsrc offs) ⊆ dom _ regs →
   mem !! pc_a = Some w →
   match regs !! rsrc with
   | None => True
   | Some (inl _) => True
   | Some (inr (p, g, b, e, a)) =>
     if isU p then
       match z_of_argument regs offs with
       | None => True
       | Some zoffs => match verify_access (LoadU_access b e a zoffs) with
                      | None => True
                      | Some a' => match mem !! a' with
                                  | None => False
                                  | Some w => True
                                  end
                      end
       end
     else True
   end ->

   nclose specN ⊆ Ep →

   spec_ctx ∗ ⤇ fill K (Instr Executable) ∗ (▷ [∗ map] a↦w ∈ mem, a ↣ₐ w) ∗ (▷ [∗ map] k↦y ∈ regs, k ↣ᵣ y)
   ={Ep}=∗ ∃ retv regs', ⤇ fill K (of_val retv) ∗ ⌜ LoadU_spec regs rdst rsrc offs regs' mem retv ⌝ ∗ ([∗ map] a↦w ∈ mem, a ↣ₐ w)∗ ([∗ map] k↦y ∈ regs', k ↣ᵣ y).
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaLoad Hnclose) "(#Hinv & Hj & >Hmem & >Hmap)".
    iDestruct "Hinv" as (ρ) "Hinv". rewrite /spec_inv.
    iInv specN as ">Hinv'" "Hclose". iDestruct "Hinv'" as (e [σr σm]) "[Hown %] /=".
    iDestruct (regspec_heap_valid_inclSepM with "Hown Hmap") as %Hregs.
    iDestruct (spec_expr_valid with "[$Hown $Hj]") as %Heq; subst e.

    (* Derive necessary register values in r *)
    pose proof (lookup_weaken _ _ _ _ HPC Hregs).
    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
    feed destruct (Hri rsrc) as [rsrcv [Hrsrc' Hrsrc]]. by set_solver+.
    feed destruct (Hri rdst) as [rdstv [Hrdst' _]]. by set_solver+.
    pose proof (regs_lookup_eq _ _ _ Hrsrc') as Hrsrc''.
    pose proof (regs_lookup_eq _ _ _ Hrdst') as Hrdst''.
    (* Derive the PC in memory *)
    iDestruct (memspec_heap_valid_inSepM _ _ _ _ pc_a with "Hown Hmem") as %Hma; eauto.

    specialize (normal_always_step (σr,σm)) as [c [ σ2 Hstep]].
    eapply step_exec_inv in Hstep; eauto. simpl in H3,Hrsrc,Hma.

    assert (Hstep':=Hstep).

    option_locate_r_once_reg σr rsrc.
    rewrite /exec in Hstep. simpl in Hstep. rewrite Hσrrsrc in Hstep.

    destruct rsrcv as [| [[[[p g] b] e] a] ].
    { inv Hstep. iFailStep_alt LoadU_fail_const. }

    destruct (isU p) eqn:HisU; cycle 1.
    { inv Hstep. iFailStep_alt LoadU_fail_perm. }

    assert (Hzofargeq: z_of_argument σr offs = z_of_argument regs offs).
    { rewrite /z_of_argument; destruct offs; auto.
      feed destruct (Hri r) as [? [?]]. by set_solver+.
      rewrite H5 H4; auto. }
    rewrite Hzofargeq in Hstep.

     destruct (z_of_argument regs offs) as [zoffs|] eqn:Hoffs; cycle 1.
     { inv Hstep. iFailStep_alt LoadU_fail_offs_arg.
       rewrite /= Hσrrsrc HisU Hzofargeq //. }

     destruct (verify_access (LoadU_access b e a zoffs)) as [a'|] eqn:Hverify; cycle 1.
     { rewrite /verify_access in Hverify. rewrite Hverify in Hstep.
       inv Hstep. iFailStep_alt LoadU_fail_verify_access. simplify_map_eq.
       rewrite /= Hσrrsrc HisU Hverify //. }

     simpl in Hstep. rewrite Hrsrc' HisU Hverify in HaLoad.
     rewrite /MemLocate in Hstep. destruct (mem !! a') as [wa|] eqn:Ha'; cycle 1.
     { inv HaLoad. }
     iDestruct (memspec_v_implies_m_v mem (σr,σm) _ b e a' with "Hmem Hown" ) as %Hma' ; eauto.
     rewrite /verify_access in Hverify. rewrite /= /MemLocate in Hma'.
     rewrite Hverify Hma' in Hstep.
     destruct (incrementPC (<[rdst:=wa]> regs)) eqn:Hincr; cycle 1.
     { assert _ as Hincr' by (eapply (incrementPC_overflow_mono (<[rdst:=wa]> regs) (<[rdst:=wa]> σr) _ _ _)).
       rewrite incrementPC_fail_updatePC in Hstep; eauto.
       inversion Hstep. subst c σ2. simpl.
       iMod (exprspec_mapsto_update _ _ (fill K (Instr Failed)) with "Hown Hj") as "[Hown Hj]".
       iMod ((regspec_heap_update_inSepM _ _ _ rdst) with "Hown Hmap") as "[Hown Hmap]"; eauto.
       (* iFailStep_alt LoadU_fail_incrementPC. *)
       iMod (exprspec_mapsto_update _ _ (fill _ (Instr Failed)) with "Hown Hj") as "[Hown Hj]".
       iMod ("Hclose" with "[Hown]") as "_";
         [iNext;iExists _,_;iFrame;iPureIntro;eapply rtc_r;eauto|];
         try (iExists (FailedV),_; iFrame;iModIntro;iFailCore LoadU_fail_incrementPC).
       simpl. exists [];eapply step_atomic with (t1:=[]) (t2:=[]);eauto;
       econstructor;eauto;constructor.
       eapply step_exec_instr with (c:=(Failed, (<[rdst:=wa]> σr, σm)));rewrite /RegLocate /MemLocate.
       rewrite H3;eauto. rewrite H3;eauto. rewrite Hma Hinstr;eauto. auto.
     }

     destruct (incrementPC_success_updatePC _ σm _ Hincr) as (p1 & g1 & b1 & e1 & a1 & a_pc1 & HPC'' & Ha_pc' & HuPC & -> & ?).
     eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono.
     rewrite HuPC in Hstep; clear HuPC; inversion Hstep; clear Hstep; subst c σ2. cbn.
     iFrame.
     iMod ((regspec_heap_update_inSepM _ _ _ rdst wa) with "Hown Hmap") as "[Hown Hmap]"; eauto.
     iMod ((regspec_heap_update_inSepM _ _ _ PC (inr (p1, g1, b1, e1, a_pc1))) with "Hown Hmap") as "[Hown Hmap]"; eauto.
     iMod (exprspec_mapsto_update _ _ (fill K (Instr NextI)) with "Hown Hj") as "[Hown Hj]".
     iExists NextIV,_. iFrame.
     iMod ("Hclose" with "[Hown]") as "_".
     { iNext. iExists _,_;iFrame. iPureIntro. eapply rtc_r;eauto.
       exists [];eapply step_atomic with (t1:=[]) (t2:=[]);eauto;
         econstructor;eauto;constructor.
       eapply step_exec_instr with (c:=(NextI, (<[PC:=inr (p1, g1, b1, e1, a_pc1)]> (<[rdst:=wa]> σr), σm)));rewrite /RegLocate /MemLocate.
       rewrite H3;eauto. rewrite H3;eauto. rewrite Hma Hinstr;eauto. auto. }
     iModIntro. iPureIntro. eapply LoadU_spec_success; eauto.
     Unshelve. all: eauto.
     { destruct (reg_eq_dec PC rdst).
       - subst rdst. rewrite lookup_insert. eauto.
       - rewrite lookup_insert_ne; eauto. }
     { eapply insert_mono; eauto. }
   Qed.

End cap_lang_spec_rules.

