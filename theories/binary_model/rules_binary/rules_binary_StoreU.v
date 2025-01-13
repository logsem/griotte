From cap_machine Require Export rules_StoreU rules_binary_base.
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

  Ltac iFailStep_alt fail_type :=
    iMod (exprspec_mapsto_update _ _ (fill _ (Instr Failed)) with "Hown Hj") as "[Hown Hj]";
    iMod ("Hclose" with "[Hown]") as "_";
    [iNext;iExists _,_;iFrame;iPureIntro;eapply rtc_r;eauto;prim_step_from_exec|];
    try (iExists (FailedV),_,_; iFrame;iModIntro;iFailCore fail_type).

  Lemma step_storeU Ep K
     pc_p pc_g pc_b pc_e pc_a
     rdst rsrc offs w wsrc mem regs :
   decodeInstrW w = StoreU rdst offs rsrc →
   isCorrectPC (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
   regs !! PC = Some (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
   regs_of (StoreU rdst offs rsrc) ⊆ dom _ regs →
   mem !! pc_a = Some w →
   word_of_argument regs rsrc = Some wsrc ->
   match regs !! rdst with
   | None => True
   | Some (inl _) => True
   | Some (inr (p, g, b, e, a)) =>
     match z_of_argument regs offs with
       | None => True
       | Some zoffs => match verify_access (StoreU_access b e a zoffs) with
                      | None => True
                      | Some a' => if isU p && canStoreU p a' wsrc then
                                    match mem !! a' with
                                    | None => False
                                    | Some w => True
                                    end
                                  else True
                      end
       end
   end ->

   nclose specN ⊆ Ep →

   spec_ctx ∗ ⤇ fill K (Instr Executable) ∗ (▷ [∗ map] a↦w ∈ mem, a ↣ₐ w) ∗ (▷ [∗ map] k↦y ∈ regs, k ↣ᵣ y)
   ={Ep}=∗ ∃ retv regs' mem', ⤇ fill K (of_val retv) ∗ ⌜ StoreU_spec regs rdst offs rsrc regs' mem mem' retv ⌝ ∗ ([∗ map] a↦w ∈ mem', a ↣ₐ w)∗ ([∗ map] k↦y ∈ regs', k ↣ᵣ y).
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc Hwsrc HaStore Hnclose) "(#Hinv & Hj & >Hmem & >Hmap)".
    iDestruct "Hinv" as (ρ) "Hinv". rewrite /spec_inv.
    iInv specN as ">Hinv'" "Hclose". iDestruct "Hinv'" as (e [σr σm]) "[Hown %] /=".
    iDestruct (regspec_heap_valid_inclSepM with "Hown Hmap") as %Hregs.
    iDestruct (spec_expr_valid with "[$Hown $Hj]") as %Heq; subst e.

    (* Derive necessary register values in r *)
    pose proof (lookup_weaken _ _ _ _ HPC Hregs).
    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
    feed destruct (Hri rdst) as [rdstv [Hrdst' Hrdst'']]. by set_solver+.
    pose proof (regs_lookup_eq _ _ _ Hrdst') as Hrdst'''.
    (* Derive the PC in memory *)
    iDestruct (memspec_heap_valid_inSepM _ _ _ _ pc_a with "Hown Hmem") as %Hma; eauto.
    specialize (normal_always_step (σr,σm)) as [c [ σ2 Hstep]].
    eapply step_exec_inv in Hstep; eauto.

    simpl in Hrdst'', Hma. option_locate_mr σm σr.
    assert (Hstep':=Hstep). rewrite /exec /reg in Hstep.
    assert ((σr, σm).1 = σr) as Heq;auto. rewrite Heq in Hstep. clear Heq.
    rewrite Hσrrdst in Hstep.

    destruct rdstv as [zdst| [[[[p g] b] e] a] ].
    { inv Hstep. iFailStep_alt StoreU_fail_const. }

     (* destruct (isU p) eqn:HisU; cycle 1. *)
     (* { simpl in Hstep. inv Hstep. iFailWP "Hφ" StoreU_fail_perm1. } *)

     assert (Hwsrc': match rsrc with
                     | inl n => inl n
                     | inr rsrc =>
                       match reg (σr, σm) !! rsrc with
                       | Some w => w
                       | None => inl 0%Z
                       end
                     end = wsrc).
     { destruct rsrc; simpl in Hwsrc; inv Hwsrc; auto.
       simpl. feed destruct (Hri r) as [aa [HA HB]]. by set_solver+.
       rewrite HB; congruence. }
     rewrite Hwsrc' in Hstep.

     (* destruct (canStoreU p a wsrc) eqn:HcanStoreU; cycle 1. *)
     (* { simpl in Hstep. inversion Hstep. *)
     (*   iFailWP "Hφ" StoreU_fail_perm2. } *)

     assert (Hzofargeq: z_of_argument σr offs = z_of_argument regs offs).
     { rewrite /z_of_argument; destruct offs; auto.
       feed destruct (Hri r) as [? [?]]. by set_solver+.
       rewrite H4 H5; auto. }
     rewrite Hzofargeq in Hstep.

     Local Opaque verify_access.
     Local Opaque exec.
     simpl in Hstep. destruct (z_of_argument regs offs) as [zoffs|] eqn:Hoffs; cycle 1.
     { inv Hstep. iFailStep_alt StoreU_fail_offs_arg. }

     destruct (verify_access (StoreU_access b e a zoffs)) as [a'|] eqn:Hverify; cycle 1.
     { inv Hstep. iFailStep_alt StoreU_fail_verify_access. }

     destruct (isU p) eqn:HisU; cycle 1.
     { simpl in Hstep. inv Hstep. iFailStep_alt StoreU_fail_perm1. }

     destruct (canStoreU p a' wsrc) eqn:HcanStoreU; cycle 1.
     { simpl in Hstep. inv Hstep. iFailStep_alt StoreU_fail_perm2. }

     rewrite Hrdst' HisU Hverify HcanStoreU /= in HaStore.
     destruct (mem !! a') as [wa|]eqn:Ha; try (inv HaStore; fail).

     destruct (addr_eq_dec a a').
     { subst a'. destruct (a + 1)%a as [a'|] eqn:Hap1; cycle 1.
       { inv Hstep. iFailStep_alt StoreU_fail_incrPC1. }

       iMod ((memspec_heap_update_inSepM _ _ _ a) with "Hown Hmem") as "[Hown Hmem]"; eauto.

       destruct (incrementPC (<[rdst:=inr (p, g, b, e, a')]> regs)) eqn:Hincr; cycle 1.
       { assert _ as Hincr' by (eapply (incrementPC_overflow_mono (<[rdst:=_]> regs) (<[rdst:=_]> σr) Hincr _ _)).
         rewrite incrementPC_fail_updatePC in Hstep; eauto.
         inv Hstep. simpl.
         iMod (exprspec_mapsto_update _ _ (fill K (Instr Failed)) with "Hown Hj") as "[Hown Hj]".
         iMod ((regspec_heap_update_inSepM _ _ _ rdst) with "Hown Hmap") as "[Hown Hmap]"; eauto.
         iFailStep_alt StoreU_fail_incrPC2. }

       destruct (incrementPC_success_updatePC _ σm _ Hincr) as (p1 & g1 & b1 & e1 & a1 & a_pc1 & HPC'' & Ha_pc' & HuPC & -> & ?).
       eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono.
       instantiate (1 := <[a:=wsrc]> σm) in HuPC.
       rewrite HuPC in Hstep. inversion Hstep; clear Hstep; subst c σ2. cbn.
       iMod (exprspec_mapsto_update _ _ (fill K (Instr NextI)) with "Hown Hj") as "[Hown Hj]".
       iMod ((regspec_heap_update_inSepM _ _ _ rdst) with "Hown Hmap") as "[Hown Hmap]"; eauto.
       iMod ((regspec_heap_update_inSepM _ _ _ PC) with "Hown Hmap") as "[Hown Hmap]"; eauto.
       rewrite <- Hwsrc'. iExists (NextIV),_,_. iFrame.
       iMod ("Hclose" with "[Hown]") as "_".
       { iNext. iExists _,_;iFrame. iPureIntro. eapply rtc_r;eauto.
         apply verify_access_spec in Hverify as (? & ? & ? & ?). simpl. rewrite Hwsrc'.
         prim_step_from_exec. }
       iModIntro. iPureIntro. apply verify_access_spec in Hverify as (? & ? & ? & ?). econstructor; eauto.
       - repeat split;eauto.
       - rewrite Hwsrc'. auto.
       - destruct (addr_eq_dec a a); try congruence.
         rewrite Hap1. auto. }

     iMod ((memspec_heap_update_inSepM _ _ _ a') with "Hown Hmem") as "[Hown Hmem]"; eauto.

     destruct (incrementPC regs) eqn:Hincr; cycle 1.
     { assert _ as Hincr' by (eapply (incrementPC_overflow_mono regs σr Hincr _ _)).
       rewrite incrementPC_fail_updatePC in Hstep; eauto.
       inv Hstep. simpl.
       iFailStep_alt StoreU_fail_incrPC3. }

     destruct (incrementPC_success_updatePC regs (<[a':=wsrc]> σm) _ Hincr) as (p1 & g1 & b1 & e1 & a1 & a_pc1 & HPC'' & Ha_pc' & HuPC & -> & ?).
     eapply updatePC_success_incl in HuPC; eauto.
     instantiate (1 := <[a':=wsrc]> σm) in HuPC.
     rewrite HuPC in Hstep.
     inversion Hstep; clear Hstep; subst c σ2. cbn.
     iMod ((regspec_heap_update_inSepM _ _ _ PC) with "Hown Hmap") as "[Hown Hmap]"; eauto.
     iMod (exprspec_mapsto_update _ _ (fill K (Instr NextI)) with "Hown Hj") as "[Hown Hj]".
     rewrite <- Hwsrc'. iExists (NextIV),_,_. iFrame.
     iMod ("Hclose" with "[Hown]") as "_".
     { iNext. iExists _,_;iFrame. iPureIntro. eapply rtc_r;eauto.
       apply verify_access_spec in Hverify as (? & ? & ? & ?). simpl. rewrite Hwsrc'.
       prim_step_from_exec. }
     iPureIntro. apply verify_access_spec in Hverify as (? & ? & ? & ?). econstructor; eauto.
     { repeat split;eauto. }
     { rewrite Hwsrc'. reflexivity. }
     { destruct (addr_eq_dec a a'); try congruence; auto. }

     Unshelve. all: eauto.
     { destruct (reg_eq_dec PC rdst).
       - subst rdst. rewrite lookup_insert. eauto.
       - rewrite lookup_insert_ne; eauto. }
     { eapply insert_mono; eauto. }
   Qed.


  Lemma step_storeU_alt Ep K
     pc_p pc_g pc_b pc_e pc_a
     rdst rsrc offs w mem regs :
   decodeInstrW w = StoreU rdst offs rsrc →
   isCorrectPC (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
   regs !! PC = Some (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
   regs_of (StoreU rdst offs rsrc) ⊆ dom _ regs →
   mem !! pc_a = Some w →
   allow_storeU_map_or_true rdst rsrc offs regs mem  ->

   nclose specN ⊆ Ep →

   spec_ctx ∗ ⤇ fill K (Instr Executable) ∗ (▷ [∗ map] a↦w ∈ mem, a ↣ₐ w) ∗ (▷ [∗ map] k↦y ∈ regs, k ↣ᵣ y)
   ={Ep}=∗ ∃ retv regs' mem', ⤇ fill K (of_val retv) ∗ ⌜ StoreU_spec regs rdst offs rsrc regs' mem mem' retv ⌝ ∗ ([∗ map] a↦w ∈ mem', a ↣ₐ w)∗ ([∗ map] k↦y ∈ regs', k ↣ᵣ y).
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaStore Hnclose) "(#Hinv & Hj & >Hmem & >Hmap)".
    apply allow_storeU_map_or_true_match in HaStore as (wsrc & Hwsrc & HaStore).
    iApply (step_storeU with "[$Hmem $Hmap $Hj]");eauto.
  Qed.

End cap_lang_spec_rules.

