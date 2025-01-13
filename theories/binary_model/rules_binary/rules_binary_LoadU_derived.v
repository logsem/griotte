From cap_machine Require Import rules_base.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac.
From cap_machine Require Import rules_binary_LoadU rules_LoadU_derived.

Section cap_lang_rules.
  Context `{cfgSG Σ, invG Σ}.
  Context `{MachineParameters}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : cap_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : cap_lang.val.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  (* loading from any offset *)
  Lemma step_loadU_success_any E K r1 r2 zoff pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a a' pc_a' :
    decodeInstrW w = LoadU r1 r2 (inl zoff) →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    isU p = true -> (a' <= e)%a →
    withinBounds ((p, g), b, a', a) = true →
    (pc_a + 1)%a = Some pc_a' →
    (a' + zoff)%a = Some a ->
    (zoff < 0)%Z ->
    nclose specN ⊆ E →

    spec_ctx ∗ ⤇ fill K (Instr Executable)
             ∗ ▷ PC ↣ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
             ∗ ▷ pc_a ↣ₐ w
             ∗ ▷ r1 ↣ᵣ w''
             ∗ ▷ r2 ↣ᵣ inr ((p,g),b,e,a')
             ∗ ▷ a ↣ₐ w'
    ={E}=∗
        ⤇ fill K (Instr NextI)
        ∗ PC ↣ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
        ∗ r1 ↣ᵣ w'
        ∗ pc_a ↣ₐ w
        ∗ r2 ↣ᵣ inr ((p,g),b,e,a')
        ∗ a ↣ₐ w'.
  Proof.
    iIntros (Hinstr Hvpc HU Hwb Hwb2 Hpca' Hincr Hlt Hnclose)
            "(#Hspec & Hj & >HPC & >Hi & >Hr1 & >Hr2 & >Ha)".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%) ]".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Ha") as "[Hmem %]"; auto.
    iMod (step_loadU with "[$Hmap $Hmem $Hspec $Hj]")
      as (regs' retv) "(Hj & #Hspec' & Hmem & Hmap)";[apply Hinstr|apply Hvpc|eauto..];simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite HU. simplify_map_eq.
      erewrite wb_implies_verify_access;eauto.
        by simplify_map_eq. }
    iDestruct "Hspec'" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iFrame.
       simplify_map_eq.
       erewrite  wb_implies_verify_access in H9;eauto. simplify_eq.
       simplify_map_eq.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite (insert_commute _ _ PC) // insert_insert insert_insert.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto. by iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto.
       all: try congruence.
       erewrite  wb_implies_verify_access in e4;eauto. simplify_eq.
       Unshelve. all:auto.
       destruct e6. congruence. destruct H6 as [?|[?|[?|[?|?]]]]; inv Hvpc; destruct H13 as [?|[?|?]].
       all: try congruence.
     }
  Qed.

  (* load from the top *)
  Lemma step_loadU_success E K r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a a' pc_a' :
    decodeInstrW w = LoadU r1 r2 (inl (-1)%Z) →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    isU p = true -> withinBounds ((p, g), b, e, a) = true →
    (pc_a + 1)%a = Some pc_a' →
    (a + 1)%a = Some a' ->
    nclose specN ⊆ E →

    spec_ctx ∗ ⤇ fill K (Instr Executable)
             ∗ ▷ PC ↣ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
             ∗ ▷ pc_a ↣ₐ w
             ∗ ▷ r1 ↣ᵣ w''
             ∗ ▷ r2 ↣ᵣ inr ((p,g),b,e,a')
             ∗ ▷ a ↣ₐ w'
    ={E}=∗
        ⤇ fill K (Instr NextI)
        ∗ PC ↣ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
        ∗ r1 ↣ᵣ w'
        ∗ pc_a ↣ₐ w
        ∗ r2 ↣ᵣ inr ((p,g),b,e,a')
        ∗ a ↣ₐ w'.
  Proof.
    iIntros (Hinstr Hvpc HU Hwb Hpca' Hincr Hnclose)
            "(#Hspec & Hj & >HPC & >Hi & >Hr1 & >Hr2 & >Ha)".
    iMod (step_loadU_success_any with "[$Hr1 $HPC $Hr2 $Hi $Ha $Hspec $Hj]");[..|iFrame];eauto.
    - apply withinBounds_le_addr in Hwb as [Hle Hlt]. solve_addr.
    - apply withinBounds_le_addr in Hwb as [Hle Hlt]. apply le_addr_withinBounds; solve_addr.
    - solve_addr.
    - lia.
  Qed.

  (* load into PC from reg *)
  Lemma step_loadU_success_reg_to_PC_any E K r1 r2 zoff pc_p pc_g pc_b pc_e pc_a w p g b e a a1 p' g' b' e' a' a'' :
    decodeInstrW w = LoadU PC r1 (inr r2)  →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (isU p' = false ∧ p' ≠ machine_base.E) → (* if an uninitialized capability is loaded into the PC, the instruction fails *)
    isU p = true -> (a1 <= e)%a →
    withinBounds ((p, g), b, a1, a) = true →
    (a' + 1)%a = Some a'' →
    (a1 + zoff)%a = Some a ->
    (zoff < 0)%Z ->
    nclose specN ⊆ E →

    spec_ctx ∗ ⤇ fill K (Instr Executable)
             ∗ ▷ PC ↣ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
             ∗ ▷ pc_a ↣ₐ w
             ∗ ▷ r1 ↣ᵣ inr ((p,g),b,e,a1)
             ∗ ▷ r2 ↣ᵣ inl zoff
             ∗ ▷ a ↣ₐ inr ((p',g'),b',e',a')
    ={E}=∗
        ⤇ fill K (Instr NextI)
        ∗ PC ↣ᵣ inr ((p',g'),b',e',a'')
        ∗ pc_a ↣ₐ w
        ∗ r1 ↣ᵣ inr ((p,g),b,e,a1)
        ∗ r2 ↣ᵣ inl zoff
        ∗ a ↣ₐ inr ((p',g'),b',e',a').
  Proof.
    iIntros (Hinstr Hvpc [HnU He] HU Hwb Hwb2 Hpca' Hincr Hlt Hnclose)
            "(#Hspec & Hj & >HPC & >Hi & >Hr1 & >Hr2 & >Ha)".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%) ]".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Ha") as "[Hmem %]"; auto.
    iMod (step_loadU with "[$Hmap $Hmem $Hspec $Hj]") as (regs' retv) "(Hj & #Hspec' & Hmem & Hmap)";[apply Hinstr |apply Hvpc|..];simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite HU. simplify_map_eq.
      erewrite wb_implies_verify_access;eauto.
        by simplify_map_eq. }
    iDestruct "Hspec'" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iFrame.
       simplify_map_eq.
       erewrite  wb_implies_verify_access in H9;eauto. simplify_eq.
       simplify_map_eq.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert insert_insert.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto. by iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; first congruence.
       all: erewrite  wb_implies_verify_access in e4;eauto.
       * by exfalso.
       * simplify_map_eq. eapply (incrementPC_None_inv _ p' _ _ _ a') in e6.
         destruct e6. congruence. 2: by simplify_map_eq.
         destruct H6 as [?|[?|[?|[?|?]]]];subst; inv HnU. done.
       Unshelve. all:auto.
     }
  Qed.

  (* load into PC from reg *)
  Lemma step_loadU_success_reg_to_PC E K r1 r2 pc_p pc_g pc_b pc_e pc_a w p g b e a a1 p' g' b' e' a' a'' :
    decodeInstrW w = LoadU PC r1 (inr r2)  →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (isU p' = false ∧ p' ≠ machine_base.E) →
    isU p = true -> withinBounds ((p, g), b, e, a) = true →
    (a' + 1)%a = Some a'' →
    (a + 1)%a = Some a1 ->
    nclose specN ⊆ E →

    spec_ctx ∗ ⤇ fill K (Instr Executable)
             ∗ ▷ PC ↣ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
             ∗ ▷ pc_a ↣ₐ w
             ∗ ▷ r1 ↣ᵣ inr ((p,g),b,e,a1)
             ∗ ▷ r2 ↣ᵣ inl (-1)%Z
             ∗ ▷ a ↣ₐ inr ((p',g'),b',e',a')
    ={E}=∗
        ⤇ fill K (Instr NextI)
        ∗ PC ↣ᵣ inr ((p',g'),b',e',a'')
        ∗ pc_a ↣ₐ w
        ∗ r1 ↣ᵣ inr ((p,g),b,e,a1)
        ∗ r2 ↣ᵣ inl (-1)%Z
        ∗ a ↣ₐ inr ((p',g'),b',e',a').
  Proof.
    iIntros (Hinstr Hvpc Hnu HU Hwb Hpca' Hincr Hnclose)
            "(#Hspec & Hj & >HPC & >Hi & >Hr1 & >Hr2 & >Ha)".
    iMod (step_loadU_success_reg_to_PC_any with "[$Hr1 $HPC $Hr2 $Hi $Ha $Hspec $Hj]");[..|iFrame];eauto.
    - apply withinBounds_le_addr in Hwb as [Hle Hlt]. solve_addr.
    - apply withinBounds_le_addr in Hwb as [Hle Hlt]. apply le_addr_withinBounds; solve_addr.
    - solve_addr.
    - lia.
  Qed.

End cap_lang_rules.
