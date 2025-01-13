From cap_machine Require Import rules_base.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac.
From cap_machine.binary_model.rules_binary Require Import rules_binary_StoreU.
From cap_machine.rules Require Import rules_StoreU_derived.

From cap_machine.binary_model.rules_binary Require Import rules_binary_AddSubLt.

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

  (* TODO: move the addsublt to its file *)
  Lemma step_add_sub_lt_success_r_dst E K dst pc_p pc_g pc_b pc_e pc_a w ins r1 n1 n2 pc_a' :
    decodeInstrW w = ins →
    is_AddSubLt ins dst (inr r1) (inr dst) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (inr (pc_p,pc_g,pc_b,pc_e,pc_a)) ->
    nclose specN ⊆ E →

    spec_ctx ∗ ⤇ fill K (Instr Executable)
             ∗ PC ↣ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
             ∗ pc_a ↣ₐ w
             ∗ r1 ↣ᵣ inl n1
             ∗ dst ↣ᵣ inl n2
    ={E}=∗
        ⤇ fill K (Instr NextI)
        ∗ PC ↣ᵣ inr (pc_p,pc_g,pc_b,pc_e,pc_a')
        ∗ pc_a ↣ₐ w
        ∗ r1 ↣ᵣ inl n1
        ∗ dst ↣ᵣ inl (denote ins n1 n2).
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hvpc Hnclose) "(#Hspec & Hj & HPC & Hpc_a & Hr2 & Hdst)".
    iDestruct (map_of_regs_3 with "HPC Hr2 Hdst") as "[Hmap (%&%&%)]".
    iMod (step_AddSubLt with "[$Hmap Hpc_a $Hspec $Hj]") as (regs' retv HSpec') "(Hj & Hpc_a & Hmap)"; eauto; simplify_map_eq; eauto.
    by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.

    destruct HSpec' as [| * Hfail].
    { (* Success *)
      iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r1 dst) //
              (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. done. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. inversion e1. congruence.
      inv Hvpc. destruct H5 as [? | [? | [? | [? | ?]]]]; destruct H12 as [? | [? | ?]]; congruence.
    }
  Qed.

  (* store and increment *)
  Lemma step_storeU_success_0_reg E K pc_p pc_g pc_b pc_e pc_a pc_a' w dst src w'
         p g b e a a' w'' :
    decodeInstrW w = StoreU dst (inl 0%Z) (inr src) →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    isU p  = true -> canStoreU p a w'' = true ->
    withinBounds ((p, g), b, e, a) = true ->
    (a + 1)%a = Some a' ->
    nclose specN ⊆ E →

    spec_ctx ∗ ⤇ fill K (Instr Executable)
    ∗ ▷ PC ↣ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
    ∗ ▷ pc_a ↣ₐ w
    ∗ ▷ src ↣ᵣ w''
    ∗ ▷ dst ↣ᵣ inr ((p,g),b,e,a)
    ∗ ▷ a ↣ₐ w'
    ={E}=∗
        ⤇ fill K (Instr NextI)
        ∗ PC ↣ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
        ∗ pc_a ↣ₐ w
        ∗ src ↣ᵣ w''
        ∗ dst ↣ᵣ inr ((p,g),b,e,a')
        ∗ a ↣ₐ w''.
  Proof.
    iIntros (Hinstr Hvpc Hpca' HU HstoreU Hwb Ha' Hnclose)
            "(#Hspec & Hj & >HPC & >Hi & >Hsrc & >Hdst & >Hsrca)".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]".

    iMod (step_storeU _ _ pc_p with "[$Hmap $Hmem $Hspec $Hj]") as (retv regs' mem') "(Hj & Hspec' & Hmem & Hmap)"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite addr_add_0. apply andb_true_iff in Hwb as [Hle%Z.leb_le Hlt%Z.ltb_lt].
      rewrite !decide_True//;[|clear;solve_addr].
      rewrite HU HstoreU /=. simplify_map_eq. auto. }
    iDestruct "Hspec'" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iFrame. destruct H9 as (?&?&?&?&?&?).
       simplify_map_eq. rewrite addr_add_0 in H8. simplify_eq.
       rewrite decide_True in H12;[|clear;solve_addr].
       rewrite insert_commute // insert_insert.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       destruct (addr_eq_dec a'0 a'0);[|contradiction].
       incrementPC_inv.
       simplify_map_eq.
       rewrite (insert_commute _ _ PC) // insert_insert.
       rewrite (insert_commute _ _ src) // insert_insert.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hsrc Hdst] ]"; eauto. iFrame. done. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto.
       all: try congruence.
       erewrite wb_implies_verify_access in e4; eauto. simplify_eq. congruence.
       erewrite wb_implies_verify_access in e4; eauto. simplify_eq.
       destruct e8. congruence. destruct H6 as [?|[?|[?|[?|?]]]]; inv Hvpc; destruct H13 as [?|[?|?]].
       all: try congruence.
       destruct e7. congruence. destruct H6 as [?|[?|[?|[?|?]]]]; inv Hvpc; destruct H13 as [?|[?|?]].
       all: try congruence.
       Unshelve. all:auto.
     }
  Qed.

  Lemma step_storeU_failure_0_reg E K pc_p pc_g pc_b pc_e pc_a pc_a' w dst src w'
         p g b e a a' w'' :
    decodeInstrW w = StoreU dst (inl 0%Z) (inr src) →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    isU p  = true -> canStoreU p a w'' = false ->
    withinBounds ((p, g), b, e, a) = true ->
    (a + 1)%a = Some a' ->
    nclose specN ⊆ E →

    spec_ctx ∗ ⤇ fill K (Instr Executable)
             ∗ ▷ PC ↣ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
             ∗ ▷ pc_a ↣ₐ w
             ∗ ▷ src ↣ᵣ w''
             ∗ ▷ dst ↣ᵣ inr ((p,g),b,e,a)
             ∗ ▷ a ↣ₐ w'
    ={E}=∗
        ⤇ fill K (Instr Failed).
  Proof.
      iIntros (Hinstr Hvpc Hpca' HU HstoreU Hwb Ha' Hnclose)
             "(#Hspec & Hj & >HPC & >Hi & >Hsrc & >Hdst & >Hsrca)".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iMod (step_storeU _ _ pc_p with "[$Hmap $Hmem $Hj $Hspec]") as (retv regs' mem') "(Hj & Hspec' & Hmem & Hmap)"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite addr_add_0. apply andb_true_iff in Hwb as [Hle%Z.leb_le Hlt%Z.ltb_lt].
      rewrite !decide_True//;[|clear;solve_addr].
      rewrite HU HstoreU /=. simplify_map_eq. auto. }
    iDestruct "Hspec'" as %Hspec.

    destruct Hspec as [ | * Hfail ].
    { (* Success (contradiction) *)
      destruct H9 as (?&?&?&?&?&?).
      simplify_map_eq. rewrite addr_add_0 in H8. simplify_eq.
       rewrite decide_True in H12;[|clear;solve_addr].
       rewrite insert_commute // insert_insert.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       destruct (addr_eq_dec a'0 a'0);[|contradiction].
       incrementPC_inv. simplify_map_eq. congruence. }
    { (* Failure (contradiction) *) iFrame. done. }
  Qed.

  (* store and increment from and to the same register *)
  Lemma step_storeU_success_0_reg_same E K pc_p pc_g pc_b pc_e pc_a pc_a' w dst w'
         p g b e a a' :
    decodeInstrW w = StoreU dst (inl 0%Z) (inr dst) →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    isU p  = true -> canStoreU p a (inr (p, g, b, e, a)) = true ->
    withinBounds ((p, g), b, e, a) = true ->
    (a + 1)%a = Some a' ->
    nclose specN ⊆ E →

    spec_ctx ∗ ⤇ fill K (Instr Executable)
             ∗ ▷ PC ↣ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
             ∗ ▷ pc_a ↣ₐ w
             ∗ ▷ dst ↣ᵣ inr ((p,g),b,e,a)
             ∗ ▷ a ↣ₐ w'
    ={E}=∗
        ⤇ fill K (Instr NextI)
        ∗ PC ↣ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
        ∗ pc_a ↣ₐ w
        ∗ dst ↣ᵣ inr ((p,g),b,e,a')
        ∗ a ↣ₐ inr ((p,g),b,e,a).
  Proof.
    iIntros (Hinstr Hvpc Hpca' HU HstoreU Hwb Ha' Hnclose)
             "(#Hspec & Hj & >HPC & >Hi & >Hdst & >Hsrca)".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iMod (step_storeU _ _ pc_p with "[$Hmap $Hmem $Hj $Hspec]") as (retv reg' mem') "(Hj & Hspec' & Hmem & Hmap)"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite addr_add_0. apply andb_true_iff in Hwb as [Hle%Z.leb_le Hlt%Z.ltb_lt].
      rewrite !decide_True//;[|clear;solve_addr].
      unfold canStoreU. rewrite HU HstoreU /=. simplify_map_eq. auto. }
    iDestruct "Hspec'" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iFrame. destruct H7 as (?&?&?&?&?&?).
       simplify_map_eq. rewrite addr_add_0 in H6;simplify_eq. simplify_map_eq.
       rewrite insert_commute // insert_insert.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       destruct (addr_eq_dec a'0 a'0);[|contradiction].
       incrementPC_inv.
       simplify_map_eq.
       rewrite (insert_commute _ _ PC) // insert_insert.
       rewrite insert_insert.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hdst]"; eauto. iFrame. done. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto.
       all: try congruence.
       erewrite wb_implies_verify_access in e4; eauto. simplify_eq. congruence.
       erewrite wb_implies_verify_access in e4; eauto. simplify_eq.
       destruct e8. congruence. destruct H4 as [?|[?|[?|[?|?]]]]; inv Hvpc;destruct H11 as [?|[?|?]].
       all: try congruence.
       destruct e7. congruence. destruct H4 as [?|[?|[?|[?|?]]]]; inv Hvpc; destruct H11 as [?|[?|?]].
       all: try congruence.
       Unshelve. all:auto.
     }
  Qed.

  Lemma step_storeU_success_0_z E K pc_p pc_g pc_b pc_e pc_a pc_a' w dst z w'
         p g b e a a' :
    decodeInstrW w = StoreU dst (inl 0%Z) (inl z) →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    isU p  = true ->
    withinBounds ((p, g), b, e, a) = true ->
    (a + 1)%a = Some a' ->
    nclose specN ⊆ E →

    spec_ctx ∗ ⤇ fill K (Instr Executable)
             ∗ ▷ PC ↣ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
             ∗ ▷ pc_a ↣ₐ w
             ∗ ▷ dst ↣ᵣ inr ((p,g),b,e,a)
             ∗ ▷ a ↣ₐ w'
    ={E}=∗
        ⤇ fill K (Instr NextI)
        ∗ PC ↣ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
        ∗ pc_a ↣ₐ w
        ∗ dst ↣ᵣ inr ((p,g),b,e,a')
        ∗ a ↣ₐ (inl z).
  Proof.
    iIntros (Hinstr Hvpc Hpca' HU Hwb Ha' Hnclose)
             "(#Hspec & Hj & >HPC & >Hi & >Hdst & >Hsrca)".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iMod (step_storeU _ _ pc_p with "[$Hmap $Hmem $Hspec $Hj]") as (retv regs' mem') "(Hj & Hspec' & Hmem & Hmap)"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite HU. erewrite wb_implies_verify_access; eauto.
      by simplify_map_eq. }
    iDestruct "Hspec'" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iFrame. destruct H7 as (?&?&?&?&?&?).
       simplify_map_eq. rewrite addr_add_0 in H6;simplify_eq.
       rewrite insert_commute // insert_insert.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       destruct (addr_eq_dec a'0 a'0);[|contradiction].
       incrementPC_inv.
       simplify_map_eq.
       rewrite (insert_commute _ _ PC) // insert_insert. rewrite insert_insert.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hdst]"; eauto. iFrame. done. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto.
       all: try congruence.
       erewrite wb_implies_verify_access in e4; eauto. simplify_eq.
       Unshelve. all:auto.
       destruct e8. congruence. destruct H4 as [?|[?|[?|[?|?]]]]; inv Hvpc; destruct H11 as [?|[?|?]].
       all: try congruence.
       destruct e7. congruence. destruct H4 as [?|[?|[?|[?|?]]]]; inv Hvpc; destruct H11 as [?|[?|?]].
       all: try congruence.
     }
  Qed.

End cap_lang_rules.
