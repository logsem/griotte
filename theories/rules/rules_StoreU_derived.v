From cap_machine Require Import rules_base.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac.
From cap_machine.rules Require Import rules_StoreU.

Section cap_lang_rules.
  Context `{memG Σ, regG Σ}.
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

  Lemma wb_implies_verify_access p g:
    ∀ b e a,
      withinBounds ((p, g), b, e, a) = true ->
      match (a + 0)%a with
        | Some a' =>
            if Addr_le_dec b a'
            then if Addr_le_dec a' a then if Addr_lt_dec a e then Some a' else None else None
            else None
        | None => None
        end = Some a.
  Proof.
    intros b e a Hwb.
    rewrite /= addr_add_0 /=.
    apply withinBounds_le_addr in Hwb as [Hle Hlt].
    destruct (Addr_le_dec b a);[|contradiction].
    destruct (Addr_le_dec a a);[|solve_addr].
    destruct (Addr_lt_dec a e);[|contradiction].
    auto.
  Qed.

  (* store and increment *)
  Lemma wp_storeU_success_0_reg E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src w'
         p g b e a a' w'' :
    decodeInstrW w = StoreU dst (inl 0%Z) (inr src) →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    isU p  = true -> canStoreU p a w'' = true ->
    withinBounds ((p, g), b, e, a) = true ->
    (a + 1)%a = Some a' ->


     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a)
           ∗ ▷ a ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ w
              ∗ src ↦ᵣ w''
              ∗ dst ↦ᵣ inr ((p,g),b,e,a')
              ∗ a ↦ₐ w'' }}}.
  Proof.
      iIntros (Hinstr Hvpc Hpca' HU HstoreU Hwb Ha' φ)
             "(>HPC & >Hi & >Hsrc & >Hdst & >Hsrca) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iApply (wp_storeU _ pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite addr_add_0. apply andb_true_iff in Hwb as [Hle%Z.leb_le Hlt%Z.ltb_lt].
      rewrite !decide_True//;[|clear;solve_addr].
      rewrite HU HstoreU /=. simplify_map_eq. auto. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ". destruct H9 as (?&?&?&?&?&?).
       simplify_map_eq. rewrite addr_add_0 in H8. simplify_eq.
       rewrite decide_True in H12;[|clear;solve_addr].
       rewrite insert_commute // insert_insert.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       destruct (addr_eq_dec a'0 a'0);[|contradiction].
       incrementPC_inv.
       simplify_map_eq.
       rewrite (insert_commute _ _ PC) // insert_insert.
       rewrite (insert_commute _ _ src) // insert_insert.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hsrc Hdst] ]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto.
       all: try congruence.
       erewrite wb_implies_verify_access in e4; eauto. simplify_eq. congruence.
       erewrite wb_implies_verify_access in e4; eauto. simplify_eq.
       destruct e8; try congruence. inv Hvpc. naive_solver.
       destruct e7; try congruence. inv Hvpc. naive_solver.
       Unshelve. all:auto.
     }
  Qed.

  Lemma wp_storeU_failure_0_reg E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src w'
         p g b e a a' w'' :
    decodeInstrW w = StoreU dst (inl 0%Z) (inr src) →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    isU p  = true -> canStoreU p a w'' = false ->
    withinBounds ((p, g), b, e, a) = true ->
    (a + 1)%a = Some a' ->


     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a)
           ∗ ▷ a ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
  Proof.
      iIntros (Hinstr Hvpc Hpca' HU HstoreU Hwb Ha' φ)
             "(>HPC & >Hi & >Hsrc & >Hdst & >Hsrca) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iApply (wp_storeU _ pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite addr_add_0. apply andb_true_iff in Hwb as [Hle%Z.leb_le Hlt%Z.ltb_lt].
      rewrite !decide_True//;[|clear;solve_addr].
      rewrite HU HstoreU /=. simplify_map_eq. auto. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
    { (* Success (contradiction) *)
      destruct H9 as (?&?&?&?&?&?).
      simplify_map_eq. rewrite addr_add_0 in H8. simplify_eq.
       rewrite decide_True in H12;[|clear;solve_addr].
       rewrite insert_commute // insert_insert.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       destruct (addr_eq_dec a'0 a'0);[|contradiction].
       incrementPC_inv. simplify_map_eq. congruence. }
    { (* Failure (contradiction) *) iApply "Hφ". done. }
  Qed.

  (* store and increment from and to the same register *)
  Lemma wp_storeU_success_0_reg_same E pc_p pc_g pc_b pc_e pc_a pc_a' w dst w'
         p g b e a a' :
    decodeInstrW w = StoreU dst (inl 0%Z) (inr dst) →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    isU p  = true -> canStoreU p a (inr (p, g, b, e, a)) = true ->
    withinBounds ((p, g), b, e, a) = true ->
    (a + 1)%a = Some a' ->


     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a)
           ∗ ▷ a ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ w
              ∗ dst ↦ᵣ inr ((p,g),b,e,a')
              ∗ a ↦ₐ inr ((p,g),b,e,a)}}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' HU HstoreU Hwb Ha' φ)
             "(>HPC & >Hi & >Hdst & >Hsrca) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iApply (wp_storeU _ pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite addr_add_0. apply andb_true_iff in Hwb as [Hle%Z.leb_le Hlt%Z.ltb_lt].
      rewrite !decide_True//;[|clear;solve_addr].
      unfold canStoreU. rewrite HU HstoreU /=. simplify_map_eq. auto. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ". destruct H7 as (?&?&?&?&?&?).
       simplify_map_eq. rewrite addr_add_0 in H6;simplify_eq. simplify_map_eq.
       rewrite insert_commute // insert_insert.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       destruct (addr_eq_dec a'0 a'0);[|contradiction].
       incrementPC_inv.
       simplify_map_eq.
       rewrite (insert_commute _ _ PC) // insert_insert.
       rewrite insert_insert.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC [Hsrc Hdst] ]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto.
       all: try congruence.
       erewrite wb_implies_verify_access in e4; eauto. simplify_eq. congruence.
       erewrite wb_implies_verify_access in e4; eauto. simplify_eq.
       destruct e8; try congruence. inv Hvpc; naive_solver.
       destruct e7; try congruence. inv Hvpc; naive_solver.
       Unshelve. all:auto.
     }
  Qed.

  Lemma wp_storeU_success_0_z E pc_p pc_g pc_b pc_e pc_a pc_a' w dst z w'
         p g b e a a' :
    decodeInstrW w = StoreU dst (inl 0%Z) (inl z) →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →
    isU p  = true ->
    withinBounds ((p, g), b, e, a) = true ->
    (a + 1)%a = Some a' ->


     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a)
           ∗ ▷ a ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ w
              ∗ dst ↦ᵣ inr ((p,g),b,e,a')
              ∗ a ↦ₐ (inl z) }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' HU Hwb Ha' φ)
             "(>HPC & >Hi & >Hdst & >Hsrca) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iApply (wp_storeU _ pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite HU. erewrite wb_implies_verify_access; eauto.
      by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ". destruct H7 as (?&?&?&?&?&?).
       simplify_map_eq. rewrite addr_add_0 in H6;simplify_eq.
       rewrite insert_commute // insert_insert.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       destruct (addr_eq_dec a'0 a'0);[|contradiction].
       incrementPC_inv.
       simplify_map_eq.
       rewrite (insert_commute _ _ PC) // insert_insert. rewrite insert_insert.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hdst]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto.
       all: try congruence.
       erewrite wb_implies_verify_access in e4; eauto. simplify_eq.
       destruct e8; try congruence. inv Hvpc. naive_solver.
       destruct e7; try congruence. inv Hvpc. naive_solver.
       Unshelve. all:auto.
     }
  Qed.

End cap_lang_rules.
