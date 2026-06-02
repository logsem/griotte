From iris.algebra Require Import gmap agree auth excl csum excl_auth.
From iris.proofmode Require Import proofmode.
From cap_machine Require Export cap_lang sts rules_base region_invariants_definitions stdpp_extra.
From stdpp Require Import countable list_relations.

Section sealing_interp.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG} {CNames : gset CmptName}
    {stsg : STSG Addr region_type OType Word Σ}
    {heapg : heapGS Σ}
    `{MP: MachineParameters}.
  Implicit Types W : WORLD.

  Definition sealing_map_def
    (W : WORLD)
    (C : CmptName)
    : iProp Σ
     := ([∗ map] o↦ws ∈ seal_std W,
           (sts_seals_std C o ws) ∗
           ∃ Po, seal_pred o Po ∗
                 (∀ w, future_priv_mono C Po w) ∗
                 ( [∗ set] w ∈ ws, ▷ Po (W, C, w) )).

  Definition sealing_map_aux : { x | x = @sealing_map_def }. by eexists. Qed.
  Definition sealing_map := proj1_sig sealing_map_aux.
  Definition sealing_map_eq : @sealing_map = @sealing_map_def := proj2_sig sealing_map_aux.

  Lemma sealing_map_def_monotone (C : CmptName) (W W' : WORLD) :
    (seal_std W) = (seal_std W') ->
    related_sts_priv_world W W' →
    sealing_map_def W C -∗
    sealing_map_def W' C.
  Proof.
    iIntros (HWseal Hrelated) "Hr".
    rewrite /sealing_map_def.
    rewrite HWseal.
    iApply big_sepM_mono; iFrame.
    iIntros (o ws Hsome) "Hm".
    iDestruct "Hm" as "($ & %Po & Hpred & #Hmono & HPo)".
    iExists Po; iFrame "∗#".
    clear -Hrelated.
    iStopProof.
    induction ws using set_ind_L; iIntros "[#Hmono Hs]"; first done.
    rewrite big_sepS_union; last set_solver+H.
    rewrite big_sepS_union; last set_solver+H.
    iDestruct "Hs" as "[Hx Hs]".
    iSplitL "Hx"; last (iApply IHws; iFrame "∗#").
    rewrite !big_sepS_singleton.
    iApply "Hmono"; eauto.
  Qed.

  Lemma sealing_map_monotone (C : CmptName) (W W' : WORLD) :
    (seal_std W) = (seal_std W') ->
    related_sts_priv_world W W' →
    sealing_map W C -∗
    sealing_map W' C.
  Proof.
    iIntros (HWseal Hrelated) "Hr".
    rewrite sealing_map_eq.
    iApply sealing_map_def_monotone; eauto.
  Qed.

  Lemma sealing_map_monotone_pub (C : CmptName) (W W' : WORLD) :
    (seal_std W) = (seal_std W') ->
    related_sts_pub_world W W' →
    sealing_map W C -∗
    sealing_map W' C.
  Proof.
    iIntros (HWseal Hrelated) "Hr".
    apply related_sts_pub_priv_world in Hrelated.
    iApply sealing_map_monotone; eauto.
  Qed.

  Lemma sealing_map_def_alloc (W : WORLD) (C : CmptName) (Po : WORLD * CmptName * Word → iProp Σ) (o : OType) (ws : gset Word)  :
    let W' := (<o[ o := ws ]o> W) in
    o ∉ dom (seal_std W) ->
    seal_pred o Po -∗
    sts_seals_std C o ws -∗
    (∀ w : Word, future_priv_mono C Po w) -∗
    ([∗ set] w ∈ ws, ▷ Po (W', C, w)) -∗
    sealing_map_def W C -∗
    sealing_map_def W' C.
  Proof.
    intros W'; subst W'.
    iIntros (Ho) "Hseal_Po Hseal_ws Hmono_Po Hws_Po Hr".
    rewrite /sealing_map_def.
    iApply big_sepM_insert; first by apply not_elem_of_dom.
    iFrame.
    iApply big_sepM_mono; iFrame.
    iIntros (o' ws' Hsome) "Hm".
    iDestruct "Hm" as "($ & %Po' & Hpred & #Hmono & HPo)".
    iExists Po'; iFrame "∗#".
    pose proof (related_sts_priv_world_alloc_ot W o ws Ho) as Hrelated.
    clear -Hrelated.
    iStopProof.
    induction ws' using set_ind_L; iIntros "[#Hmono Hs]"; first done.
    rewrite big_sepS_union; last set_solver+H.
    rewrite big_sepS_union; last set_solver+H.
    iDestruct "Hs" as "[Hx Hs]".
    iSplitL "Hx"; last ( iApply IHws'; iFrame "∗#" ).
    rewrite !big_sepS_singleton.
    iApply "Hmono"; eauto.
  Qed.


  Lemma sealing_map_def_update (W : WORLD) (C : CmptName) (Po : WORLD * CmptName * Word → iProp Σ)
    (o : OType) (ws ws' : gset Word)  :
    let W' := (<o[ o := ws' ∪ ws ]o> W) in
    (seal_std W) !! o = Some ws ->
    seal_pred o Po -∗
    ([∗ set] w ∈ ws', ▷ Po (W', C, w)) -∗
    sealing_map_def W C ∗ sts_full_world W C
    ==∗
    sealing_map_def W' C ∗ sts_full_world W' C.
  Proof.
    intros W'; subst W'.
    iIntros (Ho) "Hspred_Po Hws_Po [Hr Hsts]".
    rewrite /sealing_map_def.
    iDestruct (big_sepM_delete with "Hr") as "[(Hseal & %Po' & Hpred & #Hmono & HPo) Hr]"; eauto.
    iMod (sts_update_seal_std _ _ _ _ ws' with "[$Hsts $Hseal]") as "[Hsts #Hseal]"; eauto.
    iDestruct (seal_pred_agree with "Hspred_Po Hpred") as "#Heq".
    pose proof (related_sts_pub_world_update_ot W o ws ws' Ho) as Hrelated.
    iAssert (
         ∃ Po0 : WORLD * CmptName * Word → iProp Σ,
           seal_pred o Po0 ∗
           (∀ w : Word, future_priv_mono C Po0 w) ∗
           ([∗ set] w ∈ (ws' ∪ ws), ▷ Po0 (<o[o:=ws' ∪ ws]o>W, C, w))
      )%I with "[Hws_Po Hpred HPo]" as "H".
    { iFrame "∗#".
      rewrite -!big_sepS_later; iNext.
      iApply (big_sepS_union_2 with "[Hws_Po]")
      ; generalize Hrelated; clear Hrelated
      ; generalize (ws' ∪ ws) as ws0; intros ws0 Hrelated.
      - clear -Hrelated; iClear "Hseal".
        iStopProof.
        induction ws' using set_ind_L; iIntros "[ [#Hmono #Heq] Hs]"; first done.
        rewrite big_sepS_union; last set_solver+H.
        rewrite big_sepS_union; last set_solver+H.
        iDestruct "Hs" as "[Hx Hs]".
        iSplitL "Hx"; last ( iApply IHws'; eauto ).
        rewrite !big_sepS_singleton; iRewrite -("Heq" $! (<o[o:=ws0]o>W, C, x)); done.
      - clear -Hrelated; iClear "Hseal".
        iStopProof.
        induction ws using set_ind_L; iIntros "[ [#Hmono #Heq] Hs]"; first done.
        rewrite big_sepS_union; last set_solver+H.
        rewrite big_sepS_union; last set_solver+H.
        iDestruct "Hs" as "[Hx Hs]".
        iSplitL "Hx"; last ( iApply IHws; eauto ).
        rewrite !big_sepS_singleton.
        iApply "Hmono"; eauto.
        iPureIntro.
        by apply related_sts_pub_priv_world.
    }
    iAssert (
        [∗ map] k↦y ∈ delete o W.2, sts_seals_std C k y ∗
                                    ∃ Po0 : WORLD * CmptName * Word → iProp Σ,
                                      seal_pred k Po0 ∗
                                      (∀ w : Word, future_priv_mono C Po0 w) ∗
                                      ([∗ set] w ∈ y, ▷ Po0 (<o[o:=ws' ∪ ws]o>W, C, w))
      )%I with "[Hr]" as "Hr".
    {
      iClear "Heq Hmono Hseal".
      clear Po.
      iApply big_sepM_mono; last iFrame.
      iIntros (o' wso' Hswo') "($ & %Po & Hspred & #Hmono & Hwso')".
      iExists Po; iFrame "∗#".
      clear -Hrelated.
      iStopProof.
      induction wso' using set_ind_L; iIntros "[#Hmono Hs]"; first done.
      rewrite big_sepS_union; last set_solver+H.
      rewrite big_sepS_union; last set_solver+H.
      iDestruct "Hs" as "[Hx Hs]".
      iSplitL "Hx"; last ( iApply IHwso'; iFrame "∗#" ).
      rewrite !big_sepS_singleton.
      iApply "Hmono"; eauto.
      iPureIntro.
      by apply related_sts_pub_priv_world.
    }
    iDestruct (big_sepM_insert with "[$Hr $H]") as "Hr"; eauto.
    { by simplify_map_eq. }
    rewrite insert_delete_eq.
    by iFrame.
  Qed.

  Lemma sealing_map_update (W : WORLD) (C : CmptName) (Po : WORLD * CmptName * Word → iProp Σ)
    (o : OType) (ws ws' : gset Word)  :
    let W' := (<o[ o := ws' ∪ ws ]o> W) in
    (seal_std W) !! o = Some ws ->
    seal_pred o Po -∗
    ([∗ set] w ∈ ws', ▷ Po (W', C, w)) -∗
    sealing_map W C ∗ sts_full_world W C
    ==∗
    sealing_map W' C ∗ sts_full_world W' C.
  Proof. rewrite sealing_map_eq; apply sealing_map_def_update. Qed.


End sealing_interp.
