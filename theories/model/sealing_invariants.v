From iris.algebra Require Import gmap agree auth excl csum excl_auth.
From iris.proofmode Require Import proofmode.
From cap_machine Require Export stdpp_extra rules_base.
From cap_machine Require Export sts world_std_sts world_ghost_resources.

Section sealing_interp.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG} {CNames : gset CmptName}
    {stsg : STSG Addr region_type OType Word Σ}
    {relg : relGS Σ}
    `{MP: MachineParameters}.
  Implicit Types W : WORLD.


  (* TODO Use an actual normalisation function, which only keeps the highest authority! *)
  (* The normalisation function ensures that there's no duplicates in the set,
     modulo the locality. *)
  Definition normalise_sealed_words (s : gset Word) : gset Word :=
    set_map (fun w => force_global w) s.

  Lemma normalise_sealed_words_empty :
    normalise_sealed_words ∅ = ∅.
  Proof. by rewrite /normalise_sealed_words set_map_empty. Qed.

  Lemma normalise_sealed_words_union (s s' : gset Word) :
    normalise_sealed_words (s ∪ s') = (normalise_sealed_words s) ∪ (normalise_sealed_words s').
  Proof. by rewrite /normalise_sealed_words set_map_union_L. Qed.

  Lemma normalise_sealed_words_singleton (w : Word) :
    normalise_sealed_words {[w]} = {[ force_global w ]}.
  Proof. by rewrite /normalise_sealed_words set_map_singleton_L. Qed.

  Lemma normalise_sealed_words_mono (s s' : gset Word) :
    s ⊆ s' ->
    normalise_sealed_words s ⊆ normalise_sealed_words s'.
  Proof.
    intros Hs.
    rewrite /normalise_sealed_words. apply set_map_mono; eauto.
    rewrite /pointwise_relation; intros a; done.
  Qed.

  Lemma normalise_sealed_words_borrow (w : Word) :
    normalise_sealed_words {[w; borrow w]} = {[ force_global w ]}.
  Proof.
    rewrite normalise_sealed_words_union !normalise_sealed_words_singleton force_global_borrow.
    set_solver+.
  Qed.

  Local Definition sealing_map_def
    (W : WORLD)
    (C : CmptName)
    : iProp Σ
     := ([∗ map] o↦ws ∈ seal_std W,
           (sts_seals_std C o ws) ∗
           ∃ Po, seal_pred o Po ∗
                 (∀ w, future_priv_mono C Po w) ∗
                 ( [∗ set] w ∈ normalise_sealed_words ws, ▷ Po (W, C, w) )).

  Local Definition sealing_map_aux : { x | x = @sealing_map_def }. by eexists. Qed.
  Definition sealing_map := proj1_sig sealing_map_aux.
  Local Definition sealing_map_eq : @sealing_map = @sealing_map_def := proj2_sig sealing_map_aux.

  Local Lemma sealing_map_def_empty (C : CmptName) : ⊢ (sealing_map_def (∅, (∅, ∅), ∅) C)%I.
  Proof. iStartProof; rewrite /sealing_map_def ; done. Qed.

  Local Lemma sealing_map_def_monotone (C : CmptName) (W W' : WORLD) :
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
    move: (normalise_sealed_words ws); clear ws; intros ws.
    induction ws using set_ind_L; iIntros "[#Hmono Hs]"; first done.
    rewrite big_sepS_union; last set_solver+H.
    rewrite big_sepS_union; last set_solver+H.
    iDestruct "Hs" as "[Hx Hs]".
    iSplitL "Hx"; last (iApply IHws; iFrame "∗#").
    rewrite !big_sepS_singleton.
    iApply "Hmono"; eauto.
  Qed.

  Local Lemma sealing_map_def_alloc (W : WORLD) (C : CmptName) (Po : WORLD * CmptName * Word → iProp Σ) (o : OType) (ws : gset Word)  :
    let W' := (<o[ o := ws ]o> W) in
    o ∉ dom (seal_std W) ->
    seal_pred o Po -∗
    (∀ w : Word, future_priv_mono C Po w) -∗
    ([∗ set] w ∈ (normalise_sealed_words ws), ▷ Po (W', C, w)) -∗
    sealing_map_def W C ∗ sts_full_world W C ==∗
    sealing_map_def W' C ∗ sts_full_world W' C ∗ sts_seals_std C o ws.
  Proof.
    intros W'; subst W'.
    iIntros (Ho) "Hseal_Po Hmono_Po Hws_Po [Hr Hsts]".
    rewrite /sealing_map_def.
    iMod (sts_alloc_seal_std _ _ _ ws with "[] [$Hsts]") as "[Hsts #Hseal]"; eauto.
    iAssert (
        [∗ map] k↦y ∈ W.2, sts_seals_std C k y ∗
                                    ∃ Po0 : WORLD * CmptName * Word → iProp Σ,
                                      seal_pred k Po0 ∗
                                      (∀ w : Word, future_priv_mono C Po0 w) ∗
                                      ([∗ set] w ∈ (normalise_sealed_words y), ▷ Po0 (<o[o:=ws]o>W, C, w))
      )%I with "[Hr]" as "Hr".
    {
      iClear "Hseal".
      clear Po.
      iApply big_sepM_mono; last iFrame.
      iIntros (o' wso' Hswo') "($ & %Po & Hspred & #Hmono & Hwso')".
      iExists Po; iFrame "∗#".
      pose proof (related_sts_priv_world_update_ot W o ws) as Hrelated.
      clear -Hrelated.
      iStopProof.
      move: (normalise_sealed_words wso'); clear wso'; intros wso'.
      induction wso' using set_ind_L; iIntros "[#Hmono Hs]"; first done.
      rewrite big_sepS_union; last set_solver+H.
      rewrite big_sepS_union; last set_solver+H.
      iDestruct "Hs" as "[Hx Hs]".
      iSplitL "Hx"; last ( iApply IHwso'; iFrame "∗#" ).
      rewrite !big_sepS_singleton.
      iApply "Hmono"; eauto.
    }

    iDestruct (big_sepM_insert _ _ o ws with "[$Hr $Hseal $Hseal_Po $Hmono_Po $Hws_Po]") as "Hr".
    { by apply not_elem_of_dom. }
    iModIntro.
    iFrame "#∗".
    rewrite /seals_std_update_default.
    rewrite not_elem_of_dom in Ho; rewrite Ho /= union_empty_r_L.
    done.
  Qed.

  Local Lemma sealing_map_def_update (W : WORLD) (C : CmptName) (Po : WORLD * CmptName * Word → iProp Σ)
    (o : OType) (ws ws' : gset Word)  :
    let W' := (<o[ o := ws' ∪ ws ]o> W) in
    (seal_std W) !! o = Some ws ->
    seal_pred o Po -∗
    ([∗ set] w ∈ (normalise_sealed_words ws'), ▷ Po (W', C, w)) -∗
    sealing_map_def W C ∗ sts_full_world W C
    ==∗
    sealing_map_def W' C ∗ sts_full_world W' C ∗ sts_seals_std C o (ws' ∪ ws).
  Proof.
    intros W'; subst W'.
    iIntros (Ho) "Hspred_Po Hws_Po [Hr Hsts]".
    rewrite /sealing_map_def.
    iDestruct (big_sepM_delete with "Hr") as "[(Hseal & %Po' & Hpred & #Hmono & HPo) Hr]"; eauto.
    iMod (sts_update_seal_std _ _ _ _ ws' with "[$Hsts $Hseal]") as "[Hsts #Hseal]"; eauto.
    iDestruct (seal_pred_agree with "Hspred_Po Hpred") as "#Heq".
    pose proof (related_sts_pub_world_update_ot W o (ws' ∪ ws)) as Hrelated.
    iAssert (
         ∃ Po0 : WORLD * CmptName * Word → iProp Σ,
           seal_pred o Po0 ∗
           (∀ w : Word, future_priv_mono C Po0 w) ∗
           ([∗ set] w ∈ (normalise_sealed_words (ws' ∪ ws)), ▷ Po0 (<o[o:=ws' ∪ ws]o>W, C, w))
      )%I with "[Hws_Po Hpred HPo]" as "H".
    { iFrame "∗#".
      rewrite -!big_sepS_later; iNext.
      rewrite normalise_sealed_words_union.
      iApply (big_sepS_union_2 with "[Hws_Po]")
      ; generalize Hrelated; clear Hrelated
      ; generalize (ws' ∪ ws) as ws0; intros ws0 Hrelated.
      - clear -Hrelated; iClear "Hseal".
        iStopProof.
        move: (normalise_sealed_words ws'); clear ws'; intros ws'.
        induction ws' using set_ind_L; iIntros "[ [#Hmono #Heq] Hs]"; first done.
        rewrite big_sepS_union; last set_solver+H.
        rewrite big_sepS_union; last set_solver+H.
        iDestruct "Hs" as "[Hx Hs]".
        iSplitL "Hx"; last ( iApply IHws'; eauto ).
        rewrite !big_sepS_singleton; iRewrite -("Heq" $! (<o[o:=ws0]o>W, C, x)); done.
      - clear -Hrelated; iClear "Hseal".
        iStopProof.
        move: (normalise_sealed_words ws); clear ws; intros ws.
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
                                      ([∗ set] w ∈ normalise_sealed_words y, ▷ Po0 (<o[o:=ws' ∪ ws]o>W, C, w))
      )%I with "[Hr]" as "Hr".
    {
      iClear "Heq Hmono Hseal".
      clear Po.
      iApply big_sepM_mono; last iFrame.
      iIntros (o' wso' Hswo') "($ & %Po & Hspred & #Hmono & Hwso')".
      iExists Po; iFrame "∗#".
      clear -Hrelated.
      iStopProof.
      move: (normalise_sealed_words wso'); clear wso'; intros wso'.
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
    iFrame "#∗".
    rewrite /seals_std_update_default.
    rewrite Ho /=.
    replace (ws' ∪ ws ∪ ws) with (ws' ∪ ws) by set_solver+.
    by iFrame.
  Qed.

  Local Lemma sealing_map_def_update' (W : WORLD) (C : CmptName) (Po : WORLD * CmptName * Word → iProp Σ)
    (o : OType) (ws : gset Word)  :
    let W' := (<o[ o := ws ]o> W) in
    seal_pred o Po -∗
    (∀ w : Word, future_priv_mono C Po w) -∗
    ([∗ set] w ∈ (normalise_sealed_words ws), ▷ Po (W', C, w)) -∗
    sealing_map_def W C ∗ sts_full_world W C
    ==∗
    sealing_map_def W' C ∗ sts_full_world W' C ∗ sts_seals_std C o ws.
  Proof.
    intros W'; subst W'.
    iIntros "Hspred_Po Hmono_Po Hws_Po [Hr Hsts]".
    destruct ((seal_std W) !! o) eqn:Ho.
    - iMod (sealing_map_def_update _ _ _ _ g ws with "[$Hspred_Po] [Hws_Po] [$Hr $Hsts]")
        as "(Hseals & Hsts & Hseal)"; eauto.
      { rewrite /seals_std_update_default Ho /=.
        replace (ws ∪ g ∪ g) with (ws ∪ g) by set_solver+.
        done.
      }
      iModIntro.
      rewrite /seals_std_update_default Ho /=.
      replace (ws ∪ g ∪ g) with (ws ∪ g) by set_solver+.
      iFrame.
      iApply sts_seals_std_weaken; last done; set_solver+.
    - rewrite -not_elem_of_dom in Ho.
      iMod (sealing_map_def_alloc _ _ _ _ ws Ho with "[$Hspred_Po] [$Hmono_Po] [Hws_Po] [$Hr $Hsts]")
        as "(Hseals & Hsts & Hseal)"; eauto.
      by iFrame.
  Qed.

  Lemma sealing_map_empty (C : CmptName) : ⊢ (sealing_map (∅, (∅, ∅), ∅) C)%I.
  Proof. rewrite sealing_map_eq; apply sealing_map_def_empty. Qed.

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

  Lemma sealing_map_alloc (W : WORLD) (C : CmptName) (Po : WORLD * CmptName * Word → iProp Σ) (o : OType) (ws : gset Word)  :
    let W' := (<o[ o := ws ]o> W) in
    o ∉ dom (seal_std W) ->
    seal_pred o Po -∗
    (∀ w : Word, future_priv_mono C Po w) -∗
    ([∗ set] w ∈ (normalise_sealed_words ws), ▷ Po (W', C, w)) -∗
    sealing_map W C ∗ sts_full_world W C ==∗
    sealing_map W' C ∗ sts_full_world W' C ∗ sts_seals_std C o ws.
  Proof. rewrite sealing_map_eq; apply sealing_map_def_alloc. Qed.

  Lemma sealing_map_update (W : WORLD) (C : CmptName) (Po : WORLD * CmptName * Word → iProp Σ)
    (o : OType) (ws ws' : gset Word)  :
    let W' := (<o[ o := ws' ∪ ws ]o> W) in
    (seal_std W) !! o = Some ws ->
    seal_pred o Po -∗
    ([∗ set] w ∈ (normalise_sealed_words ws'), ▷ Po (W', C, w)) -∗
    sealing_map W C ∗ sts_full_world W C
    ==∗
    sealing_map W' C ∗ sts_full_world W' C ∗ sts_seals_std C o (ws' ∪ ws).
  Proof. rewrite sealing_map_eq; apply sealing_map_def_update. Qed.

  Lemma sealing_map_update' (W : WORLD) (C : CmptName) (Po : WORLD * CmptName * Word → iProp Σ)
    (o : OType) (ws : gset Word)  :
    let W' := (<o[ o := ws ]o> W) in
    seal_pred o Po -∗
    (∀ w : Word, future_priv_mono C Po w) -∗
    ([∗ set] w ∈ (normalise_sealed_words ws), ▷ Po (W', C, w)) -∗
    sealing_map W C ∗ sts_full_world W C
    ==∗
    sealing_map W' C ∗ sts_full_world W' C ∗ sts_seals_std C o ws.
  Proof. rewrite sealing_map_eq; apply sealing_map_def_update'. Qed.

  Lemma sealing_map_seal_pred
    (W : WORLD) (C : CmptName) (o : OType) Po `{Hpers : ∀ WCv, Persistent (Po WCv)}
    (ws : gset Word) :
    seal_pred o Po -∗
    sts_seals_std C o ws -∗
    sealing_map W C -∗
    sts_full_world W C -∗
    ▷ (sealing_map W C ∗ sts_full_world W C ∗ [∗ set] w ∈ (normalise_sealed_words ws), Po (W, C, w)).
  Proof.
    iIntros "#Hspred Hseal Hseals Hsts".
    iDestruct (sts_full_seals_std_subseteq with "Hsts Hseal") as "(%ws' & %Hws' & %Hws_sub)".
    iEval (rewrite sealing_map_eq /sealing_map_def /=) in "Hseals".
    iDestruct (big_sepM_lookup_acc with "Hseals") as "[H Hseals]"; first done.
    iDestruct "H" as "(Hseal_ws & %Po' & #Hspred_Po' & #Hmono & HPos)".
    iDestruct (seal_pred_agree with "Hspred Hspred_Po'") as "#Heq".
    iNext.
    assert ( (∀ w, Persistent (Po (W, C, w)))).
    { intros w'; apply (Hpers (W,C,w')). }
    iAssert ( [∗ set] w ∈ (normalise_sealed_words ws'), Po (W, C, w))%I with "[HPos]" as "#HPs".
    { iClear "Hspred Hspred_Po' Hmono"; clear.
      iStopProof.
      move: (normalise_sealed_words ws'); clear ws'; intros ws'.
      induction ws' using set_ind_L; iIntros "(#Heq & Hs)"; first done.
      rewrite big_sepS_union; last set_solver+H.
      rewrite big_sepS_union; last set_solver+H.
      iDestruct "Hs" as "[Hx Hs]".
      iSplitL "Hx"; last ( iApply IHws'; iFrame "∗#" ).
      rewrite !big_sepS_singleton.
      by iRewrite -("Heq" $! (W,C,x)) in "Hx".
    }
    iDestruct ("Hseals" with "[$Hseal_ws $Hspred_Po' $Hmono HPos]") as "Hseals".
    { by iApply big_sepS_later; iNext. }
    rewrite -/(sealing_map_def W C) -sealing_map_eq.
    iFrame "∗#".
    apply normalise_sealed_words_mono in Hws_sub.
    iApply big_sepS_subseteq; eauto.
  Qed.

  Lemma sealing_map_seal_pred_singleton (W : WORLD) (C : CmptName) (o : OType) Po `{Hpers: ∀ WCv, Persistent (Po WCv)} (w : Word) :
    seal_pred o Po -∗
    sts_seals_std C o {[ w ]} -∗
    sealing_map W C -∗
    sts_full_world W C -∗
    ▷ (sealing_map W C ∗ sts_full_world W C ∗ Po (W, C, force_global w)).
  Proof.
    iIntros "#Hspred Hseal Hseals Hsts".
    iDestruct (sealing_map_seal_pred with "Hspred Hseal Hseals Hsts") as "($ & $ & H)"; eauto.
    by rewrite normalise_sealed_words_singleton big_sepS_singleton.
  Qed.

  Local Definition sealing_map_open_def
    (W : WORLD)
    (C : CmptName)
    (o : OType)
    : iProp Σ
     := ([∗ map] o↦ws ∈ (delete o (seal_std W)),
           (sts_seals_std C o ws) ∗
           ∃ Po, seal_pred o Po ∗
                 (∀ w, future_priv_mono C Po w) ∗
                 ( [∗ set] w ∈ (normalise_sealed_words ws), ▷ Po (W, C, w) )).
  Local Definition sealing_map_open_aux : { x | x = @sealing_map_open_def }. by eexists. Qed.
  Definition sealing_map_open := proj1_sig sealing_map_open_aux.
  Local Definition sealing_map_open_eq : @sealing_map_open = @sealing_map_open_def := proj2_sig sealing_map_open_aux.

  Definition sealing_map_resource_open (W : WORLD) (C : CmptName) (o : OType) Po ws :=
    ( ∃ (ws' : gset Word),
        ⌜ (seal_std W) !! o = Some ws' ⌝ ∗
        ⌜ ws ⊆ ws'⌝ ∗
        sts_seals_std C o ws' ∗
        (∀ w : Word, future_priv_mono C Po w) ∗
        ([∗ set] w ∈ (normalise_sealed_words ws' ∖ normalise_sealed_words ws), Po (W, C, w))
    )%I.

  Local Lemma open_sealing_map_def (W : WORLD) (C : CmptName) (o : OType) Po (ws : gset Word) :
    seal_pred o Po -∗
    sts_seals_std C o ws -∗
    sealing_map_def W C -∗
    sts_full_world W C
    -∗
    sealing_map_open_def W C o ∗
    sts_full_world W C ∗
    ▷ (sealing_map_resource_open W C o Po ws
       ∗ ([∗ set] w ∈ (normalise_sealed_words ws), Po (W, C, w))).
  Proof.
    iIntros "Hspred Hseal Hseals Hsts".
    iDestruct (sts_full_seals_std_subseteq with "Hsts Hseal") as "(%ws' & %Hws' & %Hws_sub)".
    iEval (rewrite /sealing_map_def /=) in "Hseals".
    rewrite big_sepM_delete; last done.
    iDestruct "Hseals" as "([ Hseal_ws' (%Po' & Hspred_Po' & #Hmono_Po' & Hws_Po') ] & Hseals)".
    iDestruct (seal_pred_agree with "Hspred Hspred_Po'") as "#Heq".
    iFrame "∗%".
    iNext.
    apply normalise_sealed_words_mono in Hws_sub.
    rewrite {1}(union_difference_L (normalise_sealed_words ws) (normalise_sealed_words ws')); last done.
    iDestruct (big_sepS_union with "Hws_Po'") as "[Hws_Po Hws'_Po]"; first set_solver+.
    iSplitR "Hws_Po".
    - iSplitR "Hws'_Po".
      + iIntros (w W0 W1 Hrel) "!>HPo".
        iRewrite ("Heq" $! (W1, C, w)).
        iRewrite ("Heq" $! (W0, C, w)) in "HPo".
        iApply "Hmono_Po'"; eauto.
      + iApply (big_sepS_impl with "Hws'_Po"); eauto.
        iModIntro; iIntros (w _) "HPo'".
        by iRewrite ("Heq" $! (W, C, w)).
    - iApply (big_sepS_impl with "Hws_Po"); eauto.
      iModIntro; iIntros (w _) "HPo'".
      by iRewrite ("Heq" $! (W, C, w)).
  Qed.

  Local Lemma close_sealing_map_def' (W : WORLD) (C : CmptName) (o : OType) Po (ws : gset Word) :
    (seal_std W) !! o = Some ws ->
    seal_pred o Po -∗
    sts_seals_std C o ws -∗
    (∀ w : Word, future_priv_mono C Po w) -∗
    ([∗ set] w ∈ (normalise_sealed_words ws), ▷ Po (W, C, w)) -∗
    sealing_map_open_def W C o -∗
    sealing_map_def W C.
  Proof.
    iIntros (Ho) "Hspred_Po Hseal_ws Hmono_Po Hws_Po Hseals".
    rewrite /sealing_map_open_def.
    iDestruct (big_sepM_delete with "[ - $Hseals ]" ) as "Hseals"; eauto.
  Qed.

  Local Lemma close_sealing_map_def (W : WORLD) (C : CmptName) (o : OType) Po (ws : gset Word) :
    seal_pred o Po -∗
    sealing_map_resource_open W C o Po ws -∗
    ([∗ set] w ∈ (normalise_sealed_words ws), Po (W, C, w)) -∗
    sealing_map_open_def W C o -∗
    sealing_map_def W C.
  Proof.
    iIntros "Hspred_Po (%ws' & %Hws' & %Hws_ws' & Hseal_ws' & Hmono_ws' & Hws'_Po) Hws_Po Hseals".
    rewrite /sealing_map_open_def.
    iDestruct (big_sepS_union with "[$Hws_Po $Hws'_Po]") as "Hws_Po"; first set_solver+.
    apply normalise_sealed_words_mono in Hws_ws'.
    rewrite -(union_difference_L (normalise_sealed_words ws) (normalise_sealed_words ws')) ; last done.
    iDestruct (big_sepM_delete with "[ - $Hseals ]" ) as "Hseals"; eauto; iFrame.
    by rewrite -big_sepS_later.
  Qed.

  Lemma open_sealing_map (W : WORLD) (C : CmptName) (o : OType) Po (ws : gset Word) :
    seal_pred o Po -∗
    sts_seals_std C o ws -∗
    sealing_map W C -∗
    sts_full_world W C
    -∗
    sealing_map_open W C o ∗
    sts_full_world W C ∗
    ▷ (sealing_map_resource_open W C o Po ws ∗ ([∗ set] w ∈ (normalise_sealed_words ws), Po (W, C, w))).
  Proof. rewrite sealing_map_eq sealing_map_open_eq; apply open_sealing_map_def. Qed.

  Lemma open_sealing_map_singleton (W : WORLD) (C : CmptName) (o : OType) Po (w : Word) :
    seal_pred o Po -∗
    sts_seals_std C o {[w]} -∗
    sealing_map W C -∗
    sts_full_world W C
    -∗
    sealing_map_open W C o ∗
    sts_full_world W C ∗
    ▷ (sealing_map_resource_open W C o Po {[w]} ∗ (Po (W, C, force_global w))).
  Proof.
    iIntros "Hspred Hseal Hseals Hsts".
    iDestruct (open_sealing_map with "Hspred Hseal Hseals Hsts") as "($ & $ & Hws)".
    by rewrite normalise_sealed_words_singleton big_sepS_singleton.
  Qed.

  Lemma close_sealing_map (W : WORLD) (C : CmptName) (o : OType) Po (ws : gset Word) :
    seal_pred o Po -∗
    sealing_map_resource_open W C o Po ws -∗
    ([∗ set] w ∈ (normalise_sealed_words ws), Po (W, C, w)) -∗
    sealing_map_open W C o -∗
    sealing_map W C.
  Proof. rewrite sealing_map_eq sealing_map_open_eq; apply close_sealing_map_def. Qed.

  Lemma close_sealing_map_singleton (W : WORLD) (C : CmptName) (o : OType) Po (w : Word) :
    seal_pred o Po -∗
    sealing_map_resource_open W C o Po {[w]} -∗
    Po (W, C, force_global w) -∗
    sealing_map_open W C o -∗
    sealing_map W C.
  Proof.
    iIntros "Hspred Hseal HPo Hseals".
    iAssert ( [∗ set] w ∈ normalise_sealed_words {[ w ]}, Po (W, C, w) )%I with "[HPo]" as "HPo".
    { by rewrite normalise_sealed_words_singleton big_sepS_singleton. }
    iDestruct (close_sealing_map with "Hspred Hseal HPo Hseals") as "$".
  Qed.

End sealing_interp.
