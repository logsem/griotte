From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules logrel monotone interp_weakening.
From cap_machine Require Import memory_region proofmode.
From cap_machine Require Import world_ghost_theory.


Section Stack_World_Resources.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
  .
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).


  (** * Lemmas about [StackWorldResource], [StackWorldResources] and [StackOpenWorldResources] *)


  (* Length *)
  Lemma StackWorldResources_length (interp : V) (W : WORLD) (C : CmptName) (la : list Addr) (lw : list Word) :
    StackWorldResources interp W C la lw -∗ ⌜ length la = length lw ⌝.
  Proof. iIntros "H"; iApply (big_sepL2_length with "H"). Qed.

  Lemma StackOpenWorldResources_length (interp : V) (W : WORLD) (C : CmptName) (la : list Addr) (lw : list Word) :
    StackOpenWorldResources interp W C la lw -∗ ⌜ length la = length lw ⌝.
  Proof. iIntros "[H _]"; iApply (big_sepL2_length with "H"). Qed.

  (* App *)
  Lemma StackWorldResources_app
    (W : WORLD) ( C : CmptName ) ( la la' : list Addr ) (lv lv' : list Word) :
    length la = length lv ->
    StackWorldResources interp W C (la++la')( lv++lv' ) ⊣⊢
    (StackWorldResources interp W C la lv ∗
     StackWorldResources interp W C la' lv')%I.
  Proof. intros Hlen; rewrite /StackWorldResources.
         iSplit; [iIntros "H" | iIntros "[H1 H2]"].
         - iDestruct (big_sepL2_app' with "H") as "[$ $]"; auto.
         - iApply big_sepL2_app'; last iFrame; auto.
  Qed.

  Lemma StackOpenWorldResources_app
    (W : WORLD) ( C : CmptName ) ( la la' : list Addr ) (lv lv' : list Word) :
    length la = length lv ->
    StackOpenWorldResources interp W C (la++la') (lv++lv') ⊣⊢
    (StackOpenWorldResources interp W C la lv ∗
     StackOpenWorldResources interp W C la' lv')%I.
  Proof. rewrite /StackOpenWorldResources.
         intros Hlen.
         iSplit; [iIntros "[H1 H2]"| iIntros "[ [H1 H1'] [H2 H2'] ]"].
         - iDestruct (big_sepL_app with "H2") as "[$ $]".
           iApply StackWorldResources_app; done.
         - iSplitR "H1' H2'".
           + iApply StackWorldResources_app; auto.
           + iApply big_sepL_app; auto; iFrame.
  Qed.

  (* Zeroing *)
  Lemma StackWorldResource_zero (W : WORLD) (C : CmptName) (a : Addr) (v : Word) :
    StackWorldResource interp W C a v -∗
    StackWorldResource interp W C a (WInt 0).
  Proof.
    iIntros "(%Pa & %pa & HPa & Hmono & $ & ($&#Hzcond&#Hrcond&#Hwcond&%) & $)"; iFrame "#%".
    specialize (H (W,C,v)).
    iSplitR "Hmono".
    + iApply "Hwcond"; iApply interp_int.
    + rewrite /mono_temporary.
      destruct ( decide (isWL pa = true ∨ isDL pa = true) )
      ; iIntros (???) "!>H /="; iApply "Hzcond"; done.
  Qed.

  Lemma StackWorldResources_zeros (W : WORLD) (C : CmptName) (la : list Addr) (lv lv': list Word) :
    length lv' = length la ->
    Forall (λ y : Word, y = WInt 0) lv' ->
    StackWorldResources interp W C la lv -∗
    StackWorldResources interp W C la lv'.
  Proof.
    iIntros (Hzeros Hlen_lv') "H".
    iDestruct ( StackWorldResources_length with "H" ) as "%Hlen_lv".
    iStopProof.
    move: lv lv' Hzeros Hlen_lv Hlen_lv'.
    induction la; iIntros (lv lv' Hlen_lv' Hlen_lv Hzeros ) "H"
    ; destruct lv as [|v lv]; auto
    ; destruct lv' as [|v' lv']; try done.
    simplify_eq.
    apply Forall_cons in Hzeros as [-> Hzeros].
    iDestruct "H" as "[Ha H]".
    iSplitL "Ha"; first by iApply StackWorldResource_zero.
    iApply (IHla lv lv'); eauto.
  Qed.

  Lemma StackOpenWorldResources_zeros (W : WORLD) (C : CmptName) (la : list Addr) (lv lv': list Word) :
    length lv' = length la ->
    Forall (λ y : Word, y = WInt 0) lv' ->
    StackOpenWorldResources interp W C la lv -∗
    StackOpenWorldResources interp W C la lv'.
  Proof.
    iIntros (Hzeros Hlen_lv') "[H $]".
    iDestruct (StackWorldResources_zeros with "H") as "$"; auto.
  Qed.

  (* Get interp *)
  Lemma StackWorldResource_interp W C a w :
    StackWorldResource interp W C a w -∗ interp W C w.
  Proof.
    iIntros "(%Pa & %pa & HPa & ? & ? & (?&?&Hrcond&?&%) & %)".
    iDestruct ("Hrcond" with "HPa") as "HPa'".
    rewrite /load_word.
    destruct ( isDRO pa ) eqn:Hpa.
    { eapply isDRO_flowsto in Hpa; eauto; done. }
    destruct ( isDL pa ) eqn:Hpa'.
    { eapply isDL_flowsto in Hpa'; eauto; done. }
    done.
  Qed.

  (* Derive [StackWorldResource] from [rel] *)
  Lemma StackWorldResource_from_rel_stack W C a :
    rel C a RWL interpC -∗ StackWorldResource interp W C a (WInt 0).
  Proof.
    iIntros "Hrel".
    iExists interp, RWL; cbn. iFrame.
    iSplit; first (iApply interp_int).
    iSplit; first (iApply future_pub_mono_interp_z).
    iSplit; last done.
    iSplit.
    { iIntros (v) "!>".
      iIntros (W0 W1 Hrelated) "Hinterp".
      rewrite /=.
      iApply monotone.interp_monotone; eauto.
    }
    iSplit; first (iApply zcond_interp).
    iSplit; first (iApply rcond_interp).
    iSplit; first (iApply wcond_interp).
    iPureIntro. apply persistent_cond_interp.
  Qed.

  Lemma StackWorldResources_from_rel_stack W C la :
    ([∗ list] a ∈ la, rel C a RWL interpC) -∗
    StackWorldResources interp W C la (replicate (length la) (WInt 0)).
  Proof.
    induction la; [iIntros "H" | iIntros "[Ha H]"]; first done; cbn.
    iDestruct (IHla with "H") as "$".
    iDestruct ( StackWorldResource_from_rel_stack with "Ha" ) as "$".
  Qed.


  (** * Definition [StackRevokedResources] *)

  (** [StackRevokedResources] corresponds to the safety resources of a stack
      that had been revoked and cleared.

      This resources comes hand-to-hand with revoking/reinstating or opening/closing the
      stack region of the world.
      This is mostly bookkeeping resources, and the user would usually only passes it around.
 *)

  Definition StackRevokedResources (W : WORLD) (C : CmptName) (la : list Addr) : iProp Σ :=
    StackWorldResources interp W C la (replicate (length la) (WInt 0)).

  Global Instance StackRevokedResources_Persistent W C la : Persistent (StackRevokedResources W C la).
  Proof. apply _. Qed.

  Lemma StackRevokedResources_app
    (W : WORLD) ( C : CmptName ) ( la la' : list Addr ) :
    StackRevokedResources W C (la++la') ⊣⊢
    (StackRevokedResources W C la ∗
     StackRevokedResources W C la')%I.
  Proof. rewrite /StackRevokedResources length_app replicate_add.
         apply StackWorldResources_app.
         by rewrite length_replicate.
  Qed.

  Lemma StackRevokedResources_mono_priv (W W' : WORLD) (C : CmptName) (la : list Addr) :
    related_sts_priv_world W W' ->
    StackRevokedResources W C la -∗
    StackRevokedResources W' C la.
  Proof.
    iIntros (Hrelated) "H".
    rewrite /StackRevokedResources /StackWorldResources.
    iApply (big_sepL2_impl with "H").
    iModIntro. iIntros (?????) "H".
    apply lookup_replicate in H0 as [-> ?].
    iDestruct "H" as "[%P [%p (HP&#Hmono&#Hrel&(#Hmono'&#Hzcond&#Hwcond&#Hrcond&%Hpers)&%Hp) ] ]"
    ; pose proof (Hpers (W,C, WInt 0))
    ; iDestruct "HP" as "#HP".
    iFrame "∗#%".
    iApply "Hzcond"; done.
  Qed.


  (** Interface for revoked addresses *)
  Definition revoked_addresses (W : WORLD) (la : list Addr) :=
    Forall (λ a, std W !! a = Some Revoked) la.

  Lemma revoked_addresses_app (W : WORLD) (la la' : list Addr) :
    revoked_addresses W (la++la') <-> revoked_addresses W la ∧ revoked_addresses W la'.
  Proof. rewrite /revoked_addresses; apply Forall_app. Qed.

  Lemma revoked_addresses_weaken (W : WORLD) (la la' : list Addr) :
    la' ⊆ la ->
    Forall (λ a, std W !! a = Some Revoked) la ->
    Forall (λ a, std W !! a = Some Revoked) la'.
  Proof.
    intros Hl Hla.
    rewrite Forall_forall in Hla; apply Forall_forall.
    intros a Ha.
    apply Hla.
    by apply Hl.
  Qed.


End Stack_World_Resources.
