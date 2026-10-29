(** Throw-away prototype: the logical relation as one guarded fixpoint over
    threads, with persistent seal predicates of two kinds taking a thread
    argument.

    The cases are cut down: integers, one memory capability case, one
    sentry case, sealed words and seal ranges. A Global word's validity is
    world-free and thread-free; a Local word's validity is read through the
    regions of the thread that holds it. Nothing imports this file. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import saved_prop ghost_map.
From griotte Require Import state_interp_def world_std_sts.

(* TODO: move to program_logic/resources.v *)
#[global] Instance Thread_countable : Countable Thread.
Proof.
  refine (inj_countable'
    (λ th, match th with UserThread n => Some n | CtxSwitch => None end)
    (λ o, match o with Some n => UserThread n | None => CtxSwitch end) _).
  by intros [n|].
Qed.

(** The local world: the Temporary and Revoked keys, and the custom STSs. *)
Record WlWorld := MkWl {
  wl_std : gmap LAddr region_type;
  wl_loc : STS_states;
  wl_rel : STS_rels;
}.

#[global] Instance WlWorld_empty : Empty WlWorld := MkWl ∅ ∅ ∅.

Definition wl_related_pub (W W' : WlWorld) : Prop :=
  related_sts_std_pub (wl_std W) (wl_std W') ∧
  related_sts_pub (wl_loc W) (wl_loc W') (wl_rel W) (wl_rel W').

Lemma wl_related_pub_refl W : wl_related_pub W W.
Proof. split; [apply related_sts_std_pub_refl | apply related_sts_pub_refl]. Qed.

Lemma wl_related_pub_trans W1 W2 W3 :
  wl_related_pub W1 W2 → wl_related_pub W2 W3 → wl_related_pub W1 W3.
Proof.
  intros [Hstd12 Hloc12] [Hstd23 Hloc23]. split.
  - by eapply related_sts_std_pub_trans.
  - by eapply related_sts_pub_trans.
Qed.

(** A Temporary key stays Temporary along a public step. *)
Lemma wl_related_pub_Temporary W W' k :
  wl_related_pub W W' →
  wl_std W !! k = Some Temporary →
  wl_std W' !! k = Some Temporary.
Proof.
  intros [ [Hdom Hrel] _] Hk.
  assert (is_Some (wl_std W' !! k)) as [ρ Hρ].
  { apply elem_of_dom, Hdom. rewrite elem_of_dom. by eexists. }
  rewrite Hρ. f_equal. eapply std_rel_pub_rtc_Temporary; [done|]. by eapply Hrel.
Qed.

(** The kind of an otype's seal predicate. *)
Inductive seal_kind := SealGlobal | SealLocal.

(** The threads that may run in a compartment. *)
Class CmptThreads `{Cname : CmptNameG} := {
  cmpt_threads : CmptName → gset Thread;
}.
#[export] Hint Mode CmptThreads - : typeclass_instances.

(** Ghost names of the prototype: one region map of Global keys per
    compartment, one of Local keys per thread and compartment, one seal map. *)
Class protoG `{Cname : CmptNameG} Σ := ProtoG {
  proto_relG :: ghost_mapG Σ LAddr (gname * Perm);
  proto_sealG :: ghost_mapG Σ OType (seal_kind * gname);
  proto_pred_gG :: savedPredG Σ (CmptName * LWord);
  proto_pred_lG :: savedPredG Σ (WlWorld * CmptName * LWord);
  proto_pred_sG :: savedPredG Σ (Thread * WlWorld * CmptName * LWord);
  γrel_g : CmptName → gname;
  γrel_l : Thread → CmptName → gname;
  γseal : gname;
}.
#[export] Hint Mode protoG - - : typeclass_instances.

Section proto.
  Context
    {Σ : gFunctors}
    {ceriseb : ceriseBaseG Σ}
    {Cname : CmptNameG}
    {protog : protoG Σ}
    {cthreads : CmptThreads}
    {CL : CritLink Σ}
    `{MP : MachineParameters}.
  (** The thread whose validity stands for the world-free one. *)
  Context (th0 : Thread).

  Notation V := (WlWorld -d> leibnizO CmptName -d> leibnizO LWord -d> iPropO Σ).
  Notation TV := (Thread -d> V).
  Implicit Types W : WlWorld.
  Implicit Types C : CmptName.
  Implicit Types w : LWord.
  Implicit Types I : TV.

  (** ** Thread membership *)

  Definition thread_in_def (t : Thread) C : iProp Σ := ⌜t ∈ cmpt_threads C⌝.
  #[local] Definition thread_in_aux : seal (@thread_in_def). Proof. by eexists. Qed.
  Definition thread_in := thread_in_aux.(unseal).
  #[local] Definition thread_in_unseal : @thread_in = @thread_in_def :=
    thread_in_aux.(seal_eq).

  #[global] Instance thread_in_persistent t C : Persistent (thread_in t C).
  Proof. rewrite thread_in_unseal. apply _. Qed.

  (** ** Region relations of the two parts *)

  Definition rel_g_def C (k : LAddr) (p : Perm) (φ : CmptName * LWord → iProp Σ) : iProp Σ :=
    ∃ γ, k ↪[γrel_g C]□ (γ, p) ∗ saved_pred_own γ DfracDiscarded φ.
  #[local] Definition rel_g_aux : seal (@rel_g_def). Proof. by eexists. Qed.
  Definition rel_g := rel_g_aux.(unseal).
  #[local] Definition rel_g_unseal : @rel_g = @rel_g_def := rel_g_aux.(seal_eq).

  Definition rel_l_def (t : Thread) C (k : LAddr) (p : Perm)
      (φ : WlWorld * CmptName * LWord → iProp Σ) : iProp Σ :=
    ∃ γ, k ↪[γrel_l t C]□ (γ, p) ∗ saved_pred_own γ DfracDiscarded φ.
  #[local] Definition rel_l_aux : seal (@rel_l_def). Proof. by eexists. Qed.
  Definition rel_l := rel_l_aux.(unseal).
  #[local] Definition rel_l_unseal : @rel_l = @rel_l_def := rel_l_aux.(seal_eq).

  #[global] Instance rel_g_persistent C k p φ : Persistent (rel_g C k p φ).
  Proof. rewrite rel_g_unseal. apply _. Qed.
  #[global] Instance rel_l_persistent t C k p φ : Persistent (rel_l t C k p φ).
  Proof. rewrite rel_l_unseal. apply _. Qed.

  (** ** Seal predicates *)

  Definition seal_pred_def (o : OType) (κ : seal_kind)
      (P : Thread * WlWorld * CmptName * LWord → iProp Σ) : iProp Σ :=
    ∃ γ, o ↪[γseal]□ (κ, γ) ∗ saved_pred_own γ DfracDiscarded P.
  #[local] Definition seal_pred_aux : seal (@seal_pred_def). Proof. by eexists. Qed.
  Definition seal_pred := seal_pred_aux.(unseal).
  #[local] Definition seal_pred_unseal : @seal_pred = @seal_pred_def :=
    seal_pred_aux.(seal_eq).

  #[global] Instance seal_pred_persistent o κ P : Persistent (seal_pred o κ P).
  Proof. rewrite seal_pred_unseal. apply _. Qed.

  Lemma seal_pred_agree o κ1 κ2 P1 P2 x :
    seal_pred o κ1 P1 -∗
    seal_pred o κ2 P2 -∗
    ⌜κ1 = κ2⌝ ∗ ▷ (P1 x ≡ P2 x).
  Proof.
    rewrite seal_pred_unseal.
    iIntros "(%γ1 & Ho1 & HP1) (%γ2 & Ho2 & HP2)".
    iCombine "Ho1 Ho2" gives %[_ Heq]. simplify_eq.
    iSplit; first done.
    by iApply (saved_pred_agree with "HP1 HP2").
  Qed.

  (** The conditions on a seal predicate, by kind: a Global-kind predicate is
      constant in the thread and the world; a Local-kind one is monotone
      along public steps, constant on Global words, and stable by
      [lborrow]. *)
  Definition seal_kind_ok (κ : seal_kind) C
      (P : Thread * WlWorld * CmptName * LWord → iProp Σ) : iProp Σ :=
    ⌜∀ x, Persistent (P x)⌝ ∗
    match κ with
    | SealGlobal => □ ∀ t t' W W' w, P (t, W, C, w) -∗ P (t', W', C, w)
    | SealLocal =>
        (□ ∀ t W W' w, ⌜wl_related_pub W W'⌝ → P (t, W, C, w) -∗ P (t, W', C, w)) ∗
        (□ ∀ t t' W W' w, ⌜isGlobalWord w.(lw)⌝ → P (t, W, C, w) -∗ P (t', W', C, w)) ∗
        (□ ∀ t W w, P (t, W, C, w) -∗ P (t, W, C, lborrow w))
    end.

  #[global] Instance seal_kind_ok_persistent κ C P : Persistent (seal_kind_ok κ C P).
  Proof. destruct κ; apply _. Qed.

  Definition norm (κ : seal_kind) w : LWord :=
    if κ is SealGlobal then lforce_global w else w.

  (** ** Validity, before the fixpoint *)

  Definition full_map (regs : LReg) : iProp Σ := ∀ r : RegName, ⌜is_Some (regs !! r)⌝.

  (** Safe execution of thread [t] from [wpc], with registers valid for [t]. *)
  Definition interp_expr I (t : Thread) W C (wpc : LWord) : iProp Σ :=
    ∀ regs,
      (full_map regs ∧ ∀ (r : RegName) (v : LWord), ⌜regs !! r = Some v⌝ → I t W C v) ∗
      PC ↦ₚ[t] wpc ∗
      regs[t] regs ∗
      na_own (tpool t) ⊤ -∗
      safe[t].

  (** Memory capabilities: a Global one reads Global regions, valid for
      every thread of [C] in every world; a Local one reads Temporary
      regions of the holder's thread. *)
  Definition interp_cap I (t : Thread) W C (g : Locality) (b e : Addr) : iProp Σ :=
    match g with
    | Global =>
        [∗ list] a ∈ finz.seq_between b e,
          ∃ (p' : Perm) (P : CmptName * LWord → iProp Σ),
            rel_g C (LNonHeap a) p' P ∗
            ▷ (□ ∀ w, P (C, w) -∗ ∀ t' W', thread_in t' C -∗ I t' W' C w) ∗
            ▷ (□ ∀ t' W' w, thread_in t' C -∗ I t' W' C w -∗ P (C, w))
    | Local =>
        [∗ list] a ∈ finz.seq_between b e,
          ∃ (p' : Perm) (P : WlWorld * CmptName * LWord → iProp Σ),
            rel_l t C (LNonHeap a) p' P ∗
            ⌜wl_std W !! LNonHeap a = Some Temporary⌝ ∗
            ▷ (□ ∀ W' w, P (W', C, w) -∗ I t W' C w) ∗
            ▷ (□ ∀ W' w, I t W' C w -∗ P (W', C, w))
    end.

  (** Sentries: a Global one runs in every thread of [C] and every world; a
      Local one in the holder's public futures. *)
  Definition interp_sentry I (t : Thread) W C (p : Perm) (g : Locality) (b e a : Addr)
      (π : option AId) : iProp Σ :=
    match g with
    | Global =>
        □ ∀ t', thread_in t' C -∗ ∀ W', ▷ interp_expr I t' W' C (Cap p Global b e a @@? π)
    | Local =>
        □ ∀ W', ⌜wl_related_pub W W'⌝ → ▷ interp_expr I t W' C (Cap p Local b e a @@? π)
    end.

  (** Sealed words, read at the holder's thread [t]. *)
  Definition interp_sb (t : Thread) W C (o : OType) w : iProp Σ :=
    ∃ κ P, seal_pred o κ P ∗ seal_kind_ok κ C P ∗ ▷ P (t, W, C, norm κ w).

  (** Seal authority. *)
  Definition anchored (t : Thread) W C (A : list LAddr) : iProp Σ :=
    [∗ list] k ∈ A, ∃ p φ, rel_l t C k p φ ∗ ⌜wl_std W !! k = Some Temporary⌝.

  Definition seal_cond_k I (t : Thread) (g : Locality) W κ
      (P : Thread * WlWorld * CmptName * LWord → iProp Σ) C : iProp Σ :=
    match g with
    | Global => □ ∀ t', thread_in t' C -∗ ∀ W' w, I t' W' C w -∗ P (t', W', C, norm κ w)
    | Local => □ ∀ W', ⌜wl_related_pub W W'⌝ → ∀ w, I t W' C w -∗ P (t, W', C, norm κ w)
    end.

  Definition unseal_cond_k I (t : Thread) (g : Locality) W κ
      (P : Thread * WlWorld * CmptName * LWord → iProp Σ) C : iProp Σ :=
    match g with
    | Global => □ ∀ t', thread_in t' C -∗ ∀ W' w, P (t', W', C, norm κ w) -∗ I t' W' C w
    | Local =>
        □ ∀ W', ⌜wl_related_pub W W'⌝ → ∀ w, P (t, W', C, norm κ w) -∗ I t W' C (lborrow w)
    end.

  Definition interp_sr I (t : Thread) W C (p : SealPerms) (g : Locality) (b e : OType)
      : iProp Σ :=
    (if g is Local then ∃ A, anchored t W C A else True) ∗
    [∗ list] o ∈ finz.seq_between b e,
      ∃ κ P, seal_pred o κ P ∗ seal_kind_ok κ C P ∗
        (if permit_seal p then ▷ seal_cond_k I t g W κ P C else True) ∗
        (if permit_unseal p then ▷ unseal_cond_k I t g W κ P C else True).

  Definition interp1 (I : TV) : TV := λ t W C w,
    (if get_tag w.(lw) then
       match w.(lw) with
       | WInt _ => True
       | WCap _ _ g b e _ => interp_cap I t W C g b e
       | WSealRange _ p g b e _ => interp_sr I t W C p g b e
       | WSentry _ _ p g b e a => interp_sentry I t W C p g b e a w.(lprov)
       | WSealed o sb => interp_sb t W C o (WSealable sb @@? w.(lprov))
       end
     else True)%I.

  (** ** Contractiveness and the fixpoint *)

  #[global] Instance interp_expr_ne n :
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n) interp_expr.
  Proof.
    intros I1 I2 HI t ? <- W ? <- C ? <- wpc ? <-. rewrite /interp_expr.
    repeat f_equiv; apply HI.
  Qed.

  #[global] Instance interp1_contractive : Contractive interp1.
  Proof.
    intros n I1 I2 HI t W C [w π]. rewrite /interp1 /=.
    destruct (get_tag w); last done.
    destruct w as [z | [tg p g b e a | tg p g b e a] | k tg p g b e a | o sb]; try done.
    - rewrite /interp_cap; destruct g; repeat (f_contractive || f_equiv); apply HI.
    - rewrite /interp_sr /seal_cond_k /unseal_cond_k.
      f_equiv. apply big_sepL_ne; intros i o Ho. do 2 (apply bi.exist_ne; intros ?).
      do 2 (apply bi.sep_ne; [done|]).
      apply bi.sep_ne; [destruct (permit_seal p) | destruct (permit_unseal p)]; try done;
        f_contractive; destruct g; repeat f_equiv; apply HI.
    - rewrite /interp_sentry; destruct g; repeat (f_contractive || f_equiv); apply HI.
  Qed.

  Definition interp_def : TV := fixpoint interp1.
  #[local] Definition interp_aux : seal (@interp_def). Proof. by eexists. Qed.
  Definition interp := interp_aux.(unseal).
  #[local] Definition interp_unseal : @interp = @interp_def := interp_aux.(seal_eq).

  Lemma interp_unfold t : interp t ≡ interp1 interp t.
  Proof. rewrite interp_unseal. apply (fixpoint_unfold interp1). Qed.

  Lemma interp_unfold_app t W C w : interp t W C w ⊣⊢ interp1 interp t W C w.
  Proof. apply (interp_unfold t). Qed.

  (** ** Persistence *)

  #[global] Instance interp_sb_persistent t W C o w : Persistent (interp_sb t W C o w).
  Proof.
    rewrite /Persistent /interp_sb.
    iIntros "(%κ & %P & #Hs & #Hok & HP)".
    iDestruct "Hok" as "[%Hpers Hok']".
    iDestruct "HP" as "#HP". iModIntro. iExists κ, P. by iFrame "#".
  Qed.

  #[global] Instance interp1_persistent I t W C w : Persistent (interp1 I t W C w).
  Proof.
    rewrite /interp1. destruct (get_tag _); last apply _.
    destruct (lw w) as [z | [tg p g b e a | tg p g b e a] | k tg p g b e a | o sb];
      try apply _.
    - rewrite /interp_cap. destruct g; apply _.
    - rewrite /interp_sr /seal_cond_k /unseal_cond_k.
      destruct g, (permit_seal p), (permit_unseal p); apply _.
    - rewrite /interp_sentry. destruct g; apply _.
  Qed.

  #[global] Instance interp_persistent t W C w : Persistent (interp t W C w).
  Proof. rewrite interp_unfold_app. apply _. Qed.

  (** At a fixed thread. *)
  #[global] Instance interp_th0_persistent W C w : Persistent (interp th0 W C w).
  Proof. apply _. Qed.

  (** ** Global words are world-free and thread-free *)

  (** A sealed word whose payload is Global: the predicate is read at any
      thread and world, through [seal_kind_ok]. *)
  Lemma sealed_global_world_free t t' W W' C o w :
    isGlobalWord w.(lw) = true →
    interp_sb t W C o w -∗ interp_sb t' W' C o w.
  Proof.
    iIntros (Hg) "(%κ & %P & #Hs & #Hok & HP)".
    iExists κ, P. iFrame "Hs Hok". iNext.
    destruct κ.
    - iDestruct "Hok" as "[_ #Hconst]". by iApply ("Hconst" $! t t' W W').
    - iDestruct "Hok" as "(_ & _ & #Hglob & _)".
      iApply ("Hglob" $! t t' W W' w with "[%] HP"). by rewrite Hg.
  Qed.

  Lemma interp_global_thread_world_free t t' W W' C w :
    isGlobalWord w.(lw) = true →
    interp t W C w ⊣⊢ interp t' W' C w.
  Proof.
    intros Hg.
    assert (∀ t t' W W', interp t W C w ⊢ interp t' W' C w) as Hdir;
      last (apply bi.equiv_entails_2; apply Hdir).
    clear t t' W W'. intros t t' W W'.
    rewrite !interp_unfold_app /interp1.
    destruct w as [w π]; cbn in Hg |- *.
    destruct w as [z | [tg p g b e a | tg p g b e a] | k tg p g b e a | o sb];
      cbn in Hg |- *; try done.
    1-3: rewrite /interp_cap /interp_sr /seal_cond_k /unseal_cond_k /interp_sentry;
      destruct tg, g; done.
    destruct (get_tag_sealable sb); last done.
    iIntros "H". by iApply (sealed_global_world_free t t' W W' with "H").
  Qed.

  (** The validity of Global words, without thread nor world. *)
  Definition interp_g C w : iProp Σ := interp th0 ∅ C w.

  Lemma interp_global_factor t W C w :
    isGlobalWord w.(lw) = true →
    interp t W C w ⊣⊢ interp_g C w.
  Proof. intros Hg. by apply interp_global_thread_world_free. Qed.

  (** ** Public monotonicity *)

  Lemma interp_sb_mono_pub t W W' C o w :
    wl_related_pub W W' →
    interp_sb t W C o w -∗ interp_sb t W' C o w.
  Proof.
    iIntros (Hrel) "(%κ & %P & #Hs & #Hok & HP)".
    iExists κ, P. iFrame "Hs Hok". iNext.
    destruct κ.
    - iDestruct "Hok" as "[_ #Hconst]". by iApply ("Hconst" $! t t W W').
    - iDestruct "Hok" as "(_ & #Hmono & _)". by iApply ("Hmono" $! t W W' with "[//] HP").
  Qed.

  Lemma anchored_mono_pub t W W' C A :
    wl_related_pub W W' →
    anchored t W C A -∗ anchored t W' C A.
  Proof.
    iIntros (Hrel) "HA". iApply (big_sepL_impl with "HA").
    iIntros "!>" (i k Hk) "(%p & %φ & Hrel & %Htemp)".
    iExists p, φ. iFrame. iPureIntro. by eapply wl_related_pub_Temporary.
  Qed.

  Lemma interp_mono_pub t W W' C w :
    wl_related_pub W W' →
    interp t W C w -∗ interp t W' C w.
  Proof.
    iIntros (Hrel) "Hw". rewrite !interp_unfold_app /interp1.
    destruct (get_tag _); last done.
    destruct (lw w) as [z | [tg p g b e a | tg p g b e a] | k tg p g b e a | o sb];
      try done.
    - rewrite /interp_cap. destruct g; first done.
      iApply (big_sepL_impl with "Hw").
      iIntros "!>" (i a' Ha') "(%p' & %P & Hrel & %Htemp & HR & HW)".
      iExists p', P. iFrame. iPureIntro. by eapply wl_related_pub_Temporary.
    - rewrite /interp_sr. iDestruct "Hw" as "[HA Hos]". iSplitL "HA".
      { destruct g; first done.
        iDestruct "HA" as (A) "HA". iExists A. by iApply anchored_mono_pub. }
      iApply (big_sepL_impl with "Hos").
      iIntros "!>" (i o Ho) "(%κ & %P & Hs & Hok & Hseal & Hunseal)".
      iExists κ, P. iFrame "Hs Hok".
      destruct g; first iFrame.
      rewrite /seal_cond_k /unseal_cond_k. iSplitL "Hseal".
      + destruct (permit_seal p); last done.
        iNext. iDestruct "Hseal" as "#Hseal". iIntros "!>" (W'' Hrel'').
        iApply "Hseal". iPureIntro. by eapply wl_related_pub_trans.
      + destruct (permit_unseal p); last done.
        iNext. iDestruct "Hunseal" as "#Hunseal". iIntros "!>" (W'' Hrel'').
        iApply "Hunseal". iPureIntro. by eapply wl_related_pub_trans.
    - rewrite /interp_sentry. destruct g; first done.
      iDestruct "Hw" as "#Hw". iIntros "!>" (W'' Hrel'').
      iApply "Hw". iPureIntro. by eapply wl_related_pub_trans.
    - by iApply interp_sb_mono_pub.
  Qed.

  (** ** Two threads, one Local-kind otype *)

  (** A Local-kind predicate anchored at [k]: a Local word is acceptable
      while the holder's thread has [k] Temporary; no Global word is. *)
  Definition P_anchor (k : LAddr) (x : Thread * WlWorld * CmptName * LWord) : iProp Σ :=
    let '(t, Wx, Cx, v) := x in
    (if isGlobalWord v.(lw) then False
     else ∃ p φ, rel_l t Cx k p φ ∗ ⌜wl_std Wx !! k = Some Temporary⌝)%I.

  #[global] Instance P_anchor_persistent k x : Persistent (P_anchor k x).
  Proof.
    destruct x as [ [ [t Wx] Cx] v]. rewrite /P_anchor.
    destruct (isGlobalWord _); apply _.
  Qed.

  Lemma isGlobalWord_borrow (w : Word) : isGlobalWord (borrow w) = false.
  Proof.
    destruct w as [z | [tg p g b e a | tg p g b e a] | k tg p g b e a | o [tg p g b e a | tg p g b e a] ];
      cbn; by rewrite ?andb_false_r.
  Qed.

  Lemma P_anchor_kind_ok k C : ⊢ seal_kind_ok SealLocal C (P_anchor k).
  Proof.
    iSplit; first (iPureIntro; apply _).
    iSplit; [|iSplit].
    - iIntros "!>" (t W W' w Hrel). rewrite /P_anchor.
      destruct (isGlobalWord _); first done.
      iIntros "(%p & %φ & Hrel & %Htemp)". iExists p, φ. iFrame.
      iPureIntro. by eapply wl_related_pub_Temporary.
    - iIntros "!>" (t t' W W' w Hg). rewrite /P_anchor.
      destruct (isGlobalWord _); [by iIntros "[]" | done].
    - iIntros "!>" (t W w). rewrite /P_anchor. cbn [lborrow lift_word lw].
      rewrite isGlobalWord_borrow.
      destruct (isGlobalWord _); [by iIntros "[]" | by iIntros "H"].
  Qed.

  (** The same Local sealed word is valid for two threads, each through its
      own anchor: the thread argument of the seal predicate names the
      holder's regions. *)
  Lemma two_thread_anchor o k t1 t2 W1 W2 C p1 p2 φ1 φ2 w :
    isGlobalWord w.(lw) = false →
    seal_pred o SealLocal (P_anchor k) -∗
    rel_l t1 C k p1 φ1 -∗
    ⌜wl_std W1 !! k = Some Temporary⌝ -∗
    rel_l t2 C k p2 φ2 -∗
    ⌜wl_std W2 !! k = Some Temporary⌝ -∗
    interp_sb t1 W1 C o w ∗ interp_sb t2 W2 C o w.
  Proof.
    iIntros (Hl) "#Hs #Hr1 %Ht1 #Hr2 %Ht2".
    iPoseProof (P_anchor_kind_ok k C) as "#Hok".
    iSplit; iExists SealLocal, (P_anchor k); iFrame "Hs Hok"; iNext;
      rewrite /= /P_anchor Hl; iExists _, _; by iFrame "#".
  Qed.

  (** The validity of a sealed word at [t2] needs [t2]'s anchor: what
      [t1] holds about the same key does not transfer. *)
  Lemma interp_sb_anchor_elim o k t W C w :
    seal_pred o SealLocal (P_anchor k) -∗
    interp_sb t W C o w -∗
    ▷ ∃ p φ, rel_l t C k p φ ∗ ⌜wl_std W !! k = Some Temporary⌝.
  Proof.
    iIntros "#Hs (%κ & %P & #Hs' & _ & HP)".
    iDestruct (seal_pred_agree _ _ _ _ _ (t, W, C, norm κ w) with "Hs Hs'") as "[<- Heq]".
    iNext. iRewrite -"Heq" in "HP". rewrite /= /P_anchor.
    destruct (isGlobalWord _); [done | iFrame].
  Qed.

  (** The clauses of a Local kind make it carry, on a Global word it
      accepts, the Local borrow of that word at every thread and world. An
      anchored predicate that accepts Global words [Q] therefore also
      accepts their borrows without anchor. *)
  Lemma borrow_idemp (w : Word) : borrow (borrow w) = borrow w.
  Proof.
    by destruct w as [z | [tg p g b e a | tg p g b e a] | k tg p g b e a | o [tg p g b e a | tg p g b e a] ].
  Qed.

  Definition P_lent (k : LAddr) (Q : CmptName * LWord → iProp Σ)
      (x : Thread * WlWorld * CmptName * LWord) : iProp Σ :=
    let '(t, Wx, Cx, v) := x in
    (if isGlobalWord v.(lw) then Q (Cx, v)
     else (∃ p φ, rel_l t Cx k p φ ∗ ⌜wl_std Wx !! k = Some Temporary⌝) ∨
          (∃ v0, ⌜isGlobalWord v0.(lw) = true ∧ v = lborrow v0⌝ ∗ Q (Cx, v0)))%I.

  Lemma P_lent_kind_ok k C Q :
    (∀ x, Persistent (Q x)) →
    ⊢ seal_kind_ok SealLocal C (P_lent k Q).
  Proof.
    intros HQ.
    iSplit.
    { iPureIntro. intros [ [ [t Wx] Cx] v]. rewrite /P_lent. destruct (isGlobalWord _); apply _. }
    iSplit; [|iSplit].
    - iIntros "!>" (t W W' w Hrel). rewrite /P_lent.
      destruct (isGlobalWord _); first by iIntros "H".
      iIntros "[(%p & %φ & Hrel & %Htemp) | Hb]"; last by iRight.
      iLeft. iExists p, φ. iFrame. iPureIntro. by eapply wl_related_pub_Temporary.
    - iIntros "!>" (t t' W W' w Hg). rewrite /P_lent.
      destruct (isGlobalWord _); [by iIntros "H" | done].
    - iIntros "!>" (t W w). rewrite /P_lent. cbn [lborrow lift_word lw].
      rewrite isGlobalWord_borrow.
      destruct (isGlobalWord (lw w)) eqn:Hg.
      + iIntros "HQ". iRight. iExists w. by iFrame.
      + iIntros "[(%p & %φ & Hrel & %Htemp) | (%v0 & [%Hg0 ->] & HQ)]".
        * iLeft. iExists p, φ. by iFrame.
        * iRight. iExists v0. iFrame. iPureIntro. split; first done.
          destruct v0 as [v0 π]. rewrite /lborrow /lift_word /=. by rewrite borrow_idemp.
  Qed.
End proto.
