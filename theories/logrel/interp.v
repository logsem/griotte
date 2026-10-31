From iris.proofmode Require Import proofmode.
From griotte Require Export logrel_cont.
Import uPred.

(** The fixpoint of the logical relation, over the family of the threads'
    relations. A Global word's validity holds for every thread of its
    compartment: its sentries run, and its read conditions hold, at each
    such thread [t']. A Local word's validity is at the holder's thread. *)
Section logrel_fix.

  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ}
    {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    {cthreads : CmptThreads}
    {CL : CritLink Σ}
    `{MP: MachineParameters}
  .
  #[local] Notation V := (interpO Σ).
  #[local] Notation TV := (Thread -d> interpO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  #[local] Lemma dist_later_app n (I1 I2 : TV) (t : Thread) :
    dist_later n I1 I2 → dist_later n (I1 t) (I2 t).
  Proof. intros [HI]. constructor. intros m Hm. apply (HI m Hm). Qed.

  (** The per-address part of a memory capability's validity, at the
      holder's thread [th]. The read condition is by the capability's
      locality, the write condition by its write-local permission. *)
  Definition interp_cap_body (interp : TV) (th : Thread)
      (W : WORLD) (C : CmptName) (p : Perm) (g : Locality)
      (b e : Addr) (π : option AId) : iProp Σ :=
    ([∗ list] a ∈ finz.seq_between b e,
      ∃ (p' : Perm) (P : V),
        ⌜PermFlowsTo p p'⌝
        ∧ ⌜persistent_cond P⌝
        ∧ region_rel (th := th) W C (addr_key π a) p' P p g
        ∧ ▷ zcond P C
        ∧ (if readAllowed p'
           then ▷ (if isGlobal g then rcond_g P C p' interp else rcond_l P C p' (interp th))
           else True)
        ∧ (if writeAllowed p'
           then ▷ (if isWL p then wcond_wl P C (interp th) else wcond_nwl P C (interp th))
           else True))%I.

  #[global] Instance interp_cap_body_contractive th W C p g b e π :
    Contractive (λ interp : TV, interp_cap_body interp th W C p g b e π).
  Proof.
    intros n I1 I2 HI. rewrite /interp_cap_body. solve_contractive.
  Qed.

  #[global] Instance interp_cap_body_persistent interp th W C p g b e π :
    Persistent (interp_cap_body interp th W C p g b e π).
  Proof. apply _. Qed.

  Lemma interp_cap_body_eq interp th W C p g b e π :
    interp_cap_body interp th W C p g b e π ≡
    ([∗ list] a ∈ finz.seq_between b e,
      ∃ (p' : Perm) (P : V),
        ⌜PermFlowsTo p p'⌝
        ∗ ⌜persistent_cond P⌝
        ∗ region_rel (th := th) W C (addr_key π a) p' P p g
        ∗ ▷ zcond P C
        ∗ (if readAllowed p'
           then ▷ (if isGlobal g then rcond_g P C p' interp else rcond_l P C p' (interp th))
           else True)
        ∗ (if writeAllowed p'
           then ▷ (if isWL p then wcond_wl P C (interp th) else wcond_nwl P C (interp th))
           else True))%I.
  Proof.
    rewrite /interp_cap_body.
    apply big_sepL_proper; intros k a' Ha'.
    do 3 f_equiv. intros P.
    by rewrite !bi.persistent_and_sep.
  Qed.

  (** Interp for memory capability. *)
  Program Definition interp_cap (interp : TV) (th : Thread) : V :=
    λne W C w, (match w.(lw) with
              | WCap t (O _ _) _ _ _ _
              | WCap t (BPerm XSR _ _ _) _ _ _ _ (* XRS capabilities are never safe-to-share *)
              | WCap t (BPerm _ WL _ _) Global _ _ _ (* WL Global capabilities are never safe-to-share *)
                => False
              | WCap t p g b e a =>
                  interp_cap_body interp th W C p g b e w.(lprov)
                  ∗ ⌜disjoint_from_mmio b e⌝ ∗ heap_cap_ok p b e w.(lprov)
              | _ => False
              end)%I.
  Solve All Obligations with auto;solve_proper.

  (** Interp for sentry in [enter_cond]: a Global sentry runs at every
      thread of [C], a Local one at the holder's thread [th]. *)
  Program Definition interp_sentry (interp : TV) (th : Thread) : V :=
    λne W C w, (match w.(lw) with
                | WSentry k t p g b e a =>
                    ⌜not_heap_range b e⌝ ∗
                    (if isGlobal g
                     then □ ∀ t', thread_in t' C -∗
                            enter_cond (th := t') W C p g b e a w.(lprov) (interp t')
                     else □ enter_cond (th := th) W C p g b e a w.(lprov) (interp th))
                | _ => False
                end)%I.
  Solve All Obligations with solve_proper.

  (** Interp for sealing capability: its conditions take no thread. *)
  Program Definition interp_sr (interp : TV) : V :=
    λne W C w, (match w.(lw) with
    | WSealRange t p g b e a =>
    (if permit_seal p then safe_to_seal W C interp b e else True)
    ∗ (if permit_unseal p then safe_to_unseal W C interp b e else True)
    | _ => False end ) %I.
  Solve All Obligations with solve_proper.

  (** Definition of interp, pre-fixpoint, at the thread [th] that holds the
      word. Untagged words are safe data. Only tagged words use the
      structural authority predicates above. *)
  Program Definition interp1 (interp : TV) : TV := λ th,
    (λne W C w,
    if get_tag w.(lw) then match w.(lw) return _ with
    | WInt _ => interp_z W C w
    | WCap t (O _ _) g b e a => interp_cap_O (th := th) W C w
    | WCap t _ g b e a => interp_cap interp th W C w
    | WSentry k t p g b e a => interp_sentry interp th W C w
    | WSealRange t p g b e a => interp_sr interp W C w
    | WSealed o sb => interp_sb (th := th) W C o (WSealable sb @@? w.(lprov))
    end else True)%I.
  Solve All Obligations with solve_proper.

  (** To be able to use the fixpoint combinator to define [interp],
      we need to show that all case of [interp] are contractive. *)
  #[global] Instance interp_sentry_contractive th :
    Contractive (λ interp : TV, interp_sentry interp th).
  Proof.
    intros n x y Hdist W C [w π].
    destruct_word w; [reflexivity..| |reflexivity].
    change (dist n
      (⌜not_heap_range b e⌝ ∗
        (if isGlobal g
         then □ ∀ t', thread_in t' C -∗ enter_cond (th := t') W C sd g b e a π (x t')
         else □ enter_cond (th := th) W C sd g b e a π (x th)))%I
      (⌜not_heap_range b e⌝ ∗
        (if isGlobal g
         then □ ∀ t', thread_in t' C -∗ enter_cond (th := t') W C sd g b e a π (y t')
         else □ enter_cond (th := th) W C sd g b e a π (y th)))%I).
    f_equiv. destruct (isGlobal g).
    - do 4 f_equiv. by apply enter_cond_contractive, dist_later_app.
    - f_equiv. by apply enter_cond_contractive, dist_later_app.
  Qed.

  #[global] Instance interp_cap_contractive th :
    Contractive (λ interp : TV, interp_cap interp th).
  Proof.
    intros n x y Hdist W C [w π].
    destruct_word w; try reflexivity.
    destruct c as [rx wp dl dro].
    destruct rx, wp, g; try reflexivity.
    all: match goal with
    | |- context [WCap _ ?p ?g _ _ _] =>
        change (dist n
          (interp_cap_body x th W C p g b e π ∗
            ⌜disjoint_from_mmio b e⌝ ∗ heap_cap_ok p b e π)%I
          (interp_cap_body y th W C p g b e π ∗
            ⌜disjoint_from_mmio b e⌝ ∗ heap_cap_ok p b e π)%I);
        f_equiv; exact (interp_cap_body_contractive th W C p g b e π n x y Hdist)
    end.
  Qed.

  #[global] Instance interp_sr_contractive :
    Contractive (interp_sr).
  Proof.
    intros n x y Hdist W C [w π].
    destruct_word w; try reflexivity.
    change (dist n
      ((if permit_seal sr then safe_to_seal W C x b e else True) ∗
       (if permit_unseal sr then safe_to_unseal W C x b e else True))%I
      ((if permit_seal sr then safe_to_seal W C y b e else True) ∗
       (if permit_unseal sr then safe_to_unseal W C y b e else True))%I).
    apply bi.sep_ne.
    - destruct (permit_seal sr); last done. rewrite /safe_to_seal.
      apply big_sepL_ne; intros i o Ho. do 2 (apply bi.exist_ne; intros ?).
      do 2 (apply bi.sep_ne; [done|]). by apply seal_contractive.
    - destruct (permit_unseal sr); last done. rewrite /safe_to_unseal.
      apply big_sepL_ne; intros i o Ho. do 2 (apply bi.exist_ne; intros ?).
      do 2 (apply bi.sep_ne; [done|]). by apply unseal_contractive.
  Qed.

  #[global] Instance interp1_contractive :
    Contractive (interp1).
  Proof.
    intros n x y Hdistn th W C [w π].
    rewrite /interp1 /=.
    destruct (get_tag w); last reflexivity.
    destruct_word w; [reflexivity|..].
    - pose proof (interp_cap_contractive th n x y Hdistn W C (WCap t c g b e a @@? π)) as Hcap.
      destruct c as [rx wp dl dro].
      destruct rx, wp; try reflexivity;
        exact Hcap.
    - exact (interp_sr_contractive n x y Hdistn W C (WSealRange t sr g b e a @@? π)).
    - exact (interp_sentry_contractive th n x y Hdistn W C (WSentry k t sd g b e a @@? π)).
    - reflexivity.
  Qed.

  (** Definition of the family [interp_fam] via the fixpoint combinator. *)
  Definition interp_def : TV := fixpoint interp1.
  #[local] Definition interp_aux : seal (@interp_def). Proof. by eexists. Qed.
  Definition interp_fam := interp_aux.(unseal).
  #[local] Definition interp_fam_unseal : @interp_fam = @interp_def := interp_aux.(seal_eq).

  Lemma interp_fam_unfold (th : Thread) (W : WORLD) (C : CmptName) (w : leibnizO LWord) :
    interp_fam th W C w ≡ interp1 interp_fam th W C w.
  Proof. rewrite interp_fam_unseal. exact: (fixpoint_unfold interp1 th W C w). Qed.

  (** The pre-fixpoint is persistent for any family: its recursive
      occurrences are under [□]. *)
  #[global] Instance interp1_persistent (interp : TV) th W C w :
    Persistent (interp1 interp th W C w).
  Proof.
    destruct w as [w π].
    rewrite /interp1 /=.
    destruct (get_tag w); last apply _.
    destruct_word w.
    - apply _.
    - destruct c as [rx wp dl dro]; destruct t, rx, wp, g; cbn; apply _.
    - destruct (permit_seal sr), (permit_unseal sr);
        rewrite /safe_to_seal /safe_to_unseal; apply _.
    - apply _.
    - apply _.
  Qed.

  Lemma interp1_eq (interp : TV) (th : Thread) (W: WORLD) (C : CmptName) p g b e a π :
    ((interp1 interp th W C (Cap p g b e a @@? π)) ≡
       (if (isO p)
        then interp_cap_O (th := th) W C (Cap p g b e a @@? π)
        else
          if (has_sreg_access p)
          then False
          else ([∗ list] a ∈ finz.seq_between b e,
                  ∃ (p' : Perm) (P:V),
                    ⌜PermFlowsTo p p'⌝
                    ∗ ⌜persistent_cond P⌝
                    ∗ region_rel (th := th) W C (addr_key π a) p' P p g
                    ∗ ▷ zcond P C
                    ∗ (if readAllowed p'
                       then ▷ (if isGlobal g then rcond_g P C p' interp
                             else rcond_l P C p' (interp th))
                       else True)
                    ∗ (if writeAllowed p'
                       then ▷ (if isWL p then wcond_wl P C (interp th)
                             else wcond_nwl P C (interp th))
                       else True))
               ∗ ⌜(if isWL p then g = Local else True) ∧
                    disjoint_from_mmio b e⌝ ∗ heap_cap_ok p b e π)%I).
  Proof.
    pose proof (interp_cap_body_eq interp th W C p g b e π) as Hbody.
    destruct p as [rx wp dl dro].
    destruct rx, wp, g; cbn [isO has_sreg_access isWL].
    all: rewrite -?Hbody.
    all: rewrite ?bi.pure_and ?bi.persistent_and_sep.
    all: rewrite ?(bi.pure_True (Local = Local) eq_refl).
    all: try
      (rewrite (bi.pure_False (Global = Local)); [|discriminate]).
    all: rewrite ?bi.sep_True ?bi.True_sep ?bi.False_sep.
    all: try (rewrite (comm bi_sep _ False%I) bi.sep_False).
    all: rewrite ?bi.sep_False ?bi.False_sep.
    all: rewrite -?(bi.persistent_and_sep ⌜disjoint_from_shadow b e⌝
      ⌜revoker_addr ∉ finz.seq_between b e⌝) -?bi.pure_and.
    all: reflexivity.
  Qed.

End logrel_fix.

(** The relation at the thread [th]: the family at [th]. *)
Section interp.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ}
    {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    {cthreads : CmptThreads}
    {CL : CritLink Σ}
    `{MP: MachineParameters}
  .
  Definition interp : interpO Σ := interp_fam th.
End interp.
#[global] Arguments interp : simpl never.

Section logrel.

  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ}
    {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    {cthreads : CmptThreads}
    {CL : CritLink Σ}
    `{MP: MachineParameters}
  .
  #[local] Notation E := (interpO Σ).
  #[local] Notation V := (interpO Σ).
  #[local] Notation K := (contO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Lemma interp_unfold (W : WORLD) (C : CmptName) (w : leibnizO LWord) :
    interp W C w ≡ interp1 (λ t, interp (th := t)) th W C w.
  Proof. exact: interp_fam_unfold. Qed.

  Program Definition interp_in_mem (p : Perm) : V :=
    λne W C w, interp_in_mem_pre W C p interp w.
  Solve All Obligations with solve_proper.

  Lemma interp_in_mem_eq p W C w :
    interp_in_mem p W C w ≡ interp W C (lload_word p w).
  Proof. reflexivity. Qed.
  Definition interp_continuation : K := interp_cont interp.
  Program Definition interp_expression : E :=
    interp_expr interp interp_continuation.

  (** [frame_match] and [interp_continuation] do not read the error
      handler count of the topmost frame. *)
  Lemma frame_match_set_top_count (Ws : list WORLD) (Cs : list CmptName)
    (cstk : CSTK) (W : WORLD) (C : CmptName) (n : Z) :
    frame_match Ws Cs (cstack_set_top_count cstk n) W C ↔ frame_match Ws Cs cstk W C.
  Proof. destruct cstk as [ef [|frm frms] ]; [done|]. by destruct Ws, Cs. Qed.

  Lemma interp_cont_set_top_count (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) (n : Z) :
    interp_continuation (cstack_set_top_count cstk n) Ws Cs ⊣⊢
    interp_continuation cstk Ws Cs.
  Proof.
    destruct cstk as [ef [|frm frms] ]; by destruct Ws, Cs.
  Qed.

  Lemma interp_untagged_eq W C w :
    get_tag w.(lw) = false → interp W C w ≡ True%I.
  Proof.
    intros Htag. rewrite interp_unfold /interp1 /= Htag. reflexivity.
  Qed.

  Lemma interp_untagged W C w :
    get_tag w.(lw) = false → ⊢ interp W C w.
  Proof. intros Htag. rewrite (interp_untagged_eq W C w Htag). done. Qed.

  Lemma interp_clear_tag W C w : ⊢ interp W C (lclear_tag w).
  Proof. apply interp_untagged. rewrite lw_lclear_tag. apply get_tag_clear_tag. Qed.

  Lemma interp_int W C z π : ⊢ interp W C (WInt z @@? π).
  Proof. by apply interp_untagged. Qed.

  (** We have, and we _WANT_, [interp] to be Persistent *)
  #[global] Instance interp_persistent W C w : Persistent (interp W C w).
  Proof. rewrite /Persistent interp_unfold. apply interp1_persistent. Qed.

  (** A full register file of safe words is safe. *)
  Lemma interp_reg_intro W C (regs : LReg) :
    (∀ r, is_Some (regs !! r)) →
    (∀ (r : RegName) (v : LWord), ⌜regs !! r = Some v⌝ → interp W C v) -∗
    interp_reg interp W C regs.
  Proof.
    iIntros (Hfull) "#Hregs".
    iSplit; first (iIntros (r); iPureIntro; apply Hfull).
    iIntros (r v Hv). by iApply "Hregs".
  Qed.

  (** Register maps: a write to [cnull] is dropped, a read of [cnull] is an
      integer. *)
  Lemma interp_linsert W C (regs : LReg) dst w :
    (∀ (r : RegName) v, ⌜regs !! r = Some v⌝ → interp W C v) -∗
    (⌜dst ≠ cnull⌝ → interp W C w) -∗
    ∀ (r : RegName) v, ⌜<[dst := w]ₗ> regs !! r = Some v⌝ → interp W C v.
  Proof.
    iIntros "#Hreg #Hw" (r v Hv). rewrite /linsert_reg in Hv.
    case_decide as Hdst; first by iApply "Hreg".
    destruct (decide (r = dst)) as [->|Hne].
    - rewrite lookup_insert_eq in Hv. simplify_eq. by iApply "Hw".
    - rewrite lookup_insert_ne // in Hv. by iApply "Hreg".
  Qed.

  (** A register read: [cnull] reads an integer. *)
  Lemma interp_llookup W C (regs : LReg) r v :
    regs !!ₗ r = Some v →
    (∀ (r : RegName) v, ⌜regs !! r = Some v⌝ → interp W C v) -∗
    interp W C v.
  Proof.
    iIntros (Hv) "#Hreg". rewrite /llookup_reg in Hv.
    case_decide; simplify_eq; [by iApply interp_untagged | by iApply "Hreg"].
  Qed.

  Lemma interp_lword_of_argument W C (regs : LReg) arg v :
    lword_of_argument regs arg = Some v →
    (∀ (r : RegName) v, ⌜regs !! r = Some v⌝ → interp W C v)
    -∗ interp W C v.
  Proof.
    iIntros (Harg) "#Hreg".
    apply lword_of_argument_Some_inv in Harg as [(z & -> & ->) | (r & -> & Hr)].
    { by iApply interp_untagged. }
    by iApply (interp_llookup with "Hreg").
  Qed.

  #[global] Instance interp_in_mem_pre_persistent W C p w :
    Persistent (interp_in_mem_pre W C p interp w).
  Proof. apply _. Qed.

  #[global] Instance interp_in_mem_persistent p W C w : Persistent (interp_in_mem p W C w).
  Proof. apply _. Qed.

  Lemma interp_to_in_mem W C w : interp W C w -∗ interp_in_mem RWL W C w.
  Proof.
    change (⊢ interp W C w -∗ interp W C (lload_word RWL w))%I.
    replace (lload_word RWL w) with w by (destruct w; done).
    iIntros "$".
  Qed.

  (** A loaded word is either untagged or the loaded word itself. *)
  Lemma interp_in_mem_load_result W C p raw actual :
    actual = lclear_tag (lload_word p raw) ∨ actual = lload_word p raw ->
    interp_in_mem p W C raw -∗ interp W C actual.
  Proof.
    intros [Hactual | Hactual]; subst actual.
    - iIntros "_". iApply interp_clear_tag.
    - change (⊢ interp W C (lload_word p raw) -∗
        interp W C (lload_word p raw))%I.
      iIntros "$".
  Qed.


  (** ** Loads

      The status witness for the CLoad rule is [LoadPlain]. A stale word
      loads as itself: a dereference of it faults on its tombstone. *)
  Lemma load_witness_plain_intro : ⊢ load_witness_res LoadPlain.
  Proof. done. Qed.

  (** The CLoad post under the plain witness: the loaded word is either
      untagged, or the loaded word itself. *)
  Lemma load_post_plain p v actual :
    load_post LoadPlain p v actual ->
    actual = lclear_tag (lload_word p v) ∨ actual = lload_word p v.
  Proof. intros (_ & _ & _ & Hwit). by right. Qed.

  Lemma interp_in_mem_load_post W C p raw actual :
    load_post LoadPlain p raw actual ->
    interp_in_mem p W C raw -∗ interp W C actual.
  Proof. intros Hpost. by apply interp_in_mem_load_result, load_post_plain. Qed.

  Lemma load_post_plain_load_heap p v actual :
    load_post LoadPlain p v actual ->
    load_heap (lload_word p v) actual.
  Proof. intros Hpost. apply Hpost. Qed.

End logrel.

Notation interp_in_memC := (safeC (interp_in_mem RWL)).
Notation interp_in_mem_gC := (safeGC (interp_in_mem RWL)).
