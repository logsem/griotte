From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
Require Import Eqdep_dec.
From cap_machine Require Import
     rules logrel region_invariants fundamental region_invariants_revocation region_invariants_static.
From cap_machine Require Export stdpp_extra iris_extra.


(* Helper definitions for creating static regions *)
Definition lists_to_static_region (l1: list Addr) (l2: list Word): gmap Addr Word :=
  list_to_map (zip l1 l2).

Lemma lists_to_static_region_cons a w l1 l2 :
  lists_to_static_region (a :: l1) (w :: l2) =
  <[ a := w ]> (lists_to_static_region l1 l2).
Proof. reflexivity. Qed.


Lemma lists_to_static_region_lookup_None l1 l2 a :
  a ∉ l1 → lists_to_static_region l1 l2 !! a = None.
Proof.
  revert l2. induction l1; eauto; []. intros l2 [? ?]%not_elem_of_cons.
  destruct l2.
  { cbn. eauto. }
  { rewrite lists_to_static_region_cons. rewrite lookup_insert_None. eauto. }
Qed.

Lemma lists_to_static_region_dom l1 l2 :
  length l1 = length l2 →
  dom (gset Addr) (lists_to_static_region l1 l2) = list_to_set l1.
Proof.
  intros Hlen. apply elem_of_equiv_L. intros x.
  rewrite /lists_to_static_region elem_of_dom elem_of_list_to_set.
  split. by intros [? ?%elem_of_list_to_map_2%elem_of_zip_l].
  intros Hx.
  destruct (elem_of_list_lookup_1 _ _ Hx) as [xi Hxi].
  pose proof (lookup_lt_Some _ _ _ Hxi).
  rewrite list_to_map_lookup_is_Some fst_zip //. lia.
Qed.

Lemma lists_to_static_region_size l1 l2 :
  length l1 = length l2 → NoDup l1 ->
  size (lists_to_static_region l1 l2) = length l1.
Proof.
  revert l2.
  induction l1;intros l2 Hlen Hdup.
  - simpl. auto.
  - simpl. destruct l2;inversion Hlen. apply NoDup_cons in Hdup as [Hnin Hdup].
    rewrite -(IHl1 l2);auto.
    rewrite /lists_to_static_region /=. rewrite map_size_insert;auto.
    apply not_elem_of_list_to_map_1. rewrite fst_zip;[auto|lia].
Qed.

Lemma big_sepL2_to_static_region {Σ: gFunctors} l1 l2 (Φ : _ → _ → iProp Σ) Ψ :
  NoDup l1 →
  □ (∀ k a w, ⌜l1 !! k = Some a⌝ -∗ ⌜l2 !! k = Some w⌝ -∗ Φ a w -∗ Ψ a w) -∗
  ([∗ list] a;w ∈ l1;l2, Φ a w) -∗
  ([∗ map] a↦pv ∈ lists_to_static_region l1 l2, Ψ a pv).
Proof.
  revert l2. induction l1; intros l2 ND.
  { cbn in *. iIntros "_ _". by iApply big_sepM_empty. }
  { iIntros "#Ha H". iDestruct (big_sepL2_cons_inv_l with "H") as (w l2' ->) "[HΦ H]".
    rewrite lists_to_static_region_cons. iApply big_sepM_insert.
      by apply lists_to_static_region_lookup_None, NoDup_cons_11.
    iSplitL "HΦ". { iApply ("Ha" $! 0); try (iPureIntro; apply cons_lookup); eauto. }
    iApply IHl1; auto.
    by eauto using NoDup_cons_12.
    iModIntro. iIntros. iApply ("Ha" $! (S k)); auto. }
Qed.

Lemma static_region_to_big_sepL2 {Σ: gFunctors} l1 l2 (Φ : _ → _ -> iProp Σ) Ψ :
  NoDup l1 → length l1 = length l2 ->
  □ (∀ k a w, ⌜l1 !! k = Some a⌝ -∗ ⌜l2 !! k = Some w⌝ -∗ Ψ a w -∗ Φ a w) -∗
  ([∗ map] a↦pv ∈ lists_to_static_region l1 l2, Ψ a pv) -∗
  ([∗ list] a;w ∈ l1;l2, Φ a w).
Proof.
  revert l2. induction l1; intros l2 ND Hlen.
  { cbn in *. iIntros "_ _". destruct l2;[|inversion Hlen]. done. }
  { iIntros "#Ha H". destruct l2;[inversion Hlen|]. iDestruct (big_sepM_delete with "H") as "[Hψ H]".
    rewrite lists_to_static_region_cons. apply lookup_insert.
    iSplitL "Hψ". { iApply ("Ha" $! 0); try (iPureIntro; constructor). auto. }
    iApply IHl1; auto.
    by eauto using NoDup_cons_12.
    iModIntro. iIntros. iApply ("Ha" $! (S k)); auto; iPureIntro.
    rewrite lists_to_static_region_cons.
    rewrite delete_insert. auto. by apply lists_to_static_region_lookup_None, NoDup_cons_11. }
Qed.

Section awkward_helpers.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Lemma updatePcPerm_RX w g b e a :
    inr (RX, g, b, e, a) = updatePcPerm w ->
    w = inr (RX, g, b, e, a) ∨ w = inr (E, g, b, e, a).
  Proof.
    intros Hperm.
    destruct w;inversion Hperm.
    destruct c,p,p,p,p;simplify_eq;auto.
  Qed.


  (* Lemma which splits a list of temp resources into its persistent and non persistent parts *)
   Lemma temp_resources_split l W :
     ([∗ list] a ∈ l, (∃ (φ : WORLD * Word → iPropI Σ),
                          ⌜∀ Wv : WORLD * Word, Persistent (φ Wv)⌝ ∗ monotemp_resources W φ a ∗ rel a φ)
                        ∗ ⌜std (revoke W) !! a = Some Revoked⌝) -∗
     ∃ (ws : list Word), □ ([∗ list] a;w ∈ l;ws, ∃ φ, ⌜∀ Wv : WORLD * Word, Persistent (φ Wv)⌝
                                                             ∗ φ (W,w)
                                                             ∗ rel a φ
                                                             ∗ future_pub_a_mono a φ w )
                          ∗ ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) l⌝
                          ∗ ([∗ list] a;w ∈ l;ws, ∃ φ, a ↦ₐ w ∗ rel a φ).
   Proof.
     rewrite /monotemp_resources.
     iIntros "Hl".
     iAssert ([∗ list] a ∈ l, ∃ (v : Word), (∃ (φ : WORLD * Word → iPropI Σ),
                            ⌜∀ Wv : WORLD * Word, Persistent (φ Wv)⌝
                            ∗ a ↦ₐ v ∗ (future_pub_a_mono a φ v) ∗ φ (W, v)
                            ∗ rel a φ ∗ ⌜std (revoke W) !! a = Some Revoked⌝))%I
       with "[Hl]" as "Hl".
     { iApply (big_sepL_mono with "Hl").
       iIntros (k y Hy) "Hy".
       iDestruct "Hy" as "[Hy Hy']".
       iDestruct "Hy" as (φ) "(Hpers & Hv & Hrel)".
       iDestruct "Hv" as (v) "(Hy & Hmono & Hφ)".
       iExists v,φ. iFrame.
     }
     iDestruct (region_addrs_exists with "Hl") as (wps) "Hl".
     iExists wps. iSplit.
     - iAssert ([∗ list] a;w ∈ l;wps, ∃ φ, ⌜∀ Wv : WORLD * Word, Persistent (φ Wv)⌝
                                                             ∗ φ (W,w)
                                                             ∗ rel a φ
                                                             ∗ (future_pub_a_mono a φ w))%I
         with "[Hl]" as "Hl".
       { iApply (big_sepL2_mono with "Hl").
         iIntros (k y1 y2 Hy1 Hy2) "Hy".
         iDestruct "Hy" as (φ) "(Hpers & Hy & Hmono & Hφ & Hrel & Hrev)".
         iExists φ. iFrame.
       }
       iDestruct (region_addrs_exists2 with "Hl") as (ps Hlen) "Hl".
       (* iDestruct (region_addrs_exists2 with "Hl") as (φs Hlen') "Hl". *)
       iDestruct (big_sepL2_sep with "Hl") as "[Hpers Hl]".
       iDestruct (big_sepL2_length with "Hl") as %Hlength.
       iDestruct (big_sepL2_to_big_sepL_r with "Hpers") as "Hpers";auto.
       iDestruct (big_sepL_forall with "Hpers") as %Hpers.
       iAssert ([∗ list] y1;y2 ∈ l;(zip wps ps), □ (y2.2 (W, y2.1)
                                                   ∗ rel y1 y2.2
                                                     ∗ (future_pub_a_mono y1 y2.2 y2.1)))%I
         with "[Hl]" as "Hl".
       { iApply (big_sepL2_mono with "Hl").
         iIntros (k y1 y2 Hy1 Hy2) "Hy".
         apply Hpers with (Wv:=(W,y2.1)) in Hy2.
         iDestruct "Hy" as "#(Hy & Hrel & Hmono)".
         iModIntro. iFrame "#".
       }
       iDestruct "Hl" as "#Hl".
       iModIntro. iApply region_addrs_exists2.
       iExists ps. iSplit;auto.
       iApply big_sepL2_sep. iSplit.
       + iApply big_sepL2_to_big_sepL_r;auto. iApply big_sepL_forall. auto.
       + iApply (big_sepL2_mono with "Hl").
         iIntros (k y1 y2 Hy1 Hy2) "Hy".
         iDestruct "Hy" as "#(Hy & Hrel & Hmono)".
         iFrame "#".
     - iAssert ([∗ list] a0;c0 ∈ l;wps, (∃ (φ : WORLD * Word → iPropI Σ),
                                    ⌜∀ Wv : WORLD * Word, Persistent (φ Wv)⌝
                                      ∗ a0 ↦ₐ c0
                                        ∗ (future_pub_a_mono a0 φ c0)
                                          ∗ φ (W, c0)
                                            ∗ rel a0 φ)
                                              ∗ ⌜std (revoke W) !! a0 = Some Revoked⌝)%I
         with "[Hl]" as "Hl".
       { iApply (big_sepL2_mono with "Hl").
         iIntros (k y1 y2 Hy1 Hy2) "Hy".
         iDestruct "Hy" as (φ) "(?&?&?&?&?&?)".
         iFrame. iExists _. iFrame.
       }
       iDestruct (big_sepL2_sep with "Hl") as "[Hl #Hrev]".
       iDestruct (big_sepL2_length with "Hl") as %Hlength.
       iSplit.
       + iDestruct (big_sepL2_to_big_sepL_l with "Hrev") as "Hrev'";auto.
         iDestruct (big_sepL_forall with "Hrev'") as %Hrev.
         iPureIntro. apply Forall_forall. intros x Hin.
         apply elem_of_list_lookup in Hin as [k Hin].
           by apply Hrev with (x:=k).
       + iApply (big_sepL2_mono with "Hl").
         iIntros (k y1 y2 Hy1 Hy2) "Hy".
         iDestruct "Hy" as (φ) "(?&?&?&?&?)". iExists _.
         iFrame.
   Qed.


   (* ---------------------------------------------------------------------------------------------- *)
   (* ------------------------------------ Awkward Invariant --------------------------------------- *)
   (* ---------------------------------------------------------------------------------------------- *)

   Definition awk_inv i a :=
     (∃ x:bool, sts_state_loc (A:=Addr) i x
           ∗ if x
             then a ↦ₐ inl 1%Z
             else a ↦ₐ inl 0%Z)%I.

   Definition awk_rel_pub := λ a b, a = false ∨ b = true.
   Definition awk_rel_priv := λ (a b : bool), True.

   (* useful lemma about awk rels *)
   Lemma rtc_rel_pub y x :
     y = (encode true) ->
     rtc (convert_rel awk_rel_pub) y x ->
     x = (encode true).
   Proof.
     intros Heq Hrtc.
     induction Hrtc; auto.
     rewrite Heq in H.
     inversion H as [y' [b [Heq1 [Heq2 Hy] ] ] ].
     inversion Hy; subst; auto.
     apply encode_inj in Heq1. inversion Heq1.
   Qed.
   Lemma rtc_rel_pub' x :
     rtc (convert_rel awk_rel_pub) (encode true) (encode x) ->
     x = true.
   Proof.
     intros Hrtc.
     apply encode_inj.
     apply rtc_rel_pub with (encode true); auto.
   Qed.
   Lemma rtc_rel_pub_false y x :
     y = (encode false) ->
     rtc (convert_rel awk_rel_pub) y x ->
     x = (encode true) ∨ x = (encode false).
   Proof.
     intros Heq Hrtc.
     induction Hrtc; auto.
     rewrite Heq in H.
     inversion H as [y' [b [Heq1 [Heq2 Hy] ] ] ]. subst.
     destruct b;apply encode_inj in Heq1;auto;subst.
     left. eapply rtc_rel_pub; eauto.
   Qed.

   Definition awk_W W i : WORLD := (W.1,(<[i:=encode false]>W.2.1,<[i:=(convert_rel awk_rel_pub,convert_rel awk_rel_pub,convert_rel awk_rel_priv)]>W.2.2)).

   (* namespace definitions for the regions *)
   Definition regN : namespace := nroot .@ "regN".

   (* The proof of the awkward example goes through a number of worlds.
      Below are some helper lemmas and definitions about how these worlds
      are related *)
   Lemma related_priv_local_1 W i :
     W.2.1 !! i = Some (encode true) ->
     W.2.2 !! i = Some (convert_rel awk_rel_pub,convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
     related_sts_priv_world W (W.1, (<[i:=encode false]> W.2.1, W.2.2)).
   Proof.
     intros Hlookup Hrel.
     split;[apply related_sts_std_priv_refl|simpl].
     split;[apply dom_insert_subseteq|split;[auto|] ].
     intros j r1 r2 r3 r1' r2' r3' Hr Hr'.
     rewrite Hr in Hr'. inversion Hr'; subst; repeat (split;auto).
     intros x y Hx Hy.
     destruct (decide (i = j)).
     - subst. rewrite lookup_insert in Hy; inversion Hy; subst.
       rewrite Hrel in Hr. rewrite Hlookup in Hx. inversion Hr; inversion Hx; subst.
       right with (encode false);[|left].
       right. right. exists true,false. repeat (split;auto).
     - rewrite lookup_insert_ne in Hy;auto. rewrite Hx in Hy; inversion Hy; subst. left.
   Qed.

   Lemma related_pub_local_1 Wloc i (x : bool) :
     Wloc.1 !! i = Some (encode x) ->
     Wloc.2 !! i = Some (convert_rel awk_rel_pub,convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
     related_sts_pub Wloc.1 (<[i:=encode true]> Wloc.1) Wloc.2 Wloc.2.
   Proof.
     intros Hx Hrel.
     split;[apply dom_insert_subseteq|split;[auto|] ].
     intros j r1 r2 r3 r1' r2' r3' Hr Hr'.
     rewrite Hr in Hr'. inversion Hr'; subst; repeat (split;auto).
     intros x' y Hx' Hy.
     destruct (decide (i = j)).
     - subst. rewrite lookup_insert in Hy; inversion Hy; subst.
       rewrite Hrel in Hr. rewrite Hx in Hx'. inversion Hr; inversion Hx; subst.
       right with (encode true);[|left].
       exists x,true. inversion Hx'. subst. repeat (split;auto).
       destruct x; rewrite /awk_rel_pub; auto.
     - rewrite lookup_insert_ne in Hy;auto. rewrite Hx' in Hy; inversion Hy; subst. left.
   Qed.

   Lemma related_pub_lookup_local W W' i x :
     related_sts_pub_world W W' ->
     W.2.1 !! i = Some (encode true) ->
     W.2.2 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
     W'.2.1 !! i = Some (encode x) -> x = true.
   Proof.
     intros Hrelated Hi Hr Hi'.
     destruct Hrelated as [_ [Hdom1 [Hdom2 Htrans] ] ].
     assert (is_Some (W'.2.2 !! i)) as [r' Hr'].
     { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom2. apply Hdom2.
       apply elem_of_gmap_dom. eauto. }
     destruct r' as [(r1' & r2') r3'].
     specialize (Htrans i _ _ _ _ _ _ Hr Hr') as [Heq1 [Heq2 [Heq3 Htrans] ] ].
     subst. specialize (Htrans _ _ Hi Hi').
     apply rtc_rel_pub'; auto.
   Qed.

End awkward_helpers.
