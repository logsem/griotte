From iris.proofmode Require Import proofmode.
From machine_utils Require Import finz_interval.
From griotte Require Export spec_instance_binary memory_region.
(* For [NthSubBlock] and [SimplTC], used by the [spec_codefrag_*_acc] lemmas. *)
From griotte Require Import proofmode.

(** * Spec regions and spec code fragments

    Spec copies (with [↣ₐ]) of the region points-to and [codefrag] of
    [memory_region.v], and of the [codefrag_*_acc] lemmas of [proofmode.v].
    The points-to independent definitions and lemmas
    ([in_range], [included], [extract_from_region_inv], [region_addrs_zeroes],
    ...) are reused from [memory_region.v]. *)

Section spec_region.
  Context `{specg : specG Σ}.

  Definition spec_region_pointsto (b e : Addr) (ws : list Word) : iProp Σ :=
    ([∗ list] k↦y1;y2 ∈ (finz.seq_between b e);ws, y1 ↣ₐ y2)%I.

  Lemma spec_pointsto_decomposition l1 l2 ws1 ws2 :
    length l1 = length ws1 →
    ([∗ list] k ↦ y1;y2 ∈ (l1 ++ l2);(ws1 ++ ws2), y1 ↣ₐ y2)%I ⊣⊢
    ([∗ list] k ↦ y1;y2 ∈ l1;ws1, y1 ↣ₐ y2)%I ∗ ([∗ list] k ↦ y1;y2 ∈ l2;ws2, y1 ↣ₐ y2)%I.
  Proof. intros. rewrite big_sepL2_app' //. Qed.

  Lemma spec_extract_from_region b e a ws φ :
    let n := length (finz.seq_between b a) in
    (b <= a ∧ a < e)%a →
    (spec_region_pointsto b e ws ∗ ([∗ list] w ∈ ws, φ w)) ⊣⊢
     (∃ w,
        ⌜ws = take n ws ++ (w::drop (S n) ws)⌝
        ∗ spec_region_pointsto b a (take n ws)
        ∗ ([∗ list] w ∈ (take n ws), φ w)
        ∗ a ↣ₐ w ∗ φ w
        ∗ spec_region_pointsto ((a^+1))%a e (drop (S n) ws)
        ∗ ([∗ list] w ∈ (drop (S n) ws), φ w)%I).
  Proof.
    intros. iSplit.
    - iIntros "[A B]". unfold spec_region_pointsto.
      iDestruct (big_sepL2_length with "A") as %Hlen.
      rewrite (finz_seq_between_decomposition b a e) //.
      assert (Hlnws: n = length (take n ws)).
      { rewrite length_take. rewrite Nat.min_l; auto.
        rewrite <- Hlen. subst n. rewrite !finz_seq_between_length /finz.dist.
        solve_addr. }
      generalize (take_drop n ws). intros HWS.
      rewrite <- HWS. simpl.
      iDestruct "B" as "[HB1 HB2]".
      iDestruct (spec_pointsto_decomposition _ _ _ _ Hlnws with "A") as "[HA1 HA2]".
      case_eq (drop n ws); intros.
      + auto.
      + iDestruct "HA2" as "[HA2 HA3]".
        iDestruct "HB2" as "[HB2 HB3]".
        generalize (drop_S' _ _ _ _ _ H0). intros Hdws.
        rewrite <- H0. rewrite HWS. rewrite Hdws.
        iExists w. iFrame. by rewrite <- H0.
    - iIntros "A". iDestruct "A" as (w Hws) "[A1 [B1 [A2 [B2 AB]]]]".
      unfold spec_region_pointsto. rewrite (finz_seq_between_decomposition b a e) //.
      iDestruct "AB" as "[A3 B3]".
      rewrite {5}Hws. iFrame. rewrite {3}Hws. iFrame.
  Qed.

  Lemma spec_extract_from_region' b e a ws φ `{!∀ x, Persistent (φ x)}:
    let n := length (finz.seq_between b a) in
    (b <= a ∧ a < e)%a →
    (spec_region_pointsto b e ws ∗ ([∗ list] w ∈ ws, φ w)) ⊣⊢
     (∃ w,
        ⌜ws = take n ws ++ (w::drop (S n) ws)⌝
        ∗ spec_region_pointsto b a (take n ws)
        ∗ ([∗ list] w ∈ ws, φ w)
        ∗ a ↣ₐ w ∗ φ w
        ∗ spec_region_pointsto (a^+1)%a e (drop (S n) ws))%I.
  Proof.
    intros. iSplit.
    - iIntros "H".
      iDestruct (spec_extract_from_region with "H") as (w Hws) "(?&?&?&#Hφ&?&?)"; eauto.
      iExists _. iFrame. iSplitR; first (iPureIntro; by rewrite {1}Hws //).
      rewrite {3}Hws. iFrame. iSplit; iApply "Hφ".
    - iIntros "H". iApply (spec_extract_from_region with "[H]"); eauto.
      iDestruct "H" as (w Hws) "(?&Hl&?&#Hφ&?)". iExists _. iFrame.
      iSplitR; first (iPureIntro; by rewrite {1}Hws //).
      rewrite {1}Hws. iDestruct (big_sepL_app with "Hl") as "[? ?]".
      cbn. iFrame.
  Qed.

  Notation "[[ b , e ]] ↣ₐ [[ ws ]]" := (spec_region_pointsto b e ws)
            (at level 50, format "[[ b , e ]] ↣ₐ [[ ws ]]") : bi_scope.

  Lemma spec_region_pointsto_cons
      (b b' e : Addr) (w : Word) (ws : list Word) :
    (b + 1)%a = Some b' → (b' <= e)%a →
    [[b, e]] ↣ₐ [[ w :: ws ]] ⊣⊢ b ↣ₐ w ∗ [[b', e]] ↣ₐ [[ ws ]].
  Proof.
    intros Hb' Hb'e.
    rewrite /spec_region_pointsto.
    rewrite (finz_seq_between_decomposition b b e).
    2: revert Hb' Hb'e; clear; intros; split; solve_addr.
    rewrite finz_seq_between_empty /=.
    2: clear; solve_addr.
    rewrite (_: (b ^+ 1) = b')%a.
    2: revert Hb' Hb'e; clear; intros; solve_addr.
    eauto.
  Qed.

  Lemma spec_region_pointsto_single b e l:
    (b+1)%a = Some e →
    [[b,e]] ↣ₐ [[l]] -∗
    ∃ v, b ↣ₐ v ∗ ⌜l = [v]⌝.
  Proof.
    iIntros (Hbe) "H". rewrite /spec_region_pointsto finz_seq_between_singleton //.
    iDestruct (big_sepL2_length with "H") as %Hlen.
    cbn in Hlen. destruct l as [|x l']; [by inversion Hlen|].
    destruct l'; [| by inversion Hlen]. iExists x. cbn.
    iDestruct "H" as "(H & _)". eauto.
  Qed.

  Lemma spec_region_pointsto_split (b e a : Addr) (w1 w2 : list Word) :
    (b ≤ a ≤ e)%Z →
    (length w1) = (finz.dist b a) →
    ([[b,e]]↣ₐ[[w1 ++ w2]] ⊣⊢ [[b,a]]↣ₐ[[w1]] ∗ [[a,e]]↣ₐ[[w2]])%I.
  Proof with try (rewrite /finz.dist; solve_addr).
    intros [Hba Hae] Hsize.
    iSplit.
    - iIntros "Hbe".
      rewrite /spec_region_pointsto /finz.seq_between.
      rewrite (finz_seq_decomposition _ _ (finz.dist b a))...
      iDestruct (big_sepL2_app' with "Hbe") as "[Hba Ha'b]".
      + by rewrite finz_seq_length.
      + iFrame.
        rewrite (_: (b ^+ finz.dist b a)%a = a)...
        rewrite (_: finz.dist a e = finz.dist b e - finz.dist b a)...
    - iIntros "[Hba Hae]".
      rewrite /spec_region_pointsto /finz.seq_between.
      rewrite (finz_seq_decomposition (finz.dist b e) _ (finz.dist b a))...
      iApply (big_sepL2_app with "Hba [Hae]"); cbn.
      rewrite (_: (b ^+ finz.dist b a)%a = a)...
      rewrite (_: finz.dist b e - finz.dist b a = finz.dist a e)...
  Qed.

End spec_region.

Global Notation "[[ b , e ]] ↣ₐ [[ ws ]]" := (spec_region_pointsto b e ws)
            (at level 50, format "[[ b , e ]] ↣ₐ [[ ws ]]") : bi_scope.

Section spec_codefrag.
  Context `{specg : specG Σ} `{MP: MachineParameters}.

  Definition spec_codefrag (a0: Addr) (cs: list Word) :=
    ([[ a0, (a0 ^+ length cs)%a ]] ↣ₐ [[ cs ]])%I.

  Lemma spec_codefrag_contiguous_region a0 cs :
    spec_codefrag a0 cs -∗
      ⌜ContiguousRegion a0 (length cs)⌝.
  Proof using.
    iIntros "Hcs". unfold spec_codefrag.
    iDestruct (big_sepL2_length with "Hcs") as %Hl.
    set an := (a0 + length cs)%a in Hl |- *.
    unfold ContiguousRegion.
    destruct an eqn:Han; subst an; [ by eauto |]. cbn.
    exfalso. rewrite finz_seq_between_length /finz.dist in Hl.
    solve_addr.
  Qed.

  Lemma spec_codefrag_lookup_acc a0 (cs: list Word) (i: nat) w:
    SimplTC (cs !! i) (Some w) →
    spec_codefrag a0 cs -∗
      (a0 ^+ i)%a ↣ₐ w ∗ ((a0 ^+ i)%a ↣ₐ w -∗ spec_codefrag a0 cs).
  Proof.
    iIntros (Hi) "Hcs".
    iDestruct (spec_codefrag_contiguous_region with "Hcs") as %Hub.
    rewrite /spec_codefrag.
    destruct Hub as [? Hub].
    iDestruct (big_sepL2_lookup_acc with "Hcs") as "[Hw Hcont]"; only 2: by eauto.
    2: iFrame.
    eapply finz_seq_between_lookup with (n:=length cs).
    { apply lookup_lt_is_Some_1; eauto. }
    { solve_addr. }
  Qed.

  Lemma spec_codefrag_block0_acc a0 (l1 l2: list Word):
    spec_codefrag a0 (l1 ++ l2) -∗
    spec_codefrag a0 l1 ∗
    (spec_codefrag a0 l1 -∗ spec_codefrag a0 (l1 ++ l2)).
  Proof.
    rewrite /spec_codefrag. iIntros "H".
    iDestruct (spec_codefrag_contiguous_region with "H") as %Hregion.
    destruct Hregion as [an Han]. rewrite length_app in Han |- *.
    iDestruct (spec_region_pointsto_split _ _ (a0 ^+ length l1)%a with "H") as "[H1 H2]".
    { by solve_addr. }
    { by rewrite /finz.dist; solve_addr. }
    iFrame. iIntros "H1".
    rewrite spec_region_pointsto_split; first iFrame.
    + solve_addr.
    + rewrite /finz.dist; solve_addr.
  Qed.

  Lemma spec_codefrag_block_acc (n: nat) a0 (cs: list Word) l1 l l2:
    NthSubBlock cs n l1 l l2 →
    spec_codefrag a0 cs -∗
    ∃ (ai: Addr), ⌜(a0 + length l1)%a = Some ai⌝ ∗
    spec_codefrag ai l ∗
    (spec_codefrag ai l -∗ spec_codefrag a0 cs).
  Proof.
    unfold NthSubBlock. intros ->. rewrite /spec_codefrag. iIntros "H".
    iDestruct (spec_codefrag_contiguous_region with "H") as %[a1 Ha1].
    rewrite !length_app in Ha1 |- *.
    iDestruct (spec_region_pointsto_split _ _ (a0 ^+ length l1)%a with "H") as "[H1 H2]".
    { solve_addr. }
    { rewrite /finz.dist; solve_addr. }
    iExists (a0 ^+ length l1)%a. iSplitR; first (iPureIntro; solve_addr).
    iDestruct (spec_region_pointsto_split _ _ ((a0 ^+ length l1) ^+ length l)%a with "H2") as "[H2 H3]".
    { solve_addr. }
    { rewrite /finz.dist; solve_addr. }
    iFrame.
    iIntros "H2".
    rewrite spec_region_pointsto_split; [iFrame|..]; cycle 1.
    { solve_addr. }
    { rewrite /finz.dist; solve_addr. }
    rewrite spec_region_pointsto_split; first iFrame.
    { solve_addr. }
    { rewrite /finz.dist; solve_addr. }
  Qed.

End spec_codefrag.
