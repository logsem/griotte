From griotte Require Export stdpp_extra griotte_lang rules_base.
From iris.proofmode Require Import proofmode.
From machine_utils Require Import finz_interval.
From griotte Require Import alloc_registry rules_Load.
(* From griotte Require Import addr_reg. (* Required because of a weird Coq bug related to imports *) *)

Section region.
  Context `{MP: MachineParameters, ceriseg: ceriseG Σ}.

  Lemma isWithin_finz_seq_between_decomposition {z} (a0 a1 b e : finz z):
    (b <= a0 /\ a1 <= e /\ a0 <= a1)%f ->
    finz.seq_between b e = finz.seq_between b a0 ++
                           finz.seq_between a0 a1 ++
                           finz.seq_between a1 e.
  Proof with try (unfold finz.dist; solve_addr) using.
    intros (Hba0 & Ha1e & Ha0a1).
    rewrite (finz_seq_between_split b a0 e)... f_equal.
    rewrite (finz_seq_between_split a0 a1 e)...
  Qed.

  (*--------------------------------------------------------------------------*)

  Definition region_pointsto (b e : Addr) (ws : list LWord) : iProp Σ :=
    ([∗ list] k↦y1;y2 ∈ (finz.seq_between b e);ws, y1 ↦ₐ y2)%I.

  Definition included (b' e' : Addr) (b e : Addr) : iProp Σ :=
    (⌜(b <= b')%a⌝ ∧ (⌜e' <= e⌝)%a)%I.

  Definition in_range (a b e : Addr) : Prop :=
    (b <= a)%a ∧ (a < e)%a.

  Lemma pointsto_decomposition:
    forall l1 l2 ws1 ws2,
      length l1 = length ws1 ->
      ([∗ list] k ↦ y1;y2 ∈ (l1 ++ l2);(ws1 ++ ws2), y1 ↦ₐ y2)%I ⊣⊢
      ([∗ list] k ↦ y1;y2 ∈ l1;ws1, y1 ↦ₐ y2)%I ∗ ([∗ list] k ↦ y1;y2 ∈ l2;ws2, y1 ↦ₐ y2)%I.
  Proof. intros. rewrite big_sepL2_app' //. Qed.

  Lemma extract_from_region b e a ws φ :
    let n := length (finz.seq_between b a) in
    (b <= a ∧ a < e)%a →
    (region_pointsto b e ws ∗ ([∗ list] w ∈ ws, φ w)) ⊣⊢
     (∃ w,
        ⌜ws = take n ws ++ (w::drop (S n) ws)⌝
        ∗ region_pointsto b a (take n ws)
        ∗ ([∗ list] w ∈ (take n ws), φ w)
        ∗ a ↦ₐ w ∗ φ w
        ∗ region_pointsto ((a^+1))%a e (drop (S n) ws)
        ∗ ([∗ list] w ∈ (drop (S n) ws), φ w)%I).
  Proof.
    intros. iSplit.
    - iIntros "[A B]". unfold region_pointsto.
      iDestruct (big_sepL2_length with "A") as %Hlen.
      rewrite (finz_seq_between_decomposition b a e) //.
      assert (Hlnws: n = length (take n ws)).
      { rewrite length_take. rewrite Nat.min_l; auto.
        rewrite <- Hlen. subst n. rewrite !finz_seq_between_length /finz.dist.
        solve_addr. }
      generalize (take_drop n ws). intros HWS.
      rewrite <- HWS. simpl.
      iDestruct "B" as "[HB1 HB2]".
      iDestruct (pointsto_decomposition _ _ _ _ Hlnws with "A") as "[HA1 HA2]".
      case_eq (drop n ws); [intros|intros w ws' H0].
      + auto.
      + iDestruct "HA2" as "[HA2 HA3]".
        iDestruct "HB2" as "[HB2 HB3]".
        generalize (drop_S' _ _ _ _ _ H0). intros Hdws.
        rewrite <- H0. rewrite HWS. rewrite Hdws.
        iExists w. iFrame. by rewrite <- H0.
    - iIntros "A". iDestruct "A" as (w Hws) "[A1 [B1 [A2 [B2 AB]]]]".
      unfold region_pointsto. rewrite (finz_seq_between_decomposition b a e) //.
      iDestruct "AB" as "[A3 B3]".
      rewrite {5}Hws. iFrame. rewrite {3}Hws. iFrame.
  Qed.

  Lemma extract_from_region' b e a ws φ `{!∀ x, Persistent (φ x)}:
    let n := length (finz.seq_between b a) in
    (b <= a ∧ a < e)%a →
    (region_pointsto b e ws ∗ ([∗ list] w ∈ ws, φ w)) ⊣⊢
     (∃ w,
        ⌜ws = take n ws ++ (w::drop (S n) ws)⌝
        ∗ region_pointsto b a (take n ws)
        ∗ ([∗ list] w ∈ ws, φ w)
        ∗ a ↦ₐ w ∗ φ w
        ∗ region_pointsto (a^+1)%a e (drop (S n) ws))%I.
  Proof.
    intros. iSplit.
    - iIntros "H".
      iDestruct (extract_from_region with "H") as (w Hws) "(?&?&?&#Hφ&?&?)"; eauto.
      iExists _. iFrame. iSplitR; first (iPureIntro; by rewrite {1}Hws //).
      rewrite {3}Hws. iFrame. iSplit; iApply "Hφ".
    - iIntros "H". iApply (extract_from_region with "[H]"); eauto.
      iDestruct "H" as (w Hws) "(?&Hl&?&#Hφ&?)". iExists _. iFrame.
      iSplitR; first (iPureIntro; by rewrite {1}Hws //).
      rewrite {1}Hws. iDestruct (big_sepL_app with "Hl") as "[? ?]".
      cbn. iFrame.
  Qed.

  Lemma extract_from_region_inv b e a (φ : Addr → iProp Σ) `{!∀ x, Persistent (φ x)}:
    (b <= a ∧ a < e)%a →
    ⊢ (([∗ list] a' ∈ (finz.seq_between b e), φ a') →
     φ a)%I.
  Proof.
    iIntros (Ha) "#Hreg".
    generalize (finz_seq_between_decomposition _ _ _ Ha); intro HRA. rewrite HRA.
    iDestruct (big_sepL_app with "Hreg") as "[Hlo Hhi] /=".
    iDestruct "Hhi" as "[$ _]".
  Qed.


  Notation "[[ b , e ]] ↦ₐ [[ ws ]]" := (region_pointsto b e ws)
            (at level 50, format "[[ b , e ]] ↦ₐ [[ ws ]]") : bi_scope.

  Lemma region_pointsto_cons
      (b b' e : Addr) (w : LWord) (ws : list LWord) :
    (b + 1)%a = Some b' → (b' <= e)%a →
    [[b, e]] ↦ₐ [[ w :: ws ]] ⊣⊢ b ↦ₐ w ∗ [[b', e]] ↦ₐ [[ ws ]].
  Proof.
    intros Hb' Hb'e.
    rewrite /region_pointsto.
    rewrite (finz_seq_between_decomposition b b e).
    2: revert Hb' Hb'e; clear; intros; split; solve_addr.
    rewrite finz_seq_between_empty /=.
    2: clear; solve_addr.
    rewrite (_: (b ^+ 1) = b')%a.
    2: revert Hb' Hb'e; clear; intros; solve_addr.
    eauto.
  Qed.

  Lemma region_pointsto_single b e l:
    (b+1)%a = Some e →
    [[b,e]] ↦ₐ [[l]] -∗
    ∃ v, b ↦ₐ v ∗ ⌜l = [v]⌝.
  Proof.
    iIntros (Hbe) "H". rewrite /region_pointsto finz_seq_between_singleton //.
    iDestruct (big_sepL2_length with "H") as %Hlen.
    cbn in Hlen. destruct l as [|x l']; [by inversion Hlen|].
    destruct l'; [| by inversion Hlen]. iExists x. cbn.
    iDestruct "H" as "(H & _)". eauto.
  Qed.

  Lemma region_pointsto_split  (b e a : Addr) (w1 w2 : list LWord) :
     (b ≤ a ≤ e)%Z →
     (length w1) = (finz.dist b a) →
     ([[b,e]]↦ₐ[[w1 ++ w2]] ⊣⊢ [[b,a]]↦ₐ[[w1]] ∗ [[a,e]]↦ₐ[[w2]])%I.
   Proof with try (rewrite /finz.dist; solve_addr).
     intros [Hba Hae] Hsize.
     iSplit.
     - iIntros "Hbe".
       rewrite /region_pointsto /finz.seq_between.
       rewrite (finz_seq_decomposition _ _ (finz.dist b a))...
       iDestruct (big_sepL2_app' with "Hbe") as "[Hba Ha'b]".
       + by rewrite finz_seq_length.
       + iFrame.
         rewrite (_: (b ^+ finz.dist b a)%a = a)...
         rewrite (_: finz.dist a e = finz.dist b e - finz.dist b a)...
         (* todo: turn these two into lemmas *)
     - iIntros "[Hba Hae]".
       rewrite /region_pointsto /finz.seq_between. (* todo: use a proper region splitting lemma *)
       rewrite (finz_seq_decomposition (finz.dist b e) _ (finz.dist b a))...
       iApply (big_sepL2_app with "Hba [Hae]"); cbn.
       rewrite (_: (b ^+ finz.dist b a)%a = a)...
       rewrite (_: finz.dist b e - finz.dist b a = finz.dist a e)...
   Qed.

  (** A region splits at [a], given the length of its second part. *)
  Lemma region_pointsto_split_r (b e a : Addr) (w1 w2 : list LWord) :
    (b <= a <= e)%Z →
    length w2 = finz.dist a e →
    [[b,e]]↦ₐ[[w1 ++ w2]] ⊣⊢ [[b,a]]↦ₐ[[w1]] ∗ [[a,e]]↦ₐ[[w2]].
  Proof.
    intros Hbae Hw2. iSplit.
    - iIntros "H".
      iDestruct (big_sepL2_length with "H") as %Hlen.
      rewrite finz_seq_between_length length_app in Hlen.
      iApply (region_pointsto_split with "H"); first done.
      rewrite /finz.dist in Hlen Hw2 |- *. solve_addr.
    - iIntros "[H1 H2]".
      iDestruct (big_sepL2_length with "H1") as %Hlen.
      rewrite finz_seq_between_length in Hlen.
      iApply (region_pointsto_split with "[$H1 $H2]"); done.
  Qed.

  (** A region of memory is the separated conjunction of its cells. *)
  Lemma region_pointsto_cells (b e : Addr) (ws : list LWord) :
    (b + length ws)%a = Some e →
    [[ b , e ]] ↦ₐ [[ ws ]] ⊣⊢ [∗ list] i ↦ w ∈ ws, (b ^+ i)%a ↦ₐ w.
  Proof.
    revert b. induction ws as [|w ws IH]; intros b Hb; cbn in Hb |- *.
    - rewrite /region_pointsto finz_seq_between_empty; [done|solve_addr].
    - rewrite (region_pointsto_cons b (b ^+ 1)%a); [|solve_addr|solve_addr].
      rewrite IH; [|solve_addr].
      rewrite (_ : (b ^+ 0%nat)%a = b); [|solve_addr].
      f_equiv. apply big_sepL_proper. intros k y Hk%lookup_lt_Some.
      rewrite (_ : ((b ^+ 1) ^+ k)%a = (b ^+ S k)%a); [done|solve_addr].
  Qed.

  Lemma region_pointsto_cells_app (b a e : Addr) (ws ws' : list LWord) :
    (b + length ws)%a = Some a →
    (a <= e)%a →
    [[ b , e ]] ↦ₐ [[ ws ++ ws' ]] ⊣⊢
    ([∗ list] i ↦ w ∈ ws, (b ^+ i)%a ↦ₐ w) ∗
    [[ a , e ]] ↦ₐ [[ ws' ]].
  Proof.
    intros Ha Hae.
    rewrite (region_pointsto_split b e a); [|solve_addr|rewrite /finz.dist; solve_addr].
    by rewrite region_pointsto_cells.
  Qed.

  (** [region_cells b [w0; ...; wn]] unfolds (by [cbn]) to
      [b ↦ₐ w0 ∗ cell_addr b 1 ↦ₐ w1 ∗ ... ∗ cell_addr b n ↦ₐ wn], where
      [cell_addr b i] reduces to [b ^+ i] (or [b] for [i = 0]). It is the
      normal form used by [iRegionSplit] and [iRegionMerge]. *)
  Definition cell_addr (b : Addr) (i : nat) : Addr :=
    match i with 0%nat => b | S _ => (b ^+ i)%a end.

  Lemma cell_addr_eq b i : cell_addr b i = (b ^+ i)%a.
  Proof. destruct i; cbn; solve_addr. Qed.

  Fixpoint region_cells_from (b : Addr) (i : nat) (w : LWord) (ws : list LWord) : iProp Σ :=
    match ws with
    | [] => cell_addr b i ↦ₐ w
    | w' :: ws' => cell_addr b i ↦ₐ w ∗ region_cells_from b (S i) w' ws'
    end.

  Definition region_cells (b : Addr) (ws : list LWord) : iProp Σ :=
    match ws with [] => emp | w :: ws' => region_cells_from b 0 w ws' end.

  Lemma region_cells_from_big_sepL b i w ws :
    region_cells_from b i w ws ⊣⊢ [∗ list] k ↦ y ∈ w :: ws, (b ^+ (i + k)%nat)%a ↦ₐ y.
  Proof.
    revert i w. induction ws as [|w' ws IH]; intros i w; cbn [region_cells_from].
    - by rewrite big_sepL_singleton Nat.add_0_r cell_addr_eq.
    - rewrite big_sepL_cons IH Nat.add_0_r cell_addr_eq.
      f_equiv. apply big_sepL_proper. intros k y _. by rewrite Nat.add_succ_r.
  Qed.

  Lemma region_cells_big_sepL b ws :
    region_cells b ws ⊣⊢ [∗ list] i ↦ w ∈ ws, (b ^+ i)%a ↦ₐ w.
  Proof. destruct ws as [|w ws]; first done. apply region_cells_from_big_sepL. Qed.

  Lemma region_pointsto_region_cells (b e : Addr) (ws : list LWord) :
    (b + length ws)%a = Some e →
    [[ b , e ]] ↦ₐ [[ ws ]] ⊣⊢ region_cells b ws.
  Proof. intros. by rewrite region_cells_big_sepL region_pointsto_cells. Qed.

  Lemma region_pointsto_region_cells_app (b a e : Addr) (ws ws' : list LWord) :
    (b + length ws)%a = Some a →
    (a <= e)%a →
    [[ b , e ]] ↦ₐ [[ ws ++ ws' ]] ⊣⊢
    region_cells b ws ∗
    [[ a , e ]] ↦ₐ [[ ws' ]].
  Proof. intros. by rewrite region_cells_big_sepL region_pointsto_cells_app. Qed.

   Lemma within_in_range:
     forall a b b' e e',
    (b <= b')%a ->
    (e' <= e)%a ->
    in_range a b' e' ->
    in_range a b e.
  Proof.
    intros * ? ? [? ?]. split; solve_addr.
  Qed.

   (*--------------------------------------------------------------------------*)

  (** Persistent regions: every cell is a discarded points-to. *)
  Definition region_pointsto_pers (b e : Addr) (ws : list LWord) : iProp Σ :=
    ([∗ list] k↦y1;y2 ∈ (finz.seq_between b e);ws, y1 ↦ₐ□ y2)%I.

  Notation "[[ b , e ]] ↦ₐ□ [[ ws ]]" := (region_pointsto_pers b e ws)
            (at level 50, format "[[ b , e ]] ↦ₐ□ [[ ws ]]") : bi_scope.

  #[global] Instance region_pointsto_pers_persistent b e ws :
    Persistent ([[ b , e ]] ↦ₐ□ [[ ws ]]).
  Proof. apply _. Qed.

  #[global] Instance region_pointsto_pers_timeless b e ws :
    Timeless ([[ b , e ]] ↦ₐ□ [[ ws ]]).
  Proof. apply _. Qed.

  Lemma region_pointsto_persist b e ws :
    [[ b , e ]] ↦ₐ [[ ws ]] ==∗ [[ b , e ]] ↦ₐ□ [[ ws ]].
  Proof.
    iIntros "Hws". rewrite /region_pointsto /region_pointsto_pers.
    rewrite !big_sepL2_alt. iDestruct "Hws" as "[$ Hws]".
    iApply big_sepL_bupd. iApply (big_sepL_mono with "Hws").
    iIntros (k [a w] _) "Ha". iApply (pointsto_persist with "Ha").
  Qed.

  Lemma region_pointsto_pers_cons
      (b b' e : Addr) (w : LWord) (ws : list LWord) :
    (b + 1)%a = Some b' → (b' <= e)%a →
    [[b, e]] ↦ₐ□ [[ w :: ws ]] ⊣⊢ b ↦ₐ□ w ∗ [[b', e]] ↦ₐ□ [[ ws ]].
  Proof.
    intros Hb' Hb'e.
    rewrite /region_pointsto_pers.
    rewrite (finz_seq_between_decomposition b b e).
    2: revert Hb' Hb'e; clear; intros; split; solve_addr.
    rewrite finz_seq_between_empty /=.
    2: clear; solve_addr.
    rewrite (_: (b ^+ 1) = b')%a.
    2: revert Hb' Hb'e; clear; intros; solve_addr.
    eauto.
  Qed.

  (** A persistent region is the separated conjunction of its cells. *)
  Lemma region_pointsto_pers_cells (b e : Addr) (ws : list LWord) :
    (b + length ws)%a = Some e →
    [[ b , e ]] ↦ₐ□ [[ ws ]] ⊣⊢ [∗ list] i ↦ w ∈ ws, (b ^+ i)%a ↦ₐ□ w.
  Proof.
    revert b. induction ws as [|w ws IH]; intros b Hb; cbn in Hb |- *.
    - rewrite /region_pointsto_pers finz_seq_between_empty; [done|solve_addr].
    - rewrite (region_pointsto_pers_cons b (b ^+ 1)%a); [|solve_addr|solve_addr].
      rewrite IH; [|solve_addr].
      rewrite (_ : (b ^+ 0%nat)%a = b); [|solve_addr].
      f_equiv. apply big_sepL_proper. intros k y Hk%lookup_lt_Some.
      rewrite (_ : ((b ^+ 1) ^+ k)%a = (b ^+ S k)%a); [done|solve_addr].
  Qed.

  (** [region_cells_pers] is [region_cells] with discarded points-to. *)
  Fixpoint region_cells_from_pers (b : Addr) (i : nat) (w : LWord) (ws : list LWord) : iProp Σ :=
    match ws with
    | [] => cell_addr b i ↦ₐ□ w
    | w' :: ws' => cell_addr b i ↦ₐ□ w ∗ region_cells_from_pers b (S i) w' ws'
    end.

  Definition region_cells_pers (b : Addr) (ws : list LWord) : iProp Σ :=
    match ws with [] => emp | w :: ws' => region_cells_from_pers b 0 w ws' end.

  Lemma region_cells_from_pers_big_sepL b i w ws :
    region_cells_from_pers b i w ws ⊣⊢ [∗ list] k ↦ y ∈ w :: ws, (b ^+ (i + k)%nat)%a ↦ₐ□ y.
  Proof.
    revert i w. induction ws as [|w' ws IH]; intros i w; cbn [region_cells_from_pers].
    - by rewrite big_sepL_singleton Nat.add_0_r cell_addr_eq.
    - rewrite big_sepL_cons IH Nat.add_0_r cell_addr_eq.
      f_equiv. apply big_sepL_proper. intros k y _. by rewrite Nat.add_succ_r.
  Qed.

  Lemma region_cells_pers_big_sepL b ws :
    region_cells_pers b ws ⊣⊢ [∗ list] i ↦ w ∈ ws, (b ^+ i)%a ↦ₐ□ w.
  Proof. destruct ws as [|w ws]; first done. apply region_cells_from_pers_big_sepL. Qed.

  Lemma region_pointsto_pers_region_cells (b e : Addr) (ws : list LWord) :
    (b + length ws)%a = Some e →
    [[ b , e ]] ↦ₐ□ [[ ws ]] ⊣⊢ region_cells_pers b ws.
  Proof. intros. by rewrite region_cells_pers_big_sepL region_pointsto_pers_cells. Qed.

   (*--------------------------------------------------------------------------*)

End region.

#[global] Notation "[[ b , e ]] ↦ₐ [[ ws ]]" := (region_pointsto b e ws)
            (at level 50, format "[[ b , e ]] ↦ₐ [[ ws ]]") : bi_scope.
#[global] Notation "[[ b , e ]] ↦ₐ□ [[ ws ]]" := (region_pointsto_pers b e ws)
            (at level 50, format "[[ b , e ]] ↦ₐ□ [[ ws ]]") : bi_scope.
#[global] Notation "[[ b , e ]] ↦ₕ[ ι ] [[ ws ]]" := (heap_region_pointsto ι b e ws)
            (at level 50, format "[[ b , e ]] ↦ₕ[ ι ] [[ ws ]]") : bi_scope.

#[global] Notation "[[ b , e ]] ⊂ₐ [[ b' , e' ]]" := (included b e b' e')
            (at level 50, format "[[ b , e ]] ⊂ₐ [[ b' , e' ]]") : bi_scope.

#[global] Notation "a ∈ₐ [[ b , e ]]" := (in_range a b e)
            (at level 50, format "a ∈ₐ [[ b , e ]]") : bi_scope.

(** Normalise the spine of the list [l] into [x0 :: ... :: xn :: t], by
    unfolding the definitions that produce the list (e.g. a constant
    [Definition data := [w0; w1]]). *)
Ltac list_spine l :=
  let l := eval hnf in l in
  lazymatch l with
  | ?x :: ?t => let t := list_spine t in constr:(x :: t)
  | _ => l
  end.

(** Unfold [region_cells b [w0; ...; wn]] into
    [b ↦ₐ w0 ∗ (b ^+ 1) ↦ₐ w1 ∗ ... ∗ (b ^+ n) ↦ₐ wn], in [h]. *)
Ltac region_cells_simpl_in h :=
  iEval (cbn [region_cells region_cells_from region_cells_pers region_cells_from_pers cell_addr];
         cbv [Z.of_nat Pos.of_succ_nat Pos.succ]) in h.

(** Same as [region_cells_simpl_in], in the goal. *)
Ltac region_cells_simpl :=
  iEval (cbn [region_cells region_cells_from region_cells_pers region_cells_from_pers cell_addr];
         cbv [Z.of_nat Pos.of_succ_nat Pos.succ]).

(** Split [h : [[b, e]] ↦ₐ [[ws]]], for a concrete list [ws = [w0; ...; wn]]
    (possibly behind definitions), into
    [b ↦ₐ w0 ∗ (b ^+ 1) ↦ₐ w1 ∗ ... ∗ (b ^+ n) ↦ₐ wn], destructed with
    [pat]; a persistent region [[b, e]] ↦ₐ□ [[ws]] is split into persistent
    cells. The side condition [(b + length ws)%a = Some e] is solved by
    [done] or [solve_addr]. *)
Tactic Notation "iRegionSplit" constr(h) "as" constr(pat) :=
  lazymatch goal with |- environments.envs_entails ?Δ _ =>
  lazymatch reduction.pm_eval (environments.envs_lookup h Δ) with
  | Some (_, region_pointsto ?b ?e ?ws) =>
      let ws := list_spine ws in
      let x := iFresh in
      iDestruct (region_pointsto_region_cells b e ws with h) as x;
      [first [done | solve_addr] | region_cells_simpl_in x; iDestruct x as pat]
  | Some (_, region_pointsto_pers ?b ?e ?ws) =>
      let ws := list_spine ws in
      let x := iFresh in
      iDestruct (region_pointsto_pers_region_cells b e ws with h) as x;
      [first [done | solve_addr] | region_cells_simpl_in x; iDestruct x as pat]
  | _ => fail "iRegionSplit:" h "is not of the form [[_, _]] ↦ₐ [[_]] or [[_, _]] ↦ₐ□ [[_]]"
  end end.

(** Turn the goal [[[b, e]] ↦ₐ [[ws]]], for a concrete list
    [ws = [w0; ...; wn]] (possibly behind definitions), into
    [b ↦ₐ w0 ∗ (b ^+ 1) ↦ₐ w1 ∗ ... ∗ (b ^+ n) ↦ₐ wn]. The side condition
    [(b + length ws)%a = Some e] is solved by [done] or [solve_addr]. *)
Ltac iRegionMerge :=
  lazymatch goal with
  | |- environments.envs_entails _ (region_pointsto ?b ?e ?ws) =>
      let ws := list_spine ws in
      iApply (region_pointsto_region_cells b e ws);
      [first [done | solve_addr] | region_cells_simpl]
  | _ => fail "iRegionMerge: the goal is not of the form [[_, _]] ↦ₐ [[_]]"
  end.

Section codefrag.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}.

  (* Code is identifier-less: its words are lifted with [lword_of_word]. *)
  Definition codefrag (a0: Addr) (cs: list Word) :=
    ([[ a0, (a0 ^+ length cs)%a ]] ↦ₐ [[ lword_of_word <$> cs ]])%I.

  Lemma codefrag_contiguous_region a0 cs :
    codefrag a0 cs -∗
      ⌜ContiguousRegion a0 (length cs)⌝.
  Proof using.
    iIntros "Hcs". unfold codefrag.
    iDestruct (big_sepL2_length with "Hcs") as %Hl.
    rewrite length_fmap in Hl.
    set an := (a0 + length cs)%a in Hl |- *.
    unfold ContiguousRegion.
    destruct an eqn:Han; subst an; [ by eauto |]. cbn.
    exfalso. rewrite finz_seq_between_length /finz.dist in Hl.
    solve_addr.
  Qed.

  (* Persistent code: every cell is a discarded points-to. The definition is
     sealed, so that unifying a persistent code fragment over a concrete list
     of instructions (e.g. when framing) never unfolds its [[∗ list]]. *)
  #[local] Definition codefrag_pers_def (a0: Addr) (cs: list Word) : iProp Σ :=
    (⌜ContiguousRegion a0 (length cs)⌝ ∗
     [∗ list] i ↦ w ∈ cs, (a0 ^+ i)%a ↦ₐ□ lword_of_word w)%I.
  #[local] Definition codefrag_pers_aux : seal (@codefrag_pers_def). Proof. by eexists. Qed.
  Definition codefrag_pers := codefrag_pers_aux.(stdpp.base.unseal).
  #[local] Definition codefrag_pers_unseal :
    @codefrag_pers = @codefrag_pers_def := codefrag_pers_aux.(seal_eq).

  #[global] Instance codefrag_pers_persistent a0 cs : Persistent (codefrag_pers a0 cs).
  Proof. rewrite codefrag_pers_unseal. apply _. Qed.

  #[global] Instance codefrag_pers_timeless a0 cs : Timeless (codefrag_pers a0 cs).
  Proof. rewrite codefrag_pers_unseal. apply _. Qed.

  Lemma codefrag_contiguous_region_pers a0 cs :
    codefrag_pers a0 cs -∗
      ⌜ContiguousRegion a0 (length cs)⌝.
  Proof using. rewrite codefrag_pers_unseal. iIntros "[$ _]". Qed.

  Lemma codefrag_persist a0 cs :
    codefrag a0 cs ==∗ codefrag_pers a0 cs.
  Proof.
    iIntros "Hcs".
    iDestruct (codefrag_contiguous_region with "Hcs") as %Hcr.
    destruct Hcr as [e He].
    rewrite /codefrag codefrag_pers_unseal /codefrag_pers_def region_pointsto_cells; last first.
    { rewrite length_fmap. solve_addr. }
    iSplitR; first (iPureIntro; eexists; eauto).
    rewrite big_sepL_fmap.
    iApply big_sepL_bupd. iApply (big_sepL_mono with "Hcs").
    iIntros (k w _) "Hw". iApply (pointsto_persist with "Hw").
  Qed.

  Lemma codefrag_lookup_pers a0 cs (i: nat) w :
    cs !! i = Some w →
    codefrag_pers a0 cs -∗ (a0 ^+ i)%a ↦ₐ□ lword_of_word w.
  Proof.
    rewrite codefrag_pers_unseal.
    iIntros (Hi) "[_ Hcs]".
    iApply (big_sepL_lookup with "Hcs"); eauto.
  Qed.

  Lemma codefrag_app_pers a0 l1 l2 :
    codefrag_pers a0 (l1 ++ l2) -∗
    codefrag_pers a0 l1 ∗ codefrag_pers (a0 ^+ length l1)%a l2.
  Proof.
    rewrite codefrag_pers_unseal.
    iIntros "[%Hcr Hcs]".
    rewrite length_app in Hcr.
    rewrite big_sepL_app. iDestruct "Hcs" as "[H1 H2]".
    iSplitL "H1".
    - iFrame. iPureIntro. destruct Hcr as [e He].
      exists (a0 ^+ length l1)%a. solve_addr.
    - iSplitR.
      { iPureIntro. destruct Hcr as [e He]. exists e. solve_addr. }
      iApply (big_sepL_mono with "H2").
      iIntros (k w _) "Hw".
      rewrite (_: (a0 ^+ (length l1 + k)%nat)%a = ((a0 ^+ length l1) ^+ k)%a); first done.
      destruct Hcr as [e He]. solve_addr.
  Qed.

End codefrag.

Section region_addrs_zeroes.

  Definition region_addrs_zeroes (b e : Addr) : list LWord :=
    replicate (finz.dist b e) (lword_of_word (WInt 0%Z)).


  Lemma region_addrs_zeroes_split (b a e: Addr) :
    (b <= a)%a ∧ (a <= e)%a →
    region_addrs_zeroes b e = region_addrs_zeroes b a ++ region_addrs_zeroes a e.
  Proof.
    intros. rewrite /region_addrs_zeroes.
    rewrite (finz_dist_split a). 2: solve_addr.
    rewrite replicate_add //.
  Qed.

End region_addrs_zeroes.

Section cells_store.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} `{MP: MachineParameters}.

  (** The stores of [ws] to the cells from [a], through a capability of
      permission [p] and identifier [π]. [D i] holds once the first [i]
      cells are written. Each store gets cell [i], outside the shadow
      table, with the liveness of [π], and gives it back with the stored
      word. *)
  Definition cells_store_acc (D : nat → iProp Σ) (p : Perm) (a : Addr)
    (π : option AId) (ws : list LWord) : iProp Σ :=
    □ ∀ i : nat,
      ⌜(i < length ws)%nat⌝ -∗
      D i
      ={⊤}=∗
      ∃ (v : LWord) (q : Qp),
        ⌜is_shadow_address (a ^+ i)%a = false⌝ ∗
        (a ^+ i)%a ↦ₐ v ∗
        deref_res π q ∗
        ▷ ((a ^+ i)%a ↦ₐ lstore_word p (ws !!! i) -∗
           deref_res π q
           ={⊤}=∗
           D (S i)).

  #[global] Instance cells_store_acc_persistent D p a π ws :
    Persistent (cells_store_acc D p a π ws).
  Proof. apply _. Qed.

  (** The stores of [w :: ws] from [a], without the first: those of [ws]
      from [a ^+ 1]. *)
  Lemma cells_store_acc_tail (D : nat → iProp Σ) (p : Perm) (a : Addr)
    (π : option AId) (w : LWord) (ws : list LWord) :
    is_Some (a + length (w :: ws))%a →
    cells_store_acc D p a π (w :: ws) -∗
    cells_store_acc (λ i, D (S i)) p (a ^+ 1)%a π ws.
  Proof.
    iIntros ([a_end Ha_end]) "#Hacc". iIntros "!>" (i Hi) "HD".
    cbn in Ha_end.
    rewrite (_ : ((a ^+ 1) ^+ i)%a = (a ^+ S i)%a); last solve_addr.
    iApply ("Hacc" $! (S i) with "[] HD"). iPureIntro; cbn; lia.
  Qed.

End cells_store.

Section cells_load.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} `{MP: MachineParameters}.

  (** The loads of [n] cells from [a] through a capability of permission
      [p], end [e] and identifier [π]. [L i ls] holds once the first [i]
      cells are loaded, [ls] the loaded words. Each load of a cell below
      [e] gets cell [i], outside the shadow table, with a status witness
      and a dereference witness of [π], and gives it back with the loaded
      word. *)
  Definition cells_load_acc (L : nat → list LWord → iProp Σ) (p : Perm) (e a : Addr)
    (π : option AId) (n : nat) : iProp Σ :=
    □ ∀ (i : nat) (ls : list LWord),
      ⌜(i < n)%nat⌝ -∗
      ⌜(a + i < e)%Z⌝ -∗
      L i ls
      ={⊤}=∗
      ∃ (v : LWord) (dq : dfrac) (wit : load_witness) (dw : deref_witness),
        ⌜is_shadow_address (a ^+ i)%a = false⌝ ∗
        ⌜π = deref_id dw⌝ ∗
        (a ^+ i)%a ↦ₐ{dq} v ∗
        load_witness_res wit ∗
        deref_witness_res dw ∗
        ▷ (∀ v' : LWord,
             ⌜load_post wit p v v'⌝ -∗
             (a ^+ i)%a ↦ₐ{dq} v -∗
             load_witness_res wit -∗
             deref_witness_res dw
             ={⊤}=∗
             L (S i) (ls ++ [v'])).

  #[global] Instance cells_load_acc_persistent L p e a π n :
    Persistent (cells_load_acc L p e a π n).
  Proof. apply _. Qed.

  (** The loads of [S n] cells from [a], once the first is loaded as [w]:
      those of [n] cells from [a ^+ 1]. *)
  Lemma cells_load_acc_tail (L : nat → list LWord → iProp Σ) (p : Perm) (e a : Addr)
    (π : option AId) (n : nat) (w : LWord) :
    cells_load_acc L p e a π (S n) -∗
    cells_load_acc (λ i ls, L (S i) (w :: ls)) p e (a ^+ 1)%a π n.
  Proof.
    iIntros "#Hacc !>" (i ls Hi Hie) "HL".
    rewrite (_ : ((a ^+ 1) ^+ i)%a = (a ^+ S i)%a); last solve_addr.
    iApply ("Hacc" $! (S i) (w :: ls) with "[%] [%] HL"); [lia | solve_addr].
  Qed.

  (** The loads of the cells of an owned region outside the shadow table,
      through a capability of permission [p] without identifier: once [i]
      words are loaded, they are the first [i] words of the region, as
      loaded through [p]. *)
  Lemma region_cells_load_acc (p : Perm) (e a a' : Addr) (ws : list LWord) :
    (a + length ws)%a = Some a' →
    disjoint_from_shadow a a' →
    ⊢ cells_load_acc
        (λ i ls, [[ a , a' ]] ↦ₐ [[ ws ]] ∗ ⌜ls = take i (lload_word p <$> ws)⌝)%I
        p e a None (length ws).
  Proof.
    iIntros (Ha' Hshadow).
    iIntros "!>" (i ls Hi Hie) "[Hws ->]".
    destruct (lookup_lt_is_Some_2 ws i Hi) as [v Hv].
    iEval (rewrite (region_pointsto_cells a a' ws Ha')) in "Hws".
    iDestruct (big_sepL_lookup_acc with "Hws") as "[Ha Hclose]"; first exact Hv.
    iModIntro. iExists v, (DfracOwn 1), LoadPlain, DerefNoId.
    iFrame "Ha". iSplit.
    { iPureIntro. eapply disjoint_from_shadow_not_in; first exact Hshadow.
      apply withinBounds_true_iff. solve_addr. }
    iSplit; first done. iSplitR; first done. iSplitR; first done.
    iIntros "!>" (v' (_ & _ & _ & ->)) "Ha _ _ !>".
    iDestruct ("Hclose" with "Ha") as "Hws".
    rewrite (region_pointsto_cells a a' ws Ha'). iFrame "Hws". iPureIntro.
    rewrite (take_S_r _ _ (lload_word p v)); first done.
    by rewrite list_lookup_fmap Hv.
  Qed.

End cells_load.
