From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From griotte Require Export griotte_lang memory_region.
From iris.algebra Require Export gmap agree auth excl_auth.
From iris.base_logic Require Export invariants na_invariants saved_prop.
From griotte Require Export state_interp rules_base rules_trap_entry rules_Load machine_instructions call_stack.
From griotte Require Export world_ghost_theory.
From griotte Require Import rules_registry.
Import uPred.

Ltac auto_equiv :=
  (* Deal with "pointwise_relation" *)
  repeat lazymatch goal with
  | |- pointwise_relation _ _ _ _ => intros ?
  end;
  (* Normalize away equalities. *)
  repeat match goal with
  | H : _ ≡{_}≡ _ |-  _ => apply (discrete_iff _ _ _) in H
  | H : _ ≡ _ |-  _ => apply leibniz_equiv in H
  | _ => progress simplify_eq
  end;
  (* repeatedly apply congruence lemmas and use the equalities in the hypotheses. *)
  try (f_equiv; fast_done || auto_equiv).

Ltac solve_proper ::= (repeat intros ?; simpl; auto_equiv).

Notation safeC P :=
  (λ WCv : WORLD * CmptName * (leibnizO LWord), P WCv.1.1 WCv.1.2 WCv.2).

(** The world-free image of a safety predicate, for a Global region. *)
Notation safeGC P := (λ Cv : CmptName * LWord, P ∅ Cv.1 Cv.2).

(** The types of the logical relation: the interpretations of words and of
    register maps, and the continuations. *)
Notation interpO Σ := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).
Notation regsO Σ := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LReg) -n> iPropO Σ).
Notation contO Σ := (CSTK -n> list WORLD -n> leibnizO (list CmptName) -n> iPropO Σ).

Section logrel_expr.

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
  Implicit Types interp : (V).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Definition interp_in_mem_pre
    (W : WORLD) (C : CmptName) (p : Perm) (interp : V) (w : LWord) : iProp Σ :=
    interp W C (lload_word p w).

  #[global] Instance interp_in_mem_pre_ne W C p w :
    NonExpansive (λ interp, interp_in_mem_pre W C p interp w).
  Proof. intros n x y Hxy. apply Hxy. Qed.

  #[global] Instance interp_in_mem_pre_contractive W C p w :
    Contractive (λ interp, ▷ interp_in_mem_pre W C p interp w)%I.
  Proof. rewrite /interp_in_mem_pre. solve_contractive. Qed.

  (* Condition definitions *)
  (** [zcond] states that if the safety predicate [P] is safe for some integer in some world,
      then this integer is safe in any worlds.
      We don't have simply [□ ∀ W z, P W C (WInt z)], because for RO capabilities,
      we might not have [P W C (WInt z)] !
   *)
  Definition zcond (P : V) (C : CmptName) : iProp Σ :=
    (□ ∀ (W1 W2: WORLD) (z : Z) (π : option AId),
       P W1 C (WInt z @@? π) -∗ P W2 C (WInt z @@? π)).
  #[global] Instance zcond_ne n :
    Proper ((=) ==> (=) ==> dist n) zcond.
  Proof. solve_proper_prepare.
         repeat f_equiv;auto. Qed.
  #[global] Instance zcond_contractive (P : V) (C : CmptName) :
    Contractive (λ interp, ▷ zcond P C)%I.
  Proof. solve_contractive. Qed.

  (** [rcond_l] states that stored values satisfying [P] are safe after the
      deep-permission load filter and the current world's heap revocation filter. *)
  Definition rcond_l (P : V) (C : CmptName) (p : Perm) (interp : V) : iProp Σ :=
    (□ ∀ (W: WORLD) (w : LWord), P W C w -∗ interp_in_mem_pre W C p interp w).
  #[global] Instance rcond_l_ne n :
    Proper ((=) ==> (=) ==> (=) ==> dist n ==> dist n) rcond_l.
  Proof. rewrite /rcond_l /interp_in_mem_pre. solve_proper_prepare. repeat f_equiv;auto. Qed.
  #[global] Instance rcond_l_contractive (P : V) (C : CmptName) (p : Perm) :
    Contractive (λ interp, ▷ rcond_l P C p interp)%I.
  Proof. rewrite /rcond_l /interp_in_mem_pre. solve_contractive. Qed.

  (** [wcond_wl] states that [interp] implies the safety predicate [P].
      It comes from the fact that storing in memory consists of storing
      a value that is safe to share, but we need to store a value respecting [P]. *)
  Definition wcond_wl (P : V) (C : CmptName) (interp : V) : iProp Σ :=
    (□ ∀ (W: WORLD) (w : LWord), interp W C w -∗ P W C w).
  #[global] Instance wcond_wl_ne n :
    Proper ((=) ==> (=)  ==> dist n ==> dist n) wcond_wl.
  Proof. solve_proper_prepare. repeat f_equiv;auto. Qed.
  #[global] Instance wcond_wl_contractive (P : V) (C : CmptName) :
    Contractive (λ interp, ▷ wcond_wl P C interp)%I.
  Proof. solve_contractive. Qed.

  (** [wcond_nwl] is [wcond_wl] on the words that are not local: a capability
      that is not write-local stores only such words. *)
  Definition wcond_nwl (P : V) (C : CmptName) (interp : V) : iProp Σ :=
    (□ ∀ (W: WORLD) (w : LWord), ⌜isLocalWord w.(lw) = false⌝ → interp W C w -∗ P W C w).
  #[global] Instance wcond_nwl_ne n :
    Proper ((=) ==> (=)  ==> dist n ==> dist n) wcond_nwl.
  Proof. solve_proper_prepare. repeat f_equiv;auto. Qed.
  #[global] Instance wcond_nwl_contractive (P : V) (C : CmptName) :
    Contractive (λ interp, ▷ wcond_nwl P C interp)%I.
  Proof. solve_contractive. Qed.

  Lemma wcond_wl_wcond_nwl P C interp : wcond_wl P C interp -∗ wcond_nwl P C interp.
  Proof. iIntros "#H !>" (W w _) "Hw". by iApply "H". Qed.

  (** [persistent_cond] states that the safety predicate [P] is persistent. *)
  Definition persistent_cond (P:V) := (∀ WCv, Persistent (P WCv.1.1 WCv.1.2  WCv.2)).


  (** * Definitions interp *)


  (** Interp of the world state

      -------------------------------------------------------------
      |          |         nwl           |          pwl           |
      -------------------------------------------------------------
      | Local    |       {P,T}           |           {T}          |
      |-----------------------------------------------------------|
      | Global   |       {P}             |           N/A          |
      -------------------------------------------------------------

   *)

  (** The region key of the address [a] of a capability with identifier [π]:
      [LHeap a ι] exactly when [π = Some ι], [LNonHeap a] otherwise. It does
      not depend on the world. *)
  Definition addr_key (π : option AId) (a : Addr) : LAddr :=
    match π with
    | Some ι => LHeap a ι
    | None => LNonHeap a
    end.

  Lemma addr_key_addr π a : laddr_addr (addr_key π a) = a.
  Proof. by destruct π. Qed.

  Lemma addr_key_None a : addr_key None a = LNonHeap a.
  Proof. done. Qed.

  Lemma addr_key_Some ι a : addr_key (Some ι) a = LHeap a ι.
  Proof. done. Qed.

  Lemma addr_key_pointsto π a v :
    addr_key π a ↦ₖ v ⊣⊢ a ↦ₐ v ∗ key_share (addr_key π a).
  Proof. by rewrite key_pointsto_eq addr_key_addr. Qed.

  Lemma addr_key_pointsto_join π a v :
    a ↦ₐ v -∗ key_share (addr_key π a) -∗ addr_key π a ↦ₖ v.
  Proof. iIntros "Ha Hs". iApply addr_key_pointsto. iFrame. Qed.

  (** The status share of a heap key is a dereference witness for a
      capability with the key's identifier. *)
  Lemma key_share_deref π a :
    key_share (addr_key π a) -∗
    ∃ dw, ⌜π = deref_id dw⌝ ∗ deref_witness_res dw ∗
      (deref_witness_res dw -∗ key_share (addr_key π a)).
  Proof.
    iIntros "Hs". destruct π as [ι|]; cbn.
    - iDestruct "Hs" as (b e Hbe) "[#Hobj Htok]".
      iExists (DerefLive ι _). iFrame "Htok". iSplit; first done.
      iIntros "Htok". iExists b, e. by iFrame "∗#".
    - iExists DerefNoId. iSplit; first done. iSplit; first done. by iIntros.
  Qed.


  (** The region of a key reached through a capability. A Global region
      holds the world-free image of its predicate. A Temporary region of the
      local world is public monotone: a Temporary key only ever leaves its
      state through a revocation, which takes its body out. *)
  Definition region_rel_perm (C : CmptName) (k : LAddr) (p : Perm) (P : V) : iProp Σ :=
    k ↪ᵖ[C]{p} (safeGC P).

  Definition region_rel_l (W : WORLD) (C : CmptName) (k : LAddr) (p : Perm) (P : V) : iProp Σ :=
    k ↪ˡ[th, C]{p} (safeC P) ∗ ⌜std W !! k = Some Temporary⌝ ∗ mono_pub C (safeC P).

  (** A write-local capability reaches Temporary regions only, a Global one
      Global regions only, and a Local one either. *)
  Definition region_rel (W : WORLD) (C : CmptName) (k : LAddr) (p' : Perm) (P : V)
      (p : Perm) (g : Locality) : iProp Σ :=
    if isWL p then region_rel_l W C k p' P
    else match g with
         | Global => region_rel_perm C k p' P
         | Local => region_rel_perm C k p' P ∨ region_rel_l W C k p' P
         end%I.

  #[global] Instance region_rel_l_persistent W C k p P : Persistent (region_rel_l W C k p P).
  Proof. apply _. Qed.

  #[global] Instance region_rel_persistent W C k p' P p g :
    Persistent (region_rel W C k p' P p g).
  Proof. rewrite /region_rel. destruct (isWL p), g; apply _. Qed.

  (** The region of a key, by its part. *)
  Definition region_rel_part (ρ : region_part) (W : WORLD) (C : CmptName) (k : LAddr)
      (p : Perm) (P : V) : iProp Σ :=
    match ρ with
    | InPerm => region_rel_perm C k p P
    | InLocal => region_rel_l W C k p P
    end.

  #[global] Instance region_rel_part_persistent ρ W C k p P :
    Persistent (region_rel_part ρ W C k p P).
  Proof. destruct ρ; apply _. Qed.

  Lemma region_rel_parts W C k p' P p g :
    region_rel W C k p' P p g -∗ ∃ ρ, region_rel_part ρ W C k p' P.
  Proof.
    rewrite /region_rel. iIntros "H".
    destruct (isWL p); [by iExists InLocal|].
    destruct g; [by iExists InPerm|].
    iDestruct "H" as "[H|H]"; [by iExists InPerm|by iExists InLocal].
  Qed.

  (** A key reached through a capability that may read or write it: Temporary
      in the local world, or a Global region. *)
  Definition region_valid (W : WORLD) (C : CmptName) (k : LAddr) : iProp Σ :=
    (⌜std W !! k = Some Temporary⌝ ∨ ∃ p φ, k ↪ᵖ[C]{p} φ)%I.

  #[global] Instance region_valid_persistent W C k : Persistent (region_valid W C k).
  Proof. apply _. Qed.

  (** Interp trivially holds for integers. *)
  Definition interp_z : V := λne _ _ w, ⌜match w.(lw) with WInt z => True | _ => False end⌝%I.

  (** Heap authority belongs to the object of the word's identifier [ι],
      whose recorded range covers both bounds. An empty or reversed
      capability carries no memory authority; one without an identifier
      stays clear of the heap. *)
  Definition heap_cap_ok (p : Perm) (b e : Addr) (π : option AId) : iProp Σ :=
    (⌜(b < e)%a⌝ →
     match π with
     | Some ι =>
         ⌜is_heap_address b = true ∧ executeAllowed p = false ∧ isWL p = false⌝ ∗
         ∃ bo eo, alloc_obj ι bo eo ∗ ⌜(bo <= b)%a ∧ (e <= eo)%a⌝
     | None => ⌜disjoint_from_heap b e⌝
     end)%I.

  #[global] Instance heap_cap_ok_persistent p b e π : Persistent (heap_cap_ok p b e π).
  Proof. rewrite /heap_cap_ok. destruct π; apply _. Qed.

  #[global] Instance heap_cap_ok_timeless p b e π : Timeless (heap_cap_ok p b e π).
  Proof. rewrite /heap_cap_ok. destruct π; apply _. Qed.

  (** The key of an address of a capability with an identifier is known. *)
  Lemma heap_cap_ok_id p b e ι :
    (b < e)%a →
    heap_cap_ok p b e (Some ι) -∗
    ⌜is_heap_address b = true ∧ executeAllowed p = false ∧ isWL p = false⌝.
  Proof. iIntros (Hbe) "Hok". by iDestruct ("Hok" with "[%]") as "[$ _]". Qed.

  (** Tagged O capabilities retain authority to free their heap payload: each
      heap cell of the range is a Global region or, under a Local capability,
      a Temporary region of the local world. Nonheap ranges must stay
      disjoint from the heap under narrowing. *)
  Definition heap_cap_O_key (W : WORLD) (C : CmptName) (g : Locality) (k : LAddr) : iProp Σ :=
    (∃ p φ, ⌜∀ x, Persistent (φ x)⌝ ∗ k ↪ᵖ[C]{p} φ) ∨
    (if g is Local
     then ∃ p φ, ⌜∀ x, Persistent (φ x)⌝ ∗ k ↪ˡ[th, C]{p} φ ∗ ⌜std W !! k = Some Temporary⌝
     else False)%I.

  #[global] Instance heap_cap_O_key_persistent W C g k : Persistent (heap_cap_O_key W C g k).
  Proof. rewrite /heap_cap_O_key. destruct g; apply _. Qed.

  Definition heap_cap_O_valid (W : WORLD) (C : CmptName) (p : Perm) (g : Locality)
      (b e : Addr) (π : option AId) : iProp Σ :=
    heap_cap_ok p b e π ∗
    [∗ list] a ∈ finz.seq_between b e,
      (⌜is_heap_address a = true⌝ → heap_cap_O_key W C g (addr_key π a))%I.

  #[global] Instance heap_cap_O_valid_persistent W C p g b e π :
    Persistent (heap_cap_O_valid W C p g b e π).
  Proof. apply _. Qed.

  Program Definition interp_cap_O : V := λne W C w,
    (match w.(lw) with
      | Cap p g b e a => heap_cap_O_valid W C p g b e w.(lprov)
      | _ => True
      end)%I.
  Solve All Obligations with solve_proper.

  Lemma heap_cap_ok_disjoint p b e :
    disjoint_from_heap b e -> ⊢ heap_cap_ok p b e None.
  Proof. iIntros (Hdisjoint Hnonempty). done. Qed.

  (** A valid capability over a heap payload names the object covering it,
      and every cell of the payload is a Global region or a Temporary region
      of the local world. *)
  Lemma free_heap_cap_payload W C p g b e π :
    (heap_b < b ∧ b < e ∧ e <= heap_e)%a ->
    heap_cap_O_valid W C p g b e π -∗
    ∃ ι bo eo, ⌜π = Some ι⌝ ∗ alloc_obj ι bo eo ∗
      ⌜(bo <= b)%a ∧ (e <= eo)%a⌝ ∗
      [∗ list] x ∈ finz.seq_between b e, heap_cap_O_key W C g (LHeap x ι).
  Proof.
    iIntros ((Hb & Hbe & He)) "[#Hok #Hcoverage]".
    iDestruct ("Hok" with "[%]") as "Hlive"; first done.
    destruct π as [ι|]; last first.
    { iDestruct "Hlive" as %Hlive. exfalso. rewrite /disjoint_from_heap elem_of_disjoint in Hlive.
      eapply (Hlive b); apply elem_of_finz_seq_between; solve_addr. }
    iDestruct "Hlive" as "[_ (%bo & %eo & #Hobj & %Hbo)]".
    iExists ι, bo, eo. iFrame "Hobj". do 2 (iSplit; first done).
    iApply (big_sepL_impl with "Hcoverage").
    iIntros "!>" (i x Hx) "Hx". iApply "Hx". iPureIntro.
    apply withinBounds_true_iff.
    apply list_elem_of_lookup_2, elem_of_finz_seq_between in Hx. solve_addr.
  Qed.

  (** The payload side condition of a sealed word: its heap authority. *)
  Definition sealed_payload_ok (w : LWord) : iProp Σ :=
    match w.(lw) with
    | Cap p g b e a => heap_cap_ok p b e w.(lprov)
    | _ => True
    end.

  #[global] Instance sealed_payload_ok_persistent w : Persistent (sealed_payload_ok w).
  Proof. rewrite /sealed_payload_ok. destruct_word (lw w); apply _. Qed.

  (** Interp for sealed capability: the predicate of the otype holds of the
      payload's normal form. The payload keeps the sealed word's
      identifier. *)
  Definition interp_sb (W : WORLD) (C : CmptName) (o : OType) (w : LWord) : iProp Σ :=
    (∃ κ P, o ↪ₒ{κ} P ∗ seal_kind_ok κ C P ∗ ▷ P (th, W, C, norm κ w)) ∗
    sealed_payload_ok w.

  #[global] Instance interp_sb_persistent W C o w : Persistent (interp_sb W C o w).
  Proof.
    rewrite /Persistent /interp_sb.
    iIntros "[(%κ & %P & #Hs & #Hok & HP) #Hw]".
    iDestruct "Hok" as "[%Hpers Hok']".
    iDestruct "HP" as "#HP". iModIntro. iFrame "Hw". iExists κ, P. by iFrame "#".
  Qed.

End logrel_expr.

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

  (** The read condition of a Global capability: at every thread of [C]. *)
  Definition rcond_g (P : V) (C : CmptName) (p : Perm) (interp : TV) : iProp Σ :=
    □ ∀ t', thread_in t' C -∗ rcond_l P C p (interp t').
  #[global] Instance rcond_g_ne n :
    Proper ((=) ==> (=) ==> (=) ==> dist n ==> dist n) rcond_g.
  Proof.
    intros P ? <- C ? <- p ? <- I1 I2 HI. rewrite /rcond_g.
    by repeat f_equiv.
  Qed.
  #[global] Instance rcond_g_contractive (P : V) (C : CmptName) (p : Perm) :
    Contractive (λ interp : TV, ▷ rcond_g P C p interp)%I.
  Proof.
    intros n I1 I2 HI. f_contractive_fin. rewrite /rcond_g.
    repeat f_equiv. apply dist_later_S in HI. apply HI.
  Qed.

  (** The conditions of a seal range on the predicate [P] of an otype of
      kind [κ], at every thread of [C]: sealing a safe word gives the
      predicate of its normal form, and unsealing gives back a safe word.
      Both hold in every world. *)
  Definition seal_cond (κ : seal_kind) (P : Thread * WORLD * CmptName * LWord → iProp Σ)
      (C : CmptName) (interp : TV) : iProp Σ :=
    (□ ∀ t', thread_in t' C -∗
       ∀ (W: WORLD) (w : LWord), interp t' W C w -∗ P (t', W, C, norm κ w)).
  #[global] Instance seal_cond_ne κ P C n :
    Proper (dist n ==> dist n) (seal_cond κ P C).
  Proof. intros I1 I2 HI. rewrite /seal_cond. by repeat f_equiv. Qed.
  #[global] Instance seal_contractive κ P C :
    Contractive (λ interp : TV, ▷ seal_cond κ P C interp)%I.
  Proof. intros n I1 I2 HI. f_contractive_fin. by apply seal_cond_ne, dist_later_S. Qed.

  Definition unseal_cond (κ : seal_kind) (P : Thread * WORLD * CmptName * LWord → iProp Σ)
      (C : CmptName) (interp : TV) : iProp Σ :=
    (□ ∀ t', thread_in t' C -∗
       ∀ (W: WORLD) (w : LWord), P (t', W, C, norm κ w) -∗ interp t' W C w).
  #[global] Instance unseal_cond_ne κ P C n :
    Proper (dist n ==> dist n) (unseal_cond κ P C).
  Proof. intros I1 I2 HI. rewrite /unseal_cond. by repeat f_equiv. Qed.
  #[global] Instance unseal_contractive κ P C :
    Contractive (λ interp : TV, ▷ unseal_cond κ P C interp)%I.
  Proof. intros n I1 I2 HI. f_contractive_fin. by apply unseal_cond_ne, dist_later_S. Qed.

  (* (un)seal permission definitions *)
  Definition safe_to_seal (W : WORLD) (C : CmptName) (interp : TV) (b e : OType) : iPropO Σ :=
    ([∗ list] a ∈ (finz.seq_between b e),
       ∃ κ P, a ↪ₒ{κ} P ∗ seal_kind_ok κ C P ∗ ▷ seal_cond κ P C interp)%I.
  Definition safe_to_unseal (W : WORLD) (C : CmptName) (interp : TV) (b e : OType) : iPropO Σ :=
    ([∗ list] a ∈ (finz.seq_between b e),
       ∃ κ P, a ↪ₒ{κ} P ∗ seal_kind_ok κ C P ∗ ▷ unseal_cond κ P C interp)%I.

End logrel_fix.
