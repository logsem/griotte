From iris.algebra Require Import excl_auth.
From iris.proofmode Require Import proofmode.
From griotte Require Import named_props_extra.
From griotte Require Export context_switch_layout.

(** * The pool of user threads

    The invariant [Pool ts] of the user threads [ts]: the authority of
    [cur], the authority of the last owner (the thread whose zone halves
    the context-switch thread holds), and a slot per thread, by its state
    in [cur]. A suspended thread holds its save area, its mtdc token, its
    authorities at the values it resumes with, the halves of its zone
    unless it is the last owner, and its run; a thread being parked holds
    its authorities and the continuation of its kind of parking; a thread
    being resumed holds its authorities. *)

(** The state of user thread [t] in [cur]: [None] is suspended. *)
Definition st_of (c : option (Thread * TState)) (t : nat) : option TState :=
  match c with
  | Some (UserThread t', s) => if decide (t' = t) then Some s else None
  | _ => None
  end.

(** The thread that is not suspended, if any, is one of [ts]. *)
Definition cur_in (ts : list nat) (c : option (Thread * TState)) : Prop :=
  ∀ t s, c = Some (UserThread t, s) → t ∈ ts.

Lemma cur_alloc `{!inG Σ curUR} (c : option (Thread * TState)) :
  ⊢ |==> ∃ γ, own γ (●E (c : leibnizO _)) ∗ own γ (◯E (c : leibnizO _)).
Proof.
  iMod (own_alloc (●E (c : leibnizO _) ⋅ ◯E (c : leibnizO _))) as (γ) "[Ha Hf]".
  { apply excl_auth_valid. }
  iModIntro. iExists γ. iFrame.
Qed.

Section pool.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}
    {CL : ∀ t, CritLink Σ t} {CR : ∀ t, CritRoute Σ t (CL t)}
    {CSL : ContextSwitchLayout Σ CL CR}.

  #[local] Notation posture_of x :=
    (posture_res_gen (ceriseg := ceriseG_of x) (th := x) (CL := CL x) (CR := CR x)).
  #[local] Notation held_th x :=
    (held (ceriseg := ceriseG_of x) (th := x) (CL := CL x) (CR := CR x)).

  Lemma cur_frag_excl c c' : cur_frag c -∗ cur_frag c' -∗ False.
  Proof.
    iIntros "Hf Hf'". iCombine "Hf Hf'" gives %Hv. by apply excl_auth_frag_op_valid in Hv.
  Qed.

  (** The authorities of user thread [t] at the values [v], its mtdc at
      home, with the cover of [MSHWMB, MSHWM) by its zone and its stack
      base, its MSHWMB. *)
  Definition auths_at (t : nat) (v : resume_vals) : iProp Σ :=
    thread_auths (th := UserThread t) v.(rv_pc) v.(rv_regs)
      (mtdc_home_at (th := UserThread t)) v.(rv_mie) v.(rv_hwmb) v.(rv_hwm) v.(rv_zone) ∗
    ⌜zone_covers v.(rv_hwmb) v.(rv_hwm) v.(rv_zone)⌝ ∗
    hwm_base[u t] v.(rv_hwmb).

  #[global] Instance auths_at_timeless t v : Timeless (auths_at t v).
  Proof. rewrite /auths_at /thread_auths /hwm_rest. apply _. Qed.

  (** The continuation of a thread being parked, by kind. *)
  Definition park_cont (t : nat) (k : park_kind) : iProp Σ :=
    match k with
    | ParkIrq => ▷ safe[u t]
    | ParkYield b p =>
        ▷ (MIE ↦ₜ[u t] b -∗
           PC ↦ₚ[u t] yield_resume_pc p -∗
           held_th (UserThread t) b -∗
           safe (UserThread t))
    | ParkExit => True
    end.

  (** The slot of user thread [t] at its state [s], with the last owner
      [o]. A suspended thread ([None]) resumes with values allowed by its
      save area; if they have interrupts disabled, it gets its posture
      back. It holds the halves of its zone, unless it is the last owner:
      the context-switch thread holds them then. *)
  Definition slot (o : option (nat * gset Addr)) (t : nat) (s : option TState) : iProp Σ :=
    match s with
    | None =>
        ∃ (ws : list LWord) (v : resume_vals),
          "%Hok" ∷ ⌜resume_ok ws v⌝ ∗
          "Hsa" ∷ save_area_at t ws ∗
          "Hlent" ∷ mtdc_lent_at (th := UserThread t) ∗
          "Hauths" ∷ auths_at t v ∗
          "Hhalves" ∷ (if o is Some (t', zn) then
                         (if decide (t' = t) then ⌜zn = v.(rv_zone)⌝
                          else zone_halves[CtxSwitch] v.(rv_zone))
                       else zone_halves[CtxSwitch] v.(rv_zone)) ∗
          "Hcont" ∷ ▷ ((if v.(rv_mie) is InterruptEnabled then True
                        else posture_of (UserThread t) None None None None) -∗
                       £ 1 -∗
                       safe[u t])
    | Some Running => True
    | Some (Saving k v) =>
        "Hauths" ∷ auths_at t v ∗
        "Hcont" ∷ park_cont t k
    | Some (Resuming v) => "Hauths" ∷ auths_at t v
    end.

  (** The last owner [o] is one of [ts] and is not running; a thread
      being parked is the last owner, with its zone; a running thread
      leaves no last owner. *)
  Definition last_owner_ok (ts : list nat) (c : option (Thread * TState))
      (o : option (nat * gset Addr)) : Prop :=
    (∀ t zn, o = Some (t, zn) → t ∈ ts ∧ ∀ s, st_of c t = Some s → s ≠ Running) ∧
    (∀ t k v, c = Some (UserThread t, Saving k v) → o = Some (t, v.(rv_zone))) ∧
    (∀ t, c = Some (UserThread t, Running) → o = None).

  Definition Pool (ts : list nat) : iProp Σ :=
    ∃ c (o : option (nat * gset Addr)),
      "Hcur" ∷ cur_auth c ∗
      "%Hin" ∷ ⌜cur_in ts c⌝ ∗
      "Hlast_owner" ∷ ctx_last_owner_auth o ∗
      "%Hlast_owner_ok" ∷ ⌜last_owner_ok ts c o⌝ ∗
      "Hslots" ∷ [∗ list] t ∈ ts, slot o t (st_of c t).

  (** The slot of a thread other than the last owner [P] is the slot
      without a last owner. *)
  #[local] Lemma slot_lo_ne P zn t s :
    P ≠ t → slot (Some (P, zn)) t s ⊣⊢ slot None t s.
  Proof.
    intros Hne. destruct s as [s|]; first done. rewrite /slot /=.
    destruct (decide (P = t)); [done | reflexivity].
  Qed.

  (** The slots of the threads other than [t] do not depend on the state
      of [t]. *)
  #[local] Lemma slots_other o ts t s s' :
    t ∉ ts →
    ([∗ list] t' ∈ ts, slot o t' (st_of (Some (UserThread t, s)) t')) ⊣⊢
    ([∗ list] t' ∈ ts, slot o t' (st_of (Some (UserThread t, s')) t')).
  Proof.
    intros Hnin. apply big_sepL_proper. intros k t' Hk. rewrite /st_of.
    case_decide as Heq; last done.
    subst t'. exfalso. apply Hnin. by eapply list_elem_of_lookup_2.
  Qed.

  (** The slot of [t], and the slots at another state of [t]. *)
  #[local] Lemma slots_acc o ts t s :
    NoDup ts → t ∈ ts →
    ([∗ list] t' ∈ ts, slot o t' (st_of (Some (UserThread t, s)) t')) -∗
    slot o t (Some s) ∗
    ∀ s', slot o t (Some s') -∗ [∗ list] t' ∈ ts, slot o t' (st_of (Some (UserThread t, s')) t').
  Proof.
    intros Hnd Hin. apply list_elem_of_split in Hin as (l1 & l2 & ->).
    apply NoDup_app in Hnd as (_ & Hdisj & Hnd2).
    apply NoDup_cons in Hnd2 as [Hnin2 _].
    assert (t ∉ l1) as Hnin1.
    { intros Hin1. by apply (Hdisj t Hin1), list_elem_of_here. }
    rewrite !big_sepL_app !big_sepL_cons.
    iIntros "(H1 & Ht & H2)". rewrite {2}/st_of decide_True //. iFrame "Ht".
    iIntros (s') "Ht".
    rewrite big_sepL_app big_sepL_cons (slots_other o l1 t s s') // (slots_other o l2 t s s') //.
    iFrame "H1 H2". rewrite /st_of decide_True //.
  Qed.

  (** The slot of [t] at [c] and [o], and the slots at any state [c'] and
      last owner [o'] that agree with [c] and [o] on the other threads. *)
  #[local] Lemma slots_swap o o' ts t c s :
    NoDup ts → t ∈ ts → st_of c t = s →
    (∀ t' s'', t' ≠ t → slot o t' s'' ⊣⊢ slot o' t' s'') →
    ([∗ list] t' ∈ ts, slot o t' (st_of c t')) -∗
    slot o t s ∗
    ∀ c' s', ⌜st_of c' t = s'⌝ -∗ ⌜∀ t', t' ≠ t → st_of c t' = st_of c' t'⌝ -∗
             slot o' t s' -∗ [∗ list] t' ∈ ts, slot o' t' (st_of c' t').
  Proof.
    intros Hnd Hin Hs Ho. apply list_elem_of_split in Hin as (l1 & l2 & ->).
    apply NoDup_app in Hnd as (_ & Hdisj & Hnd2).
    apply NoDup_cons in Hnd2 as [Hnin2 _].
    assert (t ∉ l1) as Hnin1.
    { intros Hin1. by apply (Hdisj t Hin1), list_elem_of_here. }
    assert (∀ c' l, (∀ t', t' ≠ t → st_of c t' = st_of c' t') → t ∉ l →
      ([∗ list] t' ∈ l, slot o t' (st_of c t')) ⊣⊢ [∗ list] t' ∈ l, slot o' t' (st_of c' t'))
      as Hl.
    { intros c' l Hother Hnin. apply big_sepL_proper. intros k t' Hk.
      assert (t' ≠ t) as Hne.
      { intros ->. apply Hnin. by eapply list_elem_of_lookup_2. }
      rewrite Hother // Ho //. }
    rewrite !big_sepL_app !big_sepL_cons Hs.
    iIntros "(H1 & Ht & H2)". iFrame "Ht". iIntros (c' s' Hs' Hother) "Ht".
    rewrite big_sepL_app big_sepL_cons Hs' -(Hl c' l1) // -(Hl c' l2) //. iFrame.
  Qed.

  #[local] Lemma st_of_self t s : st_of (Some (UserThread t, s)) t = Some s.
  Proof. rewrite /st_of decide_True //. Qed.

  #[local] Lemma st_of_other t t' s : t' ≠ t → st_of (Some (UserThread t, s)) t' = None.
  Proof. intros Hne. by rewrite /st_of decide_False. Qed.

  (** Parking the running thread [t]: the slot of its kind into the
      pool; [t] becomes the last owner, with its zone. *)
  Lemma pool_save ts t k v E :
    NoDup ts → ↑Npool ⊆ E →
    inv Npool (Pool ts) -∗
    cur_frag (Some (UserThread t, Running)) -∗
    slot None t (Some (Saving k v)) -∗
    ctx_last_owner_frag None ={E}=∗
    cur_frag (Some (UserThread t, Saving k v)) ∗
    ctx_last_owner_frag (Some (t, v.(rv_zone))).
  Proof.
    iIntros (Hnd Hmask) "#Hinv Hf Hslot Hlast_owner_f".
    iInv Npool as "HP" "Hclose". rewrite /Pool.
    iDestruct "HP" as (c o) "(>Hcur & >%Hin & >Hlast_owner & >%Hlast_owner_ok & Hslots)".
    iDestruct (cur_agree with "Hcur Hf") as %->.
    iDestruct (ctx_last_owner_agree with "Hlast_owner Hlast_owner_f") as %->.
    iMod (cur_update _ _ (Some (UserThread t, Saving k v)) with "Hcur Hf") as "[Hcur Hf]".
    iMod (ctx_last_owner_update _ _ (Some (t, v.(rv_zone))) with "Hlast_owner Hlast_owner_f") as "[Hlast_owner Hlast_owner_f]".
    iDestruct (slots_swap None (Some (t, v.(rv_zone))) ts t _ (Some Running) with "Hslots")
      as "[_ Hslots]"; [done | by eapply Hin | apply st_of_self | |].
    { intros t' s'' Ht'. by rewrite slot_lo_ne. }
    iMod ("Hclose" with "[Hcur Hlast_owner Hslot Hslots]") as "_".
    { iNext. iExists (Some (UserThread t, Saving k v)), (Some (t, v.(rv_zone))).
      iFrame "Hcur Hlast_owner". iSplit; [|iSplit].
      - iPureIntro. intros t' s' [= <- _]. by eapply Hin.
      - iPureIntro. split_and!.
        + intros t' zn [= <- <-]. split; first by eapply Hin.
          intros s'. rewrite st_of_self. by intros [= <-].
        + intros t' k' v' [= <- <- <-]. done.
        + by intros t' ?.
      - iApply ("Hslots" $! _ (Some (Saving k v)) with "[] [] Hslot").
        + iPureIntro. apply st_of_self.
        + iPureIntro. intros t' Ht'. by rewrite !st_of_other. }
    iModIntro. iFrame.
  Qed.

  (** Running the resumed thread [B]: its authorities out of the pool; a
      running thread leaves no last owner. *)
  Lemma pool_run ts B v E :
    NoDup ts → ↑Npool ⊆ E →
    inv Npool (Pool ts) -∗
    cur_frag (Some (UserThread B, Resuming v)) -∗
    ctx_last_owner_frag None ={E}=∗
    cur_frag (Some (UserThread B, Running)) ∗
    auths_at B v ∗
    ctx_last_owner_frag None.
  Proof.
    iIntros (Hnd Hmask) "#Hinv Hf Hlast_owner_f".
    iInv Npool as "HP" "Hclose". rewrite /Pool.
    iDestruct "HP" as (c o) "(>Hcur & >%Hin & >Hlast_owner & >%Hlast_owner_ok & Hslots)".
    iDestruct (cur_agree with "Hcur Hf") as %->.
    iDestruct (ctx_last_owner_agree with "Hlast_owner Hlast_owner_f") as %->.
    iMod (cur_update _ _ (Some (UserThread B, Running)) with "Hcur Hf") as "[Hcur Hf]".
    iDestruct (slots_acc None ts B (Resuming v) with "Hslots") as "[Hauths Hslots]";
      [done | by eapply Hin |].
    iMod "Hauths".
    iMod ("Hclose" with "[Hcur Hlast_owner Hslots]") as "_".
    { iNext. iExists (Some (UserThread B, Running)), None. iFrame "Hcur Hlast_owner". iSplit; [|iSplit].
      - iPureIntro. intros t' s' [= <- _]. by eapply Hin.
      - iPureIntro. split_and!; [done | done | done].
      - by iApply "Hslots". }
    iModIntro. iFrame.
  Qed.

  (** Parking user thread [t]: the caller turns the Saving slot's contents
      into its Suspended slot, as the last owner; [cur] becomes [None]. *)
  Lemma pool_park ts t k v E :
    NoDup ts → ↑Npool ⊆ E →
    inv Npool (Pool ts) -∗
    cur_frag (Some (UserThread t, Saving k v)) -∗
    (auths_at t v -∗ ▷ park_cont t k ={E ∖ ↑Npool}=∗ slot (Some (t, v.(rv_zone))) t None) ={E}=∗
    cur_frag None.
  Proof.
    iIntros (Hnd Hmask) "#Hinv Hf Hpark".
    iInv Npool as "HP" "Hclose". rewrite /Pool.
    iDestruct "HP" as (c o) "(>Hcur & >%Hin & >Hlast_owner & >%Hlast_owner_ok & Hslots)".
    iDestruct (cur_agree with "Hcur Hf") as %->.
    destruct Hlast_owner_ok as (Hlast_owner1 & Hlast_owner2 & Hlast_owner3).
    pose proof (Hlast_owner2 t k v eq_refl) as ->.
    iMod (cur_update _ _ None with "Hcur Hf") as "[Hcur Hf]".
    iDestruct (slots_swap _ _ ts t _ (Some (Saving k v)) with "Hslots") as "[Hslot Hslots]";
      [done | by eapply Hin | apply st_of_self | done |].
    iDestruct "Hslot" as "[Hauths Hcont]".
    iMod "Hauths".
    iMod ("Hpark" with "Hauths Hcont") as "Hslot".
    iMod ("Hclose" with "[Hcur Hlast_owner Hslot Hslots]") as "_"; last done.
    iNext. iExists None, (Some (t, v.(rv_zone))). iFrame "Hcur Hlast_owner". iSplit; [|iSplit].
    - iPureIntro. by intros t' s' ?.
    - iPureIntro. split_and!.
      + intros t' zn [= <- <-]. split; first by eapply Hin. done.
      + done.
      + done.
    - iApply ("Hslots" $! None None with "[//] [] [Hslot]").
      { iPureIntro. intros t' Ht'. by rewrite st_of_other. }
      iDestruct "Hslot" as (ws w') "(Hok & Hsa & Hlent & Hauths & Hhalves & Hcont)".
      iExists ws, w'. iFrame.
  Qed.

  (** Reading the slot of the suspended thread [B]: it becomes Resuming
      with values its save area allows, which cover its zone; its save
      area, mtdc token and run come out, and the halves of its zone unless
      it is the last owner [o]. The run is under two laters: the one of the
      invariant and the one of the slot. *)
  Lemma pool_read ts B o E :
    NoDup ts → B ∈ ts → ↑Npool ⊆ E →
    inv Npool (Pool ts) -∗
    cur_frag None -∗
    ctx_last_owner_frag o ={E}=∗
    ∃ (ws : list LWord) (v : resume_vals),
      "Hcur" ∷ cur_frag (Some (UserThread B, Resuming v)) ∗
      "Hlast_owner" ∷ ctx_last_owner_frag o ∗
      "%Hok" ∷ ⌜resume_ok ws v⌝ ∗
      "%Hcov" ∷ ⌜zone_covers v.(rv_hwmb) v.(rv_hwm) v.(rv_zone)⌝ ∗
      "%Hlast_owner_B" ∷ ⌜∀ zn, o = Some (B, zn) → zn = v.(rv_zone)⌝ ∗
      "Hhalves" ∷ ▷ (if o is Some (B', _) then
                      (if decide (B' = B) then True else zone_halves[CtxSwitch] v.(rv_zone))
                    else zone_halves[CtxSwitch] v.(rv_zone)) ∗
      "Hsa" ∷ ▷ save_area_at B ws ∗
      "Hlent" ∷ ▷ mtdc_lent_at (th := UserThread B) ∗
      "Hcont" ∷ ▷ ▷ ((if v.(rv_mie) is InterruptEnabled then True
                      else posture_of (UserThread B) None None None None) -∗
                     £ 1 -∗
                     safe[u B]).
  Proof.
    iIntros (Hnd HB Hmask) "#Hinv Hf Hlast_owner_f".
    iInv Npool as "HP" "Hclose". rewrite /Pool.
    iDestruct "HP" as (c o') "(>Hcur & >%Hin & >Hlast_owner & >%Hlast_owner_ok & Hslots)".
    iDestruct (cur_agree with "Hcur Hf") as %->.
    iDestruct (ctx_last_owner_agree with "Hlast_owner Hlast_owner_f") as %->.
    iDestruct (slots_swap o o ts B None None with "Hslots") as "[Hslot Hslots]"; [done..|].
    iMod (bi.later_exist_except_0 with "Hslot") as (ws) "Hslot".
    iMod (bi.later_exist_except_0 with "Hslot") as (v) "Hslot".
    iDestruct "Hslot" as "(>%Hok & Hsa & Hlent & >Hauths & Hhalves & Hcont)".
    iDestruct "Hauths" as "(Hauths & %Hcov & #Hbase)".
    iAssert (▷ ⌜∀ zn, o = Some (B, zn) → zn = v.(rv_zone)⌝ ∗
             ▷ (if o is Some (B', _) then
                  (if decide (B' = B) then True else zone_halves[CtxSwitch] v.(rv_zone))
                else zone_halves[CtxSwitch] v.(rv_zone)))%I
      with "[Hhalves]" as "[>%Hlast_owner_B Hhalves]".
    { destruct o as [ [B' zn]|]; last (iSplitR; [iPureIntro; done | iExact "Hhalves"]).
      case_decide as HB'.
      - subst B'.
        iSplitL; [iNext; iDestruct "Hhalves" as %Hzn; iPureIntro; intros zn' [=]; by subst | done].
      - iSplitR; last iExact "Hhalves". iPureIntro. intros zn' [=]. done. }
    iMod (cur_update _ _ (Some (UserThread B, Resuming v)) with "Hcur Hf") as "[Hcur Hf]".
    iMod ("Hclose" with "[Hcur Hlast_owner Hauths Hslots]") as "_".
    { iNext. iExists (Some (UserThread B, Resuming v)), o. iFrame "Hcur Hlast_owner". iSplit; [|iSplit].
      - iPureIntro. by intros t' s' [= <- _].
      - iPureIntro. destruct Hlast_owner_ok as (Hlast_owner1 & Hlast_owner2 & Hlast_owner3). split_and!.
        + intros t' zn Ho. destruct (Hlast_owner1 t' zn Ho) as [Ht' _]. split; first done.
          intros s'. rewrite /st_of. case_decide; last done. by intros [= <-].
        + done.
        + done.
      - iApply ("Hslots" $! _ (Some (Resuming v)) with "[] [] [Hauths]").
        + iPureIntro. apply st_of_self.
        + iPureIntro. intros t' Ht'. by rewrite st_of_other.
        + rewrite /slot. iFrame "Hauths Hbase". done. }
    iModIntro. iExists ws, v. iFrame "Hf Hlast_owner_f Hsa Hlent Hcont Hhalves". done.
  Qed.

  (** At the opening write of the HWM restore window: the halves of the last
      owner [P] return to its slot (none if [P] is [B], whose halves stay
      lent), and there is no last owner any more. *)
  Lemma pool_unlend ts B v P zn E :
    NoDup ts → ↑Npool ⊆ E →
    inv Npool (Pool ts) -∗
    cur_frag (Some (UserThread B, Resuming v)) -∗
    ctx_last_owner_frag (Some (P, zn)) -∗
    (if decide (P = B) then True else zone_halves[CtxSwitch] zn) ={E}=∗
    cur_frag (Some (UserThread B, Resuming v)) ∗
    ctx_last_owner_frag None.
  Proof.
    iIntros (Hnd Hmask) "#Hinv Hf Hlast_owner_f Hhalves".
    iInv Npool as "HP" "Hclose". rewrite /Pool.
    iDestruct "HP" as (c o) "(>Hcur & >%Hin & >Hlast_owner & >%Hlast_owner_ok & Hslots)".
    iDestruct (cur_agree with "Hcur Hf") as %->.
    iDestruct (ctx_last_owner_agree with "Hlast_owner Hlast_owner_f") as %->.
    iMod (ctx_last_owner_update _ _ None with "Hlast_owner Hlast_owner_f") as "[Hlast_owner Hlast_owner_f]".
    destruct Hlast_owner_ok as (Hlast_owner1 & Hlast_owner2 & Hlast_owner3).
    destruct (Hlast_owner1 P zn eq_refl) as [HP _].
    case_decide as HPB.
    - (* [B] is the last owner: its slot is Resuming, the others do not
         depend on the last owner. *)
      subst P.
      iDestruct (slots_swap (Some (B, zn)) None ts B _ (Some (Resuming v)) with "Hslots")
        as "[Hslot Hslots]"; [done | done | apply st_of_self | |].
      { intros t' s'' Ht'. by rewrite slot_lo_ne. }
      iMod ("Hclose" with "[Hcur Hlast_owner Hslot Hslots]") as "_".
      { iNext. iExists _, None. iFrame "Hcur Hlast_owner". iSplit; [done|iSplit].
        - iPureIntro. split_and!; done.
        - iApply ("Hslots" $! _ (Some (Resuming v)) with "[] [] Hslot");
            iPureIntro; [apply st_of_self | done]. }
      iModIntro. iFrame.
    - (* The halves of [P], suspended, return to its slot. *)
      iDestruct (slots_swap (Some (P, zn)) None ts P _ None with "Hslots")
        as "[Hslot Hslots]"; [done | done | by rewrite st_of_other | |].
      { intros t' s'' Ht'. by rewrite slot_lo_ne. }
      iMod (bi.later_exist_except_0 with "Hslot") as (ws) "Hslot".
      iMod (bi.later_exist_except_0 with "Hslot") as (vP) "Hslot".
      iEval (rewrite decide_True //) in "Hslot".
      iDestruct "Hslot" as "(Hok & Hsa & Hlentm & Hauths & >%Hzn & Hcont)". subst zn.
      iMod ("Hclose" with "[Hcur Hlast_owner Hslots Hok Hsa Hlentm Hauths Hhalves Hcont]") as "_".
      { iNext. iExists _, None. iFrame "Hcur Hlast_owner". iSplit; [done|iSplit].
        - iPureIntro. split_and!; done.
        - iApply ("Hslots" $! (Some (UserThread B, Resuming v)) None with "[] [] [-]").
          + iPureIntro. by rewrite st_of_other.
          + done.
          + iExists ws, vP. iFrame. }
      iModIntro. iFrame.
  Qed.

  (** The thread of a Saving or Resuming token is one of the pool's. *)
  Lemma pool_cur_in ts t s E :
    ↑Npool ⊆ E →
    inv Npool (Pool ts) -∗
    cur_frag (Some (UserThread t, s)) ={E}=∗
    ⌜t ∈ ts⌝ ∗ cur_frag (Some (UserThread t, s)).
  Proof.
    iIntros (Hmask) "#Hinv Hf".
    iInv Npool as "HP" "Hclose". rewrite /Pool.
    iDestruct "HP" as (c o) "(>Hcur & >%Hin & Hlast_owner & >%Hlast_owner_ok & Hslots)".
    iDestruct (cur_agree with "Hcur Hf") as %->.
    iMod ("Hclose" with "[Hcur Hlast_owner Hslots]") as "_".
    { iNext. iExists _, _. by iFrame. }
    iModIntro. iFrame "Hf". iPureIntro. by eapply Hin.
  Qed.

  (** The PC of a thread being parked is the value of its PC authority in
      its Saving slot. *)
  Lemma pool_saving_pc (ts : list nat) (t : nat) (k : park_kind) (v : resume_vals)
      (lpc : LWord) E :
    ↑Npool ⊆ E →
    inv Npool (Pool ts) -∗
    cur_frag (Some (UserThread t, Saving k v)) -∗
    PC ↦ₚ[u t] lpc ={E}=∗
    ⌜v.(rv_pc) = lpc⌝ ∗
    cur_frag (Some (UserThread t, Saving k v)) ∗
    PC ↦ₚ[u t] lpc.
  Proof.
    iIntros (Hmask) "#Hinv Hf HPC".
    iInv Npool as "HP" "Hclose". rewrite /Pool.
    iDestruct "HP" as (c o) "(>Hcur & >%Hin & Hlast_owner & >%Hlast_owner_ok & Hslots)".
    iDestruct (cur_agree with "Hcur Hf") as %->.
    assert (t ∈ ts) as Ht by (by eapply Hin).
    apply list_elem_of_lookup in Ht as [i Hi].
    assert (st_of (Some (UserThread t, Saving k v)) t = Some (Saving k v)) as Hst.
    { rewrite /st_of decide_True //. }
    iAssert (▷ (slot o t (Some (Saving k v)) ∗
              (slot o t (Some (Saving k v)) -∗
               ([∗ list] t' ∈ ts, slot o t' (st_of (Some (UserThread t, Saving k v)) t')))))%I
      with "[Hslots]" as "[Hslot Hslots]".
    { iNext. iDestruct (big_sepL_lookup_acc with "Hslots") as "[Hslot Hslots]"; first exact Hi.
      rewrite Hst. iFrame. }
    iDestruct "Hslot" as "[Hauths Hcont]".
    iMod "Hauths".
    iDestruct "Hauths" as "((HPC_a & Hauths) & Hcov)".
    iDestruct (PC_agree with "HPC_a HPC") as %Hpc.
    iMod ("Hclose" with "[- Hf HPC]") as "_".
    { iNext. iExists _, _. iFrame "Hcur Hlast_owner". iSplit; first done. iSplit; first done.
      iApply "Hslots". iFrame. }
    iModIntro. by iFrame.
  Qed.
End pool.
