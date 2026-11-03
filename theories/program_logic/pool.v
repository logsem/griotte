From iris.algebra Require Import excl_auth.
From iris.proofmode Require Import proofmode.
From griotte Require Import named_props_extra.
From griotte Require Export context_switch_layout.

(** * The pool of user threads

    The invariant [Pool ts] of the user threads [ts]: the authority of
    [cur], and a slot per thread, by its state in [cur]. A suspended thread
    holds its save area, its mtdc token, its authorities at the values it
    resumes with, and its run; a thread being parked holds its authorities
    and the continuation of its kind of parking; a thread being resumed
    holds its authorities. *)

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
      home. *)
  Definition auths_at (t : nat) (v : resume_vals) : iProp Σ :=
    thread_auths (th := UserThread t) v.(rv_pc) v.(rv_regs)
      (mtdc_home_at (th := UserThread t)) v.(rv_mie).

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

  (** The slot of user thread [t] at its state [s]. A suspended thread
      ([None]) resumes with values allowed by its save area; if they have
      interrupts disabled, it gets its posture back. *)
  Definition slot (t : nat) (s : option TState) : iProp Σ :=
    match s with
    | None =>
        ∃ (ws : list LWord) (v : resume_vals),
          "%Hok" ∷ ⌜resume_ok ws v⌝ ∗
          "Hsa" ∷ save_area_at t ws ∗
          "Hlent" ∷ mtdc_lent_at (th := UserThread t) ∗
          "Hauths" ∷ auths_at t v ∗
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

  Definition Pool (ts : list nat) : iProp Σ :=
    ∃ c,
      "Hcur" ∷ cur_auth c ∗
      "%Hin" ∷ ⌜cur_in ts c⌝ ∗
      "Hslots" ∷ [∗ list] t ∈ ts, slot t (st_of c t).

  (** The slots of the threads other than [t] do not depend on the state
      of [t]. *)
  Lemma slots_other ts t s s' :
    t ∉ ts →
    ([∗ list] t' ∈ ts, slot t' (st_of (Some (UserThread t, s)) t')) ⊣⊢
    ([∗ list] t' ∈ ts, slot t' (st_of (Some (UserThread t, s')) t')).
  Proof.
    intros Hnin. apply big_sepL_proper. intros k t' Hk. rewrite /st_of.
    case_decide as Heq; last done.
    subst t'. exfalso. apply Hnin. by eapply list_elem_of_lookup_2.
  Qed.

  (** The slot of [t], and the slots at another state of [t]. *)
  Lemma slots_acc ts t s :
    NoDup ts → t ∈ ts →
    ([∗ list] t' ∈ ts, slot t' (st_of (Some (UserThread t, s)) t')) -∗
    slot t (Some s) ∗
    ∀ s', slot t (Some s') -∗ [∗ list] t' ∈ ts, slot t' (st_of (Some (UserThread t, s')) t').
  Proof.
    intros Hnd Hin. apply list_elem_of_split in Hin as (l1 & l2 & ->).
    apply NoDup_app in Hnd as (_ & Hdisj & Hnd2).
    apply NoDup_cons in Hnd2 as [Hnin2 _].
    assert (t ∉ l1) as Hnin1.
    { intros Hin1. by apply (Hdisj t Hin1), list_elem_of_here. }
    rewrite !big_sepL_app !big_sepL_cons.
    iIntros "(H1 & Ht & H2)". rewrite {2}/st_of decide_True //. iFrame "Ht".
    iIntros (s') "Ht".
    rewrite big_sepL_app big_sepL_cons (slots_other l1 t s s') // (slots_other l2 t s s') //.
    iFrame "H1 H2". rewrite /st_of decide_True //.
  Qed.

  (** Parking the running thread [t]: the slot of its kind into the
      pool. *)
  Lemma pool_save ts t k v E :
    NoDup ts → ↑Npool ⊆ E →
    inv Npool (Pool ts) -∗
    cur_frag (Some (UserThread t, Running)) -∗
    slot t (Some (Saving k v)) ={E}=∗
    cur_frag (Some (UserThread t, Saving k v)).
  Proof.
    iIntros (Hnd Hmask) "#Hinv Hf Hslot".
    iInv Npool as "HP" "Hclose". rewrite /Pool.
    iDestruct "HP" as (c) "(>Hcur & >%Hin & Hslots)".
    iDestruct (cur_agree with "Hcur Hf") as %->.
    iMod (cur_update _ _ (Some (UserThread t, Saving k v)) with "Hcur Hf") as "[Hcur Hf]".
    iDestruct (slots_acc ts t Running with "Hslots") as "[_ Hslots]"; [done | by eapply Hin |].
    iMod ("Hclose" with "[Hcur Hslot Hslots]") as "_"; last done.
    iNext. iExists (Some (UserThread t, Saving k v)). iFrame "Hcur". iSplit.
    - iPureIntro. intros t' s' [= <- _]. by eapply Hin.
    - by iApply "Hslots".
  Qed.

  (** Running the resumed thread [B]: its authorities out of the pool. *)
  Lemma pool_run ts B v E :
    NoDup ts → ↑Npool ⊆ E →
    inv Npool (Pool ts) -∗
    cur_frag (Some (UserThread B, Resuming v)) ={E}=∗
    cur_frag (Some (UserThread B, Running)) ∗
    auths_at B v.
  Proof.
    iIntros (Hnd Hmask) "#Hinv Hf".
    iInv Npool as "HP" "Hclose". rewrite /Pool.
    iDestruct "HP" as (c) "(>Hcur & >%Hin & Hslots)".
    iDestruct (cur_agree with "Hcur Hf") as %->.
    iMod (cur_update _ _ (Some (UserThread B, Running)) with "Hcur Hf") as "[Hcur Hf]".
    iDestruct (slots_acc ts B (Resuming v) with "Hslots") as "[Hauths Hslots]";
      [done | by eapply Hin |].
    rewrite /= /auths_at /thread_auths.
    iDestruct "Hauths" as "(>HPC & >Hregs & >Hmtdc & >HMIE)".
    iMod ("Hclose" with "[Hcur Hslots]") as "_".
    { iNext. iExists (Some (UserThread B, Running)). iFrame "Hcur". iSplit.
      - iPureIntro. intros t' s' [= <- _]. by eapply Hin.
      - by iApply "Hslots". }
    iModIntro. iFrame.
  Qed.
End pool.
