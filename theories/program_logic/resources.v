From iris.base_logic Require Export invariants na_invariants gen_heap ghost_map ghost_var saved_prop.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl_auth csum.
From griotte Require Export logical_words alloc_registry.

(** * The resources of Griotte

    The ghost state of the machine (the PC, the per-thread system registers
    mtdc, MIE, MSHWMB and MSHWM with the zone, and MPIE), the classes of a
    thread's instance and of the resources shared by the threads, and the
    points-to notations. *)

(** Non-atomic invariants: the pool of the running thread. Thread-level
    code names the pool of a thread [th] as [tpool th]. *)
Class cerise_na_invs Σ :=
  {
    na_invG :: na_invG Σ;
    cerise_pool : na_inv_pool_name;
  }.
#[export] Hint Mode cerise_na_invs - : typeclass_instances.

(** The logical PC: a single value, whose authoritative part is in the state
    interpretation. The fragment is fractional; [PC_frag] is the full one.
    The PC is not a general register. *)
Class pcG Σ := PcG {
  pc_inG :: ghost_mapG Σ unit LWord;
  pc_name : gname;
}.
#[export] Hint Mode pcG - : typeclass_instances.

Class pcGpreS Σ := { pc_preG_inG :: ghost_mapG Σ unit LWord }.
#[export] Hint Mode pcGpreS - : typeclass_instances.
Definition pcΣ : gFunctors := ghost_mapΣ unit LWord.
#[global] Instance subG_pcGpreS {Σ} : subG pcΣ Σ → pcGpreS Σ.
Proof. solve_inG. Qed.

Section pc_resource.
  Context `{!pcG Σ}.

  Definition PC_auth (lpc : LWord) : iProp Σ := ghost_map_auth pc_name 1 {[ tt := lpc ]}.
  Definition PC_fragq (dq : dfrac) (lpc : LWord) : iProp Σ := tt ↪[pc_name]{dq} lpc.
  Definition PC_frag (lpc : LWord) : iProp Σ := PC_fragq (DfracOwn 1) lpc.

  #[global] Instance PC_auth_timeless lpc : Timeless (PC_auth lpc).
  Proof. rewrite /PC_auth. apply _. Qed.
  #[global] Instance PC_fragq_timeless dq lpc : Timeless (PC_fragq dq lpc).
  Proof. rewrite /PC_fragq. apply _. Qed.
  #[global] Instance PC_frag_timeless lpc : Timeless (PC_frag lpc).
  Proof. rewrite /PC_frag. apply _. Qed.

  Lemma PC_agreeq dq lpc lpc' : PC_auth lpc -∗ PC_fragq dq lpc' -∗ ⌜lpc = lpc'⌝.
  Proof.
    iIntros "Ha Hf". iDestruct (ghost_map_lookup with "Ha Hf") as %Hl.
    by rewrite lookup_singleton_eq in Hl; simplify_eq.
  Qed.

  Lemma PC_agree lpc lpc' : PC_auth lpc -∗ PC_frag lpc' -∗ ⌜lpc = lpc'⌝.
  Proof. apply PC_agreeq. Qed.

  Lemma PC_update lpc lpc' lpc'' : PC_auth lpc -∗ PC_frag lpc' ==∗ PC_auth lpc'' ∗ PC_frag lpc''.
  Proof.
    iIntros "Ha Hf". iMod (ghost_map_update lpc'' with "Ha Hf") as "[Ha $]".
    by rewrite /PC_auth insert_singleton.
  Qed.

  Lemma PC_frag_excl_q dq lpc lpc' : PC_frag lpc -∗ PC_fragq dq lpc' -∗ False.
  Proof.
    iIntros "H1 H2". iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[Hv _].
    apply dfrac_valid_own_l in Hv. by destruct (irreflexivity (<)%Qp 1%Qp).
  Qed.

  Lemma PC_frag_excl lpc lpc' : PC_frag lpc -∗ PC_frag lpc' -∗ False.
  Proof. apply PC_frag_excl_q. Qed.

  (** Two halves: agreement, and the full fragment back. *)
  Lemma PC_frag_split lpc :
    PC_frag lpc ⊣⊢ PC_fragq (DfracOwn (1/2)) lpc ∗ PC_fragq (DfracOwn (1/2)) lpc.
  Proof.
    rewrite /PC_frag /PC_fragq. iSplit.
    - iIntros "[$ $]".
    - iIntros "[H1 H2]". by iCombine "H1 H2" as "H".
  Qed.

  Lemma PC_halves_merge lpc lpc' :
    PC_fragq (DfracOwn (1/2)) lpc -∗ PC_fragq (DfracOwn (1/2)) lpc' -∗
    ⌜lpc = lpc'⌝ ∗ PC_frag lpc.
  Proof.
    iIntros "H1 H2". iDestruct (ghost_map_elem_agree with "H1 H2") as %<-.
    iSplit; first done. rewrite PC_frag_split. iFrame.
  Qed.
End pc_resource.

Lemma PC_init `{!pcGpreS Σ} (lpc : LWord) :
  ⊢ |==> ∃ (pg : pcG Σ), PC_auth lpc ∗ PC_frag lpc.
Proof.
  iMod (ghost_map_alloc {[ tt := lpc ]}) as (γ) "[Ha Hf]".
  rewrite big_sepM_singleton. iModIntro. iExists (PcG _ _ γ). iFrame.
Qed.

(** * The per-thread system registers and MPIE

    mtdc and MIE are per thread, MPIE is shared; each has its own ghost
    state. The ghost value of a thread's mtdc stands for a logical word:
    the trusted stack capability up to its locality ([TStack p b e a],
    written [Capₗ p _ b e a]), or exactly [v] ([ExceptionScratch v]). *)
Inductive mtdc_val :=
| TStack (p : Perm) (b e a : Addr)
| ExceptionScratch (v : LWord).

(** The logical mtdc words that the ghost value [m] stands for: the trusted
    stack up to its locality, or exactly [v]. *)
Definition mtdc_match (m : mtdc_val) (vm : LWord) : Prop :=
  match m with
  | TStack p b e a => ∃ g, vm = Cap p g b e a
  | ExceptionScratch v => vm = v
  end.

(** [Capₗ p _ b e a]: a capability up to its locality. *)
Notation "'Capₗ' p '_' b e a" := (TStack p b e a)
  (at level 10, p, b, e, a at level 9, format "'Capₗ'  p  _  b  e  a").
Coercion ExceptionScratch : LWord >-> mtdc_val.

Lemma mtdc_match_ExceptionScratch v : mtdc_match (ExceptionScratch v) v.
Proof. done. Qed.

#[global] Instance mtdc_val_eq_dec : EqDecision mtdc_val.
Proof. solve_decision. Defined.

Definition mtdcUR := excl_authUR (leibnizO mtdc_val).
Definition intstUR := excl_authUR (leibnizO InterruptStatus).

Class mtdcG Σ := MtdcG { mtdc_inG :: inG Σ mtdcUR; mtdc_name : gname }.
#[export] Hint Mode mtdcG - : typeclass_instances.
Class mieG Σ := MieG { mie_inG :: inG Σ intstUR; mie_name : gname }.
#[export] Hint Mode mieG - : typeclass_instances.
Class mpieG Σ := MpieG { mpie_inG :: inG Σ intstUR; mpie_name : gname }.
#[export] Hint Mode mpieG - : typeclass_instances.

Class mtdcGpreS Σ := { mtdc_preG_inG :: inG Σ mtdcUR }.
#[export] Hint Mode mtdcGpreS - : typeclass_instances.
Definition mtdcΣ : gFunctors := #[GFunctor mtdcUR].
#[global] Instance subG_mtdcGpreS {Σ} : subG mtdcΣ Σ → mtdcGpreS Σ.
Proof. solve_inG. Qed.

Class intstGpreS Σ := { intst_preG_inG :: inG Σ intstUR }.
#[export] Hint Mode intstGpreS - : typeclass_instances.
Definition intstΣ : gFunctors := #[GFunctor intstUR].
#[global] Instance subG_intstGpreS {Σ} : subG intstΣ Σ → intstGpreS Σ.
Proof. solve_inG. Qed.

Section mtdc_resource.
  Context `{!mtdcG Σ}.

  Definition mtdc_auth (m : mtdc_val) : iProp Σ := own mtdc_name (●E (m : leibnizO mtdc_val)).
  Definition mtdc_frag (m : mtdc_val) : iProp Σ := own mtdc_name (◯E (m : leibnizO mtdc_val)).

  #[global] Instance mtdc_auth_timeless m : Timeless (mtdc_auth m).
  Proof. apply _. Qed.
  #[global] Instance mtdc_frag_timeless m : Timeless (mtdc_frag m).
  Proof. apply _. Qed.

  Lemma mtdc_agree m m' : mtdc_auth m -∗ mtdc_frag m' -∗ ⌜m = m'⌝.
  Proof. iIntros "Ha Hf". iCombine "Ha Hf" gives %Hv. by apply excl_auth_agree_L in Hv. Qed.

  Lemma mtdc_update m m' m'' : mtdc_auth m -∗ mtdc_frag m' ==∗ mtdc_auth m'' ∗ mtdc_frag m''.
  Proof.
    iIntros "Ha Hf". iMod (own_update_2 with "Ha Hf") as "[$ $]"; last done.
    apply excl_auth_update.
  Qed.

  Lemma mtdc_frag_excl m m' : mtdc_frag m -∗ mtdc_frag m' -∗ False.
  Proof. iIntros "H1 H2". iCombine "H1 H2" gives %Hv. by apply excl_auth_frag_op_valid in Hv. Qed.
End mtdc_resource.

Section mie_resource.
  Context `{!mieG Σ}.
  Definition MIE_auth (b : InterruptStatus) : iProp Σ := own mie_name (●E (b : leibnizO _)).
  Definition MIE_frag (b : InterruptStatus) : iProp Σ := own mie_name (◯E (b : leibnizO _)).

  #[global] Instance MIE_auth_timeless b : Timeless (MIE_auth b).
  Proof. apply _. Qed.
  #[global] Instance MIE_frag_timeless b : Timeless (MIE_frag b).
  Proof. apply _. Qed.

  Lemma MIE_agree b b' : MIE_auth b -∗ MIE_frag b' -∗ ⌜b = b'⌝.
  Proof. iIntros "Ha Hf". iCombine "Ha Hf" gives %Hv. by apply excl_auth_agree_L in Hv. Qed.

  Lemma MIE_update b b' b'' : MIE_auth b -∗ MIE_frag b' ==∗ MIE_auth b'' ∗ MIE_frag b''.
  Proof.
    iIntros "Ha Hf". iMod (own_update_2 with "Ha Hf") as "[$ $]"; last done.
    apply excl_auth_update.
  Qed.

  Lemma MIE_frag_excl b b' : MIE_frag b -∗ MIE_frag b' -∗ False.
  Proof. iIntros "H1 H2". iCombine "H1 H2" gives %Hv. by apply excl_auth_frag_op_valid in Hv. Qed.
End mie_resource.

Section mpie_resource.
  Context `{!mpieG Σ}.
  Definition MPIE_auth (b : InterruptStatus) : iProp Σ := own mpie_name (●E (b : leibnizO _)).
  Definition MPIE_frag (b : InterruptStatus) : iProp Σ := own mpie_name (◯E (b : leibnizO _)).

  #[global] Instance MPIE_auth_timeless b : Timeless (MPIE_auth b).
  Proof. apply _. Qed.
  #[global] Instance MPIE_frag_timeless b : Timeless (MPIE_frag b).
  Proof. apply _. Qed.

  Lemma MPIE_agree b b' : MPIE_auth b -∗ MPIE_frag b' -∗ ⌜b = b'⌝.
  Proof. iIntros "Ha Hf". iCombine "Ha Hf" gives %Hv. by apply excl_auth_agree_L in Hv. Qed.

  Lemma MPIE_update b b' b'' : MPIE_auth b -∗ MPIE_frag b' ==∗ MPIE_auth b'' ∗ MPIE_frag b''.
  Proof.
    iIntros "Ha Hf". iMod (own_update_2 with "Ha Hf") as "[$ $]"; last done.
    apply excl_auth_update.
  Qed.

  Lemma MPIE_frag_excl b b' : MPIE_frag b -∗ MPIE_frag b' -∗ False.
  Proof. iIntros "H1 H2". iCombine "H1 H2" gives %Hv. by apply excl_auth_frag_op_valid in Hv. Qed.
End mpie_resource.

Lemma mtdc_init `{!mtdcGpreS Σ} (m : mtdc_val) :
  ⊢ |==> ∃ (g : mtdcG Σ), mtdc_auth m ∗ mtdc_frag m.
Proof.
  iMod (own_alloc (●E (m : leibnizO mtdc_val) ⋅ ◯E (m : leibnizO mtdc_val))) as (γ) "[Ha Hf]".
  { apply excl_auth_valid. }
  iModIntro. iExists (MtdcG _ _ γ). iFrame.
Qed.

Lemma MIE_init `{!intstGpreS Σ} (b : InterruptStatus) :
  ⊢ |==> ∃ (g : mieG Σ), MIE_auth b ∗ MIE_frag b.
Proof.
  iMod (own_alloc (●E (b : leibnizO _) ⋅ ◯E (b : leibnizO _))) as (γ) "[Ha Hf]".
  { apply excl_auth_valid. }
  iModIntro. iExists (MieG _ _ γ). iFrame.
Qed.

Lemma MPIE_init `{!intstGpreS Σ} (b : InterruptStatus) :
  ⊢ |==> ∃ (g : mpieG Σ), MPIE_auth b ∗ MPIE_frag b.
Proof.
  iMod (own_alloc (●E (b : leibnizO _) ⋅ ◯E (b : leibnizO _))) as (γ) "[Ha Hf]".
  { apply excl_auth_valid. }
  iModIntro. iExists (MpieG _ _ γ). iFrame.
Qed.

(** * The stack high-water mark of a thread

    MSHWMB and MSHWM are per thread: each has an exclusive ghost value, the
    integer of its logical value. The zone of the thread is a ghost set of
    addresses with an exclusive token per address. Four more ghosts carry
    the high-water mark across thread switches:
    - [lent]: the set of addresses whose halves the thread holds for another
      thread (the context-switch thread holds the halves of the parked
      thread's zone); empty for a user thread;
    - [pend]: the HWM restore window of the context-switch thread, closed
      ([None]) or open with the cover base [Some hbT]; a half in the state
      interpretation, a quarter in the window clause, a quarter with the
      code;
    - [lo]: the last owner, the user thread whose halves the context-switch
      thread holds, and its zone; used at the context-switch thread's
      instance only;
    - [base]: the stack base of the thread, persistent: its MSHWMB at every
      hand-in, and word 20 of its save area wherever the area rests. *)
Definition hwmUR := excl_authUR (leibnizO Z).
Definition lentUR := excl_authUR (leibnizO (gset Addr)).
Definition loUR := excl_authUR (leibnizO (option (nat * gset Addr))).
Definition baseR := agreeR (leibnizO Z).

Class hwmG Σ := HwmG {
  hwm_inG :: inG Σ hwmUR;
  hwm_zone_mapG :: ghost_mapG Σ Addr unit;
  hwm_lent_inG :: inG Σ lentUR;
  hwm_pend_inG :: ghost_varG Σ (option Z);
  hwm_lo_inG :: inG Σ loUR;
  hwm_base_inG :: inG Σ baseR;
  mshwmb_name : gname;
  mshwm_name : gname;
  zone_name : gname;
  lent_name : gname;
  pend_name : gname;
  last_owner_name : gname;
  base_name : gname;
}.
#[export] Hint Mode hwmG - : typeclass_instances.

Class hwmGpreS Σ := {
  hwm_preG_inG :: inG Σ hwmUR;
  hwm_preG_zone :: ghost_mapG Σ Addr unit;
  hwm_preG_lent :: inG Σ lentUR;
  hwm_preG_pend :: ghost_varG Σ (option Z);
  hwm_preG_lo :: inG Σ loUR;
  hwm_preG_base :: inG Σ baseR;
}.
#[export] Hint Mode hwmGpreS - : typeclass_instances.
Definition hwmΣ : gFunctors :=
  #[GFunctor hwmUR; ghost_mapΣ Addr unit; GFunctor lentUR; ghost_varΣ (option Z);
    GFunctor loUR; GFunctor baseR].
#[global] Instance subG_hwmGpreS {Σ} : subG hwmΣ Σ → hwmGpreS Σ.
Proof. solve_inG. Qed.

Section hwm_resource.
  Context `{!hwmG Σ}.

  Definition mshwmb_auth (mshwmb_v : Z) : iProp Σ := own mshwmb_name (●E (mshwmb_v : leibnizO Z)).
  Definition mshwmb_frag (mshwmb_v : Z) : iProp Σ := own mshwmb_name (◯E (mshwmb_v : leibnizO Z)).
  Definition mshwm_auth (mshwm_v : Z) : iProp Σ := own mshwm_name (●E (mshwm_v : leibnizO Z)).
  Definition mshwm_frag (mshwm_v : Z) : iProp Σ := own mshwm_name (◯E (mshwm_v : leibnizO Z)).

  #[global] Instance mshwmb_auth_timeless mshwmb_v : Timeless (mshwmb_auth mshwmb_v).
  Proof. apply _. Qed.
  #[global] Instance mshwmb_frag_timeless mshwmb_v : Timeless (mshwmb_frag mshwmb_v).
  Proof. apply _. Qed.
  #[global] Instance mshwm_auth_timeless mshwm_v : Timeless (mshwm_auth mshwm_v).
  Proof. apply _. Qed.
  #[global] Instance mshwm_frag_timeless mshwm_v : Timeless (mshwm_frag mshwm_v).
  Proof. apply _. Qed.

  Lemma mshwmb_agree mshwmb_v mshwmb_v' : mshwmb_auth mshwmb_v -∗ mshwmb_frag mshwmb_v' -∗ ⌜mshwmb_v = mshwmb_v'⌝.
  Proof. iIntros "Ha Hf". iCombine "Ha Hf" gives %Hv. by apply excl_auth_agree_L in Hv. Qed.

  Lemma mshwmb_update mshwmb_v mshwmb_v' mshwmb_v'' :
    mshwmb_auth mshwmb_v -∗ mshwmb_frag mshwmb_v' ==∗ mshwmb_auth mshwmb_v'' ∗ mshwmb_frag mshwmb_v''.
  Proof.
    iIntros "Ha Hf". iMod (own_update_2 with "Ha Hf") as "[$ $]"; last done.
    apply excl_auth_update.
  Qed.

  Lemma mshwmb_frag_excl mshwmb_v mshwmb_v' : mshwmb_frag mshwmb_v -∗ mshwmb_frag mshwmb_v' -∗ False.
  Proof. iIntros "H1 H2". iCombine "H1 H2" gives %Hv. by apply excl_auth_frag_op_valid in Hv. Qed.

  Lemma mshwm_agree mshwm_v mshwm_v' : mshwm_auth mshwm_v -∗ mshwm_frag mshwm_v' -∗ ⌜mshwm_v = mshwm_v'⌝.
  Proof. iIntros "Ha Hf". iCombine "Ha Hf" gives %Hv. by apply excl_auth_agree_L in Hv. Qed.

  Lemma mshwm_update mshwm_v mshwm_v' mshwm_v'' :
    mshwm_auth mshwm_v -∗ mshwm_frag mshwm_v' ==∗ mshwm_auth mshwm_v'' ∗ mshwm_frag mshwm_v''.
  Proof.
    iIntros "Ha Hf". iMod (own_update_2 with "Ha Hf") as "[$ $]"; last done.
    apply excl_auth_update.
  Qed.

  Lemma mshwm_frag_excl mshwm_v mshwm_v' : mshwm_frag mshwm_v -∗ mshwm_frag mshwm_v' -∗ False.
  Proof. iIntros "H1 H2". iCombine "H1 H2" gives %Hv. by apply excl_auth_frag_op_valid in Hv. Qed.

  (** The exclusive token of the address [a] of the zone. *)
  Definition zone_token (a : Addr) : iProp Σ := a ↪[zone_name] ().

  (** The authoritative part of the zone [zn]. *)
  Definition zone_auth (zn : gset Addr) : iProp Σ :=
    ghost_map_auth zone_name 1 (gset_to_gmap () zn).

  #[global] Instance zone_token_timeless a : Timeless (zone_token a).
  Proof. apply _. Qed.
  #[global] Instance zone_auth_timeless Z : Timeless (zone_auth Z).
  Proof. apply _. Qed.

  Lemma zone_token_excl a : zone_token a -∗ zone_token a -∗ False.
  Proof. iIntros "H1 H2". by iDestruct (ghost_map_elem_ne with "H1 H2") as %?. Qed.

  Lemma zone_auth_elem zn a : zone_auth zn -∗ zone_token a -∗ ⌜a ∈ zn⌝.
  Proof.
    iIntros "Hauth Htok".
    iDestruct (ghost_map_lookup with "Hauth Htok") as %Hlookup.
    iPureIntro. by apply lookup_gset_to_gmap_Some in Hlookup as [? _].
  Qed.

  Lemma zone_auth_insert zn a : a ∉ zn → zone_auth zn ==∗ zone_auth ({[a]} ∪ zn) ∗ zone_token a.
  Proof.
    iIntros (Hazn) "Hauth". rewrite /zone_auth /zone_token gset_to_gmap_union_singleton.
    iApply (ghost_map_insert with "Hauth").
    by rewrite lookup_gset_to_gmap_None.
  Qed.

  Lemma zone_auth_delete zn a : zone_auth zn -∗ zone_token a ==∗ zone_auth (zn ∖ {[a]}).
  Proof.
    iIntros "Hauth Htok". rewrite /zone_auth /zone_token gset_to_gmap_difference_singleton.
    iApply (ghost_map_delete with "Hauth Htok").
  Qed.

  (** The halves that the thread holds for another thread: the authority
      [lent_auth L] in the state interpretation, the fragment with the
      thread's code (in the window clause for a user thread). *)
  Definition lent_auth (L : gset Addr) : iProp Σ := own lent_name (●E (L : leibnizO (gset Addr))).
  Definition lent_frag (L : gset Addr) : iProp Σ := own lent_name (◯E (L : leibnizO (gset Addr))).

  #[global] Instance lent_auth_timeless L : Timeless (lent_auth L).
  Proof. apply _. Qed.
  #[global] Instance lent_frag_timeless L : Timeless (lent_frag L).
  Proof. apply _. Qed.

  Lemma lent_agree L L' : lent_auth L -∗ lent_frag L' -∗ ⌜L = L'⌝.
  Proof. iIntros "Ha Hf". iCombine "Ha Hf" gives %Hv. by apply excl_auth_agree_L in Hv. Qed.

  Lemma lent_update L L' L'' : lent_auth L -∗ lent_frag L' ==∗ lent_auth L'' ∗ lent_frag L''.
  Proof.
    iIntros "Ha Hf". iMod (own_update_2 with "Ha Hf") as "[$ $]"; last done.
    apply excl_auth_update.
  Qed.

  Lemma lent_frag_excl L L' : lent_frag L -∗ lent_frag L' -∗ False.
  Proof. iIntros "H1 H2". iCombine "H1 H2" gives %Hv. by apply excl_auth_frag_op_valid in Hv. Qed.

  (** The HWM restore window: [None] closed, [Some hbT] open with the cover base
      [hbT]. [pend_si] and [pend_half] are halves (the state
      interpretation's, and the other one of a user thread's window clause);
      [pend_cl] and [pend_frag] are quarters (the context-switch thread's
      window clause, and its code). *)
  Definition pend_full (o : option Z) : iProp Σ := ghost_var pend_name 1 o.
  Definition pend_si (o : option Z) : iProp Σ := ghost_var pend_name (1/2) o.
  Definition pend_half (o : option Z) : iProp Σ := ghost_var pend_name (1/2) o.
  Definition pend_cl (o : option Z) : iProp Σ := ghost_var pend_name (1/4) o.
  Definition pend_frag (o : option Z) : iProp Σ := ghost_var pend_name (1/4) o.

  #[global] Instance pend_full_timeless o : Timeless (pend_full o).
  Proof. apply _. Qed.
  #[global] Instance pend_si_timeless o : Timeless (pend_si o).
  Proof. apply _. Qed.
  #[global] Instance pend_half_timeless o : Timeless (pend_half o).
  Proof. apply _. Qed.
  #[global] Instance pend_cl_timeless o : Timeless (pend_cl o).
  Proof. apply _. Qed.
  #[global] Instance pend_frag_timeless o : Timeless (pend_frag o).
  Proof. apply _. Qed.

  Lemma pend_half_split o : pend_half o ⊣⊢ pend_cl o ∗ pend_frag o.
  Proof.
    rewrite /pend_half /pend_cl /pend_frag -Qp.quarter_quarter.
    iSplit; [iIntros "[$ $]" | iIntros "[H1 H2]"; by iCombine "H1 H2" as "$"].
  Qed.

  Lemma pend_full_split o : pend_full o ⊣⊢ pend_si o ∗ pend_cl o ∗ pend_frag o.
  Proof.
    rewrite -pend_half_split /pend_full /pend_si /pend_half -{1}Qp.half_half.
    iSplit; first iIntros "[$ $]".
    iIntros "[H1 H2]". iCombine "H1 H2" as "H". rewrite Qp.half_half. iExact "H".
  Qed.

  Lemma pend_si_agree o o' : pend_si o -∗ pend_cl o' -∗ ⌜o = o'⌝.
  Proof. iIntros "H1 H2". by iDestruct (ghost_var_agree with "H1 H2") as %->. Qed.

  Lemma pend_si_frag_agree o o' : pend_si o -∗ pend_frag o' -∗ ⌜o = o'⌝.
  Proof. iIntros "H1 H2". by iDestruct (ghost_var_agree with "H1 H2") as %->. Qed.

  Lemma pend_cl_frag_agree o o' : pend_cl o -∗ pend_frag o' -∗ ⌜o = o'⌝.
  Proof. iIntros "H1 H2". by iDestruct (ghost_var_agree with "H1 H2") as %->. Qed.

  Lemma pend_si_half_agree o o' : pend_si o -∗ pend_half o' -∗ ⌜o = o'⌝.
  Proof. iIntros "H1 H2". by iDestruct (ghost_var_agree with "H1 H2") as %->. Qed.

  (** The three parts together change the window. *)
  Lemma pend_update o o' :
    pend_si o -∗ pend_cl o -∗ pend_frag o ==∗ pend_si o' ∗ pend_cl o' ∗ pend_frag o'.
  Proof.
    iIntros "Hs Hc Hf".
    iAssert (pend_full o) with "[Hs Hc Hf]" as "H".
    { rewrite pend_full_split. iFrame. }
    rewrite /pend_full. iMod (ghost_var_update o' with "H") as "H".
    iModIntro. by iDestruct (pend_full_split o' with "H") as "($ & $ & $)".
  Qed.

  (** The last owner: authority in [Pool], fragment with the context-switch
      thread's code. *)
  Definition last_owner_auth (o : option (nat * gset Addr)) : iProp Σ :=
    own last_owner_name (●E (o : leibnizO (option (nat * gset Addr)))).
  Definition last_owner_frag (o : option (nat * gset Addr)) : iProp Σ :=
    own last_owner_name (◯E (o : leibnizO (option (nat * gset Addr)))).

  #[global] Instance last_owner_auth_timeless o : Timeless (last_owner_auth o).
  Proof. apply _. Qed.
  #[global] Instance last_owner_frag_timeless o : Timeless (last_owner_frag o).
  Proof. apply _. Qed.

  Lemma last_owner_agree o o' : last_owner_auth o -∗ last_owner_frag o' -∗ ⌜o = o'⌝.
  Proof. iIntros "Ha Hf". iCombine "Ha Hf" gives %Hv. by apply excl_auth_agree_L in Hv. Qed.

  Lemma last_owner_update o o' o'' :
    last_owner_auth o -∗ last_owner_frag o' ==∗ last_owner_auth o'' ∗ last_owner_frag o''.
  Proof.
    iIntros "Ha Hf". iMod (own_update_2 with "Ha Hf") as "[$ $]"; last done.
    apply excl_auth_update.
  Qed.

  (** The stack base of the thread. *)
  Definition hwm_base (mshwmb_v : Z) : iProp Σ := own base_name (to_agree (mshwmb_v : leibnizO Z)).

  #[global] Instance hwm_base_persistent mshwmb_v : Persistent (hwm_base mshwmb_v).
  Proof. apply _. Qed.
  #[global] Instance hwm_base_timeless mshwmb_v : Timeless (hwm_base mshwmb_v).
  Proof. apply _. Qed.

  Lemma hwm_base_agree mshwmb_v mshwmb_v' : hwm_base mshwmb_v -∗ hwm_base mshwmb_v' -∗ ⌜mshwmb_v = mshwmb_v'⌝.
  Proof. iIntros "H1 H2". iCombine "H1 H2" gives %Hv. by apply to_agree_op_valid_L in Hv. Qed.

  (** The window and lending ghosts of a thread at rest: nothing lent, the
      window closed. *)
  Definition hwm_rest : iProp Σ := lent_auth ∅ ∗ lent_frag ∅ ∗ pend_full None.

  #[global] Instance hwm_rest_timeless : Timeless hwm_rest.
  Proof. apply _. Qed.
End hwm_resource.

(** The high-water-mark ghost state of a thread whose zone starts as [zone]:
    MSHWMB at [mshwmb_v], MSHWM at [mshwm_v], the token of every address of [zone], the
    window and lending ghosts at rest, no last owner, and the stack base
    [mshwmb_v]. *)
Lemma hwm_init_zone `{!hwmGpreS Σ} (mshwmb_v mshwm_v : Z) (zone : gset Addr) :
  ⊢ |==> ∃ g : hwmG Σ,
    mshwmb_auth mshwmb_v ∗ mshwmb_frag mshwmb_v ∗ mshwm_auth mshwm_v ∗ mshwm_frag mshwm_v ∗
    zone_auth zone ∗ ([∗ set] a ∈ zone, zone_token a) ∗
    hwm_rest ∗ last_owner_auth None ∗ last_owner_frag None ∗ hwm_base mshwmb_v.
Proof.
  iMod (own_alloc (●E (mshwmb_v : leibnizO Z) ⋅ ◯E (mshwmb_v : leibnizO Z))) as (γb) "[Hba Hbf]".
  { apply excl_auth_valid. }
  iMod (own_alloc (●E (mshwm_v : leibnizO Z) ⋅ ◯E (mshwm_v : leibnizO Z))) as (γh) "[Hha Hhf]".
  { apply excl_auth_valid. }
  iMod (ghost_map_alloc (gset_to_gmap () zone)) as (γz) "[Hzauth Hztoks]".
  iMod (own_alloc (●E (∅ : leibnizO (gset Addr)) ⋅ ◯E (∅ : leibnizO (gset Addr))))
    as (γl) "[Hla Hlf]".
  { apply excl_auth_valid. }
  iMod (ghost_var_alloc (None : option Z)) as (γp) "Hp".
  iMod (own_alloc (●E (None : leibnizO (option (nat * gset Addr))) ⋅
                   ◯E (None : leibnizO (option (nat * gset Addr)))))
    as (γo) "[Hoa Hof]".
  { apply excl_auth_valid. }
  iMod (own_alloc (to_agree (mshwmb_v : leibnizO Z))) as (γbase) "Hbase"; first done.
  iModIntro. iExists (HwmG _ _ _ _ _ _ _ γb γh γz γl γp γo γbase).
  rewrite /zone_auth /zone_token /hwm_rest /lent_auth /lent_frag /pend_full.
  rewrite /last_owner_auth /last_owner_frag /hwm_base big_sepM_gset_to_gmap. iFrame.
Qed.

(** With an empty zone. *)
Lemma hwm_init `{!hwmGpreS Σ} (mshwmb_v mshwm_v : Z) :
  ⊢ |==> ∃ g : hwmG Σ,
    mshwmb_auth mshwmb_v ∗ mshwmb_frag mshwmb_v ∗ mshwm_auth mshwm_v ∗ mshwm_frag mshwm_v ∗ zone_auth ∅ ∗
    hwm_rest ∗ last_owner_auth None ∗ last_owner_frag None ∗ hwm_base mshwmb_v.
Proof.
  iMod (hwm_init_zone mshwmb_v mshwm_v ∅) as (g) "(? & ? & ? & ? & ? & _ & ?)".
  iModIntro. iExists g. iFrame.
Qed.

(** * The ghost state of the postures

    The names shared by the threads: the pool [crit] of the critical
    sections, the unwedged token and the one-shot ghost of MTCC. Per
    thread: the token [mtdc_lent] of its mtdc, and its home value
    [mtdc_home], the value of its mtdc when the token is not lent. *)
Definition oneshotR := csumR (exclR unitO) (agreeR unitO).

Class postureG Σ := PostureG {
  posture_exclG :: inG Σ (exclR unitO);
  posture_oneshotG :: inG Σ oneshotR;
  crit : na_inv_pool_name;
  γunwedged : gname;
  γmtcc : gname;
}.
#[export] Hint Mode postureG - : typeclass_instances.

Class mtdcLentG Σ := MtdcLentG {
  mtdc_lent_inG :: inG Σ (exclR unitO);
  mtdc_lent_name : gname;
  mtdc_home : mtdc_val;
}.
#[export] Hint Mode mtdcLentG - : typeclass_instances.

(** The unwedged token, and the one-shot ghost of MTCC: pending while MTCC
    holds the trap vector, wedged (persistently) once it does not. *)
Section posture_resources.
  Context `{!postureG Σ}.

  Definition unwedged : iProp Σ := own γunwedged (Excl () : exclR unitO).
  Definition mtcc_pending : iProp Σ := own γmtcc (Cinl (Excl ()) : oneshotR).
  Definition mtcc_wedged : iProp Σ := own γmtcc (Cinr (to_agree ()) : oneshotR).

  #[global] Instance unwedged_timeless : Timeless unwedged.
  Proof. apply _. Qed.
  #[global] Instance mtcc_pending_timeless : Timeless mtcc_pending.
  Proof. apply _. Qed.
  #[global] Instance mtcc_wedged_timeless : Timeless mtcc_wedged.
  Proof. apply _. Qed.
  #[global] Instance mtcc_wedged_persistent : Persistent mtcc_wedged.
  Proof. apply _. Qed.

  Lemma unwedged_excl : unwedged -∗ unwedged -∗ False.
  Proof. iIntros "H1 H2". by iDestruct (own_valid_2 with "H1 H2") as %[]. Qed.

  Lemma mtcc_pending_wedged : mtcc_pending -∗ mtcc_wedged -∗ False.
  Proof. iIntros "H1 H2". by iDestruct (own_valid_2 with "H1 H2") as %[]. Qed.
End posture_resources.

(** The mtdc token of a thread, and the clause of its mtdc in the state
    interpretation: the ghost value is the home value, or the state
    interpretation holds the token (the token is lent). *)
Section mtdc_lent_resources.
  Context `{!mtdcLentG Σ}.

  Definition mtdc_lent : iProp Σ := own mtdc_lent_name (Excl () : exclR unitO).
  Definition mtdc_clause (m : mtdc_val) : iProp Σ := ⌜m = mtdc_home⌝ ∨ mtdc_lent.

  #[global] Instance mtdc_lent_timeless : Timeless mtdc_lent.
  Proof. apply _. Qed.
  #[global] Instance mtdc_clause_timeless m : Timeless (mtdc_clause m).
  Proof. apply _. Qed.

  Lemma mtdc_lent_excl : mtdc_lent -∗ mtdc_lent -∗ False.
  Proof. iIntros "H1 H2". by iDestruct (own_valid_2 with "H1 H2") as %[]. Qed.

  (** The holder of the token knows that the ghost value is the home
      value. *)
  Lemma mtdc_clause_lent m : mtdc_clause m -∗ mtdc_lent -∗ ⌜m = mtdc_home⌝.
  Proof.
    iIntros "[%Hm | Hl] Hl'"; first done.
    iDestruct (mtdc_lent_excl with "Hl Hl'") as %[].
  Qed.

  (** The transfers of the clause by an mtdc write: leaving the home value
      pays the token, writing another value keeps it lent, coming back to
      the home value returns it. *)
  Lemma mtdc_clause_open m' : mtdc_clause mtdc_home ∗ mtdc_lent ⊢ |==> mtdc_clause m' ∗ True.
  Proof. iIntros "[_ Hl] !>". iSplitL; [by iRight | done]. Qed.

  Lemma mtdc_clause_ex m m' : m ≠ mtdc_home → mtdc_clause m ∗ True ⊢ |==> mtdc_clause m' ∗ True.
  Proof. iIntros (Hm) "[ [%Hm' | Hl] _] !>"; first done. iSplitL; [by iRight | done]. Qed.

  Lemma mtdc_clause_close m :
    m ≠ mtdc_home → mtdc_clause m ∗ True ⊢ |==> mtdc_clause mtdc_home ∗ mtdc_lent.
  Proof. iIntros (Hm) "[ [%Hm' | Hl] _] !>"; first done. iSplitR "Hl"; [by iLeft | done]. Qed.

  Lemma mtdc_clause_keep m : mtdc_clause m ∗ True ⊢ |==> mtdc_clause m ∗ True.
  Proof. by iIntros "$ !>". Qed.
End mtdc_lent_resources.

Lemma posture_init `{!inG Σ (exclR unitO), !inG Σ oneshotR, !na_invariants.na_invG Σ} :
  ⊢ |==> ∃ pg : postureG Σ,
    na_own (@crit Σ pg) ⊤ ∗
    @own Σ _ (@posture_exclG Σ pg) (@γunwedged Σ pg) (Excl ()) ∗
    @own Σ _ (@posture_oneshotG Σ pg) (@γmtcc Σ pg) (Cinl (Excl ())).
Proof.
  iMod na_alloc as (p) "Hna".
  iMod (own_alloc (Excl ())) as (γu) "Hu"; first done.
  iMod (own_alloc (Cinl (Excl ()) : oneshotR)) as (γm) "Hm"; first done.
  iModIntro. iExists (PostureG _ _ _ p γu γm). iFrame.
Qed.

Lemma mtdc_lent_init `{!inG Σ (exclR unitO)} (m : mtdc_val) :
  ⊢ |==> ∃ g : mtdcLentG Σ,
    ⌜@mtdc_home Σ g = m⌝ ∗
    @own Σ _ (@mtdc_lent_inG Σ g) (@mtdc_lent_name Σ g) (Excl ()).
Proof.
  iMod (own_alloc (Excl ())) as (γ) "Hl"; first done.
  iModIntro. iExists (MtdcLentG _ _ γ m). by iFrame.
Qed.

(** The trap vector: the word that MTCC holds in every state, the
    capability of the exception entry of the switcher. It is tagged, so a
    fault never stops the machine. *)
Class trapVector := {
  mtcc_vec : Word;
  mtcc_vec_tagged : get_tag mtcc_vec = true;
}.
(* No [Hint Mode]: the class has no parameter, hence no input position. *)

(* CMRA for Cerise. The PC, registers, system registers and memory hold
   logical words. *)
Class ceriseG Σ :=
  CeriseG {
      cerise_invG : invGS Σ;
      cerise_nainvG :: cerise_na_invs Σ;
      mem_gen_memG :: gen_heapGS Addr LWord Σ; (* memory *)
      shadowtbl_gen_regG :: gen_heapGS Addr AllocStatus Σ; (* shadow table *)
      cerise_pcG :: pcG Σ; (* PC *)
      reg_gen_regG :: gen_heapGS RegName LWord Σ; (* register *)
      sreg_gen_regG :: gen_heapGS SRegName LWord Σ; (* system register *)
      cerise_registryG :: allocRegistryG Σ; (* allocation registry *)
      cerise_addr_allocG :: addrAllocG Σ; (* address claims *)
      cerise_trapVector :: trapVector; (* trap vector *)
      cerise_mtdcG :: mtdcG Σ; (* mtdc of the thread *)
      cerise_mieG :: mieG Σ; (* MIE of the thread *)
      cerise_mpieG :: mpieG Σ; (* MPIE *)
      cerise_postureG :: postureG Σ; (* the shared names of the postures *)
      cerise_mtdc_lentG :: mtdcLentG Σ; (* the mtdc token of the thread *)
      cerise_hwmG :: hwmG Σ (* MSHWMB, MSHWM, zone, window and lending of the thread *)
    }.
#[export] Hint Mode ceriseG - : typeclass_instances.

(** The invariants of an instance, without a link: a fancy update in a
    section with a [ceriseG] and no thread. Low priority: the invariants of
    a WP's instance are found first. *)
#[global] Instance cerise_invGS {Σ} {ceriseg : ceriseG Σ} : invGS Σ | 1000 := cerise_invG.

(** * Threads

    The user threads of the firmware image, by index, and the
    context-switch thread. [Thread] is a class, so that a section thread
    [{th : Thread}] is found by typeclass search: the per-thread instance
    [ceriseG_of] below then builds the section's [ceriseG] from it, and
    predicates defined in a thread section are used elsewhere without their
    thread. *)
Inductive Thread : Type := UserThread (t : nat) | CtxSwitch.
#[global] Instance Thread_eq_dec : EqDecision Thread.
Proof. solve_decision. Qed.
Existing Class Thread.
(* No [Hint Mode]: the class has no parameter, hence no input position. *)
#[global] Instance Thread_countable : Countable Thread.
Proof.
  refine (inj_countable'
    (λ th, match th with UserThread n => Some n | CtxSwitch => None end)
    (λ o, match o with Some n => UserThread n | None => CtxSwitch end) _).
  by intros [n|].
Qed.

(** Threads in notations: [u n] is the user thread [n], [s] the
    context-switch thread; a variable or a parenthesised term is a thread
    too. [u] and [s] are not reserved outside the entry. The escape is a
    term at level 0, not [x global] or [x ident]: those make the entry fail
    when it is imported through two paths. *)
Declare Custom Entry thread.
Notation "'u' n" := (UserThread n) (in custom thread at level 0, n constr at level 0).
Notation "'s'" := CtxSwitch (in custom thread at level 0).
Notation "x" := x (in custom thread at level 0, x constr at level 0).

(** A map from threads with finitely many distinct values: [x0] for the user
    thread 0, the [k]-th element of [xs] for the user thread [S k], [xc] for
    the context-switch thread, [d] for the other user threads. *)
Definition thread_map {A} (x0 : A) (xs : list A) (xc d : A) (th : Thread) : A :=
  match th with
  | UserThread 0 => x0
  | UserThread (S k) => nth k xs d
  | CtxSwitch => xc
  end.

(** * The switches between threads

    The values a parked thread resumes with: its general registers, its PC
    and its MIE (its mtdc is its home value), and its MSHWMB, MSHWM and
    zone. *)
Record resume_vals := ResumeVals {
  rv_regs : LReg;
  rv_pc : LWord;
  rv_mie : InterruptStatus;
  rv_hwmb : Z;
  rv_hwm : Z;
  rv_zone : gset Addr;
}.

(** How the running thread is parked: by an interrupt, by a yield (its MIE
    before the [ecall] and its MEPCC), or at its exit. *)
Inductive park_kind :=
| ParkIrq
| ParkYield (b : InterruptStatus) (p : LWord)
| ParkExit.

(** The state of the one thread that is not suspended. In [cur], [None]
    means that every user thread is suspended. *)
Inductive TState :=
| Running
| Saving (k : park_kind) (v : resume_vals)
| Resuming (v : resume_vals).

Definition curUR := excl_authUR (leibnizO (option (Thread * TState))).

(** The resources shared by the threads, and the per-thread ones as maps
    from threads: the PC, the general registers, the ghost state of mtdc and
    MIE, the mtdc token, the high-water-mark ghosts ([cb_hwm_of]), and the
    non-atomic pool [tpool th]; and the ghost
    state of the switches: the name of [cur], and the names of the saved
    propositions of the switcher's parts of [HO] ([γ_exit th], [γ_scheduler]),
    and the ghost names of the running thread and of the resume window of
    the context-switch thread. The other system registers, MPIE and the
    names of the postures are shared. The shared fields are [::] fields,
    the per-thread maps are not, so typeclass search finds a per-thread
    heap only through [ceriseG_of].
    The shared fields other than [na_invG] have a low priority: with a
    thread in scope, the invariants, the memory, the shadow table, the
    system registers, the registry, the address claims and [mtcc_vec]
    elaborate through [ceriseG_of] as in the rule library; without one,
    through the base. Both are the same resources. *)
Class ceriseBaseG Σ := CeriseBaseG {
  cb_invG :: invGS Σ | 100;
  cb_na_invG :: na_invariants.na_invG Σ;
  cb_mem :: gen_heapGS Addr LWord Σ | 100;
  cb_shadow :: gen_heapGS Addr AllocStatus Σ | 100;
  cb_sreg :: gen_heapGS SRegName LWord Σ | 100;
  cb_registry :: allocRegistryG Σ | 100;
  cb_addr_alloc :: addrAllocG Σ | 100;
  cb_trapVector :: trapVector | 100;
  cb_mpie :: mpieG Σ | 100;
  cb_posture :: postureG Σ | 100;
  cb_pc_of : Thread → pcG Σ;
  cb_regs_of : Thread → gen_heapGS RegName LWord Σ;
  cb_mtdc_of : Thread → mtdcG Σ;
  cb_mie_of : Thread → mieG Σ;
  cb_mtdc_lent_of : Thread → mtdcLentG Σ;
  cb_hwm_of : Thread → hwmG Σ;
  tpool : Thread → na_inv_pool_name;
  cb_cur_inG :: inG Σ curUR | 100;
  cb_cur_name : gname;
  cb_saved_prop :: savedPropG Σ | 100;
  γ_exit : Thread → gname;
  γ_scheduler : gname;
  cb_running_inG :: ghost_varG Σ Thread | 100;
  γ_running : gname;
  cb_resume_window_inG :: ghost_varG Σ bool | 100;
  γ_resume_window : gname;
}.
#[export] Hint Mode ceriseBaseG - : typeclass_instances.
#[global] Arguments tpool {Σ _} th : rename.
#[global] Arguments γ_exit {Σ _} th : rename.
#[global] Arguments γ_scheduler {Σ _} : rename.
#[global] Arguments γ_running {Σ _} : rename.
#[global] Arguments γ_resume_window {Σ _} : rename.

(** The instance of thread [th]. Every field is a projection of [base]:
    a record built with [{| f := f |}] would have its fields filled in by
    typeclass search from an ambient instance. The base is an implicit
    argument, so that the notations below leave it to typeclass search
    (an explicit hole is not resolved in a [Program Definition]). *)
Definition ceriseG_of {Σ} {base : ceriseBaseG Σ} (th : Thread) : ceriseG Σ :=
  @CeriseG Σ (@cb_invG Σ base)
    (@Build_cerise_na_invs Σ (@cb_na_invG Σ base) (@tpool Σ base th))
    (@cb_mem Σ base) (@cb_shadow Σ base) (@cb_pc_of Σ base th) (@cb_regs_of Σ base th)
    (@cb_sreg Σ base) (@cb_registry Σ base) (@cb_addr_alloc Σ base) (@cb_trapVector Σ base)
    (@cb_mtdc_of Σ base th) (@cb_mie_of Σ base th) (@cb_mpie Σ base)
    (@cb_posture Σ base) (@cb_mtdc_lent_of Σ base th) (@cb_hwm_of Σ base th).
#[global] Existing Instance ceriseG_of.

(* Goals keep the thread: [simpl] does not unfold the instance of a thread
   nor reduce its fields. The per-thread fields are what the thread
   notations print; a shared field reduced to the base's would no longer
   unify with a lemma generic in [ceriseG]. *)
#[global] Arguments ceriseG_of : simpl never.
#[global] Arguments cerise_invG : simpl never.
#[global] Arguments cerise_nainvG : simpl never.
#[global] Arguments mem_gen_memG : simpl never.
#[global] Arguments shadowtbl_gen_regG : simpl never.
#[global] Arguments cerise_pcG : simpl never.
#[global] Arguments reg_gen_regG : simpl never.
#[global] Arguments sreg_gen_regG : simpl never.
#[global] Arguments cerise_registryG : simpl never.
#[global] Arguments cerise_addr_allocG : simpl never.
#[global] Arguments cerise_trapVector : simpl never.
#[global] Arguments cerise_mtdcG : simpl never.
#[global] Arguments cerise_mieG : simpl never.
#[global] Arguments cerise_mpieG : simpl never.
#[global] Arguments cerise_postureG : simpl never.
#[global] Arguments cerise_mtdc_lentG : simpl never.
#[global] Arguments cerise_hwmG : simpl never.

Section thread_indep.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ}.

  (** The memory of the instance of a thread is that of the base, so a
      points-to at any fraction is the same at any two threads. *)
  Lemma pointsto_thread_indep (t t' : Thread) (a : Addr) (dq : dfrac) (w : LWord) :
    pointsto (hG := @mem_gen_memG Σ (ceriseG_of t)) (L := Addr) (V := LWord) a dq w ⊣⊢
    pointsto (hG := @mem_gen_memG Σ (ceriseG_of t')) (L := Addr) (V := LWord) a dq w.
  Proof. rewrite /ceriseG_of. reflexivity. Qed.

  Lemma pointsto_pers_thread_indep (t t' : Thread) (a : Addr) (w : LWord) :
    pointsto (hG := @mem_gen_memG Σ (ceriseG_of t)) (L := Addr) (V := LWord) a DfracDiscarded w ⊣⊢
    pointsto (hG := @mem_gen_memG Σ (ceriseG_of t')) (L := Addr) (V := LWord) a DfracDiscarded w.
  Proof. apply pointsto_thread_indep. Qed.

End thread_indep.

(* Points to predicates for the system registers of the shared heap: the
   system-wide control and status registers *)
Notation "sr ↦ₓ dq w" := (pointsto (L:=SRegName) (V:=LWord) sr dq w)
  (at level 20, dq custom dfrac at level 1, format "sr  ↦ₓ dq  w") : bi_scope.
Notation "sr ↦ₓ dq -" := (∃ w, pointsto (L:=SRegName) (V:=LWord) sr dq w)%I
  (at level 20, dq custom dfrac at level 1, format "sr  ↦ₓ dq  -") : bi_scope.

(* Points to predicate for the PC *)
Notation "'PC' ↦ₚ w" := (PC_frag w) (at level 20, format "'PC'  ↦ₚ  w") : bi_scope.

(* Points to predicates for registers *)
Notation "r ↦ᵣ dq w" := (pointsto (L:=RegName) (V:=LWord) r dq w)
  (at level 20, dq custom dfrac at level 1, format "r  ↦ᵣ dq  w") : bi_scope.
Notation "r ↦ᵣ dq -" := (∃ w, pointsto (L:=RegName) (V:=LWord) r dq w)%I
  (at level 20, dq custom dfrac at level 1, format "r  ↦ᵣ dq  -") : bi_scope.

(* Points to predicates for the PC and registers of thread [th] *)
Notation "'PC' ↦ₚ[ th ] w" := (@PC_frag _ (@cerise_pcG _ (ceriseG_of th)) w)
  (at level 20, th custom thread, format "'PC'  ↦ₚ[ th ]  w") : bi_scope.
Notation "r ↦ᵣ[ th ] dq w" :=
  (@pointsto RegName _ _ LWord _ (@reg_gen_regG _ (ceriseG_of th)) r dq w)
  (at level 20, th custom thread, dq custom dfrac at level 1,
   format "r  ↦ᵣ[ th ] dq  w") : bi_scope.
Notation "r ↦ᵣ[ th ] dq -" :=
  (∃ w, @pointsto RegName _ _ LWord _ (@reg_gen_regG _ (ceriseG_of th)) r dq w)%I
  (at level 20, th custom thread, dq custom dfrac at level 1,
   format "r  ↦ᵣ[ th ] dq  -") : bi_scope.

(** The registers of the map [rmap], owned by thread [th]; [regs₀[th]]: and
    all zero. No unannotated form. *)
Notation "'regs[' th ] rmap" :=
  ([∗ map] r↦w ∈ rmap, r ↦ᵣ[th] w)%I
  (at level 20, th custom thread, rmap at level 10, format "'regs[' th ]  rmap") : bi_scope.
Notation "'regs₀[' th ] rmap" :=
  ([∗ map] r↦w ∈ rmap, r ↦ᵣ[th] w ∗ ⌜w = lword_of_word (WInt 0%Z)⌝)%I
  (at level 20, th custom thread, rmap at level 10, format "'regs₀[' th ]  rmap") : bi_scope.

(** The mtdc fragment of a thread: [mtdc ↦ₜ m] in proofs and in
    instance-generic files, [mtdc ↦ₜ[th] m] for thread [th]. [mtdc] is a
    keyword at level 0 (a notation for [MTDC], [registers.v]); the fragment
    notations are at level 0 too, so that the two prefixes are compatible. *)
Notation "'mtdc' ↦ₜ m" := (mtdc_frag m)
  (at level 0, m at level 10, format "'mtdc'  ↦ₜ  m") : bi_scope.
Notation "'mtdc' ↦ₜ[ th ] m" := (@mtdc_frag _ (@cerise_mtdcG _ (ceriseG_of th)) m)
  (at level 0, th custom thread, m at level 10, format "'mtdc'  ↦ₜ[ th ]  m") : bi_scope.

(** The MIE fragment of a thread, released to its code: [MIE ↦ₜ b], and
    [MIE ↦ₜ[th] b] for thread [th]. *)
Notation "'MIE' ↦ₜ b" := (MIE_frag b)
  (at level 0, b at level 10, format "'MIE'  ↦ₜ  b") : bi_scope.
Notation "'MIE' ↦ₜ[ th ] b" := (@MIE_frag _ (@cerise_mieG _ (ceriseG_of th)) b)
  (at level 0, th custom thread, b at level 10, format "'MIE'  ↦ₜ[ th ]  b") : bi_scope.

(** The MSHWMB and MSHWM fragments of a thread: [mshwm ↦ₜ mshwm_v] in proofs and
    in instance-generic files, [mshwm ↦ₜ[th] mshwm_v] for thread [th]. [mshwm] and
    [mshwmb] are keywords at level 0, as [mtdc]. *)
Notation "'mshwmb' ↦ₜ mshwmb_v" := (mshwmb_frag mshwmb_v)
  (at level 0, mshwmb_v at level 10, format "'mshwmb'  ↦ₜ  mshwmb_v") : bi_scope.
Notation "'mshwmb' ↦ₜ[ th ] mshwmb_v" := (@mshwmb_frag _ (@cerise_hwmG _ (ceriseG_of th)) mshwmb_v)
  (at level 0, th custom thread, mshwmb_v at level 10, format "'mshwmb'  ↦ₜ[ th ]  mshwmb_v") : bi_scope.
Notation "'mshwm' ↦ₜ mshwm_v" := (mshwm_frag mshwm_v)
  (at level 0, mshwm_v at level 10, format "'mshwm'  ↦ₜ  mshwm_v") : bi_scope.
Notation "'mshwm' ↦ₜ[ th ] mshwm_v" := (@mshwm_frag _ (@cerise_hwmG _ (ceriseG_of th)) mshwm_v)
  (at level 0, th custom thread, mshwm_v at level 10, format "'mshwm'  ↦ₜ[ th ]  mshwm_v") : bi_scope.

(** The code's quarter of the HWM restore window and the fragment of the lent
    set of thread [th]: [pend_frag o] and [lent_frag L] in proofs and in
    instance-generic files. *)
Notation "'pend_frag[' th ] o" := (@pend_frag _ (@cerise_hwmG _ (ceriseG_of th)) o)
  (at level 20, th custom thread, o at level 9, format "'pend_frag[' th ]  o") : bi_scope.
Notation "'lent_frag[' th ] L" := (@lent_frag _ (@cerise_hwmG _ (ceriseG_of th)) L)
  (at level 20, th custom thread, L at level 9, format "'lent_frag[' th ]  L") : bi_scope.
(** The stack base of thread [th]. *)
Notation "'hwm_base[' th ] mshwmb_v" := (@hwm_base _ (@cerise_hwmG _ (ceriseG_of th)) mshwmb_v)
  (at level 20, th custom thread, mshwmb_v at level 9, format "'hwm_base[' th ]  mshwmb_v") : bi_scope.
(** The token of the address [a] of the zone of thread [th]. *)
Notation "'zone_token[' th ] a" := (@zone_token _ (@cerise_hwmG _ (ceriseG_of th)) a)
  (at level 20, th custom thread, a at level 9, format "'zone_token[' th ]  a") : bi_scope.

(** The halves that the context-switch thread lends while [o] is its last
    owner. *)
Definition last_owner_zone (o : option (nat * gset Addr)) : gset Addr := from_option snd ∅ o.

(** The last owner, at the context-switch thread's high-water-mark ghosts:
    the authority in [Pool], the fragment with the context-switch thread's
    code. *)
Section last_owner.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ}.

  Definition ctx_last_owner_auth (o : option (nat * gset Addr)) : iProp Σ :=
    @last_owner_auth Σ (@cb_hwm_of Σ ceriseb CtxSwitch) o.
  Definition ctx_last_owner_frag (o : option (nat * gset Addr)) : iProp Σ :=
    @last_owner_frag Σ (@cb_hwm_of Σ ceriseb CtxSwitch) o.

  #[global] Instance ctx_last_owner_auth_timeless o : Timeless (ctx_last_owner_auth o).
  Proof. rewrite /ctx_last_owner_auth. apply _. Qed.
  #[global] Instance ctx_last_owner_frag_timeless o : Timeless (ctx_last_owner_frag o).
  Proof. rewrite /ctx_last_owner_frag. apply _. Qed.

  Lemma ctx_last_owner_agree o o' : ctx_last_owner_auth o -∗ ctx_last_owner_frag o' -∗ ⌜o = o'⌝.
  Proof. apply last_owner_agree. Qed.

  Lemma ctx_last_owner_update o o' o'' : ctx_last_owner_auth o -∗ ctx_last_owner_frag o' ==∗ ctx_last_owner_auth o'' ∗ ctx_last_owner_frag o''.
  Proof. apply last_owner_update. Qed.
End last_owner.

(* Points to predicates for memory *)
Notation "a ↦ₐ dq w" := (pointsto (L:=Addr) (V:=LWord) a dq w)
  (at level 20, dq custom dfrac at level 1, format "a  ↦ₐ dq  w") : bi_scope.
Notation "a ↦ₐ dq -" := (∃ w, pointsto (L:=Addr) (V:=LWord) a dq w)%I
  (at level 20, dq custom dfrac at level 1, format "a  ↦ₐ dq  -") : bi_scope.

(* Points to predicates for shadow table *)
Notation "a ↦ₛ dq s" := (pointsto (L:=Addr) (V:=AllocStatus) a dq s)
  (at level 20, dq custom dfrac at level 1, format "a  ↦ₛ dq  s") : bi_scope.
Notation "a ↦ₛ dq -" := (∃ s, pointsto (L:=Addr) (V:=AllocStatus) a dq s)%I
  (at level 20, dq custom dfrac at level 1, format "a  ↦ₛ dq  -") : bi_scope.

(** * The zone of a thread *)
Section zone.
  Context `{!gen_heapGS Addr LWord Σ, !hwmG Σ}.

  (** Half of each cell of a set, each an integer: what the state
      interpretation holds of its zone and of the lent halves. *)
  Definition zone_halves (zn : gset Addr) : iProp Σ :=
    [∗ set] a ∈ zn, ∃ z : Z, a ↦ₐ{DfracOwn (1/2)} lword_of_word (WInt z).

  #[global] Instance zone_halves_timeless zn : Timeless (zone_halves zn).
  Proof. apply _. Qed.

  (** A cell of the zone at the integer [z]: its token, and half of its
      points-to, which holds [z]. The state interpretation holds the other
      half. *)
  Definition zone_cell_v_def (a : Addr) (z : Z) : iProp Σ :=
    zone_token a ∗ a ↦ₐ{DfracOwn (1/2)} lword_of_word (WInt z).
  #[local] Definition zone_cell_v_aux : seal (@zone_cell_v_def). Proof. by eexists. Qed.
  Definition zone_cell_v := zone_cell_v_aux.(unseal).
  #[local] Definition zone_cell_v_unseal : @zone_cell_v = @zone_cell_v_def :=
    zone_cell_v_aux.(seal_eq).

  Lemma zone_cell_v_unfold a z :
    zone_cell_v a z ⊣⊢ zone_token a ∗ a ↦ₐ{DfracOwn (1/2)} lword_of_word (WInt z).
  Proof. by rewrite zone_cell_v_unseal. Qed.

  #[global] Instance zone_cell_v_timeless a z : Timeless (zone_cell_v a z).
  Proof. rewrite zone_cell_v_unseal. apply _. Qed.

  (** A cell of the zone, at some integer. *)
  Definition zone_cell (a : Addr) : iProp Σ := ∃ z, zone_cell_v a z.

  Lemma zone_cell_unfold a :
    zone_cell a ⊣⊢ ∃ z, zone_token a ∗ a ↦ₐ{DfracOwn (1/2)} lword_of_word (WInt z).
  Proof. rewrite /zone_cell. by setoid_rewrite zone_cell_v_unfold. Qed.

  #[global] Instance zone_cell_timeless a : Timeless (zone_cell a).
  Proof. apply _. Qed.

  (** The cells of a list, at some integers, are cells at a list of
      integers. *)
  Lemma zone_cells_exist (l : list Addr) :
    ([∗ list] a ∈ l, zone_cell a) ⊣⊢ ∃ zs, [∗ list] a; z ∈ l; zs, zone_cell_v a z.
  Proof.
    iSplit.
    - iIntros "Hl". iInduction l as [|a l] "IH".
      + iExists []. done.
      + iDestruct "Hl" as "[[%z Ha] Hl]". iDestruct ("IH" with "Hl") as (zs) "Hl".
        iExists (z :: zs). iFrame.
    - iIntros "[%zs Hl]". iInduction l as [|a l] "IH" forall (zs).
      + done.
      + iDestruct (big_sepL2_cons_inv_l with "Hl") as (z zs' ->) "[Ha Hl]".
        iSplitL "Ha"; first by iExists z. iApply ("IH" with "Hl").
  Qed.

  Lemma zone_cell_v_excl a z z' : zone_cell_v a z -∗ zone_cell_v a z' -∗ False.
  Proof.
    rewrite !zone_cell_v_unfold. iIntros "[H1 _] [H2 _]".
    iApply (zone_token_excl with "H1 H2").
  Qed.

  Lemma zone_cell_excl a : zone_cell a -∗ zone_cell a -∗ False.
  Proof.
    iIntros "[%z H1] [%z' H2]". iApply (zone_cell_v_excl with "H1 H2").
  Qed.

  (** A zone cell excludes a full points-to of its address. *)
  Lemma zone_cell_v_pointsto_false (a : Addr) z (w : LWord) :
    zone_cell_v a z -∗ a ↦ₐ w -∗ False.
  Proof.
    rewrite zone_cell_v_unfold. iIntros "[_ Hhalf] Ha".
    iDestruct (pointsto_valid_2 with "Ha Hhalf") as %[Hv _].
    rewrite dfrac_op_own dfrac_valid_own in Hv.
    by apply Qp.not_add_le_l in Hv.
  Qed.

  Lemma zone_cell_pointsto_false (a : Addr) (w : LWord) :
    zone_cell a -∗ a ↦ₐ w -∗ False.
  Proof.
    rewrite zone_cell_unfold. iIntros "[%z [_ Hhalf]] Ha".
    iDestruct (pointsto_valid_2 with "Ha Hhalf") as %[Hv _].
    rewrite dfrac_op_own dfrac_valid_own in Hv.
    by apply Qp.not_add_le_l in Hv.
  Qed.

  (** The initial zone [zone] of a memory [m] that holds integers on [zone]: with the
      tokens of [zone], the points-to of an address of [zone] becomes a cell of
      the zone, and the other half of its points-to. *)
  Lemma zone_cells_init (zone : gset Addr) (m : gmap Addr LWord) :
    (∀ a, a ∈ zone → ∃ z, m !! a = Some (lword_of_word (WInt z))) →
    ([∗ map] a ↦ w ∈ m, a ↦ₐ w) -∗
    ([∗ set] a ∈ zone, zone_token a) -∗
    ([∗ map] a ↦ w ∈ m, if decide (a ∈ zone) then zone_cell a else a ↦ₐ w) ∗
    zone_halves zone.
  Proof.
    iIntros (Hzone) "Hm Htoks". rewrite /zone_halves.
    assert (∀ Φ : Addr → iProp Σ,
              ([∗ set] a ∈ zone, Φ a) ⊣⊢
              [∗ map] a ↦ _ ∈ m, if decide (a ∈ zone) then Φ a else emp)
      as Hsplit.
    { intros Φ. rewrite big_sepM_dom -big_sepS_filter'.
      f_equiv. apply set_eq. intros a. rewrite elem_of_filter elem_of_dom.
      split; [|naive_solver]. intros Ha. split; first done.
      destruct (Hzone a Ha) as [z Hz]. eexists. exact Hz. }
    rewrite (Hsplit (λ a, ∃ z : Z, a ↦ₐ{DfracOwn (1/2)} lword_of_word (WInt z))%I) -big_sepM_sep.
    iEval (rewrite (Hsplit zone_token)) in "Htoks". iCombine "Hm Htoks" as "Hm".
    rewrite -big_sepM_sep.
    iApply (big_sepM_mono with "Hm"). iIntros (a w Hw) "[Ha Htok]".
    case_decide as Ha; last by iFrame.
    destruct (Hzone a Ha) as [z Hz]. rewrite Hz in Hw. simplify_eq.
    iDestruct "Ha" as "[Ha1 Ha2]". rewrite zone_cell_unfold. iFrame.
  Qed.

  (** A full points-to is not in the zone. *)
  Lemma zone_cells_not_elem (zone : gset Addr) a w :
    zone_halves zone -∗
    a ↦ₐ w -∗
    ⌜a ∉ zone⌝.
  Proof.
    iIntros "Hcells Ha". destruct (decide (a ∈ zone)) as [Ha|Ha]; last done.
    iDestruct (big_sepS_elem_of with "Hcells") as (z) "Ha'"; first exact Ha.
    iDestruct (pointsto_valid_2 with "Ha Ha'") as %[Hv _].
    iPureIntro. rewrite dfrac_op_own dfrac_valid_own in Hv.
    by apply Qp.not_add_le_l in Hv.
  Qed.

  (** Three halves of a cell are impossible: the halves of two sets and a
      zone cell, or the halves of a set and a full points-to. *)
  Lemma zone_halves_cell_disj (Z1 Z2 : gset Addr) a :
    zone_halves Z1 -∗ zone_halves Z2 -∗ zone_cell a -∗ ⌜¬ (a ∈ Z1 ∧ a ∈ Z2)⌝.
  Proof.
    iIntros "H1 H2 Hc" ([Ha1 Ha2]).
    iDestruct (big_sepS_elem_of with "H1") as (z1) "Ha1"; first exact Ha1.
    iDestruct (big_sepS_elem_of with "H2") as (z2) "Ha2"; first exact Ha2.
    iDestruct (zone_cell_unfold with "Hc") as (z3) "[Htok Ha3]".
    iDestruct (pointsto_valid_2 with "Ha1 Ha2") as %[_ Heq]. simplify_eq.
    iCombine "Ha1 Ha2" as "Ha".
    iEval (rewrite ?dfrac_op_own ?Qp.half_half) in "Ha".
    iApply (zone_cell_pointsto_false with "[Ha3 Htok] Ha").
    rewrite zone_cell_unfold. iFrame.
  Qed.
End zone.

(** A cell of the zone of thread [th]; plain [zone_cell a] in proofs and in
    instance-generic files. The memory and the zone are those of
    [ceriseG_of th]. *)
Notation "'zone_cell[' th ] a" :=
  (@zone_cell _ (@mem_gen_memG _ (ceriseG_of th)) (@cerise_hwmG _ (ceriseG_of th)) a)
  (at level 20, th custom thread, a at level 9, format "'zone_cell[' th ]  a") : bi_scope.

(** A cell of the zone of thread [th] at the integer [z]. *)
Notation "'zone_cell_v[' th ] a z" :=
  (@zone_cell_v _ (@mem_gen_memG _ (ceriseG_of th)) (@cerise_hwmG _ (ceriseG_of th)) a z)
  (at level 20, th custom thread, a at level 9, z at level 9,
   format "'zone_cell_v[' th ]  a  z") : bi_scope.

(** The halves of a set at the memory of thread [th]'s instance, which is
    the base's: the same at every thread ([zone_halves_thread_indep]). *)
Notation "'zone_halves[' th ] zn" :=
  (@zone_halves _ (@mem_gen_memG _ (ceriseG_of th)) zn)
  (at level 20, th custom thread, zn at level 9, format "'zone_halves[' th ]  zn") : bi_scope.

Lemma zone_halves_thread_indep {Σ} {ceriseb : ceriseBaseG Σ} (t t' : Thread) zn :
  zone_halves[t] zn ⊣⊢ zone_halves[t'] zn.
Proof. rewrite /ceriseG_of. reflexivity. Qed.

(** The cover of [mshwmb_v, mshwm_v) by the set [zn]. *)
Definition zone_covers (mshwmb_v mshwm_v : Z) (zn : gset Addr) : Prop :=
  ∀ a : Addr, (mshwmb_v ≤ a < mshwm_v)%Z → a ∈ zn.

(** The cover base: [mshwmb_v] while the window is closed, its target while it is
    open. *)
Definition hc_of (mshwmb_v : Z) (o : option Z) : Z := default mshwmb_v o.

(** The classes of the ghost state before its allocation. *)
Class ceriseGpreS Σ := {
  cerise_preG_mem :: gen_heapGpreS Addr LWord Σ;
  cerise_preG_shadow :: gen_heapGpreS Addr AllocStatus Σ;
  cerise_preG_pc :: pcGpreS Σ;
  cerise_preG_reg :: gen_heapGpreS RegName LWord Σ;
  cerise_preG_sreg :: gen_heapGpreS SRegName LWord Σ;
  cerise_preG_registry :: allocRegistryPreG Σ;
  cerise_preG_addr_alloc :: addrAllocPreG Σ;
  cerise_preG_mtdc :: mtdcGpreS Σ;
  cerise_preG_intst :: intstGpreS Σ;
  cerise_preG_excl :: inG Σ (exclR unitO);
  cerise_preG_oneshot :: inG Σ oneshotR;
  cerise_preG_hwm :: hwmGpreS Σ;
}.
#[export] Hint Mode ceriseGpreS - : typeclass_instances.

Definition ceriseGpreΣ : gFunctors :=
  #[gen_heapΣ Addr LWord; gen_heapΣ Addr AllocStatus; pcΣ; gen_heapΣ RegName LWord;
    gen_heapΣ SRegName LWord; allocRegistryΣ; addrAllocΣ; mtdcΣ; intstΣ;
    GFunctor (exclR unitO); GFunctor oneshotR; hwmΣ].

#[global] Instance subG_ceriseGpreS {Σ} : subG ceriseGpreΣ Σ → ceriseGpreS Σ.
Proof. solve_inG. Qed.

