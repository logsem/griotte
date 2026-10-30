From iris.base_logic Require Export invariants na_invariants gen_heap ghost_map ghost_var.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl_auth.
From griotte Require Export logical_words alloc_registry.

(** * The resources of Griotte

    The ghost state of the machine (the PC, the per-thread system registers
    mtdc, MIE, MSHWMB and MSHWM with the zone, and MPIE), the classes of a
    thread's instance and of the resources shared by the threads, and the
    points-to notations. *)

(** Non-atomic invariants: the pool of the running thread, which holds the
    tokens of trap entry in the state interpretation. Thread-level code names
    the pool of a thread [th] as [tpool th]. *)
Class cerise_na_invs Σ :=
  {
    na_invG :: na_invG Σ;
    cerise_pool : na_inv_pool_name;
  }.
#[export] Hint Mode cerise_na_invs - : typeclass_instances.

(** The logical PC: a single exclusive value, whose authoritative part is in
    the state interpretation. The PC is not a general register. *)
Definition pcUR := excl_authUR (leibnizO LWord).

Class pcG Σ := PcG {
  pc_inG :: inG Σ pcUR;
  pc_name : gname;
}.
#[export] Hint Mode pcG - : typeclass_instances.

Class pcGpreS Σ := { pc_preG_inG :: inG Σ pcUR }.
#[export] Hint Mode pcGpreS - : typeclass_instances.
Definition pcΣ : gFunctors := #[GFunctor pcUR].
#[global] Instance subG_pcGpreS {Σ} : subG pcΣ Σ → pcGpreS Σ.
Proof. solve_inG. Qed.

Section pc_resource.
  Context `{!pcG Σ}.

  Definition PC_auth (lpc : LWord) : iProp Σ := own pc_name (●E (lpc : leibnizO LWord)).
  Definition PC_frag (lpc : LWord) : iProp Σ := own pc_name (◯E (lpc : leibnizO LWord)).

  #[global] Instance PC_auth_timeless lpc : Timeless (PC_auth lpc).
  Proof. apply _. Qed.
  #[global] Instance PC_frag_timeless lpc : Timeless (PC_frag lpc).
  Proof. apply _. Qed.

  Lemma PC_agree lpc lpc' : PC_auth lpc -∗ PC_frag lpc' -∗ ⌜lpc = lpc'⌝.
  Proof.
    iIntros "Ha Hf". iCombine "Ha Hf" gives %Hv.
    by apply excl_auth_agree_L in Hv.
  Qed.

  Lemma PC_update lpc lpc' lpc'' : PC_auth lpc -∗ PC_frag lpc' ==∗ PC_auth lpc'' ∗ PC_frag lpc''.
  Proof.
    iIntros "Ha Hf". iMod (own_update_2 with "Ha Hf") as "[$ $]"; last done.
    apply excl_auth_update.
  Qed.

  Lemma PC_frag_excl lpc lpc' : PC_frag lpc -∗ PC_frag lpc' -∗ False.
  Proof.
    iIntros "H1 H2". iCombine "H1 H2" gives %Hv.
    by apply excl_auth_frag_op_valid in Hv.
  Qed.
End pc_resource.

Lemma PC_init `{!pcGpreS Σ} (lpc : LWord) :
  ⊢ |==> ∃ (pg : pcG Σ), PC_auth lpc ∗ PC_frag lpc.
Proof.
  iMod (own_alloc (●E (lpc : leibnizO LWord) ⋅ ◯E (lpc : leibnizO LWord))) as (γ) "[Ha Hf]".
  { apply excl_auth_valid. }
  iModIntro. iExists (PcG _ _ γ). iFrame.
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

  Lemma MIE_update b b' b'' : MIE_auth b -∗ MIE_frag b' ==∗ MIE_auth b'' ∗ MIE_frag b''.
  Proof.
    iIntros "Ha Hf". iMod (own_update_2 with "Ha Hf") as "[$ $]"; last done.
    apply excl_auth_update.
  Qed.
End mie_resource.

Section mpie_resource.
  Context `{!mpieG Σ}.
  Definition MPIE_auth (b : InterruptStatus) : iProp Σ := own mpie_name (●E (b : leibnizO _)).
  Definition MPIE_frag (b : InterruptStatus) : iProp Σ := own mpie_name (◯E (b : leibnizO _)).

  #[global] Instance MPIE_auth_timeless b : Timeless (MPIE_auth b).
  Proof. apply _. Qed.
  #[global] Instance MPIE_frag_timeless b : Timeless (MPIE_frag b).
  Proof. apply _. Qed.

  Lemma MPIE_update b b' b'' : MPIE_auth b -∗ MPIE_frag b' ==∗ MPIE_auth b'' ∗ MPIE_frag b''.
  Proof.
    iIntros "Ha Hf". iMod (own_update_2 with "Ha Hf") as "[$ $]"; last done.
    apply excl_auth_update.
  Qed.
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
    addresses with an exclusive token per address. *)
Definition hwmUR := excl_authUR (leibnizO Z).

Class hwmG Σ := HwmG {
  hwm_inG :: inG Σ hwmUR;
  hwm_zone_mapG :: ghost_mapG Σ Addr unit;
  mshwmb_name : gname;
  mshwm_name : gname;
  zone_name : gname;
}.
#[export] Hint Mode hwmG - : typeclass_instances.

Class hwmGpreS Σ := {
  hwm_preG_inG :: inG Σ hwmUR;
  hwm_preG_zone :: ghost_mapG Σ Addr unit;
}.
#[export] Hint Mode hwmGpreS - : typeclass_instances.
Definition hwmΣ : gFunctors := #[GFunctor hwmUR; ghost_mapΣ Addr unit].
#[global] Instance subG_hwmGpreS {Σ} : subG hwmΣ Σ → hwmGpreS Σ.
Proof. solve_inG. Qed.

Section hwm_resource.
  Context `{!hwmG Σ}.

  Definition mshwmb_auth (hb : Z) : iProp Σ := own mshwmb_name (●E (hb : leibnizO Z)).
  Definition mshwmb_frag (hb : Z) : iProp Σ := own mshwmb_name (◯E (hb : leibnizO Z)).
  Definition mshwm_auth (h : Z) : iProp Σ := own mshwm_name (●E (h : leibnizO Z)).
  Definition mshwm_frag (h : Z) : iProp Σ := own mshwm_name (◯E (h : leibnizO Z)).

  #[global] Instance mshwmb_auth_timeless hb : Timeless (mshwmb_auth hb).
  Proof. apply _. Qed.
  #[global] Instance mshwmb_frag_timeless hb : Timeless (mshwmb_frag hb).
  Proof. apply _. Qed.
  #[global] Instance mshwm_auth_timeless h : Timeless (mshwm_auth h).
  Proof. apply _. Qed.
  #[global] Instance mshwm_frag_timeless h : Timeless (mshwm_frag h).
  Proof. apply _. Qed.

  Lemma mshwmb_agree hb hb' : mshwmb_auth hb -∗ mshwmb_frag hb' -∗ ⌜hb = hb'⌝.
  Proof. iIntros "Ha Hf". iCombine "Ha Hf" gives %Hv. by apply excl_auth_agree_L in Hv. Qed.

  Lemma mshwmb_update hb hb' hb'' :
    mshwmb_auth hb -∗ mshwmb_frag hb' ==∗ mshwmb_auth hb'' ∗ mshwmb_frag hb''.
  Proof.
    iIntros "Ha Hf". iMod (own_update_2 with "Ha Hf") as "[$ $]"; last done.
    apply excl_auth_update.
  Qed.

  Lemma mshwmb_frag_excl hb hb' : mshwmb_frag hb -∗ mshwmb_frag hb' -∗ False.
  Proof. iIntros "H1 H2". iCombine "H1 H2" gives %Hv. by apply excl_auth_frag_op_valid in Hv. Qed.

  Lemma mshwm_agree h h' : mshwm_auth h -∗ mshwm_frag h' -∗ ⌜h = h'⌝.
  Proof. iIntros "Ha Hf". iCombine "Ha Hf" gives %Hv. by apply excl_auth_agree_L in Hv. Qed.

  Lemma mshwm_update h h' h'' :
    mshwm_auth h -∗ mshwm_frag h' ==∗ mshwm_auth h'' ∗ mshwm_frag h''.
  Proof.
    iIntros "Ha Hf". iMod (own_update_2 with "Ha Hf") as "[$ $]"; last done.
    apply excl_auth_update.
  Qed.

  Lemma mshwm_frag_excl h h' : mshwm_frag h -∗ mshwm_frag h' -∗ False.
  Proof. iIntros "H1 H2". iCombine "H1 H2" gives %Hv. by apply excl_auth_frag_op_valid in Hv. Qed.

  (** The exclusive token of the address [a] of the zone. *)
  Definition zone_token (a : Addr) : iProp Σ := a ↪[zone_name] ().

  (** The authoritative part of the zone [Z]. *)
  Definition zone_auth (Z : gset Addr) : iProp Σ :=
    ghost_map_auth zone_name 1 (gset_to_gmap () Z).

  #[global] Instance zone_token_timeless a : Timeless (zone_token a).
  Proof. apply _. Qed.

  Lemma zone_token_excl a : zone_token a -∗ zone_token a -∗ False.
  Proof. iIntros "H1 H2". by iDestruct (ghost_map_elem_ne with "H1 H2") as %?. Qed.

  Lemma zone_auth_elem Z a : zone_auth Z -∗ zone_token a -∗ ⌜a ∈ Z⌝.
  Proof.
    iIntros "Hauth Htok".
    iDestruct (ghost_map_lookup with "Hauth Htok") as %Hlookup.
    iPureIntro. by apply lookup_gset_to_gmap_Some in Hlookup as [? _].
  Qed.

  Lemma zone_auth_insert Z a : a ∉ Z → zone_auth Z ==∗ zone_auth ({[a]} ∪ Z) ∗ zone_token a.
  Proof.
    iIntros (HaZ) "Hauth". rewrite /zone_auth /zone_token gset_to_gmap_union_singleton.
    iApply (ghost_map_insert with "Hauth").
    by rewrite lookup_gset_to_gmap_None.
  Qed.

  Lemma zone_auth_delete Z a : zone_auth Z -∗ zone_token a ==∗ zone_auth (Z ∖ {[a]}).
  Proof.
    iIntros "Hauth Htok". rewrite /zone_auth /zone_token gset_to_gmap_difference_singleton.
    iApply (ghost_map_delete with "Hauth Htok").
  Qed.
End hwm_resource.

Lemma hwm_init `{!hwmGpreS Σ} (z : Z) :
  ⊢ |==> ∃ g : hwmG Σ,
    mshwmb_auth z ∗ mshwmb_frag z ∗ mshwm_auth z ∗ mshwm_frag z ∗ zone_auth ∅.
Proof.
  iMod (own_alloc (●E (z : leibnizO Z) ⋅ ◯E (z : leibnizO Z))) as (γb) "[Hba Hbf]".
  { apply excl_auth_valid. }
  iMod (own_alloc (●E (z : leibnizO Z) ⋅ ◯E (z : leibnizO Z))) as (γh) "[Hha Hhf]".
  { apply excl_auth_valid. }
  iMod (ghost_map_alloc_empty (K:=Addr) (V:=unit)) as (γz) "Hzauth".
  iModIntro. iExists (HwmG _ _ _ γb γh γz). rewrite /zone_auth gset_to_gmap_empty. iFrame.
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
      cerise_hwmG :: hwmG Σ (* MSHWMB, MSHWM and zone of the thread *)
    }.
#[export] Hint Mode ceriseG - : typeclass_instances.

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

(** The resources shared by the threads, and the per-thread ones as maps
    from threads: the PC, the general registers, the ghost state of mtdc,
    MIE, MSHWMB, MSHWM and the zone, and the non-atomic pool [tpool th]. The other system registers and
    MPIE are shared. The shared fields are [::]
    fields, the per-thread maps are not, so typeclass search finds a
    per-thread heap only through [ceriseG_of]. The shared fields other than
    [na_invG] have a low priority: with a thread in scope, the invariants,
    the memory, the shadow table, the system registers, the registry, the
    address claims and [mtcc_vec] elaborate through [ceriseG_of] as in the
    rule library; without one, through the base. Both are the same
    resources. *)
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
  cb_pc_of : Thread → pcG Σ;
  cb_regs_of : Thread → gen_heapGS RegName LWord Σ;
  cb_mtdc_of : Thread → mtdcG Σ;
  cb_mie_of : Thread → mieG Σ;
  cb_hwm_of : Thread → hwmG Σ;
  tpool : Thread → na_inv_pool_name;
}.
#[export] Hint Mode ceriseBaseG - : typeclass_instances.
#[global] Arguments tpool {Σ _} th : rename.

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
    (@cb_hwm_of Σ base th).
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
#[global] Arguments cerise_hwmG : simpl never.

(** The namespace of the non-atomic token of trap entry: a fault hands it
    to the state interpretation, in exchange for MEPCC, mcause and mtval.
    Its part [Ntval] is exchanged for mtval, the rest for MEPCC and
    mcause. *)
Definition Ntrap : namespace := nroot .@ "trap_entry".
Definition Ntval : namespace := Ntrap .@ "tval".

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

(** The MSHWMB and MSHWM fragments of a thread: [mshwm ↦ₜ h] in proofs and
    in instance-generic files, [mshwm ↦ₜ[th] h] for thread [th]. [mshwm] and
    [mshwmb] are keywords at level 0, as [mtdc]. *)
Notation "'mshwmb' ↦ₜ hb" := (mshwmb_frag hb)
  (at level 0, hb at level 10, format "'mshwmb'  ↦ₜ  hb") : bi_scope.
Notation "'mshwmb' ↦ₜ[ th ] hb" := (@mshwmb_frag _ (@cerise_hwmG _ (ceriseG_of th)) hb)
  (at level 0, th custom thread, hb at level 10, format "'mshwmb'  ↦ₜ[ th ]  hb") : bi_scope.
Notation "'mshwm' ↦ₜ h" := (mshwm_frag h)
  (at level 0, h at level 10, format "'mshwm'  ↦ₜ  h") : bi_scope.
Notation "'mshwm' ↦ₜ[ th ] h" := (@mshwm_frag _ (@cerise_hwmG _ (ceriseG_of th)) h)
  (at level 0, th custom thread, h at level 10, format "'mshwm'  ↦ₜ[ th ]  h") : bi_scope.

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

  (** A cell of the zone: its token, and half of its points-to, which holds
      zero. The state interpretation holds the other half. *)
  Definition zone_cell_def (a : Addr) : iProp Σ :=
    zone_token a ∗ a ↦ₐ{DfracOwn (1/2)} lword_of_word (WInt 0).
  #[local] Definition zone_cell_aux : seal (@zone_cell_def). Proof. by eexists. Qed.
  Definition zone_cell := zone_cell_aux.(unseal).
  #[local] Definition zone_cell_unseal : @zone_cell = @zone_cell_def :=
    zone_cell_aux.(seal_eq).

  Lemma zone_cell_unfold a :
    zone_cell a ⊣⊢ zone_token a ∗ a ↦ₐ{DfracOwn (1/2)} lword_of_word (WInt 0).
  Proof. by rewrite zone_cell_unseal. Qed.

  #[global] Instance zone_cell_timeless a : Timeless (zone_cell a).
  Proof. rewrite zone_cell_unseal. apply _. Qed.

  Lemma zone_cell_excl a : zone_cell a -∗ zone_cell a -∗ False.
  Proof.
    rewrite !zone_cell_unfold. iIntros "[H1 _] [H2 _]".
    iApply (zone_token_excl with "H1 H2").
  Qed.

  (** A full points-to is not in the zone. *)
  Lemma zone_cells_not_elem (zone : gset Addr) a w :
    ([∗ set] a' ∈ zone, a' ↦ₐ{DfracOwn (1/2)} lword_of_word (WInt 0)) -∗
    a ↦ₐ w -∗
    ⌜a ∉ zone⌝.
  Proof.
    iIntros "Hcells Ha". destruct (decide (a ∈ zone)) as [Ha|Ha]; last done.
    iDestruct (big_sepS_elem_of with "Hcells") as "Ha'"; first exact Ha.
    iDestruct (pointsto_valid_2 with "Ha Ha'") as %[Hv _].
    iPureIntro. rewrite dfrac_op_own dfrac_valid_own in Hv.
    by apply Qp.not_add_le_l in Hv.
  Qed.
End zone.

(** A cell of the zone of thread [th]; plain [zone_cell a] in proofs and in
    instance-generic files. The memory and the zone are those of
    [ceriseG_of th]. *)
Notation "'zone_cell[' th ] a" :=
  (@zone_cell _ (@mem_gen_memG _ (ceriseG_of th)) (@cerise_hwmG _ (ceriseG_of th)) a)
  (at level 20, th custom thread, a at level 9, format "'zone_cell[' th ]  a") : bi_scope.

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
  cerise_preG_hwm :: hwmGpreS Σ;
}.
#[export] Hint Mode ceriseGpreS - : typeclass_instances.

Definition ceriseGpreΣ : gFunctors :=
  #[gen_heapΣ Addr LWord; gen_heapΣ Addr AllocStatus; pcΣ; gen_heapΣ RegName LWord;
    gen_heapΣ SRegName LWord; allocRegistryΣ; addrAllocΣ; mtdcΣ; intstΣ; hwmΣ].

#[global] Instance subG_ceriseGpreS {Σ} : subG ceriseGpreΣ Σ → ceriseGpreS Σ.
Proof. solve_inG. Qed.

