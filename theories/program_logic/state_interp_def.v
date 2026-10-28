From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import proofmode.
From griotte Require Import griotte_lang named_props_extra.
From griotte Require Export resources crit_link.

(** The logical system registers of a step, in one argument: the shared
    heap [ls_sh] (without MTDC and mstatus), the ghost value [ls_mtdc] of
    the thread's mtdc and its logical word [ls_vmtdc], MIE and MPIE. *)
Record LSys := MkLSys {
  ls_sh : LSReg;
  ls_mtdc : mtdc_val;
  ls_vmtdc : LWord;
  ls_mie : InterruptStatus;
  ls_mpie : InterruptStatus;
}.

(** The logical system registers of [erasure]. *)
Definition ls_join (ls : LSys) : LSReg :=
  lsregs_join (ls_sh ls) (ls_vmtdc ls) (ls_mie ls) (ls_mpie ls).

Definition ls_set_mstatus (ls : LSys) (mie mpie : InterruptStatus) : LSys :=
  MkLSys (ls_sh ls) (ls_mtdc ls) (ls_vmtdc ls) mie mpie.
Definition ls_set_mtdc (ls : LSys) (m : mtdc_val) (vm : LWord) : LSys :=
  MkLSys (ls_sh ls) m vm (ls_mie ls) (ls_mpie ls).
Definition ls_insert_sh (ls : LSys) (sr : SRegName) (v : LWord) : LSys :=
  MkLSys (<[sr := v]> (ls_sh ls)) (ls_mtdc ls) (ls_vmtdc ls) (ls_mie ls) (ls_mpie ls).

Lemma ls_join_mstatus ls :
  ls_join ls !! MSTATUS = Some (lword_of_word (WInt (mstatus_enc (ls_mie ls) (ls_mpie ls)))).
Proof. apply lsregs_join_mstatus. Qed.

Lemma ls_join_mtdc ls : ls_join ls !! MTDC = Some (ls_vmtdc ls).
Proof. apply lsregs_join_mtdc. Qed.

Lemma ls_join_set_mstatus ls mie mpie :
  ls_join (ls_set_mstatus ls mie mpie) =
  <[MSTATUS := lword_of_word (WInt (mstatus_enc mie mpie))]> (ls_join ls).
Proof. by rewrite /ls_join /lsregs_join /= insert_insert_eq. Qed.

Lemma ls_join_set_mtdc ls m vm :
  ls_join (ls_set_mtdc ls m vm) = <[MTDC := vm]> (ls_join ls).
Proof.
  by rewrite /ls_join /lsregs_join /= (insert_insert_ne _ MTDC MSTATUS) // insert_insert_eq.
Qed.

Lemma ls_join_insert_sh ls sr v :
  sr ≠ MTDC → sr ≠ MSTATUS → ls_join (ls_insert_sh ls sr v) = <[sr := v]> (ls_join ls).
Proof.
  intros H1 H2. rewrite /ls_join /lsregs_join /=.
  rewrite (insert_insert_ne _ sr MSTATUS) // (insert_insert_ne _ sr MTDC) //.
Qed.

(** The state interpretation: a part shared by the threads and the part of
    the running thread, related to the machine state by their erasures. *)
Section state_interp.
  Context `{MP : MachineParameters}.
  Context `{!pcG Σ,
            !gen_heapGS RegName LWord Σ, !gen_heapGS SRegName LWord Σ,
            !gen_heapGS Addr LWord Σ, !gen_heapGS Addr AllocStatus Σ,
            !allocRegistryG Σ, !addrAllocG Σ, !trapVector, !cerise_na_invs Σ,
            !mtdcG Σ, !mieG Σ, !mpieG Σ}.

  (** The trap-entry windows of the running thread: the registers trap
      entry writes (MEPCC, mcause, mtval), held here, or lent to the code
      after trap entry, which then holds their points-to while the state
      interpretation holds the trap-entry tokens of the thread's pool. MEPCC
      and mcause are lent against the token without [Ntval], mtval, which
      holds an integer, against the token of [Ntval]. *)
  Definition trap_windows : iProp Σ :=
    "Hwin" ∷ (((∃ v, MEPCC ↦ₓ v) ∗ (∃ v, MCAUSE ↦ₓ v)) ∨
              na_own cerise_pool (↑Ntrap ∖ ↑Ntval)) ∗
    "Hwin_tval" ∷ ((∃ z : Z, MTVAL ↦ₓ lword_of_word (WInt z)) ∨
                   na_own cerise_pool (↑Ntval)).

  (** The shared part: the shared system registers (MTCC, which holds the
      trap vector [mtcc_vec], is reserved: no client holds its points-to),
      memory, the shadow table, the registry, the address claims, and the
      authority and fragment of MPIE. *)
  Definition SI_shared R C (σ : ExecConf) : iProp Σ :=
    ∃ (lsh : LSReg) (lmem : LMem) (mpie : InterruptStatus),
      "Hsr" ∷ gen_heap_interp lsh ∗
      "Hmtcc" ∷ MTCC ↦ₓ lword_of_word mtcc_vec ∗
      "Hm" ∷ gen_heap_interp lmem ∗
      "Hst" ∷ gen_heap_interp (shadowtbl σ) ∗
      "HR" ∷ reg_auth R ∗
      "HC" ∷ addr_alloc_auth C ∗
      "Hmpie" ∷ MPIE_auth mpie ∗
      "Hmpie_f" ∷ MPIE_frag mpie ∗
      "%Hersh" ∷ ⌜erasure_sh R C σ lsh lmem mpie⌝.

  (** The part of the running thread: its PC, its registers, the authority
      of its mtdc ghost, the authority and fragment of MIE, its trap-entry
      windows. *)
  Definition SI_th R C (σ : ExecConf) : iProp Σ :=
    ∃ (lpc : LWord) (lreg : LReg) (m : mtdc_val) (vm : LWord) (mie : InterruptStatus),
      "HPCa" ∷ PC_auth lpc ∗
      "Hr" ∷ gen_heap_interp lreg ∗
      "Hmtdc" ∷ mtdc_auth m ∗
      "%Hmtdc_m" ∷ ⌜mtdc_match m vm⌝ ∗
      "Hmie" ∷ MIE_auth mie ∗
      "Hmie_f" ∷ MIE_frag mie ∗
      "Hwins" ∷ trap_windows ∗
      "%Herth" ∷ ⌜erasure_th R C σ lpc lreg vm mie⌝.

  (** One [∃ R C] for both parts. *)
  Definition cerise_state_interp (σ : ExecConf) : iProp Σ :=
    ∃ R C, SI_shared R C σ ∗ SI_th R C σ.

  #[global] Instance cerise_state_interp_timeless σ : Timeless (cerise_state_interp σ).
  Proof. apply _. Qed.

  (** The system registers of a step, as one hypothesis: the shared heap,
      MTCC, MPIE, the thread's mtdc and MIE and its trap-entry windows. *)
  Definition sys_interp (ls : LSys) : iProp Σ :=
    "Hsr" ∷ gen_heap_interp (ls_sh ls) ∗
    "Hmtcc" ∷ MTCC ↦ₓ lword_of_word mtcc_vec ∗
    "Hmpie" ∷ MPIE_auth (ls_mpie ls) ∗
    "Hmpie_f" ∷ MPIE_frag (ls_mpie ls) ∗
    "Hmtdc" ∷ mtdc_auth (ls_mtdc ls) ∗
    "%Hmtdc_m" ∷ ⌜mtdc_match (ls_mtdc ls) (ls_vmtdc ls)⌝ ∗
    "Hmie" ∷ MIE_auth (ls_mie ls) ∗
    "Hmie_f" ∷ MIE_frag (ls_mie ls) ∗
    "Hwins" ∷ trap_windows ∗
    "%Hlsh" ∷ ⌜ls_sh ls !! MTDC = None ∧ ls_sh ls !! MSTATUS = None⌝.
End state_interp.

(* invariants for memory, and a state interpretation for (mem,reg), with
   the link of the critical sections *)
#[global] Instance memG_irisG `{MachineParameters} {Σ} {ceriseg : ceriseG Σ} {CL : CritLink Σ} :
  irisGS griotte_lang Σ := {
  iris_invGS := cerise_invG;
  state_interp σ _ κs _ := (cerise_state_interp σ ∗ crit_link σ)%I;
  fork_post _ := True%I;
  num_laters_per_step _ := 0;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.

(** * The WP of a thread

    [WP e @[th] E {{ Φ }}] is Iris's WP at the instance of thread [th], so
    the rule library and the proof mode apply to it unchanged. *)
Notation "'WP' e '@[' th ] E {{ Φ } }" :=
  (@wp _ _ _ _ (@wp' _ _ _ (memG_irisG (ceriseg := ceriseG_of th))) NotStuck E e%E Φ)
  (at level 20, th custom thread, e, Φ at level 200,
   format "'[hv' 'WP'  e  '/' '@[' th ]  E  '/' {{  Φ  } } ']'") : bi_scope.
Notation "'WP' e '@[' th ] {{ Φ } }" :=
  (@wp _ _ _ _ (@wp' _ _ _ (memG_irisG (ceriseg := ceriseG_of th))) NotStuck ⊤ e%E Φ)
  (at level 20, th custom thread, e, Φ at level 200,
   format "'[hv' 'WP'  e  '/' '@[' th ]  '/' {{  Φ  } } ']'") : bi_scope.
Notation "'WP' e '@[' th ] E {{ v , Q } }" :=
  (@wp _ _ _ _ (@wp' _ _ _ (memG_irisG (ceriseg := ceriseG_of th))) NotStuck E e%E (λ v, Q))
  (at level 20, th custom thread, e, Q at level 200, v at level 200 as pattern,
   format "'[hv' 'WP'  e  '/' '@[' th ]  E  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e '@[' th ] {{ v , Q } }" :=
  (@wp _ _ _ _ (@wp' _ _ _ (memG_irisG (ceriseg := ceriseG_of th))) NotStuck ⊤ e%E (λ v, Q))
  (at level 20, th custom thread, e, Q at level 200, v at level 200 as pattern,
   format "'[hv' 'WP'  e  '/' '@[' th ]  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

(** The postcondition of a safe execution of thread [th]: when the thread
    halts, it gives back its non-atomic token. *)
Definition HO {Σ} `{!ceriseBaseG Σ} (th : Thread) (v : griotte_lang.val) : iProp Σ :=
  ⌜v = HaltedV⌝ → na_own (tpool th) ⊤.

(* A WP with postcondition [HO th] prints as [{{ HO th }}], not η-expanded
   by the notations with a binder. *)
Notation "'WP' e '@[' th ] E {{ 'HO' th' } }" :=
  (@wp _ _ _ _ (@wp' _ _ _ (memG_irisG (ceriseg := ceriseG_of th))) NotStuck E e%E (HO th'))
  (at level 20, th custom thread, th' at level 0, e at level 200, only printing,
   format "'[hv' 'WP'  e  '/' '@[' th ]  E  '/' {{  HO  th'  } } ']'") : bi_scope.
Notation "'WP' e '@[' th ] {{ 'HO' th' } }" :=
  (@wp _ _ _ _ (@wp' _ _ _ (memG_irisG (ceriseg := ceriseG_of th))) NotStuck ⊤ e%E (HO th'))
  (at level 20, th custom thread, th' at level 0, e at level 200, only printing,
   format "'[hv' 'WP'  e  '/' '@[' th ]  '/' {{  HO  th'  } } ']'") : bi_scope.

(** A fancy update stated with only a base in scope is at the base's
    [cb_invG]. Iris's [elim_modal_fupd_wp] states the update at the WP's
    [iris_invGS], which typeclass search does not unify with [cb_invG]:
    this instance eliminates such an update in the WP of any thread. *)
#[global] Instance elim_modal_base_fupd_wp `{MP : MachineParameters} {Σ}
    {ceriseb : ceriseBaseG Σ} {CL : CritLink Σ} (th : Thread) p E e (P : iProp Σ) Φ :
  ElimModal True p false
    (@fupd _ (@bi_fupd_fupd _ (@uPred_bi_fupd HasLc Σ (@cb_invG Σ ceriseb))) E E P) P
    (WP e @[th] E {{ Φ }}) (WP e @[th] E {{ Φ }}).
Proof.
  exact (elim_modal_fupd_wp (irisGS_gen0 := memG_irisG (ceriseg := ceriseG_of th))
           p NotStuck E e P Φ).
Qed.

(** Texan triples of thread [th], as Iris's. *)
Notation "'{{{' P } } } e '@[' th ] E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @[th] E {{ Φ }})%I
  (at level 20, th custom thread, x closed binder, y closed binder,
   format "'[hv' {{{  '[' P ']'  } } }  '/  ' e  '/' '@[' th ]  E  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q ']'  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e '@[' th ] {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @[th] {{ Φ }})%I
  (at level 20, th custom thread, x closed binder, y closed binder,
   format "'[hv' {{{  '[' P ']'  } } }  '/  ' e  '/' '@[' th ]  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q ']'  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e '@[' th ] E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @[th] E {{ Φ }})%I
  (at level 20, th custom thread,
   format "'[hv' {{{  '[' P ']'  } } }  '/  ' e  '/' '@[' th ]  E  '/' {{{  '[' RET  pat ;  '/' Q ']'  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e '@[' th ] {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @[th] {{ Φ }})%I
  (at level 20, th custom thread,
   format "'[hv' {{{  '[' P ']'  } } }  '/  ' e  '/' '@[' th ]  '/' {{{  '[' RET  pat ;  '/' Q ']'  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e '@[' th ] E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @[th] E {{ Φ }})
  (at level 20, th custom thread, x closed binder, y closed binder,
   format "'[hv' {{{  '[' P ']'  } } }  '/  ' e  '/' '@[' th ]  E  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q ']'  } } } ']'") : stdpp_scope.
Notation "'{{{' P } } } e '@[' th ] {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @[th] {{ Φ }})
  (at level 20, th custom thread, x closed binder, y closed binder,
   format "'[hv' {{{  '[' P ']'  } } }  '/  ' e  '/' '@[' th ]  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q ']'  } } } ']'") : stdpp_scope.
Notation "'{{{' P } } } e '@[' th ] E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @[th] E {{ Φ }})
  (at level 20, th custom thread,
   format "'[hv' {{{  '[' P ']'  } } }  '/  ' e  '/' '@[' th ]  E  '/' {{{  '[' RET  pat ;  '/' Q ']'  } } } ']'") : stdpp_scope.
Notation "'{{{' P } } } e '@[' th ] {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @[th] {{ Φ }})
  (at level 20, th custom thread,
   format "'[hv' {{{  '[' P ']'  } } }  '/  ' e  '/' '@[' th ]  '/' {{{  '[' RET  pat ;  '/' Q ']'  } } } ']'") : stdpp_scope.

