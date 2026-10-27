From iris.base_logic Require Export invariants na_invariants gen_heap ghost_map ghost_var.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl_auth.
From griotte Require Import griotte_lang.
From griotte Require Export logical_words alloc_registry erasure.
From griotte Require Import named_props_extra.



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
      cerise_trapVector :: trapVector (* trap vector *)
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

(** The resources shared by the threads, and the per-thread ones as maps
    from threads: the PC, the general registers and the non-atomic pool
    [tpool th]. The system registers are shared. The shared fields are [::]
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
  cb_pc_of : Thread → pcG Σ;
  cb_regs_of : Thread → gen_heapGS RegName LWord Σ;
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
    (@cb_sreg Σ base) (@cb_registry Σ base) (@cb_addr_alloc Σ base) (@cb_trapVector Σ base).
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

(** The namespace of the non-atomic token of trap entry: a fault hands it
    to the state interpretation, in exchange for MEPCC, mcause and mtval.
    Its part [Ntval] is exchanged for mtval, the rest for MEPCC and
    mcause. *)
Definition Ntrap : namespace := nroot .@ "trap_entry".
Definition Ntval : namespace := Ntrap .@ "tval".

(** The state interpretation: the logical PC, registers, system registers and
    memory, the physical shadow table, the registry and the address claims,
    related to the machine state by erasure. *)
Section state_interp.
  Context `{MP : MachineParameters}.
  Context `{!pcG Σ,
            !gen_heapGS RegName LWord Σ, !gen_heapGS SRegName LWord Σ,
            !gen_heapGS Addr LWord Σ, !gen_heapGS Addr AllocStatus Σ,
            !allocRegistryG Σ, !addrAllocG Σ, !trapVector, !cerise_na_invs Σ}.

  (** The system registers that the state interpretation reserves: mstatus,
      the registers trap entry writes (MEPCC, mcause, mtval) and MTCC, which
      holds the trap vector [mtcc_vec]. No client holds the points-to of
      mstatus and MTCC. MEPCC and mcause are held here, or lent to the code
      after trap entry, which then holds their points-to while the state
      interpretation holds the trap-entry token without [Ntval]. mtval,
      which holds an integer, is held here, or lent likewise against the
      token of [Ntval]. *)
  Definition sreg_reserved : iProp Σ :=
    "Hmstatus" ∷ (∃ v, pointsto (L:=SRegName) (V:=LWord) MSTATUS (DfracOwn 1) v) ∗
    "Hwin" ∷ (((∃ v, pointsto (L:=SRegName) (V:=LWord) MEPCC (DfracOwn 1) v) ∗
               (∃ v, pointsto (L:=SRegName) (V:=LWord) MCAUSE (DfracOwn 1) v)) ∨
              na_own cerise_pool (↑Ntrap ∖ ↑Ntval)) ∗
    "Hwin_tval" ∷ ((∃ z : Z, pointsto (L:=SRegName) (V:=LWord) MTVAL (DfracOwn 1)
                               (lword_of_word (WInt z))) ∨
                   na_own cerise_pool (↑Ntval)) ∗
    "Hmtcc" ∷ pointsto (L:=SRegName) (V:=LWord) MTCC (DfracOwn 1) (lword_of_word mtcc_vec).

  (** The logical system registers, with the reserved points-to. *)
  Definition sreg_interp (lsreg : LSReg) : iProp Σ :=
    gen_heap_interp lsreg ∗ sreg_reserved.

  Lemma sreg_interp_update_mstatus lsreg v :
    sreg_interp lsreg ==∗ sreg_interp (<[MSTATUS := v]> lsreg).
  Proof.
    iIntros "[Hsr Hres]". iNamed "Hres". iDestruct "Hmstatus" as (v0) "Hmstatus".
    iMod (gen_heap_update _ _ _ v with "Hsr Hmstatus") as "[$ Hmstatus]".
    iModIntro. iFrame.
  Qed.

  Lemma sreg_interp_mstatus lsreg :
    sreg_interp lsreg -∗ ⌜∃ v, lsreg !! MSTATUS = Some v⌝.
  Proof.
    iIntros "[Hsr Hres]". iNamed "Hres". iDestruct "Hmstatus" as (v) "Hmstatus".
    iDestruct (gen_heap_valid with "Hsr Hmstatus") as %Hlookup. eauto.
  Qed.

  (** MTCC holds the trap vector. *)
  Lemma sreg_interp_mtcc lsreg :
    sreg_interp lsreg -∗ ⌜lsreg !! MTCC = Some (lword_of_word mtcc_vec)⌝.
  Proof.
    iIntros "[Hsr Hres]". iNamed "Hres".
    iDestruct (gen_heap_valid with "Hsr Hmtcc") as %Hlookup. eauto.
  Qed.

  Definition cerise_state_interp (σ : ExecConf) : iProp Σ :=
    ∃ (lpc : LWord) (lreg : LReg) (lsreg : LSReg) (lmem : LMem) (R : RegState)
      (C : gmap Addr AddrClaim),
      "HPCa" ∷ PC_auth lpc ∗
      "Hr" ∷ gen_heap_interp lreg ∗
      "Hsr" ∷ sreg_interp lsreg ∗
      "Hm" ∷ gen_heap_interp lmem ∗
      "Hst" ∷ gen_heap_interp (shadowtbl σ) ∗
      "HR" ∷ reg_auth R ∗
      "HC" ∷ addr_alloc_auth C ∗
      "%Her" ∷ ⌜erasure R C σ lpc lreg lsreg lmem⌝.

  #[global] Instance cerise_state_interp_timeless σ : Timeless (cerise_state_interp σ).
  Proof. apply _. Qed.
End state_interp.

(* invariants for memory, and a state interpretation for (mem,reg) *)
#[global] Instance memG_irisG `{MachineParameters} `{ceriseg : !ceriseG Σ} : irisGS griotte_lang Σ := {
  iris_invGS := cerise_invG;
  state_interp σ _ κs _ := cerise_state_interp σ;
  fork_post _ := True%I;
  num_laters_per_step _ := 0;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.

(* Points to predicate for the PC *)
Notation "'PC' ↦ₚ w" := (PC_frag w) (at level 20, format "'PC'  ↦ₚ  w") : bi_scope.

(* Points to predicates for registers *)
Notation "r ↦ᵣ{ q } w" := (pointsto (L:=RegName) (V:=LWord) r q w)
  (at level 20, q at level 50, format "r  ↦ᵣ{ q }  w") : bi_scope.
Notation "r ↦ᵣ w" := (pointsto (L:=RegName) (V:=LWord) r (DfracOwn 1) w) (at level 20) : bi_scope.
Notation "r ↦ᵣ -" := (∃ w, pointsto (L:=RegName) (V:=LWord) r (DfracOwn 1) w)%I (at level 20) : bi_scope.

(* Points to predicates for the PC and registers of thread [th] *)
Notation "'PC' ↦ₚ[ th ] w" := (@PC_frag _ (@cerise_pcG _ (ceriseG_of th)) w)
  (at level 20, th custom thread, format "'PC'  ↦ₚ[ th ]  w") : bi_scope.
Notation "r ↦ᵣ[ th ]{ q } w" :=
  (@pointsto RegName _ _ LWord _ (@reg_gen_regG _ (ceriseG_of th)) r q w)
  (at level 20, th custom thread, q at level 50, format "r  ↦ᵣ[ th ]{ q }  w") : bi_scope.
Notation "r ↦ᵣ[ th ] w" :=
  (@pointsto RegName _ _ LWord _ (@reg_gen_regG _ (ceriseG_of th)) r (DfracOwn 1) w)
  (at level 20, th custom thread, format "r  ↦ᵣ[ th ]  w") : bi_scope.
Notation "r ↦ᵣ[ th ] -" :=
  (∃ w, @pointsto RegName _ _ LWord _ (@reg_gen_regG _ (ceriseG_of th)) r (DfracOwn 1) w)%I
  (at level 20, th custom thread, format "r  ↦ᵣ[ th ]  -") : bi_scope.

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
    {ceriseb : ceriseBaseG Σ} (th : Thread) p E e (P : iProp Σ) Φ :
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

(* Points to predicates for system registers *)
Notation "sr ↦ₓ{ q } w" := (pointsto (L:=SRegName) (V:=LWord) sr q w)
  (at level 20, q at level 50, format "sr  ↦ₓ{ q }  w") : bi_scope.
Notation "sr ↦ₓ w" := (pointsto (L:=SRegName) (V:=LWord) sr (DfracOwn 1) w) (at level 20) : bi_scope.
Notation "sr ↦ₓ -" := (∃ w, pointsto (L:=SRegName) (V:=LWord) sr (DfracOwn 1) w)%I (at level 20) : bi_scope.

(* Points to predicates for memory *)
Notation "a ↦ₐ{ q } w" := (pointsto (L:=Addr) (V:=LWord) a q w)
  (at level 20, q at level 50, format "a  ↦ₐ{ q }  w") : bi_scope.
Notation "a ↦ₐ w" := (pointsto (L:=Addr) (V:=LWord) a (DfracOwn 1) w) (at level 20) : bi_scope.
Notation "a ↦ₐ -" := (∃ w, pointsto (L:=Addr) (V:=LWord) a (DfracOwn 1) w)%I (at level 20) : bi_scope.
Notation "a ↦ₐ□ w" := (pointsto (L:=Addr) (V:=LWord) a DfracDiscarded w)
  (at level 20, format "a  ↦ₐ□  w") : bi_scope.

(* Points to predicates for shadow table *)
Notation "a ↦ₛ{ q } b" := (pointsto (L:=Addr) (V:=AllocStatus) a q b)
  (at level 20, q at level 50, format "a  ↦ₛ{ q }  b") : bi_scope.
Notation "a ↦ₛ b" := (pointsto (L:=Addr) (V:=AllocStatus) a (DfracOwn 1) b) (at level 20) : bi_scope.
Notation "a ↦ₛ -" := (∃ b, pointsto (L:=Addr) (V:=AllocStatus) a (DfracOwn 1) b)%I (at level 20) : bi_scope.

(** * Initialisation of the ghost state

    The logical heaps start without identifiers: the logical registers and
    memory are the physical ones (with [lnull] at [cnull]), the registry is
    empty, and the heap addresses are heap roots on a given set [H] and
    unclaimed elsewhere. *)

Class ceriseGpreS Σ := {
  cerise_preG_mem :: gen_heapGpreS Addr LWord Σ;
  cerise_preG_shadow :: gen_heapGpreS Addr AllocStatus Σ;
  cerise_preG_pc :: pcGpreS Σ;
  cerise_preG_reg :: gen_heapGpreS RegName LWord Σ;
  cerise_preG_sreg :: gen_heapGpreS SRegName LWord Σ;
  cerise_preG_registry :: allocRegistryPreG Σ;
  cerise_preG_addr_alloc :: addrAllocPreG Σ;
}.
#[export] Hint Mode ceriseGpreS - : typeclass_instances.

Definition ceriseGpreΣ : gFunctors :=
  #[gen_heapΣ Addr LWord; gen_heapΣ Addr AllocStatus; pcΣ; gen_heapΣ RegName LWord;
    gen_heapΣ SRegName LWord; allocRegistryΣ; addrAllocΣ].

#[global] Instance subG_ceriseGpreS {Σ} : subG ceriseGpreΣ Σ → ceriseGpreS Σ.
Proof. solve_inG. Qed.

(** The system registers that the state interpretation reserves. *)
Definition reserved_sregs : list SRegName := [MSTATUS; MEPCC; MCAUSE; MTVAL; MTCC].

(** The system registers that adequacy hands out: those not reserved. *)
Definition sregs_handed_out (sr : SReg) : SReg :=
  delete MTCC (delete MTVAL (delete MCAUSE (delete MEPCC (delete MSTATUS sr)))).

Lemma lookup_sregs_handed_out_mtdc (sr : SReg) w :
  sr !! MTDC = Some w → sregs_handed_out sr !! MTDC = Some w.
Proof. intros Hw. by rewrite /sregs_handed_out !lookup_delete_ne. Qed.

Section ghost_init.
  Context `{MP : MachineParameters, TV : !trapVector}.

  (** The initial logical registers: the physical ones without identifiers,
      and [lnull] at [cnull]. *)
  Definition init_lregs (regs : Reg) : LReg :=
    match regs !! cnull with
    | Some _ => <[cnull := lnull]> (lword_of_word <$> regs)
    | None => lword_of_word <$> regs
    end.

  Definition init_lmem (m : Mem) : LMem := lword_of_word <$> m.

  Definition init_lsregs (sregs : SReg) : LSReg := lword_of_word <$> sregs.

  (** The initial claims: heap roots on [H], unclaimed elsewhere in the heap. *)
  Definition init_claims (H : gset Addr) : gmap Addr AddrClaim :=
    map_imap (λ a _, Some (if decide (a ∈ H) then HeapRoot else Unclaimed))
      (gset_to_gmap tt heap_addresses).

  (** Every initial word with authority is based on a heap root, heap roots
      are unpainted, memory avoids the memory-mapped devices and covers the
      heap, [cnull] holds zero, and every tagged executable word
      has closed bounds that avoid the heap; a tagged PC, MTCC or MEPCC is an
      unsealed executable capability; the system registers that the state
      interpretation reserves exist, MTCC holds the trap vector and mtval an
      integer. *)
  Record ghost_init_cond (σ : ExecConf) (H : gset Addr) : Prop := {
    gi_roots_heap a : a ∈ H → is_heap_address a = true;
    gi_roots_unpainted a : a ∈ H → shadowtbl σ !! a = Some ShadowLive;
    gi_shadow a : is_heap_address a = true → is_Some (shadowtbl σ !! a);
    gi_mem a w b : mem σ !! a = Some w → get_tag w = true → heap_authority_base w = Some b → b ∈ H;
    gi_pc b : get_tag (pcc σ) = true → heap_authority_base (pcc σ) = Some b → b ∈ H;
    gi_regs r w b : r ≠ cnull → reg σ !! r = Some w → get_tag w = true →
                    heap_authority_base w = Some b → b ∈ H;
    gi_sregs sr w b : sreg σ !! sr = Some w → get_tag w = true →
                      heap_authority_base w = Some b → b ∈ H;
    gi_mmio : mem_avoids_mmio (mem σ);
    gi_heap_mapped : heap_mapped (mem σ);
    gi_cnull w : reg σ !! cnull = Some w → w = WInt 0;
    gi_mem_exec a w : mem σ !! a = Some w → lword_exec (lword_of_word w);
    gi_pc_exec : lword_exec (lword_of_word (pcc σ));
    gi_regs_exec r w : reg σ !! r = Some w → lword_exec (lword_of_word w);
    gi_sregs_exec sr w : sreg σ !! sr = Some w → lword_exec (lword_of_word w);
    gi_pc_ok : pc_ok (pcc σ);
    gi_sregs_pc_ok sr w : is_pc_sreg sr = true → sreg σ !! sr = Some w → pc_ok w;
    gi_reserved_sregs sr : sr ∈ reserved_sregs → is_Some (sreg σ !! sr);
    gi_mtcc : sreg σ !! MTCC = Some mtcc_vec;
    gi_mtval : ∃ z, sreg σ !! MTVAL = Some (WInt z);
  }.

  Lemma lookup_init_claims H a :
    init_claims H !! a =
      if is_heap_address a then Some (if decide (a ∈ H) then HeapRoot else Unclaimed) else None.
  Proof.
    rewrite /init_claims map_lookup_imap lookup_gset_to_gmap.
    destruct (is_heap_address a) eqn:Ha.
    - rewrite option_guard_True //=. by apply elem_of_heap_addresses.
    - rewrite option_guard_False //=. by rewrite elem_of_heap_addresses Ha.
  Qed.

  Lemma lookup_init_lregs regs r :
    init_lregs regs !! r = if decide (r = cnull) then (λ _, lnull) <$> regs !! r
                           else lword_of_word <$> regs !! r.
  Proof.
    rewrite /init_lregs. destruct (regs !! cnull) eqn:Hc.
    - case_decide as Hr; first subst r.
      + by rewrite lookup_insert_eq Hc.
      + by rewrite lookup_insert_ne // lookup_fmap.
    - case_decide; subst; by rewrite lookup_fmap ?Hc.
  Qed.

  Lemma init_erasure σ H :
    ghost_init_cond σ H →
    erasure ∅ (init_claims H) σ (lword_of_word (pcc σ)) (init_lregs (reg σ))
      (init_lsregs (sreg σ)) (init_lmem (mem σ)).
  Proof.
    intros Hinit.
    assert (∀ w, (∀ b, get_tag w = true → heap_authority_base w = Some b → b ∈ H) →
              lword_exec (lword_of_word w) →
              reg_word_ok ∅ (init_claims H) (lword_of_word w)) as Hok.
    { intros w Hroot Hexec. split; first by apply lword_prov_no_id. split; last done.
      intros b Ht Hab; cbn. rewrite lookup_init_claims.
      assert (is_heap_address b = true) as ->.
      { apply heap_authority_base_memory_cap_bounds in Hab as (? & ? & ? & ?). done. }
      case_decide as Hb; first done. exfalso. apply Hb, Hroot; done. }
    constructor.
    - constructor.
      + intros ι x a Hx. by rewrite lookup_empty in Hx.
      + intros ι x a Hx. by rewrite lookup_empty in Hx.
      + intros ι x a Hx. by rewrite lookup_empty in Hx.
      + intros a. rewrite lookup_init_claims. destruct (is_heap_address a); naive_solver.
      + intros a ι. rewrite lookup_init_claims. split.
        * destruct (is_heap_address a); last done. case_decide; done.
        * intros (x & Hx & _). by rewrite lookup_empty in Hx.
      + intros a. rewrite lookup_init_claims. destruct (is_heap_address a); last done.
        case_decide; last done. intros _. by apply Hinit.
      + apply Hinit.
    - split.
      + apply set_eq. intros r. rewrite !elem_of_dom lookup_init_lregs.
        case_decide; by rewrite fmap_is_Some.
      + intros r v. rewrite lookup_init_lregs. case_decide as Hr.
        * subst r. intros Hv. apply fmap_Some in Hv as (w & Hc & ->).
          exists w. split; first done. rewrite (gi_cnull _ _ Hinit w Hc). apply reg_phys_lnull.
        * intros Hv. apply fmap_Some in Hv as (w & Hw & ->).
          exists w. split; first done. apply reg_phys_lword_of_word.
    - intros v. rewrite lookup_init_lregs. case_decide; last done. intros Hv.
      apply fmap_Some in Hv as (? & _ & ->). done.
    - intros r v. rewrite lookup_init_lregs. case_decide.
      + intros Hv. apply fmap_Some in Hv as (? & _ & ->). apply reg_word_ok_lnull.
      + intros Hv. apply fmap_Some in Hv as (w & Hw & ->).
        apply Hok; last by eapply gi_regs_exec. intros b. eapply gi_regs; eauto.
    - intros sr v. rewrite /init_lsregs lookup_fmap. intros Hv.
      apply fmap_Some in Hv as (w & Hw & ->).
      exists w. split; first done. apply reg_phys_lword_of_word.
    - intros sr v. rewrite /init_lsregs lookup_fmap. intros Hv.
      apply fmap_Some in Hv as (w & Hw & ->).
      apply Hok; last by eapply gi_sregs_exec. intros b. eapply gi_sregs; eauto.
    - intros sr v _. rewrite /init_lsregs lookup_fmap. intros Hv _.
      by apply fmap_Some in Hv as (w & Hw & ->).
    - intros sr v Hsr. rewrite /init_lsregs lookup_fmap. intros Hv.
      apply fmap_Some in Hv as (w & Hw & ->). by eapply gi_sregs_pc_ok.
    - by rewrite /init_lmem dom_fmap_L.
    - intros a v pw Hv Hpw. rewrite /init_lmem lookup_fmap Hpw /= in Hv.
      injection Hv as <-.
      apply (reg_phys_mem_word_ok _ _ (lword_of_word pw)); last apply reg_phys_lword_of_word.
      apply Hok; last by eapply gi_mem_exec.
      intros b. eapply gi_mem; eauto.
    - apply Hinit.
    - apply reg_phys_lword_of_word.
    - apply Hok; last by apply (gi_pc_exec _ _ Hinit). intros b. by apply gi_pc.
    - apply Hinit.
    - apply Hinit.
  Qed.

  Context `{!ceriseGpreS Σ, !cerise_na_invs Σ}.

  (** The generic ghost initialisation of every adequacy theorem. It returns
      the state interpretation, the logical PC, register, system register,
      memory and shadow points-to, and the address claims. *)
  Lemma cerise_ghost_init σ H :
    ghost_init_cond σ H →
    ⊢ |==> ∃ (mg : gen_heapGS Addr LWord Σ) (sg : gen_heapGS Addr AllocStatus Σ)
             (pg : pcG Σ)
             (rg : gen_heapGS RegName LWord Σ) (srg : gen_heapGS SRegName LWord Σ)
             (regg : allocRegistryG Σ) (ag : addrAllocG Σ),
      cerise_state_interp σ ∗
      PC ↦ₚ lword_of_word (pcc σ) ∗
      ([∗ map] r ↦ w ∈ init_lregs (reg σ), r ↦ᵣ w) ∗
      ([∗ map] sr ↦ w ∈ sregs_handed_out (sreg σ), sr ↦ₓ lword_of_word w) ∗
      ([∗ map] a ↦ w ∈ init_lmem (mem σ), a ↦ₐ w) ∗
      ([∗ map] a ↦ s ∈ shadowtbl σ, a ↦ₛ s) ∗
      ([∗ map] a ↦ c ∈ init_claims H, addr_alloc a c).
  Proof.
    iIntros (Hinit).
    iMod (PC_init (lword_of_word (pcc σ))) as (pg) "[Hpc Hpcs]".
    iMod (gen_heap_init (init_lregs (reg σ))) as (rg) "(Hr & Hrs & _)".
    iMod (gen_heap_init (init_lsregs (sreg σ))) as (srg) "(Hsr & Hsrs & _)".
    iMod (gen_heap_init (init_lmem (mem σ))) as (mg) "(Hm & Hms & _)".
    iMod (gen_heap_init (shadowtbl σ)) as (sg) "(Hst & Hsts & _)".
    iMod registry_init as (regg) "HR".
    iMod (addr_alloc_init (init_claims H)) as (ag) "[HC HCs]".
    iModIntro. iExists mg, sg, pg, rg, srg, regg, ag.
    rewrite /init_lsregs big_sepM_fmap.
    destruct (gi_reserved_sregs _ _ Hinit MSTATUS) as [wst Hwst]; first set_solver.
    destruct (gi_reserved_sregs _ _ Hinit MEPCC) as [wepcc Hwepcc]; first set_solver.
    destruct (gi_reserved_sregs _ _ Hinit MCAUSE) as [wcause Hwcause]; first set_solver.
    destruct (gi_mtval _ _ Hinit) as [ztval Hwtval].
    pose proof (gi_mtcc _ _ Hinit) as Hwtcc.
    iDestruct (big_sepM_delete _ _ MSTATUS with "Hsrs") as "[Hmstatus Hsrs]"; first exact Hwst.
    iDestruct (big_sepM_delete _ _ MEPCC with "Hsrs") as "[Hmepcc Hsrs]";
      first by rewrite lookup_delete_ne.
    iDestruct (big_sepM_delete _ _ MCAUSE with "Hsrs") as "[Hmcause Hsrs]";
      first by rewrite !lookup_delete_ne.
    iDestruct (big_sepM_delete _ _ MTVAL with "Hsrs") as "[Hmtval Hsrs]";
      first by rewrite !lookup_delete_ne.
    iDestruct (big_sepM_delete _ _ MTCC with "Hsrs") as "[Hmtcc Hsrs]";
      first by rewrite !lookup_delete_ne.
    iAssert (sreg_interp (lword_of_word <$> sreg σ))
      with "[Hsr Hmstatus Hmepcc Hmcause Hmtval Hmtcc]" as "Hsr".
    { iFrame "Hsr Hmstatus Hmtcc". iSplitL "Hmepcc Hmcause"; iLeft; iFrame. }
    iFrame. iPureIntro. by apply init_erasure.
  Qed.

  (** The projection of the initial logical memory onto the physical one. *)
  Lemma init_lmem_pointsto `{!gen_heapGS Addr LWord Σ} (m : Mem) :
    ([∗ map] a ↦ w ∈ init_lmem m, a ↦ₐ w) ⊣⊢ [∗ map] a ↦ w ∈ m, a ↦ₐ lword_of_word w.
  Proof. by rewrite /init_lmem big_sepM_fmap. Qed.
End ghost_init.
