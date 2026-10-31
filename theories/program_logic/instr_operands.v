From iris.proofmode Require Import proofmode.
From griotte Require Export resources erasure register_file machine_instructions.

(** * Instruction operands

    The registers and system registers an instruction uses, the logical PC
    increment, the logical register lookups and their physical copies, and
    the dereference witnesses. No WP. *)

(* Splits the points-to of a register map built by inserts into one
   points-to per register; the inserted keys must be provably distinct. *)
Ltac iRegsMap H :=
  iRename H into "Hregs_map";
  rewrite -?insert_empty;
  repeat (
    iDestruct (big_sepM_insert_delete with "Hregs_map") as "[? Hregs_map]";
    repeat first [ rewrite delete_insert_eq
                 | rewrite delete_insert_ne; [|first [done | by apply not_eq_sym] ]
                 | rewrite delete_empty ]);
  iClear "Hregs_map".

(* ----------------- useful definitions to factor out the wp specs ---------------- *)

(*--- regs_of ---*)

Definition regs_of_argument (arg: Z + RegName): gset RegName :=
  match arg with
  | inl _ => ∅
  | inr r => {[ r ]}
  end.

(** The register operands of an instruction, read or written. *)
Definition operands_of (i: instr): gset RegName :=
  match i with
  | Lea dst src arg => {[ dst; src ]} ∪ regs_of_argument arg
  | SetA dst src arg => {[ dst; src ]} ∪ regs_of_argument arg
  | GetP r1 r2 => {[ r1; r2 ]}
  | GetB r1 r2 => {[ r1; r2 ]}
  | GetE r1 r2 => {[ r1; r2 ]}
  | GetLen r1 r2 => {[ r1; r2 ]}
  | GetA r1 r2 => {[ r1; r2 ]}
  | GetL r1 r2 => {[ r1; r2 ]}
  | GetOType dst src => {[ dst; src ]}
  | GetWType dst src => {[ dst; src ]}
  | GetTag dst src => {[ dst; src ]}
  | ClearTag dst src => {[ dst; src ]}
  | machine_instructions.Add r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | Sub r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | Mul r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | LAnd r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | LOr r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | LShiftL r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | LShiftR r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | Lt r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | Le r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | Mov r arg => {[ r ]} ∪ regs_of_argument arg
  | Restrict dst src arg => {[ dst; src ]} ∪ regs_of_argument arg
  | Subseg dst src arg1 arg2 => {[ dst; src ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | CLoad r1 r2 _ => {[ r1; r2 ]}
  | Store r1 arg _ => {[ r1 ]} ∪ regs_of_argument arg
  | Jeq off r1 r2 | Jne off r1 r2 | Jlt off r1 r2 | Jle off r1 r2 =>
      regs_of_argument off ∪ regs_of_argument r1 ∪ regs_of_argument r2
  | Jmp arg => regs_of_argument arg
  | Jalr rdst rsrc => {[ rsrc; rdst ]}
  | Seal dst r1 r2 => {[dst; r1; r2]}
  | UnSeal dst r1 r2 => {[dst; r1; r2]}
  | SpecialRW dst _ src => {[ dst ]} ∪ regs_of_argument src
  | Auipcc dst _ => {[ dst ]}
  | _ => ∅
  end.

(** The registers whose resources an instruction needs: its operands but
    [cnull], which reads as 0 and drops writes. *)
Definition regs_of (i: instr): gset RegName := operands_of i ∖ {[ cnull ]}.

(** Every operand has a word: an owned one, or [cnull]'s. *)
Lemma indom_lregs_incl D (regs regs': LReg) :
  D ∖ {[ cnull ]} ⊆ dom regs →
  regs ⊆ regs' →
  ∀ r, r ∈ D →
       ∃ (w:LWord), (regs !!ₗ r = Some w) ∧ (regs' !!ₗ r = Some w).
Proof.
  intros * HD Hincl rr Hr.
  destruct (llookup_reg_of_dom _ _ _ HD Hr) as [w Hw].
  exists w. split; auto. eapply llookup_reg_weaken; eauto.
Qed.

(** A register of [D] is [cnull] or owned. *)
Lemma elem_of_lregs_dom D (regs : LReg) r :
  D ∖ {[ cnull ]} ⊆ dom regs → r ∈ D → r = cnull ∨ r ∈ dom regs.
Proof.
  intros HD Hr. destruct (decide (r = cnull)) as [->|Hne]; first by left.
  right. apply HD. set_solver.
Qed.

Definition sregs_of (i: instr): gset SRegName :=
  match i with
  | SpecialRW _ sr _ => {[ sr ]}
  | Mret => {[ mepcc ]}
  | _ => ∅
  end.

Lemma indom_sregs_incl D (sregs sregs': LSReg) :
  D ⊆ dom sregs →
  sregs ⊆ sregs' →
  ∀ sr, sr ∈ D →
       ∃ (w:LWord), (sregs !! sr = Some w) ∧ (sregs' !! sr = Some w).
Proof.
  intros * HD Hincl rr Hr.
  assert (is_Some (sregs !! rr)) as [w Hw].
  { eapply @elem_of_dom with (D := gset SRegName); first typeclasses eauto.
    eapply elem_of_subseteq; eauto. }
  exists w. split; auto. eapply lookup_weaken; eauto.
Qed.

(*--- incrementPC ---*)

(* The logical PC increment: the PC keeps its identifier. *)
Definition incrementPC_gen (lpc : LWord) (n : Z) : option LWord :=
  match lpc with
  | WCap t p g b e a @@? π =>
    match (a + n)%a with
    | Some a' => Some (WCap t p g b e a' @@? π)
    | None => None
    end
  | _ => None
  end.

Definition incrementPC (lpc : LWord) : option LWord := incrementPC_gen lpc 1.

Lemma incrementPC_gen_Some_inv lpc lpc' n :
  incrementPC_gen lpc n = Some lpc' ->
  exists t p g b e a a' π,
    lpc = WCap t p g b e a @@? π ∧
    (a + n)%a = Some a' ∧
    lpc' = WCap t p g b e a' @@? π.
Proof.
  unfold incrementPC_gen. destruct lpc as [w π].
  destruct_word w; try congruence.
  case_eq (a+n)%a; try congruence. intros ? ?. inversion 1.
  do 8 eexists. split; eauto.
Qed.
Lemma incrementPC_Some_inv lpc lpc' :
  incrementPC lpc = Some lpc' ->
  exists t p g b e a a' π,
    lpc = WCap t p g b e a @@? π ∧
    (a + 1)%a = Some a' ∧
    lpc' = WCap t p g b e a' @@? π.
Proof. apply incrementPC_gen_Some_inv. Qed.

Lemma incrementPC_gen_None_inv lpc (t : bool) p g b e a π n :
  incrementPC_gen lpc n = None ->
  lpc = WCap t p g b e a @@? π ->
  (a + n)%a = None.
Proof.
  unfold incrementPC_gen. intros Hi ->.
  destruct (a+n)%a; congruence.
Qed.
Lemma incrementPC_None_inv lpc (t : bool) p g b e a π :
  incrementPC lpc = None ->
  lpc = WCap t p g b e a @@? π ->
  (a + 1)%a = None.
Proof. apply incrementPC_gen_None_inv. Qed.

Lemma incrementPC_add (t : bool) p g b e a a' π :
  (a + 1)%a = Some a' →
  incrementPC (WCap t p g b e a @@? π) = Some (WCap t p g b e a' @@? π).
Proof. intros Ha. by rewrite /incrementPC /incrementPC_gen /= Ha. Qed.

Lemma incrementPC_gen_add (t : bool) p g b e a a' π z :
  (a + z)%a = Some a' →
  incrementPC_gen (WCap t p g b e a @@? π) z = Some (WCap t p g b e a' @@? π).
Proof. intros Ha. by rewrite /incrementPC_gen /= Ha. Qed.

Ltac incrementPC_inv :=
  match goal with
  | H : incrementPC _ = Some _ |- _ =>
    apply incrementPC_Some_inv in H as (?&?&?&?&?&?&?&?&?&?&?)
  | H : incrementPC _ = None |- _ =>
    eapply incrementPC_None_inv in H; [|reflexivity]
  end; simplify_lmap_eq.

Tactic Notation "incrementPC_inv" "as" simple_intropattern(pat):=
  match goal with
  | H : incrementPC _ = Some _ |- _ =>
    apply incrementPC_Some_inv in H as pat
  | H : incrementPC _ = None |- _ =>
    eapply incrementPC_None_inv in H; [|reflexivity]
  | H : incrementPC_gen _ _ = Some _ |- _ =>
    apply incrementPC_gen_Some_inv in H as pat
  | H : incrementPC_gen _ _ = None |- _ =>
    eapply incrementPC_gen_None_inv in H; [|reflexivity]
  end; simplify_lmap_eq.

Section logical_lookups.
  Context `{MP : MachineParameters}.

  (** A register read: the physical word is a copy of the logical one. *)
  Lemma llookup_reg_phys R (regs : LReg) (r : Reg) x (v : LWord) :
    lregs_phys R regs r → regs !!ₗ x = Some v →
    ∃ s, lookup_reg x r = Some (and_tag s v.(lw)) ∧ reg_phys R v (and_tag s v.(lw)).
  Proof.
    intros Hincl Hx. rewrite /llookup_reg in Hx. rewrite /lookup_reg.
    case_decide; simplify_eq.
    - exists true. split; first done. apply reg_phys_lnull.
    - destruct (Hincl x v Hx) as (w & Hw & Hrel). rewrite Hw.
      destruct (reg_phys_and_tag _ _ _ Hrel) as [s ->]. by exists s.
  Qed.

  (** Integer reads are exact. *)
  Lemma llookup_reg_phys_int R (regs : LReg) (r : Reg) x z π :
    lregs_phys R regs r → regs !!ₗ x = Some (MkLWord (WInt z) π) → lookup_reg x r = Some (WInt z).
  Proof. intros Hincl Hx. by destruct (llookup_reg_phys _ _ _ _ _ Hincl Hx) as (s & -> & _). Qed.

  Lemma lz_of_argument_incl R (regs : LReg) (r : Reg) arg z :
    lregs_phys R regs r → lz_of_argument regs arg = Some z → z_of_argument r arg = Some z.
  Proof.
    intros Hincl Hz. destruct arg as [z'|x]; cbn in *; first done.
    destruct (regs !!ₗ x) as [v|] eqn:Hx; last done. simplify_eq.
    destruct (llookup_reg_phys _ _ _ _ _ Hincl Hx) as (s & -> & _).
    by rewrite /= get_a_and_tag.
  Qed.

  (** An operand register is [cnull] or owned. *)
  Definition arg_owned (regs : LReg) (arg : Z + RegName) : Prop :=
    ∀ x, arg = inr x → x ≠ cnull → x ∈ dom regs.

  Lemma arg_owned_of_dom D (regs : LReg) arg :
    D ∖ {[ cnull ]} ⊆ dom regs → regs_of_argument arg ⊆ D → arg_owned regs arg.
  Proof. intros HD Harg x -> Hx. apply HD. rewrite /regs_of_argument in Harg. set_solver. Qed.

  Lemma lz_of_argument_None R (regs : LReg) (r : Reg) arg :
    lregs_phys R regs r → arg_owned regs arg →
    lz_of_argument regs arg = None → z_of_argument r arg = None.
  Proof.
    intros Hincl Hdom Hz. destruct arg as [z|x]; cbn in *; first done.
    destruct (regs !!ₗ x) as [v|] eqn:Hx.
    - done.
    - exfalso. rewrite /llookup_reg in Hx. case_decide as Hne; first done.
      apply not_elem_of_dom in Hx. by apply Hx, Hdom.
  Qed.

  (** An operand whose register is in the map has an integer view. *)
  Lemma lz_of_argument_dom (regs : LReg) arg :
    arg_owned regs arg → is_Some (lz_of_argument regs arg).
  Proof.
    intros Hdom. apply lz_of_argument_is_Some. intros x ->.
    apply is_Some_llookup_reg. destruct (decide (x = cnull)) as [->|Hne]; first by left.
    right. by apply elem_of_dom, Hdom.
  Qed.

  (** The integer of a register holding the integer 0, [cnull] included. *)
  Lemma lz_of_argument_singleton_zero r π :
    lz_of_argument {[r := WInt 0 @@? π]} (inr r) = Some 0%Z.
  Proof.
    rewrite /lz_of_argument /llookup_reg lookup_singleton_eq /=.
    by case_decide.
  Qed.

  Lemma lz_of_argument_phys R (regs : LReg) (r : Reg) arg :
    lregs_phys R regs r →
    arg_owned regs arg →
    z_of_argument r arg = lz_of_argument regs arg.
  Proof.
    intros Hincl Hdom. destruct (lz_of_argument regs arg) eqn:Hz.
    - by eapply lz_of_argument_incl.
    - by eapply lz_of_argument_None.
  Qed.

  (** A word argument: a register read, or an exact integer. *)
  Lemma lword_of_argument_phys R (regs : LReg) (r : Reg) arg (v : LWord) :
    lregs_phys R regs r → lword_of_argument regs arg = Some v →
    ∃ s, word_of_argument r arg = Some (and_tag s v.(lw)) ∧ reg_phys R v (and_tag s v.(lw)).
  Proof.
    intros Hincl Hv. destruct arg as [z|x]; cbn in Hv.
    - simplify_eq. exists true. split; first done. apply reg_phys_lword_of_word.
    - by eapply llookup_reg_phys.
  Qed.

  Lemma llookup_reg_cap (regs : LReg) r t p g b e a :
    lw <$> regs !!ₗ r = Some (WCap t p g b e a) →
    r ≠ cnull ∧ ∃ π, regs !! r = Some (WCap t p g b e a @@? π).
  Proof.
    intros H. unfold llookup_reg in H.
    case_decide as Hne; first done.
    destruct (regs !! r) as [ [w π]|] eqn:Hr; cbn in H; simplify_eq.
    split; first done. by exists π.
  Qed.

  (** The identifier of the word read from a register, if it is a
      capability; like [read_reg_inr] for its other fields. *)
  Definition read_reg_prov (regs : LReg) (r : RegName) (π : option AId) : Prop :=
    match regs !! r with
    | Some (WCap _ _ _ _ _ _ @@? π') => π' = π
    | _ => True
    end.

  Lemma read_reg_prov_cap (regs : LReg) r p g b e a π :
    lw <$> regs !!ₗ r = Some (Cap p g b e a) →
    read_reg_prov regs r π →
    regs !! r = Some (Cap p g b e a @@? π).
  Proof.
    intros Hinr Hπ.
    destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hinr) as (_ & π' & Hr).
    rewrite /read_reg_prov Hr in Hπ. by subst π'.
  Qed.

End logical_lookups.

Section erasure_PC.
  Context `{MP : MachineParameters}.

  (* The PC increment on a copy of the PC gives the same copy of the
     incremented PC. *)
  Lemma incrementPC_gen_phys R (lpc lpc' : LWord) pc (r : Reg) sr m st n :
    reg_phys R lpc pc →
    incrementPC_gen lpc n = Some lpc' →
    ∃ pc', advancePC (pc, r, sr, m, st) n = Some (NextI, (pc', r, sr, m, st)) ∧
           reg_phys R lpc' pc'.
  Proof.
    intros Hpc Hi.
    apply incrementPC_gen_Some_inv in Hi as (t & p & g & b & e & a & a' & π & -> & Ha' & ->).
    destruct (reg_phys_and_tag _ _ _ Hpc) as [s ->].
    exists (and_tag s (WCap t p g b e a')). split.
    - rewrite /advancePC /update_pcc /= Ha'. done.
    - by apply (reg_phys_derive _ (WCap t p g b e a @@? π)).
  Qed.

  Lemma incrementPC_gen_phys_fail R (lpc : LWord) pc (r : Reg) sr m st n :
    reg_phys R lpc pc →
    incrementPC_gen lpc n = None →
    advancePC (pc, r, sr, m, st) n = None.
  Proof.
    intros Hpc Hi. destruct (reg_phys_and_tag _ _ _ Hpc) as [s ->].
    rewrite /incrementPC_gen in Hi. rewrite /advancePC /=.
    destruct lpc as [w π]; cbn in *.
    destruct w as [| [? ? ? ? ? a' | ] | |]; cbn; auto.
    destruct (a' + n)%a; auto. congruence.
  Qed.

  (* The PC increment keeps erasure: the incremented PC keeps the bounds, the
     tag and the identifier of the PC. *)
  Lemma erasure_incrementPC_gen R C (pc : Word) (r : Reg) sr m st lpc lpc' (lreg : LReg) lsreg lmem n :
    erasure R C (pc, r, sr, m, st) lpc lreg lsreg lmem →
    incrementPC_gen lpc n = Some lpc' →
    ∃ pc', advancePC (pc, r, sr, m, st) n = Some (NextI, (pc', r, sr, m, st)) ∧
           erasure R C (pc', r, sr, m, st) lpc' lreg lsreg lmem.
  Proof.
    intros Her Hi.
    destruct (incrementPC_gen_phys _ _ _ _ r sr m st _ (er_pc _ _ _ _ _ _ _ Her) Hi)
      as (pc' & Hu & Hpc').
    exists pc'. split; first done.
    apply incrementPC_gen_Some_inv in Hi as (t & p & g & b & e & a & a' & π & -> & Ha' & ->).
    destruct Her as [Hreg Hregs Hcnull Hrw Hsrw Hdom Hmw Hmmio Hpc Hpcw Hpcok].
    constructor; cbn in *; try done.
  Qed.

  Lemma erasure_incrementPC R C (pc : Word) (r : Reg) sr m st lpc lpc' (lreg : LReg) lsreg lmem :
    erasure R C (pc, r, sr, m, st) lpc lreg lsreg lmem →
    incrementPC lpc = Some lpc' →
    ∃ pc', nextPC (pc, r, sr, m, st) = Some (NextI, (pc', r, sr, m, st)) ∧
           erasure R C (pc', r, sr, m, st) lpc' lreg lsreg lmem.
  Proof. apply erasure_incrementPC_gen. Qed.

  Lemma erasure_incrementPC_fail R C (pc : Word) (r : Reg) sr m st lpc (lreg : LReg) lsreg lmem n :
    erasure R C (pc, r, sr, m, st) lpc lreg lsreg lmem →
    incrementPC_gen lpc n = None →
    advancePC (pc, r, sr, m, st) n = None.
  Proof. intros Her. apply incrementPC_gen_phys_fail with R, Her. Qed.
End erasure_PC.

(** ** Dereference witnesses

    A Load source, a Store destination or a GetTag source is read exactly
    while its identifier is live: the witness is a status share of the
    identifier, or the absence of an identifier. *)
Inductive deref_witness := DerefNoId | DerefLive (ι : AId) (q : Qp).

Definition deref_id (dw : deref_witness) : option AId :=
  match dw with DerefNoId => None | DerefLive ι _ => Some ι end.

(** The witness for an identifier [π], with share [q] if [π] is some. *)
Definition deref_witness_of (π : option AId) (q : Qp) : deref_witness :=
  match π with None => DerefNoId | Some ι => DerefLive ι q end.

Lemma deref_id_witness_of π q : deref_id (deref_witness_of π q) = π.
Proof. by destruct π. Qed.

(** The share of a witness, [1] without an identifier. *)
Definition deref_share (dw : deref_witness) : Qp :=
  match dw with DerefNoId => 1%Qp | DerefLive _ q => q end.

Section deref_witness.
  Context `{MP : MachineParameters} `{ceriseg : ceriseG Σ}.

  Definition deref_witness_res (dw : deref_witness) : iProp Σ :=
    match dw with
    | DerefNoId => emp
    | DerefLive ι q => ι ↦st{q} ALive
    end%I.

  #[global] Instance deref_witness_res_timeless dw : Timeless (deref_witness_res dw).
  Proof. destruct dw; apply _. Qed.

  (** The dereference resource of a capability with identifier [π]:
      nothing without an identifier, a share [q] of a live status
      otherwise. The share [q] is irrelevant when [π] is [None]. *)
  Definition deref_res (π : option AId) (q : Qp) : iProp Σ :=
    match π with
    | None => emp
    | Some ι => ι ↦st{q} ALive
    end%I.

  #[global] Instance deref_res_timeless π q : Timeless (deref_res π q).
  Proof. destruct π; apply _. Qed.

  (* Kept folded by instance search, so that [deref_res None q] is not taken
     for [emp] before its share is determined. *)
  #[global] Typeclasses Opaque deref_res.

  Lemma deref_res_witness π q :
    deref_res π q = deref_witness_res (deref_witness_of π q).
  Proof. by destruct π. Qed.

  (** The resource of an identifier-less capability, with share [1]. *)
  Lemma deref_res_none : ⊢ deref_res None 1.
  Proof. done. Qed.

  (** A witness is the dereference resource of its identifier. *)
  Lemma deref_witness_res_deref_res dw :
    deref_witness_res dw = deref_res (deref_id dw) (deref_share dw).
  Proof. by destruct dw. Qed.

  Definition deref_witness_ok (R : RegState) (dw : deref_witness) : Prop :=
    match dw with
    | DerefNoId => True
    | DerefLive ι _ => ∃ x, R !! ι = Some x ∧ re_status x = ALive
    end.

  Lemma deref_witness_lookup R dw :
    reg_auth R -∗ deref_witness_res dw -∗ ⌜deref_witness_ok R dw⌝.
  Proof.
    iIntros "HR Hw". destruct dw as [|ι q]; cbn; first done.
    iDestruct (reg_lookup_own with "HR Hw") as %(b & e & γ & HRι).
    iPureIntro. eexists. split; first done. done.
  Qed.

  Lemma deref_witness_not_stale R dw (v : LWord) :
    deref_witness_ok R dw → v.(lprov) = deref_id dw → ¬ stale_id R v.
  Proof.
    intros Hok Hπ (ι & x & Hι & Hx & Hs). destruct dw as [|ι' q]; cbn in *; first congruence.
    destruct Hok as (x' & Hx' & Hs'). simplify_eq; congruence.
  Qed.

  (** A word read under its witness is exact. *)
  Lemma deref_exact R dw (v : LWord) w :
    deref_witness_ok R dw → v.(lprov) = deref_id dw → load_exact_cond v →
    reg_phys R v w → w = v.(lw).
  Proof.
    intros Hok Hπ Hcond Hw. eapply reg_phys_exact_cond; eauto.
    by eapply deref_witness_not_stale.
  Qed.

  (** A tagged word with non-empty bounds has authority or no heap base. *)
  Lemma nonempty_exact_cond (v : LWord) b e :
    memory_cap_bounds v.(lw) = Some (b, e) → (b < e)%a → load_exact_cond v.
  Proof.
    intros Hb Hlt Ht. destruct (is_heap_address b) eqn:Hh.
    - left. split; first done. exists b. apply heap_authority_base_memory_cap_bounds. eauto.
    - right. by rewrite /heap_cap_base memory_cap_base_bounds Hb /= Hh.
  Qed.
End deref_witness.

Lemma reg_phys_derive_eq `{MachineParameters} R (v : LWord) s w' w'' :
  reg_phys R v (and_tag s v.(lw)) →
  memory_cap_bounds w' = memory_cap_bounds v.(lw) →
  (get_tag w' = true → get_tag v.(lw) = true) →
  and_tag s w' = w'' →
  reg_phys R (MkLWord w' v.(lprov)) w''.
Proof. intros ? ? ? <-. by apply reg_phys_derive. Qed.

(** Splits the register map of a post after the write of one register, as
    [iRegsMap]. *)
Ltac iRegsMapWrite H :=
  rewrite ?linsert_reg_cnull ?linsert_reg_not_cnull // ?insert_insert_eq ?insert_singleton;
  iRegsMap H.

Lemma lregs_phys_lookup `{MachineParameters} R (regs : LReg) (r : Reg) x (v : LWord) :
  lregs_phys R regs r → regs !! x = Some v → ∃ s, r !! x = Some (and_tag s v.(lw)).
Proof.
  intros Hincl Hv. destruct (Hincl x v Hv) as (w & Hw & Hrel).
  destruct (reg_phys_and_tag _ _ _ Hrel) as [s ->]. by exists s.
Qed.

