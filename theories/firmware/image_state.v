From stdpp Require Import gmap strings proof_irrel.
From griotte Require Import machine_base griotte_opsem.
From griotte Require Import switcher assert allocator_resources compartment_layout.
From griotte Require Import image firmware firmware_ok.

#[local] Open Scope string_scope.

(** * The initial state of an image, and checks for concrete instances

    [img_state fw img] is the machine state the loader builds for the
    firmware [fw] laid out as [img]. It is not trusted: it is used to show,
    by computation, that concrete images satisfy a predicate. The checks
    below decide the conditions of [firmware_ok] on concrete images. *)

(** ** The loader *)

Section img_state.
  Context `{MP : MachineParameters}.

  (** The PC of the start: the switcher's call of the scheduler. *)
  Definition img_pc (img : fw_image) : Word :=
    let sw := img_sw img in
    Cap XSRW_ Local (b_switcher sw) (e_switcher sw)
      (a_switcher_call sw ^+
         assembler.Asm_Griotte.label_offset_from (concat switcher_asm)
           ".Lswitch_csp_check" ".Lexception_scheduler_cjalr")%a.

  (** The registers of the start: the scheduler's three words in [cra],
      [cgp] and [csp], the idle thread's handle in [ca0], and every other
      register zero. *)
  Definition img_regs (fw : firmware) (img : fw_image) : Reg :=
    <[cra := sched_pcc_word fw img]>
      (<[cgp := sched_cgp_word fw img]>
         (<[csp := sched_csp_word img]>
            (<[ca0 := thread_handle fw img (length (fw_threads fw))]>
               (gset_to_gmap (WInt 0) all_registers_s)))).

  Definition img_sregs (img : fw_image) : SReg :=
    let sw := img_sw img in
    <[mtdc := WInt 0]>
      (<[mstatus := WInt (mstatus_enc InterruptDisabled InterruptEnabled)]>
         (<[mtcc := Cap XSRW_ Local (b_switcher sw) (e_switcher sw)
                      (a_switcher_call sw ^+
                         assembler.Asm_Griotte.label_offset_from (concat switcher_asm)
                           ".Lswitch_csp_check" "exception_entry_asm")%a]>
            (<[mepcc := WInt 0]>
               (<[mcause := WInt 0]> (<[mtval := WInt 0]> ∅))))).

  (** The memory, built in another order than in [firmware_ok], with the
      memory of every thread, of the idle thread and of the boot stack. *)
  Definition img_mem (fw : firmware) (img : fw_image) : Mem :=
    boot_mem img ∪ idle_mem img ∪
    foldr (λ '(i, ft) acc, thread_mem fw img i ft ∪ acc) ∅
      (zip (seq 0 (length (fw_threads fw))) (fw_threads fw)) ∪
    foldr (λ fc acc, cmpt_mem img fc ∪ acc) ∅ (fw_cmpts fw) ∪
    assert_flag_mem img ∪ assert_code_mem img ∪ switcher_mem fw img ∪
    initial_heap_memory.

  Definition img_state (fw : firmware) (img : fw_image) : ExecConf :=
    {| pcc := img_pc img;
       reg := img_regs fw img;
       sreg := img_sregs img;
       mem := img_mem fw img;
       shadowtbl := initial_heap_shadow;
       timedevs := {| td_mtime := 0; td_mtimecmp := 0 |} |}.
End img_state.

(** ** Canonical words

    Addresses computed by [^+] carry opaque proofs, so closed words are not
    convertible to hand-written ones. [canon_finz] rebuilds every address
    with [eq_refl] proofs; [canon_finz a = a] by proof irrelevance on
    [bool] equalities (no axiom). *)

Definition canon_true {b : bool} : b = true → b = true :=
  match b as b' return b' = true → b' = true with
  | true => λ _, eq_refl
  | false => λ H, H
  end.

Definition canon_finz {n} (a : finz n) : finz n :=
  match a with finz.FinZ z H1 H2 => finz.FinZ z (canon_true H1) (canon_true H2) end.

Lemma canon_finz_id {n} (a : finz n) : canon_finz a = a.
Proof. destruct a as [z H1 H2]. cbn. f_equal; apply proof_irrel. Qed.

Definition canon_sealable (sb : Sealable) : Sealable :=
  match sb with
  | SCap t p g b e a => SCap t p g (canon_finz b) (canon_finz e) (canon_finz a)
  | SSealRange t p g b e a => SSealRange t p g (canon_finz b) (canon_finz e) (canon_finz a)
  end.

Definition canon_word (w : Word) : Word :=
  match w with
  | WInt z => WInt z
  | WSealable sb => WSealable (canon_sealable sb)
  | WSentry k t p g b e a => WSentry k t p g (canon_finz b) (canon_finz e) (canon_finz a)
  | WSealed o sb => WSealed (canon_finz o) (canon_sealable sb)
  end.

Lemma canon_word_id w : canon_word w = w.
Proof. destruct w as [| [] | |o [] ]; cbn; rewrite ?canon_finz_id; done. Qed.

Lemma canon_word_eq (w1 w2 : Word) : canon_word w1 = canon_word w2 → w1 = w2.
Proof. by rewrite !canon_word_id. Qed.

Lemma canon_words_eq (ws1 ws2 : list Word) :
  canon_word <$> ws1 = canon_word <$> ws2 → ws1 = ws2.
Proof.
  intros Heq.
  rewrite -(list_fmap_id ws1) -(list_fmap_id ws2).
  rewrite -!(list_fmap_ext canon_word id) //; intros; apply canon_word_id.
Qed.

Lemma canon_optword_eq (w1 w2 : option Word) :
  canon_word <$> w1 = canon_word <$> w2 → w1 = w2.
Proof.
  destruct w1, w2; cbn; intros Heq; try done.
  injection Heq as Heq. rewrite !canon_word_id in Heq. by subst.
Qed.

(** [vm_compute] of a [gmap Addr _] itself blows up (memory); compare the
    canonical association lists instead. *)
Definition canon_kv (aw : Addr * Word) : Addr * Word :=
  (canon_finz aw.1, canon_word aw.2).

Lemma canon_mem_eq (m1 m2 : Mem) :
  canon_kv <$> map_to_list m1 = canon_kv <$> map_to_list m2 → m1 = m2.
Proof.
  intros Heq. apply map_to_list_inj.
  assert (∀ l : list (Addr * Word), canon_kv <$> l = l) as Hid.
  { intros l. rewrite -{2}(list_fmap_id l). apply list_fmap_ext.
    intros _ [a w] _. by rewrite /canon_kv /= canon_finz_id canon_word_id. }
  by rewrite -(Hid (map_to_list m1)) -(Hid (map_to_list m2)) Heq.
Qed.

(** ** Decision procedures for the layout conditions *)

Lemma Forall_check {A} (f : A → bool) (P : A → Prop) (l : list A) :
  (∀ x, f x = true → P x) → forallb f l = true → Forall P l.
Proof.
  intros Hf. induction l as [|x l IH]; cbn; first by constructor.
  intros [Hx Hl]%andb_true_iff. constructor; [by apply Hf | by apply IH].
Qed.

Lemma forallb_elem {A} (f : A → bool) (l : list A) x :
  forallb f l = true → x ∈ l → f x = true.
Proof.
  induction l as [|y l IH]; cbn; intros Hl Hx.
  - by apply not_elem_of_nil in Hx.
  - apply andb_true_iff in Hl as [Hy Hl].
    apply elem_of_cons in Hx as [->|Hx]; [done | by apply IH].
Qed.

(** $[b, e)$ and $[lo, hi)$ are apart. *)
Definition range_apart (b e lo hi : Addr) : bool :=
  bool_decide (e <= lo)%a || bool_decide (hi <= b)%a.

Lemma range_apart_disjoint b e lo hi :
  range_apart b e lo hi = true →
  finz.seq_between b e ## finz.seq_between lo hi.
Proof.
  intros Hap x Hx Hy.
  rewrite !elem_of_finz_seq_between in Hx, Hy.
  apply orb_true_iff in Hap as [Hap|Hap]; apply bool_decide_eq_true in Hap; solve_addr.
Qed.

Section checks.
  Context `{MP : MachineParameters}.

  (** The closed range [[b, e]] and [b] avoid the heap. *)
  Definition closed_outside_heap (b e : Addr) : bool :=
    (bool_decide (b < heap_b)%a && bool_decide (e < heap_b)%a) || bool_decide (heap_e <= b)%a.

  Lemma closed_outside_heap_spec b e y :
    closed_outside_heap b e = true →
    y = b ∨ ((b <= y)%a ∧ (y <= e)%a) →
    is_heap_address y = false.
  Proof.
    intros Hout Hy. rewrite /is_heap_address.
    apply not_true_is_false. intros Hw. apply withinBounds_true_iff in Hw.
    apply orb_true_iff in Hout as [Hout|Hout].
    - apply andb_true_iff in Hout as [Hb He].
      apply bool_decide_eq_true in Hb, He. destruct Hy as [->|Hy]; solve_addr.
    - apply bool_decide_eq_true in Hout. destruct Hy as [->|Hy]; solve_addr.
  Qed.

  Lemma not_heap_range_check b e :
    closed_outside_heap b e = true → not_heap_range b e.
  Proof.
    intros Hout. split.
    - apply (closed_outside_heap_spec b e b Hout). by left.
    - intros x Hx Hy.
      rewrite !elem_of_finz_seq_between in Hx, Hy.
      assert (is_heap_address x = false) as Hn.
      { apply (closed_outside_heap_spec b e x Hout). right. solve_addr. }
      rewrite /is_heap_address in Hn.
      assert (withinBounds heap_b heap_e x = true) as Hw by by apply withinBounds_true_iff.
      congruence.
  Qed.

  (** The address [a] is outside [b, e). *)
  Definition addr_apart (a b e : Addr) : bool :=
    bool_decide (a < b)%a || bool_decide (e <= a)%a.

  Lemma addr_apart_not_in a b e :
    addr_apart a b e = true → a ∉ finz.seq_between b e.
  Proof.
    rewrite elem_of_finz_seq_between.
    intros [Ha|Ha]%orb_true_iff; apply bool_decide_eq_true in Ha; solve_addr.
  Qed.

  Definition mmio_apart (b e : Addr) : bool :=
    range_apart b e shadow_b shadow_e &&
    addr_apart revoker_addr b e &&
    addr_apart mtime_addr b e &&
    addr_apart mtimecmp_addr b e.

  Lemma disjoint_from_mmio_check b e :
    mmio_apart b e = true → disjoint_from_mmio b e.
  Proof.
    intros [ [ [Hsh Hrev]%andb_true_iff Hmtime]%andb_true_iff Hmtimecmp]%andb_true_iff.
    rewrite /disjoint_from_mmio /disjoint_from_time_devs. split_and!.
    - by apply range_apart_disjoint.
    - by apply addr_apart_not_in.
    - by apply addr_apart_not_in.
    - by apply addr_apart_not_in.
  Qed.

  (** A word that is not executable, or whose bounds are outside the heap. *)
  Definition word_exec_okb (w : Word) : bool :=
    if executable_word w then
      match memory_cap_bounds w with
      | Some (b, e) => closed_outside_heap b e
      | None => true
      end
    else true.

  Lemma word_exec_okb_sound w : word_exec_okb w = true → word_exec_ok w.
  Proof.
    rewrite /word_exec_okb /word_exec_ok /erasure.lword_exec /lword_of_word /=.
    intros Hw _ Hx. rewrite Hx in Hw. split; first done.
    intros b e Hbe. rewrite Hbe in Hw. split.
    - apply (closed_outside_heap_spec b e b Hw). by left.
    - intros y Hy. apply (closed_outside_heap_spec b e y Hw). by right.
  Qed.

  (** A word without heap authority, or with heap authority based at one of
      the heap roots [H]. *)
  Definition word_rootedb (H : gset Addr) (w : Word) : bool :=
    match heap_authority_base w with
    | None => true
    | Some b => bool_decide (b ∈ H)
    end.

  Lemma word_rootedb_sound H w : word_rootedb H w = true → word_rooted H w.
  Proof.
    rewrite /word_rootedb. intros Hw b _ Hb. rewrite Hb in Hw.
    by apply bool_decide_eq_true in Hw.
  Qed.

  (** A global of the scheduler that is an integer or a thread handle. *)
  Definition sched_data_wordb (hs : list Word) (w : Word) : bool :=
    is_z w || bool_decide (w ∈ hs).

  Lemma sched_data_wordb_sound b e hs w :
    sched_data_wordb hs w = true → sched_data_word b e hs w.
  Proof.
    intros [Hz|Hw]%orb_true_iff.
    - left. left. by rewrite Hz.
    - right. by apply bool_decide_eq_true in Hw.
  Qed.

  (** A word of the boot stack that is an integer or a thread handle: the
      same test as [sched_data_wordb], for another predicate of the image. *)
  Definition boot_stack_wordb (hs : list Word) (w : Word) : bool :=
    is_z w || bool_decide (w ∈ hs).

  Lemma boot_stack_wordb_sound hs w :
    boot_stack_wordb hs w = true → boot_stack_word hs w.
  Proof.
    intros [Hz|Hw]%orb_true_iff.
    - left. by rewrite /is_int Hz.
    - right. by apply bool_decide_eq_true in Hw.
  Qed.
End checks.

Fixpoint ranges_apart (rs : list (Addr * Addr)) : bool :=
  match rs with
  | [] => true
  | r :: rs => forallb (λ r', range_apart r.1 r.2 r'.1 r'.2) rs && ranges_apart rs
  end.

Lemma ranges_apart_sound rs : ranges_apart rs = true → ranges_disjoint rs.
Proof.
  rewrite /ranges_disjoint.
  induction rs as [|[b e] rs IH]; cbn; intros Hrs.
  - constructor.
  - apply andb_true_iff in Hrs as [Hall Hrs].
    apply disjoint_list_cons. split; last by apply IH.
    intros x Hx Hy.
    apply elem_of_union_list in Hy as (X & HX & Hy).
    apply list_elem_of_fmap in HX as ([b' e'] & -> & Hin).
    pose proof (forallb_elem _ _ _ Hall Hin) as Hap; cbn in Hap.
    by apply (range_apart_disjoint b e b' e' Hap x).
Qed.

(** ** The tactic for concrete instances

    Solves one condition of an erased predicate on a concrete image and
    state, by computation. *)
Ltac solve_concrete_condition :=
  lazymatch goal with
  | |- @eq Mem _ _ => apply canon_mem_eq; vm_compute; reflexivity
  | |- @eq (list Word) _ _ => apply canon_words_eq; vm_compute; reflexivity
  | |- @eq Word _ _ => apply canon_word_eq; vm_compute; reflexivity
  | |- @eq (option Word) _ _ => apply canon_optword_eq; vm_compute; reflexivity
  | |- @eq ShadowTbl _ _ => reflexivity
  | |- Forall is_int _ =>
      apply (Forall_check is_z); [intros ? Hz; by rewrite /is_int Hz | vm_compute; reflexivity]
  | |- Forall (initial_data_word _ _) _ =>
      apply (Forall_check is_z); [intros ? Hz; left; by rewrite Hz | vm_compute; reflexivity]
  | |- Forall (sched_data_word _ _ ?hs) _ =>
      apply (Forall_check (sched_data_wordb hs));
      [intros ?; apply sched_data_wordb_sound | vm_compute; reflexivity]
  | |- Forall (boot_stack_word ?hs) _ =>
      apply (Forall_check (boot_stack_wordb hs));
      [apply boot_stack_wordb_sound | vm_compute; reflexivity]
  | |- Forall (word_rooted ?H) _ =>
      apply (Forall_check (word_rootedb H)); [apply word_rootedb_sound | vm_compute; reflexivity]
  | |- Forall word_exec_ok _ =>
      apply (Forall_check word_exec_okb); [apply word_exec_okb_sound | vm_compute; reflexivity]
  | |- Forall otype_valid _ =>
      apply (Forall_check (λ o, bool_decide (otype_valid o)));
      [intros ? Ho; by apply bool_decide_eq_true in Ho | vm_compute; reflexivity]
  | |- not_heap_range _ _ => apply not_heap_range_check; vm_compute; reflexivity
  | |- disjoint_from_mmio _ _ => apply disjoint_from_mmio_check; vm_compute; reflexivity
  | |- ranges_disjoint _ => apply ranges_apart_sound; vm_compute; reflexivity
  | |- disjoint_from_shadow _ _ => apply range_apart_disjoint; vm_compute; reflexivity
  | |- _ => apply (bool_decide_unpack _); vm_compute; reflexivity
  end.
