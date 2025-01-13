From iris.algebra Require Import auth agree excl gmap frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From iris.program_logic Require Import adequacy.
Require Import Eqdep_dec.
From cap_machine Require Import
     stdpp_extra iris_extra
     logrel_binary fundamental_binary linking.
From cap_machine.binary_model Require Import
     macros_binary confidentiality region_invariants_binary_allocation.
From cap_machine.examples Require Import
     disjoint_regions_tactics.

Instance DisjointList_list_Addr : DisjointList (list Addr).
Proof. exact (@disjoint_list_default _ _ app []). Defined.

Definition mkregion (r_start r_end: Addr) (contents: list Word): gmap Addr Word :=
  list_to_map (zip (region_addrs r_start r_end) contents).

Definition mbkregion (r_start r_end: Addr) (contents: list Word) (contents_spec: list Word): gmap Addr (Word * Word) :=
  list_to_map (zip (region_addrs r_start r_end) (zip contents contents_spec)).

(* Instance segment_union : Union (segment Word). *)
(* Proof. rewrite /segment. apply _. Qed. *)

Class memory_layout `{MachineParameters} := {
  (* Code for f *)
  f_start : Addr;
  f_end : Addr;

  b_stk : Addr;
  e_stk : Addr;

  f_size :
    (f_start + (length (conf_instrs 0)))%a = Some f_end;
 }.

Definition initial_state_stk `{MachineParameters} (b_stk e_stk: Addr) (stack_init : list Word) (c: machine_component): cfg cap_lang :=
  match c with
  | Lib _ _ _ _ pre_comp => ([Seq (Instr Executable)], (∅, ∅)) (* dummy value *)
  | Main _ _ _ _ (ms, _, _) c_main => ([Seq (Instr Executable)], (<[r_stk := inr (URWLX, Directed, b_stk, e_stk, b_stk)]> (<[PC := c_main]> (gset_to_gmap (inl 0%Z) (list_to_set all_registers))), (ms : Mem) ∪ (mkregion b_stk e_stk stack_init)))
  end.

Definition comp1 `{memory_layout} : machine_component :=
  Lib _ _ _ _ (mkregion f_start f_end (conf_instrs 2), ∅, {[ 0 := inr (E,Global,f_start,f_end,f_start) ]}).

Definition comp2 `{memory_layout} : machine_component :=
  Lib _ _ _ _ (mkregion f_start f_end (conf_instrs 3), ∅, {[ 0 := inr (E,Global,f_start,f_end,f_start) ]}).

Definition code_all_ints (ms : segment Word) :=
  ∀ a w, ms !! a = Some w → is_cap w = false.

Definition is_initial_context (c : machine_component) :=
  match c with
  | Lib _ _ _ _ (pre_ms,_,_) => code_all_ints pre_ms
  | Main _ _ _ _ (pre_ms,i,e) c_main => code_all_ints pre_ms ∧ (∃ p g b e a, c_main = inr (p,g,b,e,a) ∧
                                                                   (p = RX ∨ p = RWX))
                                       ∧ (∃ a, {[(0,a)]} = i) ∧ e = ∅
  (* extra assumptions on adv imports and exports that make the proof easier to go through *)
  end.

Definition is_machine_program `{memory_layout} (c : machine_component) :=
  is_program e_stk _ _ _ _ can_address_only pwlW is_global c.
Definition is_machine_context `{memory_layout} (c comp p : machine_component) :=
  is_context e_stk _ _ _ _ can_address_only pwlW is_global c comp p.

Lemma initial_registers_full_map `{MachineParameters, memory_layout} stack_init (c : machine_component) reg :
  is_machine_program c →
  (initial_state_stk b_stk e_stk stack_init c).2.1 = reg →
  (∀ r, is_Some (reg !! r)).
Proof.
  intros Hprog Hini.
  inv Hprog.
  intros r.
  destruct (decide (r = PC)) as [->|]. by eauto.
  destruct (decide (r = r_stk)) as [->|]. rewrite lookup_insert. eauto.
  rewrite lookup_insert_ne// lookup_insert_ne//.
  pose proof (all_registers_s_correct r) as Hin. clear -Hin.
  apply elem_of_gmap_dom. rewrite dom_gset_to_gmap. auto.
Qed.


Lemma dom_mkregion_incl a e l:
    dom (gset Addr) (mkregion a e l) ⊆ list_to_set (region_addrs a e).
Proof.
  rewrite /mkregion. generalize (region_addrs a e). induction l.
  { intros. rewrite zip_with_nil_r /=. rewrite dom_empty_L. apply empty_subseteq. }
  { intros ll. destruct ll as [| x ll].
    - cbn. rewrite dom_empty_L. done.
    - cbn [list_to_set zip zip_with list_to_map foldr fst snd]. rewrite dom_insert_L.
      set_solver. }
Qed.

Lemma dom_mkregion_incl_rev a e l:
  (a + length l = Some e)%a →
  list_to_set (region_addrs a e) ⊆ dom (gset Addr) (mkregion a e l).
Proof.
  rewrite /mkregion. intros Hl.
  assert (length (region_addrs a e) = length l) as Hl'.
  { rewrite region_addrs_length /region_size. solve_addr. }
  clear Hl. revert Hl'. generalize (region_addrs a e). induction l.
  { intros. rewrite zip_with_nil_r /=. rewrite dom_empty_L.
    destruct l; [| inversion Hl']. cbn. apply empty_subseteq. }
  { intros ll Hll. destruct ll as [| x ll]; [by inversion Hll|].
    cbn [list_to_set zip zip_with list_to_map foldr fst snd].
    rewrite dom_insert_L. cbn in Hll. apply Nat.succ_inj in Hll.
    specialize (IHl ll Hll). set_solver. }
Qed.

Lemma dom_mkregion_eq a e l:
  (a + length l = Some e)%a →
  dom (gset Addr) (mkregion a e l) = list_to_set (region_addrs a e).
Proof.
  intros Hlen. apply (anti_symm _).
  - apply dom_mkregion_incl.
  - by apply dom_mkregion_incl_rev.
Qed.

Lemma in_dom_mkregion a e l k:
  k ∈ dom (gset Addr) (mkregion a e l) →
  k ∈ region_addrs a e.
Proof.
  intros H.
  pose proof (dom_mkregion_incl a e l) as HH.
  rewrite elem_of_subseteq in HH |- * => HH.
  specialize (HH _ H). eapply @elem_of_list_to_set; eauto. apply _.
Qed.

Lemma in_dom_mkregion' a e l k:
  (a + length l = Some e)%a →
  k ∈ region_addrs a e →
  k ∈ dom (gset Addr) (mkregion a e l).
Proof.
  intros. rewrite dom_mkregion_eq // elem_of_list_to_set //.
Qed.

Lemma mkregion_mbkregion_None_l a e l l' k :
  length l = length l' →
  mkregion a e l !! k = None →
  mbkregion a e l l' !! k = None.
Proof.
  generalize l' a. induction l;intros l2 a' Hlen.
  - rewrite /mbkregion zip_with_nil_r /=. auto.
  - rewrite /mkregion /mbkregion.
    simpl. destruct l2;inversion Hlen.
    destruct (decide (a' < e))%a.
    2: { rewrite region_addrs_empty. 2: solve_addr. simpl. auto. }
    rewrite region_addrs_cons. 2: solve_addr.
    assert (is_Some (a' + 1)%a) as [? ?].
    { destruct (a' + 1)%a eqn:Hsome;eauto. solve_addr. }
    simpl. rewrite H /=. rewrite /mbkregion in IHl.
    intros. destruct (decide (a' = k));[subst;rewrite lookup_insert in H1;inversion H1|].
    rewrite lookup_insert_ne// IHl//. rewrite lookup_insert_ne// in H1.
Qed.

Lemma mkregion_mbkregion_None_r a e l l' k :
  length l = length l' →
  mkregion a e l' !! k = None →
  mbkregion a e l l' !! k = None.
Proof.
  generalize l' a. induction l;intros l2 a' Hlen.
  - rewrite /mbkregion zip_with_nil_r /=. auto.
  - rewrite /mkregion /mbkregion.
    simpl. destruct l2;inversion Hlen.
    destruct (decide (a' < e))%a.
    2: { rewrite region_addrs_empty. 2: solve_addr. simpl. auto. }
    rewrite region_addrs_cons. 2: solve_addr.
    assert (is_Some (a' + 1)%a) as [? ?].
    { destruct (a' + 1)%a eqn:Hsome;eauto. solve_addr. }
    simpl. rewrite H /=. rewrite /mbkregion in IHl.
    intros. destruct (decide (a' = k));[subst;rewrite lookup_insert in H1;inversion H1|].
    rewrite lookup_insert_ne// IHl//. rewrite lookup_insert_ne// in H1.
Qed.

Lemma mkregion_mbkregion_elem_of_l a e l l' b :
  length l = length l' →
  b ∈ dom (gset Addr) (mkregion a e l) ↔
  b ∈ dom (gset Addr) (mbkregion a e l l').
Proof.
  generalize l' a. induction l;intros l2 a' Hlen.
  - rewrite /mbkregion /mkregion !zip_with_nil_r /=. auto.
  - rewrite /mkregion /mbkregion.
    simpl. destruct l2;inversion Hlen.
    destruct (decide (a' < e))%a.
    2: { rewrite region_addrs_empty. 2: solve_addr. simpl. auto. }
    rewrite region_addrs_cons. 2: solve_addr.
    assert (is_Some (a' + 1)%a) as [? ?].
    { destruct (a' + 1)%a eqn:Hsome;eauto. solve_addr. }
    simpl. rewrite H /=. rewrite /mbkregion in IHl.
    rewrite !dom_insert_L. destruct (decide (b = a'));[subst;set_solver|].
    set_solver.
Qed.
Lemma mkregion_mbkregion_elem_of_r a e l l' b :
  length l = length l' →
  b ∈ dom (gset Addr) (mkregion a e l') ↔
  b ∈ dom (gset Addr) (mbkregion a e l l').
Proof.
  generalize l' a. induction l;intros l2 a' Hlen.
  - destruct l2;inversion Hlen. rewrite /mbkregion /mkregion !zip_with_nil_r /=. auto.
  - rewrite /mkregion /mbkregion.
    simpl. destruct l2;inversion Hlen.
    destruct (decide (a' < e))%a.
    2: { rewrite region_addrs_empty. 2: solve_addr. simpl. auto. }
    rewrite region_addrs_cons. 2: solve_addr.
    assert (is_Some (a' + 1)%a) as [? ?].
    { destruct (a' + 1)%a eqn:Hsome;eauto. solve_addr. }
    simpl. rewrite H /=. rewrite /mbkregion in IHl.
    rewrite !dom_insert_L. destruct (decide (b = a'));[subst;set_solver|].
    set_solver.
Qed.

Definition ms_of (c : machine_component) : Mem :=
  match c with
  | Lib _ _ _ _ (ms,_,_) => ms
  | Main _ _ _ _ (ms, _, _) _ => ms
  end.

Definition main_of (c : machine_component) : Word :=
  match c with
  | Lib _ _ _ _ (_,_,_) => inl 0%Z
  | Main _ _ _ _ (_,_,_) c_main => c_main
  end.

Instance merge_diagnone : DiagNone (λ o1 o2 : option Word, match o1 with
                                  | Some _ => o1
                                  | None => o2
                                                           end).
Proof.
  rewrite /DiagNone //.
Qed.

Instance merge_LeftId : LeftId eq None (λ o1 o2 : option Word, match o1 with
                                        | Some _ => o1
                                        | None => o2
                                                               end).
Proof. rewrite /LeftId //. Qed.

Lemma map_union_assoc :
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A))
    (H2 : ∀ A : Type, PartialAlter K A (M A)) (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A))
    (EqDecision0 : EqDecision K), FinMap K M → ∀ (A : Type) (m1 m2 m3 : M A), m1 ∪ m2 ∪ m3 = m1 ∪ (m2 ∪ m3).
Proof.
  intros. induction m1 using map_ind.
  - rewrite !fin_maps.LeftId_instance_2 //.
  - rewrite -!insert_union_l IHm1. auto.
Qed.

Instance list_addr_semiset : SemiSet Addr (list Addr).
Proof.
  apply Build_SemiSet.
  - intros. intros Hcontr. inversion Hcontr.
  - intros. split;intros.
    inversion H;subst;auto. inversion H2.
    rewrite /singleton /Singleton_list. apply elem_of_list_singleton. auto.
  - intros. split;intros.
    rewrite /union /Union_list in H.
    apply elem_of_app in H. auto.
    rewrite /union /Union_list.
    apply elem_of_app. auto.
Qed.

Lemma regions_disjoint `{MachineParameters, memory_layout} stack_init stack_init' c_adv p1 p2 (mem mem' : Mem) :
  is_machine_context c_adv comp1 p1 →
  is_machine_context c_adv comp2 p2 →
  is_initial_context c_adv →
  mem = (initial_state_stk b_stk e_stk stack_init p1).2.2 →
  mem' = (initial_state_stk b_stk e_stk stack_init' p2).2.2 →
  (b_stk + length stack_init)%a = Some e_stk →
  (b_stk + length stack_init')%a = Some e_stk →

  ∃ resolved_ms, mem = (mkregion b_stk e_stk stack_init)
                         ∪ (mkregion f_start f_end (conf_instrs 2))
                         ∪ (resolved_ms)
                 ∧ mem' = (mkregion b_stk e_stk stack_init')
                         ∪ (mkregion f_start f_end (conf_instrs 3))
                         ∪ (resolved_ms)
                 ∧ can_address_only (main_of c_adv) (dom (gset Addr) (resolved_ms))
                 ∧ is_global (main_of c_adv)
  ∧ (∀ a w, resolved_ms !! a = Some w → (is_cap w = false
                                         ∨ w = inr (E,Global,f_start,f_end,f_start)))
    ∧ ## [elements (dom (gset Addr) (resolved_ms));
         region_addrs f_start f_end;
         region_addrs b_stk e_stk].
Proof.
  intros Hp1 Hp2 Hinit Hmem Hmem' Hsize Hsize'.
  subst mem mem'. rewrite /comp1 in Hp1. rewrite /comp2 in Hp2.
  inv Hp1. inv Hp2. destruct His_program as [Hlink His_program].
  destruct His_program0 as [Hlink0 His_program0].
  inv His_program. inv His_program0. inv Hlink. inv Hlink0.
  revert ms ms0 Hwfcomp Hwfcomp0 Hlink Hlink1. rewrite /segment. intros.
  inv Hwfcomp. inv Hwf_pre. inv Hwfcomp0. inv Hwf_pre. simpl in *.
  destruct Hw_main as (Hcanaddress & Hnwpl & Hglobal).
  destruct Hw_main0 as (Hcanaddress0 & Hnwpl0 & Hglobal0).
  destruct comp3,p. revert s Hinit Hlink Hlink1 Hwf_l Hwf_l0. rewrite /segment. intros.
  destruct Hinit as [Hints [Hw_main [ [a Hin] He] ] ]. subst e i.
  destruct Hw_main as (p&l&b&e&a_main&->&?).
  destruct l;try by inversion Hglobal. simpl in *.

  assert (∀ stack_init, (b_stk + length stack_init)%a = Some e_stk →
                        ms ##ₘ mkregion b_stk e_stk stack_init) as Hdisj_ms.
  { intros si Hsi. apply map_disjoint_alt. intros a'.
    destruct (ms !! a') eqn:Hsome;auto. right.
    assert (a' ∈ dom (gset Addr) ms) as Hle%Hdisjstk;[apply elem_of_gmap_dom;eauto|].
    eapply not_elem_of_list_to_map.
    rewrite fst_zip. apply not_elem_of_region_addrs;auto.
    rewrite region_addrs_length /region_size. clear -Hsize Hsi. solve_addr. }
  assert (∀ stack_init, (b_stk + length stack_init)%a = Some e_stk →
                        ms0 ##ₘ mkregion b_stk e_stk stack_init) as Hdisj_ms'.
  { intros si Hsi. apply map_disjoint_alt. intros a'.
    destruct (ms0 !! a') eqn:Hsome;auto. right.
    assert (a' ∈ dom (gset Addr) ms0) as Hle%Hdisjstk0;[apply elem_of_gmap_dom;eauto|].
    eapply not_elem_of_list_to_map.
    rewrite fst_zip. apply not_elem_of_region_addrs;auto.
    rewrite region_addrs_length /region_size. clear -Hsize Hsi. solve_addr. }

  inversion Hlink1. subst ms1 imp1 exp1 ms2 imp2 exp2 ms3 imp exp3.
  inversion Hlink. subst ms1 imp1 exp1 ms2 imp2 exp2 ms3 imp exp3.
  rewrite /resolve_imports /set_fold /= elements_empty elements_singleton /= in Hms.
  rewrite /resolve_imports /set_fold /= elements_empty elements_singleton /= in Hms0.
  assert (exp !! 0 = Some (inr (E, Global, f_start, f_end, f_start))) as Hin0.
  { rewrite Hexp1. rewrite lookup_merge lookup_empty. eauto. }
  assert (exp0 !! 0 = Some (inr (E, Global, f_start, f_end, f_start))) as Hin1.
  { rewrite Hexp2. rewrite lookup_merge lookup_empty. eauto. }
  rewrite Hin0 in Hms. subst ms.
  rewrite Hin1 in Hms0. subst ms0.
  rewrite fin_maps.LeftId_instance_0 in Hexp2. subst exp0.
  rewrite fin_maps.LeftId_instance_0 in Hexp1. subst exp. clear Hin1.
  inv Hwf_l. inv Hwf_r.
  inv Hwf_l0. inv Hwf_r0.
  inv Hwf_pre. inv Hwf_pre0. inv Hwf_pre1. inv Hwf_pre2.

  assert (<[a:=inr (E, Global, f_start, f_end, f_start)]> s ##ₘ mkregion f_start f_end (conf_instrs 2))
    as Hdisj_ms2.
  { apply map_disjoint_alt. intros a'.
    destruct ((<[a:=inr (E, Global, f_start, f_end, f_start)]> s) !! a') eqn:Hsome;auto. right.
    destruct (decide (a = a')).
    { subst a. destruct Himp3 with 0 a';[apply elem_of_singleton;auto|].
      apply eq_None_not_Some. intros Hcontr. apply Hms_disj in Hcontr;eauto. }
    rewrite lookup_insert_ne// in Hsome.
    apply eq_None_not_Some. intros Hcontr. apply Hms_disj in Hcontr;eauto. }
  assert (<[a:=inr (E, Global, f_start, f_end, f_start)]> s ##ₘ mkregion f_start f_end (conf_instrs 3))
    as Hdisj_ms3.
  { apply map_disjoint_alt. intros a'.
    destruct ((<[a:=inr (E, Global, f_start, f_end, f_start)]> s) !! a') eqn:Hsome;auto. right.
    destruct (decide (a = a')).
    { subst a. destruct Himp5 with 0 a';[apply elem_of_singleton;auto|].
      apply eq_None_not_Some. intros Hcontr. apply Hms_disj0 in Hcontr;eauto. }
    rewrite lookup_insert_ne// in Hsome.
    apply eq_None_not_Some. intros Hcontr. apply Hms_disj0 in Hcontr;eauto. }

  exists (<[a:=inr (E, Global, f_start, f_end, f_start)]> s : Mem).
  split;[|split;[|split;[|split;[|split] ] ] ].
  - rewrite map_union_comm//.
    assert (map_union s (mkregion f_start f_end (conf_instrs 2)) = (s ∪ (mkregion f_start f_end (conf_instrs 2))))
      as ->;auto.

    erewrite insert_union_l.
    (* annoying type class stuff... *)
    Unshelve. all: rewrite /segment /=; try apply _.
    5: apply gmap_finmap.
    rewrite (map_union_comm (<[_:=_]> s) (mkregion _ _ _))// -map_union_assoc //.
    apply Hdisj_ms;auto.
  - rewrite map_union_comm//.
    assert (map_union s (mkregion f_start f_end (conf_instrs 3)) = (s ∪ (mkregion f_start f_end (conf_instrs 3))))
      as ->;auto.

    erewrite insert_union_l.
    (* annoying type class stuff... *)
    Unshelve. all: rewrite /segment /=; try apply _.
    5: apply gmap_finmap.
    rewrite (map_union_comm (<[_:=_]> s) (mkregion _ _ _))// -map_union_assoc //.
    apply Hdisj_ms';auto.
  - clear -H2 Hw_main. simpl in *.
    destruct H2 as [-> | ->].
    all: destruct Hw_main as [Hw_main _].
    all: intros; rewrite dom_insert_L;set_solver.
  - auto.
  - intros. destruct (decide (a = a0)).
    + subst. rewrite lookup_insert in H3. inv H3. auto.
    + rewrite lookup_insert_ne// in H3. apply Hints in H3. auto.
  - apply addr_disjoint_list_cons.
    { simpl. rewrite union_empty_r.
      apply elem_of_disjoint. intros x [y Hx1]%elem_of_elements%elem_of_gmap_dom Hx2.
      apply elem_of_union in Hx2 as [Hx2 | Hx2%elem_of_region_addrs].
      assert (is_Some (mkregion f_start f_end (conf_instrs 2) !! x)) as [y' Hx1'].
      { apply elem_of_gmap_dom. apply in_dom_mkregion'. apply f_size. auto. }
      eapply map_disjoint_spec;[apply Hdisj_ms2|eauto..].
      destruct (decide (a = x)).
      { subst. assert (is_Some (s !! x)) as Hsome%elem_of_gmap_dom%Hdisjstk1;[|clear -Hx2 Hsome;solve_addr].
        apply Himp3 with 0. apply elem_of_singleton;auto. }
      rewrite lookup_insert_ne// in Hx1.
      assert (is_Some (s !! x)) as Hsome%elem_of_gmap_dom%Hdisjstk1;eauto.
      clear -Hx2 Hsome;solve_addr. }
    apply disjoint_list_cons. rewrite !union_list_cons /=.
    split.
    { rewrite union_empty_r.
      apply elem_of_disjoint.
      intros x Hx1 Hx2%elem_of_region_addrs.
      assert (is_Some (mkregion f_start f_end (conf_instrs 2) !! x)) as Hsome%elem_of_gmap_dom.
      { apply elem_of_gmap_dom. apply in_dom_mkregion'. apply f_size. auto. }
      apply Hdisjstk2 in Hsome. clear -Hx2 Hsome;solve_addr. }
    apply disjoint_list_cons;auto. clear. split;[|apply disjoint_nil_2].
    apply addr_range_disj_union_empty.
Qed.

Section Adequacy.
  Context (Σ: gFunctors).
  Context {inv_preg: invPreG Σ}.
  Context {mem_preg: gen_heapPreG Addr Word Σ}.
  Context {reg_preg: gen_heapPreG RegName Word Σ}.
  Context {sts_preg: STS_preG Addr region_type Σ}.
  Context {heappreg: heapPreG Σ}.
  Context {na_invg: na_invG Σ}.
  Context `{MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).

  Lemma mkregion_sepM_to_sepL2 (a e: Addr) l (φ: Addr → Word → iProp Σ) :
    (a + length l)%a = Some e →
    ([∗ map] k↦v ∈ mkregion a e l, φ k v) -∗ ([∗ list] k;v ∈ (region_addrs a e); l, φ k v).
  Proof.
    rewrite /mkregion. revert a e. induction l as [| x l].
    { cbn. intros. rewrite zip_with_nil_r /=. assert (a = e) as -> by solve_addr.
      rewrite /region_addrs region_size_0. 2: solve_addr. cbn. eauto. }
    { cbn. intros a e Hlen. rewrite region_addrs_cons. 2: solve_addr.
      cbn. iIntros "H". iDestruct (big_sepM_insert with "H") as "[? H]".
      { rewrite -not_elem_of_list_to_map /=.
        intros [ [? ?] [-> [? ?]%elem_of_zip_l%elem_of_region_addrs] ]%elem_of_list_fmap.
        solve_addr. }
      iFrame. iApply (IHl with "H"). solve_addr. }
  Qed.

  Lemma mkregion_sepM_to_sepL2_zip (a e: Addr) l l' (φ φ': Addr → Word → iProp Σ) :
    (a + length l)%a = Some e →
    (a + length l')%a = Some e →
    ([∗ map] k↦v ∈ mkregion a e l, φ k v) -∗
    ([∗ map] k↦v ∈ mkregion a e l', φ' k v) -∗
    ([∗ map] k↦v ∈ mbkregion a e l l', φ k v.1 ∗ φ' k v.2).
  Proof.
    rewrite /mkregion. revert a e l'. induction l as [| x l].
    { cbn. intros. rewrite zip_with_nil_r /=. assert (a = e) as -> by solve_addr.
      rewrite /region_addrs region_size_0. 2: solve_addr.
      rewrite /mbkregion. rewrite region_addrs_empty. 2: solve_addr.
      cbn. eauto. }
    { cbn. intros a e l' Hlen Hlen'.
      assert (length l' = S (length l)) as Hleneq.
      { solve_addr. }
      destruct l';[inversion Hleneq|]. simpl in *.
      rewrite region_addrs_cons. 2: solve_addr.
      rewrite /mbkregion /=.
      cbn. iIntros "H H'". iDestruct (big_sepM_insert with "H") as "[? H]".
      { rewrite -not_elem_of_list_to_map /=.
        intros [ [? ?] [-> [? ?]%elem_of_zip_l%elem_of_region_addrs] ]%elem_of_list_fmap.
        solve_addr. }
      iDestruct (big_sepM_insert with "H'") as "[? H']".
      { rewrite -not_elem_of_list_to_map /=.
        intros [ [? ?] [-> [? ?]%elem_of_zip_l%elem_of_region_addrs] ]%elem_of_list_fmap.
        solve_addr. }
      rewrite (region_addrs_cons a). 2: solve_addr. simpl.
      iApply big_sepM_insert.
      { rewrite -not_elem_of_list_to_map /=.
        intros [ [? ?] [-> [? ?]%elem_of_zip_l%elem_of_region_addrs] ]%elem_of_list_fmap.
        solve_addr. }
      iFrame. iApply (IHl with "H H'"). solve_addr. solve_addr. }
  Qed.

  Lemma mkregion_prepare `{memG Σ} (a e: Addr) l :
    (a + length l)%a = Some e →
    ([∗ map] k↦v ∈ mkregion a e l, k ↦ₐ v) ==∗ ([∗ list] k;v ∈ (region_addrs a e); l, k ↦ₐ v).
  Proof.
    iIntros (?) "H". iDestruct (mkregion_sepM_to_sepL2 with "H") as "H"; auto.
  Qed.

  Lemma mkregion_prepare_spec `{cfgSG Σ} (a e: Addr) l :
    (a + length l)%a = Some e →
    ([∗ map] k↦v ∈ mkregion a e l, k ↣ₐ v) ==∗ ([∗ list] k;v ∈ (region_addrs a e); l, k ↣ₐ v).
  Proof.
    iIntros (?) "H". iDestruct (mkregion_sepM_to_sepL2 with "H") as "H"; auto.
  Qed.

  Lemma mbkregion_prepare `{memG Σ,cfgSG Σ} (a e : Addr) l l' :
    (a + length l)%a = Some e →
    (a + length l')%a = Some e →
    ([∗ map] k↦v ∈ mkregion a e l, k ↦ₐ v) -∗
    ([∗ map] k↦v ∈ mkregion a e l', k ↣ₐ v) ==∗
    ([∗ map] k↦v ∈ mbkregion a e l l', k ↦ₐ v.1 ∗ k ↣ₐ v.2).
  Proof.
    iIntros (? ?) "H H'". iDestruct (mkregion_sepM_to_sepL2_zip with "H H'") as "H"; auto.
  Qed.

  Lemma regspec_mapsto_alloc {cfg: cfgSG Σ} e (σ : gmap RegName Word * gmap Addr Word) r (w : Word) :
    σ.1 !! r = None →
    spec_res e σ ==∗ spec_res e (<[r:=w]> σ.1,σ.2) ∗ r ↣ᵣ w.
  Proof.
    iIntros (Hnone) "Hσ".
    rewrite /spec_res /regspec_mapsto.
    iMod (own_update with "Hσ") as "[Hσ Hr]".
    { eapply auth_update_alloc,prod_local_update_2,prod_local_update_1.
      eapply (alloc_singleton_local_update (to_spec_map σ.1) r (1%Qp, to_agree w)).
      by rewrite lookup_fmap Hnone. done. }
    iModIntro. iFrame "Hr". rewrite -fmap_insert. iFrame.
  Qed.
  Lemma memspec_mapsto_alloc {cfg: cfgSG Σ} e (σ : gmap RegName Word * gmap Addr Word) a (w : Word) :
    σ.2 !! a = None →
    spec_res e σ ==∗ spec_res e (σ.1,<[a:=w]> σ.2) ∗ a ↣ₐ w.
  Proof.
    iIntros (Hnone) "Hσ".
    rewrite /spec_res /memspec_mapsto.
    iMod (own_update with "Hσ") as "[Hσ Hr]".
    { eapply auth_update_alloc,prod_local_update_2,prod_local_update_2.
      eapply (alloc_singleton_local_update (to_spec_map σ.2) a (1%Qp, to_agree w)).
      by rewrite lookup_fmap Hnone. done. }
    iModIntro. iFrame "Hr". rewrite -fmap_insert. iFrame.
  Qed.
  Lemma regspec_alloc_big {cfg: cfgSG Σ} e σ σ' σs :
    σ' ##ₘ σ →
    spec_res e (σ,σs) ==∗
    spec_res e (σ' ∪ σ,σs) ∗ ([∗ map] l ↦ v ∈ σ', l ↣ᵣ v).
  Proof.
    revert σ; induction σ' as [| l v σ' Hl IH] using map_ind; iIntros (σ Hdisj) "Hσ".
    { rewrite left_id_L. auto. }
    iMod (IH with "Hσ") as "[Hσ'σ Hσ']"; first by eapply map_disjoint_insert_l.
    decompose_map_disjoint.
    rewrite !big_opM_insert // -insert_union_l //.
    iMod (regspec_mapsto_alloc with "Hσ'σ") as "($ & $)".
      by apply lookup_union_None. done.
  Qed.
  Lemma memspec_alloc_big {cfg: cfgSG Σ} e σ σ' σr :
    σ' ##ₘ σ →
    spec_res e (σr, σ) ==∗
    spec_res e (σr, map_union σ' σ) ∗ ([∗ map] l ↦ v ∈ σ', l ↣ₐ v).
  Proof.
    revert σ; induction σ' as [| l v σ' Hl IH] using map_ind; iIntros (σ Hdisj) "Hσ".
    { rewrite left_id_L. auto. }
    iMod (IH with "Hσ") as "[Hσ'σ Hσ']"; first by eapply map_disjoint_insert_l.
    decompose_map_disjoint.
    rewrite !big_opM_insert //.
    assert (map_union (<[l:=v]> σ') σ = <[l:=v]> (map_union σ' σ)) as ->.
    { rewrite insert_union_l. auto. }
    iMod (memspec_mapsto_alloc with "Hσ'σ") as "($ & $)".
    simpl. rewrite lookup_union_None//. done.
  Qed.

  Context {cfgg : inG Σ (authR cfgUR)}.

  Definition codeN : namespace := nroot .@ "conf" .@ "code".

  Lemma confidentiality_adequacy_l' {ML:memory_layout} c_adv p1 p2 stack_init stack_init' (es: list cap_lang.expr)
        reg' m' :
    is_machine_context c_adv comp1 p1 →
    is_machine_context c_adv comp2 p2 →
    is_initial_context c_adv →
    (b_stk + length stack_init)%a = Some e_stk →
    (b_stk + length stack_init')%a = Some e_stk →
    rtc erased_step (initial_state_stk b_stk e_stk stack_init p1) (of_val HaltedV :: es, (reg', m')) →
    (∃ es' conf', rtc erased_step (initial_state_stk b_stk e_stk stack_init' p2) (of_val HaltedV :: es', conf')).
  Proof.
    intros Hm1 Hm2 Hc Hstk_size Hstk_size' Hstep.
    set (reg1 := (initial_state_stk b_stk e_stk stack_init p1).2.1).
    set (m1 := (initial_state_stk b_stk e_stk stack_init p1).2.2).
    set (reg2 := (initial_state_stk b_stk e_stk stack_init' p2).2.1).
    set (m2 := (initial_state_stk b_stk e_stk stack_init' p2).2.2).
    cut (@adequate cap_lang NotStuck (Seq (Instr Executable)) (reg1,m1)
                   (λ v _, v = HaltedV → ∃ thp' conf', rtc erased_step (initial_state_stk b_stk e_stk stack_init' p2)
                                             (of_val HaltedV :: thp', conf'))).
    { destruct 1. inv Hm1. destruct His_program as [Hlink Hprog]. inv Hprog.
      apply adequate_result in Hstep. auto. auto. }
    eapply (wp_adequacy Σ _); iIntros (Hinv ?).

    iMod (gen_heap_init (∅:Mem)) as (mem_heapg) "Hmem_ctx".
    iMod (gen_heap_init (∅:Reg)) as (reg_heapg) "Hreg_ctx".

    iMod (own_alloc (● (Excl' (Seq (Instr Executable)) : optionUR (exclR (leibnizO expr)), (∅,∅))
                       ⋅ ◯ ((Excl' (Seq (Instr Executable)) : optionUR (exclR (leibnizO expr)), (∅,∅)) : cfgUR)))
      as (γc) "[Hcfg1 Hcfg2]".
    { apply auth_valid_discrete. split=>//. esplit=>//. split;eauto. simpl.
      rewrite ucmra_unit_left_id. split;auto. split=>//. }

    unshelve iMod gen_sts_init as (stsg) "Hsts"; eauto. (*XX*)
    set W0 := ((∅, (∅, ∅)) : WORLD).
    iMod heap_init as (heapg) "HRELS".
    iMod (@na_alloc Σ na_invg) as (logrel_nais) "Hna".

    pose memg := MemG Σ Hinv mem_heapg.
    pose regg := RegG Σ Hinv reg_heapg.
    pose logrel_na_invs := Build_logrel_na_invs _ na_invg logrel_nais.
    set (Hcfg := CFGSG _ _ γc).

    pose proof (
      @conf_spec_LR Σ memg regg stsg heapg logrel_na_invs Hcfg
    ) as Spec.

    iMod (gen_heap_alloc_gen _ reg1 with "Hreg_ctx") as "(Hreg_ctx & Hreg & _)".
      by apply map_disjoint_empty_r. rewrite right_id_L.
    iMod (gen_heap_alloc_gen _ m1 with "Hmem_ctx") as "(Hmem_ctx & Hmem & _)".
      by apply map_disjoint_empty_r. rewrite right_id_L.

    iMod (regspec_alloc_big _ ∅ reg2 ∅ with "[Hcfg1]") as "(Hcfg1 & Hregspec)".
      by apply map_disjoint_empty_r. rewrite /spec_res /= !/to_spec_map !fmap_empty //.
    rewrite right_id_L.
    iMod (memspec_alloc_big _ ∅ m2 reg2 with "[Hcfg1]") as "(Hcfg1 & Hmemspec)".
      by apply map_disjoint_empty_r. rewrite /spec_res /= !/to_spec_map !fmap_empty //.
    rewrite right_id_L.

    iAssert (region W0) with "[HRELS]" as "Hr".
    { rewrite region_eq /region_def. iExists ∅, ∅. iFrame.
      rewrite /= !dom_empty_L //. repeat iSplit; eauto.
      rewrite /region_map_def. by rewrite big_sepM_empty. }

    pose proof (regions_disjoint stack_init stack_init' c_adv p1 p2 m1 m2 Hm1 Hm2 Hc eq_refl eq_refl Hstk_size Hstk_size')
      as [resolved_ms [Hm1eq [Hm2eq [Hcan_address_to_main [Hisglobal_main [Hresolved_ms_spec Hdisj] ] ] ] ] ].

    (* Extract points-to for the various regions in memory *)

    rewrite {2}Hm1eq.
    rewrite {2}Hm2eq.
    rewrite disjoint_list_cons in Hdisj |- *. intros (Hdisj_a & Hdisjoint).
    rewrite disjoint_list_cons in Hdisjoint |- *. intros (Hdisj & _).
    assert (∀ z stack_init, mkregion b_stk e_stk stack_init ##ₘ mkregion f_start f_end (conf_instrs z)) as Hdisj_f.
    { intros z stack_init''. apply map_disjoint_spec. intros i x y Hx Hy.
      revert Hdisj. rewrite /= union_empty_r elem_of_disjoint =>Hdisj.
      apply Hdisj with i.
      eapply in_dom_mkregion,elem_of_gmap_dom;eauto.
      eapply in_dom_mkregion,elem_of_gmap_dom;eauto. }
    assert (∀ z stack_init, mkregion b_stk e_stk stack_init ∪ mkregion f_start f_end (conf_instrs z)
                     ##ₘ resolved_ms) as Hdisj_adv.
    { intros z stack_init''. apply map_disjoint_spec. intros i x y Hx Hy.
      revert Hdisj_a; rewrite elem_of_disjoint =>Hdisj_adv.
      apply Hdisj_adv with i.
      apply elem_of_elements,elem_of_gmap_dom;eauto.
      simpl. rewrite !elem_of_union.
      apply lookup_union_Some in Hx as [Hx | Hx];auto.
      right;left. eapply in_dom_mkregion,elem_of_gmap_dom;eauto.
      left. eapply in_dom_mkregion,elem_of_gmap_dom;eauto. }
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hadv]";auto.
    iDestruct (big_sepM_union with "Hmem") as "[Hstk Hf]";auto.
    iDestruct (big_sepM_union with "Hmemspec") as "[Hmemspec Hadv_spec]";auto.
    iDestruct (big_sepM_union with "Hmemspec") as "[Hstk_spec Hf_spec]";auto.

    (* Massage points-to into sepL2s with permission-pointsto *)

    iDestruct (mkregion_prepare with "[$Hf]") as ">Hf". by apply f_size.
    iDestruct (mkregion_prepare_spec with "[$Hf_spec]") as ">Hf_spec". by apply f_size.
    iDestruct (mbkregion_prepare with "[$Hstk] [$Hstk_spec]") as ">Hstk". by apply Hstk_size. by apply Hstk_size'.

    (* Allocate the spec invariant *)
    iMod (inv_alloc specN _ (spec_inv ([Seq (Instr Executable)],(reg2,m2)) ) with "[Hcfg1]") as "#Hspec_∅".
    { iNext. iExists _,_. iFrame. iPureIntro. rewrite /reg2 /m2 /=. left. }
    iAssert (spec_ctx)%I as "#Hspec".
    { iExists _. iFrame "#". }

    (* Allocate the uninitialized stack *)
    set (m_stk := mbkregion b_stk e_stk stack_init stack_init').
    iMod (uninitialized_region_alloc _ _ _ (λ Wv, interp Wv.1 Wv.2) with "Hsts Hr Hstk") as "(Hr & #Hrels & Hsts)".
    { intros. rewrite /W0 /=. auto. }

    (* Allocate the code into a non atomic invariant *)
    iMod (na_inv_alloc logrel_binary.logrel_nais ⊤ codeN (confL (region_addrs f_start f_end) ∗ confR (region_addrs f_start f_end))
            with "[Hf Hf_spec]" )%I as "#Hcode".
    { iNext. iFrame. }

    (* Establish that the adversary region is valid *)
    iDestruct (big_sepM_sep with "[$Hadv $Hadv_spec]") as "Hadv".
    iMod (extend_region_perm_sepM _ _ resolved_ms (λ Wv, interp Wv.1 Wv.2) with "Hsts Hr [Hadv]") as
        "(Hr & #Hadv_rels & Hsts)".
    { intros k. rewrite /m_stk. intros [y Hk].
      rewrite override_uninitialize_std_sta_lookup_none.
      rewrite /W0 /=. auto.
      specialize (Hdisj_adv 2 stack_init').
      apply map_disjoint_Some_r with (i:=k) (x:=y) in Hdisj_adv;auto.
      apply lookup_union_None in Hdisj_adv as [HH ?].
      clear -HH Hstk_size Hstk_size'.
      apply mkregion_mbkregion_None_r;eauto. solve_addr. }
    { iAssert (interp (override_uninitialize m_stk W0) (inr (E, Global, f_start, f_end, f_start),
                                                        inr (E, Global, f_start, f_end, f_start))) as "#Hval".
      { rewrite fixpoint_interp1_eq /=. iSplit;auto. iModIntro.
        iIntros (r W Hrelated). iNext. simpl.
        iIntros "(#(% & Hregs_val) & Hregs & Hregs_spec & Hr & Hsts & Hown & Hj)".
        iSplit;auto.
        rewrite /registers_mapsto /spec_registers_mapsto.
        iDestruct (big_sepM_delete _ _ PC with "Hregs") as "[HPC Hregs]";[rewrite lookup_insert;eauto|].
        iDestruct (big_sepM_delete _ _ PC with "Hregs_spec") as "[HsPC Hregs_spec]";[rewrite lookup_insert;eauto|].
        destruct H with r_stk as [ [? Hstk1] [? Hstk2] ].
        rewrite !delete_insert_delete.
        iDestruct (big_sepM_delete _ _ r_stk with "Hregs") as "[Hstk Hregs]";[rewrite lookup_delete_ne//|].
        iDestruct (big_sepM_delete _ _ r_stk with "Hregs_spec") as "[Hsstk Hregs_spec]";[rewrite lookup_delete_ne//|].
        iApply (Spec _ _ _ _ _ _ _ _ f_end
                  with "[- $Hj $Hr $Hsts $HPC $HsPC $Hregs $Hregs_spec $Hspec $Hown $Hcode $Hstk $Hsstk]").
        { intros mid Hmid. constructor;auto. }
        { apply contiguous_between_region_addrs.
          assert ((f_start + (length (conf_instrs 0)))%a = Some f_end) as Hf. apply f_size.
          clear -Hf. simpl in Hf. solve_addr. }
        { rewrite !dom_delete_L. clear -H.
          assert (dom (gset RegName) r.1 = all_registers_s) as Heq.
          { apply regmap_full_dom. intros. destruct H with x. auto. }
          rewrite Heq. clear. set_solver. }
        { rewrite !dom_delete_L. clear -H.
          assert (dom (gset RegName) r.2 = all_registers_s) as Heq.
          { apply regmap_full_dom. intros. destruct H with x. auto. }
          rewrite Heq. clear. set_solver. }
        { iSpecialize ("Hregs_val" $! r_stk with "[]");auto.
          rewrite /RegLocate Hstk1 Hstk2. iFrame "Hregs_val". }
        iNext. iIntros (v) "H". iFrame.
      }
      iAssert ([∗ map] k↦x ∈ resolved_ms, interp (override_uninitialize m_stk W0)
                                                 (inr (E, Global, f_start, f_end, f_start), inr (E, Global, f_start, f_end, f_start)))%I as "Hadv'".
      { iApply big_sepM_forall. iIntros (k x _). iFrame "Hval". }
      iDestruct (big_sepM_sep with "[$Hadv $Hadv']") as "Hadv".
      iApply (big_sepM_mono with "Hadv").
      iIntros (k x Hk) "[ [Hk1 Hk2] #Hval ]". iFrame. simpl.
      apply Hresolved_ms_spec in Hk as [Hint | ->].
      - iClear "Hval". destruct x;inversion Hint.
        iSplit;[|iModIntro;iIntros (W1 W2 Hrelated) "_";simpl];
          rewrite fixpoint_interp1_eq;auto.
      - iFrame "Hval".
        iModIntro. iIntros (W W' Hrelated) "HH".
        simpl. iApply interp_monotone_nm;eauto.
    }

    match goal with |- context [ (region ?W)%I ] =>
                    set Wstart := W
    end.
    destruct c_adv.
    { inversion Hm1. destruct His_program as [Hlink Hcontr]. inv Hlink. inv Hlink0. inversion Hcontr. }
    destruct p,p; simpl in Hc. destruct Hc as (_&Hcap&_).
    destruct Hcap as (p&g&b_main&e_main&a_main&Heq&Hx). subst w.
    simpl in Hcan_address_to_main, Hisglobal_main. destruct g;inversion Hisglobal_main.
    iAssert (interp Wstart (inr (p,Global,b_main,e_main,a_main),inr (p,Global,b_main,e_main,a_main))) as "#Hval".
    { rewrite fixpoint_interp1_eq. destruct Hx as [-> | ->];simpl.
      all: iSplit;auto.
      all: iApply big_sepL_forall; iIntros (k a Hin).
      1: iExists interp; iSplit;[iPureIntro;apply _|].
      all: assert (a ∈ region_addrs b_main e_main) as Hinms%elem_of_region_addrs%Hcan_address_to_main;
        [apply elem_of_list_lookup;eauto|].
      all: iDestruct (big_sepL_elem_of _ _ a with "Hadv_rels") as "Ha";[apply elem_of_elements;auto|].
      all: iFrame "#".
      1: iSplit;[iApply interp_weakening_binary.rcond_interp|].
      all: iPureIntro;rewrite /Wstart;apply std_sta_update_multiple_lookup_in_i,elem_of_elements;auto.
    }
    Unshelve.
    2: apply _.

    iDestruct (fundamental_binary_from_interp_correctPC _ _ _ _ _ _ (reg1,reg2) with "[Hspec] Hval") as "Hval_exec".
    { destruct Hx as [-> | ->];auto. }
    { iExact "Hspec". }
    iDestruct ("Hval_exec" with "[$Hr $Hsts Hcfg2 $Hna Hreg Hregspec]") as "[_ Hwp]".
    { rewrite /exprspec_mapsto. iFrame.
      inv Hm1; inv Hm2. destruct His_program as [Hlink His_program].
      destruct His_program0 as [Hlink0 His_program0].
      pose proof (initial_registers_full_map stack_init _ reg1 His_program eq_refl) as Hfull1.
      pose proof (initial_registers_full_map stack_init' _ reg2 His_program0 eq_refl) as Hfull2.
      inv His_program; inv His_program0.
      inv Hlink. inv Hlink1. inv Hlink0. inv Hlink.
      Local Opaque list_to_set.
      iSplitR.
      { iSplit. iPureIntro. intros. simpl. destruct Hfull1 with x. destruct Hfull2 with x;eauto.
        rewrite /registers_mapsto /spec_registers_mapsto /reg1 /reg2 /initial_state_stk /=.
        rewrite !(insert_commute _ r_stk PC)//. rewrite !insert_insert.
        iIntros (r Hne). rewrite /RegLocate lookup_insert_ne//.
        destruct (decide (r_stk = r)).
        - subst. rewrite lookup_insert. iClear "Hval_exec Hval Hcode Hadv_rels Hspec".
          rewrite fixpoint_interp1_eq /=. iSplit;auto.
          assert (addr_reg.min b_stk e_stk = b_stk) as ->;[clear -Hstk_size;solve_addr|].
          assert (addr_reg.max b_stk b_stk = b_stk) as ->;[clear;solve_addr|].
          rewrite region_addrs_empty;[|clear;solve_addr]. iSplit;auto.
          iApply big_sepL_forall. iIntros (k x Hin).
          assert (is_Some (m_stk !! x)) as [y Hy].
          { apply elem_of_gmap_dom. rewrite /m_stk.
            apply mkregion_mbkregion_elem_of_l;[clear -Hstk_size Hstk_size';solve_addr|].
            apply in_dom_mkregion';auto. apply elem_of_list_lookup;eauto. }
          iDestruct (big_sepM_delete _ _ x with "Hrels") as "[Hrel _]";[apply Hy|]. iFrame "Hrel".
          iPureIntro. right. rewrite /Wstart /=. exists y.
          rewrite std_sta_update_multiple_lookup_same_i.
          apply override_uninitialize_std_sta_lookup_some;auto. clear -Hdisj_adv Hin Hy Hstk_size Hstk_size'.
          intros [x1 Hcontr]%elem_of_elements%elem_of_gmap_dom. specialize (Hdisj_adv 2 stack_init).
          assert (x ∈ dom (gset Addr) m_stk) as Hy'.
          { apply elem_of_gmap_dom;eauto. }
          apply mkregion_mbkregion_elem_of_l in Hy'. 2: clear -Hstk_size Hstk_size'; solve_addr.
          apply elem_of_gmap_dom in Hy' as [? ?].
          assert ((∀ i x y,
                      (mkregion b_stk e_stk stack_init ∪ mkregion f_start f_end (conf_instrs 2%nat)) !! i = Some x
                      → resolved_ms !! i = Some y → False)) as Hspec.
          { apply map_disjoint_spec. auto. }
          apply Hspec with x x0 x1;eauto. apply lookup_union_Some_l. auto.
        - rewrite lookup_insert_ne//.
          destruct (gset_to_gmap (inl 0%Z) (list_to_set all_registers) !! r) eqn:Hsome.
          apply lookup_gset_to_gmap_Some in Hsome as [_ <-].
          all: iClear "#"; rewrite fixpoint_interp1_eq;done.
      }
      { rewrite /registers_mapsto /spec_registers_mapsto /reg1 /reg2 /initial_state_stk /=.
        rewrite !(insert_commute _ r_stk PC)//. rewrite !insert_insert. iFrame. } }
    rewrite /interp_expression /interp_expr /=.

    iModIntro.
    (* Must match the state_interp of [memG_irisG] in rules_base.v *)
    iExists (fun σ κs => ((gen_heap_ctx σ.1) ∗ (gen_heap_ctx σ.2)))%I.
    iExists (fun _ => True)%I. iFrame. iApply wp_fupd. iApply wp_wand_r. iFrame.
    iIntros (v) "Hcond". iIntros (->).
    iDestruct ("Hcond" $! eq_refl) as (r W') "(Hj & Hcond)".
    iClear "Hspec".
    iInv specN as ">Hres" "Hcls". iDestruct "Hres" as (e' σ') "[Hown Hsteps]".
    iDestruct "Hsteps" as %Hsteps.
    iDestruct (own_valid_2 with "Hown Hj") as %Hvalid.
    iMod ("Hcls" with "[Hown]") as "_".
    { iNext. iExists _,_. eauto. }
    apply auth_both_valid in Hvalid as [Hincl Hvalid].
    apply prod_included in Hincl as [Hincl Hincl']. simpl in *.
    revert Hincl; rewrite Excl_included =>Hincl.
    apply leibniz_equiv in Hincl as <-.
    iModIntro. iExists [],σ'. iPureIntro.
    inv Hm1; inv Hm2. destruct His_program as [Hlink His_program].
    destruct His_program0 as [Hlink0 His_program0].
    inv His_program; inv His_program0.
    inv Hlink. inv Hlink1. inv Hlink0. inv Hlink.
    apply Hsteps.
  Qed.

  Lemma confidentiality_adequacy_r' {ML:memory_layout} c_adv p1 p2 stack_init stack_init' (es: list cap_lang.expr)
        reg' m' :
    is_machine_context c_adv comp1 p1 →
    is_machine_context c_adv comp2 p2 →
    is_initial_context c_adv →
    (b_stk + length stack_init)%a = Some e_stk →
    (b_stk + length stack_init')%a = Some e_stk →
    rtc erased_step (initial_state_stk b_stk e_stk stack_init' p2) (of_val HaltedV :: es, (reg', m')) →
    (∃ es' conf', rtc erased_step (initial_state_stk b_stk e_stk stack_init p1) (of_val HaltedV :: es', conf')).
  Proof.
    intros Hm1 Hm2 Hc Hstk_size Hstk_size' Hstep.
    set (reg1 := (initial_state_stk b_stk e_stk stack_init p1).2.1).
    set (m1 := (initial_state_stk b_stk e_stk stack_init p1).2.2).
    set (reg2 := (initial_state_stk b_stk e_stk stack_init' p2).2.1).
    set (m2 := (initial_state_stk b_stk e_stk stack_init' p2).2.2).
    cut (@adequate cap_lang NotStuck (Seq (Instr Executable)) (reg2,m2)
                   (λ v _, v = HaltedV → ∃ thp' conf', rtc erased_step (initial_state_stk b_stk e_stk stack_init p1)
                                             (of_val HaltedV :: thp', conf'))).
    { destruct 1. inv Hm2. destruct His_program as [Hlink Hprog]. inv Hprog.
      apply adequate_result in Hstep. auto. auto. }
    eapply (wp_adequacy Σ _); iIntros (Hinv ?).

    iMod (gen_heap_init (∅:Mem)) as (mem_heapg) "Hmem_ctx".
    iMod (gen_heap_init (∅:Reg)) as (reg_heapg) "Hreg_ctx".

    iMod (own_alloc (● (Excl' (Seq (Instr Executable)) : optionUR (exclR (leibnizO expr)), (∅,∅))
                       ⋅ ◯ ((Excl' (Seq (Instr Executable)) : optionUR (exclR (leibnizO expr)), (∅,∅)) : cfgUR)))
      as (γc) "[Hcfg1 Hcfg2]".
    { apply auth_valid_discrete. split=>//. esplit=>//. split;eauto. simpl.
      rewrite ucmra_unit_left_id. split;auto. split=>//. }

    unshelve iMod gen_sts_init as (stsg) "Hsts"; eauto. (*XX*)
    set W0 := ((∅, (∅, ∅)) : WORLD).
    iMod heap_init as (heapg) "HRELS".
    iMod (@na_alloc Σ na_invg) as (logrel_nais) "Hna".

    pose memg := MemG Σ Hinv mem_heapg.
    pose regg := RegG Σ Hinv reg_heapg.
    pose logrel_na_invs := Build_logrel_na_invs _ na_invg logrel_nais.
    set (Hcfg := CFGSG _ _ γc).

    pose proof (
      @conf_spec_RL Σ memg regg stsg heapg logrel_na_invs Hcfg
    ) as Spec.

    iMod (gen_heap_alloc_gen _ reg2 with "Hreg_ctx") as "(Hreg_ctx & Hreg & _)".
      by apply map_disjoint_empty_r. rewrite right_id_L.
    iMod (gen_heap_alloc_gen _ m2 with "Hmem_ctx") as "(Hmem_ctx & Hmem & _)".
      by apply map_disjoint_empty_r. rewrite right_id_L.

    iMod (regspec_alloc_big _ ∅ reg1 ∅ with "[Hcfg1]") as "(Hcfg1 & Hregspec)".
      by apply map_disjoint_empty_r. rewrite /spec_res /= !/to_spec_map !fmap_empty //.
    rewrite right_id_L.
    iMod (memspec_alloc_big _ ∅ m1 reg1 with "[Hcfg1]") as "(Hcfg1 & Hmemspec)".
      by apply map_disjoint_empty_r. rewrite /spec_res /= !/to_spec_map !fmap_empty //.
    rewrite right_id_L.

    iAssert (region W0) with "[HRELS]" as "Hr".
    { rewrite region_eq /region_def. iExists ∅, ∅. iFrame.
      rewrite /= !dom_empty_L //. repeat iSplit; eauto.
      rewrite /region_map_def. by rewrite big_sepM_empty. }

    pose proof (regions_disjoint stack_init stack_init' c_adv p1 p2 m1 m2 Hm1 Hm2 Hc eq_refl eq_refl Hstk_size Hstk_size')
      as [resolved_ms [Hm1eq [Hm2eq [Hcan_address_to_main [Hisglobal_main [Hresolved_ms_spec Hdisj] ] ] ] ] ].

    (* Extract points-to for the various regions in memory *)

    rewrite {2}Hm1eq.
    rewrite {2}Hm2eq.
    rewrite disjoint_list_cons in Hdisj |- *. intros (Hdisj_a & Hdisjoint).
    rewrite disjoint_list_cons in Hdisjoint |- *. intros (Hdisj & _).
    assert (∀ z stack_init, mkregion b_stk e_stk stack_init ##ₘ mkregion f_start f_end (conf_instrs z)) as Hdisj_f.
    { intros z stack_init''. apply map_disjoint_spec. intros i x y Hx Hy.
      revert Hdisj. rewrite /= union_empty_r elem_of_disjoint =>Hdisj.
      apply Hdisj with i.
      eapply in_dom_mkregion,elem_of_gmap_dom;eauto.
      eapply in_dom_mkregion,elem_of_gmap_dom;eauto. }
    assert (∀ z stack_init, mkregion b_stk e_stk stack_init ∪ mkregion f_start f_end (conf_instrs z)
                     ##ₘ resolved_ms) as Hdisj_adv.
    { intros z stack_init''. apply map_disjoint_spec. intros i x y Hx Hy.
      revert Hdisj_a; rewrite elem_of_disjoint =>Hdisj_adv.
      apply Hdisj_adv with i.
      apply elem_of_elements,elem_of_gmap_dom;eauto.
      simpl. rewrite !elem_of_union.
      apply lookup_union_Some in Hx as [Hx | Hx];auto.
      right;left. eapply in_dom_mkregion,elem_of_gmap_dom;eauto.
      left. eapply in_dom_mkregion,elem_of_gmap_dom;eauto. }
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hadv]";auto.
    iDestruct (big_sepM_union with "Hmem") as "[Hstk Hf]";auto.
    iDestruct (big_sepM_union with "Hmemspec") as "[Hmemspec Hadv_spec]";auto.
    iDestruct (big_sepM_union with "Hmemspec") as "[Hstk_spec Hf_spec]";auto.

    (* Massage points-to into sepL2s with permission-pointsto *)

    iDestruct (mkregion_prepare with "[$Hf]") as ">Hf". by apply f_size.
    iDestruct (mkregion_prepare_spec with "[$Hf_spec]") as ">Hf_spec". by apply f_size.
    iDestruct (mbkregion_prepare with "[$Hstk] [$Hstk_spec]") as ">Hstk". by apply Hstk_size'. by apply Hstk_size.

    (* Allocate the spec invariant *)
    iMod (inv_alloc specN _ (spec_inv ([Seq (Instr Executable)],(reg1,m1)) ) with "[Hcfg1]") as "#Hspec_∅".
    { iNext. iExists _,_. iFrame. iPureIntro. rewrite /reg1 /m1 /=. left. }
    iAssert (spec_ctx)%I as "#Hspec".
    { iExists _. iFrame "#". }

    (* Allocate the uninitialized stack *)
    set (m_stk := mbkregion b_stk e_stk stack_init' stack_init).
    iMod (uninitialized_region_alloc _ _ _ (λ Wv, interp Wv.1 Wv.2) with "Hsts Hr Hstk") as "(Hr & #Hrels & Hsts)".
    { intros. rewrite /W0 /=. auto. }

    (* Allocate the code into a non atomic invariant *)
    iMod (na_inv_alloc logrel_binary.logrel_nais ⊤ codeN (confR' (region_addrs f_start f_end) ∗ confL' (region_addrs f_start f_end))
            with "[Hf Hf_spec]" )%I as "#Hcode".
    { iNext. iFrame. }

    (* Establish that the adversary region is valid *)
    iDestruct (big_sepM_sep with "[$Hadv $Hadv_spec]") as "Hadv".
    iMod (extend_region_perm_sepM _ _ resolved_ms (λ Wv, interp Wv.1 Wv.2) with "Hsts Hr [Hadv]") as
        "(Hr & #Hadv_rels & Hsts)".
    { intros k. rewrite /m_stk. intros [y Hk].
      rewrite override_uninitialize_std_sta_lookup_none.
      rewrite /W0 /=. auto.
      specialize (Hdisj_adv 2 stack_init').
      apply map_disjoint_Some_r with (i:=k) (x:=y) in Hdisj_adv;auto.
      apply lookup_union_None in Hdisj_adv as [HH ?].
      clear -HH Hstk_size Hstk_size'.
      apply mkregion_mbkregion_None_l;eauto. solve_addr. }
    { iAssert (interp (override_uninitialize m_stk W0) (inr (E, Global, f_start, f_end, f_start),
                                                        inr (E, Global, f_start, f_end, f_start))) as "#Hval".
      { rewrite fixpoint_interp1_eq /=. iSplit;auto. iModIntro.
        iIntros (r W Hrelated). iNext. simpl.
        iIntros "(#(% & Hregs_val) & Hregs & Hregs_spec & Hr & Hsts & Hown & Hj)".
        iSplit;auto.
        rewrite /registers_mapsto /spec_registers_mapsto.
        iDestruct (big_sepM_delete _ _ PC with "Hregs") as "[HPC Hregs]";[rewrite lookup_insert;eauto|].
        iDestruct (big_sepM_delete _ _ PC with "Hregs_spec") as "[HsPC Hregs_spec]";[rewrite lookup_insert;eauto|].
        destruct H with r_stk as [ [? Hstk1] [? Hstk2] ].
        rewrite !delete_insert_delete.
        iDestruct (big_sepM_delete _ _ r_stk with "Hregs") as "[Hstk Hregs]";[rewrite lookup_delete_ne//|].
        iDestruct (big_sepM_delete _ _ r_stk with "Hregs_spec") as "[Hsstk Hregs_spec]";[rewrite lookup_delete_ne//|].
        iApply (Spec _ _ _ _ _ _ _ _ f_end
                  with "[- $Hj $Hr $Hsts $HPC $HsPC $Hregs $Hregs_spec $Hspec $Hown $Hcode $Hstk $Hsstk]").
        { intros mid Hmid. constructor;auto. }
        { apply contiguous_between_region_addrs.
          assert ((f_start + (length (conf_instrs 0)))%a = Some f_end) as Hf. apply f_size.
          clear -Hf. simpl in Hf. solve_addr. }
        { rewrite !dom_delete_L. clear -H.
          assert (dom (gset RegName) r.1 = all_registers_s) as Heq.
          { apply regmap_full_dom. intros. destruct H with x. auto. }
          rewrite Heq. clear. set_solver. }
        { rewrite !dom_delete_L. clear -H.
          assert (dom (gset RegName) r.2 = all_registers_s) as Heq.
          { apply regmap_full_dom. intros. destruct H with x. auto. }
          rewrite Heq. clear. set_solver. }
        { iSpecialize ("Hregs_val" $! r_stk with "[]");auto.
          rewrite /RegLocate Hstk1 Hstk2. iFrame "Hregs_val". }
        iNext. iIntros (v) "H". iFrame.
      }
      iAssert ([∗ map] k↦x ∈ resolved_ms, interp (override_uninitialize m_stk W0)
                                                 (inr (E, Global, f_start, f_end, f_start), inr (E, Global, f_start, f_end, f_start)))%I as "Hadv'".
      { iApply big_sepM_forall. iIntros (k x _). iFrame "Hval". }
      iDestruct (big_sepM_sep with "[$Hadv $Hadv']") as "Hadv".
      iApply (big_sepM_mono with "Hadv").
      iIntros (k x Hk) "[ [Hk1 Hk2] #Hval ]". iFrame. simpl.
      apply Hresolved_ms_spec in Hk as [Hint | ->].
      - iClear "Hval". destruct x;inversion Hint.
        iSplit;[|iModIntro;iIntros (W1 W2 Hrelated) "_";simpl];
          rewrite fixpoint_interp1_eq;auto.
      - iFrame "Hval".
        iModIntro. iIntros (W W' Hrelated) "HH".
        simpl. iApply interp_monotone_nm;eauto.
    }

    match goal with |- context [ (region ?W)%I ] =>
                    set Wstart := W
    end.
    destruct c_adv.
    { inversion Hm1. destruct His_program as [Hlink Hcontr]. inv Hlink. inv Hlink0. inversion Hcontr. }
    destruct p,p; simpl in Hc. destruct Hc as (_&Hcap&_).
    destruct Hcap as (p&g&b_main&e_main&a_main&Heq&Hx). subst w.
    simpl in Hcan_address_to_main, Hisglobal_main. destruct g;inversion Hisglobal_main.
    iAssert (interp Wstart (inr (p,Global,b_main,e_main,a_main),inr (p,Global,b_main,e_main,a_main))) as "#Hval".
    { rewrite fixpoint_interp1_eq. destruct Hx as [-> | ->];simpl.
      all: iSplit;auto.
      all: iApply big_sepL_forall; iIntros (k a Hin).
      1: iExists interp; iSplit;[iPureIntro;apply _|].
      all: assert (a ∈ region_addrs b_main e_main) as Hinms%elem_of_region_addrs%Hcan_address_to_main;
        [apply elem_of_list_lookup;eauto|].
      all: iDestruct (big_sepL_elem_of _ _ a with "Hadv_rels") as "Ha";[apply elem_of_elements;auto|].
      all: iFrame "#".
      1: iSplit;[iApply interp_weakening_binary.rcond_interp|].
      all: iPureIntro;rewrite /Wstart;apply std_sta_update_multiple_lookup_in_i,elem_of_elements;auto.
    }
    Unshelve.
    2: apply _.

    iDestruct (fundamental_binary_from_interp_correctPC _ _ _ _ _ _ (reg1,reg2) with "[Hspec] Hval") as "Hval_exec".
    { destruct Hx as [-> | ->];auto. }
    { iExact "Hspec". }
    iDestruct ("Hval_exec" with "[$Hr $Hsts Hcfg2 $Hna Hreg Hregspec]") as "[_ Hwp]".
    { rewrite /exprspec_mapsto. iFrame.
      inv Hm1; inv Hm2. destruct His_program as [Hlink His_program].
      destruct His_program0 as [Hlink0 His_program0].
      pose proof (initial_registers_full_map stack_init _ reg1 His_program eq_refl) as Hfull1.
      pose proof (initial_registers_full_map stack_init' _ reg2 His_program0 eq_refl) as Hfull2.
      inv His_program; inv His_program0.
      inv Hlink. inv Hlink1. inv Hlink0. inv Hlink.
      Local Opaque list_to_set.
      iSplitR.
      { iSplit. iPureIntro. intros. simpl. destruct Hfull1 with x. destruct Hfull2 with x;eauto.
        rewrite /registers_mapsto /spec_registers_mapsto /reg1 /reg2 /initial_state_stk /=.
        rewrite !(insert_commute _ r_stk PC)//. rewrite !insert_insert.
        iIntros (r Hne). rewrite /RegLocate lookup_insert_ne//.
        destruct (decide (r_stk = r)).
        - subst. rewrite lookup_insert. iClear "Hval_exec Hval Hcode Hadv_rels Hspec".
          rewrite fixpoint_interp1_eq /=. iSplit;auto.
          assert (addr_reg.min b_stk e_stk = b_stk) as ->;[clear -Hstk_size;solve_addr|].
          assert (addr_reg.max b_stk b_stk = b_stk) as ->;[clear;solve_addr|].
          rewrite region_addrs_empty;[|clear;solve_addr]. iSplit;auto.
          iApply big_sepL_forall. iIntros (k x Hin).
          assert (is_Some (m_stk !! x)) as [y Hy].
          { apply elem_of_gmap_dom. rewrite /m_stk.
            apply mkregion_mbkregion_elem_of_l;[clear -Hstk_size Hstk_size';solve_addr|].
            apply in_dom_mkregion';auto. apply elem_of_list_lookup;eauto. }
          iDestruct (big_sepM_delete _ _ x with "Hrels") as "[Hrel _]";[apply Hy|]. iFrame "Hrel".
          iPureIntro. right. rewrite /Wstart /=. exists y.
          rewrite std_sta_update_multiple_lookup_same_i.
          apply override_uninitialize_std_sta_lookup_some;auto. clear -Hdisj_adv Hin Hy Hstk_size Hstk_size'.
          intros [x1 Hcontr]%elem_of_elements%elem_of_gmap_dom. specialize (Hdisj_adv 2 stack_init).
          assert (x ∈ dom (gset Addr) m_stk) as Hy'.
          { apply elem_of_gmap_dom;eauto. }
          apply mkregion_mbkregion_elem_of_r in Hy'. 2: clear -Hstk_size Hstk_size'; solve_addr.
          apply elem_of_gmap_dom in Hy' as [? ?].
          assert ((∀ i x y,
                      (mkregion b_stk e_stk stack_init ∪ mkregion f_start f_end (conf_instrs 2%nat)) !! i = Some x
                      → resolved_ms !! i = Some y → False)) as Hspec.
          { apply map_disjoint_spec. auto. }
          apply Hspec with x x0 x1;eauto. apply lookup_union_Some_l. auto.
        - rewrite lookup_insert_ne//.
          destruct (gset_to_gmap (inl 0%Z) (list_to_set all_registers) !! r) eqn:Hsome.
          apply lookup_gset_to_gmap_Some in Hsome as [_ <-].
          all: iClear "#"; rewrite fixpoint_interp1_eq;done.
      }
      { rewrite /registers_mapsto /spec_registers_mapsto /reg1 /reg2 /initial_state_stk /=.
        rewrite !(insert_commute _ r_stk PC)//. rewrite !insert_insert. iFrame. } }
    rewrite /interp_expression /interp_expr /=.

    iModIntro.
    (* Must match the state_interp of [memG_irisG] in rules_base.v *)
    iExists (fun σ κs => ((gen_heap_ctx σ.1) ∗ (gen_heap_ctx σ.2)))%I.
    iExists (fun _ => True)%I. iFrame. iApply wp_fupd. iApply wp_wand_r. iFrame.
    iIntros (v) "Hcond". iIntros (->).
    iDestruct ("Hcond" $! eq_refl) as (r W') "(Hj & Hcond)".
    iClear "Hspec".
    iInv specN as ">Hres" "Hcls". iDestruct "Hres" as (e' σ') "[Hown Hsteps]".
    iDestruct "Hsteps" as %Hsteps.
    iDestruct (own_valid_2 with "Hown Hj") as %Hvalid.
    iMod ("Hcls" with "[Hown]") as "_".
    { iNext. iExists _,_. eauto. }
    apply auth_both_valid in Hvalid as [Hincl Hvalid].
    apply prod_included in Hincl as [Hincl Hincl']. simpl in *.
    revert Hincl; rewrite Excl_included =>Hincl.
    apply leibniz_equiv in Hincl as <-.
    iModIntro. iExists [],σ'. iPureIntro.
    inv Hm1; inv Hm2. destruct His_program as [Hlink His_program].
    destruct His_program0 as [Hlink0 His_program0].
    inv His_program; inv His_program0.
    inv Hlink. inv Hlink1. inv Hlink0. inv Hlink.
    apply Hsteps.
  Qed.

End Adequacy.
