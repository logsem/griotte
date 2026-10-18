From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode memory_region fetch.
From griotte.allocators.common Require Import allocator_common_preamble.

(** Loop specifications. Fetch and return use the existing instruction/macro rules.
    Every loop requires a nonempty range because it stores before testing.
    Registers not mentioned in the contracts can be framed. *)

(** A tagged, nonempty capability based in the heap has authority. *)
Lemma heap_authority_base_heap_cap `{MP : MachineParameters} p g b e a :
  (heap_b <= b)%a -> (b < e)%a -> (b < heap_e)%a ->
  heap_authority_base (WCap true p g b e a) = Some b.
Proof.
  intros Hb Hbe He.
  rewrite /heap_authority_base decide_True // /heap_cap_base /=.
  assert (is_heap_address b = true) as -> by (apply withinBounds_true_iff; solve_addr).
  done.
Qed.

Lemma has_authority_heap_cap `{MP : MachineParameters} p g b e a :
  (heap_b <= b)%a -> (b < e)%a -> (b < heap_e)%a ->
  has_authority (WCap true p g b e a).
Proof.
  intros Hb Hbe He. split; first done. exists b.
  by apply heap_authority_base_heap_cap.
Qed.

Section AllocatorMacros.
  Context
    {Σ : gFunctors}
    {ceriseg : ceriseG Σ}
    {MP : MachineParameters}
  .

  (** The existing fetch macro proof specialized to an arbitrary WP mask, so
      allocator calls can keep the non-atomic service invariant open. *)

  Lemma allocator_fetch_spec
    (n off : Z) (rdst : RegName) (E : coPset)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (wentry wdst : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    let code := fetch_instrs off rdst in
    let pc_end := (pc_a ^+ length code)%a in
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a pc_end ->
    (pc_a + off)%a = Some (pc_b ^+ n)%a ->
    withinBounds pc_b pc_e (pc_b ^+ n)%a = true ->
    disjoint_from_shadow pc_b pc_e ->
    is_heap_cap wentry.(lw) = false ->
    rdst ≠ cnull ->

    PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    rdst ↦ᵣ wdst ∗
    (pc_b ^+ n)%a ↦ₐ□ wentry ∗
    codefrag_pers pc_a code ∗
    ▷ (PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_end ∗
         rdst ↦ᵣ lload_word pc_p wentry ∗
         (pc_b ^+ n)%a ↦ₐ□ wentry ∗
         codefrag_pers pc_a code
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros code pc_end Hvpc Hcont Hoff Hpc_n Hdisjoint Hnonheap Hrdst;
      subst code pc_end.
    iIntros "(HPC & Hrdst & #Hentry & #Hcode & Hφ)".
    codefrag_facts "Hcode".
    assert (is_shadow_address (pc_b ^+ n)%a = false) as Hshadow.
    { eapply disjoint_from_shadow_not_in; eauto. }
    (* Auipcc rdst off. *)
    iInstr "Hcode".
    (* CLoad rdst rdst 0. *)
    iInstr "Hcode".
    iApply "Hφ"; iFrame "∗ Hentry Hcode".
  Qed.

  Lemma allocator_return_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wret : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    let code := encodeInstrsW [Jalr cnull cra] in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length code)%a ->
    disjoint_from_shadow pc_b pc_e ->

    PC ↦ₚ WCap true RX Global pc_b pc_e pc_a ∗
    cra ↦ᵣ wret ∗
    codefrag_pers pc_a code ∗
    ▷ φ FaultedV ∗
    ▷ (PC ↦ₚ lupdatePcPerm wret ∗
         cra ↦ᵣ wret ∗
         codefrag_pers pc_a code ∗
         £ 1
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros code Hpc Hdisjoint; subst code.
    iIntros "(HPC & Hcra & #Hcode & Hfailed & Hφ)".
    codefrag_facts "Hcode".
    destruct (jalr_target_ok cnull cra wret.(lw)) eqn:Htgt; cycle 1.
    { (* Jalr cnull cra. *)
      iInstr_fail "Hcode".
      wp_end. iExact "Hfailed". }
    (* Jalr cnull cra. *)
    iInstr "Hcode" with "Hlc".
    iApply "Hφ". iFrame "∗ Hcode".
  Qed.

  Lemma allocator_zero_spec
    (rptr rend rtmp : RegName) (E : coPset)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (p : Perm) (g : Locality) (b e : Addr) (π : option AId) (dw : deref_witness) (wtmp : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    let code := allocator_zero_instrs rptr rend rtmp in
    let pc_end := (pc_a ^+ length code)%a in
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a pc_end ->
    disjoint_from_shadow pc_b pc_e ->
    writeAllowed p = true ->
    (heap_b <= b /\ b < e /\ e <= heap_e)%a ->
    NoDup [cnull; rptr; rend; rtmp] ->
    π = deref_id dw ->

    PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    rptr ↦ᵣ WCap true p g b e b @@? π ∗
    deref_witness_res dw ∗
    rend ↦ᵣ WInt (finz.to_z e) ∗
    rtmp ↦ᵣ wtmp ∗
    allocator_range_memory b e ∗
    codefrag_pers pc_a code ∗
    ▷ (PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_end ∗
         rptr ↦ᵣ WCap true p g b e e @@? π ∗
         deref_witness_res dw ∗
         rend ↦ᵣ WInt (finz.to_z e) ∗
         rtmp ↦ᵣ WInt 0 ∗
         ([∗ list] a ∈ finz.seq_between b e, a ↦ₐ WInt 0) ∗
         codefrag_pers pc_a code
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.

  Proof.
    intros code pc_end; subst code pc_end.
    iIntros (Hexec Hpc Hpc_shadow Hwrite Hheap Hregs Hπ)
      "(HPC & Hptr & Hdw & Hend & Htmp & Hmem & #Hcode & Hφ)".
    assert (Hrptr : rptr ≠ cnull) by (repeat rewrite NoDup_cons in Hregs; set_solver).
    assert (Hrend : rend ≠ cnull) by (repeat rewrite NoDup_cons in Hregs; set_solver).
    assert (Hrtmp : rtmp ≠ cnull) by (repeat rewrite NoDup_cons in Hregs; set_solver).

    (* Keep the capability's base fixed while the loop cursor advances. *)
    pose (cap_b := b).
    assert (Hcap_b : (heap_b <= cap_b)%a) by (unfold cap_b; solve_addr).
    assert (Hba : (cap_b <= b)%a) by (unfold cap_b; solve_addr).
    assert (Hbase : b = cap_b) by done.
    iEval (rewrite {1}Hbase) in "Hptr".
    iEval (rewrite {1}Hbase) in "Hφ".
    clear Hbase; clearbody cap_b.
    iLöb as "IH" forall (b wtmp Hheap Hba).
    codefrag_facts "Hcode".
    iEval (rewrite /allocator_range_memory
      (finz_seq_between_cons b e (proj1 (proj2 Hheap))) big_sepL_cons) in "Hmem".
    iDestruct "Hmem" as "[[%w Ha] Hmem]".

    iEval (rewrite deref_witness_res_deref_res -Hπ) in "Hdw".
    (* Store rptr 0: the status witness of the capability's identifier
       keeps its copy exact. *)
    iInstrApply "Hcode" wp_store_success_z_imm with "[$HPC $Hptr $Ha $Hdw]"
      as "(HPC & Hptr & Ha & Hdw)".
    { eapply disjoint_from_shadow_not_in; first exact heap_shadow_disjoint.
      apply withinBounds_true_iff; solve_addr. }
    { apply withinBounds_true_iff; solve_addr. }
    { solve_addr. }
    iEval (rewrite Hπ -deref_witness_res_deref_res) in "Hdw".

    (* Lea rptr 1 advances the heap cursor. *)
    iInstr "Hcode".
    { transitivity (Some (b ^+ 1)%a); solve_addr. }
    (* GetA rtmp rptr reads the advanced cursor. *)
    iInstr "Hcode".
    (* Sub rtmp rend rtmp computes the remaining length. *)
    iInstr "Hcode".
    destruct (decide ((b ^+ 1)%a = e)) as [Hlast | Hmore].
    - rewrite Hlast Z.sub_diag.
      (* Jnz .allocator_zero rtmp falls through after the last address. *)
      iInstr "Hcode".
      iApply "Hφ"; iFrame "∗ Hcode".
      rewrite (finz_seq_between_cons b e (proj1 (proj2 Hheap)))
        Hlast finz_seq_between_empty; last solve_addr.
      rewrite big_sepL_cons big_sepL_nil. iFrame "∗".
    - (* Jnz .allocator_zero rtmp repeats the loop. *)
      iInstrApply "Hcode" wp_jnz_success_jmp_z with "[$HPC $Htmp]" as "(HPC & Htmp)".
      { apply negb_true_iff, Z.eqb_neq. intros Hzero; cbn in Hzero; solve_addr. }
      { instantiate (1 := pc_a). solve_addr. }
      iApply ("IH" $! (b ^+ 1)%a with
        "[] [] HPC Hptr Hdw Hend Htmp Hmem [Ha Hφ]").
      { iPureIntro; solve_addr. }
      { iPureIntro; solve_addr. }
      iNext. iIntros "(HPC & Hptr & Hdw & Hend & Htmp & Hzero & _)".
      iApply "Hφ"; iFrame "∗ Hcode".
      rewrite (finz_seq_between_cons b e (proj1 (proj2 Hheap))) big_sepL_cons.
      iFrame "∗".
  Qed.

  (** The shadow stores of the paint loop are justified either because they
      store the entry's current value, or by a shared resource [R] together
      with a per-cell resource [P a]. *)
  Definition allocator_paint_ok (R : iProp Σ) (P : Addr → iProp Σ) (b e : Addr) : Prop :=
    ∀ a Rs Cs, (b <= a < e)%a →
      reg_auth Rs -∗ addr_alloc_auth Cs -∗ R ∗ P a -∗ ⌜shadow_perm_ok Rs Cs a⌝.

  (** The shadow store of the paint loop: the entry of [b] receives [s_new],
      either its current value or justified by [allocator_paint_ok]. *)
  Lemma allocator_paint_store_spec E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dq
    (rptr : RegName) (s_old s_new : AllocStatus) (b e sb : Addr)
    (R : iProp Σ) (P : Addr → iProp Σ) :
    decodeInstrW w.(lw) = Store rptr (inl (encodeAllocStatus s_new)) 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rptr ≠ cnull →
    (b < e)%a →
    (shadow_b <= sb < shadow_e)%a →
    heap_to_shadow b = Some sb →
    s_old = s_new ∨ allocator_paint_ok R P b e →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ rptr ↦ᵣ WCap true RW Global shadow_b shadow_e sb ∗
        ▷ b ↦ₛ s_old ∗
        R ∗
        P b }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        rptr ↦ᵣ WCap true RW Global shadow_b shadow_e sb ∗
        b ↦ₛ s_new ∗
        R ∗
        P b }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hrptr Hbe Hsb Hmap Hok Φ)
      "(HPC & Hi & Hptr & Hs & HR & HP) HΦ".
    destruct Hok as [<- | Hok].
    - iApply (wp_store_success_shadow_z_same with "[$HPC $Hi $Hptr $Hs]"); try solve_pure.
      { unfold is_shadow_address. apply withinBounds_true_iff; solve_addr. }
      { by apply heap_shadow_inverse. }
      { apply withinBounds_true_iff; solve_addr. }
      iIntros "!> (HPC & Hi & Hptr & Hs)". iApply "HΦ". iFrame.
    - iApply (wp_store_success_shadow_z_res _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s_new s_old b
        (R ∗ P b) with "[$HPC $Hi $Hptr $Hs $HR $HP]"); try solve_pure.
      { intros Rs Cs. iIntros "HRs HCs HRP".
        iApply (Hok b with "HRs HCs HRP"). solve_addr. }
      { unfold is_shadow_address. apply withinBounds_true_iff; solve_addr. }
      { by apply heap_shadow_inverse. }
      { apply withinBounds_true_iff; solve_addr. }
      iIntros "!> (HPC & Hi & Hptr & Hs & HR & HP)". iApply "HΦ". iFrame.
  Qed.

  (** The paint loop stores [s_new] into the shadow entries of a nonempty
      range, touching no memory. The shared resource [R] and the per-cell
      resources [P a] are returned unchanged. Its three instances: the
      same-value store of [malloc] ([↦ₛ L], any claim), the paint of [free]
      ([↦ₛ L], [Claimed ι], with [R := ι ↦st{1} APainting]), and its unpaint
      ([↦ₛ Q], [Unclaimed]).

      The translation and length premises identify the shadow interval, including
      the one-past-end pointer reached by the final LEA but never dereferenced.
      The service layout supplies them when composing the allocator operations. *)

  Lemma allocator_paint_spec
    (s_old s_new : AllocStatus) (rptr rcount : RegName) (E : coPset)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (b e sb se : Addr) (R : iProp Σ) (P : Addr → iProp Σ)
    (φ : language.val griotte_lang → iPropI Σ) :

    let code := allocator_paint_instrs rptr rcount s_new in
    let pc_end := (pc_a ^+ length code)%a in
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a pc_end ->
    disjoint_from_shadow pc_b pc_e ->
    (heap_b <= b /\ b < e /\ e <= heap_e)%a ->
    (shadow_b <= sb /\ sb < se /\ se <= shadow_e)%a ->
    (finz.to_z se - finz.to_z sb = finz.to_z e - finz.to_z b)%Z ->
    (∀ a, (b <= a /\ a < e)%a ->
       heap_to_shadow a = Some (sb ^+ (finz.to_z a - finz.to_z b))%a) ->
    NoDup [cnull; rptr; rcount] ->
    s_old = s_new ∨ allocator_paint_ok R P b e ->

    PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    rptr ↦ᵣ WCap true RW Global shadow_b shadow_e sb ∗
    rcount ↦ᵣ WInt (finz.to_z e - finz.to_z b) ∗
    R ∗
    ([∗ list] a ∈ finz.seq_between b e, a ↦ₛ s_old ∗ P a) ∗
    codefrag_pers pc_a code ∗
    ▷ (PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_end ∗
         rptr ↦ᵣ WCap true RW Global shadow_b shadow_e se ∗
         rcount ↦ᵣ WInt 0 ∗
         R ∗
         ([∗ list] a ∈ finz.seq_between b e, a ↦ₛ s_new ∗ P a) ∗
         codefrag_pers pc_a code
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros code pc_end; subst code pc_end.
    iIntros (Hexec Hpc Hpc_shadow Hheap Hshadow Hlen Htranslate Hregs Hok)
      "(HPC & Hptr & Hcount & HR & Hcells & #Hcode & Hφ)".
    assert (Hrptr : rptr ≠ cnull) by
      (clear -Hregs; repeat rewrite NoDup_cons in Hregs; set_solver).
    assert (Hrcount : rcount ≠ cnull) by
      (clear -Hregs; repeat rewrite NoDup_cons in Hregs; set_solver).
    iLöb as "IH" forall (b sb Hheap Hshadow Hlen Htranslate Hok).
    assert (Hcode_eq : allocator_paint_instrs rptr rcount s_new =
      encodeInstrsW [Store rptr (inl (encodeAllocStatus s_new)) 0;
                    Lea rptr (inl 1%Z);
                    Sub rcount (inr rcount) (inl 1%Z);
                    Jnz (inl (-3)%Z) rcount]) by (destruct s_new; reflexivity).
    rewrite Hcode_eq in Hpc |- *.
    codefrag_facts "Hcode".
    clear Hcode_eq.
    assert (Hbnext : (b + 1)%a = Some (b ^+ 1)%a) by solve_addr.
    assert (Hbnext_e : (b ^+ 1 <= e)%a) by solve_addr.
    iEval (rewrite (finz_seq_between_cons b e (proj1 (proj2 Hheap))) big_sepL_cons)
      in "Hcells".
    iDestruct "Hcells" as "[[Hs HP] Hcells]".
    assert (Hmap : heap_to_shadow b = Some sb).
    { specialize (Htranslate b).
      replace (sb ^+ (b - b))%a with sb in Htranslate by solve_addr.
      apply Htranslate; solve_addr. }
    unfold lword_of_word.

    (* Store rptr (encodeAllocStatus s_new). *)
    iInstrApply "Hcode" (allocator_paint_store_spec _ _ _ _ _ _ _ _ _ _ _ s_old s_new b e sb R P)
      with "[$HPC $Hptr $Hs $HR $HP]"
      as "(HPC & Hptr & Hs & HR & HP)".
    { solve_addr. }
    { solve_addr. }

    (* Lea rptr 1 advances the shadow cursor. *)
    iInstr "Hcode".
    { transitivity (Some (sb ^+ 1)%a); solve_addr. }
    (* Sub rcount rcount 1 consumes one word of the count. *)
    iInstr "Hcode".
    destruct (decide ((b ^+ 1)%a = e)) as [Hlast | Hmore].
    - replace (e - b - 1)%Z with 0%Z by solve_addr.
      (* Jnz .allocator_paint rcount falls through after the last address. *)
      iInstr "Hcode".
      assert (Hslast : (sb ^+ 1)%a = se) by solve_addr.
      rewrite Hslast.
      iApply "Hφ"; iFrame "∗ Hcode".
      rewrite (finz_seq_between_cons b e (proj1 (proj2 Hheap)))
        Hlast finz_seq_between_empty; last solve_addr.
      rewrite big_sepL_cons big_sepL_nil. iFrame "∗".
    - (* Jnz .allocator_paint rcount repeats the loop. *)
      iInstrApply "Hcode" wp_jnz_success_jmp_z with "[$HPC $Hcount]" as "(HPC & Hcount)".
      { apply negb_true_iff, Z.eqb_neq. intros Hzero; cbn in Hzero; solve_addr. }
      { instantiate (1 := pc_a). solve_addr. }
      replace (e - b - 1)%Z with (e - (b ^+ 1)%a)%Z by solve_addr.
      iApply ("IH" $! (b ^+ 1)%a (sb ^+ 1)%a with
        "[] [] [] [] [] HPC Hptr Hcount HR Hcells [Hs HP Hφ]").
      { iPureIntro; solve_addr. }
      { iPureIntro; solve_addr. }
      { iPureIntro; solve_addr. }
      { iPureIntro. intros a Ha_bounds.
        rewrite (Htranslate a); last solve_addr.
        f_equal. clear -Hheap Hshadow Hlen Hbnext Ha_bounds. solve_addr. }
      { iPureIntro. destruct Hok as [-> | Hok]; [by left|right].
        intros a Rs Cs Ha. apply Hok. solve_addr. }
      iNext. iIntros "(HPC & Hptr & Hcount & HR & Hpainted & _)".
      iApply "Hφ"; iFrame "∗ Hcode".
      rewrite (finz_seq_between_cons b e (proj1 (proj2 Hheap))) big_sepL_cons.
      iFrame "∗".
  Qed.

  (** The shadow-store permissions of the paint loop: over unclaimed cells,
      and over the cells claimed by [ι] while [ι] is being painted. *)

  Lemma allocator_paint_ok_unclaimed b e :
    allocator_paint_ok emp (λ a, addr_alloc a Unclaimed) b e.
  Proof.
    intros a Rs Cs _. iIntros "_ HC [_ Hc]".
    iDestruct (addr_alloc_lookup with "HC Hc") as %HCa.
    iPureIntro. by left.
  Qed.

  Lemma allocator_paint_ok_painting ι b e :
    allocator_paint_ok (ι ↦st{1} APainting) (λ a, addr_alloc a (Claimed ι)) b e.
  Proof.
    intros a Rs Cs _. iIntros "HR HC [Htok Hc]".
    iDestruct (reg_lookup_own with "HR Htok") as %(b1 & e1 & γ & HRι).
    iDestruct (addr_alloc_lookup with "HC Hc") as %HCa.
    iPureIntro. right. by exists ι, (b1, e1, γ, APainting).
  Qed.

End AllocatorMacros.

(** Facts on the layout of the allocators that do not depend on their code,
    shared by the specifications of [malloc] and [free]. *)
Section AllocatorLayoutFacts.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}
    {MP : MachineParameters} {layout : allocatorLayout} {layout_wf : allocatorCommonLayoutWf}.

  Lemma allocator_pcc_disjoint_from_shadow :
    disjoint_from_shadow allocator_pcc_b allocator_pcc_e.
  Proof.
    pose proof allocator_common_regions_disjoint as Hregions.
    unfold disjoint_from_shadow.
    rewrite !disjoint_list_cons in Hregions. cbn [union_list] in Hregions.
    set_solver.
  Qed.

  Lemma allocator_cgp_size : (allocator_cgp_b + 1)%a = Some allocator_cgp_e.
  Proof. pose proof allocator_common_size_data as Hsize. by cbn in Hsize. Qed.

  (** The bump slot lies outside the code of the allocator and outside the
      shadow table. *)
  Lemma allocator_cgp_not_in_pcc :
    allocator_cgp_b ∉ finz.seq_between allocator_pcc_b allocator_pcc_e.
  Proof.
    pose proof allocator_common_regions_disjoint as Hregions.
    rewrite !disjoint_list_cons in Hregions. cbn [union_list] in Hregions.
    pose proof allocator_cgp_size.
    assert (allocator_cgp_b ∈ finz.seq_between allocator_cgp_b allocator_cgp_e)
      by (apply elem_of_finz_seq_between; solve_addr).
    set_solver.
  Qed.

  Lemma allocator_cgp_not_shadow : is_shadow_address allocator_cgp_b = false.
  Proof.
    pose proof allocator_cgp_size.
    eapply (disjoint_from_shadow_not_in allocator_cgp_b allocator_cgp_e allocator_cgp_b).
    { pose proof allocator_common_regions_disjoint as Hregions.
      unfold disjoint_from_shadow. rewrite !disjoint_list_cons in Hregions.
      cbn [union_list] in Hregions. set_solver. }
    { apply withinBounds_true_iff. solve_addr. }
  Qed.

  (** The heap root is identifier-less and has authority. *)
  Lemma allocator_heap_root_authority next :
    has_authority (WCap true RW Global heap_b heap_e next).
  Proof. pose proof heap_valid. apply has_authority_heap_cap; solve_addr. Qed.

  (** The imported capabilities carry no heap authority. *)
  Lemma allocator_shadow_import_not_heap :
    is_heap_cap (WCap true RW Global shadow_b shadow_e shadow_b) = false.
  Proof.
    rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=.
    destruct (is_heap_address shadow_b) eqn:Hheap; last reflexivity.
    exfalso. unfold is_heap_address in Hheap.
    apply withinBounds_true_iff in Hheap.
    pose proof heap_shadow_disjoint as Hd.
    rewrite /disjoint_from_shadow elem_of_disjoint in Hd.
    apply (Hd shadow_b); apply elem_of_finz_seq_between; first exact Hheap.
    pose proof shadow_valid; solve_addr.
  Qed.

  Lemma allocator_revoker_import_not_heap : is_heap_cap allocator_revoker_cap = false.
  Proof.
    rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=.
    by rewrite revoker_not_heap_address.
  Qed.

  (** The heap translates affinely to the shadow table. *)
  Lemma allocator_heap_to_shadow x :
    (heap_b <= x /\ x < heap_e)%a ->
    heap_to_shadow x = Some (shadow_b ^+ (x - heap_b))%a.
  Proof.
    intros Hx. pose proof heap_shadow_same_size. pose proof heap_valid.
    rewrite allocator_common_translation_affine /translate_region.
    assert (withinBounds heap_b heap_e x = true) as ->
      by (apply withinBounds_true_iff; solve_addr).
    solve_addr.
  Qed.

  (** The allocator's three imports, as separate words. *)
  Lemma allocator_imports_split :
    [[allocator_pcc_b, allocator_code_b]] ↦ₐ [[lword_of_word <$> allocator_imports]] ⊣⊢
    (allocator_pcc_b ^+ allocator_shadow_import_off)%a ↦ₐ
      WCap true RW Global shadow_b shadow_e shadow_b ∗
    (allocator_pcc_b ^+ 1)%a ↦ₐ
      WSealRange true (false, true) Global AllocOtype (AllocOtype ^+ 1)%ot AllocOtype ∗
    (allocator_pcc_b ^+ allocator_revoker_import_off)%a ↦ₐ allocator_revoker_cap.
  Proof.
    pose proof allocator_common_size_imports as Hsize.
    rewrite allocator_imports_length in Hsize.
    rewrite /allocator_imports !fmap_cons fmap_nil.
    rewrite (region_pointsto_cons allocator_pcc_b (allocator_pcc_b ^+ 1)%a);
      [|solve_addr|solve_addr].
    rewrite (region_pointsto_cons (allocator_pcc_b ^+ 1)%a (allocator_pcc_b ^+ 2)%a);
      [|solve_addr|solve_addr].
    rewrite (region_pointsto_cons (allocator_pcc_b ^+ 2)%a allocator_code_b);
      [|solve_addr|solve_addr].
    rewrite /region_pointsto finz_seq_between_empty; last solve_addr.
    rewrite /allocator_shadow_import_off /allocator_revoker_import_off.
    assert ((allocator_pcc_b ^+ 0)%a = allocator_pcc_b) as -> by solve_addr.
    iSplit; [iIntros "($ & $ & $ & _)" | iIntros "($ & $ & $)"]; done.
  Qed.

  (** The allocator's three imports, as separate persistent words. *)
  Lemma allocator_imports_split_pers :
    [[allocator_pcc_b, allocator_code_b]] ↦ₐ□ [[lword_of_word <$> allocator_imports]] ⊢
    (allocator_pcc_b ^+ allocator_shadow_import_off)%a ↦ₐ□
      WCap true RW Global shadow_b shadow_e shadow_b ∗
    (allocator_pcc_b ^+ 1)%a ↦ₐ□
      WSealRange true (false, true) Global AllocOtype (AllocOtype ^+ 1)%ot AllocOtype ∗
    (allocator_pcc_b ^+ allocator_revoker_import_off)%a ↦ₐ□ allocator_revoker_cap.
  Proof.
    pose proof allocator_common_size_imports as Hsize.
    rewrite allocator_imports_length in Hsize.
    rewrite /region_pointsto_pers /allocator_imports !fmap_cons fmap_nil.
    rewrite (finz_seq_between_cons allocator_pcc_b); last solve_addr.
    rewrite (finz_seq_between_cons (allocator_pcc_b ^+ 1)%a); last solve_addr.
    rewrite (finz_seq_between_cons (allocator_pcc_b ^+ 1 ^+ 1)%a); last solve_addr.
    rewrite /allocator_shadow_import_off /allocator_revoker_import_off.
    assert ((allocator_pcc_b ^+ 0)%a = allocator_pcc_b) as -> by solve_addr.
    assert ((allocator_pcc_b ^+ 1 ^+ 1)%a = (allocator_pcc_b ^+ 2)%a) as -> by solve_addr.
    iIntros "($ & $ & $ & _)".
  Qed.

  (** The code of the allocator: [malloc], then [free]. *)
  Lemma allocator_code_b_malloc : allocator_code_b = allocator_malloc_pcc_addr.
  Proof.
    pose proof allocator_common_size_imports as Hsize.
    rewrite allocator_imports_length in Hsize.
    unfold allocator_malloc_pcc_addr, allocator_malloc_pcc_off in *.
    solve_addr.
  Qed.

End AllocatorLayoutFacts.
