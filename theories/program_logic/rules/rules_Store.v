From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base.

Section griotte_lang_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : griotte_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : griotte_lang.val.
  Implicit Types w : LWord.
  Implicit Types reg : gmap RegName LWord.
  Implicit Types ms : gmap Addr LWord.

  (* The addressing capability's identifier does not matter: only its
     physical word is read. *)
  Definition reg_allows_store_imm (regs : LReg) (r : RegName) (imm : Z) p g b e a ea :=
    lw <$> regs !!ₗ r = Some (Cap p g b e a) ∧
    (a + imm)%a = Some ea ∧ writeAllowed p = true ∧ withinBounds b e ea = true.

  (* Store relations carry the instruction's immediate and both heaps. *)
  Inductive Store_failure
      (lpc : LWord) (regs : LReg) (r1 : RegName) (r2 : Z + RegName) (imm : Z)
      (mem : LMem) (dw : deref_witness) : Prop :=
  | Store_fail_const w :
      regs !!ₗ r1 = Some w -> is_cap w.(lw) = false ->
      Store_failure lpc regs r1 r2 imm mem dw
  | Store_fail_tag p g b e a :
      lw <$> regs !!ₗ r1 = Some (Cap⁻ p g b e a) ->
      Store_failure lpc regs r1 r2 imm mem dw
  | Store_fail_addr p g b e a :
      lw <$> regs !!ₗ r1 = Some (Cap p g b e a) ->
      (a + imm)%a = None ->
      Store_failure lpc regs r1 r2 imm mem dw
  | Store_fail_bounds p g b e a ea :
      lw <$> regs !!ₗ r1 = Some (Cap p g b e a) ->
      (a + imm)%a = Some ea ->
      (writeAllowed p = false \/ withinBounds b e ea = false) ->
      Store_failure lpc regs r1 r2 imm mem dw
  | Store_fail_invalid_PC :
      incrementPC lpc = None ->
      Store_failure lpc regs r1 r2 imm mem dw
  (* A destination with an identifier not covered by the witness may have
     been revoked: its physical copy is untagged. *)
  | Store_fail_revoked p g b e a π :
      regs !!ₗ r1 = Some (Cap p g b e a @@? π) ->
      π ≠ deref_id dw ->
      Store_failure lpc regs r1 r2 imm mem dw
  (* A store to an address absent from memory faults, after the capability
     checks. *)
  | Store_fail_unmapped p g b e a ea :
      lw <$> regs !!ₗ r1 = Some (Cap p g b e a) ->
      (a + imm)%a = Some ea ->
      writeAllowed p = true -> withinBounds b e ea = true ->
      is_shadow_address ea = false -> is_revoker_address ea = false ->
      is_time_device_address ea = false ->
      mem !! ea = None ->
      Store_failure lpc regs r1 r2 imm mem dw
  (* A store to [mtime] fails. *)
  | Store_fail_timedev p g b e a ea storev :
      lw <$> regs !!ₗ r1 = Some (Cap p g b e a) ->
      (a + imm)%a = Some ea ->
      is_time_device_address ea = true ->
      mem !! ea = None ->
      lword_of_argument regs r2 = Some storev ->
      ea = mtime_addr ->
      Store_failure lpc regs r1 r2 imm mem dw.

  Inductive Store_spec
      (lpc : LWord) (regs : LReg) (r1 : RegName) (r2 : Z + RegName) (imm : Z)
      (lpc' : LWord) (mem mem' : LMem)
      (shadow shadow' : ShadowTbl) (dw : deref_witness) : griotte_lang.val -> Prop :=
  | Store_spec_success p g b e a ea storev oldv :
      lword_of_argument regs r2 = Some storev ->
      reg_allows_store_imm regs r1 imm p g b e a ea ->
      is_shadow_address ea = false ->
      mem !! ea = Some oldv ->
      mem' = <[ea := lstore_word p storev]> mem ->
      shadow' = shadow ->
      incrementPC lpc = Some lpc' ->
      Store_spec lpc regs r1 r2 imm lpc' mem mem' shadow shadow' dw griotte_lang.NextIV
  | Store_spec_success_shadow p g b e a ea heap_a storev old_status :
      lword_of_argument regs r2 = Some storev ->
      reg_allows_store_imm regs r1 imm p g b e a ea ->
      is_shadow_address ea = true ->
      shadow_to_heap ea = Some heap_a ->
      shadow !! heap_a = Some old_status ->
      mem' = mem ->
      shadow' = <[heap_a := decodeAllocStatus (word_to_bits storev.(lw))]> shadow ->
      incrementPC lpc = Some lpc' ->
      Store_spec lpc regs r1 r2 imm lpc' mem mem' shadow shadow' dw griotte_lang.NextIV
  (* A store to [mtimecmp] changes neither memory nor the shadow table: the
     logical state does not record the time devices. *)
  | Store_spec_success_timedev p g b e a ea storev :
      lword_of_argument regs r2 = Some storev ->
      reg_allows_store_imm regs r1 imm p g b e a ea ->
      is_time_device_address ea = true ->
      ea = mtimecmp_addr ->
      mem !! ea = None ->
      mem' = mem ->
      shadow' = shadow ->
      incrementPC lpc = Some lpc' ->
      Store_spec lpc regs r1 r2 imm lpc' mem mem' shadow shadow' dw griotte_lang.NextIV
  | Store_spec_failure_store :
      mem' = mem -> shadow' = shadow ->
      Store_failure lpc regs r1 r2 imm mem dw ->
      lpc' = lpc ->
      Store_spec lpc regs r1 r2 imm lpc' mem mem' shadow shadow' dw griotte_lang.FaultedV.

  Lemma Store_failure_impossible lpc regs r1 (r2 : Z + RegName) imm mem dw p g b e a ea :
    lw <$> regs !!ₗ r1 = Some (Cap p g b e a) ->
    (∀ v : LWord, regs !!ₗ r1 = Some v → v.(lprov) = deref_id dw) ->
    (a + imm)%a = Some ea ->
    writeAllowed p = true -> withinBounds b e ea = true ->
    is_shadow_address ea = false ->
    is_Some (mem !! ea) ->
    incrementPC lpc ≠ None ->
    Store_failure lpc regs r1 r2 imm mem dw -> False.
  Proof.
    intros Hreg Hid Hadd Hwa Hbounds Hshadow Hmem Hpc Hfail.
    destruct Hfail as [w0 Hw0 Hcap| ? ? ? ? ? H | ? ? ? ? ? H H0 | ? ? ? ? ? ? H H0 H1 | H
                      | ? ? ? ? ? π H H0
                      | p1 g1 b1 e1 a1 ea1 Hreg1 Hadd1 _ _ _ _ _ Hnone
                      | p1 g1 b1 e1 a1 ea1 storev1 Hreg1 Hadd1 _ Hnone _ _].
    - rewrite Hw0 in Hreg. destruct w0 as [w0 ?]. by simplify_eq/=.
    - rewrite Hreg in H. inversion H.
    - rewrite Hreg in H. inversion H; subst. congruence.
    - rewrite Hreg in H. inversion H; subst.
      rewrite Hadd in H0. inversion H0; subst.
      destruct H1; congruence.
    - congruence.
    - by apply H0, (Hid _ H).
    - rewrite Hreg in Hreg1. simplify_eq.
      destruct Hmem as [v Hv]. congruence.
    - rewrite Hreg in Hreg1. simplify_eq.
      destruct Hmem as [v Hv]. congruence.
  Qed.

  (** A shadow store keeps erasure if it stores the cell's current bit, or if
      the caller holds the cell's permission: the cell is unclaimed, or
      claimed by a painting allocation. Heap roots are never painted. *)
  Definition shadow_store_perm (a : Addr) : iProp Σ :=
    addr_alloc a Unclaimed ∨ ∃ ι q, addr_alloc a (Claimed ι) ∗ ι ↦st{q} APainting.

  Definition shadow_store_allowed (sperm : gset Addr) (shadow : ShadowTbl)
      (a : Addr) (s : AllocStatus) : Prop :=
    shadow !! a = Some s ∨ a ∈ sperm.

  Lemma shadow_store_perms_ok (sperm : gset Addr) R C st a s :
    a ∈ sperm →
    reg_auth R -∗ addr_alloc_auth C -∗ ([∗ set] a ∈ sperm, shadow_store_perm a) -∗
    ⌜shadow_store_ok R C st a s⌝.
  Proof.
    iIntros (Ha) "HR HC Hperms".
    iDestruct (big_sepS_elem_of with "Hperms") as "[Hu | (%ι & %q & Hc & Htok)]"; first exact Ha.
    - iDestruct (addr_alloc_lookup with "HC Hu") as %Hc. iPureIntro. right. by left.
    - iDestruct (addr_alloc_lookup with "HC Hc") as %Hc.
      iDestruct (reg_lookup_own with "HR Htok") as %(b & e & γ & HRι).
      iPureIntro. right. right. exists ι, (b, e, γ, APainting). done.
  Qed.

  Definition allow_store_map_or_true_imm
    (r1 : RegName) (r2 : Z + RegName) (imm : Z) (regs : LReg) (mem : LMem):=
    ∃ t p g b e a storev,
      read_reg_inr regs r1 t p g b e a ∧ lword_of_argument regs r2 = Some storev ∧
      match (a + imm)%a with
      | None => True
      | Some ea => if decide (reg_allows_store_imm regs r1 imm p g b e a ea) then
        ∃ w, mem !! ea = Some w
      else True
      end.

  Lemma allow_store_implies_storev_imm:
    ∀ (r1 : RegName)(r2 : Z + RegName) (mem0 : LMem) (r : LReg)
      (p : Perm) (g : Locality) (b e a ea : Addr) (imm : Z) storev,
      allow_store_map_or_true_imm r1 r2 imm r mem0
      → lw <$> r !!ₗ r1 = Some (Cap p g b e a)
      → lword_of_argument r r2 = Some storev
      → writeAllowed p = true
      → (a + imm)%a = Some ea
      → withinBounds b e ea = true
      → ∃ (storev : LWord),
          mem0 !! ea = Some storev.
  Proof.
    intros r1 r2 mem0 r p g b e a ea imm storev HaStore Hr2v Hwoa Hwa Hadd Hwb.
    unfold allow_store_map_or_true_imm, read_reg_inr in HaStore.
    destruct HaStore as (t&?&?&?&?&?&?&Hrinr&Hwo&Hmem).
    pose proof (llookup_reg_cap _ _ _ _ _ _ _ _ Hr2v) as (Hne & π & Hr1).
    rewrite /read_reg_inr Hr1 in Hrinr. simplify_eq.
    unfold reg_allows_store_imm in Hmem. rewrite Hadd in Hmem.
    case_decide as HAL.
    - auto.
    - exfalso. apply HAL. repeat split; auto.
  Qed.

  Lemma mem_eq_implies_allow_store_map_imm:
    ∀ (regs : LReg)(mem : LMem)(r1 : RegName)(r2 : Z + RegName)(w storev : LWord) p g b e a ea (imm : Z),
      (a + imm)%a = Some ea
      → mem = <[ea:=w]> ∅
      → lw <$> regs !!ₗ r1 = Some (Cap p g b e a)
      → lword_of_argument regs r2 = Some storev
      → allow_store_map_or_true_imm r1 r2 imm regs mem.
  Proof.
    intros regs mem r1 r2 w storev p g b e a ea imm Hadd Hmem Hrr2 Hsv.
    pose proof (llookup_reg_cap _ _ _ _ _ _ _ _ Hrr2) as (Hne & π & Hr1).
    exists true,p,g,b,e,a,storev. split; [|split; first done].
    - unfold read_reg_inr. by rewrite Hr1.
    - unfold reg_allows_store_imm. rewrite Hadd. case_decide; last done.
      exists w. subst mem. by rewrite lookup_insert_eq.
  Qed.

  Definition reg_allows_store (regs : LReg) (r : RegName) p g b e a :=
    lw <$> regs !!ₗ r = Some (Cap p g b e a) ∧
    writeAllowed p = true ∧ withinBounds b e a = true.

  Definition allow_store_mem_or_shadow
    (r1 : RegName) (r2 : Z + RegName) (regs : LReg)
    (mem : LMem) (shadow : ShadowTbl) (sperm : gset Addr) :=
    ∀ p g b e a storev,
      reg_allows_store regs r1 p g b e a →
      lword_of_argument regs r2 = Some storev →
      if is_shadow_address a then
        ∃ heap_a, shadow_to_heap a = Some heap_a ∧ is_Some (shadow !! heap_a) ∧
          shadow_store_allowed sperm shadow heap_a
            (decodeAllocStatus (word_to_bits storev.(lw)))
      else if is_time_device_address a then True else is_Some (mem !! a).

  Definition allow_store_mem_or_shadow_imm
    (r1 : RegName) (r2 : Z + RegName) (imm : Z) (regs : LReg)
    (mem : LMem) (shadow : ShadowTbl) (sperm : gset Addr) :=
    forall p g b e a ea storev,
      reg_allows_store_imm regs r1 imm p g b e a ea ->
      lword_of_argument regs r2 = Some storev ->
      if is_shadow_address ea then
        exists heap_a, shadow_to_heap ea = Some heap_a ∧
          is_Some (shadow !! heap_a) ∧
          shadow_store_allowed sperm shadow heap_a
            (decodeAllocStatus (word_to_bits storev.(lw)))
      else if is_time_device_address ea then True else is_Some (mem !! ea).


  (** A failing store leaves memory and the shadow table unchanged. *)
  Lemma Store_spec_fail lpc regs r1 (r2 : Z + RegName) imm mem shadow dw :
    Store_failure lpc regs r1 r2 imm mem dw →
    Store_spec lpc regs r1 r2 imm lpc mem mem shadow shadow dw griotte_lang.FaultedV.
  Proof. intros. by apply Store_spec_failure_store. Qed.

  (** The status-independent part of [shadow_store_ok]: the cell is unclaimed,
      or claimed by a painting allocation. *)
  Definition shadow_perm_ok (R : RegState) (C : gmap Addr AddrClaim) (a : Addr) : Prop :=
    C !! a = Some Unclaimed ∨
    (∃ ι x, C !! a = Some (Claimed ι) ∧ R !! ι = Some x ∧ re_status x = APainting).

  (** [wp_store_shadow_imm] over any per-address resource [Pm] that justifies
      the shadow store, returned unchanged. *)
  Lemma wp_store_shadow_imm_res_gen Ep
     pc_p pc_g pc_b pc_e pc_a pc_π
     r1 (r2 : Z + RegName) (imm : Z) w mem regs shadow (sperm : gset Addr)
     (Pm : Addr → iProp Σ) (fetch_in_mem : bool) dq dw :
   (∀ R C a, a ∈ sperm →
      reg_auth R -∗ addr_alloc_auth C -∗ ([∗ set] a ∈ sperm, Pm a) -∗
      ⌜shadow_perm_ok R C a⌝) →
   decodeInstrW w.(lw) = Store r1 r2 imm →
   isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Store r1 r2 imm) ⊆ dom regs →
   (if fetch_in_mem then mem !! pc_a = Some w else True) →
   allow_store_mem_or_shadow_imm r1 r2 imm regs mem shadow sperm →

   {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
       (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
       (▷ if fetch_in_mem then emp else pc_a ↦ₐ{dq} w) ∗
       (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ revoked) ∗
       ([∗ set] a ∈ sperm, Pm a) ∗
       deref_witness_res dw ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ lpc' mem' shadow' retv, RET tval_of_val retv;
       ⌜ Store_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm lpc' mem mem' shadow shadow' dw retv⌝ ∗
         PC ↦ₚ lpc' ∗
         ([∗ map] a↦w ∈ mem', a ↦ₐ w) ∗
         (if fetch_in_mem then emp else pc_a ↦ₐ{dq} w) ∗
         ([∗ map] a↦revoked ∈ shadow', a ↦ₛ revoked) ∗
         ([∗ set] a ∈ sperm, Pm a) ∗
         deref_witness_res dw ∗
         [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
   Proof.
     iIntros (HPm Hinstr Hvpc Dregs Hmem_pc HaStore φ) "(>HPC & >Hmem & >Hfetch & >Hshadow & Hperms & Hdw & >Hmap) Hφ".
     (* The instruction word is taken out of the memory map, or is the
        separate fragment, for the step. *)
     iAssert (pc_a ↦ₐ{if fetch_in_mem then DfracOwn 1 else dq} w ∗
              (pc_a ↦ₐ{if fetch_in_mem then DfracOwn 1 else dq} w -∗
               ([∗ map] a↦w ∈ mem, a ↦ₐ w) ∗ (if fetch_in_mem then emp else pc_a ↦ₐ{dq} w)))%I
       with "[Hmem Hfetch]" as "[Hpc_a Hback]".
     { destruct fetch_in_mem.
       - iDestruct (big_sepM_delete _ _ pc_a with "Hmem") as "[$ Hmem]"; first done.
         iIntros "Hpc_a". iSplitL; last done.
         iApply (big_sepM_delete _ _ pc_a); first done. iFrame.
       - iFrame "Hfetch Hmem". by iIntros "$". }
     iApply (wp_instr_step_nosw with "HPC Hpc_a Hmap"); [rewrite Hinstr; by apply sw_of_none|done|].
     iNext; iIntros (r sr m st td lreg lsreg lmem R C c σ2) "@".
     iDestruct ("Hback" with "Hpc_a") as "[Hmem Hfetch]".
     iDestruct (deref_witness_lookup with "HR Hdw") as %Hdw.
     iDestruct (gen_heap_valid_inclSepM with "Hm Hmem") as %Hlmem.
     iDestruct (gen_heap_valid_inclSepM with "Hst Hshadow") as %Hshadow_incl.
     pose proof (er_mmio _ _ _ _ _ _ _ Her) as Hmmio; cbn in Hmmio.
     specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri. unfold regs_of, operands_of in Hri.
     odestruct (Hri r1) as [r1v [Hr1l _] ]; first by set_solver+.
     rewrite Hinstr in Hstep.
     destruct (llookup_reg_phys _ _ _ _ _ Hregs Hr1l) as (s1 & Hr1 & Hrel1).
     rewrite /exec /= Hr1 /= in Hstep.
     destruct (lword_of_argument regs r2) as [ storev | ] eqn:HSV.
     2: {
       destruct r2 as [z | r2].
       - cbn in HSV; inversion HSV.
       - destruct (Hri r2) as [r0v [Hr0 _] ]; first by set_solver+.
         cbn in HSV. rewrite Hr0 in HSV. inversion HSV.
     }
     destruct (lword_of_argument_phys _ _ _ _ _ Hregs HSV) as (sv & HSV' & Hrelv).
     rewrite HSV' in Hstep. cbn in Hstep.
     assert (reg_word_ok R C storev) as Hstore_ok by by eapply erasure_lword_of_argument_word.
     destruct (is_cap r1v.(lw)) eqn:Hr1v.
     2: {
       assert ((Faulted, (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td)) = (c, σ2)) as Hstep'.
       { unfold is_cap in Hr1v. destruct r1v as [r1v ?]. cbn in *.
         destruct_word r1v; by simplify_pair_eq. }
       instr_fail Hstep'. apply Store_spec_fail. by eapply Store_fail_const.
     }
     destruct r1v as [ [ | [t p g b e a | ] | | ] π1]; try inversion Hr1v. clear Hr1v. cbn in Hstep.
     destruct t.
     2: { rewrite ?andb_false_r in Hstep.
          instr_fail Hstep. apply Store_spec_fail. eapply Store_fail_tag. by rewrite Hr1l. }
     destruct s1.
     2: { (* The physical copy of the destination is untagged. *)
       cbn in Hstep. instr_fail Hstep. apply Store_spec_fail.
       destruct (decide (π1 = deref_id dw)) as [Hπ|Hπ]; last by eapply Store_fail_revoked.
       destruct (a + imm)%a as [ea|] eqn:Hadd.
       2: by eapply Store_fail_addr; [rewrite Hr1l | done].
       destruct (withinBounds b e ea) eqn:Hwb.
       2: by eapply Store_fail_bounds; [rewrite Hr1l | done | right].
       (* A stripped destination under its witness is a heap capability
          without authority: its bounds are empty. *)
       exfalso.
       destruct Hrel1 as [ [Heq | [_ [ [Hst _] | [Hna [base Hh] ] ] ] ] _]; cbn in *; try discriminate.
       { by apply (deref_witness_not_stale R dw (Cap p g b e a @@? π1)). }
       assert (is_heap_address b = true) as Hbh.
       { rewrite /heap_cap_base /= in Hh. by destruct (is_heap_address b). }
       apply withinBounds_true_iff in Hwb. apply Hna. split; first done. exists b.
       apply heap_authority_base_memory_cap_bounds. exists e. split; first done.
       split; [solve_addr | done]. }
     cbn in Hstep.
     destruct (a + imm)%a as [ea|] eqn:Hadd.
     2: { instr_fail Hstep. apply Store_spec_fail. eapply Store_fail_addr; last done. by rewrite Hr1l. }
     cbn in Hstep.
     destruct (writeAllowed p && withinBounds b e ea) eqn:HWA.
     2 : {
       apply andb_false_iff in HWA.
       instr_fail Hstep. apply Store_spec_fail. eapply Store_fail_bounds; eauto. by rewrite Hr1l.
     }
     apply andb_true_iff in HWA; destruct HWA as (Hwa & Hwb).
     assert (Hallow : reg_allows_store_imm regs r1 imm p g b e a ea)
       by (repeat split; auto; by rewrite Hr1l).
     specialize (HaStore p g b e a ea storev Hallow HSV).
     rewrite /is_mmio_address /mmio_store /shadow_store in Hstep.
     destruct (is_shadow_address ea) eqn:Hshadow.
     - destruct (proj2 (shadow_to_heap_domain ea) Hshadow) as [heap_a Htranslate].
       rewrite Htranslate /= word_to_bits_and_tag in Hstep.
       set (status := decodeAllocStatus (word_to_bits storev.(lw))).
       destruct HaStore as (heap_a' & Htranslate' & [old_revoked Hshadowa] & Hallowed).
       assert (heap_a' = heap_a) as -> by congruence.
       assert (st !! heap_a = Some old_revoked) as Hsta.
       { eapply lookup_weaken; [exact Hshadowa|exact Hshadow_incl]. }
       iAssert (⌜shadow_store_ok R C st heap_a status⌝)%I as %Hsok.
       { destruct Hallowed as [Hsame | Hin].
         - iPureIntro. left. by eapply lookup_weaken.
         - iDestruct (HPm with "HR HC Hperms") as %Hok; first done.
           iPureIntro. by right. }
       pose proof (erasure_shadow_store _ _ _ _ _ _ _ _ _ _ _ _ heap_a status Her ltac:(eauto) Hsok) as Her1.
       rewrite /set_shadowtbl /= in Hstep.
       destruct (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π)) as [lpc'|] eqn:Hregs'.
       2: {
         pose proof Hregs' as Ha'. eapply incrementPC_None_inv in Ha'; [|reflexivity].
         unfold nextPC, advancePC in Hstep; cbn in Hstep; rewrite Ha' in Hstep.
         instr_fail Hstep. apply Store_spec_fail. by apply Store_fail_invalid_PC. }
       destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hregs') as (pc'' & Hu & Her2).
       pose proof Hregs' as Ha'.
       apply incrementPC_Some_inv in Ha' as (t' & p' & g' & b' & e' & a' & a'1 & π' & Heq & Ha'1 & ->).
       injection Heq as <- <- <- <- <- <- <-.
       rewrite /nextPC /advancePC /= Ha'1 /update_pcc in Hu. simplify_eq.
       unfold nextPC, advancePC in Hstep; cbn in Hstep; rewrite Ha'1 in Hstep.
       simplify_pair_eq. cbn.
       iDestruct (big_sepM_delete _ _ heap_a with "Hshadow") as "[Ha Hshadow]"; first exact Hshadowa.
       iMod (gen_heap_update with "Hst Ha") as "[Hst Ha]".
       iDestruct (big_sepM_insert _ _ heap_a with "[$Hshadow $Ha]") as "Hshadow".
       { apply lookup_delete_eq. }
       iEval (rewrite insert_delete_eq) in "Hshadow".
       iMod (PC_update _ _ (Cap pc_p pc_g pc_b pc_e a'1 @@? pc_π) with "HPCa HPC") as "[HPCa HPC]".
       iModIntro. iSplitR; first (iPureIntro; done).
       iSplitR "Hφ HPC Hmem Hfetch Hshadow Hperms Hdw Hmap".
       { iApply (SI_close _ _ _ _ _ _ _ Her2 with "HPCa Hr Hsr Hm Hst HR HC"). }
       iApply ("Hφ" $! _ _ _ griotte_lang.NextIV). iFrame.
       iPureIntro. eapply Store_spec_success_shadow; eauto.
     - destruct (is_time_device_address ea) eqn:Htdev.
       + rewrite (time_device_not_revoker_address _ Htdev) /= in Hstep.
         assert (mem !! ea = None) as Hnone.
         { destruct (mem !! ea) as [v|] eqn:Hv; last done.
           assert (lmem !! ea = Some v) as Hlv by by eapply lookup_weaken.
           destruct (erasure_lookup_mem _ _ _ _ _ _ _ _ _ Her Hlv) as (pv & Hpv & _).
           by rewrite (mem_avoids_mmio_not_time_device _ _ _ Hmmio Hpv) in Htdev. }
         destruct (time_dev_store td ea (and_tag sv (lw storev))) as [td'|] eqn:Htds.
         2: {
           cbn in Hstep. instr_fail Hstep. apply Store_spec_fail.
           eapply Store_fail_timedev; [by rewrite Hr1l|done|done|done|exact HSV|].
           rewrite /time_dev_store in Htds. case_bool_decide as Hmtimecmp; first done.
           by apply is_time_device_address_spec in Htdev as [|]. }
         (* A store to [mtimecmp] succeeds. *)
         rewrite /time_dev_store in Htds.
         case_bool_decide as Hmtimecmp; last done. simplify_eq.
         pose proof (erasure_set_timedevs _ _ _ _ _ _ _
           (set_mtimecmp (word_to_bits (and_tag sv (lw storev))) td) Her) as Her1.
         rewrite /set_timedevs /= in Hstep Her1.
         destruct (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π)) as [lpc'|] eqn:Hregs'.
         2: {
           pose proof Hregs' as Ha'. eapply incrementPC_None_inv in Ha'; [|reflexivity].
           unfold nextPC, advancePC in Hstep; cbn in Hstep; rewrite Ha' in Hstep.
           instr_fail Hstep. apply Store_spec_fail. by apply Store_fail_invalid_PC. }
         destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hregs') as (pc'' & Hu & Her2).
         pose proof Hregs' as Ha'.
         apply incrementPC_Some_inv in Ha' as (t' & p' & g' & b' & e' & a' & a'1 & π' & Heq & Ha'1 & ->).
         injection Heq as <- <- <- <- <- <- <-.
         rewrite /nextPC /advancePC /= Ha'1 /update_pcc in Hu. simplify_eq.
         unfold nextPC, advancePC in Hstep; cbn in Hstep; rewrite Ha'1 in Hstep.
         simplify_pair_eq. cbn.
         iMod (PC_update _ _ (Cap pc_p pc_g pc_b pc_e a'1 @@? pc_π) with "HPCa HPC") as "[HPCa HPC]".
         iModIntro. iSplitR; first (iPureIntro; done).
         iSplitR "Hφ HPC Hmem Hfetch Hshadow Hperms Hdw Hmap".
         { iApply (SI_close _ _ _ _ _ _ _ Her2 with "HPCa Hr Hsr Hm Hst HR HC"). }
         iApply ("Hφ" $! _ _ _ griotte_lang.NextIV). iFrame.
         iPureIntro. eapply Store_spec_success_timedev; eauto.
       + destruct HaStore as [oldv Hmema].
         assert (lmem !! ea = Some oldv) as Hlmea by by eapply lookup_weaken.
         destruct (erasure_lookup_mem _ _ _ _ _ _ _ _ _ Her Hlmea) as (pwea & Hmea & _).
         rewrite (mem_avoids_mmio_not_revoker _ _ _ Hmmio Hmea) Hmea in Hstep.
         rewrite /update_mem /= in Hstep.
         pose proof (erasure_store _ _ _ _ _ _ _ _ _ _ _ _ ea (lstore_word p storev) _ _ Her Hlmea
           (reg_phys_mem_word_ok _ _ _ _ (reg_word_ok_lstore_word _ _ p _ Hstore_ok)
              (reg_phys_lstore_word _ p _ _ Hrelv))) as Her1.
         destruct (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π)) as [lpc'|] eqn:Hregs'.
         2: {
           pose proof Hregs' as Ha'. eapply incrementPC_None_inv in Ha'; [|reflexivity].
           unfold nextPC, advancePC in Hstep; cbn in Hstep; rewrite Ha' in Hstep.
           instr_fail Hstep. apply Store_spec_fail. by apply Store_fail_invalid_PC. }
         destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hregs') as (pc'' & Hu & Her2).
         pose proof Hregs' as Ha'.
         apply incrementPC_Some_inv in Ha' as (t' & p' & g' & b' & e' & a' & a'1 & π' & Heq & Ha'1 & ->).
         injection Heq as <- <- <- <- <- <- <-.
         rewrite /nextPC /advancePC /= Ha'1 /update_pcc in Hu. simplify_eq.
         unfold nextPC, advancePC in Hstep; cbn in Hstep; rewrite Ha'1 in Hstep.
         simplify_pair_eq. cbn.
         iMod ((gen_heap_update_inSepM _ _ ea) with "Hm Hmem") as "[Hm Hmem]"; eauto.
         iMod (PC_update _ _ (Cap pc_p pc_g pc_b pc_e a'1 @@? pc_π) with "HPCa HPC") as "[HPCa HPC]".
         iModIntro. iSplitR; first (iPureIntro; done).
         iSplitR "Hφ HPC Hmem Hfetch Hshadow Hperms Hdw Hmap".
         { iApply (SI_close _ _ _ _ _ _ _ Her2 with "HPCa Hr Hsr Hm Hst HR HC"). }
         iApply ("Hφ" $! _ _ _ griotte_lang.NextIV). iFrame.
         iPureIntro. eapply Store_spec_success; eauto.
   Qed.

   Lemma wp_store_shadow_imm_gen Ep
     pc_p pc_g pc_b pc_e pc_a pc_π
     r1 (r2 : Z + RegName) (imm : Z) w mem regs shadow (sperm : gset Addr)
     (fetch_in_mem : bool) dq dw :
   decodeInstrW w.(lw) = Store r1 r2 imm →
   isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Store r1 r2 imm) ⊆ dom regs →
   (if fetch_in_mem then mem !! pc_a = Some w else True) →
   allow_store_mem_or_shadow_imm r1 r2 imm regs mem shadow sperm →

   {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
       (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
       (▷ if fetch_in_mem then emp else pc_a ↦ₐ{dq} w) ∗
       (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ revoked) ∗
       ([∗ set] a ∈ sperm, shadow_store_perm a) ∗
       deref_witness_res dw ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ lpc' mem' shadow' retv, RET tval_of_val retv;
       ⌜ Store_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm lpc' mem mem' shadow shadow' dw retv⌝ ∗
         PC ↦ₚ lpc' ∗
         ([∗ map] a↦w ∈ mem', a ↦ₐ w) ∗
         (if fetch_in_mem then emp else pc_a ↦ₐ{dq} w) ∗
         ([∗ map] a↦revoked ∈ shadow', a ↦ₛ revoked) ∗
         ([∗ set] a ∈ sperm, shadow_store_perm a) ∗
         deref_witness_res dw ∗
         [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
   Proof.
     intros. apply wp_store_shadow_imm_res_gen; last done; try done.
     iIntros (R C a Ha) "HR HC Hperms".
     iDestruct (shadow_store_perms_ok _ _ _ ∅ a (decodeAllocStatus 0) Ha with "HR HC Hperms")
       as %[Hst | Hok]; [by rewrite lookup_empty in Hst | done].
   Qed.

   Lemma wp_store_shadow_imm Ep
     pc_p pc_g pc_b pc_e pc_a pc_π
     r1 (r2 : Z + RegName) (imm : Z) w mem regs shadow (sperm : gset Addr) dw :
   decodeInstrW w.(lw) = Store r1 r2 imm →
   isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Store r1 r2 imm) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_store_mem_or_shadow_imm r1 r2 imm regs mem shadow sperm →

   {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
       (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
       (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ revoked) ∗
       ([∗ set] a ∈ sperm, shadow_store_perm a) ∗
       deref_witness_res dw ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ lpc' mem' shadow' retv, RET tval_of_val retv;
       ⌜ Store_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm lpc' mem mem' shadow shadow' dw retv⌝ ∗
         PC ↦ₚ lpc' ∗
         ([∗ map] a↦w ∈ mem', a ↦ₐ w) ∗
         ([∗ map] a↦revoked ∈ shadow', a ↦ₛ revoked) ∗
         ([∗ set] a ∈ sperm, shadow_store_perm a) ∗
         deref_witness_res dw ∗
         [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
   Proof.
     iIntros (Hinstr Hvpc Dregs Hmem_pc HaStore φ) "(HPC & Hmem & Hshadow & Hperms & Hdw & Hmap) Hφ".
     iApply (wp_store_shadow_imm_gen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ true (DfracOwn 1) dw
       with "[$HPC $Hmem $Hshadow $Hperms $Hdw $Hmap]"); eauto.
     iNext. iIntros (lpc' mem' shadow' retv) "(Hspec & HPC & Hmem & _ & Hshadow & Hperms & Hdw & Hmap)".
     iApply "Hφ". iFrame.
   Qed.

   (* The fetched instruction word is kept apart from the stored-to memory, and
      may be shared. *)
   Lemma wp_store_shadow_imm_fetch Ep
     pc_p pc_g pc_b pc_e pc_a pc_π
     r1 (r2 : Z + RegName) (imm : Z) w mem regs shadow (sperm : gset Addr) dq dw :
   decodeInstrW w.(lw) = Store r1 r2 imm →
   isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Store r1 r2 imm) ⊆ dom regs →
   allow_store_mem_or_shadow_imm r1 r2 imm regs mem shadow sperm →

   {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
       ▷ pc_a ↦ₐ{dq} w ∗
       (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
       (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ revoked) ∗
       ([∗ set] a ∈ sperm, shadow_store_perm a) ∗
       deref_witness_res dw ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ lpc' mem' shadow' retv, RET tval_of_val retv;
       ⌜ Store_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm lpc' mem mem' shadow shadow' dw retv⌝ ∗
         PC ↦ₚ lpc' ∗
         pc_a ↦ₐ{dq} w ∗
         ([∗ map] a↦w ∈ mem', a ↦ₐ w) ∗
         ([∗ map] a↦revoked ∈ shadow', a ↦ₛ revoked) ∗
         ([∗ set] a ∈ sperm, shadow_store_perm a) ∗
         deref_witness_res dw ∗
         [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
   Proof.
     iIntros (Hinstr Hvpc Dregs HaStore φ) "(HPC & Hfetch & Hmem & Hshadow & Hperms & Hdw & Hmap) Hφ".
     iApply (wp_store_shadow_imm_gen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ false dq dw
       with "[$HPC $Hfetch $Hmem $Hshadow $Hperms $Hdw $Hmap]"); eauto.
     iNext. iIntros (lpc' mem' shadow' retv) "(Hspec & HPC & Hmem & Hfetch & Hshadow & Hperms & Hdw & Hmap)".
     iApply "Hφ". iFrame.
   Qed.

  (** Owned memory, out of the shadow region, is an allowed store target. *)
  Lemma allow_store_map_or_true_imm_no_shadow r1 (r2 : Z + RegName) imm regs mem :
    allow_store_map_or_true_imm r1 r2 imm regs mem →
    (∀ p g b e a ea, reg_allows_store_imm regs r1 imm p g b e a ea →
       is_shadow_address ea = false) →
    allow_store_mem_or_shadow_imm r1 r2 imm regs mem (∅ : ShadowTbl) ∅.
  Proof.
    intros HaStore Hordinary p g b e a ea storev Hreg Harg.
    pose proof Hreg as (Hcap & Hadd & Hwa & Hwb).
    destruct (is_shadow_address ea) eqn:Hshadowea.
    - specialize (Hordinary p g b e a ea Hreg). congruence.
    - destruct (allow_store_implies_storev_imm r1 r2 mem regs p g b e a ea imm storev
        HaStore Hcap Harg Hwa Hadd Hwb) as [oldv Hlookup].
      destruct (is_time_device_address ea); first done.
      exists oldv. exact Hlookup.
  Qed.

  Lemma wp_store_imm Ep
     pc_p pc_g pc_b pc_e pc_a pc_π
     r1 (r2 : Z + RegName) (imm : Z) w mem regs :
   decodeInstrW w.(lw) = Store r1 r2 imm →
   isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Store r1 r2 imm) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_store_map_or_true_imm r1 r2 imm regs mem →
   (∀ p g b e a ea, reg_allows_store_imm regs r1 imm p g b e a ea →
      is_shadow_address ea = false) →
   {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
       (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ lpc' mem' retv, RET tval_of_val retv;
       ⌜ Store_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm lpc' mem mem' (∅ : ShadowTbl) (∅ : ShadowTbl) DerefNoId retv⌝ ∗
         PC ↦ₚ lpc' ∗
         ([∗ map] a↦w ∈ mem', a ↦ₐ w) ∗
         [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hmem_pc HaStore Hordinary φ) "Hres Hφ".
    iDestruct "Hres" as "(HPC & Hmem & Hmap)".
    iAssert ((▷ ([∗ map] k↦revoked ∈ (∅ : ShadowTbl), k ↦ₛ revoked))%I) as "Hshadow".
    { iNext. rewrite big_sepM_empty. done. }
    pose proof (allow_store_map_or_true_imm_no_shadow _ _ _ _ _ HaStore Hordinary) as HaStoreOffset.
    iApply (wp_store_shadow_imm Ep pc_p pc_g pc_b pc_e pc_a pc_π r1 r2 imm w mem regs (∅ : ShadowTbl) ∅
      DerefNoId with "[$HPC $Hmem $Hshadow $Hmap]"); try done.
    all: try (by rewrite big_sepS_empty).
    iNext. iIntros (lpc' mem' shadow' retv) "(%Hspec & HPC & Hmem' & Hshadow' & _ & _ & Hregs')".
    destruct Hspec as
      [p g b e a ea storev oldv Harg Hallow Hnotshadow Hlookup Hmem_eq Hshadow_eq Hinc
      |p g b e a ea heap_a storev old_status Harg Hallow Hshadowea Htranslate Hold Hmem_eq Hshadow_eq Hinc
      |p g b e a ea storev Harg Hallow Htdev Hmtimecmp Hnone Hmem_eq Hshadow_eq Hinc
      |Hmem_eq Hshadow_eq Hfail].
    - iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
    - exfalso. simplify_map_eq.
    - iApply "Hφ". iFrame. iPureIntro. eapply Store_spec_success_timedev; eauto.
    - iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
  Qed.

  Lemma wp_store_imm_fetch Ep
     pc_p pc_g pc_b pc_e pc_a pc_π
     r1 (r2 : Z + RegName) (imm : Z) w mem regs dq dw :
   decodeInstrW w.(lw) = Store r1 r2 imm →
   isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Store r1 r2 imm) ⊆ dom regs →
   allow_store_map_or_true_imm r1 r2 imm regs mem →
   (∀ p g b e a ea, reg_allows_store_imm regs r1 imm p g b e a ea →
      is_shadow_address ea = false) →
   {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
       ▷ pc_a ↦ₐ{dq} w ∗
       (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
       deref_witness_res dw ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ lpc' mem' retv, RET tval_of_val retv;
       ⌜ Store_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm lpc' mem mem' (∅ : ShadowTbl) (∅ : ShadowTbl) dw retv⌝ ∗
         PC ↦ₚ lpc' ∗
         pc_a ↦ₐ{dq} w ∗
         ([∗ map] a↦w ∈ mem', a ↦ₐ w) ∗
         deref_witness_res dw ∗
         [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs HaStore Hordinary φ) "(HPC & Hfetch & Hmem & Hdw & Hmap) Hφ".
    iAssert ((▷ ([∗ map] k↦revoked ∈ (∅ : ShadowTbl), k ↦ₛ revoked))%I) as "Hshadow".
    { iNext. rewrite big_sepM_empty. done. }
    pose proof (allow_store_map_or_true_imm_no_shadow _ _ _ _ _ HaStore Hordinary) as HaStoreOffset.
    iApply (wp_store_shadow_imm_fetch Ep pc_p pc_g pc_b pc_e pc_a pc_π r1 r2 imm w mem regs (∅ : ShadowTbl) ∅
      _ dw with "[$HPC $Hfetch $Hmem $Hshadow $Hdw $Hmap]"); try done.
    all: try (by rewrite big_sepS_empty).
    iNext. iIntros (lpc' mem' shadow' retv) "(%Hspec & HPC & Hfetch & Hmem' & Hshadow' & _ & Hdw & Hregs')".
    destruct Hspec as
      [p g b e a ea storev oldv Harg Hallow Hnotshadow Hlookup Hmem_eq Hshadow_eq Hinc
      |p g b e a ea heap_a storev old_status Harg Hallow Hshadowea Htranslate Hold Hmem_eq Hshadow_eq Hinc
      |p g b e a ea storev Harg Hallow Htdev Hmtimecmp Hnone Hmem_eq Hshadow_eq Hinc
      |Hmem_eq Hshadow_eq Hfail].
    - iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
    - exfalso. simplify_map_eq.
    - iApply "Hφ". iFrame. iPureIntro. eapply Store_spec_success_timedev; eauto.
    - iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
  Qed.

  Lemma wp_store_fetch Ep
     pc_p pc_g pc_b pc_e pc_a pc_π
     r1 (r2 : Z + RegName) w mem regs shadow sperm dq :
   decodeInstrW w.(lw) = Store r1 r2 0 →
   isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Store r1 r2 0) ⊆ dom regs →
   allow_store_mem_or_shadow r1 r2 regs mem shadow sperm →
   {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
       ▷ pc_a ↦ₐ{dq} w ∗
       (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
       (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ revoked) ∗
       ([∗ set] a ∈ sperm, shadow_store_perm a) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ lpc' mem' shadow' retv, RET tval_of_val retv;
       ⌜ Store_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 0 lpc' mem mem' shadow shadow' DerefNoId retv ⌝ ∗
         PC ↦ₚ lpc' ∗
         pc_a ↦ₐ{dq} w ∗
         ([∗ map] a↦w ∈ mem', a ↦ₐ w) ∗
         ([∗ map] a↦revoked ∈ shadow', a ↦ₛ revoked) ∗
         ([∗ set] a ∈ sperm, shadow_store_perm a) ∗
         [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hallow φ) "Hres Hφ".
    assert (Hallow0 : allow_store_mem_or_shadow_imm r1 r2 0 regs mem shadow sperm).
    { intros p g b e a ea storev Hreg Harg.
      unfold reg_allows_store_imm in Hreg.
      destruct Hreg as (Hdst & Hadd & Hwa & Hwb).
      rewrite finz_add_0 in Hadd. inversion Hadd; subst ea.
      specialize (Hallow p g b e a storev ltac:(repeat split; assumption) Harg).
      destruct (is_shadow_address a); auto. }
    iDestruct "Hres" as "(HPC & Hfetch & Hmem & Hshadow & Hperms & Hmap)".
    iApply (wp_store_shadow_imm_fetch Ep pc_p pc_g pc_b pc_e pc_a pc_π r1 r2 0 w mem regs shadow sperm
      _ DerefNoId with "[$HPC $Hfetch $Hmem $Hshadow $Hperms $Hmap]"); try done.
    iNext. iIntros (lpc' mem' shadow' retv) "(Hspec & HPC & Hfetch & Hmem & Hshadow & Hperms & _ & Hmap)".
    iApply "Hφ". iFrame.
  Qed.

  (** A store to one owned cell, apart from the fetched instruction. *)
  Lemma wp_store_next_imm E pc_p pc_g pc_b pc_e pc_a pc_π w dst src (imm : Z) regs
      p g b e a ea storev w' dq dw lpc' :
    decodeInstrW w.(lw) = Store dst src imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Store dst src imm) ⊆ dom regs →
    regs !!ₗ dst = Some (Cap p g b e a @@? deref_id dw) →
    (a + imm)%a = Some ea →
    writeAllowed p = true → withinBounds b e ea = true →
    is_shadow_address ea = false →
    lword_of_argument regs src = Some storev →
    incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ ea ↦ₐ w' ∗
        deref_witness_res dw ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        ea ↦ₐ lstore_word p storev ∗
        deref_witness_res dw ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hdecode Hvpc Dregs Hdst Hadd Hwa Hwb Hsh Harg Hinc φ)
      "(HPC & Hi & >Ha & Hdw & Hmap) Hφ".
    assert (lw <$> regs !!ₗ dst = Some (Cap p g b e a)) as Hdst' by by rewrite Hdst.
    iDestruct (memMap_resource_1 with "Ha") as "Hmem".
    iApply (wp_store_imm_fetch with "[$HPC $Hi $Hmem $Hdw $Hmap]"); eauto.
    { by eapply mem_eq_implies_allow_store_map_imm. }
    { intros ?????? (Hd & Ha' & _). rewrite Hdst' in Hd. simplify_eq. congruence. }
    iIntros "!>" (lpc0 mem' retv) "(%Hspec & HPC & Hi & Hmem & Hdw & Hmap)".
    destruct Hspec as [p0 g0 b0 e0 a0 ea0 v0 oldv0 Harg0 (Hd & Ha' & _) Hsh0 Hl0 -> _ Hinc0
                      | p0 g0 b0 e0 a0 ea0 heap_a0 v0 old_status0 Harg0 (Hd & Ha' & _) Hsh0
                      | p0 g0 b0 e0 a0 ea0 storev0 Harg0 (Hd & Ha' & _) Htdev0 _ Hnone0 _ _ _
                      | _ _ Hfail].
    - rewrite Hdst' in Hd. simplify_eq.
      rewrite insert_insert_eq -memMap_resource_1. iApply "Hφ". by iFrame.
    - by rewrite Hdst' in Hd; simplify_eq.
    - rewrite Hdst' in Hd. simplify_eq. by simplify_map_eq.
    - exfalso. eapply (Store_failure_impossible _ _ _ _ _ _ dw p g b e a ea); eauto.
      + intros v Hv. rewrite Hdst in Hv. by simplify_eq.
      + by simplify_map_eq.
      + congruence.
  Qed.

  (** A store to the cell of the fetched instruction. *)
  Lemma wp_store_next_pc_imm E pc_p pc_g pc_b pc_e pc_a pc_π w dst src (imm : Z) regs
      p g b e a storev dw lpc' :
    decodeInstrW w.(lw) = Store dst src imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Store dst src imm) ⊆ dom regs →
    regs !!ₗ dst = Some (Cap p g b e a @@? deref_id dw) →
    (a + imm)%a = Some pc_a →
    writeAllowed p = true → withinBounds b e pc_a = true →
    is_shadow_address pc_a = false →
    lword_of_argument regs src = Some storev →
    incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ w ∗
        deref_witness_res dw ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ lstore_word p storev ∗
        deref_witness_res dw ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hdecode Hvpc Dregs Hdst Hadd Hwa Hwb Hsh Harg Hinc φ) "(HPC & >Hi & Hdw & Hmap) Hφ".
    assert (lw <$> regs !!ₗ dst = Some (Cap p g b e a)) as Hdst' by by rewrite Hdst.
    iDestruct (memMap_resource_1 with "Hi") as "Hmem".
    iAssert ((▷ ([∗ map] k↦revoked ∈ (∅ : ShadowTbl), k ↦ₛ revoked))%I) as "Hshadow".
    { iNext. rewrite big_sepM_empty. done. }
    iApply (wp_store_shadow_imm _ _ _ _ _ _ _ _ _ _ _ _ _ (∅ : ShadowTbl) ∅ dw
      with "[$HPC $Hmem $Hshadow $Hdw $Hmap]"); eauto.
    { by rewrite lookup_insert_eq. }
    { apply allow_store_map_or_true_imm_no_shadow.
      - by eapply mem_eq_implies_allow_store_map_imm.
      - intros ?????? (Hd & Ha' & _). rewrite Hdst' in Hd. simplify_eq. congruence. }
    iIntros "!>" (lpc0 mem' shadow' retv) "(%Hspec & HPC & Hmem & _ & _ & Hdw & Hmap)".
    destruct Hspec as [p0 g0 b0 e0 a0 ea0 v0 oldv0 Harg0 (Hd & Ha' & _) Hsh0 Hl0 -> _ Hinc0
                      | p0 g0 b0 e0 a0 ea0 heap_a0 v0 old_status0 Harg0 (Hd & Ha' & _) Hsh0
                      | p0 g0 b0 e0 a0 ea0 storev0 Harg0 (Hd & Ha' & _) Htdev0 _ Hnone0 _ _ _
                      | _ _ Hfail].
    - rewrite Hdst' in Hd. simplify_eq.
      rewrite insert_insert_eq -memMap_resource_1. iApply "Hφ". by iFrame.
    - by rewrite Hdst' in Hd; simplify_eq.
    - rewrite Hdst' in Hd. simplify_eq. by simplify_map_eq.
    - exfalso. eapply (Store_failure_impossible _ _ _ _ _ _ dw p g b e a pc_a); eauto.
      + intros v Hv. rewrite Hdst in Hv. by simplify_eq.
      + by simplify_map_eq.
      + congruence.
  Qed.

    Lemma wp_store_success_reg_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst src w'
         p g b e a ea (imm : Z) w'' dq q :
     is_shadow_address ea = false →
      decodeInstrW w.(lw) = Store dst (inr src) imm →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e ea = true →
     (a + imm)%a = Some ea →
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ Cap p g b e a @@? π
           ∗ ▷ ea ↦ₐ w'
           ∗ deref_res π q }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ{dq} w
              ∗ src ↦ᵣ w''
              ∗ dst ↦ᵣ Cap p g b e a @@? π
              ∗ ea ↦ₐ lstore_word p w''
              ∗ deref_res π q }}}.
    Proof.
    rewrite deref_res_witness.
    generalize (deref_id_witness_of π q). generalize (deref_witness_of π q).
    intros dw <-.
    iIntros (Hsh Hdecode Hvpc Hpca' Hwa Hwb Hadd Hsrc Hdst φ)
      "(HPC & Hi & >Hsrc & >Hdst & Ha & Hdw) Hφ".
    iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %]".
    iApply (wp_store_next_imm with "[$HPC $Hi $Ha $Hdw $Hmap]"); try solve_next_side.
    iIntros "!> (HPC & Hi & Ha & Hdw & Hmap)". iRegsMap "Hmap".
    iApply "Hφ". iFrame.
    Qed.

   Lemma wp_store_success_reg_same_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst w'
         p g b e a ea (imm : Z) dq q :
     is_shadow_address ea = false →
     decodeInstrW w.(lw) = Store dst (inr dst) imm →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e ea = true →
     (a + imm)%a = Some ea →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ dst ↦ᵣ Cap p g b e a @@? π
           ∗ ▷ ea ↦ₐ w'
           ∗ deref_res π q }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ{dq} w
              ∗ dst ↦ᵣ Cap p g b e a @@? π
              ∗ ea ↦ₐ lstore_word p (Cap p g b e a @@? π)
              ∗ deref_res π q }}}.
   Proof.
    rewrite deref_res_witness.
    generalize (deref_id_witness_of π q). generalize (deref_witness_of π q).
    intros dw <-.
    iIntros (Hsh Hdecode Hvpc Hpca' Hwa Hwb Hadd Hdst φ) "(HPC & Hi & >Hdst & Ha & Hdw) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iApply (wp_store_next_imm with "[$HPC $Hi $Ha $Hdw $Hmap]"); try solve_next_side.
    iIntros "!> (HPC & Hi & Ha & Hdw & Hmap)". iRegsMap "Hmap".
    iApply "Hφ". iFrame.
   Qed.

   Lemma wp_store_success_z_imm E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst z w'
         p g b e a ea (imm : Z) dq q :
     is_shadow_address ea = false →
     decodeInstrW w.(lw) = Store dst (inl z) imm →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e ea = true →
     (a + imm)%a = Some ea →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ dst ↦ᵣ Cap p g b e a @@? π
           ∗ ▷ ea ↦ₐ w'
           ∗ deref_res π q }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ{dq} w
              ∗ dst ↦ᵣ Cap p g b e a @@? π
              ∗ ea ↦ₐ WInt z
              ∗ deref_res π q }}}.
   Proof.
    rewrite deref_res_witness.
    generalize (deref_id_witness_of π q). generalize (deref_witness_of π q).
    intros dw <-.
    iIntros (Hsh Hdecode Hvpc Hpca' Hwa Hwb Hadd Hdst φ) "(HPC & Hi & >Hdst & Ha & Hdw) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iApply (wp_store_next_imm with "[$HPC $Hi $Ha $Hdw $Hmap]"); try solve_next_side.
    iIntros "!> (HPC & Hi & Ha & Hdw & Hmap)". iRegsMap "Hmap".
    rewrite lstore_word_canStore; last by apply writeAllowed_canStore_int.
    iApply "Hφ". iFrame.
   Qed.

   Lemma wp_store_success_reg_imm E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst src w'
       p g b e a ea (imm : Z) w'' dq q :
     is_shadow_address ea = false →
     decodeInstrW w.(lw) = Store dst (inr src) imm →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e ea = true →
     (a + imm)%a = Some ea →
     canStore p w''.(lw) = true →
     src ≠ cnull → dst ≠ cnull →
     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ Cap p g b e a @@? π
           ∗ ▷ ea ↦ₐ w'
           ∗ deref_res π q }}}
       Instr Executable @ E
     {{{ RET NextIV;
         PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
           ∗ pc_a ↦ₐ{dq} w
           ∗ src ↦ᵣ w''
           ∗ dst ↦ᵣ Cap p g b e a @@? π
           ∗ ea ↦ₐ w''
           ∗ deref_res π q }}}.
   Proof.
     iIntros (Hshadow Hinstr Hvpc Hpca' Hwa Hwb Hadd HcanStore Hsrc Hdst φ) "Hres Hφ".
     iApply (wp_store_success_reg_store_word_imm with "Hres"); eauto.
     iNext. iIntros "(HPC & Hi & Hsrc & Hdst & Ha & Hdw)".
     iEval (rewrite lstore_word_canStore //) in "Ha".
     iApply "Hφ". iFrame.
   Qed.

   Lemma wp_store_success_same_imm E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst z
         p g b e a (imm : Z) q :
     is_shadow_address pc_a = false →
     decodeInstrW w.(lw) = Store dst (inl z) imm →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     (a + imm)%a = Some pc_a →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ Cap p g b e a @@? π
           ∗ deref_res π q }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ (WInt z)
              ∗ dst ↦ᵣ Cap p g b e a @@? π
              ∗ deref_res π q }}}.
    Proof.
    rewrite deref_res_witness.
    generalize (deref_id_witness_of π q). generalize (deref_witness_of π q).
    intros dw <-.
    iIntros (Hsh Hdecode Hvpc Hpca' Hwa Hwb Hadd Hdst φ) "(HPC & Hi & >Hdst & Hdw) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iApply (wp_store_next_pc_imm with "[$HPC $Hi $Hdw $Hmap]"); try solve_next_side.
    iIntros "!> (HPC & Hi & Hdw & Hmap)". iRegsMap "Hmap".
    rewrite lstore_word_canStore; last by apply writeAllowed_canStore_int.
    iApply "Hφ". iFrame.
    Qed.

   Lemma wp_store_success_reg_same'_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst
         p g b e a (imm : Z) q :
     is_shadow_address pc_a = false →
     decodeInstrW w.(lw) = Store dst (inr dst) imm →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     (a + imm)%a = Some pc_a →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ Cap p g b e a @@? π
           ∗ deref_res π q }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ lstore_word p (Cap p g b e a @@? π)
              ∗ dst ↦ᵣ Cap p g b e a @@? π
              ∗ deref_res π q }}}.
   Proof.
    rewrite deref_res_witness.
    generalize (deref_id_witness_of π q). generalize (deref_witness_of π q).
    intros dw <-.
    iIntros (Hsh Hdecode Hvpc Hpca' Hwa Hwb Hadd Hdst φ) "(HPC & Hi & >Hdst & Hdw) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iApply (wp_store_next_pc_imm with "[$HPC $Hi $Hdw $Hmap]"); try solve_next_side.
    iIntros "!> (HPC & Hi & Hdw & Hmap)". iRegsMap "Hmap".
    iApply "Hφ". iFrame.
   Qed.

   Lemma wp_store_success_reg_same_a_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst src
         p g b e a (imm : Z) w'' q :
     is_shadow_address pc_a = false →
      decodeInstrW w.(lw) = Store dst (inr src) imm →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     (a + imm)%a = Some pc_a →
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ Cap p g b e a @@? π
           ∗ deref_res π q }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ lstore_word p w''
              ∗ src ↦ᵣ w''
              ∗ dst ↦ᵣ Cap p g b e a @@? π
              ∗ deref_res π q }}}.
   Proof.
    rewrite deref_res_witness.
    generalize (deref_id_witness_of π q). generalize (deref_witness_of π q).
    intros dw <-.
    iIntros (Hsh Hdecode Hvpc Hpca' Hwa Hwb Hadd Hsrc Hdst φ) "(HPC & Hi & >Hsrc & >Hdst & Hdw) Hφ".
    iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %]".
    iApply (wp_store_next_pc_imm with "[$HPC $Hi $Hdw $Hmap]"); try solve_next_side.
    iIntros "!> (HPC & Hi & Hdw & Hmap)". iRegsMap "Hmap".
    iApply "Hφ". iFrame.
   Qed.

   Lemma wp_store_fail_reg_not_cap_lword_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_π w
     dst src (wdst : LWord) wstore dq :
      decodeInstrW w.(lw) = Store dst (inr src) imm →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     is_cap wdst.(lw) = false ->
     src ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ src ↦ᵣ wstore
           ∗ ▷ dst ↦ᵣ wdst
     }}}
       Instr Executable @ E
       {{{ RET FaultedV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
           pc_a ↦ₐ{dq} w ∗
           src ↦ᵣ wstore ∗
           dst ↦ᵣ wdst }}}.
    Proof.
    iIntros (Hinstr Hvpc Hcap Hsrc φ) "(HPC & Hi & Hs & Hd) Hφ".
    iApply (wp_instr_faulted_2 with "[$HPC $Hs $Hd $Hi]"); [done | done | | ].
    { intros r sr m st td s1 s2 H1 H2.
      rewrite /exec /= /lookup_reg H1 H2 /= (decide_False _ _ Hsrc) /=.
      case_decide; [done|].
      destruct wdst as [wd ?]; cbn in Hcap.
      destruct_word wd; cbn in Hcap; try discriminate; by destruct s2. }
    iIntros "!> (HPC & Hs & Hd & Hi)".
    iApply "Hφ". iFrame.
    Qed.

   Lemma wp_store_fail_reg_not_cap_lword E pc_p pc_g pc_b pc_e pc_a pc_π w
     dst src (wdst : LWord) wstore dq :
      decodeInstrW w.(lw) = Store dst (inr src) 0 →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     is_cap wdst.(lw) = false ->
     src ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ src ↦ᵣ wstore
           ∗ ▷ dst ↦ᵣ wdst
     }}}
       Instr Executable @ E
       {{{ RET FaultedV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
           pc_a ↦ₐ{dq} w ∗
           src ↦ᵣ wstore ∗
           dst ↦ᵣ wdst }}}.
  Proof.
    intros. eapply wp_store_fail_reg_not_cap_lword_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_fail_reg_perm_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_π π w dst src
         p g b e a w'' dq :
     decodeInstrW w.(lw) = Store dst (inr src) imm →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     writeAllowed p = false ->
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ Cap p g b e a @@? π
     }}}
       Instr Executable @ E
       {{{ RET FaultedV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
           pc_a ↦ₐ{dq} w ∗
           src ↦ᵣ w'' ∗
           dst ↦ᵣ Cap p g b e a @@? π }}}.
    Proof.
    iIntros (Hinstr Hvpc Hwa Hsrc Hdst φ) "(HPC & Hi & Hs & Hd) Hφ".
    iApply (wp_instr_faulted_2 with "[$HPC $Hs $Hd $Hi]"); [done | done | | ].
    { intros r sr m st td s1 s2 H1 H2.
      rewrite /exec /= /lookup_reg H1 H2 /= !decide_False //.
      destruct s2; cbn; last done.
      destruct (a + imm)%a; cbn; [by rewrite Hwa | done]. }
    iIntros "!> (HPC & Hs & Hd & Hi)".
    iApply "Hφ". iFrame.
    Qed.

    Lemma wp_store_fail_z_perm_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_π π w dst
         p g b e a z dq :
      decodeInstrW w.(lw) = Store dst (inl z) imm →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     writeAllowed p = false ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ dst ↦ᵣ Cap p g b e a @@? π
     }}}
       Instr Executable @ E
       {{{ RET FaultedV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
           pc_a ↦ₐ{dq} w ∗
           dst ↦ᵣ Cap p g b e a @@? π }}}.
    Proof.
    iIntros (Hinstr Hvpc Hwa Hdst φ) "(HPC & Hi & Hd) Hφ".
    iApply (wp_instr_faulted_1 with "[$HPC $Hd $Hi]"); [done | done | | ].
    { intros r sr m st td s1 H1.
      rewrite /exec /= /lookup_reg H1 /= !decide_False //.
      destruct s1; cbn; last done.
      destruct (a + imm)%a; cbn; [by rewrite Hwa | done]. }
    iIntros "!> (HPC & Hd & Hi)".
    iApply "Hφ". iFrame.
    Qed.

   Lemma wp_store_fail_reg_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_π π w dst src
         p g b e a ea w'' dq :
      decodeInstrW w.(lw) = Store dst (inr src) imm →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (a + imm)%a = Some ea →
     withinBounds b e ea = false →
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ Cap p g b e a @@? π
     }}}
       Instr Executable @ E
       {{{ RET FaultedV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
           pc_a ↦ₐ{dq} w ∗
           src ↦ᵣ w'' ∗
           dst ↦ᵣ Cap p g b e a @@? π }}}.
    Proof.
    iIntros (Hinstr Hvpc Hadd Hwb Hsrc Hdst φ) "(HPC & Hi & Hs & Hd) Hφ".
    iApply (wp_instr_faulted_2 with "[$HPC $Hs $Hd $Hi]"); [done | done | | ].
    { intros r sr m st td s1 s2 H1 H2.
      rewrite /exec /= /lookup_reg H1 H2 /= !decide_False //.
      destruct s2; cbn; last done.
      by rewrite Hadd /= Hwb andb_false_r. }
    iIntros "!> (HPC & Hs & Hd & Hi)".
    iApply "Hφ". iFrame.
    Qed.

    Lemma wp_store_fail_z_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_π π w dst
         p g b e a ea z dq :
      decodeInstrW w.(lw) = Store dst (inl z) imm →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (a + imm)%a = Some ea →
     withinBounds b e ea = false →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ dst ↦ᵣ Cap p g b e a @@? π
     }}}
       Instr Executable @ E
       {{{ RET FaultedV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
           pc_a ↦ₐ{dq} w ∗
           dst ↦ᵣ Cap p g b e a @@? π }}}.
    Proof.
    iIntros (Hinstr Hvpc Hadd Hwb Hdst φ) "(HPC & Hi & Hd) Hφ".
    iApply (wp_instr_faulted_1 with "[$HPC $Hd $Hi]"); [done | done | | ].
    { intros r sr m st td s1 H1.
      rewrite /exec /= /lookup_reg H1 /= !decide_False //.
      destruct s1; cbn; last done.
      by rewrite Hadd /= Hwb andb_false_r. }
    iIntros "!> (HPC & Hd & Hi)".
    iApply "Hφ". iFrame.
    Qed.

  Lemma wp_store_fail_tag_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_π
      w dst (src : Z + RegName) regs wa dq :
    decodeInstrW w.(lw) = Store dst src imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs !!ₗ dst = Some wa →
    get_tag wa.(lw) = false →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FaultedV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Hdst Htag φ) "(>HPC & >Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step_nosw with "HPC Hpc_a Hmap"); [rewrite Hinstr; by apply sw_of_none|..]; eauto.
    iNext; iIntros (r sr m st td lreg lsreg lmem R C c σ') "@".
    destruct (llookup_reg_phys _ _ _ _ _ Hregs Hdst) as (s0 & Hdst' & _).
    rewrite Hinstr /exec /= Hdst' /= in Hstep.
    assert (c = Faulted ∧ σ' = (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td)) as [-> ->].
    { destruct wa as [ [| [ [] p g b e a|] | |] ?]; cbn in Htag; try discriminate.
      all: destruct s0; cbn in Hstep; destruct (word_of_argument _ src); cbn in Hstep; by simplify_eq. }
    instr_fail_close.
  Qed.

   Lemma wp_store_success_same E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst z w'
         p g b e q :
     is_shadow_address pc_a = false →
     decodeInstrW w.(lw) = Store dst (inl z) 0 →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ Cap p g b e pc_a @@? π
           ∗ deref_res π q }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ (WInt z)
              ∗ dst ↦ᵣ Cap p g b e pc_a @@? π
              ∗ deref_res π q }}}.
  Proof.
    intros. eapply wp_store_success_same_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_success_reg_same'_store_word E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst
         p g b e q :
     is_shadow_address pc_a = false →
     decodeInstrW w.(lw) = Store dst (inr dst) 0 →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ Cap p g b e pc_a @@? π
           ∗ deref_res π q }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ lstore_word p (Cap p g b e pc_a @@? π)
              ∗ dst ↦ᵣ Cap p g b e pc_a @@? π
              ∗ deref_res π q }}}.
   Proof.
    intros. eapply wp_store_success_reg_same'_store_word_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_success_reg_same_a_store_word E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst src
         p g b e w'' q :
      is_shadow_address pc_a = false →
     decodeInstrW w.(lw) = Store dst (inr src) 0 →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ Cap p g b e pc_a @@? π
           ∗ deref_res π q }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ lstore_word p w''
              ∗ src ↦ᵣ w''
              ∗ dst ↦ᵣ Cap p g b e pc_a @@? π
              ∗ deref_res π q }}}.
   Proof.
    intros. eapply wp_store_success_reg_same_a_store_word_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_success_reg_store_word E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst src w'
         p g b e a w'' dq q :
      is_shadow_address a = false →
     decodeInstrW w.(lw) = Store dst (inr src) 0 →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ Cap p g b e a @@? π
           ∗ ▷ a ↦ₐ w'
           ∗ deref_res π q }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ{dq} w
              ∗ src ↦ᵣ w''
              ∗ dst ↦ᵣ Cap p g b e a @@? π
              ∗ a ↦ₐ lstore_word p w''
              ∗ deref_res π q }}}.
    Proof.
    intros. eapply wp_store_success_reg_store_word_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_success_reg E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst src w'
         p g b e a w'' dq q :
     is_shadow_address a = false →
      decodeInstrW w.(lw) = Store dst (inr src) 0 →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →
     canStore p w''.(lw) = true ->
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ Cap p g b e a @@? π
           ∗ ▷ a ↦ₐ w'
           ∗ deref_res π q }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ{dq} w
              ∗ src ↦ᵣ w''
              ∗ dst ↦ᵣ Cap p g b e a @@? π
              ∗ a ↦ₐ w''
              ∗ deref_res π q }}}.
  Proof.
    intros. eapply wp_store_success_reg_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_success_reg_same_store_word E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst w'
         p g b e a dq q :
     is_shadow_address a = false →
     decodeInstrW w.(lw) = Store dst (inr dst) 0 →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ dst ↦ᵣ Cap p g b e a @@? π
           ∗ ▷ a ↦ₐ w'
           ∗ deref_res π q }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ{dq} w
              ∗ dst ↦ᵣ Cap p g b e a @@? π
              ∗ a ↦ₐ lstore_word p (Cap p g b e a @@? π)
              ∗ deref_res π q }}}.
   Proof.
    intros. eapply wp_store_success_reg_same_store_word_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_success_z E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst z w'
         p g b e a dq q :
     is_shadow_address a = false →
     decodeInstrW w.(lw) = Store dst (inl z) 0 →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ dst ↦ᵣ Cap p g b e a @@? π
           ∗ ▷ a ↦ₐ w'
           ∗ deref_res π q }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ{dq} w
              ∗ dst ↦ᵣ Cap p g b e a @@? π
              ∗ a ↦ₐ WInt z
              ∗ deref_res π q }}}.
  Proof.
    intros. eapply wp_store_success_z_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_fail_reg E pc_p pc_g pc_b pc_e pc_a pc_π π w dst src
         p g b e a w'' dq :
      decodeInstrW w.(lw) = Store dst (inr src) 0 →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     withinBounds b e a = false →
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ Cap p g b e a @@? π
     }}}
       Instr Executable @ E
       {{{ RET FaultedV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
           pc_a ↦ₐ{dq} w ∗
           src ↦ᵣ w'' ∗
           dst ↦ᵣ Cap p g b e a @@? π }}}.
  Proof.
    intros. eapply wp_store_fail_reg_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

    Lemma wp_store_fail_z E pc_p pc_g pc_b pc_e pc_a pc_π π w dst
         p g b e a z dq :
      decodeInstrW w.(lw) = Store dst (inl z) 0 →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     withinBounds b e a = false →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ dst ↦ᵣ Cap p g b e a @@? π
     }}}
       Instr Executable @ E
       {{{ RET FaultedV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
           pc_a ↦ₐ{dq} w ∗
           dst ↦ᵣ Cap p g b e a @@? π }}}.
  Proof.
    intros. eapply wp_store_fail_z_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

Lemma wp_store_fail_reg_overflow_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_π π w dst src
         p g b e a w'' dq :
     decodeInstrW w.(lw) = Store dst (inr src) imm →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (a + imm)%a = None →
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ Cap p g b e a @@? π
     }}}
       Instr Executable @ E
       {{{ RET FaultedV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
           pc_a ↦ₐ{dq} w ∗
           src ↦ᵣ w'' ∗
           dst ↦ᵣ Cap p g b e a @@? π }}}.
    Proof.
    iIntros (Hinstr Hvpc Hadd Hsrc Hdst φ) "(HPC & Hi & Hs & Hd) Hφ".
    iApply (wp_instr_faulted_2 with "[$HPC $Hs $Hd $Hi]"); [done | done | | ].
    { intros r sr m st td s1 s2 H1 H2.
      rewrite /exec /= /lookup_reg H1 H2 /= !decide_False //.
      destruct s2; cbn; last done.
      by rewrite Hadd. }
    iIntros "!> (HPC & Hs & Hd & Hi)".
    iApply "Hφ". iFrame.
    Qed.
Lemma wp_store_fail_z_overflow_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_π π w dst
         p g b e a z dq :
     decodeInstrW w.(lw) = Store dst (inl z) imm →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (a + imm)%a = None →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ dst ↦ᵣ Cap p g b e a @@? π
     }}}
       Instr Executable @ E
       {{{ RET FaultedV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
           pc_a ↦ₐ{dq} w ∗
           dst ↦ᵣ Cap p g b e a @@? π }}}.
    Proof.
    iIntros (Hinstr Hvpc Hadd Hdst φ) "(HPC & Hi & Hd) Hφ".
    iApply (wp_instr_faulted_1 with "[$HPC $Hd $Hi]"); [done | done | | ].
    { intros r sr m st td s1 H1.
      rewrite /exec /= /lookup_reg H1 /= !decide_False //.
      destruct s1; cbn; last done.
      by rewrite Hadd. }
    iIntros "!> (HPC & Hd & Hi)".
    iApply "Hφ". iFrame.
    Qed.

End griotte_lang_rules.

Section shadow_store_res.
  Context `{MP: MachineParameters} `{ceriseg: ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.

  Lemma wp_store_shadow_imm_res_fetch Ep
     pc_p pc_g pc_b pc_e pc_a pc_π
     r1 (r2 : Z + RegName) (imm : Z) w mem regs shadow (sperm : gset Addr)
     (Pm : Addr → iProp Σ) dq dw :
   (∀ R C a, a ∈ sperm →
      reg_auth R -∗ addr_alloc_auth C -∗ ([∗ set] a ∈ sperm, Pm a) -∗
      ⌜shadow_perm_ok R C a⌝) →
   decodeInstrW w.(lw) = Store r1 r2 imm →
   isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Store r1 r2 imm) ⊆ dom regs →
   allow_store_mem_or_shadow_imm r1 r2 imm regs mem shadow sperm →

   {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
       ▷ pc_a ↦ₐ{dq} w ∗
       (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
       (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ revoked) ∗
       ([∗ set] a ∈ sperm, Pm a) ∗
       deref_witness_res dw ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ lpc' mem' shadow' retv, RET tval_of_val retv;
       ⌜ Store_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm lpc' mem mem' shadow shadow' dw retv⌝ ∗
         PC ↦ₚ lpc' ∗
         pc_a ↦ₐ{dq} w ∗
         ([∗ map] a↦w ∈ mem', a ↦ₐ w) ∗
         ([∗ map] a↦revoked ∈ shadow', a ↦ₛ revoked) ∗
         ([∗ set] a ∈ sperm, Pm a) ∗
         deref_witness_res dw ∗
         [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
   Proof.
     iIntros (HPm Hinstr Hvpc Dregs HaStore φ) "(HPC & Hfetch & Hmem & Hshadow & Hperms & Hdw & Hmap) Hφ".
     iApply (wp_store_shadow_imm_res_gen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ false dq dw
       with "[$HPC $Hfetch $Hmem $Hshadow $Hperms $Hdw $Hmap]"); eauto.
     iNext. iIntros (lpc' mem' shadow' retv) "(Hspec & HPC & Hmem & Hfetch & Hshadow & Hperms & Hdw & Hmap)".
     iApply "Hφ". iFrame.
   Qed.

  (** A store through a word that is not a capability fails, whatever its
      identifier. *)
  Lemma wp_store_fail_not_cap_imm Ep (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_π
      w dst (src : Z + RegName) regs wa dq :
    decodeInstrW w.(lw) = Store dst src imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs !!ₗ dst = Some wa →
    is_cap wa.(lw) = false →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ RET FaultedV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Hdst Hcap φ) "(>HPC & >Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step_nosw with "HPC Hpc_a Hmap"); [rewrite Hinstr; by apply sw_of_none|..]; eauto.
    iNext; iIntros (r sr m st td lreg lsreg lmem Rg Cg c σ') "@".
    destruct (llookup_reg_phys _ _ _ _ _ Hregs Hdst) as (s0 & Hdst' & _).
    rewrite Hinstr /exec /= Hdst' /= in Hstep.
    assert (c = Faulted ∧ σ' = (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td)) as [-> ->].
    { destruct wa as [ [| [|] | |] ?]; cbn in Hcap; try discriminate.
      all: destruct s0; cbn in Hstep; destruct (word_of_argument _ src); cbn in Hstep; by simplify_eq. }
    instr_fail_close.
  Qed.

End shadow_store_res.
