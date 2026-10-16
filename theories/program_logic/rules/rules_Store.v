From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base.

Section griotte_lang_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ}.
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
    lw <$> regs !!ₗ r = Some (WCap true p g b e a) ∧
    (a + imm)%a = Some ea ∧ writeAllowed p = true ∧ withinBounds b e ea = true.

  (* Store relations carry the instruction's immediate and both heaps. *)
  Inductive Store_failure
      (lpc : LWord) (regs : LReg) (r1 : RegName) (r2 : Z + RegName) (imm : Z)
      (mem : LMem) (dw : deref_witness) : Prop :=
  | Store_fail_const w :
      regs !!ₗ r1 = Some w -> is_cap w.(lw) = false ->
      Store_failure lpc regs r1 r2 imm mem dw
  | Store_fail_tag p g b e a :
      lw <$> regs !!ₗ r1 = Some (WCap false p g b e a) ->
      Store_failure lpc regs r1 r2 imm mem dw
  | Store_fail_addr p g b e a :
      lw <$> regs !!ₗ r1 = Some (WCap true p g b e a) ->
      (a + imm)%a = None ->
      Store_failure lpc regs r1 r2 imm mem dw
  | Store_fail_bounds p g b e a ea :
      lw <$> regs !!ₗ r1 = Some (WCap true p g b e a) ->
      (a + imm)%a = Some ea ->
      (writeAllowed p = false \/ withinBounds b e ea = false) ->
      Store_failure lpc regs r1 r2 imm mem dw
  | Store_fail_invalid_PC :
      incrementPC lpc = None ->
      Store_failure lpc regs r1 r2 imm mem dw
  | Store_fail_invalid_shadow p g b e a ea storev :
      lw <$> regs !!ₗ r1 = Some (WCap true p g b e a) ->
      (a + imm)%a = Some ea ->
      is_shadow_address ea = true ->
      lword_of_argument regs r2 = Some storev ->
      (forall z, storev.(lw) <> WInt z) ->
      Store_failure lpc regs r1 r2 imm mem dw
  (* A destination with an identifier not covered by the witness may have
     been revoked: its physical copy is untagged. *)
  | Store_fail_revoked p g b e a π :
      regs !!ₗ r1 = Some (WCap true p g b e a @@? π) ->
      π ≠ deref_id dw ->
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
      Store_spec lpc regs r1 r2 imm lpc' mem mem' shadow shadow' dw NextIV
  | Store_spec_success_shadow p g b e a ea heap_a z π old_status :
      lword_of_argument regs r2 = Some (WInt z @@? π) ->
      reg_allows_store_imm regs r1 imm p g b e a ea ->
      is_shadow_address ea = true ->
      shadow_to_heap ea = Some heap_a ->
      shadow !! heap_a = Some old_status ->
      mem' = mem ->
      shadow' = <[heap_a := decodeAllocStatus z]> shadow ->
      incrementPC lpc = Some lpc' ->
      Store_spec lpc regs r1 r2 imm lpc' mem mem' shadow shadow' dw NextIV
  | Store_spec_failure_store :
      mem' = mem -> shadow' = shadow ->
      Store_failure lpc regs r1 r2 imm mem dw ->
      Store_spec lpc regs r1 r2 imm lpc' mem mem' shadow shadow' dw FailedV.

  Lemma Store_failure_impossible lpc regs r1 (r2 : Z + RegName) imm mem dw p g b e a ea :
    lw <$> regs !!ₗ r1 = Some (WCap true p g b e a) ->
    (∀ v : LWord, regs !!ₗ r1 = Some v → v.(lprov) = deref_id dw) ->
    (a + imm)%a = Some ea ->
    writeAllowed p = true -> withinBounds b e ea = true ->
    is_shadow_address ea = false ->
    incrementPC lpc ≠ None ->
    Store_failure lpc regs r1 r2 imm mem dw -> False.
  Proof.
    intros Hreg Hid Hadd Hwa Hbounds Hshadow Hpc Hfail.
    destruct Hfail as [w0 Hw0 Hcap| ? ? ? ? ? H | ? ? ? ? ? H H0 | ? ? ? ? ? ? H H0 H1 | H | ? ? ? ? ? ? ? H H0 H1
                      | ? ? ? ? ? π H H0].
    - rewrite Hw0 in Hreg. destruct w0 as [w0 ?]. by simplify_eq/=.
    - rewrite Hreg in H. inversion H.
    - rewrite Hreg in H. inversion H; subst. congruence.
    - rewrite Hreg in H. inversion H; subst.
      rewrite Hadd in H0. inversion H0; subst.
      destruct H1; congruence.
    - congruence.
    - rewrite Hreg in H. inversion H; subst.
      rewrite Hadd in H0. inversion H0; subst. congruence.
    - by apply H0, (Hid _ H).
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
      → lw <$> r !!ₗ r1 = Some (WCap true p g b e a)
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
      → lw <$> regs !!ₗ r1 = Some (WCap true p g b e a)
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

  Lemma mem_neq_implies_allow_store_map_imm:
    ∀ (regs : LReg)(mem : LMem)(r1 : RegName)(r2 : Z + RegName)(pc_a : Addr)
      (w w' storev : LWord) p g b e a ea (imm : Z),
      (a + imm)%a = Some ea
      → ea ≠ pc_a
      → mem = <[pc_a:= w]> (<[ea:= w']> ∅)
      → lw <$> regs !!ₗ r1 = Some (WCap true p g b e a)
      → lword_of_argument regs r2 = Some storev
      → allow_store_map_or_true_imm r1 r2 imm regs mem.
  Proof.
    intros regs mem r1 r2 pc_a w w' storev p g b e a ea imm Hadd Hne' Hmem Hrr2 Hsv.
    pose proof (llookup_reg_cap _ _ _ _ _ _ _ _ Hrr2) as (Hne & π & Hr1).
    exists true,p,g,b,e,a,storev. split; [|split; first done].
    - unfold read_reg_inr. by rewrite Hr1.
    - unfold reg_allows_store_imm. rewrite Hadd. case_decide; last done.
      exists w'. subst mem.
      rewrite lookup_insert_ne //. by rewrite lookup_insert_eq.
  Qed.

  Definition reg_allows_store (regs : LReg) (r : RegName) p g b e a :=
    lw <$> regs !!ₗ r = Some (WCap true p g b e a) ∧
    writeAllowed p = true ∧ withinBounds b e a = true.

  Definition allow_store_map_or_true
    (r1 : RegName) (r2 : Z + RegName) (regs : LReg) (mem : LMem):=
    ∃ t p g b e a storev,
      read_reg_inr regs r1 t p g b e a ∧ lword_of_argument regs r2 = Some storev ∧
      if decide (reg_allows_store regs r1 p g b e a) then
        ∃ w, mem !! a = Some w
      else True.

  Definition allow_store_mem_or_shadow
    (r1 : RegName) (r2 : Z + RegName) (regs : LReg)
    (mem : LMem) (shadow : ShadowTbl) (sperm : gset Addr) :=
    ∀ p g b e a storev,
      reg_allows_store regs r1 p g b e a →
      lword_of_argument regs r2 = Some storev →
      if is_shadow_address a then
        (∃ z, storev.(lw) = WInt z) →
        ∃ heap_a, shadow_to_heap a = Some heap_a ∧ is_Some (shadow !! heap_a) ∧
          ∀ z, storev.(lw) = WInt z →
            shadow_store_allowed sperm shadow heap_a (decodeAllocStatus z)
      else is_Some (mem !! a).

  Definition allow_store_mem_or_shadow_imm
    (r1 : RegName) (r2 : Z + RegName) (imm : Z) (regs : LReg)
    (mem : LMem) (shadow : ShadowTbl) (sperm : gset Addr) :=
    forall p g b e a ea storev,
      reg_allows_store_imm regs r1 imm p g b e a ea ->
      lword_of_argument regs r2 = Some storev ->
      if is_shadow_address ea then
        (exists z, storev.(lw) = WInt z) ->
        exists heap_a, shadow_to_heap ea = Some heap_a ∧
          is_Some (shadow !! heap_a) ∧
          ∀ z, storev.(lw) = WInt z →
            shadow_store_allowed sperm shadow heap_a (decodeAllocStatus z)
      else is_Some (mem !! ea).


   (* Closes a failing store: the state is unchanged. *)
   #[local] Ltac store_fail Hstep :=
     injection Hstep as <- <-;
     try iApply bupd_fupd;
     iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); [done|];
     iIntros "HPC Hmap"; iApply "Hφ"; iFrame; iPureIntro;
     eapply Store_spec_failure_store; [done|done|].

   Lemma wp_store_shadow_imm_gen Ep
     pc_p pc_g pc_b pc_e pc_a pc_π
     r1 (r2 : Z + RegName) (imm : Z) w mem regs shadow (sperm : gset Addr)
     (fetch_in_mem : bool) dq dw :
   decodeInstrW w.(lw) = Store r1 r2 imm →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Store r1 r2 imm) ⊆ dom regs →
   (if fetch_in_mem then mem !! pc_a = Some w else True) →
   allow_store_mem_or_shadow_imm r1 r2 imm regs mem shadow sperm →

   {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
       (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
       (▷ if fetch_in_mem then emp else pc_a ↦ₐ{dq} w) ∗
       (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ revoked) ∗
       ([∗ set] a ∈ sperm, shadow_store_perm a) ∗
       deref_witness_res dw ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ lpc' mem' shadow' retv, RET retv;
       ⌜ Store_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm lpc' mem mem' shadow shadow' dw retv⌝ ∗
         PC ↦ₚ lpc' ∗
         ([∗ map] a↦w ∈ mem', a ↦ₐ w) ∗
         (if fetch_in_mem then emp else pc_a ↦ₐ{dq} w) ∗
         ([∗ map] a↦revoked ∈ shadow', a ↦ₛ revoked) ∗
         ([∗ set] a ∈ sperm, shadow_store_perm a) ∗
         deref_witness_res dw ∗
         [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
   Proof.
     iIntros (Hinstr Hvpc Dregs Hmem_pc HaStore φ) "(>HPC & >Hmem & >Hfetch & >Hshadow & Hperms & Hdw & >Hmap) Hφ".
     iApply wp_lift_atomic_base_step_no_fork; auto.
     iIntros (σ1 ns l1 l2 nt) "Hσ /=".
     destruct σ1 as [ [ [ [pc r] sr] m] st]; cbn.
     iDestruct "Hσ" as (lpc lreg lmem R C) "(HPCa & Hr & Hsr & Hm & Hst & HR & HC & %Her)".
     iDestruct (PC_agree with "HPCa HPC") as %->.
     pose proof (erasure_pc_correct _ _ _ _ _ _ Her Hvpc) as Hpc. cbn in Hpc. subst pc.
     iDestruct (deref_witness_lookup with "HR Hdw") as %Hdw.
    iEval (rewrite /sreg /shadowtbl /=) in "Hsr Hst".
     iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hlregs.
     pose proof (erasure_regs_incl _ _ _ _ _ _ _ Her Hlregs) as Hregs.
     iDestruct (gen_heap_valid_inclSepM with "Hm Hmem") as %Hlmem.
     iDestruct (gen_heap_valid_inclSepM with "Hst Hshadow") as %Hshadow_incl.
     pose proof (er_mmio _ _ _ _ _ _ Her) as Hmmio; cbn in Hmmio.

     (* Derive necessary register values in r *)
     specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri. unfold regs_of in Hri.
     odestruct (Hri r1) as [r1v [Hr'1 _]]; first by set_solver+.
     iAssert (⌜lmem !! pc_a = Some w⌝)%I as %Hlmem_pc.
     { destruct fetch_in_mem.
       - iPureIntro. by eapply lookup_weaken.
       - iApply (gen_heap_valid with "Hm Hfetch"). }
     destruct (erasure_lookup_mem _ _ _ _ _ _ _ _ Her Hlmem_pc) as (pw & Hpw & Hpwok).

     iModIntro. iSplitR; first (by iPureIntro; apply normal_always_base_reducible).
     iNext. iIntros (e2 σ2 efs Hpstep).
     apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
     iIntros "_".
     iSplitR; auto. eapply step_exec_inv in Hstep; eauto.
     rewrite (mem_word_ok_decode _ _ _ _ Hpwok) Hinstr in Hstep.
     destruct (llookup_reg_phys _ _ _ _ _ Hregs Hr'1) as (s1 & Hr1 & Hrel1).
     rewrite /exec /= Hr1 /= in Hstep.

     (* Now we start splitting on the different cases in the Store spec, and prove them one at a time *)

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
     2: { (* Failure: r1 is not a capability *)
       assert ((Failed, (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st)) = (c, σ2)) as Hstep'.
       { unfold is_cap in Hr1v. destruct r1v as [r1v ?]. cbn in *.
         destruct_word r1v; by simplify_pair_eq. }
       store_fail Hstep'. by eapply Store_fail_const.
     }
     destruct r1v as [[ | [t p g b e a | ] | | ] π1]; try inversion Hr1v. clear Hr1v. cbn in Hstep.
     destruct t.
     2: { rewrite ?andb_false_r in Hstep.
          store_fail Hstep. eapply Store_fail_tag. by rewrite Hr'1. }
     destruct s1.
     2: { (* The physical copy of the destination is untagged. *)
       cbn in Hstep. store_fail Hstep.
       destruct (decide (π1 = deref_id dw)) as [Hπ|Hπ]; last by eapply Store_fail_revoked.
       destruct (a + imm)%a as [ea|] eqn:Hadd.
       2: by eapply Store_fail_addr; [rewrite Hr'1 | done].
       destruct (withinBounds b e ea) eqn:Hwb.
       2: by eapply Store_fail_bounds; [rewrite Hr'1 | done | right].
       (* A stripped destination under its witness is a heap capability
          without authority: its bounds are empty. *)
       exfalso.
       destruct Hrel1 as [[Heq | [_ [[Hst _] | [Hna [base Hh]]]]] _]; cbn in *; try discriminate.
       { by apply (deref_witness_not_stale R dw (WCap true p g b e a @@? π1)). }
       assert (is_heap_address b = true) as Hbh.
       { rewrite /heap_cap_base /= in Hh. by destruct (is_heap_address b). }
       apply withinBounds_true_iff in Hwb. apply Hna. split; first done. exists b.
       apply heap_authority_base_memory_cap_bounds. exists e. split; first done.
       split; [solve_addr | done]. }
     cbn in Hstep.
     destruct (a + imm)%a as [ea|] eqn:Hadd.
     2: { store_fail Hstep. eapply Store_fail_addr; last done. by rewrite Hr'1. }
     cbn in Hstep.

     destruct (writeAllowed p && withinBounds b e ea) eqn:HWA.
     2 : { (* Failure: the destination is out of bounds or does not allow writing *)
       apply andb_false_iff in HWA.
       store_fail Hstep. eapply Store_fail_bounds; eauto. by rewrite Hr'1.
     }
     apply andb_true_iff in HWA; destruct HWA as (Hwa & Hwb).

     assert (Hallow : reg_allows_store_imm regs r1 imm p g b e a ea)
       by (repeat split; auto; by rewrite Hr'1).
     specialize (HaStore p g b e a ea storev Hallow HSV).
     destruct (is_shadow_address ea) eqn:Hshadow.
     - (* Shadow-table store: the capability addresses the shadow region,
          while its points-to is indexed by the corresponding heap address. *)
       destruct (proj2 (shadow_to_heap_domain ea) Hshadow) as [heap_a Htranslate].
       rewrite Htranslate /= in Hstep.
       destruct storev as [[z | | |] πs]; cbn in Hstep.
       2,3,4: store_fail Hstep;
         eapply Store_fail_invalid_shadow; [by rewrite Hr'1|done|done|exact HSV|by intros ? ?].
       set (status := decodeAllocStatus z).
       destruct HaStore as (heap_a' & Htranslate' & [old_revoked Hshadowa] & Hallowed);
         first by eexists.
       assert (heap_a' = heap_a) as -> by congruence.
       specialize (Hallowed z eq_refl).
       assert (st !! heap_a = Some old_revoked) as Hsta.
       { eapply lookup_weaken; [exact Hshadowa|exact Hshadow_incl]. }
       iAssert (⌜shadow_store_ok R C st heap_a status⌝)%I as %Hsok.
       { destruct Hallowed as [Hsame | Hin].
         - iPureIntro. left. by eapply lookup_weaken.
         - iApply (shadow_store_perms_ok with "HR HC Hperms"); done. }
       pose proof (erasure_shadow_store _ _ _ _ _ _ _ _ _ _ heap_a status Her ltac:(eauto) Hsok) as Her1.
       rewrite /update_shadowtbl /= in Hstep.
       destruct (incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π)) as [lpc'|] eqn:Hregs'.
       2: {
         pose proof Hregs' as Ha'. eapply incrementPC_None_inv in Ha'; [|reflexivity].
         unfold updatePC, updatePC_gen in Hstep; cbn in Hstep; rewrite Ha' in Hstep.
         store_fail Hstep. by apply Store_fail_invalid_PC. }
       destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ Her1 Hregs') as (pc'' & Hu & Her2).
       pose proof Hregs' as Ha'.
       apply incrementPC_Some_inv in Ha' as (t' & p' & g' & b' & e' & a' & a'1 & π' & Heq & Ha'1 & ->).
       injection Heq as <- <- <- <- <- <- <-.
       rewrite /updatePC /updatePC_gen /= Ha'1 in Hu. simplify_eq.
       unfold updatePC, updatePC_gen in Hstep; cbn in Hstep; rewrite Ha'1 in Hstep.
       simplify_pair_eq. cbn.
       iDestruct (big_sepM_delete _ _ heap_a with "Hshadow") as "[Ha Hshadow]"; first exact Hshadowa.
       iMod (gen_heap_update with "Hst Ha") as "[Hst Ha]".
       iDestruct (big_sepM_insert _ _ heap_a with "[$Hshadow $Ha]") as "Hshadow".
       { apply lookup_delete_eq. }
       iEval (rewrite insert_delete_eq) in "Hshadow".
       iMod (PC_update _ _ (WCap true pc_p pc_g pc_b pc_e a'1 @@? pc_π) with "HPCa HPC") as "[HPCa HPC]".
       iModIntro. iSplitR "Hφ HPC Hmem Hfetch Hshadow Hperms Hdw Hmap".
       { iExists _, _, lmem, R, C. iFrame. done. }
       iApply "Hφ". iFrame.
       iPureIntro. eapply Store_spec_success_shadow; eauto.
     - (* Ordinary-memory store *)
       destruct HaStore as [oldv Hmema].
       assert (lmem !! ea = Some oldv) as Hlmea by by eapply lookup_weaken.
       destruct (erasure_lookup_mem _ _ _ _ _ _ _ _ Her Hlmea) as (pwea & Hmea & _).
       rewrite (mem_avoids_mmio_not_revoker _ _ _ Hmmio Hmea) in Hstep.
       rewrite /update_mem /= in Hstep.
       pose proof (erasure_store _ _ _ _ _ _ _ _ _ _ ea (lstore_word p storev) _ _ Her Hlmea
         (reg_phys_mem_word_ok _ _ _ _ (reg_word_ok_lstore_word _ _ p _ Hstore_ok)
            (reg_phys_lstore_word _ p _ _ Hrelv))) as Her1.
       destruct (incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π)) as [lpc'|] eqn:Hregs'.
       2: {
         pose proof Hregs' as Ha'. eapply incrementPC_None_inv in Ha'; [|reflexivity].
         unfold updatePC, updatePC_gen in Hstep; cbn in Hstep; rewrite Ha' in Hstep.
         store_fail Hstep. by apply Store_fail_invalid_PC. }
       destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ Her1 Hregs') as (pc'' & Hu & Her2).
       pose proof Hregs' as Ha'.
       apply incrementPC_Some_inv in Ha' as (t' & p' & g' & b' & e' & a' & a'1 & π' & Heq & Ha'1 & ->).
       injection Heq as <- <- <- <- <- <- <-.
       rewrite /updatePC /updatePC_gen /= Ha'1 in Hu. simplify_eq.
       unfold updatePC, updatePC_gen in Hstep; cbn in Hstep; rewrite Ha'1 in Hstep.
       simplify_pair_eq. cbn.
       iMod ((gen_heap_update_inSepM _ _ ea) with "Hm Hmem") as "[Hm Hmem]"; eauto.
       iMod (PC_update _ _ (WCap true pc_p pc_g pc_b pc_e a'1 @@? pc_π) with "HPCa HPC") as "[HPCa HPC]".
       iModIntro. iSplitR "Hφ HPC Hmem Hfetch Hshadow Hperms Hdw Hmap".
       { iExists _, _, _, R, C. iFrame. done. }
       iApply "Hφ". iFrame.
       iPureIntro. eapply Store_spec_success; eauto.
   Qed.

   Lemma wp_store_shadow_imm Ep
     pc_p pc_g pc_b pc_e pc_a pc_π
     r1 (r2 : Z + RegName) (imm : Z) w mem regs shadow (sperm : gset Addr) dw :
   decodeInstrW w.(lw) = Store r1 r2 imm →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Store r1 r2 imm) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_store_mem_or_shadow_imm r1 r2 imm regs mem shadow sperm →

   {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
       (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
       (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ revoked) ∗
       ([∗ set] a ∈ sperm, shadow_store_perm a) ∗
       deref_witness_res dw ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ lpc' mem' shadow' retv, RET retv;
       ⌜ Store_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm lpc' mem mem' shadow shadow' dw retv⌝ ∗
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
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Store r1 r2 imm) ⊆ dom regs →
   allow_store_mem_or_shadow_imm r1 r2 imm regs mem shadow sperm →

   {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
       ▷ pc_a ↦ₐ{dq} w ∗
       (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
       (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ revoked) ∗
       ([∗ set] a ∈ sperm, shadow_store_perm a) ∗
       deref_witness_res dw ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ lpc' mem' shadow' retv, RET retv;
       ⌜ Store_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm lpc' mem mem' shadow shadow' dw retv⌝ ∗
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

  Lemma wp_store_imm Ep
     pc_p pc_g pc_b pc_e pc_a pc_π
     r1 (r2 : Z + RegName) (imm : Z) w mem regs :
   decodeInstrW w.(lw) = Store r1 r2 imm →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Store r1 r2 imm) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_store_map_or_true_imm r1 r2 imm regs mem →
   (∀ p g b e a ea, reg_allows_store_imm regs r1 imm p g b e a ea →
      is_shadow_address ea = false) →
   {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
       (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ lpc' mem' retv, RET retv;
       ⌜ Store_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm lpc' mem mem' (∅ : ShadowTbl) (∅ : ShadowTbl) DerefNoId retv⌝ ∗
         PC ↦ₚ lpc' ∗
         ([∗ map] a↦w ∈ mem', a ↦ₐ w) ∗
         [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hmem_pc HaStore Hordinary φ) "Hres Hφ".
    iDestruct "Hres" as "(HPC & Hmem & Hmap)".
    iAssert ((▷ ([∗ map] k↦revoked ∈ (∅ : ShadowTbl), k ↦ₛ revoked))%I) as "Hshadow".
    { iNext. rewrite big_sepM_empty. done. }
    assert (HaStoreOffset : allow_store_mem_or_shadow_imm r1 r2 imm regs mem (∅ : ShadowTbl) ∅).
    { intros p g b e a ea storev Hreg Harg.
      pose proof Hreg as (Hcap & Hadd & Hwa & Hwb).
      destruct (is_shadow_address ea) eqn:Hshadowea.
      - specialize (Hordinary p g b e a ea Hreg). congruence.
      - destruct (allow_store_implies_storev_imm r1 r2 mem regs p g b e a ea imm storev
          HaStore Hcap Harg Hwa Hadd Hwb) as [oldv Hlookup].
        exists oldv. exact Hlookup. }
    iApply (wp_store_shadow_imm Ep pc_p pc_g pc_b pc_e pc_a pc_π r1 r2 imm w mem regs (∅ : ShadowTbl) ∅
      DerefNoId with "[$HPC $Hmem $Hshadow $Hmap]"); try done.
    all: try (by rewrite big_sepS_empty).
    iNext. iIntros (lpc' mem' shadow' retv) "(%Hspec & HPC & Hmem' & Hshadow' & _ & _ & Hregs')".
    destruct Hspec as
      [p g b e a ea storev oldv Harg Hallow Hnotshadow Hlookup Hmem_eq Hshadow_eq Hinc
      |p g b e a ea heap_a z π old_status Harg Hallow Hshadowea Htranslate Hold Hmem_eq Hshadow_eq Hinc
      |Hmem_eq Hshadow_eq Hfail].
    - iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
    - exfalso. simplify_map_eq.
    - iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
  Qed.

  Lemma wp_store_imm_fetch Ep
     pc_p pc_g pc_b pc_e pc_a pc_π
     r1 (r2 : Z + RegName) (imm : Z) w mem regs dq :
   decodeInstrW w.(lw) = Store r1 r2 imm →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Store r1 r2 imm) ⊆ dom regs →
   allow_store_map_or_true_imm r1 r2 imm regs mem →
   (∀ p g b e a ea, reg_allows_store_imm regs r1 imm p g b e a ea →
      is_shadow_address ea = false) →
   {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
       ▷ pc_a ↦ₐ{dq} w ∗
       (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ lpc' mem' retv, RET retv;
       ⌜ Store_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm lpc' mem mem' (∅ : ShadowTbl) (∅ : ShadowTbl) DerefNoId retv⌝ ∗
         PC ↦ₚ lpc' ∗
         pc_a ↦ₐ{dq} w ∗
         ([∗ map] a↦w ∈ mem', a ↦ₐ w) ∗
         [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs HaStore Hordinary φ) "(HPC & Hfetch & Hmem & Hmap) Hφ".
    iAssert ((▷ ([∗ map] k↦revoked ∈ (∅ : ShadowTbl), k ↦ₛ revoked))%I) as "Hshadow".
    { iNext. rewrite big_sepM_empty. done. }
    assert (HaStoreOffset : allow_store_mem_or_shadow_imm r1 r2 imm regs mem (∅ : ShadowTbl) ∅).
    { intros p g b e a ea storev Hreg Harg.
      pose proof Hreg as (Hcap & Hadd & Hwa & Hwb).
      destruct (is_shadow_address ea) eqn:Hshadowea.
      - specialize (Hordinary p g b e a ea Hreg). congruence.
      - destruct (allow_store_implies_storev_imm r1 r2 mem regs p g b e a ea imm storev
          HaStore Hcap Harg Hwa Hadd Hwb) as [oldv Hlookup].
        exists oldv. exact Hlookup. }
    iApply (wp_store_shadow_imm_fetch Ep pc_p pc_g pc_b pc_e pc_a pc_π r1 r2 imm w mem regs (∅ : ShadowTbl) ∅
      _ DerefNoId with "[$HPC $Hfetch $Hmem $Hshadow $Hmap]"); try done.
    all: try (by rewrite big_sepS_empty).
    iNext. iIntros (lpc' mem' shadow' retv) "(%Hspec & HPC & Hfetch & Hmem' & Hshadow' & _ & _ & Hregs')".
    destruct Hspec as
      [p g b e a ea storev oldv Harg Hallow Hnotshadow Hlookup Hmem_eq Hshadow_eq Hinc
      |p g b e a ea heap_a z π old_status Harg Hallow Hshadowea Htranslate Hold Hmem_eq Hshadow_eq Hinc
      |Hmem_eq Hshadow_eq Hfail].
    - iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
    - exfalso. simplify_map_eq.
    - iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
  Qed.

  Lemma wp_store_imm_fetch_dw Ep
     pc_p pc_g pc_b pc_e pc_a pc_π
     r1 (r2 : Z + RegName) (imm : Z) w mem regs dq dw :
   decodeInstrW w.(lw) = Store r1 r2 imm →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Store r1 r2 imm) ⊆ dom regs →
   allow_store_map_or_true_imm r1 r2 imm regs mem →
   (∀ p g b e a ea, reg_allows_store_imm regs r1 imm p g b e a ea →
      is_shadow_address ea = false) →
   {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
       ▷ pc_a ↦ₐ{dq} w ∗
       (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
       deref_witness_res dw ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ lpc' mem' retv, RET retv;
       ⌜ Store_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm lpc' mem mem' (∅ : ShadowTbl) (∅ : ShadowTbl) dw retv⌝ ∗
         PC ↦ₚ lpc' ∗
         pc_a ↦ₐ{dq} w ∗
         ([∗ map] a↦w ∈ mem', a ↦ₐ w) ∗
         deref_witness_res dw ∗
         [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs HaStore Hordinary φ) "(HPC & Hfetch & Hmem & Hdw & Hmap) Hφ".
    iAssert ((▷ ([∗ map] k↦revoked ∈ (∅ : ShadowTbl), k ↦ₛ revoked))%I) as "Hshadow".
    { iNext. rewrite big_sepM_empty. done. }
    assert (HaStoreOffset : allow_store_mem_or_shadow_imm r1 r2 imm regs mem (∅ : ShadowTbl) ∅).
    { intros p g b e a ea storev Hreg Harg.
      pose proof Hreg as (Hcap & Hadd & Hwa & Hwb).
      destruct (is_shadow_address ea) eqn:Hshadowea.
      - specialize (Hordinary p g b e a ea Hreg). congruence.
      - destruct (allow_store_implies_storev_imm r1 r2 mem regs p g b e a ea imm storev
          HaStore Hcap Harg Hwa Hadd Hwb) as [oldv Hlookup].
        exists oldv. exact Hlookup. }
    iApply (wp_store_shadow_imm_fetch Ep pc_p pc_g pc_b pc_e pc_a pc_π r1 r2 imm w mem regs (∅ : ShadowTbl) ∅
      _ dw with "[$HPC $Hfetch $Hmem $Hshadow $Hdw $Hmap]"); try done.
    all: try (by rewrite big_sepS_empty).
    iNext. iIntros (lpc' mem' shadow' retv) "(%Hspec & HPC & Hfetch & Hmem' & Hshadow' & _ & Hdw & Hregs')".
    destruct Hspec as
      [p g b e a ea storev oldv Harg Hallow Hnotshadow Hlookup Hmem_eq Hshadow_eq Hinc
      |p g b e a ea heap_a z π old_status Harg Hallow Hshadowea Htranslate Hold Hmem_eq Hshadow_eq Hinc
      |Hmem_eq Hshadow_eq Hfail].
    - iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
    - exfalso. simplify_map_eq.
    - iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
  Qed.

  Lemma wp_store Ep
     pc_p pc_g pc_b pc_e pc_a pc_π
     r1 (r2 : Z + RegName) w mem regs shadow sperm :
   decodeInstrW w.(lw) = Store r1 r2 0 →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Store r1 r2 0) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_store_mem_or_shadow r1 r2 regs mem shadow sperm →
   {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
       (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
       (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ revoked) ∗
       ([∗ set] a ∈ sperm, shadow_store_perm a) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ lpc' mem' shadow' retv, RET retv;
       ⌜ Store_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 0 lpc' mem mem' shadow shadow' DerefNoId retv ⌝ ∗
         PC ↦ₚ lpc' ∗
         ([∗ map] a↦w ∈ mem', a ↦ₐ w) ∗
         ([∗ map] a↦revoked ∈ shadow', a ↦ₛ revoked) ∗
         ([∗ set] a ∈ sperm, shadow_store_perm a) ∗
         [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hmem_pc Hallow φ) "Hres Hφ".
    assert (Hallow0 : allow_store_mem_or_shadow_imm r1 r2 0 regs mem shadow sperm).
    { intros p g b e a ea storev Hreg Harg.
      unfold reg_allows_store_imm in Hreg.
      destruct Hreg as (Hdst & Hadd & Hwa & Hwb).
      rewrite finz_add_0 in Hadd. inversion Hadd; subst ea.
      specialize (Hallow p g b e a storev ltac:(repeat split; assumption) Harg).
      destruct (is_shadow_address a); auto. }
    iDestruct "Hres" as "(HPC & Hmem & Hshadow & Hperms & Hmap)".
    iApply (wp_store_shadow_imm Ep pc_p pc_g pc_b pc_e pc_a pc_π r1 r2 0 w mem regs shadow sperm
      DerefNoId with "[$HPC $Hmem $Hshadow $Hperms $Hmap]"); try done.
    iNext. iIntros (lpc' mem' shadow' retv) "(Hspec & HPC & Hmem & Hshadow & Hperms & _ & Hmap)".
    iApply "Hφ". iFrame.
  Qed.

  Lemma wp_store_fetch Ep
     pc_p pc_g pc_b pc_e pc_a pc_π
     r1 (r2 : Z + RegName) w mem regs shadow sperm dq :
   decodeInstrW w.(lw) = Store r1 r2 0 →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Store r1 r2 0) ⊆ dom regs →
   allow_store_mem_or_shadow r1 r2 regs mem shadow sperm →
   {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
       ▷ pc_a ↦ₐ{dq} w ∗
       (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
       (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ revoked) ∗
       ([∗ set] a ∈ sperm, shadow_store_perm a) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ lpc' mem' shadow' retv, RET retv;
       ⌜ Store_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 0 lpc' mem mem' shadow shadow' DerefNoId retv ⌝ ∗
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

  Lemma wp_store_success_mem_imm E pc_p pc_g pc_b pc_e pc_a pc_π
    dst src imm w regs lpc' mem p g b e a ea storev oldv :
    decodeInstrW w.(lw) = Store dst src imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Store dst src imm) ⊆ dom regs →
    mem !! pc_a = Some w →
    reg_allows_store_imm regs dst imm p g b e a ea →
    (∀ v : LWord, regs !!ₗ dst = Some v → v.(lprov) = None) →
    lword_of_argument regs src = Some storev →
    is_shadow_address ea = false →
    mem !! ea = Some oldv →
    incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ lpc' ∗
        ([∗ map] a↦w ∈ <[ea:=lstore_word p storev]> mem, a ↦ₐ w) ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hmem Hallow Hnoid Harg Hshadow Hlookup Hinc φ)
      "(>HPC & >Hmem & >Hmap) Hφ".
    iAssert ((▷ ([∗ map] k↦revoked ∈ (∅ : ShadowTbl), k ↦ₛ revoked))%I) as "Hshadow".
    { iNext. rewrite big_sepM_empty. done. }
    iAssert ([∗ set] a ∈ (∅ : gset Addr), shadow_store_perm a)%I as "Hperms".
    { by rewrite big_sepS_empty. }
    iApply (wp_store_shadow_imm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DerefNoId with "[$HPC $Hmem $Hshadow $Hperms $Hmap]"); eauto.
    { intros p0 g0 b0 e0 a0 ea0 v0 (Hdst0 & Hadd0 & _) Harg0.
      destruct Hallow as (Hdst & Hadd & Hwa & Hwb).
      rewrite Hdst in Hdst0. inversion Hdst0; subst.
      rewrite Hadd in Hadd0. inversion Hadd0; subst.
      rewrite Hshadow. by eexists. }
    iNext. iIntros (lpc0 mem0 shadow0 retv) "(%Hspec & HPC & Hmem & _ & _ & _ & Hmap)".
    destruct Hallow as (Hdst & Hadd & Hwa & Hwb).
    destruct Hspec as
      [p0 g0 b0 e0 a0 ea0 v0 oldv0 Harg0 (Hdst0 & Hadd0 & _) Hshadow0 Hlookup0 -> -> Hinc0
      |p0 g0 b0 e0 a0 ea0 heap_a0 z0 π0 old_status0 Harg0 (Hdst0 & Hadd0 & _) Hshadow0 Htranslate0 Hlookup0 -> -> Hinc0
      |Hmem_eq Hshadow_eq Hfail].
    - rewrite Hdst in Hdst0. inversion Hdst0; subst.
      rewrite Hadd in Hadd0. inversion Hadd0; subst.
      rewrite Harg in Harg0. inversion Harg0; subst.
      rewrite Hinc in Hinc0. inversion Hinc0; subst.
      iApply "Hφ". iFrame.
    - rewrite Hdst in Hdst0. inversion Hdst0; subst.
      rewrite Hadd in Hadd0. inversion Hadd0; subst. congruence.
    - exfalso. eapply (Store_failure_impossible _ _ _ _ _ _ DerefNoId p g b e a ea Hdst Hnoid); eauto.
      all: try congruence.
  Qed.

    Lemma wp_store_success_reg_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst src w'
         p g b e a ea (imm : Z) w'' dq :
     π = None →
     is_shadow_address ea = false →
      decodeInstrW w.(lw) = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e ea = true →
     (a + imm)%a = Some ea →
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ WCap true p g b e a @@? π
           ∗ ▷ ea ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ{dq} w
              ∗ src ↦ᵣ w''
              ∗ dst ↦ᵣ WCap true p g b e a @@? π
              ∗ ea ↦ₐ lstore_word p w'' }}}.
    Proof.
      iIntros (-> Hshadow Hinstr Hvpc Hpca' Hwa Hwb Hadd ?? φ)
             "(>HPC & >Hi & >Hsrc & >Hdst & >Hsrca) Hφ".
    iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %]".
    iDestruct (pointsto_ne with "Hsrca Hi") as %Hne_pc.
    pose proof (not_eq_sym Hne_pc).
    iDestruct (memMap_resource_1 with "Hsrca") as "Hmem".

    iApply (wp_store_imm_fetch _ pc_p pc_g with "[$HPC $Hi $Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try (intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & _); simplify_map_eq; congruence).
    all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    { eapply mem_eq_implies_allow_store_map_imm with (a := a) (ea := ea); eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (lpc' mem' retv) "(#Hspec & HPC & Hi & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec; try (simplify_map_eq; congruence).
     { (* Success *)
       iApply "Hφ".
       match goal with Hra : reg_allows_store_imm _ _ _ _ _ _ _ _ _ |- _ => destruct Hra as [? [Hadd2 _]] end; simplify_map_eq.
       try iEval (rewrite insert_insert_eq) in "Hmem".
       iDestruct (memMap_resource_1 with "Hmem") as "Ha".
       try incrementPC_inv.
       simplify_map_eq.
       try iEval (rewrite insert_insert_eq) in "Hmem".
       iRegsMap "Hmap".
       all: iFrame. }
     { (* Failure (contradiction) *)
       exfalso.
       eapply (Store_failure_impossible _ _ _ _ _ _ DerefNoId p g b e a ea); eauto.
       - by simplify_map_eq.
       - by intros ? ?; simplify_map_eq.
       - intros Hnone. rewrite /incrementPC /incrementPC_gen in Hnone.
         simplify_map_eq.

     }
    Qed.

Lemma wp_store_success_reg_store_word_imm_dw E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst src w'
         p g b e a ea (imm : Z) w'' dq dw :
     π = deref_id dw →
     is_shadow_address ea = false →
      decodeInstrW w.(lw) = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e ea = true →
     (a + imm)%a = Some ea →
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ WCap true p g b e a @@? π
           ∗ ▷ ea ↦ₐ w'
           ∗ deref_witness_res dw }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ{dq} w
              ∗ src ↦ᵣ w''
              ∗ dst ↦ᵣ WCap true p g b e a @@? π
              ∗ ea ↦ₐ lstore_word p w''
              ∗ deref_witness_res dw }}}.
    Proof.
      iIntros (-> Hshadow Hinstr Hvpc Hpca' Hwa Hwb Hadd ?? φ)
             "(>HPC & >Hi & >Hsrc & >Hdst & >Hsrca & Hdw) Hφ".
    iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %]".
    iDestruct (pointsto_ne with "Hsrca Hi") as %Hne_pc.
    pose proof (not_eq_sym Hne_pc).
    iDestruct (memMap_resource_1 with "Hsrca") as "Hmem".

    iApply (wp_store_imm_fetch_dw _ pc_p pc_g with "[$HPC $Hi $Hmap $Hmem $Hdw]"); eauto; simplify_map_eq; eauto;
      try (intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & _); simplify_map_eq; congruence).
    all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    { eapply mem_eq_implies_allow_store_map_imm with (a := a) (ea := ea); eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (lpc' mem' retv) "(#Hspec & HPC & Hi & Hmem & Hdw & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec; try (simplify_map_eq; congruence).
     { (* Success *)
       iApply "Hφ".
       match goal with Hra : reg_allows_store_imm _ _ _ _ _ _ _ _ _ |- _ => destruct Hra as [? [Hadd2 _]] end; simplify_map_eq.
       try iEval (rewrite insert_insert_eq) in "Hmem".
       iDestruct (memMap_resource_1 with "Hmem") as "Ha".
       try incrementPC_inv.
       simplify_map_eq.
       try iEval (rewrite insert_insert_eq) in "Hmem".
       iRegsMap "Hmap".
       all: iFrame. }
     { (* Failure (contradiction) *)
       exfalso.
       eapply (Store_failure_impossible _ _ _ _ _ _ dw p g b e a ea); eauto.
       - by simplify_map_eq.
       - by intros ? ?; simplify_map_eq.
       - intros Hnone. rewrite /incrementPC /incrementPC_gen in Hnone.
         simplify_map_eq.

     }
    Qed.

   Lemma wp_store_success_reg_same_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst w'
         p g b e a ea (imm : Z) dq :
     π = None →
     is_shadow_address ea = false →
     decodeInstrW w.(lw) = Store dst (inr dst) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e ea = true →
     (a + imm)%a = Some ea →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ dst ↦ᵣ WCap true p g b e a @@? π
           ∗ ▷ ea ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ{dq} w
              ∗ dst ↦ᵣ WCap true p g b e a @@? π
              ∗ ea ↦ₐ lstore_word p (WCap true p g b e a @@? π) }}}.
   Proof.
    iIntros (-> Hshadow Hinstr Hvpc Hpca' Hwa Hwb Hadd ? φ)
             "(>HPC & >Hi & >Hdst & >Hsrca) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iDestruct (pointsto_ne with "Hsrca Hi") as %Hne_pc.
    pose proof (not_eq_sym Hne_pc).
    iDestruct (memMap_resource_1 with "Hsrca") as "Hmem".

    iApply (wp_store_imm_fetch _ pc_p pc_g with "[$HPC $Hi $Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try (intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & _); simplify_map_eq; congruence).
    all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    { eapply mem_eq_implies_allow_store_map_imm with (a := a) (ea := ea); eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (lpc' mem' retv) "(#Hspec & HPC & Hi & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec; try (simplify_map_eq; congruence).
     { (* Success *)
       iApply "Hφ".
       match goal with Hra : reg_allows_store_imm _ _ _ _ _ _ _ _ _ |- _ => destruct Hra as [Hrr2 [Hadd2 _]] end. simplify_map_eq.
       try iEval (rewrite insert_insert_eq) in "Hmem".
       iDestruct (memMap_resource_1 with "Hmem") as "Ha".
       try incrementPC_inv.
       simplify_map_eq.
       try iEval (rewrite insert_insert_eq) in "Hmem".
       iRegsMap "Hmap".
       all: iFrame. }
     { (* Failure (contradiction) *)
       exfalso.
       eapply (Store_failure_impossible _ _ _ _ _ _ DerefNoId p g b e a ea); eauto.
       - by simplify_map_eq.
       - by intros ? ?; simplify_map_eq.
       - intros Hnone. rewrite /incrementPC /incrementPC_gen in Hnone.
         simplify_map_eq.

     }
    Qed.

   Lemma wp_store_success_z_imm E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst z w'
         p g b e a ea (imm : Z) dq :
     π = None →
     is_shadow_address ea = false →
     decodeInstrW w.(lw) = Store dst (inl z) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e ea = true →
     (a + imm)%a = Some ea →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ dst ↦ᵣ WCap true p g b e a @@? π
           ∗ ▷ ea ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ{dq} w
              ∗ dst ↦ᵣ WCap true p g b e a @@? π
              ∗ ea ↦ₐ WInt z }}}.
   Proof.
     iIntros (-> Hshadow Hinstr Hvpc Hpca' Hwa Hwb Hadd ? φ)
             "(>HPC & >Hi & >Hdst & >Hsrca) Hφ".
     have Hstore_word : lstore_word p (WInt z) = WInt z.
     { apply lstore_word_canStore, writeAllowed_canStore_int, Hwa. }
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iDestruct (pointsto_ne with "Hsrca Hi") as %Hne_pc.
    pose proof (not_eq_sym Hne_pc).
    iDestruct (memMap_resource_1 with "Hsrca") as "Hmem".

    iApply (wp_store_imm_fetch _ pc_p pc_g with "[$HPC $Hi $Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try (intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & _); simplify_map_eq; congruence).
    all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    { eapply mem_eq_implies_allow_store_map_imm with (a := a) (ea := ea); eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (lpc' mem' retv) "(#Hspec & HPC & Hi & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec; try (simplify_map_eq; congruence).
     { (* Success *)
       iApply "Hφ".
       match goal with Hra : reg_allows_store_imm _ _ _ _ _ _ _ _ _ |- _ => destruct Hra as [Hrr2 [Hadd2 _]] end. simplify_map_eq.
       try iEval (rewrite insert_insert_eq) in "Hmem".
       iDestruct (memMap_resource_1 with "Hmem") as "Ha".
       try incrementPC_inv.
       simplify_map_eq.
       try iEval (rewrite insert_insert_eq) in "Hmem".
       iRegsMap "Hmap".
       all: try rewrite Hstore_word; iFrame. }
     { (* Failure (contradiction) *)
       exfalso.
       eapply (Store_failure_impossible _ _ _ _ _ _ DerefNoId p g b e a ea); eauto.
       - by simplify_map_eq.
       - by intros ? ?; simplify_map_eq.
       - intros Hnone. rewrite /incrementPC /incrementPC_gen in Hnone.
         simplify_map_eq.
     }
    Qed.

Lemma wp_store_success_z_imm_dw E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst z w'
         p g b e a ea (imm : Z) dq dw :
     π = deref_id dw →
     is_shadow_address ea = false →
     decodeInstrW w.(lw) = Store dst (inl z) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e ea = true →
     (a + imm)%a = Some ea →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ dst ↦ᵣ WCap true p g b e a @@? π
           ∗ ▷ ea ↦ₐ w'
           ∗ deref_witness_res dw }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ{dq} w
              ∗ dst ↦ᵣ WCap true p g b e a @@? π
              ∗ ea ↦ₐ WInt z
              ∗ deref_witness_res dw }}}.
   Proof.
     iIntros (-> Hshadow Hinstr Hvpc Hpca' Hwa Hwb Hadd ? φ)
             "(>HPC & >Hi & >Hdst & >Hsrca & Hdw) Hφ".
     have Hstore_word : lstore_word p (WInt z) = WInt z.
     { apply lstore_word_canStore, writeAllowed_canStore_int, Hwa. }
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iDestruct (pointsto_ne with "Hsrca Hi") as %Hne_pc.
    pose proof (not_eq_sym Hne_pc).
    iDestruct (memMap_resource_1 with "Hsrca") as "Hmem".

    iApply (wp_store_imm_fetch_dw _ pc_p pc_g with "[$HPC $Hi $Hmap $Hmem $Hdw]"); eauto; simplify_map_eq; eauto;
      try (intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & _); simplify_map_eq; congruence).
    all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    { eapply mem_eq_implies_allow_store_map_imm with (a := a) (ea := ea); eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (lpc' mem' retv) "(#Hspec & HPC & Hi & Hmem & Hdw & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec; try (simplify_map_eq; congruence).
     { (* Success *)
       iApply "Hφ".
       match goal with Hra : reg_allows_store_imm _ _ _ _ _ _ _ _ _ |- _ => destruct Hra as [Hrr2 [Hadd2 _]] end. simplify_map_eq.
       try iEval (rewrite insert_insert_eq) in "Hmem".
       iDestruct (memMap_resource_1 with "Hmem") as "Ha".
       try incrementPC_inv.
       simplify_map_eq.
       try iEval (rewrite insert_insert_eq) in "Hmem".
       iRegsMap "Hmap".
       all: try rewrite Hstore_word; iFrame. }
     { (* Failure (contradiction) *)
       exfalso.
       eapply (Store_failure_impossible _ _ _ _ _ _ dw p g b e a ea); eauto.
       - by simplify_map_eq.
       - by intros ? ?; simplify_map_eq.
       - intros Hnone. rewrite /incrementPC /incrementPC_gen in Hnone.
         simplify_map_eq.
     }
    Qed.

   Lemma wp_store_success_reg_imm E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst src w'
       p g b e a ea (imm : Z) w'' dq :
     π = None →
     is_shadow_address ea = false →
     decodeInstrW w.(lw) = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e ea = true →
     (a + imm)%a = Some ea →
     canStore p w''.(lw) = true →
     src ≠ cnull → dst ≠ cnull →
     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ WCap true p g b e a @@? π
           ∗ ▷ ea ↦ₐ w' }}}
       Instr Executable @ E
     {{{ RET NextIV;
         PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
           ∗ pc_a ↦ₐ{dq} w
           ∗ src ↦ᵣ w''
           ∗ dst ↦ᵣ WCap true p g b e a @@? π
           ∗ ea ↦ₐ w'' }}}.
   Proof.
     iIntros (-> Hshadow Hinstr Hvpc Hpca' Hwa Hwb Hadd HcanStore Hsrc Hdst φ) "Hres Hφ".
     iApply (wp_store_success_reg_store_word_imm with "Hres"); eauto.
     iNext. iIntros "(HPC & Hi & Hsrc & Hdst & Ha)".
     iEval (rewrite lstore_word_canStore //) in "Ha".
     iApply "Hφ". iFrame.
   Qed.

   Lemma wp_store_success_same_imm E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst z
         p g b e a (imm : Z) :
     π = None →
     is_shadow_address pc_a = false →
     decodeInstrW w.(lw) = Store dst (inl z) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     (a + imm)%a = Some pc_a →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ WCap true p g b e a @@? π }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ (WInt z)
              ∗ dst ↦ᵣ WCap true p g b e a @@? π }}}.
    Proof.
     iIntros (-> Hshadow Hinstr Hvpc Hpca' Hwa Hwb Hadd ? φ)
            "(>HPC & >Hi & >Hdst) Hφ".
     have Hstore_word : lstore_word p (WInt z) = WInt z.
     { apply lstore_word_canStore, writeAllowed_canStore_int, Hwa. }
     iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
     iDestruct (memMap_resource_1 with "Hi") as "Hmem".

    iApply (wp_store_imm _ pc_p pc_g with "[$HPC $Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try (intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & _); simplify_map_eq; congruence).
    all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    { eapply mem_eq_implies_allow_store_map_imm; eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (lpc' mem' retv) "(#Hspec & HPC & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec; try (simplify_map_eq; congruence).
     { (* Success *)
       iApply "Hφ".
       match goal with Hra : reg_allows_store_imm _ _ _ _ _ _ _ _ _ |- _ => destruct Hra as [? [Hadd2 _]] end; simplify_map_eq.
       rewrite memMap_resource_1.
       try incrementPC_inv.
       simplify_map_eq.
       try iEval (rewrite insert_insert_eq) in "Hmem".
       iRegsMap "Hmap".
       all: try rewrite Hstore_word; iFrame. }
     { (* Failure (contradiction) *)
       exfalso.
       eapply (Store_failure_impossible _ _ _ _ _ _ DerefNoId p g b e a _); eauto.
       - by simplify_map_eq.
       - by intros ? ?; simplify_map_eq.
       - intros Hnone. rewrite /incrementPC /incrementPC_gen in Hnone.
         simplify_map_eq.
     }
     Qed.

   Lemma wp_store_success_reg_same'_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst
         p g b e a (imm : Z) :
     π = None →
     is_shadow_address pc_a = false →
     decodeInstrW w.(lw) = Store dst (inr dst) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     (a + imm)%a = Some pc_a →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ WCap true p g b e a @@? π }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ lstore_word p (WCap true p g b e a @@? π)
              ∗ dst ↦ᵣ WCap true p g b e a @@? π }}}.
   Proof.
     iIntros (-> Hshadow Hinstr Hvpc Hpca' Hwa Hwb Hadd ? φ)
            "(>HPC & >Hi & >Hdst) Hφ".
     iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
     iDestruct (memMap_resource_1 with "Hi") as "Hmem".

    iApply (wp_store_imm _ pc_p pc_g with "[$HPC $Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try (intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & _); simplify_map_eq; congruence).
    all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    { eapply mem_eq_implies_allow_store_map_imm; eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (lpc' mem' retv) "(#Hspec & HPC & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec; try (simplify_map_eq; congruence).
     { (* Success *)
       iApply "Hφ".
       match goal with Hra : reg_allows_store_imm _ _ _ _ _ _ _ _ _ |- _ => destruct Hra as [? [Hadd2 _]] end; simplify_map_eq.
       rewrite memMap_resource_1.
       try incrementPC_inv.
       simplify_map_eq.
       try iEval (rewrite insert_insert_eq) in "Hmem".
       iRegsMap "Hmap".
       all: iFrame. }
     { (* Failure (contradiction) *)
       exfalso.
       eapply (Store_failure_impossible _ _ _ _ _ _ DerefNoId p g b e a _); eauto.
       - by simplify_map_eq.
       - by intros ? ?; simplify_map_eq.
       - intros Hnone. rewrite /incrementPC /incrementPC_gen in Hnone.
         simplify_map_eq.
     }
   Qed.

   Lemma wp_store_success_reg_same_a_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst src
         p g b e a (imm : Z) w'' :
     π = None →
     is_shadow_address pc_a = false →
      decodeInstrW w.(lw) = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     (a + imm)%a = Some pc_a →
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ WCap true p g b e a @@? π }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ lstore_word p w''
              ∗ src ↦ᵣ w''
              ∗ dst ↦ᵣ WCap true p g b e a @@? π}}}.
   Proof.
     iIntros (-> Hshadow Hinstr Hvpc Hpca' Hwa Hwb Hadd ?? φ)
             "(>HPC & >Hi & >Hsrc & >Hdst) Hφ".
     iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %]".
     iDestruct (memMap_resource_1 with "Hi") as "Hmem".

    iApply (wp_store_imm _ pc_p pc_g with "[$HPC $Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try (intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & _); simplify_map_eq; congruence).
    all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    { eapply mem_eq_implies_allow_store_map_imm; eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (lpc' mem' retv) "(#Hspec & HPC & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec; try (simplify_map_eq; congruence).
     { (* Success *)
       iApply "Hφ".
       match goal with Hra : reg_allows_store_imm _ _ _ _ _ _ _ _ _ |- _ => destruct Hra as [? [Hadd2 _]] end; simplify_map_eq.
       rewrite memMap_resource_1.
       try incrementPC_inv.
       simplify_map_eq.
       try iEval (rewrite insert_insert_eq) in "Hmem".
       iRegsMap "Hmap".
       all: iFrame. }
     { (* Failure (contradiction) *)
       exfalso.
       eapply (Store_failure_impossible _ _ _ _ _ _ DerefNoId p g b e a _); eauto.
       - by simplify_map_eq.
       - by intros ? ?; simplify_map_eq.
       - intros Hnone. rewrite /incrementPC /incrementPC_gen in Hnone.
         simplify_map_eq.
     }
   Qed.

   Lemma wp_store_success_reg_same'_imm E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst
       p g b e a (imm : Z) :
     π = None →
     is_shadow_address pc_a = false →
     decodeInstrW w.(lw) = Store dst (inr dst) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     (a + imm)%a = Some pc_a →
     canStore p (WCap true p g b e a) = true →
     dst ≠ cnull →
     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ WCap true p g b e a @@? π }}}
       Instr Executable @ E
     {{{ RET NextIV;
         PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
           ∗ pc_a ↦ₐ WCap true p g b e a @@? π
           ∗ dst ↦ᵣ WCap true p g b e a @@? π }}}.
   Proof.
     iIntros (-> Hshadow Hinstr Hvpc Hpca' Hwa Hwb Hadd HcanStore Hdst φ) "Hres Hφ".
     iApply (wp_store_success_reg_same'_store_word_imm with "Hres"); eauto.
     iNext. iIntros "(HPC & Hi & Hdst)".
     iEval (rewrite lstore_word_canStore //) in "Hi".
     iApply "Hφ". iFrame.
   Qed.

   Lemma wp_store_success_reg_same_a_imm E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst src
       p g b e a (imm : Z) w'' :
     π = None →
     is_shadow_address pc_a = false →
     decodeInstrW w.(lw) = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     (a + imm)%a = Some pc_a →
     canStore p w''.(lw) = true →
     src ≠ cnull → dst ≠ cnull →
     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ WCap true p g b e a @@? π }}}
       Instr Executable @ E
     {{{ RET NextIV;
         PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
           ∗ pc_a ↦ₐ w''
           ∗ src ↦ᵣ w''
           ∗ dst ↦ᵣ WCap true p g b e a @@? π }}}.
   Proof.
     iIntros (-> Hshadow Hinstr Hvpc Hpca' Hwa Hwb Hadd HcanStore Hsrc Hdst φ) "Hres Hφ".
     iApply (wp_store_success_reg_same_a_store_word_imm with "Hres"); eauto.
     iNext. iIntros "(HPC & Hi & Hsrc & Hdst)".
     iEval (rewrite lstore_word_canStore //) in "Hi".
     iApply "Hφ". iFrame.
   Qed.

   Lemma wp_store_fail_reg_not_cap_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_π w
     dst src wdst wstore dq :
      decodeInstrW w.(lw) = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     is_cap wdst = false ->
     src ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ src ↦ᵣ wstore
           ∗ ▷ dst ↦ᵣ wdst
     }}}
       Instr Executable @ E
       {{{ RET FailedV; True}}}.
    Proof.
      iIntros (Hinstr Hvpc Hnot_cap ? φ)
             "(>HPC & >Hi & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %]".
    iAssert ([∗ map] a↦w ∈ (∅ : LMem), a ↦ₐ w)%I as "-#Hmem"; first by rewrite big_sepM_empty.

    iApply (wp_store_imm_fetch _ pc_p pc_g with "[$HPC $Hi $Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try solve [intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & Hwa0 & Hwb0);
        try (destruct (decide (dst = cnull))); simplify_map_eq; try (cbn in Hnot_cap); congruence].
    all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    { rewrite /allow_store_map_or_true_imm.
      eexists true,_,_,_,_,_,_; eauto.
      simplify_map_eq.
      split; [|split]; eauto.
      - rewrite /read_reg_inr; simplify_map_eq.
        destruct wdst as [| [] | |]; cbn in Hnot_cap; done.
      - rewrite /reg_allows_store_imm.
        destruct (_ + imm)%a; simpl; last done. simplify_map_eq.
        rewrite decide_False; auto.
        intros [].
        destruct (decide (dst = cnull)); first done.
        destruct wdst as [| [] | |]; cbn in Hnot_cap; simplify_eq.
    }
    iNext. iIntros (lpc' mem' retv) "(#Hspec & HPC & Hi & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec; try (simplify_map_eq; congruence).
     by iApply "Hφ".
     Unshelve. all: done.
    Qed.

   Lemma wp_store_fail_reg_not_cap_lword_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_π w
     dst src (wdst : LWord) wstore dq :
      decodeInstrW w.(lw) = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     is_cap wdst.(lw) = false ->
     src ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ src ↦ᵣ wstore
           ∗ ▷ dst ↦ᵣ wdst
     }}}
       Instr Executable @ E
       {{{ RET FailedV; True}}}.
    Proof.
      iIntros (Hinstr Hvpc Hnot_cap ? φ)
             "(>HPC & >Hi & >Hsrc & >Hdst) Hφ".
    destruct wdst as [wdst πd]; cbn in Hnot_cap.
    iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %]".
    iAssert ([∗ map] a↦w ∈ (∅ : LMem), a ↦ₐ w)%I as "-#Hmem"; first by rewrite big_sepM_empty.

    iApply (wp_store_imm_fetch _ pc_p pc_g with "[$HPC $Hi $Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try solve [intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & Hwa0 & Hwb0);
        try (destruct (decide (dst = cnull))); simplify_map_eq; try (cbn in Hnot_cap); congruence].
    all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    { rewrite /allow_store_map_or_true_imm.
      eexists true,_,_,_,_,_,_; eauto.
      simplify_map_eq.
      split; [|split]; eauto.
      - rewrite /read_reg_inr; simplify_map_eq.
        destruct wdst as [| [] | |]; cbn in Hnot_cap; done.
      - rewrite /reg_allows_store_imm.
        destruct (_ + imm)%a; simpl; last done. simplify_map_eq.
        rewrite decide_False; auto.
        intros [].
        destruct (decide (dst = cnull)); first done.
        destruct wdst as [| [] | |]; cbn in Hnot_cap; simplify_eq.
    }
    iNext. iIntros (lpc' mem' retv) "(#Hspec & HPC & Hi & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec; try (simplify_map_eq; congruence).
     by iApply "Hφ".
     Unshelve. all: done.
    Qed.

   Lemma wp_store_fail_reg_not_cap_lword E pc_p pc_g pc_b pc_e pc_a pc_π w
     dst src (wdst : LWord) wstore dq :
      decodeInstrW w.(lw) = Store dst (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     is_cap wdst.(lw) = false ->
     src ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ src ↦ᵣ wstore
           ∗ ▷ dst ↦ᵣ wdst
     }}}
       Instr Executable @ E
       {{{ RET FailedV; True}}}.
  Proof.
    intros. eapply wp_store_fail_reg_not_cap_lword_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

    Lemma wp_store_fail_z_not_cap_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_π w
     dst z wdst dq :
      decodeInstrW w.(lw) = Store dst (inl z) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     is_cap wdst = false ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ dst ↦ᵣ wdst
     }}}
       Instr Executable @ E
       {{{ RET FailedV; True}}}.
    Proof.
      iIntros (Hinstr Hvpc Hnot_cap ? φ)
             "(>HPC & >Hi & >Hdst) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iAssert ([∗ map] a↦w ∈ (∅ : LMem), a ↦ₐ w)%I as "-#Hmem"; first by rewrite big_sepM_empty.

    iApply (wp_store_imm_fetch _ pc_p pc_g with "[$HPC $Hi $Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try solve [intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & Hwa0 & Hwb0);
        try (destruct (decide (dst = cnull))); simplify_map_eq; try (cbn in Hnot_cap); congruence].
    all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    { rewrite /allow_store_map_or_true_imm.
      eexists true,_,_,_,_,_,_; eauto.
      simplify_map_eq.
      split; [|split]; eauto.
      - rewrite /read_reg_inr; simplify_map_eq.
        destruct wdst as [| [] | |]; cbn in Hnot_cap; done.
      - rewrite /reg_allows_store_imm.
        destruct (_ + imm)%a; simpl; last done. simplify_map_eq.
        rewrite decide_False; auto.
        intros [].
        destruct (decide (dst = cnull)); first done.
        destruct wdst as [| [] | |]; cbn in Hnot_cap; simplify_eq.
    }
    iNext. iIntros (lpc' mem' retv) "(#Hspec & HPC & Hi & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec; try (simplify_map_eq; congruence).
     by iApply "Hφ".
     Unshelve. all: done.
    Qed.

   Lemma wp_store_fail_reg_perm_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_π π w dst src
         p g b e a w'' dq :
     decodeInstrW w.(lw) = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     writeAllowed p = false ->
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ WCap true p g b e a @@? π
     }}}
       Instr Executable @ E
       {{{ RET FailedV; True}}}.
    Proof.
      iIntros (Hinstr Hvpc Hwa ?? φ)
             "(>HPC & >Hi & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %]".
    iAssert ([∗ map] a↦w ∈ (∅ : LMem), a ↦ₐ w)%I as "-#Hmem"; first by rewrite big_sepM_empty.

    iApply (wp_store_imm_fetch _ pc_p pc_g with "[$HPC $Hi $Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try solve [intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & Hwa0 & Hwb0);
        try (destruct (decide (dst = cnull))); simplify_map_eq; try (cbn in Hnot_cap); congruence].
    all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    { rewrite /allow_store_map_or_true_imm.
      eexists true,p,g,b,e,a,w''.
      split.
      { rewrite /read_reg_inr.
        by simplify_map_eq.
      }
      split.
      { rewrite /lword_of_argument.
        by simplify_map_eq.
      }
      rewrite /reg_allows_store_imm.
      destruct (a + imm)%a eqn:Haddr; simpl; last done.
      rewrite Hwa.
      rewrite decide_False; auto.
      intro; naive_solver.
      }
    iNext. iIntros (lpc' mem' retv) "(#Hspec & HPC & Hi & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec; try (simplify_map_eq; congruence).
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; by iApply "Hφ".
     }
    Qed.

    Lemma wp_store_fail_z_perm_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_π π w dst
         p g b e a z dq :
      decodeInstrW w.(lw) = Store dst (inl z) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     writeAllowed p = false ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ dst ↦ᵣ WCap true p g b e a @@? π
     }}}
       Instr Executable @ E
       {{{ RET FailedV; True}}}.
    Proof.
      iIntros (Hinstr Hvpc HcanStore ? φ)
             "(>HPC & >Hi & >Hdst) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iAssert ([∗ map] a↦w ∈ (∅ : LMem), a ↦ₐ w)%I as "-#Hmem"; first by rewrite big_sepM_empty.

    iApply (wp_store_imm_fetch _ pc_p pc_g with "[$HPC $Hi $Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try solve [intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & Hwa0 & Hwb0);
        try (destruct (decide (dst = cnull))); simplify_map_eq; try (cbn in Hnot_cap); congruence].
    all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    { rewrite /allow_store_map_or_true_imm.
      eexists true,p,g,b,e,a,_.
      split.
      { rewrite /read_reg_inr.
        by simplify_map_eq.
      }
      split.
      { rewrite /lword_of_argument.
        eauto.
      }
      rewrite /reg_allows_store_imm.
      destruct (a + imm)%a eqn:Haddr; simpl; last done.
      rewrite HcanStore.
      rewrite decide_False; auto.
      intro; naive_solver.
      }
    iNext. iIntros (lpc' mem' retv) "(#Hspec & HPC & Hi & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec; try (simplify_map_eq; congruence).
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; by iApply "Hφ".
     }
    Qed.

   Lemma wp_store_fail_reg_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_π π w dst src
         p g b e a ea w'' dq :
      decodeInstrW w.(lw) = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (a + imm)%a = Some ea →
     withinBounds b e ea = false →
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ WCap true p g b e a @@? π
     }}}
       Instr Executable @ E
       {{{ RET FailedV; True}}}.
    Proof.
      iIntros (Hinstr Hvpc Hadd Hwb ?? φ)
             "(>HPC & >Hi & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %]".
    iAssert ([∗ map] a↦w ∈ (∅ : LMem), a ↦ₐ w)%I as "-#Hmem"; first by rewrite big_sepM_empty.

    iApply (wp_store_imm_fetch _ pc_p pc_g with "[$HPC $Hi $Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try solve [intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & Hwa0 & Hwb0);
        try (destruct (decide (dst = cnull))); simplify_map_eq; try (cbn in Hnot_cap); congruence].
    all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    { rewrite /allow_store_map_or_true_imm.
      eexists true,p,g,b,e,a,w''.
      split.
      { rewrite /read_reg_inr.
        by simplify_map_eq.
      }
      split.
      { rewrite /lword_of_argument.
        by simplify_map_eq.
      }
      rewrite /reg_allows_store_imm.
      rewrite Hadd Hwb.
      rewrite decide_False; auto.
      intro; naive_solver.
      }
    iNext. iIntros (lpc' mem' retv) "(#Hspec & HPC & Hi & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec; try (simplify_map_eq; congruence).
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; by iApply "Hφ".
     }
    Qed.

    Lemma wp_store_fail_z_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_π π w dst
         p g b e a ea z dq :
      decodeInstrW w.(lw) = Store dst (inl z) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (a + imm)%a = Some ea →
     withinBounds b e ea = false →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ dst ↦ᵣ WCap true p g b e a @@? π
     }}}
       Instr Executable @ E
       {{{ RET FailedV; True}}}.
    Proof.
      iIntros (Hinstr Hvpc Hadd Hwb ? φ)
             "(>HPC & >Hi & >Hdst) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iAssert ([∗ map] a↦w ∈ (∅ : LMem), a ↦ₐ w)%I as "-#Hmem"; first by rewrite big_sepM_empty.

    iApply (wp_store_imm_fetch _ pc_p pc_g with "[$HPC $Hi $Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try solve [intros p0 g0 b0 e0 a0 ea0 (Hdst0 & Hadd0 & Hwa0 & Hwb0);
        try (destruct (decide (dst = cnull))); simplify_map_eq; try (cbn in Hnot_cap); congruence].
    all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    { rewrite /allow_store_map_or_true_imm.
      eexists true,p,g,b,e,a,_.
      split.
      { rewrite /read_reg_inr.
        by simplify_map_eq.
      }
      split.
      { rewrite /lword_of_argument. eauto.
      }
      rewrite /reg_allows_store_imm.
      rewrite Hadd Hwb.
      rewrite decide_False; auto.
      intro; naive_solver.
      }
    iNext. iIntros (lpc' mem' retv) "(#Hspec & HPC & Hi & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec; try (simplify_map_eq; congruence).
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; by iApply "Hφ".
     }
    Qed.

  Lemma wp_store_fail_tag_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_π
      w dst (src : Z + RegName) regs wa dq :
    decodeInstrW w.(lw) = Store dst src imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !!ₗ dst = Some wa →
    get_tag wa.(lw) = false →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FailedV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Hdst Htag φ) "(>HPC & >Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); eauto.
    iNext. iIntros (r sr m st lreg lmem R C c σ' Her Hregs Hregs' Hpc_a' Hstep)
      "HPCa Hr Hsr Hm Hst HR HC HPC Hpc_a Hmap".
    destruct (llookup_reg_phys _ _ _ _ _ Hregs' Hdst) as (s0 & Hdst' & _).
    rewrite Hinstr /exec /= Hdst' /= in Hstep.
    assert (c = Failed ∧ σ' = (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st)) as [-> ->].
    { destruct wa as [[| [[] p g b e a|] | |] ?]; cbn in Htag; try discriminate.
      all: destruct s0; cbn in Hstep; destruct (word_of_argument _ src); cbn in Hstep; by simplify_eq. }
    iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); first done.
    iIntros "HPC Hmap". iApply "Hφ". iFrame.
  Qed.

   Lemma wp_store_success_reg_same_imm E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst w'
         p g b e a ea (imm : Z) dq :
     π = None →
     is_shadow_address ea = false →
     decodeInstrW w.(lw) = Store dst (inr dst) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e ea = true →
     (a + imm)%a = Some ea →
     dst ≠ cnull ->

     canStore p (WCap true p g b e a) = true →
     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ dst ↦ᵣ WCap true p g b e a @@? π
           ∗ ▷ ea ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ{dq} w
              ∗ dst ↦ᵣ WCap true p g b e a @@? π
              ∗ ea ↦ₐ WCap true p g b e a @@? π }}}.
   Proof.
     iIntros (-> Hshadow Hinstr Hvpc Hpca' Hwa Hwb Hadd ? HcanStore φ) "Hres Hφ".
     iApply (wp_store_success_reg_same_store_word_imm with "Hres"); eauto.
     iNext. iIntros "Hpost".
     iEval (rewrite lstore_word_canStore //) in "Hpost".
     iApply "Hφ". iExact "Hpost".
   Qed.

  Lemma wp_store_success_mem E pc_p pc_g pc_b pc_e pc_a pc_π
    dst src w regs lpc' mem p g b e a storev oldv :
    decodeInstrW w.(lw) = Store dst src 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Store dst src 0) ⊆ dom regs →
    mem !! pc_a = Some w →
    reg_allows_store regs dst p g b e a →
    (∀ v : LWord, regs !!ₗ dst = Some v → v.(lprov) = None) →
    lword_of_argument regs src = Some storev →
    is_shadow_address a = false →
    mem !! a = Some oldv →
    incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ lpc' ∗
        ([∗ map] a↦w ∈ <[a:=lstore_word p storev]> mem, a ↦ₐ w) ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    intros Hinstr Hvpc Dregs Hmem Hallow Hnoid Harg Hshadow Hlookup Hinc.
    eapply wp_store_success_mem_imm with (imm := 0) (ea := a); eauto.
    destruct Hallow as (Hdst & Hwa & Hwb).
    unfold reg_allows_store_imm. repeat split; eauto; try by rewrite finz_add_0.
  Qed.

  (** A shadow store of the status [revoked] to [heap_a]: either it stores the
      current bit, or [heap_a] is in the permission set [sperm]. *)
  Lemma wp_store_success_shadow E pc_p pc_g pc_b pc_e pc_a pc_π
    dst src w regs lpc' mem shadow (sperm : gset Addr) p g b e a heap_a revoked πs :
    decodeInstrW w.(lw) = Store dst src 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Store dst src 0) ⊆ dom regs →
    mem !! pc_a = Some w →
    reg_allows_store regs dst p g b e a →
    (∀ v : LWord, regs !!ₗ dst = Some v → v.(lprov) = None) →
    lword_of_argument regs src = Some (MkLWord (WInt (encodeAllocStatus revoked)) πs) →
    is_shadow_address a = true →
    shadow_to_heap a = Some heap_a →
    is_Some (shadow !! heap_a) →
    shadow_store_allowed sperm shadow heap_a revoked →
    incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
        (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ revoked) ∗
        ([∗ set] a ∈ sperm, shadow_store_perm a) ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ lpc' ∗
        ([∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
        ([∗ map] a↦revoked ∈ <[heap_a:=revoked]> shadow, a ↦ₛ revoked) ∗
        ([∗ set] a ∈ sperm, shadow_store_perm a) ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hmem Hallow Hnoid Harg Hshadow Htranslate Hlookup Hok Hinc φ)
      "(>HPC & >Hmem & >Hshadow & Hperms & >Hmap) Hφ".
    iApply (wp_store with "[$HPC $Hmem $Hshadow $Hperms $Hmap]"); eauto.
    { intros p0 g0 b0 e0 a0 v0 (Hdst0 & _) Harg0.
      destruct Hallow as (Hdst & _). rewrite Hdst in Hdst0. simplify_eq.
      rewrite Hshadow. intros _. exists heap_a. split_and!; [done|done|].
      intros z Hz. cbn in Hz. simplify_eq. by rewrite decode_encode_alloc_status_inv. }
    iNext. iIntros (lpc0 mem0 shadow0 retv) "(%Hspec & HPC & Hmem & Hshadow & Hperms & Hmap)".
    destruct Hallow as (Hdst & Hwa & Hwb).
    destruct Hspec as
      [p0 g0 b0 e0 a0 ea0 v0 oldv0 Harg0 (Hdst0 & Hadd0 & _) Hshadow0 Hlookup0 -> -> Hinc0
      |p0 g0 b0 e0 a0 ea0 heap_a0 z0 π0 old_status0 Harg0 (Hdst0 & Hadd0 & _) Hshadow0 Htranslate0 Hlookup0 -> -> Hinc0
      |Hmem_eq Hshadow_eq Hfail].
    - rewrite Hdst in Hdst0. simplify_eq.
      rewrite finz_add_0 in Hadd0. simplify_eq. congruence.
    - rewrite Hdst in Hdst0. simplify_eq.
      rewrite finz_add_0 in Hadd0. simplify_eq.
      try (rewrite Harg in Harg0; simplify_eq). try (rewrite Hinc in Hinc0; simplify_eq).
      iApply "Hφ". rewrite decode_encode_alloc_status_inv. iFrame.
    - exfalso. destruct Hfail as
        [w0 Hreg0 Hcap0|p0 g0 b0 e0 a0 Hreg0|p0 g0 b0 e0 a0 Hreg0 Hadd0|
         p0 g0 b0 e0 a0 ea0 Hreg0 Hadd0 Hbounds0|Hpc0|
         p0 g0 b0 e0 a0 ea0 v0 Hreg0 Hadd0 Hshadow0 Harg0 Hbad0|
         p0 g0 b0 e0 a0 π0 Hreg0 Hπ0].
      + rewrite Hreg0 in Hdst. by destruct w0; simplify_eq/=.
      + rewrite Hreg0 in Hdst. simplify_eq.
      + rewrite finz_add_0 in Hadd0. discriminate.
      + rewrite finz_add_0 in Hadd0. simplify_eq.
        destruct Hbounds0; congruence.
      + congruence.
      + try (rewrite Harg in Harg0; simplify_eq). by apply (Hbad0 _ eq_refl).
      + by apply Hπ0, (Hnoid _ Hreg0).
  Qed.

  Lemma wp_store_success_shadow_fetch E pc_p pc_g pc_b pc_e pc_a pc_π
    dst src w regs lpc' mem shadow (sperm : gset Addr) p g b e a heap_a revoked πs dq :
    decodeInstrW w.(lw) = Store dst src 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Store dst src 0) ⊆ dom regs →
    reg_allows_store regs dst p g b e a →
    (∀ v : LWord, regs !!ₗ dst = Some v → v.(lprov) = None) →
    lword_of_argument regs src = Some (MkLWord (WInt (encodeAllocStatus revoked)) πs) →
    is_shadow_address a = true →
    shadow_to_heap a = Some heap_a →
    is_Some (shadow !! heap_a) →
    shadow_store_allowed sperm shadow heap_a revoked →
    incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
        (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ revoked) ∗
        ([∗ set] a ∈ sperm, shadow_store_perm a) ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        ([∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
        ([∗ map] a↦revoked ∈ <[heap_a:=revoked]> shadow, a ↦ₛ revoked) ∗
        ([∗ set] a ∈ sperm, shadow_store_perm a) ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hallow Hnoid Harg Hshadow Htranslate Hlookup Hok Hinc φ)
      "(>HPC & >Hfetch & >Hmem & >Hshadow & Hperms & >Hmap) Hφ".
    iApply (wp_store_fetch with "[$HPC $Hfetch $Hmem $Hshadow $Hperms $Hmap]"); eauto.
    { intros p0 g0 b0 e0 a0 v0 (Hdst0 & _) Harg0.
      destruct Hallow as (Hdst & _). rewrite Hdst in Hdst0. simplify_eq.
      rewrite Hshadow. intros _. exists heap_a. split_and!; [done|done|].
      intros z Hz. cbn in Hz. simplify_eq. by rewrite decode_encode_alloc_status_inv. }
    iNext. iIntros (lpc0 mem0 shadow0 retv) "(%Hspec & HPC & Hfetch & Hmem & Hshadow & Hperms & Hmap)".
    destruct Hallow as (Hdst & Hwa & Hwb).
    destruct Hspec as
      [p0 g0 b0 e0 a0 ea0 v0 oldv0 Harg0 (Hdst0 & Hadd0 & _) Hshadow0 Hlookup0 -> -> Hinc0
      |p0 g0 b0 e0 a0 ea0 heap_a0 z0 π0 old_status0 Harg0 (Hdst0 & Hadd0 & _) Hshadow0 Htranslate0 Hlookup0 -> -> Hinc0
      |Hmem_eq Hshadow_eq Hfail].
    - rewrite Hdst in Hdst0. simplify_eq.
      rewrite finz_add_0 in Hadd0. simplify_eq. congruence.
    - rewrite Hdst in Hdst0. simplify_eq.
      rewrite finz_add_0 in Hadd0. simplify_eq.
      try (rewrite Harg in Harg0; simplify_eq). try (rewrite Hinc in Hinc0; simplify_eq).
      iApply "Hφ". rewrite decode_encode_alloc_status_inv. iFrame.
    - exfalso. destruct Hfail as
        [w0 Hreg0 Hcap0|p0 g0 b0 e0 a0 Hreg0|p0 g0 b0 e0 a0 Hreg0 Hadd0|
         p0 g0 b0 e0 a0 ea0 Hreg0 Hadd0 Hbounds0|Hpc0|
         p0 g0 b0 e0 a0 ea0 v0 Hreg0 Hadd0 Hshadow0 Harg0 Hbad0|
         p0 g0 b0 e0 a0 π0 Hreg0 Hπ0].
      + rewrite Hreg0 in Hdst. by destruct w0; simplify_eq/=.
      + rewrite Hreg0 in Hdst. simplify_eq.
      + rewrite finz_add_0 in Hadd0. discriminate.
      + rewrite finz_add_0 in Hadd0. simplify_eq.
        destruct Hbounds0; congruence.
      + congruence.
      + try (rewrite Harg in Harg0; simplify_eq). by apply (Hbad0 _ eq_refl).
      + by apply Hπ0, (Hnoid _ Hreg0).
  Qed.

   Lemma wp_store_success_same E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst z w'
         p g b e :
     π = None →
     is_shadow_address pc_a = false →
     decodeInstrW w.(lw) = Store dst (inl z) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ WCap true p g b e pc_a @@? π }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ (WInt z)
              ∗ dst ↦ᵣ WCap true p g b e pc_a @@? π }}}.
  Proof.
    intros. eapply wp_store_success_same_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_success_reg_same'_store_word E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst
         p g b e :
     π = None →
     is_shadow_address pc_a = false →
     decodeInstrW w.(lw) = Store dst (inr dst) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ WCap true p g b e pc_a @@? π }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ lstore_word p (WCap true p g b e pc_a @@? π)
              ∗ dst ↦ᵣ WCap true p g b e pc_a @@? π }}}.
   Proof.
    intros. eapply wp_store_success_reg_same'_store_word_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_success_reg_same' E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst
         p g b e :
     π = None →
     is_shadow_address pc_a = false →
     decodeInstrW w.(lw) = Store dst (inr dst) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     canStore p (WCap true p g b e pc_a) = true ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ WCap true p g b e pc_a @@? π }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ WCap true p g b e pc_a @@? π
              ∗ dst ↦ᵣ WCap true p g b e pc_a @@? π }}}.
  Proof.
    intros. eapply wp_store_success_reg_same'_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_success_reg_same_a_store_word E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst src
         p g b e w'' :
     π = None →
      is_shadow_address pc_a = false →
     decodeInstrW w.(lw) = Store dst (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ WCap true p g b e pc_a @@? π }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ lstore_word p w''
              ∗ src ↦ᵣ w''
              ∗ dst ↦ᵣ WCap true p g b e pc_a @@? π}}}.
   Proof.
    intros. eapply wp_store_success_reg_same_a_store_word_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_success_reg_same_a E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst src
         p g b e w'' :
     π = None →
     is_shadow_address pc_a = false →
      decodeInstrW w.(lw) = Store dst (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     canStore p w''.(lw) = true ->
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ WCap true p g b e pc_a @@? π }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ w''
              ∗ src ↦ᵣ w''
              ∗ dst ↦ᵣ WCap true p g b e pc_a @@? π}}}.
  Proof.
    intros. eapply wp_store_success_reg_same_a_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_success_reg_store_word E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst src w'
         p g b e a w'' dq :
     π = None →
      is_shadow_address a = false →
     decodeInstrW w.(lw) = Store dst (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ WCap true p g b e a @@? π
           ∗ ▷ a ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ{dq} w
              ∗ src ↦ᵣ w''
              ∗ dst ↦ᵣ WCap true p g b e a @@? π
              ∗ a ↦ₐ lstore_word p w'' }}}.
    Proof.
    intros. eapply wp_store_success_reg_store_word_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_success_reg E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst src w'
         p g b e a w'' dq :
     π = None →
     is_shadow_address a = false →
      decodeInstrW w.(lw) = Store dst (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →
     canStore p w''.(lw) = true ->
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ WCap true p g b e a @@? π
           ∗ ▷ a ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ{dq} w
              ∗ src ↦ᵣ w''
              ∗ dst ↦ᵣ WCap true p g b e a @@? π
              ∗ a ↦ₐ w'' }}}.
  Proof.
    intros. eapply wp_store_success_reg_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_success_reg_same_store_word E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst w'
         p g b e a dq :
     π = None →
     is_shadow_address a = false →
     decodeInstrW w.(lw) = Store dst (inr dst) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ dst ↦ᵣ WCap true p g b e a @@? π
           ∗ ▷ a ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ{dq} w
              ∗ dst ↦ᵣ WCap true p g b e a @@? π
              ∗ a ↦ₐ lstore_word p (WCap true p g b e a @@? π) }}}.
   Proof.
    intros. eapply wp_store_success_reg_same_store_word_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_success_reg_same E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst w'
         p g b e a dq :
     π = None →
     is_shadow_address a = false →
     decodeInstrW w.(lw) = Store dst (inr dst) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →
     canStore p (WCap true p g b e a) = true ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ dst ↦ᵣ WCap true p g b e a @@? π
           ∗ ▷ a ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ{dq} w
              ∗ dst ↦ᵣ WCap true p g b e a @@? π
              ∗ a ↦ₐ WCap true p g b e a @@? π }}}.
  Proof.
    intros. eapply wp_store_success_reg_same_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_success_z E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst z w'
         p g b e a dq :
     π = None →
     is_shadow_address a = false →
     decodeInstrW w.(lw) = Store dst (inl z) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ dst ↦ᵣ WCap true p g b e a @@? π
           ∗ ▷ a ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ{dq} w
              ∗ dst ↦ᵣ WCap true p g b e a @@? π
              ∗ a ↦ₐ WInt z }}}.
  Proof.
    intros. eapply wp_store_success_z_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_fail_reg_not_cap E pc_p pc_g pc_b pc_e pc_a pc_π w
     dst src wdst wstore dq :
      decodeInstrW w.(lw) = Store dst (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     is_cap wdst = false ->
     src ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ src ↦ᵣ wstore
           ∗ ▷ dst ↦ᵣ wdst
     }}}
       Instr Executable @ E
       {{{ RET FailedV; True}}}.
  Proof.
    intros. eapply wp_store_fail_reg_not_cap_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

    Lemma wp_store_fail_z_not_cap E pc_p pc_g pc_b pc_e pc_a pc_π w
     dst z wdst dq :
      decodeInstrW w.(lw) = Store dst (inl z) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     is_cap wdst = false ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ dst ↦ᵣ wdst
     }}}
       Instr Executable @ E
       {{{ RET FailedV; True}}}.
  Proof.
    intros. eapply wp_store_fail_z_not_cap_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_fail_reg_perm E pc_p pc_g pc_b pc_e pc_a pc_π π w dst src
         p g b e a w'' dq :
      decodeInstrW w.(lw) = Store dst (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     writeAllowed p = false ->
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ WCap true p g b e a @@? π
     }}}
       Instr Executable @ E
       {{{ RET FailedV; True}}}.
  Proof.
    intros. eapply wp_store_fail_reg_perm_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

    Lemma wp_store_fail_z_perm E pc_p pc_g pc_b pc_e pc_a pc_π π w dst
         p g b e a z dq :
      decodeInstrW w.(lw) = Store dst (inl z) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     writeAllowed p = false ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ dst ↦ᵣ WCap true p g b e a @@? π
     }}}
       Instr Executable @ E
       {{{ RET FailedV; True}}}.
  Proof.
    intros. eapply wp_store_fail_z_perm_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

   Lemma wp_store_fail_reg E pc_p pc_g pc_b pc_e pc_a pc_π π w dst src
         p g b e a w'' dq :
      decodeInstrW w.(lw) = Store dst (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     withinBounds b e a = false →
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ WCap true p g b e a @@? π
     }}}
       Instr Executable @ E
       {{{ RET FailedV; True}}}.
  Proof.
    intros. eapply wp_store_fail_reg_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

    Lemma wp_store_fail_z E pc_p pc_g pc_b pc_e pc_a pc_π π w dst
         p g b e a z dq :
      decodeInstrW w.(lw) = Store dst (inl z) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     withinBounds b e a = false →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ dst ↦ᵣ WCap true p g b e a @@? π
     }}}
       Instr Executable @ E
       {{{ RET FailedV; True}}}.
  Proof.
    intros. eapply wp_store_fail_z_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.

  (** Point forms of the shadow store: with the permission for [heap_a]
      (paint, unpaint), or storing the current bit ([_same]). *)
  Lemma wp_store_success_shadow_z E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w
    dst p g b e a revoked old_revoked heap_a dq :
     π = None →
    is_shadow_address a = true →
    shadow_to_heap a = Some heap_a →
    decodeInstrW w.(lw) = Store dst (inl (encodeAllocStatus revoked)) 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    writeAllowed p = true →
    withinBounds b e a = true →
    dst ≠ cnull →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ WCap true p g b e a @@? π ∗
        ▷ heap_a ↦ₛ old_revoked ∗
        shadow_store_perm heap_a }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        dst ↦ᵣ WCap true p g b e a @@? π ∗
        heap_a ↦ₛ revoked ∗
        shadow_store_perm heap_a }}}.
  Proof.
    iIntros (-> Hshadow Htranslate Hinstr Hvpc Hpca' Hwa Hwb ? φ)
      "(>HPC & >Hi & >Hdst & >Ha & Hperm) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iAssert ([∗ map] a↦w ∈ (∅ : LMem), a ↦ₐ w)%I as "-#Hmem"; first by rewrite big_sepM_empty.
    iAssert ([∗ map] a0↦rev ∈ {[heap_a:=old_revoked]}, a0 ↦ₛ rev)%I
      with "[Ha]" as "Hshadow".
    { by rewrite big_sepM_singleton. }
    iAssert ([∗ set] a0 ∈ ({[heap_a]} : gset Addr), shadow_store_perm a0)%I
      with "[Hperm]" as "Hperms".
    { by rewrite big_sepS_singleton. }
    iApply (wp_store_success_shadow_fetch _ pc_p pc_g with "[$HPC $Hi $Hmem $Hshadow $Hperms $Hmap]");
      [..|iNext; iIntros "(HPC & Hi & Hmem & Hshadow & Hperms & Hmap)"].
    all: try (by eauto; simplify_map_eq).
    all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    all: try (by unfold reg_allows_store; split; [simplify_map_eq | split_and!; auto]).
    all: try (by rewrite /shadow_store_allowed; right; set_solver).
    all: try (by rewrite /incrementPC /incrementPC_gen; simplify_map_eq).
    all: try (by intros ? ?; simplify_map_eq).
    iApply "Hφ".
    iEval (rewrite insert_insert_eq big_sepM_singleton) in "Hshadow".
    iEval (rewrite big_sepS_singleton) in "Hperms".
    iRegsMap "Hmap"; eauto. iFrame.
  Qed.

  Lemma wp_store_success_shadow_z_same E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w
    dst p g b e a revoked heap_a dq :
     π = None →
    is_shadow_address a = true →
    shadow_to_heap a = Some heap_a →
    decodeInstrW w.(lw) = Store dst (inl (encodeAllocStatus revoked)) 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    writeAllowed p = true →
    withinBounds b e a = true →
    dst ≠ cnull →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ WCap true p g b e a @@? π ∗
        ▷ heap_a ↦ₛ revoked }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        dst ↦ᵣ WCap true p g b e a @@? π ∗
        heap_a ↦ₛ revoked }}}.
  Proof.
    iIntros (-> Hshadow Htranslate Hinstr Hvpc Hpca' Hwa Hwb ? φ)
      "(>HPC & >Hi & >Hdst & >Ha) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iAssert ([∗ map] a↦w ∈ (∅ : LMem), a ↦ₐ w)%I as "-#Hmem"; first by rewrite big_sepM_empty.
    iAssert ([∗ map] a0↦rev ∈ {[heap_a:=revoked]}, a0 ↦ₛ rev)%I
      with "[Ha]" as "Hshadow".
    { by rewrite big_sepM_singleton. }
    iAssert ([∗ set] a0 ∈ (∅ : gset Addr), shadow_store_perm a0)%I as "Hperms".
    { by rewrite big_sepS_empty. }
    iApply (wp_store_success_shadow_fetch _ pc_p pc_g pc_b pc_e pc_a pc_π _ _ w _
              (WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π)
            with "[$HPC $Hi $Hmem $Hshadow $Hperms $Hmap]");
      [..|iNext; iIntros "(HPC & Hi & Hmem & Hshadow & _ & Hmap)"].
    all: try (by eauto; simplify_map_eq).
    all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    all: try (by unfold reg_allows_store; split; [simplify_map_eq | split_and!; auto]).
    all: try (by rewrite /shadow_store_allowed; left; by simplify_map_eq).
    all: try (by rewrite /incrementPC /incrementPC_gen; simplify_map_eq).
    all: try (by intros ? ?; simplify_map_eq).
    iApply "Hφ".
    iEval (rewrite insert_insert_eq big_sepM_singleton) in "Hshadow".
    iRegsMap "Hmap"; eauto. iFrame.
  Qed.

  Lemma wp_store_success_shadow_reg E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w
    dst p g b e a src wsrc revoked old_revoked heap_a dq :
     π = None →
    is_shadow_address a = true →
    shadow_to_heap a = Some heap_a →
    decodeInstrW w.(lw) = Store dst (inr src) 0 →
    IsLInt wsrc (encodeAllocStatus revoked) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    writeAllowed p = true →
    withinBounds b e a = true →
    src ≠ cnull →
    dst ≠ cnull →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ wsrc ∗
        ▷ dst ↦ᵣ WCap true p g b e a @@? π ∗
        ▷ heap_a ↦ₛ old_revoked ∗
        shadow_store_perm heap_a }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        src ↦ᵣ wsrc ∗
        dst ↦ᵣ WCap true p g b e a @@? π ∗
        heap_a ↦ₛ revoked ∗
        shadow_store_perm heap_a }}}.
  Proof.
    iIntros (-> Hshadow Htranslate Hinstr Hwsrc Hvpc Hpca' Hwa Hwb ? ? φ)
      "(>HPC & >Hi & >Hsrc & >Hdst & >Ha & Hperm) Hφ".
    destruct (IsLInt_inv _ _ Hwsrc) as [πsrc ->].
    iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %]".
    iAssert ([∗ map] a↦w ∈ (∅ : LMem), a ↦ₐ w)%I as "-#Hmem"; first by rewrite big_sepM_empty.
    iAssert ([∗ map] a0↦rev ∈ {[heap_a:=old_revoked]}, a0 ↦ₛ rev)%I
      with "[Ha]" as "Hshadow".
    { by rewrite big_sepM_singleton. }
    iAssert ([∗ set] a0 ∈ ({[heap_a]} : gset Addr), shadow_store_perm a0)%I
      with "[Hperm]" as "Hperms".
    { by rewrite big_sepS_singleton. }
    iApply (wp_store_success_shadow_fetch _ pc_p pc_g with "[$HPC $Hi $Hmem $Hshadow $Hperms $Hmap]");
      [..|iNext; iIntros "(HPC & Hi & Hmem & Hshadow & Hperms & Hmap)"].
    all: try (by eauto; simplify_map_eq).
    all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    all: try (by unfold reg_allows_store; split; [simplify_map_eq | split_and!; auto]).
    all: try (by rewrite /shadow_store_allowed; right; set_solver).
    all: try (by rewrite /incrementPC /incrementPC_gen; simplify_map_eq).
    all: try (by intros ? ?; simplify_map_eq).
    iApply "Hφ".
    iEval (rewrite insert_insert_eq big_sepM_singleton) in "Hshadow".
    iEval (rewrite big_sepS_singleton) in "Hperms".
    iRegsMap "Hmap"; eauto. iFrame.
  Qed.

  Lemma wp_store_success_shadow_reg_same E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w
    dst p g b e a src wsrc revoked heap_a dq :
     π = None →
    is_shadow_address a = true →
    shadow_to_heap a = Some heap_a →
    decodeInstrW w.(lw) = Store dst (inr src) 0 →
    IsLInt wsrc (encodeAllocStatus revoked) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    writeAllowed p = true →
    withinBounds b e a = true →
    src ≠ cnull →
    dst ≠ cnull →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ wsrc ∗
        ▷ dst ↦ᵣ WCap true p g b e a @@? π ∗
        ▷ heap_a ↦ₛ revoked }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        src ↦ᵣ wsrc ∗
        dst ↦ᵣ WCap true p g b e a @@? π ∗
        heap_a ↦ₛ revoked }}}.
  Proof.
    iIntros (-> Hshadow Htranslate Hinstr Hwsrc Hvpc Hpca' Hwa Hwb ? ? φ)
      "(>HPC & >Hi & >Hsrc & >Hdst & >Ha) Hφ".
    destruct (IsLInt_inv _ _ Hwsrc) as [πsrc ->].
    iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %]".
    iAssert ([∗ map] a↦w ∈ (∅ : LMem), a ↦ₐ w)%I as "-#Hmem"; first by rewrite big_sepM_empty.
    iAssert ([∗ map] a0↦rev ∈ {[heap_a:=revoked]}, a0 ↦ₛ rev)%I
      with "[Ha]" as "Hshadow".
    { by rewrite big_sepM_singleton. }
    iAssert ([∗ set] a0 ∈ (∅ : gset Addr), shadow_store_perm a0)%I as "Hperms".
    { by rewrite big_sepS_empty. }
    iApply (wp_store_success_shadow_fetch _ pc_p pc_g pc_b pc_e pc_a pc_π _ _ w _
              (WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π)
            with "[$HPC $Hi $Hmem $Hshadow $Hperms $Hmap]");
      [..|iNext; iIntros "(HPC & Hi & Hmem & Hshadow & _ & Hmap)"].
    all: try (by eauto; simplify_map_eq).
    all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    all: try (by unfold reg_allows_store; split; [simplify_map_eq | split_and!; auto]).
    all: try (by rewrite /shadow_store_allowed; left; by simplify_map_eq).
    all: try (by rewrite /incrementPC /incrementPC_gen; simplify_map_eq).
    all: try (by intros ? ?; simplify_map_eq).
    iApply "Hφ".
    iEval (rewrite insert_insert_eq big_sepM_singleton) in "Hshadow".
    iRegsMap "Hmap"; eauto. iFrame.
  Qed.

  Lemma wp_store_fail_shadow_reg E pc_p pc_g pc_b pc_e pc_a pc_π π w
    dst src storev p g b e a dq :
    is_shadow_address a = true →
    decodeInstrW w.(lw) = Store dst (inr src) 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (∀ z : Z, storev.(lw) ≠ WInt z) →
    src ≠ cnull →
    dst ≠ cnull →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ storev ∗
        ▷ dst ↦ᵣ WCap true p g b e a @@? π }}}
      Instr Executable @ E
    {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hshadow Hinstr Hvpc Hinvalid ? ? φ)
      "(>HPC & >Hi & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %]".
    iAssert ([∗ map] a↦w ∈ (∅ : LMem), a ↦ₐ w)%I as "-#Hmem"; first by rewrite big_sepM_empty.
    iAssert ((▷ ([∗ map] k↦revoked ∈ (∅ : ShadowTbl), k ↦ₛ revoked))%I) as "Hshadow".
    { iNext. rewrite big_sepM_empty. done. }
    iAssert ([∗ set] a0 ∈ (∅ : gset Addr), shadow_store_perm a0)%I as "Hperms".
    { by rewrite big_sepS_empty. }
    iApply (wp_store_fetch _ pc_p pc_g with "[$HPC $Hi $Hmem $Hshadow $Hperms $Hmap]"); eauto; simplify_map_eq; eauto.
    all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    { intros p0 g0 b0 e0 a0 v0 (Hdst & _) Harg. simplify_map_eq.
      rewrite Hshadow. intros [rev Hrev].
      exfalso. by apply (Hinvalid rev). }
    iNext. iIntros (lpc' mem' shadow' retv) "(%Hspec & HPC & _ & _ & _ & _ & _)".
    destruct Hspec as
      [p0 g0 b0 e0 a0 ea0 v0 oldv Harg (Hdst & Hadd & _ & _) Hshadow0 Hlookup0 -> -> Hinc0
      |p0 g0 b0 e0 a0 ea0 heap_a0 z0 π0 old_status0 Harg (Hdst & Hadd & _ & _) Hshadow0 Htranslate0 Hlookup0 -> -> Hinc0
      |]; last by iApply "Hφ".
    - rewrite finz_add_0 in Hadd. inversion Hadd; subst ea0.
      simplify_map_eq; try congruence.
    - rewrite finz_add_0 in Hadd. inversion Hadd; subst ea0.
      simplify_map_eq; try (exfalso; by apply (Hinvalid z0)).
  Qed.

  Lemma wp_store_fail_tag E pc_p pc_g pc_b pc_e pc_a pc_π
      w dst (src : Z + RegName) regs wa dq :
    decodeInstrW w.(lw) = Store dst src 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !!ₗ dst = Some wa →
    get_tag wa.(lw) = false →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FailedV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    intros. eapply wp_store_fail_tag_imm with (imm := 0); eauto; try by rewrite finz_add_0.
  Qed.
Lemma wp_store_fail_reg_overflow_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_π π w dst src
         p g b e a w'' dq :
     decodeInstrW w.(lw) = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (a + imm)%a = None →
     src ≠ cnull ->
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ WCap true p g b e a @@? π
     }}}
       Instr Executable @ E
       {{{ RET FailedV; True}}}.
    Proof.
      iIntros (Hinstr Hvpc Hadd ?? φ)
             "(>HPC & >Hi & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %]".
    iAssert ([∗ map] a↦w ∈ (∅ : LMem), a ↦ₐ w)%I as "-#Hmem"; first by rewrite big_sepM_empty.

    iApply (wp_store_imm_fetch _ pc_p pc_g pc_b pc_e pc_a pc_π dst (inr src) imm w
      with "[$HPC $Hi $Hmap $Hmem]"); try done; try (by simplify_map_eq).
    all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    { rewrite /allow_store_map_or_true_imm.
      exists true,p,g,b,e,a,w''. split_and!.
      - rewrite /read_reg_inr. by simplify_map_eq.
      - by simplify_map_eq.
      - unfold reg_allows_store_imm. by rewrite Hadd. }
    { intros p0 g0 b0 e0 a0 ea (Hdst & Haddr & _). simplify_map_eq. }
    iNext. iIntros (lpc' mem' retv) "(%Hspec & HPC & _ & _ & _)".
    destruct Hspec as [????????? (Hdst & Haddr & _) | ??????????? (Hdst & Haddr & _) | ???].
    - simplify_map_eq; congruence.
    - simplify_map_eq; congruence.
    - by iApply "Hφ".
  Qed.
Lemma wp_store_fail_z_overflow_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_π π w dst
         p g b e a z dq :
     decodeInstrW w.(lw) = Store dst (inl z) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (a + imm)%a = None →
     dst ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ dst ↦ᵣ WCap true p g b e a @@? π
     }}}
       Instr Executable @ E
       {{{ RET FailedV; True}}}.
    Proof.
      iIntros (Hinstr Hvpc Hadd ? φ)
             "(>HPC & >Hi & >Hdst) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iAssert ([∗ map] a↦w ∈ (∅ : LMem), a ↦ₐ w)%I as "-#Hmem"; first by rewrite big_sepM_empty.

    iApply (wp_store_imm_fetch _ pc_p pc_g pc_b pc_e pc_a pc_π dst (inl z) imm w
      with "[$HPC $Hi $Hmap $Hmem]"); try done; try (by simplify_map_eq).
    all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    { rewrite /allow_store_map_or_true_imm.
      exists true,p,g,b,e,a,(WInt z : LWord). split_and!.
      - rewrite /read_reg_inr. by simplify_map_eq.
      - by simplify_map_eq.
      - unfold reg_allows_store_imm. by rewrite Hadd. }
    { intros p0 g0 b0 e0 a0 ea (Hdst & Haddr & _). simplify_map_eq. }
    iNext. iIntros (lpc' mem' retv) "(%Hspec & HPC & _ & _ & _)".
    destruct Hspec as [????????? (Hdst & Haddr & _) | ??????????? (Hdst & Haddr & _) | ???].
    - simplify_map_eq; congruence.
    - simplify_map_eq; congruence.
    - by iApply "Hφ".
  Qed.

  (** ** The revoker store

      A store to the revoker sweeps memory. It kills a chosen set [K] of
      quarantined identifiers, whose ranges are painted: their cells become
      unclaimed. Register copies of their words with authority are already
      untagged, by the register clause. *)
  Definition revoke_pre (ι : AId) : iProp Σ :=
    ∃ b e, alloc_obj ι b e ∗ ι ↦st{1} AQuar ∗
      [∗ list] a ∈ finz.seq_between b e, a ↦ₛ ShadowQuarantined ∗ addr_alloc a (Claimed ι).

  Definition revoke_post (ι : AId) : iProp Σ :=
    ∃ b e, alloc_obj ι b e ∗ ι ↦st{1} ADead ∗ ι ⊒ ADead ∗
      [∗ list] a ∈ finz.seq_between b e, a ↦ₛ ShadowQuarantined ∗ addr_alloc a Unclaimed.

  Definition revoke_reg (K : gset AId) (R : RegState) : RegState :=
    map_imap (λ ι (x : RegEntry), Some (if decide (ι ∈ K) then (x.1, ADead) else x)) R.

  Definition revoke_claims (K : gset AId) (C : gmap Addr AddrClaim) : gmap Addr AddrClaim :=
    (λ cl, match cl with
          | Claimed ι => if decide (ι ∈ K) then Unclaimed else cl
          | _ => cl end) <$> C.

  Lemma lookup_revoke_reg K R ι :
    revoke_reg K R !! ι =
      (λ x : RegEntry, if decide (ι ∈ K) then (x.1, ADead) else x) <$> R !! ι.
  Proof. rewrite /revoke_reg map_lookup_imap. by destruct (R !! ι) eqn:Hι; rewrite ?Hι. Qed.

  Lemma lookup_revoke_claims K C a :
    revoke_claims K C !! a =
      (λ cl, match cl with
            | Claimed ι => if decide (ι ∈ K) then Unclaimed else cl
            | _ => cl end) <$> C !! a.
  Proof. apply lookup_fmap. Qed.

  Lemma revoke_ghost_update (K : gset AId) R C :
    (∀ ι a, ι ∈ K → C !! a = Some (Claimed ι) → ∃ x, R !! ι = Some x ∧ re_covers x a) →
    reg_auth R -∗ addr_alloc_auth C -∗ ([∗ set] ι ∈ K, revoke_pre ι) ==∗
    reg_auth (revoke_reg K R) ∗ addr_alloc_auth (revoke_claims K C) ∗
    ([∗ set] ι ∈ K, revoke_post ι) ∗
    ⌜∀ ι, ι ∈ K → ∃ x, R !! ι = Some x ∧ re_status x = AQuar⌝.
  Proof.
    iInduction K as [|ι K HιK] "IH" using set_ind_L forall (R C);
      iIntros (Hcov) "HR HC Hpre".
    - assert (revoke_reg ∅ R = R) as ->.
      { apply map_eq. intros ι. rewrite lookup_revoke_reg.
        destruct (R !! ι) eqn:Hι; rewrite Hι /=; [|done].
        case_decide; [set_solver|done]. }
      assert (revoke_claims ∅ C = C) as ->.
      { apply map_eq. intros a. rewrite lookup_revoke_claims.
        by destruct (C !! a) as [[]|]; cbn; try done. }
      iFrame. iModIntro. iSplit; first by rewrite big_sepS_empty.
      iPureIntro. set_solver.
    - rewrite big_sepS_union; last set_solver. rewrite big_sepS_singleton.
      iDestruct "Hpre" as "[(%b & %e & #Hobj & Htok & Hcells) Hpre]".
      iDestruct (reg_lookup_own with "HR Htok") as %(b' & e' & γ & HRι).
      iDestruct (reg_lookup_obj with "HR Hobj") as %(γ' & s & HRι').
      rewrite HRι in HRι'. simplify_eq.
      rewrite big_sepL_sep. iDestruct "Hcells" as "[Hsh Hcl]".
      iDestruct (addr_alloc_lookup_list _ _ (λ _, Claimed ι) with "HC Hcl") as %Hcl.
      iMod (reg_step _ _ _ _ _ _ ADead with "HR Htok") as "[HR Htok]"; [done|simpl; lia|].
      iDestruct (st_lb_get with "Htok") as "#Hd".
      iMod (addr_alloc_update_list _ _ (λ _, Claimed ι) (λ _, Unclaimed) with "HC Hcl")
        as "[HC Hcl]".
      set (R1 := <[ι:=(b, e, γ', ADead)]> R).
      set (C1 := list_to_map ((λ a, (a, Unclaimed)) <$> finz.seq_between b e) ∪ C).
      assert (∀ a, C1 !! a = if decide (a ∈ finz.seq_between b e) then Some Unclaimed else C !! a)
        as HC1.
      { intros a. rewrite /C1 lookup_union. case_decide as Ha.
        - rewrite (elem_of_list_to_map_1 _ a Unclaimed); first by destruct (C !! a).
          + rewrite -list_fmap_compose. apply NoDup_fmap_2; first (intros ?? [=]; done).
            apply finz_seq_between_NoDup.
          + apply list_elem_of_fmap. eauto.
        - rewrite not_elem_of_list_to_map_1.
          + by destruct (C !! a).
          + rewrite -list_fmap_compose. intros (x & -> & Hx)%list_elem_of_fmap. done. }
      iMod ("IH" $! R1 C1 with "[%] HR HC Hpre") as "(HR & HC & Hpost & %HK)".
      { intros ι' a Hι' Ha. rewrite HC1 in Ha. case_decide; first done.
        destruct (Hcov ι' a ltac:(set_solver) Ha) as (x & Hx & Hc).
        exists x. rewrite /R1 lookup_insert_ne; first done. set_solver. }
      assert (revoke_reg K R1 = revoke_reg ({[ι]} ∪ K) R) as ->.
      { apply map_eq. intros ι'. rewrite !lookup_revoke_reg /R1.
        destruct (decide (ι = ι')) as [<-|Hne].
        - rewrite lookup_insert_eq HRι /=. repeat case_decide; set_solver.
        - rewrite lookup_insert_ne //. destruct (R !! ι') eqn:Hι'; rewrite ?Hι' /=; last done.
          repeat case_decide; set_solver. }
      assert (revoke_claims K C1 = revoke_claims ({[ι]} ∪ K) C) as ->.
      { apply map_eq. intros a. rewrite !lookup_revoke_claims HC1.
        case_decide as Ha.
        - rewrite (Hcl a Ha) /=. case_decide; set_solver.
        - destruct (C !! a) as [[|ι'|]|] eqn:HCa; rewrite ?HCa /=; try done.
          case_decide as H1; case_decide as H2; try done; [exfalso; set_solver|].
          assert (ι' = ι) as -> by set_solver.
          exfalso. destruct (Hcov ι a ltac:(set_solver) HCa) as (x & Hx & Hc).
          rewrite HRι in Hx. simplify_eq. apply Ha. by apply elem_of_finz_seq_between. }
      iModIntro. iFrame. rewrite big_sepS_union; last set_solver. rewrite big_sepS_singleton.
      iSplitL.
      + iFrame "Hpost". iExists b, e. iFrame "∗#". rewrite big_sepL_sep. iFrame.
      + iPureIntro. intros ι' Hι'. destruct (decide (ι' = ι)) as [->|Hne].
        * eexists. split; first exact HRι. done.
        * destruct (HK ι' ltac:(set_solver)) as (x & Hx & Hs). exists x.
          rewrite /R1 lookup_insert_ne // in Hx.
  Qed.

  Lemma wp_store_revoker E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w (regs : LReg)
      r1 (r2 : Z + RegName) imm p g b e a (K : gset AId) dq :
    decodeInstrW w.(lw) = Store r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Store r1 r2 imm) ⊆ dom regs →
    reg_allows_store_imm regs r1 imm p g b e a revoker_addr →
    (∀ v : LWord, regs !!ₗ r1 = Some v → v.(lprov) = None) →
    (pc_a + 1)%a = Some pc_a' →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        ([∗ set] ι ∈ K, revoke_pre ι) }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        ([∗ set] ι ∈ K, revoke_post ι) }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hallow Hnoid Hpca' φ) "(HPC & Hpc_a & Hmap & Hpre) Hφ".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); eauto.
    iNext. iIntros (r sr m st lreg lmem R C c σ' Her Hlregs Hregs Hpc_a Hstep)
      "HPCa Hr Hsr Hm Hst HR HC HPC Hpc_a Hmap".
    rewrite Hinstr in Hstep.
    (* The physical step: the sweep, then the PC increment. The revoker
       capability has no identifier and non-empty bounds: its copy is exact. *)
    pose proof Hallow as (Hr1l & Hadd & Hwa & Hwb).
    destruct (regs !!ₗ r1) as [v1|] eqn:Hv1; last done. cbn in Hr1l. simplify_eq.
    destruct (llookup_reg_phys _ _ _ _ _ Hregs Hv1) as (s1 & Hr1 & Hrel1).
    assert (and_tag s1 (lw v1) = lw v1) as Hex.
    { eapply reg_phys_exact_cond; first done.
      - intros (ι & x & Hι & _). by rewrite (Hnoid _ eq_refl) in Hι.
      - eapply (nonempty_exact_cond v1); [by rewrite Hr1l | apply withinBounds_true_iff in Hwb; solve_addr]. }
    rewrite Hex Hr1l in Hr1.
    assert (is_Some (word_of_argument r r2)) as [wv Hwv].
    { destruct r2 as [z|r2]; cbn; first eauto.
      assert (is_Some (regs !!ₗ r2)) as [lv Hl].
      { apply elem_of_dom_lreg, Dregs. rewrite /regs_of /=. set_solver+. }
      destruct (llookup_reg_phys _ _ _ _ _ Hregs Hl) as (s2 & Hr2 & _). eauto. }
    rewrite /exec /= Hwv Hr1 /= Hadd /= Hwa Hwb /= revoker_not_shadow_address /=
      in Hstep.
    rewrite (proj2 (is_revoker_address_spec revoker_addr) eq_refl) /= in Hstep.
    (* The ghost update *)
    iMod (revoke_ghost_update K R C with "HR HC Hpre") as "(HR & HC & Hpost & %HK)".
    { intros ι a' _ Ha'. apply (reg_ok_claimed _ _ _ (er_registry _ _ _ _ _ _ Her)) in Ha'
        as (x & Hx & Hcov & _). eauto. }
    assert (erasure (revoke_reg K R) (revoke_claims K C)
              (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, sweep_mem st m, st)
              (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) lreg lmem)
      as Her1.
    { eapply erasure_revoke; eauto.
      - apply lookup_revoke_reg.
      - apply lookup_revoke_claims. }
    assert (incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) =
              Some (WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π))
      as Hinc by by rewrite /incrementPC /incrementPC_gen Hpca'.
    destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ Her1 Hinc) as (pc'' & Hu & Her2).
    rewrite /updatePC /updatePC_gen /= Hpca' in Hu. simplify_eq.
    unfold revoker_sweep, updatePC, updatePC_gen in Hstep; cbn in Hstep.
    rewrite Hpca' in Hstep. simplify_eq.
    iMod (PC_update _ _ (WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π) with "HPCa HPC")
      as "[HPCa HPC]".
    iModIntro. iSplitR "Hφ HPC Hpc_a Hmap Hpost".
    { iExists _, _, lmem, _, _. iFrame. iPureIntro. exact Her2. }
    iApply "Hφ". iFrame.
  Qed.

End griotte_lang_rules.

Section shadow_store_res.
  Context `{MP: MachineParameters} `{ceriseg: ceriseG Σ}.

  (* Closes a failing store: the state is unchanged. *)
  #[local] Ltac store_fail Hstep :=
    injection Hstep as <- <-;
    try iApply bupd_fupd;
    iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); [done|];
    iIntros "HPC Hmap"; iApply "Hφ"; iFrame; iPureIntro;
    eapply Store_spec_failure_store; [done|done|].

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
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Store r1 r2 imm) ⊆ dom regs →
   (if fetch_in_mem then mem !! pc_a = Some w else True) →
   allow_store_mem_or_shadow_imm r1 r2 imm regs mem shadow sperm →

   {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
       (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
       (▷ if fetch_in_mem then emp else pc_a ↦ₐ{dq} w) ∗
       (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ revoked) ∗
       ([∗ set] a ∈ sperm, Pm a) ∗
       deref_witness_res dw ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ lpc' mem' shadow' retv, RET retv;
       ⌜ Store_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm lpc' mem mem' shadow shadow' dw retv⌝ ∗
         PC ↦ₚ lpc' ∗
         ([∗ map] a↦w ∈ mem', a ↦ₐ w) ∗
         (if fetch_in_mem then emp else pc_a ↦ₐ{dq} w) ∗
         ([∗ map] a↦revoked ∈ shadow', a ↦ₛ revoked) ∗
         ([∗ set] a ∈ sperm, Pm a) ∗
         deref_witness_res dw ∗
         [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
   Proof.
     iIntros (HPm Hinstr Hvpc Dregs Hmem_pc HaStore φ) "(>HPC & >Hmem & >Hfetch & >Hshadow & Hperms & Hdw & >Hmap) Hφ".
     iApply wp_lift_atomic_base_step_no_fork; auto.
     iIntros (σ1 ns l1 l2 nt) "Hσ /=".
     destruct σ1 as [ [ [ [pc r] sr] m] st]; cbn.
     iDestruct "Hσ" as (lpc lreg lmem R C) "(HPCa & Hr & Hsr & Hm & Hst & HR & HC & %Her)".
     iDestruct (PC_agree with "HPCa HPC") as %->.
     pose proof (erasure_pc_correct _ _ _ _ _ _ Her Hvpc) as Hpc. cbn in Hpc. subst pc.
     iDestruct (deref_witness_lookup with "HR Hdw") as %Hdw.
     iEval (rewrite /sreg /shadowtbl /=) in "Hsr Hst".
     iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hlregs.
     pose proof (erasure_regs_incl _ _ _ _ _ _ _ Her Hlregs) as Hregs.
     iDestruct (gen_heap_valid_inclSepM with "Hm Hmem") as %Hlmem.
     iDestruct (gen_heap_valid_inclSepM with "Hst Hshadow") as %Hshadow_incl.
     pose proof (er_mmio _ _ _ _ _ _ Her) as Hmmio; cbn in Hmmio.
     specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri. unfold regs_of in Hri.
     odestruct (Hri r1) as [r1v [Hr1l _] ]; first by set_solver+.
     iAssert (⌜lmem !! pc_a = Some w⌝)%I as %Hlmem_pc.
     { destruct fetch_in_mem.
       - iPureIntro. by eapply lookup_weaken.
       - iApply (gen_heap_valid with "Hm Hfetch"). }
     destruct (erasure_lookup_mem _ _ _ _ _ _ _ _ Her Hlmem_pc) as (pw & Hpw & Hpwok).
     iModIntro. iSplitR; first (by iPureIntro; apply normal_always_base_reducible).
     iNext. iIntros (e2 σ2 efs Hpstep).
     apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
     iIntros "_".
     iSplitR; auto. eapply step_exec_inv in Hstep; eauto.
     rewrite (mem_word_ok_decode _ _ _ _ Hpwok) Hinstr in Hstep.
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
       assert ((Failed, (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st)) = (c, σ2)) as Hstep'.
       { unfold is_cap in Hr1v. destruct r1v as [r1v ?]. cbn in *.
         destruct_word r1v; by simplify_pair_eq. }
       store_fail Hstep'. by eapply Store_fail_const.
     }
     destruct r1v as [ [ | [t p g b e a | ] | | ] π1]; try inversion Hr1v. clear Hr1v. cbn in Hstep.
     destruct t.
     2: { rewrite ?andb_false_r in Hstep.
          store_fail Hstep. eapply Store_fail_tag. by rewrite Hr1l. }
     destruct s1.
     2: { (* The physical copy of the destination is untagged. *)
       cbn in Hstep. store_fail Hstep.
       destruct (decide (π1 = deref_id dw)) as [Hπ|Hπ]; last by eapply Store_fail_revoked.
       destruct (a + imm)%a as [ea|] eqn:Hadd.
       2: by eapply Store_fail_addr; [rewrite Hr1l | done].
       destruct (withinBounds b e ea) eqn:Hwb.
       2: by eapply Store_fail_bounds; [rewrite Hr1l | done | right].
       (* A stripped destination under its witness is a heap capability
          without authority: its bounds are empty. *)
       exfalso.
       destruct Hrel1 as [[Heq | [_ [[Hst _] | [Hna [base Hh]]]]] _]; cbn in *; try discriminate.
       { by apply (deref_witness_not_stale R dw (WCap true p g b e a @@? π1)). }
       assert (is_heap_address b = true) as Hbh.
       { rewrite /heap_cap_base /= in Hh. by destruct (is_heap_address b). }
       apply withinBounds_true_iff in Hwb. apply Hna. split; first done. exists b.
       apply heap_authority_base_memory_cap_bounds. exists e. split; first done.
       split; [solve_addr | done]. }
     cbn in Hstep.
     destruct (a + imm)%a as [ea|] eqn:Hadd.
     2: { store_fail Hstep. eapply Store_fail_addr; last done. by rewrite Hr1l. }
     cbn in Hstep.
     destruct (writeAllowed p && withinBounds b e ea) eqn:HWA.
     2 : {
       apply andb_false_iff in HWA.
       store_fail Hstep. eapply Store_fail_bounds; eauto. by rewrite Hr1l.
     }
     apply andb_true_iff in HWA; destruct HWA as (Hwa & Hwb).
     assert (Hallow : reg_allows_store_imm regs r1 imm p g b e a ea)
       by (repeat split; auto; by rewrite Hr1l).
     specialize (HaStore p g b e a ea storev Hallow HSV).
     destruct (is_shadow_address ea) eqn:Hshadow.
     - destruct (proj2 (shadow_to_heap_domain ea) Hshadow) as [heap_a Htranslate].
       rewrite Htranslate /= in Hstep.
       destruct storev as [ [z | | |] πs]; cbn in Hstep.
       2,3,4: store_fail Hstep;
         eapply Store_fail_invalid_shadow; [by rewrite Hr1l|done|done|exact HSV|by intros ? ?].
       set (status := decodeAllocStatus z).
       destruct HaStore as (heap_a' & Htranslate' & [old_revoked Hshadowa] & Hallowed);
         first by eexists.
       assert (heap_a' = heap_a) as -> by congruence.
       specialize (Hallowed z eq_refl).
       assert (st !! heap_a = Some old_revoked) as Hsta.
       { eapply lookup_weaken; [exact Hshadowa|exact Hshadow_incl]. }
       iAssert (⌜shadow_store_ok R C st heap_a status⌝)%I as %Hsok.
       { destruct Hallowed as [Hsame | Hin].
         - iPureIntro. left. by eapply lookup_weaken.
         - iDestruct (HPm with "HR HC Hperms") as %Hok; first done.
           iPureIntro. by right. }
       pose proof (erasure_shadow_store _ _ _ _ _ _ _ _ _ _ heap_a status Her ltac:(eauto) Hsok) as Her1.
       rewrite /update_shadowtbl /= in Hstep.
       destruct (incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π)) as [lpc'|] eqn:Hregs'.
       2: {
         pose proof Hregs' as Ha'. eapply incrementPC_None_inv in Ha'; [|reflexivity].
         unfold updatePC, updatePC_gen in Hstep; cbn in Hstep; rewrite Ha' in Hstep.
         store_fail Hstep. by apply Store_fail_invalid_PC. }
       destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ Her1 Hregs') as (pc'' & Hu & Her2).
       pose proof Hregs' as Ha'.
       apply incrementPC_Some_inv in Ha' as (t' & p' & g' & b' & e' & a' & a'1 & π' & Heq & Ha'1 & ->).
       injection Heq as <- <- <- <- <- <- <-.
       rewrite /updatePC /updatePC_gen /= Ha'1 in Hu. simplify_eq.
       unfold updatePC, updatePC_gen in Hstep; cbn in Hstep; rewrite Ha'1 in Hstep.
       simplify_pair_eq. cbn.
       iDestruct (big_sepM_delete _ _ heap_a with "Hshadow") as "[Ha Hshadow]"; first exact Hshadowa.
       iMod (gen_heap_update with "Hst Ha") as "[Hst Ha]".
       iDestruct (big_sepM_insert _ _ heap_a with "[$Hshadow $Ha]") as "Hshadow".
       { apply lookup_delete_eq. }
       iEval (rewrite insert_delete_eq) in "Hshadow".
       iMod (PC_update _ _ (WCap true pc_p pc_g pc_b pc_e a'1 @@? pc_π) with "HPCa HPC") as "[HPCa HPC]".
       iModIntro. iSplitR "Hφ HPC Hmem Hfetch Hshadow Hperms Hdw Hmap".
       { iExists _, _, lmem, R, C. iFrame. done. }
       iApply "Hφ". iFrame.
       iPureIntro. eapply Store_spec_success_shadow; eauto.
     - destruct HaStore as [oldv Hmema].
       assert (lmem !! ea = Some oldv) as Hlmea by by eapply lookup_weaken.
       destruct (erasure_lookup_mem _ _ _ _ _ _ _ _ Her Hlmea) as (pwea & Hmea & _).
       rewrite (mem_avoids_mmio_not_revoker _ _ _ Hmmio Hmea) in Hstep.
       rewrite /update_mem /= in Hstep.
       pose proof (erasure_store _ _ _ _ _ _ _ _ _ _ ea (lstore_word p storev) _ _ Her Hlmea
         (reg_phys_mem_word_ok _ _ _ _ (reg_word_ok_lstore_word _ _ p _ Hstore_ok)
            (reg_phys_lstore_word _ p _ _ Hrelv))) as Her1.
       destruct (incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π)) as [lpc'|] eqn:Hregs'.
       2: {
         pose proof Hregs' as Ha'. eapply incrementPC_None_inv in Ha'; [|reflexivity].
         unfold updatePC, updatePC_gen in Hstep; cbn in Hstep; rewrite Ha' in Hstep.
         store_fail Hstep. by apply Store_fail_invalid_PC. }
       destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ Her1 Hregs') as (pc'' & Hu & Her2).
       pose proof Hregs' as Ha'.
       apply incrementPC_Some_inv in Ha' as (t' & p' & g' & b' & e' & a' & a'1 & π' & Heq & Ha'1 & ->).
       injection Heq as <- <- <- <- <- <- <-.
       rewrite /updatePC /updatePC_gen /= Ha'1 in Hu. simplify_eq.
       unfold updatePC, updatePC_gen in Hstep; cbn in Hstep; rewrite Ha'1 in Hstep.
       simplify_pair_eq. cbn.
       iMod ((gen_heap_update_inSepM _ _ ea) with "Hm Hmem") as "[Hm Hmem]"; eauto.
       iMod (PC_update _ _ (WCap true pc_p pc_g pc_b pc_e a'1 @@? pc_π) with "HPCa HPC") as "[HPCa HPC]".
       iModIntro. iSplitR "Hφ HPC Hmem Hfetch Hshadow Hperms Hdw Hmap".
       { iExists _, _, _, R, C. iFrame. done. }
       iApply "Hφ". iFrame.
       iPureIntro. eapply Store_spec_success; eauto.
   Qed.

  Lemma wp_store_shadow_imm_res Ep
     pc_p pc_g pc_b pc_e pc_a pc_π
     r1 (r2 : Z + RegName) (imm : Z) w mem regs shadow (sperm : gset Addr)
     (Pm : Addr → iProp Σ) dw :
   (∀ R C a, a ∈ sperm →
      reg_auth R -∗ addr_alloc_auth C -∗ ([∗ set] a ∈ sperm, Pm a) -∗
      ⌜shadow_perm_ok R C a⌝) →
   decodeInstrW w.(lw) = Store r1 r2 imm →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Store r1 r2 imm) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_store_mem_or_shadow_imm r1 r2 imm regs mem shadow sperm →

   {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
       (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
       (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ revoked) ∗
       ([∗ set] a ∈ sperm, Pm a) ∗
       deref_witness_res dw ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ lpc' mem' shadow' retv, RET retv;
       ⌜ Store_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm lpc' mem mem' shadow shadow' dw retv⌝ ∗
         PC ↦ₚ lpc' ∗
         ([∗ map] a↦w ∈ mem', a ↦ₐ w) ∗
         ([∗ map] a↦revoked ∈ shadow', a ↦ₛ revoked) ∗
         ([∗ set] a ∈ sperm, Pm a) ∗
         deref_witness_res dw ∗
         [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
   Proof.
     iIntros (HPm Hinstr Hvpc Dregs Hmem_pc HaStore φ) "(HPC & Hmem & Hshadow & Hperms & Hdw & Hmap) Hφ".
     iApply (wp_store_shadow_imm_res_gen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ true (DfracOwn 1) dw
       with "[$HPC $Hmem $Hshadow $Hperms $Hdw $Hmap]"); eauto.
     iNext. iIntros (lpc' mem' shadow' retv) "(Hspec & HPC & Hmem & _ & Hshadow & Hperms & Hdw & Hmap)".
     iApply "Hφ". iFrame.
   Qed.

  Lemma wp_store_shadow_imm_res_fetch Ep
     pc_p pc_g pc_b pc_e pc_a pc_π
     r1 (r2 : Z + RegName) (imm : Z) w mem regs shadow (sperm : gset Addr)
     (Pm : Addr → iProp Σ) dq dw :
   (∀ R C a, a ∈ sperm →
      reg_auth R -∗ addr_alloc_auth C -∗ ([∗ set] a ∈ sperm, Pm a) -∗
      ⌜shadow_perm_ok R C a⌝) →
   decodeInstrW w.(lw) = Store r1 r2 imm →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Store r1 r2 imm) ⊆ dom regs →
   allow_store_mem_or_shadow_imm r1 r2 imm regs mem shadow sperm →

   {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
       ▷ pc_a ↦ₐ{dq} w ∗
       (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
       (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ revoked) ∗
       ([∗ set] a ∈ sperm, Pm a) ∗
       deref_witness_res dw ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ lpc' mem' shadow' retv, RET retv;
       ⌜ Store_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm lpc' mem mem' shadow shadow' dw retv⌝ ∗
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

  (** A shadow store of an immediate, justified by any resource [P] that
      gives [shadow_store_ok]; [P] is returned unchanged. *)
  Lemma wp_store_success_shadow_z_res E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w
    dst p g b e a revoked old_revoked heap_a (P : iProp Σ) dq :
     π = None →
    (∀ R C, reg_auth R -∗ addr_alloc_auth C -∗ P -∗ ⌜shadow_perm_ok R C heap_a⌝) →
    is_shadow_address a = true →
    shadow_to_heap a = Some heap_a →
    decodeInstrW w.(lw) = Store dst (inl (encodeAllocStatus revoked)) 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    writeAllowed p = true →
    withinBounds b e a = true →
    dst ≠ cnull →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ WCap true p g b e a @@? π ∗
        ▷ heap_a ↦ₛ old_revoked ∗
        P }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        dst ↦ᵣ WCap true p g b e a @@? π ∗
        heap_a ↦ₛ revoked ∗
        P }}}.
  Proof.
    iIntros (-> HP Hshadow Htranslate Hinstr Hvpc Hpca' Hwa Hwb Hdst φ)
      "(>HPC & >Hi & >Hdst & >Ha & HPr) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iAssert ([∗ map] a↦w ∈ (∅ : LMem), a ↦ₐ w)%I as "-#Hmem"; first by rewrite big_sepM_empty.
    iAssert ([∗ map] a0↦rev ∈ {[heap_a:=old_revoked]}, a0 ↦ₛ rev)%I
      with "[Ha]" as "Hshadow".
    { by rewrite big_sepM_singleton. }
    iAssert ([∗ set] a0 ∈ ({[heap_a]} : gset Addr), (λ _, P) a0)%I
      with "[HPr]" as "Hperms".
    { by rewrite big_sepS_singleton. }
    iApply (wp_store_shadow_imm_res_fetch _ _ _ _ _ _ _ dst (inl (encodeAllocStatus revoked)) 0
      _ _ _ _ _ _ _ DerefNoId
      with "[$HPC $Hi $Hmem $Hshadow $Hperms $Hmap]"); eauto; simplify_map_eq; eauto.
    { intros R C a0 Ha0. iIntros "HR HC Hperms".
      rewrite big_sepS_singleton. apply elem_of_singleton in Ha0 as ->.
      iApply (HP with "HR HC Hperms"). }
    all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    { intros p0 g0 b0 e0 a0 ea0 v0 (Hdst0 & Hadd0 & _) Harg0.
      simplify_map_eq. rewrite finz_add_0 in Hadd0. simplify_eq.
      rewrite Hshadow. intros _. exists heap_a. split_and!; [done|by simplify_map_eq|].
      intros z Hz. right. set_solver. }
    iNext. iIntros (lpc' mem' shadow' retv) "(%Hspec & HPC & Hi & Hmem & Hshadow & Hperms & _ & Hmap)".
    destruct Hspec as
      [p0 g0 b0 e0 a0 ea0 v0 oldv0 Harg0 (Hdst0 & Hadd0 & _) Hshadow0 Hlookup0 -> -> Hinc0
      |p0 g0 b0 e0 a0 ea0 heap_a0 z0 π0 old_status0 Harg0 (Hdst0 & Hadd0 & _) Hshadow0 Htranslate0 Hlookup0 -> -> Hinc0
      |Hmem_eq Hshadow_eq Hfail].
    - simplify_map_eq.
    - simplify_map_eq. rewrite finz_add_0 in Hadd0. simplify_eq.
      rewrite decode_encode_alloc_status_inv.
      iRegsMap "Hshadow". iRegsMap "Hmap".
      iEval (rewrite big_sepS_singleton) in "Hperms".
      try (rewrite /incrementPC /incrementPC_gen in Hinc0; simplify_map_eq).
      iApply "Hφ". iFrame.
    - exfalso. destruct Hfail as
        [w0 Hreg0 Hcap0|p0 g0 b0 e0 a0 Hreg0|p0 g0 b0 e0 a0 Hreg0 Hadd0|
         p0 g0 b0 e0 a0 ea0 Hreg0 Hadd0 Hbounds0|Hpc0|
         p0 g0 b0 e0 a0 ea0 v0 Hreg0 Hadd0 Hshadow0 Harg0 Hbad0|p0 g0 b0 e0 a0 π0 Hreg0 Hπ0];
        simplify_map_eq; try (rewrite finz_add_0 in Hadd0; simplify_eq); try congruence.
      all: try (destruct Hbounds0; congruence).
      all: try (rewrite /incrementPC /incrementPC_gen in Hpc0; simplify_map_eq).
      all: try (by apply (Hbad0 _ eq_refl)).
  Qed.

  (** A store through a word that is not a capability fails, whatever its
      identifier. *)
  Lemma wp_store_fail_not_cap_imm Ep (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_π
      w dst (src : Z + RegName) regs wa dq :
    decodeInstrW w.(lw) = Store dst src imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !!ₗ dst = Some wa →
    is_cap wa.(lw) = false →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ RET FailedV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Hdst Hcap φ) "(>HPC & >Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); eauto.
    iNext. iIntros (r sr m st lreg lmem Rg Cg c σ' Her Hregs Hregs' Hpc_a' Hstep)
      "HPCa Hr Hsr Hm Hst HR HC HPC Hpc_a Hmap".
    destruct (llookup_reg_phys _ _ _ _ _ Hregs' Hdst) as (s0 & Hdst' & _).
    rewrite Hinstr /exec /= Hdst' /= in Hstep.
    assert (c = Failed ∧ σ' = (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st)) as [-> ->].
    { destruct wa as [ [| [|] | |] ?]; cbn in Hcap; try discriminate.
      all: destruct s0; cbn in Hstep; destruct (word_of_argument _ src); cbn in Hstep; by simplify_eq. }
    iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); first done.
    iIntros "HPC Hmap". iApply "Hφ". iFrame.
  Qed.

End shadow_store_res.
