From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Export logrel.
From griotte Require Import world_ghost_theory.
From griotte Require Import region_open interp_weakening.
From griotte Require Import rules rules_deref_quar proofmode monotone.
From griotte Require Import map_simpl register_tactics proofmode.

Section wp_interp.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    {cthreads : CmptThreads}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> (leibnizO LWord) -n> iPropO Σ).
  #[local] Notation V := (interpO Σ).
  #[local] Notation K := (contO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).

  Lemma lload_word_RW v : lload_word RW v = v.
  Proof. by destruct v as [ [] ?]. Qed.

  (** Accesses retain the original current address and report their checked
      effective address. *)

  (** Two regions of a key outside the heap whose cell is held: same part,
      same permission. *)
  Lemma region_rel_part_agree_open W C s a ρ1 ρ2 p1 p2 P1 P2 w :
    world_interp_open W C s -∗ a ↦ₐ w -∗
    region_rel_part ρ1 W C (LNonHeap a) p1 P1 -∗
    region_rel_part ρ2 W C (LNonHeap a) p2 P2 -∗
    world_interp_open W C s ∗ a ↦ₐ w ∗ ⌜ρ1 = ρ2 ∧ p1 = p2⌝.
  Proof.
    iIntros "Hw Ha #H1 #H2".
    destruct ρ1, ρ2; rewrite /region_rel_part /region_rel_perm /region_rel_l.
    - iDestruct (rel_perm_agree with "H1 H2") as "[% _]". by iFrame.
    - iDestruct "H2" as "(_ & %HT & _)". iExFalso.
      iApply (world_interp_open_rel_perm_temporary_cell with "Hw H1 Ha"). done.
    - iDestruct "H1" as "(_ & %HT & _)". iExFalso.
      iApply (world_interp_open_rel_perm_temporary_cell with "Hw H2 Ha"). done.
    - iDestruct "H1" as "(H1 & _)". iDestruct "H2" as "(H2 & _)".
      iDestruct (rel_l_agree with "H1 H2") as "[% _]". by iFrame.
  Qed.

  (** The part of a region reached through a capability: a Global one is not
      reached through a write-local capability. *)
  Lemma region_rel_part_of W C k p' P p g :
    region_rel W C k p' P p g -∗
    ∃ ρ, ⌜ρ = InPerm → isWL p = false⌝ ∗ region_rel_part ρ W C k p' P.
  Proof.
    rewrite /region_rel. iIntros "#H".
    destruct (isWL p) eqn:Hwl.
    { iExists InLocal. iSplit; [by iPureIntro|done]. }
    destruct g.
    { iExists InPerm. iSplit; [by iPureIntro|done]. }
    iDestruct "H" as "[H|H]".
    - iExists InPerm. iSplit; [by iPureIntro|done].
    - iExists InLocal. iSplit; [by iPureIntro|done].
  Qed.

  (** Opening the key of a capability address, with keys [s] open: the
      region of its part, or a tombstone, in which case the world is
      unchanged. *)
  Lemma open_world_interp_next_cases W C s π a p' P p g :
    persistent_cond P →
    addr_key π a ∉ s →
    region_rel W C (addr_key π a) p' P p g -∗ world_interp_open W C s -∗
    (∃ ρ, ⌜ρ = InPerm → isWL p = false⌝ ∗ region_rel_part ρ W C (addr_key π a) p' P ∗
       world_interp_open W C ({[ addr_key π a ]} ∪ s) ∗
       ▷ (∃ v, pc_open W C (addr_key π a) p' P v ρ))
    ∨ (∃ ι, ⌜π = Some ι⌝ ∗ ι ⊒ AQuar ∗ world_interp_open W C s).
  Proof.
    iIntros (Hpers Hnin) "#Hrel Hw".
    assert (∀ x, Persistent (safeGC P x)) as HpersG by (intros x; apply (Hpers (_, _, _))).
    assert (∀ x, Persistent (safeC P x)) as HpersL by (intros x; apply Hpers).
    iDestruct (region_rel_part_of with "Hrel") as (ρ Hρ) "#Hpart".
    destruct ρ.
    - iPoseProof "Hpart" as "Hg". rewrite /region_rel_part /region_rel_perm.
      destruct (decide (std W !! addr_key π a = Some Temporary)) as [HT|HnT].
      + iDestruct (world_interp_open_rel_perm_temporary with "Hw Hg")
          as "[Hw (%a' & %ι & %Hk & #Hq)]"; [done|done|].
        iRight. iExists ι. destruct π as [ι'|]; [|by rewrite addr_key_None in Hk].
        rewrite addr_key_Some in Hk. injection Hk as -> ->. by iFrame "Hq Hw".
      + iDestruct (open_world_interp_permanent with "Hw Hg") as "[Hw Hres]"; [done|done|].
        iDestruct (heap_key_open_cases with "Hres") as "[Hres|(%a' & %ι & %Hk & #Hq)]".
        * iDestruct "Hres" as (v) "(%HpO & Hc & HP)".
          iLeft. iExists InPerm. iFrame "Hw Hpart %". iNext. iExists v.
          iApply (pc_open_intro W C _ p' P v InPerm with "[Hc HP]"); [by intros _|by iFrame "∗%"].
        * iRight. iExists ι. destruct π as [ι'|]; [|by rewrite addr_key_None in Hk].
          rewrite addr_key_Some in Hk Hnin HnT |- *. injection Hk as -> ->.
          iSplit; first done. iFrame "Hq".
          iApply (close_world_interp_next_quarantined_heap_perm with "Hq Hw Hg"); done.
    - iPoseProof "Hpart" as "(Hl & %HT & _)".
      iDestruct (open_world_interp_temporary with "Hw Hl") as "[Hw Hres]"; [done|done|].
      iDestruct (heap_key_open_cases with "Hres") as "[Hres|(%a' & %ι & %Hk & #Hq)]".
      + iDestruct "Hres" as (v) "(%HpO & Hc & HP & Hmono)".
        iLeft. iExists InLocal. iFrame "Hw Hpart". iSplit; [iPureIntro; by intros ?|].
        iNext. iExists v.
        iApply (pc_open_intro W C _ p' P v InLocal with "[Hc HP Hmono]");
          [by intros ?|by iFrame "∗%"].
      + iRight. iExists ι. destruct π as [ι'|]; [|by rewrite addr_key_None in Hk].
        rewrite addr_key_Some in Hk Hnin HT |- *. injection Hk as -> ->.
        iSplit; first done. iFrame "Hq".
        iApply (close_world_interp_next_quarantined_heap_l with "Hq Hw Hl"); done.
  Qed.

  Lemma open_world_interp_cases W C π a p' P p g :
    persistent_cond P →
    region_rel W C (addr_key π a) p' P p g -∗ world_interp W C -∗
    (∃ ρ, ⌜ρ = InPerm → isWL p = false⌝ ∗ region_rel_part ρ W C (addr_key π a) p' P ∗
       world_interp_open W C [addr_key π a] ∗
       ▷ (∃ v, pc_open W C (addr_key π a) p' P v ρ))
    ∨ (∃ ι, ⌜π = Some ι⌝ ∗ ι ⊒ AQuar ∗ world_interp W C).
  Proof.
    iIntros (Hpers) "#Hrel Hw". iEval (rewrite open_world_interp_empty) in "Hw".
    iDestruct (open_world_interp_next_cases with "Hrel Hw")
      as "[(%ρ & H1 & H2 & Hw & H4)|(%ι & H1 & H2 & Hw)]"; [done|set_solver|..].
    - iLeft. iExists ρ. iFrame "H1 H2 H4".
      rewrite (world_interp_open_permutation W C ({[addr_key π a]} ∪ []) [addr_key π a]);
        [done|set_solver].
    - iRight. iExists ι. iFrame "H1 H2". by rewrite open_world_interp_empty.
  Qed.

  (** The stores of words [ws], safe in the world, through a safe
      capability with write permission, from its cursor: each store below
      the end opens the cell in the world and closes it with the stored
      word. The world is the destination at every step. *)
  Lemma world_interp_cells_store_acc (W : WORLD) (C : CmptName)
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId) (ws : list LWord) :
    writeAllowed p = true →
    (b <= a)%a →
    π = None →
    interp W C (Cap p g b e a @@? π) -∗
    ([∗ list] v ∈ ws, interp W C v) -∗
    cells_store_acc (λ _, world_interp W C) p e a π ws.
  Proof.
    iIntros (Hwa Hb ->) "#Hinterp_dst #Hws".
    iIntros "!>" (i Hi Hie) "Hworld_interp".
    set (ea := a ^+ i).
    assert (ea ∈ₐ [b, e)) as Hbounds by (subst ea; solve_addr).
    assert (withinBounds b e ea = true) as Hwb by (apply withinBounds_true_iff; solve_addr).
    iDestruct (write_allowed_inv _ _ ea with "Hinterp_dst")
      as (p' P Hflows Hpers) "(#Hrel & _ & #Hwcond & _)"; [solve_addr | by rewrite Hwa |].
    iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ ea with "Hinterp_dst") as %Hnot_shadow;
      [by eapply writeAllowed_nonO | done |].
    iDestruct (open_world_interp_cases W C None ea p' P p g with "Hrel Hworld_interp")
      as "[(%ρ & %Hρwl & #Hpart & Hworld_interp & (%v & WorldRes)) | (%ι & % & _)]";
      [done | | done].
    iDestruct (pc_open_acc_forall with "Hpart WorldRes") as "[ (>Ha & _) WorldRes]".
    iDestruct (addr_key_pointsto with "Ha") as "[Ha Hshare]".
    iDestruct (key_share_deref with "Hshare") as (dw Hdw) "[Hdw Hshare]".
    iEval (rewrite deref_witness_res_deref_res -Hdw) in "Hdw".
    iModIntro. iExists v, (deref_share dw). iFrame "Ha Hdw". iSplit; first done.
    iIntros "!> Ha Hdw".
    iEval (rewrite Hdw -deref_witness_res_deref_res) in "Hdw".
    iDestruct ("Hshare" with "Hdw") as "Hshare".
    set (v' := lstore_word p (ws !!! i)).
    iAssert (pc_content ρ W C P v') as "Hinterp'".
    { iApply (pc_content_wcond with "Hwcond"); first done.
      destruct (lookup_lt_is_Some_2 ws i) as [wi Hwi]; first lia.
      rewrite (list_lookup_total_correct _ _ _ Hwi).
      by iApply (big_sepL_lookup with "Hws"). }
    iDestruct (addr_key_pointsto_join None with "Ha Hshare") as "Ha".
    iDestruct ("WorldRes" with "[$Ha $Hinterp']") as "WorldRes".
    iModIntro.
    iApply (pc_close with "Hworld_interp Hpart WorldRes"); done.
  Qed.

  (** The loads of [n] cells, safe in the world, through a safe capability
      with read permission, from its cursor: each load below the end opens
      the cell in the world, with the status witness of the world's heap
      provenance, and closes it as is. The loaded words are safe. *)
  Lemma world_interp_cells_load_acc (W : WORLD) (C : CmptName)
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId) (n : nat) :
    readAllowed p = true →
    (b <= a)%a →
    π = None →
    thread_in th C -∗
    interp W C (Cap p g b e a @@? π) -∗
    cells_load_acc (λ _ ls, world_interp W C ∗ [∗ list] v ∈ ls, interp W C v)%I p e a π n.
  Proof.
    iIntros (Hra Hb ->) "#Hth #Hinterp_src".
    iIntros "!>" (i ls Hi Hie) "[Hworld_interp #Hls]".
    set (ea := a ^+ i).
    assert (ea ∈ₐ [b, e)) as Hbounds by (subst ea; solve_addr).
    assert (withinBounds b e ea = true) as Hwb by (apply withinBounds_true_iff; solve_addr).
    iDestruct (read_allowed_inv _ _ ea with "Hth Hinterp_src")
      as (p' P Hflows Hpers) "(#Hrel & Hzcond & #Hrcond & Hwcond)"; [solve_addr | auto |].
    iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ ea with "Hinterp_src") as %Hnot_shadow;
      [by eapply readAllowed_nonO | done |].
    iDestruct (open_world_interp_cases W C None ea p' P p g with "Hrel Hworld_interp")
      as "[(%ρ & %Hρwl & #Hpart & Hworld_interp & (%v & WorldRes)) | (%ι & % & _)]";
      [done | | done].
    iDestruct (pc_open_acc with "WorldRes") as "[ (>Ha & Hinterp) WorldRes]".
    iDestruct (addr_key_pointsto with "Ha") as "[Ha Hshare]".
    iPoseProof load_witness_plain_intro as "Hwit".
    iDestruct (key_share_deref with "Hshare") as (dw Hdw) "[Hdw Hshare]".
    iModIntro. iExists v, (DfracOwn 1), LoadPlain, dw.
    iFrame "Ha Hwit Hdw". iSplit; first done. iSplit; first done.
    iIntros "!>" (v' Hpost) "Ha _ Hdw".
    iDestruct ("Hshare" with "Hdw") as "Hshare".
    pose proof (pc_content_persistent ρ W C P v Hpers).
    iDestruct "Hinterp" as "#HφV".
    iDestruct (pc_content_rcond with "Hrcond HφV") as "#Hnormal_p'".
    iAssert (interp_in_mem p W C v)%I as "#Hnormal".
    { iEval (rewrite /interp_in_mem /= /interp_in_mem_pre).
      iApply (interp_weakening_word_load W C p p' v with "Hth"); first exact Hflows.
      iEval (rewrite /interp_in_mem_pre) in "Hnormal_p'".
      iExact "Hnormal_p'". }
    iDestruct (interp_in_mem_load_post with "Hnormal") as "#Hv'"; first exact Hpost.
    iDestruct (addr_key_pointsto_join None with "Ha Hshare") as "Ha".
    iDestruct ("WorldRes" with "[$Ha $HφV]") as "WorldRes".
    iModIntro. iSplitL.
    - iApply (pc_close with "Hworld_interp Hpart WorldRes"); done.
    - rewrite ?big_sepL_app /=. iFrame "Hls Hv'".
  Qed.

  (** A Permanent region whose cell is held is not a Temporary key of the
      local world, even with keys open. *)
  Lemma world_interp_open_rel_perm_cell_not_temporary W C s k p φ w :
    world_interp_open W C s -∗ k ↪ᵖ[C]{p} φ -∗ k ↦ₖ w -∗
    world_interp_open W C s ∗ k ↦ₖ w ∗ ⌜std W !! k ≠ Some Temporary⌝.
  Proof.
    iIntros "Hw #Hr Hk".
    destruct (decide (std W !! k = Some Temporary)) as [HT|HnT]; last by iFrame.
    iExFalso.
    iEval (rewrite world_interp_open_eq) in "Hw".
    iDestruct "Hw" as "[Hg _]".
    iDestruct (perm_open with "Hg Hr") as "[_ (%φ' & _ & _ & Hb & _)]".
    { rewrite elem_of_open_perm. naive_solver. }
    rewrite /body_perm. destruct k as [a0|a0 ι]; cbn.
    - iDestruct "Hb" as (v) "(_ & Hv & _)".
      iApply (heap_pointsto_valid_2 (LNonHeap a0) (LNonHeap a0) with "Hv Hk"). done.
    - iDestruct "Hb" as "[(%v & _ & Hv & _)|#Hq]".
      + iApply (heap_pointsto_valid_2 (LHeap a0 ι) (LHeap a0 ι) with "Hv Hk"). done.
      + iApply (heap_pointsto_quar_false with "Hk Hq").
  Qed.

  (** The stores of [ws] through a safe capability of the object [ι], from
      its cursor [a], in the world. The first cell is opened before the
      stores, and stays open until the world closes: its status share
      refutes the tombstones of the other cells of [ι]. When the first cell
      is a tombstone, [ι] is quarantined. *)
  Lemma world_interp_cells_store_acc_heap (W : WORLD) (C : CmptName)
    (p : Perm) (g : Locality) (b e a : Addr) (ι : AId) (ws : list LWord) :
    writeAllowed p = true →
    (b <= a)%a →
    (a < e)%a →
    interp W C (Cap p g b e a @@? Some ι) -∗
    ([∗ list] v ∈ ws, interp W C v) -∗
    world_interp W C -∗
    ◇ ((ι ⊒ AQuar ∗ world_interp W C) ∨
       ∃ D : nat → iProp Σ,
         D 0 ∗
         cells_store_acc D p e a (Some ι) ws ∗
         ▷ (∀ i, D i -∗ world_interp W C)).
  Proof.
    iIntros (Hwa Hb Hae) "#Hinterp_dst #Hws Hworld_interp".
    assert (withinBounds b e (a ^+ 0) = true) as Hwb0
      by (apply withinBounds_true_iff; solve_addr).
    iDestruct (write_allowed_inv _ _ (a ^+ 0) with "Hinterp_dst")
      as (p0 P0 Hflows0 Hpers0) "(#Hrel0 & _ & #Hwcond0 & _)";
      [solve_addr | by rewrite Hwa |].
    assert (isO p0 = false) as HnO0.
    { apply writeAllowed_nonO. by eapply writeAllowed_flowsto. }
    iDestruct (open_world_interp_cases W C (Some ι) (a ^+ 0) p0 P0 p g
                 with "Hrel0 Hworld_interp")
      as "[(%ρ0 & %Hρ0wl & #Hpart0 & Hworld_open & (%v0 & Hres0))
          | (%ι' & %Hι' & #Hq & Hworld_interp)]";
      [done |..]; cycle 1.
    { injection Hι' as <-. iModIntro. iLeft. by iFrame "Hq Hworld_interp". }
    set (k0 := addr_key (Some ι) (a ^+ 0)).
    pose proof (pc_content_persistent ρ0 W C P0 v0 Hpers0).
    iDestruct (pc_open_acc with "Hres0") as "[ (>Hk0 & #Hφ0) _]".
    iAssert (world_interp_open W C [k0] ∗ k0 ↦ₖ v0 ∗
             ⌜ρ0 = InPerm → std W !! k0 ≠ Some Temporary⌝)%I
      with "[Hworld_open Hk0]" as "(Hworld_open & Hk0 & %HnT0)".
    { destruct ρ0; last by iFrame.
      iDestruct (world_interp_open_rel_perm_cell_not_temporary with "Hworld_open Hpart0 Hk0")
        as "($ & $ & %HnT)". by iPureIntro. }
    iPoseProof (pc_open_rebuild ρ0 W C k0 p0 P0 with "Hpart0") as "#Hreb"; [done|done|].
    iModIntro. iRight.
    iExists (λ i, world_interp_open W C [k0] ∗
      match i with
      | 0 => k0 ↦ₖ v0
      | S _ => ∃ v, k0 ↦ₖ v ∗ pc_content ρ0 W C P0 v
      end)%I.
    iFrame "Hworld_open Hk0".
    iSplitR.
    - iIntros "!>" (i Hi Hie) "(Hworld_open & Hk)".
      set (ea := a ^+ i).
      assert (withinBounds b e ea = true) as Hwb
        by (apply withinBounds_true_iff; subst ea; solve_addr).
      iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ ea with "Hinterp_dst") as %Hnot_shadow;
        [by apply writeAllowed_nonO | done |].
      (* The store of [ws !!! i] into an open cell [k] of the world *)
      iAssert (∀ (k : LAddr) ρ (P : interpO Σ) v,
        ⌜k = addr_key (Some ι) ea⌝ -∗
        ⌜ρ = InPerm → isWL p = false⌝ -∗
        ▷ (if isWL p then wcond_wl P C interp else wcond_nwl P C interp) -∗
        k ↦ₖ v -∗
        ∃ q, ea ↦ₐ v ∗ deref_res (Some ι) q ∗
          ▷ (ea ↦ₐ lstore_word p (ws !!! i) -∗ deref_res (Some ι) q -∗
             k ↦ₖ lstore_word p (ws !!! i) ∗
             pc_content ρ W C P (lstore_word p (ws !!! i))))%I as "Hstore".
      { iIntros (k ρ P v -> Hρwl) "#Hwcond Hk".
        iDestruct (addr_key_pointsto with "Hk") as "[Ha Hshare]".
        iDestruct (key_share_deref with "Hshare") as (dw Hdw) "[Hdw Hshare]".
        iEval (rewrite deref_witness_res_deref_res -Hdw) in "Hdw".
        iExists (deref_share dw). iFrame "Ha Hdw".
        iIntros "!> Ha Hdw".
        iEval (rewrite Hdw -deref_witness_res_deref_res) in "Hdw".
        iDestruct ("Hshare" with "Hdw") as "Hshare".
        iDestruct (addr_key_pointsto_join with "Ha Hshare") as "$".
        iApply (pc_content_wcond with "Hwcond"); first done.
        destruct (lookup_lt_is_Some_2 ws i) as [wi Hwi]; first lia.
        rewrite (list_lookup_total_correct _ _ _ Hwi).
        by iApply (big_sepL_lookup with "Hws"). }
      destruct i as [|j].
      + iDestruct ("Hstore" $! k0 ρ0 P0 v0 with "[//] [//] Hwcond0 Hk")
          as (q) "(Ha & Hdw & Hclose)".
        iModIntro. iExists v0, q. iFrame "Ha Hdw". iSplit; first done.
        iIntros "!> Ha Hdw". iModIntro. iFrame "Hworld_open".
        iExists _. iApply ("Hclose" with "Ha Hdw").
      + iDestruct "Hk" as (vk) "[Hk Hck]".
        iDestruct (write_allowed_inv _ _ ea with "Hinterp_dst")
          as (p' P Hflows Hpers) "(#Hrel & _ & #Hwcond & _)";
          [subst ea; solve_addr | by rewrite Hwa |].
        assert (addr_key (Some ι) ea ∉ [k0]) as Hnotin.
        { rewrite /k0 /ea !addr_key_Some list_elem_of_singleton.
          intros Heq. injection Heq as Heq. solve_addr. }
        iDestruct (open_world_interp_next_cases W C [k0] (Some ι) ea p' P p g
                     with "Hrel Hworld_open")
          as "[(%ρ & %Hρwl & #Hpart & Hworld_open & (%v & Hres)) | (%ι' & %Hι' & #Hq & _)]";
          [done | exact Hnotin |..]; cycle 1.
        { injection Hι' as <-. iExFalso.
          iEval (rewrite /k0 addr_key_Some) in "Hk".
          iApply (heap_pointsto_quar_false with "Hk Hq"). }
        iDestruct (pc_open_acc_forall with "Hpart Hres") as "[ (>Hki & _) Hcl]".
        iDestruct ("Hstore" $! (addr_key (Some ι) ea) ρ P v
                    with "[//] [//] Hwcond Hki")
          as (q) "(Ha & Hdw & Hclose)".
        iModIntro. iExists v, q. iFrame "Ha Hdw". iSplit; first done.
        iIntros "!> Ha Hdw".
        iDestruct ("Hclose" with "Ha Hdw") as "Hres".
        iDestruct ("Hcl" with "Hres") as "Hres".
        iModIntro. iSplitL "Hworld_open Hres"; last by iExists vk; iFrame "Hk Hck".
        iApply (pc_close_next with "Hworld_open Hpart Hres"); done.
    - iIntros "!>" (i) "(Hworld_open & Hk)".
      destruct i as [|j].
      + iApply (pc_close with "Hworld_open Hpart0 [Hk]"); first done.
        iApply "Hreb". by iFrame "Hk Hφ0".
      + iDestruct "Hk" as (v) "Hk".
        iApply (pc_close with "Hworld_open Hpart0 [Hk]"); first done.
        by iApply "Hreb".
  Qed.

  (** The loads of [n] cells through a safe capability of the object [ι],
      from its cursor [a], in the world. As for the stores, the first cell
      is opened before the loads and stays open: its status share refutes
      the tombstones of the other cells of [ι]. The loaded words are
      safe. *)
  Lemma world_interp_cells_load_acc_heap (W : WORLD) (C : CmptName)
    (p : Perm) (g : Locality) (b e a : Addr) (ι : AId) (n : nat) :
    readAllowed p = true →
    (b <= a)%a →
    (a < e)%a →
    thread_in th C -∗
    interp W C (Cap p g b e a @@? Some ι) -∗
    world_interp W C -∗
    ◇ ((ι ⊒ AQuar ∗ world_interp W C) ∨
       ∃ L : nat → list LWord → iProp Σ,
         L 0 [] ∗
         cells_load_acc L p e a (Some ι) n ∗
         ▷ (∀ i ls, L i ls -∗ world_interp W C ∗ [∗ list] v ∈ ls, interp W C v)).
  Proof.
    iIntros (Hra Hb Hae) "#Hth #Hinterp_src Hworld_interp".
    assert (withinBounds b e (a ^+ 0) = true) as Hwb0
      by (apply withinBounds_true_iff; solve_addr).
    iDestruct (read_allowed_inv _ _ (a ^+ 0) with "Hth Hinterp_src")
      as (p0 P0 Hflows0 Hpers0) "(#Hrel0 & _ & #Hrcond0 & _)";
      [solve_addr | by rewrite Hra |].
    assert (isO p0 = false) as HnO0.
    { apply readAllowed_nonO. by eapply readAllowed_flowsto. }
    iDestruct (open_world_interp_cases W C (Some ι) (a ^+ 0) p0 P0 p g
                 with "Hrel0 Hworld_interp")
      as "[(%ρ0 & %Hρ0wl & #Hpart0 & Hworld_open & (%v0 & Hres0))
          | (%ι' & %Hι' & #Hq & Hworld_interp)]";
      [done |..]; cycle 1.
    { injection Hι' as <-. iModIntro. iLeft. by iFrame "Hq Hworld_interp". }
    set (k0 := addr_key (Some ι) (a ^+ 0)).
    pose proof (pc_content_persistent ρ0 W C P0 v0 Hpers0).
    iDestruct (pc_open_acc with "Hres0") as "[ (>Hk0 & #Hφ0) _]".
    iAssert (world_interp_open W C [k0] ∗ k0 ↦ₖ v0 ∗
             ⌜ρ0 = InPerm → std W !! k0 ≠ Some Temporary⌝)%I
      with "[Hworld_open Hk0]" as "(Hworld_open & Hk0 & %HnT0)".
    { destruct ρ0; last by iFrame.
      iDestruct (world_interp_open_rel_perm_cell_not_temporary with "Hworld_open Hpart0 Hk0")
        as "($ & $ & %HnT)". by iPureIntro. }
    iPoseProof (pc_open_rebuild ρ0 W C k0 p0 P0 with "Hpart0") as "#Hreb"; [done|done|].
    iModIntro. iRight.
    iExists (λ _ ls, world_interp_open W C [k0] ∗ k0 ↦ₖ v0 ∗
      [∗ list] v ∈ ls, interp W C v)%I.
    iFrame "Hworld_open Hk0". iSplitR; first done.
    iSplitR.
    - iIntros "!>" (i ls Hi Hie) "(Hworld_open & Hk0 & #Hls)".
      set (ea := a ^+ i).
      assert (withinBounds b e ea = true) as Hwb
        by (apply withinBounds_true_iff; subst ea; solve_addr).
      iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ ea with "Hinterp_src") as %Hnot_shadow;
        [by apply readAllowed_nonO | done |].
      (* The load of an open cell [k] of the world *)
      iAssert (∀ (k : LAddr) ρ (P : interpO Σ) p' v,
        ⌜k = addr_key (Some ι) ea⌝ -∗
        ⌜PermFlowsTo p p'⌝ -∗
        ⌜persistent_cond P⌝ -∗
        ▷ rcond_l P C p' interp -∗
        ▷ pc_content ρ W C P v -∗
        k ↦ₖ v -∗
        ∃ dw, ⌜Some ι = deref_id dw⌝ ∗ ea ↦ₐ v ∗ deref_witness_res dw ∗
          ▷ (∀ v', ⌜load_post LoadPlain p v v'⌝ -∗
                   ea ↦ₐ v -∗ deref_witness_res dw -∗
                   k ↦ₖ v ∗ interp W C v'))%I as "Hload".
      { iIntros (k ρ P p' v -> Hflows Hpers) "#Hrcond HφV Hk".
        pose proof (pc_content_persistent ρ W C P v Hpers).
        iDestruct "HφV" as "#HφV".
        iDestruct (addr_key_pointsto with "Hk") as "[Ha Hshare]".
        iDestruct (key_share_deref with "Hshare") as (dw Hdw) "[Hdw Hshare]".
        iExists dw. iFrame "Ha Hdw". iSplit; first done.
        iIntros "!>" (v' Hpost) "Ha Hdw".
        iDestruct ("Hshare" with "Hdw") as "Hshare".
        iDestruct (pc_content_rcond with "Hrcond HφV") as "#Hnormal_p'".
        iAssert (interp_in_mem p W C v)%I as "#Hnormal".
        { iEval (rewrite /interp_in_mem /= /interp_in_mem_pre).
          iApply (interp_weakening_word_load W C p p' v with "Hth"); first exact Hflows.
          iEval (rewrite /interp_in_mem_pre) in "Hnormal_p'".
          iExact "Hnormal_p'". }
        iDestruct (interp_in_mem_load_post with "Hnormal") as "#Hv'"; first exact Hpost.
        iDestruct (addr_key_pointsto_join with "Ha Hshare") as "Ha".
        by iFrame "Ha Hv'". }
      destruct i as [|j].
      + iDestruct ("Hload" $! k0 ρ0 P0 p0 v0 with "[//] [//] [//] Hrcond0 Hφ0 Hk0")
          as (dw Hdw) "(Ha & Hdw & Hclose)".
        iPoseProof load_witness_plain_intro as "Hwit".
        iModIntro. iExists v0, (DfracOwn 1), LoadPlain, dw.
        iFrame "Ha Hdw Hwit". iSplit; first done. iSplit; first done.
        iIntros "!>" (v' Hpost) "Ha _ Hdw".
        iDestruct ("Hclose" with "[//] Ha Hdw") as "[Hk0 #Hv']".
        iModIntro. iFrame "Hworld_open Hk0".
        by iFrame "Hls Hv'".
      + iDestruct (read_allowed_inv _ _ ea with "Hth Hinterp_src")
          as (p' P Hflows Hpers) "(#Hrel & _ & #Hrcond & _)";
          [subst ea; solve_addr | by rewrite Hra |].
        assert (addr_key (Some ι) ea ∉ [k0]) as Hnotin.
        { rewrite /k0 /ea !addr_key_Some list_elem_of_singleton.
          intros Heq. injection Heq as Heq. solve_addr. }
        iDestruct (open_world_interp_next_cases W C [k0] (Some ι) ea p' P p g
                     with "Hrel Hworld_open")
          as "[(%ρ & %Hρwl & #Hpart & Hworld_open & (%v & Hres)) | (%ι' & %Hι' & #Hq & _)]";
          [done | exact Hnotin |..]; cycle 1.
        { injection Hι' as <-. iExFalso.
          iEval (rewrite /k0 addr_key_Some) in "Hk0".
          iApply (heap_pointsto_quar_false with "Hk0 Hq"). }
        pose proof (pc_content_persistent ρ W C P v Hpers).
        iDestruct (pc_open_acc with "Hres") as "[ (>Hki & #Hφ) Hcl]".
        iDestruct ("Hload" $! (addr_key (Some ι) ea) ρ P p' v
                    with "[//] [//] [//] Hrcond Hφ Hki")
          as (dw Hdw) "(Ha & Hdw & Hclose)".
        iPoseProof load_witness_plain_intro as "Hwit".
        iModIntro. iExists v, (DfracOwn 1), LoadPlain, dw.
        iFrame "Ha Hdw Hwit". iSplit; first done. iSplit; first done.
        iIntros "!>" (v' Hpost) "Ha _ Hdw".
        iDestruct ("Hclose" with "[//] Ha Hdw") as "[Hki #Hv']".
        iModIntro. iFrame "Hk0 Hls Hv'".
        iApply (pc_close_next with "Hworld_open Hpart [Hcl Hki]"); [done | done |].
        iApply ("Hcl" with "[$Hki $Hφ]").
    - iIntros "!>" (i ls) "(Hworld_open & Hk0 & $)".
      iApply (pc_close with "Hworld_open Hpart0 [Hk0]"); first done.
      iApply "Hreb". by iFrame "Hk0 Hφ0".
  Qed.

End wp_interp.
