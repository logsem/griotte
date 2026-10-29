From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode logrel register_tactics clear_registers_spec.
From griotte Require Import stack_world_resources call_stack.
From griotte Require Export code_blocks.

(** * Shared helpers of the case-study specifications

    - [code_blocks] (re-exported): offsets of the blocks of the code of a
      compartment, and the tactics to focus on its blocks,
    - [switcher_call_args_0] ... [switcher_call_args_3]: the argument
      registers of a call to the switcher, for an entry point with 0 to 3
      arguments,
    - [registers_pointsto_extract] ... [registers_pointsto_ret_spec]: the
      registers of a register map. *)

(** ** Arguments of a call to the switcher

    [switcher_call_args_<n>] builds the argument registers [arg_rmap] and
    the other registers [rmap'] expected by the specification of the
    switcher call, for an entry point with [n] arguments, passed in [ca0],
    [ca1] and [ca2]. The arguments must be safe to share; the other argument
    registers are passed unchanged. *)
Section Switcher_call_args.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Lemma switcher_call_args_0 W C (rmap : LReg) :
    dom rmap = all_registers_s ∖ {[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ->
    regs[th] rmap -∗
    ∃ arg_rmap rmap',
      ⌜ dom rmap' = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ⌝ ∗
      ⌜ is_arg_rmap arg_rmap 8 ⌝ ∗
      ([∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ[th] warg ∗
                                     (if decide (rarg ∈ dom_arg_rmap 0)
                                      then interp W C warg
                                      else True)) ∗
      regs[th] rmap'.
  Proof.
    iIntros (Hrmap_dom) "Hrmap".
    iExtractList "Hrmap" [ca0;ca1;ca2;ca3;ca4;ca5;ct0]
      as ["Hca0"; "Hca1"; "Hca2"; "Hca3"; "Hca4"; "Hca5"; "Hct0"].
    iExists {[ ca0 := wca0; ca1 := wca1; ca2 := wca2; ca3 := wca3;
               ca4 := wca4; ca5 := wca5; ct0 := wct0 ]}, _.
    iFrame "Hrmap".
    iSplit.
    { iPureIntro.
      repeat (rewrite dom_delete_L).
      rewrite Hrmap_dom /dom_arg_rmap.
      set_solver+.
    }
    iSplit; first by rewrite /is_arg_rmap.
    repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
    done.
  Qed.

  Lemma switcher_call_args_1 W C (rmap : LReg) (wca0 : LWord) :
    dom rmap = all_registers_s ∖ {[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ca0 ]} ->
    ca0 ↦ᵣ[th] wca0 -∗
    interp W C wca0 -∗
    regs[th] rmap -∗
    ∃ arg_rmap rmap',
      ⌜ dom rmap' = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ⌝ ∗
      ⌜ is_arg_rmap arg_rmap 8 ⌝ ∗
      ([∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ[th] warg ∗
                                     (if decide (rarg ∈ dom_arg_rmap 1)
                                      then interp W C warg
                                      else True)) ∗
      regs[th] rmap'.
  Proof.
    iIntros (Hrmap_dom) "Hca0 #Hinterp_ca0 Hrmap".
    iExtractList "Hrmap" [ca1;ca2;ca3;ca4;ca5;ct0]
      as ["Hca1"; "Hca2"; "Hca3"; "Hca4"; "Hca5"; "Hct0"].
    iExists {[ ca0 := wca0; ca1 := wca1; ca2 := wca2; ca3 := wca3;
               ca4 := wca4; ca5 := wca5; ct0 := wct0 ]}, _.
    iFrame "Hrmap".
    iSplit.
    { iPureIntro.
      repeat (rewrite dom_delete_L).
      rewrite Hrmap_dom /dom_arg_rmap.
      set_solver+.
    }
    iSplit; first by rewrite /is_arg_rmap.
    repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
    done.
  Qed.

  Lemma switcher_call_args_2 W C (rmap : LReg) (wca0 wca1 : LWord) :
    dom rmap = all_registers_s ∖ {[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ca0 ; ca1 ]} ->
    ca0 ↦ᵣ[th] wca0 -∗
    interp W C wca0 -∗
    ca1 ↦ᵣ[th] wca1 -∗
    interp W C wca1 -∗
    regs[th] rmap -∗
    ∃ arg_rmap rmap',
      ⌜ dom rmap' = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ⌝ ∗
      ⌜ is_arg_rmap arg_rmap 8 ⌝ ∗
      ([∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ[th] warg ∗
                                     (if decide (rarg ∈ dom_arg_rmap 2)
                                      then interp W C warg
                                      else True)) ∗
      regs[th] rmap'.
  Proof.
    iIntros (Hrmap_dom) "Hca0 #Hinterp_ca0 Hca1 #Hinterp_ca1 Hrmap".
    iExtractList "Hrmap" [ca2;ca3;ca4;ca5;ct0]
      as ["Hca2"; "Hca3"; "Hca4"; "Hca5"; "Hct0"].
    iExists {[ ca0 := wca0; ca1 := wca1; ca2 := wca2; ca3 := wca3;
               ca4 := wca4; ca5 := wca5; ct0 := wct0 ]}, _.
    iFrame "Hrmap".
    iSplit.
    { iPureIntro.
      repeat (rewrite dom_delete_L).
      rewrite Hrmap_dom /dom_arg_rmap.
      set_solver+.
    }
    iSplit; first by rewrite /is_arg_rmap.
    repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
    done.
  Qed.

  Lemma switcher_call_args_3 W C (rmap : LReg) (wca0 wca1 wca2 : LWord) :
    dom rmap = all_registers_s ∖ {[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ca0 ; ca1 ; ca2 ]} ->
    ca0 ↦ᵣ[th] wca0 -∗
    interp W C wca0 -∗
    ca1 ↦ᵣ[th] wca1 -∗
    interp W C wca1 -∗
    ca2 ↦ᵣ[th] wca2 -∗
    interp W C wca2 -∗
    regs[th] rmap -∗
    ∃ arg_rmap rmap',
      ⌜ dom rmap' = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ⌝ ∗
      ⌜ is_arg_rmap arg_rmap 8 ⌝ ∗
      ([∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ[th] warg ∗
                                     (if decide (rarg ∈ dom_arg_rmap 3)
                                      then interp W C warg
                                      else True)) ∗
      regs[th] rmap'.
  Proof.
    iIntros (Hrmap_dom) "Hca0 #Hinterp_ca0 Hca1 #Hinterp_ca1 Hca2 #Hinterp_ca2 Hrmap".
    iExtractList "Hrmap" [ca3;ca4;ca5;ct0]
      as ["Hca3"; "Hca4"; "Hca5"; "Hct0"].
    iExists {[ ca0 := wca0; ca1 := wca1; ca2 := wca2; ca3 := wca3;
               ca4 := wca4; ca5 := wca5; ct0 := wct0 ]}, _.
    iFrame "Hrmap".
    iSplit.
    { iPureIntro.
      repeat (rewrite dom_delete_L).
      rewrite Hrmap_dom /dom_arg_rmap.
      set_solver+.
    }
    iSplit; first by rewrite /is_arg_rmap.
    repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
    done.
  Qed.

End Switcher_call_args.

(** ** The free part of a fresh stack

    A call from a fresh stack [[b, e)] hands to the switcher the part of the
    stack below the space reserved at its top. *)
Section Fresh_stack.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
  .

  Lemma stk_start_region_split (b e : Addr) (stk_mem : list LWord) :
    (b + StackEntry_reserved_space <= e)%Z ->
    [[b, e]] ↦ₐ [[stk_mem]] -∗
    ∃ stk_mem' stk_res,
      [[stk_free_b b (stk_start_a b e), stk_free_e e (stk_start_a b e)]] ↦ₐ [[stk_mem']] ∗
      [[stk_start_a b e, e]] ↦ₐ [[stk_res]].
  Proof.
    iIntros (Hsize) "Hstk".
    iDestruct (big_sepL2_length with "Hstk") as %Hlen.
    rewrite -(take_drop (finz.dist b (stk_start_a b e)) stk_mem).
    iDestruct (region_pointsto_split b e (stk_start_a b e) with "Hstk") as "[Hstk Hres]".
    { stk_unfold; solve_addr+Hsize. }
    { rewrite length_take finz_seq_between_length in Hlen |- *.
      stk_unfold; rewrite /finz.dist in Hlen |- *; solve_addr+Hsize Hlen. }
    iExists _, _. iFrame "Hstk Hres".
  Qed.

  Lemma stk_start_seq_split (b e : Addr) :
    (b + StackEntry_reserved_space <= e)%Z ->
    finz.seq_between b e =
      stk_free b e (stk_start_a b e) ++ finz.seq_between (stk_start_a b e) e.
  Proof.
    intros Hsize. rewrite /stk_free. apply finz_seq_between_split. stk_unfold; solve_addr+Hsize.
  Qed.

  Lemma stk_start_revoked_split (W : WORLD) (C : CmptName) (b e : Addr) :
    (b + StackEntry_reserved_space <= e)%Z ->
    StackRevokedResources W C (finz.seq_between b e) ⊣⊢
    StackRevokedResources W C (stk_free b e (stk_start_a b e)) ∗
    StackRevokedResources W C (finz.seq_between (stk_start_a b e) e).
  Proof.
    intros Hsize. by rewrite {1}(stk_start_seq_split b e Hsize) StackRevokedResources_app.
  Qed.

  Lemma stk_start_revoked_addresses (W : WORLD) (b e : Addr) :
    (b + StackEntry_reserved_space <= e)%Z ->
    revoked_addresses W (finz.seq_between b e) ->
    revoked_addresses W (stk_free b e (stk_start_a b e)).
  Proof.
    intros Hsize Hrevoked.
    rewrite (stk_start_seq_split b e Hsize) in Hrevoked.
    by apply revoked_addresses_app in Hrevoked as [? _].
  Qed.

  Lemma stk_start_region_join (b e : Addr) (stk_mem stk_res : list LWord) :
    (b + StackEntry_reserved_space <= e)%Z ->
    [[stk_free_b b (stk_start_a b e), stk_free_e e (stk_start_a b e)]] ↦ₐ [[stk_mem]] -∗
    [[stk_start_a b e, e]] ↦ₐ [[stk_res]] -∗
    [[b, e]] ↦ₐ [[stk_mem ++ stk_res]].
  Proof.
    iIntros (Hsize) "Hstk Hres".
    iDestruct (big_sepL2_length with "Hres") as %Hlen.
    iApply (region_pointsto_split_r b e (stk_start_a b e)); last iFrame.
    { stk_unfold; solve_addr+Hsize. }
    { rewrite -Hlen finz_seq_between_length. done. }
  Qed.
End Fresh_stack.

(** A sub-range of a range outside the shadow table. *)
Lemma disjoint_from_shadow_weaken `{ShadowRegion} (b e b' e' : Addr) :
  (b <= b')%a → (e' <= e)%a →
  disjoint_from_shadow b e → disjoint_from_shadow b' e'.
Proof.
  rewrite /disjoint_from_shadow !elem_of_disjoint.
  intros Hb He Hdisj a Ha Hsh. apply (Hdisj a); last done.
  apply elem_of_finz_seq_between in Ha. apply elem_of_finz_seq_between. solve_addr.
Qed.

(** ** Registers of a register map

    [registers_pointsto_extract], [registers_pointsto_extract2] and
    [registers_pointsto_extract3] take one to three registers out of a
    register map, and give the map back once they are updated.
    [registers_pointsto_switcher_return] and [registers_pointsto_ret_spec]
    split a full register map as the return routine of the switcher, and
    [switcher_ret_specification], take it. *)
Section Register_maps.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
  .

  (** A register of a register map, with the map given back once the
      register is updated. *)
  Lemma registers_pointsto_extract (rmap : LReg) (r : RegName) (w : LWord) :
    rmap !! r = Some w →
    registers_pointsto rmap ⊢
    r ↦ᵣ[th] w ∗ (∀ w', r ↦ᵣ[th] w' -∗ registers_pointsto (<[r:=w']> rmap)).
  Proof.
    iIntros (Hr) "Hregs". rewrite /registers_pointsto.
    iDestruct (big_sepM_delete _ _ r with "Hregs") as "[$ Hregs]"; first done.
    iIntros (w') "Hr". rewrite -insert_delete_eq.
    iApply (big_sepM_insert with "[$Hregs $Hr]"). by rewrite lookup_delete_eq.
  Qed.

  (** Two registers of a register map. *)
  Lemma registers_pointsto_extract2 (rmap : LReg) (r1 r2 : RegName) (w1 w2 : LWord) :
    r1 ≠ r2 →
    rmap !! r1 = Some w1 →
    rmap !! r2 = Some w2 →
    registers_pointsto rmap ⊢
    r1 ↦ᵣ[th] w1 ∗
    r2 ↦ᵣ[th] w2 ∗
    (∀ w1' w2',
       r1 ↦ᵣ[th] w1' -∗
       r2 ↦ᵣ[th] w2' -∗
       registers_pointsto (<[r1:=w1']> (<[r2:=w2']> rmap))).
  Proof.
    iIntros (Hne Hr1 Hr2) "Hregs". rewrite /registers_pointsto.
    iDestruct (big_sepM_delete _ _ r1 with "Hregs") as "[$ Hregs]"; first done.
    iDestruct (big_sepM_delete _ _ r2 with "Hregs") as "[$ Hregs]".
    { by rewrite lookup_delete_ne. }
    iIntros (w1' w2') "Hr1 Hr2".
    rewrite big_sepM_insert_delete delete_insert_ne // big_sepM_insert_delete.
    iFrame.
  Qed.

  (** Three registers of a register map. *)
  Lemma registers_pointsto_extract3 (rmap : LReg) (r1 r2 r3 : RegName) (w1 w2 w3 : LWord) :
    r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 →
    rmap !! r1 = Some w1 →
    rmap !! r2 = Some w2 →
    rmap !! r3 = Some w3 →
    registers_pointsto rmap ⊢
    r1 ↦ᵣ[th] w1 ∗
    r2 ↦ᵣ[th] w2 ∗
    r3 ↦ᵣ[th] w3 ∗
    (∀ w1' w2' w3',
       r1 ↦ᵣ[th] w1' -∗
       r2 ↦ᵣ[th] w2' -∗
       r3 ↦ᵣ[th] w3' -∗
       registers_pointsto (<[r1:=w1']> (<[r2:=w2']> (<[r3:=w3']> rmap)))).
  Proof.
    iIntros (Hne12 Hne13 Hne23 Hr1 Hr2 Hr3) "Hregs". rewrite /registers_pointsto.
    iDestruct (big_sepM_delete _ _ r1 with "Hregs") as "[$ Hregs]"; first done.
    iDestruct (big_sepM_delete _ _ r2 with "Hregs") as "[$ Hregs]".
    { by rewrite lookup_delete_ne. }
    iDestruct (big_sepM_delete _ _ r3 with "Hregs") as "[$ Hregs]".
    { by rewrite !lookup_delete_ne. }
    iIntros (w1' w2' w3') "Hr1 Hr2 Hr3".
    rewrite big_sepM_insert_delete !delete_insert_ne // big_sepM_insert_delete.
    rewrite delete_insert_ne // big_sepM_insert_delete.
    iFrame.
  Qed.

  (** The registers of a full register map, as the return routine of the
      switcher takes them. *)
  Lemma registers_pointsto_switcher_return (rmap : LReg) :
    (∀ r, is_Some (rmap !! r)) →
    registers_pointsto rmap ⊢
    ∃ rmap_ret : LReg,
      ⌜dom rmap_ret = all_registers_s ∖ {[ csp ; cgp ; cra ; cs0 ; cs1 ; ca0 ; ca1 ]}⌝ ∗
      cgp ↦ᵣ[th] - ∗
      cra ↦ᵣ[th] - ∗
      cs0 ↦ᵣ[th] - ∗
      cs1 ↦ᵣ[th] - ∗
      csp ↦ᵣ[th] (rmap !!! csp) ∗
      ca0 ↦ᵣ[th] (rmap !!! ca0) ∗
      ca1 ↦ᵣ[th] (rmap !!! ca1) ∗
      regs[th] rmap_ret.
  Proof.
    iIntros (Hfull) "Hregs". rewrite /registers_pointsto.
    pose proof (lregmap_full_dom _ Hfull) as Hdom.
    iExists (delete ca1 (delete ca0 (delete cs1 (delete cs0 (delete cra
               (delete cgp (delete csp rmap))))))).
    iSplit.
    { iPureIntro. rewrite !dom_delete_L Hdom. set_solver+. }
    iDestruct (big_sepM_delete _ _ csp with "Hregs") as "[Hcsp Hregs]".
    { apply lookup_lookup_total, Hfull. }
    iDestruct (big_sepM_delete _ _ cgp with "Hregs") as "[Hcgp Hregs]".
    { rewrite lookup_delete_ne //. apply lookup_lookup_total, Hfull. }
    iDestruct (big_sepM_delete _ _ cra with "Hregs") as "[Hcra Hregs]".
    { rewrite !lookup_delete_ne //. apply lookup_lookup_total, Hfull. }
    iDestruct (big_sepM_delete _ _ cs0 with "Hregs") as "[Hcs0 Hregs]".
    { rewrite !lookup_delete_ne //. apply lookup_lookup_total, Hfull. }
    iDestruct (big_sepM_delete _ _ cs1 with "Hregs") as "[Hcs1 Hregs]".
    { rewrite !lookup_delete_ne //. apply lookup_lookup_total, Hfull. }
    iDestruct (big_sepM_delete _ _ ca0 with "Hregs") as "[Hca0 Hregs]".
    { rewrite !lookup_delete_ne //. apply lookup_lookup_total, Hfull. }
    iDestruct (big_sepM_delete _ _ ca1 with "Hregs") as "[Hca1 Hregs]".
    { rewrite !lookup_delete_ne //. apply lookup_lookup_total, Hfull. }
    iFrame.
  Qed.

  (** The registers of a full register map, as [switcher_ret_specification]
      takes them. *)
  Lemma registers_pointsto_ret_spec (rmap : LReg) :
    (∀ r, is_Some (rmap !! r)) →
    registers_pointsto rmap ⊢
    ∃ rest : LReg,
      ⌜dom rest = all_registers_s ∖ {[ csp ; ca0 ; ca1 ]}⌝ ∗
      csp ↦ᵣ[th] (rmap !!! csp) ∗
      ca0 ↦ᵣ[th] (rmap !!! ca0) ∗
      ca1 ↦ᵣ[th] (rmap !!! ca1) ∗
      regs[th] rest.
  Proof.
    iIntros (Hfull) "Hregs". rewrite /registers_pointsto.
    pose proof (lregmap_full_dom _ Hfull) as Hdom.
    iExists (delete ca1 (delete ca0 (delete csp rmap))).
    iSplit.
    { iPureIntro. rewrite !dom_delete_L Hdom. set_solver+. }
    iDestruct (big_sepM_delete _ _ csp with "Hregs") as "[Hcsp Hregs]".
    { apply lookup_lookup_total, Hfull. }
    iDestruct (big_sepM_delete _ _ ca0 with "Hregs") as "[Hca0 Hregs]".
    { rewrite lookup_delete_ne //. apply lookup_lookup_total, Hfull. }
    iDestruct (big_sepM_delete _ _ ca1 with "Hregs") as "[Hca1 Hregs]".
    { rewrite !lookup_delete_ne //. apply lookup_lookup_total, Hfull. }
    iFrame.
  Qed.

End Register_maps.

(** An address within bounds of a region disjoint from the MMIO (resp. heap)
    region is not a shadow (resp. heap) address. *)
Ltac solve_not_shadow H :=
  eapply disjoint_from_shadow_not_in;
  [exact (disjoint_from_mmio_shadow _ _ H) | rewrite /withinBounds; solve_addr].

Ltac solve_not_heap H :=
  eapply disjoint_from_heap_not_in; [exact H | rewrite /withinBounds; solve_addr].

(** ** Revoked keys that hold their cells *)
Section Revoked_Cells.
  Context
    {Σ : gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg : sealStoreG Σ}
    {stsg : STSG Σ}
    {relg : relGS Σ}
    `{MP : MachineParameters}.

  (** Revoked keys whose resources hold their cells: no tombstone among
      them. *)
  Definition RevokedCells (W : WORLD) (C : CmptName) (s : list LAddr) : iProp Σ :=
    [∗ list] a ∈ s,
      ∃ pa Φa,
        ⌜∀ WCv, Persistent (Φa WCv)⌝ ∗
        a ↪ˡ[C]{pa} Φa ∗
        ∃ wa, ⌜isO pa = false⌝ ∗ a ↦ₖ wa ∗ future_pub_mono C Φa wa ∗ ▷ Φa (W, C, wa).

  Lemma RevokedCells_RevokedResources (W : WORLD) (C : CmptName) (s : list LAddr) :
    RevokedCells W C s -∗ RevokedResources W C s.
  Proof.
    iIntros "H". iApply (big_sepL_impl with "H").
    iIntros "!>" (i a _) "(%pa & %Φa & %Hpers & Hrel & Hres)".
    iExists pa, Φa. iFrame "Hrel". iSplit; first done.
    iApply heap_key_resource_intro. rewrite /temp_body. by iFrame.
  Qed.
End Revoked_Cells.
