From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode proofmode_binary register_tactics_binary.
From griotte Require Import memory_region memory_region_binary.
From griotte Require Import logrel_binary clear_registers_spec_binary.
From griotte Require Export code_blocks.

(** * Shared helpers of the binary case-study specifications

    - [code_blocks] (re-exported): offsets of the blocks of the code of a
      compartment, and the tactics to focus on its blocks,
    - [focus_block_lockstep n hs h of blocks at pc_a]: focus on block [n] of
      the code in both runs,
    - [iSpecRegionSplit]: the counterpart of [iRegionSplit] for the
      specification run,
    - [region_pointsto_reassemble], [spec_region_pointsto_reassemble]:
      merge a region from its part below an address, the cell at this
      address, and its part above,
    - [iInsertRegsSpec]: the counterpart of [iInsertRegs] for the
      specification run,
    - [switcher_call_args_0_binary], [switcher_call_args_1_binary]: the
      argument registers of a call to the switcher, for an entry point
      with no argument (resp. one argument). *)

(** ** Code blocks in both runs *)

(** Focus on block [n] of the code [concat blocks] (at address [pc_a]), in
    both runs, whose first address [a] is
    [pc_a + code_block_offset blocks n]. The PC of both runs is moved to
    [a], when possible. *)
Tactic Notation "focus_block_lockstep" constr(n) constr(hs) constr(h)
    "of" constr(blocks) "at" constr(pc_a)
    "as" ident(a) ident(Ha) constr(hsi) constr(hscont) constr(hi) constr(hcont) :=
  focus_block_nochangePC_lockstep n hs h as a Ha hsi hscont hi hcont;
  let Ha' := fresh in
  assert ((pc_a + code_block_offset blocks n)%a = Some a) as Ha'
      by (cbn in Ha; offsets_compute; solve_addr);
  clear Ha; rename Ha' into Ha;
  try change_pc_to a.

(** ** Memory regions of the specification run *)

Section spec_region_cells.
  Context `{specg : specG Σ} `{MP: MachineParameters}.

  (** The cells of a region of the specification run, see [region_cells]. *)
  Fixpoint spec_region_cells_from (b : Addr) (i : nat) (w : Word) (ws : list Word) : iProp Σ :=
    match ws with
    | [] => cell_addr b i ↣ₐ w
    | w' :: ws' => cell_addr b i ↣ₐ w ∗ spec_region_cells_from b (S i) w' ws'
    end.

  Definition spec_region_cells (b : Addr) (ws : list Word) : iProp Σ :=
    match ws with [] => emp | w :: ws' => spec_region_cells_from b 0 w ws' end.

  Lemma spec_region_cells_from_big_sepL b i w ws :
    spec_region_cells_from b i w ws ⊣⊢ [∗ list] k ↦ y ∈ w :: ws, (b ^+ (i + k)%nat)%a ↣ₐ y.
  Proof.
    revert i w. induction ws as [|w' ws IH]; intros i w; cbn [spec_region_cells_from].
    - by rewrite big_sepL_singleton Nat.add_0_r cell_addr_eq.
    - rewrite big_sepL_cons IH Nat.add_0_r cell_addr_eq.
      f_equiv. apply big_sepL_proper. intros k y _. by rewrite Nat.add_succ_r.
  Qed.

  Lemma spec_region_pointsto_cells (b e : Addr) (ws : list Word) :
    (b + length ws)%a = Some e →
    [[ b , e ]] ↣ₐ [[ ws ]] ⊣⊢ [∗ list] i ↦ w ∈ ws, (b ^+ i)%a ↣ₐ w.
  Proof.
    revert b. induction ws as [|w ws IH]; intros b Hb; cbn in Hb |- *.
    - rewrite /spec_region_pointsto finz_seq_between_empty; [done|solve_addr].
    - rewrite (spec_region_pointsto_cons b (b ^+ 1)%a); [|solve_addr|solve_addr].
      rewrite IH; [|solve_addr].
      rewrite (_ : (b ^+ 0%nat)%a = b); [|solve_addr].
      f_equiv. apply big_sepL_proper. intros k y Hk%lookup_lt_Some.
      rewrite (_ : ((b ^+ 1) ^+ k)%a = (b ^+ S k)%a); [done|solve_addr].
  Qed.

  Lemma spec_region_pointsto_region_cells (b e : Addr) (ws : list Word) :
    (b + length ws)%a = Some e →
    [[ b , e ]] ↣ₐ [[ ws ]] ⊣⊢ spec_region_cells b ws.
  Proof.
    intros. rewrite spec_region_pointsto_cells //.
    destruct ws as [|w ws]; first done.
    by rewrite /spec_region_cells spec_region_cells_from_big_sepL.
  Qed.

End spec_region_cells.

(** ** Merging a region around one address, in both runs *)

Section Region_reassemble.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {specg : specG Σ} `{MP: MachineParameters}.

  Lemma region_pointsto_reassemble (b a e : Addr) (lo hi : list Word) (w : Word) :
    (b <= a)%a →
    (a ^+ 1 <= e)%a →
    (a + 1)%a = Some (a ^+ 1)%a →
    length lo = finz.dist b a →
    [[ b, a ]] ↦ₐ [[ lo ]] -∗
    a ↦ₐ w -∗
    [[ (a ^+ 1)%a, e ]] ↦ₐ [[ hi ]] -∗
    [[ b, e ]] ↦ₐ [[ lo ++ w :: hi ]].
  Proof.
    iIntros (Hba Hae Ha Hlen) "Hlo Hw Hhi".
    rewrite (region_pointsto_split b e a lo (w :: hi)); [|solve_addr|done].
    rewrite (region_pointsto_cons a (a ^+ 1)%a e); [|done|done].
    iFrame.
  Qed.

  Lemma spec_region_pointsto_reassemble (b a e : Addr) (lo hi : list Word) (w : Word) :
    (b <= a)%a →
    (a ^+ 1 <= e)%a →
    (a + 1)%a = Some (a ^+ 1)%a →
    length lo = finz.dist b a →
    [[ b, a ]] ↣ₐ [[ lo ]] -∗
    a ↣ₐ w -∗
    [[ (a ^+ 1)%a, e ]] ↣ₐ [[ hi ]] -∗
    [[ b, e ]] ↣ₐ [[ lo ++ w :: hi ]].
  Proof.
    iIntros (Hba Hae Ha Hlen) "Hlo Hw Hhi".
    rewrite (spec_region_pointsto_split b e a lo (w :: hi)); [|solve_addr|done].
    rewrite (spec_region_pointsto_cons a (a ^+ 1)%a e); [|done|done].
    iFrame.
  Qed.

End Region_reassemble.

(** Split [h : [[b, e]] ↣ₐ [[ws]]], for a concrete list [ws], into
    [b ↣ₐ w0 ∗ (b ^+ 1) ↣ₐ w1 ∗ ... ∗ (b ^+ n) ↣ₐ wn], destructed with
    [pat], as [iRegionSplit] does in the implementation run. *)
Tactic Notation "iSpecRegionSplit" constr(h) "as" constr(pat) :=
  lazymatch goal with |- environments.envs_entails ?Δ _ =>
  lazymatch reduction.pm_eval (environments.envs_lookup h Δ) with
  | Some (_, spec_region_pointsto ?b ?e ?ws) =>
      let ws := list_spine ws in
      let x := iFresh in
      iDestruct (spec_region_pointsto_region_cells b e ws with h) as x;
      [first [done | solve_addr]
      | iEval (cbn [spec_region_cells spec_region_cells_from cell_addr];
               cbv [Z.of_nat Pos.of_succ_nat Pos.succ]) in x;
        iDestruct x as pat]
  | _ => fail "iSpecRegionSplit:" h "is not of the form [[_, _]] ↣ₐ [[_]]"
  end end.

(** ** Register maps of the specification run *)

(** Insert the spec register points-to of the hypotheses [Hregs] into the
    spec register map [Hmap], see [iInsertRegs]. *)
Ltac iInsertRegsSpec0 Hmap Hregs :=
  lazymatch Hregs with
  | nil => idtac
  | ?Hreg :: ?Htail =>
      let pat := constr:((Hreg ++ " " ++ Hmap)%string) in
      iDestruct (big_sepM_insert_2 (λ r w, r ↣ᵣ w)%I with pat) as Hmap;
      iInsertRegsSpec0 Hmap Htail
  end.

Tactic Notation "iInsertRegsSpec" constr(Hmap) constr(Hregs) :=
    iInsertRegsSpec0 Hmap Hregs.

(** ** Arguments of a call to the switcher

    [switcher_call_args_0_binary] (resp. [switcher_call_args_1_binary])
    builds the argument registers
    [arg_rmap] and [arg_smap] of both runs, and the other registers [rmap']
    and [smap'], expected by the specification of the switcher call, for an
    entry point with no argument (resp. one argument, passed in [ca0]). The
    argument must be safe to share; the other argument registers are passed
    unchanged. *)
Section Switcher_call_args.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Lemma switcher_call_args_0_binary W C (rmap smap : Reg) :
    dom rmap = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ->
    dom smap = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ->
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) -∗
    ([∗ map] r↦w ∈ smap, r ↣ᵣ w) -∗
    ∃ arg_rmap arg_smap rmap' smap',
      ⌜ dom rmap' = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ⌝ ∗
      ⌜ dom smap' = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ⌝ ∗
      ⌜ is_arg_rmap arg_rmap 8 ⌝ ∗
      ⌜ is_arg_rmap arg_smap 8 ⌝ ∗
      ([∗ map] rarg↦warg;sarg ∈ arg_rmap;arg_smap,
         rarg ↦ᵣ warg ∗
         rarg ↣ᵣ sarg ∗
         (if decide (rarg ∈ dom_arg_rmap 0)
          then interp W C (warg, sarg)
          else True)) ∗
      ([∗ map] r↦w ∈ rmap', r ↦ᵣ w) ∗
      ([∗ map] r↦w ∈ smap', r ↣ᵣ w).
  Proof.
    iIntros (Hrmap_dom Hsmap_dom) "Hrmap Hsmap".
    iExtractList "Hrmap" [ca0;ca1;ca2;ca3;ca4;ca5;ct0]
      as ["Hca0"; "Hca1"; "Hca2"; "Hca3"; "Hca4"; "Hca5"; "Hct0"].
    iExtractList "Hsmap" [ca0;ca1;ca2;ca3;ca4;ca5;ct0]
      as ["Hsca0"; "Hsca1"; "Hsca2"; "Hsca3"; "Hsca4"; "Hsca5"; "Hsct0"].
    iExists {[ ca0 := wca0; ca1 := wca1; ca2 := wca2; ca3 := wca3;
               ca4 := wca4; ca5 := wca5; ct0 := wct0 ]},
      {[ ca0 := wca6; ca1 := wca7; ca2 := wca8; ca3 := wca9;
         ca4 := wca10; ca5 := wca11; ct0 := wct1 ]}, _, _.
    iFrame "Hrmap Hsmap".
    iSplit.
    { iPureIntro. rewrite !dom_delete_L Hrmap_dom /dom_arg_rmap. set_solver+. }
    iSplit.
    { iPureIntro. rewrite !dom_delete_L Hsmap_dom /dom_arg_rmap. set_solver+. }
    iSplit; first by rewrite /is_arg_rmap /dom_arg_rmap /=; iPureIntro; set_solver+.
    iSplit; first by rewrite /is_arg_rmap /dom_arg_rmap /=; iPureIntro; set_solver+.
    repeat (rewrite big_sepM2_insert; [|by simplify_map_eq|by simplify_map_eq]).
    rewrite big_sepM2_empty.
    rewrite /dom_arg_rmap /=.
    iFrame.
  Qed.

  Lemma switcher_call_args_1_binary W C (rmap smap : Reg) (wca0 swca0 : Word) :
    dom rmap = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ca0 ]} ->
    dom smap = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ca0 ]} ->
    ca0 ↦ᵣ wca0 -∗
    ca0 ↣ᵣ swca0 -∗
    interp W C (wca0, swca0) -∗
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) -∗
    ([∗ map] r↦w ∈ smap, r ↣ᵣ w) -∗
    ∃ arg_rmap arg_smap rmap' smap',
      ⌜ dom rmap' = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ⌝ ∗
      ⌜ dom smap' = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ⌝ ∗
      ⌜ is_arg_rmap arg_rmap 8 ⌝ ∗
      ⌜ is_arg_rmap arg_smap 8 ⌝ ∗
      ([∗ map] rarg↦warg;sarg ∈ arg_rmap;arg_smap,
         rarg ↦ᵣ warg ∗
         rarg ↣ᵣ sarg ∗
         (if decide (rarg ∈ dom_arg_rmap 1)
          then interp W C (warg, sarg)
          else True)) ∗
      ([∗ map] r↦w ∈ rmap', r ↦ᵣ w) ∗
      ([∗ map] r↦w ∈ smap', r ↣ᵣ w).
  Proof.
    iIntros (Hrmap_dom Hsmap_dom) "Hca0 Hsca0 #Hinterp_ca0 Hrmap Hsmap".
    iExtractList "Hrmap" [ca1;ca2;ca3;ca4;ca5;ct0]
      as ["Hca1"; "Hca2"; "Hca3"; "Hca4"; "Hca5"; "Hct0"].
    iExtractList "Hsmap" [ca1;ca2;ca3;ca4;ca5;ct0]
      as ["Hsca1"; "Hsca2"; "Hsca3"; "Hsca4"; "Hsca5"; "Hsct0"].
    iExists {[ ca0 := wca0; ca1 := wca1; ca2 := wca2; ca3 := wca3;
               ca4 := wca4; ca5 := wca5; ct0 := wct0 ]},
      {[ ca0 := swca0; ca1 := wca6; ca2 := wca7; ca3 := wca8;
         ca4 := wca9; ca5 := wca10; ct0 := wct1 ]}, _, _.
    iFrame "Hrmap Hsmap".
    iSplit.
    { iPureIntro. rewrite !dom_delete_L Hrmap_dom /dom_arg_rmap. set_solver+. }
    iSplit.
    { iPureIntro. rewrite !dom_delete_L Hsmap_dom /dom_arg_rmap. set_solver+. }
    iSplit; first by rewrite /is_arg_rmap /dom_arg_rmap /=; iPureIntro; set_solver+.
    iSplit; first by rewrite /is_arg_rmap /dom_arg_rmap /=; iPureIntro; set_solver+.
    repeat (rewrite big_sepM2_insert; [|by simplify_map_eq|by simplify_map_eq]).
    rewrite big_sepM2_empty.
    rewrite /dom_arg_rmap /=.
    iFrame "∗#".
  Qed.

End Switcher_call_args.
