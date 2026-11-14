From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Export stack_cells clear_stack.

Section csrw_zeroed.
  Context {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {th : Thread} {CL : CritLink Σ th}
    `{MP: MachineParameters}.

  (** [csrw mshwm, src] with [src] at [a], after the zeroing of [z, a)
      from the logical MSHWM [v]: [z] is [v], or [a] when [v] is at or above
      it. The zeroed cells that the new value covers join the zone. *)
  Lemma wp_csrw_mshwm_zeroed E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src vsrc
      (mshwmb_v v : Z) (z a : Addr) dq :
    decodeInstrW w.(lw) = SpecialRW cnull mshwm (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    get_a vsrc.(lw) = a →
    (z <= a)%a →
    (v = z ∨ (z = a ∧ a <= v))%Z →
    (0 <= mshwmb_v)%Z →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ vsrc ∗
        ▷ hwm_regs mshwmb_v v ∗
        [[ z , a ]] ↦ₐ [[ 0…0 ]] }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        src ↦ᵣ vsrc ∗
        hwm_regs mshwmb_v a ∗
        stack_region z a (region_addrs_zeroes z a) }}}.
  Proof.
    iIntros (Hdecode Hvpc Hsr Hpca' Hsrc Hx Hza Hzv Hb0 φ)
      "(HPC & Hi & Hsrc & Hhwm & Hzero) Hφ".
    destruct (decide (Z.max mshwmb_v v <= a)%Z) as [Hlo | Hlo].
    - destruct (finz_of_z_spec MemNum (Z.max mshwmb_v v))
        as [ (lo & _ & Hlo_eq) | [_ Hlo_none] ]; last (exfalso; solve_addr).
      iMod (region_zeroes_zone_from _ z lo a with "Hzero") as "[Hzero Hcells]";
        [solve_addr | solve_addr |].
      (* The raise frames the cells at given values: here all 0. *)
      iAssert ([∗ list] a'; z' ∈ finz.seq_between lo a;
                 replicate (length (finz.seq_between lo a)) 0%Z, zone_cell_v a' z')%I
        with "[Hcells]" as "Hcells".
      { by rewrite big_sepL2_replicate_r. }
      iApply (wp_csrw_mshwm_gen _ _ _ _ _ _ _ _ _ _ _ _ _ lo a
               with "[$HPC $Hi $Hsrc $Hhwm $Hcells]"); try done.
      iIntros "!> (HPC & Hi & Hsrc & Hhwm & Hcells)".
      iEval (rewrite big_sepL2_replicate_r //) in "Hcells".
      iApply "Hφ". iFrame.
      iApply (stack_region_zeroes_join with "[$Hzero $Hcells]"); solve_addr.
    - iDestruct "Hhwm" as "[Hb Hh]".
      iDestruct (stack_region_of_pointsto with "Hzero") as "Hzero".
      destruct (decide (a < mshwmb_v)%Z) as [Hbelow | Hge].
      + iApply (wp_csrw_mshwm_below with "[$HPC $Hi $Hsrc $Hb $Hh]"); try done; first lia.
        iIntros "!> (HPC & Hi & Hsrc & Hb & Hh)".
        iApply "Hφ". rewrite Hx. iFrame.
      + iApply (wp_csrw_mshwm with "[$HPC $Hi $Hsrc $Hb $Hh]"); try done; first (cbn; lia).
        iIntros "!> (HPC & Hi & Hsrc & Hb & Hh)".
        iApply "Hφ". rewrite Hx. iFrame.
  Qed.

End csrw_zeroed.

Section hwm_after_base.
  (** A store at [x] keeps the logical MSHWM at or above MSHWMB [mshwmb_v]. *)
  Lemma hwm_after_base (x mshwmb_v : Addr) (mshwm_v mshwm_v' : Z) :
    (mshwmb_v <= mshwm_v)%Z →
    mshwm_v' = mshwm_v ∨ mshwm_v' = hwm_after x mshwmb_v mshwm_v →
    (mshwmb_v <= mshwm_v')%Z.
  Proof.
    intros Hb [-> | ->]; first done.
    destruct (hwm_after_cases x mshwmb_v mshwm_v) as [-> | [-> Hxh] ]; first done.
    solve_addr.
  Qed.

End hwm_after_base.

Section stack_region_below_hwm.
  Context {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {th : Thread} {CL : CritLink Σ th}
    `{MP: MachineParameters}.

  (** Everything is zeroed from an address below the cells. *)
  Lemma stack_zeroed_from_below (b : Addr) (v : Z) (ws : list LWord) :
    (v <= b)%Z →
    stack_zeroed_from b v ws = replicate (length ws) (lword_of_word (WInt 0)).
  Proof.
    intros Hv. rewrite /stack_zeroed_from Z2Nat.nonpos; last lia.
    by rewrite take_0 Nat.sub_0_r.
  Qed.

  (** The cells of a stack region above MSHWMB and below MSHWM are cells of
      the zone, which hold integers. *)
  Lemma wp_stack_region_below_hwm E e Φ (b er : Addr) (ws : list LWord) (mshwmb_v mshwm_v : Z) :
    to_val e = None →
    (mshwmb_v <= b)%Z →
    hwm_closed (kind_of th) -∗
    stack_region b er ws -∗
    hwm_regs mshwmb_v mshwm_v -∗
    (⌜Forall lword_int (take (Z.to_nat (mshwm_v - b)) ws)⌝ -∗
     hwm_closed (kind_of th) -∗
     stack_region b er ws -∗
     hwm_regs mshwmb_v mshwm_v -∗
     WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros (He).
    iInduction ws as [|w ws] "IH" forall (b); iIntros (Hhb) "Hcl Hstk Hhwm HΦ".
    { iApply ("HΦ" with "[%] Hcl Hstk Hhwm"). rewrite take_nil. apply Forall_nil_2. }
    destruct (decide (mshwm_v <= b)%Z) as [Hh | Hh].
    { iApply ("HΦ" with "[%] Hcl Hstk Hhwm").
      rewrite Z2Nat.nonpos; last lia.
      rewrite take_0. apply Forall_nil_2. }
    iDestruct (stack_region_length with "Hstk") as %Hlen.
    rewrite finz_seq_between_length /= in Hlen.
    assert (b < er)%a as Hber by (rewrite /finz.dist in Hlen; solve_addr).
    destruct (b + 1)%a as [b'|] eqn:Hb'; last solve_addr.
    iDestruct (stack_region_cons b b' er with "Hstk")
      as "[ [Hb | (%zb & Hb & ->) ] Hstk]"; [done|done|..].
    - (* A full points-to is outside the zone *)
      iDestruct "Hhwm" as "[Hhb Hh]".
      iApply (wp_hwm_pointsto_outside with "Hcl Hb Hhb Hh"); first done.
      iIntros (Hout). exfalso; lia.
    - iApply ("IH" $! b' with "[%] Hcl Hstk Hhwm"); first solve_addr.
      iIntros (Hz) "Hcl Hstk Hhwm".
      iApply ("HΦ" with "[%] Hcl [Hb Hstk] Hhwm").
      + rewrite (_ : Z.to_nat (mshwm_v - b) = S (Z.to_nat (mshwm_v - b'))); last solve_addr.
        cbn. apply Forall_cons; split; [by exists zb | done].
      + iApply (stack_region_cons b b' er); [done|done|]. iFrame.
        by iApply stack_cell_of_zone.
  Qed.

  (** Zeroing twice from the same address is zeroing once. *)
  Lemma stack_zeroed_from_idemp (b : Addr) (v : Z) (ws : list LWord) :
    stack_zeroed_from b v (stack_zeroed_from b v ws) = stack_zeroed_from b v ws.
  Proof.
    rewrite /stack_zeroed_from length_app length_take length_replicate.
    destruct (decide (Z.to_nat (v - b) <= length ws)%nat) as [Hle | Hgt].
    - rewrite take_app_le; last (rewrite length_take; lia).
      rewrite take_take Nat.min_id.
      f_equal. f_equal. lia.
    - rewrite take_ge; last (rewrite length_app length_take length_replicate; lia).
      rewrite (_ : Nat.min (Z.to_nat (v - b)) (length ws) + (length ws - Z.to_nat (v - b))
                   - Z.to_nat (v - b) = 0)%nat; last lia.
      by rewrite app_nil_r.
  Qed.

  (** Words zeroed from [v] are integers when those below [v] are. *)
  Lemma stack_zeroed_from_ints (b : Addr) (v : Z) (ws : list LWord) :
    Forall lword_int (take (Z.to_nat (v - b)) ws) →
    Forall lword_int (stack_zeroed_from b v ws).
  Proof.
    intros Hws. rewrite /stack_zeroed_from.
    apply Forall_app; split; first done.
    apply Forall_replicate. by exists 0%Z.
  Qed.

  (** A stack region zeroed from MSHWM, above MSHWMB, holds only integers. *)
  Lemma wp_stack_region_zeroed_from_hwm E e Φ (b er : Addr) (ws : list LWord)
    (mshwmb_v mshwm_v : Z) :
    to_val e = None →
    (mshwmb_v <= b)%Z →
    hwm_closed (kind_of th) -∗
    stack_region b er (stack_zeroed_from b mshwm_v ws) -∗
    hwm_regs mshwmb_v mshwm_v -∗
    (hwm_closed (kind_of th) -∗
     stack_ints b er -∗
     hwm_regs mshwmb_v mshwm_v -∗
     WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros (He Hhb) "Hcl Hstk Hhwm HΦ".
    iApply (wp_stack_region_below_hwm with "Hcl Hstk Hhwm"); [done|done|].
    iIntros (Hz) "Hcl Hstk Hhwm".
    (* Below MSHWM, integers; above, zeros. *)
    apply stack_zeroed_from_ints in Hz.
    rewrite stack_zeroed_from_idemp in Hz.
    iApply ("HΦ" with "Hcl [Hstk] Hhwm").
    iApply (stack_ints_of_region _ _ _ Hz with "Hstk").
  Qed.

  (** The prefix of length [n] of [ws], zeroed from [v'], is the prefix of
      [ws] zeroed from [v], when [v'] is [v] or lies between the end of the
      prefix and [v]. *)
  Lemma stack_zeroed_from_take (b : Addr) (v v' : Z) (n : nat) (ws : list LWord) :
    (n <= length ws)%nat →
    (v' = v ∨ (b + Z.of_nat n <= v' <= v)%Z) →
    stack_zeroed_from b v' (take n ws) = take n (stack_zeroed_from b v ws).
  Proof.
    intros Hn Hv. rewrite /stack_zeroed_from.
    rewrite take_take length_take take_app take_take take_replicate length_take.
    destruct Hv as [-> | Hv].
    - destruct (decide (Z.to_nat (v - b) <= n)%nat).
      + rewrite (Nat.min_l (Z.to_nat (v - b)) n) // (Nat.min_r n (Z.to_nat (v - b))) //.
        f_equal; f_equal; lia.
      + rewrite (Nat.min_r (Z.to_nat (v - b)) n); [|lia].
        rewrite (Nat.min_l n (Z.to_nat (v - b))); [|lia].
        f_equal; f_equal; lia.
    - rewrite (Nat.min_r (Z.to_nat (v' - b)) n); [|lia].
      rewrite (Nat.min_l n (Z.to_nat (v - b))); [|lia].
      f_equal; f_equal; lia.
  Qed.

  (** The cells of [lo, s), inside an integer stack region, join the zone,
      and come back. *)
  Lemma stack_region_zeroes_zone_acc E (b lo s e : Addr) :
    (b <= lo)%a → ((lo <= s)%a → (s <= e)%a) →
    stack_ints b e ⊢
    |~{E}~> ([∗ list] a ∈ finz.seq_between lo s, zone_cell a) ∗
            (([∗ list] a ∈ finz.seq_between lo s, zone_cell a) -∗
             stack_ints b e).
  Proof.
    iIntros (Hblo Hse) "Hstk".
    destruct (decide (lo <= s)%a) as [Hlos | Hslo]; cycle 1.
    { rewrite finz_seq_between_empty; last solve_addr.
      iModIntro. iSplitR; first done. iIntros "_". iExact "Hstk". }
    specialize (Hse Hlos).
    iDestruct (stack_ints_split b lo e with "Hstk") as "[Hlo Hhi]"; [solve_addr|solve_addr|].
    iDestruct (stack_ints_split lo s e with "Hhi") as "[Hmid Hhi]"; [solve_addr|solve_addr|].
    iMod (stack_ints_zone with "Hmid") as "Hmid".
    iModIntro. iFrame "Hmid". iIntros "Hmid".
    iDestruct (stack_ints_of_zone with "Hmid") as "Hmid".
    rewrite (stack_ints_split b lo e); [|solve_addr|solve_addr].
    rewrite (stack_ints_split lo s e); [|solve_addr|solve_addr].
    iFrame.
  Qed.

End stack_region_below_hwm.

Section ClearStackMacro.
  Context {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {th : Thread} {CL : CritLink Σ th}
    `{MP: MachineParameters} {CR : CritRoute Σ th CL}.

  (** Zero the cells [a_lo, a_hi) of a stack through the capability in
      [rbase], whose cursor is at [a_lo], up to the address [a_hi] in [rtop].
      Each cell is a points-to or a zone cell; zone cells are at or above the
      logical MSHWM, which is unchanged. When [a_hi <= a_lo], nothing is
      stored. *)
  Lemma clear_stack_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (g : Locality) (b e a_lo a_hi : Addr)
    (rbase rtop : RegName) (ws : list LWord) (mshwmb_v mshwm_v : Z)
    φ :
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (clear_stack_instrs rbase rtop)) ->
    (b <= a_lo)%a -> (a_hi <= e)%a ->
    (mshwm_v <= a_lo)%Z ->
    disjoint_from_shadow b e →
    rbase ≠ cnull ->
    rtop ≠ cnull ->

    ( PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a
      ∗ rbase ↦ᵣ Cap RWL g b e a_lo
      ∗ rtop ↦ᵣ WInt a_hi
      ∗ hwm_regs mshwmb_v mshwm_v
      ∗ codefrag_pers pc_a (clear_stack_instrs rbase rtop)
      ∗ stack_region a_lo a_hi ws
      ∗ ▷ ( (PC ↦ₚ Cap pc_p pc_g pc_b pc_e (pc_a ^+ length (clear_stack_instrs rbase rtop))
             ∗ rbase ↦ᵣ Cap RWL g b e (if decide (a_lo < a_hi)%a then a_hi else a_lo)
             ∗ rtop ↦ᵣ WInt a_hi
             ∗ hwm_regs mshwmb_v mshwm_v
             ∗ codefrag_pers pc_a (clear_stack_instrs rbase rtop)
             ∗ ([[ a_lo , a_hi ]] ↦ₐ [[ 0…0 ]]))
        -∗ WP Exec {{ φ }})
    )
      ⊢ WP Exec {{ φ }}%I.
  Proof.
    iIntros (Hpc_exec Hbounds Hb Hhi Hhwm Hdisjoint Hrbase_cnull Hrtop_cnull)
      "(HPC & Hrbase & Hrtop & Hhwm_regs & #Hcode & Hstack & Hφ)".
    codefrag_facts "Hcode".
    destruct (decide (a_lo < a_hi)%a) as [Hlt | Hge]; cycle 1.
    { (* Jle 4 rtop rbase *)
      iInstr "Hcode".
      iApply "Hφ". iFrame "∗ #".
      rewrite /region_pointsto finz_seq_between_empty; last solve_addr+Hge.
      rewrite /region_addrs_zeroes finz_dist_0; last solve_addr+Hge.
      done. }
    (* Jle 4 rtop rbase *)
    iInstr "Hcode".
    iAssert (⌜(b <= a_lo)%a ⌝)%I as "-#Hb"; first done.
    iAssert (⌜(a_lo < a_hi)%a ⌝)%I as "-#Hlo"; first done.
    iAssert (⌜(mshwm_v <= a_lo)%Z ⌝)%I as "-#Hhwm"; first done.
    clear Hb Hlt Hhwm.
    iLöb as "IH" forall (a_lo ws).
    iDestruct "Hb" as "%Hb".
    iDestruct "Hlo" as "%Hlo".
    iDestruct "Hhwm" as "%Hhwm".
    iDestruct (big_sepL2_length with "Hstack") as "%Hlen_stk".
    rewrite finz_seq_between_cons in Hlen_stk; last solve_addr.
    destruct ws as [|wa ws]; simplify_eq.
    rewrite (stack_region_cons _ (a_lo ^+ 1)); [| solve_addr | solve_addr].
    iDestruct "Hstack" as "[Ha Hstack]".
    iPoseProof deref_res_none as "Hderef".
    (* Store rbase 0 0 *)
    iInstrApply "Hcode" wp_store_stack_cell_z_imm
      with "[$HPC $Hrbase $Ha $Hhwm_regs $Hderef]" as "(HPC & Hrbase & Ha & Hhwm_regs & _)".
    { eapply disjoint_from_shadow_not_in; first exact Hdisjoint.
      apply withinBounds_true_iff; solve_addr. }
    { apply withinBounds_true_iff; solve_addr. }
    { solve_addr. }
    (* Lea rbase rbase 1 *)
    iInstr "Hcode".
    { instantiate (1 := a_lo ^+ 1); solve_addr. }
    destruct (decide (a_lo ^+ 1 = a_hi)) as [Hend | Hne].
    - (* Jlt -2 rbase rtop *)
      iInstr "Hcode".
      rewrite Hend finz_seq_between_empty in Hlen_stk; last solve_addr.
      destruct ws; last done.
      iApply "Hφ".
      iAssert ([[ a_lo ^+ 1 , a_hi ]] ↦ₐ [[ [] ]])%I as "Hnil".
      { rewrite /region_pointsto finz_seq_between_empty; last solve_addr. done. }
      iDestruct (region_pointsto_cons with "[$Ha $Hnil]") as "Hstk"; [solve_addr|solve_addr|].
      rewrite Hend.
      iFrame "∗ #".
      rewrite /region_addrs_zeroes (finz_dist_S a_lo); last solve_addr.
      rewrite -Hend finz_dist_0; last solve_addr.
      done.
    - (* Jlt -2 rbase rtop *)
      iInstr "Hcode".
      { instantiate (1 := pc_a ^+ 1). solve_addr. }
      iApply ("IH" $! (a_lo ^+ 1) ws with
               "[$Hhwm_regs] [$Hstack] [Ha Hφ] [$HPC] [$Hrtop] [$Hrbase] [] [] []").
      { iIntros "(HPC & Hrbase & Hrtop & Hhwm_regs & _ & Hstk)".
        iApply "Hφ"; iFrame "∗ #".
        iDestruct (region_pointsto_cons with "[$Ha $Hstk]") as "Hstk"; [solve_addr|solve_addr|].
        rewrite /region_addrs_zeroes (finz_dist_S a_lo); last solve_addr.
        by cbn. }
      { iPureIntro; solve_addr. }
      { iPureIntro; solve_addr. }
      { iPureIntro; solve_addr. }
  Qed.

  (** When the cursor [a_lo] of [rbase] is below its base and below [a_hi],
      the first store faults, at [pc_a ^+ 1], and nothing is written. *)
  Lemma clear_stack_below_base_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (g : Locality) (b e a_lo a_hi : Addr)
    (rbase rtop : RegName)
    φ :
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (clear_stack_instrs rbase rtop)) ->
    (a_lo < b)%a -> (a_lo < a_hi)%a ->
    rbase ≠ cnull ->
    rtop ≠ cnull ->

    ( PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a
      ∗ rbase ↦ᵣ Cap RWL g b e a_lo
      ∗ rtop ↦ᵣ WInt a_hi
      ∗ hwm_closed (kind_of th)
      ∗ codefrag_pers pc_a (clear_stack_instrs rbase rtop)
      ∗ ( rbase ↦ᵣ Cap RWL g b e a_lo
          ∗ rtop ↦ᵣ WInt a_hi
          -∗ hwm_closed (kind_of th)
          -∗ trap_safe (Cap pc_p pc_g pc_b pc_e (pc_a ^+ 1)) ⊤ φ )
    )
      ⊢ WP Exec {{ φ }}%I.
  Proof.
    iIntros (Hpc_exec Hbounds Hlo_b Hlo_hi Hrbase_cnull Hrtop_cnull)
      "(HPC & Hrbase & Hrtop & Hclosed & #Hcode & Hfailed)".
    codefrag_facts "Hcode".
    (* Jle 4 rtop rbase *)
    iInstr "Hcode".
        (* Store rbase 0 0 *)
    iInstrApply "Hcode" wp_store_fail_z_imm with "[$HPC $Hrbase]" as "(HPC & Hrbase)".
    { instantiate (1 := a_lo). solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    iTrap with "Hfailed".
  Qed.

End ClearStackMacro.
