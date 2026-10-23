From iris.proofmode Require Import proofmode.
From griotte Require Import logrel interp_weakening memory_region rules proofmode.
From griotte Require Import map_simpl register_tactics.
From griotte Require Export switcher_preamble.

(** * Error handlers

    The obligations of a fault that the switcher handles: the force-unwind
    continuation of a fault site, the invocation of a trusted error handler
    (mirrored for upward-growing stacks), and [trap_handler_ok], what a
    trusted fault site gives the trap vector. *)

Section Switcher_error_handler.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** [unwind_cont F cstk R_unwind_stk] is the force-unwind continuation of
      a fault site: the continuation of the unwind branch of
      [switcher_exception_path_spec] (PC at the return routine, [ca0] and
      [ca1] the error values, full registers, [na_own F]). It takes back the
      call-stack fragment, at any error handler count of the topmost frame,
      and [R_unwind_stk], the part of the callee's stack that the fault site
      holds and gives back to the unwind (the [ErrorState] slot for a
      stackful handler, the whole stack for a known callee, [True] when
      nothing is lent). *)
  Definition unwind_cont (F : coPset) (cstk : CSTK) (R_unwind_stk : iProp Σ) : iProp Σ :=
    ∀ (n : Z) (rmap : LReg),
      ⌜∀ r, is_Some (rmap !! r)⌝ -∗
      ⌜rmap !! ca0 = Some (WInt ECOMPARTMENTFAIL : LWord)⌝ -∗
      ⌜rmap !! ca1 = Some (WInt 0 : LWord)⌝ -∗
      PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_return -∗
      registers_pointsto rmap -∗
      cstack_frag (cstack_set_top_count cstk n) -∗
      R_unwind_stk -∗
      na_own cerise_nais F -∗
      WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.

  Lemma unwind_cont_give (F : coPset) (cstk : CSTK) (R_unwind_stk : iProp Σ) :
    R_unwind_stk -∗ unwind_cont F cstk R_unwind_stk -∗ unwind_cont F cstk True.
  Proof.
    iIntros "HS HU" (n rmap Hfull Hca0 Hca1) "HPC Hrmap Hcstk _ Hna".
    iApply ("HU" with "[//] [//] [//] HPC Hrmap Hcstk HS Hna").
  Qed.

  Lemma unwind_cont_weaken (F : coPset) (cstk : CSTK) (R_unwind_stk R_unwind_stk' : iProp Σ) :
    (R_unwind_stk' -∗ R_unwind_stk) -∗
    unwind_cont F cstk R_unwind_stk -∗
    unwind_cont F cstk R_unwind_stk'.
  Proof.
    iIntros "HSS HU" (n rmap Hfull Hca0 Hca1) "HPC Hrmap Hcstk HS Hna".
    iApply ("HU" with "[//] [//] [//] HPC Hrmap Hcstk [HSS HS] Hna"). by iApply "HSS".
  Qed.

  (** [unwind_cont] ignores the count of the topmost frame. *)
  Lemma unwind_cont_set_top_count (F : coPset) (cstk : CSTK) (R_unwind_stk : iProp Σ) (n : Z) :
    unwind_cont F (cstack_set_top_count cstk n) R_unwind_stk ⊣⊢
    unwind_cont F cstk R_unwind_stk.
  Proof.
    rewrite /unwind_cont. iSplit; iIntros "HU" (m).
    - rewrite -(cstack_set_top_count_twice cstk n m). iApply "HU".
    - rewrite cstack_set_top_count_twice. iApply "HU".
  Qed.

  (** ** The handler invocation (mirrored for upward-growing stacks) *)

  (** The sentry the switcher gives a handler in [cra]: the link of the
      [cjalr] of [.Lhandle_error_handler_cjalr], to the next instruction,
      [.Lhandle_error_handler_return]. Its kind follows the interrupt status
      [mie] at the [cjalr], which the logic does not track. *)
  Definition handler_return_sentry (mie : InterruptStatus) : LWord :=
    WSentry (ret_kind mie) true XSRW_ Local b_switcher e_switcher
      (a_switcher_call ^+ switcher_label_offset ".Lhandle_error_handler_return")%a.

  (** The return label follows the [cjalr] (both labels exist: an undefined
      label has offset 0). *)
  Lemma handler_return_label_after_cjalr :
    switcher_label_offset ".Lhandle_error_handler_return" =
    (switcher_label_offset ".Lhandle_error_handler_cjalr" + 1)%Z.
  Proof. reflexivity. Qed.

  Lemma handler_return_sentry_pc (mie : InterruptStatus) :
    lupdatePcPerm (handler_return_sentry mie) =
    switcher_label_pc ".Lhandle_error_handler_return".
  Proof. by destruct mie. Qed.

  (** The handler's PC, as the switcher computes it from the table's PCC
      [wpcc] and the handler offset [off]: the address set to the base, then
      moved by [off]. [None] when the result is not a capability that can be
      addressed there (the [cjalr] then faults). *)
  Definition handler_entry (wpcc : LWord) (off : Z) : option LWord :=
    match wpcc with
    | MkLWord (WCap t p g b e _) π => (λ a, MkLWord (WCap t p g b e a) π) <$> (b + off)%a
    | _ => None
    end.

  (** The word that the switcher computes in [cra] from the table's PCC
      [wpcc] and the handler offset [off], for any [wpcc]: the cursor moved
      to the base, then by [off] (two [Lea]s). *)
  Definition handler_word (wpcc : LWord) (off : Z) : LWord :=
    default wpcc
      (lea_result wpcc (get_b wpcc.(lw) - get_a wpcc.(lw)) ≫= λ w, lea_result w off).

  Lemma handler_word_entry (wpcc : LWord) (off : Z) (wpc : LWord) :
    handler_entry wpcc off = Some wpc → handler_word wpcc off = wpc.
  Proof.
    destruct wpcc as [w π]. rewrite /handler_entry /handler_word /lea_result /=.
    destruct_word w; try done; cbn.
    rewrite (_ : (a + (b - a))%a = Some b); last solve_addr.
    cbn. destruct (b + off)%a; cbn; by intros [=<-].
  Qed.

  (** When the computed word is not a handler's PC, the [cjalr] faults. *)
  Lemma handler_word_none (wpcc : LWord) (off : Z) :
    handler_entry wpcc off = None →
    jalr_target_ok cra cra (handler_word wpcc off).(lw) = false.
  Proof.
    destruct wpcc as [w π]. rewrite /handler_entry /handler_word /lea_result /=.
    destruct_word w; cbn; try done.
    - rewrite (_ : (a + (b - a))%a = Some b); last solve_addr.
      cbn. by destruct (b + off)%a.
    - intros _.
      destruct (a + (b - a))%ot; cbn; destruct (_ + off)%ot; cbn;
        rewrite /jalr_target_ok /= ?andb_false_r; done.
    - intros _. destruct sb; cbn; done.
  Qed.

  (** The registers of the [ErrorState], in the order of the register save
      area (words 1 to 15; word 0 is MEPCC). *)
  Definition error_state_regs : list RegName :=
    [cra; csp; cgp; ctp; ct0; ct1; ct2; cs0; cs1; ca0; ca1; ca2; ca3; ca4; ca5].

  (** The switcher's room test for the [ErrorState] (mirrored: the
      [ErrorState_size] words above the cursor). A sealing range passes the
      test: the first store of the [ErrorState] then faults. *)
  Definition error_state_fits (wcsp : LWord) : Prop :=
    match wcsp.(lw) with
    | WCap true _ _ _ e a => (a + ErrorState_size <= e)%Z
    | WSealRange true _ _ _ e a => (a + ErrorState_size <= e)%Z
    | _ => False
    end.

  (** The room test, on the stack pointer moved past the [ErrorState]
      ([wct0]): its tag, and its cursor not past its end. *)
  Lemma error_state_fits_lea (wcsp wct0 : LWord) :
    lea_result wcsp ErrorState_size = Some wct0 →
    (get_tag wct0.(lw) = true ∧ get_a wct0.(lw) <= get_e wct0.(lw))%Z ↔
    error_state_fits wcsp.
  Proof.
    destruct wcsp as [w π]. rewrite /lea_result /error_state_fits /ErrorState_size /=.
    destruct w as [n | [t p g b e a | t p g b e a] | k t p g b e a | ot sb];
      cbn; intros [=<-]; cbn; try (split; [by intros [? _] | done]).
    - destruct (a + 16)%a as [a'|] eqn:Ha; destruct t; cbn; split;
        try (by intros [? _]); try done; [intros [_ ?] | intros ? | intros ?]; solve_addr.
    - destruct (a + 16)%ot as [a'|] eqn:Ha; destruct t; cbn; split;
        try (by intros [? _]); try done; [intros [_ ?] | intros ? | intros ?]; solve_finz.
    - destruct sb; cbn; split; [by intros [? _] | done | by intros [? _] | done].
  Qed.

  (** The tag of the moved stack pointer is stripped only if that of the
      faulting one is. *)
  Lemma tag_strippable_lea (wcsp wct0 : LWord) (z : Z) :
    lea_result wcsp z = Some wct0 →
    tag_strippable wct0 → tag_strippable wcsp.
  Proof.
    destruct wcsp as [w π]. rewrite /lea_result /tag_strippable /=.
    destruct w as [n | [t p g b e a | t p g b e a] | k t p g b e a | ot sb];
      cbn; intros [=<-]; cbn; try done.
    - destruct (a + z)%a; cbn; [|by intros [? _] ].
      by rewrite /has_authority /heap_authority_base /heap_cap_base /memory_cap_base /=.
    - destruct (a + z)%ot; cbn; [|by intros [? _] ].
      by rewrite /has_authority /heap_authority_base /heap_cap_base /memory_cap_base /=.
    - by intros [? _].
    - destruct sb; cbn; by intros [? _].
  Qed.

  (** The room test passes and the switcher's stores of the [ErrorState]
      through the faulting [csp] succeed. *)
  Definition error_state_stores_ok (wcsp : LWord) : Prop :=
    match wcsp.(lw) with
    | WCap true p _ b e a => writeAllowed p = true ∧ (b <= a)%a ∧ (a + ErrorState_size <= e)%Z
    | _ => False
    end.

  #[global] Instance error_state_stores_ok_dec wcsp : Decision (error_state_stores_ok wcsp).
  Proof. rewrite /error_state_stores_ok. repeat case_match; apply _. Defined.

  (** When the room test passes but the stores do not succeed, the first
      store of the stackful setup, through the moved stack pointer [wct0]
      at the base of the [ErrorState], faults: [wct0] is a sealing range,
      or it has no write permission, or the [ErrorState] starts below its
      base. *)
  Lemma error_state_store_fault (wcsp wct0 : LWord) :
    lea_result wcsp ErrorState_size = Some wct0 →
    error_state_fits wcsp →
    ¬ error_state_stores_ok wcsp →
    is_cap wct0.(lw) = false ∨
    ∃ (p : Perm) (g : Locality) (b e a ea : Addr),
      wct0.(lw) = WCap true p g b e a ∧
      (a + (- ErrorState_size))%a = Some ea ∧
      (writeAllowed p = false ∨ withinBounds b e ea = false).
  Proof.
    destruct wcsp as [w π].
    rewrite /lea_result /error_state_fits /error_state_stores_ok /ErrorState_size /=.
    destruct w as [n | [t p g b e a | t p g b e a] | k t p g b e a | ot sb];
      cbn; intros [=<-] Hfits Hnot; cbn; try done.
    - destruct t; last done.
      destruct (a + 16)%a as [a'|] eqn:Ha; last solve_addr.
      right. exists p, g, b, e, a', a. split_and!; [done | solve_addr |].
      destruct (writeAllowed p) eqn:Hw; [right | by left].
      rewrite /withinBounds. apply andb_false_iff.
      destruct (decide (b <= a)%a); last (left; solve_addr).
      exfalso. apply Hnot. split_and!; done.
    - left. by destruct (a + 16)%ot.
  Qed.
  (** The [ErrorState] the switcher writes for a fault at [w] with the
      registers [rfault], through a [csp] of permission [p]: the untagged
      MEPCC, then each register as stored through [p]. *)
  Definition error_state_words (p : Perm) (w : LWord) (rfault : LReg) : list LWord :=
    lclear_tag (lmepcc_of_pc w) :: ((λ r, lstore_word p (rfault !!! r)) <$> error_state_regs).

  Lemma length_error_state_words p w rfault :
    length (error_state_words p w rfault) = Z.to_nat ErrorState_size.
  Proof. reflexivity. Qed.

  (** A word whose tag is cleared is stored as is. *)
  Lemma lstore_word_clear_tag (p : Perm) (v : LWord) :
    lstore_word p (lclear_tag v) = lclear_tag v.
  Proof.
    destruct v as [w π].
    rewrite /lstore_word /lclear_tag /lift_word /store_word /=.
    destruct (canStore p (clear_tag w)); [done | by rewrite clear_tag_idempotent].
  Qed.

  (** The words the switcher copies to the [ErrorState]: the untagged
      MEPCC, then the registers as spilled. *)
  Definition error_state_src (w : LWord) (rfault : LReg) : list LWord :=
    lclear_tag (lmepcc_of_pc w) :: ((λ r, rfault !!! r) <$> error_state_regs).

  Lemma error_state_src_store (p : Perm) (w : LWord) (rfault : LReg) :
    lstore_word p <$> error_state_src w rfault = error_state_words p w rfault.
  Proof.
    rewrite /error_state_src /error_state_words fmap_cons lstore_word_clear_tag.
    by rewrite -list_fmap_compose.
  Qed.

  Lemma length_error_state_src (w : LWord) (rmap : LReg) :
    length (error_state_src w rmap) = Z.to_nat ErrorState_size.
  Proof. reflexivity. Qed.

  (** The [ErrorState] at the faulting cursor, with the words the switcher
      writes. *)
  Definition error_state_pointsto (w : LWord) (rfault : LReg) : iProp Σ :=
    match (rfault !!! csp).(lw) with
    | WCap _ p _ _ _ a =>
        [[ a , (a ^+ ErrorState_size)%a ]] ↦ₐ [[ error_state_words p w rfault ]]
    | _ => True
    end.

  (** The [ErrorState] slot at the faulting cursor, any contents. *)
  Definition error_state_area (rfault : LReg) : iProp Σ :=
    match (rfault !!! csp).(lw) with
    | WCap _ _ _ _ _ a =>
        ∃ ws, ⌜length ws = Z.to_nat ErrorState_size⌝ ∗
              [[ a , (a ^+ ErrorState_size)%a ]] ↦ₐ [[ ws ]]
    | _ => True
    end.

  (** The [ErrorState] slot while the switcher writes it: its first [i]
      words are those of [error_state_words], the others any. *)
  Definition error_state_cells (w : LWord) (rfault : LReg) (i : nat) : iProp Σ :=
    match (rfault !!! csp).(lw) with
    | WCap _ p _ _ _ a =>
        ∃ ws, ⌜length ws = (Z.to_nat ErrorState_size - i)%nat⌝ ∗
              [[ a , (a ^+ ErrorState_size)%a ]] ↦ₐ
                [[ take i (error_state_words p w rfault) ++ ws ]]
    | _ => True
    end.

  Lemma error_state_cells_0 (w : LWord) (rfault : LReg) :
    error_state_cells w rfault 0 ⊣⊢ error_state_area rfault.
  Proof.
    rewrite /error_state_cells /error_state_area.
    by destruct (rfault !!! csp) as [ [|[ | ]|? []|] π]; cbn.
  Qed.

  Lemma error_state_cells_full (w : LWord) (rfault : LReg) :
    error_state_cells w rfault (Z.to_nat ErrorState_size) ⊣⊢ error_state_pointsto w rfault.
  Proof.
    rewrite /error_state_cells /error_state_pointsto.
    destruct (rfault !!! csp) as [ [|[ | ]|? []|] π]; cbn; try done.
    rewrite Nat.sub_diag take_ge; last by rewrite length_error_state_words.
    iSplit.
    - iIntros "(%ws & %Hws & Hws)". destruct ws; last done.
      by rewrite app_nil_r.
    - iIntros "Hws". iExists []. rewrite app_nil_r. by iFrame.
  Qed.

  (** The words of the [ErrorState] are safe, for safe registers. *)
  Lemma interp_error_state_src (W : WORLD) (C : CmptName) (w : LWord) (rmap : LReg) :
    (∀ r, is_Some (rmap !! r)) →
    (∀ (r : RegName) (v : LWord), ⌜rmap !! r = Some v⌝ → interp W C v) -∗
    [∗ list] v ∈ error_state_src w rmap, interp W C v.
  Proof.
    iIntros (Hfull) "#Hregs".
    rewrite /error_state_src big_sepL_cons big_sepL_fmap.
    iSplit; first iApply interp_clear_tag.
    iApply big_sepL_intro. iIntros "!>" (k r _).
    iApply "Hregs". iPureIntro.
    destruct (Hfull r) as [v Hv]. by rewrite (lookup_total_correct _ _ _ Hv).
  Qed.

  (** Cell [i] of the [ErrorState] slot while the switcher writes it. *)
  Lemma error_state_cells_acc (w : LWord) (rmap : LReg)
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId) (i : nat) :
    rmap !!! csp = WCap true p g b e a @@? π →
    (a + ErrorState_size <= e)%Z →
    (i < Z.to_nat ErrorState_size)%nat →
    error_state_cells w rmap i -∗
    ∃ v, (a ^+ i)%a ↦ₐ v ∗
      ((a ^+ i)%a ↦ₐ lstore_word p (error_state_src w rmap !!! i) -∗
       error_state_cells w rmap (S i)).
  Proof.
    intros Hcsp He Hi.
    rewrite /error_state_cells Hcsp; cbn [lw].
    iIntros "(%ws & %Hws & Hcells)".
    destruct ws as [|v ws]; first (cbn in Hws; lia).
    set (l := take i (error_state_words p w rmap)).
    assert (length l = i) as Hl.
    { rewrite /l length_take length_error_state_words. lia. }
    assert ((a + length (l ++ v :: ws))%a = Some (a ^+ ErrorState_size)%a) as Hend.
    { rewrite length_app Hl. cbn in Hws |- *. rewrite /ErrorState_size in He Hws Hi |- *.
      solve_addr. }
    rewrite region_pointsto_cells //.
    iDestruct (big_sepL_insert_acc _ _ i v with "Hcells") as "[Hv Hclose]".
    { by rewrite lookup_app_r Hl ?Nat.sub_diag. }
    iExists v. iFrame "Hv". iIntros "Hv".
    iExists ws. iSplit; first (iPureIntro; cbn in Hws; lia).
    destruct (lookup_lt_is_Some_2 (error_state_src w rmap) i) as [x Hx].
    { by rewrite length_error_state_src. }
    rewrite (list_lookup_total_correct _ _ _ Hx).
    assert (<[i := lstore_word p x]> (l ++ v :: ws) =
            take (S i) (error_state_words p w rmap) ++ ws) as Heq.
    { rewrite insert_app_r_alt; last lia.
      rewrite Hl Nat.sub_diag (take_S_r _ _ (lstore_word p x)); first by rewrite -app_assoc.
      by rewrite -error_state_src_store list_lookup_fmap Hx. }
    rewrite -Heq region_pointsto_cells; last by rewrite length_insert.
    by iApply "Hclose".
  Qed.

  Lemma error_state_pointsto_area (w : LWord) (rmap : LReg) :
    error_state_pointsto w rmap -∗ error_state_area rmap.
  Proof.
    rewrite -error_state_cells_full -(error_state_cells_0 w) /error_state_cells.
    destruct (rmap !!! csp) as [ [|[ | ]|? []|] π]; cbn; iIntros "Hws"; try done.
    iDestruct "Hws" as (ws Hws) "Hws". iExists _. iFrame "Hws". iPureIntro.
    rewrite length_app length_take length_error_state_words Hws. lia.
  Qed.

  (** The [ErrorState] slot does not overlap the shadow table. *)
  Definition error_state_shadow_free (wcsp : LWord) : Prop :=
    match wcsp.(lw) with
    | WCap _ _ _ _ _ a => disjoint_from_shadow a (a ^+ ErrorState_size)%a
    | _ => True
    end.

  (** What a fault site with a trusted handler lends: the slot, when the
      table declares a stackful handler (offset [eh]) and the switcher's
      stores succeed. The site also guarantees that the switcher's stores
      need no liveness resource (its [csp] has no identifier) and that the
      slot is outside the shadow table. *)
  Definition error_state_slot (eh : Z) (rfault : LReg) : iProp Σ :=
    if decide (eh ≠ ExportTable_no_handler ∧ error_state_stores_ok (rfault !!! csp))
    then (⌜(rfault !!! csp).(lprov) = None⌝ ∗
          ⌜error_state_shadow_free (rfault !!! csp)⌝ ∗
          error_state_area rfault)%I
    else True%I.

  (** The stackless handler's stack: the invocation's slice of the topmost
      pushed frame's [csp], cursor at its end (mirror of CHERIoT's cursor at
      the base), or the entry frame's [csp] as is. *)
  Definition stackless_csp (cstk : CSTK) : LWord :=
    match cstk.(cstk_frames) with
    | frm :: _ =>
        match frm.(cf_tframe).(tf_csp) with
        | MkLWord (WCap t p g _ e a) π => MkLWord (WCap t p g a e e) π
        | wcsp => wcsp
        end
    | [] => cstk.(cstk_entry).(tf_csp)
    end.

  (** The stackful handler's [csp] and [a0], from the faulting [csp]: the
      cursor above the [ErrorState], and the [ErrorState] capability. *)
  Definition stackful_regs (wcsp : LWord) : option (LWord * LWord) :=
    match wcsp with
    | MkLWord (WCap t p g b e a) π =>
        (λ a16, (MkLWord (WCap t p g b e a16) π, MkLWord (WCap t p g b e a) π)) <$>
          (a + ErrorState_size)%a
    | _ => None
    end.

  (** The stackful handler's [csp] and [a0], when the stores of the
      [ErrorState] succeed: the stack pointer moved past the [ErrorState],
      and the faulting one. *)
  Lemma stackful_regs_lea (wcsp wct0 : LWord) :
    lea_result wcsp ErrorState_size = Some wct0 →
    error_state_stores_ok wcsp →
    stackful_regs wcsp = Some (wct0, wcsp).
  Proof.
    destruct wcsp as [w π]. rewrite /lea_result /error_state_stores_ok /stackful_regs /=.
    destruct w as [n | [t p g b e a | t p g b e a] | k t p g b e a | ot sb]; cbn; try done.
    intros [=<-] Hok. destruct t; last done.
    destruct Hok as (_ & _ & Hend).
    rewrite /ErrorState_size in Hend |- *.
    destruct (a + 16)%a as [a'|] eqn:Ha; last solve_addr.
    done.
  Qed.

  (** The stackful handler's [csp] and [a0] are safe when the faulting
      [csp] is: [interp] does not read the cursor of a capability. *)
  Lemma interp_stackful_regs (W : WORLD) (C : CmptName) (wcsp wcsp' wa0 : LWord) :
    stackful_regs wcsp = Some (wcsp', wa0) →
    interp W C wcsp -∗ interp W C wcsp' ∗ interp W C wa0.
  Proof.
    destruct wcsp as [w π]. rewrite /stackful_regs.
    destruct w as [n | [t p g b e a | t p g b e a] | k t p g b e a | ot sb]; try done.
    destruct (a + ErrorState_size)%a as [a'|]; cbn; last done.
    intros [= <- <-]. iIntros "#H". iSplit; last done.
    by rewrite (interp_cap_cur_addr W C t p g b e a' a π).
  Qed.

  (** The registers at the handler's first instruction. *)
  Definition handler_invocation_regs (kind : handler_kind) (cstk : CSTK) (wcgp : LWord)
    (rfault : LReg) (mcause mtval : Z) (regs : LReg) : Prop :=
    (∀ r, is_Some (regs !! r)) ∧
    (∃ mie, regs !! cra = Some (handler_return_sentry mie)) ∧
    regs !! cgp = Some wcgp ∧
    match kind with
    | Stackful =>
        error_state_stores_ok (rfault !!! csp) ∧
        ∃ wcsp wa0, stackful_regs (rfault !!! csp) = Some (wcsp, wa0) ∧
          regs !! csp = Some wcsp ∧
          regs !! ca0 = Some wa0 ∧
          regs !! ca1 = Some (lword_of_word (WInt mcause)) ∧
          regs !! ca2 = Some (lword_of_word (WInt mtval))
    | Stackless =>
        regs !! csp = Some (stackless_csp cstk) ∧
        regs !! ca0 = Some (lword_of_word (WInt mcause)) ∧
        regs !! ca1 = Some (lword_of_word (WInt mtval)) ∧
        regs !! ca2 = Some (lword_of_word (WInt 0))
    end ∧
    (∀ r, r ∉ ({[cra; cgp; csp; ca0; ca1; ca2]} : gset RegName) →
          regs !! r = Some (lword_of_word (WInt 0))).

  (** The handler offset of kind [kind] declared by the table at [b]. *)
  Definition handler_offset (kind : handler_kind) (b : Addr) (z : Z) : iProp Σ :=
    match kind with Stackful => b ↦ₕ□{stackful} z | Stackless => b ↦ₕ□{stackless} z end.

  #[global] Instance handler_offset_persistent kind b z :
    Persistent (handler_offset kind b z).
  Proof. destruct kind; apply _. Qed.

  (** The number of words of the [ErrorState] that the switcher writes
      before it invokes a handler of kind [kind]. *)
  Definition error_state_size (kind : handler_kind) : nat :=
    match kind with Stackful => Z.to_nat ErrorState_size | Stackless => 0 end.

  (** What the handler receives of the slot, and what it gives back to the
      unwind continuation. A stackful handler receives the written
      [ErrorState], with the two facts of the site on the faulting [csp]:
      no identifier, and the slot outside the shadow table. *)
  Definition handler_slot (kind : handler_kind) (w : LWord) (rfault : LReg) : iProp Σ :=
    match kind with
    | Stackful =>
        ⌜(rfault !!! csp).(lprov) = None⌝ ∗
        ⌜error_state_shadow_free (rfault !!! csp)⌝ ∗
        error_state_pointsto w rfault
    | Stackless => True
    end.
  Definition handler_unwind_res (kind : handler_kind) (rfault : LReg) : iProp Σ :=
    match kind with Stackful => error_state_area rfault | Stackless => True end.

  (** ** Whether the switcher invokes the stackful handler *)

  (** A fault at a PC of the switcher. *)
  Definition switcher_fault_pc (w : LWord) : Prop :=
    get_b (lmepcc_of_pc w).(lw) = (b_switcher : Z).

  Lemma switcher_fault_pc_cap (t : bool) (p : Perm) (g : Locality) (e a : Addr) :
    switcher_fault_pc (WCap t p g b_switcher e a).
  Proof. by rewrite /switcher_fault_pc /lmepcc_of_pc /= get_b_mepcc_of_pc. Qed.

  (** The switcher invokes the stackful handler [eh] of the topmost table,
      whose PCC is [wpcc], for a fault at [w] with registers [rmap] and call
      stack [cstk]: no branch of the exception path before the handler
      unwinds or faults (the fault is outside the switcher, the cell of the
      table is set, the count is even and below the limit, the handler is
      declared, the switcher's stores of the [ErrorState] succeed and the
      tag of the stack pointer cannot be stripped, and the target of the
      [cjalr] is valid). *)
  Definition stackful_handler_runs (cstk : CSTK) (w : LWord) (rmap : LReg)
    (eh : Z) (wpcc : LWord) : Prop :=
    ¬ switcher_fault_pc w ∧
    (top_tframe cstk).(tf_export_tbl) ≠ lword_of_word (WInt 0) ∧
    Z.even (top_error_count cstk) = true ∧
    (top_error_count cstk + 1 <= MAX_FAULTS_PER_COMPARTMENT_CALL)%Z ∧
    eh ≠ ExportTable_no_handler ∧
    error_state_stores_ok (rmap !!! csp) ∧
    ¬ tag_strippable (rmap !!! csp) ∧
    jalr_target_ok cra cra (handler_word wpcc eh).(lw) = true.

  (** The same, with the handler words of the table named. *)
  Definition handler_runs (cstk : CSTK) (w : LWord) (rmap : LReg) : iProp Σ :=
    ∃ (eh : Z) (wpcc : LWord),
      top_export_tbl cstk ↦ₕ□{stackful} eh ∗
      top_export_tbl cstk ↦ₐ□ wpcc ∗
      ⌜stackful_handler_runs cstk w rmap eh wpcc⌝.

  #[global] Instance handler_runs_persistent cstk w rmap :
    Persistent (handler_runs cstk w rmap).
  Proof. rewrite /handler_runs. apply _. Qed.

  (** The reason given to an unwind of the exception path: the switcher
      does not invoke the stackful handler. *)
  Definition handler_skipped (cstk : CSTK) (w : LWord) (rmap : LReg) : iProp Σ :=
    □ (handler_runs cstk w rmap -∗ False).

  #[global] Instance handler_skipped_persistent cstk w rmap :
    Persistent (handler_skipped cstk w rmap).
  Proof. rewrite /handler_skipped. apply _. Qed.

  (** The stackful handler cannot both run and be skipped. *)
  Lemma handler_runs_skipped cstk w rmap :
    handler_runs cstk w rmap -∗ handler_skipped cstk w rmap -∗ False.
  Proof. iIntros "Hruns #Hskip". by iApply "Hskip". Qed.

  (** What a fault site with a trusted handler gives for the unwind: the
      stackful handler runs, or the unwind continuation. *)
  Definition unwind_or_runs (F : coPset) (cstk : CSTK) (w : LWord) (rmap : LReg)
    (R : iProp Σ) : iProp Σ :=
    handler_runs cstk w rmap ∨ unwind_cont F cstk R.

  (** The switcher's resources at a token [F]. *)
  Definition switcher_res (F : coPset) : iProp Σ :=
    ∃ Nswitcher : namespace,
      ⌜↑Nswitcher ⊆ F ∧ ↑N_trap ⊆ F ∧ Nswitcher ## N_trap⌝ ∗
      na_inv cerise_nais Nswitcher switcher_inv ∗
      switcher_static.

  (** ** Trusted handlers *)

  (** The WP of a trusted handler of kind [kind], at offset [off] of the
      PCC [wpcc] of the table at [b_tbl] (CGP [wcgp]), for its fault
      obligation [P_fault]: for every token [F] (the fault site's, with the
      switcher's resources at [F]), call stack [cstk] (the faulting one,
      count even), faulting PC [w] and registers [rfault], the handler runs
      safely from the invocation state, with the slot and, as it chooses,
      the site's unwind continuation (or the fact that the stackful handler
      runs) or [P_fault]. A stackless handler also knows that the stackful
      handler does not run. It does not mention the trap vector. *)
  Definition execute_error_handler (b_tbl : Addr) (wpcc wcgp : LWord) (off : Z)
    (kind : handler_kind) (P_fault : coPset → CSTK → LWord → LReg → iProp Σ) : iProp Σ :=
    □ ∀ (F : coPset) (cstk : CSTK) (w : LWord) (rfault : LReg) (mcause mtval : Z)
        (wpc : LWord) (regs : LReg),
      ▷ ( switcher_res F -∗
          ⌜top_export_tbl cstk = b_tbl⌝ -∗
          ⌜Z.even (top_error_count cstk) = true⌝ -∗
          ⌜mcause_ok mcause⌝ -∗
          ⌜handler_entry wpcc off = Some wpc⌝ -∗
          ⌜handler_invocation_regs kind cstk wcgp rfault mcause mtval regs⌝ -∗
          PC ↦ₚ wpc -∗
          registers_pointsto regs -∗
          handler_slot kind w rfault -∗
          (⌜kind = Stackless⌝ → handler_skipped cstk w rfault) -∗
          (unwind_or_runs F cstk w rfault (handler_unwind_res kind rfault) ∧
           P_fault F cstk w rfault) -∗
          cstack_frag (cstack_set_top_count cstk (top_error_count cstk + 1)) -∗
          na_own cerise_nais F -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ).

  #[global] Instance execute_error_handler_persistent b_tbl wpcc wcgp off kind P_fault :
    Persistent (execute_error_handler b_tbl wpcc wcgp off kind P_fault).
  Proof. rewrite /execute_error_handler. apply _. Qed.

  (** The table at [b_tbl] declares trusted handlers for [P_fault]: its
      header, and the WP of each handler it declares. *)
  Definition trusted_handler (b_tbl : Addr)
    (P_fault : coPset → CSTK → LWord → LReg → iProp Σ) : iProp Σ :=
    ∃ (wpcc wcgp : LWord) (eh ehs : Z),
      b_tbl ↦ₐ□ wpcc ∗
      (b_tbl ^+ ExportTable_offset_cgp)%a ↦ₐ□ wcgp ∗
      b_tbl ↦ₕ□{stackful} eh ∗
      b_tbl ↦ₕ□{stackless} ehs ∗
      (⌜eh ≠ ExportTable_no_handler⌝ →
         execute_error_handler b_tbl wpcc wcgp eh Stackful P_fault) ∗
      (⌜ehs ≠ ExportTable_no_handler⌝ →
         execute_error_handler b_tbl wpcc wcgp ehs Stackless P_fault).

  #[global] Instance trusted_handler_persistent b_tbl P_fault :
    Persistent (trusted_handler b_tbl P_fault).
  Proof.
    (* A plain [apply _] times out on the four existentials. *)
    rewrite /trusted_handler.
    do 4 (apply bi.exist_persistent; intros). apply _.
  Qed.

  (** ** Context installation *)

  (** The PC that InstallContext resumes: the PCC [wpcc] of the topmost
      table with its address set to [a], as the switcher computes it
      ([csetaddr] as a [Lea] by the difference). *)
  Definition resumed_pc (wpcc : LWord) (a : Z) : LWord :=
    default wpcc (lea_result wpcc (a - get_a wpcc.(lw))).

  (** The registers after InstallContext: the 15 words [ls] of the
      [ErrorState] (registers x1 to x15), the other registers of [rmap]. *)
  Definition error_state_install (rmap : LReg) (ls : list LWord) : LReg :=
    list_to_map (zip error_state_regs ls) ∪ rmap.

  (** The resumption of a context that InstallContext installs, at the PC
      [wpc] with the registers [regs], at the token [F]: the continuation of
      a trusted fault site, which it packs in its [P_fault]. *)
  Definition context_resume (F : coPset) (cstk : CSTK) (wpc : LWord) (regs : LReg)
    : iProp Σ :=
    (⌜∀ r, is_Some (regs !! r)⌝ -∗
     PC ↦ₚ wpc -∗
     registers_pointsto regs -∗
     cstack_frag cstk -∗
     na_own cerise_nais F -∗
     WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.

  (** The install's loads of the [ErrorState] below the handler's [csp]
      succeed. *)
  Definition error_state_loads_ok (wcsp : LWord) : Prop :=
    match lea_result wcsp (- ErrorState_size) with
    | Some (MkLWord (WCap true p _ b e a) _) =>
        readAllowed p = true ∧ (b <= a)%a ∧ (a + ErrorState_size <= e)%Z
    | _ => False
    end.

  (** Why the install faults: the cell of the topmost table is cleared, or
      the [ErrorState] cannot be loaded. *)
  Definition install_skipped (cstk : CSTK) (rmap : LReg) : Prop :=
    (top_tframe cstk).(tf_export_tbl) = lword_of_word (WInt 0) ∨
    ¬ error_state_loads_ok (rmap !!! csp).

  (** The [ErrorState] that the install loads, below the handler's cursor
      [a]. *)
  Definition install_region (a : Addr) (ws : list LWord) : iProp Σ :=
    [[ (a ^+ (- ErrorState_size))%a , a ]] ↦ₐ [[ ws ]].

  (** The [ErrorState] that the switcher writes, above the faulting cursor
      of [rfault]'s [csp]. *)
  Definition error_state_region (rfault : LReg) (ws : list LWord) : iProp Σ :=
    match (rfault !!! csp).(lw) with
    | WCap _ _ _ _ _ a => [[ a , (a ^+ ErrorState_size)%a ]] ↦ₐ [[ ws ]]
    | _ => True
    end.

  (** The [ErrorState] that the switcher writes for a stackful handler is
      the one that the install loads below the handler's [csp]. *)
  Lemma install_region_slot (rfault : LReg) (t : bool) (p : Perm) (g : Locality)
    (b e a : Addr) (π : option AId) (wa0 : LWord) (ws : list LWord) :
    stackful_regs (rfault !!! csp) = Some (MkLWord (WCap t p g b e a) π, wa0) →
    error_state_region rfault ws ⊣⊢ install_region a ws.
  Proof.
    rewrite /stackful_regs /error_state_region /install_region.
    destruct (rfault !!! csp) as [w π']; cbn.
    destruct w as [n | [t' p' g' b' e' a' | t' p' g' b' e' a'] | k t' p' g' b' e' a' | ot sb];
      try done.
    destruct (a' + ErrorState_size)%a as [a16|] eqn:Ha16; cbn; last done.
    intros Hregs; simplify_eq.
    rewrite /ErrorState_size in Ha16 |- *.
    rewrite (_ : (a ^- 16)%f = a'); last solve_addr.
    by rewrite (_ : (a' ^+ 16)%a = a); last solve_addr.
  Qed.

  (** When the switcher invokes the stackful handler, the cell of the
      table is set: the install faults only if the handler's [csp] does not
      allow the loads of the [ErrorState]. *)
  Lemma stackful_handler_runs_install (cstk : CSTK) (w : LWord) (rfault : LReg)
    (eh : Z) (wpcc : LWord) (n : Z) (regs : LReg) :
    stackful_handler_runs cstk w rfault eh wpcc →
    error_state_loads_ok (regs !!! csp) →
    ¬ install_skipped (cstack_set_top_count cstk n) regs.
  Proof.
    intros (_ & Hset & _) Hok [Hz | Hnok]; last done.
    rewrite top_tframe_set_count in Hz. by apply Hset.
  Qed.

  (** Setting the address of a safe word keeps it safe: a capability or a
      sealing range with its cursor moved, or untagged by an overflow, an
      integer, or an untagged word. *)
  Lemma interp_resumed_pc (W : WORLD) (C : CmptName) (wpcc : LWord) (a : Z) :
    interp W C wpcc -∗ interp W C (resumed_pc wpcc a).
  Proof.
    iIntros "#H". destruct wpcc as [w π].
    rewrite /resumed_pc /lea_result /=.
    destruct w as [n | [t p g b e a0 | t p g b e a0] | k t p g b e a0 | ot sb]; cbn.
    - iApply interp_int.
    - destruct (a0 + (a - a0))%a as [a'|]; cbn.
      + by rewrite (interp_cap_cur_addr W C t p g b e a' a0 π).
      + by iApply interp_untagged.
    - destruct (a0 + (a - a0))%ot as [a'|]; cbn.
      + iApply (interp_weakening_ot with "H"); try solve_finz.
        * apply SealPermFlowsToReflexive.
        * apply LocalityFlowsToReflexive.
      + by iApply interp_untagged.
    - iApply interp_clear_tag.
    - iApply interp_clear_tag.
  Qed.

  (** Writing a safe word to MEPCC keeps it safe: the same word, or the
      word untagged. *)
  Lemma interp_llegalise_mepcc (W : WORLD) (C : CmptName) (w : LWord) :
    interp W C w -∗ interp W C (llegalise MEPCC w).
  Proof.
    iIntros "#H". destruct w as [w π].
    rewrite /llegalise /lift_word /legalise /legalise_pc /=.
    destruct (is_sealb w && executable_word w); first done.
    iApply (interp_clear_tag W C (MkLWord w π)).
  Qed.

  (** Installing the [ErrorState]'s registers keeps a full register map
      full. *)
  Lemma error_state_install_full (rmap : LReg) (ls : list LWord) :
    (∀ r, is_Some (rmap !! r)) →
    ∀ r, is_Some (error_state_install rmap ls !! r).
  Proof.
    intros Hfull r. rewrite /error_state_install lookup_union_is_Some. right. apply Hfull.
  Qed.

  (** The registers after InstallContext, from the other registers of
      [rmap] and the 15 registers of the [ErrorState]. *)
  Lemma error_state_install_pointsto (rmap : LReg)
    (wcra wcsp wcgp wctp wct0 wct1 wct2 wcs0 wcs1 wca0 wca1 wca2 wca3 wca4 wca5 : LWord) :
    ([∗ map] k↦y ∈ delete ca5 (delete ca4 (delete ca3 (delete ca2 (delete ca1 (delete ca0
       (delete cs1 (delete cs0 (delete ct2 (delete ct1 (delete ct0 (delete ctp (delete cgp
       (delete csp (delete cra rmap)))))))))))))), k ↦ᵣ y) -∗
    cra ↦ᵣ wcra -∗
    csp ↦ᵣ wcsp -∗
    cgp ↦ᵣ wcgp -∗
    ctp ↦ᵣ wctp -∗
    ct0 ↦ᵣ wct0 -∗
    ct1 ↦ᵣ wct1 -∗
    ct2 ↦ᵣ wct2 -∗
    cs0 ↦ᵣ wcs0 -∗
    cs1 ↦ᵣ wcs1 -∗
    ca0 ↦ᵣ wca0 -∗
    ca1 ↦ᵣ wca1 -∗
    ca2 ↦ᵣ wca2 -∗
    ca3 ↦ᵣ wca3 -∗
    ca4 ↦ᵣ wca4 -∗
    ca5 ↦ᵣ wca5 -∗
    registers_pointsto (error_state_install rmap
      [wcra; wcsp; wcgp; wctp; wct0; wct1; wct2; wcs0; wcs1; wca0; wca1; wca2; wca3; wca4; wca5]).
  Proof.
    iIntros "Hrmap Hcra Hcsp Hcgp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hca3 Hca4 Hca5".
    iInsertList "Hrmap" [ca5;ca4;ca3;ca2;ca1;ca0;cs1;cs0;ct2;ct1;ct0;ctp;cgp;csp;cra].
    rewrite /registers_pointsto /error_state_install /=.
    rewrite -!insert_union_l (left_id_L ∅ (∪)). iFrame.
  Qed.

  (** ** The topmost frame of the call stack *)

  (** The stack of the caller of the topmost pushed frame: the frame's stack
      pointer is the one saved after the spill at the caller's cursor
      [a_stk]. *)
  Definition top_frame_stack_ok (cstk : CSTK) : Prop :=
    cstk.(cstk_frames) ≠ [] →
    ∃ b_stk e_stk a_stk : Addr,
      (top_tframe cstk).(tf_csp) = lword_of_word (WCap true RWL Local b_stk e_stk (stk_saved_a a_stk)) ∧
      stk_cursor_ok b_stk e_stk a_stk ∧
      stk_spill_ok a_stk.

  (** The stack pointer of the topmost pushed frame is a capability whose
      cursor is in its bounds. *)
  Lemma cstack_interp_top_csp (cstk : CSTK) (a_tstk : Addr) :
    cstack_interp cstk a_tstk -∗
    ⌜cstk.(cstk_frames) ≠ [] →
     ∃ (p : Perm) (g : Locality) (b e a : Addr),
       (top_tframe cstk).(tf_csp) = lword_of_word (WCap true p g b e a) ∧
       (b <= a)%a ∧ (a <= e)%a ∧
       disjoint_from_heap b e⌝.
  Proof.
    destruct cstk as [ef [|frm frms] ]; first by iIntros "_ %".
    rewrite /cstack_interp /=.
    iIntros "[_ Hcf]". iNamed "Hcf". iDestruct "Hcf" as (b_stk e_stk a_stk) "Hcf". iNamed "Hcf".
    destruct Hcf_csp as (Hcsp & (Hba & Hae & Ha4) & _ & Hheap & _).
    iPureIntro. intros _. rewrite /top_tframe /= Hcsp.
    eexists _, _, b_stk, e_stk, (stk_saved_a a_stk). split_and!; [done | | | done];
      stk_unfold; change (4 - 1)%Z with 3%Z in Hae; solve_addr+Hba Hae Ha4.
  Qed.

  (** The stack of the caller of the topmost pushed frame. *)
  Lemma cstack_interp_top_stack (cstk : CSTK) (a_tstk : Addr) :
    cstack_interp cstk a_tstk -∗
    ⌜top_frame_stack_ok cstk⌝.
  Proof.
    destruct cstk as [ef [|frm frms] ]; first by iIntros "_ %".
    rewrite /cstack_interp /=.
    iIntros "[_ Hcf]". iNamed "Hcf". iDestruct "Hcf" as (b_stk e_stk a_stk) "Hcf". iNamed "Hcf".
    destruct Hcf_csp as (Hcsp & (Hba & _ & Ha4) & _).
    iPureIntro. intros _. rewrite /top_tframe /= Hcsp.
    by exists b_stk, e_stk, a_stk.
  Qed.

  (** The cells of a frame of the trusted stack: the cell of the export
      table, of any fraction, holds the frame's word, cleared or a capability
      to the table, without identifier. *)
  Lemma trusted_frame_interp_open (entry : bool) (tf : trusted_frame) (a_tstk : Addr) :
    trusted_frame_interp entry tf a_tstk -∗
    ∃ (dq : dfrac),
      (a_tstk ^+ TrustedStackFrame_offset_csp)%a ↦ₐ tf.(tf_csp) ∗
      (a_tstk ^+ TrustedStackFrame_offset_calleeExportTable)%a ↦ₐ{dq} tf.(tf_export_tbl) ∗
      (a_tstk ^+ TrustedStackFrame_offset_errorHandlerCount)%a ↦ₐ WInt tf.(tf_error_count) ∗
      ⌜tf.(tf_export_tbl) = lword_of_word (WInt 0) ∨
       (exp_tbl_cap (tf_export_tbl_b tf) tf.(tf_export_tbl).(lw) ∧
        tf.(tf_export_tbl).(lprov) = None)⌝ ∗
      (∀ n : Z,
         (a_tstk ^+ TrustedStackFrame_offset_csp)%a ↦ₐ tf.(tf_csp) -∗
         (a_tstk ^+ TrustedStackFrame_offset_calleeExportTable)%a ↦ₐ{dq} tf.(tf_export_tbl) -∗
         (a_tstk ^+ TrustedStackFrame_offset_errorHandlerCount)%a ↦ₐ WInt n -∗
         trusted_frame_interp entry (tf_set_count tf n) a_tstk).
  Proof.
    rewrite /trusted_frame_interp.
    iIntros "Htf". iNamed "Htf".
    destruct entry.
    - iDestruct "Htf_tbl" as "[#Htbl %Hok]".
      iExists DfracDiscarded. iFrame "Htf_csp Htbl Htf_cnt".
      iSplit; first (iPureIntro; right; exact Hok).
      iIntros (n) "Hcsp _ Hcnt". iFrame "Hcsp Hcnt". iPureIntro. exact Hok.
    - iDestruct "Htf_tbl" as "[Htbl %Hw]".
      iExists (DfracOwn 1). iFrame "Htf_csp Htbl Htf_cnt".
      iSplit; first (iPureIntro; destruct Hw as [-> | Hok]; [by left | right; exact Hok]).
      iIntros (n) "Hcsp Htbl Hcnt". iFrame "Hcsp Htbl Hcnt".
      iPureIntro. exact Hw.
  Qed.

  (** ** Faults that the switcher handles *)

  (** A fault at [w] with registers [regs] and call stack [cstk], at a site
      that holds [na_own F], is not resumed and is one of:
      - a fault in the switcher, or in a compartment whose table declares no
        handler;
      - a fault in a trusted compartment whose table declares trusted
        handlers for some [P_fault]: the site lends the slot, and proves
        both [P_fault] and, from the same resources, its unwind continuation
        or the fact that the stackful handler runs (the handler uses one of
        them, and runs with the site's token [F]);
      - a fault in a running trusted handler (the top count is odd), with
        the handler words of the header of its table.
      Each case gives the site's unwind continuation. *)
  Definition trap_handler_ok_def (F : coPset) (cstk : CSTK) (w : LWord) (regs : LReg)
    : iProp Σ :=
    ⌜trap_no_resume w⌝ ∗
    ( (unwind_cont F cstk True ∗
       (⌜switcher_fault_pc w⌝ ∨ no_handler (top_export_tbl cstk)))
    ∨ (∃ (P_fault : coPset → CSTK → LWord → LReg → iProp Σ) (eh : Z),
         trusted_handler (top_export_tbl cstk) P_fault ∗
         top_export_tbl cstk ↦ₕ□{stackful} eh ∗
         error_state_slot eh regs ∗
         (unwind_or_runs F cstk w regs (error_state_slot eh regs) ∧ P_fault F cstk w regs))
    ∨ (unwind_cont F cstk True ∗
       ⌜Z.odd (top_error_count cstk) = true⌝ ∗
       ∃ eh ehs : Z,
         top_export_tbl cstk ↦ₕ□{stackful} eh ∗
         top_export_tbl cstk ↦ₕ□{stackless} ehs) ).
  #[local] Definition trap_handler_ok_aux : seal (@trap_handler_ok_def). Proof. by eexists. Qed.
  Definition trap_handler_ok := trap_handler_ok_aux.(unseal).
  #[local] Definition trap_handler_ok_unseal :
    @trap_handler_ok = @trap_handler_ok_def := trap_handler_ok_aux.(seal_eq).

  (** A fault in the switcher. *)
  Lemma trap_handler_ok_switcher F cstk w regs :
    trap_no_resume w →
    switcher_fault_pc w →
    unwind_cont F cstk True -∗
    trap_handler_ok F cstk w regs.
  Proof.
    rewrite trap_handler_ok_unseal. iIntros (Hno Hpc) "HU".
    iSplit; first done. iLeft. iFrame. by iLeft.
  Qed.

  (** A fault in a compartment whose table declares no handler. *)
  Lemma trap_handler_ok_no_handler F cstk w regs :
    trap_no_resume w →
    no_handler (top_export_tbl cstk) -∗
    unwind_cont F cstk True -∗
    trap_handler_ok F cstk w regs.
  Proof.
    rewrite trap_handler_ok_unseal. iIntros (Hno) "Hnh HU".
    iSplit; first done. iLeft. iFrame.
  Qed.

  (** A fault in a trusted compartment with trusted handlers. *)
  Lemma trap_handler_ok_handler F cstk w regs
    (P_fault : coPset → CSTK → LWord → LReg → iProp Σ) (eh : Z) :
    trap_no_resume w →
    trusted_handler (top_export_tbl cstk) P_fault -∗
    top_export_tbl cstk ↦ₕ□{stackful} eh -∗
    error_state_slot eh regs -∗
    (unwind_or_runs F cstk w regs (error_state_slot eh regs) ∧ P_fault F cstk w regs) -∗
    trap_handler_ok F cstk w regs.
  Proof.
    rewrite trap_handler_ok_unseal. iIntros (Hno) "Hh Heh Hslot HUP".
    iSplit; first done. iRight; iLeft.
    iExists P_fault, eh. iFrame "Hh Heh Hslot HUP".
  Qed.

  (** A fault in a running trusted handler. *)
  Lemma trap_handler_ok_running F cstk w regs (eh ehs : Z) :
    trap_no_resume w →
    Z.odd (top_error_count cstk) = true →
    top_export_tbl cstk ↦ₕ□{stackful} eh -∗
    top_export_tbl cstk ↦ₕ□{stackless} ehs -∗
    unwind_cont F cstk True -∗
    trap_handler_ok F cstk w regs.
  Proof.
    rewrite trap_handler_ok_unseal. iIntros (Hno Hodd) "Heh Hehs HU".
    iSplit; first done. iRight; iRight. by iFrame.
  Qed.

  (** The three cases, unsealed. *)
  Lemma trap_handler_ok_cases F cstk w regs :
    trap_handler_ok F cstk w regs -∗
    ⌜trap_no_resume w⌝ ∗
    ( (unwind_cont F cstk True ∗
       (⌜switcher_fault_pc w⌝ ∨ no_handler (top_export_tbl cstk)))
    ∨ (∃ (P_fault : coPset → CSTK → LWord → LReg → iProp Σ) (eh : Z),
         trusted_handler (top_export_tbl cstk) P_fault ∗
         top_export_tbl cstk ↦ₕ□{stackful} eh ∗
         error_state_slot eh regs ∗
         (unwind_or_runs F cstk w regs (error_state_slot eh regs) ∧ P_fault F cstk w regs))
    ∨ (unwind_cont F cstk True ∗
       ⌜Z.odd (top_error_count cstk) = true⌝ ∗
       ∃ eh ehs : Z,
         top_export_tbl cstk ↦ₕ□{stackful} eh ∗
         top_export_tbl cstk ↦ₕ□{stackless} ehs) ).
  Proof. rewrite trap_handler_ok_unseal. iIntros "H". iExact "H". Qed.

End Switcher_error_handler.
