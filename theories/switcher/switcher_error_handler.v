From iris.proofmode Require Import proofmode.
From griotte Require Import logrel memory_region rules proofmode.
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
    destruct_word w; cbn; intros [=<-]; cbn; try (split; [by intros [? _] | done]).
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
    destruct_word w; cbn; intros [=<-]; cbn; try done.
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

  Lemma error_state_stores_ok_fits wcsp :
    error_state_stores_ok wcsp → error_state_fits wcsp.
  Proof. rewrite /error_state_stores_ok /error_state_fits. repeat case_match; naive_solver. Qed.

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
    destruct_word w; cbn; intros [=<-] Hfits Hnot; cbn; try done.
    - destruct t; last done.
      destruct (a + 16)%a as [a'|] eqn:Ha; last solve_addr.
      right. exists c, g, b, e, a', a. split_and!; [done | solve_addr |].
      destruct (writeAllowed c) eqn:Hw; [right | by left].
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
  Definition error_state_written (kind : handler_kind) : nat :=
    match kind with Stackful => Z.to_nat ErrorState_size | Stackless => 0 end.

  (** What the handler receives of the slot, and what it gives back to the
      unwind continuation. *)
  Definition handler_slot (kind : handler_kind) (w : LWord) (rfault : LReg) : iProp Σ :=
    match kind with Stackful => error_state_pointsto w rfault | Stackless => True end.
  Definition handler_unwind_res (kind : handler_kind) (rfault : LReg) : iProp Σ :=
    match kind with Stackful => error_state_area rfault | Stackless => True end.

  (** ** Trusted handlers *)

  (** The WP of a trusted handler of kind [kind], at offset [off] of the
      PCC [wpcc] of the table at [b_tbl] (CGP [wcgp]), for its fault
      obligation [P_fault]: for every call stack [cstk] (the faulting one,
      count even), faulting PC [w] and registers [rfault], the handler runs
      safely from the invocation state. It does not mention the trap
      vector. *)
  Definition execute_error_handler (b_tbl : Addr) (wpcc wcgp : LWord) (off : Z)
    (kind : handler_kind) (P_fault : CSTK → LWord → LReg → iProp Σ) : iProp Σ :=
    □ ∀ (cstk : CSTK) (w : LWord) (rfault : LReg) (mcause mtval : Z) (wpc : LWord) (regs : LReg),
      ▷ ( ⌜top_export_tbl cstk = b_tbl⌝ -∗
          ⌜Z.even (top_error_count cstk) = true⌝ -∗
          ⌜mcause_ok mcause⌝ -∗
          ⌜handler_entry wpcc off = Some wpc⌝ -∗
          ⌜handler_invocation_regs kind cstk wcgp rfault mcause mtval regs⌝ -∗
          PC ↦ₚ wpc -∗
          registers_pointsto regs -∗
          P_fault cstk w rfault -∗
          handler_slot kind w rfault -∗
          unwind_cont ⊤ cstk (handler_unwind_res kind rfault) -∗
          cstack_frag (cstack_set_top_count cstk (top_error_count cstk + 1)) -∗
          na_own cerise_nais ⊤ -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ).

  #[global] Instance execute_error_handler_persistent b_tbl wpcc wcgp off kind P_fault :
    Persistent (execute_error_handler b_tbl wpcc wcgp off kind P_fault).
  Proof. rewrite /execute_error_handler. apply _. Qed.

  (** The table at [b_tbl] declares trusted handlers for [P_fault]: its
      header, and the WP of each handler it declares. *)
  Definition trusted_handler (b_tbl : Addr) (P_fault : CSTK → LWord → LReg → iProp Σ)
    : iProp Σ :=
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
  Proof. rewrite /trusted_handler. apply _. Qed.

  (** ** Faults that the switcher handles *)

  (** A fault at a PC of the switcher. *)
  Definition switcher_fault_pc (w : LWord) : Prop :=
    get_b (lmepcc_of_pc w).(lw) = (b_switcher : Z).

  Lemma switcher_fault_pc_cap (t : bool) (p : Perm) (g : Locality) (e a : Addr) :
    switcher_fault_pc (WCap t p g b_switcher e a).
  Proof. by rewrite /switcher_fault_pc /lmepcc_of_pc /= get_b_mepcc_of_pc. Qed.

  (** A fault at [w] with registers [regs] and call stack [cstk], at a site
      that holds [na_own F], is not resumed and is one of:
      - a fault in the switcher, or in a compartment whose table declares no
        handler;
      - a fault in a trusted compartment whose table declares trusted
        handlers for some [P_fault]: the site proves [P_fault] and lends the
        slot ([F = ⊤]: the handler runs with the whole token);
      - a fault in a running trusted handler (the top count is odd), with
        the handler words of the header of its table.
      Each case gives the site's unwind continuation. *)
  Definition trap_handler_ok_def (F : coPset) (cstk : CSTK) (w : LWord) (regs : LReg)
    : iProp Σ :=
    ⌜trap_no_resume w⌝ ∗
    ( (unwind_cont F cstk True ∗
       (⌜switcher_fault_pc w⌝ ∨ no_handler (top_export_tbl cstk)))
    ∨ (⌜F = ⊤⌝ ∗
       ∃ (P_fault : CSTK → LWord → LReg → iProp Σ) (eh : Z),
         trusted_handler (top_export_tbl cstk) P_fault ∗
         top_export_tbl cstk ↦ₕ□{stackful} eh ∗
         P_fault cstk w regs ∗
         error_state_slot eh regs ∗
         unwind_cont ⊤ cstk (error_state_slot eh regs))
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
  Lemma trap_handler_ok_handler cstk w regs
    (P_fault : CSTK → LWord → LReg → iProp Σ) (eh : Z) :
    trap_no_resume w →
    trusted_handler (top_export_tbl cstk) P_fault -∗
    top_export_tbl cstk ↦ₕ□{stackful} eh -∗
    P_fault cstk w regs -∗
    error_state_slot eh regs -∗
    unwind_cont ⊤ cstk (error_state_slot eh regs) -∗
    trap_handler_ok ⊤ cstk w regs.
  Proof.
    rewrite trap_handler_ok_unseal. iIntros (Hno) "Hh Heh HP Hslot HU".
    iSplit; first done. iRight; iLeft. iSplit; first done.
    iExists P_fault, eh. iFrame "Hh Heh HP Hslot HU".
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
    ∨ (⌜F = ⊤⌝ ∗
       ∃ (P_fault : CSTK → LWord → LReg → iProp Σ) (eh : Z),
         trusted_handler (top_export_tbl cstk) P_fault ∗
         top_export_tbl cstk ↦ₕ□{stackful} eh ∗
         P_fault cstk w regs ∗
         error_state_slot eh regs ∗
         unwind_cont ⊤ cstk (error_state_slot eh regs))
    ∨ (unwind_cont F cstk True ∗
       ⌜Z.odd (top_error_count cstk) = true⌝ ∗
       ∃ eh ehs : Z,
         top_export_tbl cstk ↦ₕ□{stackful} eh ∗
         top_export_tbl cstk ↦ₕ□{stackless} ehs) ).
  Proof. rewrite trap_handler_ok_unseal. iIntros "H". iExact "H". Qed.

End Switcher_error_handler.
