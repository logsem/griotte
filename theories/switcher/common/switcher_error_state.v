From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import call_stack switcher_tactics.

(** * Error state

    The pure definitions about a fault that the switcher handles: the
    handler's return sentry and PC, the room and store tests for the
    [ErrorState] on the faulting stack, the stackless handler's stack, and
    the PC and load test of InstallContext. *)

Section Switcher_error_state.
  Context `{MP: MachineParameters} {swlayout : switcherLayout}.

  (** ** The handler invocation *)

  (** The sentry the switcher gives a handler in [cra]: the link of the
      [cjalr] of [.Lhandle_error_handler_cjalr], to the next instruction,
      [.Lhandle_error_handler_return]. Its kind follows the interrupt status
      [mie] at the [cjalr], which the logic does not track. *)
  Definition handler_return_sentry (mie : InterruptStatus) : LWord :=
    Sentry (ret_kind mie) XSRW_ Local b_switcher e_switcher
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

  (** The switcher's room test for the [ErrorState], the [ErrorState_size]
      words below the cursor: they are above the base. The test does not
      check that the stores succeed. The first store of the [ErrorState]
      faults on a sealing range, without the write permission, or when the
      [ErrorState] starts at or above the end
      ([e <= a - ErrorState_size]). When the end is inside the
      [ErrorState] ([a - ErrorState_size < e < a]), the stores write the
      words below [e], and the first store at [e] faults. *)
  Definition error_state_fits (wcsp : LWord) : Prop :=
    match wcsp.(lw) with
    | Cap _ _ b _ a => (b + ErrorState_size <= a)%Z
    | SealRange _ _ b _ a => (b + ErrorState_size <= a)%Z
    | _ => False
    end.

  (** The room test, on the stack pointer moved down to the base of the
      [ErrorState] ([wct0]): its tag, and its cursor not below its base. *)
  Lemma error_state_fits_lea (wcsp wct0 : LWord) :
    lea_result wcsp (- ErrorState_size) = Some wct0 →
    (get_tag wct0.(lw) = true ∧ get_b wct0.(lw) <= get_a wct0.(lw))%Z ↔
    error_state_fits wcsp.
  Proof.
    destruct wcsp as [w π]. rewrite /lea_result /error_state_fits /ErrorState_size /=.
    destruct w as [n | [t p g b e a | t p g b e a] | k t p g b e a | ot sb];
      cbn; intros [=<-]; cbn; try (split; [by intros [? _] | done]).
    - destruct (a + - (16))%a as [a'|] eqn:Ha; destruct t; cbn; split;
        try (by intros [? _]); try done;
        [intros [_ ?] | intros ? | intros ?]; split_and?; solve_addr.
    - destruct (a + - (16))%ot as [a'|] eqn:Ha; destruct t; cbn; split;
        try (by intros [? _]); try done;
        [intros [_ ?] | intros ? | intros ?]; split_and?; solve_finz.
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
    | Cap p _ b e a => writeAllowed p = true ∧ (b + ErrorState_size <= a)%Z ∧ (a <= e)%a
    | _ => False
    end.

  #[global] Instance error_state_stores_ok_dec wcsp : Decision (error_state_stores_ok wcsp).
  Proof. rewrite /error_state_stores_ok. repeat case_match; apply _. Defined.

  (** The room test passes and the first store of the [ErrorState], at its
      base, through the faulting [csp] succeeds. *)
  Definition error_state_first_store_ok (wcsp : LWord) : Prop :=
    match wcsp.(lw) with
    | Cap p _ b e a =>
        writeAllowed p = true ∧ (b + ErrorState_size <= a)%Z ∧ (a - ErrorState_size < e)%Z
    | _ => False
    end.

  #[global] Instance error_state_first_store_ok_dec wcsp :
    Decision (error_state_first_store_ok wcsp).
  Proof. rewrite /error_state_first_store_ok. repeat case_match; apply _. Defined.

  Lemma error_state_stores_ok_first (wcsp : LWord) :
    error_state_stores_ok wcsp → error_state_first_store_ok wcsp.
  Proof.
    rewrite /error_state_stores_ok /error_state_first_store_ok /ErrorState_size.
    repeat case_match; try done. intros (? & ? & ?). split_and!; [done | lia | solve_addr].
  Qed.

  (** When the room test passes but the stores do not succeed, either the
      first store of the stackful setup, through the moved stack pointer
      [wct0] at the base of the [ErrorState], faults ([wct0] is a sealing
      range, it has no write permission, or its cursor is not below its
      end), or the first store succeeds and the end of the stack is inside
      the [ErrorState]: the words below the end are written, and the store
      at the end faults. *)
  Lemma error_state_store_fault (wcsp wct0 : LWord) :
    lea_result wcsp (- ErrorState_size) = Some wct0 →
    error_state_fits wcsp →
    ¬ error_state_stores_ok wcsp →
    (¬ error_state_first_store_ok wcsp ∧
     (is_cap wct0.(lw) = false ∨
      ∃ (p : Perm) (g : Locality) (b e a ea : Addr),
        wct0.(lw) = Cap p g b e a ∧
        (a + TrustedStack_offset_mepcc)%a = Some ea ∧
        (writeAllowed p = false ∨ withinBounds b e ea = false))) ∨
    (error_state_first_store_ok wcsp ∧
     ∃ (p : Perm) (g : Locality) (b e a : Addr),
       wct0.(lw) = Cap p g b e a ∧
       (a < e)%a ∧ (e < a + ErrorState_size)%Z).
  Proof.
    destruct wcsp as [w π].
    rewrite /lea_result /error_state_fits /error_state_stores_ok
      /error_state_first_store_ok /ErrorState_size /TrustedStack_offset_mepcc /=.
    destruct w as [n | [t p g b e a | t p g b e a] | k t p g b e a | ot sb];
      cbn; intros [=<-] Hfits Hnot; cbn; try done.
    - destruct t; last done.
      destruct (a + - (16))%a as [a'|] eqn:Ha; last solve_addr.
      destruct (writeAllowed p) eqn:Hw.
      + destruct (decide (a' < e)%a) as [Hlt | Hge].
        * right. split; first (split_and!; [done | done | solve_addr]).
          exists p, g, b, e, a'. split_and!; [done | done |].
          destruct (decide (a <= e)%a); last solve_addr.
          exfalso. apply Hnot. split_and!; [done | done | done].
        * left. split; first (intros (_ & _ & ?); solve_addr).
          right. exists p, g, b, e, a', a'. split_and!; [done | solve_addr |].
          right. rewrite /withinBounds. solve_addr.
      + left. split; first (by intros (? & _)).
        right. exists p, g, b, e, a', a'. split_and!; [done | solve_addr | by left].
    - left. split; first done. left. by destruct (a + - (16))%ot.
  Qed.

  (** The stackless handler's stack: the invocation's slice of the topmost
      pushed frame's [csp], below its cursor, with the cursor at its base, or
      the entry frame's [csp] as is. *)
  Definition stackless_csp (cstk : CSTK) : LWord :=
    match cstk.(cstk_frames) with
    | frm :: _ =>
        match frm.(cf_tframe).(tf_csp) with
        | MkLWord (WCap t p g b _ a) π => MkLWord (WCap t p g b a b) π
        | wcsp => wcsp
        end
    | [] => cstk.(cstk_entry).(tf_csp)
    end.

  (** ** Context installation *)

  (** The PC that InstallContext resumes: the PCC [wpcc] of the topmost
      table with its address set to [a], as the switcher computes it
      ([csetaddr] as a [Lea] by the difference). *)
  Definition resumed_pc (wpcc : LWord) (a : Z) : LWord :=
    default wpcc (lea_result wpcc (a - get_a wpcc.(lw))).

  (** The install's loads of the [ErrorState] at the handler's [csp]
      succeed. *)
  Definition error_state_loads_ok (wcsp : LWord) : Prop :=
    match wcsp.(lw) with
    | Cap p _ b e a =>
        readAllowed p = true ∧ (b <= a)%a ∧ (a + ErrorState_size <= e)%Z
    | _ => False
    end.

End Switcher_error_state.
