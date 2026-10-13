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
  Implicit Types r : RegName.
  Implicit Types v : griotte_lang.val.
  Implicit Types w : LWord.
  Implicit Types reg : gmap RegName LWord.
  Implicit Types ms : gmap Addr LWord.

  Inductive Lea_failure (lpc : LWord) (regs : LReg) (r1: RegName) (rv: Z + RegName) :=
  | Lea_fail_rv_nonconst :
     lz_of_argument regs rv = None ->
     Lea_failure lpc regs r1 rv
  | Lea_fail_allowed : forall w,
     regs !!ₗ r1 = Some w ->
     is_mutable_range w.(lw) = false →
     Lea_failure lpc regs r1 rv
  | Lea_fail_overflow_cap : forall (t : bool) p g b e a π z,
     regs !!ₗ r1 = Some (WCap t p g b e a @@? π) ->
     lz_of_argument regs rv = Some z ->
     (a + z)%a = None ->
     incrementPC lpc = None ->
     Lea_failure lpc regs r1 rv
  | Lea_fail_overflow_PC_cap : forall (t : bool) p g b e a π z a',
     regs !!ₗ r1 = Some (WCap t p g b e a @@? π) ->
     lz_of_argument regs rv = Some z ->
     (a + z)%a = Some a' ->
     incrementPC lpc = None ->
     Lea_failure lpc regs r1 rv
  | Lea_fail_overflow_sr : forall (t : bool) p g b e a π z,
     regs !!ₗ r1 = Some (WSealRange t p g b e a @@? π) ->
     lz_of_argument regs rv = Some z ->
     (a + z)%ot = None ->
     incrementPC lpc = None ->
     Lea_failure lpc regs r1 rv
  | Lea_fail_overflow_PC_sr : forall (t : bool) p g b e a π z a',
     regs !!ₗ r1 = Some (WSealRange t p g b e a @@? π) ->
     lz_of_argument regs rv = Some z ->
     (a + z)%ot = Some a' ->
     incrementPC lpc = None ->
     Lea_failure lpc regs r1 rv
  .

  Inductive Lea_spec
    (lpc : LWord) (regs : LReg) (r1: RegName) (rv: Z + RegName)
    (lpc' : LWord) (regs' : LReg) : griotte_lang.val → Prop
  :=
  | Lea_spec_success_cap: forall (t : bool) p g b e a π z a',
    regs !!ₗ r1 = Some (WCap t p g b e a @@? π) ->
    lz_of_argument regs rv = Some z ->
    (a + z)%a = Some a' ->
    incrementPC lpc = Some lpc' ->
    regs' = <[ r1 := WCap t p g b e a' @@? π ]ₗ> regs ->
    Lea_spec lpc regs r1 rv lpc' regs' NextIV
  | Lea_spec_success_sr: forall (t : bool) p g b e a π z a',
    regs !!ₗ r1 = Some (WSealRange t p g b e a @@? π) ->
    lz_of_argument regs rv = Some z ->
    (a + z)%ot = Some a' ->
    incrementPC lpc = Some lpc' ->
    regs' = <[ r1 := WSealRange t p g b e a' @@? π ]ₗ> regs ->
    Lea_spec lpc regs r1 rv lpc' regs' NextIV
  | Lea_spec_invalidated_cap: forall (t : bool) p g b e a π z,
    regs !!ₗ r1 = Some (WCap t p g b e a @@? π) ->
    lz_of_argument regs rv = Some z ->
    (a + z)%a = None ->
    incrementPC lpc = Some lpc' ->
    regs' = <[ r1 := WCap false p g b e a @@? π ]ₗ> regs ->
    Lea_spec lpc regs r1 rv lpc' regs' NextIV
  | Lea_spec_invalidated_sr: forall (t : bool) p g b e a π z,
    regs !!ₗ r1 = Some (WSealRange t p g b e a @@? π) ->
    lz_of_argument regs rv = Some z ->
    (a + z)%ot = None ->
    incrementPC lpc = Some lpc' ->
    regs' = <[ r1 := WSealRange false p g b e a @@? π ]ₗ> regs ->
    Lea_spec lpc regs r1 rv lpc' regs' NextIV
  | Lea_spec_failure :
    Lea_failure lpc regs r1 rv ->
    Lea_spec lpc regs r1 rv lpc' regs' FailedV.

   Lemma wp_lea Ep pc_p pc_g pc_b pc_e pc_a pc_π r1 w arg (regs : LReg) dq :
     decodeInstrW w.(lw) = Lea r1 arg →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     regs_of (Lea r1 arg) ⊆ dom regs →
     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
         ▷ pc_a ↦ₐ{dq} w ∗
         ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
       Instr Executable @ Ep
     {{{ lpc' regs' retv, RET retv;
         ⌜ Lea_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 arg lpc' regs' retv ⌝ ∗
         PC ↦ₚ lpc' ∗
         pc_a ↦ₐ{dq} w ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
   Proof.
     iIntros (Hinstr Hvpc Dregs φ) "(>HPC & >Hpc_a & >Hmap) Hφ".
     iApply (wp_instr_step with "HPC Hpc_a Hmap"); eauto.
     iNext. iIntros (r sr m st lreg lmem R C c σ' Her Hlregs Hregs Hpc_a Hstep)
       "HPCa Hr Hsr Hm Hst HR HC HPC Hpc_a Hmap".
     rewrite Hinstr in Hstep.
     specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri.
     unfold regs_of in Hri, Dregs.
     destruct (Hri r1) as [r1v [H'r1 _]]; first by set_solver+.
     pose proof (llookup_reg_incl _ _ _ _ Hregs H'r1) as Hr1.
     pose proof (erasure_llookup_reg_word _ _ _ _ _ _ _ _ _ Her Hlregs H'r1) as Hok.
     rewrite /exec /= Hr1 /= in Hstep.
     destruct (lz_of_argument regs arg) as [argz|] eqn:Harg.
     2: { rewrite (lz_of_argument_None regs r) /= in Hstep; [|done| |done].
          2: { intros x ->. apply Dregs. set_solver+. }
          simplify_eq. iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); first done.
          iIntros "HPC Hmap". iApply "Hφ". iFrame. iPureIntro.
          constructor. by constructor. }
     rewrite (lz_of_argument_incl regs r _ argz) /= in Hstep; [|done|done].
     destruct r1v as [[ | [t p g b e a | t p g b e a] | | ] π]; cbn in Hstep.
     1,4,5: (simplify_eq; iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); first done;
             iIntros "HPC Hmap"; iApply "Hφ"; iFrame; iPureIntro;
             constructor; eapply Lea_fail_allowed; eauto).
     - destruct (a + argz)%a as [a'|] eqn:Hoffset; cbn in Hstep.
       + iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ r1 (WCap t p g b e a' @@? π) _ _ _
           (λ lpc' regs' retv, Lea_spec _ regs r1 arg lpc' regs' retv)
           with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
         { exact Her. } { exact Hlregs. } { apply Dregs. set_solver+. }
         { eapply (reg_word_ok_derive _ _ (WCap t p g b e a @@? π)); [by left|done|done]. }
         { exact Hstep. }
         { intros lpc' Hi. eapply Lea_spec_success_cap; eauto. }
         { intros Hi. constructor. eapply Lea_fail_overflow_PC_cap; eauto. }
         iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
       + iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ r1 (WCap false p g b e a @@? π) _ _ _
           (λ lpc' regs' retv, Lea_spec _ regs r1 arg lpc' regs' retv)
           with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
         { exact Her. } { exact Hlregs. } { apply Dregs. set_solver+. }
         { eapply (reg_word_ok_derive _ _ (WCap t p g b e a @@? π)); [by left|done|done]. }
         { exact Hstep. }
         { intros lpc' Hi. eapply Lea_spec_invalidated_cap; eauto. }
         { intros Hi. constructor. eapply Lea_fail_overflow_cap; eauto. }
         iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
     - destruct (a + argz)%ot as [a'|] eqn:Hoffset; cbn in Hstep.
       + iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ r1 (WSealRange t p g b e a' @@? π) _ _ _
           (λ lpc' regs' retv, Lea_spec _ regs r1 arg lpc' regs' retv)
           with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
         { exact Her. } { exact Hlregs. } { apply Dregs. set_solver+. }
         { eapply (reg_word_ok_derive _ _ (WSealRange t p g b e a @@? π)); [by right|done|done]. }
         { exact Hstep. }
         { intros lpc' Hi. eapply Lea_spec_success_sr; eauto. }
         { intros Hi. constructor. eapply Lea_fail_overflow_PC_sr; eauto. }
         iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
       + iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ r1 (WSealRange false p g b e a @@? π) _ _ _
           (λ lpc' regs' retv, Lea_spec _ regs r1 arg lpc' regs' retv)
           with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
         { exact Her. } { exact Hlregs. } { apply Dregs. set_solver+. }
         { eapply (reg_word_ok_derive _ _ (WSealRange t p g b e a @@? π)); [by right|done|done]. }
         { exact Hstep. }
         { intros lpc' Hi. eapply Lea_spec_invalidated_sr; eauto. }
         { intros Hi. constructor. eapply Lea_fail_overflow_sr; eauto. }
         iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
   Qed.

   Lemma wp_lea_success_reg Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 rv (t : bool) p g b e a wz z a' π dq :
     decodeInstrW w.(lw) = Lea r1 (inr rv) →
     IsLInt wz z →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = Some a' →
     rv ≠ cnull ->
     r1 ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ r1 ↦ᵣ WCap t p g b e a @@? π
           ∗ ▷ rv ↦ᵣ wz }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ{dq} w
              ∗ rv ↦ᵣ wz
              ∗ r1 ↦ᵣ WCap t p g b e a' @@? π }}}.
   Proof.
     iIntros (Hinstr Hwz Hvpc Hpca' Ha' Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ".
     destruct (IsLInt_inv _ _ Hwz) as [πz ->].
     iDestruct (map_of_regs_2 with "Hrv Hr1") as "[Hmap %]".
     iApply (wp_lea with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
     all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
     iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | | | | * Hfail ].
     3,4: by simplify_lmap_eq.
     { (* Success *)
       iApply "Hφ". iFrame. try incrementPC_inv; simplify_lmap_eq.
       (* FIXME: tedious *)
       iRegsMap "Hmap"; iFrame. }
     { (* Success with WSealRange (contradiction) *)
       simplify_lmap_eq. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto.
       all: try destruct p; cbn in * ; congruence. }
    Unshelve. all: auto.
   Qed.

   Lemma wp_lea_success_z Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 (t : bool) p g b e a z a' π dq :
     decodeInstrW w.(lw) = Lea r1 (inl z) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = Some a' →
     r1 ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ r1 ↦ᵣ WCap t p g b e a @@? π }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
            ∗ pc_a ↦ₐ{dq} w
            ∗ r1 ↦ᵣ WCap t p g b e a' @@? π }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' Hcnull ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
     iDestruct (map_of_regs_1 with "Hr1") as "Hmap".
     iApply (wp_lea with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
     all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
     iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | | | | * Hfail ].
     3,4: by simplify_lmap_eq.
     { (* Success *)
       iApply "Hφ". iFrame. try incrementPC_inv; simplify_lmap_eq.
       (* FIXME: tedious *)
       iRegsMap "Hmap"; eauto. iFrame. }
     { (* Success with WSealRange (contradiction) *)
       simplify_lmap_eq. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto.
       all: try destruct p; cbn in * ; congruence. }
     Unshelve. all:auto.
   Qed.

   (* Similar rules in case we have a SealRange instead of a capability, where some cases are impossible, because a SealRange is not a valid PC *)

   Lemma wp_lea_success_reg_sr Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 rv (t : bool) p g b e a wz z a' π dq :
     decodeInstrW w.(lw) = Lea r1 (inr rv) →
     IsLInt wz z →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%ot = Some a' →
     rv ≠ cnull ->
     r1 ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? π
           ∗ ▷ rv ↦ᵣ wz }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ{dq} w
              ∗ rv ↦ᵣ wz
              ∗ r1 ↦ᵣ WSealRange t p g b e a' @@? π }}}.
   Proof.
     iIntros (Hinstr Hwz Hvpc Hpca' Ha' Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ".
     destruct (IsLInt_inv _ _ Hwz) as [πz ->].
     iDestruct (map_of_regs_2 with "Hrv Hr1") as "[Hmap %]".
     iApply (wp_lea with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
     all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
     iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | | | | * Hfail ].
     3,4: by simplify_lmap_eq.
     { (* Success with WSealCap (contradiction) *)
       simplify_lmap_eq. }
     { (* Success *)
       iApply "Hφ". iFrame. try incrementPC_inv; simplify_lmap_eq.
       (* FIXME: tedious *)
       iRegsMap "Hmap"; iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto.
       all: try congruence.
     }
    Unshelve. all: auto.
   Qed.

  Lemma wp_lea_success_z_sr Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 (t : bool) p g b e a z a' π dq :
     decodeInstrW w.(lw) = Lea r1 (inl z) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%ot = Some a' →
     r1 ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? π }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
            ∗ pc_a ↦ₐ{dq} w
            ∗ r1 ↦ᵣ WSealRange t p g b e a' @@? π }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' Hcnull ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
     iDestruct (map_of_regs_1 with "Hr1") as "Hmap".
     iApply (wp_lea with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
     all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
     iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | | | | * Hfail ].
     3,4: by simplify_lmap_eq.
     { (* Success with WSealRange (contradiction) *)
       simplify_lmap_eq. }
     { (* Success *)
       iApply "Hφ". iFrame. try incrementPC_inv; simplify_lmap_eq.
       (* FIXME: tedious *)
       iRegsMap "Hmap"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto.
       all: try congruence.
     }
     Unshelve. all:auto.
   Qed.

   Lemma wp_lea_overflow_reg Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 rv (t : bool) p g b e a wz z π dq :
     decodeInstrW w.(lw) = Lea r1 (inr rv) →
     IsLInt wz z →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = None →
     rv ≠ cnull ->
     r1 ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ r1 ↦ᵣ WCap t p g b e a @@? π
           ∗ ▷ rv ↦ᵣ wz }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ{dq} w
              ∗ rv ↦ᵣ wz
              ∗ r1 ↦ᵣ WCap false p g b e a @@? π }}}.
   Proof.
     iIntros (Hinstr Hwz Hvpc Hpca' Ha' Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ".
     destruct (IsLInt_inv _ _ Hwz) as [πz ->].
     iDestruct (map_of_regs_2 with "Hrv Hr1") as "[Hmap %]".
     iApply (wp_lea with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
     all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
     iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | | | | * Hfail ].
     1,2,4: by simplify_lmap_eq.
     { (* Success *)
       iApply "Hφ". iFrame. try incrementPC_inv; simplify_lmap_eq.
       (* FIXME: tedious *)
       iRegsMap "Hmap"; iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto.
       all: try destruct p; cbn in * ; congruence. }
    Unshelve. all: auto.
   Qed.

   Lemma wp_lea_overflow_z Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 (t : bool) p g b e a z π dq :
     decodeInstrW w.(lw) = Lea r1 (inl z) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = None →
     r1 ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ r1 ↦ᵣ WCap t p g b e a @@? π }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
            ∗ pc_a ↦ₐ{dq} w
            ∗ r1 ↦ᵣ WCap false p g b e a @@? π }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' Hcnull ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
     iDestruct (map_of_regs_1 with "Hr1") as "Hmap".
     iApply (wp_lea with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
     all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
     iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | | | | * Hfail ].
     1,2,4: by simplify_lmap_eq.
     { (* Success *)
       iApply "Hφ". iFrame. try incrementPC_inv; simplify_lmap_eq.
       (* FIXME: tedious *)
       iRegsMap "Hmap"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto.
       all: try destruct p; cbn in * ; congruence. }
     Unshelve. all:auto.
   Qed.

   Lemma wp_lea_overflow_reg_sr Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 rv (t : bool) p g b e a wz z π dq :
     decodeInstrW w.(lw) = Lea r1 (inr rv) →
     IsLInt wz z →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%ot = None →
     rv ≠ cnull ->
     r1 ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? π
           ∗ ▷ rv ↦ᵣ wz }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ{dq} w
              ∗ rv ↦ᵣ wz
              ∗ r1 ↦ᵣ WSealRange false p g b e a @@? π }}}.
   Proof.
     iIntros (Hinstr Hwz Hvpc Hpca' Ha' Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ".
     destruct (IsLInt_inv _ _ Hwz) as [πz ->].
     iDestruct (map_of_regs_2 with "Hrv Hr1") as "[Hmap %]".
     iApply (wp_lea with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
     all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
     iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | | | | * Hfail ].
     1,2,3: by simplify_lmap_eq.
     { (* Success *)
       iApply "Hφ". iFrame. try incrementPC_inv; simplify_lmap_eq.
       (* FIXME: tedious *)
       iRegsMap "Hmap"; iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto.
       all: try congruence.
     }
    Unshelve. all: auto.
   Qed.

   Lemma wp_lea_overflow_z_sr Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 (t : bool) p g b e a z π dq :
     decodeInstrW w.(lw) = Lea r1 (inl z) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%ot = None →
     r1 ≠ cnull ->

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? π }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
            ∗ pc_a ↦ₐ{dq} w
            ∗ r1 ↦ᵣ WSealRange false p g b e a @@? π }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' Hcnull ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
     iDestruct (map_of_regs_1 with "Hr1") as "Hmap".
     iApply (wp_lea with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
     all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
     iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | | | | * Hfail ].
     1,2,3: by simplify_lmap_eq.
     { (* Success *)
       iApply "Hφ". iFrame. try incrementPC_inv; simplify_lmap_eq.
       (* FIXME: tedious *)
       iRegsMap "Hmap"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto.
       all: try congruence.
     }
     Unshelve. all:auto.
   Qed.

   Lemma wp_Lea_fail_integer Ep pc_p pc_g pc_b pc_e pc_a pc_π w r1 w1 z z' dq :
     decodeInstrW w.(lw) = Lea r1 (inl z) →
     IsLInt w1 z' →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →

     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
         ∗ ▷ pc_a ↦ₐ{dq} w
         ∗ ▷ r1 ↦ᵣ w1
     }}}
       Instr Executable @ Ep
       {{{ RET FailedV; True }}}.
   Proof.
     iIntros (Hdecode Hw1 Hvpc φ) "(>HPC & >Hpc_a & >Hsrc) Hφ".
     destruct (IsLInt_inv _ _ Hw1) as [π1 ->].
     iDestruct (map_of_regs_1 with "Hsrc") as "Hmap".
     iApply (wp_lea with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
     all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
     iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.
     destruct Hspec as [* Hsucc | * Hsucc | * Hsucc | * Hsucc |].
     3,4: (destruct (decide (r1 = cnull)); simplify_lmap_eq).
     { (* Success (contradiction) *) simplify_lmap_eq.
       destruct (decide (r1 = cnull)); done.
     }
     { (* Success (contradiction) *) simplify_lmap_eq.
       destruct (decide (r1 = cnull)); done.
     }
     { (* Failure, done *) by iApply "Hφ". }
   Qed.

End griotte_lang_rules.
