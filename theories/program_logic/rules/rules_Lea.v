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
     iNext; iIntrosNamed (r sr m st lreg lmem R C c σ').
     rewrite Hinstr in Hstep.
     specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri.
     unfold regs_of in Hri, Dregs.
     destruct (Hri r1) as [r1v [H'r1 _]]; first by set_solver+.
     destruct (llookup_reg_phys _ _ _ _ _ Hregs H'r1) as (s & Hr1 & Hrel).
     pose proof (erasure_llookup_reg_word _ _ _ _ _ _ _ _ _ Her Hlregs H'r1) as Hok.
     rewrite /exec /= Hr1 /= in Hstep.
     destruct (lz_of_argument regs arg) as [argz|] eqn:Harg.
     2: { rewrite (lz_of_argument_None R regs r) /= in Hstep; [|done| |done].
          2: { intros x ->. apply Dregs. set_solver+. }
          instr_fail Hstep. constructor. by constructor. }
     rewrite (lz_of_argument_incl R regs r _ argz) /= in Hstep; [|done|done].
     destruct r1v as [[ | [t p g b e a | t p g b e a] | | ] π]; cbn in Hstep.
     1,4,5: (instr_fail Hstep; constructor; eapply Lea_fail_allowed; eauto).
     - destruct (a + argz)%a as [a'|] eqn:Hoffset; cbn in Hstep.
       + iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ r1 (WCap t p g b e a' @@? π) _ _ _ _
           (λ lpc' regs' retv, Lea_spec _ regs r1 arg lpc' regs' retv)
           with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
         { exact Her. } { exact Hlregs. } { apply Dregs. set_solver+. }
         { eapply (reg_word_ok_derive _ _ (WCap t p g b e a @@? π)); [by left|done|done|done]. }
         { exact Hstep. }
         { by apply (reg_phys_derive _ (WCap t p g b e a @@? π) s (WCap t p g b e a')). }
         { intros lpc' Hi. eapply Lea_spec_success_cap; eauto. }
         { intros Hi. constructor. eapply Lea_fail_overflow_PC_cap; eauto. }
         iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
       + iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ r1 (WCap false p g b e a @@? π) _ _ _ _
           (λ lpc' regs' retv, Lea_spec _ regs r1 arg lpc' regs' retv)
           with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
         { exact Her. } { exact Hlregs. } { apply Dregs. set_solver+. }
         { eapply (reg_word_ok_derive _ _ (WCap t p g b e a @@? π)); [by left|done|done|done]. }
         { exact Hstep. }
         { by apply reg_phys_untagged. }
         { intros lpc' Hi. eapply Lea_spec_invalidated_cap; eauto. }
         { intros Hi. constructor. eapply Lea_fail_overflow_cap; eauto. }
         iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
     - destruct (a + argz)%ot as [a'|] eqn:Hoffset; cbn in Hstep.
       + iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ r1 (WSealRange t p g b e a' @@? π) _ _ _ _
           (λ lpc' regs' retv, Lea_spec _ regs r1 arg lpc' regs' retv)
           with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
         { exact Her. } { exact Hlregs. } { apply Dregs. set_solver+. }
         { eapply (reg_word_ok_derive _ _ (WSealRange t p g b e a @@? π)); [by right|done|done|done]. }
         { exact Hstep. }
         { by apply (reg_phys_derive _ (WSealRange t p g b e a @@? π) s (WSealRange t p g b e a')). }
         { intros lpc' Hi. eapply Lea_spec_success_sr; eauto. }
         { intros Hi. constructor. eapply Lea_fail_overflow_PC_sr; eauto. }
         iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
       + iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ r1 (WSealRange false p g b e a @@? π) _ _ _ _
           (λ lpc' regs' retv, Lea_spec _ regs r1 arg lpc' regs' retv)
           with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
         { exact Her. } { exact Hlregs. } { apply Dregs. set_solver+. }
         { eapply (reg_word_ok_derive _ _ (WSealRange t p g b e a @@? π)); [by right|done|done|done]. }
         { exact Hstep. }
         { by apply reg_phys_untagged. }
         { intros lpc' Hi. eapply Lea_spec_invalidated_sr; eauto. }
         { intros Hi. constructor. eapply Lea_fail_overflow_sr; eauto. }
         iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
   Qed.

   (** The word a Lea writes into a capability or a sealing range: the moved
       cursor, or the untagged original if the cursor overflows. *)
   Definition lea_result (v : LWord) (z : Z) : option LWord :=
     match v.(lw) with
     | WCap t p g b e a =>
         Some (match (a + z)%a with
               | Some a' => WCap t p g b e a'
               | None => WCap false p g b e a
               end @@? v.(lprov))
     | WSealRange t p g b e a =>
         Some (match (a + z)%ot with
               | Some a' => WSealRange t p g b e a'
               | None => WSealRange false p g b e a
               end @@? v.(lprov))
     | _ => None
     end.

   (** A Lea on a capability or a sealing range, whose PC increments, has one
       outcome. *)
   Lemma Lea_spec_next lpc regs r1 arg lpc' regs' retv wr z wr' lpc0 :
     regs !!ₗ r1 = Some wr →
     lz_of_argument regs arg = Some z →
     lea_result wr z = Some wr' →
     incrementPC lpc = Some lpc0 →
     Lea_spec lpc regs r1 arg lpc' regs' retv →
     retv = NextIV ∧ lpc' = lpc0 ∧ regs' = <[r1 := wr']ₗ> regs.
   Proof.
     intros Hr Hz Hres Hinc Hspec.
     destruct Hspec as [* Hr' Hz' Ha' Hinc' -> | * Hr' Hz' Ha' Hinc' ->
                       | * Hr' Hz' Ha' Hinc' -> | * Hr' Hz' Ha' Hinc' -> | Hfail].
     1-4: rewrite Hr in Hr'; simplify_eq; rewrite /lea_result /= Ha' in Hres; by simplify_eq.
     destruct Hfail as [Hz' | w' Hr' Hm | | | |]; try congruence.
     rewrite Hr in Hr'. injection Hr' as <-.
     destruct wr as [w0 ?]. destruct_word w0; cbn in *; congruence.
   Qed.

   (** The map-form success rule, from which the register-shaped ones
       follow. *)
   Lemma wp_lea_next E pc_p pc_g pc_b pc_e pc_a pc_π w r1 arg regs wr z wr' lpc' dq :
     decodeInstrW w.(lw) = Lea r1 arg →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     regs_of (Lea r1 arg) ⊆ dom regs →
     regs !!ₗ r1 = Some wr →
     lz_of_argument regs arg = Some z →
     lea_result wr z = Some wr' →
     incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' →
     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
         ▷ pc_a ↦ₐ{dq} w ∗
         ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
       Instr Executable @ E
     {{{ RET NextIV;
         PC ↦ₚ lpc' ∗
         pc_a ↦ₐ{dq} w ∗
         [∗ map] k↦y ∈ <[r1 := wr']ₗ> regs, k ↦ᵣ y }}}.
   Proof.
     iIntros (Hdecode Hvpc Dregs Hr Hz Hres Hinc φ) "(HPC & Hpc_a & Hmap) Hφ".
     iApply (wp_lea with "[$HPC $Hpc_a $Hmap]"); [done..|].
     iIntros "!>" (lpc0 regs' retv) "(%Hspec & HPC & Hpc_a & Hmap)".
     destruct (Lea_spec_next _ _ _ _ _ _ _ _ _ _ _ Hr Hz Hres Hinc Hspec) as (-> & -> & ->).
     iApply "Hφ". by iFrame.
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
     iApply (wp_lea_next _ _ _ _ _ _ _ _ _ _ _ (WCap t p g b e a @@? π) _
       (WCap t p g b e a' @@? π) with "[$HPC $Hpc_a $Hmap]"); try solve_next_side;
       try by rewrite /lea_result /= Ha'.
     iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
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
     iApply (wp_lea_next _ _ _ _ _ _ _ _ _ _ _ (WCap t p g b e a @@? π) _
       (WCap t p g b e a' @@? π) with "[$HPC $Hpc_a $Hmap]"); try solve_next_side;
       try by rewrite /lea_result /= Ha'.
     iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
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
     iApply (wp_lea_next _ _ _ _ _ _ _ _ _ _ _ (WSealRange t p g b e a @@? π) _
       (WSealRange t p g b e a' @@? π) with "[$HPC $Hpc_a $Hmap]"); try solve_next_side;
       try by rewrite /lea_result /= Ha'.
     iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
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
     iApply (wp_lea_next _ _ _ _ _ _ _ _ _ _ _ (WSealRange t p g b e a @@? π) _
       (WSealRange t p g b e a' @@? π) with "[$HPC $Hpc_a $Hmap]"); try solve_next_side;
       try by rewrite /lea_result /= Ha'.
     iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
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
     iApply (wp_lea_next _ _ _ _ _ _ _ _ _ _ _ (WCap t p g b e a @@? π) _
       (WCap false p g b e a @@? π) with "[$HPC $Hpc_a $Hmap]"); try solve_next_side;
       try by rewrite /lea_result /= Ha'.
     iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
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
     iApply (wp_lea_next _ _ _ _ _ _ _ _ _ _ _ (WCap t p g b e a @@? π) _
       (WCap false p g b e a @@? π) with "[$HPC $Hpc_a $Hmap]"); try solve_next_side;
       try by rewrite /lea_result /= Ha'.
     iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
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
     iApply (wp_lea_next _ _ _ _ _ _ _ _ _ _ _ (WSealRange t p g b e a @@? π) _
       (WSealRange false p g b e a @@? π) with "[$HPC $Hpc_a $Hmap]"); try solve_next_side;
       try by rewrite /lea_result /= Ha'.
     iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
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
     iApply (wp_lea_next _ _ _ _ _ _ _ _ _ _ _ (WSealRange t p g b e a @@? π) _
       (WSealRange false p g b e a @@? π) with "[$HPC $Hpc_a $Hmap]"); try solve_next_side;
       try by rewrite /lea_result /= Ha'.
     iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
   Qed.

End griotte_lang_rules.
