From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base.

Section griotte_lang_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {CL : CritLink Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : griotte_lang.expr.
  Implicit Types r : RegName.
  Implicit Types v : griotte_lang.val.
  Implicit Types w : LWord.
  Implicit Types reg : gmap RegName LWord.
  Implicit Types ms : gmap Addr LWord.

  Inductive Lea_failure (lpc : LWord) (regs : LReg) (dst src : RegName) (rv : Z + RegName) :=
  | Lea_fail_overflow_PC_other : forall w,
     regs !!ₗ src = Some w ->
     is_mutable_range w.(lw) = false →
     incrementPC lpc = None ->
     Lea_failure lpc regs dst src rv
  | Lea_fail_overflow_cap : forall (t : bool) p g b e a π z,
     regs !!ₗ src = Some (WCap t p g b e a @@? π) ->
     lz_of_argument regs rv = Some z ->
     (a + z)%a = None ->
     incrementPC lpc = None ->
     Lea_failure lpc regs dst src rv
  | Lea_fail_overflow_PC_cap : forall (t : bool) p g b e a π z a',
     regs !!ₗ src = Some (WCap t p g b e a @@? π) ->
     lz_of_argument regs rv = Some z ->
     (a + z)%a = Some a' ->
     incrementPC lpc = None ->
     Lea_failure lpc regs dst src rv
  | Lea_fail_overflow_sr : forall (t : bool) p g b e a π z,
     regs !!ₗ src = Some (WSealRange t p g b e a @@? π) ->
     lz_of_argument regs rv = Some z ->
     (a + z)%ot = None ->
     incrementPC lpc = None ->
     Lea_failure lpc regs dst src rv
  | Lea_fail_overflow_PC_sr : forall (t : bool) p g b e a π z a',
     regs !!ₗ src = Some (WSealRange t p g b e a @@? π) ->
     lz_of_argument regs rv = Some z ->
     (a + z)%ot = Some a' ->
     incrementPC lpc = None ->
     Lea_failure lpc regs dst src rv
  .

  Inductive Lea_spec
    (lpc : LWord) (regs : LReg) (dst src : RegName) (rv : Z + RegName)
    (lpc' : LWord) (regs' : LReg) : griotte_lang.val → Prop
  :=
  | Lea_spec_success_cap: forall (t : bool) p g b e a π z a',
    regs !!ₗ src = Some (WCap t p g b e a @@? π) ->
    lz_of_argument regs rv = Some z ->
    (a + z)%a = Some a' ->
    incrementPC lpc = Some lpc' ->
    regs' = <[ dst := WCap t p g b e a' @@? π ]ₗ> regs ->
    Lea_spec lpc regs dst src rv lpc' regs' NextIV
  | Lea_spec_success_sr: forall (t : bool) p g b e a π z a',
    regs !!ₗ src = Some (WSealRange t p g b e a @@? π) ->
    lz_of_argument regs rv = Some z ->
    (a + z)%ot = Some a' ->
    incrementPC lpc = Some lpc' ->
    regs' = <[ dst := WSealRange t p g b e a' @@? π ]ₗ> regs ->
    Lea_spec lpc regs dst src rv lpc' regs' NextIV
  | Lea_spec_invalidated_cap: forall (t : bool) p g b e a π z,
    regs !!ₗ src = Some (WCap t p g b e a @@? π) ->
    lz_of_argument regs rv = Some z ->
    (a + z)%a = None ->
    incrementPC lpc = Some lpc' ->
    regs' = <[ dst := Cap⁻ p g b e a @@? π ]ₗ> regs ->
    Lea_spec lpc regs dst src rv lpc' regs' NextIV
  | Lea_spec_invalidated_sr: forall (t : bool) p g b e a π z,
    regs !!ₗ src = Some (WSealRange t p g b e a @@? π) ->
    lz_of_argument regs rv = Some z ->
    (a + z)%ot = None ->
    incrementPC lpc = Some lpc' ->
    regs' = <[ dst := SealRange⁻ p g b e a @@? π ]ₗ> regs ->
    Lea_spec lpc regs dst src rv lpc' regs' NextIV
  (* An integer moves by the offset. *)
  | Lea_spec_int: forall n π z,
    regs !!ₗ src = Some (WInt n @@? π) ->
    lz_of_argument regs rv = Some z ->
    incrementPC lpc = Some lpc' ->
    regs' = <[ dst := WInt (n + z) @@? π ]ₗ> regs ->
    Lea_spec lpc regs dst src rv lpc' regs' NextIV
  (* A sealed word or a sentry loses its tag. *)
  | Lea_spec_sealed: forall w,
    regs !!ₗ src = Some w ->
    (is_sealed w.(lw) || is_sentry w.(lw)) = true ->
    incrementPC lpc = Some lpc' ->
    regs' = <[ dst := lclear_tag w ]ₗ> regs ->
    Lea_spec lpc regs dst src rv lpc' regs' NextIV
  | Lea_spec_failure :
    Lea_failure lpc regs dst src rv ->
    lpc' = lpc ->
    regs' = regs ->
    Lea_spec lpc regs dst src rv lpc' regs' FaultedV.

   Lemma wp_lea Ep pc_p pc_g pc_b pc_e pc_a pc_π dst src w arg (regs : LReg) dq :
     decodeInstrW w.(lw) = Lea dst src arg →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     regs_of (Lea dst src arg) ⊆ dom regs →
     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
         ▷ pc_a ↦ₐ{dq} w ∗
         ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
       Instr Executable @ Ep
     {{{ lpc' regs' retv, RET retv;
         ⌜ Lea_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst src arg lpc' regs' retv ⌝ ∗
         PC ↦ₚ lpc' ∗
         pc_a ↦ₐ{dq} w ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
   Proof.
     iIntros (Hinstr Hvpc Dregs φ) "(>HPC & >Hpc_a & >Hmap) Hφ".
     iApply (wp_instr_step with "HPC Hpc_a Hmap"); eauto.
     iNext; iIntros (r sr m st lreg lsreg lmem R C c σ') "@".
     rewrite Hinstr in Hstep.
     specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri.
     unfold regs_of, operands_of in Hri, Dregs.
     destruct (Hri src) as [srcv [H'src _] ]; first by set_solver+.
     destruct (llookup_reg_phys _ _ _ _ _ Hregs H'src) as (s & Hsrc & Hrel).
     pose proof (erasure_llookup_reg_word _ _ _ _ _ _ _ _ _ _ Her Hlregs H'src) as Hok.
     rewrite /exec /= Hsrc /= in Hstep.
     destruct (lz_of_argument_dom regs arg) as [argz Harg].
     { eapply arg_owned_of_dom; [exact Dregs | try unfold regs_of, operands_of; set_solver+]. }
     rewrite (lz_of_argument_incl R regs r _ argz) /= in Hstep; [|done|done].
     destruct (decide ((is_sealed srcv.(lw) || is_sentry srcv.(lw)) = true)) as [Hsl | Hsl].
     { iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ dst (lclear_tag srcv) (clear_tag srcv.(lw)) _ _ _
          (λ lpc' regs' retv, Lea_spec _ regs dst src arg lpc' regs' retv)
          with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
       { exact Her. } { exact Hlregs. } { eapply elem_of_lregs_dom; [exact Dregs | try unfold regs_of, operands_of; set_solver+]. }
       { apply reg_word_ok_lclear_tag. }
       { rewrite -Hstep. by destruct srcv as [[| [] | | ? [] ] ?], s. }
       { apply reg_phys_lclear_tag in Hrel. by rewrite clear_tag_and_tag in Hrel. }
       { intros lpc' Hi. eapply Lea_spec_sealed; eauto. }
       { intros Hi. apply Lea_spec_failure; [|done..]. eapply Lea_fail_overflow_PC_other; eauto.
         by destruct srcv as [[| [] | | ? [] ] ?]. }
       iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame. }
     destruct srcv as [[ n | [t p g b e a | t p g b e a] | | ] π]; cbn in Hstep.
     4,5: by exfalso; apply Hsl.
     1: { iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ dst (WInt (n + argz) @@? π) _ _ _ _
          (λ lpc' regs' retv, Lea_spec _ regs dst src arg lpc' regs' retv)
          with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
       { exact Her. } { exact Hlregs. } { eapply elem_of_lregs_dom; [exact Dregs | try unfold regs_of, operands_of; set_solver+]. }
       { apply reg_word_ok_int. } { exact Hstep. } { apply reg_phys_int. }
       { intros lpc' Hi. eapply Lea_spec_int; eauto. }
       { intros Hi. apply Lea_spec_failure; [|done..]. eapply Lea_fail_overflow_PC_other; eauto. }
       iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame. }
     - destruct (a + argz)%a as [a'|] eqn:Hoffset; cbn in Hstep.
       + iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ dst (WCap t p g b e a' @@? π) _ _ _ _
           (λ lpc' regs' retv, Lea_spec _ regs dst src arg lpc' regs' retv)
           with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
         { exact Her. } { exact Hlregs. } { eapply elem_of_lregs_dom; [exact Dregs | try unfold regs_of, operands_of; set_solver+]. }
         { eapply (reg_word_ok_derive _ _ (WCap t p g b e a @@? π)); [by left|done|done|done]. }
         { exact Hstep. }
         { by apply (reg_phys_derive _ (WCap t p g b e a @@? π) s (WCap t p g b e a')). }
         { intros lpc' Hi. eapply Lea_spec_success_cap; eauto. }
         { intros Hi. apply Lea_spec_failure; [|done..]. eapply Lea_fail_overflow_PC_cap; eauto. }
         iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
       + iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ dst (Cap⁻ p g b e a @@? π) _ _ _ _
           (λ lpc' regs' retv, Lea_spec _ regs dst src arg lpc' regs' retv)
           with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
         { exact Her. } { exact Hlregs. } { eapply elem_of_lregs_dom; [exact Dregs | try unfold regs_of, operands_of; set_solver+]. }
         { eapply (reg_word_ok_derive _ _ (WCap t p g b e a @@? π)); [by left|done|done|done]. }
         { exact Hstep. }
         { by apply reg_phys_untagged. }
         { intros lpc' Hi. eapply Lea_spec_invalidated_cap; eauto. }
         { intros Hi. apply Lea_spec_failure; [|done..]. eapply Lea_fail_overflow_cap; eauto. }
         iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
     - destruct (a + argz)%ot as [a'|] eqn:Hoffset; cbn in Hstep.
       + iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ dst (WSealRange t p g b e a' @@? π) _ _ _ _
           (λ lpc' regs' retv, Lea_spec _ regs dst src arg lpc' regs' retv)
           with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
         { exact Her. } { exact Hlregs. } { eapply elem_of_lregs_dom; [exact Dregs | try unfold regs_of, operands_of; set_solver+]. }
         { eapply (reg_word_ok_derive _ _ (WSealRange t p g b e a @@? π)); [by right|done|done|done]. }
         { exact Hstep. }
         { by apply (reg_phys_derive _ (WSealRange t p g b e a @@? π) s (WSealRange t p g b e a')). }
         { intros lpc' Hi. eapply Lea_spec_success_sr; eauto. }
         { intros Hi. apply Lea_spec_failure; [|done..]. eapply Lea_fail_overflow_PC_sr; eauto. }
         iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
       + iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ dst (SealRange⁻ p g b e a @@? π) _ _ _ _
           (λ lpc' regs' retv, Lea_spec _ regs dst src arg lpc' regs' retv)
           with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
         { exact Her. } { exact Hlregs. } { eapply elem_of_lregs_dom; [exact Dregs | try unfold regs_of, operands_of; set_solver+]. }
         { eapply (reg_word_ok_derive _ _ (WSealRange t p g b e a @@? π)); [by right|done|done|done]. }
         { exact Hstep. }
         { by apply reg_phys_untagged. }
         { intros lpc' Hi. eapply Lea_spec_invalidated_sr; eauto. }
         { intros Hi. apply Lea_spec_failure; [|done..]. eapply Lea_fail_overflow_sr; eauto. }
         iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
   Qed.

   (** The word a Lea writes: for a capability or a sealing range, the moved
       cursor, or the untagged original if the cursor overflows; the moved
       integer; the untagged original otherwise. *)
   Definition lea_result (v : LWord) (z : Z) : option LWord :=
     match v.(lw) with
     | WCap t p g b e a =>
         Some (match (a + z)%a with
               | Some a' => WCap t p g b e a'
               | None => Cap⁻ p g b e a
               end @@? v.(lprov))
     | WSealRange t p g b e a =>
         Some (match (a + z)%ot with
               | Some a' => WSealRange t p g b e a'
               | None => SealRange⁻ p g b e a
               end @@? v.(lprov))
     | WInt n => Some (WInt (n + z) @@? v.(lprov))
     | _ => Some (lclear_tag v)
     end.

   (** [lea_result] is defined on every word. *)
   Lemma lea_result_is_Some (w : LWord) (z : Z) : is_Some (lea_result w z).
   Proof. rewrite /lea_result. repeat case_match; eauto. Qed.

   (** A Lea whose PC increments has one outcome. *)
   Lemma Lea_spec_next lpc regs dst src arg lpc' regs' retv wr z wr' lpc0 :
     regs !!ₗ src = Some wr →
     lz_of_argument regs arg = Some z →
     lea_result wr z = Some wr' →
     incrementPC lpc = Some lpc0 →
     Lea_spec lpc regs dst src arg lpc' regs' retv →
     retv = NextIV ∧ lpc' = lpc0 ∧ regs' = <[dst := wr']ₗ> regs.
   Proof.
     intros Hr Hz Hres Hinc Hspec.
     destruct Hspec as [* Hr' Hz' Ha' Hinc' -> | * Hr' Hz' Ha' Hinc' ->
                       | * Hr' Hz' Ha' Hinc' -> | * Hr' Hz' Ha' Hinc' ->
                       | * Hr' Hz' Hinc' -> | w' Hr' Hsl Hinc' -> | Hfail].
     1-4: rewrite Hr in Hr'; simplify_eq; rewrite /lea_result /= Ha' in Hres; by simplify_eq.
     1: rewrite Hr in Hr'; simplify_eq; rewrite /lea_result /= in Hres; by simplify_eq.
     1: { rewrite Hr in Hr'. injection Hr' as <-.
          destruct wr as [w0 ?]. destruct_word w0; cbn in *; simplify_eq; done. }
     by destruct Hfail; congruence.
   Qed.

   (** The map-form success rule, from which the register-shaped ones
       follow. *)
   Lemma wp_lea_next E pc_p pc_g pc_b pc_e pc_a pc_π w dst src arg regs wr z wr' lpc' dq :
     decodeInstrW w.(lw) = Lea dst src arg →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     regs_of (Lea dst src arg) ⊆ dom regs →
     regs !!ₗ src = Some wr →
     lz_of_argument regs arg = Some z →
     lea_result wr z = Some wr' →
     incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' →
     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
         ▷ pc_a ↦ₐ{dq} w ∗
         ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
       Instr Executable @ E
     {{{ RET NextIV;
         PC ↦ₚ lpc' ∗
         pc_a ↦ₐ{dq} w ∗
         [∗ map] k↦y ∈ <[dst := wr']ₗ> regs, k ↦ᵣ y }}}.
   Proof.
     iIntros (Hdecode Hvpc Dregs Hr Hz Hres Hinc φ) "(HPC & Hpc_a & Hmap) Hφ".
     iApply (wp_lea with "[$HPC $Hpc_a $Hmap]"); [done..|].
     iIntros "!>" (lpc0 regs' retv) "(%Hspec & HPC & Hpc_a & Hmap)".
     destruct (Lea_spec_next _ _ _ _ _ _ _ _ _ _ _ _ Hr Hz Hres Hinc Hspec) as (-> & -> & ->).
     iApply "Hφ". by iFrame.
   Qed.

   Lemma wp_lea_success_reg Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 rv (t : bool) p g b e a wz z a' π dq :
     decodeInstrW w.(lw) = Lea r1 r1 (inr rv) →
     IsLInt wz z →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = Some a' →
     rv ≠ cnull ->
     r1 ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ r1 ↦ᵣ WCap t p g b e a @@? π
           ∗ ▷ rv ↦ᵣ wz }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ{dq} w
              ∗ rv ↦ᵣ wz
              ∗ r1 ↦ᵣ WCap t p g b e a' @@? π }}}.
   Proof.
     iIntros (Hinstr Hwz Hvpc Hpca' Ha' Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ".
     destruct (IsLInt_inv _ _ Hwz) as [πz ->].
     iDestruct (map_of_regs_2 with "Hrv Hr1") as "[Hmap %]".
     iApply (wp_lea_next _ _ _ _ _ _ _ _ _ _ _ _ (WCap t p g b e a @@? π) _
       (WCap t p g b e a' @@? π) with "[$HPC $Hpc_a $Hmap]"); try solve_next_side;
       try by rewrite /lea_result /= Ha'.
     iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
   Qed.

   Lemma wp_lea_success_z Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 (t : bool) p g b e a z a' π dq :
     decodeInstrW w.(lw) = Lea r1 r1 (inl z) →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = Some a' →
     r1 ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ r1 ↦ᵣ WCap t p g b e a @@? π }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
            ∗ pc_a ↦ₐ{dq} w
            ∗ r1 ↦ᵣ WCap t p g b e a' @@? π }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' Hcnull ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
     iDestruct (map_of_regs_1 with "Hr1") as "Hmap".
     iApply (wp_lea_next _ _ _ _ _ _ _ _ _ _ _ _ (WCap t p g b e a @@? π) _
       (WCap t p g b e a' @@? π) with "[$HPC $Hpc_a $Hmap]"); try solve_next_side;
       try by rewrite /lea_result /= Ha'.
     iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
   Qed.

   (** A Lea on an integer moves it by the offset. *)
   Lemma wp_lea_success_z_int Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 n z π dq :
     decodeInstrW w.(lw) = Lea r1 r1 (inl z) →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     r1 ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ r1 ↦ᵣ WInt n @@? π }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
            ∗ pc_a ↦ₐ{dq} w
            ∗ r1 ↦ᵣ WInt (n + z) @@? π }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hcnull ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
     iDestruct (map_of_regs_1 with "Hr1") as "Hmap".
     iApply (wp_lea_next _ _ _ _ _ _ _ _ _ _ _ _ (WInt n @@? π) _
       (WInt (n + z) @@? π) with "[$HPC $Hpc_a $Hmap]"); try solve_next_side; try done.
     iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
   Qed.

   (* Similar rules in case we have a SealRange instead of a capability, where some cases are impossible, because a SealRange is not a valid PC *)

   Lemma wp_lea_success_reg_sr Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 rv (t : bool) p g b e a wz z a' π dq :
     decodeInstrW w.(lw) = Lea r1 r1 (inr rv) →
     IsLInt wz z →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%ot = Some a' →
     rv ≠ cnull ->
     r1 ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? π
           ∗ ▷ rv ↦ᵣ wz }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ{dq} w
              ∗ rv ↦ᵣ wz
              ∗ r1 ↦ᵣ WSealRange t p g b e a' @@? π }}}.
   Proof.
     iIntros (Hinstr Hwz Hvpc Hpca' Ha' Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ".
     destruct (IsLInt_inv _ _ Hwz) as [πz ->].
     iDestruct (map_of_regs_2 with "Hrv Hr1") as "[Hmap %]".
     iApply (wp_lea_next _ _ _ _ _ _ _ _ _ _ _ _ (WSealRange t p g b e a @@? π) _
       (WSealRange t p g b e a' @@? π) with "[$HPC $Hpc_a $Hmap]"); try solve_next_side;
       try by rewrite /lea_result /= Ha'.
     iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
   Qed.

  Lemma wp_lea_success_z_sr Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 (t : bool) p g b e a z a' π dq :
     decodeInstrW w.(lw) = Lea r1 r1 (inl z) →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%ot = Some a' →
     r1 ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? π }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
            ∗ pc_a ↦ₐ{dq} w
            ∗ r1 ↦ᵣ WSealRange t p g b e a' @@? π }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' Hcnull ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
     iDestruct (map_of_regs_1 with "Hr1") as "Hmap".
     iApply (wp_lea_next _ _ _ _ _ _ _ _ _ _ _ _ (WSealRange t p g b e a @@? π) _
       (WSealRange t p g b e a' @@? π) with "[$HPC $Hpc_a $Hmap]"); try solve_next_side;
       try by rewrite /lea_result /= Ha'.
     iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
   Qed.

   Lemma wp_lea_overflow_reg Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 rv (t : bool) p g b e a wz z π dq :
     decodeInstrW w.(lw) = Lea r1 r1 (inr rv) →
     IsLInt wz z →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = None →
     rv ≠ cnull ->
     r1 ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ r1 ↦ᵣ WCap t p g b e a @@? π
           ∗ ▷ rv ↦ᵣ wz }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ{dq} w
              ∗ rv ↦ᵣ wz
              ∗ r1 ↦ᵣ Cap⁻ p g b e a @@? π }}}.
   Proof.
     iIntros (Hinstr Hwz Hvpc Hpca' Ha' Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ".
     destruct (IsLInt_inv _ _ Hwz) as [πz ->].
     iDestruct (map_of_regs_2 with "Hrv Hr1") as "[Hmap %]".
     iApply (wp_lea_next _ _ _ _ _ _ _ _ _ _ _ _ (WCap t p g b e a @@? π) _
       (Cap⁻ p g b e a @@? π) with "[$HPC $Hpc_a $Hmap]"); try solve_next_side;
       try by rewrite /lea_result /= Ha'.
     iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
   Qed.

   Lemma wp_lea_overflow_z Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 (t : bool) p g b e a z π dq :
     decodeInstrW w.(lw) = Lea r1 r1 (inl z) →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = None →
     r1 ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ r1 ↦ᵣ WCap t p g b e a @@? π }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
            ∗ pc_a ↦ₐ{dq} w
            ∗ r1 ↦ᵣ Cap⁻ p g b e a @@? π }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' Hcnull ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
     iDestruct (map_of_regs_1 with "Hr1") as "Hmap".
     iApply (wp_lea_next _ _ _ _ _ _ _ _ _ _ _ _ (WCap t p g b e a @@? π) _
       (Cap⁻ p g b e a @@? π) with "[$HPC $Hpc_a $Hmap]"); try solve_next_side;
       try by rewrite /lea_result /= Ha'.
     iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
   Qed.

   Lemma wp_lea_overflow_reg_sr Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 rv (t : bool) p g b e a wz z π dq :
     decodeInstrW w.(lw) = Lea r1 r1 (inr rv) →
     IsLInt wz z →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%ot = None →
     rv ≠ cnull ->
     r1 ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? π
           ∗ ▷ rv ↦ᵣ wz }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ{dq} w
              ∗ rv ↦ᵣ wz
              ∗ r1 ↦ᵣ SealRange⁻ p g b e a @@? π }}}.
   Proof.
     iIntros (Hinstr Hwz Hvpc Hpca' Ha' Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ".
     destruct (IsLInt_inv _ _ Hwz) as [πz ->].
     iDestruct (map_of_regs_2 with "Hrv Hr1") as "[Hmap %]".
     iApply (wp_lea_next _ _ _ _ _ _ _ _ _ _ _ _ (WSealRange t p g b e a @@? π) _
       (SealRange⁻ p g b e a @@? π) with "[$HPC $Hpc_a $Hmap]"); try solve_next_side;
       try by rewrite /lea_result /= Ha'.
     iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
   Qed.

   Lemma wp_lea_overflow_z_sr Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 (t : bool) p g b e a z π dq :
     decodeInstrW w.(lw) = Lea r1 r1 (inl z) →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%ot = None →
     r1 ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ{dq} w
           ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? π }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
            ∗ pc_a ↦ₐ{dq} w
            ∗ r1 ↦ᵣ SealRange⁻ p g b e a @@? π }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' Hcnull ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
     iDestruct (map_of_regs_1 with "Hr1") as "Hmap".
     iApply (wp_lea_next _ _ _ _ _ _ _ _ _ _ _ _ (WSealRange t p g b e a @@? π) _
       (SealRange⁻ p g b e a @@? π) with "[$HPC $Hpc_a $Hmap]"); try solve_next_side;
       try by rewrite /lea_result /= Ha'.
     iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
   Qed.

   (** [Lea] on an integer, by the integer of a register. *)
   Lemma wp_lea_success_reg_int Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 rv n wz z π dq :
     decodeInstrW w.(lw) = Lea r1 r1 (inr rv) →
     IsLInt wz z →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     rv ≠ cnull →
     r1 ≠ cnull →

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
         ▷ pc_a ↦ₐ{dq} w ∗
         ▷ r1 ↦ᵣ WInt n @@? π ∗
         ▷ rv ↦ᵣ wz }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
         pc_a ↦ₐ{dq} w ∗
         rv ↦ᵣ wz ∗
         r1 ↦ᵣ WInt (n + z) @@? π }}}.
   Proof.
     iIntros (Hinstr Hwz Hvpc Hpca' Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ".
     destruct (IsLInt_inv _ _ Hwz) as [πz ->].
     iDestruct (map_of_regs_2 with "Hrv Hr1") as "[Hmap %]".
     iApply (wp_lea_next _ _ _ _ _ _ _ _ _ _ _ _ (WInt n @@? π) _
       (WInt (n + z) @@? π) with "[$HPC $Hpc_a $Hmap]"); try solve_next_side; try done.
     iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
   Qed.

   (** [Lea] by the integer of a register, on any word. *)
   Lemma wp_lea_success_reg_any Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 rv wr wr' wz z dq :
     decodeInstrW w.(lw) = Lea r1 r1 (inr rv) →
     IsLInt wz z →
     lea_result wr z = Some wr' →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     rv ≠ cnull →
     r1 ≠ cnull →

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
         ▷ pc_a ↦ₐ{dq} w ∗
         ▷ r1 ↦ᵣ wr ∗
         ▷ rv ↦ᵣ wz }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
         pc_a ↦ₐ{dq} w ∗
         rv ↦ᵣ wz ∗
         r1 ↦ᵣ wr' }}}.
   Proof.
     iIntros (Hinstr Hwz Hres Hvpc Hpca' Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ".
     destruct (IsLInt_inv _ _ Hwz) as [πz ->].
     iDestruct (map_of_regs_2 with "Hrv Hr1") as "[Hmap %]".
     iApply (wp_lea_next _ _ _ _ _ _ _ _ _ _ _ _ wr _ wr' with "[$HPC $Hpc_a $Hmap]");
       try solve_next_side; try done.
     iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
   Qed.

   (** [Lea] by an immediate, on any word. *)
   Lemma wp_lea_success_z_any Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 wr wr' z dq :
     decodeInstrW w.(lw) = Lea r1 r1 (inl z) →
     lea_result wr z = Some wr' →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     r1 ≠ cnull →

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
         ▷ pc_a ↦ₐ{dq} w ∗
         ▷ r1 ↦ᵣ wr }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
         pc_a ↦ₐ{dq} w ∗
         r1 ↦ᵣ wr' }}}.
   Proof.
     iIntros (Hinstr Hres Hvpc Hpca' Hcnull ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
     iDestruct (map_of_regs_1 with "Hr1") as "Hmap".
     iApply (wp_lea_next _ _ _ _ _ _ _ _ _ _ _ _ wr _ wr' with "[$HPC $Hpc_a $Hmap]");
       try solve_next_side; try done.
     iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
   Qed.

   (* Register-shaped rules, with a source other than the destination. *)

   Lemma wp_lea_success_reg_src Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst src rv (t : bool) p g b e a wdst wz z a' π dq :
     decodeInstrW w.(lw) = Lea dst src (inr rv) →
     IsLInt wz z →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = Some a' →
     rv ≠ cnull →
     src ≠ cnull →
     dst ≠ cnull →

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
         ▷ pc_a ↦ₐ{dq} w ∗
         ▷ src ↦ᵣ WCap t p g b e a @@? π ∗
         ▷ rv ↦ᵣ wz ∗
         ▷ dst ↦ᵣ wdst }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
         pc_a ↦ₐ{dq} w ∗
         src ↦ᵣ WCap t p g b e a @@? π ∗
         rv ↦ᵣ wz ∗
         dst ↦ᵣ WCap t p g b e a' @@? π }}}.
   Proof.
     iIntros (Hinstr Hwz Hvpc Hpca' Ha' Hcnull Hcnull' Hcnull'' ϕ) "(>HPC & >Hpc_a & >Hsrc & >Hrv & >Hdst) Hφ".
     destruct (IsLInt_inv _ _ Hwz) as [πz ->].
     iDestruct (map_of_regs_3 with "Hsrc Hrv Hdst") as "[Hmap (%&%&%)]".
     iApply (wp_lea_next _ _ _ _ _ _ _ _ _ _ _ _ (WCap t p g b e a @@? π) _
       (WCap t p g b e a' @@? π) with "[$HPC $Hpc_a $Hmap]"); try solve_next_side;
       try by rewrite /lea_result /= Ha'.
     iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
   Qed.

   (** The offset register is the destination. *)
   Lemma wp_lea_success_reg_dst_src Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst src (t : bool) p g b e a wz z a' π dq :
     decodeInstrW w.(lw) = Lea dst src (inr dst) →
     IsLInt wz z →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = Some a' →
     src ≠ cnull →
     dst ≠ cnull →

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
         ▷ pc_a ↦ₐ{dq} w ∗
         ▷ src ↦ᵣ WCap t p g b e a @@? π ∗
         ▷ dst ↦ᵣ wz }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
         pc_a ↦ₐ{dq} w ∗
         src ↦ᵣ WCap t p g b e a @@? π ∗
         dst ↦ᵣ WCap t p g b e a' @@? π }}}.
   Proof.
     iIntros (Hinstr Hwz Hvpc Hpca' Ha' Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hφ".
     destruct (IsLInt_inv _ _ Hwz) as [πz ->].
     iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %]".
     iApply (wp_lea_next _ _ _ _ _ _ _ _ _ _ _ _ (WCap t p g b e a @@? π) _
       (WCap t p g b e a' @@? π) with "[$HPC $Hpc_a $Hmap]"); try solve_next_side;
       try by rewrite /lea_result /= Ha'.
     iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
   Qed.

   Lemma wp_lea_success_z_src Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst src (t : bool) p g b e a wdst z a' π dq :
     decodeInstrW w.(lw) = Lea dst src (inl z) →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = Some a' →
     src ≠ cnull →
     dst ≠ cnull →

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
         ▷ pc_a ↦ₐ{dq} w ∗
         ▷ src ↦ᵣ WCap t p g b e a @@? π ∗
         ▷ dst ↦ᵣ wdst }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
         pc_a ↦ₐ{dq} w ∗
         src ↦ᵣ WCap t p g b e a @@? π ∗
         dst ↦ᵣ WCap t p g b e a' @@? π }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hφ".
     iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %]".
     iApply (wp_lea_next _ _ _ _ _ _ _ _ _ _ _ _ (WCap t p g b e a @@? π) _
       (WCap t p g b e a' @@? π) with "[$HPC $Hpc_a $Hmap]"); try solve_next_side;
       try by rewrite /lea_result /= Ha'.
     iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
   Qed.

   Lemma wp_lea_success_z_int_src Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst src n wdst z π dq :
     decodeInstrW w.(lw) = Lea dst src (inl z) →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     src ≠ cnull →
     dst ≠ cnull →

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
         ▷ pc_a ↦ₐ{dq} w ∗
         ▷ src ↦ᵣ WInt n @@? π ∗
         ▷ dst ↦ᵣ wdst }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
         pc_a ↦ₐ{dq} w ∗
         src ↦ᵣ WInt n @@? π ∗
         dst ↦ᵣ WInt (n + z) @@? π }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hφ".
     iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %]".
     iApply (wp_lea_next _ _ _ _ _ _ _ _ _ _ _ _ (WInt n @@? π) _
       (WInt (n + z) @@? π) with "[$HPC $Hpc_a $Hmap]"); try solve_next_side; try done.
     iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
   Qed.

   Lemma wp_lea_success_reg_any_src Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst src rv wsrc wsrc' wdst wz z dq :
     decodeInstrW w.(lw) = Lea dst src (inr rv) →
     IsLInt wz z →
     lea_result wsrc z = Some wsrc' →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     rv ≠ cnull →
     src ≠ cnull →
     dst ≠ cnull →

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
         ▷ pc_a ↦ₐ{dq} w ∗
         ▷ src ↦ᵣ wsrc ∗
         ▷ rv ↦ᵣ wz ∗
         ▷ dst ↦ᵣ wdst }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
         pc_a ↦ₐ{dq} w ∗
         src ↦ᵣ wsrc ∗
         rv ↦ᵣ wz ∗
         dst ↦ᵣ wsrc' }}}.
   Proof.
     iIntros (Hinstr Hwz Hres Hvpc Hpca' Hcnull Hcnull' Hcnull'' ϕ) "(>HPC & >Hpc_a & >Hsrc & >Hrv & >Hdst) Hφ".
     destruct (IsLInt_inv _ _ Hwz) as [πz ->].
     iDestruct (map_of_regs_3 with "Hsrc Hrv Hdst") as "[Hmap (%&%&%)]".
     iApply (wp_lea_next _ _ _ _ _ _ _ _ _ _ _ _ wsrc _ wsrc' with "[$HPC $Hpc_a $Hmap]");
       try solve_next_side; try done.
     iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
   Qed.

   Lemma wp_lea_success_z_any_src Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst src wsrc wsrc' wdst z dq :
     decodeInstrW w.(lw) = Lea dst src (inl z) →
     lea_result wsrc z = Some wsrc' →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     src ≠ cnull →
     dst ≠ cnull →

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
         ▷ pc_a ↦ₐ{dq} w ∗
         ▷ src ↦ᵣ wsrc ∗
         ▷ dst ↦ᵣ wdst }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
         pc_a ↦ₐ{dq} w ∗
         src ↦ᵣ wsrc ∗
         dst ↦ᵣ wsrc' }}}.
   Proof.
     iIntros (Hinstr Hres Hvpc Hpca' Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hφ".
     iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %]".
     iApply (wp_lea_next _ _ _ _ _ _ _ _ _ _ _ _ wsrc _ wsrc' with "[$HPC $Hpc_a $Hmap]");
       try solve_next_side; try done.
     iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
   Qed.

End griotte_lang_rules.
