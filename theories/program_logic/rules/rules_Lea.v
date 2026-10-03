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

  Inductive Lea_failure (regs : LReg) (r1: RegName) (rv: Z + RegName) :=
  | Lea_fail_rv_nonconst :
     lz_of_argument regs rv = None ->
     Lea_failure regs r1 rv
  | Lea_fail_allowed : forall w,
     regs !!ₗ r1 = Some w ->
     is_mutable_range w.(lw) = false →
     Lea_failure regs r1 rv
  | Lea_fail_overflow_cap : forall (t : bool) p g b e a π z,
     regs !!ₗ r1 = Some (WCap t p g b e a @@? π) ->
     lz_of_argument regs rv = Some z ->
     (a + z)%a = None ->
     incrementPC (<[ r1 := WCap false p g b e a @@? π ]ₗ> regs) = None ->
     Lea_failure regs r1 rv
  | Lea_fail_overflow_PC_cap : forall (t : bool) p g b e a π z a',
     regs !!ₗ r1 = Some (WCap t p g b e a @@? π) ->
     lz_of_argument regs rv = Some z ->
     (a + z)%a = Some a' ->
     incrementPC (<[ r1 := WCap t p g b e a' @@? π ]ₗ> regs) = None ->
     Lea_failure regs r1 rv
  | Lea_fail_overflow_sr : forall (t : bool) p g b e a π z,
     regs !!ₗ r1 = Some (WSealRange t p g b e a @@? π) ->
     lz_of_argument regs rv = Some z ->
     (a + z)%ot = None ->
     incrementPC (<[ r1 := WSealRange false p g b e a @@? π ]ₗ> regs) = None ->
     Lea_failure regs r1 rv
  | Lea_fail_overflow_PC_sr : forall (t : bool) p g b e a π z a',
     regs !!ₗ r1 = Some (WSealRange t p g b e a @@? π) ->
     lz_of_argument regs rv = Some z ->
     (a + z)%ot = Some a' ->
     incrementPC (<[ r1 := WSealRange t p g b e a' @@? π ]ₗ> regs) = None ->
     Lea_failure regs r1 rv
  .

  Inductive Lea_spec
    (regs : LReg) (r1: RegName) (rv: Z + RegName)
    (regs' : LReg) : griotte_lang.val → Prop
  :=
  | Lea_spec_success_cap: forall (t : bool) p g b e a π z a',
    regs !!ₗ r1 = Some (WCap t p g b e a @@? π) ->
    lz_of_argument regs rv = Some z ->
    (a + z)%a = Some a' ->
    incrementPC
      (<[ r1 := WCap t p g b e a' @@? π ]ₗ> regs) = Some regs' ->
    Lea_spec regs r1 rv regs' NextIV
  | Lea_spec_success_sr: forall (t : bool) p g b e a π z a',
    regs !!ₗ r1 = Some (WSealRange t p g b e a @@? π) ->
    lz_of_argument regs rv = Some z ->
    (a + z)%ot = Some a' ->
    incrementPC
      (<[ r1 := WSealRange t p g b e a' @@? π ]ₗ> regs) = Some regs' ->
    Lea_spec regs r1 rv regs' NextIV
  | Lea_spec_invalidated_cap: forall (t : bool) p g b e a π z,
    regs !!ₗ r1 = Some (WCap t p g b e a @@? π) ->
    lz_of_argument regs rv = Some z ->
    (a + z)%a = None ->
    incrementPC
      (<[ r1 := WCap false p g b e a @@? π ]ₗ> regs) = Some regs' ->
    Lea_spec regs r1 rv regs' NextIV
  | Lea_spec_invalidated_sr: forall (t : bool) p g b e a π z,
    regs !!ₗ r1 = Some (WSealRange t p g b e a @@? π) ->
    lz_of_argument regs rv = Some z ->
    (a + z)%ot = None ->
    incrementPC
      (<[ r1 := WSealRange false p g b e a @@? π ]ₗ> regs) = Some regs' ->
    Lea_spec regs r1 rv regs' NextIV
  | Lea_spec_failure :
    Lea_failure regs r1 rv ->
    Lea_spec regs r1 rv regs' FailedV.

   Lemma wp_lea Ep pc_p pc_g pc_b pc_e pc_a pc_π r1 w arg (regs : LReg) :
     decodeInstrW w.(lw) = Lea r1 arg →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
     regs_of (Lea r1 arg) ⊆ dom regs →
     {{{ ▷ pc_a ↦ₐ w ∗
         ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
       Instr Executable @ Ep
     {{{ regs' retv, RET retv;
         ⌜ Lea_spec regs r1 arg regs' retv ⌝ ∗
         pc_a ↦ₐ w ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
   Proof.
     iIntros (Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
     iApply (wp_instr_step with "Hpc_a Hmap"); eauto.
     iNext. iIntros (r sr m st lreg lmem R C c σ' Her Hlregs Hregs Hpc_a Hstep)
       "Hr Hsr Hm Hst HR HC Hpc_a Hmap".
     rewrite Hinstr in Hstep.
     specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri.
     unfold regs_of in Hri, Dregs.
     destruct (Hri r1) as [r1v [H'r1 _]]; first by set_solver+.
     pose proof (llookup_reg_incl _ _ _ _ Hregs H'r1) as Hr1.
     pose proof (erasure_llookup_reg_word _ _ _ _ _ _ _ _ Her Hlregs H'r1) as Hok.
     rewrite /exec /= Hr1 /= in Hstep.
     destruct (lz_of_argument regs arg) as [argz|] eqn:Harg.
     2: { rewrite (lz_of_argument_None regs r) /= in Hstep; [|done| |done].
          2: { intros x ->. apply Dregs. set_solver+. }
          simplify_eq. iApply (instr_close_fail with "Hr Hsr Hm Hst HR HC Hmap"); first done.
          iIntros "Hmap". iApply "Hφ". iFrame. iPureIntro.
          constructor. by constructor. }
     rewrite (lz_of_argument_incl regs r _ argz) /= in Hstep; [|done|done].
     destruct r1v as [[ | [t p g b e a | t p g b e a] | | ] π]; cbn in Hstep.
     1,4,5: (simplify_eq; iApply (instr_close_fail with "Hr Hsr Hm Hst HR HC Hmap"); first done;
             iIntros "Hmap"; iApply "Hφ"; iFrame; iPureIntro;
             constructor; eapply Lea_fail_allowed; eauto).
     - destruct (a + argz)%a as [a'|] eqn:Hoffset; cbn in Hstep.
       + iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ r1 (WCap t p g b e a' @@? π) _ _ _
           (λ regs' retv, Lea_spec regs r1 arg regs' retv)
           with "Hr Hsr Hm Hst HR HC Hmap [Hφ Hpc_a]").
         { exact Her. } { exact Hlregs. } { apply Dregs. set_solver+. } { by eexists. }
         { eapply (reg_word_ok_derive _ _ (WCap t p g b e a @@? π)); [by left|done|done]. }
         { exact Hstep. }
         { intros regs' Hi. eapply Lea_spec_success_cap; eauto. }
         { intros Hi. constructor. eapply Lea_fail_overflow_PC_cap; eauto. }
         iIntros (regs' retv Hspec) "Hmap". iApply "Hφ". by iFrame.
       + iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ r1 (WCap false p g b e a @@? π) _ _ _
           (λ regs' retv, Lea_spec regs r1 arg regs' retv)
           with "Hr Hsr Hm Hst HR HC Hmap [Hφ Hpc_a]").
         { exact Her. } { exact Hlregs. } { apply Dregs. set_solver+. } { by eexists. }
         { eapply (reg_word_ok_derive _ _ (WCap t p g b e a @@? π)); [by left|done|done]. }
         { exact Hstep. }
         { intros regs' Hi. eapply Lea_spec_invalidated_cap; eauto. }
         { intros Hi. constructor. eapply Lea_fail_overflow_cap; eauto. }
         iIntros (regs' retv Hspec) "Hmap". iApply "Hφ". by iFrame.
     - destruct (a + argz)%ot as [a'|] eqn:Hoffset; cbn in Hstep.
       + iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ r1 (WSealRange t p g b e a' @@? π) _ _ _
           (λ regs' retv, Lea_spec regs r1 arg regs' retv)
           with "Hr Hsr Hm Hst HR HC Hmap [Hφ Hpc_a]").
         { exact Her. } { exact Hlregs. } { apply Dregs. set_solver+. } { by eexists. }
         { eapply (reg_word_ok_derive _ _ (WSealRange t p g b e a @@? π)); [by right|done|done]. }
         { exact Hstep. }
         { intros regs' Hi. eapply Lea_spec_success_sr; eauto. }
         { intros Hi. constructor. eapply Lea_fail_overflow_PC_sr; eauto. }
         iIntros (regs' retv Hspec) "Hmap". iApply "Hφ". by iFrame.
       + iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ r1 (WSealRange false p g b e a @@? π) _ _ _
           (λ regs' retv, Lea_spec regs r1 arg regs' retv)
           with "Hr Hsr Hm Hst HR HC Hmap [Hφ Hpc_a]").
         { exact Her. } { exact Hlregs. } { apply Dregs. set_solver+. } { by eexists. }
         { eapply (reg_word_ok_derive _ _ (WSealRange t p g b e a @@? π)); [by right|done|done]. }
         { exact Hstep. }
         { intros regs' Hi. eapply Lea_spec_invalidated_sr; eauto. }
         { intros Hi. constructor. eapply Lea_fail_overflow_sr; eauto. }
         iIntros (regs' retv Hspec) "Hmap". iApply "Hφ". by iFrame.
   Qed.

   Lemma wp_lea_success_reg_PC Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w rv z a' :
     decodeInstrW w.(lw) = Lea PC (inr rv) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (a' + 1)%a = Some pc_a' →
     (pc_a + z)%a = Some a' →
     rv ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ rv ↦ᵣ WInt z }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ w
              ∗ rv ↦ᵣ WInt z }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' Hcnull φ) "(>HPC & >Hpc_a & >Hrv) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hrv") as "[Hmap %]".
     iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | | | | * Hfail ].
     3,4: by simplify_lmap_eq.
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
       rewrite !insert_insert_eq. (* TODO: add to simplify_lmap_eq via simpl_map? *)
       iApply (regs_of_map_2 with "Hmap"); eauto. }
     { (* Success with WSealRange (contradiction) *)
       simplify_lmap_eq. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto.
       all: try destruct pc_p; cbn in * ; congruence. }
    Unshelve. all: auto.
   Qed.

   Lemma wp_lea_success_reg Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 rv (t : bool) p g b e a z a' π :
     decodeInstrW w.(lw) = Lea r1 (inr rv) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = Some a' →
     rv ≠ cnull ->
     r1 ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ r1 ↦ᵣ WCap t p g b e a @@? π
           ∗ ▷ rv ↦ᵣ WInt z }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ w
              ∗ rv ↦ᵣ WInt z
              ∗ r1 ↦ᵣ WCap t p g b e a' @@? π }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ".
     iDestruct (map_of_regs_3 with "HPC Hrv Hr1") as "[Hmap (%&%&%)]".
     iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | | | | * Hfail ].
     3,4: by simplify_lmap_eq.
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
       (* FIXME: tedious *)
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq.
       rewrite (insert_insert_ne _ r1 PC) // (insert_insert_ne _ r1 rv) // insert_insert_eq.
       iApply (regs_of_map_3 with "Hmap"); eauto. }
     { (* Success with WSealRange (contradiction) *)
       simplify_lmap_eq. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto.
       all: try destruct p; cbn in * ; congruence. }
    Unshelve. all: auto.
   Qed.

   Lemma wp_lea_success_z_PC Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w z a' :
     decodeInstrW w.(lw) = Lea PC (inl z) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (a' + 1)%a = Some pc_a' →
     (pc_a + z)%a = Some a' →

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ w }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
            ∗ pc_a ↦ₐ w }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' ϕ) "(>HPC & >Hpc_a) Hφ".
     iDestruct (map_of_regs_1 with "HPC") as "Hmap".
     iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | | | | * Hfail ].
     3,4: by simplify_lmap_eq.
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
       rewrite !insert_insert_eq. iApply (regs_of_map_1 with "Hmap"); eauto. }
     { (* Success with WSealRange (contradiction) *)
       simplify_lmap_eq. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto.
       all: try destruct pc_p; cbn in * ; congruence. }
     Unshelve. all: auto.
   Qed.

   Lemma wp_lea_success_z Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 (t : bool) p g b e a z a' π :
     decodeInstrW w.(lw) = Lea r1 (inl z) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = Some a' →
     r1 ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ r1 ↦ᵣ WCap t p g b e a @@? π }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
            ∗ pc_a ↦ₐ w
            ∗ r1 ↦ᵣ WCap t p g b e a' @@? π }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' Hcnull ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
     iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | | | | * Hfail ].
     3,4: by simplify_lmap_eq.
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
       (* FIXME: tedious *)
       rewrite insert_insert_ne // insert_insert_eq insert_insert_ne // insert_insert_eq.
       iDestruct (regs_of_map_2 with "Hmap") as "[? ?]"; eauto. iFrame. }
     { (* Success with WSealRange (contradiction) *)
       simplify_lmap_eq. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto.
       all: try destruct p; cbn in * ; congruence. }
     Unshelve. all:auto.
   Qed.

   (* Similar rules in case we have a SealRange instead of a capability, where some cases are impossible, because a SealRange is not a valid PC *)

   Lemma wp_lea_success_reg_sr Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 rv (t : bool) p g b e a z a' π :
     decodeInstrW w.(lw) = Lea r1 (inr rv) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%ot = Some a' →
     rv ≠ cnull ->
     r1 ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? π
           ∗ ▷ rv ↦ᵣ WInt z }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ w
              ∗ rv ↦ᵣ WInt z
              ∗ r1 ↦ᵣ WSealRange t p g b e a' @@? π }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ".
     iDestruct (map_of_regs_3 with "HPC Hrv Hr1") as "[Hmap (%&%&%)]".
     iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | | | | * Hfail ].
     3,4: by simplify_lmap_eq.
     { (* Success with WSealCap (contradiction) *)
       simplify_lmap_eq. }
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
       (* FIXME: tedious *)
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq.
       rewrite (insert_insert_ne _ r1 PC) // (insert_insert_ne _ r1 rv) // insert_insert_eq.
       iApply (regs_of_map_3 with "Hmap"); eauto. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto.
       congruence.
     }
    Unshelve. all: auto.
   Qed.

  Lemma wp_lea_success_z_sr Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 (t : bool) p g b e a z a' π :
     decodeInstrW w.(lw) = Lea r1 (inl z) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%ot = Some a' →
     r1 ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? π }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
            ∗ pc_a ↦ₐ w
            ∗ r1 ↦ᵣ WSealRange t p g b e a' @@? π }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' Hcnull ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
     iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | | | | * Hfail ].
     3,4: by simplify_lmap_eq.
     { (* Success with WSealRange (contradiction) *)
       simplify_lmap_eq. }
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
       (* FIXME: tedious *)
       rewrite insert_insert_ne // insert_insert_eq insert_insert_ne // insert_insert_eq.
       iDestruct (regs_of_map_2 with "Hmap") as "[? ?]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto.
       congruence.
     }
     Unshelve. all:auto.
   Qed.

   Lemma wp_lea_overflow_reg_PC Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w rv z :
     decodeInstrW w.(lw) = Lea PC (inr rv) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (pc_a + z)%a = None →
     rv ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ rv ↦ᵣ WInt z }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ᵣ WCap false pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ w
              ∗ rv ↦ᵣ WInt z }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' Hcnull φ) "(>HPC & >Hpc_a & >Hrv) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hrv") as "[Hmap %]".
     iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | | | | * Hfail ].
     1,2,4: by simplify_lmap_eq.
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
       rewrite !insert_insert_eq. (* TODO: add to simplify_lmap_eq via simpl_map? *)
       iApply (regs_of_map_2 with "Hmap"); eauto. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto.
       all: try destruct pc_p; cbn in * ; congruence. }
    Unshelve. all: auto.
   Qed.

   Lemma wp_lea_overflow_reg Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 rv (t : bool) p g b e a z π :
     decodeInstrW w.(lw) = Lea r1 (inr rv) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = None →
     rv ≠ cnull ->
     r1 ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ r1 ↦ᵣ WCap t p g b e a @@? π
           ∗ ▷ rv ↦ᵣ WInt z }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ w
              ∗ rv ↦ᵣ WInt z
              ∗ r1 ↦ᵣ WCap false p g b e a @@? π }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ".
     iDestruct (map_of_regs_3 with "HPC Hrv Hr1") as "[Hmap (%&%&%)]".
     iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | | | | * Hfail ].
     1,2,4: by simplify_lmap_eq.
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
       (* FIXME: tedious *)
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq.
       rewrite (insert_insert_ne _ r1 PC) // (insert_insert_ne _ r1 rv) // insert_insert_eq.
       iApply (regs_of_map_3 with "Hmap"); eauto. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto.
       all: try destruct p; cbn in * ; congruence. }
    Unshelve. all: auto.
   Qed.

   Lemma wp_lea_overflow_z_PC Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w z :
     decodeInstrW w.(lw) = Lea PC (inl z) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (pc_a + z)%a = None →

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ w }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ᵣ WCap false pc_p pc_g pc_b pc_e pc_a' @@? pc_π
            ∗ pc_a ↦ₐ w }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' ϕ) "(>HPC & >Hpc_a) Hφ".
     iDestruct (map_of_regs_1 with "HPC") as "Hmap".
     iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | | | | * Hfail ].
     1,2,4: by simplify_lmap_eq.
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
       rewrite !insert_insert_eq. iApply (regs_of_map_1 with "Hmap"); eauto. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto.
       all: try destruct pc_p; cbn in * ; congruence. }
     Unshelve. all: auto.
   Qed.

   Lemma wp_lea_overflow_z Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 (t : bool) p g b e a z π :
     decodeInstrW w.(lw) = Lea r1 (inl z) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = None →
     r1 ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ r1 ↦ᵣ WCap t p g b e a @@? π }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
            ∗ pc_a ↦ₐ w
            ∗ r1 ↦ᵣ WCap false p g b e a @@? π }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' Hcnull ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
     iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | | | | * Hfail ].
     1,2,4: by simplify_lmap_eq.
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
       (* FIXME: tedious *)
       rewrite insert_insert_ne // insert_insert_eq insert_insert_ne // insert_insert_eq.
       iDestruct (regs_of_map_2 with "Hmap") as "[? ?]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto.
       all: try destruct p; cbn in * ; congruence. }
     Unshelve. all:auto.
   Qed.

   Lemma wp_lea_overflow_reg_sr Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 rv (t : bool) p g b e a z π :
     decodeInstrW w.(lw) = Lea r1 (inr rv) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%ot = None →
     rv ≠ cnull ->
     r1 ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? π
           ∗ ▷ rv ↦ᵣ WInt z }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
              ∗ pc_a ↦ₐ w
              ∗ rv ↦ᵣ WInt z
              ∗ r1 ↦ᵣ WSealRange false p g b e a @@? π }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ".
     iDestruct (map_of_regs_3 with "HPC Hrv Hr1") as "[Hmap (%&%&%)]".
     iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | | | | * Hfail ].
     1,2,3: by simplify_lmap_eq.
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
       (* FIXME: tedious *)
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq.
       rewrite (insert_insert_ne _ r1 PC) // (insert_insert_ne _ r1 rv) // insert_insert_eq.
       iApply (regs_of_map_3 with "Hmap"); eauto. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto.
       congruence.
     }
    Unshelve. all: auto.
   Qed.

   Lemma wp_lea_overflow_z_sr Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 (t : bool) p g b e a z π :
     decodeInstrW w.(lw) = Lea r1 (inl z) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%ot = None →
     r1 ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? π }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
            ∗ pc_a ↦ₐ w
            ∗ r1 ↦ᵣ WSealRange false p g b e a @@? π }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Ha' Hcnull ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
     iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | | | | * Hfail ].
     1,2,3: by simplify_lmap_eq.
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
       (* FIXME: tedious *)
       rewrite insert_insert_ne // insert_insert_eq insert_insert_ne // insert_insert_eq.
       iDestruct (regs_of_map_2 with "Hmap") as "[? ?]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto.
       congruence.
     }
     Unshelve. all:auto.
   Qed.

   Lemma wp_Lea_fail_integer Ep pc_p pc_g pc_b pc_e pc_a pc_π w r1 z z' :
     decodeInstrW w.(lw) = Lea r1 (inl z) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
         ∗ ▷ pc_a ↦ₐ w
         ∗ ▷ r1 ↦ᵣ WInt z'
     }}}
       Instr Executable @ Ep
       {{{ RET FailedV; True }}}.
   Proof.
     iIntros (Hdecode Hvpc φ) "(>HPC & >Hpc_a & >Hsrc) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hsrc") as "[Hmap %]".
     iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
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
