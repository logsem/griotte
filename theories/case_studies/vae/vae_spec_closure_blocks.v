From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules logrel interp_weakening.
From griotte Require Import proofmode register_tactics.
From griotte Require Import switcher interp_switcher_call switcher_spec_call.
From griotte Require Import vae vae_helper.

Section VAE_Awkward_Blocks.
  Context
    {Σ : gFunctors}
    {ceriseg : ceriseG Σ} {sealsg : sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP : MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}.

  (** Both calls to the adversary's entry point use this seven arguments registers. *)
  Definition vae_call_adv_arg_rmap : Reg :=
    {[ ca0 := WInt 0;
       ca1 := WInt 0;
       ca2 := WInt 0;
       ca3 := WInt 0;
       ca4 := WInt 0;
       ca5 := WInt 0;
       ct0 := WSentry XSRW_ Local
         b_switcher e_switcher a_switcher_call ]}.

  Lemma vae_call_adv_arg_rmap_is_arg :
    is_arg_rmap vae_call_adv_arg_rmap 8.
  Proof. by rewrite /is_arg_rmap /vae_call_adv_arg_rmap. Qed.

  (** Intermediate lemma about the argument registers *)
  Lemma vae_call_adv_arg_rmap_resources
      (W : WORLD) (C : CmptName) (Nswitcher : namespace) :
    na_inv cerise_nais Nswitcher switcher_inv
    ∗ ca0 ↦ᵣ WInt 0
    ∗ ca1 ↦ᵣ WInt 0
    ∗ ca2 ↦ᵣ WInt 0
    ∗ ca3 ↦ᵣ WInt 0
    ∗ ca4 ↦ᵣ WInt 0
    ∗ ca5 ↦ᵣ WInt 0
    ∗ ct0 ↦ᵣ WSentry XSRW_ Local b_switcher e_switcher a_switcher_call
    -∗ [∗ map] rarg ↦ warg ∈ vae_call_adv_arg_rmap, rarg ↦ᵣ warg ∗ interp W C warg.
  Proof.
    iIntros "(#Hswitcher & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & Hct0)".
    iAssert (interp W C (WInt 0)) as "#Hint".
    { iApply interp_int. }
    iAssert (interp W C (WSentry XSRW_ Local
      b_switcher e_switcher a_switcher_call)) as "#Hcall".
    { iApply (interp_switcher_call with "Hswitcher"). }
    rewrite /vae_call_adv_arg_rmap.
    repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
    done.
  Qed.

  (** Store the flag and update the matching custom-world location
      while the invariant is open. *)
  Lemma vae_awkward_store_flag_spec
      (W : WORLD) (C : CmptName) (i : positive)
      (new : bool) (awkN : namespace)
      pc_b pc_e pc_a cgp_b cgp_e (tail : list instr) :
    let W' := <l[i:=new]l>W in
    let z := if new then 1%Z else 0%Z in
    SubBounds pc_b pc_e pc_a (pc_a ^+ 1)%a ->
    ContiguousRegion pc_a 1 ->
    (cgp_b < cgp_e)%a ->
    related_sts_priv_world W W' ->
    revoke_condition W ->
    (exists old : bool, loc W !! i = Some (encode old)) ->
    wrel W !! i =
      Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->

    inv awkN (awk_inv C i cgp_b)
    ∗ sts_rel_loc (A := Addr) C i awk_rel_pub awk_rel_priv
    ∗ world_interp W C
    ∗ PC ↦ᵣ WCap RX Global pc_b pc_e pc_a
    ∗ cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b
    ∗ codefrag pc_a (encodeInstrsW (Store cgp z :: tail))

    ∗ ▷ (world_interp W' C
        ∗ PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ 1)%a
        ∗ cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b
        ∗ codefrag pc_a (encodeInstrsW (Store cgp z :: tail))
        -∗ WP Seq (Instr Executable)
          {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros W' z Hsub Hcont1 Hcgp_bounds Hrelated Hrevoke Hloc Hrel.
    subst W' z.
    iIntros "(#Hawk & #Hsts & Hworld & HPC & Hcgp & Hcode & Hpost)".
    codefrag_facts "Hcode".
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iMod (inv_acc with "Hawk") as "(>(%old & Hst & Hflag) & Hclose)"; auto.
    iAssert (cgp_b ↦ₐ (if old then WInt 1 else WInt 0))%I
      with "[Hflag]" as "Hflag".
    { destruct old; iFrame. }
    destruct new; cbn.
    - iApply (wp_store_success_z with "[$HPC $Hi $Hcgp $Hflag]");
        try solve_pure.
      { apply withinBounds_true_iff; solve_addr+Hcgp_bounds. }
      iIntros "!> (HPC & Hi & Hcgp & Hflag)".
      iDestruct (world_interp_loc_valid with "Hworld Hst") as %Hst.
      iDestruct (world_interp_update_loc _ _ _ _ true with "Hworld Hst")
        as ">[Hworld Hst]"; [done|done|].
      iMod ("Hclose" with "[$Hst $Hflag]") as "_".
      iModIntro; wp_pure; iSpecialize ("Hcode" with "[$Hi]").
      iApply "Hpost"; iFrame.
    - iApply (wp_store_success_z with "[$HPC $Hi $Hcgp $Hflag]");
        try solve_pure.
      { apply withinBounds_true_iff; solve_addr+Hcgp_bounds. }
      iIntros "!> (HPC & Hi & Hcgp & Hflag)".
      iDestruct (world_interp_loc_valid with "Hworld Hst") as %Hst.
      iDestruct (world_interp_update_loc _ _ _ _ false with "Hworld Hst")
        as ">[Hworld Hst]"; [done|done|].
      iMod ("Hclose" with "[$Hst $Hflag]") as "_".
      iModIntro; wp_pure; iSpecialize ("Hcode" with "[$Hi]").
      iApply "Hpost"; iFrame.
  Qed.

  (** Prepare the first adversary call, preserving the callback in both
      [cs1] and [ct1] for the post-call restoration. *)
  Lemma vae_awkward_call1_prep_spec
      pc_b pc_e pc_a
      (wra wcallback wcs0 wcs1 wct1 : Word) :
    let instrs := encodeInstrsW [
      Mov cs0 cra; Mov cs1 ca0; Mov ct1 ca0; Mov ca0 0; Jalr cra ct0] in
    let len := length instrs in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len)%a ->

    PC ↦ᵣ WCap RX Global pc_b pc_e pc_a
    ∗ cra ↦ᵣ wra
    ∗ ca0 ↦ᵣ wcallback
    ∗ ct0 ↦ᵣ WSentry XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ ct1 ↦ᵣ wct1
    ∗ cs0 ↦ᵣ wcs0
    ∗ cs1 ↦ᵣ wcs1
    ∗ codefrag pc_a instrs

    ∗ ▷ (PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call
        ∗ cra ↦ᵣ WSentry RX Global pc_b pc_e (pc_a ^+ len)%a
        ∗ ca0 ↦ᵣ WInt 0
        ∗ ct0 ↦ᵣ WSentry XSRW_ Local b_switcher e_switcher a_switcher_call
        ∗ ct1 ↦ᵣ wcallback
        ∗ cs0 ↦ᵣ wra
        ∗ cs1 ↦ᵣ wcallback
        ∗ codefrag pc_a instrs
        -∗ WP Seq (Instr Executable)
          {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros instrs len Hsub. subst instrs len.
    iIntros "(HPC & Hcra & Hca0 & Hct0 & Hct1 & Hcs0 & Hcs1 & Hcode & Hpost)".
    codefrag_facts "Hcode". try clear H0.
    (* --- Mov cs0 cra --- *)
    iInstr "Hcode".
    (* --- Mov cs1 ca0 --- *)
    iInstr "Hcode".
    (* --- Mov ct1 ca0 --- *)
    iInstr "Hcode".
    (* --- Mov ca0 0 --- *)
    iInstr "Hcode".
    (* --- Jalr cra ct0 --- *)
    iInstr "Hcode".
    iApply "Hpost"; iFrame.
  Qed.

  (** The second call has no callback to preserve, so its preparation block
      exposes only the registers used by the switcher call contract. *)
  Lemma vae_awkward_call2_prep_spec
      pc_b pc_e pc_a (wra wca0 wca1 wcs0 : Word) (tail : list instr) :
    let prefix := [Mov cs0 cra; Mov ca0 0; Mov ca1 0; Jalr cra ct0] in
    let instrs := encodeInstrsW (prefix ++ tail) in
    let len := length (encodeInstrsW prefix) in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len)%a ->
    ContiguousRegion pc_a len ->

    PC ↦ᵣ WCap RX Global pc_b pc_e pc_a
    ∗ cra ↦ᵣ wra
    ∗ ca0 ↦ᵣ wca0
    ∗ ca1 ↦ᵣ wca1
    ∗ ct0 ↦ᵣ WSentry XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cs0 ↦ᵣ wcs0
    ∗ codefrag pc_a instrs

    ∗ ▷ (PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call
        ∗ cra ↦ᵣ WSentry RX Global pc_b pc_e (pc_a ^+ len)%a
        ∗ ca0 ↦ᵣ WInt 0
        ∗ ca1 ↦ᵣ WInt 0
        ∗ ct0 ↦ᵣ WSentry XSRW_ Local b_switcher e_switcher a_switcher_call
        ∗ cs0 ↦ᵣ wra
        ∗ codefrag pc_a instrs
        -∗ WP Seq (Instr Executable)
          {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros prefix instrs len Hsub Hcont. subst prefix instrs len.
    iIntros "(HPC & Hcra & Hca0 & Hca1 & Hct0 & Hcs0 & Hcode & Hpost)".
    codefrag_facts "Hcode".
    (* --- Mov cs0 cra --- *)
    iInstr "Hcode".
    (* --- Mov ca0 0 --- *)
    iInstr "Hcode".
    (* --- Mov ca1 0 --- *)
    iInstr "Hcode".
    (* --- Jalr cra ct0 --- *)
    iInstr "Hcode".
    iApply "Hpost"; iFrame.
  Qed.

  (** Load the publicly stable true flag and prepare the assertion operands. *)
  Lemma vae_awkward_flag_load_spec
      (Wtrue Wbase : WORLD) (C : CmptName) (i : positive)
      (awkN : namespace) pc_b pc_e pc_code cgp_b cgp_e
      (wct0 wct1 : Word) :
    SubBounds pc_b pc_e pc_code (pc_code ^+ 6)%a ->
    (cgp_b < cgp_e)%a ->
    related_sts_pub_world Wtrue Wbase ->
    loc Wtrue !! i = Some (encode true) ->
    wrel Wtrue !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->

    inv awkN (awk_inv C i cgp_b)
    ∗ sts_rel_loc (A := Addr) C i awk_rel_pub awk_rel_priv
    ∗ world_interp (revoke Wbase) C
    ∗ PC ↦ᵣ WCap RX Global pc_b pc_e (pc_code ^+ 4)%a
    ∗ cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b
    ∗ ct0 ↦ᵣ wct0
    ∗ ct1 ↦ᵣ wct1
    ∗ codefrag pc_code (encodeInstrsW [
        Mov cs0 cra; Mov ca0 0; Mov ca1 0; Jalr cra ct0;
        Load ct0 cgp; Mov ct1 1])

    ∗ ▷ (world_interp (revoke Wbase) C
        ∗ PC ↦ᵣ WCap RX Global pc_b pc_e (pc_code ^+ 6)%a
        ∗ cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b
        ∗ ct0 ↦ᵣ WInt 1
        ∗ ct1 ↦ᵣ WInt 1
        ∗ codefrag pc_code (encodeInstrsW [
            Mov cs0 cra; Mov ca0 0; Mov ca1 0; Jalr cra ct0;
            Load ct0 cgp; Mov ct1 1])
        -∗ WP Seq (Instr Executable)
          {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hsub Hcgp_bounds Hrelated Htrue Hrel)
      "(#Hawk & #Hsts & Hworld & HPC & Hcgp & Hct0 & Hct1 & Hcode & Hpost)".
    codefrag_facts "Hcode". try clear H0.
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iMod (inv_acc with "Hawk") as "(>(%b & Hst & Hflag) & Hclose)"; auto.
    iDestruct (world_interp_loc_valid with "Hworld Hst") as %Hloc.
    change (loc Wbase !! i = Some (encode b)) in Hloc.
    pose proof (awk_loc_true_mono_pub Wtrue Wbase i Hrelated Htrue Hrel) as Hnow.
    rewrite Hloc in Hnow; simplify_eq.
    iApply (wp_load_success_alt with "[$HPC $Hi $Hct0 $Hcgp $Hflag]");
      try solve_pure.
    { split; last apply withinBounds_true_iff; solve_addr+Hcgp_bounds. }
    iIntros "!> (HPC & Hct0 & Hi & Hcgp & Hflag)".
    iMod ("Hclose" with "[$Hst $Hflag]") as "_".
    iModIntro; wp_pure; iSpecialize ("Hcode" with "[$]").
    iEval (cbn) in "Hct0".
    (* --- Mov ct1 1 --- *)
    iInstr "Hcode".
    iApply "Hpost"; iFrame.
  Qed.

  (** Restore the saved return sentry, clear argument registers, and jump to
      the switcher return protocol. *)
  Lemma vae_awkward_return_prep_spec
      pc_b pc_e pc_a (wret wcra wca0 wca1 : Word) :
    let instrs := encodeInstrsW [
      Mov cra cs0; Mov ca0 0; Mov ca1 0; Jalr cnull cra] in
    let len := length instrs in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len)%a ->

    PC ↦ᵣ WCap RX Global pc_b pc_e pc_a
    ∗ cra ↦ᵣ wcra
    ∗ cs0 ↦ᵣ wret
    ∗ ca0 ↦ᵣ wca0
    ∗ ca1 ↦ᵣ wca1
    ∗ cnull ↦ᵣ WInt 0
    ∗ codefrag pc_a instrs

    ∗ ▷ (PC ↦ᵣ updatePcPerm wret
        ∗ cra ↦ᵣ wret
        ∗ cs0 ↦ᵣ wret
        ∗ ca0 ↦ᵣ WInt 0
        ∗ ca1 ↦ᵣ WInt 0
        ∗ cnull ↦ᵣ WInt 0
        ∗ codefrag pc_a instrs
        -∗ WP Seq (Instr Executable)
          {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros instrs len Hsub. subst instrs len.
    iIntros "(HPC & Hcra & Hcs0 & Hca0 & Hca1 & Hcnull & Hcode & Hpost)".
    codefrag_facts "Hcode". try clear H0.
    (* --- Mov cra cs0 --- *)
    iInstr "Hcode".
    (* --- Mov ca0 0 --- *)
    iInstr "Hcode".
    (* --- Mov ca1 0 --- *)
    iInstr "Hcode".
    (* --- Jalr cnull cra --- *)
    iInstr "Hcode".
    iApply "Hpost"; iFrame.
  Qed.

End VAE_Awkward_Blocks.
