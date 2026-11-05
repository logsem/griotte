From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode.
From griotte Require Import logrel rules assembler fetch.
From griotte Require Import switcher kvs locks locks_spec wp_core_full.
From griotte Require Export kvs_preamble.

(** * The lock of the KVS: [acquire()], the table, [release()]

    The macros of [kvs_acquire_asm], [kvs_table_asm] and [kvs_release_asm],
    assembled, with their specifications. *)

Section KVS_acquire_code.
  Import Asm_Griotte.
  Context `{MP: MachineParameters}.

  (** The index of the fetch of [try_lock] in [acquire()]. *)
  Definition kvs_acquire_fetch_at : nat := 6.

  (** The assembled [acquire()], where [off] is the resolved offset of the
      sentry of [try_lock] from the address of the fetch. *)
  Definition kvs_acquire (off : Z) : list instr :=
    [ machine_instructions.Mov cs1 (inr cgp);
      machine_instructions.Lea cs1 cs1 (inl KVS_LOCK_OFFSET);
      machine_instructions.GetA ct0 cs1;
      machine_instructions.Add ct1 (inr ct0) (inl 1%Z);
      machine_instructions.Subseg cs1 cs1 (inr ct0) (inr ct1);
      machine_instructions.Mov ct0 (inr cs1) ] ++
    fetch off ct1 ++
    [ machine_instructions.Mov ct2 (inr cra);
      machine_instructions.Jalr cra ct1;
      machine_instructions.Mov cra (inr ct2);
      machine_instructions.Jeq (inl 3%Z) (inr ct0) (inl 0%Z);
      machine_instructions.Ecall;
      machine_instructions.Jmp (inl (-8)%Z);
      machine_instructions.Mov ct2 (inl 0%Z);
      machine_instructions.Mov cs0 (inr cs1);
      machine_instructions.Mov cs1 (inl 0%Z) ].
  Definition kvs_acquire_instrs (off : Z) : list Word :=
    encodeInstrsW (kvs_acquire off).

  (** The offsets of the fetches of [try_lock], from the address of the
      fetch in the blocks [.L<entry>_acquire]. *)
  Definition kvs_addOrUpdate_acquire_off : Z :=
    Eval vm_compute in
      (label_offset_from (concat kvs_service_asm) ".LaddOrUpdate_acquire" ".Limport_try_lock"
       - kvs_acquire_fetch_at)%Z.
  Definition kvs_read_acquire_off : Z :=
    Eval vm_compute in
      (label_offset_from (concat kvs_service_asm) ".Lread_acquire" ".Limport_try_lock"
       - kvs_acquire_fetch_at)%Z.
  Definition kvs_erase_acquire_off : Z :=
    Eval vm_compute in
      (label_offset_from (concat kvs_service_asm) ".Lerase_acquire" ".Limport_try_lock"
       - kvs_acquire_fetch_at)%Z.

  (** The blocks [.L<entry>_acquire] of the assembled service. *)
  Lemma kvs_addOrUpdate_acquire_block :
    nth 4 assembled_kvs_addOrUpdate [] = kvs_acquire kvs_addOrUpdate_acquire_off.
  Proof. vm_compute. reflexivity. Qed.
  Lemma kvs_read_acquire_block :
    nth 4 assembled_kvs_read [] = kvs_acquire kvs_read_acquire_off.
  Proof. vm_compute. reflexivity. Qed.
  Lemma kvs_erase_acquire_block :
    nth 4 assembled_kvs_erase [] = kvs_acquire kvs_erase_acquire_off.
  Proof. vm_compute. reflexivity. Qed.

  (** The assembled [cgp] restriction to the table. *)
  Definition kvs_table : list instr :=
    [ machine_instructions.GetA ct0 cgp;
      machine_instructions.Add ct1 (inr ct0) (inl KVS_LOCK_OFFSET);
      machine_instructions.Subseg cgp cgp (inr ct0) (inr ct1) ].
  Definition kvs_table_instrs : list Word := encodeInstrsW kvs_table.

  Lemma kvs_table_assembles : assemble kvs_table_asm = kvs_table.
  Proof. vm_compute. reflexivity. Qed.

  (** The assembled [release()]. *)
  Definition kvs_release : list instr :=
    [ machine_instructions.Store cs0 (inl 0%Z) 0;
      machine_instructions.Mov cs0 (inl 0%Z) ].
  Definition kvs_release_instrs : list Word := encodeInstrsW kvs_release.

  Lemma kvs_release_assembles : assemble kvs_release_asm = kvs_release.
  Proof. vm_compute. reflexivity. Qed.
End KVS_acquire_code.

Section KVS_acquire.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {kvsg:kvsG Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
    {KVS_layout : kvsLayout} {KVS_layout_WF : kvsLayoutWf}
    {LK : locksLayout}
    (kvs_users : gmap user_key_t CmptName)
  .

  (** [acquire()]: spins on [try_lock], yielding between attempts; then
      [cs0] holds the capability to the lock word, and the resource of the
      lock is in hand. *)
  Lemma kvs_acquire_spec (pc_b pc_e pc_a : Addr) (off : Z) (mie : InterruptStatus) (wcra : LWord) :
    let instrs := kvs_acquire_instrs off in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs) →
    (pc_a ^+ kvs_acquire_fetch_at + off)%a = Some (pc_b ^+ TRY_LOCK_OFFSET) →
    is_shadow_address (pc_b ^+ TRY_LOCK_OFFSET) = false →
    (KVS_cgp_b + length kvs_data)%a = Some KVS_cgp_e →
    is_heap_address kvs_lock_addr = false →
    is_heap_address b_locks = false →
    th ≠ CtxSwitch →
    route_pre th mie →
    PC ↦ₚ[th] Cap RX Global pc_b pc_e pc_a ∗
    cgp ↦ᵣ[th] Cap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
    cra ↦ᵣ[th] wcra ∗
    cs0 ↦ᵣ[th] - ∗
    cs1 ↦ᵣ[th] - ∗
    ct0 ↦ᵣ[th] - ∗
    ct1 ↦ᵣ[th] - ∗
    ct2 ↦ᵣ[th] - ∗
    MIE ↦ₜ[th] mie ∗
    held (th := th) mie ∗
    codefrag_pers pc_a instrs ∗
    (pc_b ^+ TRY_LOCK_OFFSET) ↦ₐ□ lword_of_word try_lock_entry ∗
    lock_static ∗
    kvs_lock kvs_users ∗
    ▷ (PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ length instrs) ∗
       cgp ↦ᵣ[th] Cap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
       cra ↦ᵣ[th] wcra ∗
       cs0 ↦ᵣ[th] Cap RW Global kvs_lock_addr (kvs_lock_addr ^+ 1) kvs_lock_addr ∗
       cs1 ↦ᵣ[th] WInt 0 ∗
       ct0 ↦ᵣ[th] - ∗
       ct1 ↦ᵣ[th] - ∗
       ct2 ↦ᵣ[th] WInt 0 ∗
       MIE ↦ₜ[th] mie ∗
       held (th := th) mie ∗
       kvs_R kvs_users -∗
       safe[th])
    ⊢ safe[th].
  Proof.
    intros instrs; subst instrs.
    iIntros (Hsub Hoff Htl_shadow Hdata Hlock_heap Hlocks_heap Hth Hroute)
      "(HPC & Hcgp & Hcra & [%wcs0 Hcs0] & [%wcs1 Hcs1] & [%wct0 Hct0] & [%wct1 Hct1] & Hct2
      & HMIE & Hheld & #Hcode & #Htry_lock & #Hlock_static & #Hlock & Hpost)".
    pose proof (eq_refl : length kvs_data = 49) as Hlen.
    rewrite Hlen in Hdata.
    assert (is_shadow_address kvs_lock_addr = false) as Hshadow.
    { apply (disjoint_from_shadow_not_in KVS_cgp_b KVS_cgp_e); first apply KVS_cgp_disjoint_from_shadow.
      rewrite /withinBounds /kvs_lock_addr /KVS_LOCK_OFFSET. solve_addr. }
    rewrite /kvs_acquire_instrs. codefrag_facts "Hcode".
    rename H into Hcontiguous, H0 into Hsub'.
    assert (length (encodeInstrsW (kvs_acquire off)) = 17) as Hinstrs by reflexivity.
    (* The sentry of [try_lock] is not a heap capability. The fact on its
       base goes, so that the side conditions of [Subseg] do not pick it. *)
    assert (is_heap_cap (lw (lword_of_word try_lock_entry)) = false) as Htl_heap.
    { rewrite /try_lock_entry /is_heap_cap /heap_cap_base /memory_cap_base /= Hlocks_heap //. }
    clear Hlocks_heap.
    (* Mov cs1 cgp. *)
    iInstr "Hcode".
    (* Lea cs1 cs1 KVS_LOCK_OFFSET. *)
    iInstr "Hcode".
    { instantiate (1 := kvs_lock_addr); rewrite /kvs_lock_addr /KVS_LOCK_OFFSET; solve_addr. }
    (* GetA ct0 cs1. *)
    iInstr "Hcode".
    (* Add ct1 ct0 1. *)
    iInstr "Hcode".
    (* Subseg cs1 cs1 ct0 ct1. *)
    iInstr "Hcode".
    { instantiate (1 := (kvs_lock_addr ^+ 1)%a). rewrite /kvs_lock_addr /KVS_LOCK_OFFSET; solve_addr. }
    { rewrite /isWithin /kvs_lock_addr /KVS_LOCK_OFFSET. solve_addr. }
    { solve_addr. }
    iAssert (ct0 ↦ᵣ[th] -)%I with "[Hct0]" as "Hct0"; first by iExists _.
    iAssert (ct1 ↦ᵣ[th] -)%I with "[Hct1]" as "Hct1"; first by iExists _.
    clear wct0 wct1.

    (* while (try_lock(&lock) != 0) { yield(); } *)
    iRevert "HPC Hcgp Hcra Hcs0 Hcs1 Hct0 Hct1 Hct2 HMIE Hheld Hpost".
    iLöb as "IH".
    iIntros "HPC Hcgp Hcra Hcs0 Hcs1 [%wl0 Hct0] [%wl1 Hct1] [%wl2 Hct2] HMIE Hheld Hpost".
    (* Mov ct0 cs1. *)
    iInstr "Hcode".
    (* Auipcc ct1 off. *)
    iInstr "Hcode".
    (* CLoad ct1 ct1 0. *)
    iInstr "Hcode".
    { rewrite Hinstrs in Hcontiguous Hsub'. rewrite /withinBounds /TRY_LOCK_OFFSET. solve_addr. }
    iEval (rewrite /lload_word /lift_word /= /try_lock_entry /load_word /=) in "Hct1".
    (* Mov ct2 cra. *)
    iInstr "Hcode".
    (* Jalr cra ct1. *)
    iInstr "Hcode".
    iEval (cbn) in "HPC HMIE Hheld".
    iEval (rewrite /kvs_lock) in "Hlock".
    iApply (try_lock_spec (th := th) Nkvs_lock kvs_lock_addr (kvs_R kvs_users) RW Global
              kvs_lock_addr (kvs_lock_addr ^+ 1)%a
            with "[$Hlock_static $Hlock $HPC $Hct0 $Hct1 $Hcra $HMIE $Hheld Hcgp Hcs0 Hcs1 Hct2 Hpost]");
      [done | done | rewrite /withinBounds /kvs_lock_addr /KVS_LOCK_OFFSET; solve_addr
      | exact Hshadow | by rewrite jalr_target_ok_ret_kind | exact Hth |].
    iNext. iIntros "(HPC & Hct1 & Hcra & HMIE & Hheld & Hres)".
    iEval (rewrite /lupdatePcPerm /lift_word /=) in "HPC".
    iEval (rewrite default_jalr_target_mie_ret_kind) in "HMIE Hheld".
    (* Mov cra ct2. *)
    iInstr "Hcode".
    iDestruct "Hres" as "[ [Hct0 HR] | Hct0]".
    - (* The lock is taken *)
      (* Jeq 3 ct0 0. *)
      iInstr "Hcode".
      (* Mov ct2 0. *)
      iInstr "Hcode".
      (* Mov cs0 cs1. *)
      iInstr "Hcode".
      (* Mov cs1 0. *)
      iInstr "Hcode".
      iApply "Hpost". iFrame "HPC Hcgp Hcra Hcs0 Hcs1 Hct2 HMIE Hheld HR".
      iSplitL "Hct0"; by iExists _.
    - (* The lock is busy: the thread yields, and tries again *)
      (* Jeq 3 ct0 0. *)
      iInstr "Hcode".
      (* Ecall. *)
      iInstr_lookup "Hcode" as "Hi" "Hcode_cont".
      iApply (wp_yield with "HPC Hi HMIE Hheld"); [done | solve_pure | solve_pure | |].
      { transitivity (Some (pc_a ^+ 13)%a); auto; solve_addr. }
      iNext; iIntros "HPC _ HMIE Hheld".
      (* Jmp (-8). *)
      iInstr "Hcode".
      { transitivity (Some (pc_a ^+ 5)%a); auto; solve_addr. }
      iApply ("IH" with "HPC Hcgp Hcra Hcs0 Hcs1 [Hct0] [Hct1] [Hct2] HMIE Hheld Hpost");
        by iExists _.
  Qed.

  (** [cgp] restricted to the table, for [search]. *)
  Lemma kvs_table_spec (pc_b pc_e pc_a : Addr) :
    SubBounds pc_b pc_e pc_a (pc_a ^+ length kvs_table_instrs) →
    (KVS_cgp_b + length kvs_data)%a = Some KVS_cgp_e →
    PC ↦ₚ[th] Cap RX Global pc_b pc_e pc_a ∗
    cgp ↦ᵣ[th] Cap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
    ct0 ↦ᵣ[th] - ∗
    ct1 ↦ᵣ[th] - ∗
    codefrag_pers pc_a kvs_table_instrs ∗
    ▷ (PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ length kvs_table_instrs) ∗
       cgp ↦ᵣ[th] Cap RW Global KVS_cgp_b kvs_lock_addr KVS_cgp_b ∗
       ct0 ↦ᵣ[th] - ∗
       ct1 ↦ᵣ[th] - -∗
       safe[th])
    ⊢ safe[th].
  Proof.
    iIntros (Hsub Hdata) "(HPC & Hcgp & [%wct0 Hct0] & [%wct1 Hct1] & #Hcode & Hpost)".
    pose proof (eq_refl : length kvs_data = 49) as Hlen.
    rewrite /kvs_table_instrs. codefrag_facts "Hcode".
    (* GetA ct0 cgp. *)
    iInstr "Hcode".
    (* Add ct1 ct0 KVS_LOCK_OFFSET. *)
    iInstr "Hcode".
    (* Subseg cgp cgp ct0 ct1. *)
    iInstr "Hcode".
    { instantiate (1 := kvs_lock_addr); rewrite /kvs_lock_addr /KVS_LOCK_OFFSET; solve_addr. }
    { rewrite /isWithin /kvs_lock_addr /KVS_LOCK_OFFSET Hlen in Hdata |- *. solve_addr. }
    { rewrite /kvs_lock_addr /KVS_LOCK_OFFSET. solve_addr. }
    { intros _ _. apply KVS_cgp_base_not_heap. }
    iApply "Hpost". iFrame "HPC Hcgp". iSplitL "Hct0"; by iExists _.
  Qed.

  (** [release()]: the store of [0] to the lock word, in one step with the
      critical-section token, gives the resource of the lock back. *)
  Lemma kvs_release_spec (pc_b pc_e pc_a : Addr) (mie : InterruptStatus) :
    SubBounds pc_b pc_e pc_a (pc_a ^+ 2) →
    route_pre th mie →
    PC ↦ₚ[th] Cap RX Global pc_b pc_e pc_a ∗
    cs0 ↦ᵣ[th] Cap RW Global kvs_lock_addr (kvs_lock_addr ^+ 1) kvs_lock_addr ∗
    MIE ↦ₜ[th] mie ∗
    held (th := th) mie ∗
    codefrag_pers pc_a kvs_release_instrs ∗
    kvs_lock kvs_users ∗
    ▷ kvs_R kvs_users ∗
    ▷ (PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ 2) ∗
       cs0 ↦ᵣ[th] WInt 0 ∗
       MIE ↦ₜ[th] mie ∗
       held (th := th) mie -∗
       safe[th])
    ⊢ safe[th].
  Proof.
    iIntros (Hsub Hroute) "(HPC & Hcs0 & Hmie & Hheld & #Hcode & #Hlock & HR & Hpost)".
    pose proof KVS_size_data as Hdata.
    pose proof (eq_refl : length_kvs_data = 49) as Hlen.
    rewrite Hlen in Hdata.
    assert (is_shadow_address kvs_lock_addr = false) as Hshadow.
    { apply (disjoint_from_shadow_not_in KVS_cgp_b KVS_cgp_e); first apply KVS_cgp_disjoint_from_shadow.
      rewrite /withinBounds /kvs_lock_addr /KVS_LOCK_OFFSET. solve_addr. }
    rewrite /kvs_release_instrs. codefrag_facts "Hcode".
    (* Store cs0 0 0: one step with the critical-section token, which opens
       the invariant of the lock and closes it with its resource *)
    iInstr_lookup "Hcode" as "Hi" "Hcode_cont".
    wp_instr.
    iDestruct "Hi" as "#Hi".
    iApply (wp_wand with "[HPC Hcs0 Hheld Hmie HR]").
    { iApply (wp_core_full_crit (ceriseg := ceriseG_of th) (th := th) ⊤ mie
                (λ b' v, ⌜b' = mie⌝ ∗ ⌜v = NextIV⌝ ∗
                   PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ 1) ∗
                   cs0 ↦ᵣ[th] Cap RW Global kvs_lock_addr (kvs_lock_addr ^+ 1) kvs_lock_addr)%I
               with "Hheld Hmie"); first done.
      iIntros "Hcrit Hmie".
      iMod (lock_inv_release_acc ⊤ Nkvs_lock kvs_lock_addr (kvs_R kvs_users) with "Hlock Hcrit")
        as "[ [%wlock Hl] Hclose]"; first solve_ndisj.
      iApply wp_fupd.
      iAssert (deref_res None 1%Qp) as "Hdr"; first by rewrite /deref_res.
      iApply (wp_store_success_z_imm (ceriseg := ceriseG_of th) (th := th) (CL := link_core)
                with "[$HPC $Hi $Hcs0 $Hl $Hdr]"); try solve_pure.
      { rewrite /withinBounds /kvs_lock_addr /KVS_LOCK_OFFSET. solve_addr. }
      { solve_addr. }
      iIntros "!> (HPC & _ & Hcs0 & Hl & _)".
      iMod ("Hclose" with "Hl HR") as "Hcrit".
      iModIntro. iNext. iExists mie. by iFrame. }
    iIntros (v) "Hpost'".
    iDestruct "Hpost'" as (b') "(Hheld & Hmie & >-> & >-> & HPC & Hcs0)".
    iApply wp_pure_step_later; first done.
    iNext; iIntros "_".
    (* Mov cs0 0. *)
    iInstr "Hcode".
    iApply "Hpost". iFrame.
  Qed.

End KVS_acquire.
