From iris.proofmode Require Import proofmode.
From griotte Require Import logrel proofmode switcher switcher_preamble.
From griotte Require Import switcher_spec_KtK register_tactics map_simpl.
From griotte Require Import heap_temporal_safety_preamble.
From griotte.allocator Require Import allocator allocator_preamble.
From griotte.allocator Require Export allocator_malloc_spec allocator_free_spec
  allocator_resource_spec.

Section Heap_Temporal_Safety_Interp.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ} {relg : relGS Σ}
    {allocator_historyg : allocatorHistoryG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}
  .

  (** BLOCKED: allocation must extend the heap world and make the zeroed
      result safe to return to an arbitrary caller. *)
  Lemma malloc_exec_entry_point (W : WORLD) (C : CmptName) :
    allocator_ctx ∗ allocator_service_ctx ⊢
    execute_entry_point
      (WCap true RX Global allocator_pcc_b allocator_pcc_e allocator_malloc_pcc_addr)
      (WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b)
      allocator_malloc_nargs W C.
  Proof.
  Admitted.

  (** BLOCKED: free from an unknown caller needs the shared heap protocol to
      recover live addresses or handle already quarantined addresses, then reestablish
      the world while invalidating retained aliases. Do not assume exclusive
      points-to ownership merely because the argument is safe to share. *)
  Lemma free_exec_entry_point W C :
    allocator_ctx ∗ allocator_service_ctx ⊢
    execute_entry_point
      (WCap true RX Global allocator_pcc_b allocator_pcc_e allocator_free_pcc_addr)
      (WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b)
      allocator_free_nargs W C.
  Proof.
  Admitted.


  (*** Safe entry points *)
  Lemma malloc_entry_point_spec
    (g_allocator_exp_tbl : Locality)
    (W : WORLD)
    (C : CmptName)
    (Nswitcher : namespace) :
    allocator_ctx ∗
    allocator_service_ctx ∗
    na_inv cerise_nais Nswitcher switcher_inv ∗
    inv (export_table_PCCN hts_allocator_exp_tblN)
      (allocator_exp_tbl_b ↦ₐ WCap true RX Global
        allocator_pcc_b allocator_pcc_e allocator_pcc_b) ∗
    inv (export_table_CGPN hts_allocator_exp_tblN)
      ((allocator_exp_tbl_b ^+ 1)%a ↦ₐ WCap true RW Global
        allocator_cgp_b allocator_cgp_e allocator_cgp_b) ∗
    inv (export_table_entryN hts_allocator_exp_tblN
      (allocator_exp_tbl_b ^+ allocator_malloc_exp_tbl_off)%a)
      ((allocator_exp_tbl_b ^+ allocator_malloc_exp_tbl_off)%a ↦ₐ
        WInt (encode_entry_point allocator_malloc_nargs allocator_malloc_pcc_off)) ∗
    WSealed ot_switcher (allocator_malloc g_allocator_exp_tbl)
      ↦□ₑ allocator_malloc_nargs ∗
    WSealed ot_switcher (allocator_malloc Local)
      ↦□ₑ allocator_malloc_nargs -∗
    ot_switcher_prop W C
      (WCap true RO g_allocator_exp_tbl allocator_exp_tbl_b allocator_exp_tbl_e
        (allocator_exp_tbl_b ^+ allocator_malloc_exp_tbl_off)%a).
  Proof.
  Admitted.

  Lemma free_entry_point_spec
    (g_allocator_exp_tbl : Locality)
    (W : WORLD)
    (C : CmptName)
    (Nswitcher : namespace) :
    allocator_ctx ∗
    allocator_service_ctx ∗
    na_inv cerise_nais Nswitcher switcher_inv ∗
    inv (export_table_PCCN hts_allocator_exp_tblN)
      (allocator_exp_tbl_b ↦ₐ WCap true RX Global
        allocator_pcc_b allocator_pcc_e allocator_pcc_b) ∗
    inv (export_table_CGPN hts_allocator_exp_tblN)
      ((allocator_exp_tbl_b ^+ 1)%a ↦ₐ WCap true RW Global
        allocator_cgp_b allocator_cgp_e allocator_cgp_b) ∗
    inv (export_table_entryN hts_allocator_exp_tblN
      (allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off)%a)
      ((allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off)%a ↦ₐ
        WInt (encode_entry_point allocator_free_nargs allocator_free_pcc_off)) ∗
    WSealed ot_switcher (allocator_free g_allocator_exp_tbl)
      ↦□ₑ allocator_free_nargs ∗
    WSealed ot_switcher (allocator_free Local)
      ↦□ₑ allocator_free_nargs -∗
    ot_switcher_prop W C
      (WCap true RO g_allocator_exp_tbl allocator_exp_tbl_b allocator_exp_tbl_e
        (allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off)%a).
  Proof.
  Admitted.

End Heap_Temporal_Safety_Interp.
