From stdpp Require Import gmap strings.
From griotte Require Import machine_base griotte_opsem switcher assert allocator_resources compartment_layout.
From griotte.case_studies.hts_ownership Require Import heap_temporal_safety.
From griotte.allocators.ownership Require Import allocator.
From griotte Require Import image firmware firmware_ok initial_state.

#[local] Open Scope string_scope.

(** * The firmware of the heap temporal safety case study and its initial-state predicate *)

(** The main compartment allocates a buffer with [malloc] of the
    [allocator], shares it with the adversary [B], frees it with [free],
    calls [B] again, and checks that its global is untouched. The
    allocator is an ordinary trusted compartment: it imports the shadow
    table, the unsealing key of its sealing type [ot_alloc] (a parameter)
    and the revoker, its global is the capability on the whole heap, based
    at the heap root [heap_b], and it exports [malloc] and [free], each
    taking two arguments. Main and [B] each import [malloc], [free] and
    their own allocator capability: their static sealed object
    [allocator_capability] (the owner identifier), sealed with [ot_alloc]. [B] exports one entry
    [adv], taking one argument. The thread starts at the export [entry] of
    [main], after its six imports. *)
Definition hts_firmware `{MP : MachineParameters} (ot_alloc : OType) : firmware := {|
  fw_cmpts      := [
    {| fc_name          := "main";
       fc_imports       := [
         ISwitcherCall;
         IAssert;
         IExport "B" "adv";
         IExport "allocator" "malloc";
         IExport "allocator" "free";
         ISealedStatic ot_alloc "allocator_capability"
       ];
       fc_static_sealed := [
         {| ss_name := "allocator_capability"; ss_word := WInt hts_main_owner_id |}
       ];
       fc_body          := TrustedBody {|
         tb_code    := hts_main_code;
         tb_data    := [
           FWs hts_main_data
         ];
         tb_exports := [
           (* after the 6 imports; the stack holds the saved buffer and the spill
              of the switcher calls *)
           {| fe_name := "entry"; fe_offset := 6; fe_nargs := 0; fe_min_stack := 5; fe_posture := InterruptEnabled |}
         ];
         tb_error_handler := None;
         tb_error_handler_stackless := None |} |};
    {| fc_name          := "allocator";
       fc_imports       := [
         FW (WCap true RW Global shadow_b shadow_e shadow_b);                             (* the shadow table *)
         FW (WSealRange true (false, true) Global ot_alloc (ot_alloc ^+ 1)%ot ot_alloc);  (* unseal-only key of [ot_alloc] *)
         FW (WCap true RW Global revoker_addr (revoker_addr ^+ 1)%a revoker_addr)         (* the revoker *)
       ];
       fc_static_sealed := [];
       fc_body          := TrustedBody {|
         tb_code    := allocator_code;
         tb_data    := [
           FWs [WCap true RW Global heap_b heap_e (heap_b ^+ 1)%a]  (* the whole heap *)
         ];
         tb_exports := [
           {| fe_name := "malloc"; fe_offset := allocator_malloc_pcc_off; fe_nargs := allocator_malloc_nargs; fe_min_stack := allocator_malloc_min_stack; fe_posture := InterruptEnabled |};
           {| fe_name := "free";   fe_offset := allocator_free_pcc_off;   fe_nargs := allocator_free_nargs;   fe_min_stack := allocator_free_min_stack;   fe_posture := InterruptEnabled |}
         ];
         tb_error_handler := None;
         tb_error_handler_stackless := None |} |};
    {| fc_name          := "B";
       fc_imports       := [
         ISwitcherCall;
         IExport "allocator" "malloc";
         IExport "allocator" "free";
         ISealedStatic ot_alloc "allocator_capability"
       ];
       fc_static_sealed := [
         {| ss_name := "allocator_capability"; ss_word := WInt hts_adv_owner_id |}
       ];
       fc_body          := UntrustedBody {|
         ub_owner   := "B";
         ub_exports := [
           {| ue_name := "adv"; ue_nargs := 1 |}
         ] |} |}
  ];
  fw_threads    := [
    {| ft_cmpt := "main"; ft_entry := "entry"; ft_stack_size := 100; ft_tstack_frames := 24 |}
  ];
  fw_otypes     := [
    ot_alloc
  ];
  fw_heap_roots := [
    heap_b
  ]
|}.

(** The image of the heap temporal safety firmware, from the records of its
    sections. *)
Definition hts_img (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
    (main allocator B : img_cmpt) : fw_image :=
  MkFwImage sw asrt [("main", main); ("allocator", allocator); ("B", B)] [t0].

(** The start of the firmware: some layout and sealing type, with the flag of the
    assert library at [flag], such that [σ] is the state the loader
    builds. *)
Definition hts_start `{MP : MachineParameters} (flag : Addr) (σ : ExecConf) : Prop :=
  ∃ (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
    (main allocator B : img_cmpt) (ot_alloc : OType),
    fw_start [] (hts_firmware ot_alloc) (hts_img sw asrt t0 main allocator B) flag σ.

(** The predicate, computed from [hts_start], with its comments. *)
Definition hts_initial_state_ok_annot `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(compute_initial_state (@hts_start MP) [hts_firmware; hts_img]).

(** The initial-state predicate of the heap temporal safety case study: the
    annotated one without its comments. *)
Definition hts_initial_state_ok `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(erase_annot (@hts_initial_state_ok_annot MP)).

Lemma hts_initial_state_ok_start `{MP : MachineParameters} flag σ :
  hts_initial_state_ok flag σ → hts_start flag σ.
Proof. initial_state_conv. Qed.
