From stdpp Require Import gmap strings.
From griotte Require Import machine_base griotte_opsem switcher assert allocator_resources compartment_layout.
From griotte.case_studies.hts_ownership Require Import heap_temporal_safety.
From griotte.allocators.ownership Require Import allocator.
From griotte Require Import image firmware firmware_ok.
Set Mangle Names.

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
    their own allocator capability: their first static sealed object (the
    owner identifier), sealed with [ot_alloc]. [B] exports one entry
    [adv], taking one argument. The thread starts at the export [entry] of
    [main], after its six imports. *)
Definition hts_firmware `{MP : MachineParameters} (ot_alloc : OType) : firmware := {|
  fw_cmpts      := [
    {| fc_name          := "main";
       fc_imports       := [ISwitcherCall; IAssert; IExport "B" "adv";
                            IExport "allocator" "malloc"; IExport "allocator" "free";
                            ISealedStatic ot_alloc 0];
       fc_static_sealed := hts_main_static_sealed;
       fc_body          :=
         TrustedBody {|
           tb_code    := hts_main_code;
           tb_data    := [FWs hts_main_data];
           tb_exports := [ {| fe_name    := "entry";
                              fe_offset  := 6;
                              fe_nargs   := 0;
                              fe_posture := InterruptEnabled |} ] |} |};
    {| fc_name          := "allocator";
       fc_imports       := [FW (WCap true RW Global shadow_b shadow_e shadow_b);
                            FW (WSealRange true (false, true) Global ot_alloc (ot_alloc ^+ 1)%ot ot_alloc);
                            FW (WCap true RW Global revoker_addr (revoker_addr ^+ 1)%a revoker_addr)];
       fc_static_sealed := [];
       fc_body          :=
         TrustedBody {|
           tb_code    := allocator_code;
           tb_data    := [FWs [WCap true RW Global heap_b heap_e (heap_b ^+ 1)%a]];
           tb_exports := [ {| fe_name    := "malloc";
                              fe_offset  := allocator_malloc_pcc_off;
                              fe_nargs   := allocator_malloc_nargs;
                              fe_posture := InterruptEnabled |};
                           {| fe_name    := "free";
                              fe_offset  := allocator_free_pcc_off;
                              fe_nargs   := allocator_free_nargs;
                              fe_posture := InterruptEnabled |} ] |} |};
    {| fc_name          := "B";
       fc_imports       := [ISwitcherCall; IExport "allocator" "malloc";
                            IExport "allocator" "free"; ISealedStatic ot_alloc 0];
       fc_static_sealed := hts_adv_static_sealed;
       fc_body          :=
         UntrustedBody {|
           ub_owner   := "B";
           ub_exports := [ {| ue_name  := "adv";
                              ue_nargs := 1 |} ] |} |}
  ];
  fw_threads    := [ {| ft_cmpt          := "main";
                        ft_entry         := "entry";
                        ft_stack_size    := 100;
                        ft_tstack_frames := 24 |} ];
  fw_otypes     := [ot_alloc];
  fw_heap_roots := [heap_b]
|}.

(** The image of the heap temporal safety firmware, from the records of its
    sections. *)
Definition hts_img (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
    (main allocator B : img_cmpt) : fw_image :=
  MkFwImage sw asrt [("main", main); ("allocator", allocator); ("B", B)] [t0].

(** The predicate, computed from the firmware, with its comments: some
    layout and sealing type, with the flag of the assert library at
    [flag], satisfy the translation of the firmware. *)
Definition hts_initial_state_ok_annot `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(let t := eval cbv beta delta [hts_firmware hts_img] in
          (λ (flag : Addr) (σ : ExecConf),
             ∃ (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
               (main allocator B : img_cmpt) (ot_alloc : OType),
               note "the flag of the assert library" (flag_assert asrt = flag) ∧
               firmware_ok (hts_firmware ot_alloc) (hts_img sw asrt t0 main allocator B) σ)
        in
        let t := reduce_firmware_ok t in
        exact t).

(** The initial-state predicate of the heap temporal safety case study: the
    annotated one without its comments. *)
Definition hts_initial_state_ok `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  Eval cbv beta delta [section note hts_initial_state_ok_annot] in
    @hts_initial_state_ok_annot MP.

Lemma hts_initial_state_ok_erase `{MP : MachineParameters} flag σ :
  hts_initial_state_ok_annot flag σ ↔ hts_initial_state_ok flag σ.
Proof. reflexivity. Qed.

(** The predicate is the generic translation on the heap temporal safety
    firmware. *)
Lemma hts_initial_state_ok_firmware_ok `{MP : MachineParameters} flag σ :
  hts_initial_state_ok flag σ →
  ∃ (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
    (main allocator B : img_cmpt) (ot_alloc : OType),
    flag_assert asrt = flag ∧
    firmware_ok (hts_firmware ot_alloc) (hts_img sw asrt t0 main allocator B) σ.
Proof. intros Hok. exact Hok. Qed.
