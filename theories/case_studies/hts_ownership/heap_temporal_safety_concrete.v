From stdpp Require Import gmap strings.
From iris.program_logic Require Import language.
From griotte Require Import
  machine_base machine_parameters machine_parameters_instance griotte_opsem griotte_lang machine_run
  assembler switcher assert allocator_resources compartment_layout.
From griotte.case_studies.hts_ownership Require Import heap_temporal_safety heap_temporal_safety_adequacy.
From griotte.allocators.ownership Require Import allocator.
(* Imported last: the fields of the image records. *)
From griotte Require Import image firmware firmware_ok image_state link.
From griotte.case_studies.hts_ownership Require Import hts_firmware.

#[local] Transparent MemNum ONum.
#[local] Open Scope string_scope.

(** * A concrete instance of the heap temporal safety case study

    The heap temporal safety firmware with a concrete adversary [B], laid
    out by the linker, on a machine whose heap has room for one allocation.
    Its initial state satisfies [hts_initial_state_ok] by computation, runs
    to [Halted], and [hts_adequacy] applies to it. *)

(** The default machine instance has only the allocator's reserved heap
    address. This one adds three header addresses and one payload address,
    with a matching shadow region. All instruction and permission encodings
    are reused. *)
Definition hts_heap_region : HeapRegion :=
  {| heap_b := @finz.FinZ MemNum 8192 eq_refl eq_refl;
     heap_e := @finz.FinZ MemNum 8197 eq_refl eq_refl;
     heap_valid := ltac:(solve_addr) |}.
Definition hts_shadow_region : ShadowRegion :=
  {| shadow_b := @finz.FinZ MemNum 12288 eq_refl eq_refl;
     shadow_e := @finz.FinZ MemNum 12293 eq_refl eq_refl;
     shadow_valid := ltac:(solve_addr) |}.

#[local] Instance hts_machine_parameters : MachineParameters :=
  {| instruction_encoding_mixin := @instruction_encoding_mixin machine_parameters_instance;
     permission_encoding_mixin := @permission_encoding_mixin machine_parameters_instance;
     word_encoding_mixin := @word_encoding_mixin machine_parameters_instance;
     encodeAllocStatus := @encodeAllocStatus machine_parameters_instance;
     decodeAllocStatus := @decodeAllocStatus machine_parameters_instance;
     decode_encode_alloc_status_inv := @decode_encode_alloc_status_inv machine_parameters_instance;
     heap_mixin := hts_heap_region;
     shadow_mixin := hts_shadow_region;
     heap_shadow_translation_mixin :=
       @affine_heap_shadow_translation hts_heap_region hts_shadow_region eq_refl;
     heap_shadow_disjoint := ltac:(
       intros x Hheap Hshadow;
       rewrite !elem_of_finz_seq_between in Hheap, Hshadow;
       unfold finz.le_lt in Hheap, Hshadow;
       cbn in Hheap, Hshadow; lia);
     revoker_mixin := @revoker_mixin machine_parameters_instance;
     revoker_not_heap := eq_refl;
     revoker_not_shadow := eq_refl;
     mtval_encoding_mixin := @mtval_encoding_mixin machine_parameters_instance |}.

Definition hts_switcher_sealing_type : OType := @finz.FinZ ONum 9 eq_refl eq_refl.
Definition hts_alloc_sealing_type : OType := @finz.FinZ ONum 10 eq_refl eq_refl.

(** The concrete adversary counts its calls. On the first, it saves the
    buffer it receives; on the second, it checks that the saved buffer has
    lost its tag. Its entry point is right after its four imports. *)
(* The explicit assembly injectors below avoid ambiguous sum coercions. *)
Import Asm_Griotte.
Definition hts_adv_asm : list (list Asm_Griotte.asm_code) :=
  let first := ".hts_first" in
  let second := ".hts_second" in
  let return_ := ".hts_return" in
  let bad := ".hts_bad" in
  let count := 0%Z in
  let saved := 1%Z in
  let observed := 2%Z in
  [ [load_imm ct0 cgp count; add ct0 (asmr ct0) (asmz 1);
     store_imm cgp (asmr ct0) (asmexprz count);
     sub ct1 (asmr ct0) (asmz 1); jnez (asms second) ct1;
     #first; store_imm cgp (asmr ca0) (asmexprz saved); jmp (asms return_)];
    [ #second; sub ct1 (asmr ct0) (asmz 2); jnez (asms bad) ct1;
     load_imm ct0 cgp saved; gettag ct1 ct0;
     store_imm cgp (asmr ct1) (asmexprz observed); jnez (asms bad) ct1];
    [ #return_; mov ca0 (asmz 0); mov ca1 (asmz 0); ret];
    [ #bad; fail] ].

Import machine_instructions.

Definition hts_adv_code : list Word :=
  concat (encodeInstrsW <$> Asm_Griotte.assemble_block hts_adv_asm).
Lemma hts_adv_assembles :
  Asm_Griotte.asm_ok (Asm_Griotte.assemble_block_check hts_adv_asm).
Proof. asm_check. Qed.
Definition hts_adv_data : list Word := [WInt 0; WInt 0; WInt (-1)].

Definition hts_demo_firmware : firmware := hts_firmware hts_alloc_sealing_type.

Definition hts_demo_link_cfg : link_cfg := {|
  lk_base        := 16;
  lk_ot_switcher := hts_switcher_sealing_type;
  lk_adv         := [
    ("B", {| la_code    := hts_adv_code;
             la_data    := hts_adv_data;
             la_exports := [
               4  (* after the 4 imports *)
             ];
             la_handler := ExportTable_no_handler;
             la_handler_stackless := ExportTable_no_handler |})
  ]
|}.

(** ** The linked image and its initial state *)

Definition hts_demo_image : fw_image :=
  Eval vm_compute in
    default (place hts_demo_link_cfg hts_demo_firmware).1
      (link hts_demo_link_cfg hts_demo_firmware).

Lemma hts_demo_linked :
  link hts_demo_link_cfg hts_demo_firmware = Some hts_demo_image.
Proof. vm_compute; reflexivity. Qed.

Definition hts_demo_state : ExecConf := img_state hts_demo_firmware hts_demo_image.

Ltac solve_other_registers :=
  intros r Hr; cbn [pcc reg sreg mem shadowtbl fst snd];
  rewrite !lookup_insert_ne; try set_solver;
  apply lookup_gset_to_gmap_Some; split; [apply all_registers_s_correct | done].

Lemma hts_demo_ok :
  hts_initial_state_ok (flag_assert (img_asrt hts_demo_image)) hts_demo_state.
Proof.
  rewrite /hts_initial_state_ok.
  exists (img_sw hts_demo_image), (img_asrt hts_demo_image), (thread_of hts_demo_image 0),
    (cmpt_of hts_demo_image "main"), (cmpt_of hts_demo_image "allocator"),
    (cmpt_of hts_demo_image "B"), hts_alloc_sealing_type.
  split; first done.
  split_and!.
  (* The error handler offsets of the adversaries, as the configuration gives them. *)
  all: try exists_adv_handlers hts_demo_link_cfg.
  all: try (exists 4%nat, 0%nat; split_and!).
  (* The shadow table of this machine translates the heap by a constant offset. *)
  all: try (intros a; reflexivity).
  all: try (lazymatch goal with
            | |- ∀ r, _ => rewrite /hts_demo_state /img_state /img_regs; solve_other_registers
            end).
  all: solve_concrete_condition.
Qed.

(** ** The run

    [hts_demo_state] runs to [Halted], and [hts_adequacy] applies to it:
    the flag of the assert library is still zero. *)
Theorem hts_runs_and_gracefully_halts :
  ∃ pc' reg' sreg' mem' sh',
    rtc erased_step ([Seq (Instr Executable)], hts_demo_state)
      ([Instr Halted], (pc', reg', sreg', mem', sh'))
    ∧ mem' !! flag_assert (img_asrt hts_demo_image) = Some (WInt 0%Z).
Proof.
  pose proof (machine_run_correct (N.to_nat 10000%N) Executable hts_demo_state Halted) as Hrun.
  specialize (Hrun ltac:(vm_compute; reflexivity)).
  destruct Hrun as [[[[[pc' reg'] sreg'] mem'] sh'] Hrun].
  exists pc', reg', sreg', mem', sh'. split; first exact Hrun.
  exact (hts_adequacy _ _ _ _ hts_demo_ok Hrun).
Qed.
