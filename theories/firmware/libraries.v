From stdpp Require Import strings.
From griotte Require Import machine_base machine_parameters.
From griotte Require Import assert locks firmware.

#[local] Open Scope string_scope.

(** * The libraries and the shared objects of the case studies

    The assert library and the lock library as firmware libraries, and the
    assert flag as a shared object. [reduce_firmware_ok] unfolds them. *)

(** The assert flag: one word, zero (no assert has failed). *)
Definition assert_flag_object : fw_shared_object := {|
  so_name := "assert_flag";
  so_size := 1
|}.

(** The assert library: its import table is the switcher slot, then a
    read-write capability to the assert flag; its export [assert] inherits
    the posture of its caller. *)
Definition assert_lib `{MP : MachineParameters} : fw_lib := {|
  fl_name    := "assert";
  fl_imports := [
    ISharedObject "assert_flag" SoRW
  ];
  fl_code    := assert_subroutine_instrs;
  fl_exports := [
    {| le_name := "assert"; le_offset := assert_entry_offset; le_posture := None |}
  ]
|}.

(** The lock library: its import table is the switcher slot only; its
    export [try_lock] runs with interrupts disabled. *)
Definition try_lock_lib `{MP : MachineParameters} : fw_lib := {|
  fl_name    := "locks";
  fl_imports := [];
  fl_code    := locks_try_lock_instrs;
  fl_exports := [
    {| le_name := "try_lock"; le_offset := try_lock_entry_offset;
       le_posture := Some InterruptDisabled |}
  ]
|}.
