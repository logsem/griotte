From stdpp Require Import gmap strings.
From griotte Require Import machine_base machine_parameters griotte_opsem export_table_layout.
From griotte Require Import image firmware firmware_ok link.

#[local] Open Scope string_scope.

(** * A round-robin scheduler for the demo images

    The scheduler of every concrete image. Its globals are
    [idx; count; live; h_0; …; h_n]: the handles [h_0 … h_(n-1)] of the
    user threads, then the idle thread's [h_n], which the ring never
    reaches; the slot [idx] of the thread it resumed last; the number
    [count = n] of user threads; the number [live] of user threads that
    have not exited. Called with the parked thread's handle in [ca0] and
    the cause in [ca1]:
    - on the first call, the boot (cause [0]), it returns [h_0];
    - on a thread's exit, it stops the machine if no user thread is left;
    - otherwise it stores [ca0] in slot [idx], moves to the next slot,
      modulo [count], and returns its handle.
    An exited thread's handle stays in the ring. Before it returns, it
    programs the timer threshold [mtimecmp] to [mtime + rr_time_slice],
    through the time devices it imports. Its PCC range holds its three
    imports, the switcher call, [mtime] and [mtimecmp], then its code: its
    exception entry is the first code word. *)

(** The number of timer cycles a thread runs before the next interrupt. *)
Definition rr_time_slice : Z := 10000.

Definition rr_sched_code `{MP : MachineParameters} : list Word :=
  encodeInstrsW [
    (* 0: not the boot *)
    Jne (inl 3%Z) (inr ca1) (inl 0%Z);
    (* 1-2: the boot: the first user thread *)
    CLoad ca0 cgp 3%Z;
    Jmp (inl 17%Z);
    (* 3: not an exit: rotate *)
    Jne (inl 6%Z) (inr ca1) (inl MCAUSE_THREAD_EXIT);
    (* 4-6: one live user thread less *)
    CLoad ct0 cgp 2%Z;
    Sub ct0 (inr ct0) (inl 1%Z);
    Store cgp (inr ct0) 2%Z;
    (* 7: a user thread is still live: rotate *)
    Jne (inl 2%Z) (inr ct0) (inl 0%Z);
    (* 8: every user thread exited: stop the machine *)
    Halt;
    (* 9-11: the current slot receives the parked thread *)
    CLoad ct0 cgp 0%Z;
    Lea ct1 cgp (inr ct0);
    Store ct1 (inr ca0) 3%Z;
    (* 12-16: the next slot, modulo the number of user threads *)
    CLoad ct2 cgp 1%Z;
    Add ct0 (inr ct0) (inl 1%Z);
    Jlt (inl 2%Z) (inr ct0) (inr ct2);
    Mov ct0 (inl 0%Z);
    Store cgp (inr ct0) 0%Z;
    (* 17-18: its handle *)
    Lea ct1 cgp (inr ct0);
    CLoad ca0 ct1 3%Z;
    (* 19-21: the imports of [mtime] and [mtimecmp], through the PC *)
    Auipcc ct1 (-21)%Z;
    CLoad ct0 ct1 0%Z;
    CLoad ct1 ct1 1%Z;
    (* 22-24: mtimecmp := mtime + rr_time_slice *)
    CLoad ct0 ct0 0%Z;
    Add ct0 (inr ct0) (inl rr_time_slice);
    Store ct1 (inr ct0) 0%Z;
    (* 25: back to the switcher *)
    Jalr cnull cra
  ].

(** The initial globals: the first slot is current, every user thread is
    live. *)
Definition rr_sched_data `{MP : MachineParameters} (fw : firmware) (img : fw_image) :
    list Word :=
  let n := Z.of_nat (length (fw_threads fw)) in
  WInt 0 :: WInt n :: WInt n :: thread_handles fw img.

Definition rr_sched_adv `{MP : MachineParameters} (data : list Word) : link_adv := {|
  la_code := rr_sched_code;
  la_data := data;
  la_exports := [];
  la_handler := ExportTable_no_handler;
  la_handler_stackless := ExportTable_no_handler |}.

(** The configuration with the adversaries [adv], the round-robin
    scheduler as the compartment ["sched"] and a zeroed boot stack of [k]
    words. The handles in the globals depend on the addresses of the
    trusted stacks: a first placement, with zeroed globals of the same
    length, gives them, since the placement reads only lengths. *)
Definition rr_link_cfg `{MP : MachineParameters} (base : Z) (ot : OType)
    (adv : list (string * link_adv)) (k : nat) (fw : firmware) : link_cfg :=
  let n := length (fw_threads fw) in
  let cfg0 := MkLinkCfg base ot
                (("sched", rr_sched_adv (replicate (3 + S n) (WInt 0))) :: adv)
                (replicate k (WInt 0)) in
  MkLinkCfg base ot
    (("sched", rr_sched_adv (rr_sched_data fw (place cfg0 fw).1)) :: adv)
    (replicate k (WInt 0)).

(** The PC is at [a]. *)
Definition pc_at (a : Addr) (φ : ExecConf) : bool :=
  match pcc φ with
  | WCap _ _ _ _ _ a' => bool_decide (a' = a)
  | _ => false
  end.

(** The address of the scheduler's return to the switcher in [img]. *)
Definition rr_sched_ret_addr (img : fw_image) : Addr :=
  (cmpt_a_code (cmpt_of img "sched") ^+ 25)%a.

(** The scheduler is about to return from a call with cause [c]. *)
Definition rr_returning (img : fw_image) (c : Z) (φ : ExecConf) : bool :=
  pc_at (rr_sched_ret_addr img) φ && bool_decide (reg φ !! ca1 = Some (WInt c)).

(** The registers of the start that are zero, for [img_regs]. *)
Ltac solve_start_other_registers :=
  intros r Hr; cbn [pcc reg sreg mem shadowtbl fst snd];
  rewrite !lookup_insert_ne; try (intros ->; apply Hr; set_solver+);
  apply lookup_gset_to_gmap_Some; split; [apply all_registers_s_correct | done].
