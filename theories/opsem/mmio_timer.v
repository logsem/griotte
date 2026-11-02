From griotte Require Import machine_base trap_fault cap_bits.

(** The time devices of the core-local interruptor: the timer [mtime] and
    the timer threshold [mtimecmp], each a 64-bit register at an address of
    its own, outside the heap, the shadow region and the revoker. Each is
    one word: there is no access to a half.

    The time devices exist so that the untrusted scheduler can be given an
    MMIO capability to the timer: its code programs [mtimecmp]. Trusted code
    (the switcher) and code outside the scheduler never use them. *)
Class TimeDevRegion := {
    mtime_addr : Addr;
    mtimecmp_addr : Addr;
    mtime_mtimecmp_ne : mtime_addr ≠ mtimecmp_addr;
  }.
(* No [Hint Mode]: the class has no parameter, hence no input position. *)

Definition is_time_device_address `{TimeDevRegion} (a : Addr) : bool :=
  bool_decide (a = mtime_addr) || bool_decide (a = mtimecmp_addr).

Lemma is_time_device_address_spec `{TimeDevRegion} a :
  is_time_device_address a = true <-> a = mtime_addr ∨ a = mtimecmp_addr.
Proof. rewrite /is_time_device_address orb_true_iff !bool_decide_eq_true. done. Qed.

(* A range that addresses no time device. *)
Definition disjoint_from_time_devs `{TimeDevRegion} (b e : Addr) : Prop :=
  mtime_addr ∉ finz.seq_between b e ∧ mtimecmp_addr ∉ finz.seq_between b e.

(** The values of the time devices' registers [mtime] and [mtimecmp].

    The time devices exist so that the untrusted scheduler can be given an
    MMIO capability to the timer: its code programs [mtimecmp]. Trusted code
    (the switcher) and code outside the scheduler never use them. *)
Record TimeDevs := MkTimeDevs {
  td_mtime : Z;
  td_mtimecmp : Z;
}.

#[global] Instance TimeDevs_eq_dec : EqDecision TimeDevs.
Proof. solve_decision. Defined.

#[global] Instance TimeDevs_inhabited : Inhabited TimeDevs :=
  populate (MkTimeDevs 0 0).

(** The time devices hold 64-bit values. *)
Definition TIME_MODULUS : Z := 2 ^ 64.

(** A tick of the timer, as sail-riscv's [tick_clock]: [mtime] grows by one,
    modulo 2^64. *)
Definition time_dev_tick (td : TimeDevs) : TimeDevs :=
  {| td_mtime := (td_mtime td + 1) mod TIME_MODULUS; td_mtimecmp := td_mtimecmp td |}.

(** * The time devices *)
Section time_device.
  Context `{TimeDevRegion} `{CapBitsEncoding}.

  (** The register at the time-device address [a]: [mtime] at its address,
      [mtimecmp] at the other. *)
  Definition time_dev_value (td : TimeDevs) (a : Addr) : Z :=
    if bool_decide (a = mtime_addr) then td_mtime td else td_mtimecmp td.

  (** A store of [z] to [mtimecmp] writes its low 64 bits. *)
  Definition set_mtimecmp (z : Z) (td : TimeDevs) : TimeDevs :=
    {| td_mtime := td_mtime td; td_mtimecmp := z mod TIME_MODULUS |}.

  (** A load from a time device reads the integer value of its register. *)
  Definition time_dev_load (td : TimeDevs) (ea : Addr) : option Word :=
    Some (WInt (time_dev_value td ea)).

  (** [mtimecmp] receives the bits of any word, as sail-riscv's
      [clint_store]. A store to [mtime] fails. *)
  Definition time_dev_store (td : TimeDevs) (ea : Addr) (w : Word) : option TimeDevs :=
    if bool_decide (ea = mtimecmp_addr) then Some (set_mtimecmp (word_to_bits w) td)
    else None.

  (** A load raises no access fault of its own. A failing store is a store
      access fault, as sail-riscv's [clint_store] at an address it does not
      map. *)
  Definition time_dev_load_fault (ea : Addr) : fault := fault_default.
  Definition time_dev_store_fault (ea : Addr) (w : Word) : fault :=
    if bool_decide (ea = mtimecmp_addr) then fault_default else FaultStoreAccess ea.
End time_device.
