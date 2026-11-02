From griotte Require Import machine_base heap_layout mmio_shadow trap_fault.

(** The revoker is a memory-mapped device at a single address, outside the
    heap and the shadow region. A store to it sweeps memory; a load from it
    reads as zero. *)
Class RevokerRegion := {
    revoker_addr : Addr;
  }.

Definition is_revoker_address `{RevokerRegion} (a : Addr) : bool :=
  bool_decide (a = revoker_addr).

Lemma is_revoker_address_spec `{RevokerRegion} a :
  is_revoker_address a = true <-> a = revoker_addr.
Proof. rewrite /is_revoker_address. apply bool_decide_eq_true. Qed.

(** * The revoker device *)
Section revoker_device.
  Context `{HeapRegion}.

  (** The revoker's atomic sweep clears the tag of exactly the words that the
      CLoad filter strips: those whose heap base is quarantined. *)
  Definition sweep_word (shadow : ShadowTbl) (w : Word) : Word :=
    match heap_cap_base w with
    | Some base =>
        match shadow !! base with
        | Some ShadowQuarantined => clear_tag w
        | _ => w
        end
    | None => w
    end.

  Definition sweep_mem (shadow : ShadowTbl) (m : Mem) : Mem :=
    sweep_word shadow <$> m.

  (** A load from the revoker reads as zero. *)
  Definition revoker_load (ea : Addr) : option Word := Some (WInt 0).

  (** The revoker raises no access fault of its own. *)
  Definition revoker_load_fault (ea : Addr) : fault := fault_default.
  Definition revoker_store_fault (ea : Addr) (w : Word) : fault := fault_default.
End revoker_device.
