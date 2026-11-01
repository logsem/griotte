From griotte Require Import machine_base heap_layout mmio_shadow mmio_revoker trap_fault
  exec_conf.

(* Memory-mapped addresses are never memory: the shadow region and the revoker. *)
Definition is_mmio_address `{ShadowRegion} `{RevokerRegion} (a : Addr) : bool :=
  is_shadow_address a || is_revoker_address a.

Lemma not_mmio_not_shadow `{ShadowRegion} `{RevokerRegion} a :
  is_mmio_address a = false -> is_shadow_address a = false.
Proof. rewrite /is_mmio_address. by intros [? ?]%orb_false_iff. Qed.

Lemma not_mmio_not_revoker `{ShadowRegion} `{RevokerRegion} a :
  is_mmio_address a = false -> is_revoker_address a = false.
Proof. rewrite /is_mmio_address. by intros [? ?]%orb_false_iff. Qed.

(* A range that addresses no memory-mapped device. *)
Definition disjoint_from_mmio `{ShadowRegion} `{RevokerRegion} (b e : Addr) : Prop :=
  disjoint_from_shadow b e ∧ revoker_addr ∉ finz.seq_between b e.

Lemma disjoint_from_mmio_shadow `{ShadowRegion} `{RevokerRegion} (b e : Addr) :
  disjoint_from_mmio b e → disjoint_from_shadow b e.
Proof. by intros [? _]. Qed.

Lemma disjoint_from_mmio_not_in `{ShadowRegion} `{RevokerRegion} (b e a : Addr) :
  disjoint_from_mmio b e →
  withinBounds b e a = true →
  is_mmio_address a = false.
Proof.
  intros [Hshadow Hrev] Hbounds. rewrite /is_mmio_address.
  rewrite (disjoint_from_shadow_not_in b e a Hshadow Hbounds) /=.
  apply bool_decide_eq_false. intros ->. apply Hrev.
  apply elem_of_finz_seq_between. by apply withinBounds_true_iff.
Qed.

Lemma disjoint_from_mmio_weaken `{ShadowRegion} `{RevokerRegion} (b e b' e' : Addr) :
  (b <= b')%a → (e' <= e)%a →
  disjoint_from_mmio b e → disjoint_from_mmio b' e'.
Proof.
  intros Hb He [Hshadow Hrev]. split.
  - rewrite /disjoint_from_shadow in Hshadow |- *.
    intros x Hx Hx'. apply (Hshadow x); last done.
    apply elem_of_finz_seq_between in Hx. apply elem_of_finz_seq_between. solve_addr.
  - intros Hx. apply Hrev.
    apply elem_of_finz_seq_between in Hx. apply elem_of_finz_seq_between. solve_addr.
Qed.

(** * The dispatch to the devices

    A load from or a store to a memory-mapped address goes to the device at
    that address. The devices act on their own state; the dispatch lifts
    them to the configuration. *)
Section mmio_dispatch.
  Context `{HeapRegion} `{ShadowRegion} `{!HeapShadowTranslation}
    `{AllocStatusEncoding} `{RevokerRegion}.

  Definition revoker_sweep (φ : ExecConf) : ExecConf :=
    {| pcc := pcc φ; reg := reg φ; sreg := sreg φ;
       mem := sweep_mem (shadowtbl φ) (mem φ); shadowtbl := shadowtbl φ |}.

  (** A load from the memory-mapped address [ea], by the device at [ea]. *)
  Definition mmio_load (φ : ExecConf) (ea : Addr) : option Word :=
    if is_shadow_address ea then shadow_load (shadowtbl φ) ea
    else if is_revoker_address ea then revoker_load ea
    else None.

  (** A store of [w] to the memory-mapped address [ea], by the device at
      [ea]: it gives the configuration after the store. A store to the
      revoker sweeps memory; the value is ignored. *)
  Definition mmio_store (φ : ExecConf) (ea : Addr) (w : Word) : option ExecConf :=
    if is_shadow_address ea then
      sh' ← shadow_store (shadowtbl φ) ea w;
      Some (set_shadowtbl φ sh')
    else if is_revoker_address ea then Some (revoker_sweep φ)
    else None.

  (** The fault of a load from, or a store of [w] to, the memory-mapped
      address [ea], once the capability checks pass. *)
  Definition mmio_load_fault (φ : ExecConf) (ea : Addr) : fault :=
    if is_shadow_address ea then shadow_load_fault (shadowtbl φ) ea
    else if is_revoker_address ea then revoker_load_fault ea
    else fault_default.

  Definition mmio_store_fault (φ : ExecConf) (ea : Addr) (w : Word) : fault :=
    if is_shadow_address ea then shadow_store_fault ea w
    else if is_revoker_address ea then revoker_store_fault ea w
    else fault_default.
End mmio_dispatch.
