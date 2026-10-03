From iris.base_logic Require Export invariants na_invariants gen_heap ghost_map ghost_var.
From iris.program_logic Require Export weakestpre.
From griotte Require Import griotte_lang entry.
From griotte Require Import alloc_registry.



(* Non atomic invariants *)
Class cerise_na_invs Σ :=
  {
    na_invG :: na_invG Σ;
    cerise_nais : na_inv_pool_name;
  }.

(* CMRA for Cerise *)
Class ceriseG Σ :=
  CeriseG {
      cerise_invG : invGS Σ;
      cerise_nainvG :: cerise_na_invs Σ;
      mem_gen_memG :: gen_heapGS Addr Word Σ; (* memory *)
      shadowtbl_gen_regG :: gen_heapGS Addr AllocStatus Σ; (* shadow table *)
      reg_gen_regG :: gen_heapGS RegName Word Σ; (* register *)
      sreg_gen_regG :: gen_heapGS SRegName Word Σ; (* system register *)
      entryG :: entryGS Σ; (* entry point *)
      cerise_registryG :: allocRegistryG Σ (* allocation registry *)
    }.

(* Memory never covers a memory-mapped address (shadow region or revoker):
   Load and Store reach those devices only through their dedicated branches. *)
Definition mem_avoids_mmio `{MachineParameters} (m : Mem) : Prop :=
  ∀ a, a ∈ dom m → is_mmio_address a = false.

Section mem_avoids_mmio.
  Context `{MachineParameters}.

  Lemma mem_avoids_mmio_lookup m a w :
    mem_avoids_mmio m → m !! a = Some w → is_mmio_address a = false.
  Proof. intros Hm Ha. apply Hm. by apply elem_of_dom_2 in Ha. Qed.

  Lemma mem_avoids_mmio_not_shadow m a w :
    mem_avoids_mmio m → m !! a = Some w → is_shadow_address a = false.
  Proof. intros. eapply not_mmio_not_shadow, mem_avoids_mmio_lookup; eauto. Qed.

  Lemma mem_avoids_mmio_not_revoker m a w :
    mem_avoids_mmio m → m !! a = Some w → is_revoker_address a = false.
  Proof. intros. eapply not_mmio_not_revoker, mem_avoids_mmio_lookup; eauto. Qed.

  Lemma mem_avoids_mmio_insert m a w :
    is_mmio_address a = false → mem_avoids_mmio m → mem_avoids_mmio (<[a := w]> m).
  Proof.
    intros Ha Hm a'. rewrite dom_insert_L elem_of_union elem_of_singleton.
    intros [-> | Ha']; [done | by apply Hm].
  Qed.

  Lemma mem_avoids_mmio_update m a w w' :
    m !! a = Some w' → mem_avoids_mmio m → mem_avoids_mmio (<[a := w]> m).
  Proof.
    intros Ha Hm. apply mem_avoids_mmio_insert; last done.
    eapply mem_avoids_mmio_lookup; eauto.
  Qed.

  Lemma mem_avoids_mmio_sweep shadow m :
    mem_avoids_mmio m → mem_avoids_mmio (sweep_mem shadow m).
  Proof. intros Hm a. rewrite dom_sweep_mem. apply Hm. Qed.

  Lemma mem_avoids_mmio_union m1 m2 :
    mem_avoids_mmio m1 → mem_avoids_mmio m2 → mem_avoids_mmio (m1 ∪ m2).
  Proof.
    intros Hm1 Hm2 a. rewrite dom_union_L elem_of_union.
    intros [Ha | Ha]; [by apply Hm1 | by apply Hm2].
  Qed.

  Lemma mem_avoids_mmio_empty : mem_avoids_mmio ∅.
  Proof. intros a. rewrite dom_empty_L. set_solver. Qed.

  Lemma updatePC_gen_mem φ imm c :
    updatePC_gen φ imm = Some c → mem c.2 = mem φ.
  Proof. rewrite /updatePC_gen. repeat case_match; intros; simplify_eq; done. Qed.

  (* Every instruction preserves the clause: Load and Store reach the shadow
     region and the revoker through their own branches, an ordinary store
     writes a non-MMIO address, and the sweep keeps the memory's domain. *)
  Lemma exec_mem_avoids_mmio i p φ :
    mem_avoids_mmio (mem φ) → mem_avoids_mmio (mem (exec i p φ).2).
  Proof.
    intros Hφ. rewrite /exec.
    destruct (exec_opt i p φ) as [c|] eqn:Hexec; last done.
    destruct i; cbn in Hexec; repeat case_match; simplify_eq; try done.
    all: repeat match goal with
      | H : mbind _ ?x = Some _ |- _ => destruct x eqn:?; cbn in H; try discriminate
      | H : (match ?x with _ => _ end) = Some _ |- _ =>
          destruct x eqn:?; cbn in H; try discriminate
      end.
    all: try (match goal with H : updatePC_gen _ _ = Some _ |- _ =>
                rewrite (updatePC_gen_mem _ _ _ H) end).
    all: try (match goal with H : updatePC _ = Some _ |- _ =>
                rewrite (updatePC_gen_mem _ _ _ H) end).
    all: try (match goal with H : Some _ = Some _ |- _ => injection H as <- end).
    all: cbn; try done.
    - (* Revoker store *)
      by apply mem_avoids_mmio_sweep.
    - (* Ordinary store *)
      apply mem_avoids_mmio_insert; last done.
      by rewrite /is_mmio_address Heqb2 Heqb3.
  Qed.

  Lemma step_mem_avoids_mmio (cf cf' : ConfFlag) (φ φ' : ExecConf) :
    griotte_opsem.step (cf, φ) (cf', φ') →
    mem_avoids_mmio (mem φ) →
    mem_avoids_mmio (mem φ').
  Proof.
    inversion 1; subst; try done.
    intros. by apply exec_mem_avoids_mmio.
  Qed.
End mem_avoids_mmio.

(* invariants for memory, and a state interpretation for (mem,reg) *)
Global Instance memG_irisG `{MachineParameters} `{!ceriseG Σ} : irisGS griotte_lang Σ := {
  iris_invGS := cerise_invG;
  state_interp σ _ κs _ := (((((gen_heap_interp (reg σ))
                            ∗ (gen_heap_interp (sreg σ)))
                            ∗ (gen_heap_interp (mem σ)))
                            ∗ (gen_heap_interp (shadowtbl σ)))
                            ∗ ⌜mem_avoids_mmio (mem σ)⌝
                           )%I;
  fork_post _ := True%I;
  num_laters_per_step _ := 0;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.

(* Points to predicates for registers *)
Notation "r ↦ᵣ{ q } w" := (pointsto (L:=RegName) (V:=Word) r q w)
  (at level 20, q at level 50, format "r  ↦ᵣ{ q }  w") : bi_scope.
Notation "r ↦ᵣ w" := (pointsto (L:=RegName) (V:=Word) r (DfracOwn 1) w) (at level 20) : bi_scope.
Notation "r ↦ᵣ -" := (∃ w, pointsto (L:=RegName) (V:=Word) r (DfracOwn 1) w)%I (at level 20) : bi_scope.

(* Points to predicates for system registers *)
Notation "sr ↦ₛᵣ{ q } w" := (pointsto (L:=SRegName) (V:=Word) sr q w)
  (at level 20, q at level 50, format "sr  ↦ₛᵣ{ q }  w") : bi_scope.
Notation "sr ↦ₛᵣ w" := (pointsto (L:=SRegName) (V:=Word) sr (DfracOwn 1) w) (at level 20) : bi_scope.
Notation "sr ↦ₛᵣ -" := (∃ w, pointsto (L:=SRegName) (V:=Word) sr (DfracOwn 1) w)%I (at level 20) : bi_scope.

(* Points to predicates for memory *)
Notation "a ↦ₐ{ q } w" := (pointsto (L:=Addr) (V:=Word) a q w)
  (at level 20, q at level 50, format "a  ↦ₐ{ q }  w") : bi_scope.
Notation "a ↦ₐ w" := (pointsto (L:=Addr) (V:=Word) a (DfracOwn 1) w) (at level 20) : bi_scope.
Notation "a ↦ₐ -" := (∃ w, pointsto (L:=Addr) (V:=Word) a (DfracOwn 1) w)%I (at level 20) : bi_scope.

(* Points to predicates for shadow table *)
Notation "a ↦ₛ{ q } b" := (pointsto (L:=Addr) (V:=AllocStatus) a q b)
  (at level 20, q at level 50, format "a  ↦ₛ{ q }  b") : bi_scope.
Notation "a ↦ₛ b" := (pointsto (L:=Addr) (V:=AllocStatus) a (DfracOwn 1) b) (at level 20) : bi_scope.
Notation "a ↦ₛ -" := (∃ b, pointsto (L:=Addr) (V:=AllocStatus) a (DfracOwn 1) b)%I (at level 20) : bi_scope.
