From stdpp Require Import gmap fin_maps list.
From griotte Require Export griotte_opsem.

Section opsem_prop.
  Context `{MachineParameters}.
(*--- z_of_argument ---*)

Lemma z_of_argument_Some_inv (regs: Reg) (arg: Z + RegName) (z:Z) :
  z_of_argument regs arg = Some z →
  (arg = inl z ∨ ∃ r, arg = inr r ∧ regs !!ᵣ r = Some (WInt z)).
Proof.
  unfold z_of_argument. intro. repeat case_match; simplify_eq/=; eauto.
Qed.

Lemma z_of_argument_Some_inv' (regs regs': Reg) (arg: Z + RegName) (z:Z) :
  z_of_argument regs arg = Some z →
  regs ⊆ regs' →
  (arg = inl z ∨ ∃ r, arg = inr r ∧ regs !!ᵣ r = Some (WInt z) ∧ regs' !!ᵣ r  = Some (WInt z)).
Proof.
  unfold z_of_argument. intro. repeat case_match; simplify_eq/=; eauto.
  intros HH. unshelve epose proof (lookup_reg_weaken _ _ _ _ _ HH); eauto.
Qed.

Lemma z_of_arg_mono (regs r: Reg) arg argz:
regs ⊆ r
-> z_of_argument regs arg = Some argz
-> z_of_argument r arg = Some argz.
Proof.
  intros.
  unfold z_of_argument in *.
  destruct arg; auto. destruct (lookup_reg _ _)  eqn:Heq; [| congruence].
  eapply lookup_reg_weaken in Heq as ->; auto.
Qed.

(*--- word_of_argument ---*)
Lemma word_of_argument_Some_inv (regs: Reg) (arg: Z + RegName) (w:Word) :
  word_of_argument regs arg = Some w →
  ((∃ z, arg = inl z ∧ w = WInt z) ∨
   (∃ r, arg = inr r ∧ regs !!ᵣ r = Some w)).
Proof.
  unfold word_of_argument. intro. repeat case_match; simplify_eq/=; eauto.
Qed.

Lemma word_of_argument_Some_inv' (regs regs': Reg) (arg: Z + RegName) (w:Word) :
  word_of_argument regs arg = Some w →
  regs ⊆ regs' →
  ((∃ z, arg = inl z ∧ w = WInt z) ∨
   (∃ r, arg = inr r ∧ regs !!ᵣ r = Some w ∧ regs' !!ᵣ r = Some w)).
Proof.
  unfold word_of_argument. intro. repeat case_match; simplify_eq/=; eauto.
  intros HH. unshelve epose proof (lookup_reg_weaken _ _ _ _ _ HH); eauto.
Qed.

Lemma word_of_argument_inr (regs: Reg) (arg: Z + RegName) p g b e a:
  word_of_argument regs arg = Some (WCap p g b e a) →
  (∃ r : RegName, arg = inr r ∧ regs !!ᵣ r = Some (WCap p g b e a)).
Proof.
  intros HStoreV.
  unfold word_of_argument in HStoreV.
  destruct arg.
      - by inversion HStoreV.
      - exists r. destruct (regs !!ᵣ r) eqn:Hvr0; last by inversion HStoreV.
        split; auto.
Qed.

Lemma word_of_arg_mono (regs r: Reg) arg w:
regs ⊆ r
-> word_of_argument regs arg = Some w
-> word_of_argument r arg = Some w.
Proof.
  intros.
  unfold word_of_argument in *.
  destruct arg; auto. destruct (_ !!ᵣ _)  eqn:Heq; [| congruence].
  eapply lookup_reg_weaken in Heq as ->; auto.
Qed.

(*--- addr_of_argument ---*)

Lemma addr_of_argument_Some_inv (regs: Reg) (arg: Z + RegName) (a:Addr) :
  addr_of_argument regs arg = Some a →
  ∃ z, z_to_addr z = Some a ∧
       (arg = inl z ∨ ∃ r, arg = inr r ∧ regs !!ᵣ r = Some (WInt z)).
Proof.
  unfold addr_of_argument, z_of_argument.
  intro. repeat case_match; simplify_eq/=; eauto. eexists. eauto.
Qed.

Lemma addr_of_argument_Some_inv' (regs regs': Reg) (arg: Z + RegName) (a:Addr) :
  addr_of_argument regs arg = Some a →
  regs ⊆ regs' →
  ∃ z, z_to_addr z = Some a ∧
       (arg = inl z ∨ ∃ r, arg = inr r ∧ regs !!ᵣ r = Some (WInt z) ∧ regs' !!ᵣ r = Some (WInt z)).
Proof.
  unfold addr_of_argument, z_of_argument.
  intros ? HH. repeat case_match; simplify_eq/=; eauto. eexists. split; eauto.
  unshelve epose proof (lookup_reg_weaken _ _ _ _ _ HH); eauto.
Qed.

Lemma addr_of_arg_mono (regs r: Reg) arg w:
regs ⊆ r
-> addr_of_argument regs arg = Some w
-> addr_of_argument r arg = Some w.
Proof.
  intros.
  unfold addr_of_argument, z_of_argument in *.
  destruct arg; auto. destruct (_ !!ᵣ _)  eqn:Heq; [| congruence].
  eapply lookup_reg_weaken in Heq as ->; auto.
Qed.

(*--- otype_of_argument ---*)

Lemma otype_of_argument_Some_inv (regs: Reg) (arg: Z + RegName) (o:OType) :
  otype_of_argument regs arg = Some o →
  ∃ z, z_to_otype z = Some o ∧
       (arg = inl z ∨ ∃ r, arg = inr r ∧ regs !!ᵣ r = Some (WInt z)).
Proof.
  unfold otype_of_argument, z_of_argument.
  intro. repeat case_match; simplify_eq/=; eauto. eexists. eauto.
Qed.

Lemma otype_of_argument_Some_inv' (regs regs': Reg) (arg: Z + RegName) (o:OType) :
  otype_of_argument regs arg = Some o →
  regs ⊆ regs' →
  ∃ z, z_to_otype z = Some o ∧
       (arg = inl z ∨ ∃ r, arg = inr r ∧ regs !!ᵣ r = Some (WInt z) ∧ regs' !!ᵣ r = Some (WInt z)).
Proof.
  unfold otype_of_argument, z_of_argument.
  intros ? HH. repeat case_match; simplify_eq/=; eauto. eexists. split; eauto.
  unshelve epose proof (lookup_reg_weaken _ _ _ _ _ HH); eauto.
Qed.

Lemma otype_of_arg_mono (regs r: Reg) arg w:
regs ⊆ r
-> otype_of_argument regs arg = Some w
-> otype_of_argument r arg = Some w.
Proof.
  intros.
  unfold otype_of_argument, z_of_argument in *.
  destruct arg; auto. destruct (_ !!ᵣ _)  eqn:Heq; [| congruence].
  eapply lookup_reg_weaken in Heq as ->; auto.
Qed.


  Lemma normal_always_step:
    forall φ, exists cf φ', step (Executable, φ) (cf, φ').
  Proof.
    intros. destruct (reg φ !! PC) as [wpc | ] eqn:Hreg
    ; last (eexists _,_; by econstructor).
    destruct (isCorrectPC_dec wpc) as [Hcorr | ]
    ; last (eexists _,_; by econstructor).
    set (Hcorr' := Hcorr).
    inversion Hcorr' as [?????? Hre]. subst wpc.
    destruct (mem φ !! a) as [wa | ] eqn:Hmem.
    all: eexists _,_; by econstructor.
  Qed.

  Lemma step_deterministic:
    forall c1 c2 c2' σ1 σ2 σ2',
      step (c1, σ1) (c2, σ2) →
      step (c1, σ1) (c2', σ2') →
      c2 = c2' ∧ σ2 = σ2'.
  Proof.
    intros * H1 H2; split; inv H1; inv H2; auto; try congruence.
  Qed.

  Lemma step_exec_inv
    (regs: Reg) (sregs : SReg) (mem : Mem)
    (p : Perm) (g : Locality) (b e a : Addr) (w : Word)
    (instr : instr) (c: ConfFlag) (σ: ExecConf) :
    regs !! PC = Some (WCap p g b e a) →
    isCorrectPC (WCap p g b e a) →
    mem !! a = Some w →
    decodeInstrW w = instr →
    step (Executable, (regs, sregs, mem)) (c, σ) →
    exec instr p (regs, sregs, mem) = (c, σ).
  Proof.
    intros HPC Hpc Hm Hinstr. inversion 1; cbn in *.
    1,2,3: congruence.
    simplify_eq. by destruct (exec _ _).
  Qed.

  Lemma step_fail_inv (wpc : Word) (c : ConfFlag) (σ σ': ExecConf) :
    reg σ !! PC = Some wpc →
    ¬ isCorrectPC wpc →
    step (Executable, σ) (c, σ') →
    c = Failed ∧ σ' = σ.
  Proof.
    intros Hw HPC Hs. inversion Hs; subst; auto.
    congruence.
  Qed.

  Lemma updatePC_gen_some φ imm c:
    updatePC_gen φ imm = Some c → ∃ φ', c = (NextI, φ').
  Proof.
    rewrite /updatePC_gen; repeat case_match; try congruence. inversion 1. eauto.
  Qed.

  Lemma updatePC_some φ c:
    updatePC φ = Some c → ∃ φ', c = (NextI, φ').
  Proof.
    rewrite /updatePC; apply updatePC_gen_some.
  Qed.

  Lemma instr_atomic i p φ :
    ∃ φ', (exec i p φ = (Failed, φ') ) ∨ (exec i p φ = (NextI, φ')) ∨
          (exec i p φ = (Halted, φ')).
  Proof.
    unfold exec, exec_opt.
    repeat case_match; simplify_eq; eauto;rename H0 into Heqo.
    (* Create more goals through *_of_argument, now that some have been pruned *)
    all: repeat destruct (addr_of_argument (reg φ) _)
    ; repeat destruct (otype_of_argument (reg φ) _)
    ; repeat destruct (word_of_argument (reg φ) _)
    ; repeat destruct (z_of_argument (reg φ) _)
    ; cbn in *; try by exfalso.
    all: repeat destruct (reg _ !!ᵣ _); cbn in *; repeat case_match.
    all: repeat destruct (reg _ !! PC); cbn in *; repeat case_match.
    all: repeat destruct (sreg _ !! _); cbn in *; repeat case_match.
    all: repeat destruct (mem _ !! _); cbn in *; repeat case_match.
    all: simplify_eq; try by exfalso.
    all: try apply updatePC_some in Heqo as [φ' Heqo]; eauto.
    all: try apply updatePC_gen_some in Heqo as [φ' Heqo]; eauto.
  Qed.

End opsem_prop.
