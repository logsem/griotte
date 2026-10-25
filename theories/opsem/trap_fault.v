From stdpp Require Import finite.
From griotte Require Import machine_base.

(** * What a fault reports

    Trap entry writes the cause of a fault to mcause and a value to mtval.
    Both come from one description of the fault, in cheriot-sail's terms: a
    CHERI fault, with a cause code and the register that caused it, an
    illegal instruction, or an access fault, with the faulting address. *)

(** CHERIoT's [CauseCode] ([sdk/include/cheri.h]), restricted to the codes
    that the machine raises. *)
Inductive cheri_cause_code : Type :=
| BoundsViolation
| TagViolation
| SealViolation
| PermitExecuteViolation
| PermitLoadViolation
| PermitStoreViolation
| PermitAccessSystemRegistersViolation.

(** CHERIoT's [RegisterNumber] ([sdk/include/cheri.h]), restricted to the
    machine's registers: a general register, the PC, and the special
    capability registers. *)
Inductive cheri_reg : Type :=
| CheriGPR (r : RegName)
| CheriPCC
| CheriMTCC
| CheriMTDC
| CheriMEPCC.

(** A fault: a CHERI fault on a register, an illegal instruction, or an
    access fault on an instruction fetch, a load or a store, at an
    address. *)
Inductive fault : Type :=
| FaultCheri (c : cheri_cause_code) (r : cheri_reg)
| FaultIllegal
| FaultInstAccess (a : Addr)
| FaultLoadAccess (a : Addr)
| FaultStoreAccess (a : Addr).

#[global] Instance cheri_cause_code_eq_dec : EqDecision cheri_cause_code.
Proof. solve_decision. Defined.

#[global] Instance cheri_reg_eq_dec : EqDecision cheri_reg.
Proof. solve_decision. Defined.

#[global] Instance fault_eq_dec : EqDecision fault.
Proof. solve_decision. Defined.

#[global] Instance cheri_cause_code_finite : Finite cheri_cause_code.
Proof.
  refine {| enum := [BoundsViolation; TagViolation; SealViolation;
                     PermitExecuteViolation; PermitLoadViolation; PermitStoreViolation;
                     PermitAccessSystemRegistersViolation] |}.
  - repeat constructor; set_solver.
  - intros []; set_solver.
Defined.

#[global] Instance cheri_reg_finite : Finite cheri_reg.
Proof.
  refine {| enum := (CheriGPR <$> enum RegName) ++
                    [CheriPCC; CheriMTCC; CheriMTDC; CheriMEPCC] |}.
  - apply NoDup_app. split_and!.
    + apply NoDup_fmap; [by intros ? ? [=] | apply NoDup_enum].
    + intros x Hx. apply list_elem_of_fmap in Hx as (r & -> & _). set_solver.
    + repeat constructor; set_solver.
  - intros [r| | | |]; rewrite elem_of_app; [left | right; set_solver ..].
    apply list_elem_of_fmap. exists r. split; first done. apply elem_of_enum.
Defined.

(** The number of a general register: its RISC-V index. *)
Definition reg_index (r : RegName) : Z :=
  match r with registers.R n _ => Z.of_nat n end.

#[global] Instance reg_index_inj : Inj (=) (=) reg_index.
Proof.
  intros [n fin] [m fin'] Heq. cbn in Heq.
  assert (n = m) as <- by lia.
  f_equal. apply (eq_pi _ _).
Qed.

Lemma reg_index_range r : (0 ≤ reg_index r ≤ Z.of_nat RegNum)%Z.
Proof. destruct r as [n fin]. cbn. apply Nat.leb_le in fin. lia. Qed.

Lemma reg_index_surj (z : Z) : (0 ≤ z ≤ Z.of_nat RegNum)%Z → ∃ r, reg_index r = z.
Proof.
  intros Hz. assert (Z.to_nat z <=? RegNum = true) as fin.
  { apply Nat.leb_le. lia. }
  exists (registers.R (Z.to_nat z) fin). cbn. lia.
Qed.

(** The element of a finite type with the image [y] by [f], if any: the
    first in the enumeration. *)
Definition finite_preimage `{Finite A} `{EqDecision B} (f : A → B) (y : B) : option A :=
  head (filter (λ x, f x = y) (enum A)).

Lemma head_filter_elem_of {A} (P : A → Prop) `{∀ x, Decision (P x)} (l : list A) x :
  x ∈ l → P x → ∃ y, head (filter P l) = Some y ∧ P y.
Proof.
  induction l as [|z l IH]; intros Hx HP; first by apply not_elem_of_nil in Hx.
  rewrite filter_cons. case_decide as Hz; first by eexists.
  apply elem_of_cons in Hx as [-> | Hx]; first done. by apply IH.
Qed.

Lemma finite_preimage_inj `{Finite A} `{EqDecision B} (f : A → B) `{!Inj (=) (=) f} x :
  finite_preimage f (f x) = Some x.
Proof.
  rewrite /finite_preimage.
  destruct (head_filter_elem_of (λ y, f y = f x) (enum A) x) as (y & -> & Hy);
    [apply elem_of_enum | done |].
  by rewrite (inj f _ _ Hy).
Qed.
