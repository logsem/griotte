From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules proofmode.
From cap_machine Require Import checkra checkints check_valid_stack_object check_no_overlap_spec.
From cap_machine Require Import region_invariants_revocation.
From cap_machine Require Import logrel.


Section Check_Valid_SO_spec.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
  .

  Context {C : CmptName}.

  Lemma check_valid_stack_object_spec
    (W : WORLD)
    (rsrc r1 r2 : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (csp_b csp_e csp_a : Addr)
    (wsrc w1 w2 : Word)
    (φ : language.val cap_lang → iPropI Σ) :

    let check_valid_stack_object := (check_valid_stack_object_instrs rsrc r1 r2) in
    let a_last := (pc_a ^+ length check_valid_stack_object)%a in
    executeAllowed pc_p = true →
    SubBounds pc_b pc_e pc_a a_last →

    ▷ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
    ∗ ▷ rsrc ↦ᵣ wsrc
    ∗ ▷ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_a
    ∗ ▷ r1 ↦ᵣ w1
    ∗ ▷ r2 ↦ᵣ w2
    ∗ ▷ region W C ∗ ▷ sts_full_world W C ∗ ▷ interp W C wsrc
    ∗ ▷ codefrag pc_a check_valid_stack_object
    ∗ ▷ ( (∃ p g b e a,
          ⌜ wsrc = WCap p g b e a⌝
          ∗ ⌜ readAllowed p = true ⌝
          ∗ ⌜ (finz.seq_between b e) ## (finz.seq_between csp_b csp_e) ⌝
          ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e a_last
          ∗ rsrc ↦ᵣ wsrc
          ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_a
          ∗ r1 ↦ᵣ WInt 0%Z
          ∗ r2 ↦ᵣ WInt 0%Z
          ∗ region W C ∗ sts_full_world W C ∗ interp (revoke W) C wsrc
          ∗ codefrag pc_a check_valid_stack_object )
            -∗ WP Seq (Instr Executable) {{ φ }}
        )
    ∗ ▷ φ FailedV
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
  Admitted.


End Check_Valid_SO_spec.
