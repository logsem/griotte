From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel addr_reg_sample fundamental rules proofmode.

Section getotype.

  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  Definition getotype_instrs r := encodeInstrsW [ GetOType r_t1 r ].

  Lemma getotype_spec r w pc_p pc_b pc_e a_first φ :
    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length (getotype_instrs r))%a →

      ▷ codefrag a_first (getotype_instrs r)
    ∗ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e a_first
    ∗ ▷ r ↦ᵣ w
    ∗ ▷ r_t1 ↦ᵣ WInt 0%Z
    ∗ ▷ (r_t1 ↦ᵣ WInt (-1)%Z -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont) "(>Hprog & >HPC & >Hr & >Hr_t1 & Hφ)".
    codefrag_facts "Hprog".
    iInstr "Hprog".
    Admitted.

End getotype.
