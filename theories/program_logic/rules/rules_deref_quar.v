From iris.proofmode Require Import proofmode.
From griotte Require Import rules_Load rules_Store rules_registry.

(** * Dereferencing a capability of a quarantined object

    A register word with authority whose identifier [ι] is quarantined or
    dead has an untagged physical copy ([reg_phys]). [reg_refilter] clears
    its logical tag from [ι ⊒ AQuar]; a CLoad from it, or a Store through
    it, then faults on the tag. These derived rules need no cell of the
    target, so they apply after the object's cells are gone. The register
    ends with the untagged word.

    For CLoad only the source register is read on the fault path, so the
    rules need no resource for the destination, and [dst = src] needs no
    separate rule. For Store only the address register is read. *)

Section rules_deref_quar.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {CL : CritLink Σ}.
  Implicit Types P Q : iProp Σ.

  (** The register lookup of an untagged register: [cnull] reads as
      [lnull], which is untagged too. *)
  Lemma llookup_reg_lclear_tag_untagged r (v : LWord) :
    ∃ wa, ({[r := lclear_tag v]} : LReg) !!ₗ r = Some wa ∧ get_tag wa.(lw) = false.
  Proof.
    rewrite /llookup_reg. case_decide.
    - by exists lnull.
    - exists (lclear_tag v). rewrite lookup_singleton_eq. split; first done.
      by rewrite lw_lclear_tag get_tag_clear_tag.
  Qed.

  Lemma wp_load_quar_imm Ep pc_p pc_g pc_b pc_e pc_a pc_π
      dst src (imm : Z) w ws ι dq :
    decodeInstrW w.(lw) = CLoad dst src imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_authority ws.(lw) → ws.(lprov) = Some ι →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ ws ∗
        ι ⊒ AQuar }}}
      Instr Executable @ Ep
    {{{ RET FaultedV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        src ↦ᵣ lclear_tag ws }}}.
  Proof.
    iIntros (Hinstr Hvpc Hauth Hι Φ) "(HPC & Hi & >Hsrc & #Hq) HΦ".
    iMod (reg_refilter Ep src ws ι Hauth Hι with "Hq Hsrc") as "Hsrc".
    iDestruct (map_of_regs_1 with "Hsrc") as "Hmap".
    destruct (llookup_reg_lclear_tag_untagged src ws) as (wa & Hsrc & Htag).
    (* CLoad dst src imm *)
    iApply (wp_load_fail_tag_imm with "[$HPC $Hi $Hmap]");
      [exact Hinstr | exact Hvpc | exact Hsrc | exact Htag |].
    iNext. iIntros "(HPC & Hi & Hmap)".
    iApply "HΦ". iFrame "HPC Hi". by iApply regs_of_map_1.
  Qed.

  Lemma wp_load_quar Ep pc_p pc_g pc_b pc_e pc_a pc_π dst src w ws ι dq :
    decodeInstrW w.(lw) = CLoad dst src 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_authority ws.(lw) → ws.(lprov) = Some ι →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ ws ∗
        ι ⊒ AQuar }}}
      Instr Executable @ Ep
    {{{ RET FaultedV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        src ↦ᵣ lclear_tag ws }}}.
  Proof. apply wp_load_quar_imm. Qed.

  Lemma wp_store_quar_imm Ep pc_p pc_g pc_b pc_e pc_a pc_π
      dst (src : Z + RegName) (imm : Z) w wd ι dq :
    decodeInstrW w.(lw) = Store dst src imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_authority wd.(lw) → wd.(lprov) = Some ι →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ wd ∗
        ι ⊒ AQuar }}}
      Instr Executable @ Ep
    {{{ RET FaultedV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        dst ↦ᵣ lclear_tag wd }}}.
  Proof.
    iIntros (Hinstr Hvpc Hauth Hι Φ) "(HPC & Hi & >Hdst & #Hq) HΦ".
    iMod (reg_refilter Ep dst wd ι Hauth Hι with "Hq Hdst") as "Hdst".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    destruct (llookup_reg_lclear_tag_untagged dst wd) as (wa & Hdst & Htag).
    (* Store dst src imm *)
    iApply (wp_store_fail_tag_imm with "[$HPC $Hi $Hmap]");
      [exact Hinstr | exact Hvpc | exact Hdst | exact Htag |].
    iNext. iIntros "(HPC & Hi & Hmap)".
    iApply "HΦ". iFrame "HPC Hi". by iApply regs_of_map_1.
  Qed.

  Lemma wp_store_quar Ep pc_p pc_g pc_b pc_e pc_a pc_π
      dst (src : Z + RegName) w wd ι dq :
    decodeInstrW w.(lw) = Store dst src 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_authority wd.(lw) → wd.(lprov) = Some ι →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ wd ∗
        ι ⊒ AQuar }}}
      Instr Executable @ Ep
    {{{ RET FaultedV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        dst ↦ᵣ lclear_tag wd }}}.
  Proof. apply wp_store_quar_imm. Qed.

End rules_deref_quar.
