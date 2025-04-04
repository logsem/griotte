From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import addr_reg_sample rules proofmode.
From cap_machine Require Import logrel.

Section ClearRegistersMacro.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (* TODO should depend on the number of registers used by entry point. *)
  Definition dom_arg_rmap : gset RegName := {[ ca0 ; ca1 ; ca2 ; ca3 ; ca4 ; ca5 ; ca5 ; ct0 ]}.
  Definition is_arg_rmap (rmap : Reg) :=
    dom rmap = dom_arg_rmap.

  Definition clear_registers_pre_call_skip_instrs : list Word :=
    encodeInstrsW [ Jmp ct2;
                    Mov ca0 0%Z;
                    Mov ca1 0%Z;
                    Mov ca2 0%Z;
                    Mov ca3 0%Z;
                    Mov ca4 0%Z;
                    Mov ca5 0%Z;
                    Mov ct0 0%Z].

  Lemma clear_registers_pre_call_skip_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (arg_rmap : Reg) (z : Z)
    (W : WORLD) (C : CmptName) φ :
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length clear_registers_pre_call_skip_instrs)%a ->

    is_arg_rmap arg_rmap ->
    (1 <= z <= 8)%Z ->

    ( PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
      ∗ ct2 ↦ᵣ WInt z
      ∗ ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg ∗ interp W C warg )
      ∗ codefrag pc_a clear_registers_pre_call_skip_instrs
      ∗ ▷ ( (∃ arg_rmap',
              ⌜ is_arg_rmap arg_rmap' ⌝
              ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e (pc_a ^+ length clear_registers_pre_call_skip_instrs)%a
              ∗ ct2 ↦ᵣ WInt z
              ∗ (  [∗ map] rarg↦warg ∈ arg_rmap', rarg ↦ᵣ warg ∗ interp W C warg )
              ∗ codefrag pc_a clear_registers_pre_call_skip_instrs)
               -∗ WP Seq (Instr Executable) {{ φ }})
    )
    ⊢ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
  Admitted.


  Definition clear_registers_pre_call_instrs : list Word :=
    encodeInstrsW [
        Mov cnull 0%Z;
        Mov ctp 0%Z;
        Mov ct1 0%Z;
        Mov ct2 0%Z;
        Mov cs0 0%Z;
        Mov cs1 0%Z;
        Mov ca6 0%Z;
        Mov ca7 0%Z;
        Mov cs2 0%Z;
        Mov cs3 0%Z;
        Mov cs4 0%Z;
        Mov cs5 0%Z;
        Mov cs6 0%Z;
        Mov cs7 0%Z;
        Mov cs8 0%Z;
        Mov cs9 0%Z;
        Mov cs10 0%Z;
        Mov cs11 0%Z;
        Mov ct3 0%Z;
        Mov ct4 0%Z;
        Mov ct5 0%Z;
        Mov ct6 0%Z
      ].

  Lemma clear_registers_pre_call_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (rmap : Reg) φ :
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length clear_registers_pre_call_instrs)%a ->

    dom rmap = all_registers_s ∖ (dom_arg_rmap ∪ {[ PC ; cra ; cgp ; csp ]}) ->

    ( PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )
      ∗ codefrag pc_a clear_registers_pre_call_instrs
      ∗ ▷ ( (∃ (rmap' : Reg),
              ⌜ dom rmap' = all_registers_s ∖ (dom_arg_rmap ∪ {[ PC ; cra ; cgp ; csp ]}) ⌝
              ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e (pc_a ^+ length clear_registers_pre_call_instrs)%a
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              ∗ codefrag pc_a clear_registers_pre_call_instrs)
               -∗ WP Seq (Instr Executable) {{ φ }})
    )
    ⊢ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
  Admitted.


  Definition clear_registers_post_call_instrs : list Word :=
    encodeInstrsW [
        Mov ct0 0%Z;
        Mov cnull 0%Z;
        Mov ctp 0%Z;
        Mov ct1 0%Z;
        Mov ct2 0%Z;
        Mov ct3 0%Z;
        Mov ct4 0%Z;
        Mov ct5 0%Z;
        Mov ct6 0%Z;
        Mov ca2 0%Z;
        Mov ca3 0%Z;
        Mov ca4 0%Z;
        Mov ca5 0%Z;
        Mov ca6 0%Z;
        Mov ca7 0%Z;
        Mov cs0 0%Z;
        Mov cs1 0%Z;
        Mov cs2 0%Z;
        Mov cs3 0%Z;
        Mov cs4 0%Z;
        Mov cs5 0%Z;
        Mov cs6 0%Z;
        Mov cs7 0%Z;
        Mov cs8 0%Z;
        Mov cs9 0%Z;
        Mov cs10 0%Z;
        Mov cs11 0%Z
      ].

  Lemma clear_registers_post_call_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (rmap : Reg) φ :
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length clear_registers_pre_call_instrs)%a ->

    dom rmap = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; ca0 ; ca1 ]} ->

    ( PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )
      ∗ codefrag pc_a clear_registers_post_call_instrs
      ∗ ▷ ( (∃ (rmap' : Reg),
              ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cra ; cgp ; ca0 ; ca1 ]} ⌝
              ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e (pc_a ^+ length clear_registers_pre_call_instrs)%a
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              ∗ codefrag pc_a clear_registers_post_call_instrs)
               -∗ WP Seq (Instr Executable) {{ φ }})
    )
    ⊢ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
  Admitted.


End ClearRegistersMacro.
