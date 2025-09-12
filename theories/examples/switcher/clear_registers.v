From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import addr_reg_sample rules proofmode.
From iris.program_logic Require Export weakestpre.
From cap_machine Require Export cap_lang region seal_store region_invariants.
From iris.algebra Require Export gmap agree auth excl_auth.
From iris.base_logic Require Export invariants na_invariants saved_prop.
From cap_machine.rules Require Import rules_base.

Section ClearRegistersMacro.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ}
    {heapg : heapGS Σ}
    `{MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation TFRAME := (leibnizO nat).
  Notation WORLD := ( prodO (prodO STS_STD STS) TFRAME) .
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (* TODO should depend on the number of registers used by entry point. *)
  (* Fixpoint dom_arg_rmap (nargs : nat) : gset RegName := *)
  (*     match nargs with *)
  (*     | 0 => ∅ *)
  (*     | S n => *)
  (*         if nargs <? 8 *)
  (*         then *)
  (*           match nargs with *)
  (*           | 1 => {[ ca0 ]} ∪ dom_arg_rmap n *)
  (*           | 2 => {[ ca1 ]} ∪ dom_arg_rmap n *)
  (*           | 3 => {[ ca2 ]} ∪ dom_arg_rmap n *)
  (*           | 4 => {[ ca3 ]} ∪ dom_arg_rmap n *)
  (*           | 5 => {[ ca4 ]} ∪ dom_arg_rmap n *)
  (*           | 6 => {[ ca5 ]} ∪ dom_arg_rmap n *)
  (*           | 7 => {[ ct0 ]} ∪ dom_arg_rmap n *)
  (*           | _ => ∅ *)
  (*           end *)
  (*         else ∅ *)
  (*     end. *)

  Definition dom_arg_rmap (nargs : nat) : gset RegName :=
    match nargs with
    | 0 => ∅
    | 1 => {[ ca0 ]}
    | 2 => {[ ca0 ; ca1 ]}
    | 3 => {[ ca0 ; ca1 ; ca2 ]}
    | 4 => {[ ca0 ; ca1 ; ca2 ; ca3 ]}
    | 5 => {[ ca0 ; ca1 ; ca2 ; ca3 ; ca4 ]}
    | 6 => {[ ca0 ; ca1 ; ca2 ; ca3 ; ca4 ; ca5 ]}
    | _ => {[ ca0 ; ca1 ; ca2 ; ca3 ; ca4 ; ca5 ; ct0 ]}
    end.


  Definition is_arg_rmap (rmap : Reg) (nargs : nat) :=
    dom rmap = dom_arg_rmap nargs.

  Definition clear_registers_pre_call_skip_instrs : list Word :=
    encodeInstrsW [ Jmp ct2;
                    Mov ca0 0%Z;
                    Mov ca1 0%Z;
                    Mov ca2 0%Z;
                    Mov ca3 0%Z;
                    Mov ca4 0%Z;
                    Mov ca5 0%Z;
                    Mov ct0 0%Z].

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
    SubBounds pc_b pc_e pc_a (pc_a ^+ length clear_registers_post_call_instrs)%a ->

    dom rmap = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ->

    ( PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )
      ∗ codefrag pc_a clear_registers_post_call_instrs
      ∗ ▷ ( (∃ (rmap' : Reg),
              ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝
              ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e (pc_a ^+ length clear_registers_post_call_instrs)%a
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              ∗ codefrag pc_a clear_registers_post_call_instrs)
               -∗ WP Seq (Instr Executable) {{ φ }})
    )
    ⊢ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
    iIntros (Hx Hbounds Hdom) "(HPC & Hregs & Hcode & Hcont)".

    iAssert ([∗ map] r↦_ ∈ rmap, ∃ w, r ↦ᵣ w)%I with "[Hregs]" as "Hregs".
    { iApply (big_sepM_mono with "Hregs"). intros. eauto. }

    iDestruct (big_sepM_dom with "Hregs") as "Hregs".
    rewrite Hdom.

    iDestruct (big_sepS_delete _ _ ct0 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cnull with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ ctp with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ ct1 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ ct2 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ ct3 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ ct4 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ ct5 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ ct6 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ ca2 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ ca3 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ ca4 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ ca5 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ ca6 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ ca7 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs2 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs3 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs4 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs5 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs6 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs7 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs8 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs9 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs10 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs11 with "Hregs") as "[[% ?] _]";[set_solver|].

    codefrag_facts "Hcode". clear H0.
    iGo "Hcode".

    iApply "Hcont".
    iExists
      (<[ct0:=_]> (<[cnull:=_]> (<[ctp:=_]> (<[ct1:=_]>(<[ct2:=_]>(<[ct3:=_]>(<[ct4:=_]>(<[ct5:=_]>(<[ct6:=_]>(<[ca2:=_]>(<[ca3:=_]>(<[ca4:=_]>(<[ca5:=_]>(<[ca6:=_]>(<[ca7:=_]> (<[cs2:=_]> (<[cs3:=_]> (<[cs4:=_]> (<[cs5:=_]> (<[cs6:=_]> (<[cs7:=_]> (<[cs8:=_]> (<[cs9:=_]> (<[cs10:=_]> (<[cs11:=_]> ∅))))))))))))))))))))))))).
    repeat (rewrite big_sepM_insert;[|by simplify_map_eq]).
    iFrame. iSplit.
    { iPureIntro. rewrite !dom_insert_L. set_solver. }
    repeat (iSplit;[done|]). done.
  Qed.


End ClearRegistersMacro.
