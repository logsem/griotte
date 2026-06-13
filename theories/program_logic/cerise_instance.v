From iris.base_logic Require Export invariants na_invariants gen_heap.
From iris.program_logic Require Export weakestpre.
From griotte Require Import griotte_lang entry.



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
      reg_gen_regG :: gen_heapGS RegName Word Σ; (* register *)
      sreg_gen_regG :: gen_heapGS SRegName Word Σ; (* system register *)
      entryG :: entryGS Σ (* entry point *)
    }.

(* invariants for memory, and a state interpretation for (mem,reg) *)
Global Instance memG_irisG `{MachineParameters} `{!ceriseG Σ} : irisGS griotte_lang Σ := {
  iris_invGS := cerise_invG;
  state_interp σ _ κs _ := (((gen_heap_interp (reg σ))
                            ∗ (gen_heap_interp (sreg σ)))
                            ∗ (gen_heap_interp (mem σ)))%I;
  fork_post _ := True%I;
  num_laters_per_step _ := 0;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.

(* Points to predicates for registers *)
Notation "r ↦ᵣ{ q } w" := (pointsto (L:=RegName) (V:=Word) r q w)
  (at level 20, q at level 50, format "r  ↦ᵣ{ q }  w") : bi_scope.
Notation "r ↦ᵣ w" := (pointsto (L:=RegName) (V:=Word) r (DfracOwn 1) w) (at level 20) : bi_scope.

(* Points to predicates for system registers *)
Notation "sr ↦ₛᵣ{ q } w" := (pointsto (L:=SRegName) (V:=Word) sr q w)
  (at level 20, q at level 50, format "sr  ↦ₛᵣ{ q }  w") : bi_scope.
Notation "sr ↦ₛᵣ w" := (pointsto (L:=SRegName) (V:=Word) sr (DfracOwn 1) w) (at level 20) : bi_scope.

(* Points to predicates for memory *)
Notation "a ↦ₐ{ q } w" := (pointsto (L:=Addr) (V:=Word) a q w)
  (at level 20, q at level 50, format "a  ↦ₐ{ q }  w") : bi_scope.
Notation "a ↦ₐ w" := (pointsto (L:=Addr) (V:=Word) a (DfracOwn 1) w) (at level 20) : bi_scope.
