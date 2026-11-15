From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region.

(** * The static part of a library

    A library, as CHERIoT lays one out: its PCC region [[b, e)] holds its
    import table, word [0] the switcher slot, then the import words
    [imps], then its code, entered after the import table. All of it is
    read-only, hence persistent. No spec reads the switcher slot: its word
    is existential. *)

Section lib_static.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} `{MP : MachineParameters}.

  Definition lib_static (b e : Addr) (imps code : list Word) : iProp Σ :=
    ⌜is_heap_address b = false⌝ ∗
    ⌜(b + Z.of_nat (S (length imps) + length code))%a = Some e⌝ ∗
    (∃ w_sw : LWord, b ↦ₐ□ w_sw) ∗
    ([∗ list] k ↦ w ∈ imps, (b ^+ Z.of_nat (S k)) ↦ₐ□ lword_of_word w) ∗
    codefrag_pers (b ^+ Z.of_nat (S (length imps))) code.

  #[global] Instance lib_static_persistent b e imps code :
    Persistent (lib_static b e imps code).
  Proof. apply _. Qed.

  #[global] Instance lib_static_timeless b e imps code :
    Timeless (lib_static b e imps code).
  Proof. apply _. Qed.

  (** The persistent region of a library, its switcher slot holding
      [w_sw], is its static part. *)
  Lemma lib_static_of_region (b e : Addr) (w_sw : Word) (imps code : list Word) :
    is_heap_address b = false →
    (b + Z.of_nat (S (length imps) + length code))%a = Some e →
    [[ b , e ]] ↦ₐ□ [[ lword_of_word <$> (w_sw :: imps ++ code) ]] -∗
    lib_static b e imps code.
  Proof.
    iIntros (Hheap He) "Hreg".
    rewrite region_pointsto_pers_cells; last first.
    { rewrite length_fmap /= length_app. solve_addr. }
    rewrite fmap_cons big_sepL_cons fmap_app big_sepL_app.
    iDestruct "Hreg" as "(Hsw & Himps & Hcode)".
    iSplit; first done. iSplit; first done.
    iSplitL "Hsw"; first (iExists _; rewrite (_ : b ^+ Z.of_nat 0 = b); [iFrame | solve_addr]).
    rewrite big_sepL_fmap.
    iSplitL "Himps"; first iExact "Himps".
    iApply (codefrag_pers_of_region _ e); first solve_addr.
    rewrite region_pointsto_pers_cells; last (rewrite length_fmap; solve_addr).
    rewrite !big_sepL_fmap length_fmap.
    iApply (big_sepL_mono with "Hcode").
    iIntros (k w _) "Hw".
    rewrite (_ : ((b ^+ Z.of_nat (S (length imps))) ^+ Z.of_nat k) =
                 (b ^+ Z.of_nat (S (length imps + k)))); first done.
    solve_addr.
  Qed.

End lib_static.

Section lib_static_thread_indep.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}.

  (** The static part of a library is the same at any two threads. *)
  Lemma lib_static_thread_indep (t t' : Thread) (b e : Addr) (imps code : list Word) :
    lib_static (ceriseg := ceriseG_of t) b e imps code ⊣⊢
    lib_static (ceriseg := ceriseG_of t') b e imps code.
  Proof.
    rewrite /lib_static.
    setoid_rewrite (codefrag_pers_thread_indep t t').
    setoid_rewrite (pointsto_pers_thread_indep t t').
    reflexivity.
  Qed.
End lib_static_thread_indep.
