From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From cap_machine Require Import region_invariants_revocation region_invariants_allocation.
From cap_machine Require Export world_ghost_theory.
From stdpp Require Import base.

Section world_ghost_theory_interface.

  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    `{MP: MachineParameters}
  .
  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (* TODO sort the lemma defined here:
     - avoid re-defining lemmas already existing in initial world_ghost_theory.v
     - move actually useful lemmas in world_ghost_theory.v
   *)

  Lemma world_interp_init (W : WORLD) (C : CmptName) :
    region W C ∗ sts_full_world W C -∗ world_interp W C.
  Proof. rewrite world_interp_eq /world_interp_def; iIntros "[? ?]"; iFrame. Qed.

  (* TODO use everywhere: clean *)
  Lemma close_world_interp W C a φ p v (ρ : region_type) `{forall Wv, Persistent (φ Wv)} :
    ρ = Temporary ∨ ρ = Permanent →
    sts_state_std C a ρ
    ∗ world_interp_open W C [a]
    ∗ a ↦ₐ v
    ∗ ⌜isO p = false⌝
    ∗ (if (decide (ρ = Temporary))
       then ( if isWL p
              then future_pub_mono C φ v
              else (if isDL p then future_pub_mono C φ v else future_priv_mono C φ v))
       else future_priv_mono C φ v)
    ∗ ▷ φ (W,C,v)
    ∗ rel C a p φ
      -∗ world_interp W C.
  Proof.
    rewrite world_interp_eq /world_interp_def.
    rewrite world_interp_open_eq /world_interp_open_def.
    rewrite -region_open_prepare.
    iIntros (Htp) "(Hstate & [Hreg_open $] & Hl & Hp & HmonoV & Hφ & Hrel)".
    iApply (region_close with "[$Hstate $Hreg_open $Hl $Hp $HmonoV $Hφ $Hrel]"); eauto.
  Qed.

  (* TODO use everywhere: clean *)
  Lemma open_world_interp W C a p φ (ρ : region_type) :
    ρ = Temporary ∨ ρ = Permanent →
    (std W) !! a = Some ρ →
    rel C a p φ ∗ world_interp W C -∗
    ∃ v, world_interp_open W C [a]
         ∗ sts_state_std C a ρ
         ∗ a ↦ₐ v
         ∗ ⌜isO p = false⌝
         ∗ (▷ if (decide (ρ = Temporary))
              then ( if isWL p
                     then future_pub_mono C φ v
                     else (if isDL p then future_pub_mono C φ v else future_priv_mono C φ v))
              else future_priv_mono C φ v)
         ∗ ▷ φ (W,C,v).
  Proof.
    rewrite world_interp_eq /world_interp_def.
    rewrite world_interp_open_eq /world_interp_open_def.
    iIntros (Hne Htemp) "(Hrel & Hreg & Hfull)".
    iDestruct (region_open with "[$Hrel $Hreg $Hfull]") as (v) "(Hr & Hfull & Hstate & Hl & Hp & Hmono & φ)"; eauto.
    iFrame.
    by rewrite -region_open_prepare.
  Qed.

  (* TODO essentially like al instance of open_world_interp + see open_world_perm *)
  Lemma open_world_interp_perm W C a p φ :
    (std W) !! a = Some Permanent →
    rel C a p φ ∗ world_interp W C -∗
    ∃ v, world_interp_open W C [a]
         ∗ sts_state_std C a Permanent
         ∗ a ↦ₐ v
         ∗ ⌜isO p = false⌝
         ∗ ▷ future_priv_mono C φ v
         ∗ ▷ φ (W,C,v).
  Proof.
    rewrite world_interp_eq /world_interp_def.
    rewrite world_interp_open_eq /world_interp_open_def.
    iIntros (?) "(Hrel & [Hr Hsts])".
    iDestruct (
        region_open_perm with "[$Hrel $Hr $Hsts]"
      ) as (v) "(? & $ & $ & $ & $ & $ & $)"; auto.
    by rewrite region_open_prepare.
  Qed.

  (* TODO only used on CMDC adequacy *)
  Lemma world_interp_extend_revoked_sepL2 E W C l1 p φ `{∀ Wv, Persistent (φ Wv)}:
    Forall (λ k, std W !! k = None) l1 →
    world_interp W C

     ={E}=∗

     world_interp (std_update_multiple W l1 Revoked) C
     ∗ ([∗ list] k ∈ l1, rel C k p φ).
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros (?) "[Hr Hsts]".
    iMod (extend_region_revoked_sepL2 with "Hsts Hr") as "($&$&$)"; auto.
  Qed.

  (* TODO used in many places *)
  Lemma world_interp_revoked_by_separation_many
    (W : WORLD) (C : CmptName)
    (la : list Addr) (lw : list Word) :
    Forall (λ a, a ∈ dom (std W)) la →
    world_interp W C
    ∗ ([∗ list] a;w ∈ la;lw, a ↦ₐ w)
    ==∗
    world_interp W C
    ∗ ([∗ list] a;w ∈ la;lw, a ↦ₐ w)
    ∗ ⌜ Forall (λ a, std W !! a = Some Revoked) la⌝
  .
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros (?) "([Hr Hsts] & Hl)".
    iMod (revoked_by_separation_many with "[$Hr $Hsts $Hl]")
      as "($ & $ & $ & $)"; auto.
  Qed.

  (* TODO used in counter closure, vae closure and stack_object_closure *)
  Lemma world_interp_revoked_by_separation_many_with_temp_resources
    (W W' : WORLD) (C' : CmptName)
    (la : list Addr) :
    Forall (λ a, a ∈ dom (std W')) la →
    world_interp W' C' ∗
    close_list_resources C' W la false
    ==∗
    world_interp W' C' ∗
    close_list_resources C' W la false ∗
    ⌜ Forall (λ a, std W' !! a = Some Revoked) la⌝.
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros (Hin) "([Hr Hsts] & Hl)"; cbn.
    iMod (revoked_by_separation_many_with_temp_resources with "[$Hsts $Hr $Hl]") as "($ & $ & $ & $)"; auto.
  Qed.

  (* TODO "core" part of the interface *)
  Lemma world_interp_alloc_loc
    { D : Type } {eqd : EqDecision D} {countD : Countable D}
    {E : coPset}
    (W : WORLD) (C : CmptName) (d : D) (rpub rpriv : D → D → Prop) :
    let i := fresh_cus_name W in
    world_interp W C ={E}=∗
    world_interp (<l[ i := d , (rpub,rpriv) ]l> W) C
    ∗ ⌜i ∉ dom (loc W)⌝ ∗ ⌜i ∉ dom (wrel W)⌝
    ∗ sts_state_loc C i d ∗ sts_rel_loc C i rpub rpriv.
  Proof.
    intros i.
    rewrite world_interp_eq /world_interp_def.

    iIntros "[Hr Hsts]".
    iDestruct (sts_alloc_loc W C d rpub rpriv with "Hsts") as ">($ & $ & $ & $ & $)"; auto.
    iDestruct (region_monotone with "Hr") as "$"; auto.
    subst i.
    eapply related_sts_pub_world_fresh_loc; eauto
    ; intro Hcontra
    ; apply (fresh_name_notin W (fresh_cus_name W))
    ; try done ; [by left | by right].
  Qed.

  (* TODO "core" part of the interface *)
  Lemma world_interp_update_loc
    { D : Type } {eqd : EqDecision D} {countD : Countable D}
    {E : coPset}
    (W : WORLD) (C' : CmptName) (i : positive) (d d' : D) :
    revoke_condition W ->
    related_sts_priv_world W (<l[i:=d']l>W) ->
    world_interp W C' -∗
    sts_state_loc C' i d
    ={E}=∗
    world_interp (<l[ i := d' ]l> W) C' ∗
    sts_state_loc C' i d'.
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros (Hrevoke_conditions Hrelated) "[Hr Hsts] Hst_i".
    iMod (sts_update_loc _ _ _ _ d' with "Hsts Hst_i") as "[Hsts Hst_i]".
    iMod (update_region_revoked_update_loc with "Hsts Hr" ) as "[Hr Hsts]"; auto.
    iFrame.
    done.
  Qed.

  (* TODO "core" part of the interface *)
  Lemma world_interp_rel_loc_valid
    { D : Type } {eqd : EqDecision D} {countD : Countable D}
    (W : WORLD) (C' : CmptName) (i : positive)
    (rpub rpriv: D -> D -> Prop) :
    world_interp W C' -∗
    sts_rel_loc C' i rpub rpriv -∗
    ⌜ wrel W !! i = Some (convert_rel rpub,convert_rel rpriv)⌝.
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros "[Hr Hsts] Hsts_rel".
    iDestruct (sts_full_rel_loc  with "Hsts Hsts_rel") as "$".
  Qed.

  (* TODO "core" part of the interface *)
  Lemma world_interp_loc_valid
    { D : Type } {eqd : EqDecision D} {countD : Countable D}
    (W : WORLD) (C' : CmptName) (i : positive) (d : D) :
    world_interp W C' -∗
    sts_state_loc C' i d -∗
    ⌜loc W !! i = Some (encode d)⌝.
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros "[Hr Hsts] Hst_i".
    iDestruct (sts_full_state_loc  with "Hsts Hst_i") as "$".
  Qed.

  (* TODO "core" part of the interface, but should have better interface *)
  Lemma world_interp_extend_perm E W C a v p φ `{∀ Wv, Persistent (φ Wv)}:
    isO p = false ->
    a ∉ dom (std W) →
    future_priv_mono C φ v -∗
    world_interp W C -∗
    a ↦ₐ v -∗
    φ (W,C,v)

    ={E}=∗

    world_interp (<s[a := Permanent ]s>W) C
    ∗ rel C a p φ.
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros (??) "? [? ?] ? ?".
    iMod (extend_region_perm with "[$] [$] [$] [$] [$]") as "($ & $ & $)"; auto.
  Qed.

  (* TODO "core" part of the interface, but should have better interface *)
  Lemma world_interp_extend_temp E W C a v p φ `{∀ Wv, Persistent (φ Wv)}:
    isO p = false ->
    a ∉ dom (std W) →
    (if isWL p then future_pub_mono C φ v else
       (if isDL p then future_pub_mono C φ v else future_priv_mono C φ v)) -∗
    world_interp W C -∗
    a ↦ₐ v -∗
    φ (W,C,v)

    ={E}=∗

    world_interp (<s[a := Temporary ]s>W) C
    ∗ rel C a p φ.
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros (??) "? [? ?] ? ?".
    iMod (extend_region_temp with "[$] [$] [$] [$] [$]") as "($ & $ & $)"; auto.
  Qed.



  (* TODO "core" part of the interface, but should have better interface *)
  Lemma world_interp_extend_perm_sepL2 E W C l1 l2 p φ `{∀ Wv, Persistent (φ Wv)}:
    isO p = false ->
    Forall (λ k, std W !! k = None) l1 →
    world_interp W C
    -∗ ([∗ list] k;v ∈ l1;l2,
          k ↦ₐ v
          ∗ φ (W, C, v)
          ∗ future_priv_mono C φ v)

    ={E}=∗

    world_interp (std_update_multiple W l1 Permanent) C
    ∗ ([∗ list] k ∈ l1, rel C k p φ).
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros (??) "[Hr Hsts] Hres".
    iMod (extend_region_perm_sepL2 with "Hsts Hr Hres") as "($&$&$)"; auto.
  Qed.

  (* TODO "core" part of the interface, but should have better interface *)
  Lemma world_interp_extend_perm_sepL2_open E W C l1 l2 p φ `{∀ Wv, Persistent (φ Wv)}:
    NoDup l1 ->
    isO p = false ->
    Forall (λ k, std W !! k = None) l1 →
    world_interp W C
    -∗ ([∗ list] k;v ∈ l1;l2, k ↦ₐ v)
    -∗ (
         ([∗ list] k ∈ l1, rel C k p φ)
         -∗ ([∗ list] v ∈ l2,
               (φ ((std_update_multiple W l1 Permanent), C, v)) ∗ future_priv_mono C φ v)
       )

    ={E}=∗

    world_interp (std_update_multiple W l1 Permanent) C
    ∗ ([∗ list] k ∈ l1, rel C k p φ)
    ∗ ([∗ list] v ∈ l2,
               (φ ((std_update_multiple W l1 Permanent), C, v)) ∗ future_priv_mono C φ v).
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros (HNoDup Hp Hl1) "[Hr Hsts] Hreg Hl".
    iMod (extend_region_perm_sepL2_open with "Hsts Hr Hreg Hl") as "($&$&$)"; auto.
  Qed.

  (* TODO "core" part of the interface, but should have better interface *)
  Lemma world_interp_extend_temp_sepL2 E W C l1 l2 p φ `{∀ Wv, Persistent (φ Wv)}:
    isO p = false ->
    Forall (λ k, std W !! k = None) l1 →
    world_interp W C
    -∗ ([∗ list] k;v ∈ l1;l2,
          k ↦ₐ v
          ∗ φ (W, C, v)
          ∗ (if isWL p then future_pub_mono C φ v else
               (if isDL p then future_pub_mono C φ v else future_priv_mono C φ v)) )

    ={E}=∗

    world_interp (std_update_multiple W l1 Temporary) C
    ∗ ([∗ list] k ∈ l1, rel C k p φ).
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros (??) "[Hr Hsts] Hres".
    iMod (extend_region_temp_sepL2 with "Hsts Hr Hres") as "($&$&$)"; auto.
  Qed.


End world_ghost_theory_interface.
