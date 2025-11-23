From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel region_invariants bitblast.
From cap_machine Require Import interp_weakening.
From cap_machine Require Import wp_rules_interp switcher_macros_spec.
From cap_machine Require Import rules proofmode monotone.
From cap_machine Require Import fundamental.
From cap_machine.proofmode Require Import map_simpl register_tactics proofmode.


Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {cstackg : CSTACKG Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> (leibnizO Word) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation K := (WORLD -n> (leibnizO CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (V).

  Lemma interp_expr_switcher_call (W : WORLD) (C : CmptName)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) (wstk : Word)
    (Nswitcher : namespace)
    :
    na_inv logrel_nais Nswitcher switcher_inv
    ⊢ interp_expr interp (interp_cont interp cstk Ws Cs) cstk Ws Cs W C (WCap XSRW_ Local b_switcher e_switcher a_switcher_call) wstk.
  Proof.
    iIntros  "#Hinv_switcher %regs [[%Hfull_rmap #Hreg] (Hrmap & %Hstk & Hr & Hsts & Hcont & Hna & Hcstk & %Hframe)]".
    rewrite /registers_pointsto.
    iPoseProof (fundamental_ih with "Hinv_switcher") as "IH". (* used for weakening lemma later *)

    (* --- Extract the code from the invariant --- *)
    iMod (na_inv_acc with "Hinv_switcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    rewrite /switcher_inv.
    iDestruct "Hswitcher_inv"
      as (a_tstk cstk' tstk_next)
           "(>Hmtdc & >%Hot_bounds & >Hcode & >Hb_switcher & >Htstk & >[%Hbounds_tstk_b %Hbounds_tstk_e]
           & Hcstk_full & >%Hlen_cstk & Hstk_interp & #Hp_ot_switcher)".
    codefrag_facts "Hcode".
    rename H into Hcont_switcher_region.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hinv_switcher" as hinv_switcher.

    iExtract "Hrmap" PC as "HPC".
    iExtract "Hrmap" csp as "Hcsp".
    specialize (Hfull_rmap cs0) as HH;destruct HH as [? ?].
    specialize (Hfull_rmap cs1) as HH;destruct HH as [? ?].
    specialize (Hfull_rmap cra) as HH;destruct HH as [? ?].
    specialize (Hfull_rmap cgp) as HH;destruct HH as [? ?].
    specialize (Hfull_rmap ct2) as HH;destruct HH as [? ?].
    specialize (Hfull_rmap ctp) as HH;destruct HH as [? ?].
    specialize (Hfull_rmap ct1) as HH;destruct HH as [? ?].
    iExtract "Hrmap" cs0 as "Hcs0".
    iExtract "Hrmap" cs1 as "Hcs1".
    iExtract "Hrmap" cra as "Hcra".
    iExtract "Hrmap" cgp as "Hcgp".
    iExtract "Hrmap" ct2 as "Hct2".
    iExtract "Hrmap" ctp as "Hctp".
    iExtract "Hrmap" ct1 as "Hct1".

    set (Hcall := switcher_call_entry_point).
    set (Hsize := switcher_size).
    assert (SubBounds b_switcher e_switcher a_switcher_call (a_switcher_call ^+(length switcher_instrs))%a)
      by solve_addr.

    iDestruct ("Hreg" $! csp with "[//] [//]") as "#Hspv".
    (* --- GetP ct2 csp --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_Get_unknown with "[$HPC $Hi $Hct2 $Hcsp]"); try solve_pure.
    iIntros "!>" (v) "[-> | (%p0 & %Hp0 & Hcap_wstk & -> & HPC & Hi & Hcsp & Hct2)] /=".
    { wp_pure. wp_end. iIntros "%Hcontr";done. }
    wp_pure.
    iSpecialize ("Hcode" with "[$]").

    (* ---  Mov ctp (encodePerm RWL) --- *)
    iInstr "Hcode".

    (* --- Sub ct2 ct2 ctp --- *)
    iInstr "Hcode".

    (* --- Jnz 2 ct2 --- *)
    destruct (decide ((p0 - encodePerm RWL)%Z = 0)) as [Hp0'|];cycle 1.
    { (* p ≠ RWL *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_jnz_success_jmp_z with "[$HPC $Hi $Hct2]"); try solve_pure.
      { intros Hcontr; inversion Hcontr; done. }
      iIntros "!> (HPC & Hi & Hct2)".
      wp_pure.
      iSpecialize ("Hcode" with "[$]").
      iInstr "Hcode".
      wp_end. iIntros "%Hcontr";done.
    }
    (* p = RWL *)
    rewrite Hp0'.
    iInstr "Hcode".

    (* --- Jmp 2 --- *)
    iInstr "Hcode".

    (* --- GetL ct2 csp --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_Get_unknown with "[$HPC $Hi $Hct2 $Hcsp]"); try solve_pure.
    iIntros "!>" (v) "[-> | (%g0 & %Hg0 & _ & -> & HPC & Hi & Hcsp & Hct2)] /=".
    { wp_pure. wp_end. iIntros "%Hcontr";done. }
    wp_pure.
    iSpecialize ("Hcode" with "[$]").

    (* --- Mov ctp (encodeLoc Local) --- *)
    iInstr "Hcode".

    (* --- Sub ct2 ct2 ctp --- *)
    iInstr "Hcode".

    (* --- Jnz 2 ct2 --- *)
    destruct (decide ((g0 - encodeLoc Local)%Z = 0)) as [Hg0'|];cycle 1.
    { (* g ≠ Local *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_jnz_success_jmp_z with "[$HPC $Hi $Hct2]"); try solve_pure.
      { intros Hcontr; inversion Hcontr; done. }
      iIntros "!> (HPC & Hi & Hct2)".
      wp_pure.
      iSpecialize ("Hcode" with "[$]").
      iInstr "Hcode".
      wp_end. iIntros "%Hcontr";done.
    }
    rewrite Hg0'.
    (* g = Local *)
    iInstr "Hcode".

    (* --- Jmp 2 --- *)
    iInstr "Hcode".

    (* --- Store csp cs0 --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_store_interp with "[$HPC $Hi Hcsp Hcs0 $Hr $Hsts]"); try solve_pure.
    { iFrame. iFrame "#". by iApply "Hreg";eauto. }
    iIntros "!>" (v) "[-> | (% & % & % & % & % & -> & -> & HPC & Hi & Hcs0
    & Hcsp & Hr & Hsts & %Hcanstore & %bounds)] /=".
    { wp_pure. wp_end. iIntros "%Hcontr";done. }
    wp_pure.
    iSpecialize ("Hcode" with "[$]").
    cbn in Hp0,Hg0; simplify_eq.
    assert (encodePerm p = encodePerm RWL)%Z as ?%encodePerm_inj by lia; simplify_eq; clear Hp0'.
    assert (encodeLoc g = encodeLoc Local)%Z as ?%encodeLoc_inj by lia; simplify_eq; clear Hg0'.

    (* --- Lea csp 1 --- *)
    destruct (a + 1)%a eqn:Ha1;cycle 1.
    { iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_Lea_fail_none_z with "[$HPC $Hi $Hcsp]")
      ; try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done. }
    iInstr "Hcode".

    (* --- Store csp cs1 --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_store_interp_cap with "[$HPC $Hi Hcsp Hcs1 $Hr $Hsts]"); try solve_pure.
    { iFrame. iSplit;[by iApply "Hreg";eauto|].
      by iApply (interp_lea with "Hspv"). }
    iIntros "!>" (v) "[-> | (-> & HPC & Hi & Hcs1
    & Hcsp & Hr & Hsts & _)] /=".
    { wp_pure. wp_end. iIntros "%Hcontr";done. }
    wp_pure.
    iSpecialize ("Hcode" with "[$]").

    (* --- Lea csp 1 --- *)
    destruct (f + 1)%a eqn:Ha2;cycle 1.
    { iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_Lea_fail_none_z with "[$HPC $Hi $Hcsp]")
      ; try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done. }
    iInstr "Hcode".

    (* --- Store csp cra --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_store_interp_cap with "[$HPC $Hi Hcsp Hcra $Hr $Hsts]"); try solve_pure.
    { iFrame. iSplit;[by iApply "Hreg";eauto|].
      by iApply (interp_lea with "Hspv"). }
    iIntros "!>" (v) "[-> | (-> & HPC & Hi & Hcra
    & Hcsp & Hr & Hsts & _)] /=".
    { wp_pure. wp_end. iIntros "%Hcontr";done. }
    wp_pure.
    iSpecialize ("Hcode" with "[$]").

    (* --- Lea csp 1 --- *)
    destruct (f0 + 1)%a eqn:Ha3;cycle 1.
    { iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_Lea_fail_none_z with "[$HPC $Hi $Hcsp]")
      ; try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done. }
    iInstr "Hcode".


    (* --- Store csp cs1 --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_store_interp_cap with "[$HPC $Hi Hcsp Hcgp $Hr $Hsts]"); try solve_pure.
    { iFrame. iSplit;[by iApply "Hreg";eauto|].
      by iApply (interp_lea with "Hspv"). }
    iIntros "!>" (v) "[-> | (-> & HPC & Hi & Hcgp
    & Hcsp & Hr & Hsts & _ & %bounds')] /=".
    { wp_pure. wp_end. iIntros "%Hcontr";done. }
    wp_pure.
    iSpecialize ("Hcode" with "[$]").

    (* --- Lea csp 1 --- *)
    destruct (f1 + 1)%a eqn:Ha4;cycle 1.
    { iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_Lea_fail_none_z with "[$HPC $Hi $Hcsp]")
      ; try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done. }
    iInstr "Hcode".


    (* --- ReadSR ct2 mtdc --- *)
    iInstr "Hcode".

    (* --- GetA cs0 ct2 --- *)
    iInstr "Hcode".

    (* --- Add cs0 cs0 1%Z --- *)
    iInstr "Hcode".

    (* --- GetE ctp ct2 --- *)
    iInstr "Hcode".

    (* --- Sub ctp ctp cs0 --- *)
    iInstr "Hcode".

    (* --- Jnz 2%Z ctp --- *)
    destruct ( (a_tstk + 1 <? e_trusted_stack)%Z) eqn:Hsize_tstk
    ; iEval (cbn) in "Hctp"
    ; cycle 1.
    {
      iInstr "Hcode".
      (* --- Fail --- *)
      iInstr "Hcode".
      wp_end. iIntros "%Hcontr";done.
    }
    iInstr "Hcode".

    (* --- Lea ct2 1 --- *)
    assert ( ∃ f3, (a_tstk + 1)%a = Some f3) as [f3 Hastk] by (exists (a_tstk ^+ 1)%a; solve_addr+Hsize_tstk).
    iInstr "Hcode".

    (* --- Store ct2 csp --- *)
    iDestruct (big_sepL2_length with "Htstk") as %Hlen.
    erewrite finz_incr_eq in Hlen;[|eauto].
    rewrite finz_seq_between_length in Hlen.
    destruct tstk_next.
    { exfalso.
      rewrite /= /finz.dist Z2Nat.inj_sub in Hlen;[|solve_addr].
      assert (e_trusted_stack = f3) as Heq;[solve_addr|].
      subst. solve_addr. }
    assert (is_Some (f3 + 1)%a) as [f4 Hf4];[solve_addr|].
    iDestruct (region_pointsto_cons _ f4 with "Htstk") as "[Hf3 Htstk]";[solve_addr|solve_addr|].
    replace (a_tstk ^+ 1)%a with f3 by solve_addr.
    iInstr "Hcode".
    { solve_addr. }

    (* --- WriteSR mtdc ct2 --- *)
    iInstr "Hcode".

    (* --- GetE cs0 csp --- *)
    iInstr "Hcode".

    (* --- GetA cs1 csp --- *)
    iInstr "Hcode".

    (* --- Subseg csp cs1 cs0 --- *)
    iInstr "Hcode".
    { solve_addr. }

    (* --- clear stack --- *)
    rewrite /switcher_instrs /switcher_call_instrs -app_assoc -app_assoc.
    focus_block 1 "Hcode" as a_clear_stk1 Ha_clear_stk1 "Hcode" "Hcls". iHide "Hcls" as hcont.
    iApply (clear_stack_interp_spec with "[- $HPC $Hcode $Hcsp $Hcs0 $Hcs1 $Hr $Hsts]"); try solve_pure.
    iSplit.
    { iApply interp_weakeningEO;eauto. all: solve_addr. }
    iSplitL;cycle 1.
    { iIntros "!> %Hcontr"; done. }
    iIntros "!> ((HPC & Hcsp & Hcs0 & Hcs1 & Hcode) & Hr & Hsts)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
    focus_block 2 "Hcode" as a_rest Ha_rest "Hcode" "Hcls". iHide "Hcls" as hcont.

    (* --- GetB cs1 PC --- *)
    iInstr "Hcode".

    (* --- GetA cs0 PC --- *)
    iInstr "Hcode".

    (* --- Sub cs1 cs1 cs0 --- *)
    iInstr "Hcode".

    (* --- Mov cs0 PC --- *)
    iInstr "Hcode".

    (* --- Lea cs0 cs1 --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_lea_success_reg with "[$HPC $Hi $Hcs0 $Hcs1]");[solve_pure..| |].
    { instantiate (1:=(b_switcher ^+ 2)%a). solve_addr. }
    iIntros "!> (HPC & Hi & Hcs1 & Hcs0)".
    wp_pure.
    iSpecialize ("Hcode" with "[$]").

    (* --- Lea cs0 -2 --- *)
    iInstr "Hcode".
    { instantiate (1:= b_switcher). solve_addr. }

    (* --- Load cs0 cs0 --- *)
    iInstr "Hcode".

    (* --- UnSeal ct1 cs0 ct1 --- *)
    rewrite /load_word. iSimpl in "Hcs0".
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_unseal_unknown with "[$HPC $Hi $Hcs0 $Hct1]"); try solve_pure.
    iIntros "!>" (ret) "[-> | (% & % & % & % & % & %wsb & -> & HPC & Hi & Hcs0 & Hct1 & %Heq & % & %spec)]".
    { wp_pure. wp_end. iIntros "%Hcontr";done. }
    simplify_eq.

    (* get the seal inv and compare with wsb *)
    iDestruct ("Hreg" $! ct1 with "[//] [//]") as "#Hct1v".
    rewrite (fixpoint_interp1_eq _ _ (WSealed ot_switcher wsb)).
    iDestruct "Hct1v" as (P HpersP) "(HmonoP & HPseal & HP & HPborrow)".
    iDestruct (seal_pred_agree with "Hp_ot_switcher HPseal") as "Hagree".
    iSpecialize ("Hagree" $! (W,C,WSealable wsb)).

    wp_pure.
    iSpecialize ("Hcode" with "[$]").
    rewrite /safeC.
    iSimpl in "Hagree".
    iRewrite -"Hagree" in "HP".
    iDestruct "HP" as (??????????? Heq????) "(Htbl1 & Htbl2 & Htbl3 & #Hentry & Hexec)". simpl fst. simpl snd.
    inversion Heq.

    (* --- Load cs0 ct1 --- *)
    wp_instr.
    iInv "Htbl3" as ">Ha_tbl" "Hcls_tbl".
    iInstr "Hcode".
    { split;auto. solve_addr. }
    iMod ("Hcls_tbl" with "[$]") as "_". iModIntro.
    wp_pure.

    (* --- LAnd ct2 cs0 7 --- *)
    iInstr "Hcode".

    (* --- LShiftR cs0 cs0 3 --- *)
    iInstr "Hcode".

    (* --- GetB cgp ct1 --- *)
    iInstr "Hcode".

    (* --- GetA cs1 ct1 --- *)
    iInstr "Hcode".

    (* --- Sub cs1 cgp cs1 --- *)
    iInstr "Hcode".

    (* --- Lea ct1 cs1 --- *)
    iInstr "Hcode".
    { instantiate (1:=b_tbl). solve_addr-. }

    (* --- Load cra ct1 --- *)
    wp_instr.
    iInv "Htbl1" as ">Hb_tbl" "Hcls_tbl".
    iInstr "Hcode".
    { split;auto. solve_addr. }
    iMod ("Hcls_tbl" with "[$]") as "_". iModIntro.
    wp_pure.

    (* --- Lea ct1 1 --- *)
    iInstr "Hcode".
    { instantiate (1:=(b_tbl ^+ 1)%a). solve_addr. }

    (* --- Load cgp ct1 --- *)
    wp_instr.
    iInv "Htbl2" as ">Hb_tbl" "Hcls_tbl".
    iInstr "Hcode".
    { split;auto. solve_addr. }
    iMod ("Hcls_tbl" with "[$]") as "_". iModIntro.
    wp_pure.

    (* --- Lea cra cs0 --- *)
    destruct (bpcc + encode_entry_point nargs off ≫ 3)%a eqn:Hentry;cycle 1.
    { iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_Lea_fail_none_reg with "[$HPC $Hi $Hcs0 $Hcra]")
      ; try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    iInstr "Hcode".

    (* --- Add ct2 ct2 1 --- *)
    iInstr "Hcode".

    (* clear registers except parameters *)
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
    rewrite -!app_assoc.
    focus_block 3 "Hcode" as a_clear Ha_clear "Hcode" "Hcls". iHide "Hcls" as hcont.

    match goal with |- context [ ([∗ map] k↦y ∈ ?r , k ↦ᵣ y)%I ] => set (rmap' := r) end.
    set (params := dom_arg_rmap 8).
    (* ({[ca0; ca1; ca2; ca3; ca4; ca5; ca5; ct0]} : gset RegName)). *)
    set (Pf := ((λ '(r,_), r ∈ params) : RegName * Word → Prop)).
    rewrite -(map_filter_union_complement Pf rmap').
    iDestruct (big_sepM_union with "Hrmap") as "[Hparams Hrest]".
    { apply map_disjoint_filter_complement. }

    rewrite encode_entry_point_eq_nargs;last lia.
    iApply (clear_registers_pre_call_skip_spec _ _ _ _ _ _ (nargs+1) with "[- $HPC $Hcode]"); try solve_pure.
    { instantiate (1:=filter (λ v : RegName * Word, (Pf v)%type) rmap').
      rewrite /is_arg_rmap /dom_arg_rmap.
      apply dom_filter_L. clear -Hfull_rmap.
      rewrite /rmap'. split.
      - intros Hi.
        repeat (rewrite lookup_delete_ne;[|set_solver]).
        specialize (Hfull_rmap i) as [x Hx].
        exists x. split;auto.
      - intros [? [? ?] ]. auto. }
    { lia. }
    iSplitL "Hct2".
    { replace (Z.of_nat nargs + 1)%Z with (Z.of_nat (nargs + 1))%Z by lia; done. }
    iSplitL "Hparams".
    { iApply big_sepM_sep. iFrame. iApply big_sepM_forall.
      { intros k v.
        destruct (decide ( (k ∈ dom_arg_rmap (nargs + 1 - 1)) )); tc_solve.
      }
      iIntros (k v [Hin Hspec]%map_lookup_filter_Some).
      destruct ( decide (k ∈ dom_arg_rmap (nargs + 1 - 1)) ); last done.
      iApply ("Hreg" $! k);iPureIntro; first set_solver+Hspec.
      repeat (apply lookup_delete_Some in Hin as [_ Hin]); auto.
    }
    iIntros "!> (%arg_rmap' & %Hisarg_rmap' & HPC & Hct2 & Hparams & Hcode)".

    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
    focus_block 4 "Hcode" as a_clear' Ha_clear' "Hcode" "Hcls". iHide "Hcls" as hcont.

    rewrite /rmap'. rewrite !map_filter_delete.
    iDestruct (big_sepM_insert with "[$Hrest $Hct1]") as "Hrest"
    ; [clear; by simplify_map_eq|rewrite insert_delete_insert].
    rewrite -(delete_insert_ne _ ctp);[|auto].
    iDestruct (big_sepM_insert with "[$Hrest $Hctp]") as "Hrest"
    ; [clear; by simplify_map_eq|rewrite insert_delete_insert].
    repeat (rewrite -(delete_insert_ne _ ct2);[|auto]).
    iDestruct (big_sepM_insert with "[$Hrest $Hct2]") as "Hrest"
    ; [clear; by simplify_map_eq|rewrite insert_delete_insert].
    repeat (rewrite (delete_commute _ _ cs1)//). repeat rewrite -(delete_insert_ne _ cs1)//.
    iDestruct (big_sepM_insert with "[$Hrest $Hcs1]") as "Hrest"
    ; [clear; by simplify_map_eq|rewrite insert_delete_insert].
    repeat (rewrite (delete_commute _ _ cs0)//). repeat rewrite -(delete_insert_ne _ cs0)//.
    iDestruct (big_sepM_insert with "[$Hrest $Hcs0]") as "Hrest"
    ; [clear; by simplify_map_eq|rewrite insert_delete_insert].

    iApply (clear_registers_pre_call_spec with "[- $HPC $Hcode $Hrest]"); try solve_pure.
    { clear -Hfull_rmap. apply regmap_full_dom in Hfull_rmap as Heq'.
      rewrite !dom_insert_L !dom_delete_L.
      cut (dom (filter (λ v, ¬ Pf v) regs) = all_registers_s ∖ dom_arg_rmap 8);[set_solver|].
      apply (dom_filter_L _ (regs : gmap RegName Word)).
      split.
      - intros [Hi Hni]%elem_of_difference.
        specialize (Hfull_rmap i) as [x Hx]. eauto.
      - intros [? [? ?] ]. apply elem_of_difference.
        split;auto. apply all_registers_s_correct. }

    iIntros "!> (%rmap'' & %Hrmap'' & HPC & Hrest & Hcode)".

    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
    focus_block 5 "Hcode" as a_jalr Ha_halr "Hcode" "Hcls". iHide "Hcls" as hcont.

    eset (frame :=
           {| wret := WInt 0;
              wstk := (WCap RWL Local b e a);
              wcgp := WInt 0;
              wcs0 := WInt 0;
              wcs1 := WInt 0;
              is_untrusted_caller := true
           |}).

    iSpecialize ("Hexec" $! _ (frame :: cstk) (W :: Ws) (C :: Cs) with "[]").
    { iPureIntro. apply related_sts_priv_refl_world. }
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
    rewrite /load_word. iSimpl in "Hcgp".

    iDestruct (cstack_agree with "Hcstk_full Hcstk") as %Heq'. subst.
    iMod (cstack_update _ _ (frame :: cstk) with "Hcstk_full Hcstk") as "[Hcstk_full Hcstk]".
    iMod ("Hclose_switcher_inv" with "[$Hcode $Hna Hb_switcher $Hcstk_full Hmtdc Htstk Hf3 Hstk_interp]") as "HH".
    { iNext. iExists _,_. iFrame "∗ #".
      rewrite (finz_incr_eq Hf4).
      replace (f3 ^+ -1)%a with a_tstk by solve_addr+Hastk.
      iFrame. simpl. iPureIntro.
      repeat (split;auto);[solve_addr..|repeat f_equiv;solve_addr].
    }

    iApply "Hexec".
    iSplitL "Hcont".
    { iFrame. iNext. simpl.
      iSplit.
      - iApply (interp_weakening with "IH Hspv");auto;solve_addr.
      - iIntros (W' HW' ???????) "(HPC & _)".
        rewrite /interp_conf.
        wp_instr.
        iApply (wp_notCorrectPC with "[$]").
        { intros Hcontr;inversion Hcontr. }
        iIntros "!> HPC". wp_pure. wp_end. iIntros (Hcontr);done. }
    iSplitR.
    { iPureIntro. simpl. split;auto. apply related_sts_pub_refl_world. }
    iFrame.
    rewrite /execute_entry_point_register.
    iDestruct (big_sepM_sep with "Hrest") as "[Hrest #Hnil]".
    iDestruct (big_sepM_sep with "Hparams") as "[Hparams #Hval]".
    iDestruct (big_sepM_union with "[$Hparams $Hrest]") as "Hregs".
    { apply map_disjoint_dom. rewrite Hrmap'' Hisarg_rmap'.
      rewrite /dom_arg_rmap. clear. set_solver. }
    iDestruct (big_sepM_insert_2 with "[Hcsp] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hcra] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hcgp] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[HPC] Hregs") as "Hregs";[iFrame|].

    cbn.
    iFrame.
    iSplit;last (iPureIntro; split ;[split|];[reflexivity|reflexivity|solve_addr]).
    iSplit.
    { iPureIntro. simpl. intros rr. clear -Hisarg_rmap' Hrmap''.
      destruct (decide (rr = PC));simplify_map_eq;[eauto|].
      destruct (decide (rr = cgp));simplify_map_eq;[eauto|].
      destruct (decide (rr = cra));simplify_map_eq;[eauto|].
      destruct (decide (rr = csp));simplify_map_eq;[eauto|].
      apply elem_of_dom. rewrite dom_union_L Hrmap'' Hisarg_rmap'.
      rewrite difference_union_distr_r_L union_intersection_l.
      rewrite -union_difference_L;[|apply all_registers_subseteq].
      apply elem_of_intersection. split;[apply all_registers_s_correct|].
      apply elem_of_union. right.
      apply elem_of_difference. split;[apply all_registers_s_correct|set_solver].
    }
    repeat iSplit.
    - clear-Hentry. iPureIntro. simplify_map_eq. repeat f_equiv.
      rewrite encode_entry_point_eq_off in Hentry. solve_addr.
    - iPureIntro. clear. simplify_map_eq. auto.
    - iPureIntro.
      simplify_map_eq.
      clear -Ha_halr Hcall.
      pose proof switcher_return_entry_point.
      cbn in *.
      do 2 (f_equal; auto). solve_addr.
    - iPureIntro. clear -Ha4 Ha3 Ha2 Ha1 bounds. simplify_map_eq.
      replace f2 with (a^+4)%a by solve_addr.
      done.
    - iApply (interp_weakening with "IH Hspv");auto
      ;[solve_addr+bounds' Ha4 Ha3 Ha2 Ha1|solve_addr-].
    - iIntros (r v Hr Hv).
      assert (r ∉ ({[ PC ; cgp ; cra ; csp ]} : gset RegName)) as Hr'.
      {
        clear -Hr.
        do 8 (destruct nargs; first set_solver).
        induction nargs.
        + set_solver+Hr.
        + apply IHnargs; set_solver+Hr.
      }
      repeat (rewrite lookup_insert_ne in Hv;[|set_solver+Hr Hr']).
      apply lookup_union_Some in Hv.
      2: {
        apply map_disjoint_dom_2.
        rewrite Hisarg_rmap' Hrmap'' /=; set_solver+.
      }
      replace (nargs + 1 - 1) with nargs by lia.
      destruct Hv.
      + iDestruct (big_sepM_lookup with "Hval") as "?" ;eauto.
        destruct (decide (r ∈ _)) as [|Hcontra]; first iFrame "#".
        set_solver+Hcontra Hr.
      + iDestruct (big_sepM_lookup with "Hnil") as "%";eauto; simplify_eq.
        iApply interp_int.
    - iIntros (r v Hr Hv).
      repeat (rewrite lookup_insert_ne in Hv;[|set_solver+Hr]).
      apply lookup_union_Some in Hv.
      2: {
        apply map_disjoint_dom_2.
        rewrite Hisarg_rmap' Hrmap'' /=; set_solver+.
      }
      replace (nargs + 1 - 1) with nargs by lia.
      destruct Hv.
      + iDestruct (big_sepM_lookup with "Hval") as "?";eauto.
        destruct (decide (r ∈ _)) as [Hcontra|]; last iFrame "#".
        set_solver+Hcontra Hr.
      + iDestruct (big_sepM_lookup with "Hnil") as "%";eauto; simplify_eq.
  Qed.

  Lemma interp_switcher_call (W : WORLD) (C : CmptName) (Nswitcher : namespace)
    :
    na_inv logrel_nais Nswitcher switcher_inv
    ⊢ interp W C (WSentry XSRW_ Local b_switcher e_switcher a_switcher_call).
  Proof.
    iIntros "#Hinv".
    rewrite fixpoint_interp1_eq /=.
    iIntros "!> %cstk %Ws %Cs %regs %W' _% %".
    destruct g'; first done.
    iNext ; iApply (interp_expr_switcher_call with "Hinv").
  Qed.

End fundamental.
