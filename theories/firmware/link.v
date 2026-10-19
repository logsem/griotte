From stdpp Require Import gmap strings.
From griotte Require Import machine_base machine_parameters switcher assert compartment_layout.
From griotte Require Import image firmware firmware_ok.
Set Mangle Names.

#[local] Open Scope string_scope.

(** * A linker for concrete instances

    [link cfg fw] lays out the firmware [fw] from the address [lk_base cfg]
    on, section after section: the switcher, the assert library, then for
    each compartment its export table, its PCC range, its globals and its
    static sealed objects, then for each thread its trusted stack and its
    stack. The contents of the untrusted compartments are given by [cfg].
    The linker is not trusted: its result is checked against the
    predicate. *)

(** The contents of an untrusted compartment: code, globals, export offsets. *)
Record link_adv : Type := MkLinkAdv {
  la_code : list Word;
  la_data : list Word;
  la_exports : list nat;
}.

Record link_cfg : Type := MkLinkCfg {
  lk_base : Z;
  lk_ot_switcher : OType;
  lk_adv : list (string * link_adv);
}.

Definition default_link_adv : link_adv := MkLinkAdv [] [] [].

Definition mk_addr (z : Z) : Addr :=
  match finz.of_z z with Some a => a | None => za0 end.

Definition chunks_len (ds : list fw_chunk) : nat :=
  sum_list_with (λ d, match d with FWs ws => length ws | FWord _ => 1%nat end) ds.

Section link.
  Context `{MP : MachineParameters}.
  Context (cfg : link_cfg).

  Definition adv_of (n : string) : link_adv := assoc n (lk_adv cfg) default_link_adv.

  (** The lengths of the code, the globals and the export table. *)
  Definition cmpt_lengths (fc : fw_cmpt) : nat * nat * nat :=
    match fc_body fc with
    | TrustedBody code data exps => (length code, chunks_len data, length exps)
    | UntrustedBody _ _ =>
        let a := adv_of (fc_name fc) in
        (length (la_code a), length (la_data a), length (la_exports a))
    end.

  (** The addresses of a compartment placed at [a], and the next free
      address. *)
  Definition place_cmpt (a : Z) (fc : fw_cmpt) : img_cmpt * Z :=
    let '(nc, nd, ne) := cmpt_lengths fc in
    let ni := length (fc_imports fc) in
    let ns := length (fc_static_sealed fc) in
    let pcc := (a + 2 + Z.of_nat ne)%Z in
    let code := (pcc + Z.of_nat ni)%Z in
    let epcc := (code + Z.of_nat nc)%Z in
    let ecgp := (epcc + Z.of_nat nd)%Z in
    let ess := (ecgp + Z.of_nat ns)%Z in
    (MkImgCmpt (mk_addr pcc) (mk_addr code) (mk_addr epcc) (mk_addr epcc) (mk_addr ecgp)
       (mk_addr ecgp) (mk_addr ess) (mk_addr a) (mk_addr (a + 1)) (mk_addr (a + 2))
       (mk_addr (a + 2 + Z.of_nat ne)) [] [] [] [] [],
     ess).

  Fixpoint place_cmpts (a : Z) (fcs : list fw_cmpt) : list (string * img_cmpt) * Z :=
    match fcs with
    | [] => ([], a)
    | fc :: fcs =>
        let '(c, a') := place_cmpt a fc in
        let '(cs, a'') := place_cmpts a' fcs in
        ((fc_name fc, c) :: cs, a'')
    end.

  Fixpoint place_threads (a : Z) (fts : list fw_thread) : list img_thread * Z :=
    match fts with
    | [] => ([], a)
    | ft :: fts =>
        let ets := (a + Z.of_nat (length (initial_trusted_stack_content (ft_tstack_frames ft))))%Z in
        let est := (ets + Z.of_nat (ft_stack_size ft))%Z in
        let '(ts, a') := place_threads est fts in
        (MkImgThread (mk_addr ets) (mk_addr est) (mk_addr a) (mk_addr ets) :: ts, a')
    end.

  (** The image with the addresses only, and the end of the image. *)
  Definition place (fw : firmware) : fw_image * Z :=
    let b := lk_base cfg in
    let call := (b + 1)%Z in
    let esw := (call + Z.of_nat (length switcher_instrs))%Z in
    let ret := (b + 1 + Z.of_nat (length switcher_call_instrs))%Z in
    let cap := (esw + Z.of_nat (length assert_subroutine_instrs))%Z in
    let flag := (cap + 1)%Z in
    let '(cs, a) := place_cmpts (flag + 1) (fw_cmpts fw) in
    let '(ts, a') := place_threads a (fw_threads fw) in
    (MkFwImage
       (MkImgSwitcher (mk_addr b) (mk_addr esw) (mk_addr call) (mk_addr ret) (lk_ot_switcher cfg))
       (MkImgAssert (mk_addr esw) (mk_addr flag) (mk_addr cap) (mk_addr flag))
       cs ts,
     a').

  (** The contents of a compartment, given the addresses of the image. *)
  Definition fill_cmpt (img : fw_image) (fc : fw_cmpt) : string * img_cmpt :=
    let n := fc_name fc in
    let c := cmpt_of img n in
    let imports := map (fw_word_of img c) (fc_imports fc) in
    let '(code, data, entries) :=
      match fc_body fc with
      | TrustedBody code data exps => (code, chunks_words img c data, map export_word exps)
      | UntrustedBody _ _ =>
          let a := adv_of n in
          (la_code a, la_data a,
           map (λ off, WInt (encode_entry_point InterruptEnabled 0 (Z.of_nat off))) (la_exports a))
      end in
    (n, MkImgCmpt (cmpt_b_pcc c) (cmpt_a_code c) (cmpt_e_pcc c) (cmpt_b_cgp c) (cmpt_e_cgp c)
          (cmpt_b_static_sealed c) (cmpt_e_static_sealed c) (cmpt_exp_tbl_pcc c)
          (cmpt_exp_tbl_cgp c) (cmpt_exp_tbl_entries_start c) (cmpt_exp_tbl_entries_end c)
          imports code data (fc_static_sealed fc) entries).

  (** The linked image, if it fits in memory. *)
  Definition link (fw : firmware) : option fw_image :=
    let '(img, a) := place fw in
    match (finz.of_z a : option Addr) with
    | Some _ =>
        Some (MkFwImage (img_sw img) (img_asrt img) (map (fill_cmpt img) (fw_cmpts fw))
                (img_threads img))
    | None => None
    end.
End link.
