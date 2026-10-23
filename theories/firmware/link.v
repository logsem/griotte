From stdpp Require Import gmap strings.
From griotte Require Import machine_base machine_parameters switcher assert compartment_layout.
From griotte Require Import image firmware firmware_ok.

#[local] Open Scope string_scope.

(** * A linker for concrete instances

    [link cfg fw] lays out the firmware [fw] from the address [lk_base cfg]
    on, section after section: the switcher, the assert library, then for
    each compartment its export table, its PCC range, its globals and its
    static sealed objects, then for each thread its trusted stack and its
    stack. The contents of the untrusted compartments, including their error
    handler offsets, are given by [cfg].
    The linker is not trusted: its result is checked against the
    predicate. *)

(** The contents of an untrusted compartment: code, globals, the offsets
    of its exports, in the order of its exports, and the two words of its
    export table header for its stackful and stackless error handlers. Its
    exports declare a minimum stack size of 0. *)
Record link_adv : Type := MkLinkAdv {
  la_code : list Word;
  la_data : list Word;
  la_exports : list nat;
  la_handler : Z;
  la_handler_stackless : Z;
}.

Record link_cfg : Type := MkLinkCfg {
  lk_base : Z;
  lk_ot_switcher : OType;
  lk_adv : list (string * link_adv);
}.

Definition default_link_adv : link_adv :=
  MkLinkAdv [] [] [] ExportTable_no_handler ExportTable_no_handler.

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
    | TrustedBody b => (length (tb_code b), chunks_len (tb_data b), length (tb_exports b))
    | UntrustedBody _ =>
        let a := adv_of (fc_name fc) in
        (length (la_code a), length (la_data a), length (la_exports a))
    end.

  (** The addresses of a compartment placed at [a], and the next free
      address. *)
  Definition place_cmpt (a : Z) (fc : fw_cmpt) : img_cmpt * Z :=
    let '(nc, nd, ne) := cmpt_lengths fc in
    let ni := length (fc_imports fc) in
    let ns := length (fc_static_sealed fc) in
    let pcc := (a + ExportTable_offset_entries + Z.of_nat ne)%Z in
    let code := (pcc + Z.of_nat ni)%Z in
    let epcc := (code + Z.of_nat nc)%Z in
    let ecgp := (epcc + Z.of_nat nd)%Z in
    let ess := (ecgp + Z.of_nat ns)%Z in
    (MkImgCmpt (mk_addr pcc) (mk_addr code) (mk_addr epcc) (mk_addr epcc) (mk_addr ecgp)
       (mk_addr ecgp) (mk_addr ess) (mk_addr a) (mk_addr (a + ExportTable_offset_cgp))
       (mk_addr (a + ExportTable_offset_entries))
       (mk_addr (a + ExportTable_offset_entries + Z.of_nat ne)) [] [] [] [] (WInt 0) (WInt 0) [],
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
        let ets := (a + tstack_frame_offset (S (ft_tstack_frames ft)))%Z in
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
  Definition fill_cmpt (fw : firmware) (img : fw_image) (fc : fw_cmpt) : string * img_cmpt :=
    let n := fc_name fc in
    let c := cmpt_of img n in
    let ss := fc_static_sealed fc in
    let imports := map (fw_word_of fw img ss c) (fc_imports fc) in
    let '(code, data, eh, ehs, entries) :=
      match fc_body fc with
      | TrustedBody b =>
          let eh :=
            match tb_error_handler b with
            | Some off => Z.of_nat off
            | None => ExportTable_no_handler
            end in
          (tb_code b, chunks_words fw img ss c (tb_data b), eh, ExportTable_no_handler,
           map export_word (tb_exports b))
      | UntrustedBody b =>
          let a := adv_of n in
          (la_code a, la_data a, la_handler a, la_handler_stackless a,
           zip_with (λ off e, export_word (MkFwExport "" off (ue_nargs e) 0 InterruptEnabled))
             (la_exports a) (ub_exports b))
      end in
    (n, MkImgCmpt (cmpt_b_pcc c) (cmpt_a_code c) (cmpt_e_pcc c) (cmpt_b_cgp c) (cmpt_e_cgp c)
          (cmpt_b_static_sealed c) (cmpt_e_static_sealed c) (cmpt_exp_tbl_pcc c)
          (cmpt_exp_tbl_cgp c) (cmpt_exp_tbl_entries_start c) (cmpt_exp_tbl_entries_end c)
          imports code data (map ss_word ss) (WInt eh) (WInt ehs) entries).

  (** The linked image, if it fits in memory. *)
  Definition link (fw : firmware) : option fw_image :=
    let '(img, a) := place fw in
    match (finz.of_z a : option Addr) with
    | Some _ =>
        Some (MkFwImage (img_sw img) (img_asrt img) (map (fill_cmpt fw img) (fw_cmpts fw))
                (img_threads img))
    | None => None
    end.
End link.

(** In the predicate of an image linked with [cfg], the error handler
    offsets of the untrusted compartment [n] are the ones [cfg] gives. *)
Ltac exists_adv_handlers cfg :=
  lazymatch goal with
  | |- ∃ eh ehs : Z, cmpt_exp_tbl_handler (cmpt_of _ ?n) = _ ∧ _ =>
      exists (la_handler (adv_of cfg n)), (la_handler_stackless (adv_of cfg n)); split
  end.
