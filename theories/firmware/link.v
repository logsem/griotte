From stdpp Require Import gmap strings.
From griotte Require Import machine_base machine_parameters switcher compartment_layout.
From griotte Require Import image firmware firmware_ok.

#[local] Open Scope string_scope.

(** * A linker for concrete instances

    [link cfg fw] lays out the firmware [fw] from the address [lk_base cfg]
    on, section after section: the switcher, the shared objects, the
    libraries (import table, then code), then for each compartment its
    export table, its PCC range, its globals and its static sealed
    objects, then for each thread its trusted stack and its
    stack, then the idle thread's trusted stack and hazard slots, and the
    boot stack. The contents of the untrusted compartments, including their
    error handler offsets, the code and globals of the scheduler, and the
    words of the boot stack are given by [cfg].
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
  lk_boot : list Word;
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
    | SchedulerBody _ =>
        let a := adv_of (fc_name fc) in
        (length (la_code a), length (la_data a), 0%nat)
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

  (** The shared objects placed from [a], in the order of the firmware, and
      the next free address. *)
  Fixpoint place_shared (a : Z) (os : list fw_shared_object)
      : list (string * img_shared_object) * Z :=
    match os with
    | [] => ([], a)
    | o :: os =>
        let e := (a + Z.of_nat (so_size o))%Z in
        let '(xs, a') := place_shared e os in
        ((so_name o, MkImgShared (mk_addr a) (mk_addr e)) :: xs, a')
    end.

  (** The libraries placed from [a]: each its import table (the switcher
      slot, then its imports), then its code. *)
  Fixpoint place_libs (a : Z) (ls : list fw_lib) : list (string * img_lib) * Z :=
    match ls with
    | [] => ([], a)
    | l :: ls =>
        let e := (a + Z.of_nat (S (length (fl_imports l)) + length (fl_code l)))%Z in
        let '(xs, a') := place_libs e ls in
        ((fl_name l, MkImgLib (mk_addr a) (mk_addr e)) :: xs, a')
    end.

  Fixpoint place_threads (a : Z) (fts : list fw_thread) : list img_thread * Z :=
    match fts with
    | [] => ([], a)
    | ft :: fts =>
        let ets := (a + tstack_frame_offset (S (ft_tstack_frames ft)))%Z in
        let est := (ets + Z.of_nat (ft_stack_size ft))%Z in
        let ehz := (est + 2)%Z in
        let '(ts, a') := place_threads ehz fts in
        (MkImgThread (mk_addr ets) (mk_addr est) (mk_addr a) (mk_addr ets) (mk_addr est)
           (mk_addr ehz) :: ts, a')
    end.

  (** The image with the addresses only, and the end of the image. *)
  Definition place (fw : firmware) : fw_image * Z :=
    let b := lk_base cfg in
    let call := (b + 5)%Z in
    let esw := (call + Z.of_nat (length switcher_instrs))%Z in
    let ret := (b + 5 + Z.of_nat (length switcher_call_instrs))%Z in
    let '(os, eso) := place_shared esw (fw_shared fw) in
    let '(ls, elib) := place_libs eso (fw_libs fw) in
    let '(cs, a) := place_cmpts elib (fw_cmpts fw) in
    let '(ts, a') := place_threads a (fw_threads fw) in
    let eits := (a' + tstack_frame_offset 1)%Z in
    let eihz := (eits + 2)%Z in
    let eboot := (eihz + Z.of_nat (length (lk_boot cfg)))%Z in
    (MkFwImage
       (MkImgSwitcher (mk_addr b) (mk_addr esw) (mk_addr call) (mk_addr ret) (lk_ot_switcher cfg))
       ls os cs ts
       (MkImgIdleThread (mk_addr a') (mk_addr eits) (mk_addr eits) (mk_addr eihz))
       (MkImgBootStack (mk_addr eihz) (mk_addr eboot) (lk_boot cfg)),
     eboot).

  (** The contents of a compartment, given the addresses of the image. *)
  Definition fill_cmpt (fw : firmware) (img : fw_image) (fc : fw_cmpt) : string * img_cmpt :=
    let n := fc_name fc in
    let c := cmpt_of img n in
    let ss := fc_static_sealed fc in
    let imports := map (fw_word_of fw img ss c) (fc_imports fc) in
    let '(code, data, eh, ehs, entries) :=
      match fc_body fc with
      | TrustedBody b =>
          (tb_code b, chunks_words fw img ss c (tb_data b),
           handler_word (tb_error_handler b), handler_word (tb_error_handler_stackless b),
           map export_word (tb_exports b))
      | UntrustedBody b =>
          let a := adv_of n in
          (la_code a, la_data a, la_handler a, la_handler_stackless a,
           zip_with (λ off e, export_word (MkFwExport "" off (ue_nargs e) 0 InterruptEnabled))
             (la_exports a) (ub_exports b))
      | SchedulerBody _ =>
          let a := adv_of n in
          (la_code a, la_data a, ExportTable_no_handler, ExportTable_no_handler, [])
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
        Some (MkFwImage (img_sw img) (img_libs img) (img_shared img)
                (map (fill_cmpt fw img) (fw_cmpts fw))
                (img_threads img) (img_idle img) (img_boot img))
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
