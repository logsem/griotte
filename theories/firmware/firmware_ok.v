From stdpp Require Import gmap strings.
From griotte Require Import machine_base griotte_opsem.
From griotte Require Import switcher assert allocator_resources compartment_layout.
(* Imported last: the fields of the image records shadow the fields of the
   layout records of [compartment_layout] and [switcher]. *)
From griotte Require Import image firmware.

#[local] Open Scope string_scope.

(** * The translation of a firmware into a condition on an image and a state

    [firmware_ok fw img σ] holds when [σ] is the machine state that the
    loader builds for the firmware [fw] laid out as [img], and [img] is a
    well-formed layout ([img_wf]). It is not trusted: a case study reduces
    it on its firmware ([reduce_firmware_ok]) and the reduced predicate is
    what is read. The translation therefore uses its own list functions,
    unfolded by the reduction, and only applies them to the lists of the
    firmware, which are concrete. *)

(** ** List functions unfolded by the reduction *)

Fixpoint fw_map {A B} (f : A → B) (l : list A) : list B :=
  match l with [] => [] | x :: l => f x :: fw_map f l end.

Fixpoint fw_imap_from {A B} (f : nat → A → B) (k : nat) (l : list A) : list B :=
  match l with [] => [] | x :: l => f k x :: fw_imap_from f (S k) l end.

Definition fw_imap {A B} (f : nat → A → B) (l : list A) : list B := fw_imap_from f 0 l.

Fixpoint fw_app {A} (l1 l2 : list A) : list A :=
  match l1 with [] => l2 | x :: l1 => x :: fw_app l1 l2 end.

Fixpoint fw_flat_map {A B} (f : A → list B) (l : list A) : list B :=
  match l with [] => [] | x :: l => fw_app (f x) (fw_flat_map f l) end.

(** The conjunction and the union of a list, without a trailing [True] or
    [∅]. *)
Fixpoint big_and (ps : list Prop) : Prop :=
  match ps with [] => True | [p] => p | p :: ps => p ∧ big_and ps end.

Fixpoint big_union (ms : list Mem) : Mem :=
  match ms with [] => ∅ | [m] => m | m :: ms => m ∪ big_union ms end.

(** The set of a list of addresses, without a trailing [∅]. *)
Fixpoint fw_set (l : list Addr) : gset Addr :=
  match l with [] => ∅ | [a] => {[a]} | a :: l => {[a]} ∪ fw_set l end.

(** Small numbers, for the comments. *)
Definition nat_str (k : nat) : string :=
  match k with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
  | 6 => "6" | 7 => "7" | 8 => "8" | 9 => "9" | 10 => "10" | 11 => "11"
  | 12 => "12" | 13 => "13" | 14 => "14" | 15 => "15" | _ => "15+"
  end.

(** [a ^+ k], with a literal offset when [k] is small, so that the reduced
    predicate reads [a ^+ 2] rather than [a ^+ Z.of_nat 2]. *)
Definition addr_off (a : Addr) (k : nat) : Addr :=
  match k with
  | 0 => a | 1 => (a ^+ 1)%a | 2 => (a ^+ 2)%a | 3 => (a ^+ 3)%a
  | 4 => (a ^+ 4)%a | 5 => (a ^+ 5)%a | 6 => (a ^+ 6)%a | 7 => (a ^+ 7)%a
  | 8 => (a ^+ 8)%a | 9 => (a ^+ 9)%a | 10 => (a ^+ 10)%a | 11 => (a ^+ 11)%a
  | 12 => (a ^+ 12)%a | 13 => (a ^+ 13)%a | 14 => (a ^+ 14)%a | 15 => (a ^+ 15)%a
  | _ => (a ^+ Z.of_nat k)%a
  end.

Definition default_export : fw_export := MkFwExport "" 0 0 0 InterruptDisabled.

(** The export named [e] of a trusted compartment, if any. *)
Definition fw_export_named (e : string) (exps : list fw_export) : fw_export :=
  match fw_find_export e exps with Some x => x | None => default_export end.

Definition body_str (b : fw_body) : string :=
  match b with
  | TrustedBody _ => " (trusted)"
  | UntrustedBody b => " (untrusted, " ++ ub_owner b ++ ")"
  end.

(** The export entry word of an export. *)
Definition export_word (e : fw_export) : Word :=
  WInt (encode_entry_point (fe_posture e) (Z.of_nat (fe_nargs e)) (Z.of_nat (fe_min_stack e))
          (Z.of_nat (fe_offset e))).

(** The export table header word of an error handler: its offset if it is
    declared, [ExportTable_no_handler] otherwise. *)
Definition handler_word (eh : option nat) : Z :=
  match eh with Some off => Z.of_nat off | None => ExportTable_no_handler end.

Section translation.
  Context `{MP : MachineParameters}.
  Context (fw : firmware) (img : fw_image).

  (** *** The words the loader writes *)

  (** The word for [w] in the compartment [c], whose static sealed objects
      are [ss]. *)
  Definition fw_word_of (ss : list fw_static) (c : img_cmpt) (w : fw_word) : Word :=
    match w with
    | FW w => w
    | ISwitcherCall =>
        note "switcher call"
          (WSentry FwdDisable true XSRW_ Local
             (b_switcher (img_sw img)) (e_switcher (img_sw img))
             (a_switcher_call (img_sw img)))
    | IAssert =>
        note "assert"
          (WSentry Inherit true RX Global
             (b_assert (img_asrt img)) (e_assert (img_asrt img)) (b_assert (img_asrt img)))
    | IExport n e =>
        let x := cmpt_of img n in
        let k := match fw_export_index fw n e with Some k => k | None => 0 end in
        note (n ++ ", export " ++ e)
          (WSealed (ot_switcher (img_sw img))
             (SCap true RO Global (cmpt_exp_tbl_pcc x) (cmpt_exp_tbl_entries_end x)
                (cmpt_exp_tbl_pcc x ^+ ExportTable_offset_entry k)%a))
    | ISealedStatic o s =>
        let k := match fw_index_of ss_name s ss with Some k => k | None => 0 end in
        let a := addr_off (cmpt_b_static_sealed c) k in
        note ("own static " ++ s)
          (WSealed o (SCap true RO Global a (a ^+ 1)%a a))
    end.

  (** The words of a list of chunks. *)
  Fixpoint chunks_words (ss : list fw_static) (c : img_cmpt) (ds : list fw_chunk) : list Word :=
    match ds with
    | [] => []
    | [FWs ws] => ws
    | FWs ws :: ds => (ws ++ chunks_words ss c ds)%list
    | FWord w :: ds => fw_word_of ss c w :: chunks_words ss c ds
    end.

  (** The first import or global of a compartment naming an unknown
      export or an unknown static sealed object of its own, if any. *)
  Definition fw_word_unknown (ss : list fw_static) (w : fw_word) : option string :=
    match w with
    | IExport n e =>
        match fw_export_index fw n e with
        | Some _ => None
        | None => Some ("export " ++ e ++ " of " ++ n)
        end
    | ISealedStatic _ s =>
        match fw_index_of ss_name s ss with
        | Some _ => None
        | None => Some ("static sealed object " ++ s)
        end
    | _ => None
    end.

  Fixpoint fw_words_unknown (ss : list fw_static) (ws : list fw_word) : option string :=
    match ws with
    | [] => None
    | w :: ws =>
        match fw_word_unknown ss w with Some s => Some s | None => fw_words_unknown ss ws end
    end.

  Definition chunks_fw_words (ds : list fw_chunk) : list fw_word :=
    fw_flat_map (λ d, match d with FWs _ => [] | FWord w => [w] end) ds.

  Definition fc_unknown_export (fc : fw_cmpt) : option string :=
    fw_words_unknown (fc_static_sealed fc)
      (fw_app (fc_imports fc)
         (match fc_body fc with
          | TrustedBody b => chunks_fw_words (tb_data b)
          | UntrustedBody _ => []
          end)).

  (** *** Compartments *)

  (** The export entries of an untrusted compartment: one entry per number
      of arguments in [ns], with an arbitrary offset inside the PCC range,
      that number of arguments, an arbitrary minimum stack size, and
      interrupts enabled. *)
  Fixpoint hole_exports (c : img_cmpt) (ns : list nat) (k : list Word → Prop) : Prop :=
    match ns with
    | [] => k []
    | n :: ns =>
        ∃ off minstk : nat,
          (Z.of_nat off < cmpt_e_pcc c - cmpt_b_pcc c)%Z ∧
          hole_exports c ns
            (λ ws, k (export_word (MkFwExport "" off n minstk InterruptEnabled) :: ws))
    end.

  Definition body_ok (ss : list fw_static) (c : img_cmpt) (b : fw_body) : Prop :=
    match b with
    | TrustedBody b =>
        cmpt_code c = tb_code b ∧
        cmpt_data c = chunks_words ss c (tb_data b) ∧
        match tb_error_handler b, tb_error_handler_stackless b with
        | None, None =>
            note "no error handler"
              (cmpt_exp_tbl_handler c = WInt ExportTable_no_handler ∧
               cmpt_exp_tbl_handler_stackless c = WInt ExportTable_no_handler)
        | eh, ehs =>
            note "declared error handlers"
              (cmpt_exp_tbl_handler c = WInt (handler_word eh) ∧
               cmpt_exp_tbl_handler_stackless c = WInt (handler_word ehs))
        end ∧
        cmpt_exp_tbl_entries c =
          fw_imap (λ _ e, note ("export " ++ fe_name e) (export_word e)) (tb_exports b)
    | UntrustedBody b =>
        note "arbitrary, any length" (Forall is_int (cmpt_code c)) ∧
        note "arbitrary, any length"
          (Forall (initial_data_word (cmpt_b_cgp c) (cmpt_e_cgp c)) (cmpt_data c)) ∧
        note "arbitrary error handler offsets"
          (∃ eh ehs : Z, cmpt_exp_tbl_handler c = WInt eh ∧ cmpt_exp_tbl_handler_stackless c = WInt ehs) ∧
        note "arbitrary offsets, inside the PCC range, and minimum stack sizes" (hole_exports c (fw_map ue_nargs (ub_exports b)) (λ ws, cmpt_exp_tbl_entries c = ws))
    end.

  Definition cmpt_ok (fc : fw_cmpt) : Prop :=
    let c := cmpt_of img (fc_name fc) in
    section (fc_name fc ++ body_str (fc_body fc))
      (match fc_unknown_export fc with
       | Some s => note ("unknown " ++ s) False
       | None =>
           cmpt_imports c = fw_imap (λ _ w, fw_word_of (fc_static_sealed fc) c w) (fc_imports fc) ∧
           cmpt_static_sealed c = fw_map ss_word (fc_static_sealed fc) ∧
           body_ok (fc_static_sealed fc) c (fc_body fc)
       end).

  (** *** Memory *)

  Definition switcher_mem : Mem :=
    let sw := img_sw img in
    mem_region (b_switcher sw) (switcher_data_words (ot_switcher sw) ++ switcher_instrs).

  Definition assert_code_mem : Mem :=
    let asrt := img_asrt img in
    mem_region (b_assert asrt)
      (assert_subroutine_instrs ++
         [WCap true RW Global (flag_assert asrt) (flag_assert asrt ^+ 1)%a (flag_assert asrt)])%list.

  Definition assert_flag_mem : Mem := mem_region (flag_assert (img_asrt img)) [WInt 0].

  Definition cmpt_mem (fc : fw_cmpt) : Mem :=
    let n := fc_name fc in
    let c := cmpt_of img n in
    note (n ++ ", PCC range") (mem_region (cmpt_b_pcc c) (cmpt_imports c ++ cmpt_code c)%list) ∪
    note (n ++ ", CGP range") (mem_region (cmpt_b_cgp c) (cmpt_data c)) ∪
    note (n ++ ", static sealed") (mem_region (cmpt_b_static_sealed c) (cmpt_static_sealed c)) ∪
    note (n ++ ", export table")
      (mem_region (cmpt_exp_tbl_pcc c)
         (WCap true RX Global (cmpt_b_pcc c) (cmpt_e_pcc c) (cmpt_b_pcc c) ::
          WCap true RW Global (cmpt_b_cgp c) (cmpt_e_cgp c) (cmpt_b_cgp c) ::
          cmpt_exp_tbl_handler c ::
          cmpt_exp_tbl_handler_stackless c ::
          cmpt_exp_tbl_entries c)).

  (** The trusted stack holds a register save area, the header, the entry
      frame and zeroed frames. The register save area is zeroed but for its
      word [hazardPointers], the store-only capability to the hazard slots
      of the thread. As the loader does, the entry frame holds the stack
      pointer of the thread (its initial [csp]) and the export table of the
      compartment the thread starts in, read-write and global, as the loader
      writes it. The stack and the hazard slots are zeroed. *)
  Definition thread_mem (i : nat) (ft : fw_thread) : Mem :=
    let t := thread_of img i in
    let c := cmpt_of img (ft_cmpt ft) in
    note ("thread " ++ nat_str i ++ ", trusted stack, entry frame in " ++ ft_cmpt ft)
      (mem_region (b_trusted_stack t)
         (initial_trusted_stack_content
            (WCap true RWL Local (b_stack t) (e_stack t)
               (e_stack t ^+ (- StackEntry_reserved_space))%a)
            (WCap true RW Global (cmpt_exp_tbl_pcc c) (cmpt_exp_tbl_entries_end c)
               (cmpt_exp_tbl_pcc c))
            (WCap true WO Global (b_hazard t) (e_hazard t) (b_hazard t))
            (ft_tstack_frames ft))) ∪
    note ("thread " ++ nat_str i ++ ", stack")
      (mem_region (b_stack t) (replicate (ft_stack_size ft) (WInt 0))) ∪
    note ("thread " ++ nat_str i ++ ", hazard slots")
      (mem_region (b_hazard t) [WInt 0; WInt 0]).

  Definition mem_ok (σ : ExecConf) : Prop :=
    mem σ =
      note "heap, zeroed" initial_heap_memory ∪
      note "switcher" switcher_mem ∪
      note "assert, code and flag capability" assert_code_mem ∪
      note "assert, flag" assert_flag_mem ∪
      big_union (fw_map cmpt_mem (fw_cmpts fw)) ∪
      big_union (fw_imap thread_mem (fw_threads fw)) ∧
    note "every heap address live" (shadowtbl σ = initial_heap_shadow).

  (** *** Registers

      The first thread starts at an export of its compartment, with
      interrupts disabled, and the switcher's return sentry in [cra]. The PC
      of a trusted export is at the offset that the firmware gives; the PC of
      an untrusted export is at the offset that its entry word in the export
      table encodes ([export_entry_offset]), as the switcher decodes it. *)

  Definition regs_ok (σ : ExecConf) : Prop :=
    match fw_threads fw with
    | [] => note "no thread" False
    | ft :: _ =>
        let fc := fw_cmpt_of (fw_cmpts fw) (ft_cmpt ft) in
        let m := cmpt_of img (ft_cmpt ft) in
        let t := thread_of img 0 in
        match fc_body fc with
        | TrustedBody b =>
            note (ft_cmpt ft ++ ", export " ++ ft_entry ft)
              (pcc σ = WCap true RX Global (cmpt_b_pcc m) (cmpt_e_pcc m)
                         (addr_off (cmpt_b_pcc m)
                            (fe_offset (fw_export_named (ft_entry ft) (tb_exports b)))))
        | UntrustedBody b =>
            match fw_index_of ue_name (ft_entry ft) (ub_exports b) with
            | None => note ("unknown export " ++ ft_entry ft ++ " of " ++ ft_cmpt ft) False
            | Some k =>
                note (ft_cmpt ft ++ ", export " ++ ft_entry ft ++
                        ", at the offset its entry word encodes")
                  (∃ z : Z, cmpt_exp_tbl_entries m !! k = Some (WInt z) ∧
                     pcc σ = WCap true RX Global (cmpt_b_pcc m) (cmpt_e_pcc m)
                               (cmpt_b_pcc m ^+ export_entry_offset z)%a)
            end
        end ∧
        reg σ !! cgp = Some (WCap true RW Global (cmpt_b_cgp m) (cmpt_e_cgp m) (cmpt_b_cgp m)) ∧
        reg σ !! csp =
          Some (WCap true RWL Local (b_stack t) (e_stack t)
                  (e_stack t ^+ (- StackEntry_reserved_space))%a) ∧
        note "the switcher's return sentry: a return from the entry exits the thread"
          (reg σ !! cra =
             Some (WSentry RetDisable true XSRW_ Local (b_switcher (img_sw img))
                     (e_switcher (img_sw img)) (a_switcher_return (img_sw img)))) ∧
        note "every other register cleared"
          (∀ r, r ∉ ({[cgp; cra; csp]} : gset RegName) → reg σ !! r = Some (WInt 0)) ∧
        sreg σ !! MTDC =
          Some (WCap true RWL Global (b_trusted_stack t) (e_trusted_stack t) (b_trusted_stack t)) ∧
        note "interrupts disabled (the posture of the export is not used yet)"
          (sreg σ !! MSTATUS = Some (WInt (mstatus_enc InterruptDisabled InterruptDisabled))) ∧
        sreg σ !! MTCC =
          Some (WCap true XSRW_ Local (b_switcher (img_sw img)) (e_switcher (img_sw img))
                  (a_switcher_call (img_sw img) ^+
                     assembler.Asm_Griotte.label_offset_from (concat switcher_asm)
                       ".Lswitch_csp_check" "exception_entry_asm")%a) ∧
        sreg σ !! MEPCC = Some (WInt 0) ∧
        sreg σ !! MCAUSE = Some (WInt 0) ∧
        sreg σ !! MTVAL = Some (WInt 0)
    end.

  (** *** Layout conditions *)

  (** Outside the heap, the shadow region and the revoker
      ([disjoint_from_mmio], unfolded). *)
  Definition range_ok (b e : Addr) : Prop :=
    not_heap_range b e ∧ disjoint_from_shadow b e ∧ revoker_addr ∉ finz.seq_between b e.

  (** The regions of a compartment, named. *)
  Definition cmpt_ranges (fc : fw_cmpt) : list (string * Addr * Addr) :=
    let n := fc_name fc in
    let c := cmpt_of img n in
    [(n ++ ", PCC range", cmpt_b_pcc c, cmpt_e_pcc c);
     (n ++ ", CGP range", cmpt_b_cgp c, cmpt_e_cgp c);
     (n ++ ", static sealed", cmpt_b_static_sealed c, cmpt_e_static_sealed c);
     (n ++ ", export table", cmpt_exp_tbl_pcc c, cmpt_exp_tbl_entries_end c)].

  Definition thread_ranges (i : nat) (ft : fw_thread) : list (string * Addr * Addr) :=
    let t := thread_of img i in
    [("thread " ++ nat_str i ++ ", trusted stack", b_trusted_stack t, e_trusted_stack t);
     ("thread " ++ nat_str i ++ ", stack", b_stack t, e_stack t);
     ("thread " ++ nat_str i ++ ", hazard slots", b_hazard t, e_hazard t)].

  Definition ranges_ok (rs : list (string * Addr * Addr)) : Prop :=
    big_and (fw_map (λ '(s, b, e), note s (range_ok b e)) rs).

  (** Every region of the image. *)
  Definition all_ranges : list (Addr * Addr) :=
    let sw := img_sw img in
    let asrt := img_asrt img in
    fw_map (λ '(s, b, e), note s (b, e))
      (("switcher", b_switcher sw, e_switcher sw) ::
       ("assert", b_assert asrt, e_assert asrt) ::
       ("assert flag", flag_assert asrt, (flag_assert asrt ^+ 1)%a) ::
       fw_app (fw_flat_map cmpt_ranges (fw_cmpts fw))
         (fw_flat_map (λ x, x) (fw_imap thread_ranges (fw_threads fw)))).

  (** The words of a compartment that the loader placed. *)
  Definition img_cmpt_words (c : img_cmpt) : list Word :=
    (cmpt_imports c ++ cmpt_code c ++ cmpt_data c ++ cmpt_static_sealed c ++
     cmpt_exp_tbl_entries c)%list.

  Definition export_in_pcc (c : img_cmpt) (k : nat) (e : fw_export) : Prop :=
    note ("export " ++ fe_name e ++ " inside the PCC range")
      (Z.of_nat (fe_offset e) < cmpt_e_pcc c - cmpt_b_pcc c)%Z.

  Definition cmpt_wf (fc : fw_cmpt) : Prop :=
    let n := fc_name fc in
    let c := cmpt_of img n in
    section (n ++ ", layout")
      (big_and
        (fw_app
          [(cmpt_b_pcc c + Z.of_nat (length (cmpt_imports c)))%a = Some (cmpt_a_code c);
           (cmpt_a_code c + Z.of_nat (length (cmpt_code c)))%a = Some (cmpt_e_pcc c);
           (cmpt_b_cgp c + Z.of_nat (length (cmpt_data c)))%a = Some (cmpt_e_cgp c);
           (cmpt_b_static_sealed c + Z.of_nat (length (cmpt_static_sealed c)))%a =
             Some (cmpt_e_static_sealed c);
           (cmpt_exp_tbl_pcc c + ExportTable_offset_cgp)%a = Some (cmpt_exp_tbl_cgp c);
           (cmpt_exp_tbl_pcc c + ExportTable_offset_entries)%a = Some (cmpt_exp_tbl_entries_start c);
           (cmpt_exp_tbl_entries_start c + Z.of_nat (length (cmpt_exp_tbl_entries c)))%a =
             Some (cmpt_exp_tbl_entries_end c);
           ranges_ok (cmpt_ranges fc);
           note "closed PCC bounds outside the heap" (is_heap_address (cmpt_e_pcc c) = false)]
          (fw_app
            (match fc_body fc with
             | TrustedBody b => fw_imap (export_in_pcc c) (tb_exports b)
             | UntrustedBody _ => []
             end)
            [note
               (match fw_heap_roots fw with
                | [] => "no heap capability (no heap root)"
                | _ => "heap capabilities based on the heap roots"
                end)
               (Forall (word_rooted (fw_set (fw_heap_roots fw))) (img_cmpt_words c));
             note "executable words outside the heap"
               (Forall word_exec_ok (img_cmpt_words c))]))).

  Definition switcher_wf : Prop :=
    let sw := img_sw img in
    section "switcher, layout"
      ((b_switcher sw + 5)%a = Some (a_switcher_call sw) ∧
       (a_switcher_call sw + Z.of_nat (length switcher_instrs))%a = Some (e_switcher sw) ∧
       (b_switcher sw + (5 + Z.of_nat (length switcher_call_instrs)))%a =
         Some (a_switcher_return sw) ∧
       range_ok (b_switcher sw) (e_switcher sw) ∧
       note "closed bounds outside the heap" (is_heap_address (e_switcher sw) = false)).

  Definition assert_wf : Prop :=
    let asrt := img_asrt img in
    section "assert, layout"
      ((b_assert asrt + Z.of_nat (length assert_subroutine_instrs))%a = Some (cap_assert asrt) ∧
       (cap_assert asrt + 1)%a = Some (e_assert asrt) ∧
       note "the flag is not the last address" (is_Some (flag_assert asrt + 1)%a) ∧
       range_ok (b_assert asrt) (e_assert asrt) ∧
       note "closed bounds outside the heap" (is_heap_address (e_assert asrt) = false) ∧
       note "flag" (range_ok (flag_assert asrt) (flag_assert asrt ^+ 1)%a)).

  (** The layout of the thread [i]: its stack, its trusted stack with room
      for the entry frame and [ft_tstack_frames] frames ([tstack_frame_offset]
      giving the offset of a frame), and its two hazard slots. [min_stack] is
      the condition that the stack holds the minimum stack size of the entry
      plus the space reserved at its top ([StackEntry_reserved_space]). *)
  Definition thread_layout_ok (i : nat) (ft : fw_thread) (min_stack : Prop) : Prop :=
    let t := thread_of img i in
    (b_stack t + Z.of_nat (ft_stack_size ft))%a = Some (e_stack t) ∧
    (b_trusted_stack t + tstack_frame_offset (S (ft_tstack_frames ft)))%a =
      Some (e_trusted_stack t) ∧
    note "stack" (range_ok (b_stack t) (e_stack t)) ∧
    note "trusted stack" (range_ok (b_trusted_stack t) (e_trusted_stack t)) ∧
    note "trusted stack not at address 0" ((b_trusted_stack t : Z) ≠ 0) ∧
    min_stack ∧
    (b_hazard t + 2)%a = Some (e_hazard t) ∧
    note "hazard slots" (range_ok (b_hazard t) (e_hazard t)).

  (** The layout of the thread [i], which starts at an export of a
      compartment of the firmware. The minimum stack size of a trusted
      export is the firmware's. That of an untrusted export is the one its
      entry word encodes ([export_entry_min_stack]), as the switcher decodes
      it. *)
  Definition thread_wf (i : nat) (ft : fw_thread) : Prop :=
    section ("thread " ++ nat_str i ++ ", layout")
      (match fc_body (fw_cmpt_of (fw_cmpts fw) (ft_cmpt ft)) with
       | TrustedBody b =>
           match fw_find_export (ft_entry ft) (tb_exports b) with
           | None => note ("unknown export " ++ ft_entry ft ++ " of " ++ ft_cmpt ft) False
           | Some e =>
               thread_layout_ok i ft
                 (note "minimum stack size of the entry"
                    (Z.of_nat (fe_min_stack e) + StackEntry_reserved_space <=
                       Z.of_nat (ft_stack_size ft))%Z)
           end
       | UntrustedBody b =>
           match fw_index_of ue_name (ft_entry ft) (ub_exports b) with
           | None => note ("unknown export " ++ ft_entry ft ++ " of " ++ ft_cmpt ft) False
           | Some k =>
               thread_layout_ok i ft
                 (note "minimum stack size of the entry, as its entry word encodes it"
                    (∃ z : Z,
                       cmpt_exp_tbl_entries (cmpt_of img (ft_cmpt ft)) !! k = Some (WInt z) ∧
                       export_entry_min_stack z + StackEntry_reserved_space <=
                         Z.of_nat (ft_stack_size ft))%Z)
           end
       end).

  (** The conditions on the machine that the use of the heap and of the
      revoker needs, when the firmware hands out heap authority: the shadow
      table translates the heap by a constant offset, and the revoker is
      not the last address. *)
  Definition heap_machine_ok : Prop :=
    note "the shadow table translates the heap by a constant offset"
      (∀ a, heap_to_shadow a = translate_region heap_b heap_e shadow_b a) ∧
    note "the revoker is not the last address" (revoker_addr < revoker_addr ^+ 1)%a.

  Definition img_wf : Prop :=
    switcher_wf ∧
    assert_wf ∧
    big_and (fw_map cmpt_wf (fw_cmpts fw)) ∧
    big_and (fw_imap thread_wf (fw_threads fw)) ∧
    section "image, layout"
      (big_and
        (fw_app
          [note "pairwise disjoint" (ranges_disjoint all_ranges);
           note "sealing types distinct" (NoDup (ot_switcher (img_sw img) :: fw_otypes fw));
           note "sealing types valid"
             (Forall otype_valid (ot_switcher (img_sw img) :: fw_otypes fw))]
          (fw_app
             (fw_map (λ a, note "heap root in the heap" (is_heap_address a = true))
                (fw_heap_roots fw))
             (match fw_heap_roots fw with
              | [] => []
              | _ => [section "Machine (heap and revoker)" heap_machine_ok]
              end)))).
End translation.

Definition firmware_ok `{MP : MachineParameters}
    (fw : firmware) (img : fw_image) (σ : ExecConf) : Prop :=
  big_and (fw_map (cmpt_ok fw img) (fw_cmpts fw)) ∧
  section "Memory" (mem_ok fw img σ) ∧
  section "Registers" (regs_ok fw img σ) ∧
  img_wf fw img.

(** The start of a firmware: the flag of the assert library at [flag],
    the conditions [params] on the parameters of the firmware, and the
    machine state [σ] built by the loader for [fw] laid out as [img].
    Without parameter conditions, there is no section for them. *)
Definition fw_start `{MP : MachineParameters} (params : list Prop)
    (fw : firmware) (img : fw_image) (flag : Addr) (σ : ExecConf) : Prop :=
  note "the flag of the assert library" (flag_assert (img_asrt img) = flag) ∧
  match params with
  | [] => firmware_ok fw img σ
  | _ => section "Parameters" (big_and params) ∧ firmware_ok fw img σ
  end.

(** ** Reduction on a concrete firmware

    [reduce_firmware_ok t] unfolds the translation in [t], and only the
    translation: the code, [mem_region], [length], address arithmetic and the
    words stay folded. The firmware and the image-building functions of the
    case study must be unfolded first. *)
Ltac reduce_firmware_ok t :=
  eval cbv beta iota zeta delta [
    fw_start firmware_ok mem_ok regs_ok img_wf cmpt_ok body_ok fw_word_of chunks_words
    hole_exports export_word switcher_mem assert_code_mem assert_flag_mem
    cmpt_mem thread_mem range_ok ranges_ok cmpt_ranges thread_ranges all_ranges
    img_cmpt_words
    export_in_pcc cmpt_wf switcher_wf assert_wf thread_wf thread_layout_ok heap_machine_ok
    fw_map fw_imap fw_imap_from fw_app fw_flat_map big_and big_union nat_str
    addr_off default_export fw_export_named body_str fw_set handler_word
    fw_word_unknown fw_words_unknown chunks_fw_words fc_unknown_export
    fw_index_of fw_body_export_index fw_export_index fw_find_export
    cmpt_of thread_of assoc fw_nth fw_cmpt_of
    fw_cmpts fw_threads fw_otypes fw_heap_roots
    fc_name fc_imports fc_static_sealed fc_body ss_name ss_word
    tb_code tb_data tb_exports tb_error_handler tb_error_handler_stackless
    ub_owner ub_exports
    fe_name fe_offset fe_nargs fe_min_stack fe_posture ue_name ue_nargs
    ft_cmpt ft_entry ft_stack_size ft_tstack_frames
    img_sw img_asrt img_cmpts img_threads
    String.append String.eqb Ascii.eqb Bool.eqb andb]
  in t.
