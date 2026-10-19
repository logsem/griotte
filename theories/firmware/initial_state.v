From griotte Require Import firmware firmware_ok.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
Set Mangle Names.

(** * Defining the initial-state predicate of a case study

    A case study states its start as [<cs>_start flag σ], an [∃] over its
    layout and parameters of [fw_start] on its firmware and image. Then

    - [compute_initial_state (@<cs>_start MP) [<cs>_firmware; <cs>_img]]
      computes the annotated predicate: it unfolds [<cs>_start] and the
      given constants, then the translation ([reduce_firmware_ok]);
    - [erase_annot (@<cs>_initial_state_ok_annot MP)] removes its headings
      and comments;
    - [initial_state_conv] proves [<cs>_initial_state_ok flag σ →
      <cs>_start flag σ], by conversion. *)

(** The constant at the head of [c]. *)
Ltac2 head_reference (c : constr) : Std.reference :=
  let err () := Control.throw (Invalid_argument (Some (Message.of_constr c))) in
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constant r _ => Std.ConstRef r
  | Constr.Unsafe.App f _ =>
      match Constr.Unsafe.kind f with
      | Constr.Unsafe.Constant r _ => Std.ConstRef r
      | _ => err ()
      end
  | _ => err ()
  end.

Ltac2 compute_initial_state_tac (src : constr) (cs : constr list) : unit :=
  let t := Std.eval_cbv
             { Std.rBeta := true; Std.rMatch := false; Std.rFix := false;
               Std.rCofix := false; Std.rZeta := false; Std.rDelta := false;
               Std.rConst := List.map head_reference (src :: cs);
               Std.rStrength := Std.Norm }
             src in
  ltac1:(t |- let t := reduce_firmware_ok t in exact t) (Ltac1.of_constr t).

Tactic Notation "compute_initial_state" constr(src) "[" ne_constr_list_sep(cs, ";") "]" :=
  let f := ltac2:(src cs |-
    let src := Option.get (Ltac1.to_constr src) in
    let cs := List.map (fun c => Option.get (Ltac1.to_constr c)) (Option.get (Ltac1.to_list cs)) in
    compute_initial_state_tac src cs) in
  f src cs.

Ltac erase_annot t :=
  let h := lazymatch t with ?h _ => h | ?h => h end in
  let t := eval cbv beta delta [section note h] in t in
  exact t.

Ltac initial_state_conv :=
  let Hok := fresh "Hok" in
  intros Hok; exact Hok.
