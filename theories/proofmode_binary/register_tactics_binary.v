From iris.proofmode Require Import reduction proofmode.
From iris.proofmode Require Import environments.
From griotte Require Import stdpp_extra rules_base map_simpl spec_instance_binary.
From griotte Require Export register_tactics.

(** * Register map tactics for the specification run

    [iExtract] and [iExtractList] of [register_tactics] are generic in the
    points-to predicate, and work as well on maps of spec register points-to
    predicates. The insertion tactics below are the counterparts of [iInsert],
    [iInsertList] and [iInsertRegs] for spec register points-to predicates
    [r ↣ᵣ w]. *)

Ltac iInsertSpec_core m' Hmap rnames Hrdom :=
  match rnames with
  | nil => idtac
  | ?rname :: ?rtail =>
      match goal with |- context [ Esnoc _ (INamed ?Hname) ?mtch ] =>
          lazymatch mtch with | context [(rname ↣ᵣ ?rval)%I] =>
            insert_pointsto_map m' Hmap rname Hrdom Hname;
            apply (f_equal (fun x => ({[rname]} ∪ x))) in Hrdom;
            rewrite -(dom_insert_L _ _ rval) in Hrdom;
            iInsertSpec_core (<[rname:=rval]> m') Hmap rtail Hrdom
          end
      end
  end.

Ltac iInsertSpec0 Hmap rnames :=
  lazymatch goal with
    | |- envs_entails ?H _ =>
      lazymatch pm_eval (envs_lookup Hmap H) with
      | Some (_, ?X) =>
        lazymatch X with
        | ([∗ map] _↦_ ∈ ?m', _)%I =>
          let Hrdom := fresh "Hrdom" in
            get_map_dom m' as Hrdom;
            iInsertSpec_core m' Hmap rnames Hrdom;
            clear Hrdom;
            map_simpl Hmap
        end
      end
    end.

Tactic Notation "iInsertSpec" constr(Hmap) constr(rname):=
    iInsertSpec0 Hmap [rname].

Tactic Notation "iInsertListSpec" constr(Hmap) constr(rnames):=
    iInsertSpec0 Hmap rnames.

(** Insert the spec register points-to of the hypotheses [Hregs] into the
    spec register map [Hmap], see [iInsertRegs]: no disjointness proof and no
    simplification of the resulting map. *)
Ltac iInsertRegsSpec0 Hmap Hregs :=
  lazymatch Hregs with
  | nil => idtac
  | ?Hreg :: ?Htail =>
      let pat := constr:((Hreg ++ " " ++ Hmap)%string) in
      iDestruct (big_sepM_insert_2 (λ r w, r ↣ᵣ w)%I with pat) as Hmap;
      iInsertRegsSpec0 Hmap Htail
  end.

Tactic Notation "iInsertRegsSpec" constr(Hmap) constr(Hregs) :=
    iInsertRegsSpec0 Hmap Hregs.
