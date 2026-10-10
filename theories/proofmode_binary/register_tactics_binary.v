From iris.proofmode Require Import reduction proofmode.
From iris.proofmode Require Import environments.
From griotte Require Import stdpp_extra rules_base map_simpl spec_instance_binary.
From griotte Require Export register_tactics.

(** * Register map tactics for the specification run

    [iExtract] and [iExtractList] of [register_tactics] are generic in the
    points-to predicate, and work as well on maps of spec register points-to
    predicates. The insertion tactics below are the counterparts of [iInsert]
    and [iInsertList] for spec register points-to predicates [r ↣ᵣ w]. *)

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
