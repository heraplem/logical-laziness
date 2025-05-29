Require Import Stdlib.Unicode.Utf8.
Require Import Stdlib.Logic.JMeq.
Require Import LogicalLaziness.Core.

Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.
Generalizable All Variables.

Inductive type : Type :=
| bool__t : type
| list__t : type -> type.

Definition Rep : Type :=
  type -> Type.

Section term.

  Context (rep : Rep).

  Inductive term : type -> Type :=
  | false__t : term bool__t
  | true__t : term bool__t
  | if__t `(c : rep bool__t) `(t : term α) (f : term α) : term α
  | nil__t : `(term (list__t α))
  | cons__t `(x : rep α) (xs : rep (list__t α)) : term (list__t α)
  | fold_right__t `(f : rep α -> rep β -> term β) (e : rep β) (xs : rep (list__t α)) : term β
  | var__t `(r : rep α) : term α
  | let__t {α β} (d : term α) (t : rep α -> term β) : term β.

End term.

Definition program (a : type) : Type :=
  forall rep, term rep a.

Fixpoint value (α : type) : Type :=
  match α with
  | bool__t => bool
  | list__t α => list (value α)
  end.

Inductive whnf (rep : Rep) : type → Type :=
| true__v : whnf rep bool__t
| false__v : whnf rep bool__t
| nil__v : `(whnf rep (list__t α))
| cons__v `(x : term rep α) (xs : term rep (list__t α)) : whnf rep (list__t α).

Module Type Heap.
  Axiom ix : Type.
  Axiom t : Type : ix -> type.
  Axiom ix : Type.
  Axiom key : type → Type.
  Axiom extend : `(term key α → t -> key α * t).
  Axiom lookup : `(key α → t → option (term key α)).

  Axiom In : 
End Heap.

Module eval (H : Heap).
  Fixpoint eval (Γ : H.t) `(t : term key α) : option (whnf key α * H.t * nat).
    refine (match t with
            | false__t => Some (false__v, Γ, 1)
            | true__t => Some (true__v, Γ, 1)
            | if__t c t f => match eval Γ _ _ (var__t c) with
                            | Some (c, Δ, m) =>
                                let k := match c with
                                         | true__v => t
                                         | false__v => f
                                         | _ => _
                                         end in
                                let (r, Θ, n) := eval Γ _ _ k
                                               in Some (r, Θ, m + n)
                            | None => None
                            end
            | _ => TODO
            end).

Section env.

  Context (rep : Rep).

  Definition env :=
    forall {α : type}, rep α → option (value α).

  (* Axiom extend : forall (e : env) `(r : rep α) (v : value α), env. *)

  Context (rep_term : forall {α}, term rep α → rep α).

  Fixpoint denote_term `(e : env) `(t : term rep α) : value α * nat :=
    match t in term _ α return value α * nat with
    | false__t => (false, 1)
    | true__t => (true, 1)
    | let__t d b => denote_term e (b (rep_term d))
    | _ => TODO
    end.
