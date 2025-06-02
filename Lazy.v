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
  | true__t : term bool__t
  | false__t : term bool__t
  | if__t `(c : term bool__t) `(t : term α) (f : term α) : term α
  | nil__t : `(term (list__t α))
  | cons__t `(x : term α) (xs : term (list__t α)) : term (list__t α)
  | fold_right__t `(f : rep α -> rep β -> term β) (e : term β) (xs : term (list__t α)) : term β
  | var__t `(r : rep α) : term α
  | let__t {α β} (d : term α) (t : rep α -> term β) : term β.

End term.

Definition program (a : type) : Type :=
  forall {rep}, term rep a.
