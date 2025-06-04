Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.
Generalizable All Variables.

Inductive type : Type :=
| bool__type : type
| list__type (alpha : type) : type.

Definition Rep : Type :=
  type -> Type.

Section term.

  Context (rep : Rep).

  Inductive term : type -> Type :=
  | true__term : term bool__type
  | false__term : term bool__type
  | if__term (alpha : type) (t__1 : term bool__type) (t__2 t__3 : term alpha) : term alpha
  | nil__term (alpha : type) : term (list__type alpha)
  | cons__term (alpha : type) (t__1 : term alpha) (t__2 : term (list__type alpha)) : term (list__type alpha)
  | fold_right__term (alpha beta : type) (f : rep alpha -> rep beta -> term beta) (e : term beta) (xs : term (list__type alpha)) : term beta
  | var__term (alpha : type) (r : rep alpha) : term alpha
  | let__term (alpha beta : type) (d : term alpha) (t : rep alpha -> term beta) : term beta.

End term.

Definition program (alpha : type) : Type :=
  forall rep, term rep alpha.
