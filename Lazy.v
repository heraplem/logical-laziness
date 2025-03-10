Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.
Generalizable All Variables.

Inductive type : Type :=
| bool__t : type
| prod__t (a b : type) : type
| list__t (a : type) : type.

Definition Var : Type :=
  type -> Type.

Section term.

  Context (var : Var).

  Inductive term : type -> Type :=
  | false__t : term bool__t
  | true__t : term bool__t
  | eq__t `(x : term a) (y : term a) : term bool__t
  | if__t (b : term bool__t) `(t : term a) (f : term a) : term a
  | pair__t `(x : term a) `(y : term b) : term (prod__t a b)
  | fst__t `(p : term (prod__t a b)) : term a
  | snd__t `(p : term (prod__t a b)) : term b
  | nil__t : `(term (list__t a))
  | cons__t `(x : term a) (xs : term (list__t a)) : term (list__t a)
  | foldr__t `(t : var a -> var b -> term b) (e : term b) `(xs : term (list__t a)) : term b
  | var__t `(u : var a) : term a
  | let__t `(t1 : term a) `(t2 : var a -> term b) : term b.

End term.
