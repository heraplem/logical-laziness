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
  | foldr__t `(f : var a -> var b -> term b) (e : term b) `(xs : term (list__t a)) : term b
  | var__t `(u : var a) : term a
  | let__t `(t1 : term a) `(t2 : var a -> term b) : term b.

End term.

(* semantics in terms of Rocq types *)

Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.

Fixpoint denote_type (a : type) : Type :=
  match a with
  | bool__t => bool
  | prod__t a b => denote_type a * denote_type b
  | list__t a => list (denote_type a)
  end.

Definition eq_dec : forall `(x : denote_type a) (y : denote_type a), {x = y} + {x <> y}.
  fix eq_dec 1.
  intros.
  destruct a; simpl in *.
  - exact (bool_dec x y).
  - destruct x as [x' y'], y as [x'' y''].
    destruct (eq_dec _ x' x''), (eq_dec _ y' y'').
    1: subst. auto.
    1, 2, 3: right; inversion 1; contradiction.
  - exact (list_eq_dec (eq_dec _) x y).
Defined.
Arguments eq_dec {a} (x) (y).

Definition eq `(x : denote_type a) (y : denote_type a) : bool :=
  match eq_dec x y with
  | left _ => true
  | right _ => false
  end.

Fixpoint denote_term `(t : term denote_type a) : denote_type a :=
  match t in term _ a return denote_type a with
  | false__t => false
  | true__t => true
  | eq__t x y => eq (denote_term x) (denote_term y)
  | if__t b t f => if denote_term b then denote_term t else denote_term f
  | pair__t x y => (denote_term x, denote_term y)
  | fst__t p => fst (denote_term p)
  | snd__t p => snd (denote_term p)
  | nil__t => nil
  | cons__t x xs => cons (denote_term x) (denote_term xs)
  | foldr__t f e xs =>
      fold_right (fun x y => denote_term (f x y)) (denote_term e) (denote_term xs)
  | var__t u => u
  | let__t t1 t2 => denote_term (t2 (denote_term t1))
  end.
