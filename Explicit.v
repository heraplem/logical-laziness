Require Import LogicalLaziness.Core.
Require LogicalLaziness.Lazy.

Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.
Generalizable All Variables.

Inductive type : Type :=
| bool__t : type
| list__t (a : type) : type
| t__t (a : type) : type.

Definition Rep : Type :=
  type -> Type.

Section term.

  Context (rep : Rep).

  Inductive term : type -> Type :=
  | false__t : term bool__t
  | true__t : term bool__t
  | if__t (b : term bool__t) `(t : term a) (f : term a) : term a
  | nil__t : `(term (list__t a))
  | cons__t `(x : term (t__t a)) (xs : term (t__t (list__t a))) : term (list__t a)
  | fold_right__t `(f : rep (t__t a) -> rep (t__t b) -> term b) (e : term b) (xs : term (list__t a)) : term b
  | let__t `(t1 : term a) `(t2 : rep a -> term b) : term b
  | var__t `(x : rep a) : term a
  | tick__t `(t : term a) : term a
  | lazy__t `(t : term a) : term (t__t a)
  | force__t `(t : term (t__t a)) : term a.

  Fixpoint translate_type (a : Lazy.type) : type :=
    match a with
    | Lazy.bool__t => bool__t
    | Lazy.list__t a => list__t (translate_type a)
    end.

  Definition rep' : Lazy.Rep :=
    fun a => rep (t__t (translate_type a)).

  Fixpoint translate_term `(t : Lazy.term rep' a) : term (translate_type a) :=
    match t with
    | Lazy.false__t => false__t
    | Lazy.true__t => true__t
    | Lazy.if__t b t f =>
        if__t
          (translate_term b)
          (translate_term t)
          (translate_term f)
    | Lazy.nil__t => nil__t
    | Lazy.cons__t x xs =>
        cons__t
          (lazy__t (translate_term x))
          (lazy__t (translate_term xs))
    | Lazy.fold_right__t f e xs =>
        fold_right__t
          (fun x y => translate_term (f x y))
          (translate_term e)
          (translate_term xs)
    | Lazy.var__t u =>
        force__t (var__t u)
    | Lazy.let__t t k =>
        let__t (translate_term t)
          (fun x => let__t (lazy__t (var__t x))
                   (fun x => translate_term (k x)))
    end.

End term.
