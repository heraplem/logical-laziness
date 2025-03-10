Require LogicalLaziness.Lazy.

Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.
Generalizable All Variables.

Inductive type : Type :=
| bool__t : type
| prod__t (a b : type) : type
| list__t (a : type) : type
| t__t (a : type) : type.  (* new *)

Definition Var : Type :=
  type -> Type.

Section term.

  Context (var : Var).

  Inductive term : type -> Type :=
  (* core language *)
  | false__t : term bool__t
  | true__t : term bool__t
  | eq__t `(x : term a) (y : term a) : term bool__t
  | if__t (b : term bool__t) `(t : term a) (f : term a) : term a
  | pair__t `(x : term (t__t a)) `(y : term (t__t b)) : term (prod__t a b)
  | fst__t `(p : term (prod__t a b)) : term a
  | snd__t `(p : term (prod__t a b)) : term b
  | nil__t : `(term (list__t a))
  | cons__t `(x : term (t__t a)) (xs : term (t__t (list__t a))) : term (list__t a)
  | foldr__t `(f : var (t__t a) -> var (t__t b) -> term b) (e : term b) (xs : term (list__t a)) : term b
  | var__t `(u : var a) : term a
  | let__t `(t1 : term a) `(t2 : var (t__t a) -> term b) : term b
  (* lazy/force *)
  | lazy__t `(t : term a) : term (t__t a)
  | force__t `(t : term (t__t a)) : term a.

  Fixpoint denote_type (a : Lazy.type) : type :=
    match a with
    | Lazy.bool__t => bool__t
    | Lazy.prod__t a b => prod__t (denote_type a) (denote_type b)
    | Lazy.list__t a => list__t (denote_type a)
    end.

  Definition lazy_var : Lazy.Var :=
    fun a => var (denote_type a).

  Section denote_term.

    (* XXX ??? *)
    Context (force_var : forall (a : type), var (t__t a) -> var a).

    Fixpoint denote_term `(t : Lazy.term lazy_var a) : term (denote_type a) :=
      match t in Lazy.term _ a return term (denote_type a) with
      | Lazy.false__t => false__t
      | Lazy.true__t => true__t
      | Lazy.eq__t x y => eq__t (denote_term x) (denote_term y)
      | Lazy.if__t b t f =>
          if__t (denote_term b) (denote_term t) (denote_term f)
      | Lazy.pair__t x y => pair__t (lazy__t (denote_term x)) (lazy__t (denote_term y))
      | Lazy.fst__t p => fst__t (denote_term p)
      | Lazy.snd__t p => snd__t (denote_term p)
      | Lazy.nil__t => nil__t
      | Lazy.cons__t x xs => cons__t (lazy__t (denote_term x)) (lazy__t (denote_term xs))
      | Lazy.foldr__t f e xs =>
          foldr__t (fun u v => denote_term (f (force_var u) (force_var v))) (denote_term e) (denote_term xs)
      | Lazy.var__t u => var__t u
      | Lazy.let__t t1 t2 => let__t (denote_term t1) (fun u => denote_term (t2 (force_var u)))
      end.

  End denote_term.

End term.
