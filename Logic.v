Require LogicalLaziness.Explicit.

Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.
Generalizable All Variables.

Inductive type : Type :=
| bool__t : type
| option__t (a : type) : type  (* new *)
| prod__t (a b : type) : type
| list__t (a : type) : type.

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
  | foldr__t `(f : var (t__t a) -> var (t__t b) -> term b) (e : term b) `(xs : term (list__t a)) : term b
  | var__t `(v : var a) : term a
  | let__t `(t1 : term a) `(t2 : var (t__t a) -> term b) : term b
  (* option *)
  | none__t : `(term (option__t a))
  | some__t `(t : term a) : term (option__t a)
  (* logic programming *)
  | fail__t : `(term a)
  | choose__t `(x : term a) (y : term a) : term a
  | free__t `(t : var a -> term b) : term b.

  Fixpoint denote_type (a : Explicit.type) : type :=
    match a with
    | Explicit.bool__t => bool__t
    | Explicit.prod__t a b => prod__t (denote_type a) (denote_type b)
    | Explicit.list__t a => list__t (denote_type a)
    | Explicit.t__t a => option__t (denote_type a)
    end.

  Definition thunks_var : Explicit.type -> Type :=
    fun a => var (denote_type a).

  Section denote_term.

    Fixpoint denote_term `(t : Explicit.term thunks_var a) : term (denote_type a) :=
      match t in Explicit.term _ a return term (denote_type a) with
      | Explicit.false__t => false__t
      | Explicit.true__t => true__t
      | Explicit.eq__t x y => eq__t (denote_term x) (denote_term y)
      | Explicit.if__t b t f =>
          if__t (denote_term b) (denote_term t) (denote_term f)
      | Explicit.pair__t x y => pair__t (denote_term x) (denote_term y)
      | Explicit.fst__t p => fst__t (denote_term p)
      | Explicit.snd__t p => snd__t (denote_term p)
      | Explicit.nil__t => nil__t
      | Explicit.cons__t x xs => cons__t (denote_term x) (denote_term xs)
      | Explicit.foldr__t f e xs =>
          foldr__t (fun u v => denote_term (f u v)) (denote_term e) (denote_term xs)
      | Explicit.var__t v => var__t v
      | Explicit.let__t t1 t2 => let__t (denote_term t1) (fun u => denote_term (t2 u))
      | Explicit.lazy__t t => choose__t none__t (some__t (denote_term t))
      | Explicit.force__t t =>
          free__t (fun u => let u := var__t u
                         in if__t (eq__t (denote_term t) (some__t u))
                              u
                              fail__t)
      end.
    
  End denote_term.

End term.
