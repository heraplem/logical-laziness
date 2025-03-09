Require Lazy.

Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.
Generalizable All Variables.

Axiom TODO : forall {A : Type}, A.

Section Logic.

  Parameter (name : Type).

  Inductive type : Type :=
  | t_bool : type
  | t_prod (a b : type) : type
  | t_list (a : type) : type
  | t_t (a : type) : type.

  Inductive term : type -> Type :=
  | t_false : term t_bool
  | t_true : term t_bool
  | t_if (b : term t_bool) `(t : term a) (f : term a) : term a
  | t_pair `(x : term (t_t a)) `(y : term (t_t b)) : term (t_prod a b)
  | t_fst `(p : term (t_prod a b)) : term a
  | t_snd `(p : term (t_prod a b)) : term b
  | t_nil : `(term (t_list a))
  | t_cons `(x : term (t_t a)) (xs : term (t_t (t_list a))) : term (t_list a)
  | t_foldr (u v : name) `(t : term b) (e : term b) `(xs : term (t_list a)) : term b
  | t_var (u : name) : `(term a)
  | t_let (u : name) `(t1 : term a) `(t2 : term b) : term b
  | t_undefined : `(term (t_t a))
  | t_thunk `(t : term a) : term (t_t a)
  | t_choose `(x : term a) (y : term a) : term a
  | t_free (u : name) `(t : term a) : term a.

  Fixpoint denote_type (a : Lazy.type) : type :=
    match a with
    | Lazy.t_bool => t_bool
    | Lazy.t_prod a b => t_prod (denote_type a) (denote_type b)
    | Lazy.t_list a => t_list (denote_type a)
    end.

  Fixpoint denote_term `(t : Lazy.term name a) : term (denote_type a) :=
    let denote_term1 `(t : Lazy.term name b) : term (t_t (denote_type b)) :=
      t_choose t_undefined (t_thunk (denote_term t))
    in match t in Lazy.term _ a return term (denote_type a) with
    | Lazy.t_false => t_false
    | Lazy.t_true => t_true
    | Lazy.t_if b t f =>
        t_if (denote_term b) (denote_term t) (denote_term f)
    | Lazy.t_pair x y => t_pair (denote_term1 x) (denote_term1 y)
    | Lazy.t_fst p => t_fst (denote_term p)
    | Lazy.t_snd p => t_snd (denote_term p)
    | Lazy.t_nil => t_nil
    | Lazy.t_cons x xs => t_cons (denote_term1 x) (denote_term1 xs)
    | Lazy.t_foldr u v t e xs =>
        t_foldr u v (denote_term t) (denote_term e) (denote_term xs)
    | Lazy.t_var n => t_var n
    | Lazy.t_let u t1 t2 => t_let u (denote_term t1) (denote_term t2)
    end.
