Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.
Generalizable All Variables.

Section Lazy.

  Context (name : Type).

  Inductive type : Type :=
  | t_bool : type
  | t_prod (a b : type) : type
  | t_list (a : type) : type.

  Inductive term : type -> Type :=
  | t_false : term t_bool
  | t_true : term t_bool
  | t_if (b : term t_bool) `(t : term a) (f : term a) : term a
  | t_pair `(x : term a) `(y : term b) : term (t_prod a b)
  | t_fst `(p : term (t_prod a b)) : term a
  | t_snd `(p : term (t_prod a b)) : term b
  | t_nil : `(term (t_list a))
  | t_cons `(x : term a) (xs : term (t_list a)) : term (t_list a)
  | t_foldr (u v : name) `(t : term b) (e : term b) `(xs : term (t_list a)) : term b
  | t_var (u : name) : `(term a)
  | t_let (u : name) `(t1 : term a) `(t2 : term b) : term b.

End Lazy.
