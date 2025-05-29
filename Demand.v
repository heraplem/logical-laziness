Require Import LogicalLaziness.Core.
Require Import LogicalLaziness.Lazy.

Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.
Generalizable All Variables.

Axiom type : Type.

Definition Rep : Type :=
  type -> Type.

Section term.

  Context (rep : Rep).

  Axiom term : type -> Type.

  Axiom translate_type : Lazy.type -> type.

  Definition rep' : Lazy.Rep :=
    fun (a : Lazy.type) => rep (translate_type a).

  Axiom translate : `(Lazy.term rep' a -> term (translate_type a)).

  Definition translate_open `(f : rep' a -> Lazy.term rep' a) :
    rep (translate_type a) -> term (translate_type a).
    intros.
    apply translate.
    apply f.
    exact X.
  Defined.

  Theorem demand_logic :
    forall {a}
      (f : rep' (Lazy.list__t a) -> term (Lazy.list__t a))
      (x inD : list__t (translate_type a)),
      assert__t
        (approx__t x inD)
        (assert_t (eq__t (translate_open f inD)

End term.
