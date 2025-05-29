From Stdlib Require Import Arith.

Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.
Generalizable All Variables.

Lemma sumbool_map `(f : A -> A') `(g : B -> B') :
  {A} + {B} -> {A'} + {B'}.
  firstorder.
Qed.

Lemma nat_dec (m n : nat) : {m = n} + {m <> n}.
Proof.
  intros.
  eapply sumbool_map.
  3: apply (eq_nat_decide m n).
  all: firstorder with arith.
Qed.
Arguments nat_dec m n : clear implicits.

Inductive listA (a : Type) : Type :=
| nilA : listA a
| consA : option a -> option (listA a) -> listA a.

Fixpoint fold_rightA `(f : option a -> option b -> b) (e : b) (xsA : listA a) : b :=
  match xsA with
  | nilA => e
  | consA xT xsT => f xT (option_map (fold_rightA f e) xsT)
  end.

Axiom TODO : forall a, a.
