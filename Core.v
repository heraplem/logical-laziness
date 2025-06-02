Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Monad.
Import MonadNotation.
Open Scope monad_scope.
Require Import ExtLib.Data.Monads.OptionMonad.

Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.
Generalizable All Variables.

Class Lub (a : Type) :=
  lub : a -> a -> option a.

Global Instance Lub_bool : Lub bool :=
  { lub := fun x y => match x, y with
                   | true, true => Some true
                   | false, false => Some false
                   | _, _ => None
                   end
  }.

Inductive T (a : Type) : Type :=
| thunk (x : a)
| undefined.

Global Instance Functor_T : Functor T :=
  { fmap := fun _ _ f x => match x with
                        | thunk x => thunk (f x)
                        | undefined => undefined
                        end
  }.

Global Instance Monad_T : Monad T :=
  { ret := @thunk
  ; bind := fun _ _ c1 c2 => match c1 with
                          | thunk x => c2 x
                          | undefined => undefined
                          end
  }.

Global Instance Lub_T (a : Type) `{Lub a} : Lub (T a) :=
  { lub := fun x y => match x, y with
                   | undefined, _ => Some y
                   | _, undefined => Some x
                   | thunk x, thunk y => option_map thunk (lub x y)
                   end
  }.

Inductive listA (a : Type) : Type :=
| nilA : listA a
| consA : T a -> T (listA a) -> listA a.

Fixpoint fold_rightA (a b : Type) (f : T a -> T b -> b) (e : b) (xsA : listA a) : b :=
  match xsA with
  | nilA => e
  | consA xT xsT => f xT (fmap (fold_rightA f e) xsT)
  end.

Inductive these (a b : Type) : Type :=
| This (x : a)
| That (y : b)
| These (x : a) (y : b).

Global Instance Lub_listA (a : Type) `{Lub a} : Lub (listA a) :=
  { lub := fix lub_listA xs₁ xs₂ := match xs₁, xs₂ with
                                    | nilA, nilA => Some nilA
                                    | consA x₁ xs₁, consA x₂ xs₂ =>
                                        x <- lub x₁ x₂ ;;
                                        xs <- @lub _ (@Lub_T _ lub_listA) xs₁ xs₂ ;;
                                        ret (consA x xs)
                                    | _, _ => None
                                    end
  }.

Axiom TODO : forall a, a.
