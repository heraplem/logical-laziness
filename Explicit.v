Require Import Stdlib.Lists.List.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Data.Monads.WriterMonad.

Require Import LogicalLaziness.Core.
Require LogicalLaziness.Lazy.

Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.
Generalizable All Variables.

Inductive type : Type :=
| bool__type : type
| T__type (alpha : type) : type
| list__type (alpha : type) : type.

Reserved Notation "[[ alpha ]]__eval".
Fixpoint value (alpha : type) : Type :=
  match alpha with
  | bool__type => bool
  | T__type alpha => [[ alpha ]]__eval
  | list__type alpha => list [[ alpha ]]__eval
  end
where "[[ alpha ]]__eval" := (value alpha).

Reserved Notation "[[ alpha ]]__approx".
Fixpoint approx (alpha : type) : Type :=
  match alpha with
  | bool__type => bool
  | T__type alpha => T [[ alpha ]]__approx
  | list__type alpha => listA [[ alpha ]]__approx
  end
where "[[ alpha ]]__approx" := (approx alpha).

Definition Rep : Type :=
  type -> Type.

Definition Hom : Type :=
  type -> type -> Type.

Section term.

  (* Context (hom : Hom). *)
  Context (rep : Rep).

  Inductive term : type -> Type :=
  | var__term `(x : rep alpha) : term alpha
  | let__term (alpha beta : type) (t__1 : term alpha) (t__2 : rep alpha -> term beta) : term beta
  | true__term : term bool__type
  | false__term : term bool__type
  | if__term (b : term bool__type) `(t : term alpha) (f : term alpha) : term alpha
  | nil__term : `(term (list__type alpha))
  | cons__term `(x : term (T__type alpha)) (xs : term (T__type (list__type alpha))) : term (list__type alpha)
  | fold_right__term (alpha beta : type) (f : rep (T__type alpha) -> rep (T__type beta) -> term beta) (e : term beta) (xs : term (list__type alpha)) : term beta
  | tick__term `(t : term alpha) : term alpha
  | lazy__term `(t : term alpha) : term (T__type alpha)
  | force__term `(t : term (T__type alpha)) : term alpha.

End term.

(* Fixpoint map__term {rep__1 rep__2 : Rep} (eta : forall alpha, rep__1 alpha -> rep__2 alpha) {alpha : type} (t : term rep__1 alpha) : term rep__2 alpha := *)
(*   match t with *)
(*   | var__t x => var__t (eta _ x) *)
(*   | let__t t__1 k__2 => let__t (map__term eta t__1) (fun x => map__term eta (k__2 x)) *)
(*   | true__t => true *)
(*   | false__t => false *)
(*   | if__t t__1 t__2 t__3 => if__t (map__term eta t__1) (map__term eta t__2) (map__term eta t__3) *)
(*   | cons__t t__1 t__2 => cons__t (map__term eta t__1) (map__term eta t__2) *)
(*   | fold_right__t k__1 t__2 t__3 => fold_right__t (fun x__1 x__2 => map__term eta (k__1 x__1 x__2)) (map__term eta t__2) (map__term eta t__3) *)
(*   | tick__t t__1 => tick__t (map__term eta t__1) *)
(*   | lazy__t t__1 => lazy__t (map__term eta t__1) *)
(*   | force__t t__1 => force__t (map__term eta t__1) *)
(*   end. *)


(* Reserved Notation "⟦ t ⟧__eval". *)
(* Fixpoint eval (alpha : type) (t : term value alpha) : ⟦alpha⟧__eval := *)
(*   match t with *)
(*   | var__t x => x *)
(*   | let__t t₁ k₂ => eval (k₂ ⟦t₁⟧__eval) *)
(*   | true__t => true *)
(*   | false__t => false *)
(*   | if__t t₁ t₂ t₃ => if ⟦t₁⟧__eval then ⟦t₂⟧__eval else ⟦t₃⟧__eval *)
(*   | nil__t => nil *)
(*   | cons__t t₁ t₂ => cons ⟦t₁⟧__eval ⟦t₂⟧__eval *)
(*   | fold_right__t k₁ t₂ t₃ => fold_right (fun x₁ x₂ => ⟦k₁ x₁ x₂⟧__eval) ⟦t₂⟧__eval ⟦t₃⟧__eval *)
(*   | tick__t t₁ => ⟦t₁⟧__eval *)
(*   | force__t t₁ => ⟦t₁⟧__eval *)
(*   | lazy__t t₁ => ⟦t₁⟧__eval *)
(*   end *)
(* where "⟦ t ⟧__eval" := (eval t). *)

Section eval.
  Parameter (rep : Rep).
  Parameter (proj : forall (alpha : type), rep alpha -> [[ alpha ]]__eval).
  Parameter (inj : forall (alpha : type), [[ alpha ]]__eval -> rep alpha).

  Local Definition toT (alpha : type) (r : rep alpha) : rep (T__type alpha) :=
    inj (proj r : [[ T__type alpha ]]__eval).
  Local Definition fromT (alpha : type) (r : rep (T__type alpha)) : rep alpha :=
    inj (proj r : [[ alpha ]]__eval).

  Reserved Notation "[[ t ]]__eval".

  (* Fixpoint eval (alpha : type) (t : term rep alpha) : rep alpha := *)
  (*   match t with *)
  (*   | var__term x => x *)
  (*   | let__term t__1 k__2 => eval (k__2 (eval t__1)) *)
  (*   | true__term => inj (true : value bool__type) *)
  (*   | false__term => inj (false : value bool__type) *)
  (*   | if__term t__1 t__2 t__3 => if (proj [[ t__1 ]]__eval) then [[ t__2 ]]__eval else [[ t__3 ]]__eval *)
  (*   | nil__term => inj (nil : value (list__type _)) *)
  (*   | cons__term t__1 t__2 => inj (cons (proj [[ t__1 ]]__eval) (proj [[ t__2 ]]__eval) : value (list__type _)) *)
  (*   | fold_right__term k__1 t__2 t__3 => *)
  (*       fold_right (fun x__1 x__2 => eval (k__1 (inj (x__1 : value (T__type _))) (toT x__2))) *)
  (*         [[ t__2 ]]__eval *)
  (*         (proj [[ t__3 ]]__eval) *)
  (*   | tick__term t__1 => [[ t__1 ]]__eval *)
  (*   | force__term t__1 => fromT [[ t__1 ]]__eval *)
  (*   | lazy__term t__1 => toT [[ t__1 ]]__eval *)
  (*   end *)
  (* where "[[ t ]]__eval" := (eval t). *)

  Fixpoint eval (alpha : type) (t : term rep alpha) : [[ alpha ]]__eval :=
    match t with
    | var__term x => proj x
    | let__term t__1 k__2 => [[ k__2 (inj [[ t__1 ]]__eval) ]]__eval
    | true__term => true
    | false__term => false
    | if__term t__1 t__2 t__3 => if [[ t__1 ]]__eval then [[ t__2 ]]__eval else [[ t__3 ]]__eval
    | nil__term => nil
    | cons__term t__1 t__2 => cons [[ t__1 ]]__eval [[ t__2 ]]__eval
    | fold_right__term k__1 t__2 t__3 =>
        fold_right
          (fun x__1 x__2 => eval (k__1 (inj x__1) (inj x__2)))
          [[ t__2 ]]__eval
          [[ t__3 ]]__eval
    | tick__term t__1 => [[ t__1 ]]__eval
    | force__term t__1 => [[ t__1 ]]__eval
    | lazy__term t__1 => [[ t__1 ]]__eval
    end
  where "[[ t ]]__eval" := (eval t).
End eval.

(* Fixpoint hom__demand : Hom := *)
(*   (* fun alpha beta => ⟦alpha⟧__eval -> ⟦beta⟧__eval * ⟦alpha⟧__approx. *) *)
(*   fun alpha beta => ⟦alpha⟧__eval -> term hom__demand value beta. *)

Require Import ExtLib.Data.Monads.StateMonad.
Import ListNotations.
Import MonadNotation.
Open Scope type_scope.

Module Type Map.
  Parameter t : Type.
  Parameter key : Type.
  Parameter val : Type.

  Parameter empty : t.
  Parameter update : (val -> val) -> val -> key -> val.
End Map.

Fixpoint demand1 (alpha beta : type) (k : [[ alpha ]]__eval -> term value beta) : [[ alpha ]]__eval -> [[ beta ]]__approx -> [[ alpha ]]__approx * nat.
  intros v outD.
  specialize (k v).

Fixpoint demand (alpha : type) (t : term (fun beta => nat * [[ beta ]]__eval) alpha) : [[ alpha ]]__approx -> state nat (list (nat * {beta : type & [[ beta ]]__approx}) * nat) :=
  match t with
  | true__term => fun _ => ret (nil, 0)
  | false__term => fun _ => ret (nil, 0)
  | var__term (x, _) => fun outD => ret ([(x, existT _ _ outD)], 0)
  | tick__term t__1 => fun outD =>
      '(Gamma, c) <- demand t__1 outD ;;
      ret (Gamma, S c)
  | lazy__term t__1 => fun outD => match outD with
                           | undefined => ret ([], 0)
                           | thunk outD__1 => demand t__1 outD__1
                           end
  | force__term t__1 => fun outD => demand t__1 (thunk outD)
  | _ => TODO
  end.


(* Fixpoint demand1 (alpha beta : type) (k : _ alpha -> term _ beta) (outD : [[ beta ]]__approx) : [[ alpha ]]__approx := *)
(*   match k (fun _ => _) with *)
(*   | true__t =>  *)
(*   | var__term x => _ *)
(*   | _ => TODO *)
(*   end. *)

Inductive lt : ∀ α, approx α -> approx α -> Prop :=
| lt_refl {α} (x : ⟦ α ⟧ₐ) : lt _ x x
| lt_undefined {α} (x : ⟦ T__t α ⟧ₐ) :
  lt (T__t α) undefined x
| lt_t {α} (x y : ⟦ α ⟧ₐ) :
  lt α x y ->
  lt (T__t α) (thunk x) (thunk y)
| lt_cons {α} (x₁ x₂ : ⟦ T__t α ⟧ₐ) (xs₁ xs₂ : ⟦ T__t (listA__t α) ⟧ₐ) :
  lt (T__t α) x₁ x₂ →
  lt (T__t (listA__t α)) xs₁ xs₂ →
  lt (listA__t α) (consA x₁ xs₁) (consA x₂ xs₂).

(* Import MonadNotation. *)
(* Open Scope monad_scope. *)

Fixpoint lub' {α : type} : ⟦ α ⟧ₐ → ⟦ α ⟧ₐ → option ⟦ α ⟧ₐ :=
  match α with
  | bool__t => Lub_bool
  | T__t _ => @Lub_T _ lub'
  | listA__t _ => @Lub_listA _ lub'
  end.

(*   match α return ⟦ α ⟧ₐ → ⟦ α ⟧ₐ → option ⟦ α ⟧ₐ with *)
(*   | bool__t => fun v₁ v₂ => match v₁, v₂ with *)
(*                         | true, true => Some true *)
(*                         | false, false => Some false *)
(*                         | _, _ => None *)
(*                         end *)
(*   | T__t α => fun v₁ v₂ => match v₁, v₂ with *)
(*                        | undefined, _ => Some v₂ *)
(*                        | _, undefined => Some v₁ *)
(*                        | thunk v₁₁, thunk v₁₂ => option_map thunk (lub v₁₁ v₁₂) *)
(*                        end *)
(*   | listA__t α => *)
(*       fun v₁ v₂ =>  *)

      (* fun v₁ v₂ => match v₁, v₂ with *)
      (*                      | nilA, nilA => Some nilA *)
      (*                      | consA v₁₁ v₁₂, consA v₂₁ v₂₂ => *)
      (*                          v₁' <- match v₁₁, v₂₁ with *)
      (*                                | undefined, _ => Some v₂₁ *)
      (*                                | _, undefined => Some v₁₁ *)
      (*                                | thunk v₁₁₁, thunk v₂₁₁ => option_map thunk (lub v₁₁₁ v₂₁₁) *)
      (*                                end ;; *)
      (*                          v₂' <- match v₁₂, v₂₂ with *)
      (*                                | undefined, _ => Some v₂₂ *)
      (*                                | _, undefined => Some v₁₂ *)
      (*                                | thunk v₁₂₁, thunk v₂₂₁ => option_map thunk (lub (v₁₂₁ : ⟦ listA__t _ ⟧ₐ) v₂₂₁) *)
      (*                                end ;; *)
      (*                          TODO *)
      (*                      | _, _ => None *)
      (*                      end *)
  end.

  intros v₁ v₂.
  destruct α.
  - exact TODO.
  - destruct v₁.
    + destruct v₂.
      * exact (option_map thunk (lub _ x x0)).
      * exact None.
    + exact (Some v₂).
  - destruct v₁, v₂.
    + exact (Some nilA).
    + exact None.
    + exact None.
    + destruct t, t1.
      * admit.
         
  
  
  match α as α return ⟦ α ⟧ₐ → ⟦ α ⟧ₐ → option ⟦ α ⟧ₐ with
  | listA__t α =>
      fun v₁ v₂ => match v₁, v₂ with
                (* | nilA, nilA => Some nilA *)
                | consA v₁₁ v₁₂, consA v₂₁ v₂₂ =>
                    v₁' <- match v₁₁, v₂₁ with
                          | None, _ => Some v₂₁
                          | Some x, Some y => Some (lub x y)
                          | _, _ => None
                          end ;;
                    v₂' <- match v₁₂, v₂₂ with
                          | None, _ => Some v₂₂
                          | Some x, Some y => Some (lub (x : ⟦ listA__t _ ⟧ₐ) y)
                          | _, _ => None
                          end ;;
                    ret (consA v₁' v₂')
                    (* match lub' v₁₁ v₂₁ lub, lub' (v₁₂ : ⟦ t__t (listA__t α) ⟧ₐ) v₂₂ lub with *)
                    (* | Some v₁', Some v₂' => Some (consA v₁' v₂') *)
                    (* | _, _ => None *)
                    (* end *)
                      (* | _, _ => None *)
                | _, _ => TODO
                end
  | _ => TODO
  end.
  
Section translate.

  Fixpoint translate_type (a : Lazy.type) : type :=
    match a with
    | Lazy.bool__t => bool__t
    | Lazy.list__t a => list__t (translate_type a)
    end.

  Context (rep : Rep).
  Local Notation term := (term rep).

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

End translate.
