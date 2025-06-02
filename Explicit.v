Require Import Stdlib.Unicode.Utf8.
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
| bool__t : type
| T__t (alpha : type) : type
| list__t (alpha : type) : type.

Reserved Notation "⟦ alpha ⟧__eval".
Fixpoint value (alpha : type) : Type :=
  match alpha with
  | bool__t => bool
  | prod__t alpha beta => ⟦ alpha ⟧__eval * ⟦ beta ⟧__eval
  | T__t alpha => ⟦ alpha ⟧__eval
  | list__t alpha => list ⟦ alpha ⟧__eval
  end
where "⟦ α ⟧__eval" := (value α).

Reserved Notation "⟦ alpha ⟧__approx".
Fixpoint approx (α : type) : Type :=
  match α with
  | bool__t => bool
  | prod__t alpha beta => T ⟦ alpha ⟧__approx * T ⟦ beta ⟧__approx
  | T__t alpha => T ⟦ alpha ⟧__approx
  | list__t alpha => listA ⟦ alpha ⟧__approx
  end
where "⟦ alpha ⟧__approx" := (approx alpha).

Definition Rep : Type :=
  type -> Type.

Definition Hom : Type :=
  type -> type -> Type.

Section term.

  (* Context (hom : Hom). *)
  Context (rep : Rep).

  Inductive term : type -> Type :=
  | var__t `(x : rep alpha) : term alpha
  | let__t (alpha beta : type) (t__1 : term alpha) (t__2 : rep alpha -> term beta) : term beta
  | true__t : term bool__t
  | false__t : term bool__t
  | if__t (b : term bool__t) `(t : term alpha) (f : term alpha) : term alpha
  | proj1__t (alpha beta : type) : term (prod__t alpha beta) -> term alpha
  | proj2__t (alpha beta : type) : term (prod__t alpha beta) -> term beta
  | nil__t : `(term (list__t alpha))
  | cons__t `(x : term (T__t alpha)) (xs : term (T__t (list__t alpha))) : term (list__t alpha)
  | fold_right__t `(f : rep (T__t alpha) -> rep (T__t beta) -> term beta) (e : term beta) (xs : term (list__t alpha)) : term beta
  | tick__t `(t : term alpha) : term alpha
  | lazy__t `(t : term alpha) : term (T__t alpha)
  | force__t `(t : term (T__t alpha)) : term alpha.

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

(* Fixpoint hom__demand : Hom := *)
(*   (* fun alpha beta => ⟦alpha⟧__eval -> ⟦beta⟧__eval * ⟦alpha⟧__approx. *) *)
(*   fun alpha beta => ⟦alpha⟧__eval -> term hom__demand value beta. *)

Fixpoint demand (alpha : type) (t : term value α) : approx α → nat :=
  (* let demand1 (α : type) (t : term value α) *)
  match t with
  | var__t _ => fun _ => 0
  | let__t t₁ k₂ => fun d => let c__1 := demand (k₂ ⟦t₁⟧__eval) d in
                         let c₂ := demand t₁ d
  | _ => TODO
  end.

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
