Require Import Stdlib.Unicode.Utf8.

Require Import Stdlib.Bool.Bool.
Require Stdlib.Init.Nat.

Require Import LogicalLaziness.Core.
Require Import LogicalLaziness.Explicit.

Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.
Generalizable All Variables.

Inductive type : Type :=
| bool__t : type
| prod__t (a b : type)
| option__t (a : type) : type
| nat__t : type
| listA__t (a : type) : type.

Definition Rep : Type :=
  type -> Type.

Section term.

  Context (rep : Rep).

  Inductive term : type -> Type :=
  | false__t : term bool__t
  | true__t : term bool__t
  | equals__t `(u : term α) (v : term α) : term bool__t
  | approx__t `(u : term α) (v : term α) : term bool__t
  | if__t (c : term bool__t) `(t : term α) (f : term α) : term α
  | pair__t `(u : term α) `(v : term β) : term (prod__t α β)
  | fst__t `(t : term (prod__t α β)) : term α
  | snd__t `(t : term (prod__t α β)) : term β
  | Some__t `(u : term α) : term (option__t α)
  | None__t : `(term (option__t α))
  | option_rec__t `(u : rep α -> term β) (v : term β) (t : term (option__t α)) : term β
  | O__t : term nat__t
  | S__t (n : term nat__t) : term nat__t
  | iter__t (n : term nat__t) `(s : rep α -> term α) `(z : term α) : term α
  | nilA__t : `(term (listA__t α))
  | consA__t `(x : term (option__t α)) (xs : term (option__t (listA__t α))) : term (listA__t α)
  | fold_right__t `(f : rep (option__t α) -> rep (option__t β) -> term (m__t β)) (e : term β) (xs : term (listA__t α)) : term β
  | let__t `(d : term α) `(t : rep α -> term β) : term β
  | var__t `(x : rep α) : term α
  | choose__t `(u : term α) (v : term α) : term α
  | fail__t : `(term α)
  | free__t `(f : rep α → term β) : term β.

End term.

Definition program (α : type) : Type :=
  forall {rep}, term rep α.

Section eval.

  (* Embed object language types into metalanguage types. *)
  Reserved Notation "⌈ α ⌉".
  Fixpoint embed_type (α : type) : Type :=
    match α with
    | bool__t => bool
    | option__t α => option ⌈ α ⌉
    | prod__t α β => ⌈ α ⌉ * ⌈ β ⌉
    | nat__t => nat
    | listA__t α => listA ⌈ α ⌉
    end
  where "⌈ α ⌉" := (embed_type α).

  (* The language is nondeterministic, so a term is denoted by a set of
     values. *)
  Definition denote_type (α : type) : Type :=
    ⌈ α ⌉ → Prop.
  Notation "⟦ α ⟧" := (denote_type α).

  Local Notation term := (term embed_type).

  Reserved Notation "t ⇓ v" (at level 50).
  Inductive eval : `(term α -> ⟦ α ⟧) :=
  | false__d : false__t ⇓ false
  | true__d : true__t ⇓ true
  | equals__d
      `(t₁ : term α) (t₂ : term α) :
    `(t₁ ⇓ v₁ → t₂ ⇓ v₂ → reflect (v₁ = v₂) b → equals__t t₁ t₂ ⇓ b)
  | if__d
      `(c : term bool__t) `(t : term α) (f : term α) :
    `(c ⇓ b → (if b then t else f) ⇓ v → if__t c t f ⇓ v)
  | pair__d
      `(t₁ : term α) `(t₂ : term β) :
    `(t₁ ⇓ a → t₂ ⇓ b → pair__t t₁ t₂ ⇓ (a, b))
  | fst__d
      `(t : term (prod__t α β)) :
    `(t ⇓ v → fst__d t ⇓ fst v)
  | snd__d
      `(t : term (prod__t α β)) :
    `(t ⇓ v → snd__d t ⇓ snd v)
  | None__d : `(@None__t _ α ⇓ None)
  | Some__d `(t : term α) : `(t ⇓ v → Some__t t ⇓ Just v)
  | O__d : O__t ⇓ O
  | S__d : `(t ⇓ n → S__t t ⇓ (S n))
  | nilA__d : `(@nilA__t _ α ⇓ nilA)
  | consA__d
      `(t₁ : term (option__t α)) (t₂ : term (option__t (listA__t α))) :
    `(t₁ ⇓ v₁ → t₂ ⇓ v₂ → consA__t t₁ t₂ ⇓ consA v₁ v₂)
  | iter__d
      (n : term nat__t)
      `(s : ⌈ α ⌉ → term α) (z : term α) :
    `(n ⇓ n' → Nat.iter n' (lift__t s) z ⇓ v → iterate__t n s z ⇓ v)
  | let__d
      `(d : term α) `(b : ⌈ α ⌉ → term β) :
    `(d ⇓ v₁ → b v₁ ⇓ v₂ → let__t d b ⇓ v₂)
  | var__d `(t : term α) : `(t ⇓ v → var t ⇓ v)
  | choose_left__d `(t₁ : term α) (t₂ : term α) : `(t₁ ⇓ v → choose__t t₁ t₂ ⇓ v)
  | choose_right__d `(t₁ : term α) (t₂ : term α) : `(t₂ ⇓ v → choose__t t₁ t₂ ⇓ v)
  | free__d `(r : ⌈ α ⌉) `(k : ⌈ α ⌉ → term β) : `(k r ⇓ t → free__t k ⇓ t)
  where "t ⇓ v" := (eval t v).

End eval.

Section translate.

  (* Terms translated from the explicit language land in a writer monad over the
     natural numbers with addition, which we here denote m__t. *)
  Definition m__t (a : type) : type :=
    prod__t a nat__t.

  Context (rep : Rep).

  Local Notation term := (term rep).

  Definition lift__t `(f : rep α → term β) : term α → term β :=
    fun t => let__t t f.

  Definition assert__t (t1 : term bool__t) `(t2 : term a) : term a :=
    if__t t1 t2 fail__t.

  Definition add__t (m n : term nat__t) : term nat__t :=
    iter__t n (fun x => S__t (var__t x)) m.

  Definition bind__t `(u : term (m__t a)) `(k : rep a -> term (m__t b)) :
    term (prod__t b nat__t) :=
    let__t u
      (fun u =>
         let__t (fst__t (var__t u))
           (fun x =>
              let__t (k x)
                (fun v =>
                   pair__t
                     (fst__t (var__t v))
                     (add__t (snd__t (var__t u)) (snd__t (var__t v)))))).

  Definition pure__t `(u : term a) : term (m__t a) :=
    pair__t u O__t.

  Definition map__t `(f : rep a -> term b) (u : term (m__t a)) : term (m__t b) :=
    let__t u
      (fun u =>
         let__t (fst__t (var__t u))
           (fun x =>
              pair__t (f x) (snd__t (var__t u)))).

  Definition lazy__t `(u : term a) : term (option__t a) :=
    choose__t None__t (Some__t u).

  Definition lazily__t `(u : term (m__t a)) : term (m__t (option__t a)) :=
    choose__t (map__t (fun x => Some__t (var__t x)) u)
      (pair__t None__t O__t).

  Definition force__t `(u : term (option__t a)) : term (m__t a) :=
    option_rec__t (fun x => pure__t (var__t x)) fail__t u.

  Definition and__t (u v : rep bool__t) : term bool__t :=
    let u := var__t u in
    let v := var__t v in
    if__t u v false__t.

  Fixpoint translate_type (a : Explicit.type) : type :=
    match a with
    | Explicit.bool__t => bool__t
    | Explicit.t__t a => option__t (translate_type a)
    | Explicit.list__t a => listA__t (translate_type a)
    end.

  Definition rep' : Explicit.Rep :=
    fun α => rep (translate_type α).

  Fixpoint translate `(u : Explicit.term rep' a) : term (m__t (translate_type a)) :=
    match u with
    | Explicit.false__t =>
        pure__t false__t
    | Explicit.true__t =>
        pure__t true__t
    | Explicit.if__t c t f =>
        bind__t (translate c)
          (fun c => if__t (var__t c)
                   (translate t)
                   (translate f))
    | Explicit.nil__t =>
        pure__t nilA__t
    | Explicit.cons__t x xs =>
        bind__t (translate x)
          (fun x => bind__t (translate xs)
                   (fun xs => pure__t (consA__t (var__t x) (var__t xs))))
    | Explicit.foldr__t f e xs =>
        bind__t (translate e)
          (fun e => bind__t (translate xs)
                   (fun xs => pure__t (fold_right__t
                                      (fun x y => translate (f x y))
                                      (var__t e)
                                      (var__t xs))))
    | Explicit.var__t x =>
        pure__t (var__t x)
    | Explicit.let__t d b =>
        bind__t (translate d)
          (fun d => translate (b d))
    | Explicit.tick__t t =>
        let__t (translate t)
          (fun u => pair__t
                   (fst__t (var__t u))
                   (S__t (snd__t (var__t u))))
    | Explicit.lazy__t t =>
        bind__t (translate t)
          (fun t => (pure__t (choose__t
                             (Some__t (var__t t))
                             None__t)))
    | Explicit.force__t t =>
        bind__t (translate t)
          (fun t => pure__t (option_rec__t
                            var__t
                            fail__t
                            (var__t t)))
    end.

  (* Translate a term with one free variable. *)
  Definition translate1 `(f : rep' α → Explicit.term rep' β) :
    rep' α → term (m__t (translate_type β)) :=
    fun r => translate (f r).

  Definition demand
    `(input : rep' α)
    `(outputD : rep' β)
    `(f : rep' α → Explicit.term rep' β) : term (m__t (translate_type α)) :=
    free__t
      (fun inputD =>
         free__t
           (fun c =>
              assert__t (approx__t (var__t inputD) (var__t input))
                (assert__t (equals__t
                              (translate1 f inputD)
                              (pair__t (var__t outputD) (var__t c)))
                   (pair__t (var__t inputD) (var__t c))))).

(*
let inputD free in
let c free in
assert inputD ≲ input;
assert ⟦f⟧(inputD) = (outputD, c);
(inputD, c)

⟦t⟧__demand : ⟦Γ⟧__eval × ⟦B⟧__approx → ⟦Γ⟧__approx × ℕ
*)


End translate.
