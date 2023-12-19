(* Exception monad *)

From Equations Require Import Equations.
From Coq Require Import Utf8 List Arith Lia.
From PartialFun Require Import PartialFun Monad.

Import ListNotations.
Import MonadNotations.

Set Default Goal Selector "!".
Set Equations Transparent.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Inductive exn E A :=
| success (x : A)
| exception (e : E).

Arguments success {E A}.
Arguments exception {E A}.

Definition exn_bind {E A B} (c : exn E A) (f : A → exn E B) :=
  match c with
  | success x => f x
  | exception e => exception e
  end.

(* #[export] Instance *) Definition MonadExn {E} : Monad (exn E) := {|
  ret A x := success x ;
  bind A B c f := exn_bind c f
|}.

(* Exception monad transformer *)
(* #[export] Instance *) Definition MonadExnT {E M} `{Monad M} : Monad (λ A, M (exn E A)) := {|
  ret A x := ret (success x) ;
  bind A B c f := bind (M := M) c (λ x,
    match x with
    | success y => f y
    | exception e => ret (exception e)
    end
  )
|}.

Class MonadRaise E (M : Type → Type) := {
  raise : ∀ (A : Type), E → M A
}.

Arguments raise {E M _ A} e.

#[export] Instance MonadRaiseExnT {E M} `{Monad M} : MonadRaise E (λ A, M (exn E A)) := {|
  raise A e := ret (exception e)
|}.

#[export] Instance OrecEffectExn E : OrecEffect (exn E).
Proof.
  constructor.
  intros I H A B. apply MonadExnT.
Defined.

#[export] Existing Instance combined_monad.
