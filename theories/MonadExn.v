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

#[export] Typeclasses Opaque exn_bind.
Opaque exn_bind.

Definition MonadExn {E} : Monad (exn E) := {|
  ret A x := success x ;
  bind A B c f := exn_bind c f
|}.

(* Exception monad transformer *)
Definition MonadExnT {E M} `{Monad M} : Monad (λ A, M (exn E A)) := {|
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

#[export] Hint Mode MonadRaise ! ! : typeclass_instances.

Definition MonadRaiseExn {E} : MonadRaise E (exn E) :=
  {| raise := @exception E |}.

Definition MonadRaiseExnT {E M} `{Monad M} : MonadRaise E (λ A, M (exn E A)) := {|
  raise A e := ret (exception e)
|}.

Definition OrecEffectExn E : OrecEffect (exn E). 
Proof. 
  constructor; intros.
  apply MonadExnT.
Defined.

Definition OrecEffectExnRaise E I `{CallTypes I} A B: MonadRaise E (combined_orec (exn E) I A B) :=
{| 
  raise A e := ret (exception e)
|}.

Module ExportInstance.
  #[export]Existing Instance MonadExn | 5.
  #[export]Existing Instance MonadExnT.
  #[export]Existing Instance MonadRaiseExn.
  #[export]Existing Instance MonadRaiseExnT.
  #[export]Existing Instance OrecEffectExn.
  #[export]Existing Instance OrecEffectExnRaise.
End ExportInstance.