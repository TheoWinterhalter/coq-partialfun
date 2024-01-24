(* (Yet another) description of monads *)

From Equations Require Import Equations.
From Coq Require Import Utf8 List Arith Lia.
Import ListNotations.

Set Default Goal Selector "!".
Set Equations Transparent.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Class Monad (M : Type → Type) := {
  ret : ∀ A, A → M A ;
  bind : ∀ A B, M A → (A → M B) → M B
}.

#[global] Hint Mode Monad ! : typeclass_instances.
Arguments ret {M _ A}.
Arguments bind {M _ A B}.

Definition map {M} `{Monad M} {A B} (f : A → B) (m : M A) : M B :=
  bind m (λ x, ret (f x)).

Module MonadNotations.

  Declare Scope monad_scope.
  Delimit Scope monad_scope with monad.

  Open Scope monad_scope.

  Notation "c >>= f" :=
    (bind c f)
    (at level 50, left associativity) : monad_scope.

  Notation "x ← e ;; f" :=
    (bind e (λ x, f))
    (at level 100, e at next level, right associativity)
    : monad_scope.

  Notation "x ← e ;;[ M ] f" :=
      (bind (M:=M) e (λ x, f))
      (at level 100, e at next level, M at level 50, right associativity)
      : monad_scope.

  Notation "' pat ← e ;; f" :=
    (bind e (λ pat, f))
    (at level 100, e at next level, right associativity, pat pattern)
    : monad_scope.

  Notation "' pat ← e ;;[ M ] f" :=
    (bind (M:=M) e (λ pat, f))
    (at level 100, e at next level, M at level 50, right associativity, pat pattern)
    : monad_scope.

  Notation "e ;; f" :=
    (bind e (λ _, f))
    (at level 100, right associativity)
    : monad_scope.

  Notation "e ;;[ M ] f" :=
    (bind (M:=M) e (λ _, f))
    (at level 100, M at level 50, right associativity)
    : monad_scope.

  Notation "f '<*>' m" :=
    (map f m)
    (at level 50, left associativity)
    : monad_scope.

End MonadNotations.
