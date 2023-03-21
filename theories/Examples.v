From Equations Require Import Equations.
From Coq Require Import Utf8 List Arith Lia.
Import ListNotations.
From PartialFun Require Import PartialFun.
(* Small examples *)

Equations div : ∇ (p : nat * nat), nat :=
  div (0, m) := ret 0 ;
  div (n, m) := q ← rec (n - m, m) ;; ret (S q).

Equations test_div : ∇ (p : nat * nat), bool :=
  test_div (n, m) := q ← call div (n, m) ;; ret (q * m =? n).

Definition div_10_5 := div @ (10, 5).
Fail Definition div_10_0 := div @ (10, 0).

Compute div @ (50,6).

Lemma div_below :
  funind div
    (λ '(n, m), n < m)
    (λ '(n, m) q, match n with 0 => q = 0 | _ => q = 1 end).
Proof.
  intros [n m] h.
  funelim (div (n, m)).
  all: cbn - ["-"].
  - reflexivity.
  - split.
    + lia.
    + intros q hq.
      replace (S n - m) with 0 in hq by lia.
      lia.
Qed.

Lemma div_domain :
  ∀ n m,
    (n = 0 ∨ m ≠ 0) →
    domain div (n, m).
Proof.
  intros n m hm.
  assert (hw : WellFounded lt).
  { exact _. }
  specialize (hw n). induction hw as [n hn ih].
  apply compute_domain. funelim (div (n, m)). all: cbn - ["-"].
  - constructor.
  - split. 2: auto.
    apply ih. all: lia.
Qed.

Lemma div_domain_implies :
  ∀ n m,
    domain div (n, m) →
    n = 0 ∨ m ≠ 0.
Proof.
  assert (h : funind div (λ _, True) (λ '(n, m) _, n = 0 ∨ m ≠ 0)).
  { intros [n m] _.
    funelim (div (n, m)). all: cbn - ["-"].
    - left. reflexivity.
    - intuition lia.
  }
  intros n m [v hd].
  refine (funind_graph _ _ _ (_,_) _ h _ _). all: eauto.
Qed.

Lemma test_div_domain :
  ∀ n m,
    (n = 0 ∨ m ≠ 0) →
    domain test_div (n, m).
Proof.
  intros n m hm.
  apply compute_domain. simpl.
  split. 2: auto.
  apply div_domain. assumption.
Qed.

(* Example: Untyped λ-calculus *)

Inductive term : Type :=
| tVar (n : nat)
| tLam (t : term)
| tApp (u v : term).

Fixpoint lift n k t :=
  match t with
  | tVar i => tVar (if Nat.leb k i then (n + i) else i)
  | tLam t => tLam (lift n (S k) t)
  | tApp u v => tApp (lift n k u) (lift n k v)
  end.

Fixpoint substk k t u :=
  match t with
  | tVar n =>
    match Nat.compare k n with
    | Eq => lift k 0 u
    | Gt => tVar n
    | Lt => tVar (Nat.pred n)
    end
  | tLam t => tLam (substk (S k) t u)
  | tApp f x => tApp (substk k f u) (substk k x u)
  end.

Notation subst t u := (substk 0 t u).

Inductive stack :=
| sApp (u : term) (π : stack)
| sLam (π : stack)
| sNil.

Fixpoint zip t π :=
  match π with
  | sApp u π => zip (tApp t u) π
  | sLam π => zip (tLam t) π
  | sNil => t
  end.

(* What we want *)
Fail Equations eval (u : term) (π : stack) : term :=
  eval (tVar n) π := zip (tVar n) π ;
  eval (tLam t) (sApp u π) := eval (subst t u) π ;
  eval (tLam t) π := eval t (sLam π) ;
  eval (tApp u v) π := eval u (sApp v π).

(* Notice the partial arrow "⇀" *)
Equations eval : term * stack ⇀ term :=
  eval (tVar n, π) := ret (zip (tVar n) π) ;
  eval (tLam t, sApp u π) := v ← rec (subst t u, π) ;; ret v ;
  eval (tLam t, π) := v ← rec (t, sLam π) ;; ret v ;
  eval (tApp u v, π) := w ← rec (u, sApp v π) ;; ret w.

(* We get the fueled and wf versions for free *)

Definition eval_fuel n t π := fueled eval n (t, π).

Definition eval_def t π := def eval (t, π).

(* Extraction eval_def. *)

(* Let's prove some properties about eval *)

Inductive red : term → term → Prop :=
| red_beta :
    ∀ t u,
      red (tApp (tLam t) u) (subst t u)

| red_lam :
    ∀ t t',
      red t t' →
      red (tLam t) (tLam t')

| red_app_l :
    ∀ u v u',
      red u u' →
      red (tApp u v) (tApp u' v)

| red_app_r :
    ∀ u v v',
      red v v' →
      red (tApp u v) (tApp u v').

Import Relation_Operators Relation_Definitions.

Definition reds :=
  clos_refl_trans _ red.

Lemma reds_trans :
  ∀ u v w,
    reds u v →
    reds v w →
    reds u w.
Proof.
  apply rt_trans.
Qed.

Lemma red_zip :
  ∀ u v π,
    red u v →
    red (zip u π) (zip v π).
Proof.
  intros u v π h.
  induction π as [w π ih | π ih |] in u, v, h |- *.
  - simpl. eapply ih. constructor. assumption.
  - simpl. eapply ih. constructor. assumption.
  - simpl. assumption.
Qed.

Lemma reds_zip :
  ∀ u v π,
    reds u v →
    reds (zip u π) (zip v π).
Proof.
  intros u v π h.
  induction h as [u v h | u | u v w h1 ih1 h2 ih2] in π |- *.
  - constructor. apply red_zip. assumption.
  - apply rt_refl.
  - eapply rt_trans.
    + eapply ih1.
    + eapply ih2.
Qed.

Lemma eval_sound :
  funind eval (λ _, True) (λ '(t, π) v, reds (zip t π) v).
Proof.
  intros [t π] _. funelim (eval (_, _)).
  all: simpl.
  - apply rt_refl.
  - split. 1: constructor.
    intros v h.
    eapply reds_trans. 2: eassumption.
    eapply reds_zip. constructor. constructor.
  - split. 1: constructor.
    intros v h. assumption.
  - intuition assumption.
  - split. 1: constructor.
    intros w h. assumption.
Qed.

Lemma eval_fuel_sound :
  ∀ n t π v,
    eval_fuel n t π = Success v →
    reds (zip t π) v.
Proof.
  intros n t π v h.
  refine (funind_fuel _ _ _ (_,_) _ _ eval_sound _ h).
  constructor.
Qed.

Lemma eval_def_sound :
  ∀ t π h,
    reds (zip t π) (eval_def t π h).
Proof.
  intros t π h.
  refine (def_ind _ _ _ (_,_) _ eval_sound _).
  constructor.
Qed.

(* Tests *)

Definition t₀ :=
  tApp (tLam (tVar 0)) (tLam (tVar 1)).

Compute (eval_fuel 1000 t₀ sNil).
Definition nf₀ : term := eval @ (t₀, sNil).
Compute nf₀.

Definition t₁ :=
  tLam t₀.

Compute (eval_fuel 1000 t₁ sNil).
Definition nf₁ : term := eval @ (t₁, sNil).

Definition tDelta :=
  tLam (tApp (tVar 0) (tVar 0)).

Compute (eval_fuel 1000 tDelta sNil).
Definition nfDela : term := eval @ (tDelta, sNil).

Definition tOmega :=
  tApp tDelta tDelta.

Compute (eval_fuel 1000 tOmega sNil).
Fail Definition nfOmega : term := eval @ (tOmega, sNil).

Definition t₂ :=
  tApp (tApp t₁ (tVar 2)) tOmega.

Compute (eval_fuel 1000 t₂ sNil).
Definition nf₂ : term := eval @ (t₂, sNil).

(* Composition test with a conversion checker *)

Fixpoint eqterm (u v : term) : bool :=
  match u, v with
  | tVar i, tVar j => i =? j
  | tApp u u', tApp v v' => eqterm u v && eqterm u' v'
  | tLam u, tLam v => eqterm u v
  | _, _ => false
  end.

Equations conv : ∇ (p : term * term), bool :=
  conv (u, v) :=
    u' ← call eval (u, sNil) ;;
    v' ← call eval (v, sNil) ;;
    ret (eqterm u' v').

Definition conv_fuel n u v := fueled conv n (u, v).
Definition conv_def u v := def conv (u, v).

(* We cannot compute the thing below yet, need Acc gen trick *)

Definition delta_refl : bool := conv @ (tDelta, tDelta).

Fail Definition omega_refl : bool := conv @ (tOmega, tOmega).

Compute conv_fuel 1000 t₂ (tVar 2).
Compute conv_fuel 1000 t₂ (tVar 0).

(* We can also prove properties about conv *)

Definition isconv u v :=
  ∃ u' v',
    reds u u' ∧
    reds v v' ∧
    eqterm u' v' = true.

Ltac splits :=
  lazymatch goal with
  | |- _ ∧ _ => split ; splits
  | |- _ * _ => split ; splits
  | |- _ => idtac
  end.

Lemma conv_sound :
  funind conv (λ _, True) (λ '(u, v) b, b = true → isconv u v).
Proof.
  intros [u v] _. simpl.
  eexists _, _. splits.
  1: apply eval_sound.
  1: simpl ; auto.
  simpl. intros u' hu.
  eexists _, _. splits.
  1: apply eval_sound.
  1: simpl ; auto.
  simpl. intros v' hv e.
  exists u', v'.
  intuition assumption.
Qed.

(* We now wish to use this definition for a class we know to be terminating. *)

Inductive type :=
| base
| arrow (a b : type).

Definition context := list type.

Inductive typing (Γ : context) : term → type → Prop :=
| typing_var :
    ∀ n A,
      nth_error Γ n = Some A →
      typing Γ (tVar n) A

| typing_lam :
    ∀ t A B,
      typing (A :: Γ) t B →
      typing Γ (tLam t) (arrow A B)

| typing_app :
    ∀ t u A B,
      typing Γ t (arrow A B) →
      typing Γ u A →
      typing Γ (tApp t u) B.

Definition cored u v :=
  red v u.

(* A term is strongly normalising when all its reduction paths are finite *)
Definition SN (t : term) := Acc cored t.

(* We could prove that all well-typed terms are SN. *)

(* We also need the subterm relation (or a subset of it) *)

Inductive subterm : term → term → Prop :=
| subterm_lam : ∀ t, subterm t (tLam t)
| subterm_app : ∀ u v, subterm u (tApp u v).

Derive Signature for subterm.
Derive NoConfusion NoConfusionHom for term.

Lemma subterm_wf :
  well_founded subterm.
Proof.
  intros t.
  induction t as [n | t ih | u ihu v ihv].
  - constructor. intros t h. depelim h.
  - constructor. intros t' h. depelim h. assumption.
  - constructor. intros t h. depelim h. assumption.
Qed.

Definition lex {A B} (leA : A → A → Prop) (leB : B → B → Prop) :=
  lexprod leA (λ _, leB).

Notation "( u ; v )" := (existT _ u v).

Lemma lex_acc :
  ∀ A B leA leB x y,
    @Acc A leA x →
    @well_founded B leB →
    Acc (lex leA leB) (x ; y).
Proof.
  intros A B leA leB x y hA hB.
  eapply Lexicographic_Product.acc_A_B_lexprod. all: eauto.
Qed.

Definition R_aux :=
  lex cored subterm.

Definition R x y :=
  let u := fst x in
  let π := snd x in
  let v := fst y in
  let ρ := snd y in
  R_aux (zip u π ; u) (zip v ρ ; v).

Lemma R_acc :
  ∀ t π,
    Acc cored (zip t π) →
    Acc R (t, π).
Proof.
  intros t π h.
  eapply lex_acc with (y := t) (leB := subterm) in h. 2: eapply subterm_wf.
  remember (zip t π ; t) as z eqn:e.
  induction h as [z h ih] in t, π, e |- *. subst.
  constructor. intros [v ρ] hr.
  red in hr. red in hr. simpl in hr.
  eapply ih. 2: reflexivity.
  assumption.
Qed.

Lemma R_left :
  ∀ u v π ρ,
    red (zip v ρ) (zip u π) →
    R (u, π) (v, ρ).
Proof.
  intros u v π ρ h.
  apply left_lex. red. assumption.
Qed.

Lemma right_lex_eq :
  ∀ A B (leA : A → A → Prop) (leB : B → B → Prop) a a' b b',
    a = a' →
    leB b b' →
    lex leA leB (a ; b) (a' ; b').
Proof.
  intros A B leA leB a a' b b' e h.
  subst a'.
  apply right_lex. assumption.
Qed.

Lemma R_right :
  ∀ u v π ρ,
    zip u π = zip v ρ →
    subterm u v →
    R (u, π) (v, ρ).
Proof.
  intros u v π ρ e h.
  apply right_lex_eq. all: eauto.
Qed.

Lemma SN_eval_domain :
  ∀ t π,
    SN (zip t π) →
    domain eval (t, π).
Proof.
  intros t π h.
  eapply R_acc in h.
  set (z := (t, π)) in *. clearbody z.
  induction h as [z h ih].
  apply compute_domain. funelim (eval z).
  all: simpl.
  2-5: split ; [| auto].
  - auto.
  - apply ih. apply R_left. simpl.
    apply red_zip. constructor.
  - apply ih. apply R_right. 1: reflexivity.
    constructor.
  - apply ih. apply R_right. 1: reflexivity.
    constructor.
  - apply ih. apply R_right. 1: reflexivity.
    constructor.
Qed.