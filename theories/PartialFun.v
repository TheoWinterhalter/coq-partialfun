(* Open general recursion library *)

From Equations Require Import Equations.
From Coq Require Import Utf8 List Arith Lia.
Import ListNotations.

Set Default Goal Selector "!".
Set Equations Transparent.
Set Universe Polymorphism.

(* TODOs

  - Maybe some subclasses to be able to only specify the fueled and/or the wf
    versions.
    + Maybe use a hint with high cost for the default instance to ease override.
  - Make fueled resumable so it can be composed in the continuation to have
    exponential fuel with linear input.
  - Use the Acc_gen trick for the success_domain stuff.
  - Mutual functions without the need for encoding?

*)

(* A class of true booleans *)

Class IsTrue (b : bool) := {
  is_true : b = true
}.

#[export] Hint Extern 1 (IsTrue ?b) =>
  constructor ; reflexivity
  : typeclass_instances.

(* Specific to fuel implementations *)

Inductive Fueled (A : Type) :=
| Success (b : A)
| NotEnoughFuel
| Undefined.

Arguments Success {A}.
Arguments NotEnoughFuel {A}.
Arguments Undefined {A}.

Derive NoConfusion NoConfusionHom for Fueled.

(* Partial function class *)
Class PFun {A} (f : A) := {
  psrc : Type ;
  ptgt : psrc → Type ;
  pgraph : ∀ x, ptgt x → Prop ;
  pdomain x := ∃ v, pgraph x v ;
  pgraph_fun : ∀ x v w, pgraph x v → pgraph x w → v = w ;
  pfueled : nat → ∀ x, Fueled (ptgt x) ;
  pfueled_graph : ∀ n x v, pfueled n x = Success v → pgraph x v ;
  pdef : ∀ x, pdomain x → ptgt x ;
  pdef_graph : ∀ x h, pgraph x (pdef x h) ;
  pfunind : (psrc → Prop) → (∀ x, ptgt x → Prop) → Prop ;
  pfunind_graph : ∀ φ ψ x v, pfunind φ ψ → φ x → pgraph x v → ψ x v
}.

Arguments psrc {A} f {_}.
Arguments ptgt {A} f {_}.
Arguments pgraph {A} f {_}.
Arguments pdomain {A} f {_}.
Arguments pgraph_fun {A} f {_}.
Arguments pfueled {A} f {_}.
Arguments pfueled_graph {A} f {_}.
Arguments pdef {A} f {_}.
Arguments pdef_graph {A} f {_}.
Arguments pfunind {A} f {_}.
Arguments pfunind_graph {A} f {_}.

Lemma pfunind_fueled :
  ∀ A f `{PFun A f} φ ψ n x v,
    pfunind f φ ψ →
    pfueled f n x = Success v →
    φ x →
    ψ x v.
Proof.
  intros A f hf φ ψ n x v hfi e hpre.
  apply pfueled_graph in e.
  eapply pfunind_graph. all: eassumption.
Qed.

Lemma pfunind_def :
  ∀ A f `{PFun A f} φ ψ x h,
    pfunind f φ ψ →
    φ x →
    ψ x (pdef f x h).
Proof.
  intros A f hf φ ψ x h hfi hpre.
  eapply pfunind_graph. 1,2: eassumption.
  apply pdef_graph.
Qed.

Inductive orec A B C :=
| ret (x : C)
| rec (x : A) (κ : B x → orec A B C)
| call F f `{hf : PFun F f} (x : psrc f) (κ : ptgt f x → orec A B C)
| undefined.

Arguments ret {A B C}.
Arguments rec {A B C}.
Arguments call {A B C F} f {hf}.
Arguments undefined {A B C}.

Notation "∇ x , B" :=
  (∀ x, orec _ (λ x, B) B)
  (x binder, at level 200).

Notation "A ⇀ B" :=
  (∇ (_ : A), B)
  (at level 199).

Notation "x ← e ;; f" :=
  (e (λ x, f))
  (at level 100, e at next level, right associativity, only parsing).

Notation "' pat ← e ;; f" :=
  (e (λ x, f))
  (at level 100, e at next level, right associativity, pat pattern, only parsing).

#[local] Notation "t ∙1" := (proj1_sig t) (at level 20).
#[local] Notation "⟨ x ⟩" := (exist _ x _) (only parsing).
#[local] Notation "⟨ x | h ⟩" := (exist _ x h).

Section Lib.

  Context {A B} (f : ∇ (x : A), B x).

  Inductive orec_graph {a} : orec A B (B a) → B a → Prop :=
  | ret_graph :
      ∀ x,
        orec_graph (ret x) x

  | rec_graph :
      ∀ x κ v w,
        orec_graph (f x) v →
        orec_graph (κ v) w →
        orec_graph (rec x κ) w

  | call_graph :
      ∀ F g hg x κ v w,
        pgraph g x v →
        orec_graph (κ v) w →
        orec_graph (call (F := F) g (hf := hg) x κ) w.

  Definition graph x v :=
    orec_graph (f x) v.

  Inductive orec_lt {a} : A → orec A B (B a) → Prop :=
  | top_lt :
      ∀ x κ,
        orec_lt x (rec x κ)

  | rec_lt :
      ∀ x κ v y,
        graph x v →
        orec_lt y (κ v) →
        orec_lt y (rec x κ)

  | call_lt :
      ∀ F g hg x κ v y,
        pgraph g x v →
        orec_lt y (κ v) →
        orec_lt y (call (F := F) g (hf := hg) x κ).

  Definition partial_lt x y :=
    orec_lt x (f y).

  Definition domain x :=
    ∃ v, graph x v.

  Derive Signature for orec_graph.
  Derive Signature for orec_lt.
  Derive NoConfusion NoConfusionHom for orec.

  Lemma orec_graph_functional :
    ∀ a o v w,
      orec_graph (a := a) o v →
      orec_graph o w →
      v = w.
  Proof.
    intros a o v w hv hw.
    induction hv in w, hw |- *.
    - depelim hw. reflexivity.
    - depelim hw.
      assert (v = v0).
      { apply IHhv1. assumption. }
      subst. apply IHhv2. assumption.
    - depelim hw.
      assert (v = v0).
      { apply pgraph_fun. all: assumption. }
      subst. apply IHhv. assumption.
  Qed.

  Lemma lt_preserves_domain :
    ∀ x y,
      domain x →
      partial_lt y x →
      domain y.
  Proof.
    intros x y h hlt.
    destruct h as [v h].
    red in hlt. red in h.
    set (o := f _) in *. clearbody o.
    induction h in y, hlt |- *.
    - depelim hlt.
    - depelim hlt.
      + eexists. eassumption.
      + assert (v = v0).
        { eapply orec_graph_functional. all: eassumption. }
        subst.
        apply IHh2. assumption.
    - depelim hlt.
      assert (v = v0).
      { eapply pgraph_fun. all: eassumption. }
      subst.
      apply IHh. assumption.
  Qed.

  (* Fuel version *)

  Fixpoint orec_fuel_inst {a} n (e : orec A B (B a)) (r : ∀ x, Fueled (B x)) :=
    match e with
    | ret v => Success v
    | rec x κ =>
      match r x with
      | Success v => orec_fuel_inst n (κ v) r
      | NotEnoughFuel => NotEnoughFuel
      | Undefined => Undefined
      end
    | call g x κ =>
      match pfueled g n x with
      | Success v => orec_fuel_inst n (κ v) r
      | NotEnoughFuel => NotEnoughFuel
      | Undefined => Undefined
      end
    | undefined => Undefined
    end.

  Fixpoint fueled n x : Fueled (B x) :=
    match n with
    | 0 => NotEnoughFuel
    | S n => orec_fuel_inst n (f x) (fueled n)
    end.

  (* We show the fueled version is sound with respect to the graph *)

  Lemma orec_fuel_inst_graph :
    ∀ a n (o : orec _ _ (_ a)) r v,
      orec_fuel_inst n o r = Success v →
      (∀ x w, r x = Success w → graph x w) →
      orec_graph o v.
  Proof.
    intros a n o r v e hr.
    induction o as [w | x κ ih | G g hg x κ ih |] in v, e |- *.
    - simpl in e. noconf e. constructor.
    - simpl in e. destruct r as [w | |] eqn:e'. 2,3: discriminate.
      econstructor.
      + eapply hr. eassumption.
      + apply ih. assumption.
    - simpl in e. destruct pfueled as [w | |] eqn:e'. 2,3: discriminate.
      econstructor.
      + eapply pfueled_graph. eassumption.
      + apply ih. assumption.
    - discriminate.
  Qed.

  Lemma fueled_graph_sound :
    ∀ n x v,
      fueled n x = Success v →
      graph x v.
  Proof.
    intros n x v e.
    induction n as [| n ih] in x, v, e |- *. 1: discriminate.
    simpl in e.
    eapply orec_fuel_inst_graph. all: eassumption.
  Qed.

  (** Note: the lemma above says that if fueled succeeds, then its argument is
      in the domain of f, so later on we can use it in the well-founded version.
      In particular we can do a nice construction that automatically builds the
      proof when it exists.
  **)

  Definition succeeds n x :=
    match fueled n x with
    | Success v => true
    | _ => false
    end.

  Definition succeeds_domain :
    ∀ n x,
      succeeds n x = true →
      domain x.
  Proof.
    intros n x e.
    unfold succeeds in e. destruct fueled as [v | |] eqn: e'. 2,3: discriminate.
    exists v. eapply fueled_graph_sound. eassumption.
  Qed.

  (* Well-founded version *)

  Lemma partial_lt_acc :
    ∀ x,
      domain x →
      Acc partial_lt x.
  Proof.
    intros x h.
    destruct h as [v h].
    constructor. intros x' h'.
    red in h. red in h'.
    set (o := f _) in *. clearbody o.
    induction h in x', h' |- *.
    - depelim h'.
    - depelim h'.
      + constructor. intros y h.
        apply IHh1. assumption.
      + assert (v = v0).
        { eapply orec_graph_functional. all: eassumption. }
        subst.
        apply IHh2. assumption.
    - depelim h'.
      assert (v = v0).
      { eapply pgraph_fun. all: eassumption. }
      subst.
      apply IHh. assumption.
  Qed.

  Notation sigmaarg :=
    (sigma (λ x, domain x)).

  #[local] Instance wf_partial :
    WellFounded (λ (x y : sigmaarg), partial_lt (pr1 x) (pr1 y)).
  Proof.
    intros [x h].
    pose proof (partial_lt_acc x h) as hacc.
    induction hacc as [x hacc ih] in h |- *.
    constructor. intros [y h'] hlt.
    apply ih. assumption.
  Qed.

  Definition image x :=
    { v | graph x v }.

  Definition oimage {a} (o : orec A B (B a)) :=
    { v | orec_graph o v }.

  Definition orec_domain {a} (o : orec A B (B a)) :=
    ∃ v, orec_graph o v.

  Equations? orec_inst {a} (e : orec A B (B a)) (de : orec_domain e)
    (da : domain a)
    (ha : ∀ x, orec_lt x e → partial_lt x a)
    (r : ∀ y, domain y → partial_lt y a → image y) : oimage e :=
    orec_inst (ret v) de da ha r := ⟨ v ⟩ ;
    orec_inst (rec x κ) de da ha r := ⟨ (orec_inst (κ ((r x _ _) ∙1)) _ _ _ r) ∙1 ⟩ ;
    orec_inst (call g x κ) de da ha r := ⟨ (orec_inst (κ (pdef g x _)) _ _ _ r) ∙1 ⟩ ;
    orec_inst undefined de da ha r := False_rect _ _.
  Proof.
    - constructor.
    - eapply lt_preserves_domain. 1: eassumption.
      apply ha. constructor.
    - apply ha. constructor.
    - destruct de as [v hg]. depelim hg. simpl in *.
      destruct r as [w hw]. simpl.
      red in hw.
      assert (w = v0).
      { eapply orec_graph_functional. all: eassumption. }
      subst.
      eexists. eassumption.
    - apply ha. econstructor. 2: eassumption.
      red. destruct r. assumption.
    - simpl. destruct orec_inst. simpl.
      econstructor. 2: eassumption.
      destruct r. assumption.
    - destruct de as [v hg]. depelim hg.
      eexists. eassumption.
    - lazymatch goal with
      | |- context [ pdef g x ?prf ] => set (hh := prf) ; clearbody hh
      end.
      destruct de as [v hg]. depelim hg. simpl in *.
      pose proof (pdef_graph g x hh) as hg'.
      move hg' at top. eapply pgraph_fun in hg'. 2: eassumption.
      subst. eexists. eassumption.
    - lazymatch goal with
      | h : context [ pdef g x ?prf ] |- _ =>
          set (hh := prf) in h ; clearbody hh
      end.
      apply ha. econstructor. 2: eassumption.
      apply pdef_graph.
    - destruct orec_inst. simpl.
      lazymatch goal with
      | h : context [ pdef g x ?prf ] |- _ =>
          set (hh := prf) in h ; clearbody hh
      end.
      econstructor. 2: eassumption.
      apply pdef_graph.
    - destruct de as [v hg]. depelim hg.
  Defined.

  Equations def_p (x : A) (h : domain x) : image x
    by wf x partial_lt :=
    def_p x h := orec_inst (a := x) (f x) _ _ _ (λ y hy hr, def_p y _).

  Definition def x h :=
    def_p x h ∙1.

  Lemma def_graph_sound :
    ∀ x h,
      graph x (def x h).
  Proof.
    intros x h.
    unfold def. destruct def_p. assumption.
  Qed.

  (* Well-founded version with automatic domain inferrence *)

  Definition autodef (x : A) `{e : IsTrue (succeeds 1000 x)} :=
    def x (succeeds_domain 1000 x e.(is_true)).

  (* Proving properties about such functions *)

  Notation precond := (A → Prop).
  Notation postcond := (∀ x, B x → Prop).

  Fixpoint orec_ind_step a (pre : precond) (post : postcond) o :=
    match o with
    | ret v => post a v
    | rec x κ => pre x ∧ ∀ v, post x v → orec_ind_step a pre post (κ v)
    | call g x κ =>
        ∃ φ ψ, pfunind g φ ψ ∧ φ x ∧ ∀ v, ψ x v → orec_ind_step a pre post (κ v)
    | undefined => True
    end.

  Definition funind (pre : precond) post :=
    ∀ x, pre x → orec_ind_step x pre post (f x).

  (* The fueled case *)

  Lemma orec_fuel_inst_ind_step :
    ∀ a n pre post o r v,
      orec_ind_step a pre post o →
      orec_fuel_inst n o r = Success v →
      (∀ x w, pre x → r x = Success w → post x w) →
      post a v.
  Proof.
    intros a n pre post o r v h e hr.
    induction o as [w | x κ ih | G g hg x κ ih |] in v, h, e |- *.
    - simpl in *. noconf e. assumption.
    - simpl in *. destruct r as [w | |] eqn:e'. 2,3: discriminate.
      eapply ih. 2: eassumption.
      apply h. eapply hr.
      + apply h.
      + assumption.
    - simpl in *.
      destruct pfueled as [w | |] eqn:e'. 2,3: discriminate.
      eapply ih. 2: eassumption.
      destruct h as [φ [ψ [hig [hx hκ]]]].
      apply hκ. eapply pfunind_fueled. all: eassumption.
    - discriminate.
  Qed.

  Lemma funind_fuel :
    ∀ pre post x n v,
      funind pre post →
      pre x →
      fueled n x = Success v →
      post x v.
  Proof.
    intros pre post x n v h hpre e.
    induction n as [| n ih] in x, v, hpre, e |- *. 1: discriminate.
    eapply orec_fuel_inst_ind_step. 2: eassumption.
    - apply h. assumption.
    - apply ih.
  Qed.

  (* The wf case *)

  Lemma orec_inst_ind_step :
    ∀ a o hdo da ha (r : ∀ y, domain y → partial_lt y a → image y) pre post,
      orec_ind_step a pre post o →
      (∀ x h hlt, pre x → post x ((r x h hlt) ∙1)) →
      post a ((orec_inst (a := a) o hdo da ha r) ∙1).
  Proof.
    intros a o hdo da ha r pre post ho hr.
    induction o as [w | x κ ih | G g hg x κ ih |] in ha, hdo, ho |- *.
    - simpl in ho. simp orec_inst.
    - simpl in ho. simp orec_inst. simpl.
      apply ih. apply ho. apply hr. apply ho.
    - simpl in ho. simp orec_inst. simpl.
      apply ih.
      destruct ho as [φ [ψ [hig [hx hκ]]]].
      apply hκ. eapply pfunind_def. all: eassumption.
    - destruct hdo as [? h]. depelim h.
  Qed.

  Lemma def_ind :
    ∀ pre post x h,
      funind pre post →
      pre x →
      post x (def x h).
  Proof.
    intros pre post x h ho hpre.
    unfold def.
    revert hpre.
    (* funelim fails with an anomaly *)
    apply_funelim (def_p x h). intros.
    refine (orec_inst_ind_step _ _ _ _ _ _ _ _ _ _).
    - apply ho. assumption.
    - intros. eapply H1. assumption.
  Qed.

  (* We deduce the graph case from the above *)

  Lemma funind_graph :
    ∀ pre post x v,
      funind pre post →
      pre x →
      graph x v →
      post x v.
  Proof.
    intros pre post x v h hpre e.
    assert (hx : domain x).
    { eexists. eassumption. }
    pose proof (def_graph_sound x hx) as hgr.
    assert (v = def x hx).
    { eapply orec_graph_functional. all: eassumption. }
    subst.
    eapply def_ind. all: eassumption.
  Qed.

  (* Computing the domain, easier than using the graph *)

  Fixpoint comp_domain {a} (o : orec A B a) :=
    match o with
    | ret v => True
    | rec x κ => domain x ∧ ∀ v, graph x v → comp_domain (κ v)
    | call g x κ => pdomain g x ∧ ∀ v, pgraph g x v → comp_domain (κ v)
    | undefined => False
    end.

  Lemma comp_domain_orec_domain :
    ∀ a (o : orec A B (B a)),
      comp_domain o →
      orec_domain o.
  Proof.
    intros a o h.
    induction o as [w | x κ ih | G g hg x κ ih |] in h |- *.
    - eexists. constructor.
    - simpl in h. destruct h as [[v hx] hκ].
      specialize (hκ v hx). apply ih in hκ. destruct hκ as [w h].
      eexists. econstructor. all: eassumption.
    - simpl in h. destruct h as [[v hx] hκ].
      specialize (hκ v hx). apply ih in hκ. destruct hκ as [w h].
      eexists. econstructor. all: eassumption.
    - contradiction.
  Qed.

  Lemma compute_domain :
    ∀ x,
      comp_domain (f x) →
      domain x.
  Proof.
    intro x. apply comp_domain_orec_domain.
  Qed.

End Lib.

(* We can provide an instance for all partial functions defined as above. *)
#[export, refine] Instance pfun_gen A B (f : ∇ (x : A), B x) : PFun f := {|
  psrc := A ;
  ptgt := B ;
  pgraph := graph f ;
  pfueled := fueled f ;
  pdef := def f ;
  pfunind := funind f
|}.
Proof.
  - intros. eapply orec_graph_functional. all: eassumption.
  - apply fueled_graph_sound.
  - apply def_graph_sound.
  - apply funind_graph.
Defined.

(* Handy notation for autodef *)
Notation "f @ x" := (autodef f x) (at level 10).

(* Small examples *)

Equations div : ∇ (p : nat * nat), nat :=
  div (0, m) := ret 0 ;
  div (n, m) := q ← rec (n - m, m) ;; ret (S q).

Equations test_div : ∇ (p : nat * nat), bool :=
  test_div (n, m) := q ← call div (n, m) ;; ret (q * m =? n).

Definition div_10_5 := div @ (10, 5).
Fail Definition div_10_0 := div @ (10, 0).

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

Axiom SN :
  ∀ Γ t A,
    typing Γ t A →
    Acc cored t.

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

Lemma welltyped_eval :
  ∀ Γ t π A,
    typing Γ (zip t π) A →
    domain eval (t, π).
Proof.
  intros Γ t π A h.
  eapply SN in h. clear Γ A.
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