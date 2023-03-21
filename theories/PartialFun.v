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
  - Mutual functions without the need for encoding?

*)

(* Parameters *)

#[local] Notation default_fuel := 1000.
#[local] Notation acc_fuel := default_fuel.

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
    eapply Acc_intro_generator with (1 := acc_fuel).
    intros [x h].
    pose proof (partial_lt_acc x h) as hacc.
    induction hacc as [x hacc ih] in h |- *.
    constructor. intros [y h'] hlt.
    apply ih. assumption.
  Defined.

  (* We need this for the proofs to go through *)
  Opaque wf_partial.

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

  Definition autodef (x : A) `{e : IsTrue (succeeds default_fuel x)} :=
    def x (succeeds_domain default_fuel x e.(is_true)).

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

  (* Now we can let it compute *)
  Transparent wf_partial.

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