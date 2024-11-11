(* Open general recursion library *)

From Equations Require Import Equations.
From Coq Require Import Utf8 List Arith Lia.
From PartialFun Require Import Monad.

Import ListNotations.

Set Default Goal Selector "!".
Set Equations Transparent.
Unset Equations With Funext.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Set Primitive Projections.

(* TODOs

  - Maybe some subclasses to be able to only specify the fueled and/or the wf
    versions.
    + Maybe use a hint with high cost for the default instance to ease override.
  - Mutual functions without the need for encoding?
  - Better support for monads by having orec be a monad transformer?
  - Have scopes or even modules for notations.
  - Better class for autodef.
  - Fix extraction, maybe by doing things manually instead of using Equations?
  - Maybe use Hint Extern instead of instanced to better control Monad.

*)

(* Parameters *)

#[local] Notation default_fuel := 1000.
#[local] Notation acc_fuel := default_fuel.

(* A class of true booleans *)

Class IsTrue (b : bool) := mk_is_true {
  is_true : b = true
}.
#[global] Hint Mode IsTrue + : typeclass_instances.

(* #[export] Hint Extern 1 (IsTrue ?b) =>
  constructor ; reflexivity
  : typeclass_instances. *)

#[export] Hint Extern 1000 (IsTrue ?b) =>
  vm_cast_no_check (mk_is_true b eq_refl)
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

(* Class of things one can call *)
Class Callable I := {
  csrc : I → Type ;
  ctgt : ∀ (i : I), csrc i → Type ;
  cgraph : ∀ (i : I) (x : csrc i), ctgt i x → Prop ;
  cdomain i x := ∃ v, cgraph i x v ;
  cgraph_fun : ∀ i x v w, cgraph i x v → cgraph i x w → v = w ;
  cfueled i : nat → ∀ x, Fueled (ctgt i x) ;
  cfueled_graph i : ∀ n x v, cfueled i n x = Success v → cgraph i x v ;
  cdef i : ∀ x, cdomain i x → ctgt i x ;
  cdef_graph i : ∀ x h, cgraph i x (cdef i x h)
}.

#[global] Hint Mode Callable ! : typeclass_instances.

Arguments csrc {I _} i.
Arguments ctgt {I _ i}.
Arguments cgraph {I _} i.
Arguments cdomain {I _} i.
Arguments cgraph_fun {I _ i}.
Arguments cfueled {I _} i.
Arguments cfueled_graph {I _ i}.
Arguments cdef {I _} i.
Arguments cdef_graph {I _ i}.

(** Splitting callable types *)

Class CallTypes I := {
  ct_src : I → Type ;
  ct_tgt : ∀ (i : I), ct_src i → Type
}.

#[global] Hint Mode CallTypes ! : typeclass_instances.

Class CallableProps {I} `(CT : CallTypes I) := {
  cp_graph : ∀ (i : I) (x : ct_src i), ct_tgt i x → Prop ;
  cp_domain i x := ∃ v, cp_graph i x v ;
  cp_graph_fun : ∀ i x v w, cp_graph i x v → cp_graph i x w → v = w ;
  cp_fueled i : nat → ∀ x, Fueled (ct_tgt i x) ;
  cp_fueled_graph i : ∀ n x v, cp_fueled i n x = Success v → cp_graph i x v ;
  cp_def i : ∀ x, cp_domain i x → ct_tgt i x ;
  cp_def_graph i : ∀ x h, cp_graph i x (cp_def i x h)
}.

#[global] Hint Mode CallableProps ! - : typeclass_instances.

Arguments ct_src {I _} i.
Arguments ct_tgt {I _} [i].
Arguments cp_graph {I _ _} i.
Arguments cp_domain {I _ _} i.
Arguments cp_graph_fun {I _ _} [i].
Arguments cp_fueled {I _ _} i.
Arguments cp_fueled_graph {I _ _} [i].
Arguments cp_def {I _ _} i.
Arguments cp_def_graph {I _ _} [i].

Definition CallableSplit I (CT : CallTypes I) `(!CallableProps CT) : Callable I := {|
  csrc := ct_src ;
  ctgt := ct_tgt ;
  cgraph := cp_graph ;
  cgraph_fun := cp_graph_fun ;
  cfueled := cp_fueled ;
  cfueled_graph := cp_fueled_graph ;
  cdef := cp_def ;
  cdef_graph := cp_def_graph
|}.

(* Main inductive type *)

Inductive orec I `{CallTypes I} A B C :=
| _ret (x : C)
| _rec (x : A) (κ : B x → orec I A B C)
| _call (i : I) (x : ct_src i) (κ : ct_tgt x → orec I A B C)
| undefined.

Arguments _ret {I _ A B C}.
Arguments _rec {I _ A B C}.
Arguments _call {I _ A B C} i.
Arguments undefined {I _ A B C}.

Fixpoint _bind {I} `{CallTypes I} {A B C D} (c : orec I A B C) (f : C → orec I A B D) : orec I A B D :=
  match c with
  | _ret x => f x
  | _rec x κ => _rec x (λ y, _bind (κ y) f)
  | _call i x κ => _call i x (λ y, _bind (κ y) f)
  | undefined => undefined
  end.

#[export] Typeclasses Opaque _bind.
Opaque _bind.

Notation "∇ x , [ I ]⇒ B" :=
  (∀ x, orec I _ (λ x, B%type) B)
  (x binder, at level 200).

#[local] Notation "t ∙1" := (proj1_sig t) (at level 20).
#[local] Notation "⟨ x ⟩" := (exist _ x _) (only parsing).
#[local] Notation "⟨ x | h ⟩" := (exist _ x h).

#[local] Notation "t .1" := (projT1 t).
#[local] Notation "t .2" := (projT2 t).
#[local] Notation "( x ; y )" := (existT _ x y).

Section Lib.

  Context {I} `{CT : CallTypes I} `{!CallableProps CT} {A B} (f : ∇ (x : A), [I]⇒ B x).

  Inductive orec_graph {a} : orec I A B (B a) → B a → Prop :=
  | ret_graph :
      ∀ x,
        orec_graph (_ret x) x

  | rec_graph :
      ∀ x κ v w,
        orec_graph (f x) v →
        orec_graph (κ v) w →
        orec_graph (_rec x κ) w

  | call_graph :
      ∀ i x κ v w,
        cp_graph i x v →
        orec_graph (κ v) w →
        orec_graph (_call i x κ) w.

  Definition graph x v :=
    orec_graph (f x) v.

  Inductive orec_graphT {a} : orec I A B (B a) → B a → Type :=
  | ret_graphT :
      ∀ x,
        orec_graphT (_ret x) x

  | rec_graphT :
      ∀ x κ v w,
        orec_graphT (f x) v →
        orec_graphT (κ v) w →
        orec_graphT (_rec x κ) w

  | call_graphT :
      ∀ i x κ v w,
        cp_graph i x v →
        orec_graphT (κ v) w →
        orec_graphT (_call i x κ) w.

  Definition graphT x v :=
    orec_graphT (f x) v.

  Inductive orec_lt {a} : A → orec I A B (B a) → Prop :=
  | top_lt :
      ∀ x κ,
        orec_lt x (_rec x κ)

  | rec_lt :
      ∀ x κ v y,
        graph x v →
        orec_lt y (κ v) →
        orec_lt y (_rec x κ)

  | call_lt :
      ∀ i x κ v y,
        cp_graph i x v →
        orec_lt y (κ v) →
        orec_lt y (_call i x κ).

  Definition partial_lt x y :=
    orec_lt x (f y).

  Definition domain x :=
    ∃ v, graph x v.

  Derive Signature for orec_graph orec_graphT orec_lt.
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
      { apply cp_graph_fun. all: assumption. }
      subst. apply IHhv. assumption.
  Qed.

  Lemma orec_graphT_graph :
    ∀ a o v,
      orec_graphT (a := a) o v →
      orec_graph o v.
  Proof.
    induction 1.
    all: econstructor ; eauto.
  Qed.

  Lemma graphT_graph :
    ∀ x y,
      graphT x y →
      graph x y.
  Proof.
    intros.
    now apply orec_graphT_graph.
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
      { eapply cp_graph_fun. all: eassumption. }
      subst.
      apply IHh. assumption.
  Qed.

  (* Fuel version *)

  Fixpoint orec_fuel_inst {a} n (e : orec I A B (B a)) (r : ∀ x, Fueled (B x)) :=
    match e with
    | _ret v => Success v
    | _rec x κ =>
      match r x with
      | Success v => orec_fuel_inst n (κ v) r
      | NotEnoughFuel => NotEnoughFuel
      | Undefined => Undefined
      end
    | _call g x κ =>
      match cp_fueled g n x with
      | Success v => orec_fuel_inst n (κ v) r
      | NotEnoughFuel => NotEnoughFuel
      | Undefined => Undefined
      end
    | undefined => Undefined
    end.

  (* fumes is there to get depth exponential in n *)
  Fixpoint fueled_gen n (fumes : ∀ y, Fueled (B y)) x : Fueled (B x) :=
    match n with
    | 0 => fumes x
    | S n => orec_fuel_inst n (f x) (fueled_gen n (λ x, fueled_gen n fumes x))
    end.

  Definition fueled n x :=
    fueled_gen n (λ _, NotEnoughFuel) x.

  (* We show the fueled version is sound with respect to the graph *)

  Lemma orec_fuel_inst_graph :
    ∀ a n (o : orec _ _ _ (_ a)) r v,
      orec_fuel_inst n o r = Success v →
      (∀ x w, r x = Success w → graph x w) →
      orec_graph o v.
  Proof.
    intros a n o r v e hr.
    induction o as [w | x κ ih | i x κ ih |] in v, e |- *.
    - simpl in e. noconf e. constructor.
    - simpl in e. destruct r as [w | |] eqn:e'. 2,3: discriminate.
      econstructor.
      + eapply hr. eassumption.
      + apply ih. assumption.
    - simpl in e. destruct cp_fueled as [w | |] eqn:e'. 2,3: discriminate.
      econstructor.
      + eapply cp_fueled_graph. eassumption.
      + apply ih. assumption.
    - discriminate.
  Qed.

  Lemma fueled_gen_graph_sound :
    ∀ n fumes x v,
      (∀ y w, fumes y = Success w → graph y w) →
      fueled_gen n fumes x = Success v →
      graph x v.
  Proof.
    intros n fumes x v hfumes e.
    induction n as [| n ih] in x, v, e, fumes, hfumes |- *.
    - eapply hfumes. assumption.
    - simpl in e.
      eapply orec_fuel_inst_graph.
      + eassumption.
      + intros y w e'.
        eapply ih. 2: eassumption.
        intros z k e2.
        eapply ih. 2: eassumption.
        eapply hfumes.
  Qed.

  Lemma fueled_graph_sound :
    ∀ n x v,
      fueled n x = Success v →
      graph x v.
  Proof.
    intros n x v e.
    eapply fueled_gen_graph_sound. 2: eassumption.
    intros. discriminate.
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
      { eapply cp_graph_fun. all: eassumption. }
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

  Definition oimage {a} (o : orec I A B (B a)) :=
    { v | orec_graph o v }.

  Definition orec_domain {a} (o : orec I A B (B a)) :=
    ∃ v, orec_graph o v.

  Definition oimageT {a} (o : orec I A B (B a)) :=
    { v & orec_graphT o v }.


  (* The calls to depelim in orec_inst create a lot of universes
     That's probably a bug/shortcoming of equation but for now
     we derive explicitly the two inversion principles that are required.
   *)
  Lemma orec_graph_rec_inv {a x κ} {w : B a} (e : orec_graph (_rec x κ) w) :
    ∃ v, orec_graph (f x) v ∧ orec_graph (κ v) w.
  Proof.
    refine (match e in orec_graph m r return
                  match m with
                  | _rec x κ => ∃ v, orec_graph (f x) v ∧ orec_graph (κ v) r
                  | _ => True
                  end
            with
            | rec_graph _ _ _ _ _ _ => _
            | _ => _
            end); try constructor.
    eexists; split; eassumption.
  Qed.

  Lemma orec_graph_call_inv {g a x κ} {w : B a} (e : orec_graph (_call g x κ) w) :
    ∃ v, cp_graph g x v ∧ orec_graph (κ v) w.
  Proof.
    refine (match e in orec_graph m r return
                  match m with
                  | _call g x κ => ∃ v, cp_graph g x v ∧ orec_graph (κ v) r
                  | _ => True
                  end
            with
            | call_graph _ _ _ _ _ _ _ => _
            | _ => _
            end); try constructor.
    eexists; split; eassumption.
  Qed.

  (* orec_inst should no introduce any universe, but we cannot specify it because of Equations *)
  Equations? orec_inst@{+} {a} (e : orec I A B (B a)) (de : orec_domain e)
    (da : domain a)
    (ha : ∀ x, orec_lt x e → partial_lt x a)
    (r : ∀ y, domain y → partial_lt y a → oimage (f y)) : oimage e :=
    orec_inst (_ret v) de da ha r := ⟨ v ⟩ ;
    orec_inst (_rec x κ) de da ha r := ⟨ ((orec_inst (κ ((r x _ _) ∙1)) _ _ _ r)) ∙1 ⟩ ;
    orec_inst (_call g x κ) de da ha r := ⟨ (orec_inst (κ (cp_def g x _)) _ _ _ r) ∙1 ⟩ ;
    orec_inst undefined de da ha r := False_rect _ _.
  Proof.
    - constructor.
    - eapply lt_preserves_domain. 1: eassumption.
      apply ha. constructor.
    - apply ha. constructor.
    - destruct de as [v hg].
      pose proof (orec_graph_rec_inv hg) as (v0&?&?).
      simpl in *.
      destruct r as [w hw]. simpl.
      assert (w = v0).
      { eapply orec_graph_functional.
        all: eassumption.
      }
      subst.
      eexists. eassumption.
    - apply ha. econstructor. 2: eassumption.
      red. destruct r. assumption.
    - simpl. destruct orec_inst. simpl.
      econstructor. 2: eassumption.
      destruct r. assumption.
    - destruct de as [v hg].
      pose proof (orec_graph_call_inv hg) as (?&?&?).
      eexists. eassumption.
    - lazymatch goal with
      | |- context [ cp_def g x ?prf ] => set (hh := prf) ; clearbody hh
      end.
      destruct de as [v hg].
      pose proof (orec_graph_call_inv hg) as (?&?&?).
      simpl in *.
      pose proof (cp_def_graph x hh) as hg'.
      move hg' at top. eapply cp_graph_fun in hg'. 2: eassumption.
      subst. eexists. eassumption.
    - intros; lazymatch goal with
      | h : context [ cp_def g x ?prf ] |- _ =>
          set (hh := prf) in h ; clearbody hh
      end.
      apply ha. econstructor. 2: eassumption.
      apply cp_def_graph.
    - destruct orec_inst. simpl.
      lazymatch goal with
      | h : context [ cp_def g x ?prf ] |- _ =>
          set (hh := prf) in h ; clearbody hh
      end.
      econstructor. 2: eassumption.
      apply cp_def_graph.
    - destruct de as [v hg]. inversion hg.
  Defined.

  #[derive(equations=no),tactic=idtac] Equations? def_p (x : A) (h : domain x) : oimage (f x)
    by wf x partial_lt :=
    def_p x h := orec_inst (a := x) (f x) h h (λ x Hx, Hx) (λ y hy hr, def_p y hy).
  Proof. exact hr. Defined.


  (* Same as for orec_inst, there should be no universe parameter here *)
  Equations? orec_instT@{+} {a} (e : orec I A B (B a)) (de : orec_domain e)
    (da : domain a)
    (ha : ∀ x, orec_lt x e → partial_lt x a)
    (r : ∀ y, domain y → partial_lt y a → oimageT (f y)) : oimageT e :=
    orec_instT (_ret v) de da ha r := (v ; _) ;
    orec_instT (_rec x κ) de da ha r := (((orec_instT (κ (projT1 (r x _ _))) _ _ _ r)).1 ; _) ;
    orec_instT (_call g x κ) de da ha r := ((orec_instT (κ (cp_def g x _)) _ _ _ r).1 ; _) ;
    orec_instT undefined de da ha r := False_rect _ _.
  Proof.
    - constructor.
    - eapply lt_preserves_domain. 1: eassumption.
      apply ha. constructor.
    - apply ha. constructor.
    - destruct de as [v hg].
      pose proof (orec_graph_rec_inv hg) as (v0&?&?).
      simpl in *.
      destruct r as [w hw]. simpl.
      assert (w = v0).
      { eapply orec_graph_functional. 1: eapply orec_graphT_graph.
        all: eassumption.
      }
      subst.
      eexists. eassumption.
    - apply ha. econstructor. 2: eassumption.
      red. destruct r. apply orec_graphT_graph. assumption.
    - simpl. destruct orec_instT. simpl.
      econstructor. 2: eassumption.
      destruct r. assumption.
    - destruct de as [v hg].
      pose proof (orec_graph_call_inv hg) as (?&?&?).
      eexists. eassumption.
    - lazymatch goal with
      | |- context [ cp_def g x ?prf ] => set (hh := prf) ; clearbody hh
      end.
      destruct de as [v hg].
      pose proof (orec_graph_call_inv hg) as (?&?&?).
      simpl in *.
      pose proof (cp_def_graph x hh) as hg'.
      move hg' at top. eapply cp_graph_fun in hg'. 2: eassumption.
      subst. eexists. eassumption.
    - lazymatch goal with
      | h : context [ cp_def g x ?prf ] |- _ =>
          set (hh := prf) in h ; clearbody hh
      end.
      apply ha. econstructor. 2: eassumption.
      apply cp_def_graph.
    - destruct orec_instT. simpl.
      lazymatch goal with
      | h : context [ cp_def g x ?prf ] |- _ =>
          set (hh := prf) in h ; clearbody hh
      end.
      econstructor. 2: eassumption.
      apply cp_def_graph.
    - destruct de as [v hg]. inversion hg.
  Defined.

  #[derive(equations=no)] Equations def_pT (x : A) (h : domain x) : oimageT (f x)
    by wf x partial_lt :=
    def_pT x h := orec_instT (a := x) (f x) h h (λ x Hx, Hx) (λ y hy hr, def_pT y hy).

  Definition def x h :=
    (def_p x h) ∙1.

  Definition defT x h :=
    (def_pT x h).1.

  Lemma def_graph_sound :
    ∀ x h,
      graph x (def x h).
  Proof.
    intros x h.
    unfold def. destruct def_p. assumption.
  Qed.

  Lemma defT_graph_sound :
    ∀ x h,
      graph x (defT x h).
  Proof.
    intros x h.
    unfold defT. destruct def_pT. apply orec_graphT_graph. assumption.
  Qed.


  Lemma graph_graphT :
    ∀ x v,
      graph x v →
      graphT x v.
  Proof.
    intros x v h.
    unshelve epose proof (def_pT x _) as [v' hT].
    1: eexists ; eassumption.
    assert (v = v').
    { eapply orec_graph_functional.
      - eassumption.
      - apply graphT_graph. assumption.
    }
    subst. assumption.
  Qed.

  (* Well-founded version with automatic domain inferrence *)

  Definition autodef (x : A) `{e : IsTrue (succeeds default_fuel x)} :=
    def x (succeeds_domain default_fuel x e.(is_true)).

  (* Proving properties about such functions *)

  Notation precond := (A → Prop).
  Notation postcond := (∀ x, B x → Prop).

  Fixpoint orec_ind_step a (pre : precond) (post : postcond) (o : orec I A B _) :=
    match o with
    | _ret v => post a v
    | _rec x κ => pre x ∧ ∀ v, post x v → orec_ind_step a pre post (κ v)
    | _call g x κ => ∀ v, cp_graph g x v → orec_ind_step a pre post (κ v)
    | undefined => True
    end.

  Definition funind (pre : precond) post :=
    ∀ x, pre x → orec_ind_step x pre post (f x).

  (* Functional induction on the graph *)

  Lemma orec_graph_inst_ind_step :
    ∀ pre post x o v,
      funind pre post →
      orec_ind_step x pre post o →
      pre x →
      orec_graph o v →
      post x v.
  Proof.
    intros pre post x o v hind h hpre hgraph.
    induction hgraph as [w | x y κ v w hy ihy hκ ihκ | x i y κ v w hy hκ ihκ].
    all: cbn in *.
    - assumption.
    - destruct h as [hpy hv].
      apply ihκ. 2: assumption.
      apply hv. apply ihy. 2: assumption.
      apply hind. assumption.
    - apply ihκ. 2: assumption.
      apply h. assumption.
  Qed.

  Lemma funind_graph :
    ∀ pre post x v,
      funind pre post →
      pre x →
      graph x v →
      post x v.
  Proof.
    intros pre post x v h hpre hgraph.
    eapply orec_graph_inst_ind_step.
    all: eauto.
  Qed.

  (* The fueled case *)

  Lemma funind_fuel :
    ∀ pre post x n v,
      funind pre post →
      pre x →
      fueled n x = Success v →
      post x v.
  Proof.
    intros pre post x n v h hpre ?%fueled_graph_sound.
    eapply funind_graph. all: eauto.
  Qed.

  (* The wf case *)

  Lemma def_ind :
    ∀ pre post x h,
      funind pre post →
      pre x →
      post x (def x h).
  Proof.
    intros pre post x h ho hpre.
    pose proof def_graph_sound.
    eapply funind_graph. all: eauto.
  Qed.

  (* Same as funind but for Type *)

  Notation precondT := (A → Type).
  Notation postcondT := (∀ x, B x → Type).

  Fixpoint orec_ind_stepT a (pre : precondT) (post : postcondT) (o : orec I _ _ _) :=
    match o with
    | _ret v => post a v
    | _rec x κ => pre x * ∀ v, graph x v → post x v → orec_ind_stepT a pre post (κ v)
    | _call g x κ => ∀ v, cp_graph g x v → orec_ind_stepT a pre post (κ v)
    | undefined => True
    end%type.

  Definition funrect pre post :=
    ∀ x, pre x → orec_ind_stepT x pre post (f x).

  Lemma orec_graph_inst_rect_step :
    ∀ pre post x y v,
      funrect pre post →
      orec_ind_stepT x pre post y →
      pre x →
      orec_graphT y v →
      post x v.
  Proof.
    intros pre post x y v hind h hpre hgraph.
    induction hgraph as [w | x y κ v w hy ihy hκ ihκ | x i y κ v w hy hκ ihκ].
    all: cbn in *.
    - assumption.
    - destruct h as [hpy hv].
      apply ihκ. 2: assumption.
      apply hv. 1: now eapply graphT_graph.
      apply ihy. 2: assumption.
      apply hind. assumption.
    - apply ihκ. 2: assumption.
      apply h. assumption.
  Qed.

  Lemma funrect_graph :
    ∀ pre post x v,
      funrect pre post →
      pre x →
      graph x v →
      post x v.
  Proof.
    intros pre post x v h hpre hgraph%graph_graphT.
    eapply orec_graph_inst_rect_step.
    all: eauto.
  Qed.

  (* The fueled case *)

  Lemma funrect_fuel :
    ∀ pre post x n v,
      funrect pre post →
      pre x →
      fueled n x = Success v →
      post x v.
  Proof.
    intros pre post x n v h hpre ?%fueled_graph_sound.
    eapply funrect_graph. all: eauto.
  Qed.

  (* The wf case *)

  Lemma def_rect :
    ∀ pre post x h,
      funrect pre post →
      pre x →
      post x (def x h).
  Proof.
    intros pre post x h ho hpre.
    pose proof def_graph_sound.
    eapply funrect_graph. all: eauto.
  Qed.

  (* Computing the domain, easier than using the graph *)

  Fixpoint comp_domain {a} (o : orec I A B a) :=
    match o with
    | _ret v => True
    | _rec x κ => domain x ∧ ∀ v, graph x v → comp_domain (κ v)
    | _call g x κ => cp_domain g x ∧ ∀ v, cp_graph g x v → comp_domain (κ v)
    | undefined => False
    end.

  Lemma comp_domain_orec_domain :
    ∀ a (o : orec I A B (B a)),
      comp_domain o →
      orec_domain o.
  Proof.
    intros a o h.
    induction o as [w | x κ ih | i x κ ih |] in h |- *.
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

(** To be able to compose partial functions, we use a special instance for
    the Callable class. It comes at the cost of having to have types directly
    in the data structure which means making the universe level grow. In most
    cases it should not matter however.
*)

Class PFun {F} (f : F) := {
  psrc : Type ;
  ptgt : psrc → Type ;
  pgraph : ∀ x, ptgt x → Prop ;
  pdomain x := ∃ v, pgraph x v ;
  pgraph_fun : ∀ x v w, pgraph x v → pgraph x w → v = w ;
  pfueled : nat → ∀ x, Fueled (ptgt x) ;
  pfueled_graph : ∀ n x v, pfueled n x = Success v → pgraph x v ;
  pdef : ∀ x, pdomain x → ptgt x ;
  pdef_graph : ∀ x h, pgraph x (pdef x h)
}.

#[local] Hint Mode PFun ! ! : typeclass_instances.

Arguments psrc {F} f {_}.
Arguments ptgt {F} f {_}.
Arguments pgraph {F} f {_}.
Arguments pdomain {F} f {_}.
Arguments pgraph_fun {F} f {_}.
Arguments pfueled {F} f {_}.
Arguments pfueled_graph {F} f {_}.
Arguments pdef {F} f {_}.
Arguments pdef_graph {F} f {_}.

(* Packed PFun *)
Record PPFun := {
  pfun_ty : Type ;
  pfun : pfun_ty ;
  ispfun : PFun pfun
}.

Arguments pfun_ty _ : clear implicits.
Arguments pfun _ : clear implicits.

#[local] Existing Instance ispfun.

Definition PPFun_mk {F} (f : F) `{PFun _ f} := {|
  pfun_ty := F ;
  pfun := f ;
  ispfun := _
|}.

#[export] Instance CallTypesPPFun : CallTypes PPFun := {|
  ct_src i := psrc (pfun i) ;
  ct_tgt i := ptgt (pfun i) ;
|}.

#[export, refine] Instance CallablePropsPPFun : CallableProps CallTypesPPFun :=
  {|
  cp_graph i := pgraph (pfun i) ;
  cp_fueled i := pfueled (pfun i) ;
  cp_def i := pdef (pfun i)
|}.
Proof.
  - intros. eapply pgraph_fun. all: eassumption.
  - intro. apply pfueled_graph.
  - intro. apply pdef_graph.
Defined.

#[export] Instance CallablePPFun : Callable PPFun :=
  CallableSplit _ _ CallablePropsPPFun.

Notation "∇ x , B" :=
  (∇ x, [PPFun]⇒ B)
  (x binder, at level 200).

Notation "A ⇀ B" :=
  (∇ (_ : A), B)
  (at level 199).

(* We can provide an instance for all partial functions defined as above. *)
#[local, refine] Instance pfun_gen A B {I} `{CT:CallTypes I, !CallableProps CT} (f : ∇ (x : A), [I]⇒ B x) : PFun f := {|
  psrc := A ;
  ptgt := B ;
  pgraph := graph f ;
  pfueled := fueled f ;
  pdef := def f
|}.
Proof.
  - intros. eapply orec_graph_functional. all: eassumption.
  - apply fueled_graph_sound.
  - apply def_graph_sound.
Defined.

(* Handy notation for autodef *)
Notation "f @ x" := (autodef f x) (at level 10).

(* orec is a monad *)
#[export] Instance MonadOrec {I} `{CallTypes I} {A B} : Monad (orec I A B) | 5 := {|
  ret C x := _ret x ;
  bind C D c f := _bind c f
|}.

(* It has some actions *)
Definition rec {I} `{CallTypes I} {A B} (x : A) : orec I A B (B x) :=
  _rec x (λ y, ret y).

Definition ext_call {I} `{CallTypes I} {A B} f (x : ct_src f) : orec I A B (ct_tgt x) :=
  _call f x (λ y, ret y).

Definition call {A B} {F} f `{PFun F f} (x : psrc f) : orec PPFun A B (ptgt f x) :=
  ext_call (PPFun_mk f) x.

#[export] Typeclasses Opaque rec.
#[export] Typeclasses Opaque ext_call.
#[export] Typeclasses Opaque call.

(* Combining orec with other effects (rather constrained) *)

Definition combined_orec (M : Type → Type) I `{CallTypes I} A B C :=
  orec I A B (M C).

#[export] Typeclasses Opaque combined_orec.

Class OrecEffect M := { combined_monad : forall I `{_ : CallTypes I} A B, Monad (combined_orec M I A B) }.
#[global] Hint Mode OrecEffect ! : typeclass_instances.


(* Typeclasses Opaque combined. *)

Notation "∇ x , [ I ]⇒[ M ] B" :=
  (∀ x, combined_orec M I _ (λ x, M%function B%type) B)
  (x binder, at level 200).

Notation "∇ x , [ M ] B" := (∇ x, [PPFun]⇒[ M ] B)
  (* (∀ x, combined_orec M PPFun _ (λ x, M%function B%type) B) *)
  (x binder, at level 200).



(* Useful tactics *)

Tactic Notation "funind" constr(p) "in" hyp(h) :=
  lazymatch type of h with
  | graph ?f ?x ?v =>
    lazymatch type of p with
    | context [ funind _ _ _ ] =>
      eapply funind_graph with (1 := p) in h ; [| try (exact I)]
    | context [ funrect _ _ _ ] =>
      eapply funrect_graph with (1 := p) in h ; [| try (exact I)]
    | _ => fail "Argument should be of type funind or funrect"
    end
  | _ => fail "Hypothesis should be about graph"
  end.

Tactic Notation "funind" constr(p) "in" hyp(h) "as" ident(na) :=
  lazymatch type of h with
  | graph ?f ?x ?v =>
    lazymatch type of p with
    | context [ funind _ _ _ ] =>
      eapply funind_graph with (1 := p) in h as na ; [| try (exact I)]
    | context [ funrect _ _ _ ] =>
      eapply funrect_graph with (1 := p) in h as na ; [| try (exact I)]
    | _ => fail "Argument should be of type funind or funrect"
    end
  | _ => fail "Hypothesis should be about graph"
  end.



(* Instances that should not be exported arbitrarily *)
Module PFUnInstances.

  #[export] Existing Instance ispfun.

  #[export] Existing Instance pfun_gen.

  (* PFun instance for effectful partial functions *)
  #[export] Instance pfun_eff_gen
    A B E `{Monad (combined_orec E PPFun A B)} (f : ∇ (x : A), [ E ] B x) : PFun f :=
    pfun_gen A (λ x, E (B x)) f.

End PFUnInstances.
