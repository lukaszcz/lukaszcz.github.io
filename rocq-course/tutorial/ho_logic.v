(* Tutorial 3: Higher-order logic *)

(************************************************************************************)
(* Higher-order logic *)

Definition Reflexive {A} (R : A -> A -> Prop) :=
  forall x, R x x.

Definition Transitive {A} (R : A -> A -> Prop) :=
  forall x y z, R x y -> R y z -> R x z.

Definition Subrelation {A} (R : A -> A -> Prop) (S : A -> A -> Prop) :=
  forall x y, R x y -> S x y.

Definition Closure {A} (Q : (A -> A -> Prop) -> Prop) (R : A -> A -> Prop) :=
  fun x y => forall S, Q S -> Subrelation R S -> S x y.

Definition ReflexiveClosure {A} (R : A -> A -> Prop) := Closure Reflexive R.

Definition TransitiveClosure {A} (R : A -> A -> Prop) := Closure Transitive R.

Lemma lem_refl_closure {A} (R : A -> A -> Prop) : Reflexive (ReflexiveClosure R).
Proof.
  unfold ReflexiveClosure, Closure, Reflexive, Subrelation.
  auto.
Qed.

Lemma lem_trans_closure {A} (R : A -> A -> Prop) : Transitive (TransitiveClosure R).
Proof.
  unfold TransitiveClosure, Closure, Transitive, Subrelation.
  intros x y z H1 H2 S Htrans Hsub.
  generalize (H1 S Htrans Hsub).
  generalize (H2 S Htrans Hsub).
  eauto. (* `eauto` works like `auto` but uses `eapply` instead of `apply` *)
Qed.

(* Higher-order encodings of logical connectives *)

Definition hor (A B : Prop) := forall P : Prop, (A -> P) -> (B -> P) -> P.

Lemma lem_hor_introl {A B : Prop} : A -> hor A B.
Proof.
  unfold hor.
  intros H P H1 H2.
  apply H1.
  exact H.
Qed.

Definition hex {A : Type} (R : A -> Prop) :=
  forall P : Prop, (forall x, R x -> P) -> P.

Lemma lem_hex_intro {A} (R : A -> Prop) : forall x, R x -> hex R.
Proof.
  unfold hex.
  intros x H P H1.
  auto.
  eauto.
Qed.

(* Leibniz equality *)

Definition leq {A : Type} (x y : A) : Prop := forall P : A -> Prop, P x -> P y.

Notation "x == y" := (leq x y) (at level 25).

Lemma lem_leq_refl {A : Type} : forall x : A, x == x.
Proof.
  unfold leq.
  intros x P H.
  assumption.
Qed.

Lemma lem_leq_sym {A : Type} : forall x y : A, x == y -> y == x.
Proof.
  unfold leq.
  intros x y H1 P H2.
  generalize (H1 (fun y => P y -> P x)); intro H3.
  auto.
Qed.

Lemma lem_leq_trans {A : Type} : forall x y z : A, x == y -> y == z -> x == z.
Proof.
  unfold leq.
  intros x y z H1 H2 P H3.
  apply H2.
  apply H1.
  assumption.
Qed.

(************************************************************************************)
(* Axioms *)

Require Import ClassicalChoice.

Check choice.
Print Assumptions choice.

Require Import FunctionalExtensionality.

Check functional_extensionality.
Print Assumptions functional_extensionality.

Definition FunctionalExtensionality :=
  forall (A B : Type) (f g : A -> B), (forall x, f x = g x) -> f = g.
Check FunctionalExtensionality.
Print FunctionalExtensionality.

Lemma lem_funex2 :
  FunctionalExtensionality -> forall (A B C : Type) (f g : A -> B -> C),
    (forall x y, f x y = g x y) -> f = g.
Proof.
  intro Hfunex.
  unfold FunctionalExtensionality in Hfunex.
  intros A B C f g H.
  apply Hfunex.
  intro x.
  Check (f x).
  apply Hfunex.
  apply H.

  Restart.

  auto.
Qed.

Axiom predicate_extensionality :
  forall A (R1 R2 : A -> Prop), (forall x, R1 x <-> R2 x) -> R1 = R2.

Require Import PropExtensionality.

Check propositional_extensionality.
Print Assumptions propositional_extensionality.

(* Classical logic *)
Require Import Classical_Prop.
Print classic.
Print Assumptions classic.
