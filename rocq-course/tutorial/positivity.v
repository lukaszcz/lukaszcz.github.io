(* Tutorial 14: Positivity, large elimination and induction schemes *)

(************************************************************************************)
(* Strict positivity *)

Fail Inductive I : Prop := not_I_I : (I -> False) -> I.

Unset Positivity Checking.

Inductive I : Prop := not_I_I : (I -> False) -> I.

Lemma lem_I : False.
Proof.
  enough (H: I).
  { inversion H.
    auto. }
  constructor.
  intro H.
  inversion H; auto.
Qed.

Set Positivity Checking.

Fail Inductive Lam := lam : (Lam -> Lam) -> Lam.

Unset Positivity Checking.

Inductive Lam := lam : (Lam -> Lam) -> Lam.

Fixpoint loop (l : Lam) : False :=
  match l with lam f => loop (f l) end.

Check (loop (lam (fun x => x))).

Set Positivity Checking.

Fail Inductive NSP : Type := introNPS : ((NSP -> Prop) -> Prop) -> NSP.

Unset Positivity Checking.

Inductive NSP : Type := introNSP : ((NSP -> Prop) -> Prop) -> NSP.

Definition f (x : NSP -> Prop) : NSP := introNSP (fun z => z = x).

Lemma lem_inj : forall x y, f x = f y -> x = y.
Proof.
  intros x y H.
  injection H.
  intro H1.
  assert (Heq: (x = x) = (x = y)).
  { change ((fun z : NSP -> Prop => z = x) x =
            (fun z : NSP -> Prop => z = y) x).
    rewrite H1.
    reflexivity. }
  rewrite <- Heq.
  reflexivity.
Qed.

Definition diag (x : NSP) : Prop := exists s, x = f s /\ ~s x.

Lemma lem_cantor : False.
Proof.
  enough (diag (f diag) <-> ~(diag (f diag))) by tauto.
  split.
  - intros _ H.
    unfold diag in H.
    destruct H as [s [H1 H2]].
    apply lem_inj in H1.
    apply H2.
    rewrite H1 in *.
    change ((fun x => x (f s)) s).
    rewrite <- H1.
    exists s.
    auto.
  - intro H.
    exists diag.
    auto.
Qed.

Set Positivity Checking.

(************************************************************************************)
(* Using large elimination to implement discrimination *)

Lemma lem_discriminate : true <> false.
Proof.
  intro H.
  change ((fun b => match b with true => True | false => False end) false).
  now rewrite <- H.
  (* "now tac" is the same as "tac; easy" *)
Qed.

Lemma lem_discriminate' : true <> false.
Proof.
  intro H.
  discriminate H.
Qed.

(************************************************************************************)
(* Implementing injection *)

Definition pred (n : nat) := match n with 0 => 0 | S n => n end.

Lemma lem_inject : forall n m, S n = S m -> n = m.
Proof.
  intros n m H.
  change (pred (S n) = pred (S m)).
  f_equal.
  assumption.
Qed.

Lemma lem_inject' : forall n m, S n = S m -> n = m.
Proof.
  intros n m H.
  injection H.
  trivial.
Qed.

(************************************************************************************)
(* Generating induction schemes *)

Print nat.
Print nat_ind.

Inductive Even : nat -> Prop :=
| Even_0 : Even 0
| Even_1 : forall n, Even n -> Even (S (S n)).

Print Even_ind.

Scheme Induction for Even Sort Prop.

Print Even_ind_dep.

Inductive vector (A : Type) : nat -> Type :=
| vnil : vector A 0
| vcons : forall {n}, A -> vector A n -> vector A (S n).

Print vector_ind.
Print vector_rect.

Scheme Minimality for vector Sort Set.

Print vector_rec_nodep.
