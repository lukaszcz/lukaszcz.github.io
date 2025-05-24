(* Tutorial 2: Basic logic and proofs *)

(************************************************************************************)
(* Prop vs bool *)

Print bool.
(* "Print Prop" gives a syntax error. Prop is a universe (of
   propositions), not an inductive type. *)
Check Prop.

Print false.
Print False.

Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

(* Definition negp (p : Prop) : Prop :=
  match p with
  | True => False
  end. *)

Print orb.
Print or.

Print andb.
Print and.

(* No unbounded quantification in bool! *)

(************************************************************************************)
(* Propositional logic *)

(* Function types as implication *)

Section FunctionTypes.

Variables A B C : Prop.

Definition id (x : A) : A := x.

Check id.

Definition id' : A -> A :=
  fun x => x.

Definition cK : A -> B -> A :=
  fun x y => x.

Definition cS : (A -> B -> C) -> (A -> B) -> A -> C :=
  fun x y z => x z (y z).

End FunctionTypes.

Check id.

(* Conjunction *)

Locate "/\".
Print and.

Definition conj_eliml {A B} : A /\ B -> A :=
  fun x => match x with conj a _ => a end.

Definition conj_elimr {A B} : A /\ B -> B :=
  fun x => match x with conj _ b => b end.

(* Equivalence *)

Locate "<->".
Print iff.
(* "iff" is abbreviated with "<->" *)

(* "(A /\ B) <-> (B /\ A)" is defined as
  "((A /\ B) -> (B /\ A)) /\ ((B /\ A) -> (A /\ B))" *)
Definition and_comm {A B} : (A /\ B) <-> (B /\ A) :=
  conj (fun x : A /\ B => conj (conj_elimr x) (conj_eliml x))
       (fun x : B /\ A => conj (conj_elimr x) (conj_eliml x)).

(* Disjunction *)

Locate "\/".
Print or.

Definition or_elim {A B C : Prop} : (A -> C) -> (B -> C) -> A \/ B -> C :=
  fun f g x => match x with or_introl a => f a | or_intror b => g b end.

Definition or_comm {A B} : (A \/ B) <-> (B \/ A) :=
  conj (fun x : A \/ B => or_elim (fun x : A => or_intror x) (fun x : B => or_introl x) x)
       (fun x : B \/ A => or_elim (fun x : B => or_intror x) (fun x : A => or_introl x) x).

(* Truth *)

Print True.

(* Falsity *)

Print False.

Definition false_elim {A} : False -> A :=
  fun x : False => match x with end.

Definition lem_false {A B} : (B -> False) -> B -> A :=
  fun H1 H2 => false_elim (H1 H2).

(* Negation *)

Locate "~".
Print not.
(* "not" is abbreviated with "~" *)

(* "~~A" is defined as "(A -> False) -> False" *)
Definition a_not_not {A : Prop} : A -> ~~A :=
  fun x : A => fun y : A -> False => y x.

(************************************************************************************)
(* Predicate logic *)

(* Dependent function types as universal quantification *)

Section DependentFunctionTypes.

Variable A : Set.
Variables P Q : A -> Prop.

Definition qlem1 : forall x : A, P x -> P x :=
  fun x : A => fun p : P x => p.

Definition qlem2 : forall x : A, P x -> Q x -> P x /\ Q x :=
  fun x : A => fun p : P x => fun q : Q x => conj p q.

Definition qlem2' (x : A) (p : P x) (q : Q x) := conj p q.
Check qlem2'.

End DependentFunctionTypes.

(* Existential quantification *)

Locate "exists".
Print ex.

Definition ex_elim {A : Set} {P : A -> Prop} {Q : Prop} :
  (forall x : A, P x -> Q) -> (exists x, P x) -> Q :=
  fun (f : forall x : A, P x -> Q) (e : exists x, P x) =>
    match e with ex_intro _ x p => f x p end.

Definition elem1 {A : Set} {P : A -> A -> Prop} :
  (exists x, forall y, P x y) -> forall y, exists x, P x y :=
  fun e y => ex_elim (fun (x : A) (p : forall y, P x y) =>
                        ex_intro (fun x => P x y) x (p y)) e.


(************************************************************************************)
(* Tactics *)

(* Function types as implication *)

Section FunctionTypesTactics.

Variables A B C : Prop.

(* Goal: the statement you're trying to prove -- below the line *)
(* Context: your assumptions (hypotheses) -- above the line *)

Definition id'' : A -> A.
  Show Proof.
  intro H.
  Show Proof.
  exact H.
  Show Proof.
Qed.

Lemma id''' : A -> A.
Proof.
  intro H.
  exact H.
Qed.

Lemma cK' : A -> B -> A.
Proof.
  intros H1 H2.
  exact H1.
Qed.

Print cK'.

Lemma cS' : (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
  intros H1 H2 H3.
  Show Proof.
  apply H1.
  Show Proof.
  - exact H3.
  - Show Proof.
    apply H2.
    Show Proof.
    exact H3.
Qed.

End FunctionTypesTactics.

(* Conjunction *)

Lemma conj_eliml' {A B} : A /\ B -> A.
Proof.
  intro H.
  Print and.
  (* "destruct" performs reasoning by cases *)
  (* the "as" patterns provide argument names for each constructor *)
  (* a value of type "A /\ B" must have the form "conj H1 H2" *)
  destruct H as [H1 H2].
  Show Proof.
  exact H1.
Qed.

Lemma conj_elimr' {A B} : A /\ B -> B.
Proof.
  intro H.
  destruct H; assumption.
  (* "tac1; tac2" means "run tac1, and then run tac2 on each resulting subgoal" *)
  (* "assumption" is like "exact H" except that it finds the "H" automatically *)
Qed.

(* Equivalence *)

Lemma and_comm' {A B} : (A /\ B) <-> (B /\ A).
Proof.
  split.
  Show Proof.
  - (* intro H; destruct H as [H1 H2]. *)
    intros [H1 H2].
    Show Proof.
    split.
    Show Proof.
    + exact H2.
    + exact H1.
  - intros [H1 H2].
    split; assumption.
Qed.

Lemma and_comm'' {A B} : (A /\ B) <-> (B /\ A).
Proof.
  split; intro H; destruct H; split; assumption.
Qed.

(* Disjunction *)

Lemma or_elim' {A B C : Prop} : (A -> C) -> (B -> C) -> A \/ B -> C.
Proof.
  intros H1 H2 H3.
  Print or.
  (* a value of type "A \/ B" must have
     the form "or_introl H" or "or_intror H" *)
  destruct H3 as [ H | H ].
  Show Proof.
  - apply H1.
    exact H.
  - apply H2.
    exact H.
Qed.

Lemma or_elim'' {A B C : Prop} : (A -> C) -> (B -> C) -> A \/ B -> C.
Proof.
  intros ? ? H3; destruct H3; auto.
  (* "auto" searches for a proof using "intro", "apply" and "exact" *)
Qed.

Lemma or_comm' {A B} : (A \/ B) <-> (B \/ A).
Proof.
  split.
  - intros [H|H].
    Show Proof.
    + right.
      Show Proof.
      exact H.
    + left.
      Show Proof.
      exact H.
  - intro H; destruct H; auto.
    (* "auto" also knows how to create proofs of
      disjunctions (but not how to destruct them) *)
Qed.

(* Falsity *)

Lemma false_elim' {A : Prop} : False -> A.
Proof.
  intro H.
  destruct H.
  Show Proof.
Qed.

Lemma lem_false' {A B} : (B -> False) -> B -> A.
Proof.
  intros H1 H2.
(*  apply false_elim.
  Undo. (* undo last step *) *)
  exfalso. (* standard Coq tactic for falsity elimination *)
  auto.
Qed.

Print lem_false'.
Check False_rect.

(* Negation *)

Lemma a_not_not' {A : Prop} : A -> ~~A.
Proof.
  intro H.
  intro H1.
  apply H1.
  exact H.

  Restart. (* restart proof *)

  auto.
Qed.

(* Dependent function types as universal quantification *)

Section DependentFunctionTypesTactics.

Variable A : Set.
Variables P Q : A -> Prop.

Lemma qlem1' : forall x : A, P x -> P x.
Proof.
  intros x H.
  exact H.
Qed.

Lemma qlem2'' : forall x : A, P x -> Q x -> P x /\ Q x.
Proof.
  auto.
  (* "auto" also knows how to create conjunction proofs *)
Qed.

End DependentFunctionTypesTactics.

(* Existential quantification *)

Print ex.

Lemma ex_elim' {A : Set} {P : A -> Prop} {Q : Prop} :
  (forall x : A, P x -> Q) -> (exists x, P x) -> Q.
Proof.
  intros H1 H2.
  Print ex.
  (* a value of type "exists x, P x" must
    have the form "ex_intro _ x H" *)
  destruct H2 as [x H].
  Show Proof.
  (* apply H1. *)
  Fail apply H1.
  eapply H1.
  Show Proof.
  exact H.
Qed.

Lemma elem1' {A : Set} {P : A -> A -> Prop} :
  (exists x, forall y, P x y) -> forall y, exists x, P x y.
Proof.
  intros H y.
  destruct H as [x H].
  Show Proof.
  exists x.
  Show Proof.
  apply H.
Qed.
