(* Tutorial 22: Hoare logic *)

From Hammer Require Import Tactics Reflect.
Require Import String.
Require Import Arith.
Require Import Lia.

(* A simple imperative language *)

Inductive aexpr :=
| Aval : nat -> aexpr
| Avar : string -> aexpr
| Aplus : aexpr -> aexpr -> aexpr
| Aminus : aexpr -> aexpr -> aexpr.

Coercion Aval : nat >-> aexpr.
Notation "A +! B" := (Aplus A B) (at level 50).
Notation "A -! B" := (Aminus A B) (at level 50).
Notation "^ A" := (Avar A) (at level 40).

Definition state := string -> nat.

Fixpoint aval (s : state) (e : aexpr) :=
  match e with
  | Aval n => n
  | Avar x => s x
  | Aplus x y => aval s x + aval s y
  | Aminus x y => aval s x - aval s y
  end.

Lemma lem_aval_plus :
  forall s e1 e2, aval s (e1 +! e2) = aval s e1 + aval s e2.
Proof.
  sauto.
Qed.

Lemma lem_aval_minus :
  forall s e1 e2, aval s (e1 -! e2) = aval s e1 - aval s e2.
Proof.
  sauto.
Qed.

Hint Rewrite lem_aval_plus lem_aval_minus : prog_simpl.

Inductive bexpr :=
| Bval : bool -> bexpr
| Bnot : bexpr -> bexpr
| Band : bexpr -> bexpr -> bexpr
| Bless : aexpr -> aexpr -> bexpr.

Coercion Bval : bool >-> bexpr.
Notation "~! A" := (Bnot A) (at level 55).
Notation "A &! B" := (Band A B) (at level 55).
Notation "A <! B" := (Bless A B) (at level 54).

Check (3 <! ^"x" +! 2 &! ~! 6 <! 7).

Fixpoint bval (s : state) (e : bexpr) :=
  match e with
  | Bval b => b
  | Bnot e1 => negb (bval s e1)
  | Band e1 e2 => bval s e1 && bval s e2
  | Bless a1 a2 => aval s a1 <? aval s a2
  end.

Inductive cmd :=
| Nop : cmd
| Assign : string -> aexpr -> cmd
| Seq : cmd -> cmd -> cmd
| If : bexpr -> cmd -> cmd -> cmd
| While : bexpr -> cmd -> cmd.

Notation "'nop" := Nop.
Notation "A <- B" := (Assign A B) (at level 60).
Notation "A ;; B" := (Seq A B) (at level 70).
Notation "'if A 'then B 'else C" := (If A B C) (at level 65).
Notation "'while A 'do B" := (While A B) (at level 65).

Check ('if 4 <! ^"x" 'then 'nop ;; "x" <- 5 'else 'nop).

Definition update (s : state) x v y :=
  if string_dec x y then v else s y.

Definition state_subst (s : state) (x : string) (a : aexpr) : state :=
  (update s x (aval s a)).

Notation "s [ x := a ]" := (state_subst s x a) (at level 5).

Lemma lem_subst_eq : forall s x a, s[x := a] x = aval s a.
Proof.
  sauto unfold: state_subst, update.
Qed.

Lemma lem_subst_neq : forall s x y a, x <> y -> s[x := a] y = s y.
Proof.
  sauto unfold!: state_subst, update.
Qed.

Hint Rewrite lem_subst_eq : prog_simpl.

Ltac prog_simpl :=
  simpl; autorewrite with prog_simpl; simpl;
  repeat rewrite lem_subst_neq by strivial; simpl.

(* Big-step operational semantics *)

Inductive BigStep : cmd -> state -> state -> Prop :=
| NopSem : forall s, BigStep 'nop s s
| AssignSem : forall s x a, BigStep (x <- a) s s[x := a]
| SeqSem : forall c1 c2 s1 s2 s3, BigStep c1 s1 s2 -> BigStep c2 s2 s3 ->
                                  BigStep (c1 ;; c2) s1 s3
| IfTrue : forall b c1 c2 s s', bval s b -> BigStep c1 s s' ->
                                BigStep ('if b 'then c1 'else c2) s s'
| IfFalse : forall b c1 c2 s s', negb (bval s b) -> BigStep c2 s s' ->
                                 BigStep ('if b 'then c1 'else c2) s s'
| WhileFalse : forall b c s, negb (bval s b) ->
                             BigStep ('while b 'do c) s s
| WhileTrue : forall b c s1 s2 s3,
    bval s1 b -> BigStep c s1 s2 -> BigStep ('while b 'do c) s2 s3 ->
    BigStep ('while b 'do c) s1 s3.

Notation "A >> B ==> C" :=
  (BigStep A B C) (at level 80, no associativity).

Print BigStep.

(* Hoare triples *)

Definition assn := state -> Prop.

Definition hoare_valid (P : assn) (c : cmd) (Q : assn): Prop :=
  forall s s', c >> s ==> s' -> P s -> Q s'.

Notation "|= {{ P }} c {{ Q }}" := (hoare_valid P c Q).

(* Hoare logic *)

Definition entails (P Q : assn) : Prop := forall s, P s -> Q s.

Inductive hoare : assn -> cmd -> assn -> Prop :=
| Hoare_Nop : forall P, hoare P 'nop P
| Hoare_Assign : forall P a x,
    hoare (fun s => P s[x := a]) (x <- a) P
| Hoare_Seq : forall P Q R c1 c2,
    hoare P c1 Q -> hoare Q c2 R -> hoare P (c1 ;; c2) R
| Hoare_If : forall P Q b c1 c2,
    hoare (fun s => P s /\ bval s b) c1 Q ->
    hoare (fun s => P s /\ negb (bval s b)) c2 Q ->
    hoare P ('if b 'then c1 'else c2) Q
| Hoare_While : forall P b c,
    hoare (fun s => P s /\ bval s b) c P ->
    hoare P ('while b 'do c) (fun s => P s /\ negb (bval s b))
| Hoare_conseq: forall P P' Q Q' c,
    hoare P c Q -> entails P' P -> entails Q Q' -> hoare P' c Q'.

Notation "|- {{ s | P }} c {{ s' | Q }}" :=
  (hoare (fun s => P) c (fun s' => Q)).
Notation "|- {{ s | P }} c {{ Q }}" := (hoare (fun s => P) c Q).
Notation "|- {{ P }} c {{ s' | Q }}" := (hoare P c (fun s' => Q)).
Notation "|- {{ P }} c {{ Q }}" := (hoare P c Q).

Print hoare.

Lemma hoare_strengthen_pre : forall P P' Q c,
    entails P' P -> |- {{P}} c {{Q}} -> |- {{P'}} c {{Q}}.
Proof.
  sauto unfold: entails.
Qed.

Lemma hoare_weaken_post : forall P Q Q' c,
    entails Q Q' -> |- {{P}} c {{Q}} -> |- {{P}} c {{Q'}}.
Proof.
  sauto unfold: entails.
Qed.

Lemma hoare_assign : forall (P Q : assn) x a,
    (forall s, P s -> Q s[x := a]) -> |- {{P}} x <- a {{Q}}.
Proof.
  intros P Q a x.
  (* best use: (hoare_strengthen_pre (fun s => Q s[a := x])). *)
  hecrush use: (hoare_strengthen_pre (fun s => Q s[a := x])).
Qed.

Lemma hoare_while : forall b (P Q: assn) c,
    |- {{s | P s /\ bval s b}} c {{P}} ->
       (forall s, P s /\ negb (bval s b) -> Q s) ->
    |- {{P}} ('while b 'do c) {{Q}}.
Proof.
  intros b P Q c.
  sauto use:
    (hoare_weaken_post P
                       (fun s : state => P s /\ negb (bval s b))
                       Q ('while b 'do c)).
Qed.

Definition sum_prog :=
  'while 0 <! ^"n" 'do ("x" <- ^"x" +! ^"n" ;; "n" <- ^"n" -! 1).

Open Scope string_scope.

Example ex_sum n :
|- {{s | s "x" = 0 /\ s "n" = n}} sum_prog {{s | 2 * s "x" = n * (n + 1)}}.
Proof.
  unfold sum_prog.
  apply hoare_strengthen_pre with
      (P := fun s => 2 * s "x" + s "n" * (s "n" + 1) = n * (n + 1));
    [ sauto unfold: entails | ].
  apply hoare_while.
  - apply Hoare_Seq with
        (Q := fun s => 2 * s "x" + s "n" * s "n" - s "n" = n * (n + 1) /\
                       s "n" > 0).
    + apply hoare_assign.
      intros.
      prog_simpl.
      sauto brefl: on.
    + apply hoare_assign.
      intros.
      prog_simpl.
      assert (s "n" - 1 + 1 = s "n") by lia.
      destruct H as [H1 H2].
      assert ((s "n" - 1) * s "n" = s "n" * s "n" - s "n") by sauto l: on drew: off.
      lia.
  - intros.
    assert (s "n" = 0) by sauto brefl: on.
    sauto.
Qed.

(* Correctness (soundness) of Hoare logic *)

Theorem thm_hoare_correct : forall P Q c,
    |- {{P}} c {{Q}} -> |= {{P}} c {{Q}}.
Proof.
  unfold hoare_valid.
  induction 1.
  - sauto.
  - sauto.
  - sauto inv: BigStep.
  - sauto inv: BigStep.
  - intros *.
    remember ('while b 'do c) as c'.
    induction 1; qauto inv: BigStep.
  - sauto unfold: entails.
Qed.
