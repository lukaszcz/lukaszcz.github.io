(* Tutorial 11: Proof automation with Ltac *)

From Hammer Require Import Tactics.

Locate "+".
Print Nat.add.

(* "R_add n m k" holds iff "k = n + m" *)
Inductive R_add : nat -> nat -> nat -> Prop :=
| add_0 : forall m, R_add 0 m m
| add_S : forall p m k, R_add p m k -> R_add (S p) m (S k).

Lemma lem_R_add_complete : forall n m, R_add n m (n + m).
Proof.
  Fail sauto.
  induction n; sauto.
Qed.

Lemma lem_R_add_correct : forall n m k, R_add n m k -> k = n + m.
Proof.
  (* time (induction n; sauto). *)
  time (induction 1; sauto).
Qed.

Example ex_8_plus_5 : 8 + 5 = 13.
Proof.
  reflexivity.
Qed.

Example ex_8_plus_5' : R_add 8 5 13.
Proof.
  Fail reflexivity.
  repeat constructor.
Qed.

Print ex_8_plus_5.
Print ex_8_plus_5'.

Example ex_8_plus_5'' : R_add 8 5 13.
Proof.
  auto using R_add.
  (* "auto" has a default search depth limit of 5 *)
  auto 9 using R_add.
Qed.

Print ex_8_plus_5''.

Example ex_minus : exists x, R_add x 2 5.
Proof.
  auto using R_add.
  Check ex_intro.
  Fail apply ex_intro.
  eapply ex_intro.
  apply add_S.
  do 2 apply add_S.
  (* "do n tac" applies "tac" to the current goal, then to all
     generated subgoals, and so on "n" times *)
  apply add_0.

  Restart.

  eauto using R_add.
Qed.

(********************************************************************************)
(* Hint and rewriting databases *)

Print R_add.

Lemma lem_plus_S : forall p m k, p + m = k -> S p + m = S k.
Proof.
  sauto.
Qed.

Hint Resolve lem_plus_S : mydb.

Check plus_O_n.
Hint Immediate plus_O_n : mydb.
(* immediate hints are applied only at the leaves of
   the proof search tree, i.e., when all generated subgoals
   can be solved with "trivial" *)

Example ex_1 : exists x, x + 2 = 5.
Proof.
  eauto.
  eauto with mydb.
Qed.

Example ex_2 : exists x, 4 + x + 0 = 7.
Proof.
  eauto 6 with mydb.
Abort.

Lemma lem_plus_0 : forall n m, n = m -> n + 0 = m.
Proof.
  sauto.
Qed.

Hint Resolve lem_plus_0 : mydb.

Example ex_2 : exists x, 4 + x + 0 = 7.
Proof.
  eauto 6 with mydb.
Qed.

Check eq_trans.

Example ex_3 : exists x, 1 + x = 0.
Proof.
  eauto using eq_trans.
  eauto.
  time eauto 1 using eq_trans.
  time eauto 2 using eq_trans.
  time eauto 3 using eq_trans.
  time eauto 4 using eq_trans.
  time eauto 5 using eq_trans.
  (* time eauto 6 using eq_trans. *)
  debug eauto 3 using eq_trans.
Abort.
(* The presence of "eq_trans" causes exponential blow-up, because
   "eq_trans" may always be applied generating two subgoals and
   introducing a new existential metavariable. *)
(* One needs to be careful when constructing hint databases! *)

(* Constructor hints *)

Hint Constructors R_add : R_add_db.

Example ex_minus' : exists x, R_add x 2 5.
Proof.
  eauto.
  eauto with R_add_db.
Qed.

(* Unfolding hints *)

Locate "<->".

Hint Unfold iff : mydb.

Example ex_iff : forall P Q : Prop, P -> Q -> (P <-> Q).
Proof.
  auto.
  auto with mydb.
Qed.

(* External hints *)

Hint Extern 1 (_ = _) => congruence : mydb.

Example ex_eq : forall A (f : A -> A) (g : A -> A -> A) (x y : A),
    (forall x y : A, g x y = g y x) -> x = y ->
      g (f (g x y)) y = g y (f (g y x)).
Proof.
  auto.
  congruence.
  Restart.
  auto with mydb.
Qed.

(* Rewriting hints *)

Section Rewriting.

  Variable A : Set.
  Variable f : A -> A.

  Hypothesis Hf : forall x, f (f x) = f x.

  Hint Rewrite Hf : my_rew_db.

  Lemma lem_f3 : forall x, f (f (f x)) = f x.
  Proof.
    Fail auto with my_rew_db.
    autorewrite with my_rew_db.
    autorewrite with my_rew_db in *.
    (* By default, rewriting does not occur under binders! We need to
       do intro first to remove the binder in the goal. *)
    intro x.
    autorewrite with my_rew_db.
    reflexivity.
  Qed.

End Rewriting.

Check lem_f3.

(* "sauto" (and most other tactics from CoqHammer) can also use hint
   and rewriting databases with the "db:" option *)

Print HintDb R_add_db.
Fail Print HintDb list.
Print Rewrite HintDb list.

Example ex_minus'' : exists x, R_add x 2 18.
Proof.
  sauto.
  (* "sauto" by default tries to apply all possible constructors,
     so it solves this goal *)
  Undo.
  (* "hauto" is essentially "sauto inv: - ctrs: -" *)
  Fail hauto.
  hauto db: R_add_db.
Qed.

(* Useful hint databases: arith (Require Import Arith), datatypes *)
(* Useful rewriting databases: list (Require Import List) *)

(********************************************************************************)
(* Failure, success and progress *)

(* A tactic may succeed or fail. If it succeeds it may progress
   (change the proof state) or not. *)

(* "auto", "eauto" and "trivial" always succeed, but they might not
   progress *)

Example ex_success_failure :
  forall P, P 0 -> (forall x, P x -> P (S x)) -> P 20.
Proof.
  auto.
  Fail progress auto.
  Fail solve [ auto ].
  (* solve [ tac1 | ... | tacn ] tries the tactics in turn and fails
     if none of the tactics completely solves the goal *)
  Fail fail. (* "fail" always fails. *)
  idtac. (* "idtac" always succeeds, doing nothing *)
  Fail progress idtac.
  progress intro.
  repeat intro.
  (* "repeat tac" applies "tac" to the current goal, then to all
      generated subgoals, and so on, as long as "tac" progresses *)
  Fail intro.
  try intro.
  (* "try tac" runs "tac" ignoring failure ("try tac" always succeeds) *)
  Fail progress try intro.
  repeat try intro.
  progress apply X0.
  first [ intro | apply X0 ].
  (* first [ tac1 | ... | tacn ] runs the tactics in turn from left to
     right and stops when a tactic succeeds *)
  first [ idtac | apply X0 ].
  idtac || apply X0.
  (* "tac1 || tac2" is equivalent to first [ progress tac1 | tac2 ] *)
  tryif intro then intro else apply X0.
  (* "tryif tac0 then tac1 else tac2" runs tac0 and then if it
  succeeds runs tac1, otherwise tac2 *)
  repeat apply X0.
  solve [ idtac | assumption ].
Qed.

(********************************************************************************)
(* Pattern matching *)

Ltac destruct_match :=
  match goal with
  | [ |- match ?X with _ => _ end ] => destruct X
  end.

Require Import Arith. (* for <? notation *)

Example ex_match_1 : forall x y, if x <? y then True else x = x.
Proof.
  Fail destruct_match.
  intros.
  destruct_match.
  Undo.
  destruct_match; [ exact I | reflexivity ].
Qed.

Ltac destruct_match_2 :=
  match goal with
  | [ |- context[match ?X with _ => _ end] ] => destruct X
  end.

Example ex_match_2 : forall x y, (if x <? y then False else x <> x) -> False.
Proof.
  Fail destruct_match_2.
  (* No matching of bound variables! *)
  intros x y.
  Fail destruct_match.
  destruct_match_2.
  Undo.
  destruct_match_2; auto.
Qed.

Ltac destruct_match_3 :=
  match goal with
  | [ H : match ?X with _ => _ end |- _ ] => destruct X
  end.

Example ex_match_3 : forall x y, (if x <? y then False else x <> x) -> False.
Proof.
  intros.
  Fail destruct_match.
  Fail destruct_match_2.
  destruct_match_3.
  Undo.
  destruct_match_3; auto.
Qed.

Ltac destruct_match_4 :=
  match goal with
  | [ H: context[match ?X with _ => _ end] |- _ ] => destruct X
  | [ |- context[match ?X with _ => _ end] ] => destruct X
  end.
(* Backtracking semantics for failure.

   * If the tactic in a branch fails, then another possibility of
     matching the pattern in that branch is tried.

   * If the tactic in a branch fails for all possible ways of
     matching the branch pattern, then the next branch is tried.
*)

Example ex_match_4 : forall x y, (if x <? y then False else True) ->
                                 if x <=? y then x = y else True.
Proof.
  intros.
  destruct_match_4.
  destruct_match_4.
  Restart.
  intros.
  repeat destruct_match_4; try strivial.
Abort.

Ltac destruct_matches :=
  repeat match goal with
         | [ H : context[match ?X with _ => _ end] |- _ ] => destruct X eqn:?
         | [ |- context[match ?X with _ => _ end] ] => destruct X eqn:?
         end.

Example ex_matches : forall x y, if 2 =? x then
                                   (if x <? y then False else True) ->
                                   if x <=? y then x = y else True
                                 else
                                   (if x <? y then True else False) ->
                                   x <? y = true.
Proof.
  intros.
  destruct_matches; try strivial.
  apply leb_complete in Heqb1.
  apply Nat.ltb_nlt in Heqb0.
  strivial.
Qed.

Print BoolSpec.

Check Nat.ltb_spec.
Check Nat.leb_spec.

Print Bool.reflect.

Check Nat.eqb_spec.

Ltac destruct_bool t :=
  match t with
  | ?X <? ?Y => destruct (Nat.ltb_spec X Y)
  | ?X <=? ?Y => destruct (Nat.leb_spec X Y)
  | ?X =? ?Y => destruct (Nat.eqb_spec X Y)
  end.
(* matching on terms also has the backtracking failure semantics *)

Ltac mydestruct t :=
  match type of t with
  | bool => destruct_bool t
  | _ => destruct t eqn:?
  end.

Ltac destruct_matches' :=
  repeat match goal with
         | [ H : context[match ?X with _ => _ end] |- _ ] => mydestruct X
         | [ |- context[match ?X with _ => _ end] ] => mydestruct X
         end.

Example ex_matches' : forall x y, if 2 =? x then
                                    (if x <? y then False else True) ->
                                    if x <=? y then x = y else True
                                  else
                                    (if x <? y then True else False) ->
                                    x <? y = true.
Proof.
  intros.
  destruct_matches'; strivial.

  Restart.

  intros.
  repeat match goal with
         | [ |- context[match ?X with _ => _ end] ] => sdestruct X
         end.
  (* The "sdestruct" tactic from Hammer.Tactics is essentially a more
     sophisticated version of "mydestruct" *)
  all: strivial.

  Restart.

  sauto.
  (* "sauto" performs cases destruction (destruction of terms matched on
      somewhere in the goal or a hypothesis) by default *)
  Undo.
  Fail sauto cases: -.
  (* sauto cases: bool *)
  simpl.
  Undo.
  sauto cases: bool ered: off.
  Undo.
  sauto cases: bool, nat.
Qed.

(********************************************************************************)
(* Programming in Ltac *)

Require List.
Open Scope list_scope.
Import List.ListNotations.

Fail Ltac len l :=
  match l with
  | [] => 0
  | _ :: t => S (len t)
  end.

Fail Ltac len l :=
  match l with
  | [] => 0
  | _ :: ?t => S (len t)
  end.

Fail Ltac len l :=
  match l with
  | [] => 0
  | _ :: ?t =>
    let n := len t in
    S n
  end.

Ltac len l :=
  match l with
  | [] => 0
  | _ :: ?t =>
    let n := len t in
    constr:(S n)
  end.

Goal False.
  Fail let l := len [1; 2; 3] in
       idtac l.
  (* idtac displays its argument (useful for debugging tactics) *)
Abort.

Reset len.

Ltac len l :=
  match l with
  | [] => constr:(0)
  | _ :: ?t =>
    let n := len t in
    constr:(S n)
  end.

Goal False.
  let l := len [1; 2; 3] in
  idtac l.
Abort.

(********************************************************************************)
(* Proof search with Ltac *)

Ltac myauto_gen tac n :=
  match n with
  | 0 => solve [ tac ]
  | S ?k =>
    match goal with
    | [ |- forall _, _ ] => intros; myauto_gen tac n
    | [ H: _ |- _ ] => apply H; myauto_gen tac k
    (* ordinary "auto" does not do rewriting, constructor or destruct *)
    | [ H: context[_ = _] |- _ ] => rewrite H; clear H; myauto_gen tac k
    | [ H: ?I |- _ ] =>
      match I with
      | forall _, _ =>
        fail 1 (* "fail n" jumps out of n matches ignoring unexplored branches *)
      | _ =>
        match type of I with
        | Prop => destruct H; subst; simpl in *; myauto_gen tac k
        end
      end
    | [ |- _ ] => constructor; myauto_gen tac k
    end
  end.

Tactic Notation "myauto" := myauto_gen easy 5.
Tactic Notation "myauto" "depth:" int(n) := myauto_gen easy n.
Tactic Notation "myauto" "solve:" tactic(tac) := myauto_gen tac 5.
Tactic Notation "myauto" "using:" ne_constr_list_sep(lst,",") :=
  generalize lst; myauto_gen easy 5.
Tactic Notation "myauto" "using:" ne_constr_list_sep(lst,",") "solve:" tactic(tac) :=
  generalize lst; myauto_gen tac 5.
(* See: https://coq.inria.fr/refman/user-extensions/syntax-extensions.html#tactic-notations *)

Example ex_auto_1 (A B : Prop) : (forall P : Prop, (A -> B -> P) -> P) <-> A /\ B.
Proof.
(*
  split. (* "split" just applies the constructor for conjunction *)
  - intro H.
    split; apply H; trivial.
  - intro H.
    destruct H.
    auto.
*)
  time auto.
  time myauto.
  Undo.
  time sauto.
Qed.

Example ex_auto_2 {A} :
  forall l1 l2 : list A, List.rev (l1 ++ l2) = List.rev l2 ++ List.rev l1.
Proof.
(*
  induction l1 as [|? ? IH].
  - intro.
    simpl.
    rewrite List.app_nil_r; reflexivity.
  - intro.
    simpl.
    rewrite IH.
    rewrite List.app_assoc.
    reflexivity. (* reflexivity is essentially applying the
                    constructor of equality (eq_refl) *)
 *)
  Fail (induction l1; myauto using: List.app_nil_r, List.app_assoc).
  time (induction l1; simpl; myauto using: List.app_nil_r, List.app_assoc).
  Undo.
  time (induction l1; sauto use: List.app_nil_r, List.app_assoc).
Qed.
