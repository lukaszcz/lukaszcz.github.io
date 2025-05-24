(* Tutorial 5: Induction *)

(************************************************************************************)
(* Induction on natural numbers *)

Lemma lem_refl' : forall x : nat, 1 + x = S x.
Proof.
  intro x.
  reflexivity.
  Show Proof.
Qed.

Lemma lem_refl1 : forall x : nat, x + 1 = S x.
Proof.
  intro x.
  Fail reflexivity.
  Print Nat.add.
  induction x.
  - reflexivity.
  - simpl. (* computes in the goal *)
    rewrite IHx.
    reflexivity.
Qed.

Print lem_refl1.
Print nat_ind.
(* The "induction" tactic just applies an
   appropriate induction principle. *)

(************************************************************************************)
(* Structural induction *)

Require List.
Import List.ListNotations.
Open Scope list_scope.

Print List.map.

Lemma lem_map_id {A} (l : list A) : List.map (fun x => x) l = l.
Proof.
  Print list.
  (* the "as" patterns are like with "destruct" (listing all
     non-parameter arguments for each constructor), except that after
     each recursive argument there is the corresponding inductive
     hypothesis for this argument *)
  induction l as [ | x l IH ].
  - reflexivity.
  - simpl. (* "simpl" computes in the goal (simplifies the goal) *)
    rewrite IH.
    reflexivity.
Qed.

Check lem_map_id.

Inductive tree A := leaf (x : A) | node (l r : tree A).

Arguments leaf {A}.
Arguments node {A}.

Fixpoint mirror {A} (t : tree A) :=
  match t with
  | leaf _ => t
  | node l r => node (mirror r) (mirror l)
  end.

Lemma lem_mirror_mirror {A} (t : tree A) : mirror (mirror t) = t.
Proof.
  induction t as [ x | l IHl r IHr ]; simpl.
  - reflexivity.
  - rewrite IHl.
    rewrite IHr.
    reflexivity.
Qed.

(************************************************************************************)
(* Induction heuristics *)

Locate "++".
Print app.

Lemma lem_append_assoc A (l1 l2 l3 : list A) :
  l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.
  induction l2; simpl.
  Show 2.
  Undo.
  induction l3; simpl.
  Show 2.
  Undo.
  Print app.
  (* Heuristic: do induction on the argument which
                the topmost function recurses on *)
  induction l1 as [| x l1 Hl1].
  - reflexivity.
  - simpl.
    rewrite Hl1.
    reflexivity.
Qed.

Inductive btree A := bleaf (x : A) | bnode (x : A) (l r : btree A).

Arguments bleaf {A}.
Arguments bnode {A}.

Fixpoint itpre {A} (t : btree A) acc :=
  match t with
  | bleaf x => x :: acc
  | bnode x l r => x :: itpre l (itpre r acc)
  end.

Fixpoint preorder {A} (t : btree A) :=
  match t with
  | bleaf x => [x]
  | bnode x l r => x :: preorder l ++ preorder r
  end.

Lemma lem_pre {A} (t : btree A) : itpre t [] = preorder t.
Proof.
  induction t; simpl; trivial.
Abort.

(* Heuristic: generalise goals for induction by replacing constants
              with variables *)

Lemma lem_pre {A} (t : btree A) acc : itpre t acc = preorder t ++ acc.
Proof.
  induction t as [x|x l IHl r IHr].
  - reflexivity.
  - simpl.
    rewrite IHr.
Abort.

(* Heuristic: generalise goals for induction by generalising free variables *)

Lemma lem_pre {A} (t : btree A) acc : itpre t acc = preorder t ++ acc.
Proof.
  revert acc.
  induction t as [x|x l IHl r IHr].
  - reflexivity.
  - simpl.
    intro acc.
    rewrite IHr.
    rewrite IHl.
    rewrite lem_append_assoc.
    reflexivity.
Qed.
