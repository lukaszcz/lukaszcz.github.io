(* Tutorial 15: More dependent types *)

From Hammer Require Import Tactics.
Require Import Arith.

Require List.
Import List.ListNotations.
Open Scope list_scope.

(*
Fixpoint last {A} (l : list A) {struct l} : l <> [] -> A.
  refine (
      match l as l' return l' <> [] -> A with
      | [] => fun p : [] = [] -> False => _ (* first subgoal *)
      | h :: t =>
          match t as t' return h :: t' <> [] -> A with
          | [] => fun _ => h
          | x :: u => fun p => last A t _ (* second subgoal *)
          (* | x :: u => fun p => last A (x :: u) _ *)
          end
      end
    ).
  - congruence.
  - congruence.
Defined.
*)

Fixpoint last {A} (l : list A) (p : l <> []) {struct l} : A.
  refine (
      match l as l' return l = l' -> A with
      | [] => fun q => _ (* first subgoal *)
      | h :: t =>
        fun q =>
          match t as t' return t = t' -> A with
          | [] => fun _ => h
          | _ => fun r => last A t _ (* second subgoal *)
          end eq_refl
      end eq_refl
    ).
  - congruence.
  - congruence.
Defined.
(* Generalizing the return type of a match with equalities is a very
   common technique! *)


(* Reasoning with vectors *)

Inductive vector (A : Type) : nat -> Type :=
| vnil : vector A 0
| vcons : forall (n : nat), A -> vector A n -> vector A (S n).

Arguments vnil {A}.
Arguments vcons {A n}.

Notation "[: :]" := vnil.
Notation "[: x :]" := (vcons x vnil).
Notation "[: x ; y ; .. ; z :]" := (vcons x (vcons y .. (vcons z vnil) ..)).
(* See:
https://coq.inria.fr/refman/user-extensions/syntax-extensions.html#notations
https://coq.inria.fr/refman/language/coq-library.html#init-notations
*)

Definition vhd {A n} (v : vector A (S n)) : A :=
  match v with
  | vcons x _ => x
  end.

Print vhd.

(* idProp is a "dummy" value *)
Print IDProp.
Print idProp.

Fixpoint vapp {A n m} (v1 : vector A n) (v2 : vector A m) : vector A (n + m) :=
  match v1 with
  | vnil => v2
  | vcons x v => vcons x (vapp v v2)
  end.

Print vapp.

(*
vapp =
fix vapp (A : Type) (n m : nat) (v1 : vector A n) (v2 : vector A m) {struct v1} :
vector A (n + m) :=
  match v1 in (vector _ n') return (vector A (n' + m)) with
  | vnil => v2 (* : vector A (0 + m) which is definitionally equal to "vector A m" *)
  | @vcons _ k x v1' => vcons x (vapp A k m v1' v2) (* : vector A (S k + m) *)
       (* vcons x (vapp A k m v1' v2) : vector A (S (k + m)) *)
       (* But (S (k + m)) and (S k + m) are definitionally equal,
          so everything works out *)
  end (* match .. end : vector A (n + m) *)
     : forall (A : Type) (n m : nat), vector A n -> vector A m -> vector A (n + m)
*)

Compute (vapp [: 1; 2 :] [: 1 :]).

Fail Definition vrev {A n} (v : vector A n) : vector A n :=
  let fix vrev {n m} (v : vector A n) (acc : vector A m) : vector A (n + m) :=
    match v with
    | vnil => acc
    | vcons x v' => vrev v' (vcons x acc)
    end
  in
  vrev v vnil.

Fail Definition vrev {A n} (v : vector A n) : vector A n :=
  let fix vrev {n m} (v : vector A n) (acc : vector A m) : vector A (n + m) :=
    match v in vector _ k return vector A (k + m) with
    | vnil => acc
    | vcons x v' => vrev v' (vcons x acc)
    end
  in
  vrev v vnil.

Print eq.

Print eq_rect.

Definition vcast {A} n m (p : n = m) (v : vector A n) : vector A m :=
  eq_rect n (fun k => vector A k) v m p.

Require Import Psatz. (* for "lia" and some lemmas about natural numbers *)

Fail Definition vrev {A n} (v : vector A n) : vector A n :=
  let fix vrev {n m} (v : vector A n) (acc : vector A m) : vector A (n + m) :=
    match v in vector _ k return vector A (k + m) with
    | vnil => acc
    | @vcons _ k' x v' =>
      vcast (k' + S m) (S k' + m) ltac:(lia) (vrev v' (vcons x acc))
    end
  in
  vrev v vnil.

Definition vrev {A n} (v : vector A n) : vector A n :=
  let fix vrev {n m} (v : vector A n) (acc : vector A m) : vector A (n + m) :=
    match v in vector _ k return vector A (k + m) with
    | vnil => acc
    | @vcons _ k' x v' => vcast (k' + S m) (S k' + m) ltac:(lia) (vrev v' (vcons x acc))
    end
  in
  vcast (n + 0) n ltac:(auto) (vrev v vnil).

Compute (vrev [: 1; 2 :]). (* oops! *)

(* The reason for a blocked computation are opaque constants
   (lemma definitions) which are never unfolded by the computation
   mechanism. "Qed" defines a constant as opaque, "Defined" as
   transparent. Most lemmas in the standard library are opaque, even
   if proven constructively. *)

(* However, this is not a "logical" but an (intended) "implementation"
   limitation. Extraction still works. *)

Require Import Extraction.
Extraction Language Haskell.

Extraction Inline vcast.
Extraction Inline eq_rect.

Recursive Extraction vrev.

Require Import Program.

Program Definition vrev' {A n} (v : vector A n) : vector A n :=
  let fix vrev {n m} (v : vector A n) (acc : vector A m) : vector A (n + m) :=
    match v with
    | vnil => acc
    | vcons x v' => vrev v' (vcons x acc)
    end
  in
  vrev v vnil.

Print vrev'.
Print vrev'_obligation_1.
Print vrev'_obligation_2.

(* The "Program" command does not help with the opaqueness of
   definitions. *)
Compute (vrev' [: 1; 2 :]). (* oops! *)

Recursive Extraction vrev'.

(* To make the proofs compute we need to re-prove the opaque lemmas we
   used, redefining them as transparent. *)

Lemma lem_plus_n_0 : forall n, n + 0 = n.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Defined. (* transparent *)

Lemma lem_plus_n_Sm : forall n m, n + S m = S n + m.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - intro m.
    simpl.
    rewrite IH.
    reflexivity.
Defined. (* transparent *)

Obligation Tactic := idtac.

Program Definition vrev'' {A n} (v : vector A n) : vector A n :=
  let fix vrev {n m} (v : vector A n) (acc : vector A m) : vector A (n + m) :=
    match v with
    | vnil => acc
    | vcons x v' => vrev v' (vcons x acc)
    end
  in
  vrev v vnil.
Next Obligation.
  auto using lem_plus_n_Sm.
Defined.
Next Obligation.
  auto using lem_plus_n_0.
Defined.

Obligation Tactic := program_simpl.

Compute (vrev'' [: 1; 2 :]).

(* This is annoying for larger developments! *)

(* We can:
1) give up on computation of the function inside Coq (extraction still
   works)
2) use an alternative proof-relevant library of lemmas
*)
