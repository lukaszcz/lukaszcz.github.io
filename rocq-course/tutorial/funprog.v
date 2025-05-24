(* Tutorial 1: Functional programming in Rocq *)

(***********************************************************************************)
(* Functions and definitions *)

Definition square := fun x => x * x.

Check square.

Definition square' (x : nat) : nat := x * x.

Print square'.

Definition square'' x := x * x.

Print square''.

Compute square 2.

(***********************************************************************************)
(* Booleans *)

Print bool.

Compute if true then 1 else 2.

Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Print negb.

Compute negb true.
Compute negb (negb true).

Search bool.

Print xorb.

(***********************************************************************************)
(* Natural numbers *)

Print nat.

Search nat.

Print Nat.pred.

(* In Rocq, all functions are true "mathematical functions": they are
   total, they never "fail" or raise exceptions. *)

(* In pattern matches all cases must be covered! *)
Fail Definition pred (n : nat) : nat :=
  match n with
  | S m => m
  end.

Print option.

Definition pred (n : nat) : option nat :=
  match n with
  | 0 => None
  | S m => Some m
  end.

Compute pred 5.
Compute pred 0.

(***********************************************************************************)
(* Recursion *)

Fixpoint mult2 (n : nat) :=
  match n with
  | 0 => 0
  | S m => S (S (mult2 m))
  end.

Print mult2.

Compute mult2 8.

Definition explicitFixMult := fix mult2 (n : nat) :=
                                match n with
                                | 0 => 0
                                | S m => S (S (mult2 m))
                                end.

Print explicitFixMult.

Search nat.
Compute (Nat.even 10).
Compute (Nat.even 11).
Compute (Nat.div2 10).

(* Only structural recursion is allowed! *)
Fail Fixpoint collatz (n : nat) : bool :=
  match n with
  | 0 => false
  | 1 => true
  | _ => collatz (if Nat.even n then Nat.div2 n else 3 * n + 1)
  end.

Fail Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | S (S m) => fib m + fib (S m)
  end.

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 1
  | 1 => 1
  | S (S m as m') => fib m + fib m'
  end.

Compute fib 10.

(* Mutual structural recursion is also allowed. *)
Fixpoint even (n : nat) : bool :=
  match n with
  | 0 => true
  | S m => odd m
  end
with odd (n : nat) : bool :=
  match n with
  | 0 => false
  | S m => even m
  end.

(***********************************************************************************)
(* Polymorphism and higher-order functions *)

(* Arguments in curly braces { } are implicit - they need not be
   provided by the user when invoking the function but instead are
   inferred by Rocq (when possible). *)
Definition compose {A B C} (g : B -> C) (f : A -> B) :=
  fun x : A => g (f x).

Fixpoint iterate {A} (f : A -> A) n : A -> A :=
  match n with
  | 0 => fun x => x
  | S m => compose f (iterate f m)
  end.

Definition my_plus := iterate S.
(* `my_plus m n` applies `S` `m` times to `n` *)

Compute my_plus 3 7.

Definition my_mult m n := iterate (my_plus n) m 0.

Compute my_mult 3 7.

Definition my_exp m n := iterate (my_mult m) n 1.

Compute my_exp 3 7.

(* Ackermann's function:

ackermann 0 n = n + 1
ackermann (m + 1) 0 = ackermann m 1
ackermann (m + 1) (n + 1) = ackermann m (ackermann (m + 1) n)

Notice: ackermann (m + 1) n = iterate (ackermann m) (n + 1) 1

*)

(* Ackermann's function is not primitive recursive. This means it
grows extremely fast. Even though Rocq allows only structural
recursion, Ackermann's function can be encoded using polymorphic
higher-order functions. Despite the restrictions on recursion, the set
of definable functions is quite large. *)

Definition ackermann m : nat -> nat :=
  iterate (fun (f : nat -> nat) (n : nat) => iterate f (S n) 1) m S.

Compute ackermann 3 5.

(***********************************************************************************)
(* Pairs and currying *)

Print pair.

Check pair 2 3.
Check (2, 3).

Definition curry {A B C} (f : A * B -> C) (x : A) (y : B) : C :=
  f (x, y).

Check curry.
Check @curry.

Definition uncurry {A B C} (f : A -> B -> C) (p : A * B) : C :=
  f (fst p) (snd p).

Check uncurry.
Check @uncurry.

(**********************************************************************************)
(* Algebraic data types as inductive types *)

Inductive color_rgb := red | green | blue.

Print color_rgb.

Fail Definition partial c :=
  match c with
  | green => blue
  | blue => green
  end.

Inductive ntree := nleaf (n : nat) | nnode (l r : ntree).

Print ntree.

(* This inductive type is parameterised by A *)
Inductive tree A := leaf (x : A) | node (l r : tree A).

Print tree.

(* Each constructor has extra arguments corresponding to the
   parameters. *)
Check leaf.

Fail Check (leaf 3).
Check (leaf nat 3).

(* One can declare the parameter arguments implicit, so that they need
   not be provided and are inferred by Coq instead (when possible). *)
Arguments leaf {A}.
Arguments node {A}.

Check (leaf 3).

Definition tree1 := node (leaf 1) (node (leaf 2) (leaf 3)).

Print tree1.
Set Printing All.
Print tree1.
Unset Printing All.

Check leaf.
Check @leaf.

(* Inference of implicit arguments is not decidable in general, so it
   sometimes fails. Here, we need to explicitly provide the type of
   t. *)
Fail Fixpoint mirror t :=
  match t with
  | leaf _ => t
  | node l r => node (mirror r) (mirror l)
  end.

Fixpoint mirror {A} (t : tree A) :=
  match t with
  | leaf _ => t
  | node l r => node (mirror r) (mirror l)
  end.

Compute mirror tree1.

(************************************************************************************)
(* Lists *)

Print list.

Open Scope list_scope.
(* Now the notation :: for cons is available *)

Compute (1 :: 2 :: nil).

Require List.
Import List.ListNotations.
(* More list notations. *)

Compute [1; 2; 3].
Compute [].

Fixpoint gen n :=
  match n with
  | 0 => nil
  | S m => n :: gen m
  end.

Compute (gen 3).

Print List.rev.

Definition reverse {A} (l : list A) :=
  let fix reverse l acc :=
    match l with
    | nil => acc
    | h :: t => reverse t (h :: acc)
    end
  in
  reverse l nil.

Compute reverse (gen 3).

Search list.

Print app.
Compute (app (gen 1) (gen 2)).
Compute (gen 1 ++ gen 2).

Print List.map.
Print List.fold_right.
Print List.fold_left.

Definition reverse2 {A} (l : list A) :=
  List.fold_left (fun acc x => x :: acc) l nil.

Compute reverse2 [1; 2; 3].

(************************************************************************************)
(* Tail recursion *)

(* A function is tail-recursive if all results of recursive calls are
   returned directly without any further processing. *)

(* Not tail-recursive, exponential runtime. *)
Print fib.

(* Tail-recursive, linear runtime. *)
Definition fib' n :=
  (* Invariant: a = fib (n - k), b = fib (n - k + 1) *)
  let fix hlp a b k :=
      match k with
      | 0 => a
      | S m => hlp b (a + b) m
      end
  in
  hlp 1 1 n.

(* Imperative loops can be naturally encoded as tail-recursive
   functional programs *)
(*
a := 1
b := 1
k := n
while (k <> 0) do
   (a, b) := (b, a + b)
   k := k - 1
done
return a
*)

(************************************************************************************)
(* Generalized algebraic data types (GADTs) as inductive types *)

Require Import String.
Open Scope string_scope.
(* Makes string notation available. *)

Compute "abba".

(* Well-typed expressions *)
Inductive expr : Type -> Type :=
| var : string -> expr nat
| plus : expr nat -> expr nat -> expr nat
| equal : expr nat -> expr nat -> expr bool
| const {A} : A -> expr A
| ite {A} : expr bool -> expr A -> expr A -> expr A.

Check (const 3).
Check (const true).
Check (ite (const true) (const 1) (const 2)).
Fail Check (ite (const true) (const 1) (const true)).

Definition or e1 e2 := ite e1 (const true) e2.
Definition and e1 e2 := ite e1 e2 (const false).

Check or.

Definition expr1 :=
  ite (or (equal (plus (var "x") (const 1)) (var "y"))
          (equal (var "y") (const 7)))
      (const "abba")
      (const "bubba").

Definition store := string -> nat.

Fixpoint eval {A} (s : store) (e : expr A) : A :=
  match e with
  | var v => s v
  | plus e1 e2 => eval s e1 + eval s e2
  | const x => x
  | equal e1 e2 => Nat.eqb (eval s e1) (eval s e2)
  | ite b e1 e2 => if eval s b then eval s e1 else eval s e2
  end.

Definition s1 v := match v with "x" => 2 | "y" => 3 | _ => 0 end.

Compute eval s1 expr1.
Compute eval (fun _ => 0) expr1.
Compute eval (fun _ => 7) expr1.

(************************************************************************************)
(* A taste of dependent types *)

(* We will treat dependent types in more depth later. Now we give only
   a few brief examples. *)

Inductive vector (A : Type) : nat -> Type :=
  nil : vector A 0 | cons (_ : A) (n : nat) : vector A n -> vector A (S n).

Arguments nil {A}.
Arguments cons {A} _ {n}.

Fixpoint vgen n :=
  match n with
  | 0 => nil
  | S m => cons n (vgen m)
  end.

Check vgen.

Print List.tl.
Compute List.tl [].

(* With dependent pattern matching,
  impossible cases may be omitted. *)
Definition tl {A n} (v : vector A (S n)) : vector A n :=
  match v with
  (* the case "nil" is impossible: `v` would need
     to have type `vector A 0` *)
  | cons _ v' => v'
  end.

Print tl.

Compute tl (vgen 10).
Fail Compute tl (vgen 0).

Definition hd {A n} (v : vector A (S n)) : A :=
  match v with
  | cons x _ => x
  end.

Compute hd (vgen 5).
Fail Compute hd (vgen 0).

Fixpoint vapp {A n m} (v1 : vector A n) (v2 : vector A m) : vector A (n + m) :=
  match v1 with
  | nil => v2
  | cons x v1' => cons x (vapp v1' v2)
  end.

Compute vapp (vgen 3) (vgen 5).
Compute hd (vapp (vgen 3) (vgen 5)).
Fail Compute hd (vapp (vgen 0) (vgen 0)).

Fail Definition vrev {A n} (v : vector A n) : vector A n :=
  let fix vrev {n m} (v : vector A n) (acc : vector A m) : vector A (n + m) :=
    match v with
    | nil => acc
    | cons x v' => vrev v' (cons x acc)
    end
  in
  vrev v nil.

(* Agda and Idris have better built-in support for dependent pattern
   matching syntax. For Rocq, there exists the "Program" command which
   redefines Rocq's "match" to automatically choose the right types and
   synthesise parts of the program. It may leave some "proof
   obligations" to be solved by the user if it can't do everything
   automatically. *)

Require Program.

Program Definition vrev {A n} (v : vector A n) : vector A n :=
  let fix vrev {n m} (v : vector A n) (acc : vector A m) : vector A (n + m) :=
    match v with
    | nil => acc
    | cons x v' => vrev v' (cons x acc)
    end
  in
  vrev v nil.

(* With the "Program" command we need to explicitly handle impossible
   cases, but we can use wildcards "_" to automatically synthesise
   code for them. *)
Program Definition hd1 {A n} (v : vector A (S n)) : A :=
  match v with
  | nil => _
  | cons x _ => x
  end.

Print hd1.

(* The "Equations" package brings Rocq even closer to
   Agda/Idris/Haskell by allowing to define functions by equations. If
   the package cannot be found try installing it with:
   `opam install coq-equations`. *)

From Equations Require Equations.

Equations hd' {A n} (v : vector A (S n)) : A :=
  hd' (cons x _) := x.

(* We'll talk more about the "Program" command later! *)

(************************************************************************************)
(* A taste of program extraction *)

(* Coq definitions may be extracted to Ocaml, Haskell or Scheme. More
   about this later. *)

Require Extraction.

Extraction Language Haskell.

Print fib.
Recursive Extraction fib.

Print vapp.
Recursive Extraction vapp.

Print vrev.
Recursive Extraction vrev.

Extraction Inline eq_rect.
Recursive Extraction vrev.
