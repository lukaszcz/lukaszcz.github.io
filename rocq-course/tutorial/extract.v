(* Tutorial 21: Program extraction *)

Require Extraction.
Require Import Arith.
Require List.
Import List.ListNotations.
Open Scope list_scope.
Open Scope bool_scope.

Fixpoint insert (l : list nat) (x : nat) : list nat :=
  match l with
  | [] => [x]
  | h :: t => if x <=? h then x :: l else h :: insert t x
  end.

Fixpoint isort (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => insert (isort t) h
  end.

Extraction isort.
Recursive Extraction isort.

Extract Inductive bool => "bool" [ "true" "false" ].
(* The inductive type "bool" in Coq should be mapped to type "bool" in
   OCaml, the first constructor of "bool" in Coq should be mapped to
   "true" in OCaml, and the second to "false" *)
Extract Inductive list => "list" [ "[]" "(::)" ].

Recursive Extraction isort.
(* Now we use the native OCaml types for "bool" and "list", but
   natural numbers are still represented in unary format. *)

Extract Inductive nat => "int" [ "0" "(fun x -> x + 1)" ].

Recursive Extraction isort.
(* Oops! Invalid pattern matches - the "Extract Inductive" command
   defines a simple syntactic translation which is not checked in any
   way. *)

Extract Inductive nat => "int" [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n ->
      if n=0 then zero () else succ (n-1))".
(* We need to explicitly specify a function which will act as a
   recursor if we map some constructors to OCaml/Haskell expressions
   which are not constructors of algebraic data types. *)

Recursive Extraction isort.
(* We no longer use unary numbers, but the extracted "Nat.leb"
   comparison function has runtime linear in its arguments. *)

Extract Constant Nat.leb => "( <= )".
Recursive Extraction isort.

Extraction Inline Nat.leb.
Recursive Extraction isort.

(* The ExtrOcamlNatInt module defines the mappings for extracting
   "nat" to "int" and associated basic functions on "nat" in the
   standard library to appropriate OCaml functions. *)
Require Import ExtrOcamlNatInt.
Recursive Extraction isort.
(* Require Import ExtrHaskellNatInt. *)

(* This way of extracting Nat to a native integer datatype is
   potentially brittle (and might introduce bugs in the verified code
   because native integers are not unbounded natural numbers). A
   better way is either to use Coq's Z (integer) type which has a
   "normal" logarithmic-size binary representation, or to use an
   abstract type and only instantiate it with required types on the
   OCaml level. *)

Extraction "isort.ml" isort.
(* Recursive extraction into a file. *)

(* Coq's extraction is not formally verified - it is a part of the
   trusted code base. There exists a verified compiler from Coq to
   OCaml - OEuf (https://oeuf.uwplse.org). *)
