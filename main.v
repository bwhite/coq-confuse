Eval simpl in S 1.

Inductive poss : Type :=
  | mp: nat -> poss.

Inductive negs : Type :=
  | mn : nat -> negs.

Inductive posg :=
| nilp : posg
| consp : poss -> negg -> posg
with negg:=
| niln : negg
| consn : negs -> posg -> negg.

Notation "x +:: l" := (consp x l) (at level 60, right associativity).
Notation "x -:: l" := (consn x l) (at level 60, right associativity).
Notation "[+]" := nilp.
Notation "[-]" := niln.
Eval simpl in  (mp 6) +:: (mn 5) -:: [+].
