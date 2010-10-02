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

Fixpoint numposp (x: posg) : nat :=
  match x with
    | nilp => 1
    | (mp h) +:: t => (numposn t) + h + 1
  end
  with numposn (x: negg) : nat :=
  match x with
    | niln => 0
    | (mn h) -:: t => (numposp t) + 1
  end.

Eval simpl in numposp ((mp 6) +:: (mn 5) -:: [+]).

Eval simpl in  (mp 6) +:: (mn 5) -:: [+].
Eval simpl in (mn 0) -:: [+].
Eval simpl in {x : nat | x > 0}.