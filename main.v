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
    | nilp => 0
    | (mp h) +:: t => (numposn t) + h + 1
  end
  with numposn (x: negg) : nat :=
  match x with
    | niln => 0
    | _ -:: t => (numposp t)
  end.

Fixpoint numnegp (x: posg) : nat :=
  match x with
    | nilp => 0
    | _ +:: t => (numnegn t)
  end
  with numnegn (x: negg) : nat :=
  match x with
    | niln => 0
    | (mn h) -:: t => (numnegp t) + h + 1
  end.


Eval simpl in numposp ((mp 6) +:: (mn 5) -:: [+]).
Eval simpl in numnegn ((mn 6) -:: (mp 5) +:: [-]).
Eval simpl in numnegp ((mp 6) +:: (mn 5) -:: [+]).
Eval simpl in numposn ((mn 6) -:: (mp 5) +:: [-]).
Eval simpl in  (mp 6) +:: (mn 5) -:: [+].
Eval simpl in (mn 0) -:: [+].
