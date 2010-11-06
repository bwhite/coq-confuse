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

(* Proofs that cons'ing values has the expected effect on the count *)
Lemma add_n_to_p_count_p : forall (n:nat) (l:posg), numposn((mn n) -:: l) = numposp l.
Proof. intros. reflexivity. Qed.

Lemma add_n_to_p_count_n : forall (n:nat) (l:posg), numnegn((mn n) -:: l) = (numnegp l) + n + 1.
Proof. intros. reflexivity. Qed.

Lemma add_p_to_n_count_p : forall (n:nat) (l:negg), numposp((mp n) +:: l) = (numposn l) + n + 1.
Proof. intros. reflexivity. Qed.

Lemma add_p_to_n_count_n : forall (n:nat) (l:negg), numnegp((mp n) +:: l) = (numnegn l).
Proof. intros. reflexivity. Qed.

Inductive confmat: Type :=
  | cm :  nat -> nat -> nat -> nat -> confmat.
Notation "[ a , b , c , d ]" := (cm a b c d).
Eval simpl in [ 5, 6 , 3 , 2 ].

Definition cmsum (a b:confmat) : confmat :=
  match a, b with
    [ a0, a1, a2, a3 ], [ b0, b1, b2, b3 ] => [ a0 + b0, a1 + b1, a2 + b2, a3 + b3 ]
  end.

Definition settp (a:nat) : confmat :=
  [a, 0, 0, 0].

Definition setfp (a:nat) : confmat :=
  [0, a, 0, 0].

Definition settn (a:nat) : confmat :=
  [0, 0, a, 0].

Definition setfn (a:nat) : confmat :=
  [0, 0, 0, a].

Definition gettp (a:confmat) : nat :=
  match a with
    [a0, a1, a2, a3] => a0
  end.

Definition getfp (a:confmat) : nat :=
  match a with
    [a0, a1, a2, a3] => a1
  end.

Definition gettn (a:confmat) : nat :=
  match a with
    [a0, a1, a2, a3] => a2
  end.

Definition getfn (a:confmat) : nat :=
  match a with
    [a0, a1, a2, a3] => a3
  end.

Definition cmleftp (l:posg) : confmat :=
  [0, 0, numnegp l, numposp l].

Definition cmleftn (l:negg) : confmat :=
  [0, 0, numnegn l, numposn l].
    
Definition cmrightp (l:posg) : confmat :=
  [numposp l, numnegp l, 0, 0].

Definition cmrightn (l:negg) : confmat :=
  [numposn l, numnegn l, 0, 0].


Check True.
Require Import Arith.Lt.
Require Import Arith.Le.
Eval simpl in 5 <= 7.

Definition cmle (a b:confmat) : Prop :=
  gettp a <= gettp b /\ gettn a <= gettn b /\ getfn b <= getfn a /\ getfp b <= getfp a.

Definition cmlt (a b:confmat) : Prop :=
  cmle a b /\ (gettp a < gettp b \/ gettn a < gettn b \/ getfn b < getfn a \/ getfp b < getfp a).


Check le_S.
Lemma le_same: forall (a:nat), a <= a. intros. apply le_n. Qed.
Lemma le_same_p_one: forall (a:nat), a <= S a. intros. apply le_S. apply le_n. Qed.
Lemma le_same_p_n: forall (a n:nat), a <= n + a. intros. induction n. simpl. apply le_same. simpl. apply le_S. apply IHn. Qed.
Lemma cmle_plus_tp_conv: forall (a b c d n:nat), cmle [a,b,c,d] (cmsum (settp n) [a,b,c,d]) = cmle [a, b, c, d] [n + a, b, c, d]. reflexivity. Qed.
Lemma cmle_plus_tp: forall (a b c d n:nat), cmle [a,b,c,d] (cmsum (settp n) [a,b,c,d]).
Proof. intros. simpl. unfold cmle. simpl. split. apply le_same_p_n. split. apply le_same. split. apply le_same. apply le_same. Qed.

Lemma cmle_plus_tn: forall (a b c d n:nat), cmle [a,b,c,d] (cmsum (settn n) [a,b,c,d]).
Proof. intros. simpl. unfold cmle. simpl. split. apply le_n. split. apply le_same_p_n. split. apply le_same. apply le_same. Qed.

Lemma cmle_plus_fp: forall (a b c d n:nat), cmle (cmsum (setfp n) [a,b,c,d]) [a,b,c,d].
Proof. intros. simpl. unfold cmle. simpl. split. apply le_n. split. apply le_same. split. apply le_same. apply le_same_p_n. Qed.

Require Import Arith.Plus.
(* Lemma lt_same_p_n: forall (a n:nat), n > 0 -> a < n + a.
Proof. intros. induction a. rewrite plus_comm. simpl. unfold lt. auto. induction n. simpl.
(* This isn't true when n = 0 *)
Lemma cmlt_plus_tp: forall (a b c d n:nat), cmlt [a,b,c,d] (cmsum (settp n) [a,b,c,d]).
Proof. intros. simpl. unfold cmlt. split. rewrite <- cmle_plus_tp_conv. apply cmle_plus_tp. left. simpl. *)
Notation "x |<| y" := (cmlt x y) (at level 70, right associativity).
Notation "x |+| y" := (cmsum x y) (at level 60, right associativity).
(* Note a is turned around to allow for it to match with b.  Show that selecting points intermediate to a group will never produce a threshold larger than either endpoint. *)
Lemma real_p: forall (a b: negg) (n:nat),
  [numposn a, numposp (mp n +:: b),  numnegn a, numnegn b] |<|
  [numposn a, numposn b,  numnegp (mp n +:: a), numnegn b]. intros. simpl. unfold cmlt. simpl. split. unfold cmle. simpl. split. induction a. simpl. apply le_n. simpl. apply le_n. split. apply le_n. split. apply le_n. induction n. rewrite plus_comm. simpl. apply le_S. rewrite plus_comm. simpl. apply le_n. rewrite plus_comm. apply le_S. assert (n + 1 = S n). apply plus_comm. rewrite <- H. assert (numposn b + (n + 1) = numposn b + n + 1). rewrite plus_assoc. reflexivity. rewrite H0. apply IHn. right. right. right. rewrite <- plus_assoc. rewrite plus_comm. unfold lt. rewrite <- plus_assoc. simpl. apply le_plus_r. Qed.

(* Show that by adding positive points to the left side always hurts performance *)
Lemma dont_take_middle_points_p: forall (a b: negg) (n m:nat),
  cmleftp ((mp n) +:: a) |+| (cmrightp ((mp m) +:: b)) |<|
  ((cmleftn a) |+| (cmrightp ((mp (n + m)) +:: b))). Admitted.