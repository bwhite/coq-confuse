

(* Polarities are modeled as +=true and -=false *)
Inductive polarities : Type :=
| nilpol : polarities
| conspol : bool -> polarities -> polarities.

Notation "x :: l" := (conspol x l) (at level 60, right associativity).
Notation "[]" := nilpol.

(* This is the form of confusion matrix used [TP, FP, TN, FN].  All gets and sets
   must happen through the getters and setters to prevent any ordering errors as
   they will be proven to function properly (prevents proof definition errors). *)
Inductive confmat: Type :=
  | cm :  nat -> nat -> nat -> nat -> confmat.
Notation "[ a , b , c , d ]" := (cm a b c d).

Fixpoint numtrue (x: polarities) : nat :=
  match x with
    | nilpol => 0
    | true :: t => numtrue t + 1
    | false :: t => numtrue t
  end.

Fixpoint numfalse (x: polarities) : nat :=
  match x with
    | nilpol => 0
    | true :: t => (numfalse t)
    | false :: t => numfalse t + 1
  end.


Definition mkcm (a:(polarities * polarities)) : confmat :=
  match a with
    (x, y) =>[numtrue y, numfalse y, numfalse x, numtrue x]
  end.

Definition settp (x:confmat) (y:nat) : confmat :=
  match x with
    | [a, b, c, d] => [y, b, c, d]
  end.

Definition setfp (x:confmat) (y:nat) : confmat :=
  match x with
    | [a, b, c, d] => [a, y, c, d]
  end.

Definition settn (x:confmat) (y:nat) : confmat :=
  match x with
    | [a, b, c, d] => [a, b, y, d]
  end.

Definition setfn (x:confmat) (y:nat) : confmat :=
  match x with
    | [a, b, c, d] => [a, b, c, y]
  end.

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

Example test_cm0: mkcm ((true :: []), (false :: [])) = [0, 1, 0, 1].
auto.

Example test_cm1: mkcm ((false :: []), (true :: [])) = [1, 0, 1, 0].
auto.

Example test_cm2: mkcm ([], (true :: [])) = [1, 0, 0, 0].
auto.

Example test_cm3: mkcm ([], []) = [0, 0, 0, 0].
auto.

Lemma numtrue_cons_true: forall (p: polarities), (numtrue p) + 1 = numtrue (true :: p).
auto. Qed.

Lemma numtrue_cons_false: forall (p: polarities), (numtrue p) = numtrue (false :: p).
auto. Qed.

Lemma numfalse_cons_true: forall (p: polarities), (numfalse p) = numfalse (true :: p).
auto. Qed.

Lemma numfalse_cons_false: forall (p: polarities), (numfalse p) + 1 = numfalse (false :: p).
auto. Qed.


Definition cmle (a b: confmat) : Prop :=
  gettp a <= gettp b /\ gettn a <= gettn b /\ getfn b <= getfn a /\ getfp b <= getfp a.

Definition cmlt (a b:confmat) : Prop :=
  cmle a b /\ ~(a = b).

Lemma cmle_same: forall (a b c d: nat), cmle [a, b, c, d] [a, b, c, d].
  intros. unfold cmle. auto. Qed.

Definition nexttrue (x: polarities) : bool :=
  match x with
    | nilpol => false
    | true :: t => true
    | false :: t => false
  end.

Definition nextfalse (x: polarities) : bool :=
  match x with
    | nilpol => false
    | true :: t => false
    | false :: t => true
  end.

Definition keep_cm (a: (polarities * polarities)) : Prop :=
  match a with
    | (true :: l, _) => False
    | (_, false :: r) => False
    | _ => True
  end.


Fixpoint split_polarity_rec (a b: polarities) (n:nat): (polarities * polarities) :=
  match a, b, n with
    | _, _, O => (a, b)
    | x, z :: y, S n => split_polarity_rec (z :: x) y n
    | x, y, S n => (a, b)
  end.

Definition split_polarity (a: polarities) (y:nat): (polarities * polarities) :=
  split_polarity_rec [] a y.


Definition keep_cm2 (a: (polarities * polarities)) : Prop :=
  match a with
    | (false :: _, true :: _) => True
    | _ => False
  end.

Fixpoint join_polarities (a b: polarities): polarities :=
  match a, b with
    | x :: xs, ys =>  join_polarities xs (x :: ys)
    | [], ys => ys
  end.

Theorem test_split_pol : forall (n: nat) (al bl : polarities) (a b: bool),
  keep_cm2 (a :: al, b :: bl) -> a = false /\ b = true.
  intros. split. unfold keep_cm2 in H.  destruct a. inversion H. destruct b. reflexivity. reflexivity.  destruct b. reflexivity. simpl in H. destruct a. inversion H. inversion H. Qed.

(* I think the way to do this right is to start with two sets of polarities and have a left slider function and a right slider function, showing that the results for each of these things shows that the current split is best *)
Theorem test_split_pol2 : forall (n m: nat) (al bl: polarities) (a b: bool),
  keep_cm2 (a :: al, b :: bl) -> a = false -> b = true -> split_polarity p m = (a :: al, b :: bl) -> cmle (mkcm (split_polarity p n)) (mkcm (a :: al, b :: bl)).
  intros.  subst. simpl. induction n. unfold split_polarity. destruct p. simpl. admit. destruct b. simpl.

induction n. unfold mkcm. unfold split_polarity. simpl.

apply test_split_pol in H. admit. 

simpl. inversion H.


  keep_cm2 (split_polarity p n) -> cmle (mkcm (split_polarity p n)) (mkcm (split_polarity p m)).
  intros. unfold keep_cm2 in H. simpl in H.


Theorem test_split_pol : forall (n m: nat) (p : polarities),
  keep_cm (split_polarity p n) -> cmle (mkcm (split_polarity p n)) (mkcm (split_polarity p m)).
  intros. destruct p. induction n. induction m. simpl. apply cmle_same. simpl. apply cmle_same. simpl.

  intros. induction n. unfold cmle. 



Theorem test_split_pol0 : forall (n : nat) (p : polarities), p = (false :: false :: true :: true :: []) -> cmle (mkcm (split_polarity p n)) (mkcm (split_polarity p 2)).
Proof.
intros. rewrite H. simpl. destruct n. simpl. unfold cmle. simpl. split. auto. split. auto. split. auto. auto. unfold split_polarity. simpl. destruct n. simpl. unfold cmle. split. simpl. auto. split. simpl. auto. split. simpl. auto. simpl. auto. simpl. destruct n. simpl. unfold cmle. split. simpl. auto. split. simpl. auto. split. auto. auto. simpl. destruct n. simpl. unfold cmle. split. simpl. auto. split. simpl. auto. split. simpl. auto. simpl. auto. simpl. destruct n. simpl. unfold cmle. split. simpl. auto. split. auto. split. simpl. auto. auto. simpl. unfold cmle. split. simpl. auto. split. simpl. auto. split. simpl. auto. simpl. auto. Qed.



  intro. intro. intro.


  unfold keep_cm. intro. intro. intro. intro. unfold cmle.
  intros. unfold keep_cm in H. 


p = (false :: false :: true :: true :: []) -> cmle (mkcm (split_polarity p n)) (mkcm (split_polarity p 2)).

(* Show that keep_cm is only true in our listed cases *)

(* Show that if keep_cm is true, then the confusion matrix from it is not less than or equal to any other in the list *)


Require Import Arith.

Lemma cmlt_one_tp: forall (a b: polarities), cmlt (mkcm (true :: a) (b)) (mkcm (a) (true :: b)).
intros. unfold mkcm. simpl. unfold cmlt. split. unfold cmle. simpl.  split. auto with arith. split. apply le_n. split. auto with arith. auto with ari