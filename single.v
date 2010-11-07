Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.


Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Ltac Case name := Case_aux Case name.
Ltac SCase name := Case_aux SCase name.
Ltac SSCase name := Case_aux SSCase name.
Ltac SSSCase name := Case_aux SSSCase name.
Ltac SSSSCase name := Case_aux SSSSCase name.
Ltac SSSSSCase name := Case_aux SSSSSCase name.
Ltac SSSSSSCase name := Case_aux SSSSSSCase name.
Ltac SSSSSSSCase name := Case_aux SSSSSSSCase name.


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


Definition mkcm (a b:polarities) : confmat :=
  [numtrue b, numfalse b, numfalse a, numtrue a].

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
(*
Example test_cm0: mkcm (true :: []) (false :: []) = [0, 1, 0, 1].
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

*)
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

Fixpoint move_pol_right (a b: polarities) (n:nat): (polarities * polarities) :=
  match a, b, n with
    | _, _, O => (a, b)
    | x, z :: y, S n => move_pol_right (z :: x) y n
    | x, y, S n => (a, b)
  end.

Fixpoint move_pol_left_l (n:nat) (a b: polarities): polarities  :=
  match n, a, b with
    | O, _, _ => a
    | S n, z :: x, y => move_pol_left_l n x (z :: y)
    | S n, [], _ => []
  end.

Fixpoint move_pol_left_r (n:nat) (a b: polarities): polarities  :=
  match n, a, b with
    | O, _, _ => b
    | S n, z :: x, y => move_pol_left_r n x (z :: y)
    | S n, [], _ => b
  end.

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
Require Import Arith.
Theorem le_Sn_n : forall n, ~ S n <= n. Admitted.

Theorem test_move_left_part : forall (n: nat) (al bl: polarities),
n > 0 -> ~(numfalse (move_pol_left_r n al (false :: true :: bl)) <= numfalse bl).
  intros. unfold not. intros. induction n. simpl in H0. rewrite plus_comm in H0. remember le_Sn_n as le_Sn_n0. unfold not in le_Sn_n0. apply le_Sn_n0 in H0. apply H0. simpl in H0. 

Theorem test_move_left : forall (n: nat) (al bl: polarities) (a b: bool) (cm0 cm1: confmat),
  a = false -> b = true -> cm0 = mkcm (a :: al) (b :: bl) -> n > 0 -> cm1 = mkcm (move_pol_left_l n (a :: al) (b :: bl)) (move_pol_left_r n (a :: al) (b :: bl)) ->
  ~ (cmle cm0 cm1).
  unfold not. intros. subst. unfold cmle in H4. simpl in H4. inversion H4. inversion H0. inversion H3. destruct n. inversion H2. simpl in H6. induction n. simpl in H6. remember le_Sn_n as H7. unfold not in H7. rewrite plus_comm in H6. simpl in H6. apply H7 in H6. apply H6. simpl in H6. destruct al. simpl in H6. remember le_Sn_n as H7. unfold not in H7. rewrite plus_comm in H6. simpl in H6. apply H7 in H6. apply H6. simpl in H6.

rewrite le_Sn_0 in H6.



  PREV
  intros. subst. simpl. destruct n. 
  Case "n = 0".
    inversion H2.
  Case "S n > 0".
    induction n. destruct al.
      SCase "al = []".
        simpl. unfold cmle. simpl. split. auto. split. auto. split. auto. rewrite plus_comm. apply le_S. auto. 
      SCase "al = b :: al'".
destruct b. simpl. unfold cmle. simpl. split. auto. split. rewrite plus_comm. simpl. auto. split. auto. rewrite plus_comm. simpl. auto. simpl. unfold cmle. simpl. split. auto. split. remember (numfalse al + 1) as b. rewrite plus_comm. simpl. auto. split. auto. rewrite plus_comm. simpl. auto.
 unfold cmle.  simpl. split. simpl. destruct al. simpl. apply le_n. 

Theorem test_move_left_part0: forall (n: nat) (al bl: polarities) (a b: bool) (cm0 cm1: confmat),
move_pol_left_r n al (b :: false :: true :: bl) .

(*  numtrue
     match al with
     | [] => false :: true :: bl
     | z :: x => move_pol_left_r n (z :: false :: true :: bl) x
     end <= numtrue bl + 1 *)

simpl. induction n. destruct al. simpl. apply le_n. simpl. destruct b. simpl.


assert ((move_pol_left_r al (b :: false :: true :: bl) 0) = b :: false :: true :: bl). unfold move_pol_left_r. simpl.

 destruct al. simpl. 

 destruct al. simpl. apply le_n. simpl. induction n. 

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




Lemma cmlt_one_tp: forall (a b: polarities), cmlt (mkcm (true :: a) (b)) (mkcm (a) (true :: b)).
intros. unfold mkcm. simpl. unfold cmlt. split. unfold cmle. simpl.  split. auto with arith. split. apply le_n. split. auto with arith. auto with ari