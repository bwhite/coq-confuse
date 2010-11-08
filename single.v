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

Require Import Arith.
Require Import Coq.Lists.List.

(* Above this line is a set of helper tactics and imports *)

(* POLARITY DEFINITION

   Summary: Given real valued confidence values from a classifier (larger is more confident) on a validation set, we can pair the confidence values with the associated ground truth, sort ascending by confidence, secondary sort by polarity with + coming before - (i.e., + < -), and finally drop the confidence values, leaving the ground truth.

   Facts
   - Polarities are modeled as +=true and -=false.
   - We can break the list L into two parts A B s.t. L = A ++ B.
   - The list may be empty or any any number of +'s and -'s in any order.  This defines a partitioning of the polarities from which a confusion matrix can be computed.
   *)

(* Define simple functions that count the number of true/false polarities in a list. *)
Fixpoint numtrue (x: list bool) : nat :=
  match x with
    | nil => 0
    | true :: t => numtrue t + 1
    | false :: t => numtrue t
  end.

Fixpoint numfalse (x: list bool) : nat :=
  match x with
    | nil => 0
    | true :: t => (numfalse t)
    | false :: t => numfalse t + 1
  end.

Definition move_pol_left_l (n:nat) (a b: list bool): list bool :=
  skipn n a.

Definition move_pol_left_r (n:nat) (a b: list bool): list bool  :=
  (firstn n a) ++ b.

Definition move_pol_right_l (n:nat) (a b: list bool): list bool :=
  (firstn n b) ++ a.

Definition move_pol_right_r (n:nat) (a b: list bool): list bool  :=
  skipn n b.

Lemma numfalse_app_dist : forall (a b: list bool),
numfalse (a ++ b) = (numfalse a) + (numfalse b).
  intros. induction a.
  Case "a = nil".
  induction b.
    SCase "b = nil".
      simpl. reflexivity.
    SCase "b = a :: b".
      simpl. reflexivity.
  Case "a = a :: a0".
      simpl. destruct a.
      SCase "a = true".
        apply IHa.
      SCase "a = false".
        rewrite IHa.  remember (numfalse a0 + numfalse b) as j. rewrite plus_comm. subst. remember (numfalse a0 + 1 ) as j. rewrite plus_comm in Heqj. subst. simpl. reflexivity.
  Qed.

Lemma numtrue_app_dist : forall (a b: list bool),
numtrue (a ++ b) = (numtrue a) + (numtrue b).
  intros. induction a.
  Case "a = nil".
  induction b.
    SCase "b = nil".
      simpl. reflexivity.
    SCase "b = a :: b".
      simpl. reflexivity.
  Case "a = a :: a0".
      simpl. destruct a.
      SCase "a = true".
        rewrite IHa.  remember (numtrue a0 + numtrue b) as j. rewrite plus_comm. subst. remember (numtrue a0 + 1 ) as j. rewrite plus_comm in Heqj. subst. simpl. reflexivity. 
      SCase "a = false".
        apply IHa.
  Qed.

(* This is the form of confusion matrix used [TP, FP, TN, FN]. *)
Inductive confmat: Type :=
  | cm :  nat -> nat -> nat -> nat -> confmat.

Notation "[ a , b , c , d ]" := (cm a b c d).

Definition mkcm (a b:list bool) : confmat :=
  [numtrue b, numfalse b, numfalse a, numtrue a].

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

(* We now define a partial ordering on confusion matrices.  A confusion matrix is less than or equal to another is it has less than or equal TP and TN and greater than or equal FP and FN. *)
Definition cmle (a b: confmat) : Prop :=
  gettp a <= gettp b /\ gettn a <= gettn b /\ getfn b <= getfn a /\ getfp b <= getfp a.

(* Defined as a strict partial order where <= defined a weak partial order *)
Definition cmlt (a b:confmat) : Prop :=
  cmle a b /\ ~(a = b).

Lemma cmle_reflexive: forall (a: confmat),
  cmle a a.
  intros. unfold cmle. auto. Qed.

Lemma cmle_antisymmetry: forall (a b: confmat),
  cmle a b -> cmle b a -> a = b.
  intros. unfold cmle in H. inversion H. inversion H2. inversion H4. clear H4 H H2. unfold cmle in H0. inversion H0. inversion H2. inversion H7. clear H7 H2 H0. remember le_antisym. clear Heqe. apply e in H. apply e in H4.  apply e in H5. apply e in H6. destruct a. destruct b. simpl in H5. simpl in H. simpl in H4. simpl in H6. rewrite H. rewrite H4. rewrite H5. rewrite H6. reflexivity. auto. auto. auto. auto. Qed.

Lemma cmle_transitivity: forall (a b c: confmat),
  cmle a b -> cmle b c -> cmle a c.
  intros. unfold cmle. unfold cmle in H. inversion H. inversion H2. inversion H4. clear H4 H2 H. unfold cmle in H0. inversion H0. inversion H2. inversion H7. clear H0 H2 H7. split.
  Case "gettp a <= gettp c".
    apply le_trans with (m := gettp b). auto. auto.
  split.
  Case "gettp a <= gettp c".
    apply le_trans with (m := gettn b). auto. auto.
  split.
  Case "getfn a <= getfn c".
    apply le_trans with (m := getfn b). auto. auto.
  Case "getfp a <= getfp c".
    apply le_trans with (m := getfp b). auto. auto.
  Qed.

(* Examples of computing confusion matrices from confidence lists *)
Example test_cm0: mkcm (true :: nil) (false :: nil) = [0, 1, 0, 1].
auto.

Example test_cm1: mkcm (false :: nil) (true :: nil) = [1, 0, 1, 0].
auto.

Example test_cm2: mkcm nil (true :: nil) = [1, 0, 0, 0].
auto.

Example test_cm3: mkcm nil nil = [0, 0, 0, 0].
auto.

(* Show the effects of adding a known bool on numtrue and numfalse *)
Lemma numtrue_cons_true: forall (p: list bool), (numtrue p) + 1 = numtrue (true :: p).
auto. Qed.

Lemma numtrue_cons_false: forall (p: list bool), (numtrue p) = numtrue (false :: p).
auto. Qed.

Lemma numfalse_cons_true: forall (p: list bool), (numfalse p) = numfalse (true :: p).
auto. Qed.

Lemma numfalse_cons_false: forall (p: list bool), (numfalse p) + 1 = numfalse (false :: p).
auto. Qed.

(* Given a split list of bools, we 'keep' that split as a representative as long as the first element from the left side isn't true or the first element from the right side isn't false.  The reason for this is if the left is true, we would always prefer that point. *)
Definition keep_cm (a b: list bool) : Prop :=
  match a, b with
    | true :: l, _ => False
    | _, false :: r => False
    | _, _ => True
  end.

Lemma a_plus_1_b_le_b : forall (a b: nat),
  a + 1 + b <= b -> False.
  intros. induction a.
  Case "a = 0".
    simpl in H. apply le_Sn_n in H. apply H.
  Case "S a > 0".
    apply IHa. simpl in H. apply le_Sn_le. apply H.
  Qed.

Lemma keep_test_move_left_morefp : forall (n: nat) (al bl: list bool),
  n > 0 -> numfalse (move_pol_left_r n (false :: al) bl) <= numfalse bl -> False. 
  intros. unfold move_pol_left_r in H0. rewrite numfalse_app_dist in H0. simpl in H0. destruct n.
  Case "n = 0".
    inversion H.
  Case "S n > 0".
    simpl in H0. apply a_plus_1_b_le_b in H0. apply H0.
  Qed.

(* No split to the left will produce a confusion matrix better than this one *)
Lemma keep_test_move_left : forall (n: nat) (al bl: list bool) (cm0 cm1: confmat),
  keep_cm al bl -> cm0 = mkcm al bl -> cm1 = mkcm (move_pol_left_l n al bl) (move_pol_left_r n al bl) ->
  ~ (cmlt cm0 cm1).
unfold not. intros. subst. unfold cmlt in H2. unfold cmle in H2. simpl in H2.
  destruct al.
  Case "al = []".
    inversion H2. unfold not in H1. apply H1. unfold move_pol_left_r. unfold move_pol_left_l. destruct n.
    SCase "n = 0".
      reflexivity.
    SCase "S n > 0".
      reflexivity.
  Case "al = b :: al".
    destruct b.
    SCase "b = true".
      simpl in H. apply H.
    SCase "b = false".
      simpl in H2. inversion H2. destruct n.
      SSCase "n = 0".
        unfold move_pol_left_l in H1. unfold move_pol_left_r in H1. unfold not in H1. apply H1. reflexivity.
      SSCase "S n > 0".
        inversion H0. inversion H4. inversion H6. apply keep_test_move_left_morefp in H8. apply H8. apply gt_Sn_O.
  Qed.


Lemma keep_test_move_right_morefn : forall (n: nat) (al bl: list bool),
  n > 0 -> numtrue (move_pol_right_l n al (true :: bl)) <= numtrue al -> False. 
  intros. unfold move_pol_right_l in H0. rewrite numtrue_app_dist in H0. simpl in H0. destruct n.
  Case "n = 0".
    inversion H.
  Case "S n > 0".
    simpl in H0. apply a_plus_1_b_le_b in H0. apply H0.
  Qed.

(* No split to the right will produce a confusion matrix better than this one *)
Lemma keep_test_move_right : forall (n: nat) (al bl: list bool) (cm0 cm1: confmat),
  keep_cm al bl -> cm0 = mkcm al bl -> cm1 = mkcm (move_pol_right_l n al bl) (move_pol_right_r n al bl) ->
  ~ (cmlt cm0 cm1).
unfold not. intros. subst. unfold cmlt in H2. unfold cmle in H2. simpl in H2.
  destruct bl.
  Case "bl = []".
    inversion H2. unfold not in H1. apply H1. unfold move_pol_right_r. unfold move_pol_right_l. destruct n.
    SCase "n = 0".
      reflexivity.
    SCase "S n > 0".
      reflexivity.
  Case "bl = b :: al".
    destruct b.
    SCase "b = true".
      simpl in H2. inversion H2. inversion H0. inversion H4. inversion H6. destruct n.
      SSCase "n = 0".
        unfold not in H1. unfold move_pol_right_r in H1. unfold move_pol_right_l in H1. simpl in H1. apply H1. reflexivity. 
      SSCase "S n > 0".
        simpl in H1. apply keep_test_move_right_morefn in H7. apply H7. apply gt_Sn_O.
    SCase "b = false".
      destruct al. simpl in H. apply H. simpl in H. destruct b. apply H. apply H.
  Qed.

Theorem keep_test_move_left_right : forall (n: nat) (al bl: list bool) (cm0 cm1 cm2: confmat),
  keep_cm al bl -> cm0 = mkcm al bl -> cm1 = mkcm (move_pol_right_l n al bl) (move_pol_right_r n al bl) -> cm2 = mkcm (move_pol_left_l n al bl) (move_pol_left_r n al bl) ->
  (~ (cmlt cm0 cm1)) /\ (~ (cmlt cm0 cm2)).
  split.
  Case "~ cmlt cm0 cm1".
    apply keep_test_move_right with (al := al) (bl := bl) (n := n). auto. auto. auto.
  Case "~ cmlt cm0 cm2".
    apply keep_test_move_left with (al := al) (bl := bl) (n := n). auto. auto. auto.
  Qed.

(* For any partition that we decide not to keep, there exists a confusion matrix that is strictly better than it *)
Theorem not_keep_test_move_left_right : forall (al bl: list bool) (cm0 cm1 cm2: confmat),
  ~(keep_cm al bl) -> cm0 = mkcm al bl  -> exists n, cm1 = mkcm (move_pol_right_l n al bl) (move_pol_right_r n al bl) -> cm2 = mkcm (move_pol_left_l n al bl) (move_pol_left_r n al bl) ->
  (cmlt cm0 cm2) \/ (cmlt cm0 cm1).
  intros. unfold not in H. subst. destruct al.
  Case "al = []".
    destruct bl.
    SCase "bl = []".
      simpl in H. assert(True). apply I. apply H in H0. inversion H0.
    SCase "bl = b :: bl".
      simpl in H. destruct b.
      SSCase "b = true".
        assert(True). apply I. apply H in H0. inversion H0.
      SSCase "b = false".
        exists 1. right. subst. simpl. unfold cmlt. split. unfold cmle. simpl.  split. auto. split. auto. split. auto. rewrite plus_comm. simpl. apply le_n_Sn. unfold not. intros. inversion H0. 
  Case "al = b :: al".
    destruct b.
    SSCase "b = true".
      exists 1. left. subst. simpl. unfold cmlt. unfold cmle. simpl. split. auto with arith. unfold not. intros. inversion H0. remember n_Sn. unfold not in n. apply n with (n := numtrue bl). rewrite plus_comm in H2. simpl in H2. apply H2.
    SSCase "b = false".
      simpl in H. destruct bl.
      SSSCase "b = true".
        remember I. clear Heqt. apply H in t. inversion t. 
      SSSCase "b = false".
        destruct b. remember I. clear Heqt. apply H in t. inversion t. exists 1. right. subst. simpl. unfold cmlt. split. unfold cmle. simpl.  split. auto. split. rewrite plus_comm. simpl. rewrite plus_comm. simpl. auto. split. auto. rewrite plus_comm. simpl. apply le_n_Sn. unfold not. intros. inversion H0.  rewrite plus_comm in H2. simpl in H2. remember n_Sn. unfold not in n. apply n with (n := numfalse bl). rewrite H2. reflexivity.
  Qed.