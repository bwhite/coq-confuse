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
  

(* These functions maximally split a list into one part with the specified polarity, and the other part with the rest of the list *)
Fixpoint split_true_l (x: list bool) : list bool :=
  match x with
    | nil => nil
    | true :: t => true :: split_true_l t
    | false :: t => nil
  end.

Fixpoint split_true_r (x: list bool) : list bool :=
  match x with
    | nil => nil
    | true :: t => split_true_r t
    | false :: t => false :: t
  end.

Fixpoint split_false_l (x: list bool) : list bool :=
  match x with
    | nil => nil
    | true :: t => nil
    | false :: t => false :: split_false_l t
  end.

Fixpoint split_false_r (x: list bool) : list bool :=
  match x with
    | nil => nil
    | true :: t => true :: t
    | false :: t => split_false_r t
  end.

Lemma numfalse_split_false_r_le: forall (l : list bool),
  numfalse (split_false_r l) <= numfalse l.
  intros. induction l. auto. simpl. destruct a. auto. rewrite plus_comm. simpl. auto. Qed.

Hint Resolve numfalse_split_false_r_le.

Lemma numtrue_split_true_r_le: forall (l : list bool),
  numtrue (split_true_r l) <= numtrue l.
  intros. induction l. auto. simpl. destruct a. rewrite plus_comm. simpl. auto. auto. Qed.

Hint Resolve numtrue_split_true_r_le.


Lemma split_false_l_false_head_tail: forall (a: list bool),
split_false_l a ++ false :: nil = false :: split_false_l a.
  intros. induction a. auto. destruct a. auto. simpl. rewrite IHa. reflexivity. Qed.

(* As the split on the left is always the same boolean value, we can move an element from the front to the back *)
Lemma split_true_l_true_head_tail: forall (a: list bool),
split_true_l a ++ true :: nil = true :: split_true_l a.
  intros. induction a. auto. destruct a. simpl. rewrite IHa. reflexivity.  auto. Qed.

Lemma split_true_l_false_head_tail: forall (a: list bool),
split_false_l a ++ false :: nil = false :: split_false_l a.
  intros. induction a. auto. destruct a. auto. simpl. rewrite IHa. reflexivity. Qed.

(* As the split on the left is always the same boolean value, we can reverse the list *)
Lemma split_false_l_rev: forall (a : list bool),
rev (split_false_l a) = split_false_l a.
  intros. induction a. reflexivity. simpl. destruct a. reflexivity. simpl. rewrite IHa. apply split_false_l_false_head_tail. Qed.

Hint Resolve split_false_l_rev.

Lemma split_true_l_rev: forall (a : list bool),
rev (split_true_l a) = split_true_l a.
  intros. induction a. reflexivity. simpl. destruct a. simpl. rewrite IHa. apply split_true_l_true_head_tail. reflexivity. Qed.

Hint Resolve split_true_l_rev.

Lemma numtrue_split_false_l: forall (l: list bool),
numtrue (split_false_l l) = 0.
  intros. induction l. auto. simpl. destruct a; auto. Qed.

Hint Resolve numtrue_split_false_l.

Lemma numfalse_split_true_l: forall (l: list bool),
numfalse (split_true_l l) = 0.
  intros. induction l. auto. simpl. destruct a; auto. Qed.

Hint Resolve numtrue_split_false_l.

Definition move_pol_left_l (n:nat) (a b: list bool): list bool :=
  skipn n a.

Hint Unfold move_pol_left_l.

Definition move_pol_left_r (n:nat) (a b: list bool): list bool  :=
  (rev (firstn n a)) ++  b.

Hint Unfold move_pol_left_r.

Definition move_pol_right_l (n:nat) (a b: list bool): list bool :=
  (rev (firstn n b)) ++  a.

Hint Unfold move_pol_right_l.

Definition move_pol_right_r (n:nat) (a b: list bool): list bool  :=
  skipn n b.

Hint Unfold move_pol_right_r.

(* Lemma rev_app_distr : forall x y: (list bool), rev (x ++ y) = rev y ++ rev x. Admitted.

Lemma list_app_dist : forall x y z: (list bool), x ++ y ++ z = (x ++ y) ++ z. Admitted.

Lemma move_left_test: forall (n: nat) (a b: list bool),
  (rev a) ++ b = (rev (move_pol_left_l n a b)) ++ (move_pol_left_r n a b).
  intros. unfold move_pol_left_l. unfold move_pol_left_r.  rewrite list_app_dist. rewrite <- rev_app_distr. rewrite firstn_skipn. reflexivity. Qed.
*)
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
Hint Unfold gettp getfp gettn getfn.

(* We now define a partial ordering on confusion matrices.  A confusion matrix is less than or equal to another is it has less than or equal TP and TN and greater than or equal FP and FN. *)
Definition cmle (a b: confmat) : Prop :=
  gettp a <= gettp b /\ gettn a <= gettn b /\ getfn b <= getfn a /\ getfp b <= getfp a.

Hint Unfold cmle.

(* Defined as a strict partial order where <= defined a weak partial order *)
Definition cmlt (a b:confmat) : Prop :=
  cmle a b /\ ~(a = b).

Hint Unfold cmlt.

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

Lemma cmlt_irreflexive: forall (a: confmat),
  ~ (cmlt a a).
  unfold not. intros. unfold cmlt in H. inversion H. unfold not in H1. apply H1. reflexivity. Qed.

Lemma cmlt_asymmetry: forall (a b: confmat),
  cmlt a b -> ~ (cmlt b a).
  unfold not. intros. unfold cmlt in H. unfold cmlt in H0. inversion H. inversion H0. clear H H0. unfold not in H2. unfold not in H4. unfold cmle in H1. unfold cmle in H3. destruct a. destruct b. simpl in H1. simpl in H3. apply H2.  inversion H1. inversion H0. inversion H6. clear H1 H0 H6. inversion H3. inversion H1. inversion H9. clear H3 H1 H9. remember le_antisym. clear Heqe. apply e in H. apply e in H5. apply e in H8. apply e in H10. rewrite H10. rewrite H8. rewrite H5. rewrite H. reflexivity. auto. auto. auto. auto. Qed.

Lemma cmlt_transitivity: forall (a b c: confmat),
  cmlt a b -> cmlt b c -> cmlt a c.
  unfold cmlt. unfold cmle. destruct a. destruct b. destruct c. unfold not. simpl. intros. inversion H. inversion H1. inversion H4. inversion H6. clear H H1 H4 H6. inversion H0. inversion H. inversion H6. inversion H10. clear H0 H H6 H10. split. 
  Case "<=".
    split.
    SCase "0".
      apply le_trans with (m := n3). auto. auto.
    split.
    SCase "1".
      apply le_trans with (m := n5). auto. auto.
    split.
    SCase "2".
      apply le_trans with (m := n6). auto. auto.
    SCase "3".
      apply le_trans with (m := n4). auto. auto.
  Case "!=".
    intros. remember le_antisym. clear Heqe. apply e in H3. rewrite H3 in H1. apply e in H8. rewrite <- H8 in H1. apply e in H5. rewrite H5 in H1. apply e in H7. rewrite <- H7 in H1. apply H1 in H. apply H. inversion H. auto. inversion H. auto. inversion H. auto. inversion H. auto.
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

Lemma numfalse_tail_false_plus_1: forall (l: list bool),
  numfalse (l ++ false :: nil) = numfalse l + 1.
  intros. induction l. auto. simpl. destruct a; auto. Qed.

Lemma numtrue_tail_true_plus_1: forall (l: list bool),
  numtrue (l ++ true :: nil) = numtrue l + 1.
  intros. induction l. auto. simpl. destruct a; auto. Qed.


Lemma keep_test_move_left_morefp : forall (n: nat) (al bl: list bool),
  n > 0 -> numfalse (move_pol_left_r n (false :: al) bl) <= numfalse bl -> False. 
  intros. unfold move_pol_left_r in H0.  rewrite numfalse_app_dist in H0. simpl in H0. destruct n.
  Case "n = 0".
    inversion H.
  Case "S n > 0".
    simpl in H0.  rewrite numfalse_tail_false_plus_1 in H0. apply a_plus_1_b_le_b in H0. auto.
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
    simpl in H0. rewrite numtrue_tail_true_plus_1 in H0. apply a_plus_1_b_le_b in H0. auto.
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

(* For any partition that we decide to keep, there is no confusion matrix strictly better than it *)
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

(* Simple theorems that aren't built into coq *)

Lemma a_le_b_a_1: forall (a b: nat),
  a <= b + a + 1.
  intros. induction b. simpl. rewrite plus_comm. simpl. auto. simpl. auto. Qed.

Hint Resolve a_le_b_a_1.

Lemma a_le_a_b_1: forall (a b: nat),
  a <= a + (b + 1).
  intros. rewrite plus_assoc. induction b. rewrite plus_comm. simpl. rewrite plus_comm. simpl. auto. rewrite plus_comm.  simpl. rewrite plus_comm. simpl. rewrite plus_comm in IHb. simpl in IHb. rewrite plus_comm in IHb. auto. Qed.
Qed.

Hint Resolve a_le_a_b_1.


Lemma a_plus_0_le: forall (a: nat),
a + 0 <= a.
  intros. rewrite plus_comm. auto. Qed.

Hint Resolve a_plus_0_le.

Lemma left_is_kept_and_better: forall (bl al' al alh alt blh blt: list bool) (cml cmr: list bool) (cm0 cm1: confmat),
  al = true :: al' -> cm0 = mkcm al bl ->
  alh = split_true_l al -> alt = split_true_r al -> cml = alt -> cmr = alh ++ bl -> cm1 = mkcm cml cmr -> keep_cm cml cmr /\ cmlt cm0 cm1.
  intros. split.
  Case "keep_cm cml cmr".
    destruct al'.
    SCase "al' = nil".
      subst. simpl. apply I.
    SCase "al' = b :: al'".
      destruct b.
      SSCase "al' = true :: al'".
        subst. simpl. induction al'.
        SSSCase "al' = nil".
          simpl. apply I.
        SSSCase "al' = a :: al'".
          destruct a.
          SSSSCase "al' = true :: al'".
            simpl. apply IHal'.
          SSSSCase "al' = false :: al'".
            simpl. apply I.
      SSCase "al' = false :: al'".
        subst. simpl. apply I.
  Case "cmlt cm0 cm1".
    subst. simpl. split.
    SCase "cmle".
      unfold cmle. simpl. split. rewrite numtrue_app_dist. apply a_le_b_a_1. split. induction al'. auto. simpl. destruct a. auto. simpl. auto. split. induction al'. simpl. auto. simpl. destruct a. auto with arith. auto with arith. rewrite numfalse_app_dist. induction al'. auto. simpl. destruct a. auto with arith. auto with arith.
    SCase "<>".
      unfold not. intros. inversion H. rewrite numtrue_app_dist in H1. rewrite plus_comm in H1. simpl in H1. remember succ_plus_discr. clear Heqn. unfold not in n. apply n in H1. apply H1.
  Qed.  

Lemma numtrue_le_split_false_r: forall (l : list bool),
numtrue l <= numtrue (split_false_r l).
  intros. induction l. auto. simpl. destruct a. auto. auto. Qed.

Hint Resolve numtrue_le_split_false_r.

Lemma right_is_kept_and_better: forall (bl bl' al alh alt blh blt: list bool) (cml cmr: list bool) (cm0 cm1: confmat),
  bl = false :: bl' -> cm0 = mkcm al bl ->
  blh = split_false_l bl -> blt = split_false_r bl -> cml = (rev blh) ++ al -> cmr = blt -> cm1 = mkcm cml cmr -> keep_cm cml cmr /\ cmlt cm0 cm1.
  intros. split.
  Case "keep_cm cml cmr".
    destruct bl'.
    SCase "bl' = nil".
      subst. simpl. apply I.
    SCase "bl' = b :: bl'".
      destruct b.
      SSCase "bl' = true :: al'".
        subst. simpl. apply I.
      SSCase "bl' = false :: bl'".
        subst. simpl. rewrite split_false_l_rev. rewrite split_false_l_false_head_tail. simpl. induction bl'.
        SSSCase "bl' = nil".
          apply I.
        SSSCase "bl' = a :: bl'".
          destruct a.
          SSSSCase "bl' = true :: bl'".
            apply I.
          SSSSCase "bl' = false :: bl'".
            simpl. apply IHbl'.
  Case "cmlt cm0 cm1".
    subst. simpl. split.
    SCase "cmle".
      unfold cmle. simpl. split. auto. split. rewrite numfalse_app_dist. rewrite plus_comm. rewrite split_false_l_rev. rewrite numfalse_app_dist. simpl. apply a_le_a_b_1. split.  rewrite split_false_l_rev. rewrite numtrue_app_dist. rewrite numtrue_app_dist. simpl. rewrite numtrue_split_false_l. auto. rewrite plus_comm. simpl. auto.
    SCase "<>".
      unfold not. intros. inversion H. rewrite numfalse_app_dist in H3. rewrite plus_comm in H3. simpl in H3. remember succ_plus_discr. clear Heqn. unfold not in n.  rewrite split_false_l_rev in H3. rewrite split_true_l_false_head_tail in H3. simpl in H3. rewrite plus_assoc in H3. rewrite plus_comm in H3. simpl in H3. rewrite plus_comm in H3. apply n in H3. apply H3.
  Qed.
          
Lemma not_true: ~ True -> False.
  unfold not. intros. remember I. clear Heqt. apply H in t. apply t. Qed.

Lemma something_is_kept_and_better: forall (bl al' bl' al alh alt blh blt: list bool) (cm1l cm1r cm2l cm2r: list bool) (cm0 cm1 cm2: confmat),
  ~(keep_cm al bl) -> cm0 = mkcm al bl -> cm1 = mkcm cm1l cm1r -> cm2 = mkcm cm2l cm2r ->
  blh = split_false_l bl -> blt = split_false_r bl -> cm1l = (rev blh) ++ al -> cm1r = blt ->
  alh = split_true_l al -> alt = split_true_r al -> cm2l = alt -> cm2r = (rev alh) ++ bl ->
  keep_cm cm1l cm1r /\ cmlt cm0 cm1 \/ keep_cm cm2l cm2r /\ cmlt cm0 cm2.
  simpl. intros. destruct al.
  Case "al = nil".
    destruct bl.
    SCase "bl = nil".
      apply not_true in H. inversion H.
    SCase "bl = b :: bl".
      destruct b.
      SSCase "bl = true :: bl".
        apply not_true in H. inversion H.
      SSCase "bl = false :: bl".
        left. apply right_is_kept_and_better with (bl := false :: bl) (bl' := bl) (al := nil) (blh := blh) (blt := blt); auto.
  Case "al = b :: al".
    destruct b.
    SCase "al = true :: al".
      right. apply left_is_kept_and_better with (al := true :: al) (al' := al) (bl := bl) (alh := alh) (alt := alt); auto. subst. rewrite split_true_l_rev. auto.
    SCase "al = false :: al".
      destruct bl. 
      SSCase "bl = nil".
        apply not_true in H. inversion H.
      SSCase "bl = b :: bl".
        destruct b.
        SSSCase "bl = true :: bl".
          apply not_true in H. inversion H.
        SSSCase "bl = true :: bl".
          left. apply right_is_kept_and_better with (bl := false :: bl) (bl' := bl) (al := false :: al) (blh := blh) (blt := blt); auto.
  Qed.

Lemma keep_cm_is_necessary_and_sufficient: forall (bl al' bl' al alh alt blh blt: list bool) (cm1l cm1r cm2l cm2r: list bool) (cm0 cm1 cm2 cm3 cm4: confmat) (n: nat),
  cm0 = mkcm al bl ->
  cm1 = mkcm cm1l cm1r ->
  cm2 = mkcm cm2l cm2r ->
  cm3 = mkcm (move_pol_right_l n al bl) (move_pol_right_r n al bl) ->
  cm4 = mkcm (move_pol_left_l n al bl) (move_pol_left_r n al bl) ->
  blh = split_false_l bl -> blt = split_false_r bl -> cm1l = (rev blh) ++ al -> cm1r = blt ->
  alh = split_true_l al -> alt = split_true_r al -> cm2l = alt -> cm2r = (rev alh) ++ bl ->
  (keep_cm al bl /\ (~ cmlt cm0 cm3) /\ (~ cmlt cm0 cm4)) \/
  (~ keep_cm al bl /\ ((keep_cm cm1l cm1r /\ cmlt cm0 cm1) \/ (keep_cm cm2l cm2r /\ cmlt cm0 cm2))).
  intros. destruct al.
  Case "al = nil".
    destruct bl.
    SCase "bl = nil".
      left. simpl. split. auto. apply keep_test_move_left_right with (n := n) (al := nil) (bl := nil); simpl; auto.
    SCase "bl = b :: bl".
      destruct b.
      SSCase "bl = true :: bl".
        left. simpl. split. auto. apply keep_test_move_left_right with (n := n) (al := nil) (bl := true :: bl); simpl; auto.
      SSCase "bl = false :: bl".
        right. simpl. split. auto. apply something_is_kept_and_better with (bl := false :: bl) (al := nil) (alh := nil) (alt := nil) (blh := blh) (blt := blt); subst; simpl; auto. simpl.
 Case "al = b :: al".
   destruct b.
   SCase "al = true :: al".
     right. simpl. split. auto. apply something_is_kept_and_better with (bl := bl) (al := true :: al) (alh := alh) (alt := alt) (blh := blh) (blt := blt); subst; simpl; auto.
   SCase "al = false :: al".
     destruct bl.
     SSCase "bl = nil".
        left. simpl. split. auto. apply keep_test_move_left_right with (n := n) (al := false :: al) (bl := nil); simpl; auto.
     SSCase "bl = b :: bl".
       destruct b.
       SSSCase "bl = true :: bl".
         left. simpl. split. auto. apply keep_test_move_left_right with (n := n) (al := false :: al) (bl := true :: bl); simpl; auto.
       SSSCase "bl = false :: bl".
         right. simpl. split. auto. apply something_is_kept_and_better with (bl := false :: bl) (al := false :: al) (alh := alh) (alt := alt) (blh := blh) (blt := blt); subst; simpl; auto.
  Qed.


Hint Resolve split.
Hint Unfold not.
Example test_cmlt0: cmlt [0, 2, 0, 0] [2, 0, 0, 0].
unfold cmlt. split. auto with arith. unfold not. intros. inversion H. Qed.

Example test_cmlt1: cmlt [0, 0, 0, 2] [2, 0, 0, 0].
unfold cmlt. split. auto with arith. unfold not. intros. inversion H. Qed.


(* |-++ < -|++ *)
Example test_mvpol_right0:
forall x a b, x = false :: true :: true :: nil ->
a = move_pol_right_l 1 nil x ->
b = move_pol_right_r 1 nil x ->
cmlt (mkcm nil x) (mkcm a b).
intros. subst.  unfold cmlt. split. auto with arith. unfold not. intros. inversion H. Qed.
Recursive Extraction numtrue numfalse split_true_l split_true_r split_false_l split_false_r move_pol_left_l move_pol_left_r move_pol_right_l move_pol_right_r mkcm gettp getfp gettn getfn cmle cmlt keep_cm.