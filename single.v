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
Open Scope list_scope.


(* Polarities are modeled as +=true and -=false *)

(* This is the form of confusion matrix used [TP, FP, TN, FN].  All gets and sets
   must happen through the getters and setters to prevent any ordering errors as
   they will be proven to function properly (prevents proof definition errors). *)
Inductive confmat: Type :=
  | cm :  nat -> nat -> nat -> nat -> confmat.
Notation "[ a , b , c , d ]" := (cm a b c d).

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


Definition mkcm (a b:list bool) : confmat :=
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

Example test_cm0: mkcm (true :: nil) (false :: nil) = [0, 1, 0, 1].
auto.

Example test_cm1: mkcm (false :: nil) (true :: nil) = [1, 0, 1, 0].
auto.

Example test_cm2: mkcm nil (true :: nil) = [1, 0, 0, 0].
auto.

Example test_cm3: mkcm nil nil = [0, 0, 0, 0].
auto.

Lemma numtrue_cons_true: forall (p: list bool), (numtrue p) + 1 = numtrue (true :: p).
auto. Qed.

Lemma numtrue_cons_false: forall (p: list bool), (numtrue p) = numtrue (false :: p).
auto. Qed.

Lemma numfalse_cons_true: forall (p: list bool), (numfalse p) = numfalse (true :: p).
auto. Qed.

Lemma numfalse_cons_false: forall (p: list bool), (numfalse p) + 1 = numfalse (false :: p).
auto. Qed.


Definition cmle (a b: confmat) : Prop :=
  gettp a <= gettp b /\ gettn a <= gettn b /\ getfn b <= getfn a /\ getfp b <= getfp a.

Definition cmlt (a b:confmat) : Prop :=
  cmle a b /\ ~(a = b).

Lemma cmle_same: forall (a b c d: nat), cmle [a, b, c, d] [a, b, c, d].
  intros. unfold cmle. auto. Qed.

Definition move_pol_left_l (n:nat) (a b: list bool): list bool :=
  skipn n a.

Definition move_pol_left_r (n:nat) (a b: list bool): list bool  :=
  (firstn n a) ++ b.

Definition move_pol_right_l (n:nat) (a b: list bool): list bool :=
  (firstn n b) ++ a.

Definition move_pol_right_r (n:nat) (a b: list bool): list bool  :=
  skipn n b.

Theorem numfalse_app_dist : forall (a b: list bool),
numfalse (a ++ b) = (numfalse a) + (numfalse b).
  intros. induction a. induction b. simpl. reflexivity. simpl. reflexivity. simpl. destruct a. apply IHa. rewrite IHa.  remember (numfalse a0 + numfalse b) as j. rewrite plus_comm. subst. remember (numfalse a0 + 1 ) as j. rewrite plus_comm in Heqj. subst. simpl. reflexivity. Qed.


Theorem test_move_left_part0 : forall (n: nat) (al bl: list bool),
~(n + numfalse bl + 1 <= numfalse bl).
  unfold not. intros. induction n. simpl in H. rewrite plus_comm in H. remember le_Sn_n as le_Sn_n. unfold not in le_Sn_n. simpl in H. apply le_Sn_n in H. apply H. simpl in H. apply le_Sn_le in H. apply IHn. apply H. Qed.

Theorem test_move_left : forall (n: nat) (al bl: list bool) (a b: bool) (cm0 cm1: confmat),
  a = false -> b = true -> cm0 = mkcm (a :: al) (b :: bl) -> n > 0 -> cm1 = mkcm (move_pol_left_l n (a :: al) (b :: bl)) (move_pol_left_r n (a :: al) (b :: bl)) ->
  ~ (cmle cm0 cm1).
  unfold not. intros. subst. unfold cmle in H4. simpl in H4. inversion H4. inversion H0. inversion H3. destruct n. inversion H2. simpl in H6. rewrite numfalse_app_dist in H6. simpl in H6. induction n. simpl in H6. rewrite plus_comm in H6. remember le_Sn_n  as le_Sn_n. unfold not in le_Sn_n. simpl in H6. apply le_Sn_n in H6. apply H6. simpl. remember test_move_left_part0 as HH. unfold not in HH. apply HH in H6. apply H6. apply al. Qed.

Theorem numtrue_app_dist : forall (a b: list bool),
numtrue (a ++ b) = (numtrue a) + (numtrue b).
  intros. induction a. induction b. simpl. reflexivity. simpl. reflexivity. simpl. destruct a. rewrite IHa.  remember (numtrue a0 + numtrue b) as j. rewrite plus_comm. subst. remember (numtrue a0 + 1 ) as j. rewrite plus_comm in Heqj. subst. simpl. reflexivity. apply IHa. Qed.

Theorem test_move_right_part0 : forall (n: nat) (al bl: list bool),
~(n + numtrue bl + 1 <= numtrue bl).
  unfold not. intros. induction n. simpl in H. rewrite plus_comm in H. remember le_Sn_n as le_Sn_n. unfold not in le_Sn_n. simpl in H. apply le_Sn_n in H. apply H. simpl in H. apply le_Sn_le in H. apply IHn. apply H. Qed.


Theorem test_move_right : forall (n: nat) (al bl: list bool) (a b: bool) (cm0 cm1: confmat),
  a = false -> b = true -> cm0 = mkcm (a :: al) (b :: bl) -> n > 0 -> cm1 = mkcm (move_pol_right_l n (a :: al) (b :: bl)) (move_pol_right_r n (a :: al) (b :: bl)) ->
  ~ (cmle cm0 cm1).
  unfold not. intros. subst. unfold cmle in H4. simpl in H4. inversion H4. inversion H0. inversion H3. destruct n. inversion H2. simpl in H5. rewrite numtrue_app_dist in H5. simpl in H5. induction n. simpl in H5. rewrite plus_comm in H5. remember le_Sn_n  as le_Sn_n. unfold not in le_Sn_n. simpl in H5. apply le_Sn_n in H5. apply H5. simpl. remember test_move_right_part0 as HH. unfold not in HH. apply HH in H5. apply H5. apply al. Qed.



Definition keep_cm (a b: list bool) : Prop :=
  match a, b with
    | true :: l, _ => False
    | _, false :: r => False
    | _, _ => True
  end.

Theorem a_plus_1_b_le_b : forall (a b: nat),
  a + 1 + b <= b -> False.
  intros. induction a.
  Case "a = 0".
    simpl in H. apply le_Sn_n in H. apply H.
  Case "S a > 0".
    apply IHa. simpl in H. apply le_Sn_le. apply H.
  Qed.

Theorem keep_test_move_left_part0 : forall (n: nat) (al bl: list bool),
  n > 0 -> numfalse (move_pol_left_r n (false :: al) bl) <= numfalse bl -> False. 
  intros. unfold move_pol_left_r in H0. rewrite numfalse_app_dist in H0. simpl in H0. destruct n.
  Case "n = 0".
    inversion H.
  Case "S n > 0".
    simpl in H0. apply a_plus_1_b_le_b in H0. apply H0.
  Qed.

(* No split to the left will produce a confusion matrix better than this one *)
Theorem keep_test_move_left : forall (n: nat) (al bl: list bool) (cm0 cm1: confmat),
  keep_cm al bl -> cm0 = mkcm al bl -> n > 0 -> cm1 = mkcm (move_pol_left_l n al bl) (move_pol_left_r n al bl) ->
  ~ (cmlt cm0 cm1).
unfold not. intros. subst. unfold cmlt in H3. unfold cmle in H3. simpl in H3.
  destruct al.
  Case "al = []".
    inversion H3. unfold not in H2. apply H2. unfold move_pol_left_r. unfold move_pol_left_l. destruct n.
    SCase "n = 0".
      reflexivity.
    SCase "S n > 0".
      reflexivity.
  Case "al = b :: al".
    destruct b.
    SCase "b = true".
      simpl in H. apply H.
    SCase "b = false".
      simpl in H3. inversion H3. inversion H0. inversion H5. inversion H7. apply keep_test_move_left_part0 in H9. apply H9. apply H1.
  Qed.

Theorem keep_test_move_right_part0 : forall (n: nat) (al bl: list bool),
  n > 0 -> numtrue (move_pol_right_l n al (true :: bl)) <= numtrue al -> False. 
  intros. unfold move_pol_right_l in H0. rewrite numtrue_app_dist in H0. simpl in H0. destruct n.
  Case "n = 0".
    inversion H.
  Case "S n > 0".
    simpl in H0. apply a_plus_1_b_le_b in H0. apply H0.
  Qed.

(* No split to the right will produce a confusion matrix better than this one *)
Theorem keep_test_move_right : forall (n: nat) (al bl: list bool) (cm0 cm1: confmat),
  keep_cm al bl -> cm0 = mkcm al bl -> n > 0 -> cm1 = mkcm (move_pol_right_l n al bl) (move_pol_right_r n al bl) ->
  ~ (cmlt cm0 cm1).
unfold not. intros. subst. unfold cmlt in H3. unfold cmle in H3. simpl in H3.
  destruct bl.
  Case "bl = []".
    inversion H3. unfold not in H2. apply H2. unfold move_pol_right_r. unfold move_pol_right_l. destruct n.
    SCase "n = 0".
      reflexivity.
    SCase "S n > 0".
      reflexivity.
  Case "bl = b :: al".
    destruct b.
    SCase "b = true".
      simpl in H3. inversion H3. inversion H0. inversion H5. inversion H7. apply keep_test_move_right_part0 in H8. apply H8. apply H1.
    SCase "b = false".
      destruct al. simpl in H. apply H. simpl in H. destruct b. apply H. apply H.
  Qed.

(* This is the proof that every confusion matrix generated corresponding to a partition accepted by keep_cm is not strictly less than another other confusion matrix (where less than is defined in cmlt) *)
Theorem keep_test_move_left_right : forall (n: nat) (al bl: list bool) (cm0 cm1 cm2: confmat),
  keep_cm al bl -> cm0 = mkcm al bl -> n > 0 -> cm1 = mkcm (move_pol_right_l n al bl) (move_pol_right_r n al bl) -> cm2 = mkcm (move_pol_left_l n al bl) (move_pol_left_r n al bl) ->
  (~ (cmlt cm0 cm1)) /\ (~ (cmlt cm0 cm2)).
split. apply keep_test_move_right with (al := al) (bl := bl) (n := n). auto. auto. auto. auto. apply keep_test_move_left with (al := al) (bl := bl) (n := n). auto. auto. auto. auto. Qed.