From LF Require Export Poly.
Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).
Theorem silly1 : forall (n m o p : nat),
     n = m ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1. rewrite -> eq2. reflexivity.
Qed.

Theorem silly1' : forall (n m o p : nat),
     n = m ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1. apply eq2. 
Qed.

Theorem silly2 : forall (n m o p : nat),
    n = m ->
    (n = m -> [n;o] = [m;p]) ->
    [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. Qed.

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m) ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.

Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 4 = true ->
     oddb 3 = true.
Proof.
  intros eq1 eq2.
  apply eq1. apply eq2. Qed.

Notation "x = y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <= y" := (leb x y) (at level 70) : nat_scope.
Theorem silly3_firsttry : forall (n : nat),
     true = (n = 5) ->
     ((S (S n)) = 7) = true.
Proof.
  intros n H.
  symmetry.
  apply H. Qed.

Print prod.
Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros. induction l. 
  - induction l'.
    + simpl. reflexivity.
    + rewrite -> H. rewrite -> rev_involutive. reflexivity.
  - induction l'.
    + rewrite -> H. rewrite -> rev_involutive. reflexivity.
    + rewrite -> H. rewrite -> rev_involutive. reflexivity.
Qed.

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity. Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with [c;d].
  apply eq1. apply eq2.
Qed.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  apply trans_eq with m.
  apply eq2. apply eq1.
Qed.

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2. rewrite H1. reflexivity.
Qed.

Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H as Hnm. apply Hnm.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  (* 课上已完成 *)
  injection H as H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

Theorem injection_ex2 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  injection H.
  (* 课上已完成 *)
  intros H1 H2. rewrite H1. rewrite H2. reflexivity.
Qed.

Theorem eqb_0_l : forall n,
   ((0 = n) = true) -> n = 0.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    intros H. reflexivity.
  - (* n = S n' *)
    simpl. intros H. discriminate H.
Qed. 

Theorem discriminate_ex1 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. discriminate contra. Qed.
Theorem discriminate_ex2 : forall (n m : nat),
  false = true ->
  [n] = [m].
Proof.
  intros n m contra. discriminate contra. Qed.

Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros. discriminate H.
Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.
Theorem eq_implies_succ_equal : forall (n m : nat),
    n = m -> S n = S m.
Proof. intros n m H. apply f_equal. apply H. Qed.

Theorem eq_implies_succ_equal' : forall (n m : nat),
    n = m -> S n = S m.
Proof. intros n m H. f_equal. apply H. Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
     ((S n) = (S m)) = b ->
     (n = m) = b.
Proof.
  intros n m b H. simpl in H. apply H. Qed.

Theorem silly3' : forall (n : nat),
  ((n = 5) = true -> ((S (S n)) = 7) = true) ->
  true = (n = 5) ->
  true = ((S (S n)) = 7).
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H. Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Theorem double_injective_FAILED: forall n m,
         double n = double m -> n = m.
Proof.
  intros n m. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) discriminate eq.
    + (* m = S m' *) apply f_equal.
Abort.

Theorem double_injective: forall n m,
         double n = double m -> n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) simpl. intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) simpl. discriminate eq.
    + (* m = S m' *)
      apply f_equal. apply IHn'. injection eq as goal. apply goal. 
Qed.

(*  
  - (* n = O *) 
    + (* m = O *) 
    + (* m = S m' *) 
  - (* n = S n' *) 
    + (* m = O *) 
    + (* m = S m' *)
*)
Theorem eqb_true : forall n m,
    (n = m) = true -> n = m.
(*Proof.
  intros n m eq. induction n as [| n' IHn'].
  - (* n = O *) destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *)simpl in eq. discriminate eq.
  - (* n = S n' *) destruct m as [| m'] eqn:E.
    + (* m = O *) simpl in eq. discriminate eq.
    + (* m = S m' *)simpl in eq.
Abort.*)
      
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = O *) intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *)simpl in eq. discriminate eq. 
  - (* n = S n' *) intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) simpl in eq. discriminate eq.
    + (* m = S m' *) simpl in eq. apply IHn' in eq. 
      apply f_equal. apply eq.
Qed. 

Check plus_n_Sm.
(*forall n m : nat, S (n + m) = n + S m*)

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  - (* n = O *) intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) simpl in eq. discriminate eq.
  - (* n = S n' *) intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) simpl in eq. discriminate eq.
    + (* m = S m' *) apply f_equal. apply IHn'. injection eq as goal.
      rewrite <- plus_n_Sm in goal. rewrite <- plus_n_Sm in goal.
      injection goal as Hsm. apply Hsm.
Qed.

Theorem double_injective_take2_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction m as [| m' IHm'].
  - (* m = O *) simpl. intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
        (* 和前面一样，又卡在这儿了。 *)
Abort.

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m.
  (* n and m are both in the context *)
  generalize dependent n.
  (* 现在 n 回到了目标中，我们可以对 m 进行归纳并得到足够一般的归纳假设了。 *)
  induction m as [| m' IHm'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
      apply IHm'. injection eq as goal. apply goal. Qed.

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof.
  intros. generalize dependent n. induction l.
  - simpl. intros. reflexivity.
  - intros. induction n.
    + simpl in H. discriminate H.
    + simpl. apply IHl. simpl in H. injection H as Hsm. apply Hsm.
Qed.

Definition square n := n * n.

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  (* 请在此处解答 *) Admitted.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  (* 请在此处解答 *) Admitted.

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl. unfold square.
  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
    { rewrite mult_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.

Definition foo (x: nat) := 5.

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl. (* 啥也没做！ *)
Abort.

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Definition sillyfun (n : nat) : bool :=
  if (n = 3) then false
  else if (n = 5) then false
  else false.
Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n = 3) eqn:E1.
    - (* n =? 3 = true *) reflexivity.
    - (* n =? 3 = false *) destruct (n = 5) eqn:E2.
      + (* n =? 5 = true *) reflexivity.
      + (* n =? 5 = false *) reflexivity. Qed.

Fixpoint split {X Y : Type} (l : list (X * Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

Lemma tail_eq : forall {X : Type} (x : X) (l1 l2: list X), l1 = l2 -> x :: l1 = x :: l2.
Proof.
  intros. rewrite -> H. reflexivity.
Qed.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.

Proof.
  intros X Y l. induction l. 
  - intros. inversion H. reflexivity.
  - intros. inversion H. destruct x. destruct (split l).
    simpl in H1. inversion H1. simpl. apply tail_eq. apply IHl.
    reflexivity.
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if n = 3 then true
  else if n = 5 then true
  else false.

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n = 3) eqn:Heqe3.
  (* 现在我们的状态和前面卡住的地方一样了，除了上下文中包含了额外的相等关系假设，
     它就是我们继续推进所需要的。 *)
    - (* e3 = true *) apply eqb_true in Heqe3.
      rewrite -> Heqe3. reflexivity.
    - (* e3 = false *)
     (* 当我们到达正在推理的函数体中第二个相等关系测试时，我们可以再次使用
        eqn:，以便结束此证明。 *)
      destruct (n = 5) eqn:Heqe5.
        + (* e5 = true *)
          apply eqb_true in Heqe5.
          rewrite -> Heqe5. reflexivity.
        + (* e5 = false *) discriminate eq. Qed.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros. destruct b.
  - destruct (f true) eqn:eq1.
    + destruct (f true) eqn:eq2.
      * destruct (f true) eqn:eq3.
       -- reflexivity.
       -- discriminate eq2.
      * destruct (f false) eqn:eq4.
       -- reflexivity.
       -- discriminate eq1.
    + destruct (f false) eqn:eq5.
      * destruct (f true) eqn:eq3.
       -- discriminate eq1.
       -- reflexivity.
      * destruct (f false) eqn:eq4.
       -- discriminate eq5.
       -- reflexivity.
  - destruct (f false) eqn:eq1.
    + destruct (f true) eqn:eq2.
      * destruct (f true) eqn:eq3.
       -- reflexivity.
       -- discriminate eq2.
      * destruct (f false) eqn:eq4.
       -- reflexivity.
       -- discriminate eq1.
    + destruct (f false) eqn:eq5.
      * destruct (f true) eqn:eq3.
       -- discriminate eq1.
       -- reflexivity.
      * destruct (f false) eqn:eq4.
       -- discriminate eq5.
       -- reflexivity.
Qed.

Theorem eqb_sym : forall (n m : nat),
  (n = m) = (m = n).
Proof.
  intros n. induction n.
  - intros m. induction m.
    + reflexivity.
    + injection IHm.
  (* 请在此处解答 *) Admitted.











