From Coq Require Export String.
From LF Require Export Basics.


Theorem plus_n_O_firsttry : forall n:nat,
  n = n + 0.

Proof.
  intros n.
  simpl. (* Does nothing! *)
Abort.

Theorem plus_n_O_secondtry : forall n:nat,
  n = n + 0.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    reflexivity. (* 虽然目前还没啥问题... *)
  - (* n = S n' *)
    simpl. (* ...不过我们又卡在这儿了 *)
Abort.


Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  (* 课上已完成 *)
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity. 
Qed.
(*my proof*)
Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  -(* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.
Qed.
(*my proof*)
Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IHn'].
  -(* n = 0 *)
    destruct m as [| m'] eqn:E.
    +(* m = 0 *)
      simpl. reflexivity.
    +(* m = S m' *)
      simpl. reflexivity.
  - (* n = S n' *)
    destruct m as [| m'] eqn:E.
    +(* m = 0 *)
      simpl. rewrite -> IHn'. reflexivity.
    +(* m = S m' *)
      simpl. rewrite -> IHn'. reflexivity.
Qed.
(*my proof*)
Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [| n' IHn'].
  -(* n = 0 *)
    induction m as [| m' IHm'].
    +(* m = 0 *)
      simpl. reflexivity.
    +(* m = S m' *)
      simpl. rewrite <- IHm'. reflexivity.
  - (* n = S n' *)
    induction m as [| m' IHm'].
    +(* m = 0 *)
      simpl. rewrite -> IHn'. reflexivity.
    +(* m = S m' *)
      simpl. rewrite -> IHn'. simpl. rewrite <- plus_n_Sm. reflexivity.
Qed.
(*my proof*)
Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.
(*my proof*)
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.
(*my proof*)
Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n. induction n as [| n' IHn'].
  -(* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. rewrite <- plus_n_Sm. reflexivity.
Qed.
(*my proof*)
Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  intros n. induction n as [| n' IHn'].
  -(* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    rewrite -> IHn'. simpl. rewrite -> negb_involutive. reflexivity.
Qed.

(* 请勿修改下面这一行： *)
Definition manual_grade_for_destruct_induction : option (nat*string) := None.

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity. 
Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Check plus_comm.
(*forall n m : nat, n + m = m + n*)
Proof.
  intros n m p q.
  (* 我们只需要将 (m + n) 交换为 (n + m)... 看起来 plus_comm 能搞定！*)
  rewrite -> plus_comm.
  (* 搞不定... Coq 选错了要改写的加法！ *)
Abort.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity. Qed.

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
  simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity. Qed.
(*my proof*)
Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p. 
  rewrite -> plus_comm.
  assert (H: p+n=n+p). { rewrite -> plus_comm. reflexivity. }
  rewrite <- H. rewrite <- plus_assoc'. reflexivity.
Qed. 

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (p + n).
Proof.
  intros n m p. 
  rewrite -> plus_comm.
  rewrite -> plus_assoc.
  reflexivity.
Qed. 

Theorem plus_swap'' : forall n m p q : nat,
  n + m + (p + q)  = n + p + (m+ q).
Proof.
  intros n m p q.  
  rewrite <- plus_assoc.
  assert (H: m + (p + q) = p + (m + q)). 
  { rewrite -> plus_swap. reflexivity. }
  rewrite -> H. rewrite <- plus_assoc.
  reflexivity.
Qed. 

(* ===> forall n m : nat, n * m + n = n * S m *)

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n.
  induction m as [].
  - induction n as [].
    + reflexivity.
    + simpl. rewrite <- IHn. simpl. 
      reflexivity.
  - induction n as [].
    + simpl. rewrite -> IHm. simpl. 
      reflexivity.
    + simpl. rewrite -> IHm. simpl.
      rewrite <- mult_n_Sm. simpl.
      rewrite -> plus_swap'. reflexivity.
Qed.

Theorem leb_refl : forall n:nat,
  true = (n <= n).
Proof.
  intros n.
  simpl. induction n as []. simpl. 
  reflexivity. simpl. apply IHn.
Qed.
Theorem zero_nbeq_S : forall n:nat,
  (0 = (S n)) = false.
Proof.
  intros n.
  simpl. reflexivity.
Qed.
Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  (* 请在此处解答 *) 
  intros b. destruct b as []. simpl.
  reflexivity. simpl. reflexivity.
Qed.
Theorem plus_ble_compat_l : forall n m p : nat,
  (n <= m) = true -> ((p + n) <= (p + m)) = true.
Proof.
  (* 请在此处解答 *) 
  intros n m p eq. induction p as []. 
  - simpl. rewrite -> eq. reflexivity.
  - simpl. rewrite -> IHp. reflexivity.
Qed.
Theorem S_nbeq_0 : forall n:nat,
  ((S n) = 0) = false.
Proof.
  (* 请在此处解答 *) 
  intros n. simpl. reflexivity. 
Qed.
Theorem mult_1_l :forall n:nat, 1* n = n.
Proof.
  (* 请在此处解答 *) 
  intros n. simpl.
  induction n as []. 
  - simpl. reflexivity.
  - simpl. rewrite -> IHn.
    reflexivity.
Qed.
Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  (* 请在此处解答 *) 
  intros b c.
  destruct b as [].
  - destruct c as [].
    * simpl. reflexivity.
    * simpl. reflexivity.
  - destruct c as [].
    * simpl. reflexivity.
    * simpl. reflexivity.
Qed.

(* mult_n_Sm ===> forall n m : nat, n * m + n = n * S m *)

  
(*  plus_swap'' ===> forall n m p q : nat,
  n + m + (p + q)  = n + p + (m+ q) *)
Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  (* 请在此处解答 *) 
  intros n m p.
  induction p as [].
  - simpl. rewrite <- mult_n_O.
    rewrite -> mult_n_0_m_0.
    reflexivity.
  - simpl. rewrite <- mult_n_Sm. 
    rewrite <- mult_n_Sm. rewrite <- mult_n_Sm.
    rewrite -> IHp. rewrite -> plus_swap''.
    reflexivity.
Qed.
Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  (* 请在此处解答 *) 
  intros n m p.
  rewrite -> mult_comm.
  induction n as [].
  - simpl. rewrite <- mult_n_O.
    reflexivity.
  - simpl. rewrite -> mult_plus_distr_r.
    rewrite <- IHn. rewrite <- mult_n_Sm.
    rewrite <- plus_comm. reflexivity.
Qed.

Theorem eqb_refl : forall n : nat,
  true = (n = n).
Proof.
  (* 请在此处解答 *) 
  intros n. induction n as [].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn. reflexivity.
Qed.

Theorem plus_swap''' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* 请在此处解答 *) 
  intros n m p.
  rewrite -> plus_assoc''.
  rewrite -> plus_assoc''.
  replace (m+n) with (n+m). 
  - reflexivity.
  - rewrite -> plus_comm. reflexivity.
Qed.

Lemma nat_add' : forall n : nat,
  S (n +S (n+0)) = S (S (n+(n+0))).
Proof.
  intros n. rewrite <- plus_n_O.
  rewrite <- plus_n_Sm. reflexivity.
Qed.

Lemma  bin_to_nat_pres_incr : forall b : bin , 
  bin_to_nat (incr b) = S (bin_to_nat b). 
Proof.
  intros b.
  induction b as [].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite -> IHb. simpl.
    rewrite -> nat_add'. reflexivity. 
Qed.

Fixpoint nat_to_bin (n:nat) : bin :=
  (* 将本行替换成 ":= _你的_定义_ ." *) 
  match n with
  |O => Z
  |S n' => incr (nat_to_bin n')
end.

Compute (nat_to_bin 8).

Theorem nat_bin_nat : forall n, 
  bin_to_nat (nat_to_bin n) = n.
Proof.
  (* 请在此处解答 *)
  intros n. induction n as [].
  - simpl. reflexivity. 
  - simpl. rewrite -> bin_to_nat_pres_incr.
    rewrite -> IHn. reflexivity. 
Qed.

Fixpoint normalize (b : bin) : bin := 
  match b with
  |Z=>Z
  |A b' => match normalize b' with
           |Z => Z
           |b'' => A b''
           end
  |B b' => B (normalize b')
end.

Compute (normalize (A (A (A (A Z))))).













