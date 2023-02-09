From Coq Require Export String.

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Compute (next_weekday friday).

Compute (next_weekday (next_weekday friday)).

Example test1:
(next_weekday (next_weekday friday)) = tuesday.
Proof.
simpl. reflexivity.
Qed.

Inductive bool : Type :=
  | true
  | false.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.
Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1:
  (orb true false) = true.
Proof.
simpl. reflexivity.
Qed.
(*dasda[Notation "x || y" := (orb x y).]sd*)
Notation "x || y" := (orb x y).
(*hello*)
Example test_orb2:
  (true || false) = true.
Proof.
simpl. reflexivity.
Qed.

Definition negb' (b:bool) : bool :=
  if b then false
  else true.
Definition andb' (b1:bool) (b2:bool) : bool :=
  if b1 then b2
  else false.
Definition orb' (b1:bool) (b2:bool) : bool :=
  if b1 then true
  else b2.

(*my proof*)
Definition nandb (b1 b2:bool):bool:=
  if b1 then if b2 then false
             else true
  else true.

Definition nandb' (b1:bool) (b2:bool) : bool :=
  match b1 with
  |true => 
        match b2 with
        |true => false
        |false => true
        end
  |false => true
end.

Example test_nandb1: (nandb true false) = true.
Proof.
simpl. reflexivity.
Qed.
Example test_nandb2: (nandb false false) = true.
Proof.
simpl. reflexivity.
Qed.
Example test_nandb3: (nandb false true) = true.
Proof.
simpl. reflexivity.
Qed.
Example test_nandb4: (nandb true true) = false.
Proof.
simpl. reflexivity.
Qed.
(*my proof*)
Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool
  :=
  if b1 then if b2 then if b3 then true
                        else false
             else false
  else false.
Example test_andb31: (andb3 true true true) = true.
Proof.
simpl. reflexivity.
Qed.
Example test_andb32: (andb3 false true true) = false.
Proof.
simpl. reflexivity.
Qed.
Example test_andb33: (andb3 true false true) = false.
Proof.
simpl. reflexivity.
Qed.
Example test_andb34: (andb3 true true false) = false.
Proof.
simpl. reflexivity.
Qed.

Inductive rgb : Type :=
  | red
  | green
  | blue.
Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.

Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

Inductive bit : Type :=
  | B0
  | B1.
Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).
Check (bits B1 B0 B1 B0)
    : nybble.

Definition all_zero (nb : nybble) : bool :=
  match nb with
    | (bits B0 B0 B0 B0) => true
    | (bits _ _ _ _) => false
  end.
Compute (all_zero (bits B1 B0 B1 B0)).
(* ===> false : bool *)
Compute (all_zero (bits B0 B0 B0 B0)).

Module NatPlayground.
Inductive nat : Type :=
  | O
  | S (n : nat).

Compute (S O).

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

End NatPlayground.

Check (S (S O)).

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.
Compute (minustwo 4).

Check S.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.
Definition oddb (n:nat) : bool :=
  negb (evenb n).
Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Compute (plus 3 2).

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.
Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.
Compute (minus 4 2).

End NatPlayground2.
Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.
Compute (exp 3 2).

Compute (mult 3 4).

(*my proof*)
Fixpoint factorial (n:nat) : nat :=
  match n with
    | 0 => 1
    | S n' => mult (S n') (factorial n')
  end.
Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Compute (5-1).

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

(*my proof*)
Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.
Example test_leb1: leb 2 2 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: leb 2 4 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: leb 4 2 = false.
Proof. simpl. reflexivity. Qed.

Notation "x = y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <= y" := (leb x y) (at level 70) : nat_scope.
Example test_leb3': (4 <= 2) = false.
Proof. simpl. reflexivity. Qed.

Compute (andb true true).

Definition ltb (n m : nat) : bool :=
   andb (negb (n = m)) (n <= m).
Compute (ltb 5 4).

Notation "x < y" := (ltb x y) (at level 70) : nat_scope.
Example test_ltb1: (ltb 2 2) = false.
Proof. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_O_n'' : forall n : nat, 0 + n = n.
Proof.
  intros m. reflexivity. Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.
Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.

Proof.
  (* 将两个量词移到上下文中： *)
  intros n m.
  (* 将前提移到上下文中： *)
  intros H.
  (* 用前提改写目标： *)
  rewrite <- H.
  reflexivity. Qed.

(*my proof*)
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H.
  intros H1.
  rewrite -> H.
  rewrite <- H1.
  reflexivity.
Qed.

Check plus_id_exercise.

Check mult_n_O.
(* ===> forall n : nat, 0 = n * 0 *)
Check mult_n_Sm.
(* ===> forall n m : nat, n * m + n = n * S m *)

Theorem mult_n_0_m_0 : forall n m : nat,
  (n * 0) + (m * 0) = 0.
Proof.
  intros n m.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity. Qed.
(*my proof*)
Theorem mult_n_1 : forall n : nat,
  n * 1 = n.
Proof.
  intros n.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  reflexivity.
  Qed.

Theorem plus_1_neq_0_firsttry : forall n : nat,
  ((n + 1) = 0) = false.
Proof.
  intros n.
  simpl. (* 无能为力! *)
Abort.

Theorem plus_1_neq_0_firsttry : forall n : nat,
  ((n + 1) = 0) = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.
(*my proof*)
Theorem plus_1_neq_0' : forall n : nat,
  ((n + 1) = 0) = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity. Qed.

Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
(*my proof*)
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c eq. simpl in eq.
  destruct b as [].
  - destruct c as [].
    * reflexivity.
    * simpl in eq.
      discriminate eq.
  - destruct c as [].
    * reflexivity.
    * simpl in eq.
      discriminate eq.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  (0 = (n + 1)) = false.
Proof.
  intros n.
  destruct n as [].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f eq. intros b.
  rewrite -> eq. rewrite -> eq. reflexivity.
Qed.

(*my proof*)
Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f eq b.
  rewrite -> eq. rewrite -> eq. apply negb_involutive.
Qed.
(*my proof*)
Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c eq.
  destruct b as [].
  - destruct c as [].
    + reflexivity.
    + discriminate eq.
  - destruct c as [].
    + discriminate eq.
    + reflexivity.
Qed.

Inductive bin : Type :=
  | Z
  | A (n : bin)
  | B (n : bin).

Compute (B Z).
(*my proof*)
Fixpoint incr (m:bin) : bin :=
  match m with
  |Z => B Z
  |A m' => B m'
  |B m' => A (incr m')
end. 

Compute (incr (B (B (B Z)))).
(*my proof*)
Fixpoint decr (m:bin) : bin :=
  match m with
  |Z => Z
  |B m' => A m'
  |A m' => B (decr m')
end. 
(*my proof*)
Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  |Z => 0
  |A m' => 2*(bin_to_nat m')
  |B m' => S (2*(bin_to_nat m'))
end.

Compute (bin_to_nat (B (B (B Z)))).








