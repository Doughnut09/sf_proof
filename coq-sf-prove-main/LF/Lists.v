From LF Require Export Induction.
Module NatList.

Inductive natprod : Type :=
| pair (n1 n2 : nat).

Check (pair 3 5) : natprod.

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.
Compute (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Compute (fst (3,5)).
Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.
Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.
Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity. Qed.

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* 啥也没有归约！ *)
Abort.

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  (* 请在此处解答 *) 
  intros p. destruct p as [n m].
  simpl. reflexivity. 
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  (* 请在此处解答 *) 
  intros p. destruct p as [n m].
  simpl. reflexivity. 
Qed.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Notation "x + y" := (plus x y)
                      (at level 50, left associativity).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).
Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.
Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.
Compute tl [0;1;0;2;3;0;0].
Fixpoint nonzeros (l:natlist) : natlist :=
  (* 将本行替换成 ":= _你的_定义_ ." *)
  match l with
  |[]=>[]
  |h::t => if h=0 then (nonzeros t) else [h]++(nonzeros t)
end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof.
  simpl. reflexivity.
Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  (* 将本行替换成 ":= _你的_定义_ ." *)
  match l with
  |[]=>[]
  |h::t=> if evenb h then (oddmembers t) else [h]++(oddmembers t)
end.
Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof.
  simpl. reflexivity.
Qed.

Fixpoint countoddmembers (l:natlist) : nat :=
  (* 将本行替换成 ":= _你的_定义_ ." *)
  match l with
  |[]=>0
  |h::t=> if evenb h then (countoddmembers t) else 1+(countoddmembers t)
end.
Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof.
  simpl. reflexivity.
Qed.
Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof.
  simpl. reflexivity.
Qed.
Example test_countoddmembers3:
  countoddmembers nil = 0.
  (* 请在此处解答 *) 
Proof.
  simpl. reflexivity.
Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  (* 将本行替换成 ":= _你的_定义_ ." *)
  match l1,l2 with
  |[],[] => []
  |[],_ => l2
  |_,[]=> l1
  |h1::t1 , h2::t2 => [h1;h2]++(alternate t1 t2)
end.
Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof.
  simpl. reflexivity.
Qed.
Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof.
  simpl. reflexivity.
Qed.
Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof.
  simpl. reflexivity.
Qed.
Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof.
  simpl. reflexivity.
Qed.

Definition bag := natlist.

(** * Boolean equality on [nat] *)

Fixpoint beq_nat n m : bool :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n1, S m1 => beq_nat n1 m1
  end.

Check beq_nat.

Fixpoint count (v:nat) (s:bag) : nat :=
  (* 将本行替换成 ":= _你的_定义_ ." *)
  match s with
  |[]=>0
  |h::t=>(if beq_nat h v then 1 else 0) + (count v t)
end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof.
  simpl. reflexivity.
Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof.
  simpl. reflexivity.
Qed.

Definition sum : bag -> bag -> bag :=
  (* 将本行替换成 ":= _你的_定义_ ." *)
  app.
Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof.
  simpl. reflexivity.
Qed.
Definition add (v:nat) (s:bag) : bag :=
  (* 将本行替换成 ":= _你的_定义_ ." *)
  match s with
  |[]=>[v]
  |h::t=>[v]++h::t
end.
Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof.
  simpl. reflexivity.
Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof.
  simpl. reflexivity.
Qed.
Definition member (v:nat) (s:bag) : bool:=
  (* 将本行替换成 ":= _你的_定义_ ." *)
  match s with
  |[]=>false
  |h::t=>if h=v then true else false
end.
Example test_member1: member 1 [1;4;1] = true.
Proof.
  simpl. reflexivity.
Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof.
  simpl. reflexivity.
Qed.

Fixpoint remove_one (v:nat) (s:bag) : bag:=
  (* 将本行替换成 ":= _你的_定义_ ." *)
  match s with
  |[]=>[]
  |h::t=>if h=v then t else h::(remove_one v t)
end.
Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof.
  simpl. reflexivity.
Qed.
Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof.
  simpl. reflexivity.
Qed.
Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof.
  simpl. reflexivity.
Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof.
  simpl. reflexivity.
Qed.
Fixpoint remove_all (v:nat) (s:bag) : bag:=
  (* 将本行替换成 ":= _你的_定义_ ." *)
  match s with
  |[]=>[]
  |h::t=>if h=v then (remove_all v t) else h::(remove_all v t)
end.
Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof.
  simpl. reflexivity.
Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof.
  simpl. reflexivity.
Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof.
  simpl. reflexivity.
Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof.
  simpl. reflexivity.
Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool:=
  (* 将本行替换成 ":= _你的_定义_ ." *)
  match s1 with
  |[]=>true
  |h::t=>if (count h s2)=0 then false
                           else subset t (remove_one h s2)
end.
Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof.
  simpl. reflexivity.
Qed.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof.
  simpl. reflexivity.
Qed. 

Theorem bag_count_add : forall s : bag,
  count 1 (add 1 s) = S (count 1 s).
Proof.
  intros s. destruct s as [].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity. 
Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.
Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = n :: l' *)
    (* 这种情况比较棘手。我们从一般的化简开始。 *)
    simpl.
    (* 现在我们好像卡住了：目标是要证明涉及 ++ 的等式，
       但是我们在上下文和全局环境下并没有任何有用的等式！
       通过用 IH 来重写目标，我们可以推进一点... *)
    rewrite <- IHl'.
    (* ...但也仅此而已。 *)
Abort.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* 课上已完成 *)
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> app_length.
    simpl. rewrite -> IHl'. rewrite plus_comm.
    reflexivity.
Qed.

Search app.

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  (* 请在此处解答 *) 
  intros l. induction l as [].
  - simpl. reflexivity.
  - simpl. rewrite -> IHl. reflexivity.
Qed.
Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  (* 请在此处解答 *) 
  intros l1 l2. induction l1 as [].
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IHl1. rewrite -> app_assoc. reflexivity.
Qed.
Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  (* 请在此处解答 *) 
  intros l. induction l as [].
  - simpl. reflexivity.
  - simpl. rewrite -> rev_app_distr. simpl.
    rewrite -> IHl. reflexivity.
Qed. 

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  (* 请在此处解答 *) 
  intros l1 l2 l3 l4. rewrite -> app_assoc.
  rewrite -> app_assoc. reflexivity.
Qed.

Search nonzeros.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  (* 请在此处解答 *) 
  intros l1 l2. induction l1 as [].
  - simpl. reflexivity.
  - simpl. rewrite -> IHl1. 
    destruct n as [].
    * simpl. reflexivity.
    * simpl. reflexivity.
Qed.

Fixpoint eqblist (l1 l2 : natlist) : bool:=
  (* 将本行替换成 ":= _你的_定义_ ." *)
  match l1,l2 with
  |[],[]=>true
  |[],_ =>false
  |_ ,[]=>false
  |h1::t1,h2::t2=>if h1=h2 then eqblist t1 t2 
                           else false
end.
Example test_eqblist1 :
  (eqblist nil nil = true).
 (* 请在此处解答 *) 
Proof.
  reflexivity.
Qed.
Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
(* 请在此处解答 *) 
Proof.
  reflexivity.
Qed.
Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
 (* 请在此处解答 *) Proof.
  reflexivity.
Qed.
Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
  intros l. induction l as [].
  - simpl. reflexivity.
  - simpl. induction n as [].
    * simpl. rewrite <- IHl. reflexivity.
    * simpl. rewrite <- IHn. reflexivity.
Qed.

Theorem count_member_nonzero : forall (s : bag),
  (1 <= (count 1 (1 :: s))) = true.
Proof.
  (* 请在此处解答 *) 
  intros s. simpl. reflexivity.
Qed.

Theorem leb_n_Sn : forall n,
  (n <= (S n)) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity. Qed.

Theorem remove_does_not_increase_count: forall (s : bag),
  ((count 0 (remove_one 0 s)) <= (count 0 s)) = true.
Proof.
  (* 请在此处解答 *) 
  intros s. induction s as [].
  - simpl. reflexivity.
  - simpl. induction n as [].
    * simpl. rewrite -> leb_n_Sn. reflexivity.
    * simpl. rewrite -> IHs. reflexivity.
Qed.

(*Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.*)
Theorem bag_count_sum : forall (n : nat) (s1 s2 : bag),
  count n (sum s1 s2) = count n s1 + count n s2.
Proof.
  intros n s1 s2. induction s1 as [|h1 t1 IHs1].
  - simpl. reflexivity.
  - induction s2 as [|h2 t2 IHs2].
    * simpl. rewrite <- plus_n_O. rewrite -> app_nil_r. reflexivity.
    * simpl. rewrite -> IHs1. simpl. rewrite -> plus_assoc. reflexivity.
Qed.

Theorem rev_injective : forall (l1 l2 : natlist), 
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2 eq.
  rewrite <- rev_involutive. 
  rewrite <- eq. rewrite -> rev_involutive. 
  reflexivity.
Qed.

Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 42
  | a :: l' => match n with
               | 0 => a
               | S n' => nth_bad l' n'
               end
  end.

Compute nth_bad [1;4;5;6] 4.

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.
Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof.
  simpl. reflexivity.
Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof.
  simpl. reflexivity.
Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof.
  simpl. reflexivity.
Qed.

Fixpoint nth_error' (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => if n = O then Some a
               else nth_error' l' (pred n)
  end.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

(*Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.*)
Definition hd_error (l : natlist) : natoption :=
  (* 将本行替换成 ":= _你的_定义_ ." *)
  match l with
  | nil => None
  | a::l => Some a
end.
Example test_hd_error1 : hd_error [] = None.
Proof.
  simpl. reflexivity.
Qed.
Example test_hd_error2 : hd_error [1] = Some 1.
Proof.
  simpl. reflexivity.
Qed.
Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof.
  simpl. reflexivity.
Qed.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  (* 请在此处解答 *) 
  intros l default. destruct l as [].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.
End NatList.

Inductive id : Type :=
  | Id (n : nat).

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 = n2
  end.

Compute eqb_id (Id 2) (Id 2).

Theorem eqb_id_refl : forall x, true = eqb_id x x.
Proof.
  (* 请在此处解答 *) 
  intros x. destruct x as []. simpl. 
  induction n as [].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn. reflexivity.
Qed.

Module PartialMap.
Export NatList.

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

Check record (Id 1) 4 empty.

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Compute update (record (Id 1) 1 empty) (Id 2) 2.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.
Compute find (Id 0) (record (Id 2) 2 (record (Id 1) 1 empty)).

Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
  intros d x v.
  simpl. rewrite <- eqb_id_refl. reflexivity.
Qed.

Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros d x y o eq.
  simpl. rewrite -> eq. reflexivity.
Qed.

End PartialMap.

Inductive baz : Type :=
  | Baz1 (x : baz)
  | Baz2 (y : baz) (b : bool).


























