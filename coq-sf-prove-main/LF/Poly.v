From LF Require Export Lists.

Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b : bool) (l : boollist).

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Check list : Type -> Type.

Check (nil nat) : list nat.
Check (cons nat 3 (nil nat)) : list nat.
Check nil : forall X : Type, list X.
Check cons.
Check (cons nat 2 (cons nat 1 (nil nat))).

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.

Module MumbleGrumble.
Inductive mumble : Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.
Inductive grumble (X:Type) : Type :=
  | d (m : mumble)
  | e (x : X).

End MumbleGrumble.
Fixpoint repeat' X x count : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat' X x count')
  end.
Check repeat'
  : forall X : Type, X -> nat -> list X.
Check repeat
  : forall X : Type, X -> nat -> list X.

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0 => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat''' x count')
  end.

Inductive list' {X:Type} : Type :=
  | nil'
  | cons' (x : X) (l : list').

Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.
Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.
Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.
Print length.

Definition mynil : list nat := nil.

Check @nil : forall X : Type, list X.
Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).
Check [1; 2; 3].
Definition list123''' := [1; 2; 3].

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  intros. induction l.
  - simpl. reflexivity.
  - simpl. rewrite->IHl. reflexivity. 
Qed.
Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros. induction l. 
  - simpl. reflexivity.
  - simpl. rewrite -> IHl. reflexivity.
Qed.
Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2. 
Proof.
  intros. induction l1.
  - simpl. reflexivity.
  - simpl. rewrite->IHl1. reflexivity.
Qed.
Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros. induction l1.
  - simpl. rewrite->app_nil_r. reflexivity.
  - simpl. rewrite->IHl1. rewrite<-app_assoc. reflexivity.
Qed.
Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros. induction l as [].
  - simpl. reflexivity.
  - simpl. rewrite -> rev_app_distr. simpl.
    rewrite -> IHl. reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).
Print prod.
Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.
Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Check @combine.

Compute (combine [1;2] [false;false;true;true]).

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: tl => match split tl with
                    | (lx, ly) => (x :: lx,y :: ly)
                    end
   end.
Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
(* 请在此处解答 *) 
  simpl. reflexivity.
Qed.

Module OptionPlayground.
Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.
Arguments Some {X} _.
Arguments None {X}.
End OptionPlayground.

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | [] => None
  | a :: l' => if n = O then Some a else nth_error l' (pred n)
  end.

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | [] => None 
  | hd :: tl => Some hd 
  end.

Check @hd_error.

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t)
                        else filter test t
  end.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) = 1.
Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof.
(* 请在此处解答 *) 
  simpl. reflexivity.
Qed.

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Definition filter_even_gt7 (l : list nat) : list nat:=
  filter (fun n => if leb 7 n then true else false) (filter evenb l).

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof.
  unfold filter_even_gt7. simpl. reflexivity.
Qed.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof.
  unfold filter_even_gt7. simpl. reflexivity.
Qed.

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X :=
  (filter test l, filter (fun x => negb (test x)) l).
Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. unfold partition. simpl. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. unfold partition. simpl. reflexivity. Qed.

Fixpoint map {X Y: Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Theorem map_app : forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
  map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  intros. induction l1. 
  - simpl. reflexivity. 
  - simpl. rewrite IHl1. reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros. induction l.
  + simpl. reflexivity.
  + simpl. rewrite -> map_app. simpl.
     rewrite -> IHl. reflexivity.
Qed.

Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X)
                   : (list Y) :=
  match l with
  | [] => []
  | h :: t => f h ++ (flat_map f t)
  end.
Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof.
  unfold flat_map. simpl. reflexivity.
Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

Fixpoint filter' (X:Type) (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | [] => nil
  | h :: t => if test h then h :: (filter' X test t)
                        else filter' X test t
  end.

Fixpoint map' (X Y: Type) (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map' X Y f t)
  end.

Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (b: Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Check (fold andb).

Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k:nat) => x.
Definition ftrue := constfun true.

Module Exercises.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.
Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros. 
  induction l. 
  + simpl. unfold fold_length. simpl. 
    reflexivity.
  + simpl. unfold fold_length. simpl. 
    rewrite <- IHl.  unfold fold_length.
    reflexivity.
Qed.

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
  fold (fun m n => f m :: n) l [].

Theorem fold_map_correct : forall X Y (f: X -> Y) (l : list X),
  fold_map f l = map f l.
Proof.
  intros. induction l.
  + simpl. unfold fold_map. simpl. reflexivity.
  + simpl. unfold fold_map. simpl. rewrite <- IHl.
    unfold fold_map. reflexivity.
Qed.

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z
  := f (fst p) (snd p).

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros. unfold prod_curry. unfold prod_uncurry.
  simpl. reflexivity.
Qed.
Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros. unfold prod_uncurry. unfold prod_curry. 
  destruct p. simpl. reflexivity.
Qed.

Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
     match l with
     | [] => None
     | a :: l' => if n = O then Some a else nth_error l' (pred n)
     end.

Theorem eqb_l_0 : forall n,
   ((n = 0) = true) -> n = 0.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    intros H. reflexivity.
  - (* n = S n' *)
    simpl. intros H. discriminate H.
Qed.

Lemma ntherror_len : forall X l n, length l = n -> @nth_error X l n = None.
Proof.
  intros. generalize dependent n. induction l.
  - simpl. intros. reflexivity.
  - intros. induction n.
    + simpl in H. discriminate H.
    + simpl. apply IHl. simpl in H. injection H as Hsm. apply Hsm.
Qed.

Module Church.
Definition cnat := forall X : Type, (X -> X) -> X -> X.

Definition one : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

Definition two : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

Definition zero : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

Definition three : cnat := @doit3times.

Definition succ (n : cnat) : cnat
  := fun (X : Type) (f : X -> X) (x : X) => f (n X f x).

Example succ_1 : succ zero = one.
Proof. 
  reflexivity.
Qed.
Example succ_2 : succ one = two.
Proof. 
  reflexivity.
Qed.
Example succ_3 : succ two = three.
Proof. 
  reflexivity.
Qed.

Definition plus (n m : cnat) : cnat
  := fun (X : Type) (f : X -> X) (x : X) => m X f (n X f x).
Example plus_1 : plus zero one = one.
Proof. 
  reflexivity.
Qed.
Example plus_2 : plus two three = plus three two.
Proof.
  reflexivity.
Qed.
Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. 
  reflexivity.
Qed.

Definition mult (n m : cnat) : cnat
  := fun (X : Type) (f : X -> X) (x : X) => m X (n X f) x.
Example mult_1 : mult one one = one.
Proof. 
  reflexivity.
Qed.
Example mult_2 : mult zero (plus three three) = zero.
Proof. 
  reflexivity.
Qed.
Example mult_3 : mult two three = plus three three.
Proof. 
  reflexivity.
Qed.

Definition exp (n m : cnat) : cnat 
  := fun (X : Type) => m (X -> X) (n X).

Example exp_1 : exp two two = plus two two.
Proof. 
  reflexivity.
Qed.
Example exp_2 : exp three zero = one.
Proof. 
  reflexivity.
Qed.
Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof. 
  reflexivity.
Qed.

End Church.
End Exercises.



















































