Require Export Basics.

Module NatList.

Inductive natprod : Type :=
  pair : nat -> nat -> natprod.
Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.
Definition snd (p: natprod) : nat :=
  match p with
  | pair x y => y
  end.

Notation "( x , y )" := (pair x y).

Eval simpl in (fst (3,5)).

Definition fst' (p:natprod):nat:=
  match p with
  | (x,y)=>x
  end.
Definition snd' (p:natprod):nat:=
  match p with 
  | (x,y)=>y
  end.

Definition swap_pair (p:natprod):natprod :=
  match p with
  | (x,y)=>(y,x)
  end.

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.  Qed.

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* Doesn't reduce anything! *)
Admitted.

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p.  destruct p as (n,m).  simpl.  reflexivity.  Qed.


Require Unicode.Utf8.

Theorem snd_fst_is_swap : ∀p:natprod,
  (snd p,fst p) = swap_pair p.
Proof.
  intros p. 
  destruct p.
  simpl. reflexivity.
  Qed.

Theorem fst_swap_is_snd :∀p:natprod,
  fst (swap_pair p) = snd p.
Proof.
  intros p.
  destruct p.
  simpl. reflexivity.
  Qed.

Inductive natlist : Type :=
  | nil: natlist
  | cons: nat -> natlist -> natlist.

Definition mylist:=cons 1 (cons 2 (cons 3 nil)).


Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1,2,3].

Eval simpl in 1+2.

Eval simpl in 1+2::[3].

Fixpoint repeat (n count:nat):natlist:=
  match count with
  | 0=> nil
  | S count'=>n::(repeat n count')
  end.

Eval simpl in repeat 2 10.

Fixpoint length (l:natlist):nat:=
  match l with
  | nil =>0
  | h::t=>S (length t)
  end.

Eval simpl in length (repeat 2 19).


Fixpoint app (l1 l2:natlist) :natlist:=
  match l1 with
  | nil=>l2
  |h::t=>h::(app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1:             [1,2,3] ++ [4,5] = [1,2,3,4,5].
Proof. reflexivity.  Qed.
Example test_app2:             nil ++ [4,5] = [4,5].
Proof. reflexivity.  Qed.
Example test_app3:             [1,2,3] ++ nil = [1,2,3].
Proof. reflexivity.  Qed.

Definition hd (default:nat)(l:natlist):nat:=
  match l with 
  | nil=>default
  | h::t =>h
  end.

Definition tail (l:natlist):natlist:=
  match l with
  |nil=>nil
  |h::t=>t
  end.

Example test_hd1:             hd 0 [1,2,3] = 1.
Proof. reflexivity.  Qed.
Example test_hd2:             hd 0 [] = 0.
Proof. reflexivity.  Qed.
Example test_tail:            tail [1,2,3] = [2,3].
Proof. reflexivity.  Qed.

Fixpoint nonzeros(l:natlist):natlist:=
  match l with
  | nil=>nil
  | 0::t=>nonzeros t
  | h::t=>h::nonzeros t
end.

Example test_nonzeros: nonzeros [0,1,0,2,3,0,0] = [1,2,3].
Proof. simpl. reflexivity. Qed.

Fixpoint oddmembers(l:natlist):natlist:=
  match l with
  |nil=>nil
  |h::t=> match oddb h with
          | true => h::oddmembers t
          | false => oddmembers t
          end
  end.

Example test_oddmembers: oddmembers [0,1,0,2,3,0,0] = [1,3].
Proof. simpl. reflexivity. Qed.

Fixpoint countoddmembers (l:natlist):nat:=
  match l with 
  |nil=>0
  |h::t=>match oddb h with
         | true=> 1+countoddmembers t
         | false=>countoddmembers t
         end
   end.



Example test_countoddmembers1: countoddmembers [1,0,3,1,4,5] = 4.
 Proof. simpl. reflexivity. Qed.
Example test_countoddmembers2: countoddmembers [0,2,4] = 0.
 Proof. simpl. reflexivity. Qed.
Example test_countoddmembers3: countoddmembers nil = 0.
 Proof. simpl. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1,l2 with
  | nil,l=>l
  | l,nil=>l
  | h1::t1,h2::t2=>h1::h2::alternate t1 t2
  end.

Example test_alternate1: alternate [1,2,3] [4,5,6] = [1,4,2,5,3,6].
  Proof. simpl. reflexivity. Qed.
Example test_alternate2: alternate [1] [4,5,6] = [1,4,5,6].
  Proof. simpl. reflexivity. Qed.
Example test_alternate3: alternate [1,2,3] [4] = [1,4,2,3].
  Proof. simpl. reflexivity. Qed.
Example test_alternate4: alternate [] [20,30] = [20,30].
  Proof. simpl. reflexivity. Qed.

Definition bag:=natlist.

Fixpoint count(v:nat)(s:bag):nat:=
  match s with
  |nil=>0
  |h::t => 
    match beq_nat v h with
    | true => 1+count v t
    | false => count v t
    end
  end.

Example test_count1: count 1 [1,2,3,1,4,1] = 3.
  Proof. simpl. reflexivity. Qed.
Example test_count2: count 6 [1,2,3,1,4,1] = 0.
  Proof. simpl. reflexivity. Qed.

Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1,2,3] [1,4,1]) = 3.
  Proof. simpl. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag := cons v s.

Example test_add1: count 1 (add 1 [1,4,1]) = 3.
  Proof. simpl. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1,4,1]) = 0.
  Proof. simpl. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool := 
  negb (beq_nat 0 (count v s)).

Example test_member1: member 1 [1,4,1] = true.
  Proof. simpl. reflexivity. Qed.
Example test_member2: member 2 [1,4,1] = false.
  Proof. simpl. reflexivity. Qed.

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  (* When remove_one is applied to a bag without the number to remove,
     it should return the same bag unchanged. *)
  match s with
  | nil => nil
  | h::t => match beq_nat v h with
            | true => t
            | false => h::remove_one v t
            end
  end.

Example test_remove_one1: count 5 (remove_one 5 [2,1,5,4,1]) = 0.
  Proof. simpl. reflexivity. Qed.
Example test_remove_one2: count 5 (remove_one 5 [2,1,4,1]) = 0.
  Proof. simpl. reflexivity. Qed.
Example test_remove_one3: count 4 (remove_one 5 [2,1,4,5,1,4]) = 2.
  Proof. simpl. reflexivity. Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2,1,5,4,5,1,4]) = 1.
  Proof. simpl. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  |nil =>nil
  | h::t=>match beq_nat v h with
          | true => remove_all v t
          | false => h::remove_all v t
          end
  end.

Example test_remove_all1: count 5 (remove_all 5 [2,1,5,4,1]) = 0.
  Proof. simpl. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2,1,4,1]) = 0.
  Proof. simpl. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2,1,4,5,1,4]) = 2.
  Proof. simpl. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2,1,5,4,5,1,4,5,1,4]) = 0.
  Proof. simpl. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
  |nil=>true
  |h::t => match member h s2 with
          | true => subset t (remove_one h s2)
          | false=> false
          end
  end.

Example test_subset1: subset [1,2] [2,1,4,1] = true.
  Proof. simpl. reflexivity. Qed.
Example test_subset2: subset [1,2,2] [2,1,4,1] = false.
  Proof. simpl. reflexivity. Qed.

Theorem count_nil:∀n:nat, count n []=0.
Proof. intros n. simpl. reflexivity. Qed.

Theorem add_nil:∀n:nat,add n []=[n].
Proof. intros n. simpl. reflexivity. Qed.

Theorem beq_true:∀n:nat,beq_nat n n=true.
Proof. intros. induction n.
 Case "n=0". simpl. reflexivity.
 Case"n=Sn".  simpl. rewrite->IHn. reflexivity. Qed.


Theorem bag_count_add:∀n:nat,∀s:bag,
count n (add n s)= S (count n s).
Proof.
  intros n s.
  induction n as [|n'].
  Case "n=0". simpl. reflexivity.
  Case "n=S n'". simpl. rewrite->beq_true. reflexivity.
Qed.

(**************** Reasoning About Lists ****************)

Theorem nil_app : ∀l:natlist,
  [] ++ l = l.
Proof.
   reflexivity. Qed.

Theorem tl_length_pred : ∀l:natlist,
  pred (length l) = length (tail l).
Proof.
  intros l. (* why not induction? ie induction l as [|l'].*)
 destruct l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n l'".
    reflexivity. Qed.


(* ###################################################### *)
(** ** Induction on Lists *)


Theorem app_ass : ∀l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons n l1'".
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Theorem app_length : ∀l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORKED IN CLASS *)
  intros l1 l2. induction l1 as [| n l1'].
  Case "l1 = nil". simpl.
    reflexivity.
  Case "l1 = cons".
    simpl. rewrite -> IHl1'. reflexivity. Qed.

(*Fixpoint rev (l:natlist):natlist :=
  match l with
  |nil=>nil
  |h::t=>rev t++cons h nil
end.*)

Fixpoint snoc (l:natlist) (v:nat) : natlist := 
  match l with
  | nil    => [v]
  | h :: t => h :: (snoc t v)
  end.

(** ... and use it to define a list-reversing function [rev]
    like this: *)

Fixpoint rev (l:natlist) : natlist := 
  match l with
  | nil    => nil
  | h :: t => snoc (rev t) h
  end.

Example test_rev1:            rev [1,2,3] = [3,2,1].
Proof. reflexivity.  Qed.
Example test_rev2:            rev nil = nil.
Proof. reflexivity.  Qed.

(** Now let's prove some more list theorems using our newly
    defined [snoc] and [rev].  For something a little more challenging
    than the inductive proofs we've seen so far, let's prove that
    reversing a list does not change its length.  Our first attempt at
    this proof gets stuck in the successor case... *)

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = []".
    simpl. reflexivity.
  Case "l = n :: l'".
    (* This is the tricky case.  Let's begin as usual by simplifying. *)
    simpl. 
    (* Now we seem to be stuck: the goal is an equality involving
       [snoc], but we don't have any equations in either the
       immediate context or the global environment that have
       anything to do with [snoc]! 

       We can make a little progress by using the IH to rewrite the 
       goal... *)
    rewrite <- IHl'.
    (* ... but now we can't go any further. *)
Admitted.

(** So let's take the equation about [snoc] that would have
    enabled us to make progress and prove it as a separate lemma. *)

Theorem length_snoc : forall n : nat, forall l : natlist,
  length (snoc l n) = S (length l).
Proof.
  intros n l. induction l as [| n' l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n' l'".
    simpl. rewrite -> IHl'. reflexivity.  Qed. 

(** Now we can complete the original proof. *)

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons".
    simpl. rewrite -> length_snoc. 
    rewrite -> IHl'. reflexivity.  Qed.

(** For comparison, here are informal proofs of these two theorems: 

    _Theorem_: For all numbers [n] and lists [l],
       [length (snoc l n) = S (length l)].
 
    _Proof_: By induction on [l].

    - First, suppose [l = []].  We must show
        length (snoc [] n) = S (length []),
      which follows directly from the definitions of
      [length] and [snoc].

    - Next, suppose [l = n'::l'], with
        length (snoc l' n) = S (length l').
      We must show
        length (snoc (n' :: l') n) = S (length (n' :: l')).
      By the definitions of [length] and [snoc], this
      follows from
        S (length (snoc l' n)) = S (S (length l')),
]] 
      which is immediate from the induction hypothesis. [] *)
                        
(** _Theorem_: For all lists [l], [length (rev l) = length l].
    
    _Proof_: By induction on [l].  

      - First, suppose [l = []].  We must show
          length (rev []) = length [],
        which follows directly from the definitions of [length] 
        and [rev].
    
      - Next, suppose [l = n::l'], with
          length (rev l') = length l'.
        We must show
          length (rev (n :: l')) = length (n :: l').
        By the definition of [rev], this follows from
          length (snoc (rev l') n) = S (length l')
        which, by the previous lemma, is the same as
          S (length (rev l')) = S (length l').
        This is immediate from the induction hypothesis. [] *)

(** Obviously, the style of these proofs is rather longwinded
    and pedantic.  After the first few, we might find it easier to
    follow proofs that give a little less detail overall (since we can
    easily work them out in our own minds or on scratch paper if
    necessary) and just highlight the non-obvious steps.  In this more
    compressed style, the above proof might look more like this: *)

(** _Theorem_:
     For all lists [l], [length (rev l) = length l].

    _Proof_: First, observe that
       length (snoc l n) = S (length l)
     for any [l].  This follows by a straightforward induction on [l].
     The main property now follows by another straightforward
     induction on [l], using the observation together with the
     induction hypothesis in the case where [l = n'::l']. [] *)

(** Which style is preferable in a given situation depends on
    the sophistication of the expected audience and on how similar the
    proof at hand is to ones that the audience will already be
    familiar with.  The more pedantic style is a good default for
    present purposes. *)


Theorem snoc_append : ∀l:natlist, ∀n:nat,
  snoc l n = l ++ [n].
Proof.
  intros l n. induction l as [|n' l'].
  Case "l=[]". simpl. reflexivity.
  Case "l=n'::l'". simpl. rewrite <- IHl'. reflexivity. Qed.


SearchAbout rev.

(* ###################################################### *)
(** ** List Exercises, Part 1 *)

Theorem app_nil_end : ∀l : natlist,
  l ++ [] = l.
Proof.
 intros l. induction l as [|n l'].
  Case "l=[]". simpl. reflexivity.
  Case "l= n::l'".
    simpl. rewrite -> IHl'. reflexivity. Qed.

Theorem rev_id :∀n:nat,rev [n]=[n].
Proof. intros n. simpl. reflexivity. Qed.


Theorem rev_dist :∀l1 l2:natlist,
rev(l1++l2)=rev l2++rev l1.
Proof. intros l1 l2. induction l1 as [|n l1'].
  Case "l1=[]". simpl. rewrite->app_nil_end. reflexivity.
  Case "l1=n::l1'".
  simpl. rewrite->IHl1'. 
  rewrite->snoc_append. rewrite->snoc_append. 
  rewrite->app_ass. reflexivity. Qed.


Theorem rev_involutive : ∀l : natlist,
  rev (rev l) = l.
Proof.
 intros l. induction l as [|n l'].
 Case"l=[]". simpl. reflexivity.
 Case"l=n::l'".
 simpl. rewrite->snoc_append. 
 rewrite->rev_dist. rewrite->IHl'. simpl. reflexivity. Qed.

Theorem distr_rev : ∀l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  intros l1 l2. rewrite->rev_dist. reflexivity. Qed.

Theorem app_ass4 : ∀l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
 rewrite->app_ass. rewrite->app_ass. reflexivity. Qed.


Lemma nonzeros_length : ∀l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2. induction l1 as [|n l1'].
  Case "l1=[]". simpl. reflexivity.
  Case "l1=n::l1'". induction n.
    SCase "n=0". simpl. rewrite->IHl1'. reflexivity.
    SCase "n=Sn". simpl. rewrite->IHl1'. reflexivity. Qed.

(* ###################################################### *)
(** ** List Exercises, Part 2 *)

Theorem cons_snoc_append:∀l1 l2:natlist,∀n1 n2:nat,
  cons n1 l1++snoc l2 n2 = snoc (cons n1 (l1++l2)) n2.
Proof.
  intros l1 l2 n1 n2. induction l1 as [|n1' l1'].
  Case "l1=[]". simpl. reflexivity.
  Case "l1=n1'::l1'".
  simpl. 
  rewrite->snoc_append. rewrite->snoc_append. rewrite->app_ass. 
  reflexivity. Qed.

Theorem count_member_nonzero : ∀s : bag,
  ble_nat 1 (count 1 (1 :: s)) = true.
Proof.
  intros s. induction s as [|n l].
  Case "s=[]". simpl. reflexivity.
  Case "s=n::l". simpl. reflexivity. Qed.

(** The following lemma about [ble_nat] might help you in the next proof. *)

Theorem ble_n_Sn : forall n,
  ble_nat n (S n) = true.
Proof.
  intros n. induction n as [| n'].
  Case "0".  
    simpl.  reflexivity.
  Case "S n'".
    simpl.  rewrite IHn'.  reflexivity.  Qed.

Theorem remove_decreases_count: forall (s : bag),
  ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
 intros s. induction s as [|n l].
 simpl. reflexivity.
 destruct n. simpl. apply ble_n_Sn.
 simpl. apply IHl. Qed.

Theorem rev_nil: rev [] = [].
Proof. simpl. reflexivity. Qed.

(*
Theorem rev_inj_conv :∀l1 l2:natlist,not (l1=l2)-> not (rev l1=rev l2).
Proof.
  intros l1 l2. induction l1 as [|n1 l1'].
  Case "l1=[]". simpl. intros H. induction l2 as [|n2 l2']. rewrite->rev_nil.*)

(* skipping this for now until I learn more coq tactics *)

Theorem rev_rev:∀l l': natlist, l=l'->rev l = rev l'.
Proof. intros l l' H. rewrite ->H. reflexivity. Qed.

Theorem flip_rev:∀l l':natlist,
rev l = l' -> l = rev l'.
Proof.
  intros l l' H. apply rev_rev in H. SearchAbout rev. rewrite-> rev_involutive in H. apply H. Qed.

(*Theorem rev_nil_inj : ∀l:natlist,rev l=[] -> l=[].
Proof.
 intros l H.
 induction l as [|n l']. reflexivity.
 inversion H. inversion H1. 
 reflexivity. 
 simpl. rewrite->snoc_append. destruct l'. simpl. intros H. inversion H.
  simpl. rewrite->snoc_append.
 unfold app. intros H. inversion H. simpl.
 *)
(*Theorem snoc_rev : ∀l:natlist, ∀n:nat,*)
  

Theorem rev_injective : ∀l1 l2 : natlist, rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2 H. apply rev_rev in H. rewrite->rev_involutive in H. rewrite->rev_involutive in H. apply H. Qed.
