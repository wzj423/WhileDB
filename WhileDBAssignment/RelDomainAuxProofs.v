Require Import Coq.Classes.Morphisms.
Require Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import compcert.lib.Integers.
Require Import WhileDB.SetsDomain.
Require Import WhileDB.RelDomain.
Require Import WhileDB.Lang.
Local Open Scope Z.
Local Open Scope sets_scope.
Require Import Lia.

Lemma Rel_Concat_element_concat:
forall
{A B: Type}  
(X Y Z: A -> list B -> A-> Prop)
(a c d:A) (b1 b2 b12: list B),
  X a b1 c -> Y c b2 d -> b12 = b1 ++ b2
  -> Z=X∘Y -> Z a b12 d.
Proof.
  intros;revert H2;rel_unfold;intros.
  rewrite H2.
  exists c, b1 ,b2.
  repeat split; auto.
Qed.

Lemma Rel_Concat_element_concat2:
forall
{A B: Type}  
(X Y Z: A -> list B -> A-> Prop)
(a c d:A) (b1 b2 b12: list B),
  X a b1 c -> Y c b2 d -> b12 = b1 ++ b2
  -> Z==X∘Y -> Z a b12 d.
Proof.
  intros;revert H2;rel_unfold;intros.
  rewrite H2.
  exists c, b1 ,b2.
  repeat split; auto.
Qed.
 
Lemma Rel_Concat_element_concat_rev:
forall
{A B: Type}   
(X Y Z: A -> list B -> A-> Prop)
(a d:A) (b12: list B),
  Z=X∘Y -> Z a b12 d-> 
  exists b1 b2 c,b12 = b1 ++ b2 /\
  X a b1 c /\ Y c b2 d.
Proof.
  intros. revert H. rel_unfold;intros.
  rewrite H in H0;repeat destruct H0; destruct H1.
  exists x0,x1,x.
  repeat split; auto.
Qed.

Lemma Rel_Concat_element_concat_rev2:
forall
{A B: Type}   
(X Y Z: A -> list B -> A-> Prop)
(a d:A) (b12: list B),
  Z==X∘Y -> Z a b12 d-> 
  exists b1 b2 c,b12 = b1 ++ b2 /\
  X a b1 c /\ Y c b2 d.
Proof.
  intros. revert H. rel_unfold;intros.
  rewrite H in H0;repeat destruct H0; destruct H1.
  exists x0,x1,x.
  repeat split; auto.
Qed.

Lemma Rel_Concat_element_concat_rev3:
forall
{A B: Type}   
(X Y Z: A -> list B -> A-> Prop)
(a d:A) (b12: list B),
  Z a b12 d ->  Z==X∘Y ->
  exists b1 b2 c, b1 ++ b2 =b12/\
  X a b1 c /\ Y c b2 d.
Proof.
  intros. revert H0. rel_unfold;intros.
  rewrite H0 in H;repeat destruct H0; repeat destruct H;destruct H1.
  exists x0,x1,x.
  repeat split; auto.
Qed.


Lemma nsteps_O_id:
  forall
  {X: Type}
  {_RELS: Rels.RELS X X X}
  {_RELS_Id: Rels.RELS_ID X}
  {_SETS: Sets.SETS X}
  {_SETS_Properties: SETS_Properties X}
  (x: X),
  nsteps x O == Rels.id.
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma nsteps_1_self:
  forall
  {X: Type}
  {_RELS: Rels.RELS X X X}
  {_RELS_Id: Rels.RELS_ID X}
  {_SETS: Sets.SETS X}
  {_SETS_Properties: SETS_Properties X}
  {_RELS_RightId: RELS_RightId X X}
  (x: X),
nsteps x (S O) == x.
Proof.
intros. 
simpl. apply Rel_concat_id_r.
Qed.

Lemma nsteps_1n:
forall 
  {A B: Type}
  (X: A -> list B->A-> Prop)
  (n: nat)
  (a d:A) (b12: list B)
  ,
  (n > 0)%nat -> nsteps X n a b12 d -> exists b1 b2 c, b12=b1++b2/\ X a b1 c /\nsteps X (n-1) c b2 d.
Proof. 
  intros. pose proof nsteps_n_m X 1 (n-1).
  assert ((1+(n-1)%nat)%nat=n). { lia. }
  rewrite H2 in H1.
  eapply Rel_Concat_element_concat_rev;eauto.
  pose proof nsteps_1_self X.
  rewrite H3 in H1.
  apply H1.
  auto.
Qed.

Lemma nsteps_1n_rev:
forall 
  {A B: Type}
  (X: A -> list B->A-> Prop)
  (n: nat)
  (a d:A) (b12: list B),
  (n > 0)%nat -> (exists b1 b2 c, b12=b1++b2/\ X a b1 c /\nsteps X (n-1) c b2 d) -> nsteps X n a b12 d .
Proof. 
  intros. destruct H0 as [? [? [? [?[? ?]]]]].
  pose proof nsteps_n_m X 1 (n-1).
  assert ((1+(n-1)%nat)%nat=n). { lia. }
  rewrite H4 in H3.
  eapply Rel_Concat_element_concat2;eauto.
  rewrite (nsteps_1_self X) in H3.
  rewrite H3.
  reflexivity.
Qed.


  
Lemma rt_refl:
forall
  {X: Type}
  {_RELS: Rels.RELS X X X}
  {_RELS_Id: Rels.RELS_ID X}
  {_SETS: Sets.SETS X}
  {_RELS_Properties: RELS_Properties X X X}
  {_RELS_Assoc: RELS_Assoc X X X X X X}
  {_RELS_LeftId: RELS_LeftId X X}
  {_SETS_Properties: SETS_Properties X}
  (x: X),
  Sets.included
    Rels.id
    (clos_refl_trans x).
Proof.
intros.
unfold clos_refl_trans.
unfold Sets.omega_union.
pose proof Sets_included_indexed_union nat (nsteps x) O.
simpl in H. auto.
Qed.

Lemma rt_refl_concrete:
forall
  {A B: Type}
  (x: A->list B-> A->Prop)
  (a: A),
    (clos_refl_trans x a nil a).
Proof.
intros.
rel_unfold.
unfold clos_refl_trans.
unfold Sets.omega_union.
sets_unfold;rel_unfold.
exists O.
pose proof nsteps_O_id x.
unfold nsteps.
simpl.
sets_unfold.
auto.
Qed.

Lemma rt_step:
  forall
    {X: Type}
    {_RELS: Rels.RELS X X X}
    {_RELS_Id: Rels.RELS_ID X}
    {_SETS: Sets.SETS X}
    {_RELS_Properties: RELS_Properties X X X}
    {_RELS_Assoc: RELS_Assoc X X X X X X}
    {_RELS_LeftId: RELS_LeftId X X}
    {_RELS_RightId: RELS_RightId X X}
    {_SETS_Properties: SETS_Properties X}
    (x: X),
    Sets.included
      x
      (clos_refl_trans x).
Proof.
  intros.
  unfold clos_refl_trans.
  unfold Sets.omega_union.
  pose proof Sets_included_indexed_union nat (nsteps x) (S O).
  simpl in H.
  pose proof Rel_concat_id_r x.
  apply Sets_equiv_Sets_included in H0;destruct H0.
  transitivity( x ∘ Rels.id);auto.
Qed.

Lemma in_included:
forall     {A:Type}(a:A)
  (*{_SETS: Sets.SETS (A->Prop)}*) (*为什么这里加上这一句之后sets_unfold就失效了？*)
  (x1 x2:A->Prop),
  Sets.In a x1 -> Sets.included x1 x2-> Sets.In a x2.
Proof.
intros.
revert H H0. sets_unfold. intros. specialize (H0 a). auto.
Qed. 

Lemma indexed_union_include_index:
forall     {A:Type}
  (a:A)
  (xs:nat-> (A->Prop))
  (n:nat),
  Sets.In a (xs n) -> Sets.In a (Sets.indexed_union xs).
Proof.
sets_unfold.
intros.
sets_unfold. exists n. auto.
Qed.

Lemma indexed_union_include_index_iff:
forall     {A:Type}
  (xs:nat-> A->Prop)
  (a:A),
  Sets.In a (Sets.indexed_union xs) <-> exists n:nat, xs n a.
Proof.
unfold iff.
sets_unfold.
intros. split;
sets_unfold;auto.
Qed.   

Lemma rt_trans_concrete:
  forall
  {A B: Type}
  (x: A->list B-> A->Prop)
  (a c d: A) (b1 b2 b12:list B),
    (clos_refl_trans x a b1 c) 
      -> (clos_refl_trans x c b2 d)
      -> b12 = b1++b2
      -> (clos_refl_trans x a b12 d).
Proof.
  intros.
  revert H H0.
  unfold clos_refl_trans.
  unfold Sets.omega_union.
  sets_unfold.
  sets_unfold.
  intros. destruct H. destruct H0.
  pose proof nsteps_n_m x x0 x1.
  assert(nsteps x (x0 + x1) ==nsteps x x0 ∘ nsteps x x1 ). rewrite H2. reflexivity.
  exists (x0+x1)%nat.
  epose proof 
    Rel_Concat_element_concat2 (nsteps x x0)
    (nsteps x x1) (nsteps x (x0+x1)%nat) a c d b1 b2 b12 
    H H0 H1 H3.
  apply H4.
Qed.

Lemma rel_union_or_iff:
	  forall
  {A B: Type}
  (x y: A->list B-> A->Prop)
  (a c: A) (b:list B),
    (x∪y) a b c <-> x a b c \/ y a b c.
Proof.
	intros.
	sets_unfold. reflexivity.
Qed. 

Search iter.
Lemma Nat_iter_succ:
forall {A : Type} (n : nat) (f : A -> A) (x : A), Nat.iter (S n) f x = f (Nat.iter n f x).
Proof.
intros. simpl. auto.
Qed.

Search iter.
Lemma Nat_iter_succ2:
forall (A : Type) (n : nat) (f : A -> A) (x : A), Nat.iter (S n) f x = f (Nat.iter n f x).
Proof.
intros. simpl. auto.
Qed.

