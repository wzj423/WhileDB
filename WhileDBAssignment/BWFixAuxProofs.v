Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import compcert.lib.Integers.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import WhileDB.SetsDomain.
Require Import WhileDB.RelDomain.
Require Import WhileDB.BWFix.
Require Import WhileDB.Lang.

Local Open Scope list.
Local Open Scope bool.
Local Open Scope Z.
Local Open Scope sets.

  (*证明三元关系和subseteq构成一个偏序关系*)
  #[export] Instance R_while_fin {A B C: Type}: Order (A -> B -> C -> Prop) :=
  Sets.included.
#[export] Instance Equiv_while_fin {A B C: Type}: Equiv (A -> B -> C -> Prop) :=
  Sets.equiv.
#[export] Instance PO_while_fin {A B C: Type}: PartialOrder_Setoid (A -> B -> C -> Prop).
Proof.
  split.
  + unfold Reflexive_Setoid.
    unfold equiv, order_rel, R_while_fin, Equiv_while_fin; simpl.
    sets_unfold; intros a b H x y z H0.
    specialize (H x y z). unfold iff in H;destruct H;auto.
  + unfold Transitive.
    unfold equiv, order_rel, R_while_fin, Equiv_while_fin; simpl.
    sets_unfold; intros a b c H H0 x y z.
    specialize (H x y z);specialize (H0 x y z).
    tauto.
  + unfold AntiSymmetric_Setoid.
    unfold equiv, order_rel, R_while_fin, Equiv_while_fin; simpl.
    sets_unfold; intros a b H H0 x y z.
    specialize (H x y z);specialize (H0 x y z).
    tauto.
Qed.
(** 下面再定义上确界计算函数与完备偏序集中的最小值。*)
#[export] Instance oLub_while_fin {A B C: Type}: OmegaLub (A -> B -> C-> Prop) :=
  Sets.omega_union.

#[export] Instance Bot_while_fin {A B C: Type}: Bot (A -> B-> C-> Prop) :=
  ∅: A -> B -> C-> Prop.

(** 下面证明这构成一个Omega完备偏序集。*)
#[export] Instance oCPO_while_fin {A B C: Type}:
  OmegaCompletePartialOrder_Setoid (A -> B -> C-> Prop).
Proof.
  split.
  + apply PO_while_fin.
  + unfold increasing, is_omega_lub, is_omega_ub, is_lb.
    unfold omega_lub, order_rel, R_while_fin, oLub_while_fin; simpl.
    sets_unfold; intros T H.
    split.
    - intros n x y z; intros.
      exists n.
      tauto.
    - intros a H0 x y z H1.
      destruct H1 as [n ?].
      specialize (H0 n x y z).
      tauto.
  + unfold is_least.
    unfold bot, order_rel, R_while_fin, Bot_while_fin; simpl.
    sets_unfold; intros a.
    tauto.
Qed.

(** 额外需要补充一点：_[Equiv_while_fin]_确实是一个等价关系。先前Bourbaki-Witt不
    动点定理的证明中用到了这一前提。证明可见SetsDomain.v*)
#[export] Instance Equiv_equiv_while_fin {A B C: Type}:
  Equivalence (@equiv (A -> B -> C-> Prop) _).
Proof.
  (*Print Sets_equiv_equiv.*)
  apply Sets_equiv_equiv.
Qed.

Print Rels.
(*https://www.cis.upenn.edu/~plclub/blog/2020-05-15-Rewriting-in-Coq/*)

#[export] Instance TriRel_concat_included_congr : 
forall (R S T : Type) (W: Rels.RELS R S T)         {_SETS_R: Sets.SETS R}
        {_SETS_S: Sets.SETS S}
        {_SETS_T: Sets.SETS T}
        {_RELS_Properties: RELS_Properties R S T}
        {_SETS_Properties_R: SETS_Properties R}
        {_SETS_Properties_S: SETS_Properties S}
        {_SETS_Properties_T: SETS_Properties T}
        ,  
Proper
      (Sets.equiv ==> Sets.equiv ==> Sets.equiv)
      (@Rels.concat R S T W).
Proof.
  Compute Rels.concat.
  Print Rels.concat.
  intros.
  Compute @Rels.concat R S T W. 
  Compute @Rels.concat R S T W. 
  Compute R->S->T .
  Compute concat.
  Search concat.
  unfold Proper, respectful. intros.
  apply Sets_equiv_Sets_included. split.
  + apply Rel_concat_mono.
    - rewrite H; reflexivity.
    - rewrite H0; reflexivity.
  + apply Rel_concat_mono.
    - rewrite H; reflexivity.
    - rewrite H0; reflexivity.
Qed.


Lemma Rels_concat_left_mono:
  forall (A B C D: Type) (Y: A -> list B -> C-> Prop),
    mono (fun X: C -> list B -> D-> Prop => Y ∘ X).
Proof.
  intros.
  unfold mono.
  unfold order_rel, R_while_fin.
  intros.
  Compute Rels.concat Y a1.
  pose proof TriRel_concat_included_congr.
  rel_unfold.
  sets_unfold.
  intros. destruct H1 as [? [? [? [? [ ? ?]]]]].
  exists x.
  exists x0. exists x1.
  repeat split;auto.
  revert H. sets_unfold.
  intros. specialize (H x x1 a3). auto.
Qed.

Lemma Rels_concat_left_continuous:
forall (A B C D: Type) (Y: A ->list B -> C-> Prop),
    continuous (fun X: C -> list B -> D -> Prop => Y ∘ X).
Proof.
  intros.
  unfold continuous.
  unfold increasing, omega_lub, order_rel, equiv,
         oLub_while_fin, R_while_fin, Equiv_while_fin, iff.
  sets_unfold; rel_unfold.
  unfold iff.
  intros. split;intros.
  +  destruct H0 as [? [? [? [? [? [? ?]]]]]]. exists x2; exists x; exists x0; exists x1. auto.
  +  destruct H0 as [? [? [? [? [? [? ?]]]]]]. exists x0; exists x1; exists x2. repeat split; try auto. exists x. auto.
Qed.
  
Lemma Rels_concat_left_mono_and_continuous:
  forall
    (A B C D: Type)
    (Y: A -> list B -> C -> Prop)
    (f: (A -> list B -> C -> Prop) -> (C -> list B -> D -> Prop)),
  mono f /\ continuous f ->
  mono (fun X => Y ∘ f X) /\ continuous (fun X => Y ∘ f X).
Proof.
  intros.
  destruct H.
  pose proof Rels_concat_left_mono A B C D Y.
  pose proof Rels_concat_left_continuous A B C D Y.
  split.
  + exact (compose_mono f _ H H1).
  + exact (compose_continuous f _ H H1 H0 H2).
Qed.

(** 下面证明前面提到的步骤(3)：如果_[F]_是单调连续的，那么_[G(X) = Y ∘ F(X)]_也
    是单调连续的。主结论为_[union_right2_mono_and_continuous]_，其用到了两条下面
    的辅助引理以及前面证明过的复合函数单调连续性定理。*)

Lemma union_right2_mono:
  forall (A B C: Type) (Y: A -> list B -> C-> Prop),
    mono (fun X => X ∪ Y).
Proof.
  intros.
  unfold mono.
  unfold order_rel, R_while_fin.
  sets_unfold.
  intros.
  specialize (H a a0 a3).
  tauto.
Qed.

Lemma union_right2_continuous:
  forall (A B C: Type) (Y: A -> list  B -> C-> Prop),
    continuous (fun X => X ∪ Y).
Proof.
  intros.
  unfold continuous.
  unfold increasing, omega_lub, order_rel, equiv,
         oLub_while_fin, R_while_fin, Equiv_while_fin.
  sets_unfold.
  intros. split;intros.
  + destruct H0 as [[? ?] |?]. 
    - exists x; auto.
    - exists O. right;auto.
  + destruct H0 as [n [? | ? ] ].
    2:{  right;auto. }
    { left. exists n. auto.  }
Qed.

Lemma union_right2_mono_and_continuous:
  forall
    (A B C D: Type)
    (Y: C -> list B -> D-> Prop)
    (f: (A -> list B -> C -> Prop) -> (C ->list  B -> D-> Prop)),
  mono f /\ continuous f ->
  mono (fun X => f X ∪ Y) /\ continuous (fun X => f X ∪ Y).
Proof.
  intros.
  destruct H.
  pose proof union_right2_mono _ _ _ Y.
  pose proof union_right2_continuous _ _ _ Y.
  split.
  + exact (compose_mono f _ H H1).
  + exact (compose_continuous f _ H H1 H0 H2).
Qed.
