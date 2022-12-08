Require Import Coq.Classes.Morphisms.
Require Coq.Lists.List.
Require Import WhileDB.SetsDomain.
Local Open Scope sets_scope.

Module Rels.

Class ACCUM (I1 I2 I: Type): Type := {
  app: I1 -> I2 -> I;
}.

Class ACCUM_NIL (I: Type): Type := {
  nil: I;
}.

Class ACCUM_EQ (I: Type): Type :=
  i_equiv: I -> I -> Prop.

Class PRE_RELS (A R S T: Type): Type :=
{
  concat_aux: R -> S -> A -> T
}.

Class PRE_RELS_ID (A R: Type): Type :=
{
  id_aux: A -> R
}.

Class RELS (R S T: Type): Type :=
{
  concat: R -> S -> T
}.

Class RELS_ID (R: Type): Type :=
{
  id: R
}.

End Rels.

#[export] Instance Prop_PRE_RELS
           (A S: Type)
           {_SETS_S: Sets.SETS S}:
  Rels.PRE_RELS A (A -> Prop) S S :=
  {|
    Rels.concat_aux := fun X Y =>
      Sets.test1 X ∩ Sets.lift1 Y
  |}.

#[export] Instance Prop_PRE_RELS_ID (A: Type):
  Rels.PRE_RELS_ID A (A -> Prop) :=
  {|
    Rels.id_aux := fun a b => a = b
  |}.

#[export] Instance lift_PRE_RELS
           (I1 I2 I A R S T: Type)
           {_REL: Rels.PRE_RELS A R S T}
           {_ACC: Rels.ACCUM I1 I2 I}
           {_SETS_T: Sets.SETS T}:
  Rels.PRE_RELS A (I1 -> R) (I2 -> S) (I -> T) :=
  {|
    Rels.concat_aux := fun X Y a i =>
      Sets.indexed_union (Sets.indexed_union (fun i2 i1 =>
        Sets.prop_inj (Rels.app i1 i2 = i) ∩ Rels.concat_aux (X i1) (Y i2) a))
  |}.

#[export] Instance lift_PRE_RELS_ID
           (I A T: Type)
           {_REL_ID: Rels.PRE_RELS_ID A T}
           {_ACC_NIL: Rels.ACCUM_NIL I}
           {_SETS_T: Sets.SETS T}:
  Rels.PRE_RELS_ID A (I -> T) :=
  {|
    Rels.id_aux := fun a i =>
      Sets.intersect
        (Sets.prop_inj (i = Rels.nil))
        (Rels.id_aux a)
  |}.

#[export] Instance Derived_RELS
           (B A R S T: Type)
           {_REL: Rels.PRE_RELS A R S T}
           {_SETS_T: Sets.SETS T}:
  Rels.RELS (B -> R) (A -> S) (B -> T) :=
  {|
    Rels.concat := fun X Y a =>
      Sets.indexed_union (fun b => Rels.concat_aux (X a) (Y b) b)
  |}.

#[export] Instance Derived_RELS_ID
           (A T: Type)
           {_REL_ID: Rels.PRE_RELS_ID A T}
           {_SETS_T: Sets.SETS T}:
  Rels.RELS_ID (A -> T) :=
  {|
    Rels.id := Rels.id_aux
  |}.

Goal forall X Y: nat -> nat -> Prop, Rels.concat X Y = fun a c => exists b, X a b /\ Y b c.
  intros.
  reflexivity.
Qed.

Goal forall X: nat -> Prop, Rels.concat Rels.id X = fun a => exists b, a = b /\ X b.
  intros.
  reflexivity.
Qed.

Class ACCUM_Assoc
        (I1 I2 I3 I12 I23 I123: Type)
        {_ACC_1_2: Rels.ACCUM I1 I2 I12}
        {_ACC_2_3: Rels.ACCUM I2 I3 I23}
        {_ACC_12_3: Rels.ACCUM I12 I3 I123}
        {_ACC_1_23: Rels.ACCUM I1 I23 I123}: Prop :=
{
  app_assoc: forall i1 i2 i3,
    Rels.app (Rels.app i1 i2) i3 = Rels.app i1 (Rels.app i2 i3);
}.

Class ACCUM_LeftId
        (I1 I2: Type)
        {_ACC: Rels.ACCUM I1 I2 I2}
        {_ACC_NIL: Rels.ACCUM_NIL I1}: Prop :=
{
  app_nil_l_setoid: forall i,
    Rels.app Rels.nil i = i
}.

Class ACCUM_RightId
        (I1 I2: Type)
        {_ACC: Rels.ACCUM I1 I2 I1}
        {_ACC_NIL: Rels.ACCUM_NIL I2}: Prop :=
{
  app_nil_r_setoid: forall i,
    Rels.app i Rels.nil = i;
}.

Class PRE_RELS_Properties
        (A R S T: Type)
        {_REL: Rels.PRE_RELS A R S T}
        {_SETS_R: Sets.SETS R}
        {_SETS_S: Sets.SETS S}
        {_SETS_T: Sets.SETS T}: Prop :=
{
  Rel_concat_union_distr_r_aux:
    forall x1 x2 y a,
      Sets.equiv
        (Rels.concat_aux (x1 ∪ x2) y a)
        (Rels.concat_aux x1 y a ∪ Rels.concat_aux x2 y a);
  Rel_concat_union_distr_l_aux:
    forall x y1 y2 a,
      Sets.equiv
        (Rels.concat_aux x (y1 ∪ y2) a)
        (Rels.concat_aux x y1 a ∪ Rels.concat_aux x y2 a);
  Rel_concat_indexed_union_distr_r_aux:
    forall {I} (xs: I -> _) y a,
      Sets.equiv
        (Rels.concat_aux (Sets.indexed_union xs) y a)
        (Sets.indexed_union (fun i => Rels.concat_aux (xs i) y a));
  Rel_concat_indexed_union_distr_l_aux:
    forall {I} x (ys: I -> _) a,
      Sets.equiv
        (Rels.concat_aux x (Sets.indexed_union ys) a)
        (Sets.indexed_union (fun i => Rels.concat_aux x (ys i) a));
  Rel_concat_prop_inj_intersect_l_aux:
    forall x P y a,
      Sets.equiv
        (Rels.concat_aux x (Sets.intersect (Sets.prop_inj P) y) a)
        (Sets.intersect (Sets.prop_inj P) (Rels.concat_aux x y a));
  Rel_concat_prop_inj_intersect_r_aux:
    forall x P y a,
      Sets.equiv
        (Rels.concat_aux (Sets.intersect (Sets.prop_inj P) x) y a)
        (Sets.intersect (Sets.prop_inj P) (Rels.concat_aux x y a));
  Rel_concat_mono_aux:>
    forall a,
      Proper
        (Sets.included ==> Sets.included ==> Sets.included)
        (fun x y => @Rels.concat_aux _ _ _ _ _REL x y a)
}.

Class RELS_Properties
        (R S T: Type)
        {_REL: Rels.RELS R S T}
        {_SETS_R: Sets.SETS R}
        {_SETS_S: Sets.SETS S}
        {_SETS_T: Sets.SETS T}: Prop :=
{
  Rel_concat_union_distr_r:
    forall x1 x2 y,
      Sets.equiv
        (Rels.concat (x1 ∪ x2) y)
        (Rels.concat x1 y ∪ Rels.concat x2 y);
  Rel_concat_union_distr_l:
    forall x y1 y2,
      Sets.equiv
        (Rels.concat x (y1 ∪ y2))
        (Rels.concat x y1 ∪ Rels.concat x y2);
  Rel_concat_indexed_union_distr_r:
    forall {I} (xs: I -> _) y,
      Sets.equiv
        (Rels.concat (Sets.indexed_union xs) y)
        (Sets.indexed_union (fun i => Rels.concat (xs i) y));
  Rel_concat_indexed_union_distr_l:
    forall {I} x (ys: I -> _),
      Sets.equiv
        (Rels.concat x (Sets.indexed_union ys))
        (Sets.indexed_union (fun i => Rels.concat x (ys i)));
  Rel_concat_mono:>
    Proper
      (Sets.included ==> Sets.included ==> Sets.included)
      (@Rels.concat _ _ _ _REL)
}.

Class PRE_RELS_Assoc
        (A12 A23 X1 X2 X3 X12 X23 X123: Type)
        {_REL_1_2: Rels.PRE_RELS A12 X1 X2 X12}
        {_REL_12_3: Rels.PRE_RELS A23 X12 X3 X123}
        {_REL_2_3: Rels.PRE_RELS A23 X2 X3 X23}
        {_REL_1_23: Rels.PRE_RELS A12 X1 X23 X123}
        {_SETS: Sets.SETS X123}: Prop :=
{
  Rel_concat_assoc_aux:
    forall (x: X1) (y: X2) (z: X3) (axy: A12) (ayz: A23),
      Sets.equiv
        (Rels.concat_aux (Rels.concat_aux x y axy) z ayz)
        (Rels.concat_aux x (Rels.concat_aux y z ayz) axy)
}.

Class RELS_Assoc
        (X1 X2 X3 X12 X23 X123: Type)
        {_REL_1_2: Rels.RELS X1 X2 X12}
        {_REL_12_3: Rels.RELS X12 X3 X123}
        {_REL_2_3: Rels.RELS X2 X3 X23}
        {_REL_1_23: Rels.RELS X1 X23 X123}
        {_SETS: Sets.SETS X123}: Prop :=
{
  Rel_concat_assoc: 
    forall (x: X1) (y: X2) (z: X3),
      Sets.equiv
        (Rels.concat (Rels.concat x y) z)
        (Rels.concat x (Rels.concat y z))
}.

Class PRE_RELS_LeftId
        (A X Y: Type)
        {_REL: Rels.PRE_RELS A X Y Y}
        {_REL_ID: Rels.PRE_RELS_ID A X}
        {_SETS: Sets.SETS Y}: Prop :=
{
  Rel_concat_id_l_aux:
    forall a b y,
      Sets.equiv
        (Rels.concat_aux (Rels.id_aux a) y b)
        (Sets.intersect (Sets.prop_inj (a = b)) y)
}.

Class PRE_RELS_RightId
        (A X Y: Type)
        {_REL: Rels.PRE_RELS A X Y X}
        {_REL_ID: Rels.PRE_RELS_ID A Y}
        {_SETS: Sets.SETS X}: Prop :=
{
  Rel_concat_id_r_aux:
    forall x,
      Sets.equiv
        (Sets.indexed_union (fun a => (Rels.concat_aux x (Rels.id_aux a) a)))
        x
}.

Class RELS_LeftId
        (X Y: Type)
        {_REL: Rels.RELS X Y Y}
        {_REL_ID: Rels.RELS_ID X}
        {_SETS: Sets.SETS Y}: Prop :=
{
  Rel_concat_id_l:
    forall y,
      Sets.equiv
        (Rels.concat Rels.id y) y
}.

Class RELS_RightId
        (X Y: Type)
        {_REL: Rels.RELS X Y X}
        {_REL_ID: Rels.RELS_ID Y}
        {_SETS: Sets.SETS X}: Prop :=
{
  Rel_concat_id_r:
    forall x,
      Sets.equiv
        (Rels.concat x Rels.id) x
}.

#[export] Instance Prop_PRE_RELS_Properties
           {A S}
           {_SETS_S: Sets.SETS S}
           {_SETS_S_Properties: SETS_Properties S}:
  PRE_RELS_Properties A (A -> Prop) S S.
Proof.
  constructor.
  + intros; simpl.
    unfold Sets.test1, Sets.lift1, lift_SETS; simpl.
    unfold Sets.intersect; simpl.
    unfold Sets.lift_intersect.
    rewrite <- Sets_intersect_union_distr_r.
    rewrite <- Sets_prop_inj_or.
    reflexivity.
  + intros; simpl.
    unfold Sets.test1, Sets.lift1, lift_SETS; simpl.
    unfold Sets.intersect; simpl.
    unfold Sets.lift_intersect.
    rewrite <- Sets_intersect_union_distr_l.
    reflexivity.
  + intros; simpl.
    unfold Sets.test1, Sets.lift1, lift_SETS; simpl.
    unfold Sets.intersect; simpl.
    unfold Sets.lift_intersect.
    rewrite <- Sets_intersect_indexed_union_distr_r.
    rewrite <- Sets_prop_inj_ex.
    reflexivity.
  + intros; simpl.
    unfold Sets.test1, Sets.lift1, lift_SETS; simpl.
    unfold Sets.intersect; simpl.
    unfold Sets.lift_intersect.
    rewrite <- Sets_intersect_indexed_union_distr_l.
    reflexivity.
  + intros; simpl.
    unfold Sets.test1, Sets.lift1, lift_SETS; simpl.
    unfold Sets.intersect at 1 4; simpl.
    unfold Sets.lift_intersect. 
    rewrite <- !Sets_intersect_assoc.
    rewrite (Sets_intersect_comm (Sets.prop_inj _)).
    reflexivity.
  + intros; simpl.
    unfold Sets.test1, Sets.lift1, lift_SETS; simpl.
    unfold Sets.intersect at 1 4; simpl.
    unfold Sets.lift_intersect.
    rewrite <- Sets_intersect_assoc.
    rewrite <- Sets_prop_inj_and.
    reflexivity.
  + intros.
    unfold Proper, respectful.
    simpl; intros.
    apply Sets_intersect_mono; auto.
    unfold Sets.test1.
    apply Sets_prop_inj_included_prop_inj.
    apply H.
Qed.

#[export] Instance lift_PRE_RELS_Properties
           {A R S T I1 I2 I}
           {_REL: Rels.PRE_RELS A R S T}
           {_ACC: Rels.ACCUM I1 I2 I}
           {_SETS_R: Sets.SETS R}
           {_SETS_S: Sets.SETS S}
           {_SETS_T: Sets.SETS T}
           {_RELS_Properties: PRE_RELS_Properties A R S T}
           {_SETS_R_Properties: SETS_Properties R}
           {_SETS_S_Properties: SETS_Properties S}
           {_SETS_T_Properties: SETS_Properties T}:
  PRE_RELS_Properties A (I1 -> R) (I2 -> S) (I -> T).
Proof.
  constructor.
  + intros.
    sets_unfold.
    intros i; simpl.
    unfold Sets.lift_indexed_union.
    apply Sets_equiv_Sets_included; split.
    - apply Sets_indexed_union_included; intros i2.
      unfold Sets.lift_indexed_union; simpl.
      apply Sets_indexed_union_included; intros i1.
      apply Sets_prop_inj_included; intros.
      rewrite Rel_concat_union_distr_r_aux.
      apply Sets_union_mono.
      * rewrite <- (Sets_included_indexed_union _ _ i2).
        rewrite <- (Sets_included_indexed_union _ _ i1).
        apply Sets_included_intersect; [| reflexivity].
        apply Sets_included_prop_inj; auto.
      * rewrite <- (Sets_included_indexed_union _ _ i2).
        rewrite <- (Sets_included_indexed_union _ _ i1).
        apply Sets_included_intersect; [| reflexivity].
        apply Sets_included_prop_inj; auto.
    - apply Sets_union_included.
      * apply Sets_indexed_union_mono; intros i2.
        apply Sets_indexed_union_mono; intros i1.
        rewrite Rel_concat_union_distr_r_aux.
        apply Sets_intersect_mono; [reflexivity |].
        apply Sets_included_union1.
      * apply Sets_indexed_union_mono; intros i2.
        apply Sets_indexed_union_mono; intros i1.
        rewrite Rel_concat_union_distr_r_aux.
        apply Sets_intersect_mono; [reflexivity |].
        apply Sets_included_union2.
  + intros.
    sets_unfold.
    intros i; simpl.
    unfold Sets.lift_indexed_union.
    apply Sets_equiv_Sets_included; split.     
    - apply Sets_indexed_union_included; intros i2.
      apply Sets_indexed_union_included; intros i1.
      apply Sets_prop_inj_included; intros.
      rewrite Rel_concat_union_distr_l_aux.
      apply Sets_union_mono.
      * rewrite <- (Sets_included_indexed_union _ _ i2).
        rewrite <- (Sets_included_indexed_union _ _ i1).
        apply Sets_included_intersect; [| reflexivity].
        apply Sets_included_prop_inj; auto.
      * rewrite <- (Sets_included_indexed_union _ _ i2).
        rewrite <- (Sets_included_indexed_union _ _ i1).
        apply Sets_included_intersect; [| reflexivity].
        apply Sets_included_prop_inj; auto.
    - apply Sets_union_included.
      * apply Sets_indexed_union_mono; intros i2.
        apply Sets_indexed_union_mono; intros i1.
        rewrite Rel_concat_union_distr_l_aux.
        apply Sets_intersect_mono; [reflexivity |].
        apply Sets_included_union1.
      * apply Sets_indexed_union_mono; intros i2.
        apply Sets_indexed_union_mono; intros i1.
        rewrite Rel_concat_union_distr_l_aux.
        apply Sets_intersect_mono; [reflexivity |].
        apply Sets_included_union2.
  + intros.
    simpl.
    sets_unfold; intros i; simpl.
    unfold Sets.lift_indexed_union.
    apply Sets_equiv_Sets_included; split.     
    - apply Sets_indexed_union_included; intros i2.
      apply Sets_indexed_union_included; intros i1.
      apply Sets_prop_inj_included; intros.
      rewrite Rel_concat_indexed_union_distr_r_aux.
      apply Sets_indexed_union_mono; intros i0.
      rewrite <- (Sets_included_indexed_union _ _ i2).
      rewrite <- (Sets_included_indexed_union _ _ i1).
      apply Sets_included_intersect; [| reflexivity].
      apply Sets_included_prop_inj; auto.
    - apply Sets_indexed_union_included; intros i0.
      apply Sets_indexed_union_included; intros i2.
      apply Sets_indexed_union_included; intros i1.
      apply Sets_prop_inj_included; intros.
      rewrite <- (Sets_included_indexed_union _ _ i2).
      rewrite <- (Sets_included_indexed_union _ _ i1).
      apply Sets_included_intersect.
      * apply Sets_included_prop_inj; auto.
      * apply Rel_concat_mono_aux; [| reflexivity].
        rewrite <- (Sets_included_indexed_union _ _ i0).
        reflexivity.
  + intros.
    simpl.
    sets_unfold; intros i; simpl.
    unfold Sets.lift_indexed_union.
    apply Sets_equiv_Sets_included; split.     
    - apply Sets_indexed_union_included; intros i2.
      apply Sets_indexed_union_included; intros i1.
      apply Sets_prop_inj_included; intros.
      rewrite Rel_concat_indexed_union_distr_l_aux.
      apply Sets_indexed_union_mono; intros i0.
      rewrite <- (Sets_included_indexed_union _ _ i2).
      rewrite <- (Sets_included_indexed_union _ _ i1).
      apply Sets_included_intersect; [| reflexivity].
      apply Sets_included_prop_inj; auto.
    - apply Sets_indexed_union_included; intros i0.
      apply Sets_indexed_union_included; intros i2.
      apply Sets_indexed_union_included; intros i1.
      apply Sets_prop_inj_included; intros.
      rewrite <- (Sets_included_indexed_union _ _ i2).
      rewrite <- (Sets_included_indexed_union _ _ i1).
      apply Sets_included_intersect.
      * apply Sets_included_prop_inj; auto.
      * apply Rel_concat_mono_aux; [reflexivity |].
        rewrite <- (Sets_included_indexed_union _ _ i0).
        reflexivity.
  + intros.
    simpl.
    sets_unfold; intros i; simpl.
    unfold Sets.lift_indexed_union.
    apply Sets_equiv_Sets_included; split.     
    - apply Sets_indexed_union_included; intros i2.
      apply Sets_indexed_union_included; intros i1.
      apply Sets_prop_inj_included; intros.
      rewrite Rel_concat_prop_inj_intersect_l_aux.
      apply Sets_prop_inj_included; intros.
      apply Sets_included_intersect; [apply Sets_included_prop_inj; auto |].
      rewrite <- (Sets_included_indexed_union _ _ i2).
      rewrite <- (Sets_included_indexed_union _ _ i1).
      apply Sets_included_intersect; [| reflexivity].
      apply Sets_included_prop_inj; auto.
    - apply Sets_prop_inj_included; intros.
      apply Sets_indexed_union_included; intros i2.
      apply Sets_indexed_union_included; intros i1.
      apply Sets_prop_inj_included; intros.
      rewrite <- (Sets_included_indexed_union _ _ i2).
      rewrite <- (Sets_included_indexed_union _ _ i1).
      rewrite Rel_concat_prop_inj_intersect_l_aux.
      apply Sets_included_intersect; [| apply Sets_included_intersect].
      * apply Sets_included_prop_inj; auto.
      * apply Sets_included_prop_inj; auto.
      * reflexivity.
  + intros.
    simpl.
    sets_unfold; intros i; simpl.
    unfold Sets.lift_indexed_union.
    apply Sets_equiv_Sets_included; split.     
    - apply Sets_indexed_union_included; intros i2.
      apply Sets_indexed_union_included; intros i1.
      apply Sets_prop_inj_included; intros.
      rewrite Rel_concat_prop_inj_intersect_r_aux.
      apply Sets_prop_inj_included; intros.
      apply Sets_included_intersect; [apply Sets_included_prop_inj; auto |].
      rewrite <- (Sets_included_indexed_union _ _ i2).
      rewrite <- (Sets_included_indexed_union _ _ i1).
      apply Sets_included_intersect; [| reflexivity].
      apply Sets_included_prop_inj; auto.
    - apply Sets_prop_inj_included; intros.
      apply Sets_indexed_union_included; intros i2.
      apply Sets_indexed_union_included; intros i1.
      apply Sets_prop_inj_included; intros.
      rewrite <- (Sets_included_indexed_union _ _ i2).
      rewrite <- (Sets_included_indexed_union _ _ i1).
      rewrite Rel_concat_prop_inj_intersect_r_aux.
      apply Sets_included_intersect; [| apply Sets_included_intersect].
      * apply Sets_included_prop_inj; auto.
      * apply Sets_included_prop_inj; auto.
      * reflexivity.
  + intros a; unfold Proper, respectful; intros.
    simpl.
    sets_unfold; intros i; simpl.
    unfold Sets.lift_indexed_union.
    apply Sets_indexed_union_mono; intros i2.
    apply Sets_indexed_union_mono; intros i1.
    apply Sets_intersect_mono; [reflexivity |].
    apply Rel_concat_mono_aux; auto.
Qed.

#[export] Instance Deriveds_RELS_Properties
           {B A R S T}
           {_REL: Rels.PRE_RELS A R S T}
           {_SETS_R: Sets.SETS R}
           {_SETS_S: Sets.SETS S}
           {_SETS_T: Sets.SETS T}
           {_RELS_Properties: PRE_RELS_Properties A R S T}
           {_SETS_T_Properties: SETS_Properties T}:
  RELS_Properties (B -> R) (A -> S) (B -> T).
Proof.
  intros.
  constructor.
  + intros; simpl.
    sets_unfold.
    intros b.
    apply Sets_equiv_Sets_included; split.     
    - apply Sets_indexed_union_included; intros a.
      rewrite Rel_concat_union_distr_r_aux.
      apply Sets_union_mono.
      * rewrite <- (Sets_included_indexed_union _ _ a).
        reflexivity.
      * rewrite <- (Sets_included_indexed_union _ _ a).
        reflexivity.
    - apply Sets_union_included.
      * apply Sets_indexed_union_mono; intros a.
        rewrite Rel_concat_union_distr_r_aux.
        apply Sets_included_union1.
      * apply Sets_indexed_union_mono; intros a.
        rewrite Rel_concat_union_distr_r_aux.
        apply Sets_included_union2.
  + intros; simpl.
    sets_unfold.
    intros b.
    apply Sets_equiv_Sets_included; split.     
    - apply Sets_indexed_union_included; intros a.
      rewrite Rel_concat_union_distr_l_aux.
      apply Sets_union_mono.
      * rewrite <- (Sets_included_indexed_union _ _ a).
        reflexivity.
      * rewrite <- (Sets_included_indexed_union _ _ a).
        reflexivity.
    - apply Sets_union_included.
      * apply Sets_indexed_union_mono; intros a.
        rewrite Rel_concat_union_distr_l_aux.
        apply Sets_included_union1.
      * apply Sets_indexed_union_mono; intros a.
        rewrite Rel_concat_union_distr_l_aux.
        apply Sets_included_union2.
  + intros; simpl.
    sets_unfold.
    intros b; simpl.
    unfold Sets.lift_indexed_union.
    apply Sets_equiv_Sets_included; split.     
    - apply Sets_indexed_union_included; intros a.
      rewrite Rel_concat_indexed_union_distr_r_aux.
      apply Sets_indexed_union_mono; intros i.
      rewrite <- (Sets_included_indexed_union _ _ a).
      reflexivity.
    - apply Sets_indexed_union_included; intros i.
      apply Sets_indexed_union_mono; intros a.
      rewrite Rel_concat_indexed_union_distr_r_aux.
      rewrite <- (Sets_included_indexed_union _ _ i).
      reflexivity.
  + intros; simpl.
    sets_unfold.
    intros b; simpl.
    unfold Sets.lift_indexed_union.
    apply Sets_equiv_Sets_included; split.     
    - apply Sets_indexed_union_included; intros a.
      rewrite Rel_concat_indexed_union_distr_l_aux.
      apply Sets_indexed_union_mono; intros i.
      rewrite <- (Sets_included_indexed_union _ _ a).
      reflexivity.
    - apply Sets_indexed_union_included; intros i.
      apply Sets_indexed_union_mono; intros a.
      rewrite Rel_concat_indexed_union_distr_l_aux.
      rewrite <- (Sets_included_indexed_union _ _ i).
      reflexivity.
  + unfold Proper, respectful.
    simpl; intros.
    intros b.
    apply Sets_indexed_union_mono; intros a.
    apply Rel_concat_mono_aux; auto.
Qed.

#[export] Instance Prop_PRE_RELS_Assoc
           {A B S}
           {_SETS_S: Sets.SETS S}
           {_SETS_S_Properties: SETS_Properties S}:
  PRE_RELS_Assoc A B (A -> Prop) (B -> Prop) S (B -> Prop) S S.
Proof.
  constructor.
  intros.
  simpl.
  sets_unfold.
  unfold Sets.lift1.
  rewrite <- Sets_intersect_assoc.
  rewrite Sets_prop_inj_and.
  reflexivity.
Qed.

#[export] Instance lift_PRE_RELS_Assoc
           (A12 A23 I1 I2 I3 I12 I23 I123 X1 X2 X3 X12 X23 X123: Type)
           {_REL_1_2: Rels.PRE_RELS A12 X1 X2 X12}
           {_REL_12_3: Rels.PRE_RELS A23 X12 X3 X123}
           {_REL_2_3: Rels.PRE_RELS A23 X2 X3 X23}
           {_REL_1_23: Rels.PRE_RELS A12 X1 X23 X123}
           {_ACC_1_2: Rels.ACCUM I1 I2 I12}
           {_ACC_2_3: Rels.ACCUM I2 I3 I23}
           {_ACC_12_3: Rels.ACCUM I12 I3 I123}
           {_ACC_1_23: Rels.ACCUM I1 I23 I123}
           {_SETS_1: Sets.SETS X1}
           {_SETS_3: Sets.SETS X3}
           {_SETS_12: Sets.SETS X12}
           {_SETS_23: Sets.SETS X23}
           {_SETS_123: Sets.SETS X123}
           {_PRE_RELS_Assoc: PRE_RELS_Assoc A12 A23 X1 X2 X3 X12 X23 X123}
           {_PRE_RELS_Properties_1_23: PRE_RELS_Properties A12 X1 X23 X123}
           {_PRE_RELS_Properties_12_3: PRE_RELS_Properties A23 X12 X3 X123}
           {_ACCUM_Assoc: ACCUM_Assoc I1 I2 I3 I12 I23 I123}
           {_SETS_Properties: SETS_Properties X123}:
  PRE_RELS_Assoc A12 A23 (I1 -> X1) (I2 -> X2) (I3 -> X3) (I12 -> X12) (I23 -> X23) (I123 -> X123).
Proof.
  constructor.
  intros.
  unfold lift_PRE_RELS.
  simpl.
  intros i.
  unfold Sets.lift_indexed_union.
  apply Sets_equiv_Sets_included.
  split.
  + apply Sets_indexed_union_included.
    intros i12.
    apply Sets_indexed_union_included.
    intros i3.
    apply Sets_prop_inj_included; intros.
    rewrite Rel_concat_indexed_union_distr_r_aux.
    apply Sets_indexed_union_included.
    intros i1.
    rewrite Rel_concat_indexed_union_distr_r_aux.
    apply Sets_indexed_union_included.
    intros i2.
    rewrite Rel_concat_prop_inj_intersect_r_aux.
    apply Sets_prop_inj_included; intros.
    rewrite <- (Sets_included_indexed_union _ _ i1).
    rewrite <- (Sets_included_indexed_union _ _ (Rels.app i2 i3)).
    apply Sets_included_intersect. {
      apply Sets_included_prop_inj.
      rewrite <- app_assoc.
      rewrite <- H, <- H0.
      reflexivity.
    }
    rewrite Rel_concat_indexed_union_distr_l_aux.
    rewrite <- (Sets_included_indexed_union _ _ i2).
    rewrite Rel_concat_indexed_union_distr_l_aux.
    rewrite <- (Sets_included_indexed_union _ _ i3).
    rewrite Rel_concat_prop_inj_intersect_l_aux.
    apply Sets_included_intersect; [apply Sets_included_prop_inj; reflexivity |].
    rewrite Rel_concat_assoc_aux; reflexivity.
  + apply Sets_indexed_union_included.
    intros i1.
    apply Sets_indexed_union_included.
    intros i23.
    apply Sets_prop_inj_included; intros.
    rewrite Rel_concat_indexed_union_distr_l_aux.
    apply Sets_indexed_union_included.
    intros i2.
    rewrite Rel_concat_indexed_union_distr_l_aux.
    apply Sets_indexed_union_included.
    intros i3.
    rewrite Rel_concat_prop_inj_intersect_l_aux.
    apply Sets_prop_inj_included; intros.
    rewrite <- (Sets_included_indexed_union _ _ (Rels.app i1 i2)).
    rewrite <- (Sets_included_indexed_union _ _ i3).
    apply Sets_included_intersect. {
      apply Sets_included_prop_inj.
      rewrite app_assoc.
      rewrite <- H, <- H0; reflexivity.
    }
    rewrite Rel_concat_indexed_union_distr_r_aux.
    rewrite <- (Sets_included_indexed_union _ _ i1).
    rewrite Rel_concat_indexed_union_distr_r_aux.
    rewrite <- (Sets_included_indexed_union _ _ i2).
    rewrite Rel_concat_prop_inj_intersect_r_aux.
    apply Sets_included_intersect; [apply Sets_included_prop_inj; reflexivity |].
    rewrite Rel_concat_assoc_aux; reflexivity.
Qed.

#[export] Instance Derived_RELS_Assoc
           (B A12 A23 X1 X2 X3 X12 X23 X123: Type)
           {_REL_1_2: Rels.PRE_RELS A12 X1 X2 X12}
           {_REL_12_3: Rels.PRE_RELS A23 X12 X3 X123}
           {_REL_2_3: Rels.PRE_RELS A23 X2 X3 X23}
           {_REL_1_23: Rels.PRE_RELS A12 X1 X23 X123}
           {_SETS_1: Sets.SETS X1}
           {_SETS_3: Sets.SETS X3}
           {_SETS_12: Sets.SETS X12}
           {_SETS_23: Sets.SETS X23}
           {_SETS_123: Sets.SETS X123}
           {_PRE_RELS_Assoc: PRE_RELS_Assoc A12 A23 X1 X2 X3 X12 X23 X123}
           {_PRE_RELS_Properties_1_23: PRE_RELS_Properties A12 X1 X23 X123}
           {_PRE_RELS_Properties_12_3: PRE_RELS_Properties A23 X12 X3 X123}
           {_SETS_1_Properties: SETS_Properties X1}
           {_SETS_3_Properties: SETS_Properties X3}
           {_SETS_12_Properties: SETS_Properties X12}
           {_SETS_23_Properties: SETS_Properties X23}
           {_SETS_Properties: SETS_Properties X123}:
  RELS_Assoc (B -> X1) (A12 -> X2) (A23 -> X3) (B -> X12) (A12 -> X23) (B -> X123).
Proof.
  intros.
  constructor.
  intros.
  simpl.
  intros b.
  apply Sets_equiv_Sets_included.
  split.
  + apply Sets_indexed_union_included.
    intros ayz.
    rewrite Rel_concat_indexed_union_distr_r_aux.
    apply Sets_indexed_union_included.
    intros axy.
    rewrite Rel_concat_assoc_aux.
    rewrite <- (Sets_included_indexed_union _ _ axy).
    apply Rel_concat_mono_aux; [reflexivity |].
    rewrite <- (Sets_included_indexed_union _ _ ayz).
    reflexivity.
  + apply Sets_indexed_union_included.
    intros axy.
    rewrite Rel_concat_indexed_union_distr_l_aux.
    apply Sets_indexed_union_included.
    intros ayz.
    rewrite <- Rel_concat_assoc_aux.
    rewrite <- (Sets_included_indexed_union _ _ ayz).
    apply Rel_concat_mono_aux; [| reflexivity].
    rewrite <- (Sets_included_indexed_union _ _ axy).
    reflexivity.
Qed.

#[export] Instance Prop_PRE_RELS_LeftId
           (A X: Type)
           {_SETS: Sets.SETS X}
           {_SETS_Properties: SETS_Properties X}:
  PRE_RELS_LeftId A (A -> Prop) X.
Proof.
  constructor.
  intros; simpl.
  sets_unfold.
  unfold Sets.lift1.
  reflexivity.
Qed.

#[export] Instance lift_PRE_RELS_LeftId
           (I1 I2 A X Y: Type)
           {_ACC: Rels.ACCUM I1 I2 I2}
           {_ACC_NIL: Rels.ACCUM_NIL I1}
           {_RELS: Rels.PRE_RELS A X Y Y}
           {_RELS_Id: Rels.PRE_RELS_ID A X}
           {_SETS_X: Sets.SETS X}
           {_SETS_Y: Sets.SETS Y}
           {_SETS_X_Properties: SETS_Properties X}
           {_SETS_Y_Properties: SETS_Properties Y}
           {_RELS_Properties: PRE_RELS_Properties A X Y Y}
           {_ACC_LeftId: ACCUM_LeftId I1 I2}
           {_RELS_LeftId: PRE_RELS_LeftId A X Y}:
  PRE_RELS_LeftId A (I1 -> X) (I2 -> Y).
Proof.
  constructor.
  intros; simpl.
  sets_unfold.
  intros i2.
  unfold Sets.lift_indexed_union.
  apply Sets_equiv_Sets_included.
  split.
  + apply Sets_indexed_union_included; intros i1.
    apply Sets_indexed_union_included; intros i2'.
    apply Sets_prop_inj_included; intros.
    rewrite Rel_concat_prop_inj_intersect_r_aux.
    apply Sets_prop_inj_included; intros.
    rewrite H0, app_nil_l_setoid in H.
    rewrite Rel_concat_id_l_aux.
    rewrite H; reflexivity.
  + rewrite <- (Sets_included_indexed_union _ _ Rels.nil).
    rewrite <- (Sets_included_indexed_union _ _ i2).
    apply Sets_included_intersect.
    - apply Sets_included_prop_inj.
      apply app_nil_l_setoid.
    - rewrite Rel_concat_prop_inj_intersect_r_aux.
      apply Sets_included_intersect.
      * apply Sets_included_prop_inj; reflexivity.
      * rewrite Rel_concat_id_l_aux.
        reflexivity.
Qed.

#[export] Instance Prop_PRE_RELS_RightId
           (A: Type):
  PRE_RELS_RightId A (A -> Prop) (A -> Prop).
Proof.
  constructor.
  sets_unfold.
  simpl.
  sets_unfold.
  intros.
  split; intros.
  + destruct H as [? [? ?]]; subst; tauto.
  + eauto.
Qed.

#[export] Instance lift_PRE_RELS_RightId
           (I1 I2 A X Y: Type)
           {_ACC: Rels.ACCUM I1 I2 I1}
           {_ACC_NIL: Rels.ACCUM_NIL I2}
           {_RELS: Rels.PRE_RELS A X Y X}
           {_RELS_Id: Rels.PRE_RELS_ID A Y}
           {_SETS_X: Sets.SETS X}
           {_SETS_Y: Sets.SETS Y}
           {_SETS_X_Properties: SETS_Properties X}
           {_SETS_Y_Properties: SETS_Properties Y}
           {_RELS_Properties: PRE_RELS_Properties A X Y X}
           {_ACC_LeftId: ACCUM_RightId I1 I2}
           {_RELS_LeftId: PRE_RELS_RightId A X Y}:
  PRE_RELS_RightId A (I1 -> X) (I2 -> Y).
Proof.
  constructor.
  intros; simpl.
  sets_unfold.
  intros i1.
  unfold Sets.lift_indexed_union.
  apply Sets_equiv_Sets_included.
  split.
  + apply Sets_indexed_union_included; intros a.
    apply Sets_indexed_union_included; intros i1'.
    apply Sets_indexed_union_included; intros i2.
    apply Sets_prop_inj_included; intros.
    rewrite Rel_concat_prop_inj_intersect_l_aux.
    apply Sets_prop_inj_included; intros.
    rewrite H0, app_nil_r_setoid in H.
    rewrite <- (Rel_concat_id_r_aux (x i1)).
    rewrite <- (Sets_included_indexed_union _ _ a).
    rewrite H; reflexivity.
  + rewrite <- (Rel_concat_id_r_aux (x i1)).
    apply Sets_indexed_union_included; intros a.
    rewrite <- (Sets_included_indexed_union _ _ a).
    rewrite <- (Sets_included_indexed_union _ _ i1).
    rewrite <- (Sets_included_indexed_union _ _ Rels.nil).
    apply Sets_included_intersect.
    - apply Sets_included_prop_inj.
      apply app_nil_r_setoid.
    - rewrite Rel_concat_prop_inj_intersect_l_aux.
      apply Sets_included_intersect.
      * apply Sets_included_prop_inj; reflexivity.
      * reflexivity.
Qed.

#[export] Instance Derived_RELS_LeftId
           (A X Y: Type)
           {_RELS: Rels.PRE_RELS A X Y Y}
           {_RELS_Id: Rels.PRE_RELS_ID A X}
           {_SETS_X: Sets.SETS X}
           {_SETS_Y: Sets.SETS Y}
           {_SETS_X_Properties: SETS_Properties X}
           {_SETS_Y_Properties: SETS_Properties Y}
           {_RELS_Properties: PRE_RELS_Properties A X Y Y}
           {_RELS_LeftID: PRE_RELS_LeftId A X Y}:
  RELS_LeftId (A -> X) (A -> Y).
Proof.
  constructor.
  intros.
  simpl.
  sets_unfold.
  intros a.
  apply Sets_equiv_Sets_included.
  split.
  + apply Sets_indexed_union_included; intros b.
    rewrite Rel_concat_id_l_aux.
    apply Sets_prop_inj_included; intros.
    rewrite H; reflexivity.
  + rewrite <- (Sets_included_indexed_union _ _ a).
    rewrite Rel_concat_id_l_aux.
    apply Sets_included_intersect.
    - apply Sets_included_prop_inj.
      reflexivity.
    - reflexivity.
Qed.

#[export] Instance Derived_RELS_RightId
           (A X Y: Type)
           {_RELS: Rels.PRE_RELS A X Y X}
           {_RELS_Id: Rels.PRE_RELS_ID A Y}
           {_SETS_X: Sets.SETS X}
           {_SETS_Y: Sets.SETS Y}
           {_SETS_X_Properties: SETS_Properties X}
           {_SETS_Y_Properties: SETS_Properties Y}
           {_RELS_Properties: PRE_RELS_Properties A X Y X}
           {_RELS_LeftID: PRE_RELS_RightId A X Y}:
  RELS_RightId (A -> X) (A -> Y).
Proof.
  constructor.
  intros.
  simpl.
  sets_unfold.
  intros a.
  rewrite <- (Rel_concat_id_r_aux (x a)).
  reflexivity.
Qed.

#[export] Instance Rel_concat_congr
           {R S T: Type}
           {_REL: Rels.RELS R S T}
           {_SETS_R: Sets.SETS R}
           {_SETS_S: Sets.SETS S}
           {_SETS_T: Sets.SETS T}
           {_RELS_Properties: RELS_Properties R S T}
           {_SETS_Properties_R: SETS_Properties R}
           {_SETS_Properties_S: SETS_Properties S}
           {_SETS_Properties_T: SETS_Properties T}:
  Proper
    (Sets.equiv ==> Sets.equiv ==> Sets.equiv)
    (@Rels.concat _ _ _ _REL).
Proof.
  unfold Proper, respectful.
  intros.
  apply Sets_equiv_Sets_included; split.
  + apply Rel_concat_mono.
    - rewrite H; reflexivity.
    - rewrite H0; reflexivity.
  + apply Rel_concat_mono.
    - rewrite H; reflexivity.
    - rewrite H0; reflexivity.
Qed.

Ltac ACC_simplify T :=
  match T with
  | @Rels.nil ?I ?_ACC =>
    let _ACC' := eval hnf in _ACC in
    match _ACC' with
    | Rels.Build_ACCUM_NIL _ _ => idtac
    end;
    let op := eval cbv delta [Rels.nil] in @Rels.nil in
    let T' := eval cbv beta zeta iota in (op I _ACC') in
    change T with T'
  | @Rels.app ?I1 ?I2 ?I ?_ACC =>
    let _ACC' := eval hnf in _ACC in
    match _ACC' with
    | Rels.Build_ACCUM _ _ _ _ => idtac
    end;
    let op := eval cbv delta [Rels.app] in @Rels.app in
    let T' := eval cbv beta zeta iota in (op I1 I2 I _ACC') in
    change T with T'
  end.

Ltac RELS_unfold1 RELS :=
  match RELS with
  | lift_PRE_RELS _ _ _ _ _ _ _ =>
      let p := eval unfold lift_PRE_RELS at 1 in RELS in
      constr:(p)
  | Prop_PRE_RELS _ _ =>
      let p := eval unfold Prop_PRE_RELS in RELS in
      constr:(p)
  | Derived_RELS _ _ _ _ _ =>
      let p := eval unfold Derived_RELS in RELS in
      constr:(p)
  | lift_PRE_RELS_ID _ _ _ =>
      let p := eval unfold lift_PRE_RELS_ID at 1 in RELS in
      constr:(p)
  | Prop_PRE_RELS_ID _ =>
      let p := eval unfold Prop_PRE_RELS_ID in RELS in
      constr:(p)
  | Derived_RELS_ID _ _ =>
      let p := eval unfold Derived_RELS_ID in RELS in
      constr:(p)
  end.

Ltac RELS_simplify T :=
  first
    [ match T with
      | @Rels.concat ?R0 ?S0 ?T0 ?RELS =>
        match RELS with
        | Derived_RELS _ _ _ _ _ => idtac
        end;
        let op1 := eval cbv delta [Rels.concat] in (@Rels.concat) in
        let RELS1 := RELS_unfold1 RELS in
        let T1 := eval cbv beta zeta iota in (op1 R0 S0 T0 RELS1) in
        change T with T1;
        try RELS_simplify T1
      | @Rels.concat_aux ?A ?R0 ?S0 ?T0 ?RELS =>
        match RELS with
        | lift_PRE_RELS _ _ _ _ _ _ _ => idtac
        | Prop_PRE_RELS _ _ => idtac
        end;
        let op1 := eval cbv delta [Rels.concat_aux] in (@Rels.concat_aux) in
        let RELS1 := RELS_unfold1 RELS in
        let T1 := eval cbv beta zeta iota in (op1 A R0 S0 T0 RELS1) in
        change T with T1;
        try RELS_simplify T1
      end
    ].

Ltac unfold_RELS_tac :=
  repeat
  match goal with
  | |- context [@Rels.concat ?R0 ?S0 ?T0 ?RELS] =>
         RELS_simplify (@Rels.concat R0 S0 T0 RELS)
  | |- context [@Rels.concat_aux ?A ?R0 ?S0 ?T0 ?RELS] =>
         RELS_simplify (@Rels.concat_aux A R0 S0 T0 RELS)
  | |- context [@Rels.nil ?I ?ACC] =>
         ACC_simplify (@Rels.nil I ACC)
  | |- context [@Rels.app ?I1 ?I2 ?I ?ACC] =>
         ACC_simplify (@Rels.app I1 I2 I ACC)
  | |- _ => unfold_SETS_tac
  end.

Fixpoint nsteps
           {X: Type}
           {_RELS: Rels.RELS X X X}
           {_RELS_Id: Rels.RELS_ID X}
           (x: X) (n: nat): X :=
  match n with
  | O => Rels.id
  | S n' => Rels.concat x (nsteps x n')
  end.

Definition clos_refl_trans
             {X: Type}
             {_RELS: Rels.RELS X X X}
             {_RELS_Id: Rels.RELS_ID X}
             {_SETS: Sets.SETS X}
             (x: X): X :=
  Sets.omega_union (nsteps x).

Lemma nsteps_n_m:
  forall
    {X: Type}
    {_RELS: Rels.RELS X X X}
    {_RELS_Id: Rels.RELS_ID X}
    {_SETS: Sets.SETS X}
    {_RELS_Properties: RELS_Properties X X X}
    {_RELS_Assoc: RELS_Assoc X X X X X X}
    {_RELS_LeftId: RELS_LeftId X X}
    {_SETS_Properties: SETS_Properties X}
    (x: X) (n m: nat),
    Sets.equiv
      (Rels.concat (nsteps x n) (nsteps x m))
      (nsteps x (n + m)%nat).
Proof.
  intros.
  induction n; simpl.
  + apply Rel_concat_id_l.
  + rewrite Rel_concat_assoc.
    rewrite IHn.
    reflexivity.
Qed.

Lemma rt_trans:
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
      (Rels.concat (clos_refl_trans x) (clos_refl_trans x))
      (clos_refl_trans x).
Proof.
  intros.
  unfold clos_refl_trans.
  unfold Sets.omega_union.
  rewrite Rel_concat_indexed_union_distr_r.
  apply Sets_indexed_union_included; intros n.
  rewrite Rel_concat_indexed_union_distr_l.
  apply Sets_indexed_union_included; intros m.
  rewrite <- (Sets_included_indexed_union _ _ (n + m)).
  rewrite nsteps_n_m.
  reflexivity.
Qed.

Lemma rt_trans_1n:
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
      (Rels.concat x (clos_refl_trans x))
      (clos_refl_trans x).
Proof.
  intros.
  unfold clos_refl_trans.
  unfold Sets.omega_union.
  rewrite Rel_concat_indexed_union_distr_l.
  apply Sets_indexed_union_included; intros m.
  rewrite <- (Sets_included_indexed_union _ _ (1 + m)).
  rewrite <- nsteps_n_m.
  simpl.
  rewrite Rel_concat_assoc.
  rewrite Rel_concat_id_l.
  reflexivity.
Qed.

Lemma rt_trans_n1:
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
      (Rels.concat (clos_refl_trans x) x)
      (clos_refl_trans x).
Proof.
  intros.
  unfold clos_refl_trans.
  unfold Sets.omega_union.
  rewrite Rel_concat_indexed_union_distr_r.
  apply Sets_indexed_union_included; intros n.
  rewrite <- (Sets_included_indexed_union _ _ (n + 1)).
  rewrite <- nsteps_n_m.
  simpl.
  rewrite Rel_concat_id_r.
  reflexivity.
Qed.

Ltac get_head_explicit_rt x :=
  match x with
  | @clos_refl_trans _ _ _ _ _ => constr:(x)
  | ?y ?z => get_head_explicit_rt y
  | _ => let x' := eval cbv delta [x] in x in
         match x' with
         | @clos_refl_trans _ _ _ _ _ => constr:(x')
         end
  end.

Ltac get_head_implicit_rt x :=
  match x with
  | @clos_refl_trans _ _ _ _ _ => constr:(x)
  | ?y ?z => get_head_implicit_rt y
  | _ => let x' := eval cbv delta [x] in x in
         match x' with
         | @clos_refl_trans _ _ _ _ _ => constr:(x)
         end
  end.

Ltac transitivity_General :=
  match goal with
  | |- ?P => let R := get_head_explicit_rt P in
             let R' := get_head_implicit_rt P in
             match R with
             | @clos_refl_trans _ ?_RELS _ _ ?R0 =>
               let H := constr:(rt_trans R0) in
               apply H;
               match goal with
               | |- context[Rels.concat R R] =>
                 change (Rels.concat R R) with (Rels.concat R' R')
               end;
               pattern (@Rels.concat _ _ _ _RELS);
               match goal with
               | |- ?P0 (@Rels.concat _ _ _ _RELS) =>
                 let Pname := fresh "P" in
                 set (Pname := P0);
                 unfold_RELS_tac;
                 unfold Pname; clear Pname
               end
             end
  end.

Ltac transitivity_1n_General :=
  match goal with
  | |- ?P => let R := get_head_explicit_rt P in
             let R' := get_head_implicit_rt P in
             match R with
             | @clos_refl_trans _ ?_RELS _ _ ?R0 =>
               let H := constr:(rt_trans_1n R0) in
               apply H;
               match goal with
               | |- context[Rels.concat ?R1 R] =>
                 change (Rels.concat R1 R) with (Rels.concat R1 R')
               end;
               pattern (@Rels.concat _ _ _ _RELS);
               match goal with
               | |- ?P0 (@Rels.concat _ _ _ _RELS) =>
                 let Pname := fresh "P" in
                 set (Pname := P0);
                 unfold_RELS_tac;
                 unfold Pname; clear Pname
               end
             end
  end.

Ltac transitivity_n1_General :=
  match goal with
  | |- ?P => let R := get_head_explicit_rt P in
             let R' := get_head_implicit_rt P in
             match R with
             | @clos_refl_trans _ ?_RELS _ _ ?R0 =>
               let H := constr:(rt_trans_n1 R0) in
               apply H;
               match goal with
               | |- context[Rels.concat R ?R1] =>
                 change (Rels.concat R R1) with (Rels.concat R' R1)
               end;
               pattern (@Rels.concat _ _ _ _RELS);
               match goal with
               | |- ?P0 (@Rels.concat _ _ _ _RELS) =>
                 let Pname := fresh "P" in
                 set (Pname := P0);
                 unfold_RELS_tac;
                 unfold Pname; clear Pname
               end
             end
  end.

Tactic Notation "transitivity_nn" uconstr(x) :=
  transitivity_General;
  exists x;
  match goal with
  | |-  _ /\ _ => split
  end.

Tactic Notation "transitivity_nn" uconstr(x) uconstr(y1) uconstr(y2) :=
  transitivity_General;
  exists x, y1, y2;
  match goal with
  | |-  _ /\ _ /\ _ => split; [| split]
  end.

Tactic Notation "etransitivity_nn" :=
  first
    [ transitivity_General;
      eexists;
      match goal with
      | |-  _ /\ _ => split
      end
    | transitivity_General;
      do 3 eexists;
      match goal with
      | |-  _ /\ _ /\ _ => split; [| split]
      end ].

Tactic Notation "transitivity_1n" uconstr(x) :=
  transitivity_1n_General;
  exists x;
  match goal with
  | |-  _ /\ _ => split
  end.

Tactic Notation "transitivity_1n" uconstr(x) uconstr(y1) uconstr(y2) :=
  transitivity_1n_General;
  exists x, y1, y2;
  match goal with
  | |-  _ /\ _ /\ _ => split; [| split]
  end.

Tactic Notation "etransitivity_1n" :=
  first
    [ transitivity_1n_General;
      eexists;
      match goal with
      | |-  _ /\ _ => split
      end
    | transitivity_1n_General;
      do 3 eexists;
      match goal with
      | |-  _ /\ _ /\ _ => split; [| split]
      end ].

Tactic Notation "transitivity_n1" uconstr(x) :=
  transitivity_n1_General;
  exists x;
  match goal with
  | |-  _ /\ _ => split
  end.

Tactic Notation "transitivity_n1" uconstr(x) uconstr(y1) uconstr(y2) :=
  transitivity_n1_General;
  exists x, y1, y2;
  match goal with
  | |-  _ /\ _ /\ _ => split; [| split]
  end.

Tactic Notation "etransitivity_n1" :=
  first
    [ transitivity_n1_General;
      eexists;
      match goal with
      | |-  _ /\ _ => split
      end
    | transitivity_n1_General;
      do 3 eexists;
      match goal with
      | |-  _ /\ _ /\ _ => split; [| split]
      end ].

Ltac revert_dependent_except x H :=
  repeat
    match goal with
    | H0: context [x] |- _ => revert H0; assert_succeeds (revert H)
    end.

Ltac revert_dependent_component x H :=
  first
  [
    is_var x;
    revert_dependent_except x H
  |
    match x with
    | ?y ?z => match type of y with
               | _ -> _ => revert_dependent_component y H;
                           revert_dependent_component z H
               | _ => idtac
               end
    | _ => idtac
    end
  ].

Ltac revert_component x :=
  first
  [
    is_var x;
    revert x
  |
    match x with
    | ?y ?z => match type of y with
               | _ -> _ => revert_component y; revert_component z
               | _ => idtac
               end
    | _ => idtac
    end
  ].

Import List.

#[export] Instance list_ACC A: Rels.ACCUM (list A) (list A) (list A) :=
  {|
    Rels.app := @app _;
  |}.

#[export] Instance list_ACC_Nil A: Rels.ACCUM_NIL (list A) :=
  {|
    Rels.nil := @nil _;
  |}.

#[export] Instance list_ACC_LeftId A: ACCUM_LeftId (list A) (list A).
Proof.
  constructor.
  intros.
  apply app_nil_l.
Qed.

#[export] Instance list_ACC_RightId A: ACCUM_RightId (list A) (list A).
Proof.
  constructor.
  intros.
  apply app_nil_r.
Qed.

#[export] Instance list_ACC_Assoc A: ACCUM_Assoc (list A) (list A) (list A) (list A) (list A) (list A).
Proof.
  constructor.
  intros.
  symmetry.
  apply app_assoc.
Qed.

Module test.

Goal forall X: nat -> list nat -> nat -> Prop,
  Sets.equiv (Rels.concat X X) X.
Abort.

Parameter X :nat * nat -> list nat -> nat * nat -> Prop.

Definition msteps := clos_refl_trans X.

Goal forall a1 a2 l b1 b2,
  X (a1, a2) l (b1, b2) ->
  msteps (a1, a2) l (b1, b2).
Proof.
  intros.
  transitivity_n1 (a1, a2) nil l.
Abort.

Goal forall a1 a2 l b1 b2,
  X (a1, a2) l (b1, b2) ->
  msteps (a1, a2) l (b1, b2).
Proof.
  intros.
  transitivity_1n (a1, a2) nil l.
Abort.

Goal forall a1 a2 l b1 b2,
  X (a1, a2) l (b1, b2) ->
  msteps (a1, a2) l (b1, b2).
Proof.
  intros.
  transitivity_nn (a1, a2) nil l.
Abort.

Goal forall a1 a2 l b1 b2,
  msteps (a1, a2) l (b1, b2) ->
  msteps (a1, a2) l (b1, b2).
Proof.
  intros.
  tauto.
Qed.


End test.

Notation "X ∘ Y" := (Rels.concat X Y)
  (right associativity, at level 60): sets_scope.

Ltac rel_unfold := unfold_RELS_tac.
