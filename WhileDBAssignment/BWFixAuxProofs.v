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

