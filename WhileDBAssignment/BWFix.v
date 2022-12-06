Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import WhileDB.SetsDomain.

(** 本文件为库文件，其中的admit不需要填充 *)

Class Order (A: Type): Type :=
  order_rel: A -> A -> Prop.

Declare Scope order_scope.
Notation "a <= b" := (order_rel a b): order_scope.
Local Open Scope order_scope.

Definition is_lb
             {A: Type} {RA: Order A}
             (X: A -> Prop) (a: A): Prop :=
  forall a', X a' -> a <= a'.

Definition is_ub
             {A: Type} {RA: Order A}
             (X: A -> Prop) (a: A): Prop :=
  forall a', X a' -> a' <= a.

Definition is_omega_lb
             {A: Type} {RA: Order A}
             (l: nat -> A) (a: A): Prop :=
  forall n, a <= l n.

Definition is_omega_ub
             {A: Type} {RA: Order A}
             (l: nat -> A) (a: A): Prop :=
  forall n, l n <= a.

Definition is_omega_lub
             {A: Type} {RA: Order A}
             (l: nat -> A) (a: A): Prop :=
  is_omega_ub l a /\ is_lb (is_omega_ub l) a.

Lemma is_omega_lub_sound:
  forall {A: Type} {RA: Order A} {l: nat -> A} {a: A},
    is_omega_lub l a -> is_omega_ub l a.
Proof. unfold is_omega_lub; intros; tauto. Qed.

Lemma is_omega_lub_tight:
  forall {A: Type} {RA: Order A} {l: nat -> A} {a: A},
    is_omega_lub l a -> is_lb (is_omega_ub l) a.
Proof. unfold is_omega_lub; intros; tauto. Qed.

Class Equiv (A: Type): Type :=
  equiv: A -> A -> Prop.

Notation "a == b" := (equiv a b): order_scope.

Class Reflexive_Setoid
        (A: Type) {RA: Order A} {EA: Equiv A}: Prop :=
  reflexivity_setoid:
    forall a b, a == b -> a <= b.

Class AntiSymmetric_Setoid
        (A: Type) {RA: Order A} {EA: Equiv A}: Prop :=
  antisymmetricity_setoid:
    forall a b, a <= b -> b <= a -> a == b.

Class PartialOrder_Setoid
        (A: Type) {RA: Order A} {EA: Equiv A}: Prop :=
{
  PO_Reflexive_Setoid:> Reflexive_Setoid A;
  PO_Transitive:> Transitive order_rel;
  PO_AntiSymmetric_Setoid:> AntiSymmetric_Setoid A
}.

Instance PartialOrder_Setoid_Proper
           {A: Type} `{POA: PartialOrder_Setoid A} {EquivA: Equivalence equiv}:
  Proper (equiv ==> equiv ==> iff) order_rel.
Proof.
  unfold Proper, respectful.
  intros.
  split; intros.
  + transitivity x0; [| apply reflexivity_setoid; tauto].
    transitivity x; [apply reflexivity_setoid; symmetry; tauto |].
    tauto.
  + transitivity y0; [| apply reflexivity_setoid; symmetry; tauto].
    transitivity y; [apply reflexivity_setoid; tauto |].
    tauto.
Qed.

Lemma same_omega_ub_same_omega_lub:
  forall
    {A: Type}
    `{POA: PartialOrder_Setoid A}
    (l1 l2: nat -> A)
    (a1 a2: A),
  (is_omega_ub l1 == is_omega_ub l2)%sets ->
  is_omega_lub l1 a1 ->
  is_omega_lub l2 a2 ->
  a1 == a2.
Proof.
  intros A ? ? POA.
  sets_unfold.
  intros.
  apply antisymmetricity_setoid.
  + apply (is_omega_lub_tight H0).
    apply H.
    apply (is_omega_lub_sound H1).
  + apply (is_omega_lub_tight H1).
    apply H.
    apply (is_omega_lub_sound H0).
Qed.

Class OmegaLub (A: Type): Type :=
  omega_lub: (nat -> A) -> A.

Class Bot (A: Type): Type :=
  bot: A.

Definition increasing
             {A: Type} {RA: Order A} (l: nat -> A): Prop :=
  forall n, l n <= l (S n).

Definition is_least {A: Type} {RA: Order A} (a: A): Prop :=
  forall a', a <= a'.

Class OmegaCompletePartialOrder_Setoid
        (A: Type)
        {RA: Order A} {EA: Equiv A}
        {oLubA: OmegaLub A} {BotA: Bot A}: Prop :=
{
  oCPO_PartialOrder:> PartialOrder_Setoid A;
  oCPO_completeness: forall T,
    increasing T -> is_omega_lub T (omega_lub T);
  bot_is_least: is_least bot
}.

Lemma same_omega_ub_same_omega_lub':
  forall
    {A: Type}
    `{oCPOA: OmegaCompletePartialOrder_Setoid A}
    (l1 l2: nat -> A),
  (is_omega_ub l1 == is_omega_ub l2)%sets ->
  increasing l1 ->
  increasing l2 ->
  omega_lub l1 == omega_lub l2.
Proof.
  intros.
  apply (same_omega_ub_same_omega_lub _ _ _ _ H).
  + apply oCPO_completeness.
    apply H0.
  + apply oCPO_completeness.
    apply H1.
Qed.

Definition mono
             {A B: Type}
             `{POA: PartialOrder_Setoid A}
             `{POB: PartialOrder_Setoid B}
             (f: A -> B): Prop :=
  forall a1 a2, a1 <= a2 -> f a1 <= f a2.

Definition continuous
             {A B: Type}
             `{oCPOA: OmegaCompletePartialOrder_Setoid A}
             `{oCPOB: OmegaCompletePartialOrder_Setoid B}
             (f: A -> B): Prop :=
  forall l: nat -> A,
    increasing l ->
    f (omega_lub l) == omega_lub (fun n => f (l n)).

Lemma id_mono:
  forall {A: Type}
         `{POA: PartialOrder_Setoid A},
  mono (fun x => x).
Proof.
Admitted.

Lemma compose_mono:
  forall {A B C: Type}
         `{POA: PartialOrder_Setoid A}
         `{POB: PartialOrder_Setoid B}
         `{POC: PartialOrder_Setoid C}
         (f: A -> B)
         (g: B -> C),
  mono f -> mono g -> mono (fun x => g (f x)).
Proof.
Admitted.

Lemma id_continuous:
  forall {A: Type}
         `{oCPOA: OmegaCompletePartialOrder_Setoid A}
         {EquivA: Equivalence equiv},
  continuous (fun x => x).
Proof.
Admitted.

Lemma increasing_mono_increasing:
  forall {A B: Type}
         `{POA: PartialOrder_Setoid A}
         `{POB: PartialOrder_Setoid B}
         (f: A -> B)
         (l: nat -> A),
  increasing l -> mono f -> increasing (fun n => f (l n)).
Proof.
Admitted.

Lemma mono_equiv_congr:
  forall {A B: Type}
         `{POA: PartialOrder_Setoid A}
         `{POB: PartialOrder_Setoid B}
          {EquivA: Equivalence (equiv: A -> A -> Prop)}
         (f: A -> B),
  mono f -> Proper (equiv ==> equiv) f.
Proof.
Admitted.

Lemma compose_continuous:
  forall {A B C: Type}
         `{oCPOA: OmegaCompletePartialOrder_Setoid A}
         `{oCPOB: OmegaCompletePartialOrder_Setoid B}
         `{oCPOC: OmegaCompletePartialOrder_Setoid C}
          {EquivB: Equivalence (equiv: B -> B -> Prop)}
          {EquivC: Equivalence (equiv: C -> C -> Prop)}
         (f: A -> B)
         (g: B -> C),
  mono f ->
  mono g ->
  continuous f ->
  continuous g ->
  continuous (fun x => g (f x)).
Proof.
Admitted.

Lemma iter_bot_increasing:
  forall
    {A: Type}
    `{oCPOA: OmegaCompletePartialOrder_Setoid A}
    (f: A -> A),
    mono f ->
    increasing (fun n => Nat.iter n f bot).
Proof.
  unfold increasing.
  intros.
  induction n; simpl.
  + apply bot_is_least.
  + apply H.
    apply IHn.
Qed.

Lemma iter_S_bot_increasing:
  forall
    {A: Type}
    `{oCPOA: OmegaCompletePartialOrder_Setoid A}
    (f: A -> A),
    mono f ->
    increasing (fun n => f (Nat.iter n f bot)).
Proof.
  unfold increasing.
  intros.
  apply H.
  apply iter_bot_increasing.
  apply H.
Qed.

Definition BW_LFix
             {A: Type}
             `{CPOA: OmegaCompletePartialOrder_Setoid A}
             (f: A -> A): A :=
  omega_lub (fun n => Nat.iter n f bot).

Lemma BW_LFix_is_fix:
  forall
    {A: Type}
    `{CPOA: OmegaCompletePartialOrder_Setoid A}
    {EquivA: Equivalence equiv}
    (f: A -> A),
    mono f ->
    continuous f ->
    f (BW_LFix f) == BW_LFix f.
Proof.
  unfold BW_LFix; intros.
  rewrite H0 by (apply iter_bot_increasing; tauto).
  apply same_omega_ub_same_omega_lub'.
  + intros; unfold is_omega_ub.
    split; intros.
    - destruct n.
      * apply bot_is_least.
      * apply H1.
    - specialize (H1 (S n)).
      apply H1.
  + apply iter_S_bot_increasing.
    apply H.
  + apply iter_bot_increasing.
    apply H.
Qed.

Lemma BW_LFix_is_least_fix:
  forall
    {A: Type}
    `{CPOA: OmegaCompletePartialOrder_Setoid A}
    {EquivA: Equivalence equiv}
    (f: A -> A)
    (a: A),
    mono f ->
    continuous f ->
    f a == a ->
    BW_LFix f <= a.
Proof.
  unfold BW_LFix; intros.
  pose proof iter_bot_increasing f H.
  pose proof oCPO_completeness (fun n => Nat.iter n f bot) H2.
  apply (is_omega_lub_tight H3).
  unfold is_omega_ub.
  induction n; simpl.
  + apply bot_is_least.
  + rewrite <- H1.
    apply H.
    apply IHn.
Qed.

Local Close Scope order_scope.
