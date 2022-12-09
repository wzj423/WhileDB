Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import compcert.lib.Integers.
Require Import WhileDB.SetsDomain.
Require Import WhileDB.RelDomain.
Require Import WhileDB.RelDomainAuxProofs.
Require Import WhileDB.DenotationalSemantics.
Require Import WhileDB.Lang.
Require Import Lia.
Local Open Scope Z.
Local Open Scope sets_scope.

Inductive expr_ectx: Type :=
| KBinopL (op: binop) (e: expr)
| KBinopR (i: int64) (op: binop)
| KUnop (op: unop)
| KDeref
| KMalloc.

Inductive expr_loc: Type :=
| EL_Value (i: int64)
| EL_FocusedExpr (e: expr)
| EL_Cont (el: expr_loc) (k: expr_ectx).

Inductive expr_com_ectx: Type :=
| KWhileCond (e: expr) (c: com)
| KIf (c1 c2: com)
| KAsgnVar (x: var_name)
| KAsgnMemL (e: expr)
| KAsgnMemR (i: int64)
| KWriteInt
| KWriteChar.

Inductive com_ectx: Type :=
| KSeq (c: com)
| KWhileBody (e: expr) (c: com).

Inductive com_loc: Type :=
| CL_Finished
| CL_FocusedCom (c: com)
| CL_ECont (el: expr_loc) (k: expr_com_ectx)
| CL_CCont (cl: com_loc) (k: com_ectx).

Definition short_circuit (op: binop) (i i': int64): Prop :=
  match op with
  | OAnd => i = Int64.repr 0 /\ i' = Int64.repr 0
  | OOr => Int64.signed i <> 0 /\ i' = Int64.repr 1
  | _ => False
  end.

Definition no_short_circuit (op: binop) (i: int64): Prop :=
  match op with
  | OAnd => Int64.signed i <> 0
  | OOr => i = Int64.repr 0
  | _ => True
  end.

Definition bool_compute (n1 n2 n: int64): Prop :=
  n2 = Int64.repr 0 /\ n = Int64.repr 0 \/
  Int64.signed n2 <> 0 /\ n = Int64.repr 1.

Definition binop_compute (op: binop):
  int64 -> int64 -> int64 -> Prop :=
  match op with
  | OOr => bool_compute
  | OAnd => bool_compute
  | OLt => cmp_compute Clt
  | OLe => cmp_compute Cle
  | OGt => cmp_compute Cgt
  | OGe => cmp_compute Cge
  | OEq => cmp_compute Ceq
  | ONe => cmp_compute Cne
  | OPlus => arith_compute1 Z.add Int64.add
  | OMinus => arith_compute1 Z.sub Int64.sub
  | OMul => arith_compute1 Z.mul Int64.mul
  | ODiv => arith_compute2 Int64.divs
  | OMod => arith_compute2 Int64.mods
  end.

Definition neg_compute (n0 n: int64): Prop :=
  n = Int64.neg n0 /\
  Int64.signed n0 <> Int64.min_signed.

Definition not_compute (n0 n: int64): Prop :=
  Int64.signed n0 <> 0 /\ n = Int64.repr 0 \/
  n0 = Int64.repr 0 /\ n = Int64.repr 1.

Definition unop_compute (op: unop):
  int64 -> int64 -> Prop :=
  match op with
  | ONeg => neg_compute
  | ONot => not_compute
  end.

Inductive estep:
  expr_loc * prog_state -> list event -> expr_loc * prog_state -> Prop :=
| ES_Var: forall (x: var_name) s,
    estep
      (EL_FocusedExpr (EVar x), s)
      nil
      (EL_Value (s.(vars) x), s)
| ES_Const: forall (n: Z) s,
    n <= Int64.max_signed ->
    n >= Int64.min_signed ->
    estep
      (EL_FocusedExpr (ENum n), s)
      nil
      (EL_Value (Int64.repr n), s)
| ES_BinopL: forall op e1 e2 s,
    estep
      (EL_FocusedExpr (EBinop op e1 e2), s)
      nil
      (EL_Cont (EL_FocusedExpr e1) (KBinopL op e2), s)
| ES_BinopR_SC: forall op n1 n1' e2 s,
    short_circuit op n1 n1' ->
    estep
      (EL_Cont (EL_Value n1) (KBinopL op e2), s)
      nil
      (EL_Value n1', s)
| ES_BinopR_NSC: forall op n1 e2 s,
    no_short_circuit op n1 ->
    estep
      (EL_Cont (EL_Value n1) (KBinopL op e2), s)
      nil
      (EL_Cont (EL_FocusedExpr e2) (KBinopR n1 op), s)
| ES_BinopStep: forall op n1 n2 n s,
    binop_compute op n1 n2 n ->
    estep
      (EL_Cont (EL_Value n2) (KBinopR n1 op), s)
      nil
      (EL_Value n, s)
| ES_Unop: forall op e s,
    estep
      (EL_FocusedExpr (EUnop op e), s)
      nil
      (EL_Cont (EL_FocusedExpr e) (KUnop op), s)
| ES_UnopStep: forall op n0 n s,
    unop_compute op n0 n ->
    estep
      (EL_Cont (EL_Value n0) (KUnop op), s)
      nil
      (EL_Value n, s)
| ES_Deref: forall e s,
    estep
      (EL_FocusedExpr (EDeref e), s)
      nil
      (EL_Cont (EL_FocusedExpr e) KDeref, s)
| ES_DerefStep: forall n0 n s,
    s.(mem) n0 = Some n ->
    estep
      (EL_Cont (EL_Value n0) KDeref, s)
      nil
      (EL_Value n, s)
| ES_Malloc: forall e s,
    estep
      (EL_FocusedExpr (EMalloc e), s)
      nil
      (EL_Cont (EL_FocusedExpr e) KMalloc, s)
| ES_MallocStep: forall n0 n s1 tr s2,
    malloc_action n0 n s1 tr s2 ->
    estep
      (EL_Cont (EL_Value n0) KMalloc, s1)
      tr
      (EL_Value n, s2)
| ES_ReadIntStep: forall n s,
    estep
      (EL_FocusedExpr EReadInt, s)
      (EV_ReadInt n :: nil)
      (EL_Value n, s)
| ES_ReadCharStep: forall n s,
    estep
      (EL_FocusedExpr EReadChar, s)
      (EV_ReadChar n :: nil)
      (EL_Value n, s)
| ES_Cont: forall el1 s1 tr el2 s2 k,
    estep (el1, s1) tr (el2, s2) ->
    estep (EL_Cont el1 k, s1) tr (EL_Cont el2 k, s2).


Check (EV_ReadInt (Int64.repr 3) :: nil).

  (** 尝试1207**)
(*Inductive cstep:
  com_loc * prog_state -> list event -> com_loc * prog_state -> Prop :=
. Goal False. admit. Abort. (* 请删去这一行并自行补充定义，必要时可以添加辅助定义 *)*)


Inductive cstep:
  com_loc * prog_state -> list event-> com_loc * prog_state -> Prop :=
| CS_AsgnVar: forall s x e,
    cstep
      (CL_FocusedCom (CAss (EVar x) e), s)
      nil
      (CL_ECont (EL_FocusedExpr e) (KAsgnVar x), s)
| CS_AsgnVarStep: forall s1 s2 x n,
    s2.(vars) x = n ->
    (forall y, x <> y -> s1.(vars) y = s2.(vars) y) ->
    (forall p, s1.(mem) p = s2.(mem) p) ->
    cstep
      (CL_ECont (EL_Value n) (KAsgnVar x), s1)
      nil
      (CL_Finished, s2)

| CS_AsgnMemL: forall s e1 e2,
    cstep
      (CL_FocusedCom (CAss (EDeref e1) e2), s)
      nil
      (CL_ECont (EL_FocusedExpr e1) (KAsgnMemL e2), s)
| CS_AsgnMemR: forall s n1 e2,
    cstep
      (CL_ECont (EL_Value n1) (KAsgnMemL e2), s)
      nil
      (CL_ECont (EL_FocusedExpr e2) (KAsgnMemR n1), s)
| CS_AsgnMemStep: forall s1 s2 n1 n2,
    s1.(mem) n1 <> None ->
    s2.(mem) n1 = Some n2 ->
    (forall x, s1.(vars) x = s2.(vars) x) ->
    (forall p, n1 <> p -> s1.(mem) p = s2.(mem) p) ->
    cstep
      (CL_ECont (EL_Value n2) (KAsgnMemR n1), s1)
      nil
      (CL_Finished, s2)

| CS_Seq: forall s c1 c2,
    cstep
      (CL_FocusedCom (CSeq c1 c2), s)
      nil
      (CL_CCont (CL_FocusedCom c1) (KSeq c2), s)
| CS_SeqStep: forall s c,
    cstep
      (CL_CCont CL_Finished (KSeq c), s)
      nil
      (CL_FocusedCom c, s)

| CS_If: forall s e c1 c2,
    cstep
      (CL_FocusedCom (CIf e c1 c2), s)
      nil
      (CL_ECont (EL_FocusedExpr e) (KIf c1 c2), s)
| CS_IfStepTrue: forall s n c1 c2,
    Int64.signed n <> 0 ->
    cstep
      (CL_ECont (EL_Value n) (KIf c1 c2), s)
      nil
      (CL_FocusedCom c1, s)
| CS_IfStepFalse: forall s n c1 c2,
    n = Int64.repr 0 ->
    cstep
      (CL_ECont (EL_Value n) (KIf c1 c2), s)
      nil
      (CL_FocusedCom c2, s)

| CS_WhileBegin: forall s e c,
    cstep
      (CL_FocusedCom (CWhile e c), s)
      nil
      (CL_ECont (EL_FocusedExpr e) (KWhileCond e c), s)
| CS_WhileStepTrue: forall s n e c,
    Int64.signed n <> 0 ->
    cstep
      (CL_ECont (EL_Value n) (KWhileCond e c), s)
      nil
      (CL_CCont (CL_FocusedCom c) (KWhileBody e c), s)
| CS_WhileStepFalse: forall s n e c,
    n = Int64.repr 0 ->
    cstep
      (CL_ECont (EL_Value n) (KWhileCond e c), s)
      nil
      (CL_Finished, s)
| CS_WhileRestart: forall s e c,
    cstep
      (CL_CCont CL_Finished (KWhileBody e c), s)
      nil
      (CL_ECont (EL_FocusedExpr e) (KWhileCond e c), s)

  (*上面的都没有太大问题，关键在于下面*)
| CS_WriteInt: forall s e,
    cstep
      (CL_FocusedCom (CWriteInt e), s)
      nil
      (CL_ECont (EL_FocusedExpr e) (KWriteInt), s)
| CS_WriteIntStep: forall s n,
   cstep
   (CL_ECont (EL_Value n) (KWriteInt), s)
      (EV_WriteInt n :: nil)
    (CL_Finished, s)
    
| CS_WriteChar: forall s e,
    cstep
      (CL_FocusedCom (CWriteChar e), s)
      nil
      (CL_ECont (EL_FocusedExpr e) (KWriteChar), s)
| CS_WriteCharStep: forall s n,
	cstep
    (CL_ECont (EL_Value n) (KWriteChar), s)
      ((EV_WriteChar n) :: nil)
    (CL_Finished, s)

| CS_ECont: forall el1 el2 s1 s2 k tr,
    estep (el1,s1) tr (el2,s2) ->
    cstep (CL_ECont el1 k, s1) tr (CL_ECont el2 k, s2)
| CS_CCont: forall cl1 s1 cl2 s2 k tr,
    cstep (cl1, s1) tr (cl2, s2) ->
    cstep (CL_CCont cl1 k, s1) tr (CL_CCont cl2 k, s2).
    (*上下两边都是从el1->el2 或者cl1->cl2， 那么两边经历的时间应当是一样的   *)


(** Coq中定义多步关系 *)
Definition multi_estep :
  (expr_loc * prog_state) -> list event -> (expr_loc * prog_state) -> Prop :=
  clos_refl_trans estep.
Definition multi_cstep:
  com_loc * prog_state -> list event -> com_loc * prog_state -> Prop :=
  clos_refl_trans cstep.

(** 多步关系的基本性质 *)
Lemma MES_Cont: forall s1 s2 el1 el2 tr k,
  multi_estep (el1,s1) tr (el2,s2) ->
  multi_estep ((EL_Cont el1 k),s1) tr ((EL_Cont el2 k),s2).
Proof.
  intros.
  pose proof nsteps_1_self estep.
  assert(forall s1 s2 el1 el2 tr k, nsteps estep (S O) (el1,s1) tr (el2,s2) ->
  nsteps estep (S O) ((EL_Cont el1 k),s1) tr ((EL_Cont el2 k),s2) ).
  {
    intros. apply H0. apply H0 in H1. apply ES_Cont. auto.
  }
  assert (forall n tr el1 s1 el2 s2 k, nsteps estep n (el1, s1) tr (el2, s2) -> nsteps estep n (EL_Cont el1 k, s1) tr (EL_Cont el2 k, s2) ).
  {
    induction n.
    {
      unfold nsteps. simpl. sets_unfold;rel_unfold;sets_unfold;rel_unfold.
      intros;destruct H2.
      split;auto.
      inversion H3.
      injection H3.
      intros. congruence.
    }
    intros.
    assert( ((S n)%nat > O)%nat). lia.
    epose proof nsteps_1n estep (S n) (el0,s0) (el3,s3) tr0 H3 H2.
    destruct H4 as[? [? [? [? [? ?]]]]].
    assert ( ((S n)-1 = n)%nat). lia.
    rewrite H7 in H6. clear H7.
    destruct x1 as (el4,x4).
    specialize ( IHn x0 el4 x4 el3 s3 k0 H6).
    specialize (H1 s0 x4 el0 el4 x k).
   pose proof nsteps_1_self estep.
  (*    assert( nsteps estep 1 (el0, s0) x (el4, x4)  ). { apply H7. apply H5. }
 	apply H1 in H8. *)
 	eapply nsteps_1n_rev.
 	+ auto.
 	+ exists x,x0,(EL_Cont el4 k0,x4). repeat split;auto. eapply ES_Cont;eauto.
 	assert ( ((S n - 1)=n)%nat). lia. rewrite H8. auto.
 	}
 	revert H.
	unfold multi_estep. unfold clos_refl_trans.
	sets_unfold. intros. destruct H. exists x. eapply H2 in H;eauto.
Qed.



Lemma MCS_ECont: forall s1 s2 tr el1 el2 k,
  multi_estep (el1,s1) tr (el2,s2) ->
  multi_cstep (CL_ECont el1 k, s1) tr (CL_ECont el2 k, s2).
Proof.
  intros.
  pose proof nsteps_1_self cstep.
  pose proof nsteps_1_self estep as HH0.
  assert(forall s1 s2 el1 el2 tr k, nsteps estep (S O) (el1,s1) tr (el2,s2) ->
  nsteps cstep (S O) ((CL_ECont el1 k),s1) tr ((CL_ECont el2 k),s2) ).
  {
    intros. apply H0. apply HH0 in H1. apply CS_ECont. auto.
  }
  assert (forall n tr el1 s1 el2 s2 k, nsteps estep n (el1, s1) tr (el2, s2) -> nsteps cstep n (CL_ECont el1 k, s1) tr (CL_ECont el2 k, s2) ).
  {
    induction n.
    {
      unfold nsteps. simpl. sets_unfold;rel_unfold;sets_unfold;rel_unfold.
      intros;destruct H2.
      split;auto.
      inversion H3.
      injection H3.
      intros. congruence.
    }
    intros.
    assert( ((S n)%nat > O)%nat). lia.
    epose proof nsteps_1n estep (S n) (el0,s0) (el3,s3) tr0 H3 H2.
    destruct H4 as[? [? [? [? [? ?]]]]].
    assert ( ((S n)-1 = n)%nat). lia.
    rewrite H7 in H6. clear H7.
    destruct x1 as (el4,x4).
    specialize ( IHn x0 el4 x4 el3 s3 k0 H6).
    specialize (H1 s0 x4 el0 el4 x k).
   pose proof nsteps_1_self estep.
(*    assert( nsteps estep 1 (el0, s0) x (el4, x4)  ). { apply H7. apply H5. }
 	apply H1 in H8. *)
 	eapply nsteps_1n_rev.
 	+ auto.
 	+ exists x,x0,(CL_ECont el4 k0,x4). repeat split;auto. eapply CS_ECont;eauto.
 	assert ( ((S n - 1)=n)%nat). lia. rewrite H8. auto.
 	}
 	revert H.
	unfold multi_estep. unfold clos_refl_trans.
	sets_unfold. intros. destruct H. exists x. eapply H2 in H;eauto.
Qed.

Lemma MCS_CCont: forall cl1 s1 cl2 s2 k tr,
  multi_cstep (cl1, s1) tr (cl2, s2) ->
  multi_cstep (CL_CCont cl1 k, s1) tr (CL_CCont cl2 k, s2).
Proof.
  intros.
  pose proof nsteps_1_self cstep.
  pose proof nsteps_1_self estep as HH0.
  assert(forall s1 s2 el1 el2 tr k, nsteps cstep (S O) (el1,s1) tr (el2,s2) ->
  nsteps cstep (S O) ((CL_CCont el1 k),s1) tr ((CL_CCont el2 k),s2) ).
  {
    intros. apply H0. apply H0 in H1. apply  CS_CCont. auto.
  }
  assert (forall n tr el1 s1 el2 s2 k, nsteps cstep n (el1, s1) tr (el2, s2) -> nsteps cstep n (CL_CCont el1 k, s1) tr (CL_CCont el2 k, s2) ).
  {
    induction n.
    {
      unfold nsteps. simpl. sets_unfold;rel_unfold;sets_unfold;rel_unfold.
      intros;destruct H2.
      split;auto.
      inversion H3.
      injection H3.
      intros. congruence.
    }
    intros.    
    assert( ((S n)%nat > O)%nat). lia.
    epose proof nsteps_1n cstep (S n) (el1,s0) (el2,s3) tr0 H3 H2.
    destruct H4 as[? [? [? [? [? ?]]]]].
    assert ( ((S n)-1 = n)%nat). lia.
    rewrite H7 in H6. clear H7.
    destruct x1 as (el4,x4).
    specialize ( IHn x0 el4 x4 el2 s3 k0 H6).
    specialize (H1 s0 x4 el1 el4 x k).
   pose proof nsteps_1_self estep.
(*    assert( nsteps estep 1 (el0, s0) x (el4, x4)  ). { apply H7. apply H5. }
 	apply H1 in H8. *)
 	eapply nsteps_1n_rev.
 	+ auto.
 	+ exists x,x0,(CL_CCont el4 k0,x4). repeat split;auto. eapply CS_CCont;eauto.
 	assert ( ((S n - 1)=n)%nat). lia. rewrite H8. auto.
 	}
 	revert H.
	unfold multi_estep. unfold clos_refl_trans.
	sets_unfold. intros. destruct H. exists x. eapply H2 in H;eauto.
Qed.


Lemma eeval_multi_estep: forall e n s1 s2 tr,
  eeval e n s1 tr s2 ->
  multi_estep (EL_FocusedExpr e,s1) tr (EL_Value n,s2).

Proof.
  intros.
  revert n H. revert tr s2 s1.  induction e; simpl; intros.
  + unfold const_denote in H.
  	transitivity_1n_General.
    exists ((EL_Value (Int64.repr n), s1)),nil,nil.
    destruct H as [? [? [? [? ?]]]].
    repeat split;auto.
    constructor;auto.
    subst n0.
    subst s2.
    apply rt_refl_concrete.
  + unfold var_denote in H.
  	destruct H as [? [? ?]].
    subst n tr  s1.
  	transitivity_1n_General.
  	exists (EL_Value (vars s2 x), s2),nil,nil.
  	repeat split;simpl.
  	constructor.
    apply rt_refl_concrete.
  + destruct op; simpl in H.
    - 
     etransitivity_1n; [eapply app_nil_l |constructor |]. (*用app_nil_l解决多出来的分支问题*)
      unfold or_denote in H.
      destruct H as [? | [? | ?] ].
      {
       destruct H as [n1 [? [? ?] ] ].
        specialize (IHe1 _ _ _ _ H).
        (*etransitivity_nn. { assert(tr++nil=tr). apply app_nil_r. apply H2. } apply MES_Cont,IHe1. [apply app_nil_r| |].*)
        etransitivity_nn; [apply app_nil_r| apply MES_Cont,IHe1 |].
        (*etransitivity; [apply MES_Cont, IHe1 |].*)
        etransitivity_1n;[apply app_nil_r| constructor;unfold short_circuit;split;eauto| ].
        apply rt_refl_concrete.
       }
      {
       destruct H as [n2 [? [? ? ] ] ].
      epose proof Rel_Concat_element_concat_rev2 as HOR1.
      specialize (HOR1 (eeval e1 (Int64.repr 0))  (eeval e2 n2 )  (eeval e1 (Int64.repr 0) ∘ eeval e2 n2)  s1 s2 tr).
      assert(eeval e1 (Int64.repr 0) ∘ eeval e2 n2 == eeval e1 (Int64.repr 0) ∘ eeval e2 n2) as HOR1_hlp. reflexivity.
      specialize (HOR1 HOR1_hlp H). clear HOR1_hlp. destruct HOR1 as [tr1 [tr2 [s1_2 [? [? ?]]]]].

        specialize (IHe1 _ _ _ _ H3).
        specialize (IHe2 _ _ _ _ H4).
        symmetry in H2.
        etransitivity_nn; [apply H2 | apply MES_Cont, IHe1 |].
        etransitivity_1n; [apply app_nil_l | apply ES_BinopR_NSC; simpl; tauto |].
        etransitivity_nn; [apply app_nil_r | apply MES_Cont, IHe2 |].
        etransitivity_1n. apply app_nil_l. constructor. unfold binop_compute. unfold bool_compute. right. split;eauto. apply rt_refl_concrete.
        }
      {
       destruct H as [? ? ].
       
       epose proof Rel_Concat_element_concat_rev2 as HOR1.
      specialize (HOR1 (eeval e1 (Int64.repr 0))  (eeval e2  (Int64.repr 0) )  (eeval e1 (Int64.repr 0) ∘ eeval e2  (Int64.repr 0))  s1 s2 tr).
      assert(eeval e1 (Int64.repr 0) ∘ eeval e2 (Int64.repr 0) == eeval e1 (Int64.repr 0) ∘ eeval e2  (Int64.repr 0)) as HOR1_hlp. reflexivity.
      specialize (HOR1 HOR1_hlp H). clear HOR1_hlp. destruct HOR1 as [tr1 [tr2 [s1_2 [? [? ?]]]]].
       
        specialize (IHe1 _ _ _ _ H2).
        specialize (IHe2 _ _ _ _ H3).
        symmetry in H1.
        etransitivity_nn; [apply H1 | apply MES_Cont, IHe1 |].
        etransitivity_1n; [ apply app_nil_l | apply ES_BinopR_NSC; simpl; tauto |].
        etransitivity_nn; [ apply app_nil_r | apply MES_Cont, IHe2 |].
        etransitivity_1n; [apply app_nil_l | | apply rt_refl_concrete].
        constructor.
        simpl.
        unfold bool_compute.
        tauto.
        }
        (* Not revised below, further debugging needed.**)
    - etransitivity_1n; [apply app_nil_l |constructor |]. 
      unfold and_denote in H.
      destruct H as [? | [? | ?] ].
      * destruct H as [? ?].
        specialize (IHe1 _ _ _ _ H).
        etransitivity_nn; [apply app_nil_r | apply MES_Cont, IHe1 |].
        etransitivity_1n; [ apply app_nil_l |  | apply rt_refl_concrete ].
        apply ES_BinopR_SC.
        simpl.
        tauto.
      * destruct H as [n1 [? [? ? ] ] ].
             epose proof Rel_Concat_element_concat_rev2 as HAND1.
      specialize (HAND1 (eeval e1 n1)  (eeval e2  (Int64.repr 0) )  (eeval e1 n1 ∘ eeval e2  (Int64.repr 0))  s1 s2 tr).
      assert(eeval e1 n1 ∘ eeval e2 (Int64.repr 0) == eeval e1 n1 ∘ eeval e2  (Int64.repr 0)) as HAND1_hlp. reflexivity.
      specialize (HAND1 HAND1_hlp H). clear HAND1_hlp. destruct HAND1 as [tr1 [tr2 [s1_2 [? [? ?]]]]].
        specialize (IHe1 _ _ _ _ H3).
        specialize (IHe2 _ _ _ _ H4).
        symmetry in H2.
        etransitivity_nn; [apply H2 | apply MES_Cont, IHe1 |].
        etransitivity_1n; [ apply app_nil_l | apply ES_BinopR_NSC; simpl; tauto |].
        etransitivity_nn; [ apply app_nil_r | apply MES_Cont, IHe2 |].
        etransitivity_1n; [apply app_nil_l | | apply rt_refl_concrete].
        constructor.
        simpl.
        unfold bool_compute.
        tauto.
      * destruct H as [n1 [n2 [? [? [? ? ] ] ] ] ].
             epose proof Rel_Concat_element_concat_rev2 as HAND1.
      specialize (HAND1 (eeval e1 n1)  (eeval e2 n2 )  (eeval e1 n1 ∘ eeval e2   n2)  s1 s2 tr).
      assert(eeval e1 n1 ∘ eeval e2  n2 == eeval e1 n1 ∘ eeval e2  n2) as HAND1_hlp. reflexivity.
      specialize (HAND1 HAND1_hlp H). clear HAND1_hlp. destruct HAND1 as [tr1 [tr2 [s1_2 [? [? ?]]]]].
        specialize (IHe1 _ _ _ _ H4).
        specialize (IHe2 _ _ _ _ H5).
        symmetry in H3.
        etransitivity_nn; [apply H3 | apply MES_Cont, IHe1 |].
        etransitivity_1n; [ apply app_nil_l | apply ES_BinopR_NSC; simpl; tauto |].
        etransitivity_nn; [ apply app_nil_r | apply MES_Cont, IHe2 |].
        etransitivity_1n; [apply app_nil_l | | apply rt_refl_concrete].
        constructor.
        simpl.
        unfold bool_compute.
        tauto.
    - unfold cmp_denote in H.
      destruct H as [n1 [n2 [? ? ] ] ].
    	
    	epose proof Rel_Concat_element_concat_rev2 as HCmp1.
      specialize (HCmp1 (eeval e1 n1)  (eeval e2 n2 )  (eeval e1 n1 ∘ eeval e2   n2)  s1 s2 tr).
      assert(eeval e1 n1 ∘ eeval e2  n2 == eeval e1 n1 ∘ eeval e2  n2) as HCmp1_hlp. reflexivity.
      specialize (HCmp1 HCmp1_hlp H). clear HCmp1_hlp. destruct HCmp1 as [tr1 [tr2 [s1_2 [? [? ?]]]]].
      
      specialize (IHe1 _ _ _ _ H2).
      specialize (IHe2 _ _ _  _ H3).
      symmetry in H1.
      
      etransitivity_1n ; [apply app_nil_l | constructor |].
      etransitivity_nn; [apply H1 |apply MES_Cont, IHe1 |].
      etransitivity_1n; [apply app_nil_l |apply ES_BinopR_NSC; simpl; tauto |].
      etransitivity_nn; [apply app_nil_r |apply MES_Cont, IHe2 |].
      etransitivity_1n; [apply app_nil_l | | apply rt_refl_concrete].
      constructor.
      simpl.
      unfold cmp_compute.
      tauto.
     - unfold cmp_denote in H.
      destruct H as [n1 [n2 [? ? ] ] ].
    	
    	epose proof Rel_Concat_element_concat_rev2 as HCmp1.
      specialize (HCmp1 (eeval e1 n1)  (eeval e2 n2 )  (eeval e1 n1 ∘ eeval e2   n2)  s1 s2 tr).
      assert(eeval e1 n1 ∘ eeval e2  n2 == eeval e1 n1 ∘ eeval e2  n2) as HCmp1_hlp. reflexivity.
      specialize (HCmp1 HCmp1_hlp H). clear HCmp1_hlp. destruct HCmp1 as [tr1 [tr2 [s1_2 [? [? ?]]]]].
      
      specialize (IHe1 _ _ _ _ H2).
      specialize (IHe2 _ _ _  _ H3).
      symmetry in H1.
      
      etransitivity_1n ; [apply app_nil_l | constructor |].
      etransitivity_nn; [apply H1 |apply MES_Cont, IHe1 |].
      etransitivity_1n; [apply app_nil_l |apply ES_BinopR_NSC; simpl; tauto |].
      etransitivity_nn; [apply app_nil_r |apply MES_Cont, IHe2 |].
      etransitivity_1n; [apply app_nil_l | | apply rt_refl_concrete].
      constructor.
      simpl.
      unfold cmp_compute.
      tauto.
     - unfold cmp_denote in H.
      destruct H as [n1 [n2 [? ? ] ] ].
    	
    	epose proof Rel_Concat_element_concat_rev2 as HCmp1.
      specialize (HCmp1 (eeval e1 n1)  (eeval e2 n2 )  (eeval e1 n1 ∘ eeval e2   n2)  s1 s2 tr).
      assert(eeval e1 n1 ∘ eeval e2  n2 == eeval e1 n1 ∘ eeval e2  n2) as HCmp1_hlp. reflexivity.
      specialize (HCmp1 HCmp1_hlp H). clear HCmp1_hlp. destruct HCmp1 as [tr1 [tr2 [s1_2 [? [? ?]]]]].
      
      specialize (IHe1 _ _ _ _ H2).
      specialize (IHe2 _ _ _  _ H3).
      symmetry in H1.
      
      etransitivity_1n ; [apply app_nil_l | constructor |].
      etransitivity_nn; [apply H1 |apply MES_Cont, IHe1 |].
      etransitivity_1n; [apply app_nil_l |apply ES_BinopR_NSC; simpl; tauto |].
      etransitivity_nn; [apply app_nil_r |apply MES_Cont, IHe2 |].
      etransitivity_1n; [apply app_nil_l | | apply rt_refl_concrete].
      constructor.
      simpl.
      unfold cmp_compute.
      tauto.
     - unfold cmp_denote in H.
      destruct H as [n1 [n2 [? ? ] ] ].
    	
    	epose proof Rel_Concat_element_concat_rev2 as HCmp1.
      specialize (HCmp1 (eeval e1 n1)  (eeval e2 n2 )  (eeval e1 n1 ∘ eeval e2   n2)  s1 s2 tr).
      assert(eeval e1 n1 ∘ eeval e2  n2 == eeval e1 n1 ∘ eeval e2  n2) as HCmp1_hlp. reflexivity.
      specialize (HCmp1 HCmp1_hlp H). clear HCmp1_hlp. destruct HCmp1 as [tr1 [tr2 [s1_2 [? [? ?]]]]].
      
      specialize (IHe1 _ _ _ _ H2).
      specialize (IHe2 _ _ _  _ H3).
      symmetry in H1.
      
      etransitivity_1n ; [apply app_nil_l | constructor |].
      etransitivity_nn; [apply H1 |apply MES_Cont, IHe1 |].
      etransitivity_1n; [apply app_nil_l |apply ES_BinopR_NSC; simpl; tauto |].
      etransitivity_nn; [apply app_nil_r |apply MES_Cont, IHe2 |].
      etransitivity_1n; [apply app_nil_l | | apply rt_refl_concrete].
      constructor.
      simpl.
      unfold cmp_compute.
      tauto.
     - unfold cmp_denote in H.
      destruct H as [n1 [n2 [? ? ] ] ].
    	
    	epose proof Rel_Concat_element_concat_rev2 as HCmp1.
      specialize (HCmp1 (eeval e1 n1)  (eeval e2 n2 )  (eeval e1 n1 ∘ eeval e2   n2)  s1 s2 tr).
      assert(eeval e1 n1 ∘ eeval e2  n2 == eeval e1 n1 ∘ eeval e2  n2) as HCmp1_hlp. reflexivity.
      specialize (HCmp1 HCmp1_hlp H). clear HCmp1_hlp. destruct HCmp1 as [tr1 [tr2 [s1_2 [? [? ?]]]]].
      
      specialize (IHe1 _ _ _ _ H2).
      specialize (IHe2 _ _ _  _ H3).
      symmetry in H1.
      
      etransitivity_1n ; [apply app_nil_l | constructor |].
      etransitivity_nn; [apply H1 |apply MES_Cont, IHe1 |].
      etransitivity_1n; [apply app_nil_l |apply ES_BinopR_NSC; simpl; tauto |].
      etransitivity_nn; [apply app_nil_r |apply MES_Cont, IHe2 |].
      etransitivity_1n; [apply app_nil_l | | apply rt_refl_concrete].
      constructor.
      simpl.
      unfold cmp_compute.
      tauto.
     - unfold cmp_denote in H.
      destruct H as [n1 [n2 [? ? ] ] ].
    	
    	epose proof Rel_Concat_element_concat_rev2 as HCmp1.
      specialize (HCmp1 (eeval e1 n1)  (eeval e2 n2 )  (eeval e1 n1 ∘ eeval e2   n2)  s1 s2 tr).
      assert(eeval e1 n1 ∘ eeval e2  n2 == eeval e1 n1 ∘ eeval e2  n2) as HCmp1_hlp. reflexivity.
      specialize (HCmp1 HCmp1_hlp H). clear HCmp1_hlp. destruct HCmp1 as [tr1 [tr2 [s1_2 [? [? ?]]]]].
      
      specialize (IHe1 _ _ _ _ H2).
      specialize (IHe2 _ _ _  _ H3).
      symmetry in H1.
      
      etransitivity_1n ; [apply app_nil_l | constructor |].
      etransitivity_nn; [apply H1 |apply MES_Cont, IHe1 |].
      etransitivity_1n; [apply app_nil_l |apply ES_BinopR_NSC; simpl; tauto |].
      etransitivity_nn; [apply app_nil_r |apply MES_Cont, IHe2 |].
      etransitivity_1n; [apply app_nil_l | | apply rt_refl_concrete].
      constructor.
      simpl.
      unfold cmp_compute.
      tauto.
    - unfold arith_denote1 in H.
      destruct H as [n1 [n2 [? [? [? ? ] ] ] ] ].
    	epose proof Rel_Concat_element_concat_rev2 as HArith1.
      specialize (HArith1 (eeval e1 n1)  (eeval e2 n2 )  (eeval e1 n1 ∘ eeval e2   n2)  s1 s2 tr).
      assert(eeval e1 n1 ∘ eeval e2  n2 == eeval e1 n1 ∘ eeval e2  n2) as HArith1_hlp. reflexivity.
      specialize (HArith1 HArith1_hlp H). clear HArith1_hlp. destruct HArith1 as [tr1 [tr2 [s1_2 [? [? ?]]]]].
      specialize (IHe1 _ _ _ _ H4).
      specialize (IHe2 _ _ _ _ H5).
      etransitivity_1n ; [apply app_nil_l | constructor |].
      etransitivity_nn; [symmetry in H3;apply H3 |apply MES_Cont, IHe1 |].
      etransitivity_1n; [apply app_nil_l |apply ES_BinopR_NSC; simpl; tauto |].
      etransitivity_nn; [apply app_nil_r |apply MES_Cont, IHe2 |].
      etransitivity_1n; [apply app_nil_l | | apply rt_refl_concrete].
      constructor.
      simpl.
      unfold arith_compute1.
      tauto.
    - unfold arith_denote1 in H.
      destruct H as [n1 [n2 [? [? [? ? ] ] ] ] ].
    	epose proof Rel_Concat_element_concat_rev2 as HArith1.
      specialize (HArith1 (eeval e1 n1)  (eeval e2 n2 )  (eeval e1 n1 ∘ eeval e2   n2)  s1 s2 tr).
      assert(eeval e1 n1 ∘ eeval e2  n2 == eeval e1 n1 ∘ eeval e2  n2) as HArith1_hlp. reflexivity.
      specialize (HArith1 HArith1_hlp H). clear HArith1_hlp. destruct HArith1 as [tr1 [tr2 [s1_2 [? [? ?]]]]].
      specialize (IHe1 _ _ _ _ H4).
      specialize (IHe2 _ _ _ _ H5).
      etransitivity_1n ; [apply app_nil_l | constructor |].
      etransitivity_nn; [symmetry in H3;apply H3 |apply MES_Cont, IHe1 |].
      etransitivity_1n; [apply app_nil_l |apply ES_BinopR_NSC; simpl; tauto |].
      etransitivity_nn; [apply app_nil_r |apply MES_Cont, IHe2 |].
      etransitivity_1n; [apply app_nil_l | | apply rt_refl_concrete].
      constructor.
      simpl.
      unfold arith_compute1.
      tauto.
    - unfold arith_denote1 in H.
      destruct H as [n1 [n2 [? [? [? ? ] ] ] ] ].
    	epose proof Rel_Concat_element_concat_rev2 as HArith1.
      specialize (HArith1 (eeval e1 n1)  (eeval e2 n2 )  (eeval e1 n1 ∘ eeval e2   n2)  s1 s2 tr).
      assert(eeval e1 n1 ∘ eeval e2  n2 == eeval e1 n1 ∘ eeval e2  n2) as HArith1_hlp. reflexivity.
      specialize (HArith1 HArith1_hlp H). clear HArith1_hlp. destruct HArith1 as [tr1 [tr2 [s1_2 [? [? ?]]]]].
      specialize (IHe1 _ _ _ _ H4).
      specialize (IHe2 _ _ _ _ H5).
      etransitivity_1n ; [apply app_nil_l | constructor |].
      etransitivity_nn; [symmetry in H3;apply H3 |apply MES_Cont, IHe1 |].
      etransitivity_1n; [apply app_nil_l |apply ES_BinopR_NSC; simpl; tauto |].
      etransitivity_nn; [apply app_nil_r |apply MES_Cont, IHe2 |].
      etransitivity_1n; [apply app_nil_l | | apply rt_refl_concrete].
      constructor.
      simpl.
      unfold arith_compute1.
      tauto.
    - unfold arith_denote2 in H.
      destruct H as [n1 [n2 [? [? [? ? ] ] ] ] ].
    	epose proof Rel_Concat_element_concat_rev2 as HArith1.
      specialize (HArith1 (eeval e1 n1)  (eeval e2 n2 )  (eeval e1 n1 ∘ eeval e2   n2)  s1 s2 tr).
      assert(eeval e1 n1 ∘ eeval e2  n2 == eeval e1 n1 ∘ eeval e2  n2) as HArith1_hlp. reflexivity.
      specialize (HArith1 HArith1_hlp H). clear HArith1_hlp. destruct HArith1 as [tr1 [tr2 [s1_2 [? [? ?]]]]].
      specialize (IHe1 _ _ _ _ H4).
      specialize (IHe2 _ _ _ _ H5).
      etransitivity_1n ; [apply app_nil_l | constructor |].
      etransitivity_nn; [symmetry in H3;apply H3 |apply MES_Cont, IHe1 |].
      etransitivity_1n; [apply app_nil_l |apply ES_BinopR_NSC; simpl; tauto |].
      etransitivity_nn; [apply app_nil_r |apply MES_Cont, IHe2 |].
      etransitivity_1n; [apply app_nil_l | | apply rt_refl_concrete].
      constructor.
      simpl.
      unfold arith_compute2.
      tauto.
    - unfold arith_denote2 in H.
      destruct H as [n1 [n2 [? [? [? ? ] ] ] ] ].
    	epose proof Rel_Concat_element_concat_rev2 as HArith1.
      specialize (HArith1 (eeval e1 n1)  (eeval e2 n2 )  (eeval e1 n1 ∘ eeval e2   n2)  s1 s2 tr).
      assert(eeval e1 n1 ∘ eeval e2  n2 == eeval e1 n1 ∘ eeval e2  n2) as HArith1_hlp. reflexivity.
      specialize (HArith1 HArith1_hlp H). clear HArith1_hlp. destruct HArith1 as [tr1 [tr2 [s1_2 [? [? ?]]]]].
      specialize (IHe1 _ _ _ _ H4).
      specialize (IHe2 _ _ _ _ H5).
      etransitivity_1n ; [apply app_nil_l | constructor |].
      etransitivity_nn; [symmetry in H3;apply H3 |apply MES_Cont, IHe1 |].
      etransitivity_1n; [apply app_nil_l |apply ES_BinopR_NSC; simpl; tauto |].
      etransitivity_nn; [apply app_nil_r |apply MES_Cont, IHe2 |].
      etransitivity_1n; [apply app_nil_l | | apply rt_refl_concrete].
      constructor.
      simpl.
      unfold arith_compute2.
      tauto.
      (*Arithment ooperations' proof reconstructed.*)
  + destruct op; simpl in H.
    - unfold not_denote in H.
      destruct H as [n0 [H0 [H|H] ]].
      * destruct H as [? ? ].
        specialize (IHe _ _ _ _ H0).
        etransitivity_1n; [apply app_nil_l | constructor |].
        etransitivity_nn; [apply app_nil_r|apply MES_Cont, IHe |].
        etransitivity_1n; [apply app_nil_l | | apply rt_refl_concrete].
        constructor.
        simpl.
        unfold not_compute.
        tauto.
       * destruct H as [? ? ].
        specialize (IHe _ _ _ _ H0).
        etransitivity_1n; [apply app_nil_l | constructor |].
        etransitivity_nn; [apply app_nil_r|apply MES_Cont, IHe |].
        etransitivity_1n; [apply app_nil_l | | apply rt_refl_concrete].
        constructor.
        simpl.
        unfold not_compute.
        tauto.
    - unfold neg_denote in H.
      destruct H as [n0 [? [? ? ] ] ].
      specialize (IHe _ _ _ _ H).
        etransitivity_1n; [apply app_nil_l | constructor |].
        etransitivity_nn; [apply app_nil_r|apply MES_Cont, IHe |].
        etransitivity_1n; [apply app_nil_l | | apply rt_refl_concrete].
      constructor.
      simpl.
      unfold neg_compute.
      tauto.
  + unfold deref_denote in H.
    destruct H as [n0 [? ?] ].
    specialize (IHe _ _ _ _ H).
        etransitivity_1n; [apply app_nil_l | constructor |].
        etransitivity_nn; [apply app_nil_r|apply MES_Cont, IHe |].
        etransitivity_1n; [apply app_nil_l | | apply rt_refl_concrete].
    constructor.
    tauto.
    (*Proofs for our new definiton:*)
   + unfold malloc_denote in H.
   		destruct H as [n0].
       epose proof Rel_Concat_element_concat_rev2 as HArith1.
      specialize (HArith1 (eeval e n0)   (malloc_action n0 n)  (eeval e n0 ∘ malloc_action n0 n) s1 s2 tr).
      assert(eeval e n0 ∘ malloc_action n0 n==eeval e n0 ∘ malloc_action n0 n) as HArith1_hlp. reflexivity.
      specialize (HArith1 HArith1_hlp H). clear HArith1_hlp. destruct HArith1 as [tr1 [tr2 [s1_2 [? [? ?]]]]].
      
      specialize (IHe _ _ _ _ H1).
      symmetry in H0.
   	      etransitivity_1n ; [apply app_nil_l | constructor |].
      etransitivity_nn; [apply H0 |apply MES_Cont, IHe |].
      etransitivity_1n; [apply app_nil_r |apply ES_MallocStep,H2;simpl|apply rt_refl_concrete].
	+ unfold read_int_denote in H.
		destruct H as [? ?].
		subst tr s2.
		etransitivity_1n;[apply app_nil_r | constructor | apply rt_refl_concrete].
	+ unfold read_char_denote in H.
		destruct H as [? ?].
		subst tr s2.
		etransitivity_1n;[apply app_nil_r |  | apply rt_refl_concrete].
		constructor.
Qed.

(*eeval_multi_estep Finished. *)


Lemma ceval_multi_cstep: forall c s1 s2 tr,
  (ceval c) s1 tr  s2 ->
  multi_cstep (CL_FocusedCom c, s1) tr (CL_Finished, s2).
Proof.
  intros c.
  induction c; simpl; intros.
  + destruct e1; try tauto.
    - unfold asgn_var_denote in H. 
      destruct H as [n ].
      
       epose proof Rel_Concat_element_concat_rev2 as HArith1.
      specialize (HArith1 (eeval e2 n)   (asgn_var_action_denote x n)  (eeval e2 n ∘asgn_var_action_denote x n) s1 s2 tr).
      assert(eeval e2 n ∘ asgn_var_action_denote x n==eeval e2 n ∘asgn_var_action_denote x n) as HArith1_hlp. reflexivity.
      specialize (HArith1 HArith1_hlp H). clear HArith1_hlp. destruct HArith1 as [tr1 [tr2 [s1_2 [? [? ?]]]]].
      
      epose proof eeval_multi_estep. specialize (H3 _ _ _ _ _ H1).
      etransitivity_1n; [ apply app_nil_l |constructor |].
      etransitivity_nn; [ symmetry in H0; apply H0 |apply MCS_ECont,H3|].
      etransitivity_1n; [apply app_nil_r| |apply rt_refl_concrete].
      
      unfold asgn_var_action_denote in H2.
      destruct H2 as [? [? [? ?]]].
      subst tr2.
      constructor; auto.
    - unfold asgn_deref_denote in H.
      destruct H as [n1 [n2 ] ].
      
      epose proof Rel_Concat_element_concat_rev3 _ _ _  _ _ _ H as HArith1.
      assert(eeval e1 n1 ∘ eeval e2 n2 ∘ asgn_deref_action_denote n1 n2 ==eeval e1 n1 ∘ eeval e2 n2 ∘ asgn_deref_action_denote n1 n2) as HArith1_hlp. reflexivity.
      specialize (HArith1 HArith1_hlp). clear HArith1_hlp. destruct HArith1 as [tr1 [tr4 [s1a2 [? [? ?]]]]].
      
      epose proof Rel_Concat_element_concat_rev3 _ _ _  _ _ _ H2 as HArith1.
      assert(eeval e2 n2 ∘ asgn_deref_action_denote n1 n2 == eeval e2 n2 ∘ asgn_deref_action_denote n1 n2) as HArith1_hlp. reflexivity.
      specialize (HArith1 HArith1_hlp). clear HArith1_hlp. destruct HArith1 as [tr2 [tr3 [s1b2 [? [? ?]]]]].
      
      
      pose proof eeval_multi_estep _ _ _ _ _ H1.
      pose proof eeval_multi_estep _ _ _ _ _ H4.
      etransitivity_1n; [apply app_nil_l | constructor |].
      etransitivity_nn; [apply H0 | apply MCS_ECont,H6 | ].
      etransitivity_1n; [apply app_nil_l | constructor |].
      etransitivity_nn; [apply H3 | apply MCS_ECont, H7 |].
      
      unfold asgn_deref_action_denote in H5.
      destruct H5 as [?].
      subst tr3. 
      
      etransitivity_1n; [apply app_nil_l | |apply rt_refl_concrete].
      constructor; tauto.
      (*Stopped here*)
  + unfold BinRel.concat in H.
    destruct H as [s1' [? ?] ].
    specialize (IHc1 _ _ H).
    specialize (IHc2 _ _ H0).
    etransitivity_1n; [constructor |].
    etransitivity; [apply MCS_CCont, IHc1 |].
    etransitivity_1n; [constructor |].
    etransitivity; [apply IHc2 |].
    reflexivity.
  + destruct H as [H | H]; unfold BinRel.concat in H.
    - destruct H as [s1' [? ?] ].
      unfold test1 in H.
      destruct H as [n [? [? ?] ] ]; subst s1'.
      pose proof eeval_multi_estep _ _ _ H1.
      specialize (IHc1 _ _ H0).
      etransitivity_1n; [constructor |].
      etransitivity; [apply MCS_ECont, H |].
      etransitivity_1n; [constructor; tauto |].
      apply IHc1.
    - destruct H as [s1' [? ?] ].
      unfold test0 in H.
      destruct H as [? ?]; subst s1'.
      pose proof eeval_multi_estep _ _ _ H1.
      specialize (IHc2 _ _ H0).
      etransitivity_1n; [constructor |].
      etransitivity; [apply MCS_ECont, H |].
      etransitivity_1n; [constructor; tauto |].
      apply IHc2.
  + etransitivity_1n; [constructor |].
    unfold BW_LFix in H.
    unfold omega_lub, oLub_while_fin in H.
    destruct H as [n ?].
    revert s1 H; induction n; simpl; intros.
    - unfold bot, Bot_while_fin in H.
      contradiction.
    - destruct H.
      * destruct H as [s1' [? ?]].
        destruct H0 as [s1'' [? ?]].
        specialize (IHn _ H1); clear H1.
        unfold test1 in H.
        destruct H as [n0 [? [? ?] ] ]; subst s1'.
        pose proof eeval_multi_estep _ _ _ H1.
        etransitivity; [apply MCS_ECont, H |].
        etransitivity_1n; [constructor; tauto |].
        specialize (IHc _ _ H0).
        etransitivity; [apply MCS_CCont, IHc |].
        etransitivity_1n; [constructor |].
        apply IHn.
      * destruct H as [? ?].
        subst s2.
        pose proof eeval_multi_estep _ _ _ H0.
        etransitivity; [apply MCS_ECont, H |].
        etransitivity_1n; [constructor; tauto |].
        reflexivity.
Qed.

