Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import compcert.lib.Integers.
Require Import WhileDB.SetsDomain.
Require Import WhileDB.RelDomain.
Require Import WhileDB.RelDomainAuxProofs.
Require Import WhileDB.BWFix.
Require Import WhileDB.BWFixAuxProofs.
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
  assert (forall n tr el1 s1 el2 s2 k, nsteps estep n (el1, s1) tr (el2, s2)
   -> nsteps estep n (EL_Cont el1 k, s1) tr (EL_Cont el2 k, s2) ).
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
  assert (forall n tr el1 s1 el2 s2 k, nsteps estep n (el1, s1) tr (el2, s2) -> 
  			nsteps cstep n (CL_ECont el1 k, s1) tr (CL_ECont el2 k, s2) ).
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
        etransitivity_1n. apply app_nil_l. constructor. unfold binop_compute. 
        unfold bool_compute. right. split;eauto. apply rt_refl_concrete.
        }
      {
       destruct H as [? ? ].
       
       epose proof Rel_Concat_element_concat_rev2 as HOR1.
      specialize (HOR1 (eeval e1 (Int64.repr 0))  (eeval e2  (Int64.repr 0) )  
      	(eeval e1 (Int64.repr 0) ∘ eeval e2  (Int64.repr 0))  s1 s2 tr).
      assert(eeval e1 (Int64.repr 0) ∘ eeval e2 (Int64.repr 0) == 
      eeval e1 (Int64.repr 0) ∘ eeval e2  (Int64.repr 0)) as HOR1_hlp. reflexivity.
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
      assert(eeval e1 n1 ∘ eeval e2 n2 ∘ asgn_deref_action_denote n1 n2 ==
      eeval e1 n1 ∘ eeval e2 n2 ∘ asgn_deref_action_denote n1 n2) as HArith1_hlp. reflexivity.
      specialize (HArith1 HArith1_hlp). clear HArith1_hlp. destruct HArith1 as [tr1 [tr4 [s1a2 [? [? ?]]]]].
      
      epose proof Rel_Concat_element_concat_rev3 _ _ _  _ _ _ H2 as HArith1.
      assert(eeval e2 n2 ∘ asgn_deref_action_denote n1 n2 == 
      eeval e2 n2 ∘ asgn_deref_action_denote n1 n2) as HArith1_hlp. reflexivity.
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
      (*Stopped here 2022-12-9-23:12*)
  + unfold seq_denote in H.
  
      epose proof Rel_Concat_element_concat_rev3 _ _ _  _ _ _ H as HArith1.
      assert(ceval c1∘ ceval c2 ==ceval c1∘ ceval c2) as HArith1_hlp. reflexivity.
      specialize (HArith1 HArith1_hlp). clear HArith1_hlp. destruct HArith1 as [tr1 [tr2 [s1a2 [? [? ?]]]]].
      
    specialize (IHc1 _ _ _ H1).
    specialize (IHc2 _ _ _ H2).
      etransitivity_1n; [apply app_nil_l | constructor |].
    etransitivity_nn; [apply H0 |apply MCS_CCont, IHc1 |].
    etransitivity_1n; [apply app_nil_l |constructor |].
    etransitivity_nn ; [apply app_nil_r |apply IHc2 | apply rt_refl_concrete].

  + 
  unfold if_denote in H. 
  epose proof rel_union_or_iff  as HIF1. specialize (HIF1 (test1 (eeval e) ∘ ceval c1) (test0 (eeval e) ∘ ceval c2) s1 s2 tr ).
	destruct HIF1. apply H0 in H. clear H0 H1.

  destruct H as [H | H].
    - 
    	epose proof Rel_Concat_element_concat_rev3 _ _ _  _ _ _ H as HArith1.
      assert(test1 (eeval e) ∘ ceval c1==test1 (eeval e) ∘ ceval c1) as HArith1_hlp. reflexivity.
      specialize (HArith1 HArith1_hlp). clear HArith1_hlp. destruct HArith1 as [tr1 [tr2 [s1a2 [? [? ?]]]]].
    
      unfold test1 in H1.
      destruct H1 as [n [? ? ] ]. 
      pose proof eeval_multi_estep _ _ _ _ _ H1.
      specialize (IHc1 _ _ _ H2).
      etransitivity_1n; [apply app_nil_l | constructor |].
      etransitivity_nn; [apply H0 | apply MCS_ECont,H4 |].
      etransitivity_1n; [apply app_nil_l | constructor; tauto |].
      apply IHc1.
    -     	
    	epose proof Rel_Concat_element_concat_rev3 _ _ _  _ _ _ H as HArith1.
      assert(test0 (eeval e) ∘ ceval c2==test0 (eeval e) ∘ ceval c2) as HArith1_hlp. reflexivity.
      specialize (HArith1 HArith1_hlp). clear HArith1_hlp. destruct HArith1 as [tr1 [tr2 [s1a2 [? [? ?]]]]].
    
      unfold test0 in H1.
(*       destruct H1 as [n [? ? ] ].  *)
      pose proof eeval_multi_estep _ _ _ _ _ H1.
      specialize (IHc2 _ _ _ H2).
      etransitivity_1n; [apply app_nil_l | constructor |].
      etransitivity_nn; [apply H0 | apply MCS_ECont,H3 |].
      etransitivity_1n; [apply app_nil_l | constructor; tauto |].
      apply IHc2.
      (*2022-12-9 22:32:59*)
  + etransitivity_1n; [apply app_nil_l |constructor |].
    unfold while_denote,BW_LFix in H.
    unfold omega_lub, oLub_while_fin in H.
    destruct H as [n ?].
    revert s1 s2 tr H ; induction n;[simpl |]. (* ; simpl; intros. *)
    { simpl. intros. unfold bot, Bot_while_fin in H.
      contradiction.
     }
    { revert IHn. sets_unfold. intros. 
    remember  (fun (X : prog_state -> list event -> prog_state -> Prop) (a : prog_state) (a0 : list event) (a1 : prog_state) =>
       (test1 (eeval e) ∘ ceval c ∘ X) a a0 a1 \/ test0 (eeval e) a a0 a1) as fX.

    pose proof Nat_iter_succ2 (prog_state -> list event -> prog_state -> Prop) n fX bot.
       rewrite H0 in H. clear H0.
       subst fX.
           remember  (fun (X : prog_state -> list event -> prog_state -> Prop) (a : prog_state) (a0 : list event) (a1 : prog_state) =>
       (test1 (eeval e) ∘ ceval c ∘ X) a a0 a1 \/ test0 (eeval e) a a0 a1) as fX.

    	 destruct H. (* 到这里和原来的证明搭上了边，但不能直接destruct，而需要用引力分拆H  *)
      *
          	epose proof Rel_Concat_element_concat_rev3 _ _ _  _ _ _ H as HArith1.
      assert(test1 (eeval e) ∘ ceval c ∘ Nat.iter n fX bot==test1 (eeval e) ∘ ceval c ∘ Nat.iter n fX bot) as HArith1_hlp. reflexivity.
      specialize (HArith1 HArith1_hlp). clear HArith1_hlp. destruct HArith1 as [tr1 [tr23 [s1a2 [? [? ?]]]]].
      
      epose proof Rel_Concat_element_concat_rev3 _ _ _  _ _ _ H2 as HArith1.
      assert(ceval c ∘ Nat.iter n fX bot== ceval c ∘ Nat.iter n fX bot) as HArith1_hlp. reflexivity.
      specialize (HArith1 HArith1_hlp). clear HArith1_hlp. destruct HArith1 as [tr2 [tr3 [s1b2 [? [? ?]]]]].

				clear H  H2.

        specialize (IHn _ _ _ H5); clear H5.
        unfold test1 in H1. destruct H1 as [n0 [? ?]].
(*         destruct H as [n0 [? [? ?] ] ]; subst s1'. *)
        pose proof eeval_multi_estep _ _ _ _ _ H.
        etransitivity_nn; [apply H0 |apply MCS_ECont, H2 |].
        etransitivity_1n; [apply app_nil_l|constructor; tauto |].
        specialize (IHc _ _ _  H4).
        etransitivity_nn; [apply H3|apply MCS_CCont, IHc |].
        etransitivity_1n; [apply app_nil_l |constructor |].
        apply IHn.
      * unfold test0 in H.
        pose proof eeval_multi_estep _ _ _ _ _ H.
        etransitivity_nn; [apply app_nil_r|apply MCS_ECont, H0 |].
        etransitivity_1n; [apply app_nil_l|constructor; tauto |apply rt_refl_concrete].
     }
     + unfold write_int_denote, write_int_denote_aux in H. destruct H.
               	epose proof Rel_Concat_element_concat_rev3 _ _ _  _ _ _ H as HArith1.
      assert((eeval e x ∘ write_int_action_denote x)==eeval e x ∘ write_int_action_denote x) as HArith1_hlp. reflexivity.
      specialize (HArith1 HArith1_hlp). clear HArith1_hlp. destruct HArith1 as [tr1 [tr2 [s1a2 [? [? ?]]]]].
      pose proof eeval_multi_estep _ _ _ _ _ H1.
      unfold write_int_action_denote in H2. destruct H2. subst s1a2.
      etransitivity_1n; [apply app_nil_l|constructor; tauto |].
      etransitivity_nn; [apply H0|apply MCS_ECont, H3 |].
      subst tr2. 
      etransitivity_1n; [apply app_nil_r |constructor |apply rt_refl_concrete].
     + unfold write_char_denote, write_char_denote_aux in H. destruct H.
               	epose proof Rel_Concat_element_concat_rev3 _ _ _  _ _ _ H as HArith1.
      assert((eeval e x ∘ write_char_action_denote x)==eeval e x ∘ write_char_action_denote x) as HArith1_hlp. reflexivity.
      specialize (HArith1 HArith1_hlp). clear HArith1_hlp. destruct HArith1 as [tr1 [tr2 [s1a2 [? [? ?]]]]].
      pose proof eeval_multi_estep _ _ _ _ _ H1.
      unfold write_char_action_denote in H2. destruct H2. subst s1a2.
      etransitivity_1n; [apply app_nil_l|constructor; tauto |].
      etransitivity_nn; [apply H0|apply MCS_ECont, H3 |].
      subst tr2. 
      etransitivity_1n; [apply app_nil_r |constructor |apply rt_refl_concrete].
Qed.


(** 先定义“后续表达式”求值的指称语义 *)
(*笔记： 吴子健，2022-12-10 19:25, 这里一定要注意短路求值的问题，
比如，当KBinOpL, op=Or， n1<>0的时候，相应的ek_eval后面的context
指称语义就自然地要求context的求值被短路，也就是ek_eval
此时满足有s1=s2，tr=nil 下面注释中是一开始时的错误定义方式
*)
(* Definition binop_compute_step1
             (op: binop)
             (n1: int64)
             (D2: int64 -> Prop)
             (n: int64): Prop :=
  match op with
  | OOr => Int64.signed n1 <> 0 /\ n = Int64.repr 1 \/
           (exists n2,
              n1 = Int64.repr 0 /\
              D2 n2 /\
              Int64.signed n2 <> 0 /\
              n = Int64.repr 1) \/
           (n1 = Int64.repr 0 /\
            D2 (Int64.repr 0) /\
            n = Int64.repr 0)
  | OAnd => n1 = Int64.repr 0 /\ n = Int64.repr 0 \/
            (Int64.signed n1 <> 0 /\
             D2 (Int64.repr 0) /\
             n = Int64.repr 0) \/
            (exists n2,
               Int64.signed n1 <> 0 /\
               D2 n2 /\
               Int64.signed n2 <> 0 /\
               n = Int64.repr 1)
  | _ => exists n2, D2 n2 /\ binop_compute op n1 n2 n
  end.

Definition  eeval_to_D 
	(x: int64 -> prog_state -> list event -> prog_state -> Prop)
	(p1:prog_state) (tr:list event) (p2: prog_state):
	int64->Prop:=
	fun n => x n p1 tr p2. 

(*暂定第一版 ek_eval,定义如下（很有可能后期还要重修）*)
(*int64_1: 之前的expr_loc求得的值
最后总表达式的值是int64_2
prog_state_1: expr_lock求值完成后的state
接下来，求值expr_ectx，
经过了 list event 的 trace 达到了另外的一个 prop_state2,获得了最后的返回值 *)
Definition ek_eval (k: expr_ectx):
  int64 -> int64-> prog_state -> list event -> prog_state  -> Prop :=
  match k with
  | KBinopL op e2 => fun n1 n s1 tr s2 =>
      binop_compute_step1 op n1 ((eeval_to_D (eeval e2)) s1 tr s2) n
      	 (*这里出错了！当n1产生短路时，s1 tr s2实际可取任意值！！！*)
  | KBinopR n1 op => fun n2 n s1 tr s2 =>
  		s1=s2 /\ tr=nil /\
      binop_compute op n1 n2 n
  | KUnop op => fun n0 n s1 tr s2 =>
    	s1=s2 /\ tr=nil /\
      unop_compute op n0 n
  | KDeref => fun n0 n s1 tr s2 =>
      	s1=s2 /\ tr=nil /\
      s1.(mem) n0 = Some n
	| KMalloc =>  fun n0 n s1 tr s2 =>
    malloc_action n0 n s1 tr s2
  end. *)

Definition binop_compute_step1
             (op: binop)
             (n1: int64)
             (D2: int64-> prog_state -> list event ->prog_state -> Prop)
             (n: int64)
             (s1: prog_state)
             (tr:list event)
             (s2:prog_state ): Prop :=
  match op with
  | OOr => Int64.signed n1 <> 0 /\ n = Int64.repr 1 /\ s1=s2 /\ tr=nil	\/
           (exists n2,
              n1 = Int64.repr 0 /\
              D2 n2 s1 tr s2 /\
              Int64.signed n2 <> 0 /\
              n = Int64.repr 1) \/
           (n1 = Int64.repr 0 /\
            D2 (Int64.repr 0) s1 tr s2 /\
            n = Int64.repr 0)
  | OAnd => n1 = Int64.repr 0 /\ n = Int64.repr 0  /\ s1=s2 /\ tr=nil  \/
            (Int64.signed n1 <> 0 /\
             D2 (Int64.repr 0) s1 tr s2 /\
             n = Int64.repr 0) \/
            (exists n2,
               Int64.signed n1 <> 0 /\
               D2 n2 s1 tr s2 /\
               Int64.signed n2 <> 0 /\
               n = Int64.repr 1)
  | _ => exists n2, D2 n2 s1 tr s2 /\ binop_compute op n1 n2 n
  end.

Definition  eeval_to_D 
	(x: int64 -> prog_state -> list event -> prog_state -> Prop)
	(p1:prog_state) (tr:list event) (p2: prog_state):
	int64->Prop:=
	fun n => x n p1 tr p2. 

Definition ek_eval (k: expr_ectx):
  int64 -> int64-> prog_state -> list event -> prog_state  -> Prop :=
  match k with
  | KBinopL op e2 => fun n1 n s1 tr s2 =>
      binop_compute_step1 op n1 (eeval e2) n s1 tr s2
  | KBinopR n1 op => fun n2 n s1 tr s2 =>
  		s1=s2 /\ tr=nil /\
      binop_compute op n1 n2 n
  | KUnop op => fun n0 n s1 tr s2 =>
    	s1=s2 /\ tr=nil /\
      unop_compute op n0 n
  | KDeref => fun n0 n s1 tr s2 =>
      	s1=s2 /\ tr=nil /\
      s1.(mem) n0 = Some n
	| KMalloc =>  fun n0 n s1 tr s2 =>
    malloc_action n0 n s1 tr s2
  end.

Fixpoint el_eval (el: expr_loc):
   int64-> prog_state -> list event -> prog_state  -> Prop :=
  match el with
  | EL_Value n0 => fun n s1 tr s2 =>
  s1=s2/\ tr=nil/\
      n = n0
  | EL_FocusedExpr e => 
      eeval e
  | EL_Cont el k => fun n s1 tr s2 =>
(*   exists n0, ((el_eval el  n0)∘(ek_eval k n0 n)) s1 tr s2 *)
       exists n0 tr1 tr2 s1_2, tr1++tr2=tr/\ el_eval el n0 s1 tr1 s1_2 /\ ek_eval k n0 n s1_2 tr2 s2 
(*   | EL_Cont el k => fun s n =>
      exists n0, el_eval el s n0 /\ ek_eval k s n0 n *)
  end.   
  
Check eeval.
Check el_eval.

Ltac intros_until_EQ EQ :=
  match goal with
  | |- ?P -> ?Q => intros EQ
  | _ => intro; intros_until_EQ EQ
  end.
  
Ltac specialize_until_EQ H :=
  match type of H with
  | ?P -> ?Q => specialize (H eq_refl)
  | forall _:?A, _ => let a := fresh "a" in
                      evar (a: A);
                      specialize (H a);
                      subst a;
                      specialize_until_EQ H
  end.


Ltac new_intros_and_subst Base0 :=
  match goal with
  | |- Base0 => idtac
  | |- _ = ?x -> _ => is_var x;
                      let H := fresh "H" in
                      intros H;
                      revert Base0;
                      rewrite <- H in *;
                      clear x H;
                      intros Base0;
                      new_intros_and_subst Base0
  end.

(* Set Ltac Debug. *)


Ltac induction_step2 H :=
  match type of H with
  | ?cstep ?a ?tr ?b =>
    revert_dependent_component a H;
    revert_dependent_component b H;
    let a0 := fresh "cst" in
    let b0 := fresh "cst" in
    let EQa := fresh "EQ" in
    let EQb := fresh "EQ" in
    remember a as a0 eqn:EQa in H;
    remember b as b0 eqn:EQb in H;
    revert EQa EQb;
    revert_component a;
    revert_component b;
    match goal with
    | |- ?Q =>
      let Pab := eval pattern a0, b0 in Q in
      match Pab with
      | ?P0 a0 b0 =>
        let P := fresh "P" in
        set (P := P0); change (P a0 b0);
        induction H; intros_until_EQ EQa; intros EQb;
        repeat
          match goal with
          | IH: context [P] |- _ =>
            unfold P in IH;
            specialize_until_EQ IH;
            specialize (IH eq_refl)
          end;
        unfold P; clear P;
        match goal with
          | |- ?Base =>
            let Base0 := fresh in
            set (Base0 := Base);
            first [ injection EQa; injection EQb; clear EQa; clear EQb;
                    new_intros_and_subst Base0
                  | revert EQa EQb; new_intros_and_subst Base0
                  | idtac ];
            unfold Base0; clear Base0
        end
      end
    end
  end.

Lemma binop_compute_step1_binop_denote:
  forall s1 tr1 s2 tr2 s3 tr12 op (D1 D2: int64->prog_state->list event ->prog_state -> Prop) n1 n,
    D1 n1 s1 tr1 s2 ->
    tr1++tr2=tr12->
    binop_compute_step1 op n1 (D2) n s2 tr2 s3 ->
    binop_denote op D1 D2 n s1 tr12 s3.
Proof.
  intros.
  destruct op; simpl in *.
  + unfold or_denote.
    destruct H1 as [? | [? | ?]];[left | right; left | right; right].
    - exists n1. destruct H1 as [? [? [?]]]. repeat split;auto.
    subst tr2 s3. rewrite app_nil_r in H0. congruence.
    - destruct H1 as [n2 [? [? [?]]]]; exists n2.
     	repeat split;auto.
     	rel_unfold. exists s2, tr1, tr2. repeat split;auto. congruence.
    - destruct H1 as [? [?]]. repeat split;auto.
     	rel_unfold.
			exists s2, tr1, tr2. repeat split;auto. congruence.
  + unfold and_denote.
    destruct H1 as [? | [? | ?]];[left | right; left | right; right].
    - destruct H1 as [? [? [?]]]. repeat split;auto. subst n1.
    subst tr2 s3. rewrite app_nil_r in H0. congruence.
    - destruct H1 as [? [? ?]]. exists n1.
     	repeat split;auto.
     	rel_unfold. exists s2, tr1, tr2. repeat split;auto.
    - destruct H1 as [? [? [? [? ?]]]]. repeat split;auto.
     	rel_unfold. exists n1 ,x. split.
			exists s2, tr1, tr2. repeat [>repeat split;auto]. repeat split;auto.
  + unfold cmp_denote. (* unfold cmp_compute in H1.*)
    destruct H1 as [n2 [?]]. exists n1, n2. split;[|tauto]. rel_unfold. 
    exists s2,tr1,tr2. repeat split;auto.
  + unfold cmp_denote. 
    destruct H1 as [n2 [?]]. exists n1, n2. split;[|tauto]. rel_unfold. 
    exists s2,tr1,tr2. repeat split;auto.
  + unfold cmp_denote. 
    destruct H1 as [n2 [?]]. exists n1, n2. split;[|tauto]. rel_unfold. 
    exists s2,tr1,tr2. repeat split;auto.
  + unfold cmp_denote. 
    destruct H1 as [n2 [?]]. exists n1, n2. split;[|tauto]. rel_unfold. 
    exists s2,tr1,tr2. repeat split;auto.
  + unfold cmp_denote. 
    destruct H1 as [n2 [?]]. exists n1, n2. split;[|tauto]. rel_unfold. 
    exists s2,tr1,tr2. repeat split;auto.
  + unfold cmp_denote. 
    destruct H1 as [n2 [?]]. exists n1, n2. split;[|tauto]. rel_unfold. 
    exists s2,tr1,tr2. repeat split;auto.
  + unfold arith_denote1. (* unfold arith_compute1 in H0.*)
    destruct H1 as [n2 [?]]; exists n1, n2. split;[| tauto]. 
    rel_unfold; exists s2,tr1,tr2. repeat split;auto.
  + unfold arith_denote1. (* unfold arith_compute1 in H0.*)
    destruct H1 as [n2 [?]]; exists n1, n2. split;[| tauto]. 
    rel_unfold; exists s2,tr1,tr2. repeat split;auto.
  + unfold arith_denote1. (* unfold arith_compute1 in H0.*)
    destruct H1 as [n2 [?]]; exists n1, n2. split;[| tauto]. 
    rel_unfold; exists s2,tr1,tr2. repeat split;auto.
  + unfold arith_denote2. (* unfold arith_compute1 in H0.*)
    destruct H1 as [n2 [?]]; exists n1, n2. split;[| tauto]. 
    rel_unfold; exists s2,tr1,tr2. repeat split;auto.
  + unfold arith_denote2. (* unfold arith_compute1 in H0.*)
    destruct H1 as [n2 [?]]; exists n1, n2. split;[| tauto]. 
    rel_unfold; exists s2,tr1,tr2. repeat split;auto.
Qed. 


Lemma estep_sound: forall s1  el1 tr1 tr2 tr12 s2 s3 el2 n,
  estep (el1,s1) tr1 (el2,s2) ->
  el_eval el2 n s2 tr2 s3 ->
  tr1++tr2=tr12 ->
  el_eval el1 n s1 tr12 s3.
Proof.
  intros. 
  revert n H0. generalize dependent tr2. revert s3. revert tr12.  induction_step2 H.
  1:{ (*Rule 1: Var denote*) 	simpl. intros. simpl. unfold var_denote. repeat destruct H0 as [? H0].
    	repeat split;auto. subst tr2. auto. }
  1:{ (*Rule 2:Const denote*)simpl in*. unfold const_denote. intros. destruct H2 as [? [? ?]].
     repeat split;try auto;try congruence. }
  1:{ (*Rule 3*) intros. simpl in H1.  subst tr2.  intros. simpl. simpl in H0.  destruct H0 as [n1 [tr1 [tr2 [s1_2 [? [? ?]]]]]].
  	eapply binop_compute_step1_binop_denote;eauto. }
	{ (*Rule 4*) simpl  in *; intros. destruct H0 as [? [? ?]]. subst. exists n1, nil,nil,s3. repeat split;auto.
		unfold short_circuit in H. destruct op; simpl in *; try contradiction;left;repeat split;auto;destruct H;repeat auto.
		}
  {  (*Rule 5*)destruct op; simpl in *; 
  			try [>intros;destruct H0 as [n2 [? [? [? [? [? [? [? ?]]] ] ]]]]; 
  			exists n1,nil, tr2,s;subst; repeat split;auto;
  			exists n2;rewrite app_nil_r; auto].
  		+ intros. destruct H0 as [n2 [? [? [? [? [? [? [? ?]]] ] ]]]]. exists n1,nil, tr2,s.  subst. repeat split;auto. 
  				unfold bool_compute in H5. destruct H5 as [[? ?]|[? ?]].
  				{ right;right. repeat split;auto. rewrite app_nil_r. subst;auto. }
  				{ right;left. exists n2. repeat split;auto. rewrite app_nil_r. subst;auto. }
  		+ intros. destruct H0 as [n2 [? [? [? [? [? [? [? ?]]] ] ]]]]. exists n1,nil, tr2,s.  subst. repeat split;auto. 
  				unfold bool_compute in H5. destruct H5 as [[? ?]|[? ?]].
  				{ right;left. subst n2. repeat split;auto. rewrite app_nil_r. subst;auto. }
  				{ right;right. exists n2. repeat split;auto. rewrite app_nil_r. subst;auto. }
	}
	{
		intros. destruct op; simpl in * ;try [>destruct H0 as[? [? ?]]; exists n2, nil,nil,s;subst;repeat split;auto];
		try [>unfold arith_compute2 in H;unfold arith_compute1 in H; tauto].
		(*Rule 6*)
	}
	{ (*Rule 7*)
		intros. rewrite app_nil_l in H1. subst. simpl in *. destruct H0 as [? [? [? [? [? [? [? [? ?]]]]]]]]. subst. rewrite app_nil_r. 
		destruct op; simpl in *; intros.
		+ unfold not_denote;unfold not_compute in H3. exists x. tauto.
		+ unfold neg_denote;unfold neg_compute in H3. exists x. tauto.
	}
	{	 (*Rule 8*)
		intros. rewrite app_nil_l in H1. subst. simpl in *. destruct H0 as [? [? ?]]. subst.
		exists n0, nil,nil, s3. repeat split;tauto.
	}
	{ (*Rule 9*)
		intros. rewrite app_nil_l in H1. subst. simpl in *. destruct H0 as [? [? [? [? [? [? [? [? ?]]]]]]]]. subst. rewrite app_nil_r. 
		unfold deref_denote. exists x. tauto.
	}
	{ (*Rule 10*)
			intros. rewrite app_nil_l in H1. subst. simpl in *.  destruct H0 as [? [? ?]]. subst.
					exists n0, nil,nil, s3. repeat split;tauto.
	}
	{ (*Rule 11*)
				intros. rewrite app_nil_l in H1. subst. simpl in *.  destruct H0 as [? [? [? [? [? [?]]]]]]. 
				unfold malloc_denote. exists x. rel_unfold. exists x2, x0,x1. tauto.
	}
	{ (*Rule 12*)
						intros. simpl in *. destruct H0 as [? [?]];subst. exists n0, nil, tr,s1. split; try tauto.
						rewrite app_nil_l,app_nil_r. tauto.
	}
	{
					intros. simpl in *.  destruct H0 as [? [?]]. subst.
					unfold read_int_denote. tauto. 
	}
  { (*Rule 14: Write Char*)simpl in *. intros. unfold read_char_denote. destruct H0 as [? [? ?]]. split;[congruence| auto]. }
  { (*Rule 15: Cont*)simpl in IHestep.  simpl in *. intros. destruct H0 as [n0 [tr1 [tr3 [s2_3 [? [? ?]]]]]].
  			specialize (IHestep s2 el2 s1 el1).
  			assert ( (el1, s1) = (el1, s1)). auto. assert ( (el2, s2) = (el2, s2)). auto. 
  			specialize (IHestep H4 H5). clear H4 H5.
  			remember (tr++tr1) as tr01 eqn:Htr.
  			assert(tr01++tr3=tr12). { rewrite Htr. rewrite <- ((Coq.Lists.List.app_assoc)).  congruence. }
  			exists n0,tr01,tr3,s2_3.
  			specialize (IHestep tr01 s2_3 tr1). symmetry in Htr. specialize (IHestep Htr n0 H2).
  			repeat split;auto. }	
Qed.

(*Above check passed. 22-12-10 20:47*)














(** 最后要证明多步关系到指称语义的推导，只需对步数归纳即可。*)
Lemma multi_estep_eeval: forall s1 e tr s2 n,
  multi_estep (EL_FocusedExpr e,s1) tr (EL_Value n,s2) ->
  eeval e n s1 tr s2.
Proof.
  intros.
  assert (el_eval (EL_Value n) n s2 nil s2). {
    simpl.
    auto.
  }
  assert (el_eval (EL_FocusedExpr e) n s1 tr s2  -> eeval e n s1 tr s2). {
    simpl.
    tauto.
  }
  apply H1; clear H1.
  set (el1 := EL_FocusedExpr e) in *; clearbody el1.
  set (el2 := EL_Value n) in *; clearbody el2.
  clear e.
  unfold multi_estep in H.
  unfold clos_refl_trans in H.
  unfold Sets.omega_union in H.
  simpl in H. destruct H.
  revert H H0. revert tr s1 s2 el1 el2 n.
	induction x;intros.
	+ epose proof nsteps_O_id estep.  revert H H1. sets_unfold. intros. 
		specialize (H1 (el1,s1) tr (el2,s2)). unfold iff in H1;destruct H1. specialize (H1 H). clear H2.
		revert H1. simpl. rel_unfold. intros. destruct H1;subst. injection H2. intros. subst. tauto.
	+       assert( ((S x)%nat > O)%nat) as Hn1. lia.
				assert ( ((S x)-1 = x)%nat) as Hn2. lia.
    epose proof nsteps_1n estep (S x) (el1,s1) (el2,s2) tr Hn1 H.
    destruct H1 as [tr0 [tr1 [(el3,s3)  [? [? ?] ]]]]. rewrite Hn2 in H3.
    
    specialize (IHx _ _ _ _ _ n H3 H0).
    
    epose proof estep_sound as Htarget.
    specialize (Htarget s1 el1 tr0 tr1 tr s3 s2 el3 n H2 IHx).
    symmetry in H1.  specialize (Htarget H1). tauto.
Qed.



(** 下面定义_[com_ectx]_与_[expr_com_ectx]_的指称。*)
Definition ck_eval (k: com_ectx): prog_state -> list event -> prog_state -> Prop :=
  match k with
  | KSeq c => (ceval c) (*(ceval c).fin*)
  | KWhileBody e c => (ceval (CWhile e c))
  end.

Definition eck_eval (k: expr_com_ectx):
  int64 -> prog_state -> list event -> prog_state -> Prop :=
  match k with
  | KWhileCond e c =>
      fun n s1 tr s2 =>
        Int64.signed n <> 0 /\
          ((ceval c) ∘ (ceval (CWhile e c))) s1 tr s2 \/
        n = Int64.repr 0 /\ Rels.id s1 tr s2
  | KIf c1 c2 =>
      fun n s1 tr s2 =>
        Int64.signed n <> 0 /\ ((ceval c1) s1 tr s2) \/
        n = Int64.repr 0 /\ ((ceval c2) s1 tr s2)
  | KAsgnVar X =>
      fun n s1 tr s2 =>
        s2.(vars) X = n /\
        (forall Y, X <> Y -> s1.(vars) Y = s2.(vars) Y) /\
        (forall p, s1.(mem) p = s2.(mem) p) /\ tr=nil	
  | KAsgnMemL e2 =>
      fun n1 s1 tr s3 =>
        exists n2 s2,
          eeval e2 n2 s1 tr s2 /\
          s2.(mem) n1 <> None /\
          s3.(mem) n1 = Some n2 /\
          (forall X, s2.(vars) X = s3.(vars) X) /\
          (forall q, n1 <> q -> s2.(mem) q = s3.(mem) q)
  | KAsgnMemR n1 =>
      fun n2 s1 tr s2 =>
        s1.(mem) n1 <> None /\
        s2.(mem) n1 = Some n2 /\
        (forall X, s1.(vars) X = s2.(vars) X) /\
        (forall q, n1 <> q -> s1.(mem) q = s2.(mem) q) /\ tr=nil
	| KWriteInt =>
		fun n1 s1 tr s2=>
			s1=s2 /\ tr = (EV_WriteInt n1)::nil
	| KWriteChar =>
		fun n1 s1 tr s2=>
			s1=s2 /\ tr = (EV_WriteChar n1)::nil
  end.
  

Fixpoint cl_eval (cl: com_loc): prog_state -> list event->prog_state -> Prop :=
  match cl with
  | CL_Finished => Rels.id
  | CL_FocusedCom c => (ceval c)
  | CL_ECont el k => fun s1 tr s3 => exists n tr1 s2 tr2, el_eval el n s1 tr1 s2  /\ eck_eval k n s2 tr2 s3 /\ tr1++tr2 =tr
  | CL_CCont cl0 k => (cl_eval cl0) ∘ (ck_eval k)
  end.
  

  
Lemma cstep_sound: forall s1  cl1 tr1 tr2 tr12 s2 s3 cl2,
  cstep (cl1,s1) tr1 (cl2,s2) ->
  cl_eval cl2 s2 tr2 s3 ->
  tr1++tr2=tr12 ->
  cl_eval cl1 s1 tr12 s3.
Proof.
  intros. revert H1 H0. revert tr12 tr2 s3.
	induction_step2 H.
  + simpl in *; intros. unfold asgn_var_denote.  unfold asgn_var_action_denote. rel_unfold. simpl in *. intros.
  destruct H0 as[ n [tr1 [s2 [tr3 ?]]]]. exists n. exists  s2. exists  tr12,nil.  repeat split;try tauto.
  apply app_nil_r.  destruct H as [? [? ?]]. destruct H0 as [? [? [?]]]. subst tr3. rewrite app_nil_r in H2.
  subst tr12 tr2. tauto. 
  + simpl in *; intros. revert H3. rel_unfold. intros. destruct H3. subst tr2 tr12 s3. exists n,nil,s1,nil. tauto.
  + simpl in *; intros. unfold asgn_deref_denote, asgn_deref_action_denote. rel_unfold. simpl.
  destruct H0 as[ n [tr2a3 [s2 [tr2b3 ?]]]]. 
  destruct H as [? [?  ]]. destruct H0 as [n2 [? [? [? [? ?]]]]].
  exists n. exists n2. exists s2, tr2a3. exists tr2b3. repeat split; try tauto. subst tr2;auto.
  exists x. exists tr2b3,nil. repeat split;try tauto. apply app_nil_r.
  + simpl in *; intros.  destruct H0 as[ n [tr2a3 [s2 [tr2b3 ?]]]]. 
  destruct H as [? [?  ]]. destruct H0 as [n2 [? [? [?]]]]. subst tr2b3. rewrite app_nil_r in H2. subst tr2a3 tr12.
  exists n1,nil, s,tr2. repeat split;try tauto;auto. exists n. repeat split;try tauto;auto.
  exists s2. tauto.
  + simpl in *; intros. revert_component H4. rel_unfold. intros. destruct H4. subst tr2 tr12 s3. exists n2,nil,s1,nil.
  	repeat split;try tauto;auto.

  + simpl in *; intros. revert_component H0. rel_unfold. intros. destruct H0 as [s2 [tra1 [tra2]]]. 
  unfold seq_denote. rel_unfold. exists s2,tra1,tra2. congruence.
  + simpl in *; intros. rel_unfold. exists s,nil,tr2. subst tr2. rewrite app_nil_l. tauto. 
  + simpl in *; intros. unfold if_denote. rel_unfold. destruct H0 as [? [? [? [? [? [?]]]]]].
  destruct H0 as [[? ?]|[? ?]].
    - left.
      exists x1; simpl; unfold test1.
      exists x0,x2. subst tr12.   	repeat split;try tauto;auto.
      exists x.   	repeat split;try tauto;auto.
    - right.
      exists x1; simpl; unfold test0.
      exists x0,x2. subst tr12.   	repeat split;try tauto;auto.
      subst x.   	repeat split;try tauto;auto.
  + simpl in *; intros. subst tr2. simpl in *. exists n,nil,s,tr12.  	repeat split;try tauto;auto.
  + simpl in *; intros. subst tr2. simpl in *. exists n,nil,s,tr12.  	repeat split;try tauto;auto.
  + simpl in *; intros. revert_component H0. rel_unfold. intros. destruct H0 as [n [tr1 [s2 [tr3]]]].
      (*Stopped here to prove while_denote_is_fix*) 
    destruct H as [? [? ]].    
    apply (while_denote_is_fix e c).
(*     destruct H as [? [? | ?] ]. *)
 		destruct H0 as [[? ?] |? ].
 		subst tr12.
    - left. rel_unfold.
      unfold test1.
      destruct H3 as [s2_3 [ tr2a3 [tr2b3 [? [? ?]]] ]].
      exists s2. exists tr1,tr3. split;auto. split; [exists n;tauto| exists s2_3,tr2a3,tr2b3;tauto].
    - right.
    unfold test0. destruct H0 as[? [? ?]]. subst tr3 tr12 s3. rewrite app_nil_r in H2. subst.
    tauto.
  + simpl in *; intros. revert_component H0. rel_unfold. intros. simpl in *.
  	destruct H0 as [s1 [tr1 [tr3 ]]]. destruct H0 as [? [? ?]].
  	exists n, nil. exists s, tr2. subst. repeat split;try tauto;try auto.
  	left. split;auto. exists s1,tr1,tr3. tauto.
  + simpl in *; intros.  revert_component H0. rel_unfold. intros. simpl in *. simpl in *. destruct H0.

  	 exists n,nil. exists s.    exists tr2. subst tr12. split. tauto. split;[ | apply app_nil_l].
  	 right;tauto.

  +  intros.  rewrite app_nil_l in H1.  subst tr12.
  		revert H0. simpl. rel_unfold. intros.
  		exists s,nil,tr2. repeat split;try tauto.
  		apply (while_denote_is_fix e c). rel_unfold. 
  		destruct H0 as [? [? [ ? [? [? ?] ]]]].
      destruct H0 as [?]. destruct H0 as [?|? ].
      - unfold test1. left. exists x1,x0,x2. split;auto. split. destruct H0 as [? [? [? [? ?]]]]. exists x. tauto. tauto.
      - unfold test0. right. destruct H0 as [? [? ?]]. subst. rewrite app_nil_r. auto.
      
   + intros. rewrite app_nil_l in H1. subst tr12. simpl in *. unfold write_int_denote. unfold write_int_denote_aux.
   rel_unfold. destruct H0 as [? [? [? [? ?]]]]. destruct H as [? [[? ?] ?]]. subst. exists x,s3,x0,(EV_WriteInt x :: nil).
   repeat split;auto.
   
   + simpl in *. rel_unfold. intros. destruct H0. subst. exists n,nil,s3,(EV_WriteInt n :: nil). tauto.
   + intros. rewrite app_nil_l in H1. subst tr12. simpl in *. unfold write_char_denote. unfold write_char_denote_aux.
   rel_unfold. destruct H0 as [? [? [? [? ?]]]]. destruct H as [? [[? ?] ?]]. subst. exists x,s3,x0,(EV_WriteChar x :: nil).
   repeat split;auto.
   + simpl in *. rel_unfold. intros. destruct H0. subst. exists n,nil,s3,(EV_WriteChar n :: nil). tauto.
  + simpl in *. intros.   destruct H0 as [? [? [? [? [? [? ?]]]]]].
  remember (tr++x0) as trx0 eqn: Hhelp. symmetry in Hhelp.
  epose proof estep_sound _ _ _ _ _ _ _ _ _ H H0 Hhelp. exists x. exists trx0. exists x1. exists x2.
  repeat split;auto. subst trx0. rewrite <- Coq.Lists.List.app_assoc. congruence.
  + simpl in *. rel_unfold. intros. 
    destruct H0 as [s' [? [? [?  [? ?] ] ]]]. specialize (IHcstep s2 cl2 s1 cl1).
  			assert ( (cl1, s1) = (cl1, s1)). auto. assert ( (cl2, s2) = (cl2, s2)). auto. 
  			specialize (IHcstep H4 H5). clear H4 H5.
  			remember (tr++x) as tr01 eqn:Htr.
  			assert(tr01++x0=tr12). { rewrite Htr. rewrite <- ((Coq.Lists.List.app_assoc)).    congruence. }
  			
  			specialize (IHcstep tr01 x  s'). symmetry in Htr. specialize (IHcstep Htr H2).
  			exists s' ,tr01,x0.  tauto.
Qed.









