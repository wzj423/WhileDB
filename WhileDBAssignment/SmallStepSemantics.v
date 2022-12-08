Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import compcert.lib.Integers.
Require Import WhileDB.SetsDomain.
Require Import WhileDB.RelDomain.
Require Import WhileDB.RelDomainAuxProofs.
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
      (EL_FocusedExpr EReadInt, s)
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
