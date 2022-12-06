Require Import Coq.ZArith.ZArith.
Require Import compcert.lib.Integers.
Require Import WhileDB.SetsDomain.
Require Import WhileDB.Lang.
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

Inductive cstep:
  com_loc * prog_state -> list event -> com_loc * prog_state -> Prop :=
. Goal False. admit. Abort. (* 请删去这一行并自行补充定义，必要时可以添加辅助定义 *)
