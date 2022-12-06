Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import compcert.lib.Integers.
Local Open Scope Z.

Definition var_name: Type := string.

(** 程序状态 *)
Record prog_state: Type := {
  vars: var_name -> int64;
  mem: int64 -> option int64;
}.

(** 事件 *)
Inductive event: Type :=
  | EV_Malloc (arg: int64) (ret: int64)
  | EV_ReadInt (ret: int64)
  | EV_ReadChar (ret: int64)
  | EV_WriteInt (arg: int64)
  | EV_WriteChar (arg: int64).

(** 表达式 *)
Inductive binop : Type :=
  | OOr | OAnd
  | OLt | OLe | OGt | OGe | OEq | ONe
  | OPlus | OMinus | OMul | ODiv | OMod.

Inductive unop : Type :=
  | ONot | ONeg.

Inductive expr : Type :=
  | ENum (n: Z): expr
  | EVar (x: var_name): expr
  | EBinop (op: binop) (e1 e2: expr): expr
  | EUnop (op: unop) (e: expr): expr
  | EDeref (e: expr): expr
  | EMalloc (e: expr)
  | EReadInt
  | EReadChar.

(** 语句 *)
Inductive com : Type :=
  | CAss (e1 e2: expr): com
  | CSeq (c1 c2: com): com
  | CIf (e: expr) (c1 c2: com): com
  | CWhile (e: expr) (c: com): com
  | CWriteInt (e: expr)
  | CWriteChar (e: expr).

Definition arith_compute1
             (Zfun: Z -> Z -> Z)
             (int64fun: int64 -> int64 -> int64)
             (n1 n2 n: int64): Prop :=
    n = int64fun n1 n2 /\
    Zfun (Int64.signed n1) (Int64.signed n2)
      <= Int64.max_signed /\
    Zfun (Int64.signed n1) (Int64.signed n2)
      >= Int64.min_signed.

Definition arith_compute2
             (int64fun: int64 -> int64 -> int64)
             (n1 n2 n: int64): Prop :=
    n = int64fun n1 n2 /\
    Int64.signed n2 <> 0 /\
    (Int64.signed n1 <> Int64.min_signed \/
     Int64.signed n2 <> - 1).

Definition cmp_compute
             (c: comparison)
             (n1 n2 n: int64): Prop :=
    n = if Int64.cmp c n1 n2 then Int64.repr 1 else Int64.repr 0.

Definition malloc_action
             (n1 n2: int64)
             (s1: prog_state)
             (tr: list event)
             (s2: prog_state): Prop :=
  exists k: Z,
    k > 1 /\
    8 * (k - 1) < Int64.signed n1 <= 8 * k /\
    (8 | Int64.signed n2) /\
    Int64.signed n2 + 8 * k < Int64.max_signed /\
    tr = EV_Malloc n1 n2 :: nil /\
    (forall i,
      0 <= i < k ->
      s1.(mem) (Int64.repr (Int64.signed n2 + 8 * i)) = None /\
      s2.(mem) (Int64.repr (Int64.signed n2 + 8 * i)) <> None).

