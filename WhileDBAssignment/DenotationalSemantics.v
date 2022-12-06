Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import compcert.lib.Integers.
Require Import WhileDB.SetsDomain.
Require Import WhileDB.RelDomain.
Require Import WhileDB.BWFix.
Require Import WhileDB.Lang.
Local Open Scope list.
Local Open Scope bool.
Local Open Scope Z.
Local Open Scope sets.

(** 表达式的指称是：int64 -> prog_state -> list event -> prog_state -> Prop，表
    示返回值、起始状态、事件列表（时间序）、终止状态之间的四元关系。 *)

Definition const_denote
           (z: Z)
           (n: int64)
           (s1: prog_state)
           (tr: list event)
           (s2: prog_state): Prop :=
  n = Int64.repr z /\
  z <= Int64.max_signed /\
  z >= Int64.min_signed /\
  tr = nil /\
  s1 = s2.

Definition var_denote
           (X: var_name)
           (n: int64)
           (s1: prog_state)
           (tr: list event)
           (s2: prog_state): Prop :=
  n = s1.(vars) X /\
  tr = nil /\
  s1 = s2.

Definition arith_denote1
             (Zfun: Z -> Z -> Z)
             (int64fun: int64 -> int64 -> int64)
             (D1 D2: int64 -> prog_state -> list event -> prog_state -> Prop)
             (n: int64)
             (s1: prog_state)
             (tr: list event)
             (s2: prog_state): Prop :=
  exists n1 n2,
    ((D1 n1) ∘ (D2 n2)) s1 tr s2 /\
    arith_compute1 Zfun int64fun n1 n2 n.

Definition arith_denote2
             (int64fun: int64 -> int64 -> int64)
             (D1 D2: int64 -> prog_state -> list event -> prog_state -> Prop)
             (n: int64)
             (s1: prog_state)
             (tr: list event)
             (s2: prog_state): Prop :=
  exists n1 n2,
    ((D1 n1) ∘ (D2 n2)) s1 tr s2 /\
    arith_compute2 int64fun n1 n2 n.

Definition cmp_denote
             (c: comparison)
             (D1 D2: int64 -> prog_state -> list event -> prog_state -> Prop)
             (n: int64)
             (s1: prog_state)
             (tr: list event)
             (s2: prog_state): Prop :=
  exists n1 n2,
    ((D1 n1) ∘ (D2 n2)) s1 tr s2 /\
    cmp_compute c n1 n2 n.

(** 注：上面 ∘ 表示三元关系的连接。可以用_[rel_unfold]_指令展开。*)

Goal forall (R1 R2: prog_state -> list event -> prog_state -> Prop)
            (s1: prog_state) (l: list event) (s2: prog_state),
  (R1 ∘ R2) s1 l s2 /\ True -> True.
Proof.
  intros R1 R2 s1 l s2.
  rel_unfold.
  intros [? ?].
  auto.
Qed.
(*Abort.*)

Definition and_denote
             (D1 D2: int64 -> prog_state -> list event -> prog_state -> Prop)
             (n: int64)
             (s1: prog_state)
             (tr: list event)
             (s2: prog_state): Prop
. Admitted. (* 请删去这一行并自行补充定义，必要时可以添加辅助定义 *)

Definition or_denote
             (D1 D2: int64 -> prog_state -> list event -> prog_state -> Prop)
             (n: int64)
             (s1: prog_state)
             (tr: list event)
             (s2: prog_state): Prop
. Admitted. (* 请删去这一行并自行补充定义，必要时可以添加辅助定义 *)

Definition binop_denote
             (op: binop)
             (D1 D2: int64 -> prog_state -> list event -> prog_state -> Prop):
  int64 -> prog_state -> list event -> prog_state -> Prop :=
  match op with
  | OOr => or_denote D1 D2
  | OAnd => and_denote D1 D2
  | OLt => cmp_denote Clt D1 D2
  | OLe => cmp_denote Cle D1 D2
  | OGt => cmp_denote Cgt D1 D2
  | OGe => cmp_denote Cge D1 D2
  | OEq => cmp_denote Ceq D1 D2
  | ONe => cmp_denote Cne D1 D2
  | OPlus => arith_denote1 Z.add Int64.add D1 D2
  | OMinus => arith_denote1 Z.sub Int64.sub D1 D2
  | OMul => arith_denote1 Z.mul Int64.mul D1 D2
  | ODiv => arith_denote2 Int64.divs D1 D2
  | OMod => arith_denote2 Int64.mods D1 D2
  end.

Definition neg_denote
             (D: int64 -> prog_state -> list event -> prog_state -> Prop)
             (n: int64)
             (s1: prog_state)
             (tr: list event)
             (s2: prog_state): Prop :=
  exists n0,
    D n0 s1 tr s2 /\
    n = Int64.neg n0 /\
    Int64.signed n0 <> Int64.min_signed.

Definition not_denote
             (D: int64 -> prog_state -> list event -> prog_state -> Prop)
             (n: int64)
             (s1: prog_state)
             (tr: list event)
             (s2: prog_state): Prop :=
  exists n0,
    D n0 s1 tr s2 /\
    (Int64.signed n0 <> 0 /\
     n = Int64.repr 0 \/
     n0 = Int64.repr 0 /\
     n = Int64.repr 1).

Definition unop_denote
             (op: unop)
             (D: int64 -> prog_state -> list event -> prog_state -> Prop):
  int64 -> prog_state -> list event -> prog_state -> Prop :=
  match op with
  | ONeg => neg_denote D
  | ONot => not_denote D
  end.

Definition deref_denote
             (D: int64 -> prog_state -> list event -> prog_state -> Prop)
             (n: int64)
             (s1: prog_state)
             (tr: list event)
             (s2: prog_state): Prop :=
  exists n0, D n0 s1 tr s2 /\ s2.(mem) n0 = Some n.

Definition malloc_denote
             (D: int64 -> prog_state -> list event -> prog_state -> Prop)
             (n: int64)
             (s1: prog_state)
             (tr: list event)
             (s2: prog_state): Prop :=
  exists n0, ((D n0) ∘ (malloc_action n0 n)) s1 tr s2.

Definition read_int_denote
             (n: int64)
             (s1: prog_state)
             (tr: list event)
             (s2: prog_state): Prop :=
  tr = EV_ReadInt n :: nil /\ s1 = s2.

Definition read_char_denote
             (n: int64)
             (s1: prog_state)
             (tr: list event)
             (s2: prog_state): Prop :=
  tr = EV_ReadChar n :: nil /\ s1 = s2.

Fixpoint eeval (e : expr):
  int64 -> prog_state -> list event -> prog_state -> Prop :=
  match e with
  | ENum n => const_denote n
  | EVar X => var_denote X
  | EBinop op e1 e2 => binop_denote op (eeval e1) (eeval e2)
  | EUnop op e0 => unop_denote op (eeval e0)
  | EDeref e0 => deref_denote (eeval e0)
  | EMalloc e0 => malloc_denote (eeval e0)
  | EReadInt => read_int_denote
  | EReadChar => read_char_denote
  end.

(** 表达式的指称是：prog_state -> list event -> prog_state -> Prop，表示起始状
    态、事件列表（时间序）、终止状态之间的三元关系。 *)

Definition asgn_var_action_denote
             (X: var_name)
             (n: int64)
             (s1: prog_state)
             (tr: list event)
             (s2: prog_state): Prop :=
  tr = nil /\
  s2.(vars) X = n /\
  (forall Y, X <> Y -> s1.(vars) Y = s2.(vars) Y) /\
  (forall p, s1.(mem) p = s2.(mem) p).

Definition asgn_var_denote
             (X: var_name)
             (D: int64 -> prog_state -> list event -> prog_state -> Prop)
             (s1: prog_state)
             (tr: list event)
             (s2: prog_state): Prop :=
  exists n,
    ((D n) ∘ (asgn_var_action_denote X n)) s1 tr s2.

Definition asgn_deref_action_denote
             (n1 n2: int64)
             (s1: prog_state)
             (tr: list event)
             (s2: prog_state): Prop :=
  tr = nil /\
  s1.(mem) n1 <> None /\
  s2.(mem) n1 = Some n2 /\
  (forall X, s1.(vars) X = s2.(vars) X) /\
  (forall q, n1 <> q -> s1.(mem) q = s2.(mem) q).

Definition asgn_deref_denote
             (D1 D2: int64 -> prog_state -> list event -> prog_state -> Prop)
             (s1: prog_state)
             (tr: list event)
             (s2: prog_state): Prop :=
  exists n1 n2,
    ((D1 n1) ∘ (D2 n2) ∘ (asgn_deref_action_denote n1 n2)) s1 tr s2.

Definition seq_denote (D1 D2: prog_state -> list event -> prog_state -> Prop):
  prog_state -> list event -> prog_state -> Prop :=
  D1 ∘ D2.

Definition test0
             (D: int64 -> prog_state -> list event -> prog_state -> Prop)
             (s1: prog_state)
             (tr: list event)
             (s2: prog_state): Prop :=
  D (Int64.repr 0) s1 tr s2.

Definition test1
             (D: int64 -> prog_state -> list event -> prog_state -> Prop)
             (s1: prog_state)
             (tr: list event)
             (s2: prog_state): Prop :=
  exists n, D n s1 tr s2 /\ Int64.signed n <> 0.

Definition if_denote
             (D0: int64 -> prog_state -> list event -> prog_state -> Prop)
             (D1 D2: prog_state -> list event -> prog_state -> Prop):
  prog_state -> list event -> prog_state -> Prop :=
  (test1 D0 ∘ D1) ∪ (test0 D0 ∘ D2).

Definition while_denote
             (D0: int64 -> prog_state -> list event -> prog_state -> Prop)
             (D: prog_state -> list event -> prog_state -> Prop):
  prog_state -> list event -> prog_state -> Prop
. Admitted. (* 请删去这一行并自行补充定义，必要时可以添加辅助定义 *)

Definition write_int_denote
             (D0: int64 -> prog_state -> list event -> prog_state -> Prop):
  prog_state -> list event -> prog_state -> Prop
. Admitted. (* 请删去这一行并自行补充定义，必要时可以添加辅助定义 *)

Definition write_char_denote
             (D0: int64 -> prog_state -> list event -> prog_state -> Prop):
  prog_state -> list event -> prog_state -> Prop
. Admitted. (* 请删去这一行并自行补充定义，必要时可以添加辅助定义 *)

Fixpoint ceval (c: com): prog_state -> list event -> prog_state -> Prop :=
  match c with
  | CAss e1 e2 =>
    match e1 with
    | EVar X => asgn_var_denote X (eeval e2)
    | EDeref e0 => asgn_deref_denote (eeval e0) (eeval e2)
    | _ => ∅
    end
  | CSeq c1 c2 => seq_denote (ceval c1) (ceval c2)
  | CIf e c1 c2 => if_denote (eeval e) (ceval c1) (ceval c2)
  | CWhile e c0 => while_denote (eeval e) (ceval c0)
  | CWriteInt e => write_int_denote (eeval e)
  | CWriteChar e => write_char_denote (eeval e)
  end.

