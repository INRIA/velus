Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Coq.Sorting.Permutation.

Require Import Coq.FSets.FMapPositive.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.NLustre.NLSyntax.
Require Import Streams.

Module Type NLSEMANTICSCOMMON
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Clks  : CLOCKS    Ids)
       (Import Syn   : NLSYNTAX  Ids Op Clks).

  Definition idents := List.map (@fst ident (type * clock)).

  Infix ":::" := Cons (at level 60, right associativity) : stream_scope.
  Infix "≡" := EqSt (at level 70, no associativity) : stream_scope.
  Delimit Scope stream_scope with Stream.
  Open Scope stream_scope.

  Definition history := PM.t (Stream value).

  CoFixpoint const (c: const) (b: Stream bool): Stream value :=
    match b with
    | true  ::: b' => present (sem_const c) ::: const c b'
    | false ::: b' => absent ::: const c b'
    end.

  Inductive sem_var: history -> ident -> Stream value -> Prop :=
    sem_var_intro:
      forall H x xs xs',
        PM.MapsTo x xs' H ->
        xs ≡ xs' ->
        sem_var H x xs.

   CoInductive when (k: bool): Stream value -> Stream value -> Stream value -> Prop :=
  | WhenA:
      forall xs cs rs,
        when k xs cs rs ->
        when k (absent ::: xs) (absent ::: cs) (absent ::: rs)
  | WhenPA:
      forall x c xs cs rs,
        when k xs cs rs ->
        val_to_bool c = Some (negb k) ->
        when k (present x ::: xs) (present c ::: cs) (absent ::: rs)
  | WhenPP:
      forall x c xs cs rs,
        when k xs cs rs ->
        val_to_bool c = Some k ->
        when k (present x ::: xs) (present c ::: cs) (present x ::: rs).

  CoInductive lift1 (op: unop) (ty: type): Stream value -> Stream value -> Prop :=
  | Lift1A:
      forall xs rs,
        lift1 op ty xs rs ->
        lift1 op ty (absent ::: xs) (absent ::: rs)
  | Lift1P:
      forall x r xs rs,
        sem_unop op x ty = Some r ->
        lift1 op ty xs rs ->
        lift1 op ty (present x ::: xs) (present r ::: rs).

  CoInductive lift2 (op: binop) (ty1 ty2: type): Stream value -> Stream value -> Stream value -> Prop :=
  | Lift2A:
      forall xs ys rs,
        lift2 op ty1 ty2 xs ys rs ->
        lift2 op ty1 ty2 (absent ::: xs) (absent ::: ys) (absent ::: rs)
  | Lift2P:
      forall x y r xs ys rs,
        sem_binop op x ty1 y ty2 = Some r ->
        lift2 op ty1 ty2 xs ys rs ->
        lift2 op ty1 ty2 (present x ::: xs) (present y ::: ys) (present r ::: rs).

  CoInductive merge
    : Stream value -> Stream value -> Stream value -> Stream value -> Prop :=
  | MergeA:
      forall xs ts fs rs,
        merge xs ts fs rs ->
        merge (absent ::: xs) (absent ::: ts) (absent ::: fs) (absent ::: rs)
  | MergeT:
      forall t xs ts fs rs,
        merge xs ts fs rs ->
        merge (present true_val ::: xs)
              (present t ::: ts) (absent ::: fs) (present t ::: rs)
  | MergeF:
      forall f xs ts fs rs,
        merge xs ts fs rs ->
        merge (present false_val ::: xs)
              (absent ::: ts) (present f ::: fs) (present f ::: rs).

  CoInductive ite
    : Stream value -> Stream value -> Stream value -> Stream value -> Prop :=
  | IteA:
      forall s ts fs rs,
        ite s ts fs rs ->
        ite (absent ::: s) (absent ::: ts) (absent ::: fs) (absent ::: rs)
  | IteT:
      forall t f s ts fs rs,
        ite s ts fs rs ->
        ite (present true_val ::: s)
              (present t ::: ts) (present f ::: fs) (present t ::: rs)
  | IteF:
      forall t f s ts fs rs,
        ite s ts fs rs ->
        ite (present false_val ::: s)
              (present t ::: ts) (present f ::: fs) (present f ::: rs).

  Inductive sem_lexp: history -> Stream bool -> lexp -> Stream value -> Prop :=
  | Sconst:
      forall H b c,
        sem_lexp H b (Econst c) (const c b)
  | Svar:
      forall H b x ty xs,
        sem_var H x xs ->
        sem_lexp H b (Evar x ty) xs
  | Swhen:
      forall H b e x k es xs os,
        sem_lexp H b e es ->
        sem_var H x xs ->
        when k es xs os ->
        sem_lexp H b (Ewhen e x k) os
  | Sunop:
      forall H b op e ty es os,
        sem_lexp H b e es ->
        lift1 op (typeof e) es os ->
        sem_lexp H b (Eunop op e ty) os
  | Sbinop:
      forall H b op e1 e2 ty es1 es2 os,
        sem_lexp H b e1 es1 ->
        sem_lexp H b e2 es2 ->
        lift2 op (typeof e1) (typeof e2) es1 es2 os ->
        sem_lexp H b (Ebinop op e1 e2 ty) os.

  Inductive sem_cexp: history -> Stream bool -> cexp -> Stream value -> Prop :=
  | Smerge:
      forall H b x t f xs ts fs os,
        sem_var H x xs ->
        sem_cexp H b t ts ->
        sem_cexp H b f fs ->
        merge xs ts fs os ->
        sem_cexp H b (Emerge x t f) os
  | Site:
      forall H b e t f es ts fs os,
        sem_lexp H b e es ->
        sem_cexp H b t ts ->
        sem_cexp H b f fs ->
        ite es ts fs os ->
        sem_cexp H b (Eite e t f) os
  | Sexp:
      forall H b e es,
        sem_lexp H b e es ->
        sem_cexp H b (Eexp e) es.

  CoFixpoint clocks_of (ss: list (Stream value)) : Stream bool :=
    existsb (fun s => hd s <>b absent) ss ::: clocks_of (List.map (@tl value) ss).

  CoFixpoint reset_of : Stream value -> Stream bool :=
    map (fun x => match x with
               | present x => x ==b true_val
               | _ => false
               end).

End NLSEMANTICSCOMMON.
