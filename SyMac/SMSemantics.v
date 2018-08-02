Require Import List.
Import List.ListNotations.
Open Scope list_scope.

(* Require Import Coq.Sorting.Permutation. *)
(* Require Import Setoid. *)
(* Require Import Morphisms. *)
(* Require Import Coq.Arith.EqNat. *)

(* Require Import Coq.FSets.FMapPositive. *)
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.SyMac.SMSyntax.
(* Require Import Velus.NLustre.Ordered. *)
Require Import Velus.NLustre.Streams.


Module Type SMSEMANTICS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Clks  : CLOCKS    Ids)
       (Import Syn   : SMSYNTAX  Ids Op Clks)
       (* (Import Ord   : ORDERED   Ids Op Clks Syn) *)
.

  Definition History := PM.t (Stream value).

  Definition History_tl (H: History) : History := PM.map (@tl value) H.

  CoFixpoint const (c: const) (b: Stream bool): Stream value :=
    (if hd b then present (sem_const c) else absent) ::: const c (tl b).

  Inductive sem_var: History -> ident -> Stream value -> Prop :=
    sem_var_intro:
      forall H x xs xs',
        PM.MapsTo x xs' H ->
        xs ≡ xs' ->
        sem_var H x xs.

  Remark MapsTo_sem_var:
    forall H x xs,
      PM.MapsTo x xs H ->
      sem_var H x xs.
  Proof. econstructor; eauto; reflexivity. Qed.

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

  CoInductive lift2 (op: binop) (ty1 ty2: type)
    : Stream value -> Stream value -> Stream value -> Prop :=
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

  CoInductive sem_clock: History -> Stream bool -> clock -> Stream bool -> Prop :=
  | Sbase:
      forall H b b',
        b ≡ b' ->
        sem_clock H b Cbase b'
  | Son:
      forall H b bk bs ck x k xs c,
        sem_clock H b ck (true ::: bk) ->
        sem_var H x (present c ::: xs) ->
        val_to_bool c = Some k ->
        sem_clock (History_tl H) (tl b) (Con ck x k) bs ->
        sem_clock H b (Con ck x k) (true ::: bs)
  | Son_abs1:
      forall H b bk bs ck x k xs,
        sem_clock H b ck (false ::: bk) ->
        sem_var H x (absent ::: xs) ->
        sem_clock (History_tl H) (tl b) (Con ck x k) bs ->
        sem_clock H b (Con ck x k) (false ::: bs)
  | Son_abs2:
      forall H b bk bs ck x k c xs,
        sem_clock H b ck (true ::: bk) ->
        sem_var H x (present c ::: xs) ->
        val_to_bool c = Some k ->
        sem_clock (History_tl H) (tl b) (Con ck x (negb k)) bs ->
        sem_clock H b (Con ck x (negb k)) (false ::: bs).

  Inductive sem_lexp: History -> Stream bool -> lexp -> Stream value -> Prop :=
  | Sconst:
      forall H b c cs,
        cs ≡ const c b ->
        sem_lexp H b (Econst c) cs
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

  Inductive sem_cexp: History -> Stream bool -> cexp -> Stream value -> Prop :=
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

  CoInductive sem_avar: History -> Stream bool -> clock -> ident -> Stream value -> Prop :=
  | SVtick:
      forall H b ck x v vs bs,
        sem_var H x (present v ::: vs) ->
        sem_clock H b ck (true ::: bs) ->
        sem_avar (History_tl H) (tl b) ck x vs ->
        sem_avar H b ck x (present v ::: vs)
  | SVabs:
      forall H b ck x vs bs,
        sem_var H x (absent ::: vs) ->
        sem_clock H b ck (false ::: bs) ->
        sem_avar (History_tl H) (tl b) ck x vs ->
        sem_avar H b ck x (absent ::: vs).

  CoInductive sem_aexp {A} (sem: History -> Stream bool -> A -> Stream value -> Prop):
    History -> Stream bool -> clock -> A -> Stream value -> Prop :=
  | Stick:
      forall H b ck a e es bs,
        sem H b a (present e ::: es) ->
        sem_clock H b ck (true ::: bs) ->
        sem_aexp sem (History_tl H) (tl b) ck a es ->
        sem_aexp sem H b ck a (present e ::: es)
  | Sabs:
      forall H b ck a es bs,
        sem H b a (absent ::: es) ->
        sem_clock H b ck (false ::: bs) ->
        sem_aexp sem (History_tl H) (tl b) ck a es ->
        sem_aexp sem H b ck a (absent ::: es).

  Definition sem_laexp := sem_aexp sem_lexp.
  Definition sem_caexp := sem_aexp sem_cexp.

  CoInductive sem_laexps: History -> Stream bool -> clock -> list lexp -> list (Stream value) -> Prop :=
  | SLsTick:
      forall H b ck les ess bs,
        Forall2 (sem_lexp H b) les ess ->
        Forall (fun es => hd es <> absent) ess ->
        sem_clock H b ck (true ::: bs) ->
        sem_laexps (History_tl H) (tl b) ck les (List.map (@tl value) ess) ->
        sem_laexps H b ck les ess
  | SLsAbs:
      forall H b ck les ess bs,
        Forall2 (sem_lexp H b) les ess ->
        Forall (fun es => hd es = absent) ess ->
        sem_clock H b ck (false ::: bs) ->
        sem_laexps (History_tl H) (tl b) ck les (List.map (@tl value) ess) ->
        sem_laexps H b ck les ess.

  Lemma sem_laexps_cons:
     forall H b ck le les es ess,
        sem_laexps H b ck (le :: les) (es :: ess) ->
        sem_laexps H b ck les ess.
  Proof.
    cofix Cofix; intros ** Sem.
    inversion_clear Sem as [? ? ? ? ? ? F2 F1|? ? ? ? ? ? F2 F1]; inv F2; inv F1.
    - eleft; eauto.
    - eright; eauto.
  Qed.

  Section NodeSemantics.

    Variable G: global.

    Inductive sem_equation: History -> Stream bool -> equation -> Prop :=
    | SeqDef:
        forall H b x ck e es,
          sem_caexp H b ck e es ->
          sem_var H x es ->
          sem_equation H b (EqDef x ck e)
    | SeqApp:
        forall H b ys ck f es ess oss,
          sem_laexps H b ck es ess ->
          sem_node f ess oss ->
          Forall2 (sem_var H) ys oss ->
          sem_equation H b (EqApp ys ck f es None)
    | SeqReset:
        forall H b ys ck f es r ck_r rs ess oss,
          sem_laexps H b ck es ess ->
          sem_avar H b ck_r r rs ->
          sem_reset f (reset_of rs) ess oss ->
          Forall2 (sem_var H) ys oss ->
          sem_equation H b (EqApp ys ck f es (Some (r, ck_r)))
    | SeqFby:
        forall H b x ck c0 e es os,
          sem_laexp H b ck e es ->
          os = fby (sem_const c0) es ->
          sem_var H x os ->
          sem_equation H b (EqFby x ck c0 e)

    with
    sem_reset
    : ident -> Stream bool -> list (Stream value) -> list (Stream value) -> Prop :=
      SReset:
        forall f r xss yss,
          (forall k, sem_node f (List.map (mask_v k r) xss) (List.map (mask_v k r) yss)) ->
          sem_reset f r xss yss

    with
    sem_node: ident -> list (Stream value) -> list (Stream value) -> Prop :=
      SNode:
        forall H f n xss oss,
          find_node f G = Some n ->
          Forall2 (sem_var H) (idents n.(n_in)) xss ->
          Forall2 (sem_var H) (idents n.(n_out)) oss ->
          same_clock (xss ++ oss) ->
          Forall (sem_equation H (clocks_of xss)) n.(n_eqs) ->
          sem_node f xss oss.

  End NodeSemantics.

  Section SemInd.

    Variable G: global.

    Variable P_equation: History -> Stream bool -> equation -> Prop.
    Variable P_reset: ident -> Stream bool -> list (Stream value) -> list (Stream value) -> Prop.
    Variable P_node: ident -> list (Stream value) -> list (Stream value) -> Prop.

    Hypothesis EqDefCase:
      forall H b x ck e es,
        sem_caexp H b ck e es ->
        sem_var H x es ->
        P_equation H b (EqDef x ck e).

    Hypothesis EqAppCase:
      forall H b ys ck f es ess oss,
        sem_laexps H b ck es ess ->
        sem_node G f ess oss ->
        Forall2 (sem_var H) ys oss ->
        P_node f ess oss ->
        P_equation H b (EqApp ys ck f es None).

    Hypothesis EqResetCase:
      forall H b ys ck f es r ck_r rs ess oss,
        sem_laexps H b ck es ess ->
        sem_avar H b ck_r r rs ->
        sem_reset G f (reset_of rs) ess oss ->
        Forall2 (sem_var H) ys oss ->
        P_reset f (reset_of rs) ess oss ->
        P_equation H b (EqApp ys ck f es (Some (r, ck_r))).

    Hypothesis EqFbyCase:
      forall H b x ck c0 e es os,
        sem_laexp H b ck e es ->
        os = fby (sem_const c0) es ->
        sem_var H x os ->
        P_equation H b (EqFby x ck c0 e).

    Hypothesis ResetCase:
      forall f r xss yss,
        (forall k, sem_node G f (List.map (mask_v k r) xss) (List.map (mask_v k r) yss)
              /\ P_node f (List.map (mask_v k r) xss) (List.map (mask_v k r) yss)) ->
        P_reset f r xss yss.

    Hypothesis NodeCase:
      forall H f n xss oss,
        find_node f G = Some n ->
        Forall2 (sem_var H) (idents n.(n_in)) xss ->
        Forall2 (sem_var H) (idents n.(n_out)) oss ->
        same_clock (xss ++ oss) ->
        Forall (sem_equation G H (clocks_of xss)) n.(n_eqs) ->
        Forall (P_equation H (clocks_of xss)) n.(n_eqs) ->
        P_node f xss oss.

    Fixpoint sem_equation_mult
             (H: History) (b: Stream bool) (e: equation)
             (Sem: sem_equation G H b e) {struct Sem}
      : P_equation H b e
    with sem_reset_mult
           (f: ident) (r: Stream bool) (xss oss: list (Stream value))
           (Sem: sem_reset G f r xss oss) {struct Sem}
         : P_reset f r xss oss
    with sem_node_mult
           (f: ident) (xss oss: list (Stream value))
           (Sem: sem_node G f xss oss) {struct Sem}
         : P_node f xss oss.
    Proof.
      - destruct Sem; eauto.
      - destruct Sem as [???? Sem]; eauto.
      - destruct Sem; eauto.
        eapply NodeCase; eauto.
        induction H4; auto.
    Qed.

    Combined Scheme sem_equation_node_ind from
             sem_equation_mult, sem_node_mult, sem_reset_mult.

  End SemInd.

End SMSEMANTICSCOIND.
