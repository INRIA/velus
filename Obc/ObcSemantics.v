Require Import Coq.FSets.FMapPositive.
Require Import List.

Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.RMemory.
Require Import Velus.Obc.ObcSyntax.

(** * Obc semantics *)

(**

  The semantics of Obc relies on a tree-structure [memory], based
  on [Velus.RMemory], to store object instances and a [stack] to keep
  track of local variables during method calls.

 *)

Module Type OBCSEMANTICS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Syn   : OBCSYNTAX Ids Op OpAux).

  (* TODO: rename types to env/menv and the instances to ve/me *)
  Definition heap : Type := memory val.
  Definition stack : Type := PM.t val.

  (* TODO: rename to vempty/mempty *)
  Definition sempty: stack := PM.empty val.
  Definition hempty: heap := empty_memory _.

  Hint Unfold sempty.

  Inductive exp_eval heap stack: exp -> val -> Prop :=
  | evar:
      forall x v ty,
        PM.find x stack = Some v ->
        exp_eval heap stack (Var x ty) v
  | estate:
      forall x v ty,
        mfind_mem x heap = Some v ->
        exp_eval heap stack (State x ty) v
  | econst:
      forall c v,
        v = sem_const c ->
        exp_eval heap stack (Const c) v
  | eunop :
      forall op e c v ty,
        exp_eval heap stack e c ->
        sem_unop op c (typeof e) = Some v ->
        exp_eval heap stack (Unop op e ty) v
  | ebinop :
      forall op e1 e2 c1 c2 v ty,
        exp_eval heap stack e1 c1 ->
        exp_eval heap stack e2 c2 ->
        sem_binop op c1 (typeof e1) c2 (typeof e2) = Some v ->
        exp_eval heap stack (Binop op e1 e2 ty) v.

  (* =stmt_eval= *)
  Inductive stmt_eval :
    program -> heap -> stack -> stmt -> heap * stack -> Prop :=
  | Iassign: forall prog menv env x e v env',
      exp_eval menv env e v ->
      PM.add x v env = env' ->
      stmt_eval prog menv env (Assign x e) (menv, env')
  | Iassignst:
    forall prog menv env x e v menv',
      exp_eval menv env e v ->
      madd_mem x v menv = menv' ->
      stmt_eval prog menv env (AssignSt x e) (menv', env)
  | Icall: forall prog menv env es vs clsid o f ys menv' env' omenv omenv' rvs,
      omenv = match mfind_inst o menv with None => hempty | Some om => om end ->
      Forall2 (exp_eval menv env) es vs ->
      stmt_call_eval prog omenv clsid f vs omenv' rvs ->
      madd_obj o omenv' menv = menv' ->
      adds ys rvs env = env' ->
      stmt_eval prog menv env (Call ys clsid o f es) (menv', env')
  | Icomp:
      forall prog menv env a1 a2 env1 menv1 env2 menv2,
        stmt_eval prog menv env a1 (menv1, env1) ->
        stmt_eval prog menv1 env1 a2 (menv2, env2) ->
        stmt_eval prog menv env (Comp a1 a2) (menv2, env2)
  | Iifte:
      forall prog menv env cond v b ifTrue ifFalse env' menv',
        exp_eval menv env cond v ->
        val_to_bool v = Some b ->
        stmt_eval prog menv env (if b then ifTrue else ifFalse) (menv', env') ->
        stmt_eval prog menv env (Ifte cond ifTrue ifFalse) (menv', env')
  | Iskip:
      forall prog menv env,
        stmt_eval prog menv env Skip (menv, env)

  with stmt_call_eval :
     program -> heap -> ident -> ident -> list val -> heap -> list val -> Prop :=
  | Iecall:
      forall prog menv clsid f fm vs prog' menv' env' cls rvs,
        find_class clsid prog = Some(cls, prog') ->
        find_method f cls.(c_methods) = Some fm ->
        stmt_eval prog' menv (adds (map fst fm.(m_in)) vs sempty)
                  fm.(m_body) (menv', env') ->
        Forall2 (fun x v => PM.find x env' = Some v) (map fst fm.(m_out)) rvs ->
        stmt_call_eval prog menv clsid f vs menv' rvs.

  Scheme stmt_eval_ind_2 := Minimality for stmt_eval Sort Prop
  with stmt_call_eval_ind_2 := Minimality for stmt_call_eval Sort Prop.
  Combined Scheme stmt_eval_call_ind from stmt_eval_ind_2, stmt_call_eval_ind_2.


  (** ** Determinism of semantics *)

  Lemma exp_eval_det:
    forall menv env e v1 v2,
      exp_eval menv env e v1 ->
      exp_eval menv env e v2 ->
      v1 = v2.
  Proof.
    induction e (* using exp_ind2 *);
    intros v1 v2 H1 H2;
    inversion H1 as [xa va tya Hv1|xa va tya Hv1|xa va Hv1
                     |opa ea ca va tya IHa Hv1
                     |opa e1a e2a c1a c2a va tya IH1a IH2a Hv1];
    inversion H2 as [xb vb tyb Hv2|xb vb tyb Hv2|xb vb Hv2
                     |opb eb cb vb tyb IHb Hv2
                     |opb e1b e2b c1b c2b vb tyb IH1b IH2b Hv2];
    try (rewrite Hv1 in Hv2; (injection Hv2; trivial) || apply Hv2); subst.
    - reflexivity.
    - pose proof (IHe ca cb IHa IHb); subst.
      now rewrite Hv1 in Hv2; injection Hv2.
    - pose proof (IHe1 c1a c1b IH1a IH1b); pose proof (IHe2 c2a c2b IH2a IH2b); subst.
      now rewrite Hv1 in Hv2; injection Hv2.
  Qed.

  Lemma stmt_eval_fold_left_shift:
    forall A prog f (xs:list A) iacc menv env menv' env',
      stmt_eval prog menv env
                (List.fold_left (fun i x => Comp (f x) i) xs iacc)
                (menv', env')
      <->
      exists menv'' env'',
        stmt_eval prog menv env
                  (List.fold_left (fun i x => Comp (f x) i) xs Skip)
                  (menv'', env'')
        /\
        stmt_eval prog menv'' env'' iacc (menv', env').
  Proof.
    Hint Constructors stmt_eval.
    induction xs.
    - split; [ now eauto | ].
      intro H; do 2 destruct H.
      destruct H as [H0 H1].
      inversion_clear H0; apply H1.
    - intros.
      split.
      + intro H0.
        apply IHxs in H0.
        destruct H0 as [menv'' H0].
        destruct H0 as [env'' H0].
        destruct H0 as [H0 H1].
        inversion_clear H1.
        exists menv1. exists env1.
        split; try apply IHxs; eauto.
      + intros;
        repeat progress
               match goal with
               | H:exists _, _ |- _ => destruct H
               | H:_ /\ _ |- _ => destruct H
               | H:stmt_eval _ _ _ (Comp _ Skip) _ |- _ => inversion_clear H
               | H:stmt_eval _ _ _ Skip _ |- _ => inversion H; subst
               | H:stmt_eval _ _ _ (List.fold_left _ _ _) _ |- _ => apply IHxs in H
               | _ => eauto
               end.
        apply IHxs; eauto.
  Qed.

  (** ** Other properties *)

  (** If we add irrelevent values to [env], evaluation does not change. *)
  Lemma exp_eval_extend_env : forall mem env x v' e v,
      ~Is_free_in_exp x e -> exp_eval mem env e v -> exp_eval mem (PM.add x v' env) e v.
  Proof.
    intros mem env x v' e.
    induction e (* using exp_ind2 *); intros v1 Hfree Heval.
    - inv Heval. constructor. not_free. now rewrite PM.gso.
    - inv Heval. now constructor.
    - inv Heval. now constructor.
    - inv Heval. constructor 4 with c; trivial.
      not_free.
      now apply IHe.
    - inv Heval. constructor 5 with (c1 := c1) (c2 := c2); trivial; not_free.
      + now apply IHe1.
      + now apply IHe2.
  Qed.

  (** If we add irrelevent values to [mem], evaluation does not change. *)
  Lemma exp_eval_extend_mem : forall mem env x v' e v,
      ~Is_free_in_exp x e -> exp_eval mem env e v -> exp_eval (madd_mem x v' mem) env e v.
  Proof.
    intros mem env x v' e.
    induction e (* using exp_ind2 *); intros v1 Hfree Heval.
    - inversion_clear Heval. now constructor.
    - inversion_clear Heval. constructor. not_free. now rewrite mfind_mem_gso.
    - inversion_clear Heval. now constructor.
    - inversion_clear Heval. constructor 4 with c; trivial.
      not_free.
      now apply IHe.
    - inv Heval. constructor 5 with (c1 := c1) (c2 := c2); trivial; not_free.
      + now apply IHe1.
      + now apply IHe2.
  Qed.

  (** If we add objects to [mem], evaluation does not change. *)
  Lemma exp_eval_extend_mem_by_obj : forall mem env f obj e v,
      exp_eval mem env e v -> exp_eval (madd_obj f obj mem) env e v.
  Proof.
    intros mem env f v' e.
    induction e (* using exp_ind2 *); intros v1 Heval.
    - inversion_clear Heval. now constructor.
    - inversion_clear Heval. constructor. now rewrite mfind_mem_add_inst.
    - inversion_clear Heval. now constructor.
    - inversion_clear Heval. constructor 4 with c; trivial.
      now apply IHe.
    - inv Heval. constructor 5 with (c1 := c1) (c2 := c2); trivial.
      + now apply IHe1.
      + now apply IHe2.
  Qed.

  Lemma mfind_inst_empty:
    forall o, mfind_inst o hempty = None.
  Proof.
    intro o. unfold mfind_inst.
    apply PM.gempty.
  Qed.

End OBCSEMANTICS.

Module ObcSemanticsFun
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Syn   : OBCSYNTAX Ids Op OpAux) <: OBCSEMANTICS Ids Op OpAux Syn.
  Include OBCSEMANTICS Ids Op OpAux Syn.
End ObcSemanticsFun.
