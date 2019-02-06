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

  Definition menv := memory val.
  Definition venv := env val.

  Definition mempty: menv := empty_memory _.
  Definition vempty: venv := Env.empty val.

  Inductive exp_eval (me: menv) (ve: venv): exp -> val -> Prop :=
  | evar:
      forall x v ty,
        Env.find x ve = Some v ->
        exp_eval me ve (Var x ty) v
  | estate:
      forall x v ty,
        find_val x me = Some v ->
        exp_eval me ve (State x ty) v
  | econst:
      forall c v,
        v = sem_const c ->
        exp_eval me ve (Const c) v
  | eunop :
      forall op e c v ty,
        exp_eval me ve e c ->
        sem_unop op c (typeof e) = Some v ->
        exp_eval me ve (Unop op e ty) v
  | ebinop :
      forall op e1 e2 c1 c2 v ty,
        exp_eval me ve e1 c1 ->
        exp_eval me ve e2 c2 ->
        sem_binop op c1 (typeof e1) c2 (typeof e2) = Some v ->
        exp_eval me ve (Binop op e1 e2 ty) v.

  (* =stmt_eval= *)
  Inductive stmt_eval :
    program -> menv -> venv -> stmt -> menv * venv -> Prop :=
  | Iassign:
      forall prog me ve x e v ve',
        exp_eval me ve e v ->
        Env.add x v ve = ve' ->
        stmt_eval prog me ve (Assign x e) (me, ve')
  | Iassignst:
      forall prog me ve x e v me',
        exp_eval me ve e v ->
        add_val x v me = me' ->
        stmt_eval prog me ve (AssignSt x e) (me', ve)
  | Icall:
      forall prog me ve es vs clsid o f ys me' ve' ome ome' rvs,
        ome = match find_inst o me with None => mempty | Some om => om end ->
        Forall2 (exp_eval me ve) es vs ->
        stmt_call_eval prog ome clsid f vs ome' rvs ->
        add_inst o ome' me = me' ->
        Env.adds ys rvs ve = ve' ->
        stmt_eval prog me ve (Call ys clsid o f es) (me', ve')
  | Icomp:
      forall prog me ve a1 a2 ve1 me1 ve2 me2,
        stmt_eval prog me ve a1 (me1, ve1) ->
        stmt_eval prog me1 ve1 a2 (me2, ve2) ->
        stmt_eval prog me ve (Comp a1 a2) (me2, ve2)
  | Iifte:
      forall prog me ve cond v b ifTrue ifFalse ve' me',
        exp_eval me ve cond v ->
        val_to_bool v = Some b ->
        stmt_eval prog me ve (if b then ifTrue else ifFalse) (me', ve') ->
        stmt_eval prog me ve (Ifte cond ifTrue ifFalse) (me', ve')
  | Iskip:
      forall prog me ve,
        stmt_eval prog me ve Skip (me, ve)

  with stmt_call_eval :
     program -> menv -> ident -> ident -> list val -> menv -> list val -> Prop :=
  | Iecall:
      forall prog me clsid f fm vs prog' me' ve' cls rvs,
        find_class clsid prog = Some(cls, prog') ->
        find_method f cls.(c_methods) = Some fm ->
        stmt_eval prog' me (Env.adds (map fst fm.(m_in)) vs vempty)
                  fm.(m_body) (me', ve') ->
        Forall2 (fun x v => Env.find x ve' = Some v) (map fst fm.(m_out)) rvs ->
        stmt_call_eval prog me clsid f vs me' rvs.

  Scheme stmt_eval_ind_2 := Minimality for stmt_eval Sort Prop
  with stmt_call_eval_ind_2 := Minimality for stmt_call_eval Sort Prop.
  Combined Scheme stmt_eval_call_ind from stmt_eval_ind_2, stmt_call_eval_ind_2.


  (** ** Determinism of semantics *)

  Lemma exp_eval_det:
    forall me ve e v1 v2,
      exp_eval me ve e v1 ->
      exp_eval me ve e v2 ->
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
    forall A prog f (xs:list A) iacc me ve me' ve',
      stmt_eval prog me ve
                (List.fold_left (fun i x => Comp (f x) i) xs iacc)
                (me', ve')
      <->
      exists me'' ve'',
        stmt_eval prog me ve
                  (List.fold_left (fun i x => Comp (f x) i) xs Skip)
                  (me'', ve'')
        /\
        stmt_eval prog me'' ve'' iacc (me', ve').
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
        destruct H0 as [me'' H0].
        destruct H0 as [ve'' H0].
        destruct H0 as [H0 H1].
        inversion_clear H1.
        exists me1. exists ve1.
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
  Lemma exp_eval_extend_env :
    forall me ve x v' e v,
      ~Is_free_in_exp x e -> exp_eval me ve e v -> exp_eval me (Env.add x v' ve) e v.
  Proof.
    intros me ve x v' e.
    induction e (* using exp_ind2 *); intros v1 Hfree Heval.
    - inv Heval. constructor. not_free. now rewrite Env.gso.
    - inv Heval. now constructor.
    - inv Heval. now constructor.
    - inv Heval. constructor 4 with c; trivial.
      not_free.
      now apply IHe.
    - inv Heval. constructor 5 with (c1 := c1) (c2 := c2); trivial; not_free.
      + now apply IHe1.
      + now apply IHe2.
  Qed.

  (** If we add irrelevent values to [me], evaluation does not change. *)
  Lemma exp_eval_extend_mem :
    forall me ve x v' e v,
      ~Is_free_in_exp x e -> exp_eval me ve e v -> exp_eval (add_val x v' me) ve e v.
  Proof.
    intros me ve x v' e.
    induction e (* using exp_ind2 *); intros v1 Hfree Heval.
    - inversion_clear Heval. now constructor.
    - inversion_clear Heval. constructor. not_free. now rewrite find_val_gso.
    - inversion_clear Heval. now constructor.
    - inversion_clear Heval. constructor 4 with c; trivial.
      not_free.
      now apply IHe.
    - inv Heval. constructor 5 with (c1 := c1) (c2 := c2); trivial; not_free.
      + now apply IHe1.
      + now apply IHe2.
  Qed.

  (** If we add objects to [me], evaluation does not change. *)
  Lemma exp_eval_extend_mem_by_obj :
    forall me ve f obj e v,
      exp_eval me ve e v -> exp_eval (add_inst f obj me) ve e v.
  Proof.
    intros me ve f v' e.
    induction e (* using exp_ind2 *); intros v1 Heval.
    - inversion_clear Heval. now constructor.
    - inversion_clear Heval. constructor. now rewrite find_val_add_inst.
    - inversion_clear Heval. now constructor.
    - inversion_clear Heval. constructor 4 with c; trivial.
      now apply IHe.
    - inv Heval. constructor 5 with (c1 := c1) (c2 := c2); trivial.
      + now apply IHe1.
      + now apply IHe2.
  Qed.

End OBCSEMANTICS.

Module ObcSemanticsFun
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Syn   : OBCSYNTAX Ids Op OpAux) <: OBCSEMANTICS Ids Op OpAux Syn.
  Include OBCSEMANTICS Ids Op OpAux Syn.
End ObcSemanticsFun.
