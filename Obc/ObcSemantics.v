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

  Lemma exps_eval_det:
    forall me ve es vs1 vs2,
      Forall2 (exp_eval me ve) es vs1 ->
      Forall2 (exp_eval me ve) es vs2 ->
      vs1 = vs2.
  Proof.
    intros ** Sem1 Sem2; revert dependent vs2; induction Sem1;
      inversion_clear 1; auto.
    f_equal; auto.
    eapply exp_eval_det; eauto.
  Qed.

  Lemma stmt_eval_call_eval_det:
    (forall prog me ve s meve1,
        stmt_eval prog me ve s meve1 ->
        forall meve2,
          stmt_eval prog me ve s meve2 ->
          meve1 = meve2)
    /\
    (forall prog me clsid f vs me1 rvs1,
        stmt_call_eval prog me clsid f vs me1 rvs1 ->
        forall me2 rvs2,
          stmt_call_eval prog me clsid f vs me2 rvs2 ->
          me1 = me2 /\ rvs1 = rvs2).
  Proof.
    apply stmt_eval_call_ind; intros ** Sem; inversion Sem; subst;
      try match goal with
            H: exp_eval ?me ?ve ?e _, H': exp_eval ?me ?ve ?e _ |- _ =>
            eapply exp_eval_det in H; eauto; subst
          end; auto.
    - match goal with
        H: Forall2 _ _ _, H': Forall2 _ _ _ |- _ =>
        eapply exps_eval_det with (2 := H') in H; eauto; inv H
      end.
      match goal with
        H: stmt_call_eval _ _ _ _ _ ?me' ?rvs', H': stmt_call_eval _ _ _ _ _ ome' rvs |- _ =>
        assert (ome' = me' /\ rvs = rvs') as E; eauto; inv E
      end; auto.
    - match goal with
        H: stmt_eval _ ?me ?ve ?s ?mv1, H': stmt_eval _ ?me ?ve ?s ?mv2 |- _ =>
        let E := fresh in assert (mv1 = mv2) as E; eauto; inv E
      end; eauto.
    - match goal with
        H: val_to_bool ?v = _, H': val_to_bool ?v = _ |- _ =>
        rewrite H in H'; inv H'
      end.
      destruct b; eauto.
    - match goal with
        H: find_class ?c ?p = _, H': find_class ?c ?p = _ |- _ =>
        rewrite H in H'; inv H'
      end;
        match goal with
          H: find_method ?f ?m = _, H': find_method ?f ?m = _ |- _ =>
          rewrite H in H'; inv H'
        end.
      match goal with
        H: stmt_eval _ _ _ _ ?mv |- _ =>
        assert ((me', ve') = mv) as E; eauto; inv E
      end.
      intuition.
      match goal with
        H: Forall2 _ ?xs _, H': Forall2 _ ?xs ?ys |- _ =>
        clear - H H'; revert dependent ys; induction H; intros; inv H'; auto
      end.
      f_equal; auto; congruence.
  Qed.

  Lemma stmt_eval_det:
    forall prog s me ve me1 ve1 me2 ve2,
      stmt_eval prog me ve s (me1, ve1) ->
      stmt_eval prog me ve s (me2, ve2) ->
      me1 = me2 /\ ve1 = ve2.
  Proof.
    intros ** Sem1 Sem2; apply (proj1 stmt_eval_call_eval_det) with (2 := Sem2) in Sem1; auto.
    intuition; congruence.
  Qed.

  Lemma stmt_call_eval_det:
    forall prog me clsid f vs me1 rvs1 me2 rvs2,
        stmt_call_eval prog me clsid f vs me1 rvs1 ->
        stmt_call_eval prog me clsid f vs me2 rvs2 ->
        me1 = me2 /\ rvs1 = rvs2.
  Proof.
    intros; eapply (proj2 stmt_eval_call_eval_det); eauto.
  Qed.

  Lemma stmt_eval_fold_left_shift:
    forall A prog f (xs:list A) iacc me ve me' ve',
      stmt_eval prog me ve
                (fold_left (fun i x => Comp (f x) i) xs iacc)
                (me', ve')
      <->
      exists me'' ve'',
        stmt_eval prog me ve
                  (fold_left (fun i x => Comp (f x) i) xs Skip)
                  (me'', ve'')
        /\
        stmt_eval prog me'' ve'' iacc (me', ve').
  Proof.
    induction xs; simpl.
    - split; eauto using stmt_eval.
      intros (?&?& H &?); now inv H.
    - setoid_rewrite IHxs; split.
      + intros (?&?&?& H); inv H; eauto 8 using stmt_eval.
      + intros (?&?&(?&?&?& H)&?);
          inversion_clear H as [| | |?????????? H'| |]; inv H';
            eauto using stmt_eval.
  Qed.

  Lemma stmt_eval_fold_left_lift:
    forall A prog f (xs: list A) me ve iacc me' ve',
      stmt_eval prog me ve
                (fold_left (fun i x => Comp i (f x)) xs iacc)
                (me', ve')
      <->
      exists me'' ve'',
        stmt_eval prog me ve iacc (me'', ve'')
        /\ stmt_eval prog me'' ve''
                    (fold_left (fun i x => Comp i (f x)) xs Skip)
                    (me', ve').
  Proof.
    induction xs; simpl.
    - split; eauto using stmt_eval.
      intros (?&?&?& H); now inv H.
    - setoid_rewrite IHxs; split.
      + intros (?&?& H &?); inv H; eauto 8 using stmt_eval.
      + intros (?&?&?&?&?& H &?);
          inversion_clear H as [| | |????????? H'| |]; inv H';
            eauto using stmt_eval.
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

  Lemma stmt_call_eval_cons:
    forall prog c' c me f vs me' rvs,
      c_name c <> c' ->
      (stmt_call_eval (c :: prog) me c' f vs me' rvs
       <-> stmt_call_eval prog me c' f vs me' rvs).
  Proof.
    intros ** Neq; rewrite <-ident_eqb_neq in Neq; split; intros Sem.
    - inversion_clear Sem as [??????????? Find].
      simpl in Find; rewrite Neq in Find; eauto using stmt_call_eval.
    - inv Sem; econstructor; eauto.
      simpl; rewrite Neq; auto.
  Qed.

End OBCSEMANTICS.

Module ObcSemanticsFun
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Syn   : OBCSYNTAX Ids Op OpAux) <: OBCSEMANTICS Ids Op OpAux Syn.
  Include OBCSEMANTICS Ids Op OpAux Syn.
End ObcSemanticsFun.
