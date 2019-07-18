From Coq Require Import FSets.FMapPositive.
From Coq Require Import Setoid.
From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Memory.
From Velus Require Import Obc.ObcSyntax.

(** * Obc semantics *)

(**

  The semantics of Obc relies on a tree-structure [memory], based
  on [Velus.Memory], to store object instances and a [venv] to keep
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

  Hint Unfold vempty.

  (* Function call arguments either evaluate fully (i.e., to Some value), or
     they are undefined variables in [menv] or [env] (i.e., None). The idea
     is to distinguish a failed operator application, e.g., division by zero,
     or an operation on undefined values, from an undefined variable.

     This complication allows the use of Obc as a target for NLustre
     programs with subclocked inputs. We are not supposed to perform
     calculations in the target code (Obc) for expressions whose value
     is absent in the source program (NLustre); e.g., this could lead
     to a division by zero in the code generated from a program that
     provably never divides by zero. But, it should be possible to pass
     variables as arguments even if their values have not been defined
     (we don't care about their value since they are absent). What can
     we pass otherwise?

     Another solution would be to use an undefined value (like CompCert's
     [Val.Vundef]) and to change the rules for [Var] and [State] in
     [exp_eval] to return it. E.g.,
                [Var x ty => match PM.find x s with
                             | None => Some Val.Vundef
                             | Some v => Some v end]
     But this complicates some of the relations in ObcTyping and also
     the statement of invariants between Obc and Clight where [None] is
     used to signal a "don't care" on variable values. *)

  Inductive exp_eval (me: menv) (ve: venv): exp -> option val -> Prop :=
  | evar:
      forall x v ty,
        Env.find x ve = v ->
        exp_eval me ve (Var x ty) v
  | estate:
      forall x v ty,
        find_val x me = Some v ->
        exp_eval me ve (State x ty) (Some v)
  | econst:
      forall c,
        exp_eval me ve (Const c) (Some (sem_const c))
  | eunop :
      forall op e c v ty,
        exp_eval me ve e (Some c) ->
        sem_unop op c (typeof e) = Some v ->
        exp_eval me ve (Unop op e ty) (Some v)
  | ebinop :
      forall op e1 e2 c1 c2 v ty,
        exp_eval me ve e1 (Some c1) ->
        exp_eval me ve e2 (Some c2) ->
        sem_binop op c1 (typeof e1) c2 (typeof e2) = Some v ->
        exp_eval me ve (Binop op e1 e2 ty) (Some v)
  | evalid:
      forall x v ty,
        Env.find x ve = Some v ->
        exp_eval me ve (Valid x ty) (Some v).

  Inductive stmt_eval :
    program -> menv -> venv -> stmt -> menv * venv -> Prop :=
  | Iassign:
      forall prog me ve x e v ve',
        exp_eval me ve e (Some v) ->
        Env.add x v ve = ve' ->
        stmt_eval prog me ve (Assign x e) (me, ve')
  | Iassignst:
    forall prog me ve x e v me',
      exp_eval me ve e (Some v) ->
      add_val x v me = me' ->
      stmt_eval prog me ve (AssignSt x e) (me', ve)
  | Icall:
      forall prog me ve es vos clsid o f ys me' ve' ome ome' rvos,
        ome = match find_inst o me with
              | None => mempty
              | Some om => om
              end ->
        Forall2 (exp_eval me ve) es vos ->
        stmt_call_eval prog ome clsid f vos ome' rvos ->
        add_inst o ome' me = me' ->
        Env.updates ys rvos ve = ve' ->
        stmt_eval prog me ve (Call ys clsid o f es) (me', ve')
  | Icomp:
      forall prog me ve a1 a2 ve1 me1 ve2 me2,
        stmt_eval prog me ve a1 (me1, ve1) ->
        stmt_eval prog me1 ve1 a2 (me2, ve2) ->
        stmt_eval prog me ve (Comp a1 a2) (me2, ve2)
  | Iifte:
      forall prog me ve cond v b ifTrue ifFalse ve' me',
        exp_eval me ve cond (Some v) ->
        val_to_bool v = Some b ->
        stmt_eval prog me ve (if b then ifTrue else ifFalse) (me', ve') ->
        stmt_eval prog me ve (Ifte cond ifTrue ifFalse) (me', ve')
  | Iskip:
      forall prog me ve,
        stmt_eval prog me ve Skip (me, ve)

  with stmt_call_eval : program -> menv -> ident -> ident -> list (option val)
                        -> menv -> list (option val) -> Prop :=
  | Iecall:
      forall prog me clsid f fm vos prog' me' ve' cls rvos,
        find_class clsid prog = Some(cls, prog') ->
        find_method f cls.(c_methods) = Some fm ->
        length vos = length fm.(m_in) ->
        stmt_eval prog' me (Env.adds_opt (map fst fm.(m_in)) vos vempty)
                  fm.(m_body) (me', ve') ->
        Forall2 (fun x vo => Env.find x ve' = vo) (map fst fm.(m_out)) rvos ->
        stmt_call_eval prog me clsid f vos me' rvos.

  Scheme stmt_eval_ind_2 := Minimality for stmt_eval Sort Prop
  with stmt_call_eval_ind_2 := Minimality for stmt_call_eval Sort Prop.
  Combined Scheme stmt_eval_call_ind from stmt_eval_ind_2, stmt_call_eval_ind_2.

  (* Definition present_consts: list const -> list (option val) := *)
  (*   map (fun c => Some (sem_const c)). *)

  CoInductive loop_call (prog: program) (clsid f: ident) (ins outs: nat -> list (option val)): nat -> menv -> Prop :=
    Step:
      forall n me me',
      (* let cins := present_consts (ins n) in *)
      (* let couts := present_consts (outs n) in *)
      stmt_call_eval prog me clsid f (ins n) me' (outs n) ->
      loop_call prog clsid f ins outs (S n) me' ->
      loop_call prog clsid f ins outs n me.

  Section LoopCallCoind.

    Variable R: program -> ident -> ident -> (nat -> list (option val)) -> (nat -> list (option val)) -> nat -> menv -> Prop.

    Hypothesis LoopCase:
      forall prog clsid f ins outs n me,
        R prog clsid f ins outs n me ->
        exists me',
          (* let cins := present_consts (ins n) in *)
        (* let couts := present_consts (outs n) in *)
          stmt_call_eval prog me clsid f (ins n) me' (outs n)
          /\ R prog clsid f ins outs (S n) me'.

    Lemma loop_call_coind:
      forall prog clsid f ins outs n me,
        R prog clsid f ins outs n me ->
        loop_call prog clsid f ins outs n me.
    Proof.
      cofix COINDHYP.
      intros * HR.
      destruct LoopCase with (1 := HR) as (?&?&?).
      econstructor; eauto.
    Qed.

  End LoopCallCoind.


  Add Parametric Morphism P f m: (loop_call P f m)
        with signature (fun a b => forall n, a n = b n) ==> (fun a b => forall n, a n = b n) ==> eq ==> eq ==> Basics.impl
          as loop_call_eq_str.
  Proof.
    cofix COFIX.
    intros * E ?? E' ?? Loop.
    inv Loop; econstructor.
    - rewrite <-E, <-E'; eauto.
    - eapply COFIX; eauto.
  Qed.

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
                     |opa e1a e2a c1a c2a va tya IH1a IH2a Hv1|? va ? Hv1];
    inversion H2 as [xb vb tyb Hv2|xb vb tyb Hv2|xb vb Hv2
                     |opb eb cb vb tyb IHb Hv2
                     |opb e1b e2b c1b c2b vb tyb IH1b IH2b Hv2|? vb ? Hv2];
    try (rewrite Hv1 in Hv2; (injection Hv2; trivial) || apply Hv2); subst; auto.
    - assert (Some ca = Some cb) as HH by (apply IHe; auto).
      inv HH. now rewrite Hv1 in Hv2.
    - assert (Some c1a = Some c1b) as HH1 by (apply IHe1; auto).
      assert (Some c2a = Some c2b) as HH2 by (apply IHe2; auto).
      inv HH1. inv HH2. now rewrite Hv1 in Hv2.
  Qed.

  Lemma exps_eval_det:
    forall me ve es vs1 vs2,
      Forall2 (exp_eval me ve) es vs1 ->
      Forall2 (exp_eval me ve) es vs2 ->
      vs1 = vs2.
  Proof.
    intros * Sem1 Sem2; revert dependent vs2; induction Sem1;
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
    apply stmt_eval_call_ind; intros.
    - (* Assign *)
      match goal with H:stmt_eval _ _ _ _ _ |- _ => inv H end;
        match goal with
          H: exp_eval ?me ?ve ?e _, H': exp_eval ?me ?ve ?e _ |- _ =>
          eapply exp_eval_det in H; eauto; subst
        end; congruence.
    - (* AssignSt *)
      match goal with H:stmt_eval _ _ _ _ _ |- _ => inv H end;
        try match goal with
              H: exp_eval ?me ?ve ?e _, H': exp_eval ?me ?ve ?e _ |- _ =>
              eapply exp_eval_det in H; eauto; subst
            end; congruence.
    - (* Call *)
      match goal with H:stmt_eval _ _ _ (Call _ _ _ _ _) _ |- _ => inv H end.
      match goal with
        H: Forall2 _ _ _, H': Forall2 _ _ _ |- _ =>
        eapply exps_eval_det with (2 := H') in H; eauto; inv H
      end.
      match goal with
        H: stmt_call_eval _ _ _ _ _ ?me' ?rvs',
           H': stmt_call_eval _ _ _ _ _ ?ome' ?rvs |- _ =>
        assert (ome' = me' /\ rvs = rvs') as E; eauto; inv E
      end; auto.
    - (* Comp *)
      match goal with H:stmt_eval _ _ _ (Comp _ _) _ |- _ => inv H end.
      match goal with
        H: stmt_eval _ ?me ?ve ?s ?mv1, H': stmt_eval _ ?me ?ve ?s ?mv2 |- _ =>
        let E := fresh in assert (mv1 = mv2) as E; eauto; inv E
      end; eauto.
    - (* Ifte *)
      match goal with H:stmt_eval _ _ _ (Ifte _ _ _) _ |- _ => inv H end.
      match goal with
        H: exp_eval ?me ?ve ?e _, H': exp_eval ?me ?ve ?e _ |- _ =>
        eapply exp_eval_det in H; eauto; subst
      end.
      match goal with H: _ = _ |- _ => inv H end.
      match goal with
        H: val_to_bool ?v = _, H': val_to_bool ?v = _ |- _ =>
        rewrite H in H'; inv H'
      end.
      cases; eauto.
    - (* Skip *)
      now match goal with H:stmt_eval _ _ _ _ _ |- _ => inv H end.
    - (* stmt_call_eval *)
      match goal with H:stmt_call_eval _ _ _ _ _ _ _ |- _ => inv H end.
      match goal with
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
    intros * Sem1 Sem2; apply (proj1 stmt_eval_call_eval_det) with (2 := Sem2) in Sem1; auto.
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

(*
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
*)
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

  (** If we add irrelevent values to [ve], evaluation does not change. *)
  Lemma exp_eval_extend_venv : forall me ve x v' e v,
      ~Is_free_in_exp x e ->
      (exp_eval me ve e v <-> exp_eval me (Env.add x v' ve) e v).
  Proof.
    intros me ve x v' e v Hfree.
    split; intro Heval.
    - revert v Hfree Heval.
      induction e; intros v Hfree Heval; inv Heval;
        try not_free; eauto using exp_eval;
          now constructor; rewrite Env.gso.
    - revert v Hfree Heval.
      induction e; intros v Hfree Heval; inv Heval;
        try not_free; eauto using exp_eval.
      now constructor; rewrite Env.gso.
      constructor; erewrite <-Env.gso; eauto.
  Qed.

  Lemma exp_eval_reduce_venv : forall me ve x e v,
      ~Is_free_in_exp x e ->
      (exp_eval me ve e v <-> exp_eval me (Env.remove x ve) e v).
  Proof.
    intros me ve x e v Hfree.
    split; intro Heval.
    - revert v Hfree Heval.
      induction e; intros v Hfree Heval; inv Heval;
        try not_free; eauto using exp_eval;
          now constructor; rewrite Env.gro.
    - revert v Hfree Heval.
      induction e; intros v Hfree Heval; inv Heval;
        try not_free; eauto using exp_eval.
      now constructor; rewrite Env.gro.
      constructor; erewrite <-Env.gro; eauto.
  Qed.

  Lemma exp_eval_adds_extend_venv:
    forall me e xs rvs ve v,
      (forall x, In x xs -> ~Is_free_in_exp x e) ->
      (exp_eval me (Env.adds_opt xs rvs ve) e v <-> exp_eval me ve e v).
  Proof.
    induction xs as [|x xs IH]; destruct rvs as [|rv rvs]; auto; try reflexivity.
    destruct rv.
    2:now setoid_rewrite Env.adds_opt_cons_cons_None; auto with datatypes.
    intros ve v' Hnfree.
    rewrite Env.adds_opt_cons_cons, <-exp_eval_extend_venv; auto with datatypes.
  Qed.

  Lemma exp_eval_updates_extend_venv:
    forall me e xs rvs ve v,
      (forall x, In x xs -> ~Is_free_in_exp x e) ->
      (exp_eval me (Env.updates xs rvs ve) e v <-> exp_eval me ve e v).
  Proof.
    induction xs as [|x xs IH]; destruct rvs as [|rv rvs]; auto; try reflexivity.
    intros ve v' Hnfree.
    rewrite Env.updates_cons_cons.
    destruct rv.
    - rewrite <-exp_eval_extend_venv; auto with datatypes.
    - rewrite <-exp_eval_reduce_venv; auto with datatypes.
  Qed.

  (** If we add irrelevent values to [me], evaluation does not change. *)
  Lemma exp_eval_extend_menv : forall me ve x v' e v,
      ~Is_free_in_exp x e ->
      (exp_eval (add_val x v' me) ve e v <-> exp_eval me ve e v).
  Proof.
    intros me ve x v' e v Hfree. split.
    - revert v Hfree.
      induction e; intros v1 Hfree Heval; inv Heval;
        try not_free; try rewrite find_val_gso in *; eauto using exp_eval.
    - revert v Hfree.
      induction e; intros v1 Hfree Heval; inv Heval;
        try not_free; eauto using exp_eval.
      now constructor; rewrite find_val_gso.
  Qed.

  (** If we add objects to [me], evaluation does not change. *)
  Lemma exp_eval_extend_menv_by_obj : forall me ve f obj e v,
      exp_eval (add_inst f obj me) ve e v <-> exp_eval me ve e v.
  Proof.
    intros me ve f v' e v. split; revert v.
    - induction e; intros v1 Heval; inv Heval; eauto using exp_eval.
    - induction e; intros v1 Heval; inv Heval; eauto using exp_eval.
  Qed.

  Lemma Forall2_exp_eval_not_None:
    forall me ve es vos,
      Forall2 (exp_eval me ve) es vos ->
      Forall (fun e => forall x ty, e <> Var x ty) es ->
      Forall (fun vo => vo <> None) vos.
  Proof.
    induction 1 as [|e vo es vos Hexp Hvos IH]; auto.
    inversion_clear 1 as [|? ? Hnvar Hnvars].
    constructor; auto.
    inv Hexp; try discriminate.
    specialize (Hnvar x ty); auto.
  Qed.

  Lemma stmt_eval_find_val_mono:
    forall prog s me ve me' ve',
      stmt_eval prog me ve s (me', ve') ->
      forall x, find_val x me <> None ->
                find_val x me' <> None.
  Proof.
    induction s; inversion_clear 1; subst; auto; intros x Hmfind.
    - destruct (ident_eq_dec x i).
      now subst; setoid_rewrite find_val_gss.
      now setoid_rewrite find_val_gso.
    - destruct b;
      match goal with H:stmt_eval _ _ _ _ _ |- _ =>
        apply IHs1 with (x:=x) in H || apply IHs2 with (x:=x) in H end;
      auto.
    - match goal with H:stmt_eval _ _ _ s1 _ |- _ => eapply IHs1 in H end;
      match goal with H:stmt_eval _ _ _ s2 _ |- _ => eapply IHs2 in H end; eauto.
  Qed.

  Lemma stmt_eval_mono:
    forall p,
      (forall ome ome' clsid f vos rvos,
          stmt_call_eval p ome clsid f vos ome' rvos ->
          Forall (fun x => x <> None) rvos) ->
      forall s me ve me' ve',
        stmt_eval p me ve s (me', ve') ->
        forall x, Env.In x ve -> Env.In x ve'.
  Proof.
    induction s; intros * Heval x Hin; inv Heval; eauto.
    - destruct b; eauto.
    - match goal with H:stmt_call_eval _ _ _ _ _ _ _ |- _ => rename H into He end.
      apply H in He. auto using Env.updates_mono.
  Qed.

  Lemma stmt_call_eval_cons:
    forall prog c' c me f vs me' rvs,
      c_name c <> c' ->
      (stmt_call_eval (c :: prog) me c' f vs me' rvs
       <-> stmt_call_eval prog me c' f vs me' rvs).
  Proof.
    intros * Neq; rewrite <-ident_eqb_neq in Neq; split; intros Sem.
    - inversion_clear Sem as [??????????? Find].
      simpl in Find; rewrite Neq in Find; eauto using stmt_call_eval.
    - inv Sem; econstructor; eauto.
      simpl; rewrite Neq; auto.
  Qed.

  Ltac chase_skip :=
    match goal with
      H: stmt_eval _ _ _ Skip _ |- _ => inv H
    end.

End OBCSEMANTICS.

Module ObcSemanticsFun
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Syn   : OBCSYNTAX Ids Op OpAux) <: OBCSEMANTICS Ids Op OpAux Syn.
  Include OBCSEMANTICS Ids Op OpAux Syn.
End ObcSemanticsFun.
