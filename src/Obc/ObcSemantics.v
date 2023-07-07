From Coq Require Import FSets.FMapPositive.
From Coq Require Import Setoid.
From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import VelusMemory.
From Velus Require Import Obc.ObcSyntax.

(** * Obc semantics *)

(**

  The semantics of Obc relies on a tree-structure [memory], based
  on [Velus.VelusMemory], to store object instances and a [venv] to keep
  track of local variables during method calls.

 *)

Module Type OBCSEMANTICS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Syn   : OBCSYNTAX Ids Op OpAux).

  Definition menv := memory value.
  Definition venv := env value.

  Definition mempty: menv := empty_memory _.
  Definition vempty: venv := Env.empty _.

  Definition instance_match (i: ident) (me: menv) : menv :=
    match find_inst i me with
    | None => mempty
    | Some i => i
    end.

  Lemma instance_match_empty:
    forall x, instance_match x mempty = mempty.
  Proof.
    intros. unfold instance_match, find_inst; simpl.
    now rewrite Env.gempty.
  Qed.

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

  Inductive exp_eval (me: menv) (ve: venv): exp -> option value -> Prop :=
  | evar:
      forall x ty,
        exp_eval me ve (Var x ty) (Env.find x ve)
  | estate:
      forall x v ty islast,
        find_val x me = Some v ->
        exp_eval me ve (State x ty islast) (Some v)
  | econst:
      forall c,
        exp_eval me ve (Const c) (Some (Vscalar (sem_cconst c)))
  | eenum:
      forall x ty,
        exp_eval me ve (Enum x ty) (Some (Venum x))
  | eunop :
      forall op e v v' ty,
        exp_eval me ve e (Some v) ->
        sem_unop op v (typeof e) = Some v' ->
        exp_eval me ve (Unop op e ty) (Some v')
  | ebinop :
      forall op e1 e2 v1 v2 v' ty,
        exp_eval me ve e1 (Some v1) ->
        exp_eval me ve e2 (Some v2) ->
        sem_binop op v1 (typeof e1) v2 (typeof e2) = Some v' ->
        exp_eval me ve (Binop op e1 e2 ty) (Some v')
  (* | eextern : *)
  (*     forall f es ty ge tyins vs v', *)
  (*       Forall2 (fun e ty => typeof e = Tprimitive ty) es tyins -> *)
  (*       Forall2 (fun e v => exp_eval me ve e (Some (Vscalar v))) es vs -> *)
  (*       sem_extern (* XXX *) ge f tyins vs ty v' -> *)
  (*       exp_eval me ve (Extern f es (Tprimitive ty)) (Some (Vscalar v')) *)
  | evalid:
      forall x v ty,
        Env.find x ve = Some v ->
        exp_eval me ve (Valid x ty) (Some v).

  Inductive stmt_eval :
    program -> menv -> venv -> stmt -> menv * venv -> Prop :=
  | Iassign:
      forall prog me ve x e v,
        exp_eval me ve e (Some v) ->
        stmt_eval prog me ve (Assign x e) (me, Env.add x v ve)
  | Iassignst:
    forall prog me ve x e isreset v,
      exp_eval me ve e (Some v) ->
      stmt_eval prog me ve (AssignSt x e isreset) (add_val x v me, ve)
  | Icall:
      forall prog me ve es vos clsid o f ys ome' rvos,
        Forall2 (exp_eval me ve) es vos ->
        stmt_call_eval prog (instance_match o me) clsid f vos ome' rvos ->
        stmt_eval prog me ve (Call ys clsid o f es) (add_inst o ome' me, Env.adds_opt ys rvos ve)
  | Iexterncall:
    forall prog me ve es f tyout tyins vs y rvo,
      Forall2 (fun e ty => typeof e = Tprimitive ty) es tyins ->
      Forall2 (fun e v => exp_eval me ve e (Some (Vscalar v))) es vs ->
      sem_extern f tyins vs tyout rvo ->
      stmt_eval prog me ve (ExternCall y f es tyout) (me, Env.add y (Vscalar rvo) ve)
  | Icomp:
      forall prog me ve a1 a2 ve1 me1 ve2 me2,
        stmt_eval prog me ve a1 (me1, ve1) ->
        stmt_eval prog me1 ve1 a2 (me2, ve2) ->
        stmt_eval prog me ve (Comp a1 a2) (me2, ve2)
  | Iswitch:
      forall prog me ve cond branches default c s me' ve',
        exp_eval me ve cond (Some (Venum c)) ->
        nth_error branches c = Some s ->
        stmt_eval prog me ve (or_default default s) (me', ve') ->
        stmt_eval prog me ve (Switch cond branches default) (me', ve')
  | Iskip:
      forall prog me ve,
        stmt_eval prog me ve Skip (me, ve)

  with stmt_call_eval : program -> menv -> ident -> ident -> list (option value)
                        -> menv -> list (option value) -> Prop :=
  | Iecall:
      forall prog me clsid f fm vos prog' me' ve' cls rvos,
        find_class clsid prog = Some(cls, prog') ->
        find_method f cls.(c_methods) = Some fm ->
        length vos = length fm.(m_in) ->
        stmt_eval prog' me (Env.adds_opt (map fst fm.(m_in)) vos vempty)
                  fm.(m_body) (me', ve') ->
        Forall2 (fun x => eq (Env.find x ve')) (map fst fm.(m_out)) rvos ->
        stmt_call_eval prog me clsid f vos me' rvos.

  Global Hint Constructors exp_eval stmt_eval stmt_call_eval : obcsem.

  Section stmt_eval_call_eval_ind.

    Variable P_stmt : program -> menv -> venv -> stmt -> menv * venv -> Prop.
    Variable P_call : program -> menv -> ident -> ident -> list (option value)
                        -> menv -> list (option value) -> Prop.

    Hypothesis assignCase:
      forall prog me ve x e v,
        exp_eval me ve e (Some v) ->
        P_stmt prog me ve (Assign x e) (me, Env.add x v ve).

    Hypothesis assignstCase:
      forall prog me ve x e isreset v,
        exp_eval me ve e (Some v) ->
        P_stmt prog me ve (AssignSt x e isreset) (add_val x v me, ve).

    Hypothesis callCase:
      forall prog me ve es vos clsid o f ys ome' rvos,
        Forall2 (exp_eval me ve) es vos ->
        stmt_call_eval prog (instance_match o me) clsid f vos ome' rvos ->
        P_call prog (instance_match o me) clsid f vos ome' rvos ->
        P_stmt prog me ve (Call ys clsid o f es) (add_inst o ome' me, Env.adds_opt ys rvos ve).

    Hypothesis externcallCase:
      forall prog me ve es f tyout tyins vs y rvo,
        Forall2 (fun e ty => typeof e = Tprimitive ty) es tyins ->
        Forall2 (fun e v => exp_eval me ve e (Some (Vscalar v))) es vs ->
        sem_extern f tyins vs tyout rvo ->
        P_stmt prog me ve (ExternCall y f es tyout) (me, Env.add y (Vscalar rvo) ve).

    Hypothesis compCase:
      forall prog me ve a1 a2 ve1 me1 ve2 me2,
        stmt_eval prog me ve a1 (me1, ve1) ->
        P_stmt prog me ve a1 (me1, ve1) ->
        stmt_eval prog me1 ve1 a2 (me2, ve2) ->
        P_stmt prog me1 ve1 a2 (me2, ve2) ->
        P_stmt prog me ve (Comp a1 a2) (me2, ve2).

    Hypothesis switchCase:
      forall prog me ve cond branches default c s me' ve',
        exp_eval me ve cond (Some (Venum c)) ->
        nth_error branches c = Some s ->
        P_stmt prog me ve (or_default default s) (me', ve') ->
        P_stmt prog me ve (Switch cond branches default) (me', ve').

    Hypothesis skipCase:
      forall prog me ve,
        P_stmt prog me ve Skip (me, ve).

    Hypothesis Call:
      forall prog me clsid f fm vos prog' me' ve' cls rvos,
        find_class clsid prog = Some(cls, prog') ->
        find_method f cls.(c_methods) = Some fm ->
        length vos = length fm.(m_in) ->
        stmt_eval prog' me (Env.adds_opt (map fst fm.(m_in)) vos vempty) fm.(m_body) (me', ve') ->
        P_stmt prog' me (Env.adds_opt (map fst fm.(m_in)) vos vempty) fm.(m_body) (me', ve') ->
        Forall2 (fun x => eq (Env.find x ve')) (map fst fm.(m_out)) rvos ->
        P_call prog me clsid f vos me' rvos.

    Fixpoint stmt_eval_ind_2
            (prog: program) (me: menv) (ve: venv) (s: stmt) (meve': menv * venv)
            (Sem: stmt_eval prog me ve s meve') {struct Sem}
      : P_stmt prog me ve s meve'
    with stmt_call_eval_ind_2
           (prog: program) (me: menv) (c f: ident) (xs: list (option value)) (me': menv) (ys: list (option value))
           (Sem: stmt_call_eval prog me c f xs me' ys) {struct Sem}
         : P_call prog me c f xs me' ys.
    Proof.
      - inv Sem.
        + apply assignCase; auto.
        + apply assignstCase; auto.
        + eapply callCase; eauto.
        + eapply externcallCase; eauto.
        + eapply compCase; eauto.
        + eapply switchCase; eauto.
        + apply skipCase.
      - inv Sem; eapply Call; eauto.
    Defined.

    Combined Scheme stmt_eval_call_ind from stmt_eval_ind_2, stmt_call_eval_ind_2.

  End stmt_eval_call_eval_ind.

  CoInductive loop_call (prog: program) (clsid f: ident) (ins outs: nat -> list (option value)): nat -> menv -> Prop :=
    Step:
      forall n me me',
      stmt_call_eval prog me clsid f (ins n) me' (outs n) ->
      loop_call prog clsid f ins outs (S n) me' ->
      loop_call prog clsid f ins outs n me.

  Section LoopCallCoind.

    Variable R: program -> ident -> ident -> (nat -> list (option value)) -> (nat -> list (option value)) -> nat -> menv -> Prop.

    Hypothesis LoopCase:
      forall prog clsid f ins outs n me,
        R prog clsid f ins outs n me ->
        exists me',
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
    induction e; intros * H1 H2; inv H1; inv H2; try congruence.
    - assert (Some v = Some v0) as E by auto; inv E.
      congruence.
    - assert (Some v1 = Some v0) as E by auto; inv E.
      assert (Some v4 = Some v3) as E by auto; inv E.
      congruence.
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

  Lemma exps_eval_det':
    forall me ve es vs1 vs2,
      Forall2 (fun e v => exp_eval me ve e (Some (Vscalar v))) es vs1 ->
      Forall2 (fun e v => exp_eval me ve e (Some (Vscalar v))) es vs2 ->
      vs1 = vs2.
  Proof.
    intros * Sem1 Sem2; revert dependent vs2; induction Sem1;
      inversion_clear 1; auto.
    f_equal; auto.
    eapply exp_eval_det in H; eauto. now inv H.
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
    - (* Extern Call *)
      take (stmt_eval _ _ _ _ _) and inv it. repeat f_equal.
      match goal with
        H: Forall2 _ _ _, H': Forall2 _ _ _ |- _ =>
        eapply exps_eval_det' with (2 := H') in H; eauto; inv H
      end.
      assert (tyins = tyins0); subst.
      { apply Forall2_eq.
        eapply Forall2_swap_args in H. eapply Forall2_trans_ex in H10; [|eauto].
        simpl_Forall. congruence.
      }
      eapply sem_extern_det; eauto.

    - (* Comp *)
      match goal with H:stmt_eval _ _ _ (Comp _ _) _ |- _ => inv H end.
      match goal with
        H: stmt_eval _ ?me ?ve ?s ?mv1, H': stmt_eval _ ?me ?ve ?s ?mv2 |- _ =>
        let E := fresh in assert (mv1 = mv2) as E; eauto; inv E
      end; eauto.
    - take (stmt_eval _ _ _ (Switch _ _ _) _) and inv it.
      match goal with
        H: exp_eval ?me ?ve ?e _, H': exp_eval ?me ?ve ?e _ |- _ =>
        eapply exp_eval_det in H; eauto; inv H
      end.
      match goal with
        H: nth_error _ _ = _, H': nth_error _ _ = _ |- _ =>
        rewrite H in H'; inv H'
      end; auto.
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
        clear - H H'; revert dependent ys; induction H; intros; inv H'; auto with datatypes
      end.
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
          inversion_clear H as [| | | |?????????? H'| |]; inv H';
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
          inversion_clear H as [| | | |????????? H'| |]; inv H';
            eauto using stmt_eval.
  Qed.

  (** ** Other properties *)

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
    intros * Sem.
    (* trick to perform the induction *)
    change me' with (fst (me', ve')).
    revert Sem; generalize (me', ve').
    induction 1 using stmt_eval_ind_2
      with (P_call := fun prog me c f xs me' ys => True);
      subst; simpl; auto; intros y Hmfind.
    destruct (ident_eq_dec y x).
    - now subst; setoid_rewrite find_val_gss.
    - now setoid_rewrite find_val_gso.
  Qed.

  Lemma stmt_call_eval_cons:
    forall prog c' c me f vs me' rvs enums externs,
      c_name c <> c' ->
      (stmt_call_eval (Program enums externs (c :: prog)) me c' f vs me' rvs
       <-> stmt_call_eval (Program enums externs prog) me c' f vs me' rvs).
  Proof.
    intros * Neq; split; intros Sem.
    - inversion_clear Sem as [??????????? Find].
      eapply find_unit_cons in Find as [[]|[? Find]]; simpl in *; eauto using stmt_call_eval; congruence.
    - inv Sem; econstructor; eauto.
      eapply find_unit_cons; simpl; eauto.
  Qed.

  Ltac chase_skip :=
    match goal with
      H: stmt_eval _ _ _ Skip _ |- _ => inv H
    end.

End OBCSEMANTICS.

Module ObcSemanticsFun
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Syn   : OBCSYNTAX Ids Op OpAux) <: OBCSEMANTICS Ids Op OpAux Syn.
  Include OBCSEMANTICS Ids Op OpAux Syn.
End ObcSemanticsFun.
