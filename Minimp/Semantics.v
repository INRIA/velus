Require Import Coq.FSets.FMapPositive.
Require Import Rustre.Nelist.
Require Import List.

Require Import Rustre.Common.
Require Import Rustre.RMemory.
Require Import Rustre.Minimp.Syntax.

(** * Minimp semantics *)

(** 

  The semantics of Minimp relies on a tree-structure [memory], based
  on [Rustre.RMemory], to store object instances and a [stack] to keep
  track of local variables during method calls.

 *)

Module Type SEMANTICS
       (Import Op : OPERATORS)
       (Import Syn : SYNTAX Op).
  Definition heap: Type := memory val.
  Definition stack : Type := PM.t val.

  Implicit Type mmem: heap.
  Implicit Type stack: stack.

  Definition sempty: stack := PM.empty val.
  Definition hempty: heap := empty_memory _.

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
      forall c ty,
        exp_eval heap stack (Const c ty) c
   | eunop :
      forall op e c v ty,
        exp_eval heap stack e c ->
        sem_unary op c (typeof e) = Some v ->
        exp_eval heap stack (Unop op e ty) v
  | ebinop :
      forall op e1 e2 c1 c2 v ty,
        exp_eval heap stack e1 c1 ->
        exp_eval heap stack e2 c2 ->
        sem_binary op c1 (typeof e1) c2 (typeof e2) = Some v ->
        exp_eval heap stack (Binop op e1 e2 ty) v.

  Axiom exps_eval_const:
    forall h s cs,
      Nelist.Forall2 (exp_eval h s) (Nelist.map (fun c => Const c (typ_of_val c)) cs) cs.

  (* =stmt_eval= *)
  Inductive stmt_eval :
    program -> heap -> stack -> stmt -> heap * stack -> Prop :=
  | Iassign: forall prog menv env x e v env',
      exp_eval menv env e v ->
      PM.add x v env = env' ->
      stmt_eval prog menv env (Assign x e) (menv, env')
  | (*...*)
  (* =end= *)
  Iassignst:
    forall prog menv env x e v menv',
      exp_eval menv env e v ->
      madd_mem x v menv = menv' ->
      stmt_eval prog menv env (AssignSt x e) (menv', env)
  (* =stmt_eval:step= *)
  | Istep: forall prog menv env es vs clsid o y menv' env' omenv omenv' rv,
      mfind_inst o menv = Some(omenv) ->
      Nelist.Forall2 (exp_eval menv env) es vs ->
      stmt_step_eval prog omenv clsid vs omenv' rv ->
      madd_obj o omenv' menv = menv' ->
      PM.add y rv env  = env' ->
      stmt_eval prog menv env (Step_ap y clsid o es) (menv', env')
  | (*...*)
  (* =end= *)
  Ireset:
    forall prog menv env o clsid omenv' menv',
      stmt_reset_eval prog clsid omenv' ->
      madd_obj o omenv' menv = menv' ->
      stmt_eval prog menv env (Reset_ap clsid o) (menv', env)
  | Icomp:
      forall prog menv env a1 a2 env1 menv1 env2 menv2,
        stmt_eval prog menv env a1 (menv1, env1) ->
        stmt_eval prog menv1 env1 a2 (menv2, env2) ->
        stmt_eval prog menv env (Comp a1 a2) (menv2, env2)
   | Iifte:
      forall prog menv env cond b ifTrue ifFalse env' menv',
        exp_eval menv env cond (Vbool b) ->
        stmt_eval prog menv env (if b then ifTrue else ifFalse) (menv', env') -> 
        stmt_eval prog menv env (Ifte cond ifTrue ifFalse) (menv', env')
  | Iskip:
      forall prog menv env,
        stmt_eval prog menv env Skip (menv, env)
  (* =stmt_step_eval= *)
  with stmt_step_eval :
         program -> heap -> ident -> nelist val -> heap -> val -> Prop :=
       | Iestep:
           forall prog menv env clsid ivs prog' menv' ov cls env',
             find_class clsid prog = Some(cls, prog') ->
             env = adds cls.(c_input) ivs sempty ->
             stmt_eval prog' menv env cls.(c_step)
                                            (menv', env') ->
             PM.find cls.(c_output) env' = Some(ov) ->
             stmt_step_eval prog menv clsid ivs menv' ov
  (* =end= *)

  with stmt_reset_eval : program -> ident -> heap -> Prop :=
       | Iereset:
           forall prog clsid cls prog' menv' env',
             find_class clsid prog = Some(cls, prog') ->
             stmt_eval prog' hempty sempty cls.(c_reset) (menv', env') ->
             stmt_reset_eval prog clsid menv'.

  Scheme stmt_eval_mult := Induction for stmt_eval Sort Prop
                           with stmt_step_eval_mult := Induction for stmt_step_eval Sort Prop
                                                       with stmt_reset_eval_mult := Induction for stmt_reset_eval Sort Prop.

  (** ** Determinism of semantics *)

  Axiom exp_eval_det:
    forall menv env e v1 v2,
      exp_eval menv env e v1 ->
      exp_eval menv env e v2 ->
      v1 = v2.

  (* OBLIGATOIRE SINON ERREUR DANS UNE PREUVE DE Correctness.v *)
  Hint Constructors stmt_eval.
  
  Axiom stmt_eval_fold_left_shift:
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

  Axiom exp_evals_det:
    forall menv env es vs1 vs2,
      Nelist.Forall2 (exp_eval menv env) es vs1 ->
      Nelist.Forall2 (exp_eval menv env) es vs2 ->
      vs1 = vs2.

  Axiom stmt_eval_det:
    forall prog s menv env renv1 renv2,
      stmt_eval prog menv env s renv1
      -> stmt_eval prog menv env s renv2
      -> renv1 = renv2.

End SEMANTICS.

Module SemanticsFun' (Import Op: OPERATORS) (Import Syn: SYNTAX Op).
  Definition heap: Type := memory val.
  Definition stack : Type := PM.t val.

  Implicit Type mmem: heap.
  Implicit Type stack: stack.

  Definition sempty: stack := PM.empty val.
  Definition hempty: heap := empty_memory _.

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
      forall c ty,
        exp_eval heap stack (Const c ty) c
   | eunop :
      forall op e c v ty,
        exp_eval heap stack e c ->
        sem_unary op c (typeof e) = Some v ->
        exp_eval heap stack (Unop op e ty) v
  | ebinop :
      forall op e1 e2 c1 c2 v ty,
        exp_eval heap stack e1 c1 ->
        exp_eval heap stack e2 c2 ->
        sem_binary op c1 (typeof e1) c2 (typeof e2) = Some v ->
        exp_eval heap stack (Binop op e1 e2 ty) v.

  Theorem exps_eval_const:
    forall h s cs,
      Nelist.Forall2 (exp_eval h s) (Nelist.map (fun c => Const c (typ_of_val c)) cs) cs.
  Proof.
    Hint Constructors exp_eval.
    intros h s cs. induction cs; constructor; eauto.
  Qed.

  (* =stmt_eval= *)
  Inductive stmt_eval :
    program -> heap -> stack -> stmt -> heap * stack -> Prop :=
  | Iassign: forall prog menv env x e v env',
      exp_eval menv env e v ->
      PM.add x v env = env' ->
      stmt_eval prog menv env (Assign x e) (menv, env')
  | (*...*)
  (* =end= *)
  Iassignst:
    forall prog menv env x e v menv',
      exp_eval menv env e v ->
      madd_mem x v menv = menv' ->
      stmt_eval prog menv env (AssignSt x e) (menv', env)
  (* =stmt_eval:step= *)
  | Istep: forall prog menv env es vs clsid o y menv' env' omenv omenv' rv,
      mfind_inst o menv = Some(omenv) ->
      Nelist.Forall2 (exp_eval menv env) es vs ->
      stmt_step_eval prog omenv clsid vs omenv' rv ->
      madd_obj o omenv' menv = menv' ->
      PM.add y rv env  = env' ->
      stmt_eval prog menv env (Step_ap y clsid o es) (menv', env')
  | (*...*)
  (* =end= *)
  Ireset:
    forall prog menv env o clsid omenv' menv',
      stmt_reset_eval prog clsid omenv' ->
      madd_obj o omenv' menv = menv' ->
      stmt_eval prog menv env (Reset_ap clsid o) (menv', env)
  | Icomp:
      forall prog menv env a1 a2 env1 menv1 env2 menv2,
        stmt_eval prog menv env a1 (menv1, env1) ->
        stmt_eval prog menv1 env1 a2 (menv2, env2) ->
        stmt_eval prog menv env (Comp a1 a2) (menv2, env2)
   | Iifte:
      forall prog menv env cond b ifTrue ifFalse env' menv',
        exp_eval menv env cond (Vbool b) ->
        stmt_eval prog menv env (if b then ifTrue else ifFalse) (menv', env') -> 
        stmt_eval prog menv env (Ifte cond ifTrue ifFalse) (menv', env')
  | Iskip:
      forall prog menv env,
        stmt_eval prog menv env Skip (menv, env)
  (* =stmt_step_eval= *)
  with stmt_step_eval :
         program -> heap -> ident -> nelist val -> heap -> val -> Prop :=
       | Iestep:
           forall prog menv env clsid ivs prog' menv' ov cls env',
             find_class clsid prog = Some(cls, prog') ->
             env = adds cls.(c_input) ivs sempty ->
             stmt_eval prog' menv env cls.(c_step)
                                            (menv', env') ->
             PM.find cls.(c_output) env' = Some(ov) ->
             stmt_step_eval prog menv clsid ivs menv' ov
  (* =end= *)

  with stmt_reset_eval : program -> ident -> heap -> Prop :=
       | Iereset:
           forall prog clsid cls prog' menv' env',
             find_class clsid prog = Some(cls, prog') ->
             stmt_eval prog' hempty sempty cls.(c_reset) (menv', env') ->
             stmt_reset_eval prog clsid menv'.

  Scheme stmt_eval_mult := Induction for stmt_eval Sort Prop
                           with stmt_step_eval_mult := Induction for stmt_step_eval Sort Prop
                                                       with stmt_reset_eval_mult := Induction for stmt_reset_eval Sort Prop.

  (** ** Determinism of semantics *)

  Theorem exp_eval_det:
    forall menv env e v1 v2,
      exp_eval menv env e v1 ->
      exp_eval menv env e v2 ->
      v1 = v2.
  Proof.
    induction e (* using exp_ind2 *);
    intros v1 v2 H1 H2;
    inversion H1 as [xa va tya Hv1|xa va tya Hv1|xa va tya Hv1
                     |opa ea ca va tya IHa Hv1|opa e1a e2a c1a c2a va tya IH1a IH2a Hv1];
    inversion H2 as [xb vb tyb Hv2|xb vb tyb Hv2|xb vb tyb Hv2
                     |opb eb cb vb tyb IHb Hv2|opb e1b e2b c1b c2b vb tyb IH1b IH2b Hv2];
    try (rewrite Hv1 in Hv2; (injection Hv2; trivial) || apply Hv2); subst.
    - pose proof (IHe ca cb IHa IHb); subst.
      now rewrite Hv1 in Hv2; injection Hv2.
    - pose proof (IHe1 c1a c1b IH1a IH1b); pose proof (IHe2 c2a c2b IH2a IH2b); subst.
      now rewrite Hv1 in Hv2; injection Hv2.
  Qed.

  Theorem stmt_eval_fold_left_shift:
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

  Theorem exp_evals_det:
    forall menv env es vs1 vs2,
      Nelist.Forall2 (exp_eval menv env) es vs1 ->
      Nelist.Forall2 (exp_eval menv env) es vs2 ->
      vs1 = vs2.
  Proof.
    intros menv env es vs1 vs2 H1; generalize dependent vs2.
    induction H1 as [|e1 c1 es1 cs1]; intros vs2 H2;
    inversion_clear H2 as [|e2 c2 es2 cs2].
    - f_equal. eauto using exp_eval_det.
    - assert (c1 = c2) by eauto using exp_eval_det.
      assert (cs1 = cs2) by eauto using IHForall2.
      congruence.
  Qed.

  Theorem stmt_eval_det:
    forall prog s menv env renv1 renv2,
      stmt_eval prog menv env s renv1
      -> stmt_eval prog menv env s renv2
      -> renv1 = renv2.
  Proof.
    intros prog s menv env renv1 renv2 Hs1.
    revert renv2.
    induction Hs1 using stmt_eval_mult
    with (P:=fun prog menv env s renv1 sev=>
               forall renv2, stmt_eval prog menv env s renv2 -> renv1 = renv2)
           (P0:=fun prog menv clsid v menv' rv ssev=>
                  forall menv'' rv', stmt_step_eval prog menv clsid v menv'' rv'
                                -> menv' = menv'' /\ rv = rv')
           (P1:=fun prog i menv srev=>
                  forall menv', stmt_reset_eval prog i menv' -> menv = menv');
      inversion_clear 1;
    repeat progress match goal with
                      | b: bool |- _ => destruct b
                      | H: ?env = adds _ _ _ |- _ => subst env
                      | Ht: exp_eval ?menv ?env ?e (Vbool true),
                            Hf: exp_eval ?menv ?env ?e (Vbool false) |- _ =>
                        pose proof (exp_eval_det _ _ _ _ _ Ht Hf) as Hneq; discriminate
                      | H1:exp_eval ?menv ?env ?e ?v1,
                           H2:exp_eval ?menv ?env ?e ?v2 |- _ =>
                        pose proof (exp_eval_det _ _ _ _ _ H1 H2) as Heq;
                          rewrite Heq in *; clear Heq H1 H2
                      | H1: Nelist.Forall2 (exp_eval ?menv ?env) ?es ?vs1,
                            H2: Nelist.Forall2 (exp_eval ?menv ?env) ?es ?vs2 |- _ =>
                        pose proof (exp_evals_det _ _ _ _ _ H1 H2) as Heq;
                          rewrite Heq in *; clear Heq H1 H2
                      | H1: PM.add ?x ?v ?env = ?env1,
                            H2: PM.add ?x ?v ?env = ?env2 |- _ =>
                        rewrite H1 in H2; rewrite H2 in *; clear H1 H2
                      | H1: madd_mem ?x ?v ?menv = ?menv1,
                            H2: madd_mem ?x ?v ?menv = ?menv2 |- _ =>
                        rewrite H1 in H2; rewrite H2 in *; clear H1 H2
                      | H1: mfind_inst ?o ?menv = Some ?omenv1,
                            H2: mfind_inst ?o ?menv = Some ?omenv2 |- _ =>
                        rewrite H1 in H2; injection H2; intro Heq; rewrite Heq in *;
                        clear H1 H2 Heq
                      | H1: find_class ?clsid ?prog = _,
                            H2: find_class ?clsid ?prog = _ |- _ =>
                        rewrite H1 in H2; injection H2;
                        intros Heq1 Heq2; rewrite Heq1, Heq2 in *; clear H2 H2 Heq1 Heq2
                      | H1: PM.find ?x ?env = ?rv1,
                            H2: PM.find ?x ?env = ?rv2 |- _ =>
                        rewrite H1 in H2; injection H2; rewrite H2 in *; clear H1 H2
                      | Hs: stmt_step_eval ?prog ?omenv ?clsid ?v _ _,
                            IH: context[stmt_step_eval ?prog ?omenv ?clsid ?v _ _ -> _ = _ /\ _ = _]
                        |- _ =>
                        apply IH in Hs; destruct Hs as [Heq1 Heq2]; try rewrite Heq1 in *;
                        try rewrite Heq2 in *; clear Heq1 Heq2
                      | Hs: stmt_reset_eval ?prog ?clsid _,
                            IH: context[stmt_reset_eval ?prog ?clsid _ -> _ = _] |- _ =>
                        apply IH in Hs; try rewrite Hs in *; clear Hs
                      | Hs: stmt_eval ?prog ?menv ?env ?stmt _,
                            IH: context[stmt_eval ?prog ?menv ?env ?stmt _ -> (_, _) = _] |- _ =>
                        apply IH in Hs; injection Hs; intros Heq1 Heq2;
                        try rewrite Heq1 in *; try rewrite Heq2 in *; clear Heq1 Heq2 Hs
                      | H1: madd_obj ?o ?omenv ?menv = ?menv1,
                            H2: madd_obj ?o ?omenv ?menv = ?menv2 |- _ =>
                        rewrite H1 in H2; rewrite H2 in *; clear H1 H2
                      | _ => intuition
                      end.
  Qed.
  
End SemanticsFun'.
Module SemanticsFun <: SEMANTICS := SemanticsFun'.