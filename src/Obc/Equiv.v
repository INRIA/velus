Require Import Coq.FSets.FMapPositive.
Require Import PArith.
Require Import Velus.Common.Common.
Require Import Velus.Environment.
Require Import Velus.Operators.
Require Import Velus.Obc.ObcSyntax.
Require Import Velus.Obc.ObcSemantics.
Require Import Velus.Obc.ObcTyping.

Require Import Relations.
Require Import Morphisms.
Require Import Setoid.

Import List.

(** * Equivalence of Obc programs *)

(**

To prove the soundness of the if-then-else fusing optimization, we
define (and prove some properties about) equivalence of Obc
programs.

 *)
Module Type EQUIV
       (Ids          : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX    Op)
       (Import Syn   : OBCSYNTAX    Ids Op OpAux)
       (Import Sem   : OBCSEMANTICS Ids Op OpAux Syn)
       (Import Typ   : OBCTYPING    Ids Op OpAux Syn Sem).

  Definition stmt_eval_eq s1 s2: Prop :=
    forall prog menv env menv' env',
      stmt_eval prog menv env s1 (menv', env')
      <->
      stmt_eval prog menv env s2 (menv', env').

  Lemma stmt_eval_eq_refl:
    reflexive stmt stmt_eval_eq.
  Proof. now apply iff_refl. Qed.

  Lemma stmt_eval_eq_sym:
    symmetric stmt stmt_eval_eq.
  Proof.
    intros s1 s2 Heq prog menv env menv' env'.
    split; apply Heq.
  Qed.

  Lemma stmt_eval_eq_trans:
    transitive stmt stmt_eval_eq.
  Proof.
    intros s1 s2 s3 Heq1 Heq2 prog menv env menv' env'.
    split; intro HH; [apply Heq2, Heq1|apply Heq1, Heq2]; exact HH.
  Qed.

  Add Relation stmt (stmt_eval_eq)
      reflexivity proved by stmt_eval_eq_refl
      symmetry proved by stmt_eval_eq_sym
      transitivity proved by stmt_eval_eq_trans
        as stmt_eval_equiv.

  Instance stmt_eval_eq_Proper:
    Proper (eq ==> eq ==> eq ==> stmt_eval_eq ==> eq ==> iff) stmt_eval.
  Proof.
    intros prog' prog HR1 menv' menv HR2 env' env HR3 s1 s2 Heq r' r HR4;
    subst; destruct r as [menv' env'].
    now apply Heq.
  Qed.

  Instance stmt_eval_eq_Comp_Proper:
    Proper (stmt_eval_eq ==> stmt_eval_eq ==> stmt_eval_eq) Comp.
  Proof.
    intros s s' Hseq t t' Hteq prog menv env menv' env'.
    split; inversion_clear 1;
    [rewrite Hseq, Hteq in *; econstructor; eassumption
    |rewrite <-Hseq, <-Hteq in *; econstructor; eassumption].
  Qed.

  Lemma Comp_assoc:
    forall s1 s2 s3,
      stmt_eval_eq (Comp s1 (Comp s2 s3)) (Comp (Comp s1 s2) s3).
  Proof.
    intros prog s1 s2 s3 menv env menv' env'.
    split;
      intro HH;
      repeat progress
             match goal with
             | H:stmt_eval _ _ _ (Comp _ _) _ |- _ => inversion H; subst; clear H
             | |- _ => repeat econstructor; now eassumption
             end.
  Qed.

  Lemma stmt_eval_eq_Comp_Skip1:
    forall s, stmt_eval_eq (Comp Skip s) s.
  Proof.
    split; eauto using stmt_eval.
    inversion_clear 1; now chase_skip.
  Qed.

  Lemma stmt_eval_eq_Comp_Skip2:
    forall s, stmt_eval_eq (Comp s Skip) s.
  Proof.
    split; eauto using stmt_eval.
    inversion_clear 1; now chase_skip.
  Qed.

  Instance stmt_eval_eq_Ifte_Proper:
    Proper (eq ==> stmt_eval_eq ==> stmt_eval_eq ==> stmt_eval_eq) Ifte.
  Proof.
    intros e e' Heeq s s' Hseq t t' Hteq prog menv env menv' env'.
    rewrite <-Heeq.
    split; inversion_clear 1;
      destruct b;
      try match goal with
          | H: exp_eval _ _ _ _ |- _ => apply Iifte with (1:=H)
          | H: stmt_eval _ _ _ _ _ |- _ =>
            (rewrite <-Hseq in H
             || rewrite <-Hteq in H
             || rewrite Hseq in H
                                || rewrite Hteq in H)
          end;
      try match goal with
          | H:val_to_bool ?v = Some true |- _ =>
            apply val_to_bool_true' in H
          | H:val_to_bool ?v = Some false |- _ =>
            apply val_to_bool_false' in H
          end; subst;
        econstructor; try eassumption;
          try apply val_to_bool_true;
          try apply val_to_bool_false';
          easy.
  Qed.

  (** A refinement relation for Obc.
      Refining programs are allowed to replace [None] by any value. *)

    (* If an environment env1 <refines> env2, it should be possible to use
     env1 instead of env2. *)

  Definition env_refines (env1 env2 : Env.t val) : Prop :=
    forall x v, Env.find x env2 = Some v -> Env.find x env1 = Some v.

  Lemma env_refines_empty:
    forall env, env_refines env vempty.
  Proof.
    intros env x v Hfind. now rewrite Env.gempty in Hfind.
  Qed.

  Lemma env_refines_refl:
    reflexive _ env_refines.
  Proof. now intros env x v. Qed.

  Lemma env_refines_trans:
    transitive _ env_refines.
  Proof.
    intros env1 env2 env3 H1 H2 x v Hfind.
    now apply H2, H1 in Hfind.
  Qed.

  Add Relation _ env_refines
      reflexivity proved by env_refines_refl
      transitivity proved by env_refines_trans
        as env_refines_preorder.

  Lemma exp_eval_refines:
    forall menv' env1 env2 e v,
      env_refines env1 env2 ->
      exp_eval menv' env2 e (Some v) ->
      exp_eval menv' env1 e (Some v).
  Proof.
    intros menv' env1 env2.
    induction e; intros v Henv; inversion 1; subst; eauto using exp_eval.
  Qed.

  Lemma exp_eval_refines':
    forall menv env1 env2 e vo,
      env_refines env1 env2 ->
      exp_eval menv env2 e vo ->
      exists vo',
        exp_eval menv env1 e vo' /\ (forall v, vo = Some v -> vo' = Some v).
  Proof.
    intros menv env1 env2.
    induction e; intros vo Henv; inversion 1; subst;
      eauto using exp_eval, exp_eval_refines.
  Qed.

  Lemma Forall2_exp_eval_refines':
    forall menv env1 env2 es vos,
      env_refines env1 env2 ->
      Forall2 (exp_eval menv env2) es vos ->
      exists vos',
        Forall2 (exp_eval menv env1) es vos'
        /\ Forall2 (fun vo vo' => forall v, vo = Some v -> vo' = Some v) vos vos'.
  Proof.
    intros menv env1 env2 es vos Henv Hvos.
    induction Hvos; eauto.
    apply exp_eval_refines' with (1:=Henv) in H.
    destruct H as (vo' & Heval & Hvo').
    destruct IHHvos as (vos' & Hevals & Hvos').
    eauto using Forall2_cons.
  Qed.

  Lemma env_refines_add:
    forall env1 env2 x v,
      env_refines env1 env2 ->
      env_refines (Env.add x v env1) (Env.add x v env2).
  Proof.
    intros env1 env2 x v Henv y vy Hfind.
    destruct (ident_eq_dec x y).
    - now subst; rewrite Env.gss in *.
    - rewrite Env.gso in *; auto.
  Qed.

  Lemma env_refines_add_left:
    forall env1 env2 x v,
      env_refines env1 env2 ->
      ~ Env.In x env2 ->
      env_refines (Env.add x v env1) env2.
  Proof.
    intros env1 env2 x vx Henv Hnin y vy Hfind.
    destruct (ident_eq_dec x y); subst.
    rewrite Env.In_find in Hnin; exfalso; apply Hnin; eauto.
    rewrite Env.gso; auto.
  Qed.

  Lemma env_refines_remove:
    forall env1 env2 x,
      env_refines env1 env2 ->
      env_refines (Env.remove x env1) (Env.remove x env2).
  Proof.
    intros env1 env2 x Henv y v Hfind.
    destruct (ident_eq_dec x y).
    - now subst; rewrite Env.grs in *.
    - rewrite Env.gro in *; auto.
  Qed.

  Lemma env_refines_add_remove:
    forall env1 env2 x v,
      env_refines env1 env2 ->
      env_refines (Env.add x v env1) (Env.remove x env2).
  Proof.
    intros env1 env2 x v Henv y vy Hfind.
    destruct (ident_eq_dec x y).
    - now subst; rewrite Env.grs in Hfind.
    - rewrite Env.gro in Hfind; auto.
      rewrite Env.gso; auto.
  Qed.

  Instance env_refines_Proper:
    Proper (Basics.flip env_refines ==> env_refines ==> Basics.impl) env_refines.
  Proof.
    intros m1 m1' Henv1 m2 m2' Henv2.
    intros Henv x v Hfind.
    now apply Henv2, Henv, Henv1 in Hfind.
  Qed.

  Instance env_refines_Equal_Proper:
    Proper (@Env.Equal _ ==> @Env.Equal _ ==> iff) env_refines.
  Proof.
    intros m1 m1' Heq1 m2 m2' Heq2.
    split; intros Henv x v Hfind.
    - rewrite <-Heq2 in Hfind. apply Henv in Hfind.
      now rewrite Heq1 in Hfind.
    - rewrite Heq2 in Hfind. apply Henv in Hfind.
      now rewrite <-Heq1 in Hfind.
  Qed.

  Instance add_env_refines_Proper:
    Proper (@eq ident ==> @eq val ==> env_refines ==> env_refines) (@Env.add val).
  Proof.
    intros x y Hxy vx vy Hv m1 m2 Henv.
    subst. now apply env_refines_add.
  Qed.

  Lemma updates_refines:
    forall ys env' env rvos' rvos,
      env_refines env' env ->
      Forall2 (fun vo1 vo2 => forall v, vo2 = Some v -> vo1 = Some v) rvos' rvos ->
      env_refines (Env.updates ys rvos' env') (Env.updates ys rvos env).
  Proof.
    induction ys as [|y ys]. now auto.
    intros env' env rvos' rvos Henv Hrvos.
    inversion_clear Hrvos as [|rv' rv rvs' rvs Hv Hrvs]; subst. now auto.
    setoid_rewrite Env.updates_cons_cons.
    destruct rv' as [rv'|], rv as [rv|].
    - specialize (Hv rv eq_refl); inv Hv.
      apply env_refines_add. now apply IHys.
    - apply env_refines_add_remove. now apply IHys.
    - now specialize (Hv rv eq_refl).
    - apply env_refines_remove. now apply IHys.
  Qed.

  Lemma env_refines_adds_opt:
    forall xs m1 m2 vos1 vos2,
      env_refines m1 m2 ->
      Forall2 (fun vo1 vo2 => forall v, vo2 = Some v -> vo1 = Some v) vos1 vos2 ->
      NoDup xs ->
      Forall (fun x => ~Env.In x m1 /\ ~Env.In x m2) xs ->
      env_refines (Env.adds_opt xs vos1 m1) (Env.adds_opt xs vos2 m2).
  Proof.
    induction xs as [|x xs]; induction 2 as [|vo1 vo2 vos1 vos2 Hvo Hvos]; auto.
    inversion_clear 1 as [|? ? Hnxs Hndup].
    rewrite Forall_cons2. destruct 1 as ((Hnin1 & Hnin2) & Hnin).
    destruct vo1, vo2.
    - specialize (Hvo v0 eq_refl); inv Hvo.
      setoid_rewrite Env.adds_opt_cons_cons.
      auto using env_refines_add.
    - setoid_rewrite Env.adds_opt_cons_cons'; auto.
      setoid_rewrite Env.adds_opt_cons_cons_None.
      apply IHxs; auto.
      now apply env_refines_add_left.
      apply Forall_impl_In with (2:=Hnin).
      intros y Hyin (Hyn1 & Hyn2). split; auto.
      rewrite Env.Props.P.F.add_in_iff. destruct 1 as [HH|HH]; subst; auto.
    - now specialize (Hvo v eq_refl).
    - setoid_rewrite Env.adds_opt_cons_cons_None; auto.
  Qed.

  (* If a statement s' refines s, it should be possible to use s' instead
     of s. *)

  Definition stmt_refines prog1 prog2 P s1 s2 : Prop :=
    forall menv env1 env2 menv' env2',
      P env1 env2 ->
      env_refines env1 env2 ->
      stmt_eval prog2 menv env2 s2 (menv', env2') ->
      (exists env1',
          env_refines env1' env2'
          /\ stmt_eval prog1 menv env1 s1 (menv', env1')).

  Definition method_refines prog1 prog2 P m1 m2 : Prop :=
    m1.(m_in) = m2.(m_in)
    /\ m1.(m_out) = m2.(m_out)
    /\ stmt_refines prog1 prog2 (P m1.(m_in)) m1.(m_body) m2.(m_body).

  Definition class_refines prog1 prog2 P c1 c2 : Prop :=
    forall f m2,
      find_method f c2.(c_methods) = Some m2 ->
      exists m1,
        find_method f c1.(c_methods) = Some m1
        /\ method_refines prog1 prog2 (P f) m1 m2.

  Definition program_refines
             (P : ident -> ident -> list (ident * type)
                  -> Env.t val -> Env.t val -> Prop)
             (prog1 prog2 : program) : Prop :=
    (PFix ltsuffix2_wf
          (fun (progs : program * program)
               (program_refines :
                  (forall (progs' : program * program),
                      ltsuffix2 progs' progs -> Prop)) =>
             forall n c2 prog2'
                    (Hf2: find_class n (snd progs) = Some (c2, prog2')),
             exists (c1 : class) (prog1' : program)
                    (Hf1: find_class n (fst progs) = Some (c1, prog1')),
               class_refines prog1' prog2' (P n) c1 c2
               /\ program_refines (prog1', prog2')
                                  (conj (find_class_ltsuffix n (fst progs) c1 prog1' Hf1)
                                        (find_class_ltsuffix n (snd progs) c2 prog2' Hf2))
    )) (prog1, prog2).

  Lemma program_refines_def:
    forall (P : ident -> ident -> list (ident * type)
                -> Env.t val -> Env.t val -> Prop) prog1 prog2,
      program_refines P prog1 prog2 <->
      (forall n c2 prog2',
          find_class n prog2 = Some (c2, prog2') ->
          exists (c1 : class) (prog1' : program),
            find_class n prog1 = Some (c1, prog1')
            /\ class_refines prog1' prog2' (P n) c1 c2
            /\ program_refines P prog1' prog2').
  Proof.
    intros.
    unfold program_refines at 1.
    rewrite PFix_eq.
    - split; intros HH n c2 prog2' Hfind;
        destruct (HH n c2 prog2' Hfind) as (c1' & prog1' & Hfind' & Hcr & Hfix);
        eauto.
    - intros * H. now setoid_rewrite H.
  Qed.

  (* TODO: Try an alternative definition of program_refines based on
           [stmt_call_eval]?

           Advantages:
           - simplicity
           - ability to add a precondition on input arguments
             (but maybe the only interesting precondition is that
              all the input arguments are not None, unless the
              predicate is also over the class name, method name,
              and input names).

           Disadvantages:
           - harder to work with since it's less syntactic?

        P vos1 vos2 ->
        stmt_call_eval p2 omenv clsid f vos2 omenv' rvos2 ->
        exists rvos1,
          stmt_call_eval p1 omenv clsid f vos1 omenv' rvos1
          /\ Forall2 (fun rv1 rv2 => forall v, rv2 = Some v => rv1 = Some v)
                     rvos1 rvos2
   *)

  Lemma statement_refines_pre:
    forall (P Q : ident -> ident -> list (ident * type)
                  -> Env.t val -> Env.t val -> Prop) p1 p2 s1 s2,
      (forall c m mins env1 env2, Q c m mins env1 env2 -> P c m mins env1 env2) ->
      forall n f mins,
        stmt_refines p1 p2 (P n f mins) s1 s2 ->
        stmt_refines p1 p2 (Q n f mins) s1 s2.
  Proof.
    intros P Q p1 p2 s1 s2 HPQ n f mins Hsr.
    intros menv env1 env2 menv' env2' HQ Henv Heval.
    unfold stmt_refines in Hsr.
    apply Hsr with (2:=Henv) in Heval; auto.
  Qed.

  Lemma method_refines_pre:
    forall (P Q : ident -> ident -> list (ident * type)
                  -> Env.t val -> Env.t val -> Prop) p1 p2 m1 m2,
      (forall c m min env1 env2, Q c m min env1 env2 -> P c m min env1 env2) ->
      forall n f,
        method_refines p1 p2 (P n f) m1 m2 ->
        method_refines p1 p2 (Q n f) m1 m2.
  Proof.
    intros P Q p1 p2 m1 m2 HPQ n f (Hmr1 & Hmr2 & Hmr3).
    repeat split; auto.
    now apply statement_refines_pre with (1:=HPQ).
  Qed.

  Lemma class_refines_pre:
    forall (P Q : ident -> ident -> list (ident * type)
                  -> Env.t val -> Env.t val -> Prop) p1 p2 c1 c2,
      (forall c m min env1 env2, Q c m min env1 env2 -> P c m min env1 env2) ->
      forall n,
        class_refines p1 p2 (P n) c1 c2 ->
        class_refines p1 p2 (Q n) c1 c2.
  Proof.
    intros P Q p1 p2 c1 c2 HPQ n Hcr f m2 Hfind2.
    apply Hcr in Hfind2 as (m1 & Hfind1 & Hmr).
    exists m1. split; auto.
    now apply method_refines_pre with (1:=HPQ).
  Qed.

  Lemma program_refines_pre:
    forall (P Q : ident -> ident -> list (ident * type)
                  -> Env.t val -> Env.t val -> Prop) p1 p2,
      (forall c m min env1 env2, Q c m min env1 env2 -> P c m min env1 env2) ->
      program_refines P p1 p2 ->
      program_refines Q p1 p2.
  Proof.
    intros P Q p1 p2 HPQ.
    set (p := (p1, p2)).
    assert (p1 = fst p) as Hp1 by auto.
    assert (p2 = snd p) as Hp2 by auto.
    rewrite Hp1, Hp2; clear Hp1 Hp2; generalize p; clear p p1 p2.
    induction p as [(p1, p2) IH] using (well_founded_ind ltsuffix2_wf).
    simpl; intros Hpr.
    rewrite program_refines_def.
    rewrite program_refines_def in Hpr.
    intros n c2 p2' Hfind.
    specialize (Hpr _ _ _ Hfind).
    destruct Hpr as (c1 & p1' & Hfind' & Hcr & Hpr').
    apply (IH (p1', p2')) in Hpr'; eauto using find_class_ltsuffix2.
    exists c1, p1'. repeat split; auto.
    now apply class_refines_pre with (1:=HPQ).
  Qed.

  (* This basic property of stmt_refines has an important consequence:
     executing a statement in a refined environment (program and env with
     menv the same) produces a refined environment (env' with menv' the
     same).

     An intrinsic property of Obc is that executing a program in a
     refined initial environment gives a refined final environment.

     The reason: if a statement has a semantics in a given initial
     environment, then it still has a semantics when more variables
     are defined, and a program only has a semantics if it does not
     depend on undefined ('None') values. Undefined values can be
     passed into and out of method calls, but they cannot otherwise be
     used.

     The form of ObcSemantics is crucial here; notably the use of
     [adds] and [updates] for function calls, and the fact that
     assignments only apply to defined values.

   *)

  Theorem stmt_refines_refl:
    forall (P : Env.t val -> Env.t val -> Prop) p1 p2,
      (forall env1 env2, env_refines env1 env2 -> P env1 env2) ->
      program_refines (fun c m mins => P) p1 p2 ->
      reflexive _ (stmt_refines p1 p2 P).
  Proof.
    intros P prog1 prog2 HPref Hpr s menv env1 env2 menv' env2' Hpre Henv Heval.
    clear Hpre; revert prog1 Hpr env1 Henv.
    (* TODO: reformulate stmt_eval to uncurry the final pair or tweak the
       induction principle for stmt_eval? *)
    remember (menv', env2') as rr.
    assert (menv' = fst rr /\ env2' = snd rr) as (HR1 & HR2) by (subst; auto).
    rewrite HR1, HR2; clear Heqrr HR1 HR2 menv' env2'.
    induction Heval using stmt_eval_ind_2
      with (P0 := fun prog2 omenv clsid f vos omenv' rvos =>
                    forall prog1 vos',
                      program_refines (fun c m mins => P) prog1 prog2 ->
                      Forall2 (fun vo vo' => forall v, vo = Some v -> vo' = Some v) vos vos' ->
                      exists rvos',
                        stmt_call_eval prog1 omenv clsid f vos' omenv' rvos'
                        /\  Forall2 (fun vo' vo => forall v, vo = Some v -> vo' = Some v) rvos' rvos);
      intros prog1; eauto using stmt_eval.
    - (* Assign x e *)
      intros Hpr env1 Henv. exists (Env.add x v env1).
      subst; eauto using env_refines_add, stmt_eval, exp_eval_refines.
    - (* AssignSt x e *)
      intros Hpr env1 Henv. subst; eauto using exp_eval_refines, stmt_eval.
    - (* Call ys clsid o f es *)
      intros Hpr env1 Henv.
      match goal with H:Forall2 (exp_eval _ _) _ _ |- _ =>
                      apply Forall2_exp_eval_refines' with (1:=Henv) in H;
                        destruct H as (vos' & Heval1 & Hvos)
      end.
      destruct (IHHeval _ _ Hpr Hvos) as (rvos' & Hcall1 & Hrvos').
      subst; eauto using updates_refines, stmt_eval.
    - (* Comp s1 s2 *)
      intros Hpr env' Henv1.
      destruct (IHHeval1 _ Hpr _ Henv1) as (env1' & Henv2 & Heval1').
      destruct (IHHeval2 _ Hpr _ Henv2) as (env1'' & Henv3 & Heval2').
      eauto using stmt_eval.
    - (* Ifte c et ef *)
      intros Hpr env1 Henv.
      destruct (IHHeval _ Hpr _ Henv) as (env1' & Henv' & Hs1).
      eauto using exp_eval_refines, stmt_eval.
    - (* stmt_call_eval *)
      intros vos' Hpr Hvos'.
      clear IHHeval (* use program_refines2 *).
      rewrite program_refines_def in Hpr.
      match goal with Hc:find_class _ _ = _, Hm:find_method _ _ = _ |- _ =>
                      destruct (Hpr _ _ _ Hc) as (c1 & prog1' & Hfindc1 & Hcr & Hpr');
                        destruct (Hcr _ _ Hm) as (m1 & Hfindm1 & (Hm1in & Hm1out & Hm1r))
      end.
      apply (Hm1r _ (Env.adds_opt (map fst m1.(m_in)) vos' vempty)) in Heval; auto.
      + (* P0: obligation of induction *)
        destruct Heval as (env1' & Henv & Hmeval2).
        exists (map (fun x => Env.find x env1') (map fst m1.(m_out))).
        split.
        * econstructor; eauto.
          now apply Forall2_length in Hvos'; rewrite Hm1in, <-Hvos'.
          now apply Forall2_map_2, Forall2_same, Forall_forall; auto.
        * rewrite Hm1out.
          match goal with H:Forall2 _ _ rvos |- _ =>
                          apply Forall2_map_1, Forall2_impl_In with (2:=H) end.
          intros; subst; auto.
      + (* P (adds ...) (adds ...) *)
        rewrite Hm1in. apply HPref.
        pose proof (m_nodupvars fm) as Hnodup.
        unfold vempty. apply env_refines_adds_opt; auto using env_refines_empty.
        * now apply Forall2_swap_args.
        * now apply NoDupMembers_app_l, fst_NoDupMembers in Hnodup.
        * apply Forall_forall; split; rewrite Env.Props.P.F.empty_in_iff; auto.
      + (* env_refines (adds ...) (adds ...) *)
        rewrite Hm1in.
        apply Forall2_swap_args in Hvos'.
        apply env_refines_adds_opt; auto using (env_refines_empty vempty).
        * apply fst_NoDupMembers, m_nodupin.
        * apply Forall_forall; split;  rewrite Env.Props.P.F.empty_in_iff; auto.
  Qed.

  Lemma method_refines_refl:
    forall (P : list (ident * type) -> Env.t val -> Env.t val -> Prop) p1 p2,
      (forall xs env1 env2, env_refines env1 env2 -> P xs env1 env2) ->
      program_refines (fun c m min env1 env2 => exists xs, P xs env1 env2) p1 p2 ->
      reflexive _ (method_refines p1 p2 P).
  Proof.
    repeat split; auto.
    apply stmt_refines_refl; auto.
    eapply program_refines_pre; eauto.
    simpl; intros; eauto.
  Qed.

  Lemma class_refines_refl:
    forall (P : ident -> list (ident * type) -> Env.t val -> Env.t val -> Prop) p1 p2,
      (forall m xs env1 env2, env_refines env1 env2 -> P m xs env1 env2) ->
      program_refines (fun c m min env1 env2 => exists m xs, P m xs env1 env2) p1 p2 ->
      reflexive _ (class_refines p1 p2 P).
  Proof.
    eexists; split; eauto.
    apply method_refines_refl; auto.
    eapply program_refines_pre; eauto.
    simpl; intros; eauto.
  Qed.

  Lemma program_refines_refl:
    forall (P : ident -> ident -> list (ident * type) -> Env.t val -> Env.t val -> Prop),
      (forall c m xs env1 env2, env_refines env1 env2 -> P c m xs env1 env2) ->
      (forall n env1 env2 m xs, P n m xs env1 env2 ->
                                forall n' m' xs', P n' m' xs' env1 env2) ->
      reflexive _ (program_refines P).
  Proof.
    intros P HP1 HP2 p; change (program_refines P (fst (p, p)) (snd (p, p))).
    pose proof (eq_refl : fst (p, p) = snd (p, p)). revert H.
    generalize (p, p); clear p.
    induction p as [(p1, p2) IH] using (well_founded_ind ltsuffix2_wf).
    simpl; intro Heq; subst p2.
    rewrite program_refines_def.
    intros n c1 p1' Hfind.
    exists c1, p1'. split; auto.
    cut (program_refines P p1' p1').
    - split; auto. apply class_refines_refl; auto.
      eapply program_refines_pre; eauto.
      intros c m min env1 env2 (m' & xs' & HP); auto.
      apply HP2 with (1:=HP).
    - apply (IH (p1', p1')); eauto using find_class_ltsuffix2.
  Qed.

  Lemma stmt_refines_trans:
    forall P, (forall x y, P x y -> P x x) ->
              forall p1 p2 p3 s1 s2 s3,
                stmt_refines p1 p2 P s1 s2 ->
                stmt_refines p2 p3 P s2 s3 ->
                stmt_refines p1 p3 P s1 s3.
  Proof.
    intros P HP p1 p2 p3 s1 s2 s3 Hs12 Hs23.
    intros menv env1 env3 menv' env3' P13 Henv13 Heval3.
    unfold stmt_refines in *.
    apply Hs23 with (1:=P13) (2:=Henv13) in Heval3 as (env2' & Henv23' & Heval2).
    eapply Hs12 in Heval2. 3:reflexivity.
    destruct Heval2 as (env1' & Henv12' & Heval1);
      eauto using env_refines_trans.
    apply HP with (1:=P13).
  Qed.

  Lemma method_refines_trans:
    forall P, (forall m x y, P m x y -> P m x x) ->
              forall p1 p2 p3 m1 m2 m3,
                method_refines p1 p2 P m1 m2 ->
                method_refines p2 p3 P m2 m3 ->
                method_refines p1 p3 P m1 m3.
  Proof.
    intros P HP p1 p2 p3 m1 m2 m3
           (Hmin12 & Hmout12 & Hm12) (Hmin23 & Hmout23 & Hm23).
    unfold method_refines.
    rewrite Hmin12, Hmin23, Hmout12, Hmout23.
    repeat split; auto. rewrite <-Hmin23. rewrite Hmin12 in Hm12.
    eapply stmt_refines_trans with (2:=Hm12) in Hm23; eauto.
  Qed.

  Lemma class_refines_trans:
    forall P, (forall f m x y, P f m x y -> P f m x x) ->
              forall p1 p2 p3 c1 c2 c3,
                class_refines p1 p2 P c1 c2 ->
                class_refines p2 p3 P c2 c3 ->
                class_refines p1 p3 P c1 c3.
  Proof.
    intros P HP p1 p2 p3 c1 c2 c3 Hcr12 Hcr23.
    intros f m3 Hfind3.
    apply Hcr23 in Hfind3.
    destruct Hfind3 as (m2 & Hfind2 & Hmr23).
    apply Hcr12 in Hfind2.
    destruct Hfind2 as (m1 & Hfind1 & Hmr12).
    apply method_refines_trans with (2:=Hmr12) in Hmr23; eauto.
  Qed.

  Lemma program_refines_ind:
    forall (Pre : ident -> ident -> list (ident * type)
                  -> Env.t val -> Env.t val -> Prop)
           P,
      (forall p1 p2,
          (forall p2' n c2,
              find_class n p2 = Some (c2, p2') ->
              exists c1 p1',
                find_class n p1 = Some (c1, p1')
                /\ class_refines p1' p2' (Pre n) c1 c2
                /\ program_refines Pre p1' p2'
                /\ P p1' p2') -> P p1 p2) ->
      forall p1 p2, program_refines Pre p1 p2 -> P p1 p2.
  Proof.
    intros Pre P IH p1 p2.
    change (program_refines Pre (fst (p1, p2)) (snd (p1, p2)) ->
            P (fst (p1, p2)) (snd (p1, p2))).
    generalize (p1, p2); clear p1 p2.
    intros p Hpr. revert Hpr.
    apply (@well_founded_ind (program * program) _ ltsuffix2_wf) with (a:=p).
    intros (p1, p2) IHH Hpr; simpl in *.
    apply IH.
    intros p2' n c2 Hfind2.
    rewrite program_refines_def in Hpr.
    destruct (Hpr _ _ _ Hfind2) as (c1 & p1' & Hfind1 & Hcr & Hpr').
    specialize (IHH _ (find_class_ltsuffix2 _ _ _ _ _ _ _ Hfind1 Hfind2) Hpr').
    eauto 6.
  Qed.

  Lemma program_refines_trans:
    forall (P : ident -> ident -> list (ident * type) -> Env.t val -> Env.t val -> Prop),
      (forall n f m x y, P n f m x y -> P n f m x x) ->
      transitive _ (program_refines P).
  Proof.
    intros P HP p1 p2 p3 Hpr12. revert p3.
    induction Hpr12 as [p1 p2 IH] using program_refines_ind.
    setoid_rewrite program_refines_def.
    intros p3 Hpr23 n c3 p3' Hfind3.
    apply Hpr23 in Hfind3.
    destruct Hfind3 as (c2 & p2' & Hfind2 & Hcr23 & Hpr23').
    destruct (IH _ _ _ Hfind2) as (c1 & p1' & Hfind1 & Hcr12 & Hpr' & IH').
    apply IH' in Hpr23'.
    exists c1, p1'. split; auto.
    split; eauto using class_refines_trans.
  Qed.

  Section program_refines_Relation.

    Variable P : ident -> ident -> list (ident * type) -> Env.t val -> Env.t val -> Prop.

    Hypothesis HP1:
      forall c m xs env1 env2, env_refines env1 env2 -> P c m xs env1 env2.

    Hypothesis HP2:
      forall n env1 env2 m xs, P n m xs env1 env2 ->
                               forall n' m' xs', P n' m' xs' env1 env2.

    Hypothesis HP3:
      forall n m xs env1 env2, P n m xs env1 env2 -> P n m xs env1 env1.

    Add Relation _ (program_refines P)
        reflexivity proved by (program_refines_refl _ HP1 HP2)
        transitivity proved by (program_refines_trans _ HP3)
          as stmt_refines_preorder.

  End program_refines_Relation.

  Lemma stmt_refines_strengthen:
    forall P Q p1 p2 s1 s2,
      stmt_refines p1 p2 P s1 s2 ->
      (forall env1 env2, Q env1 env2 -> P env1 env2) ->
      stmt_refines p1 p2 Q s1 s2.
  Proof.
    intros P Q p1 p2 s1 s2 Hr HQP menv env1 env2 menv' env2' HQ Henv Heval.
    eapply Hr in Heval; eauto.
  Qed.

  Instance stmt_refines_Proper:
    Proper (eq ==> eq ==>
               pointwise_relation _
               (pointwise_relation _ (Basics.flip Basics.impl))
               ==> eq ==> eq ==> Basics.impl) stmt_refines.
  Proof.
    intros p1 p2 Hp12 p3 p4 Hp34 pre1 pre2 Hpre s1 s2 Hs12 s3 s4 Hs34 HH.
    subst p2 p4 s2 s4. apply stmt_refines_strengthen with (1:=HH).
    intros env1 env2 Hpre2. apply (Hpre env1 env2 Hpre2).
  Qed.

  (* Proof principle for the simpler case where one program refines another
     class by class. *)
  Lemma program_refines_by_class:
    forall P p1 p2,
      Forall2 (fun c1 c2 => forall p1' p2',
                   program_refines P p1' p2' ->
                   c1.(c_name) = c2.(c_name)
                   /\ class_refines p1' p2' (P c1.(c_name)) c1 c2) p1 p2 ->
      program_refines P p1 p2.
  Proof.
    intros P p1 p2 Hfa.
    pose proof (Forall2_length _ _ _ Hfa) as Hlen.
    revert Hfa.
    pattern p1, p2.
    apply forall2_right; auto.
    now intros; rewrite program_refines_def; inversion 1.
    clear Hlen. intros c1 c2 p1' p2' Hfa' Hpr'.
    inversion_clear Hpr' as [|? ? ? ? Hcr' Hpr].
    apply Hfa' in Hpr. clear Hfa'.
    destruct (Hcr' _ _ Hpr) as [Hcn Hcr].
    rewrite program_refines_def.
    intros n c2' p2'' Hfind2.
    simpl in Hfind2.
    destruct (ident_eqb c2.(c_name) n) eqn:Heq.
    - inv Hfind2. apply ident_eqb_eq in Heq.
      rewrite <-Heq, <-Hcn.
      simpl. setoid_rewrite ident_eqb_refl. eauto.
    - rewrite program_refines_def in Hpr.
      destruct (Hpr _ _ _ Hfind2) as (c1' & p1''' & Hfind1 & Hcr1 & Hpr1).
      exists c1', p1'''. simpl.
      setoid_rewrite Hcn. setoid_rewrite Heq. auto.
  Qed.

  Lemma program_refines_stmt_call_eval:
    forall P p1 p2 omenv omenv' clsid f vos vos' rvos,
      program_refines P p1 p2 ->
      (forall cls prog' m,
          find_class clsid p2 = Some (cls, prog') ->
          find_method f cls.(c_methods) = Some m ->
          length vos = length m.(m_in) ->
          length vos' = length m.(m_in) ->
          P clsid f m.(m_in) (Env.adds_opt (map fst m.(m_in)) vos' vempty)
                             (Env.adds_opt (map fst m.(m_in)) vos vempty)) ->
      stmt_call_eval p2 omenv clsid f vos omenv' rvos ->
      Forall2 (fun vo vo' => forall v, vo = Some v -> vo' = Some v) vos vos' ->
      exists rvos',
        stmt_call_eval p1 omenv clsid f vos' omenv' rvos'
        /\ Forall2 (fun vo' vo => forall v, vo = Some v -> vo' = Some v) rvos' rvos.
  Proof.
    intros * Hpr HP Hcall Hvos.
    inversion_clear Hcall as [? ? ? ? ? ? ? ? ? ? ? Hfindc Hfindm Hlvos Heval Hrvos].
    rewrite program_refines_def in Hpr.
    assert (Hfindc2:=Hfindc). assert (Hfindm2:=Hfindm).
    apply Hpr in Hfindc as (c & p & Hfindc & Hcr & Hpr').
    apply Hcr in Hfindm as (m & Hfindm & (Hm1 & Hm2 & Hsr)).
    assert (env_refines (Env.adds_opt (map fst m.(m_in)) vos' vempty)
                        (Env.adds_opt (map fst fm.(m_in)) vos vempty)) as Henv.
    { rewrite <-Hm1. apply env_refines_adds_opt.
      - reflexivity.
      - now apply Forall2_swap_args in Hvos.
      - apply fst_NoDupMembers. pose proof m.(m_nodupvars) as Hnd.
        rewrite app_assoc in Hnd. now repeat apply NoDupMembers_app_l in Hnd.
      - apply Forall_forall; setoid_rewrite Env.Props.P.F.empty_in_iff; auto.
    }
    eapply Hsr in Heval as (env1' & Henv1' & Heval'); eauto.
    - exists (map (fun x => Env.find x env1') (map fst fm.(m_out))).
      split; [econstructor; eauto|].
      + apply Forall2_length in Hvos. now rewrite <-Hvos, Hm1.
      + rewrite Forall2_map_2, <-Hm2. apply Forall2_same. apply Forall_forall; auto.
      + rewrite Forall2_map_1. apply Forall2_impl_In with (2:=Hrvos).
        intros x vo Hxin Hvoin Hfind v Hv. subst. now apply Henv1' in Hv.
    - rewrite Hm1. apply Forall2_length in Hvos.
      eapply HP; eauto. now rewrite <-Hvos, Hlvos.
  Qed.

  Lemma wt_stmt_program_refines:
    forall P p1 p2 insts mems vars s,
      program_refines P p1 p2 ->
      wt_stmt p2 insts mems vars s ->
      wt_stmt p1 insts mems vars s.
  Proof.
    intros * Hpr WTs.
    induction s; inv WTs; eauto using wt_stmt.
    rewrite program_refines_def in Hpr.
    match goal with H:find_class _ _ = _ |- _ =>
      apply Hpr in H as (c & p1' & Hfindc & Hcr & Hpr') end.
    match goal with H:find_method _ _ = _ |- _ =>
      apply Hcr in H as (m' & Hfindm & (Hmi & Hmo & Hmr)) end.
    rewrite <-Hmi, <-Hmo in *.
    econstructor; eauto.
  Qed.

  Lemma wt_method_program_refines:
    forall P p1 p2 insts mem m,
      program_refines P p1 p2 ->
      wt_method p2 insts mem m ->
      wt_method p1 insts mem m.
  Proof.
    unfold wt_method, meth_vars. intros * Hpr WTm.
    destruct m as [n ins vars outs s nodup good]; simpl in *.
    apply wt_stmt_program_refines with (1:=Hpr) (2:=WTm).
  Qed.

  Lemma env_refines_In:
    forall env1 env2,
      env_refines env1 env2 ->
      forall x, Env.In x env2 ->
                Env.In x env1.
  Proof.
    setoid_rewrite Env.In_find.
    intros * Henv x (v & Hin); eauto.
  Qed.

  Lemma env_refines_not_In:
    forall env1 env2,
      env_refines env1 env2 ->
      forall x, ~Env.In x env1 ->
                ~Env.In x env2.
  Proof.
    setoid_rewrite Env.In_find.
    intros env1 env2 Henv x H (v & Hin); eauto.
  Qed.

  (* TODO: Move earlier *)
  Lemma program_refines_by_class':
    forall (Pc : class -> class -> Prop) P p1 p2,
      wt_program p2 ->
      Forall2 (fun c1 c2 => forall p1' p2',
                   wt_program p2' ->
                   wt_class p2' c2 ->
                   program_refines P p1' p2' ->
                   Forall2 Pc p1' p2' ->
                   Pc c1 c2 ->
                   c1.(c_name) = c2.(c_name)
                   /\ class_refines p1' p2' (P c1.(c_name)) c1 c2) p1 p2 ->
      Forall2 Pc p1 p2 ->
      program_refines P p1 p2.
  Proof.
    intros Pc P p1 p2 WTp Hfa.
    pose proof (Forall2_length _ _ _ Hfa) as Hlen.
    revert WTp Hfa.
    pattern p1, p2.
    apply forall2_right; auto.
    now intros; rewrite program_refines_def; inversion 1.
    clear Hlen. intros c1 c2 p1' p2' Hfa' WTp2' Hpr' Hpc'.
    inversion_clear Hpr' as [|? ? ? ? Hcr' Hpr].
    inversion_clear Hpc' as [|? ? ? ? Hpc Hpcs].
    inversion_clear WTp2' as [|? ? WTc WTp Hnodup].
    apply Hfa' in Hpr; auto. clear Hfa'.
    destruct (Hcr' _ _ WTp WTc Hpr Hpcs Hpc) as [Hcn Hcr].
    rewrite program_refines_def.
    intros n c2' p2'' Hfind2.
    simpl in Hfind2.
    destruct (ident_eqb c2.(c_name) n) eqn:Heq.
    - inv Hfind2. apply ident_eqb_eq in Heq.
      rewrite <-Heq, <-Hcn.
      simpl. setoid_rewrite ident_eqb_refl. eauto.
    - rewrite program_refines_def in Hpr.
      destruct (Hpr _ _ _ Hfind2) as (c1' & p1''' & Hfind1 & Hcr1 & Hpr1).
      exists c1', p1'''. simpl.
      setoid_rewrite Hcn. setoid_rewrite Heq. auto.
  Qed.

  Lemma env_refines_updates:
    forall ws vos env1 env2,
      env_refines env1 env2 ->
      (forall x, In x ws -> ~Env.In x env2) ->
      env_refines (Env.updates ws vos env1) env2.
  Proof.
    induction ws as [|w ws IH]; auto.
    intros vos env1 env2 Henv Hin.
    destruct vos. now unfold Env.updates; simpl.
    rewrite Env.updates_cons_cons.
    destruct o; simpl.
    - apply env_refines_add_left; auto using in_eq.
      now apply IH; auto using in_cons.
    - cut (Env.Equal env2 (Env.remove w env2)).
      + intro Henv2. setoid_rewrite Henv2.
        apply env_refines_remove.
        now apply IH; auto using in_cons.
      + intro x.
        destruct (ident_eq_dec x w); [|now rewrite Env.gro].
        subst. specialize (Hin _ (in_eq w ws)).
        apply Env.Props.P.F.not_find_in_iff in Hin; rewrite Hin.
        now rewrite Env.grs.
  Qed.

End EQUIV.

Module EquivFun
       (Ids          : IDS)
       (Op           : OPERATORS)
       (Import OpAux : OPERATORS_AUX    Op)
       (Import Syn   : OBCSYNTAX    Ids Op OpAux)
       (Import Sem   : OBCSEMANTICS Ids Op OpAux Syn)
       (Import Typ   : OBCTYPING    Ids Op OpAux Syn Sem)
  <: EQUIV Ids Op OpAux Syn Sem Typ.
  Include EQUIV Ids Op OpAux Syn Sem Typ.
End EquivFun.
