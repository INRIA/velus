From Coq Require Import FSets.FMapPositive.
From Coq Require Import PArith.
From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Obc.ObcSyntax.
From Velus Require Import Obc.ObcSemantics.
From Velus Require Import Obc.ObcTyping.

From Coq Require Import Relations.
From Coq Require Import Morphisms.
From Coq Require Import Setoid.

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

  Import Env.Notations.

  Lemma exp_eval_refines:
    forall menv' env1 env2 e v,
      env2 ⊑ env1 ->
      exp_eval menv' env2 e (Some v) ->
      exp_eval menv' env1 e (Some v).
  Proof.
    intros menv' env1 env2.
    induction e; intros v Henv; inversion 1; subst; eauto using exp_eval.
    - take (Env.find _ _ = Some _) and (rewrite it; apply Henv in it as (v' & -> & <-));
        eauto using exp_eval.
    - take (Env.find _ _ = Some _) and apply Henv in it as (v' & -> & ?);
        eauto using exp_eval.
  Qed.

  Lemma exp_eval_refines':
    forall menv env1 env2 e vo,
      env2 ⊑ env1 ->
      exp_eval menv env2 e vo ->
      exists vo', exp_eval menv env1 e vo' /\ (forall v, vo = Some v -> vo' = Some v).
  Proof.
    intros menv env1 env2.
    induction e; intros vo Henv; inversion 1; subst;
      eauto using exp_eval, exp_eval_refines.
    destruct (Env.find i env2).
    - eauto using exp_eval_refines.
    - exists (Env.find i env1); split; eauto using exp_eval.
      discriminate.
  Qed.

  Lemma Forall2_exp_eval_refines':
    forall menv env1 env2 es vos,
      env2 ⊑ env1 ->
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

  (* If a statement s' refines s, it should be possible to use s' instead
     of s. *)

  Definition stmt_refines prog1 prog2 P s1 s2 : Prop :=
    forall menv env1 env2 menv' env2',
      P env1 env2 ->
      env2 ⊑ env1 ->
      stmt_eval prog2 menv env2 s2 (menv', env2') ->
      (exists env1',
          env2' ⊑ env1'
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
    assert ((Env.adds_opt (map fst fm.(m_in)) vos vempty)
              ⊑ (Env.adds_opt (map fst m.(m_in)) vos' vempty)) as Henv.
    { rewrite <-Hm1. apply Env.refines_adds_opt.
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
        intros x vo Hxin Hvoin Hfind v Hv. subst.
        now apply Henv1' in Hv as (? & -> & ?).
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
