Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Rustre.Common.
Open Scope positive.

Require Import Rustre.RMemory.
Require Import Rustre.Dataflow.
Require Import Rustre.Minimp.
Require Import Rustre.DataflowToMinimp.Translation.
Require Import Rustre.DataflowToMinimp.Correctness.IsPresent.
Require Import Rustre.DataflowToMinimp.Correctness.MemoryCorres.
Require Import Rustre.Minimp.FuseIfte.

Module Type CORRECTNESS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import DF    : DATAFLOW Ids Op OpAux)
       (Import MP    : MINIMP Ids Op OpAux)
       (Import Mem   : MEMORIES Ids Op DF.Syn)

       (Import Trans : TRANSLATION Ids Op OpAux DF.Syn MP.Syn Mem)
       
       (Import IsP   : ISPRESENT Ids Op OpAux DF.Syn MP.Syn MP.Sem Mem Trans)
       (Import MemCor: MEMORYCORRES Ids Op OpAux DF MP)
       (Import Fus   : FUSEIFTE Ids Op OpAux DF.Syn MP.Syn MP.Sem MP.Equ).

  (** ** Technical lemmas *)

  Lemma exp_eval_tovar:
    forall x ty v menv env mems,
      exp_eval menv env (tovar mems (x, ty)) v
      <-> (exp_eval menv env (State x ty) v /\ PS.In x mems)
        \/ (exp_eval menv env (Var x ty) v /\ ~PS.In x mems).
  Proof.
    split; intro Heval;
    destruct In_dec with x mems as [Hxm|Hxm];
    pose proof Hxm as Hxmt;
    apply PS.mem_spec in Hxmt || apply mem_spec_false in Hxmt;
    unfold tovar in *;
    rewrite Hxmt in *;
    intuition.
  Qed.

  Lemma stmt_eval_translate_eqns_cons:
    forall prog mems menv env menv' env' eq eqs,
      stmt_eval prog menv env (translate_eqns mems (eq :: eqs)) (menv', env')
      <->
      (exists menv'' env'',
          stmt_eval prog menv env (translate_eqns mems eqs) (menv'', env'')
          /\ stmt_eval prog menv'' env'' (translate_eqn mems eq) (menv', env')).
  Proof. (* TODO: redo proof *)
    split.
    - intro H.
      unfold translate_eqns in H.
      simpl in H.
      apply stmt_eval_fold_left_shift in H.
      destruct H as [menv'' [env'' [H1 H2]]].
      exists menv'', env''.
      split; [now apply H1|].
      inversion_clear H2.
      inversion H0.
      subst.
      exact H.
    - intro H.
      destruct H as [menv'' [env'' [H1 H2]]].
      unfold translate_eqns.
      simpl.
      apply stmt_eval_fold_left_shift.
      exists menv'', env''.
      split; [now apply H1|].
      eapply Icomp. apply H2.
      apply Iskip.
  Qed.

  (** ** [Control] absorption theorems *)

  Lemma stmt_eval_Control_fwd:
    forall prog menv env mems c s menv' env',
      stmt_eval prog menv env (Control mems c s) (menv', env')
      -> (Is_present_in mems menv env c
         /\ stmt_eval prog menv env s (menv', env'))
        \/ (Is_absent_in mems menv env c
           /\ menv' = menv /\ env' = env).
  Proof.
    Hint Constructors Is_present_in Is_absent_in.
    intros prog menv env mems c s menv' env' Hs.
    revert s Hs.
    induction c; [now intuition|].
    intros s Hs.
    simpl in Hs.
    destruct b;
    specialize (IHc _ Hs); clear Hs;
      destruct IHc as [[Hp Hs]|[Hp [Hmenv Henv]]];
      try inversion_clear Hs; subst; intuition.
    - destruct b; [now eauto|].
      right. match goal with H:stmt_eval _ _ _ _ _ |- _ => inv H end.
      assert (true = negb false) as Htrue by reflexivity.
      rewrite Htrue. eauto.
    - destruct b; [|now eauto].
      right. match goal with H:stmt_eval _ _ _ _ _ |- _ => inv H end.
      assert (false = negb true) as Hfalse by reflexivity.
      rewrite Hfalse. eauto.
  Qed.
  
  Lemma stmt_eval_Control:
    forall prog mems menv env ck stmt,
      (Is_absent_in mems menv env ck
       -> stmt_eval prog menv env (Control mems ck stmt) (menv, env))
      /\
      (forall menv' env',
          Is_present_in mems menv env ck
          -> stmt_eval prog menv env stmt (menv', env')
          -> stmt_eval prog menv env (Control mems ck stmt) (menv', env')).
  Proof.
    Hint Constructors stmt_eval.
    intros prog mems menv env ck.
    induction ck; intro s; split.
    - inversion 1.
    - intros menv' env' Hp Hs; exact Hs.
    - inversion_clear 1 as [? ? ? Hp|? ? ? ? Hp Hexp];
        destruct b; destruct (PS.mem i mems); try destruct b0;
          apply IHck with (1:=Hp); eauto.
    - inversion_clear 1 as [|? ? ? ? Hp Hexp]; intro Hs;
        destruct b; destruct (PS.mem i mems); try destruct b0;
          apply IHck with (1:=Hp); eauto.
  Qed.

  (** If the clock is absent, then the controlled statement evaluates as
  a [Skip].  *)

  Theorem stmt_eval_Control_absent:
    forall prog mems menv env ck stmt,
      Is_absent_in mems menv env ck
      -> stmt_eval prog menv env (Control mems ck stmt) (menv, env).
  Proof.
    apply stmt_eval_Control.
  Qed.

  (** If the clock is present, then the controlled statement evaluates
  as the underlying one.  *)

  Theorem stmt_eval_Control_present:
    forall prog mems menv env ck stmt menv' env',
      Is_present_in mems menv env ck
      -> stmt_eval prog menv env stmt (menv', env')
      -> stmt_eval prog menv env (Control mems ck stmt) (menv', env').
  Proof.
    apply stmt_eval_Control.
  Qed.

  (** ** More technical lemmas *)

  Lemma stmt_eval_translate_cexp_menv_inv:
    forall prog menv env mems x menv' env' ce,
      stmt_eval prog menv env (translate_cexp mems x ce) (menv', env')
      -> menv' = menv.
  Proof.
    intros prog menv env mems x menv' env'.
    induction ce;
      (apply IHce || inversion_clear 1; try destruct b); auto.
  Qed.

  Lemma stmt_eval_translate_cexp_env_add:
    forall prog menv env mems x menv' env' ce,
      stmt_eval prog menv env (translate_cexp mems x ce) (menv', env')
      -> exists c, env' = PM.add x c env.
  Proof.
    intros prog menv env mems x menv' env'.
    induction ce;
      (apply IHce || inversion_clear 1; try destruct b); auto;
      exists v; rewrite <- H1; intuition.
  Qed.

  Lemma not_Is_defined_in_eq_stmt_eval_menv_inv:
    forall prog x eq menv env mems menv' env',
      ~Is_defined_in_eq x eq
      -> stmt_eval prog menv env (translate_eqn mems eq) (menv', env')
      -> mfind_mem x menv' = mfind_mem x menv.
  Proof. (* TODO: Tidy proof *)
    intros prog x eq menv env mems menv' env' Hneq Heval.
    destruct eq as [y ck ce | y ck f les | y ck v0 lae]; simpl in Heval.
    - apply stmt_eval_Control_fwd in Heval; destruct Heval as [Heval|Heval];
      destruct Heval as [Heval1 Heval2].
      apply stmt_eval_translate_cexp_menv_inv in Heval2.
      rewrite Heval2. intuition.
      destruct Heval2 as [Hmenv]; rewrite Hmenv; intuition.
    - simpl in Heval.
      apply stmt_eval_Control_fwd in Heval; destruct Heval as [Heval|Heval];
      destruct Heval as [Hipi Heval].
      inversion_clear Heval.
      rewrite <- H2.
      reflexivity.
      destruct Heval as [Hmenv Henv]; rewrite Hmenv; intuition.
    - apply not_Is_defined_in_eq_EqFby in Hneq.
      unfold translate_eqn in Heval.
      apply stmt_eval_Control_fwd in Heval; destruct Heval as [Heval|Heval];
      destruct Heval as [Hipi Heval].
      inversion_clear Heval.
      rewrite <- H0.
      unfold mfind_mem, madd_mem.
      simpl; rewrite PM.gso; [intuition | apply Hneq].
      destruct Heval as [Hmenv Henv]; rewrite Hmenv; intuition.
  Qed.

  Lemma not_Is_defined_in_eq_stmt_eval_mobj_inv:
    forall prog x eq menv env mems menv' env',
      ~Is_defined_in_eq x eq
      -> stmt_eval prog menv env (translate_eqn mems eq) (menv', env')
      -> mfind_inst x menv' = mfind_inst x menv.
  Proof. (* TODO: Tidy proof *)
    intros prog x eq menv env mems menv' env' Hneq Heval.
    destruct eq as [y ck ce | y ck f les | y ck v0 lae].
    - simpl in Heval.
      apply stmt_eval_Control_fwd in Heval; destruct Heval as [Heval|Heval];
      destruct Heval as [Heval1 Heval2].
      apply stmt_eval_translate_cexp_menv_inv in Heval2.
      rewrite Heval2. intuition.
      destruct Heval2 as [Hmenv]; rewrite Hmenv; intuition.
    - simpl in Heval.
      apply stmt_eval_Control_fwd in Heval; destruct Heval as [Heval|Heval];
      destruct Heval as [Hipi Heval].
      + inversion_clear Heval.
        rewrite <- H2.
        destruct (ident_eq_dec x y) as [Hxy|Hxny].
        * rewrite Hxy in Hneq; exfalso; apply Hneq; constructor.
        * rewrite mfind_inst_gso; [reflexivity|assumption].
      + destruct Heval as [HR1 HR2]; rewrite HR1; reflexivity.
    - unfold translate_eqn in Heval.
      apply stmt_eval_Control_fwd in Heval; destruct Heval as [Heval|Heval];
      destruct Heval as [Hipi Heval].
      inversion_clear Heval.
      rewrite <- H0.
      unfold mfind_inst, madd_mem.
      reflexivity.
      destruct Heval as [Hmenv Henv]; rewrite Hmenv; intuition.
  Qed.

  Lemma not_Is_variable_in_eq_stmt_eval_env_inv:
    forall prog x eq menv env mems menv' env',
      ~Is_variable_in_eq x eq
      -> stmt_eval prog menv env (translate_eqn mems eq) (menv', env')
      -> PM.find x env' = PM.find x env.
  Proof.
    intros prog x eq menv env mems menv' env' Hnd Heval.
    destruct eq as [y ck ce | y ck f les | y ck v0 ce]; simpl in Heval.
    - apply stmt_eval_Control_fwd in Heval;
        destruct Heval as [[Hipi Heval]|[Habs [Hmenv Henv]]];
        [|rewrite Henv; reflexivity].
      apply stmt_eval_translate_cexp_env_add in Heval.
      destruct Heval; rewrite H; rewrite PM.gso;
      [reflexivity|intro HR; rewrite HR in *; apply Hnd; constructor].
    - apply stmt_eval_Control_fwd in Heval; destruct Heval as [Heval|Heval];
        destruct Heval as [Heval1 Heval2].
      2:now destruct Heval2; subst.
      inversion_clear Heval2.
      rewrite <- H3.
      unfold adds.
      destruct rvs; [reflexivity|].
      simpl; rewrite PM.gso; [reflexivity|].
      intro Hxy; apply Hnd; rewrite Hxy; constructor.
    - apply stmt_eval_Control_fwd in Heval; destruct Heval as [Heval|Heval];
      destruct Heval as [Heval1 Heval2].
      inversion Heval2; intuition.
      destruct Heval2 as [Hmenv Henv]; rewrite Henv; intuition.
  Qed.

  Lemma not_Is_defined_in_eq_stmt_eval_env_inv:
    forall prog x eq menv env mems menv' env',
      ~Is_defined_in_eq x eq
      -> stmt_eval prog menv env (translate_eqn mems eq) (menv', env')
      -> PM.find x env' = PM.find x env.
  Proof.
    intros prog x eq menv env mems menv' env' Hidi Hstmt.
    apply not_Is_defined_in_eq_not_Is_variable_in_eq in Hidi.
    now apply not_Is_variable_in_eq_stmt_eval_env_inv with (1:=Hidi) (2:=Hstmt).
  Qed.

  Lemma stmt_eval_translate_eqns_menv_inv:
    forall prog menv env mems eqs menv' env',
      stmt_eval prog menv env (translate_eqns mems eqs) (menv', env')
      -> (forall x, ~Is_defined_in_eqs x eqs ->
              mfind_mem x menv' = mfind_mem x menv).
  Proof.
    induction eqs as [ |eq].
    + inversion_clear 1; reflexivity.
    + intros menv' env' Heval x Hnmem.
      apply not_Is_defined_in_cons in Hnmem.
      destruct Hnmem as [H0 H1].
      apply stmt_eval_translate_eqns_cons in Heval.
      destruct Heval as [menv'' [env'' [Heval0 Heval1]]].
      apply IHeqs with (x:=x) (2:=H1) in Heval0.
      apply not_Is_defined_in_eq_stmt_eval_menv_inv with (1:=H0) in Heval1.
      rewrite Heval1, Heval0.
      reflexivity.
  Qed.

  Lemma stmt_eval_translate_eqns_minst_inv:
    forall prog menv env mems eqs menv' env',
      stmt_eval prog menv env (translate_eqns mems eqs) (menv', env')
      -> (forall x, ~Is_defined_in_eqs x eqs ->
              mfind_inst x menv' = mfind_inst x menv).
  Proof.
    induction eqs as [ |eq].
    + inversion_clear 1; reflexivity.
    + intros menv' env' Heval x Hnmem.
      apply not_Is_defined_in_cons in Hnmem.
      destruct Hnmem as [H0 H1].
      apply stmt_eval_translate_eqns_cons in Heval.
      destruct Heval as [menv'' [env'' [Heval0 Heval1]]].
      apply IHeqs with (x:=x) (2:=H1) in Heval0.
      apply not_Is_defined_in_eq_stmt_eval_mobj_inv with (1:=H0) in Heval1.
      rewrite Heval1, Heval0.
      reflexivity.
  Qed.

  Lemma stmt_eval_translate_eqns_env_inv:
    forall prog menv env mems eqs menv' env',
      stmt_eval prog menv env (translate_eqns mems eqs) (menv', env')
      -> (forall x, ~Is_variable_in_eqs x eqs ->
              PM.find x env' = PM.find x env).
  Proof.
    induction eqs as [ |eq].
    + inversion_clear 1; reflexivity.
    + intros menv' env' Heval x Hndef.
      apply not_Is_variable_in_cons in Hndef.
      destruct Hndef as [H0 H1].
      apply stmt_eval_translate_eqns_cons in Heval.
      destruct Heval as [menv'' [env'' [Heval0 Heval1]]].
      apply IHeqs with (x:=x) (2:=H1) in Heval0.
      apply not_Is_variable_in_eq_stmt_eval_env_inv with (1:=H0) in Heval1.
      rewrite Heval1, Heval0.
      reflexivity.
  Qed.

  Local Ltac split_env_assumption :=
    match goal with
    | Henv: context Is_free_in_lexp [_], Hsem: sem_var_instant _ ?y _
      |- _ => apply Henv in Hsem; [destruct Hsem |solve [auto]]; clear Henv
    | Henv: context Is_free_in_clock [_], Hsem: sem_var_instant _ ?y _
      |- _ => apply Henv in Hsem; [destruct Hsem |solve [auto]]; clear Henv
    end.

  (** ** Correctness of expression's translation *)

  (** 

An imperative stack [env] and an imperative memory [menv] are faithful
to a dataflow environment [R] over a set of identifiers [Is_free] if
their values agree with the dataflow environment.

   *)

  Definition equiv_env (Is_free: ident -> Prop) R memories env menv :=
    forall x c, Is_free x
           -> sem_var_instant R x (present c)
           -> (~PS.In x memories -> PM.find x env = Some c)
             /\ (PS.In x memories -> mfind_mem x menv = Some c).
  Hint Unfold equiv_env.

  (** We often need to weaken an equivalence to a subterm: for example we
know that the environments are equivalent for all [Is_free_caexp x
(AnnExp e ck)], we can deduce that the environements are equivalent
for all [Is_free_exp x e]. *)
  Lemma equiv_env_map (Is_free1 Is_free2: ident -> Prop) H memories env menv:
    (forall x, Is_free2 x -> Is_free1 x) ->
    equiv_env Is_free1 H memories env menv ->
    equiv_env Is_free2 H memories env menv.
  Proof.
    intros Hinv Hequiv1 x **; auto.
  Qed.

  Ltac weaken_equiv_env :=
    match goal with
    | [H: equiv_env ?is_free1 ?R ?mems ?env ?menv
       |- equiv_env ?is_free2 ?R ?mems ?env ?menv] =>
      eapply equiv_env_map; [|exact H]; constructor(auto)
    end.


  (** *** Correctness of clock's translation *)

  Lemma get_exp_eval_tovar:
    forall x ty mems menv env v,
      (~ PS.In x mems -> PM.find x env = Some v)
      -> (PS.In x mems -> mfind_mem x menv = Some v)
      -> exp_eval menv env (tovar mems (x, ty)) v.
  Proof.
    intros x ty mems menv env v Hvar Hmem.
    unfold tovar.
    destruct (In_dec x mems) as [Hin|Hnin].
    - specialize (Hmem Hin).
      apply PS.mem_spec in Hin; rewrite Hin.
      constructor; exact Hmem.
    - specialize (Hvar Hnin).
      apply mem_spec_false in Hnin; rewrite Hnin.
      constructor; exact Hvar.
  Qed.

  Theorem clock_correct_true:
    forall base R mems menv env ck,
      equiv_env (fun x => Is_free_in_clock x ck) R mems env menv
      -> sem_clock_instant base R ck true
      -> Is_present_in mems menv env ck.
  Proof.
    Hint Constructors Is_present_in.
    Hint Constructors sem_clock_instant.
    Hint Constructors Is_free_in_clock.
    Hint Constructors exp_eval.
    intros until env.
    induction ck as [|? ? x]; [ intuition | ].
    intro Henv.
    inversion 1; subst.
    econstructor; try eassumption.
    - apply IHck; [now weaken_equiv_env|assumption].
    - split_env_assumption.
      apply exp_eval_tovar.
      destruct In_dec with x mems; intuition.
  Qed.

  Theorem clock_correct_false:
    forall R mems menv env ck,
      equiv_env (fun x => Is_free_in_clock x ck) R mems env menv
      -> sem_clock_instant true R ck false
      -> Is_absent_in mems menv env ck.
  Proof.
    Hint Constructors Is_absent_in sem_clock_instant Is_free_in_clock exp_eval.
    intros until env.
    induction ck as [|? ? x]; [ now inversion 2 | ].
    intro Henv.
    inversion_clear 1.
    - constructor. apply IHck; auto.
    - destruct b0; [apply val_to_bool_true' in H2
                   |apply val_to_bool_false' in H2]; subst;
        eapply IsAbs2;
        try eapply clock_correct_true with (2:=H0);
        try apply val_to_bool_true;
        try apply val_to_bool_false;
        auto;
        split_env_assumption;
        destruct In_dec with x mems as [Hin|Hin];
        match goal with
        | H:~PS.In _ _ -> _, Hin:~PS.In _ _ |- _ => specialize (H Hin)
        | H:PS.In _ _ -> _, Hin:PS.In _ _ |- _ => specialize (H Hin)
        end;
        apply PS.mem_spec in Hin || apply mem_spec_false in Hin;
        unfold tovar; rewrite Hin; intuition.
  Qed.

  (** *** Correctness of [translate_lexp] *)

  Theorem typ_correct:
    forall mems e,
      typeof (translate_lexp mems e) = DF.Syn.typeof e.
  Proof.
    induction e as [|y ty| | |]; simpl; auto.
    destruct (PS.mem y mems); simpl; auto.
  Qed.
  
  Theorem lexp_correct:
    forall R mems menv env c e,
      sem_lexp_instant true R e (present c)
      -> equiv_env (fun x => Is_free_in_lexp x e) R mems env menv 
      -> exp_eval menv env (translate_lexp mems e) c.
  Proof.
    Hint Constructors exp_eval.
    intros until e. revert c.
    (* XXX: Tidy up this proof *)
    induction e as [c0|y ty|e IH y yb|op le IHle ty|op le1 IHle1 le2 IHle2 ty];
      intro c; inversion 1 as [c' v Hp H'|x v ty' H'|s x b v ty' H' H''|
                      | |le' op' c' ty' H'| |le1' le2' op' c1 c2 ty' H' H''|];
        try (subst; injection H'); intros; subst;
          try apply IH; try apply econst; auto.
    - simpl. injection Hp. intro; subst. constructor.
    - split_env_assumption;
      unfold translate_lexp;
      destruct (PS.mem y mems) eqn:Hm;
      simpl; rewrite Hm.
      + auto.  
      + rewrite mem_spec_false in Hm; auto.
    - simpl. apply eunop with c'.
      + apply IHle; auto.
      + now rewrite typ_correct.
    - simpl. apply ebinop with (c1 := c1) (c2 := c2).
      + apply IHle1; auto.
      + apply IHle2; auto.
      + now rewrite 2 typ_correct.
  Qed.

  Theorem lexps_correct:
    forall R mems menv env cs es,
      let vs := map present cs in
      Forall2 (fun e v => sem_lexp_instant true R e v) es vs
      -> equiv_env (fun x => Exists (Is_free_in_lexp x) es) R mems env menv 
      -> Forall2 (exp_eval menv env) (map (translate_lexp mems) es) cs.
  Proof.
    Hint Constructors Forall2.
    intros until cs.
    induction cs; intros es Hvs Hsem Hequiv; subst Hvs.
    now inv Hsem; constructor.
    inv Hsem. constructor.
    - now eapply lexp_correct; eauto.
    - apply IHcs; trivial.
      repeat intro. apply Hequiv; trivial. now constructor(assumption).
  Qed.

  (** *** Correctness of [translate_cexp] *)

  Theorem cexp_correct:
    forall R mems prog menv env c x e,
      sem_cexp_instant true R e (present c)
      -> equiv_env (fun x => Is_free_in_cexp x e) R mems env menv
      -> stmt_eval prog menv env (translate_cexp mems x e)
                  (menv, PM.add x c env).
  Proof.
    intros until x.
    induction e as [y ty et IHt ef IHf|y t IHt f IHf|e].
    - (* Emerge *)
      inversion_clear 1; intro Henv.
      + apply IHt in H1; [|auto].
        simpl.
        eapply Iifte; [|now apply val_to_bool_true'|assumption].
        split_env_assumption. apply get_exp_eval_tovar; auto.
      + apply IHf in H2; [|auto].
        eapply Iifte; [|now apply val_to_bool_false'|assumption].
        split_env_assumption. apply get_exp_eval_tovar; auto.
    - (* Eite *)
      intro HH; inv HH; intro Henv.
      simpl; econstructor; [|eassumption|].
      eapply lexp_correct; now eauto.
      destruct b;
        match goal with H:present _ = present _ |- _ => injection H end;
        intro; subst; [apply IHt|apply IHf]; eauto.
    - (* Eexp *)
      inversion_clear 1; intro Henv.
      unfold translate_cexp.
      econstructor.
      eapply lexp_correct; [eassumption|now auto].
      reflexivity.
  Qed.

  (* Notes:
   1. The assumption sem_equations must be shown for a set of equations.
      TODO: lemma showing that a well-typed and well-clocked set of
            equations has a semantics.

   2. The assumption stmt_eval (translate_eqns mems eqs) implies that an
      execution exists and thus that exp_eval's evar and estate find some
      value for each required variable.
      This is somehow backwards; it should be an obligation to show that
      an execution exists. This is something assured indirectly in the
      lemma below where we require not just that evar and estate find
      some value, but also that it is the correct value.
   *)


  Lemma Is_memory_in_msem_var:
    forall G bk H M n x eqs c,
      Is_defined_in_eqs x eqs
      -> ~Is_variable_in_eqs x eqs
      -> sem_var_instant (restr H n) x (present c)
      -> List.Forall (msem_equation G bk H M) eqs
      -> (exists ms, mfind_mem x M = Some ms /\ ms n = c).
  Proof.
    induction eqs as [|eq eqs IH];
    inversion_clear 1 as [? ? Hidi|? ? Hidi];
    intros Hnvi Hsv Hmsem;
    apply Forall_cons2 in Hmsem;
    apply not_Is_variable_in_cons in Hnvi;
    destruct Hnvi as [Hnvi0 Hnvi1];
    destruct Hmsem as [Hmeq Hmeqs].
    - destruct eq; inversion Hidi; subst;
      try (exfalso; apply Hnvi0; now constructor).
      inversion_clear Hmeq
        as [| |? ? ? ? ? ? ls ? ? ? Hmfind Hms0 Hsemls HxS Hmls].
      exists ms.
      split; [apply Hmfind|].
      specialize Hmls with n; specialize (HxS n); simpl in HxS.
      destruct (ls n);
        destruct Hmls as [Hms Hsv'].
      rewrite Hsv' in HxS.
      + assert (present c = absent) by sem_det; discriminate.
      + cut (present (ms n) = present c); [injection 1; auto|].
        rewrite Hsv' in HxS.
        sem_det.
    - apply IH; assumption.
  Qed.

  (** *** Correctness of [translate_eqns] *)

  Definition equiv_node G prog f :=
    forall n xss ys M menv inputs output,
      Memory_Corres G n f M menv
      -> msem_node G f xss M ys
      -> present_list xss n inputs
      -> ys n = present output
      -> exists menv',
          stmt_call_eval prog menv f step inputs menv' [output]
          /\  Memory_Corres G (S n) f M menv'.

  Definition equiv_prog G prog :=
    forall f,
      equiv_node G prog f.



  Section IsStepCorrect.

    Variables (G: global)
              (HG: Welldef_global G)
              (bk: stream bool)
              (H: history)
              (M: memory)
              (mems: PS.t)
              (alleqs : list equation)
              (Hsems: msem_equations G bk H M alleqs)
              (prog: program)
              (Hnode: equiv_prog G prog)
              (inputs: list ident)
              (Hinput: forall input, In input inputs -> ~ PS.In input mems)
              (n: nat)
              (Hbase: bk n = true)
              (menv: heap)
              (env: stack).

    (* TODO: Can we replace
    (forall x, PS.In x mems ->
		(Is_defined_in x alleqs /\ ~Is_variable_in x alleqs)) ->
  and
    ~PS.In input mems ->

  with a simply definition of mems in terms of alleqs and one or two
  auxilliary lemmas? *)

    Lemma is_step_correct:
      forall (eqs: list equation),
        (exists oeqs, alleqs = oeqs ++ eqs)
        -> (forall x, PS.In x mems
                -> (Is_defined_in_eqs x alleqs
                   /\ ~Is_variable_in_eqs x alleqs))

        (* - input (assumed) *)
        -> (forall c input, In input inputs ->
                      (sem_var_instant (restr H n) input (present c)
                       <-> PM.find input env = Some c))
        (* NB: PM.find x env' = Some c -> sem_var H x n (present c)
                 does not hold if PM.find x env = Some arbitrary_c, since
                 x will not be written to when its clock is absent.

                 It may just be better to show the direction:
                 sem_var H x n (present c) -> PM.find x env' = Some c

                 which is enough if the outputs are only sampled when
                 they are present (normally the case).

                 More discussion/context is needed. *)
        -> (forall x, Is_variable_in_eqs x eqs -> PM.find x env = None)
        -> (forall input, In input inputs -> ~ Is_defined_in_eqs input eqs)

        (* - execution of translated equations *)
        -> Is_well_sch mems inputs eqs

        (* - unwritten memories (assumed) *)
        -> List.Forall (Memory_Corres_eq G n M menv) alleqs

        (* - locals (shown) *)
        -> (exists menv' env',
              stmt_eval prog menv env (translate_eqns mems eqs) (menv', env')
              /\ (forall x, Is_variable_in_eqs x eqs
                  -> forall c : val, sem_var_instant (restr H n) x (present c)
                               <-> PM.find x env' = Some c)
              (* - written memories (shown) *)
              /\ List.Forall (Memory_Corres_eq G (S n) M menv') eqs).
    Proof.
      (* Induction on equations: translate_eqns [] = Skip *)
      induction eqs as [|eq];
      [ intros; exists menv, env;
        split; [unfold translate_eqns; constructor|];
        split; intros; [ match goal with
                         | H:Is_variable_in_eqs _ nil |- _ => inversion H
                         end | now constructor ]| ].
      intros Hall Hinmems Hin Henv Hin2 Hwsch Hmc.

      assert (exists menv' env',
               stmt_eval prog menv env (translate_eqns mems eqs) (menv', env')
               /\ (forall x, Is_variable_in_eqs x eqs
                       -> forall c, sem_var_instant (restr H n) x (present c)
                              <-> PM.find x env' = Some c)
               /\ List.Forall (Memory_Corres_eq G (S n) M menv') eqs) as IHeqs'.
      { eapply IHeqs; trivial.
        - apply List_shift_away with (1:=Hall).
        - intros; apply Henv; constructor(assumption).
        - intros; eapply not_Is_defined_in_cons; eauto.
        - eapply Is_well_sch_cons; eauto.
      }

      clear IHeqs.
      destruct IHeqs' as [menv' [env' [Hstmt [IHeqs0 IHeqs1]]]].

      destruct Hall as [oeqs Hall].
      assert (Hsems' := Hsems); rewrite Hall in Hsems'.

      apply Forall_app in Hsems'.
      destruct Hsems' as [H0 Hsems']; clear H0.
      apply Forall_cons2 in Hsems'.
      destruct Hsems' as [Hsem Hsems'].

      inversion Hsem as
          [bk0 H0 M0 i ck xs ce Hvar Hce HR1 HR2 HR3
          |bk0 H0 M0 y ck f Mo les ty ls xs Hmfind Hlaes Hvar Hmsem HR1 HR2 HR3
          |bk0 H0 M0 ms y ck ls yS v0 le Hmfind Hms0 Hlae HyS Hvar HR1 HR2 HR3];
        subst bk0 H0 M0 eq;
        (*    (rewrite <-HR3 in *; clear HR1 HR2 HR3 H0 M0); *)
        specialize (Hvar n).
      - (* Case EqDef: y = cae *)
        exists menv'. (* the memory does not change *)

        specialize (Hce n); simpl in *.
        assert (equiv_env (fun x => Is_free_in_caexp x ck ce)
                          (restr H n) mems env' menv')
          as Hce'.
        {
          Hint Constructors Is_free_in_eq.
          intros.
          split; intro Hmems.

          - assert (Hdecide_x: Is_variable_in_eqs x eqs \/ In x inputs)
              by (eapply Is_well_sch_free_variable; eauto).

            destruct Hdecide_x; try subst x.
            + apply IHeqs0; assumption.
            + erewrite stmt_eval_translate_eqns_env_inv; try eassumption.
              now apply Hin.
              apply not_Is_defined_in_not_Is_variable_in.
              intro Hnot_def. eapply Hin2; try eauto.
              constructor(assumption).

          - assert (~ Is_defined_in_eqs x eqs)
              by (eapply Is_well_sch_free_variable_in_mems; eauto).

            specialize (Hinmems _ Hmems); destruct Hinmems.
            erewrite stmt_eval_translate_eqns_menv_inv; try eassumption.
            eapply Is_memory_in_msem_var in H1; try eassumption.
            do 2 destruct H1; subst c.
            assert (Is_defined_in_eqs x alleqs) by intuition.
            assert (~ Is_variable_in_eqs x alleqs) by intuition.
            erewrite Is_memory_in_Memory_Corres_eqs; try eauto.
        }

        inversion Hce; subst ck0 ce0;
        match goal with
        | H: present _ = xs n |- _ => rewrite <- H in *
        | H: absent = xs n |- _ => rewrite <- H in *
        end.

        + (* xs n = present *)
          rename c into v.
          exists (PM.add i v env').
          split; [|split].
          * apply stmt_eval_translate_eqns_cons.
            exists menv', env'.
            split; [exact Hstmt|].
            apply stmt_eval_Control_present.
            eapply clock_correct_true; now eauto.
            rewrite Hbase in *.
            eapply cexp_correct; now eauto.
          * intros x0 Hivi c.
            inversion_clear Hivi as [? ? Hivi'|]; [inversion_clear Hivi'|].
            { rewrite PM.gss; split; intro HH.
              - assert (c = v) by
                    (cut (present c = present v); [injection 1; auto|];
                     sem_det).
                congruence.
              - injection HH; intro Heq. subst. assumption. }
            { destruct (ident_eq_dec x0 i) as [Hxy|Hnxy].
              - rewrite Hxy in *; clear Hxy.
                rewrite PM.gss.
                split; intro Hsv'.
                * assert (v = c)
                    by (cut (present v = present c); [injection 1; auto|]; sem_det).
                  congruence.
                * injection Hsv'; congruence.
              - erewrite PM.gso; try eassumption.
                apply IHeqs0; assumption.
            }
          * rewrite Hall in Hmc.
            apply Forall_app in Hmc; destruct Hmc as [Hmc0 Hmc]; clear Hmc0.
            apply Forall_cons2 in Hmc; destruct Hmc as [Hmc Hmc0]; clear Hmc0.
            inversion_clear Hmc.
            repeat constructor; assumption.

        + (* xs n = absent *)
          exists env'.
          split; [|split].
          * apply stmt_eval_translate_eqns_cons.
            exists menv', env'.
            split; [exact Hstmt|].
            rewrite Hbase in *.
            apply stmt_eval_Control_absent; auto.
            eapply clock_correct_false; eauto.
          * intros x0 Hivi c.
            (* TODO: do we really need this [destruct]? It seems that we *know*
                     that it cannot be a variable (proof by
                     [contradiction]/[discriminate]). If not, remove dependency
                     on [Dataflow.IsVariable.Decide] *)
            destruct (Is_variable_in_dec x0 eqs) as [Hvin|Hvin];
              [now apply IHeqs0 with (1:=Hvin)|].
            apply stmt_eval_translate_eqns_env_inv with (2:=Hvin) in Hstmt.
            rewrite Hstmt.
            inversion_clear Hivi as [? ? Hivi'|];
              [|unfold Is_variable_in_eqs in Hvin; contradiction].
            inversion_clear Hivi'.
            split; intro Hsv'.
            assert (present c = absent) by sem_det. discriminate.
            assert (PM.find i env = None).
            apply Henv; now repeat constructor.
            rewrite Hsv' in *; discriminate.
          * rewrite Hall in Hmc.
            apply Forall_app in Hmc; destruct Hmc as [Hmc0 Hmc]; clear Hmc0.
            apply Forall_cons2 in Hmc; destruct Hmc as [Hmc Hmc0]; clear Hmc0.
            inversion_clear Hmc.
            repeat constructor; assumption.

      - (* Case EqApp: y = f lae *)

        (* used variables are defined *)
        assert (equiv_env (fun x => Is_free_in_laexps x ck les)
                          (restr H n) mems env' menv')
          as Hlae'. {
          intros.
          split; intro Hmems.

          - assert (Hdecide_x: Is_variable_in_eqs x eqs \/ In x inputs)
              by (eapply Is_well_sch_free_variable;
                   eassumption || constructor (assumption)).

            destruct Hdecide_x; try subst x.
            + apply IHeqs0; assumption.
            + erewrite stmt_eval_translate_eqns_env_inv; try eassumption.
              apply Hin; now eauto.
              apply not_Is_defined_in_not_Is_variable_in.
              intro Hnot_def. eapply Hin2; eauto.
              econstructor(eassumption).

          - assert (~ Is_defined_in_eqs x eqs)
              by (eapply Is_well_sch_free_variable_in_mems;
                   eassumption || constructor (assumption)).
            specialize (Hinmems _ Hmems); destruct Hinmems.
            erewrite stmt_eval_translate_eqns_menv_inv; try eassumption.
            eapply Is_memory_in_msem_var in H1; try eassumption.
            do 2 destruct H1; subst c.
            assert (Is_defined_in_eqs x alleqs) by intuition.
            assert (~ Is_variable_in_eqs x alleqs) by intuition.
            erewrite Is_memory_in_Memory_Corres_eqs; try eauto.
        }

        (* memory correspondence before execution *)
        rewrite Hall in Hmc.
        apply Forall_app in Hmc.
        destruct Hmc as [Hmc0 Hmc]; clear Hmc0.
        apply Forall_cons2 in Hmc.
        destruct Hmc as [Hmceq Hmceqs].
        inversion_clear Hmceq as [|? ? ? ? ? ? ? Hmc0|].
        specialize (Hmc0 _ Hmfind).
        destruct Hmc0 as [omenv [Hfindo Hmc0]].
        (* dataflow semantics *)
        assert (Hmsem':=Hmsem).
        inversion_clear Hmsem'
          as [? ? ? ? ? i o v neqs
                ingt0 defd vout nodup good Hck Hfind Hnsem].
        destruct Hnsem as [Hn [Hlsn [Hxsn [Hout Hnsem]]]].

        (* no other instance *)
        assert (~Is_defined_in_eqs y eqs) as Hniii.
            (* by (inversion_clear Hwsch; eauto). *)
        inversion_clear Hwsch; apply H2; constructor.
        
        specialize (Hlaes n);
          specialize (Hxsn n);
          specialize (Hout n);
          simpl in *.

        inversion_clear Hlaes as [? ? ? ? Hlsp|].
        + (* y = present *)
          rename cs into inValues.
          assert (exists c : val, xs n = present c) as [outValue Hxsc].
          {
            apply not_absent_present.
            intro HH.
            apply Hout in HH.
            pose proof (sem_vars_gt0 _ _ _ _ ingt0 Hlsn n) as Hingt0.
            rewrite Hlsp, map_length in Hingt0.
            apply not_absent_present_list with (1:=Hingt0) (3:=HH); auto.
          }
          rewrite Hxsc in *.

          assert (exists menv' : heap,
                     stmt_call_eval prog omenv f step inValues menv' [outValue]
                     /\ Memory_Corres G (S n) f Mo menv') as Hclass
              by (eapply Hnode; eauto).
          destruct Hclass as (omenv' & Hnstmt & Hnmc).

          simpl in *.
          exists (madd_obj y omenv' menv'), (PM.add y outValue env').
          split;[|split].
          * apply stmt_eval_translate_eqns_cons.
            exists menv', env'.
            split; [exact Hstmt|].
            apply stmt_eval_Control_present.
            eapply clock_correct_true; now eauto.

            assert (equiv_env (fun x : ident => Exists (Is_free_in_lexp x) les)
                              (restr H n) mems env' menv')
              by weaken_equiv_env.

            assert (Forall2 (exp_eval menv' env')
                            (map (translate_lexp mems) les) inValues).
            {
              rewrite Hbase in *.
              eapply lexps_correct; eauto.
              match goal with
              | H: _ = map present inValues |- _ => rewrite <- H
              | H: map present inValues = _ |- _ => rewrite H
              end. eauto.
            }
            Hint Constructors stmt_eval.
            erewrite <-stmt_eval_translate_eqns_minst_inv in Hfindo; eauto.
            econstructor; eauto. rewrite Hfindo. eauto. eauto.
          * {
              intros x Hivi c.
              apply Is_variable_in_cons in Hivi.
              destruct Hivi as [Hivi | [notxy Hivi] ].
              - (* x = y *)
                inversion_clear Hivi.
                rewrite PM.gss. split; intro HH.
                + assert (present c = present outValue) by sem_det.
                  congruence.
                + injection HH. intro Heq; rewrite <-Heq.
                  apply Hvar.
              - (* x <> y *)
                not_Is_variable x y.
                rewrite PM.gso; [|assumption].
                apply IHeqs0; assumption.
            }
          * apply Forall_cons.
            2:now apply Memory_Corres_eqs_add_obj with (1:=IHeqs1) (2:=Hniii).
            constructor.
            intros Mo' Hmfind'.
            rewrite Hmfind in Hmfind'.
            injection Hmfind'; intro Heq; rewrite <-Heq in *; clear Heq Hmfind'.
            exists omenv'.
            split; [rewrite mfind_inst_gss; reflexivity|exact Hnmc].

        + (* y = absent *)
          exists menv', env'.

          assert (Habs: absent_list ls n ->
                        Forall (rhs_absent_instant (bk0 n) (restr Hn n)) neqs)
            by (eapply subrate_property_eqns; eauto;
                apply sem_vars_gt0 with (1:=ingt0) (2:=Hlsn)).

          assert (absent_list ls n)
            by (unfold absent_list; now rewrite H0, map_map).

          assert (xs n = absent) as Hout'
              by (apply Hout; auto).

          split; [|split].
          * apply stmt_eval_translate_eqns_cons.
            exists menv', env'.
            split; [exact Hstmt|].
            rewrite Hbase in *.
            apply stmt_eval_Control_absent.
            eapply clock_correct_false; eauto.
          * intros x Hivi c.
            destruct (Is_variable_in_dec x eqs) as [Hvin|Hvin];
              [now apply IHeqs0 with (1:=Hvin)|].
            apply stmt_eval_translate_eqns_env_inv with (2:=Hvin) in Hstmt.
            rewrite Hstmt.
            inversion_clear Hivi as [? ? Hivi'|];
              [|unfold Is_variable_in_eqs in Hvin; contradiction].
            inversion Hivi' as [|x' ck' f' e ty' HR1 [HR2 HR3 HR4]];
              subst x' ck' f' x e ty'.
            split; intro Hsv'.
            { inversion_clear Hsv' as [Hfind'].
              inversion_clear Hvar as [Hfind''].
              rewrite Hfind' in Hfind''.
              injection Hfind''; intro HR1;
                rewrite <-HR1 in *; clear HR1 Hfind''.
              discriminate. }
            { assert (PM.find y env = None) as Hnone
                  by (apply Henv; repeat constructor).
              rewrite Hnone in Hsv'.
              discriminate. }
          * apply Forall_cons; [|now apply IHeqs1].
            constructor.
            intros Mo' Hmfind'.
            rewrite Hmfind in Hmfind'.
            injection Hmfind'; intro He; rewrite <-He in *; clear He Hmfind'.
            exists omenv.
            rewrite stmt_eval_translate_eqns_minst_inv
              with (1:=Hstmt) (2:=Hniii).
            split; [exact Hfindo|].
            eapply Memory_Corres_unchanged; eauto.

      - (* Case EqFby: y = v0 fby lae *)
        specialize (Hlae n).
        assert (equiv_env (fun x => Is_free_in_laexp x ck le)
                          (restr H n) mems env' menv')
          as Hlae'.
        {
          intros.
          split; intro Hmems.

          - assert (Hdecide_x: Is_variable_in_eqs x eqs \/ In x inputs)
              by (eapply Is_well_sch_free_variable;
                   eassumption || constructor (assumption)).

            destruct Hdecide_x; try subst x.
            + apply IHeqs0; assumption.
            + erewrite stmt_eval_translate_eqns_env_inv; try eassumption.
              apply Hin; now eauto.
              apply not_Is_defined_in_not_Is_variable_in.
              intro. eapply Hin2; eauto. econstructor(eassumption).

          - assert (~ Is_defined_in_eqs x eqs)
              by (eapply Is_well_sch_free_variable_in_mems;
                   eassumption || constructor (assumption)).
            specialize (Hinmems _ Hmems); destruct Hinmems.
            erewrite stmt_eval_translate_eqns_menv_inv; try eassumption.
            eapply Is_memory_in_msem_var in H1; try eassumption.
            do 2 destruct H1; subst c.
            assert (Is_defined_in_eqs x alleqs) by intuition.
            assert (~ Is_variable_in_eqs x alleqs) by intuition.
            erewrite Is_memory_in_Memory_Corres_eqs; try eauto.
        }

        inversion Hlae; subst ck0 ce;
        match goal with
        | H: present _ = ls n |- _ => rewrite <- H in *
        | H: absent = ls n |- _ => rewrite <- H in *
        end;
        destruct Hvar as [Hms Hvar].
        + (* y = present *)
          rename c into v.
          exists (madd_mem y v menv'), env'.
          split; [|split].
          * apply stmt_eval_translate_eqns_cons.
            exists menv', env'.
            split; [exact Hstmt|].
            apply stmt_eval_Control_present.
            eapply clock_correct_true; now eauto.
            econstructor.
            rewrite Hbase in *.
            eapply lexp_correct; now eauto.
            reflexivity.
          * intros x Hivi c.
            inversion_clear Hivi as [? ? Hivi'|]; [now inversion_clear Hivi'|].
            apply IHeqs0.
            assumption.
          * rewrite <-Hms.
            apply Forall_cons.
            2:now apply Memory_Corres_eqs_add_mem with (1:=Hmfind) (2:=IHeqs1).
            constructor.
            intros ms' Hmfind'.
            rewrite Hmfind in Hmfind'.
            injection Hmfind'; intro Heq; rewrite <-Heq in *; clear Hmfind' Heq.
            now apply mfind_mem_gss.
        + (* y = absent *)
          exists menv', env'.
          split; [|split].
          * apply stmt_eval_translate_eqns_cons.
            exists menv', env'.
            split; [exact Hstmt|].
            rewrite Hbase in *;
              apply stmt_eval_Control_absent.
            eapply clock_correct_false; eauto.
          * intros x Hivi c.
            destruct (Is_variable_in_dec x eqs) as [Hvin|Hvin];
              [now apply IHeqs0 with (1:=Hvin)|].
            apply stmt_eval_translate_eqns_env_inv with (2:=Hvin) in Hstmt.
            rewrite Hstmt.
            inversion_clear Hivi as [? ? Hivi'|];
              [|unfold Is_variable_in_eqs in Hvin; contradiction].
            inversion_clear Hivi'.
          * {
              constructor.
              2:assumption.
              constructor.
              intros ms0' Hmfind'.
              rewrite Hmfind in Hmfind'.
              injection Hmfind'; intro Heq; rewrite <-Heq in *;
                clear Heq Hmfind'.
              (* TODO: do we really need this? We seem to *know* that it
        cannot be equal ([exfalso] branch). If unnecessary, remove the
        import on Dataflow.IsDefined.Decide *)

              destruct (Is_defined_in_dec y eqs) as [Hxin|Hxin].        
              - Hint Constructors Is_defined_in_eq.
                exfalso.
                inversion_clear Hwsch;
                  match goal with 
                  | H: context[~ Is_defined_in_eqs _ _] |- _ =>
                    eapply H
                  end; eauto.
                
              - eauto.
                rewrite Hall in Hmc.
                apply Forall_app in Hmc.
                destruct Hmc as [HZ Hmc]; clear HZ.
                apply Forall_cons2 in Hmc.
                destruct Hmc as [Hmc HZ]; clear HZ.
                inversion_clear Hmc as [| |? ? ? ? ? ? Hfindc].
                rewrite Hms.
                eapply stmt_eval_translate_eqns_menv_inv in Hstmt;
                  try eassumption.
                rewrite Hstmt.
                eapply Hfindc; auto.
            }
    Qed.

  End IsStepCorrect.

  (** *** Correctness of [translate] *)

  Section IsNodeCorrect.

    Lemma equiv_prog_empty: equiv_prog [] (translate []).
    Proof.
      intro Hwdef.
      intros n **.
      exfalso.
      repeat match goal with
             | H: msem_node [] _ _ _ _ |- _ => inversion H; clear H
             | H: find_node _ [] = Some _ |- _ => inversion H; clear H
             end.
    Qed.
    
    Lemma adds_sem_var_find:
      forall Hn i (iargs: list (ident * type)) ivals c,
        NoDupMembers iargs ->
        In i (map fst iargs) ->
        Forall2 (sem_var_instant Hn) (map fst iargs) (map present ivals) ->
        (sem_var_instant Hn i (present c)
        <-> PM.find i (adds iargs ivals sempty) = Some c).
    Proof.
      intros ** Hndup Hin Hsem.
      assert (length (map fst iargs) = length (map present ivals)) as Hlen
        by (apply Forall2_length with (1:=Hsem)).
      apply Forall2_combine in Hsem.
      unfold adds.
      assert (PM.find i (fold_right
                            (fun (xbv : ident * type * val) (env : PM.t val) =>
                               let '(x, _, v) := xbv in PM.add x v env)
                            sempty (combine iargs ivals)) = Some c
              <-> PM.find i (fold_right (fun (xv : ident * value) env =>
                                           PM.add (fst xv) (snd xv) env)
                    (PM.empty _) (combine (map fst iargs) (map present ivals)))
                  = Some (present c)) as Hfeq.
      - clear Hndup Hin Hsem.
        rewrite combine_map_both.
        assert (forall x c, PM.find x sempty = Some c
                            <-> PM.find x (PM.empty value) = Some (present c))
          as Hrem by (intros; rewrite 2 PM.gempty; split; inversion 1).
        revert Hrem.
        generalize (combine iargs ivals), sempty, (PM.empty value).
        intro xs. induction xs as [|x xs]; [now auto|].
        intros S T Hrem.
        destruct x as [x ty]. destruct x as [i' ?]. simpl.
        destruct (equiv_dec i i') as [Heq|Hneq].
        + rewrite Heq.
          rewrite 2 PM.gss.
          split; injection 1; intro; now subst.
        + rewrite 2 PM.gso; try easy.
          now apply IHxs.
      - rewrite Hfeq; clear Hfeq.
        apply fst_NoDupMembers in Hndup.
        apply In_InMembers_combine with (1:=Hlen) in Hin.
        apply NoDup_NoDupMembers_combine with (ys:=map present ivals) in Hndup.
        revert Hndup Hin Hsem.
        generalize (combine (map fst iargs) (map present ivals)).
        clear Hlen iargs ivals.
        intros xs Hndup Hin Hsem.
        induction xs as [|ity xs]; [now inversion Hin|].
        simpl.
        destruct ity as [i' v'].
        apply nodupmembers_cons in Hndup.
        destruct Hndup as [Hnin Hndup].
        destruct Hin as [Heq|Hneq].
        + rewrite Heq in *.
          rewrite PM.gss.
          inversion_clear Hsem as [|? ? Hvar Hsem'].
          split; intro HH.
          now apply sem_var_instant_det with (1:=Hvar) in HH; rewrite HH.
          injection HH; intro Heq'; now rewrite <-Heq'.
        + rewrite PM.gso.
          2:intro Heq; rewrite Heq in *; contradiction.
          inversion_clear Hsem.
          apply IHxs; auto.
    Qed.

    Theorem is_node_correct:
      forall (G: global),
        (* =is_node_correct= *)
        Welldef_global G ->
        equiv_prog G (translate G).
    (* =end= *)
    Proof.
      (* TODO: Develop a version of msem_node_mult that works for eqs? *)
      induction G as [|node G IH].
      - intro; apply equiv_prog_empty.
      - intros Hwd f n xs ys M menv inputs output Hmc Hmsem Hxs Hys.
        set (nodeName := n_name node).

        assert (Welldef_global G) as HwdG
            by (eapply Welldef_global_cons; eassumption).

        assert (Ordered_nodes (node::G)) as Hord
            by (apply Welldef_global_Ordered_nodes; assumption).

        destruct (ident_eqb nodeName f) eqn:Hfeq.
        + (* Case: f = nodeName *)
          assert (nodeName = f)
            by (apply Pos.eqb_eq; assumption).
          subst f.

          set (prog := translate (node :: G)).

          inversion_clear Hwd as [|? ? Hwd' eqs Hwsch Hndef_in Hfind Hnodup].
          clear Hwd'.
          inversion_clear Hmsem as [? ? ? ? ? ? ? ? ? ? ? ? ? ? Hck Heqs
                                      [H [Hin [Hout [Hrabs Hall]]]]].
          subst eqs nodeName.
          simpl in Heqs; rewrite Hfeq in Heqs; simpl in Heqs.
          injection Heqs. intro Hnode. rewrite Hnode in *. clear Heqs. simpl in *.

          assert (i = node.(n_in) /\ o = node.(n_out) /\ eqs0 = node.(n_eqs))
            as HR by (rewrite Hnode; intuition).
          destruct HR as (HR1 & HR2 & HR3). subst i o eqs0.

          set (env := adds node.(n_in) inputs sempty).

          assert (msem_equations G bk H M node.(n_eqs))
            by (eapply Forall_msem_equation_global_tl; try eassumption).

          assert (exists (menv' : heap) (env' : stack),
                     stmt_eval (translate G) menv env
                       (translate_eqns (memories node.(n_eqs)) node.(n_eqs))
                       (menv', env') /\
                     (forall x : ident,
                         Is_variable_in_eqs x node.(n_eqs) ->
                         forall c : val,
                           sem_var_instant (restr H n) x (present c) <->
                           PM.find x env' = Some c) /\
                     Forall (Memory_Corres_eq G (S n) M menv') node.(n_eqs))
            as His_step_correct.
          {
            eauto.
            eapply is_step_correct; eauto.
            - apply Hck; eauto.
            - exists []; auto.
            - intros y Hinm.
              assert (NoDup_defs node.(n_eqs)) as Hndds
                  by (eapply Is_well_sch_NoDup_defs; eauto).
              split; [now apply Is_defined_in_memories
                     |now apply not_Is_variable_in_memories].
            - intros c input Hinput.
              subst env.
              specialize (Hin n). rewrite Hxs in Hin.
              now apply adds_sem_var_find with (1:=NoDupMembers_app_l _ _ nodup)
                                               (2:=Hinput) (3:=Hin).
            - intros x Hivi.
              subst env.
              destruct (in_dec ident_eq_dec x (map fst node.(n_in)))
                as [HinA|HninA].
              + apply Is_variable_in_eqs_Is_defined_in_eqs in Hivi.
                contradiction (not_Exists_Is_defined_in_eqs_n_in node).
                apply Exists_exists. exists x; intuition.
              + assert (~InMembers x node.(n_in)) as Hninm
                    by (intro; apply HninA; now apply fst_InMembers).
                apply NotInMembers_find_adds with (1:=Hninm).
                apply PM.gempty.
            - intros input Hinput Hisdef.
              contradiction (not_Exists_Is_defined_in_eqs_n_in node).
              apply Exists_exists. exists input; intuition.
            - inversion_clear Hmc as [? ? ? ? ? ? ? ? ? ? ? ? Hf Hmeqs].
              simpl in Hf.
              rewrite ident_eqb_refl in Hf.
              injection Hf; intros Heq0 Heq1 Heq2 Heq3.
              rewrite <-Heq0 in *.
              eapply Memory_Corres_eqs_node_tl; try eassumption.
          }

          destruct His_step_correct as (menv' & env' & Hstmt & Hsemvar & Hmem).
          exists menv'.
          split.
          * { destruct (exists_step_method node) as [stepm Hstepm].
              econstructor; eauto.
              - simpl. rewrite Pos.eqb_refl. reflexivity.
              - subst env.
                simpl in Hstepm.
                rewrite ident_eqb_refl in Hstepm.
                injection Hstepm.
                clear Hstepm. intro Hstepm.
                rewrite <-Hstepm, Hnode. clear Hstepm.
                simpl in *.
                rewrite ps_from_list_gather_eqs_memories.
                eassumption.
              - rewrite find_method_stepm with (1:=Hstepm).
                specialize (Hout n); simpl in Hout; rewrite Hys in Hout.
                constructor; auto.
                apply Hsemvar.
                apply n_out_variable_in_eqs.
                assumption.
            }
          * {
              econstructor.
              - simpl; rewrite Pos.eqb_refl; reflexivity.
              - eapply Memory_Corres_eqs_node_tl; eassumption.
            }

        + (* Case: f <> nodeName *)
          assert (nodeName <> f) as Hfneq
              by (eapply Pos.eqb_neq; try eassumption).

          rewrite Memory_Corres_node_tl in Hmc; try eassumption.
          apply msem_node_cons in Hmsem; try eassumption.
          eapply IH in HwdG.
          edestruct HwdG as [menv' [Hstmt' Hmc']]; try eassumption.
          inversion_clear Hstmt'.
          exists menv'; split.
          * econstructor; try eassumption.
            simpl. subst nodeName. rewrite Hfeq.
            eassumption.
          * rewrite Memory_Corres_node_tl; try assumption.
    Qed.

  End IsNodeCorrect.

  (** *** Correctness of the [reset] code *)

  (* TODO: remove after rewrite of translate_reset_eqns *)
  Lemma stmt_eval_translate_reset_eqn_shift:
    forall prog eqs iacc menv env menv' env',
      stmt_eval prog menv env
                (List.fold_left translate_reset_eqn eqs iacc)
                (menv', env')
      <->
      exists menv'' env'',
        stmt_eval prog menv env
                  (List.fold_left translate_reset_eqn eqs Skip)
                  (menv'', env'')
        /\
        stmt_eval prog menv'' env'' iacc (menv', env').
  Proof.
    Hint Constructors stmt_eval.
    induction eqs as [|eq eqs IH].
    - split; [ now eauto | ].
      intro H; do 2 destruct H.
      destruct H as [H0 H1].
      inversion_clear H0; apply H1.
    - intros.
      split.
      + intro H0.
        apply IH in H0.
        destruct H0 as [menv'' [env'' [H0 H1]]].
        destruct eq; [now eauto| |];
        inversion_clear H1;
        exists menv1; exists env1;
        split; try (simpl; apply IH); eauto.
      + intros.
        destruct eq; [ now (apply IH; auto) | |];
        (apply IH;
          simpl in H;
          destruct H as [menv'' [env'' [H0 H1]]];
          apply IH in H0;
          destruct H0 as [menv0 [env0 [H2 H3]]];
          exists menv0; exists env0;
          split; [now auto|];
          inversion_clear H3;
          inversion H0; subst;
          econstructor; eauto).
  Qed.

  Lemma stmt_eval_translate_reset_eqns_cons:
    forall prog menv env (eq:equation) eqs P,
      (exists menv'' env'',
          stmt_eval prog menv env
                    (translate_reset_eqns (eq :: eqs)) (menv'', env'')
          /\ P menv'' env'')
      <->
      (exists menv' env' menv'' env'',
          stmt_eval prog menv env (translate_reset_eqns eqs) (menv', env')
          /\ stmt_eval prog menv' env'
                      (translate_reset_eqn Skip eq) (menv'', env'')
          /\ P menv'' env'').
  Proof.
    split.
    - intro H.
      destruct H as [menv'' [env'' H]].
      unfold translate_reset_eqns in H.
      simpl in H.
      destruct H as [H HP].
      apply stmt_eval_translate_reset_eqn_shift in H.
      destruct H as [menv' [env' [H1 H2]]].
      exists menv', env', menv'', env''.
      now intuition.
    - intro H.
      destruct H as [menv' [env' [menv'' [env'' [H1 [H2 HP]]]]]].
      unfold translate_reset_eqns.
      simpl.
      exists menv'', env''.
      intuition.
      apply stmt_eval_translate_reset_eqn_shift.
      exists menv', env'.
      intuition.
  Qed.

  Definition equiv_reset G prog f :=
    forall xs ys M,
      msem_node G f xs M ys
      -> forall menv,
        exists menv',
          stmt_call_eval prog menv f reset [] menv' []
        /\ Memory_Corres G 0 f M menv'.

  (* TODO: remove/factorize with equiv_prog *)
  Lemma equiv_reset_empty: forall f, equiv_reset [] (translate []) f.
  Proof.
    intro Hwdef.
    intros n **.
    exfalso.
    repeat match goal with
           | H: msem_node [] _ _ _ _ |- _ => inversion H; clear H
           | H: find_node _ [] = Some _ |- _ => inversion H; clear H
           end.
  Qed.

  Section IsResetCorrect.

    Variables (G: global)
              (HG: Welldef_global G)
              (H: history)
              (M: memory)
              (mems: PS.t)
              (inputs: list ident).


    Lemma is_reset_correct:
      forall bk eqs,
        msem_equations G bk H M eqs ->
        Is_well_sch mems inputs eqs ->
        (forall f, equiv_reset G (translate G) f) ->
        forall menv,
        exists menv' env',
          stmt_eval (translate G) menv sempty (translate_reset_eqns eqs)
                    (menv', env')
          /\ Forall (Memory_Corres_eq G 0 M menv') eqs.
    Proof.
      intros * Hmsem Hwsch Hreset.
      induction eqs as [|eq eqs IH]; [eauto|].
      intro menv.
      destruct eq as [i ck e | i ck f e | i ck v e];
        inversion_clear Hmsem as [| ? ? Hsem Hmsem' ];
        inversion_clear Hwsch;
        edestruct IH as [menv' [env' [Hstmt Hmc]]]; try eassumption.
      - (* EqDef *)
        Hint Constructors Forall.
        Hint Constructors Memory_Corres_eq.
        eauto.
      - (* EqApp *)
        unfold translate_reset_eqns; simpl.
        inversion_clear Hsem
          as [|? ? ? ? ? ? Mo ? ? xs' ys' Hmfind Hxs' Hys' HsemNode|].
        set (omenv := match mfind_inst i menv' with
                      | Some m => m | None => hempty end).
        assert (exists omenv',
                   stmt_call_eval (translate G) omenv f reset [] omenv' []
                   /\ Memory_Corres G 0 f Mo omenv')
          as [omenv' [Hstmt_reset Hmcf]]
          by (eapply Hreset; try eassumption).
        exists (madd_obj i omenv' menv'), env'.
        split.
        + rewrite stmt_eval_translate_reset_eqn_shift.
          exists menv', env'.
          split; try eassumption.
          econstructor; [|constructor].
          subst omenv.
          econstructor; eauto.
        + repeat constructor; [| apply Memory_Corres_eqs_add_obj; eauto].
          intros M' Hmfind'.
          rewrite Hmfind in Hmfind'; injection Hmfind'; intro Heq; subst M'.
          exists omenv'.
          rewrite mfind_inst_gss.
          auto.
      - (* EqFby *)
        exists (madd_mem i (sem_const v) menv'), env'.
        split.
        + unfold translate_reset_eqns; simpl;
          rewrite stmt_eval_translate_reset_eqn_shift.
          exists menv', env'.
          Hint Constructors stmt_eval.
          eauto.
        + inversion_clear Hsem as [| | ? ? ? ? ? ? ? ? ? ? Hmfind Hms Hlae Hls].
          rewrite <- Hms.
          constructor; [|apply Memory_Corres_eqs_add_mem; assumption].
          constructor. intros ms' Hmfind'.
          rewrite Hmfind in Hmfind'.
          injection Hmfind'; intro HR; rewrite HR in *; clear HR Hmfind'.
          rewrite mfind_mem_gss.
          reflexivity.
    Qed.

  End IsResetCorrect.

  Theorem is_node_reset_correct:
    forall (G: global) f,
      Welldef_global G ->
      equiv_reset G (translate G) f.
  Proof.
    induction G as [|node G IH].
    - intros f Hwd.
      apply equiv_reset_empty.
    - intros f Hwdef xs ys M Hmsem menv.

      assert (Ordered_nodes (node :: G)) as HordG
          by (apply Welldef_global_Ordered_nodes; assumption).

      set (nodeName := n_name node).

      destruct (ident_eqb nodeName f) eqn:Heqb.
      + assert (nodeName = f) as Hfeq
            by (apply Pos.eqb_eq; assumption).
        inversion_clear Hmsem as [? ? ? ? ? inArgs outArg v eqs
                                    ingt0 defd vout nodup good
                                    Hbk Hfind [H [Hin [Hout [Hrhs Hmsem']]]]].
        rename Hmsem' into Hmsem.

        specialize (Hin 0)%nat; specialize (Hout 0)%nat;
        simpl in Hin, Hout.

        simpl in Hfind; subst nodeName; rewrite Heqb in Hfind;
        injection Hfind; clear Hfind; intro Hfind.

        assert (msem_equations G bk H M eqs).
        {
          inversion_clear Hwdef. subst eqs0; rewrite Hfind in *; simpl in *.
          eapply Forall_msem_equation_global_tl; try eassumption.
        }

        set (inArgs_fst := map fst inArgs).
        assert (Is_well_sch (memories eqs) inArgs_fst eqs)
          by (inversion Hwdef; subst inArgs_fst eqs0; now rewrite Hfind in *).

        assert (Welldef_global G)
          by (inversion Hwdef; assumption).

        assert (exists menv' env',
                   stmt_eval (translate G) menv sempty
                             (translate_reset_eqns eqs)
                             (menv', env')
                   /\ Forall (Memory_Corres_eq G 0 M menv') eqs)
          as [menv' [env' [Hstmt Hmc]]].
        {
          eapply is_reset_correct; try eassumption.
          intro; apply IH; assumption.
        }

        exists menv'.
        split.
        * { econstructor.
            - simpl. rewrite Heqb. reflexivity.
            - apply exists_reset_method.
            - unfold adds. rewrite Hfind. simpl.
              unfold adds. simpl. eassumption.
            - constructor.
          }
        * {
            econstructor.
            - simpl; rewrite Heqb. subst node. reflexivity.
            - apply Memory_Corres_eqs_node_tl; try assumption.
              inversion Hwdef. subst eqs0. rewrite Hfind in *.
              simpl. assumption.
          }

      + assert (nodeName <> f) as Hfneq
            by (apply Pos.eqb_neq; assumption).

        apply Welldef_global_cons in Hwdef.
        apply msem_node_cons in Hmsem; try assumption.
        edestruct IH as [menv' [Hstmt Hmc]]; try eassumption.
        exists menv'; split.
        * inversion_clear Hstmt.
          econstructor; try eassumption.
          simpl. subst nodeName. rewrite Heqb.
          eassumption.
        * apply Memory_Corres_node_tl; eassumption.
  Qed.

  (** ** Correctness, from the point of view of the event loop *)

  Section EventLoop.

    Variables (G     : global)
              (main  : ident)
              (css   : stream (list const))
              (ys    : stream value)
              (r     : ident)
              (ty    : type)
              (obj   : ident)
              (Hwdef : Welldef_global G).

    Let xss := fun n => map (fun c => present (sem_const c)) (css n).

    Variable (Hsem: sem_node G main xss ys).

    (* TODO: Tim: It seems a little bit strange to interpret the system input
                  as a stream of constant values that is 'passed' to a program
                  by converting them into expressions at each instant.
                  Maybe it would be better to put them in envN and execute
                  a statement whose arguments are the corresponding variable
                  names? *)
    
    Open Scope nat_scope.
    (* =step= *)
    Fixpoint dostep (n: nat) P r main obj css menv env: Prop :=
      match n with
      | 0 => stmt_eval P hempty sempty (Call [] main obj reset []) (menv, env)
      | S n => let cs := map Const (css n) in
               exists menvN envN, dostep n P r main obj css menvN envN
               /\ stmt_eval P menvN envN (Call [(r, ty)] main obj step cs)
                            (menv, env)
      end.
    (* =end= *)

    Lemma is_event_loop_correctG:
      forall M,
        let P := translate G in
        msem_node G main xss M ys ->
        forall n,
        exists menv env omenv,
          dostep (S n) P r main obj css menv env
          /\ mfind_inst obj menv = Some omenv
          /\ Memory_Corres G (S n) main M omenv
          /\ (forall co, ys n = present co <-> PM.find r env = Some co).
    Proof.
      intros * Hmsem n.
      assert (exists menv' env',
                 stmt_eval (translate G) hempty sempty
                           (Call [] main obj reset []) (menv', env')
                 /\ (exists omenv0, mfind_inst obj menv' = Some omenv0
                                    /\ Memory_Corres G 0 main M omenv0))
        as (menv0 & env0 & Hstmtr & (omenv0 & Hmf0 & Hmc0)).
      {
        pose proof (is_node_reset_correct _ _ Hwdef _ _ _ Hmsem hempty) as Hrst.
        destruct Hrst as (omenv' & Hcall & Hcor).
        intros. do 2 eexists.
        split.
        - econstructor; eauto.
          rewrite mfind_inst_empty. eassumption.
        - exists omenv'.
          split; auto.
          apply mfind_inst_gss.
      }

      set (ci0 := css 0).

      assert (Hpres: present_list xss 0 (map sem_const ci0))
        by (subst xss; unfold present_list; rewrite map_map; eauto).

      assert (exists co0, ys 0 = present co0)%nat as [co0 Hco0].
      {
        inversion_clear Hmsem as
            [? ? ? ? ? ? ? ? ? ? ? ? ? ? Hbk Hfind
                [H [Hsem_in [Hsem_out [Habs Hsem_eqns]]]]].
        apply not_absent_present;
          rewrite <- Habs;
          eapply not_absent_present_list; eauto.
        subst ci0.
        pose proof (sem_vars_gt0 _ _ _ _ ingt0 Hsem_in) as Hxssgt0.
        specialize (Hxssgt0 0).
        rewrite Hpres, map_length in Hxssgt0.
        assumption.
      }

      induction n.
      - (* Case: n ~ 0 *)

        assert (exists menv' env',
                   stmt_eval (translate G) menv0 env0
                             (Call [(r, ty)] main obj step (map Const ci0))
                             (menv', env')
                   /\ (exists omenv, mfind_inst obj menv' = Some omenv
                                     /\ Memory_Corres G 1 main M omenv)
                   /\ PM.find r env' = Some co0)
          as (menv' & env' & Hstmt & (omenv & Hmfind & Hmc) & Hout).
        { pose proof (is_node_correct _ Hwdef _ _ _ _ _ omenv0 _ _
                                      Hmc0 Hmsem Hpres Hco0)
            as (omenv' & Hstmt & Hmc1).
          do 2 eexists.
          repeat split.
          - econstructor; eauto.
            2:rewrite Hmf0; now eapply Hstmt.
            clear Hstmt Hpres.
            induction ci0; simpl; auto.
          - exists omenv'. split; auto.
            now rewrite mfind_inst_gss.
          - unfold adds. simpl. now rewrite PM.gss.
        }

        do 3 eexists.
        split; [|split; [| split]]; try eauto.
        + do 2 eexists; eauto.
        + rewrite Hco0. intro co0'.
          split; try rewrite Hout;
            now injection 1; intro; subst.

      - (* Case: n ~ S n *)

        destruct IHn as [menvN [envN [omenvN [HstepN [HmfindN [HmcN HeqN]]]]]].

        set (ciSn := css (S n)).

        assert (HpresN: present_list xss (S n) (map sem_const ciSn))
          by (subst xss; unfold present_list; rewrite map_map; eauto).

        assert (exists coSn, ys (S n) = present coSn) as [coSn Hys].
        {
          inversion_clear Hmsem as
              [? ? ? ? ? ? ? ? ? ? ? ? ? ? Hbk Hfind
                  [H [Hsem_in [Hsem_out [Habs Hsem_eqns]]]]].
          apply not_absent_present; rewrite <- Habs;
            eapply not_absent_present_list; eauto.
          eapply Forall2_length in Hsem_in.
          rewrite HpresN in Hsem_in.
          rewrite 2 map_length in Hsem_in.
          now rewrite <-Hsem_in.
        }

        assert (exists menvN' envN',
                   stmt_eval (translate G) menvN envN
                             (Call [(r, ty)] main obj step (map Const ciSn))
                             (menvN', envN')
                   /\ (exists omenvsN, mfind_inst obj menvN' = Some omenvsN
                                    /\ Memory_Corres G (S (S n)) main M omenvsN)
                   /\ PM.find r envN' = Some coSn)
          as (menvSn & envsN & Hstmt & (omenvSn & Hmfind & Hmc) & Hout).
        { pose proof (is_node_correct _ Hwdef _ _ _ _ _ omenvN _ _
                                      HmcN Hmsem HpresN Hys)
            as (omenvsN & Hstmt & HmcSn).
          do 2 eexists.
          repeat split.
          - econstructor; eauto.
            2:rewrite HmfindN; now eapply Hstmt.
            clear Hstmt HpresN.
            induction ciSn; simpl; auto.
          - exists omenvsN. split; auto.
            now rewrite mfind_inst_gss.
          - unfold adds. simpl. now rewrite PM.gss.
        }

        (* XXX: this explicit [exists] is necessary:
                Coq picks a wrong instance otherwise. *)
        exists (menvSn).
        do 2 eexists.

        split; [|split; [| split]]; eauto.
        + do 2 eexists; split; simpl step; try eauto.
        + rewrite Hys. intro coSn'.
          split; try rewrite Hout;
            now injection 1; intro; subst.
    Qed.

    Theorem is_event_loop_correct:
      (* =translate_correct= *)
      sem_node G main xss ys ->
      forall n, exists menv env,
          dostep (S n) (translate G) r main obj css menv env
          /\ (forall co, ys n = present co <-> PM.find r env = Some co).
    (* =end= *)
    Proof.
      intros until n.

      assert (exists M, msem_node G main xss M ys) as [M Hmsem]
          by (eapply sem_msem_node; eauto).

      assert (exists menv env omenv,
                 dostep (S n) (translate G) r main obj css menv env
                 /\ mfind_inst obj menv = Some omenv
                 /\ Memory_Corres G (S n) main M omenv
                 /\ (forall co, ys n = present co <-> PM.find r env = Some co))
        as [menv [env [omenv [Hstep [_ [_ Hys]]]]]]
          by (eapply is_event_loop_correctG; eauto).

      do 2 eexists; eauto.
    Qed.

  End EventLoop.

  (** ** Correctness of optimized code *)

  Lemma not_Can_write_in_translate_cexp:
    forall x mems ce i,
      x <> i -> ~ Can_write_in i (translate_cexp mems x ce).
  Proof.
    induction ce; intros j Hxni Hcw.
    - specialize (IHce1 _ Hxni).
      specialize (IHce2 _ Hxni).
      inversion_clear Hcw; intuition.
    - specialize (IHce1 _ Hxni).
      specialize (IHce2 _ Hxni).
      inversion_clear Hcw; intuition.
    - inversion Hcw; intuition.
  Qed.

  Lemma Is_free_in_tovar:
    forall mems i j ty,
      Is_free_in_exp j (tovar mems (i, ty)) <-> i = j.
  Proof.
    unfold tovar.
    intros mems i j ty.
    destruct (PS.mem i mems); split; intro HH;
    (inversion_clear HH; reflexivity || subst; now constructor).
  Qed.

  Lemma Is_free_translate_lexp:
    forall j mems l,
      Is_free_in_exp j (translate_lexp mems l) -> Is_free_in_lexp j l.
  Proof.
    induction l; simpl; intro H.
    - inversion H.
    - now apply Is_free_in_tovar in H; subst.
    - constructor; auto.
    - constructor; inversion H; auto.
    - constructor; inversion H; subst.
      destruct H2; [left; auto | right; auto].
  Qed.
  
  Lemma IsFusible_translate_cexp:
    forall mems x ce,
      (forall i, Is_free_in_cexp i ce -> x <> i)
      -> IsFusible (translate_cexp mems x ce).
  Proof.
    intros mems x ce Hfree.
    induction ce.
    - simpl; constructor;
      [apply IHce1; now auto|apply IHce2; now auto|].
      intros j Hfree'; split;
      (apply not_Can_write_in_translate_cexp;
        apply Is_free_in_tovar in Hfree';
        subst; apply Hfree; constructor).
    - simpl; constructor;
      [apply IHce1; now auto|apply IHce2; now auto|].
      intros j Hfree'; split;
      apply not_Can_write_in_translate_cexp;
      apply Hfree;
      now constructor; apply Is_free_translate_lexp with mems.
    - now constructor.
  Qed.

  Lemma IsFusible_Control_caexp:
    forall mems ck f ce,
      (forall i, Is_free_in_caexp i ck ce -> ~Can_write_in i (f ce))
      -> IsFusible (f ce)
      -> IsFusible (Control mems ck (f ce)).
  Proof.
    induction ck as [|ck IH i b]; [now intuition|].
    intros f ce Hxni Hfce.
    simpl.
    destruct b.
    - apply IH with (f:=fun ce=>Ifte (tovar mems (i, bool_type)) (f ce) Skip).
      + intros j Hfree Hcw.
        apply Hxni with (i0:=j); [inversion_clear Hfree; now auto|].
        inversion_clear Hcw as [| | |? ? ? ? Hskip| | |];
          [assumption|inversion Hskip].
      + repeat constructor; [assumption| |now inversion 1].
        apply Hxni.
        match goal with
        | H:Is_free_in_exp _ (tovar mems _) |- _ => rename H into Hfree
        end.
        unfold tovar in Hfree.
        destruct (PS.mem i mems); inversion Hfree; subst; now auto.
    - apply IH with (f:=fun ce=>Ifte (tovar mems (i, bool_type)) Skip (f ce)).
      + intros j Hfree Hcw.
        apply Hxni with (i0:=j); [inversion_clear Hfree; now auto|].
        inversion_clear Hcw as [| |? ? ? ? Hskip| | | |];
          [inversion Hskip|assumption].
      + repeat constructor; [assumption|now inversion 1|].
        apply Hxni.
        match goal with
        | H:Is_free_in_exp _ (tovar mems _) |- _ => rename H into Hfree
        end.
        unfold tovar in Hfree.
        destruct (PS.mem i mems); inversion Hfree; subst; now auto.
  Qed.

  Lemma IsFusible_Control_laexp:
    forall mems ck s,
      (forall i, Is_free_in_clock i ck -> ~Can_write_in i s)
      -> IsFusible s
      -> IsFusible (Control mems ck s).
  Proof.
    induction ck as [|ck IH i b]; [now intuition|].
    intros s Hxni Hfce.
    simpl.
    destruct b; apply IH.
    - intros j Hfree Hcw.
      apply Hxni with (i0:=j); [inversion_clear Hfree; now auto|].
      inversion_clear Hcw as [| | |? ? ? ? Hskip| | |];
        [assumption|inversion Hskip].
    - repeat constructor; [assumption| |now inversion 1].
      apply Hxni.
      rename H into Hfree.
      destruct (PS.mem i mems); inversion Hfree; subst; now auto.
    - intros j Hfree Hcw.
      apply Hxni with (i0:=j); [inversion_clear Hfree; now auto|].
      inversion_clear Hcw as [| |? ? ? ? Hskip| | | | ];
        [inversion Hskip|assumption].
    - repeat constructor; [assumption|now inversion 1|].
      apply Hxni.
      rename H into Hfree.
      destruct (PS.mem i mems); inversion Hfree; subst; now auto.
  Qed.

  Require Import Rustre.Dataflow.Clocking.
  Require Import Rustre.Dataflow.Clocking.Properties.

  Lemma translate_eqns_Ifte_free_write:
    forall C mems inputs eqs,
      Well_clocked_env C
      -> Forall (Well_clocked_eq C) eqs
      -> Is_well_sch mems inputs eqs
      -> (forall x, PS.In x mems -> ~Is_variable_in_eqs x eqs)
      -> (forall input, In input inputs -> ~ Is_defined_in_eqs input eqs)
      -> IsFusible (translate_eqns mems eqs).
  Proof.
    intros C mems inputs eqs Hwk Hwks Hwsch Hnvi Hnin.
    induction eqs as [|eq eqs IH]; [now constructor|].
    inversion Hwks as [|eq' eqs' Hwkeq Hwks']; subst.
    specialize (IH Hwks' (Is_well_sch_cons _ _ _ _ Hwsch)).
    unfold translate_eqns.
    simpl; apply IsFusible_fold_left_shift.
    split.
    - apply IH.
      + intros x Hin; apply Hnvi in Hin.
        apply not_Is_variable_in_cons in Hin.
        now intuition.
      + intros x Hin. apply Hnin in Hin.
        apply not_Is_defined_in_cons in Hin.
        now intuition.
    - clear IH.
      repeat constructor.
      destruct eq as [x ck e|x ck f e|x ck v0 e]; simpl.
      + assert (~PS.In x mems) as Hnxm
            by (intro Hin; apply Hnvi with (1:=Hin); repeat constructor).
        inversion_clear Hwsch as [|? ? Hwsch' HH Hndef].
        assert (forall i, Is_free_in_caexp i ck e -> x <> i) as Hfni.
        { intros i Hfree.
          assert (Hfree': Is_free_in_eq i (EqDef x ck e)) by auto.
          eapply HH in Hfree'.
          destruct Hfree' as [Hm Hnm].
          assert (~ In x inputs) as Hninp
            by (intro Hin; eapply Hnin; eauto; do 2 constructor).
          assert (~PS.In x mems) as Hnxm' by intuition.
          intro Hxi; rewrite Hxi in *; clear Hxi.
          specialize (Hnm Hnxm').
          eapply Hndef; intuition.
          now eapply Is_variable_in_eqs_Is_defined_in_eqs.
        }
        apply IsFusible_Control_caexp.
        intros i Hfree.
        apply (not_Can_write_in_translate_cexp).
        apply Hfni with (1:=Hfree).
        apply (IsFusible_translate_cexp).
        intros i Hfree; apply Hfni; intuition.
      + assert (~Is_free_in_clock x ck) as Hnfree
            by (apply Well_clocked_EqApp_not_Is_free_in_clock
                with (1:=Hwk) (2:=Hwkeq));
          apply IsFusible_Control_laexp; try intuition.
        match goal with H:Can_write_in _ _ |- _ => inversion_clear H end.
        match goal with H:InMembers _ _ |- _ => inversion_clear H end.
        subst. now apply Hnfree.
        contradiction.
      + assert (~Is_free_in_clock x ck) as Hnfree
            by (apply Well_clocked_EqFby_not_Is_free_in_clock
                with (1:=Hwk) (2:=Hwkeq));
        apply IsFusible_Control_laexp;
        [intros i Hfree Hcw; inversion Hcw; subst; contradiction|intuition].
  Qed.

End CORRECTNESS.

