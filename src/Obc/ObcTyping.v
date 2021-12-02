From Velus Require Import Common.
From Velus Require Import CommonTyping.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import VelusMemory.
From Velus Require Import Obc.ObcSyntax.
From Velus Require Import Obc.ObcSemantics.

From Coq Require Import Morphisms.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

(** * Obc typing *)

(**

  Typing judgements for Obc and resulting properties.
  Classify Obc programs which are statically well-formed.

 *)

Module Type OBCTYPING
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Syn   : OBCSYNTAX     Ids Op OpAux)
       (Import ComTyp: COMMONTYPING  Ids Op OpAux)
       (Import Sem   : OBCSEMANTICS  Ids Op OpAux Syn).

  Section WellTyped.

    Variable p     : program.
    Variable insts : list (ident * ident).
    Variable Γm  : list (ident * type).
    Variable Γv  : list (ident * type).

    Inductive wt_exp : exp -> Prop :=
    | wt_Var: forall x ty,
        In (x, ty) Γv ->
        wt_exp (Var x ty)
    | wt_State: forall x ty,
        In (x, ty) Γm ->
        wt_exp (State x ty)
    | wt_Const: forall c,
        wt_exp (Const c)
    | wt_Enum: forall c tn,
        In tn p.(enums) ->
        c < snd tn ->
        wt_exp (Enum c (Tenum tn))
    | wt_Unop: forall op e ty,
        type_unop op (typeof e) = Some ty ->
        wt_exp e ->
        wt_exp (Unop op e ty)
    | wt_Binop: forall op e1 e2 ty,
        type_binop op (typeof e1) (typeof e2) = Some ty ->
        wt_exp e1 ->
        wt_exp e2 ->
        wt_exp (Binop op e1 e2 ty)
    | wt_Valid: forall x ty,
        In (x, ty) Γv ->
        wt_exp (Valid x ty).

    (* TODO: eliminate the result types in Call (and EqApp). *)
    Inductive wt_stmt : stmt -> Prop :=
    | wt_Assign: forall x e,
        In (x, typeof e) Γv ->
        wt_exp e ->
        wt_stmt (Assign x e)
    | wt_AssignSt: forall x e,
        In (x, typeof e) Γm ->
        wt_exp e ->
        wt_stmt (AssignSt x e)
    | wt_Switch: forall e ss d tn,
        wt_exp e ->
        typeof e = Tenum tn ->
        In tn p.(enums) ->
        snd tn = length ss ->
        wt_stmt d ->
        (forall s, In (Some s) ss -> wt_stmt s) -> (* cannot write it with Forall and or_default_with because of positive occurence check *)
        wt_stmt (Switch e ss d)
    | wt_Comp: forall s1 s2,
        wt_stmt s1 ->
        wt_stmt s2 ->
        wt_stmt (Comp s1 s2)
    | wt_Call: forall clsid cls p' o f fm ys es,
        In (o, clsid) insts ->
        find_class clsid p = Some(cls, p') ->
        find_method f cls.(c_methods) = Some fm ->
        NoDup ys ->
        Forall2 (fun y xt => In (y, snd xt) Γv) ys fm.(m_out) ->
        Forall2 (fun e xt => typeof e = snd xt) es fm.(m_in) ->
        Forall wt_exp es ->
        wt_stmt (Call ys clsid o f es)
    | wt_Skip:
        wt_stmt Skip.

  End WellTyped.

  Definition wt_method (p     : program)
                       (insts : list (ident * ident))
                       (Γm  : list (ident * type))
                       (m     : method) : Prop
    := wt_stmt p insts Γm (meth_vars m) m.(m_body)
       /\ (forall x tn,
             In (x, Tenum tn) (meth_vars m) ->
             In tn (enums p)
             /\ 0 < snd tn).

  Definition wt_class (p : program) (cls: class) : Prop
    := (Forall (fun ocls=> find_class (snd ocls) p <> None) cls.(c_objs))
       /\ Forall (wt_method p cls.(c_objs) cls.(c_mems)) cls.(c_methods).

  Definition wt_program := CommonTyping.wt_program wt_class.

  Hint Constructors wt_exp wt_stmt: obctyping.

  Global Instance wt_exp_Proper:
    Proper (@eq program
                ==> @Permutation.Permutation (ident * type)
                ==> @Permutation.Permutation (ident * type)
                ==> @eq exp ==> iff) wt_exp.
  Proof.
    intros p2 p1 Hp m2 m1 Hm v2 v1 Hv e' e He; subst.
    induction e; split; inversion_clear 1; econstructor; eauto;
      try rewrite Hm in *;
      try rewrite Hv in *;
      repeat match goal with H:_ <-> _ |- _ => apply H; clear H end;
      auto with obctyping.
  Qed.

  Global Instance wt_stmt_Proper:
    Proper (@eq program
                ==> @Permutation.Permutation (ident * ident)
                ==> @Permutation.Permutation (ident * type)
                ==> @Permutation.Permutation (ident * type)
                ==> @eq stmt ==> iff) wt_stmt.
  Proof.
    intros p' p Hp xs2 xs1 Hxs ys2 ys1 Hys zs2 zs1 Hzs s' s Hs.
    rewrite Hp, Hs in *; clear Hp Hs.
    induction s using stmt_ind2'; split; intro HH; inv HH.
    (* Assign *)
    - constructor; rewrite <-Hzs; try rewrite <-Hys; auto.
    - constructor; rewrite Hzs; try rewrite Hys; auto.
    (* AssignSt *)
    - constructor; try rewrite <-Hzs; rewrite <-Hys; auto.
    - constructor; try rewrite Hzs; rewrite Hys; auto.
    (* Switch *)
    - econstructor; eauto.
      + rewrite <-Hys, <-Hzs; auto.
      + now apply IHs.
      + intros * Hin.
        take (Forall _ _) and eapply Forall_forall in it; eauto; simpl in *.
        apply it; auto.
    - econstructor; eauto.
      + rewrite Hys, Hzs; auto.
      + now apply IHs.
      + intros * Hin.
        take (Forall _ _) and eapply Forall_forall in it; eauto; simpl in *.
        apply it; auto.
    (* Comp *)
    - constructor; try rewrite <-IHs1; try rewrite <-IHs2; auto.
    - constructor; try rewrite IHs1; try rewrite IHs2; auto.
    (* Call *)
    - econstructor; eauto.
      * now rewrite <-Hxs.
      * match goal with H:Forall2 _ _ fm.(m_out) |- _ =>
                      apply Forall2_impl_In with (2:=H) end.
        intros; now rewrite <-Hzs.
      * match goal with H:Forall (wt_exp _ _ _) _ |- _ =>
                        apply Forall_impl with (2:=H) end.
        intros; now rewrite <-Hys, <-Hzs.
    - econstructor; eauto.
      * now rewrite Hxs.
      * match goal with H:Forall2 _ _ fm.(m_out) |- _ =>
                        apply Forall2_impl_In with (2:=H) end.
        intros; now rewrite Hzs.
      * match goal with H:Forall (wt_exp _ _ _) _ |- _ =>
                        apply Forall_impl with (2:=H) end.
        intros; now rewrite Hys, Hzs.
    (* Skip *)
    - constructor.
    - constructor.
  Qed.

  (** Properties *)

  Definition wt_state (p: program) (me: menv) (ve: venv) (c: class) (Γv: list (ident * type)) : Prop :=
    wt_memory me p c.(c_mems) c.(c_objs) /\ wt_env ve Γv.

  Lemma wt_program_nodup_classes:
    forall p,
      wt_program p ->
      NoDup (map c_name p.(classes)).
  Proof.
    unfold wt_program, CommonTyping.wt_program; simpl.
    induction 1 as [|?? []]; simpl; constructor; auto.
    intro Hin; apply in_map_iff in Hin as (?&E&Hin).
    eapply Forall_forall in Hin; eauto; simpl in Hin.
    apply Hin; auto.
  Qed.

  Lemma wt_class_find_method:
    forall p cls f fm,
      wt_class p cls ->
      find_method f cls.(c_methods) = Some fm ->
      wt_method p cls.(c_objs) cls.(c_mems) fm.
  Proof.
    intros p cls f fm WTc Hfindm.
    destruct WTc as (Hfo & WTms).
    apply Forall_forall with (1:=WTms).
    apply find_method_In with (1:=Hfindm).
  Qed.

  Lemma wt_exp_chained:
    forall e f p cl p' mems insts,
    find_class f p = Some (cl, p') ->
    wt_exp p' mems insts e ->
    wt_exp p mems insts e.
  Proof.
    induction e; inversion_clear 2; eauto using wt_exp.
    econstructor; eauto.
    assert (enums p = enums p') as ->
        by (take (find_class _ _ = _) and apply find_unit_equiv_program in it;
            specialize (it []); inv it; auto); auto.
  Qed.
  Hint Resolve wt_exp_chained.

  Corollary wt_exps_chained:
    forall es f p cl p' mems insts,
    find_class f p = Some (cl, p') ->
    Forall (wt_exp p' mems insts) es ->
    Forall (wt_exp p mems insts) es.
  Proof.
    induction 2; constructor; eauto.
  Qed.
  Hint Resolve wt_exps_chained.

  Lemma pres_sem_exp:
    forall p Γm Γv me ve e v,
      wt_env (values me) Γm ->
      wt_env ve Γv ->
      wt_exp p Γm Γv e ->
      exp_eval me ve e (Some v) ->
      wt_value v (typeof e).
  Proof.
    intros until v. intros WTm WTv.
    revert v.
    induction e; intros ? WTe Hexp.
    - inv WTe. inv Hexp.
      eapply env_find_wt_value with (1:=WTv); eauto.
    - inv WTe. inv Hexp.
      unfold find_val in *.
      eapply env_find_wt_value with (1:=WTm); eauto.
    - inv WTe. inv Hexp. now constructor.
    - inv Hexp. simpl. constructor. apply wt_cvalue_cconst.
    - inv WTe. inv Hexp. eapply pres_sem_unop; eauto.
    - inv WTe. inv Hexp. eapply pres_sem_binop; eauto.
    - inv WTe. inv Hexp.
      eapply env_find_wt_value with (1:=WTv); eauto.
  Qed.

  Lemma pres_sem_exp':
    forall prog c Γv me ve e v,
      wt_state prog me ve c Γv ->
      wt_exp prog c.(c_mems) Γv e ->
      exp_eval me ve e (Some v) ->
      wt_value v (typeof e).
  Proof.
    intros * (WT_mem&?) ? ?.
    inv WT_mem.
    eapply pres_sem_exp with (Γv:=Γv); eauto.
  Qed.
  Hint Resolve pres_sem_exp'.

  Lemma pres_sem_expo:
    forall prog Γm Γv me ve e vo,
      wt_env (values me) Γm ->
      wt_env ve Γv ->
      wt_exp prog Γm Γv e ->
      exp_eval me ve e vo ->
      wt_option_value vo (typeof e).
  Proof.
    intros. destruct vo; simpl;
              eauto using pres_sem_exp.
  Qed.

  Lemma pres_sem_expo':
    forall prog c Γv me ve e vo,
      wt_state prog me ve c Γv ->
      wt_exp prog c.(c_mems) Γv e ->
      exp_eval me ve e vo ->
      wt_option_value vo (typeof e).
  Proof.
    intros. destruct vo; simpl; eauto.
  Qed.
  Hint Resolve pres_sem_expo'.

  Lemma pres_sem_expos:
    forall prog Γm Γv me ve es vos,
      wt_env (values me) Γm ->
      wt_env ve Γv ->
      Forall (wt_exp prog Γm Γv) es ->
      Forall2 (exp_eval me ve) es vos ->
      Forall2 (fun e vo => wt_option_value vo (typeof e)) es vos.
  Proof.
    intros; eapply Forall2_impl_In; eauto.
    intros. simpl in *.
    match goal with Hf:Forall _ ?xs, Hi: In _ ?xs |- _ =>
      apply Forall_forall with (1:=Hf) in Hi end.
    eapply pres_sem_expo; eauto.
  Qed.

  Lemma pres_sem_expos':
    forall prog c Γv me ve es vos,
      wt_state prog me ve c Γv ->
      Forall (wt_exp prog c.(c_mems) Γv) es ->
      Forall2 (exp_eval me ve) es vos ->
      Forall2 (fun e vo => wt_option_value vo (typeof e)) es vos.
  Proof.
    intros; eapply Forall2_impl_In; eauto.
    intros. simpl in *.
    match goal with Hf:Forall _ ?xs, Hi: In _ ?xs |- _ =>
      apply Forall_forall with (1:=Hf) in Hi end.
    eapply pres_sem_expo'; eauto.
  Qed.
  Hint Resolve pres_sem_expos'.

  Corollary wt_state_add:
    forall prog me ve c Γv x v t,
      wt_state prog me ve c Γv ->
      NoDupMembers Γv ->
      In (x, t) Γv ->
      wt_value v t ->
      wt_state prog me (Env.add x v ve) c Γv.
  Proof.
    intros * (?&?) ???; split; eauto.
  Qed.
  Hint Resolve wt_state_add.

  Corollary wt_state_adds:
    forall xs prog me ve c Γv vs (xts: list (ident * type)),
      wt_state prog me ve c Γv ->
      NoDupMembers Γv ->
      Forall2 (fun y xt => In (y, snd xt) Γv) xs xts ->
      NoDup xs ->
      Forall2 (fun rv xt => wt_value rv (snd xt)) vs xts ->
      wt_state prog me (Env.adds xs vs ve) c Γv.
  Proof.
    induction xs; inversion 3; inversion 1; inversion 1; subst; auto.
    rewrite Env.adds_cons_cons; eauto.
  Qed.
  Hint Resolve wt_state_adds.

  Corollary wt_state_adds_opt:
    forall xs prog me ve c Γv vs (xts: list (ident * type)),
      wt_state prog me ve c Γv ->
      NoDupMembers Γv ->
      Forall2 (fun y xt => In (y, snd xt) Γv) xs xts ->
      NoDup xs ->
      Forall2 (fun rv xt => wt_value rv (snd xt)) vs xts ->
      wt_state prog me (Env.adds_opt xs (map Some vs) ve) c Γv.
  Proof.
    intros; rewrite Env.adds_opt_is_adds; eauto.
  Qed.
  Hint Resolve wt_state_adds_opt.

  Corollary wt_state_add_val:
     forall prog me ve c Γv x v t,
      wt_state prog me ve c Γv ->
      In (x, t) (c_mems c) ->
      wt_value v t ->
      wt_state prog (add_val x v me) ve c Γv.
  Proof.
    intros * (?&?) ??; split; eauto.
    eapply wt_memory_add_val; eauto using c_nodupmems.
  Qed.
  Hint Resolve wt_state_add_val.

  Corollary wt_state_add_inst:
     forall prog me ve c c' prog' Γv x me_x c_x,
      wt_state prog me ve c Γv ->
      In (x, c_x) (c_objs c) ->
      find_class c_x prog = Some (c', prog') ->
      wt_memory me_x prog' c'.(c_mems) c'.(c_objs) ->
      wt_state prog (add_inst x me_x me) ve c Γv.
  Proof.
    intros * (?&?) ??; split; eauto.
    eapply wt_memory_add_inst; eauto using c_nodupobjs.
  Qed.
  Hint Resolve wt_state_add_inst.

  Lemma wt_params:
    forall vos xs es,
      Forall2 (fun e vo => wt_option_value vo (typeof e)) es vos ->
      Forall2 (fun e (xt: ident * type) => typeof e = snd xt) es xs ->
      Forall2 (fun vo xt => wt_option_value vo (snd xt)) vos xs.
  Proof.
    induction vos, xs, es; intros * Wt Eq; inv Wt;
    inversion_clear Eq as [|? ? ? ? E]; auto.
    constructor; eauto.
    now rewrite <- E.
  Qed.
  Hint Resolve wt_params.

  Lemma wt_env_params:
    forall vos callee,
      Forall2 (fun vo xt => wt_option_value vo (snd xt)) vos (m_in callee) ->
      wt_env (Env.adds_opt (map fst (m_in callee)) vos vempty) (meth_vars callee).
  Proof.
    intros * Wt.
    unfold wt_env.
    apply Forall_app.
    pose proof (m_nodupvars callee) as Nodup.
    split.
    - apply NoDupMembers_app_l in Nodup.
      apply wt_env_adds_opt with (outs:=m_in callee); eauto.
      + now apply fst_NoDupMembers.
      + clear; induction (m_in callee) as [|(?, ?)]; simpl; auto.
        constructor; auto.
        eapply Forall2_impl_In; eauto.
        intros; now right.
    - apply Forall_forall.
      intros (x, t) Hin.
      assert (~ In x (map fst (m_in callee))).
      { intro Hin'.
        apply in_map_iff in Hin'; destruct Hin' as [(x', t') [? Hin']]; simpl in *; subst.
        apply in_split in Hin; destruct Hin as (? & ? & Hin).
        apply in_split in Hin'; destruct Hin' as (? & ? & Hin').
        rewrite Hin, Hin' in Nodup.
        rewrite <-app_assoc, <-app_comm_cons in Nodup.
        apply NoDupMembers_app_r in Nodup.
        inversion_clear Nodup as [|? ? ? Notin].
        apply Notin.
        apply InMembers_app; right; apply InMembers_app; right; apply inmembers_eq.
      }
      unfold wt_env_value; simpl.
      rewrite Env.find_In_gsso_opt, Env.gempty; auto.
  Qed.
  Hint Resolve wt_env_params.

  Lemma wt_env_params_exprs:
    forall vos callee es,
      Forall2 (fun e vo => wt_option_value vo (typeof e)) es vos ->
      Forall2 (fun (e : exp) (xt : ident * type) => typeof e = snd xt) es (m_in callee) ->
      wt_env (Env.adds_opt (map fst (m_in callee)) vos vempty) (meth_vars callee).
  Proof.
    intros * Wt Eq.
    eapply wt_env_params, wt_params; eauto.
  Qed.
  Hint Resolve wt_env_params_exprs.

  Lemma pres_sem_stmt':
    (forall p me ve stmt e',
        stmt_eval p me ve stmt e' ->
        forall mems insts Γv,
          let (me', ve') := e' in
          NoDupMembers Γv ->
          NoDupMembers mems ->
          NoDupMembers insts ->
          wt_program p ->
          wt_memory me p mems insts ->
          wt_env ve Γv ->
          wt_stmt p insts mems Γv stmt ->
          wt_memory me' p mems insts /\ wt_env ve' Γv)
    /\ (forall p me clsid f vs me' rvs,
          stmt_call_eval p me clsid f vs me' rvs ->
          forall p' cls fm,
            wt_program p ->
            find_class clsid p = Some(cls, p') ->
            find_method f cls.(c_methods) = Some fm ->
            wt_memory me p' cls.(c_mems) cls.(c_objs) ->
            Forall2 (fun v xt => wt_option_value v (snd xt)) vs fm.(m_in) ->
            wt_memory me' p' cls.(c_mems) cls.(c_objs)
            /\ Forall2 (fun v yt => wt_option_value v (snd yt)) rvs fm.(m_out)).
  Proof.
    apply stmt_eval_call_ind.
    - (* assign *)
      intros * Hexp mems insts Γv Hndup Hndupm Hndupi WTp WTm WTe WTstmt.
      split; auto.
      inv WTstmt. inversion_clear WTm as [???? WTmv WTmi].
      eapply pres_sem_exp with (1:=WTmv) (2:=WTe) in Hexp; eauto.

    - (* assign state *)
      intros * Hexp mems insts Γv Hndup Hndupm Hndupi WTp WTm WTe WTstmt.
      split; auto.
      inv WTstmt. inversion_clear WTm as [???? WTmv WTmi].
      eapply pres_sem_exp with (1:=WTmv) (2:=WTe) in Hexp; eauto.
      constructor.
      + eapply wt_env_add; eauto.
      + apply Forall_impl_In with (2:=WTmi).
        inversion 2.
        * left; auto.
        * eright; eauto.

    - (* call *)
      intros p * Hevals Hcall IH
             mems insts Γv Hndups Hndupm Hndupi WTp WTm WTe WTstmt.
      inv WTstmt.
      edestruct IH; eauto; clear IH; simpl.
      + (* Instance memory is well-typed before execution. *)
        unfold instance_match; destruct (find_inst o me) eqn:Hmfind; auto using wt_memory_empty.
        inversion_clear WTm as [???? WTv WTi].
        eapply Forall_forall in WTi; eauto.
        inversion_clear WTi as [? ? ? ? Hmfind'|? ? ? ? ? ? ? Hmfind' Hcfind' WTm];
          rewrite Hmfind' in Hmfind; try discriminate.
        match goal with Hcfind:find_class _ _ = Some (_, p') |- _ =>
                        simpl in Hcfind'; setoid_rewrite Hcfind in Hcfind' end.
        injection Hmfind; injection Hcfind'. intros; subst.
        assumption.
      + (* Arguments are well-typed if given. *)
        rewrite Forall2_swap_args in Hevals.
        match goal with H:Forall2 _ es fm.(m_in) |- _ => rename H into Hes end.
        apply all_In_Forall2.
        now rewrite <-(Forall2_length _ _ _ Hes), (Forall2_length _ _ _ Hevals).
        intros x v Hin.
        apply Forall2_chain_In' with (1:=Hevals) (2:=Hes) in Hin.
        destruct Hin as (e & Hexp & Hty & Hxy & Hyv).
        rewrite <-Hty.
        apply in_combine_r in Hxy.
        match goal with H:Forall _ es |- _ =>
          apply Forall_forall with (1:=H) in Hxy end.
        eapply pres_sem_expo in Hxy; eauto; inv WTm; auto.

    - (* sequential composition *)
      intros p menv env s1 s2
             * Hstmt1 IH1 Hstmt2 IH2 mems insts Γv Hndups Hndupm Hndupi WTp WTm Wte WTstmt.
      inv WTstmt.
      (* match goal with WTstmt1:wt_stmt _ _ _ _ s1 |- _ => *)
      (*                 specialize (IH1 _ _ Hndups WTp WTs WTstmt1) end. *)
      edestruct IH1 with (Γv := Γv) as (WTm1 & WTe1); eauto.

    - (* switch *)
      intros prog me ve cond branches d c s me' ve'
             Hexp Nth IH mems insts Γv Hndups Hndupm Hndupi WTp WTm WTe WTstmt.
      apply IH; auto.
      inv WTstmt; destruct s; simpl; auto.
      eapply nth_error_In in Nth; auto.

    - (* skip *)
      intros; auto.

    - (* call eval *)
      intros * Hfindc Hfindm Hlvos Hstmt IH Hrvs
             p'' cls'' fm'' WTp Hfindc' Hfindm' WTmem WTv.
      rewrite Hfindc in Hfindc';
        injection Hfindc'; intros; subst cls'' p''; clear Hfindc'.
      rewrite Hfindm in Hfindm';
        injection Hfindm'; intros; subst fm''; clear Hfindm'.
      destruct (wt_program_find_unit _ _ _ _ _ WTp Hfindc) as (WTc & WTp').
      edestruct IH with (Γv := meth_vars fm) (5 := WTmem);
        eauto using m_nodupvars, c_nodupmems, c_nodupobjs.
      + (* In a well-typed class, method bodies are well-typed. *)
        apply wt_class_find_method with (1:=WTc) (2:=Hfindm).
      + split; auto.
        (* Show that result values are well-typed. *)
        rewrite Forall2_map_1 in Hrvs.
        apply Forall2_swap_args in Hrvs.
        eapply Forall2_impl_In with (2:=Hrvs).
        intros v x Hvin Hxin Hxv.
        destruct x as (x & ty). simpl in *.
        destruct v; simpl; auto.
        eapply env_find_wt_value with (3:=Hxv);
          eauto using in_or_app.
  Qed.

  Lemma pres_sem_stmt:
    forall p mems insts Γv stmt me ve me' ve',
      NoDupMembers Γv ->
      NoDupMembers mems ->
      NoDupMembers insts ->
      wt_program p ->
      wt_memory me p mems insts ->
      wt_env ve Γv ->
      wt_stmt p insts mems Γv stmt ->
      stmt_eval p me ve stmt (me', ve') ->
      wt_memory me' p mems insts /\ wt_env ve' Γv.
  Proof.
    intros.
    eapply ((proj1 pres_sem_stmt') _ _ _ _ (me', ve')); eauto.
  Qed.

  Lemma pres_sem_stmt_call:
    forall p clsid p' cls f fm me vs me' rvs,
      wt_program p ->
      find_class clsid p = Some(cls, p') ->
      find_method f cls.(c_methods) = Some fm ->
      wt_memory me p' cls.(c_mems) cls.(c_objs) ->
      Forall2 (fun vo xt => wt_option_value vo (snd xt)) vs fm.(m_in) ->
      stmt_call_eval p me clsid f vs me' rvs ->
      wt_memory me' p' cls.(c_mems) cls.(c_objs)
      /\ Forall2 (fun vo yt => wt_option_value vo (snd yt)) rvs fm.(m_out).
  Proof.
    intros; eapply (proj2 pres_sem_stmt'); eauto.
  Qed.

  Lemma pres_loop_call_spec:
    forall n prog cid c prog' fid f ins outs me,
      wt_program prog ->
      find_class cid prog = Some (c, prog') ->
      find_method fid c.(c_methods) = Some f ->
      (forall n, Forall2 (fun vo xt => wt_option_value vo (snd xt)) (ins n) f.(m_in)) ->
      wt_memory me prog' c.(c_mems) c.(c_objs) ->
      loop_call prog cid fid ins outs 0 me ->
      exists me_n,
        loop_call prog cid fid ins outs n me_n
        /\ wt_memory me_n prog' c.(c_mems) c.(c_objs)
        /\ Forall2 (fun vo xt => wt_option_value vo (snd xt)) (outs n) f.(m_out).
  Proof.
    induction n; intros * ????? Loop.
    - exists me; split; auto; split; auto.
      inv Loop; eapply pres_sem_stmt_call; eauto.
    - edestruct IHn as (me_n & Loop_n & ? & ?); eauto.
      inversion_clear Loop_n as [???? Loop_Sn].
      assert (wt_memory me' prog' c.(c_mems) c.(c_objs)) by (eapply pres_sem_stmt_call; eauto).
      eexists; split; eauto; split; auto.
      inv Loop_Sn.
      eapply pres_sem_stmt_call; eauto.
  Qed.

  Corollary pres_loop_call:
    forall prog cid c prog' fid f ins outs me,
      wt_program prog ->
      find_class cid prog = Some (c, prog') ->
      find_method fid c.(c_methods) = Some f ->
      (forall n, Forall2 (fun vo xt => wt_option_value vo (snd xt)) (ins n) f.(m_in)) ->
      wt_memory me prog' c.(c_mems) c.(c_objs) ->
      loop_call prog cid fid ins outs 0 me ->
      forall n, Forall2 (fun vo xt => wt_option_value vo (snd xt)) (outs n) f.(m_out).
  Proof.
    intros; edestruct pres_loop_call_spec as (?&?&?&?); eauto.
  Qed.

  Remark wt_program_not_class_in:
    forall pre post o c cid prog,
      classes prog = pre ++ c :: post ->
      wt_program prog ->
      In (o, cid) c.(c_objs) ->
      find_class cid (Program prog.(enums) pre) = None.
  Proof.
    unfold wt_program, CommonTyping.wt_program.
    intros * E WT Hin; setoid_rewrite E in WT; clear E.
    induction pre as [|k]; auto.
    simpl in WT. inversion WT as [|?? []]; subst; clear WT.
    unfold find_class, find_unit; simpl.
    match goal with H: Forall _ _ |- _ => apply Forall_app_weaken, Forall_cons2 in H as (Hneq &?) end.
    apply ident_eqb_neq in Hneq.
    match goal with H:Forall' _ _ |- _ =>
      specialize (IHpre H); apply Forall'_app_r in H;
        inversion_clear H as [|?? [WTc Hnodup]] end.
    simpl in *.
    destruct (ident_eq_dec k.(c_name) cid); auto.
    subst.
    inversion_clear WTc as [Ho Hm].
    apply Forall_forall with (1:=Ho) in Hin.
    apply not_None_is_Some in Hin as ((cls, p') & Hin).
    simpl in Hin.
    apply find_unit_In in Hin as (?& Hin).
    clear Hnodup.
    eapply Forall_forall in Hin; eauto; simpl in Hin.
    simpl in *; congruence.
  Qed.

  Remark wt_program_not_same_name:
    forall post o c cid enums,
      wt_program (Program enums (c :: post)) ->
      In (o, cid) c.(c_objs) ->
      cid <> c.(c_name).
  Proof.
    intros * WTp Hin Hc'.
    rewrite Hc' in Hin; clear Hc'.
    inversion_clear WTp as [|?? [WTc Hnodup] WTp']; clear WTp'; simpl in *.
    inversion_clear WTc as [Ho Hm].
    apply Forall_forall with (1:=Ho) in Hin.
    apply not_None_is_Some in Hin as ((cls, p') & Hin).
    simpl in Hin.
    apply find_unit_In in Hin as [? Hin].
    eapply Forall_forall in Hin; eauto.
    now apply Hin.
  Qed.

  Lemma wt_program_find_class_chained_in_objs:
    forall p f i g cl p',
      wt_program p ->
      find_class f p = Some (cl, p') ->
      In (i, g) cl.(c_objs) ->
      find_class g p' = find_class g p.
  Proof.
    intros * WTp Hfc Hin.
    destruct (find_class g p) eqn: Hfc'.
    - assert (equiv_program p p')
        by (eapply find_unit_equiv_program; eauto).
      apply find_unit_spec in Hfc as (?& cls & E &?); subst.
      pose proof Hin as Hin'.
      eapply wt_program_not_class_in in Hin; eauto.
      eapply wt_program_not_same_name in Hin';
        [|eapply wt_program_app in WTp as []; simpl in *; eauto].
      setoid_rewrite find_unit_app in Hfc'; eauto; simpl in *.
      setoid_rewrite Hin in Hfc'.
      setoid_rewrite <-find_unit_other; eauto.
    - apply find_unit_None; apply find_unit_None in Hfc'.
      apply find_unit_spec in Hfc as (?& cls & E &?); subst.
      rewrite E in Hfc'.
      apply Forall_app in Hfc' as [? Hfc']; inv Hfc'; auto.
  Qed.

  Lemma wt_exp_suffix:
    forall prog prog' Γm Γv e,
      wt_exp prog' Γm Γv e ->
      suffix prog' prog ->
      wt_exp prog Γm Γv e.
  Proof.
    induction 1; intros * Sub; econstructor; eauto.
    inv Sub; auto.
    take (equiv_program _ _) and specialize (it nil); inv it; auto.
  Qed.

  Lemma wt_stmt_suffix:
    forall prog prog' insts Γm Γv s,
      wt_stmt prog' insts Γm Γv s ->
      wt_program prog ->
      suffix prog' prog ->
      wt_stmt prog insts Γm Γv s.
  Proof.
    induction s using stmt_ind2'; inversion_clear 1;
      intros * Sub; econstructor; eauto using wt_exp_suffix.
    - take (suffix _ _) and inv it; auto.
      take (equiv_program _ _) and specialize (it nil); inv it; auto.
    - intros.
      take (Forall _ _) and eapply Forall_forall in it; eauto; simpl in *; auto.
    - eapply find_unit_suffix_same; eauto.
    - apply Forall_forall; intros.
      take (Forall _ _) and eapply Forall_forall in it; eauto.
      eapply wt_exp_suffix; eauto.
  Qed.

  Hint Constructors suffix.

  Lemma stmt_call_eval_suffix:
    forall p p' me clsid f vs ome rvs,
      stmt_call_eval p me clsid f vs ome rvs ->
      wt_program p' ->
      suffix p p' ->
      stmt_call_eval p' me clsid f vs ome rvs.
  Proof.
    intros * Ev ? ?.
    induction Ev.
    econstructor; eauto.
    eapply find_unit_suffix_same; eauto.
  Qed.
  Hint Resolve stmt_call_eval_suffix.

  Lemma stmt_eval_suffix:
    forall p p' me ve s S,
      stmt_eval p me ve s S ->
      wt_program p' ->
      suffix p p' ->
      stmt_eval p' me ve s S.
  Proof.
    intros * Ev ? ?.
    induction Ev; econstructor; eauto.
  Qed.
  Hint Resolve stmt_eval_suffix.

  Lemma wt_mem_skip:
    forall p p' f c mem,
      wt_program p ->
      find_class f p = Some (c, p') ->
      wt_memory mem p c.(c_mems) c.(c_objs) ->
      wt_memory mem p' c.(c_mems) c.(c_objs).
  Proof.
    intros * WT Find WTm.
    (* pose proof Find as Eq; apply find_class_enums in Eq. *)
    assert (enums p = enums p') as Enums
      by (apply find_unit_equiv_program in Find; specialize (Find nil); inv Find; auto).
    inversion_clear WTm as [????? WTinsts]; constructor; auto.
    apply Forall_forall; intros (?&?) Hin.
    eapply Forall_forall in WTinsts; eauto.
    apply find_unit_spec in Find as (?&?&?&?); simpl in *.
    (* apply find_class_app in Find as (prog'' & ? &?); simpl in *; subst. *)
    pose proof WT as WT'.
    eapply wt_program_not_class_in in WT; eauto.
    inversion_clear WTinsts as [|???????? Find].
    - left; auto.
    - eright; eauto.
      erewrite find_unit_app in Find; eauto; setoid_rewrite WT in Find.
      eapply wt_program_app in WT' as [? WT']; eauto.
      eapply wt_program_not_same_name in Hin; eauto.
      + simpl in *.
        eapply find_unit_cons in Find as [[]|[]]; simpl in *; eauto; try congruence.
        destruct p'; simpl in *; subst; auto.
      + unfold wt_program, CommonTyping.wt_program in *; simpl in *; eauto.
  Qed.
  Hint Resolve wt_mem_skip.

  Lemma find_class_rev:
    forall prog n c prog',
      wt_program prog ->
      find_class n prog = Some (c, prog') ->
      exists prog'', find_class n (rev_prog prog) = Some (c, prog'').
  Proof.
    intros (enums & prog).
    unfold rev_prog; setoid_rewrite rev_tr_spec.
    induction prog as [|c']; simpl; intros * WTP Find; try discriminate.
    inversion_clear WTP as [|?? [Hwtc Hndup] Hwtp]; simpl.
    setoid_rewrite find_unit_app; simpl; eauto.
    eapply find_unit_cons in Find as [[E Find]|[]]; simpl in *; eauto.
    - inv Find.
      assert (find_unit (c_name c') (Program enums (rev prog)) = None) as E
          by (apply find_unit_None; simpl; apply Forall_rev; auto).
      setoid_rewrite E.
      unfold find_unit; simpl.
      destruct (ident_eq_dec (c_name c') (c_name c')); try contradiction; eauto.
    - edestruct IHprog as (? & Find'); eauto.
      setoid_rewrite Find'; eauto.
  Qed.

End OBCTYPING.

Module ObcTypingFun
       (Ids    : IDS)
       (Op     : OPERATORS)
       (OpAux  : OPERATORS_AUX Ids Op)
       (Syn    : OBCSYNTAX     Ids Op OpAux)
       (ComTyp : COMMONTYPING  Ids Op OpAux)
       (Sem    : OBCSEMANTICS  Ids Op OpAux Syn)
       <: OBCTYPING Ids Op OpAux Syn ComTyp Sem.
  Include OBCTYPING Ids Op OpAux Syn ComTyp Sem.
End ObcTypingFun.
