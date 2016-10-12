Require Import Rustre.Common.
Require Import Rustre.Operators.
Require Import Rustre.RMemory.
Require Import Rustre.Obc.Syntax.
Require Import Rustre.Obc.Semantics.

Require Import Morphisms.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

(** * Obc typing *)

(** 

  Typing judgements for Obc and resulting properties.
  Classify Obc programs which are statically well-formed.

 *)

Module Type TYPING
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Syn   : SYNTAX Ids Op OpAux)
       (Import Sem   : SEMANTICS Ids Op OpAux Syn).

  Section WellTyped.

    Variable p     : program.
    Variable insts : list (ident * ident).
    Variable mems  : list (ident * type).
    Variable vars  : list (ident * type).
    
    Inductive wt_exp : exp -> Prop :=
    | wt_Var: forall x ty,
        In (x, ty) vars ->
        wt_exp (Var x ty)
    | wt_State: forall x ty,
        In (x, ty) mems ->
        wt_exp (State x ty)
    | wt_Const: forall c,
        wt_exp (Const c)
    | wt_Unop: forall op e ty,
        type_unop op (typeof e) = Some ty ->
        wt_exp e ->
        wt_exp (Unop op e ty)
    | wt_Binop: forall op e1 e2 ty,
        type_binop op (typeof e1) (typeof e2) = Some ty ->
        wt_exp e1 ->
        wt_exp e2 ->
        wt_exp (Binop op e1 e2 ty).

    (* TODO: eliminate the result types in Call (and EqApp). *)
    Inductive wt_stmt : stmt -> Prop :=
    | wt_Assign: forall x e,
        In (x, typeof e) vars ->
        wt_exp e ->
        wt_stmt (Assign x e)
    | wt_AssignSt: forall x e,
        In (x, typeof e) mems ->
        wt_exp e ->
        wt_stmt (AssignSt x e)
    | wt_Ifte: forall e s1 s2,
        wt_exp e ->
        typeof e = bool_type ->
        wt_stmt s1 ->
        wt_stmt s2 ->
        wt_stmt (Ifte e s1 s2)
    | wt_Comp: forall s1 s2,
        wt_stmt s1 ->
        wt_stmt s2 ->
        wt_stmt (Comp s1 s2)
    | wt_Call: forall clsid cls p' o f fm ys es,
        In (o, clsid) insts ->
        find_class clsid p = Some(cls, p') ->
        find_method f cls.(c_methods) = Some fm ->
        NoDup ys ->
        Forall2 (fun y xt => In (y, snd xt) vars) ys fm.(m_out) ->
        Forall2 (fun e xt => typeof e = snd xt) es fm.(m_in) ->
        Forall wt_exp es ->
        wt_stmt (Call ys clsid o f es)
    | wt_Skip:
        wt_stmt Skip.

  End WellTyped.

  Definition wt_method (p     : program)
                       (insts : list (ident * ident))
                       (mems  : list (ident * type))
                       (m     : method) : Prop
    := wt_stmt p insts mems (m.(m_in) ++ m.(m_vars) ++ m.(m_out)) m.(m_body).

  Definition wt_class (p : program) (cls: class) : Prop
    := (Forall (fun ocls=> find_class (snd ocls) p <> None) cls.(c_objs))
       /\ Forall (wt_method p cls.(c_objs) cls.(c_mems)) cls.(c_methods).
  
  Inductive wt_program : program -> Prop :=
  | wtp_nil:
      wt_program []
  | wtp_cons: forall cls p,
      wt_class p cls ->
      wt_program p ->
      NoDup (map c_name (cls::p)) ->
      wt_program (cls::p).

  Hint Constructors wt_exp wt_stmt wt_program : obctyping.

  Instance wt_exp_Proper:
    Proper (@Permutation.Permutation (ident * type)
                                     ==> @Permutation.Permutation (ident * type)
                                     ==> @eq exp ==> iff) wt_exp.
  Proof.
    intros m2 m1 Hm v2 v1 Hv e' e He; subst.
    induction e; split; inversion_clear 1; constructor;
      try rewrite Hm in *;
      try rewrite Hv in *;
      repeat match goal with H:_ <-> _ |- _ => apply H; clear H end;
      auto with obctyping.
  Qed.
  
  Instance wt_stmt_Proper:
    Proper (@eq program
                ==> @Permutation.Permutation (ident * ident)
                ==> @Permutation.Permutation (ident * type)
                ==> @Permutation.Permutation (ident * type)
                ==> @eq stmt ==> iff) wt_stmt.
  Proof.
    intros p' p Hp xs2 xs1 Hxs ys2 ys1 Hys zs2 zs1 Hzs s' s Hs.
    subst.
    induction s; split; intro HH; inv HH; try econstructor;
      repeat match goal with
             | H:Permutation.Permutation _ _ |- _ =>
               (erewrite H || erewrite <-H); clear H
             | H:_ <-> _ |- _ => (try apply H); clear H
             end;
      eauto with obctyping.
    - match goal with H:Forall2 _ _ fm.(m_out) |- _ =>
                      apply Forall2_impl_In with (2:=H) end.
      intros; now rewrite <-Hzs.
    - match goal with H:Forall (wt_exp _ _) _ |- _ =>
                      apply Forall_impl with (2:=H) end.
      intros; now rewrite <-Hys, <-Hzs.
    - match goal with H:Forall2 _ _ fm.(m_out) |- _ =>
                      apply Forall2_impl_In with (2:=H) end.
      intros; now rewrite Hzs.
    - match goal with H:Forall (wt_exp _ _) _ |- _ =>
                      apply Forall_impl with (2:=H) end.
      intros; now rewrite Hys, Hzs.
  Qed.
  
  (** Properties *)
  
  Definition wt_valo (ve: stack) (xty: ident * type) :=
    match PM.find (fst xty) ve with
    | None => True
    | Some v => wt_val v (snd xty)
    end.

  Definition wt_env (ve: stack) (vars: list (ident * type)) :=
    Forall (wt_valo ve) vars.

  Hint Unfold wt_env.
    
  Inductive wt_mem : heap -> program -> class -> Prop :=
  | WTmenv: forall me p cl,
      wt_env me.(mm_values) cl.(c_mems) ->
      Forall (wt_mem_inst me p) cl.(c_objs) ->
      wt_mem me p cl
  with wt_mem_inst : heap -> program -> (ident * ident) -> Prop :=
  | WTminst_empty: forall me p oclsid,
      mfind_inst (fst oclsid) me = None ->
      wt_mem_inst me p oclsid
  | WTminst: forall me p oclsid mo cls p',
      mfind_inst (fst oclsid) me = Some mo ->
      find_class (snd oclsid) p = Some(cls, p') ->
      wt_mem mo p' cls ->
      wt_mem_inst me p oclsid.

  Lemma wt_sempty:
    forall vars,
      wt_env sempty vars.
  Proof.
    induction vars as [|v vars]; auto.
    apply Forall_cons; auto.
    unfold wt_valo; simpl.
    now rewrite PM.gempty.
  Qed.

  Lemma wt_hempty:
    forall p cls,
      wt_mem hempty p cls.
  Proof.
    constructor.
    now apply wt_sempty.
    induction (cls.(c_objs)) as [|o os]; auto.
    apply Forall_cons; auto.
    apply WTminst_empty.
    apply mfind_inst_empty.
  Qed.

  Lemma venv_find_wt_val:
    forall vars ve x ty v,
      wt_env ve vars ->
      In (x, ty) vars ->
      PM.find x ve = Some v ->
      wt_val v ty.
  Proof.
    intros ** WTe Hin Hfind.
    apply In_Forall with (1:=WTe) in Hin.
    unfold wt_valo in Hin.
    simpl in Hin.
    now rewrite Hfind in Hin.
  Qed.

  Lemma wt_program_find_class:
    forall clsid p cls p',
      wt_program p ->
      find_class clsid p = Some (cls, p') ->
      wt_class p' cls /\ wt_program p'.
  Proof.
    induction p as [|cls p]; [now inversion 2|].
    intros cls' p' WTp Hfind.
    inversion Hfind as [Heq]; clear Hfind.
    inversion_clear WTp as [|? ? WTc WTp' Hnodup]; rename WTp' into WTp.
    destruct (ident_eq_dec cls.(c_name) clsid) as [He|Hne].
    - subst. rewrite ident_eqb_refl in Heq.
      injection Heq; intros; subst. auto.
    - rewrite (proj2 (ident_eqb_neq cls.(c_name) clsid) Hne) in Heq.
      apply IHp with (1:=WTp) (2:=Heq).
  Qed.      
  
  Lemma wt_class_find_method:
    forall p cls f fm,
      wt_class p cls ->
      find_method f cls.(c_methods) = Some fm ->
      wt_method p cls.(c_objs) cls.(c_mems) fm.
  Proof.
    intros p cls f fm WTc Hfindm.
    destruct WTc as (Hfo & WTms).
    apply In_Forall with (1:=WTms).
    apply find_method_In with (1:=Hfindm).
  Qed.
  
  Lemma pres_sem_exp:
    forall mems vars me ve e v,
      wt_env me.(mm_values) mems ->
      wt_env ve vars ->
      wt_exp mems vars e ->
      exp_eval me ve e v ->
      wt_val v (typeof e).
  Proof.
    intros until v. intros WTm WTv.
    revert v.
    induction e; intros v WTe Hexp.
    - inv WTe. inv Hexp.
      eapply venv_find_wt_val with (1:=WTv); eauto.
    - inv WTe. inv Hexp.
      unfold mfind_mem in *.
      eapply venv_find_wt_val with (1:=WTm); eauto.
    - inv Hexp. apply wt_val_const.
    - inv WTe. inv Hexp.
      match goal with
      | WTe:wt_exp _ _ ?e, Hexp:exp_eval _ _ ?e ?v |- _ =>
        specialize (IHe v WTe Hexp)
      end.
      eapply pres_sem_unop in IHe; now eauto.
    - inv WTe. inv Hexp.
      repeat match goal with
             | IH: forall v, _, WTe:wt_exp _ _ ?e, Hexp:exp_eval _ _ ?e ?v |- _
                 => specialize (IH v WTe Hexp)
             end.
      eapply pres_sem_binop with (3:=IHe1) in IHe2; eauto.
  Qed.

  Lemma wt_valo_add:
    forall env v x y ty,
      (y = x /\ wt_val v ty) \/ (y <> x /\ wt_valo env (y, ty)) ->
      wt_valo (PM.add x v env) (y, ty).
  Proof.
    intros ** Hor. unfold wt_valo; simpl.
    destruct Hor as [[Heq Hwt]|[Hne Hwt]].
    - subst. now rewrite PM.gss.
    - now rewrite PM.gso with (1:=Hne).
  Qed.
  
  Lemma wt_env_add:
    forall vars env x e v,
      NoDupMembers vars ->
      wt_env env vars ->
      In (x, typeof e) vars ->
      wt_val v (typeof e) ->
      wt_env (PM.add x v env) vars.
  Proof.
    intros ** Hndup WTenv Hin WTv.
    unfold wt_env.
    induction vars as [|y vars]; auto.
    apply Forall_cons2 in WTenv.
    destruct WTenv as (WTx & WTenv).
    destruct y as (y & ty).
    apply nodupmembers_cons in Hndup.    
    destruct Hndup as (Hnin & Hndup).
    inv Hin.
    - match goal with H:(y, ty) = _ |- _ => injection H; intros; subst end.
      constructor.
      + apply wt_valo_add; left; auto.
      + apply Forall_impl_In with (2:=WTenv).
        destruct a as (y & ty).
        intros Hin HTy.
        apply NotInMembers_NotIn with (b:=ty) in Hnin.
        apply wt_valo_add; right; split.
        intro; subst; contradiction.
        now apply HTy.
    - constructor.
      + apply wt_valo_add.
        destruct (ident_eq_dec x y);
          [subst; left; split|right]; auto.
        apply NotInMembers_NotIn with (b:=typeof e) in Hnin.
        contradiction.
      + apply IHvars; auto.
  Qed.

  Lemma pres_sem_stmt':
    (forall p me ve stmt e',
        stmt_eval p me ve stmt e' ->
        forall cls vars,
          let (me', ve') := e' in
          NoDupMembers vars ->
          wt_program p ->
          wt_mem me p cls ->
          wt_env ve vars ->
          wt_stmt p cls.(c_objs) cls.(c_mems) vars stmt ->
          wt_mem me' p cls /\ wt_env ve' vars)
    /\ (forall p me clsid f vs me' rvs,
           stmt_call_eval p me clsid f vs me' rvs ->
           forall p' cls fm,
             wt_program p ->
             find_class clsid p = Some(cls, p') ->
             find_method f cls.(c_methods) = Some fm ->
             wt_mem me p' cls ->
             Forall2 (fun v xt => wt_val v (snd xt)) vs fm.(m_in) ->
             wt_mem me' p' cls
             /\ Forall2 (fun v yt => wt_val v (snd yt)) rvs fm.(m_out)).
  Proof.
    apply stmt_eval_call_ind.
    - (* assign *)
      intros ** Hexp Henv' cls vars Hndup WTp WTm WTe WTstmt.
      split; auto.
      rewrite <-Henv'.
      inv WTstmt. inversion_clear WTm as [? ? ? WTmv WTmi].
      eapply pres_sem_exp with (1:=WTmv) (2:=WTe) in Hexp; auto.
      eapply wt_env_add; eauto.
    - (* assign state *)
      intros ** Hexp Henv' cls vars Hndup WTp WTm WTe WTstmt.
      split; auto.
      rewrite <-Henv'.
      inv WTstmt. inversion_clear WTm as [? ? ? WTmv WTmi].
      eapply pres_sem_exp with (1:=WTmv) (2:=WTe) in Hexp; auto.
      constructor.
      + eapply wt_env_add; eauto.
        apply fst_NoDupMembers.
        now apply NoDup_app_weaken with (1:=cls.(c_nodup)).
      + apply Forall_impl_In with (2:=WTmi).
        inversion 2; now eauto using wt_mem_inst.
    - (* call *)
      intros p ** Homenv Hevals Hcall IH Hmenv' Henv'
             cls vars Hndups WTp WTm WTe WTstmt.
      inv WTstmt.
      match goal with
      | Hfc:find_class _ _ = Some _, Hfm:find_method _ _ = Some _ |- _ =>
        destruct (IH _ _ _ WTp Hfc Hfm); clear IH end; [| |split].
      + (* Instance memory is well-typed before execution. *)
        destruct (mfind_inst o menv) eqn:Hmfind;
          auto using wt_hempty.
        inversion_clear WTm as [? ? ? WTv WTi].
        eapply In_Forall in WTi; eauto.
        inversion_clear WTi as [? ? ? Hmfind'|? ? ? ? ? ? Hmfind' Hcfind' WTm];
          simpl in Hmfind'; rewrite Hmfind in Hmfind'; try discriminate.
        match goal with Hcfind:find_class _ _ = Some (_, p') |- _ =>
                        simpl in Hcfind'; rewrite Hcfind in Hcfind' end.
        injection Hmfind'; injection Hcfind'. intros; subst.
        assumption.
      + (* Inputs are well-typed before execution. *)
        match goal with H1:Forall2 _ es fm.(m_in), H2:Forall _ es |- _ =>
                        rename H1 into Hin, H2 into Hes end.
        apply Forall2_forall2 in Hin.
        destruct Hin as (Hlen_in & Hin).
        apply Forall2_forall2 in Hevals.
        destruct Hevals as (Hlen_es & Hevals).
        apply Forall2_forall2.
        split; [now rewrite <-Hlen_es, <-Hlen_in|].
        intros def1 def2 n v xty Hlen Hnv Hnxty.
        destruct xty as (x & ty).
        assert (def3 := Var x ty).
        assert (n < length es) as Hlen'
            by now rewrite Hlen_es.
        specialize (Hevals _ _ n (nth n es def3) v Hlen' eq_refl Hnv).
        rewrite <- (Hin def3 _ _ _ _ Hlen' eq_refl Hnxty).
        eapply pres_sem_exp.
        * inv WTm; eassumption.
        * apply WTe.
        * apply In_Forall with (x0:=nth n es def3) in Hes; auto.
          now apply nth_In.
        * assumption.
      + (* Instance memory is well-typed after execution. *)
        inv WTm. constructor; auto.
        apply Forall_forall.
        destruct x as (o', clsid'). intros Hin.
        destruct (ident_eq_dec o o').
        * subst o'.
          econstructor 2; eauto.
          now apply mfind_inst_gss.
          assert (NoDupMembers cls.(c_objs)) as Hndup.
          { apply fst_NoDupMembers.
            eapply NoDup_app_weaken.
            rewrite Permutation.Permutation_app_comm.
            apply cls.(c_nodup).
          }
          match goal with H:In (o, clsid) cls.(c_objs) |- _ =>
          apply NoDupMembers_det with (1:=Hndup) (2:=H) in Hin end.
          subst clsid'. assumption.
        * destruct (mfind_inst o' menv) eqn:Heq.
          2:constructor; simpl; rewrite mfind_inst_gso; now auto.
          match goal with H:Forall _ cls.(c_objs) |- _ =>
          apply In_Forall with (1:=H) in Hin end.
          inv Hin; [constructor 1|econstructor 2]; simpl in *;
            match goal with H:o <> o' |- _ =>
            try rewrite (mfind_inst_gso _ _ (not_eq_sym n)) end; eauto.
      + (* Output values are well-typed after execution. *)
        apply Forall_forall.
        destruct x as (x, ty). intro Hin.
        unfold wt_valo; simpl.
        revert Hndups WTe Hin H8 H0 H7; clear; intros.
        destruct (in_dec ident_eq_dec x ys) as [Hx|Hx].
        * repeat match goal with
                   H:Forall2 _ _ _ |- _ => apply Forall2_forall2 in H end.
          match goal with H:length ys = _ /\ _ |- _ =>
                          destruct H as (Hlen_ys & Hys) end.
          match goal with H:length rvs = _ /\ _ |- _ =>
                          destruct H as (Hlen_rvs & Hrvs) end.
          pose proof x as def1.
          pose proof (x, ty) as def2.
          apply In_ex_nth with (d:=def1) in Hx.
          destruct Hx as (n & Hlen & Hx).
          specialize (Hys _ def2 _ _ _ Hlen Hx eq_refl); simpl in Hys.
          apply NoDupMembers_det with (1:=Hndups) (2:=Hin) in Hys; subst ty.
          assert (def3 := true_val).
          assert (n < length rvs) as Hlen'
            by (now rewrite Hlen_ys, <-Hlen_rvs in Hlen).
          specialize (Hrvs def3 def2 n _ _ Hlen' eq_refl eq_refl).
          rewrite find_gssn with (d2:=def3) (1:=Hlen) (4:=Hx); auto.
          now setoid_rewrite Hlen_ys; rewrite Hlen_rvs.
        * rewrite NotInMembers_find_adds with (v:=PM.find x env) (1:=Hx); auto.
          now apply Forall_forall with (1:=WTe) in Hin.
    - (* sequential composition *)
      intros p menv env s1 s2
             ** Hstmt1 IH1 Hstmt2 IH2 cls vars Hndups WTp WTm WTe WTstmt.
      inv WTstmt.
      match goal with WTstmt1:wt_stmt _ _ _ _ s1 |- _ =>
        specialize (IH1 _ _ Hndups WTp WTm WTe WTstmt1) end.
      destruct IH1 as (WTm1 & WTe1).
      match goal with WTstmt2:wt_stmt _ _ _ _ s2 |- _ =>
        specialize (IH2 _ _ Hndups WTp WTm1 WTe1 WTstmt2) end.
      assumption.
    - (* if/then/else *)
      intros ** b st sf env' menv'
             Hexp Hvtb Hstmt IH cls vars Hndups WTp WTm WTe WTstmt.
      apply IH; auto.
      inv WTstmt. destruct b; auto.
    - (* skip *)
      intros; auto.
    - (* call eval *)
      intros p menv clsid f fm vs p' ** Hfindc Hfindm Hstmt IH Hrvs
             p'' cls'' fm'' WTp Hfindc' Hfindm' WTm WTvs.
      rewrite Hfindc in Hfindc';
        injection Hfindc'; intros; subst cls'' p''; clear Hfindc'.
      rewrite Hfindm in Hfindm';
        injection Hfindm'; intros; subst fm''; clear Hfindm'.
      destruct (wt_program_find_class _ _ _ _ WTp Hfindc) as (WTc & WTp').
      destruct (IH cls _ fm.(m_nodupvars) WTp' WTm).
      + (* Well-typed inputs give a well-typed initial environment. *)
        apply Forall_app. split.
        * pose proof (NoDupMembers_app_l _ _ fm.(m_nodupvars)) as Hndup.
          revert Hndup WTvs. clear.
          induction 2 as [|v xt vs xts]; auto.
          apply Forall_cons.
          unfold wt_valo. destruct xt as (x & ty); simpl. now rewrite find_gsss.
          inversion_clear Hndup as [|x tx ? Hnin Hndup'].
          apply Forall_impl_In with (2:=(IHWTvs Hndup')).
          destruct a as (y & ty).
          intros Hin WTvo.
          unfold wt_valo; simpl.
          rewrite find_gsso. now apply WTvo.
          apply In_InMembers in Hin.
          intro; subst. contradiction.
        * apply Forall_impl_In with (P:=wt_valo sempty).
          2:now apply wt_sempty.
          destruct a as (x & ty).
          intros Hin Hvalo; clear Hvalo.
          unfold wt_valo; simpl.
          rewrite NotInMembers_find_adds with (v:=None); eauto using PM.gempty.
          apply NoDup_app_In with (xs:=map fst fm.(m_vars) ++ map fst fm.(m_out)).
          rewrite Permutation.Permutation_app_comm.
          now rewrite <- 2 map_app, <-fst_NoDupMembers; apply fm.(m_nodupvars).
          rewrite <- map_app, <-fst_InMembers.
          apply In_InMembers with (1:=Hin).
      + (* In a well-typed class, method bodies are well-typed. *)
        apply wt_class_find_method with (1:=WTc) (2:=Hfindm).
      + split; auto.
        (* Show that result values are well-typed. *)
        apply Forall2_map_1 in Hrvs.
        apply Forall2_swap_args in Hrvs.
        eapply Forall2_impl_In with (2:=Hrvs).
        intros v x Hvin Hxin Hxv.
        destruct x as (x & ty). simpl in *.
        eapply venv_find_wt_val with (3:=Hxv);
          eauto using in_or_app.
  Qed.

  Lemma pres_sem_stmt:
    forall p cls vars stmt me ve me' ve',
      NoDupMembers vars ->
      wt_program p ->
      wt_mem me p cls ->
      wt_env ve vars ->
      wt_stmt p cls.(c_objs) cls.(c_mems) vars stmt ->
      stmt_eval p me ve stmt (me', ve') ->
      wt_mem me' p cls /\ wt_env ve' vars.
  Proof.
    intros ** Hndup WTp WTm WTe WTs Heval.
    apply ((proj1 pres_sem_stmt') _ _ _ _ (me', ve') Heval cls vars); auto.
  Qed.

  Lemma pres_sem_stmt_call:
    forall p clsid p' cls f fm me vs me' rvs,
      wt_program p ->
      find_class clsid p = Some(cls, p') ->
      find_method f cls.(c_methods) = Some fm ->
      wt_mem me p' cls ->
      Forall2 (fun v xt => wt_val v (snd xt)) vs fm.(m_in) ->
      stmt_call_eval p me clsid f vs me' rvs ->
      wt_mem me' p' cls
      /\ Forall2 (fun v yt => wt_val v (snd yt)) rvs fm.(m_out).
  Proof.
    intros; eapply (proj2 pres_sem_stmt'); eauto.
  Qed.
  
  Lemma wt_program_app:
    forall cls cls',
      wt_program (cls ++ cls') ->
      wt_program cls'.
  Proof.
    induction cls; inversion 1; auto.
  Qed.

  Remark wt_program_not_class_in:
    forall pre post o c c',
      wt_program (pre ++ c :: post) ->
      In (o, c'.(c_name)) c.(c_objs) ->
      find_class c'.(c_name) pre = None.
  Proof.
    induction pre as [|k]; intros post o c c' WT Hin; auto.
    simpl in WT. inv WT.
    match goal with H:NoDup _ |- _ =>
      rewrite map_cons in H; apply NoDup_cons' in H;
        destruct H as (Hnin & Hndup) end.
    rewrite map_app, in_app, map_cons in Hnin.
    apply Decidable.not_or in Hnin.
    rewrite not_in_cons in Hnin.
    destruct Hnin as (Hnpre & Hneq & Hnpost).
    apply ident_eqb_neq in Hneq.
    simpl.
    match goal with H:wt_program _ |- _ =>
      specialize (IHpre _ _ _ _ H Hin); apply wt_program_app in H;
        inversion_clear H as [|? ? WTc WTp Hnodup] end.
    destruct (ident_eqb k.(c_name) c'.(c_name)) eqn: Heq; auto.
    apply ident_eqb_eq in Heq; rewrite Heq in *; clear Heq.
    inversion_clear WTc as [Ho Hm].
    apply In_Forall with (1:=Ho) in Hin.
    apply not_None_is_Some in Hin.
    destruct Hin as ((cls, p') & Hin).
    simpl in Hin.
    rewrite <-(find_class_name _ _ _ _ Hin) in *.
    apply find_class_In in Hin.
    apply in_map with (f:=c_name) in Hin.
    contradiction.
  Qed.

  Remark wt_program_not_same_name:
    forall post o c c',
      wt_program (c :: post) ->
      In (o, c'.(c_name)) c.(c_objs) ->
      c'.(c_name) <> c.(c_name).
  Proof.
    intros ** WTp Hin Hc'.
    rewrite Hc' in Hin; clear c' Hc'.
    inversion_clear WTp as [|? ? WTc WTp' Hnodup]; clear WTp'.
    inversion_clear Hnodup as [|? ? Hnin Hnodup'].
    apply Hnin.
    inversion_clear WTc as [Ho Hm]; clear Hm.
    apply In_Forall with (1:=Ho) in Hin.
    apply not_None_is_Some in Hin.    
    destruct Hin as ((cls, p') & Hin).
    simpl in Hin. rewrite <-(find_class_name _ _ _ _ Hin) in *.
    apply find_class_In in Hin.
    now apply in_map.
  Qed.

  Inductive sub_prog: program -> program -> Prop := 
    sub_prog_intro: forall p p', 
      sub_prog p (p' ++ p).

  Lemma sub_prog_refl:
    forall p, sub_prog p p.
  Proof.
    intro; rewrite <-app_nil_l; constructor.
  Qed.
    
  Add Parametric Relation: program sub_prog
      reflexivity proved by sub_prog_refl
        as sub_prog_rel.

  Lemma sub_prog_cons:
    forall cls prog' prog,
      sub_prog (cls :: prog') prog ->
      sub_prog prog' prog.
  Proof.
    intros ** Hsub.
    inv Hsub.
    rewrite <-app_last_app. constructor.
  Qed.
  
  Remark find_class_sub_same: 
    forall prog1 prog2 clsid cls prog', 
      find_class clsid prog2 = Some (cls, prog') -> 
      wt_program prog1 -> 
      sub_prog prog2 prog1 -> 
      find_class clsid prog1 = Some (cls, prog'). 
  Proof. 
    intros ** Hfind WD Sub.
    inv Sub.
    induction p' as [|cls' p']; simpl; auto.
    inversion_clear WD as [|? ? WTc WTp Hnodup].
    specialize (IHp' WTp).
    destruct (ident_eq_dec cls'.(c_name) clsid) as [He|Hne].
    - rewrite map_cons in Hnodup.
      apply NoDup_cons' in Hnodup.
      destruct Hnodup as (Hnin & Hnodup).
      rewrite He in *; clear He.
      contradiction Hnin.
      rewrite <-(find_class_name _ _ _ _ IHp').
      apply find_class_In in IHp'.
      now apply in_map.
    - apply ident_eqb_neq in Hne.
      now rewrite Hne, IHp'.
  Qed.

  Lemma find_class_sub: 
    forall prog clsid cls prog', 
      find_class clsid prog = Some (cls, prog') -> 
      sub_prog prog' prog. 
  Proof. 
    intros ** Find. 
    apply find_class_app in Find.
    destruct Find as (? & ? & ?); subst. 
    rewrite List_shift_first. 
    constructor. 
  Qed. 

  Hint Constructors sub_prog.  

  Lemma find_class_chained:
    forall prog c1 c2 cls prog' cls' prog'',
      wt_program prog ->
      find_class c1 prog = Some (cls, prog') ->
      find_class c2 prog' = Some (cls', prog'') ->
      find_class c2 prog = Some (cls', prog'').
  Proof.
    induction prog as [|c prog IH]; [now inversion 2|].
    intros ** WTp Hfc Hfc'.
    simpl in Hfc.
    inversion_clear WTp as [|? ? WTc WTp' Hnodup].
    pose proof (find_class_In _ _ _ _ Hfc') as Hfcin.
    pose proof (find_class_name _ _ _ _ Hfc') as Hc2.
    destruct (ident_eq_dec c.(c_name) c1) as [He|Hne].
    - rewrite He, ident_eqb_refl in Hfc.
      injection Hfc; intros R1 R2; rewrite <-R1, <-R2 in *; clear Hfc R1 R2.
      inversion_clear Hnodup as [|? ? Hnin Hnodup'].
      assert (c.(c_name) <> cls'.(c_name)) as Hne.
      + intro Hn. apply Hnin.
        apply in_split in Hfcin.
        destruct Hfcin as (ws & xs & Hfcin).
        rewrite Hfcin, map_app, map_cons.
        apply in_or_app; right. now constructor.
      + simpl. apply ident_eqb_neq in Hne.
        rewrite Hc2 in Hne. now rewrite Hne.
    - apply ident_eqb_neq in Hne.
      rewrite Hne in Hfc. clear Hne.
      rewrite <- (IH _ _ _ _ _ _ WTp' Hfc Hfc').
      inversion_clear Hnodup as [|? ? Hnin Hnodup'].
      apply find_class_app in Hfc.
      destruct Hfc as (cls'' & Hprog & Hfc).
      rewrite Hprog in Hnin.
      assert (c.(c_name) <> cls'.(c_name)) as Hne.
      + intro Hn. apply Hnin.
        apply in_split in Hfcin.
        destruct Hfcin as (ws & xs & Hfcin).
        rewrite Hfcin, map_app, map_cons, map_app, map_cons.
        apply in_or_app; right.
        constructor 2.
        apply in_or_app; right.
        now constructor.
      + simpl. rewrite <-Hc2. apply ident_eqb_neq in Hne.
        now rewrite Hne.
  Qed.
  
End TYPING.

Module Typing
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Syn   : SYNTAX Ids Op OpAux)
       (Import Sem   : SEMANTICS Ids Op OpAux Syn)
           <: TYPING Ids Op OpAux Syn Sem.
  Include TYPING Ids Op OpAux Syn Sem.
End Typing.

