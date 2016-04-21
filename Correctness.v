Require Import Rustre.Nelist.
Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Rustre.Common.
Open Scope positive.

Require Import Rustre.RMemory.
Require Import Rustre.Dataflow.
(* TODO: these should go *)
Require Import Rustre.Dataflow.IsVariable.Decide.
Require Import Rustre.Dataflow.IsDefined.Decide.

Require Import Rustre.Minimp.
Require Import Rustre.Translation.
Require Import Rustre.Correctness.Proper.
Require Import Rustre.Correctness.IsPresent.
Require Import Rustre.Correctness.MemoryCorres.
Require Import Rustre.Minimp.FuseIfte.
Require Import Rustre.Dataflow.Clocking.Parents.
Require Import Rustre.Dataflow.Clocking.Properties.

Module Type CORRECTNESS
       (Op : OPERATORS)
       (Import SynDF : Rustre.Dataflow.Syntax.SYNTAX Op)
       (Import SynMP : Rustre.Minimp.Syntax.SYNTAX Op)
       (Import Str : STREAM Op)
       (Import Ord : ORDERED Op SynDF)
       (Import IsF : ISFREE Op SynDF)
       (Import SemDF : Rustre.Dataflow.Semantics.SEMANTICS Op SynDF Str Ord)
       (Import SemMP : Rustre.Minimp.Semantics.SEMANTICS Op SynMP)
       (Import Mem : MEMORIES Op SynDF)
       (Import IsD : ISDEFINED Op SynDF Mem)
       (Import Trans : TRANSLATION Op SynDF SynMP)
       (Import IsV : ISVARIABLE Op SynDF Mem IsD)
       (Import IsP : ISPRESENT Op SynDF SynMP SemMP Trans)
       (Import NoD : NODUP Op SynDF Mem IsD IsV)
       (Import WeF : WELLFORMED Op SynDF IsF Ord Mem IsD IsV NoD)
       (Import MemSem : MEMSEMANTICS Op SynDF Str Ord Mem IsF IsD SemDF IsV NoD WeF)
       (Import MemCor : MEMORYCORRES Op SynDF SynMP SemMP Str Ord Mem IsF IsD SemDF IsV NoD WeF MemSem)
       
       (Import IsVDec : IsVariable.Decide.DECIDE Op SynDF Mem IsD IsV)
       (Import IsDDec : IsDefined.Decide.DECIDE Op SynDF Mem IsD)

       (Import Proper : PROPER Op SynDF SynMP Trans Mem)
       (Equ : EQUIV Op SynMP SemMP)
       (Import Fus : FUSEIFTE Op SynDF SynMP SemMP Equ)
       (Import Clo : CLOCKING Op SynDF)
       (Par : PARENTS Op SynDF Clo)
       (Import Pro : PROPERTIES Op SynDF IsF Clo Mem IsD Par).
      
       (** ** Technical lemmas *)

       Lemma exp_eval_tovar:
  forall x v menv env mems,
    exp_eval menv env (tovar mems x) v
    <-> (exp_eval menv env (State x) v /\ PS.In x mems)
      \/ (exp_eval menv env (Var x) v /\ ~PS.In x mems).
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
              try inversion_clear Hs;
              (left; now intuition)
              || (right;
                  repeat progress
                         match goal with
                         | H: stmt_eval _ _ _ Skip _ |- _ => inversion H; subst; clear H
                         | Hp: Is_present_in _ _ _ _,
                               He: exp_eval _ _ _ _ |- Is_absent_in _ _ _ _
                           => apply IsAbs2 with (1:=Hp) (2:=He)
                         | _ => intuition
                         end).
          Admitted.

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
            intros prog mems menv env ck.
            induction ck; intro s; split.
            - inversion 1.
            - intros menv' env' Hp Hs; exact Hs.
            - inversion_clear 1 as [ ? ? ? Hp|? ? ? ? Hp Hexp Hneq];
              destruct b;
              try (now apply IHck with (1:=Hp));
              apply not_eq_sym in Hneq;
              (apply Bool.not_true_is_false in Hneq
                                               || apply Bool.not_false_is_true in Hneq);
              subst;
              apply IHck with (1:=Hp);
              (apply Iifte_false with (1:=Hexp)
                                      || apply Iifte with (1:=Hexp));
              rewrite Op.bool_inv; constructor.
            - inversion_clear 1 as [|? ? ? Hp Hexp];
              intro Hs;
              destruct b;
              apply IHck; auto;
              eapply Iifte; eauto; rewrite Op.bool_inv; auto.
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
              (apply IHce || inversion_clear 1; destruct (Op.to_bool v)); auto.
          Qed.

          Lemma stmt_eval_translate_cexp_env_add:
            forall prog menv env mems x menv' env' ce,
              stmt_eval prog menv env (translate_cexp mems x ce) (menv', env')
              -> exists c, env' = PM.add x c env.
          Proof.
            intros prog menv env mems x menv' env'.
            induction ce;
              (apply IHce || inversion_clear 1; destruct (Op.to_bool v)); auto;
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
            - unfold translate_eqn in Heval.
              apply stmt_eval_Control_fwd in Heval;
                destruct Heval as [[Hipi Heval]|[Habs [Hmenv Henv]]];
                [|rewrite Henv; reflexivity].
              apply stmt_eval_translate_cexp_env_add in Heval.
              destruct Heval; rewrite H; rewrite PM.gso;
              [reflexivity|intro HR; rewrite HR in *; apply Hnd; constructor].
            - apply stmt_eval_Control_fwd in Heval; destruct Heval as [Heval|Heval];
              destruct Heval as [Heval1 Heval2].
              inversion_clear Heval2.
              rewrite <- H3.
              rewrite PM.gso; [reflexivity|].
              intro Hxy; apply Hnd; rewrite Hxy; constructor.
              destruct Heval2 as [Hmenv Henv]; rewrite Henv; intuition.
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
            forall x mems menv env v,
              (~ PS.In x mems -> PM.find x env = Some v)
              -> (PS.In x mems -> mfind_mem x menv = Some v)
              -> exp_eval menv env (tovar mems x) v.
          Proof.
            intros x mems menv env v Hvar Hmem.
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
            inversion_clear 1.
            constructor. apply IHck; auto.
            intros.
            split_env_assumption.
            apply exp_eval_tovar.
            destruct In_dec with x mems;
              intuition.
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
            constructor; apply IHck; now auto.
            eapply clock_correct_true in H0; auto.
            eapply IsAbs2; eauto.
            split_env_assumption.
            destruct In_dec with x mems as [Hin|Hin];
              match goal with
              | H:~PS.In _ _ -> _, Hin:~PS.In _ _ |- _ => specialize (H Hin)
              | H:PS.In _ _ -> _, Hin:PS.In _ _ |- _ => specialize (H Hin)
              end;
              apply PS.mem_spec in Hin || apply mem_spec_false in Hin;
              unfold tovar;
              rewrite Hin;
              intuition.
          Qed.

          (** *** Correctness of [translate_lexp] *)

          Theorem lexp_correct:
            forall R mems menv env c e,
              sem_lexp_instant true R e (present c)
              -> equiv_env (fun x => Is_free_in_lexp x e) R mems env menv 
              -> exp_eval menv env (translate_lexp mems e) c.
          Proof.
            Hint Constructors exp_eval.
            intros until e. revert c.
            (* XXX: This is extremely shaky *)
            induction e as [c0|y|e IH y yb|op le IHle|op le1 IHle1 le2 IHle2] (* using lexp_ind2 *); intro c;
            inversion 1; try (subst; injection H1); intros; subst; try apply IH; try apply econst; auto.
            - split_env_assumption;
              unfold translate_lexp;
              destruct (PS.mem y mems) eqn:Hm;
              rewrite PS.mem_spec in Hm || rewrite mem_spec_false in Hm;
              auto.
            - simpl. apply eunop with c0.
              + apply IHle; auto.
              + destruct (Op.sem_unary op c0); [now inversion H3 | discriminate].
            - simpl. apply ebinop with (c1 := c1) (c2 := c2).
              + apply IHle1; auto.
              + apply IHle2; auto.
              + destruct (Op.sem_binary op c1 c2); [now inversion H4 | discriminate].
                (* - subst. simpl. apply eop with cs. *)
            (* + clear H2 H4 H. *)
            (*   assert (Hlen : Nelist.length les = Nelist.length cs). *)
            (*   { rewrite <- (Nelist.map_length present). eapply Nelist.Forall2_length; eassumption. } *)
            (*   revert cs Hlen H3. induction les; intros cs Hlen Hrec. *)
            (* - { destruct cs as [c1 | c1 cs]. *)
            (*     + constructor. inversion_clear Hrec. inversion_clear IHle. apply H0; trivial. *)
            (*       weaken_equiv_env. constructor(eauto). *)
            (*     + destruct cs; simpl in Hlen; discriminate. } *)
            (* - { destruct cs as [c1 | c1 cs]. *)
            (*     * inversion Hrec. *)
            (*     * simpl. constructor. *)
            (*     + inversion_clear IHle. *)
            (*       apply H. *)
            (*     - now inversion_clear Hrec. *)
            (*     - weaken_equiv_env. constructor(auto). *)
            (*       + inversion_clear Hrec. apply IHles; omega || trivial. *)
            (*     - now inversion IHle. *)
            (*     - weaken_equiv_env. inversion H1. constructor(assumption). *)
            (*     - simpl in Hlen. omega. } *)
            (*   + destruct (apply_op op cs); now inversion H2. *)
          Qed.

          Theorem lexps_correct:
            forall R mems menv env cs es,
              let vs := Nelist.map present cs in
              Nelist.Forall2 (fun e v => sem_lexp_instant true R e v) es vs
              -> equiv_env (fun x => Nelist.Exists (Is_free_in_lexp x) es) R mems env menv 
              -> Nelist.Forall2 (exp_eval menv env) (Nelist.map (translate_lexp mems) es) cs.
          Proof.
            Hint Constructors Forall2.
            intros until cs.
            induction cs; intros es Hvs Hsem Hequiv; subst Hvs.
            + inv Hsem. constructor. eapply lexp_correct; eauto.
              repeat intro. apply Hequiv; trivial. now constructor.
            + inv Hsem. simpl. constructor.
            - eapply lexp_correct; eauto.
              repeat intro. apply Hequiv; trivial. now constructor.
            - apply IHcs; trivial. repeat intro. apply Hequiv; trivial. now constructor(assumption).
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
            induction e as [b et IHt ef IHf|e].
            - (* Emerge *)
              inversion_clear 1; intro Henv.
              + apply Iifte with (Op.of_bool true).
                * split_env_assumption.
                  apply get_exp_eval_tovar; now auto.
                * rewrite Op.bool_inv; apply IHt; now auto.
              + apply Iifte with (Op.of_bool false).
                * split_env_assumption.
                  apply get_exp_eval_tovar; now auto.
                * rewrite Op.bool_inv; apply IHf; now auto.
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
              inversion_clear Hmeq as [| |? ? ? ? ? ? ls ? ? ? Hmfind Hms0 Hsemls HxS Hmls].
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
                  stmt_step_eval prog menv f inputs menv' output
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
                      (inputs: nelist ident)
                      (Hinput: forall input, Nelist.In input inputs -> ~ PS.In input mems)
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
                -> (forall c input, Nelist.In input inputs ->
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
                -> (forall input, Nelist.In input inputs -> ~ Is_defined_in_eqs input eqs)

                (* - execution of translated equations *)
                -> Is_well_sch mems inputs eqs

                (* - unwritten memories (assumed) *)
                -> List.Forall (Memory_Corres_eq G n M menv) alleqs

                (* - locals (shown) *)
                -> (exists menv' env',
                      stmt_eval prog menv env (translate_eqns mems eqs) (menv', env')
                      /\ (forall x, Is_variable_in_eqs x eqs
                              -> forall c : Op.val, sem_var_instant (restr H n) x (present c)
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

              inversion Hsem as [ bk0 H0 M0 i ck xs ce Hvar Hce HR1 HR2 HR3
                                | bk0 H0 M0 y ck f Mo les ls xs Hmfind Hlaes Hvar Hmsem HR1 HR2 HR3
                                | bk0 H0 M0 ms y ck ls yS v0 le Hmfind Hms0 Hlae HyS Hvar HR1 HR2 HR3];
                subst bk0 H0 M0 eq;
                (*    (rewrite <-HR3 in *; clear HR1 HR2 HR3 H0 M0); *)
                specialize (Hvar n).
              - (* Case EqDef: y = cae *)
                exists menv'. (* the memory does not change *)

                specialize (Hce n); simpl in *.
                assert (equiv_env (fun x => Is_free_in_caexp x ck ce) (restr H n) mems env' menv')
                  as Hce'.
                {
                  Hint Constructors Is_free_in_eq.
                  intros.
                  split; intro Hmems.

                  - assert (Hdecide_x: Is_variable_in_eqs x eqs \/ Nelist.In x inputs)
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
                    eapply Is_memory_in_msem_var in H1; try eassumption. do 2 destruct H1; subst c.
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
                    (* TODO: do we really need this [destruct]? It seems that we *know* that it cannot be a variable (proof by [contradiction]/[discriminate]).
                 If not, remove dependency on [Dataflow.IsVariable.Decide] *)
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
                assert (equiv_env (fun x => Is_free_in_laexps x ck les) (restr H n) mems env' menv')
                  as Hlae'. {
                  intros.
                  split; intro Hmems.

                  - assert (Hdecide_x: Is_variable_in_eqs x eqs \/ Nelist.In x inputs)
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
                    eapply Is_memory_in_msem_var in H1; try eassumption. do 2 destruct H1; subst c.
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
                inversion_clear Hmceq as [|? ? ? ? ? ? Hmc0|].
                specialize (Hmc0 _ Hmfind).
                destruct Hmc0 as [omenv [Hfindo Hmc0]].
                (* dataflow semantics *)
                assert (Hmsem':=Hmsem).
                inversion_clear Hmsem' as [? ? ? ? ? i o neqs Hck Hfind Hnsem].
                destruct Hnsem as [Hn [Hlsn [Hxsn [Hout Hnsem]]]].

                (* no other instance *)
                assert (~Is_defined_in_eqs y eqs) as Hniii
                    by (inversion_clear Hwsch; eauto).

                specialize (Hlaes n);
                  specialize (Hxsn n);
                  specialize (Hout n);
                  simpl in *.

                inversion_clear Hlaes.
                + (* y = present *)
                  rename cs into inValues.

                  assert (exists c : Op.val, xs n = present c) as [outValue Hxsc].
                  {
                    apply not_absent_present.
                    intro HH.
                    apply Hout in HH.
                    eapply not_absent_present_list; eauto.
                  }
                  rewrite Hxsc in *.

                  assert (exists menv' : heap,
                             stmt_step_eval prog omenv  f inValues menv' outValue
                             /\ Memory_Corres G (S n) f Mo menv') as Hclass
                      by (eapply Hnode; eauto).
                  destruct Hclass as [omenv' [Hnstmt Hnmc]].

                  simpl in *.
                  exists (madd_obj y omenv' menv'), (PM.add y outValue env').
                  split;[|split].
                  * apply stmt_eval_translate_eqns_cons.
                    exists menv', env'.
                    split; [exact Hstmt|].
                    apply stmt_eval_Control_present.
                    eapply clock_correct_true; now eauto.

                    assert (equiv_env (fun x : ident => Nelist.Exists (Is_free_in_lexp x) les)
                                      (restr H n) mems env' menv')
                      by weaken_equiv_env.

                    assert (Nelist.Forall2 (exp_eval menv' env')
                                           (Nelist.map (translate_lexp mems) les) inValues).
                    {
                      rewrite Hbase in *.
                      eapply lexps_correct; eauto.
                      match goal with
                      | H: _ = Nelist.map present inValues |- _ => rewrite <- H
                      | H: Nelist.map present inValues = _ |- _ => rewrite H
                      end. eauto.
                    }
                    erewrite <-stmt_eval_translate_eqns_minst_inv in Hfindo; eauto.
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
                                List.Forall (rhs_absent_instant (bk0 n) (restr Hn n)) neqs)
                    by (eapply subrate_property_eqns; eauto).

                  assert (absent_list ls n)
                    by (unfold absent_list; rewrite H0, Nelist.map_compose; auto).

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
                    inversion Hivi' as [|x' ck' f' e HR1 [HR2 HR3 HR4]];
                      subst x' ck' f' x e.
                    split; intro Hsv'.
                    { inversion_clear Hsv' as [Hfind'].
                      inversion_clear Hvar as [Hfind''].
                      rewrite Hfind' in Hfind''.
                      injection Hfind''; intro HR1; rewrite <-HR1 in *; clear HR1 Hfind''.
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
                    rewrite stmt_eval_translate_eqns_minst_inv with (1:=Hstmt) (2:=Hniii).
                    split; [exact Hfindo|].
                    eapply Memory_Corres_unchanged; eauto.

              - (* Case EqFby: y = v0 fby lae *)
                specialize (Hlae n).
                assert (equiv_env (fun x => Is_free_in_laexp x ck le) (restr H n) mems env' menv')
                  as Hlae'.
                {
                  intros.
                  split; intro Hmems.

                  - assert (Hdecide_x: Is_variable_in_eqs x eqs \/ Nelist.In x inputs)
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
                    eapply Is_memory_in_msem_var in H1; try eassumption. do 2 destruct H1; subst c.
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
                      injection Hmfind'; intro Heq; rewrite <-Heq in *; clear Heq Hmfind'.
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

            Lemma assoc_inputs:
              forall R inArgs inputs c arg,
                Nelist.In arg inArgs -> Nelist.NoDup inArgs ->
                sem_var_instant R arg (present c) ->
                Nelist.Forall2 (sem_var_instant R) inArgs (Nelist.map present inputs) ->
                Assoc inArgs inputs arg c.
            Proof.
              intros * Hin Hnodup Hsem_var. revert inputs.
              induction inArgs as [|inArg inArgs']; intros inputs Hall; inv Hall.
              + symmetry in H0. rewrite Nelist.map_eq_nebase in H0. destruct H0 as [? [? ?]]. subst.
                inv Hin.
                assert (x = c) by (cut (present x = present c); [ injection 1; congruence | sem_det]); subst.
                constructor.
              + symmetry in H1. rewrite Nelist.map_eq_necons in H1. decompose [ex and] H1. clear H1. subst.
                inv Hnodup. inv Hin.
              - assert (x = c) by (cut (present x = present c); [ injection 1; congruence | sem_det]); subst.
                constructor.
              - constructor; auto.
                intro. subst. contradiction.
            Qed.


            Lemma sem_var_assoc:
              forall R inArg inputs c input,
                Assoc inArg inputs input c ->
                Nelist.Forall2 (sem_var_instant R) inArg (Nelist.map present inputs) ->
                sem_var_instant R input (present c).
            Proof.
              intros ** Hassoc Hsem_vars.
              induction Hassoc; inversion_clear Hsem_vars; eauto.
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

                  inversion_clear Hwd as [|? ? Hwd' eqs inArg outArg
                                             HnodupIn Hwsch Hndef_in Hdef_out Hne Hfind Hnodup].
                  clear Hwd'.
                  inversion_clear Hmsem as [? ? ? ? ? ? ? ? Hck Heqs
                                              [H [Hin [Hout [Hrabs Hall]]]]].
                  subst eqs inArg outArg nodeName.
                  simpl in Heqs; rewrite Hfeq in Heqs; simpl in Heqs.
                  injection Heqs. intro Hnode. rewrite Hnode in *. clear Heqs. simpl in *.

                  rename i into inArg; rename o into outArg; rename eqs0 into eqs.

                  set (env := adds inArg inputs sempty).

                  assert (msem_equations G bk H M eqs)
                    by (eapply Forall_msem_equation_global_tl; try eassumption).

                  assert (exists (menv' : heap) (env' : stack),
                             stmt_eval (translate G) menv env (translate_eqns (memories eqs) eqs) (menv', env') /\
                             (forall x : ident,
                                 Is_variable_in_eqs x eqs ->
                                 forall c : Op.val,
                                   sem_var_instant (restr H n) x (present c) <->
                                   PM.find x env' = Some c) /\
                             Forall (Memory_Corres_eq G (S n) M menv') eqs) as His_step_correct.
                  {
                    assert (Hlen : Nelist.length inArg = Nelist.length inputs).
                    {
                      transitivity (Nelist.length (xs n)).
                      * eapply Nelist.Forall2_length; eauto.
                      * rewrite Hxs, Nelist.map_length. auto.
                    }
                    eauto.
                    eapply is_step_correct; eauto.
                    - apply Hck; eauto.
                    - exists []; auto.
                    - intros y Hinm.
                      assert (NoDup_defs eqs) as Hndds
                          by (eapply Is_well_sch_NoDup_defs; eauto).
                      split; [now apply Is_defined_in_memories
                             |now apply not_Is_variable_in_memories].
                    - intros c input Hinput.
                      specialize (Hin n).
                      split; intro HH.
                      + subst env.
                        apply gsss; eauto.
                        rewrite nelist2list_NoDup in HnodupIn. eapply assoc_inputs; eauto; [].
                        match goal with | H : context[inputs] |- _ => move H at bottom end.
                        unfold present_list in Hxs. rewrite <- Hxs. auto.
                      + subst env.
                        apply gsss in HH; trivial.
                        eapply sem_var_assoc; eauto.
                        match goal with | H : context[inputs] |- _ => move H at bottom end.
                        unfold present_list in Hxs.
                        rewrite <- Hxs. auto.
                    - intros x Hivi.
                      subst env.
                      rewrite gsos, PM.gempty; auto.
                      rewrite <- Nelist.nelist2list_In. intro.
                      apply Is_variable_in_eqs_Is_defined_in_eqs in Hivi.
                      apply Hndef_in, Exists_exists; eauto.

                    - intros input Hinput Hisdef.
                      rewrite <- Nelist.nelist2list_In in Hinput.
                      apply Hndef_in. apply Exists_exists.
                      eauto.

                    - inversion_clear Hmc as [? ? ? ? ? ? Hf Hmeqs].

                      simpl in Hf.
                      rewrite ident_eqb_refl in Hf.
                      injection Hf; intros Heq0 Heq1 Heq2;
                      rewrite <-Heq0, <-Heq1, <-Heq2 in *;
                      clear Heq0 Heq1 Heq2 Hf.

                      eapply Memory_Corres_eqs_node_tl; try eassumption.
                  }

                  destruct His_step_correct as [menv' [env' [Hstmt [Hsemvar Hmem]]]].
                  exists menv'.
                  split.
                  * {
                      econstructor; eauto.
                      - simpl. rewrite Pos.eqb_refl. reflexivity.
                      - subst env. simpl.
                        assert (inArg = n_input node)
                          by (rewrite Hnode; auto).
                        assert (eqs = n_eqs node)
                          by (rewrite Hnode; auto).
                        subst inArg; subst eqs.
                        rewrite ps_from_list_gather_eqs_memories. eapply Hstmt.
                      - assert (outArg = n_output node)
                          by (rewrite Hnode; auto).
                        subst outArg.
                        specialize (Hout n); simpl in Hout; rewrite Hys in Hout.
                        simpl. apply Hsemvar; try assumption.
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
                    simpl; subst nodeName; rewrite Hfeq.
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
              -> exists menv',
                stmt_reset_eval prog f menv'
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
                      (inputs: Nelist.nelist ident).


            Lemma is_reset_correct:
              forall bk eqs,
                msem_equations G bk H M eqs ->
                Is_well_sch mems inputs eqs ->
                (forall f, equiv_reset G (translate G) f) ->
                exists menv' env',
                  stmt_eval (translate G) hempty sempty (translate_reset_eqns eqs)
                            (menv', env')
                  /\ Forall (Memory_Corres_eq G 0 M menv') eqs.
            Proof.
              intros * Hmsem Hwsch Hreset.
              induction eqs as [|eq eqs IH]; [eauto|].
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
                inversion_clear Hsem as [|? ? ? ? ? ? Mo ? xs' ys' Hmfind Hxs' Hys' HsemNode|].
                assert (exists omenv, stmt_reset_eval (translate G) f omenv
                                 /\ Memory_Corres G 0 f Mo omenv) as [omenv [Hstmt_reset Hmcf]]
                    by (eapply Hreset; try eassumption).

                exists (madd_obj i omenv menv'), env'.
                split.
                + rewrite stmt_eval_translate_reset_eqn_shift.
                  exists menv', env'.
                  split; try assumption.
                  econstructor; [|constructor].
                  econstructor; auto.
                  assumption.
                + repeat constructor; [| apply Memory_Corres_eqs_add_obj; eauto].
                  intros M' Hmfind'.
                  rewrite Hmfind in Hmfind'; injection Hmfind'; intro Heq; subst M'.
                  exists omenv.
                  rewrite mfind_inst_gss.
                  auto.
              - (* EqFby *)
                exists (madd_mem i v menv'), env'.
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
            - intros f Hwdef xs ys M Hmsem.

              assert (Ordered_nodes (node :: G)) as HordG
                  by (apply Welldef_global_Ordered_nodes; assumption).

              set (nodeName := n_name node).

              destruct (ident_eqb nodeName f) eqn:Heqb.
              + assert (nodeName = f) as Hfeq
                    by (apply Pos.eqb_eq; assumption).

                inversion_clear Hmsem as [? ? ? ? ? inArg outArg eqs Hbk Hfind
                                            [H [Hin [Hout [Hrhs Hmsem']]]]].
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

                assert (Is_well_sch (memories eqs) inArg eqs)
                  by (inversion Hwdef; subst ni eqs0;
                      rewrite Hfind in *; simpl in *; assumption).

                assert (Welldef_global G)
                  by (inversion Hwdef; assumption).

                assert (exists menv' env',
                           stmt_eval (translate G) hempty sempty (translate_reset_eqns eqs)
                                     (menv', env')
                           /\ Forall (Memory_Corres_eq G 0 M menv') eqs)
                  as [menv' [env' [Hstmt Hmc]]].
                {
                  eapply is_reset_correct; try eassumption.
                  intro; apply IH; assumption.
                }

                exists menv'.
                split.
                * {
                    econstructor.
                    - simpl. rewrite Heqb. reflexivity.
                    - subst node; eassumption.
                  }
                * {
                    econstructor.
                    - simpl; rewrite Heqb. subst node. reflexivity.
                    - apply Memory_Corres_eqs_node_tl; try assumption.
                      inversion Hwdef. subst eqs0. rewrite Hfind in *. simpl. assumption.
                  }

              + assert (nodeName <> f) as Hfneq
                    by (apply Pos.eqb_neq; assumption).

                apply Welldef_global_cons in Hwdef.
                apply msem_node_cons in Hmsem; try assumption.
                edestruct IH as [menv' [Hstmt Hmc]]; try eassumption.
                exists menv'; split.
                * inversion_clear Hstmt.
                  econstructor; try eassumption.
                  simpl. subst nodeName; rewrite Heqb. assumption.
                * apply Memory_Corres_node_tl; eassumption.
          Qed.

          (** ** Correctness, from the point of view of the event loop *)

          Section EventLoop.

            Variables (G     : global)
                      (main  : ident)
                      (css   : stream (nelist Op.val))
                      (ys    : stream value)
                      (r     : ident)
                      (obj   : ident)
                      (Hwdef : Welldef_global G).

            Let xss := fun n => Nelist.map present (css n).

            Variable (Hsem: sem_node G main xss ys).

            Open Scope nat_scope.
            (* =step= *)
            Fixpoint step (n: nat) P r main obj css menv env: Prop :=
              match n with
              | 0 => stmt_eval P hempty sempty (Reset_ap main obj) (menv, env)
              | S n => let vs := Nelist.map Const (css n) in
                      exists menvN envN, step n P r main obj css menvN envN
                                    /\ stmt_eval P menvN envN (Step_ap r main obj vs) (menv, env)
              end.
            (* =end= *)

            Lemma is_event_loop_correctG:
              forall M,
                let P := translate G in
                msem_node G main xss M ys ->
                forall n,
                exists menv env omenv,
                  step (S n) P r main obj css menv env
                  /\ mfind_inst obj menv = Some omenv
                  /\ Memory_Corres G (S n) main M omenv
                  /\ (forall co, ys n = present co <-> PM.find r env = Some co).
            Proof.
              intros * Hmsem n.
              assert (exists menv0,
                         stmt_reset_eval (translate G) main menv0
                         /\ Memory_Corres G 0 main M menv0) as [menv0 [Hstmtr Hmc0]]
                  by (eapply is_node_reset_correct; try eassumption).

              set (ci0 := css 0).

              assert (Hpres: present_list xss 0 ci0)
                by (subst xss; unfold present_list; eauto).

              assert (exists co0, ys 0 = present co0)%nat as [co0 Hco0].
              {
                inversion_clear Hmsem as
                    [ ? ? ? ? ? ? ? ? Hbk Hfind
                        [H [Hsem_in [Hsem_out [Habs Hsem_eqns]]]]].
                apply not_absent_present;
                  rewrite <- Habs;
                  eapply not_absent_present_list; eauto.
              }

              induction n.
              - (* Case: n ~ 0 *)
                assert (exists menv,
                           stmt_step_eval (translate G) menv0 main ci0 menv co0
                           /\  Memory_Corres G 1 main M menv) as [menv1 [Hstmt1 Hmem1]]
                    by (eapply is_node_correct; eauto).

                do 3 eexists.
                split; [|split; [| split]]; try eauto.
                + do 2 eexists; split; simpl step; eauto.
                  econstructor; eauto.
                  * apply mfind_inst_gss.
                  * apply exps_eval_const.
                + apply mfind_inst_gss.
                + rewrite Hco0, PM.gss. intuition congruence.

              - (* Case: n ~ S n *)

                destruct IHn as [menvN [envN [omenvN [HstepN [HmfindN [HmcN HeqN]]]]]].

                set (ciSn := css (S n)).

                assert (HpresN: present_list xss (S n) ciSn)
                  by (subst xss; unfold present_list; eauto).

                assert (exists coSn, ys (S n) = present coSn) as [coSn Hys].
                {
                  inversion_clear Hmsem as
                      [ ? ? ? ? ? ? ? ? Hbk Hfind
                          [H [Hsem_in [Hsem_out [Habs Hsem_eqns]]]]].
                  apply not_absent_present; rewrite <- Habs;
                  eapply not_absent_present_list; eauto.
                }

                assert (exists omenvSn,
                           stmt_step_eval (translate G) omenvN main ciSn omenvSn coSn
                           /\  Memory_Corres G (S (S n)) main M omenvSn) as [omenvSn [HstmtSn HmemSn]]
                    by (eapply is_node_correct; eauto).

                (* XXX: this explicit [exists] is necessary: Coq picks a wrong instance otherwise. *)
                exists (madd_obj obj omenvSn menvN).
                do 2 eexists.

                split; [|split; [| split]]; eauto.
                + do 2 eexists; split; simpl step; try eauto.
                  econstructor; eauto.
                  apply exps_eval_const.
                + apply mfind_inst_gss.
                + rewrite Hys, PM.gss. intuition congruence.
            Qed.

            Theorem is_event_loop_correct:
              (* =translate_correct= *)
              sem_node G main xss ys ->
              forall n, exists menv env,
                  step (S n) (translate G) r main obj css menv env
                  /\ (forall co, ys n = present co <-> PM.find r env = Some co).
            (* =end= *)
            Proof.
              intros until n.

              assert (exists M, msem_node G main xss M ys) as [M Hmsem]
                  by (eapply sem_msem_node; eauto).

              assert (exists menv env omenv,
                         step (S n) (translate G) r main obj css menv env
                         /\ mfind_inst obj menv = Some omenv
                         /\ Memory_Corres G (S n) main M omenv
                         /\ (forall co, ys n = present co <-> PM.find r env = Some co))
                as [menv [env [omenv [Hstep [_ [_ Hys]]]]]]
                  by (eapply is_event_loop_correctG; eauto).

              do 2 eexists; eauto.
            Qed.

          End EventLoop.

          (** ** Correctness of optimized code *)

          Require Import Minimp.FuseIfte.

          Lemma not_Can_write_in_translate_cexp:
            forall x mems ce i,
              x <> i -> ~ Can_write_in i (translate_cexp mems x ce).
          Proof.
            induction ce.
            - intros j Hxni Hcw.
              specialize (IHce1 _ Hxni).
              specialize (IHce2 _ Hxni).
              inversion_clear Hcw; intuition.
            - intros j Hxni Hcw.
              inversion Hcw; intuition.
          Qed.

          Lemma Is_free_in_tovar:
            forall mems i j,
              Is_free_in_exp j (tovar mems i) <-> i = j.
          Proof.
            unfold tovar.
            intros mems i j.
            destruct (PS.mem i mems); split; intro HH;
            (inversion_clear HH; reflexivity || subst; now constructor).
          Qed.

          Lemma Ifte_free_write_translate_cexp:
            forall mems x ce,
              (forall i, Is_free_in_cexp i ce -> x <> i)
              -> Ifte_free_write (translate_cexp mems x ce).
          Proof.
            intros mems x ce Hfree.
            induction ce.
            - simpl; constructor;
              [apply IHce1; now auto|apply IHce2; now auto|].
              intros j Hfree'; split;
              (apply not_Can_write_in_translate_cexp;
                apply Is_free_in_tovar in Hfree';
                subst; apply Hfree; constructor).
            - now constructor.
          Qed.

          Lemma Ifte_free_write_Control_caexp:
            forall mems ck f ce,
              (forall i, Is_free_in_caexp i ck ce -> ~Can_write_in i (f ce))
              -> Ifte_free_write (f ce)
              -> Ifte_free_write (Control mems ck (f ce)).
          Proof.
            induction ck as [|ck IH i b]; [now intuition|].
            intros f ce Hxni Hfce.
            simpl.
            destruct b.
            - apply IH with (f:=fun ce=>Ifte (tovar mems i) (f ce) Skip).
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
            - apply IH with (f:=fun ce=>Ifte (tovar mems i) Skip (f ce)).
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

          Lemma Ifte_free_write_Control_laexp:
            forall mems ck s,
              (forall i, Is_free_in_clock i ck -> ~Can_write_in i s)
              -> Ifte_free_write s
              -> Ifte_free_write (Control mems ck s).
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
              match goal with
              | H:Is_free_in_exp _ (tovar mems _) |- _ => rename H into Hfree
              end.
              unfold tovar in Hfree.
              destruct (PS.mem i mems); inversion Hfree; subst; now auto.
            - intros j Hfree Hcw.
              apply Hxni with (i0:=j); [inversion_clear Hfree; now auto|].
              inversion_clear Hcw as [| |? ? ? ? Hskip| | | | ];
                [inversion Hskip|assumption].
            - repeat constructor; [assumption|now inversion 1|].
              apply Hxni.
              match goal with
              | H:Is_free_in_exp _ (tovar mems _) |- _ => rename H into Hfree
              end.
              unfold tovar in Hfree.
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
              -> (forall input, Nelist.In input inputs -> ~ Is_defined_in_eqs input eqs)
              -> Ifte_free_write (translate_eqns mems eqs).
          Proof.
            intros C mems inputs eqs Hwk Hwks Hwsch Hnvi Hnin.
            induction eqs as [|eq eqs IH]; [now constructor|].
            inversion Hwks as [|eq' eqs' Hwkeq Hwks']; subst.
            specialize (IH Hwks' (Is_well_sch_cons _ _ _ _ Hwsch)).
            unfold translate_eqns.
            simpl; apply Ifte_free_write_fold_left_shift.
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
                  assert (~ Nelist.In x inputs) as Hninp
                      by (intro Hin; eapply Hnin; eauto; constructor(auto)).

                  assert (~PS.In x mems) as Hnxm' by intuition.
                  intro Hxi; rewrite Hxi in *; clear Hxi.
                  specialize (Hnm Hnxm').
                  eapply Hndef; intuition.
                  eapply Is_variable_in_eqs_Is_defined_in_eqs. auto. }
                apply Ifte_free_write_Control_caexp.
                intros i Hfree.
                apply (not_Can_write_in_translate_cexp).
                apply Hfni with (1:=Hfree).
                apply (Ifte_free_write_translate_cexp).
                intros i Hfree; apply Hfni; intuition.
              + assert (~Is_free_in_clock x ck) as Hnfree
                    by (apply Well_clocked_EqApp_not_Is_free_in_clock
                        with (1:=Hwk) (2:=Hwkeq));
                apply Ifte_free_write_Control_laexp;
                [intros i Hfree Hcw; inversion Hcw; subst; contradiction|intuition].
              + assert (~Is_free_in_clock x ck) as Hnfree
                    by (apply Well_clocked_EqFby_not_Is_free_in_clock
                        with (1:=Hwk) (2:=Hwkeq));
                apply Ifte_free_write_Control_laexp;
                [intros i Hfree Hcw; inversion Hcw; subst; contradiction|intuition].
          Qed.

End CORRECTNESS.