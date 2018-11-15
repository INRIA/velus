Require Import Coq.FSets.FMapPositive.
Require Import PArith.
Require Import Logic.FunctionalExtensionality.

Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.NLustre.NLExprSyntax.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.Memories.
Require Import Velus.SyBloc.SBSyntax.
Require Import Velus.NLustre.Ordered.
Require Import Velus.NLustre.Stream.
Require Import Velus.NLustre.NLExprSemantics.
Require Import Velus.NLustre.NLSemantics.
Require Import Velus.SyBloc.SBSemantics.
Require Import Velus.NLustreToSyBloc.Translation.
Require Import Velus.RMemory.
Require Import Velus.NLustre.NLInterpretor.
Require Import Velus.NLustre.WellFormed.
Require Import Velus.NLustre.IsFree.
Require Import Velus.NLustre.IsVariable.
Require Import Velus.NLustre.IsDefined.
Require Import Velus.NLustre.NoDup.

Require Import List.
Import List.ListNotations.

Open Scope list.
Open Scope nat.

Module Type CORRECTNESS
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import OpAux   : OPERATORS_AUX     Op)
       (Import Clks    : CLOCKS          Ids)
       (Import ExprSyn : NLEXPRSYNTAX        Op)
       (Import SynNL   : NLSYNTAX        Ids Op       Clks ExprSyn)
       (SynSB          : SBSYNTAX        Ids Op       Clks ExprSyn)
       (Import Str     : STREAM              Op OpAux)
       (Import Ord     : ORDERED         Ids Op       Clks ExprSyn SynNL)
       (Import ExprSem : NLEXPRSEMANTICS Ids Op OpAux Clks ExprSyn             Str)
       (Import SemNL   : NLSEMANTICS     Ids Op OpAux Clks ExprSyn SynNL       Str ExprSem Ord)
       (SemSB          : SBSEMANTICS     Ids Op OpAux Clks ExprSyn       SynSB Str ExprSem)
       (Import Mem     : MEMORIES        Ids Op       Clks ExprSyn SynNL)
       (Import Trans   : TRANSLATION     Ids Op       Clks ExprSyn SynNL SynSB                 Mem)
       (Import Interp  : NLINTERPRETOR   Ids Op OpAux Clks ExprSyn             Str ExprSem)
       (Import IsD     : ISDEFINED       Ids Op       Clks ExprSyn SynNL                       Mem)
       (Import IsV     : ISVARIABLE      Ids Op       Clks ExprSyn SynNL                       Mem IsD)
       (Import IsF     : ISFREE          Ids Op       Clks ExprSyn SynNL)
       (Import NoD     : NODUP           Ids Op       Clks ExprSyn SynNL                       Mem IsD IsV)
       (Import WeF     : WELLFORMED      Ids Op       Clks ExprSyn SynNL                   Ord Mem IsD IsV IsF NoD).


   Inductive inst_in_eq: ident -> SynSB.equation -> Prop :=
  | InstInEqReset:
      forall x ck m r,
        inst_in_eq x (SynSB.EqReset ck m x r)
  | InstInEqCall:
      forall x xs ck m es,
        inst_in_eq x (SynSB.EqCall xs ck m x es).

  Definition inst_in_eqs (x: ident) (eqs: list SynSB.equation) : Prop :=
    List.Exists (inst_in_eq x) eqs.

  Lemma inst_in_Is_defined_in_eqs:
    forall G bk H xs eqs,
      Forall (sem_equation G bk H) eqs ->
      inst_in_eqs (hd default xs) (translate_eqns eqs) ->
      Is_defined_in_eqs (hd default xs) eqs.
  Proof.
    intros ** Sem_eqs In.
    unfold translate_eqns, concatMap in In.
    induction eqs as [|eq]; simpl in *;
      inversion_clear Sem_eqs as [|?? Sem].
    - inv In.
    - apply Exists_app' in In as [E|E].
      + left.
        destruct eq; try destruct o as [()|]; simpl in *; inversion_clear E as [?? Def|?? Nil];
          try inversion_clear Nil as [?? Def|?? Nil'];
          try inv Def; try inv Nil'; match goal with H: hd _ _ = hd _ _ |- _ => rewrite H end;
            eapply Is_defined_in_EqApp, sem_EqApp_gt0; eauto.
      + right; apply IHeqs; auto.
  Qed.

  Lemma not_inst_in_eqs_cons:
    forall x eq eqs,
      ~ inst_in_eqs x (eq :: eqs)
      <-> ~ inst_in_eq x eq /\ ~ inst_in_eqs x eqs.
  Proof.
    split.
    - intro Hndef; split; intro;
        eapply Hndef; constructor (assumption).
    - intros [? ?] Hdef_all.
      inv Hdef_all; eauto.
  Qed.

  Lemma not_inst_in_eqs_app:
    forall eqs eqs' x,
      ~ inst_in_eqs x (eqs ++ eqs') ->
      ~ inst_in_eqs x eqs /\ ~ inst_in_eqs x eqs'.
  Proof.
    unfold inst_in_eqs.
    intros * Nd.
    split; intro; apply Nd.
    - now apply Exists_app_l.
    - now apply Exists_app.
  Qed.

  Lemma mfby_add_inst:
    forall i v0 ls M xs x M',
      SemSB.mfby i v0 ls M xs ->
      SemSB.mfby i v0 ls (add_inst x M' M) xs.
  Proof.
    inversion_clear 1.
    econstructor; eauto.
  Qed.
  Hint Resolve mfby_add_inst.

  Lemma mfby_add_val:
    forall i v0 ls M xs x mv,
      i <> x ->
      SemSB.mfby i v0 ls M xs ->
      SemSB.mfby i v0 ls (add_val x mv M) xs.
  Proof.
    inversion_clear 2.
    econstructor; eauto.
    rewrite find_val_gso; auto.
  Qed.

  Inductive defined_in_eq: ident -> SynSB.equation -> Prop :=
  | DefEqDef:
      forall x ck e,
        defined_in_eq x (SynSB.EqDef x ck e)
  | DefEqFby:
      forall x ck v e,
        defined_in_eq x (SynSB.EqFby x ck v e)
  | DefEqCall:
      forall x xs ck b o es,
        In x xs ->
        defined_in_eq x (SynSB.EqCall xs ck b o es).

  Definition defined_in_eqs (x: ident) (eqs: list SynSB.equation) : Prop :=
    List.Exists (defined_in_eq x) eqs.

  Lemma defined_in_Is_defined_in_eqs:
    forall x eqs,
      defined_in_eqs x (translate_eqns eqs) ->
      Is_defined_in_eqs x eqs.
  Proof.
    intros ** Def.
    induction eqs as [|eq].
    - inv Def.
    - unfold translate_eqns, concatMap in Def; simpl in Def.
      apply Exists_app' in Def; destruct Def as [E|E].
      + left.
        destruct eq; try destruct o as [()|]; simpl in E;
          inversion_clear E as [?? Def|?? Nil];
          try inversion_clear Nil as [?? Def|?? Nil'];
          try inv Def; try inv Nil'; constructor; auto.
      + right; apply IHeqs; auto.
  Qed.

  Lemma not_defined_in_eqs_cons:
    forall x eq eqs,
      ~ defined_in_eqs x (eq :: eqs)
      <-> ~ defined_in_eq x eq /\ ~ defined_in_eqs x eqs.
  Proof.
    split.
    - intro Hndef; split; intro;
        eapply Hndef; constructor(assumption).
    - intros [? ?] Hdef_all; inv Hdef_all; eauto.
  Qed.

  Lemma not_defined_in_eqs_app:
    forall eqs eqs' x,
      ~ defined_in_eqs x (eqs ++ eqs') ->
      ~ defined_in_eqs x eqs /\ ~ defined_in_eqs x eqs'.
  Proof.
    unfold defined_in_eqs.
    intros * Nd.
    split; intro; apply Nd.
    - now apply Exists_app_l.
    - now apply Exists_app.
  Qed.

  Inductive compat_eq: equation -> list SynSB.equation -> Prop :=
  | CompatEqDef:
      forall x ck e eqs,
        compat_eq (EqDef x ck e) eqs
  | CompatEqFby:
      forall x ck c0 e eqs,
        ~ defined_in_eqs x eqs ->
        compat_eq (EqFby x ck c0 e) eqs
  | CompatEqApp:
      forall xs ck f es r eqs,
        ~ inst_in_eqs (hd default xs) eqs ->
        compat_eq (EqApp xs ck f es r) eqs.

  Inductive compat_eqs: list equation -> Prop :=
  | CompatNil:
      compat_eqs []
  | CompatCons:
      forall eq eqs,
        compat_eqs eqs ->
        compat_eq eq (translate_eqns eqs) ->
        compat_eqs (eq :: eqs).

  Lemma Is_well_sch_compat:
    forall G n bk H mems,
      Forall (sem_equation G bk H) (n_eqs n) ->
      Is_well_sch mems (map fst (n_in n)) (n_eqs n) ->
      compat_eqs (n_eqs n).
  Proof.
    intros ** Heqs WSCH.
    induction (n_eqs n) as [|eq];
      inversion_clear Heqs as [|?? Heq Heqs']; inversion_clear WSCH as [|???? NotDef];
        constructor; auto.
    destruct eq; constructor.
    - intro E; apply (NotDef (hd default i)).
      + eapply Is_defined_in_EqApp, sem_EqApp_gt0; eauto.
      + eapply inst_in_Is_defined_in_eqs; eauto.
    - intro E; eapply NotDef; try constructor.
      now apply defined_in_Is_defined_in_eqs.
  Qed.

  Inductive is_block_in_eq: ident -> SynSB.equation -> Prop :=
    IBI:
      forall xs ck b i es,
        is_block_in_eq b (SynSB.EqCall xs ck b i es).

  Definition is_block_in (b: ident) (eqs: list SynSB.equation) : Prop :=
    Exists (is_block_in_eq b) eqs.

  Lemma not_is_block_in_cons:
    forall b eq eqs,
      ~ is_block_in b (eq :: eqs) <-> ~ is_block_in_eq b eq /\ ~ is_block_in b eqs.
  Proof.
    intros.
    split; intro HH.
    - split; intro; apply HH; unfold is_block_in; intuition.
    - destruct HH; inversion_clear 1; intuition.
  Qed.

  Lemma is_block_in_Forall:
    forall b eqs,
      ~ is_block_in b eqs <-> Forall (fun eq => ~ is_block_in_eq b eq) eqs.
  Proof.
    induction eqs as [|eq eqs IH];
      [split; [now constructor|now inversion 2]|].
    split; intro HH.
    - apply not_is_block_in_cons in HH.
      destruct HH as [Heq Heqs].
      constructor; [exact Heq|apply IH with (1:=Heqs)].
    - apply not_is_block_in_cons.
      inversion_clear HH as [|? ? Heq Heqs].
      apply IH in Heqs.
      intuition.
  Qed.

  Lemma is_block_is_node:
    forall f eqs,
      Is_node_in f eqs <-> is_block_in f (translate_eqns eqs).
  Proof.
    induction eqs; split; inversion 1 as [?? InEq E|??? E].
    - inv InEq.
      unfold translate_eqns, concatMap; simpl.
      destruct r as [()|].
      + right; left; econstructor.
      + left; constructor.
    - unfold translate_eqns, concatMap; simpl.
      apply Exists_app; rewrite <-IHeqs; auto.
    - inv InEq.
      unfold translate_eqns, concatMap in E; simpl in E.
      destruct a; try destruct o as [()|]; simpl in E; inv E.
      left; constructor.
    - unfold translate_eqns, concatMap in H; simpl in H.
      apply Exists_app' in H as [E'|E'].
      + left.
        destruct a; try destruct o as [()|]; simpl in E';
          inversion_clear E' as [?? Def|?? Nil];
          try inversion_clear Nil as [?? Def|?? Nil'];
          try inv Def; try inv Nil'; constructor.
      + right; rewrite IHeqs; auto.
  Qed.

  Section Global.

    Variable G: SynNL.global.
    Let P := translate G.

    Section Sem.

      Variable bk: stream bool.
      Variable H: history.

      Lemma sem_equation_add_inst:
        forall M M' x eqs,
          ~ inst_in_eqs x eqs ->
          Forall (SemSB.sem_equation P bk H M) eqs ->
          Forall (SemSB.sem_equation P bk H (add_inst x M' M)) eqs.
      Proof.
        intros * Hnd Hsem.
        induction eqs as [|eq eqs IH]; [now constructor|].
        apply not_inst_in_eqs_cons in Hnd as [Hnd].
        apply Forall_cons2 in Hsem as [Hsem Hsems].
        constructor; auto.
        induction eq; inv Hsem; eauto using SemSB.sem_equation.
        - econstructor; eauto.
          unfold sub_inst.
          unfold sub_inst; rewrite find_inst_gso; auto.
          intro; apply Hnd; subst; constructor.
        - econstructor; eauto.
          unfold sub_inst; rewrite find_inst_gso; auto.
          intro; apply Hnd; subst; constructor.
      Qed.

      Lemma sem_equation_add_val:
        forall M mv x eqs,
          ~ defined_in_eqs x eqs ->
          Forall (SemSB.sem_equation P bk H M) eqs ->
          Forall (SemSB.sem_equation P bk H (add_val x mv M)) eqs.
      Proof.
        intros * Hnd Hsem.
        induction eqs as [|eq eqs IH]; [now constructor|].
        apply not_defined_in_eqs_cons in Hnd as [Hnd].
        apply Forall_cons2 in Hsem as [Hsem Hsems].
        constructor; auto.
        induction eq; inv Hsem; eauto using SemSB.sem_equation.
        econstructor; eauto.
        apply mfby_add_val; auto.
        intro; subst; apply Hnd; constructor.
      Qed.

    End Sem.

    Lemma equation_correctness:
      forall bk H eqs M eq,
        (forall f xss oss,
            sem_node G f xss oss ->
            exists M, SemSB.sem_block P f M xss oss) ->
        (forall f r xss oss,
            sem_reset G f r xss oss ->
            exists M, SemSB.sem_block P f M xss oss
                 /\ SemSB.reset_regs r M) ->
        sem_equation G bk H eq ->
        compat_eq eq eqs ->
        Forall (SemSB.sem_equation P bk H M) eqs ->
        SemSB.well_structured_memories eqs M ->
        exists M', Forall (SemSB.sem_equation P bk H M') (translate_eqn eq ++ eqs)
              /\ SemSB.well_structured_memories (translate_eqn eq ++ eqs) M'.
    Proof.
      intros ** IHnode IHreset Heq WF Heqs WS.
      inv Heq; simpl; inv WF.
      - repeat (econstructor; eauto).
      - edestruct IHnode as (M' & Block); eauto.
        exists (add_inst (hd default x) M' M); split.
        + constructor.
          * econstructor; eauto.
            apply find_inst_gss.
          * apply sem_equation_add_inst; auto.
        + apply SemSB.well_structured_add_inst_call; auto.
      - edestruct IHreset as (M' & Block & Reset); eauto.
        exists (add_inst (hd default x) M' M); split.
        + constructor.
          * econstructor; eauto.
            apply find_inst_gss.
          *{ constructor.
             - econstructor; eauto.
               apply find_inst_gss.
             - apply sem_equation_add_inst; auto.
           }
        + apply SemSB.well_structured_add_inst_reset_call; auto.
      - exists (add_val x {| SemSB.content := hold (sem_const c0) ls; SemSB.reset := fun _ => false |} M); split.
        + constructor.
          *{ econstructor; eauto.
             econstructor.
             - apply find_val_gss.
             - reflexivity.
             - intro; unfold fby; simpl.
               destruct (ls n); auto.
           }
          * apply sem_equation_add_val; auto.
        + apply SemSB.well_structured_add_val_fby; auto.
    Qed.

    Lemma well_structured_empty:
      SemSB.well_structured_memories [] (empty_memory SemSB.mvalues).
    Proof.
      constructor; unfold find_val, find_inst, SemSB.fbys, SemSB.insts;
        simpl; intros; split; intro H; contradict H; auto; apply not_In_empty.
    Qed.

    Corollary equations_correctness:
      forall bk H eqs,
        (forall f xss oss,
            sem_node G f xss oss ->
            exists M, SemSB.sem_block P f M xss oss) ->
        (forall f r xss oss,
            sem_reset G f r xss oss ->
            exists M, SemSB.sem_block P f M xss oss
                 /\ SemSB.reset_regs r M) ->
        compat_eqs eqs ->
        Forall (sem_equation G bk H) eqs ->
        exists M', Forall (SemSB.sem_equation P bk H M') (translate_eqns eqs)
              /\ SemSB.well_structured_memories (translate_eqns eqs) M'.
    Proof.
      intros ** IHnode IHreset WF Heqs.
      induction eqs as [|eq eqs IHeqs].
      - exists (@empty_memory SemSB.mvalues).
        split; try now constructor.
        apply well_structured_empty.
      - apply Forall_cons2 in Heqs as [Heq Heqs].
        inv WF.
        eapply IHeqs in Heqs as [? ()]; eauto.
        unfold translate_eqns; rewrite concatMap_cons.
        eapply equation_correctness; eauto.
    Qed.

    Lemma find_block_later_not_is_block_in:
      forall b n bl P',
        Ordered_nodes (n :: G) ->
        SynSB.find_block b P = Some (bl, P') ->
        ~ is_block_in n.(n_name) bl.(SynSB.b_eqs).
    Proof.
      intros ** Hord Hfind Hini.
      pose proof (SynSB.find_block_name _ _ _ _ Hfind) as Hb.
      apply find_block_translate in Hfind as (n' & Hfind' & E).
      rewrite E in Hini; simpl in Hini.
      apply is_block_is_node in Hini.
      eapply find_node_later_not_Is_node_in; eauto.
    Qed.

    Lemma find_block_not_is_block_in:
      forall b bl P',
        Ordered_nodes G ->
        SynSB.find_block b P = Some (bl, P') ->
        ~ is_block_in bl.(SynSB.b_name) bl.(SynSB.b_eqs).
    Proof.
      intros ** Hord Hfind Hini.
      pose proof (SynSB.find_block_name _ _ _ _ Hfind) as Hb.
      apply find_block_translate in Hfind as (n' & Hfind' & E).
      apply find_node_split in Hfind' as [G' [aG Hge]].
      rewrite Hge in Hord.
      apply Ordered_nodes_append in Hord.
      inversion_clear Hord as [|? ? Hord' Heqs Hnin].
      destruct (Heqs (SynSB.b_name bl)) as (Eq).
      - subst bl; simpl in *.
        clear - Hini.
        induction (n_eqs n') as [|eq]; simpl in *.
        + inv Hini.
        + unfold translate_eqns, concatMap, is_block_in in Hini; simpl in Hini.
          unfold is_block_in in Hini; rewrite Exists_app' in Hini.
          destruct Hini as [Hini|Hini].
          * left.
            destruct eq; try destruct o as [()|]; simpl in Hini;
              inversion_clear Hini as [?? In|?? Nil];
              try inversion_clear Nil as [?? In|?? Nil']; try inv In; try inv Nil';
                constructor.
          * right. apply IHl; auto.
      - apply Eq; subst bl; reflexivity.
    Qed.

    Lemma sem_block_cons:
      forall n f xs M ys,
        Ordered_nodes (n :: G) ->
        n.(n_name) <> f ->
        SemSB.sem_block (translate (n :: G)) f xs M ys ->
        SemSB.sem_block P f xs M ys.
    Proof.
      intros ** Hord Hnf Hsem.
      revert Hnf.
      induction Hsem
        as [| | | |????????? Hfind ????? Heqs WS IHeqs]
             using SemSB.sem_block_mult
        with (P_equation := fun bk H M eq =>
                              ~ is_block_in_eq n.(n_name) eq ->
                              SemSB.sem_equation (translate G) bk H M eq);
        eauto using SemSB.sem_equation.
      - intros Hnin.
        econstructor; eauto.
        apply IHHsem.
        intro Hnb; apply Hnin.
        rewrite Hnb; constructor.
      - intro; simpl in Hfind; apply ident_eqb_neq in Hnf; rewrite Hnf in Hfind; eauto.
        econstructor; eauto.
        assert (Forall (fun eq => ~ is_block_in_eq (n_name n) eq) (SynSB.b_eqs bl)) as NotIns
            by (eapply is_block_in_Forall, find_block_later_not_is_block_in; eauto).
        clear Heqs WS.
        induction (SynSB.b_eqs bl); inv NotIns; inv IHeqs; constructor; auto.
    Qed.

    Lemma sem_block_cons2:
      forall n f xs M ys,
        Forall (fun n' => n_name n <> n_name n') G ->
        SemSB.sem_block P f xs M ys ->
        SemSB.sem_block (translate (n :: G)) f xs M ys.
    Proof.
      intros ** Hnin Hsem.
      induction Hsem
        as [| | | |????????? Hfind]
             using SemSB.sem_block_mult
        with (P_equation := fun bk H M eq =>
                              SemSB.sem_equation (translate (n :: G)) bk H M eq);
        eauto using SemSB.sem_equation.
      econstructor; eauto.
      simpl.
      assert (n.(n_name) <> b) as Hnf.
      { intro Hnf.
        rewrite Hnf in *.
        pose proof (SynSB.find_block_name _ _ _ _ Hfind) as Hb.
        apply find_block_translate in Hfind as (n' & Hfind' & ?).
        apply find_node_split in Hfind' as [G' [aG Hge]].
        rewrite Hge in Hnin.
        apply Forall_app in Hnin.
        destruct Hnin as [H' Hfg]; clear H'.
        inversion_clear Hfg.
        match goal with H:b<>_ |- False => apply H end.
        rewrite <-Hb; subst bl; auto.
      }
      apply ident_eqb_neq in Hnf; rewrite Hnf.
      eauto.
    Qed.

    Lemma sem_equation_cons:
      forall bk H M eqs n,
        Ordered_nodes (n :: G) ->
        ~Is_node_in n.(n_name) eqs ->
        Forall (SemSB.sem_equation P bk H M) (translate_eqns eqs) ->
        Forall (SemSB.sem_equation (translate (n :: G)) bk H M) (translate_eqns eqs).
    Proof.
      intros ** Hord Hnini Hsem.
      induction eqs as [|eq eqs IH]; [now constructor|].
      unfold translate_eqns in *; rewrite concatMap_cons in Hsem.
      apply Forall_app in Hsem as [Heq Heqs].
      apply not_Is_node_in_cons in Hnini.
      destruct Hnini as [Hnini Hninis].
      apply IH with (1:=Hninis) in Heqs.
      rewrite concatMap_cons.
      apply Forall_app; split; auto.
      inv Hord.
      induction eq; simpl in *.
      - constructor; auto.
        inversion_clear Heq as [|?? Hsem].
        inv Hsem; eauto using SemSB.sem_equation.
      - destruct o as [(r, ckr)|]; inversion_clear Heq as [|?? Hsem Heq'];
          constructor; inv Hsem; econstructor; eauto.
        + inversion_clear Heq' as [|?? Hsem'].
          inv Hsem'; econstructor; eauto.
          apply sem_block_cons2; auto.
        + apply sem_block_cons2; auto.
      - constructor; auto.
        inversion_clear Heq as [|?? Hsem].
        inv Hsem; eauto using SemSB.sem_equation.
    Qed.

  End Global.


  Fixpoint path_inst (p: list ident) (M: SemSB.memories) : option SemSB.memories :=
    match p with
    | [] => Some M
    | x :: p =>
      match find_inst x M with
      | Some M => path_inst p M
      | None => None
      end
    end.

  Lemma path_inst_last:
    forall p M M' x M'',
      path_inst p M = Some M' ->
      sub_inst x M' M'' ->
      path_inst (p ++ [x]) M = Some M''.
  Proof.
    induction p as [|y]; simpl; intros ** Path Sub.
    - inv Path; rewrite Sub; auto.
    - destruct (find_inst y M); inv Path; eauto.
  Qed.

  Section Choices.

    Variable Fm: nat -> SemSB.memories.
    Variable Fh: nat -> history.
    Variable Fmvs: nat -> SemSB.mvalues.
    Variable r: stream bool.

    Definition reset_content (x: ident) (p: list ident) : stream val :=
      fun n => match path_inst p (Fm (count r n)) with
            | Some M =>
              match find_val x M with
              | Some mv => mv.(SemSB.content) n
              | None => false_val
              end
            | None => false_val
            end.

    Definition reset_reset (x: ident) (p: list ident) : stream bool :=
      fun n => match path_inst p (Fm (count r n)) with
            | Some M =>
              match find_val x M with
              | Some mv => r n || mv.(SemSB.reset) n
              | None => r n
              end
            | None => r n
            end.

    Lemma reset_reset_spec:
      forall n x p,
        r n = true ->
        reset_reset x p n = true.
    Proof.
      unfold reset_reset; intros ** ->.
      destruct (path_inst p (Fm (count r n))); auto.
      destruct (find_val x m); auto.
    Qed.

    Definition reset_memories_path (p: list ident) (M0: SemSB.memories) : SemSB.memories :=
      mmapi (fun p x mv =>
               {| SemSB.content := reset_content x p;
                  SemSB.reset := reset_reset x p |})
            p M0.

    Definition reset_memories := reset_memories_path [].

    Lemma sub_inst_reset_memories_path:
      forall x p M M',
        sub_inst x M M' ->
        sub_inst x (reset_memories_path p M) (reset_memories_path (p ++ [x]) M').
    Proof.
      intros ** Find; unfold sub_inst, reset_memories_path.
      rewrite find_inst_mmapi, Find; auto.
    Qed.

    Lemma sub_inst_reset_memories_path':
      forall x p M M',
        sub_inst x (reset_memories_path p M) M' ->
        exists M'', M' = reset_memories_path (p ++ [x]) M''
               /\ sub_inst x M M''.
    Proof.
      unfold sub_inst, reset_memories_path; intros ** Find.
      rewrite find_inst_mmapi in Find.
      destruct (find_inst x M) eqn: E; inv Find; eauto.
    Qed.

    Lemma reset_memories_path_spec:
      forall k p r',
        (forall n,
            r' n = true ->
            r n = true) ->
        SemSB.reset_regs r' (reset_memories_path p (Fm k)).
    Proof.
      intros ** Spec; unfold reset_memories_path.
      revert p.
      induction (Fm k) as [?? IH] using memory_ind'.
      constructor.
      - intros x mvs.
        unfold find_val.
        simpl; rewrite Env.find_mapi.
        intro Find.
        destruct (Env.find x xvs); inv Find; auto.
        intros; simpl; apply reset_reset_spec; auto.
      - induction xms as [|[y]].
        + intros; discriminate.
        + simpl in IH; inv IH.
          intros x M'.
          unfold sub_inst, find_inst.
          simpl.
          destruct (Env.POTB.compare x y); simpl;
            intro Find; inv Find; eauto.
    Qed.

    Corollary reset_memories_path_sub_spec:
      forall k p r' x M,
        sub_inst x (Fm k) M ->
        (forall n, r' n = true -> r n = true) ->
        SemSB.reset_regs r' (reset_memories_path (p ++ [x]) M).
    Proof.
      intros ** Sub Spec; eapply reset_memories_path_spec with (k := k) in Spec.
      inversion_clear Spec as [??? Inst]; eapply Inst, sub_inst_reset_memories_path; eauto.
    Qed.

    Corollary reset_memories_spec:
      forall k r',
        (forall n, r' n = true -> r n = true) ->
        SemSB.reset_regs r (reset_memories (Fm k)).
    Proof.
      intros; now apply reset_memories_path_spec.
    Qed.

    Definition reset_history (H0: history) : history :=
      PM.mapi (fun x _ => fun n => match PM.find x (Fh (count r n)) with
                             | Some xs => xs n
                             | None => absent
                             end) H0.

    Definition reset_mvalues: SemSB.mvalues :=
    {| SemSB.content := fun n => (Fmvs (count r n)).(SemSB.content) n;
       SemSB.reset := fun n => r n || (Fmvs (count r n)).(SemSB.reset) n |}.

    Lemma reset_mvalues_spec:
      forall x e c0 ck xss,
        (forall n, 0 < length (xss n)) ->
        (forall k,
            exists bk xs ls,
              sem_var (Fh k) x xs
              /\ sem_laexp bk (Fh k) ck e ls
              /\ find_val x (Fm k) = Some (Fmvs k)
              /\ SemSB.content (Fmvs k) 0 = sem_const c0
              /\ (forall n : nat,
                    match ls n with
                    | absent =>
                      SemSB.content (Fmvs k) (S n) =
                      (if SemSB.reset (Fmvs k) (S n)
                       then sem_const c0
                       else SemSB.content (Fmvs k) n)
                      /\ xs n = absent
                    | present v' =>
                      SemSB.content (Fmvs k) (S n) =
                      (if SemSB.reset (Fmvs k) (S n)
                       then sem_const c0
                       else v')
                      /\ xs n = present (SemSB.content (Fmvs k) n)
                    end)
              /\ clock_of (mask (all_absent (xss 0)) k r xss) bk) ->
        forall n, r n = true ->
             SemSB.content reset_mvalues n = sem_const c0.
    Proof.
      intros ** Length Spec n E.
      unfold reset_mvalues; simpl.
      induction n; simpl; rewrite E.
      - destruct (Spec 1) as (?&?&?&?); intuition.
      - specialize (Spec (S (count r n))); destruct Spec as (bk &?&?&?& Hexp &?& Init & Heq & Clock).
        assert (forall n',
                   n' <= n ->
                   interp_laexp_instant (bk n') (restr_hist (Fh (S (count r n))) n') ck e = absent)
          as Absent.
        { assert (forall n',
                     n' <= n ->
                     bk n' = false) as Hbk.
          { clear - Clock Length.
            intros ** Lte.
            specialize (Clock n').
            rewrite mask_opaque in Clock; auto.
            - apply Bool.not_true_is_false; intro Ebk.
              apply Clock in Ebk.
              specialize (Length 0).
              clear - Ebk Length; induction (xss 0); simpl in *; inv Ebk; auto; omega.
            - apply Lt.le_lt_or_eq in Lte as [Lt|]; subst; auto.
              apply (count_le' r) in Lt; omega.
          }
          intros.
          specialize (Hexp n'); simpl in Hexp.
          pose proof Hexp as Hexp'; apply interp_laexp_instant_sound in Hexp'; rewrite Hexp' in Hexp.
          destruct (interp_laexp_instant (bk n') (restr_hist (Fh (S (count r n))) n') ck e); auto.
          inversion_clear Hexp as [???? HClock|].
          rewrite Hbk in HClock; auto; contradict HClock.
          apply not_subrate_clock.
        }
        assert (forall n', n' <= n -> SemSB.content (Fmvs (S (count r n))) n' = sem_const c0) as Spec.
        { intros ** Lte.
          induction n'; auto.
          specialize (Hexp n'); simpl in Hexp; apply interp_laexp_instant_sound in Hexp.
          specialize (Heq n').
          rewrite Hexp, Absent in Heq; try omega; destruct Heq as (->).
          destruct (SemSB.reset (Fmvs (S (count r n))) (S n')); auto.
          apply IHn'; omega.
        }
        specialize (Hexp n); simpl in Hexp; apply interp_laexp_instant_sound in Hexp.
        specialize (Heq n);
          rewrite Hexp, Absent in Heq; auto; destruct Heq as (->).
        destruct (SemSB.reset (Fmvs (S (count r n))) (S n)); auto.
    Qed.

    Lemma find_val_reset_memories:
      forall x,
        (forall k, find_val x (Fm k) = Some (Fmvs k)) ->
        find_val x (reset_memories (Fm 0)) = Some reset_mvalues.
    Proof.
      intros ** Spec.
      unfold reset_mvalues, reset_memories, reset_memories_path.
      rewrite find_val_mmapi.
      destruct (find_val x (Fm 0)) eqn: E; simpl.
      - do 3 f_equal.
        + unfold reset_content; simpl.
          extensionality n.
          rewrite Spec; auto.
        + unfold reset_reset.
          extensionality n.
          simpl; rewrite Spec; auto.
      - rewrite Spec in E; discriminate.
    Qed.

    Section InterpReset.

      Variable n: nat.

      Definition spec_var (x: ident) : Prop :=
        forall k, PM.find x (Fh k) <> None.

      Definition spec_vars := Forall spec_var.

      Inductive spec_clock: clock -> Prop :=
      | spec_clock_base:
          spec_clock Cbase
      | spec_clock_con:
          forall ck x b,
            spec_var x ->
            spec_clock ck ->
            spec_clock (Con ck x b).

      Inductive spec_lexp: lexp -> Prop :=
      | spec_lexp_const:
          forall c,
            spec_lexp (Econst c)
      | spec_lexp_var:
          forall x t,
            spec_var x ->
            spec_lexp (Evar x t)
      | spec_lexp_when:
          forall e x b,
            spec_var x ->
            spec_lexp e ->
            spec_lexp (Ewhen e x b)
      | spec_lexp_unop:
          forall op e t,
            spec_lexp e ->
            spec_lexp (Eunop op e t)
      | spec_lexp_binop:
          forall op e1 e2 t,
            spec_lexp e1 ->
            spec_lexp e2 ->
            spec_lexp (Ebinop op e1 e2 t).

      Definition spec_lexps := Forall spec_lexp.

      Inductive spec_cexp: cexp -> Prop :=
      | spec_cexp_merge:
          forall x e1 e2,
            spec_var x ->
            spec_cexp e1 ->
            spec_cexp e2 ->
            spec_cexp (Emerge x e1 e2)
      | spec_cexp_ite:
          forall le e1 e2,
            spec_lexp le ->
            spec_cexp e1 ->
            spec_cexp e2 ->
            spec_cexp (Eite le e1 e2)
      | spec_cexp_exp:
          forall e,
            spec_lexp e ->
            spec_cexp (Eexp e).

      Inductive spec_eq: SynSB.equation -> Prop :=
      | spec_eq_def:
          forall x ck e,
            spec_var x ->
            spec_clock ck ->
            spec_cexp e ->
            spec_eq (SynSB.EqDef x ck e)
      | spec_eq_fby:
          forall x ck c0 e,
            spec_var x ->
            spec_clock ck ->
            spec_lexp e ->
            spec_eq (SynSB.EqFby x ck c0 e)
      | spec_eq_reset:
          forall ck b i r,
            spec_var r ->
            spec_eq (SynSB.EqReset ck b i r)
      | spec_eq_call:
          forall xs ck b i es,
            spec_vars xs ->
            spec_clock ck ->
            spec_lexps es ->
            spec_eq (SynSB.EqCall xs ck b i es).

      Lemma sem_var_instant_reset:
        forall x v,
          spec_var x ->
          sem_var_instant (restr_hist (Fh (count r n)) n) x v ->
          sem_var_instant (restr_hist (reset_history (Fh 0)) n) x v.
      Proof.
        intros ** Spec Sem.
        induction Sem; constructor.
        unfold reset_history, restr_hist, PM.map in *.
        repeat rewrite PM.gmapi in *; rewrite option_map_map.
        destruct (PM.find x (Fh (count r n))) eqn: E.
        - destruct (PM.find x (Fh 0)) eqn: E'; auto.
          exfalso; eapply Spec; eauto.
        - exfalso; eapply Spec; eauto.
      Qed.
      Hint Resolve sem_var_instant_reset.

      Lemma sem_vars_instant_reset:
        forall xs vs,
          spec_vars xs ->
          sem_vars_instant (restr_hist (Fh (count r n)) n) xs vs ->
          sem_vars_instant (restr_hist (reset_history (Fh 0)) n) xs vs.
      Proof.
        intros ** Spec Sem.
        induction Sem; inv Spec; constructor; auto.
        apply IHSem; auto.
      Qed.

      Variable bk: stream bool.
      Variable xss: stream (list value).
      Hypothesis Clk: clock_of (mask (all_absent (xss 0)) (count r n) r xss) bk.
      Let bk' := clock_of' xss.

      Lemma sem_clock_instant_reset:
        forall ck b,
          spec_clock ck ->
          sem_clock_instant (bk n) (restr_hist (Fh (count r n)) n) ck b ->
          sem_clock_instant (bk' n) (restr_hist (reset_history (Fh 0)) n) ck b.
      Proof.
        intros ** Spec Sem; induction Sem; inv Spec; eauto using sem_clock_instant.
        apply clock_of_equiv' in Clk; rewrite Clk.
        subst bk'.
        unfold clock_of'.
        rewrite mask_transparent; constructor.
      Qed.
      Hint Resolve sem_clock_instant_reset.

      Lemma sem_lexp_instant_reset:
        forall e v,
          spec_lexp e ->
          sem_lexp_instant (bk n) (restr_hist (Fh (count r n)) n) e v ->
          sem_lexp_instant (bk' n) (restr_hist (reset_history (Fh 0)) n) e v.
      Proof.
        intros ** Spec Sem; induction Sem; inv Spec; eauto using sem_lexp_instant.
        constructor; subst.
        apply clock_of_equiv' in Clk; rewrite Clk.
        unfold clock_of'.
        rewrite mask_transparent; auto.
      Qed.
      Hint Resolve sem_lexp_instant_reset.

      Lemma sem_lexps_instant_reset:
        forall es vs,
          spec_lexps es ->
          sem_lexps_instant (bk n) (restr_hist (Fh (count r n)) n) es vs ->
          sem_lexps_instant (bk' n) (restr_hist (reset_history (Fh 0)) n) es vs.
      Proof.
        unfold sem_lexps_instant; intros ** Spec Sem;
          induction Sem; inv Spec; constructor; eauto.
      Qed.
      Hint Resolve sem_lexps_instant_reset.

      Lemma sem_laexp_instant_reset:
        forall ck e v,
          spec_clock ck ->
          spec_lexp e ->
          sem_laexp_instant (bk n) (restr_hist (Fh (count r n)) n) ck e v ->
          sem_laexp_instant (bk' n) (restr_hist (reset_history (Fh 0)) n) ck e v.
      Proof.
        induction 3; constructor; auto.
      Qed.

      Lemma sem_laexps_instant_reset:
        forall ck es vs,
          spec_clock ck ->
          spec_lexps es ->
          sem_laexps_instant (bk n) (restr_hist (Fh (count r n)) n) ck es vs ->
          sem_laexps_instant (bk' n) (restr_hist (reset_history (Fh 0)) n) ck es vs.
      Proof.
        induction 3.
        - eapply SLticks; eauto.
        - apply SLabss; auto.
      Qed.

      Lemma sem_cexp_instant_reset:
        forall e v,
          spec_cexp e ->
          sem_cexp_instant (bk n) (restr_hist (Fh (count r n)) n) e v ->
          sem_cexp_instant (bk' n) (restr_hist (reset_history (Fh 0)) n) e v.
      Proof.
        intros ** Spec Sem; induction Sem; inv Spec; eauto using sem_cexp_instant.
      Qed.
      Hint Resolve sem_cexp_instant_reset.

      Lemma sem_caexp_instant_reset:
        forall ck e v,
          spec_clock ck ->
          spec_cexp e ->
          sem_caexp_instant (bk n) (restr_hist (Fh (count r n)) n) ck e v ->
          sem_caexp_instant (bk' n) (restr_hist (reset_history (Fh 0)) n) ck e v.
      Proof.
        induction 3; constructor; auto.
      Qed.

    End InterpReset.

    Lemma sem_spec_var_instant:
      forall x,
        (forall k n, exists v, sem_var_instant (restr_hist (Fh k) n) x v) ->
        spec_var x.
    Proof.
      intros ** Sem k E; destruct (Sem k 0) as (?& Sem');
        inversion_clear Sem' as [?? Find].
      unfold restr_hist, PM.map in Find.
      rewrite PM.gmapi, E in Find.
      discriminate.
    Qed.

    Corollary sem_spec_var:
      forall x,
        (forall k, exists xs, sem_var (Fh k) x xs) ->
        spec_var x.
    Proof.
      intros x Sem; apply sem_spec_var_instant.
      intros; destruct (Sem k) as (?& Sem');
        specialize (Sem' n); eauto.
    Qed.

    Lemma sem_spec_vars_instant:
      forall xs,
        (forall k n, exists xss, sem_vars_instant (restr_hist (Fh k) n) xs xss) ->
        spec_vars xs.
    Proof.
      intros ** Sem; induction xs; constructor.
      - apply sem_spec_var_instant; intros; destruct (Sem k n) as (?& Sem'); inv Sem'; eauto.
      - apply IHxs; intros; destruct (Sem k n) as (?& Sem'); inv Sem'; eauto.
    Qed.

    Corollary sem_spec_vars:
      forall xs,
        (forall k, exists xss, sem_vars (Fh k) xs xss) ->
        spec_vars xs.
    Proof.
      intros ** Sem; apply sem_spec_vars_instant.
      intros; destruct (Sem k) as (?& Sem'); specialize (Sem' n); eauto.
    Qed.

    Lemma sem_spec_clock_instant:
      forall ck,
        (forall k n, exists base b, sem_clock_instant base (restr_hist (Fh k) n) ck b) ->
        spec_clock ck.
    Proof.
      intros ** Sem; induction ck; constructor.
      - apply sem_spec_var_instant; intros.
        destruct (Sem k n) as (?&?& Clock); inv Clock; eauto.
      - apply IHck.
        intros; destruct (Sem k n) as (?&?& Clock); inv Clock; eauto.
    Qed.

    Corollary sem_spec_clock_caexp:
      forall ck e,
        (forall k, exists bk vs, sem_caexp bk (Fh k) ck e vs) ->
        spec_clock ck.
    Proof.
      intros ** Sem; apply sem_spec_clock_instant.
      intros; destruct (Sem k) as (?&?& Sem'); specialize (Sem' n); simpl in Sem'.
      inv Sem'; eauto.
    Qed.

    Corollary sem_spec_clock_laexp:
      forall ck e,
        (forall k, exists bk vs, sem_laexp bk (Fh k) ck e vs) ->
        spec_clock ck.
    Proof.
      intros ** Sem; apply sem_spec_clock_instant.
      intros; destruct (Sem k) as (?&?& Sem'); specialize (Sem' n); simpl in Sem'.
      inv Sem'; eauto.
    Qed.

    Lemma sem_spec_clock_laexps:
      forall ck es,
        (forall k, exists bk vss, sem_laexps bk (Fh k) ck es vss) ->
        spec_clock ck.
    Proof.
      intros ** Sem; apply sem_spec_clock_instant.
      intros; destruct (Sem k) as (?&?& Sem'); specialize (Sem' n); simpl in Sem'.
      inv Sem'; eauto.
    Qed.

    Lemma sem_spec_lexp_instant:
      forall e,
        (forall k n, exists base v, sem_lexp_instant base (restr_hist (Fh k) n) e v) ->
        spec_lexp e.
    Proof.
      intros ** Sem; induction e; auto using spec_lexp.
      - constructor; apply sem_spec_var_instant;
          intros; destruct (Sem k n) as (?&?& Sem'); inv Sem'; eauto.
      - constructor.
        + apply sem_spec_var_instant; intros; destruct (Sem k n) as (?&?& Sem'); inv Sem'; eauto.
        + apply IHe; intros; destruct (Sem k n) as (?&?& Sem'); inv Sem'; eauto.
      - constructor; apply IHe; intros; destruct (Sem k n) as (?&?& Sem'); inv Sem'; eauto.
      - constructor.
        + apply IHe1; intros; destruct (Sem k n) as (?&?& Sem'); inv Sem'; eauto.
        + apply IHe2; intros; destruct (Sem k n) as (?&?& Sem'); inv Sem'; eauto.
    Qed.

    Corollary sem_spec_laexp:
      forall e ck,
        (forall k, exists bk vs, sem_laexp bk (Fh k) ck e vs) ->
        spec_lexp e.
    Proof.
      intros ** Sem.
      apply sem_spec_lexp_instant; intros.
      destruct (Sem k) as (?&?& Sem'); specialize (Sem' n); inv Sem'; eauto.
    Qed.

    Lemma sem_spec_cexp_instant:
      forall e,
        (forall k n, exists base v, sem_cexp_instant base (restr_hist (Fh k) n) e v) ->
        spec_cexp e.
    Proof.
      intros ** Sem; induction e.
      - constructor.
        + apply sem_spec_var_instant; intros; destruct (Sem k n) as (?&?& Sem'); inv Sem'; eauto.
        + apply IHe1; intros; destruct (Sem k n) as (?&?& Sem'); inv Sem'; eauto.
        + apply IHe2; intros; destruct (Sem k n) as (?&?& Sem'); inv Sem'; eauto.
      - constructor.
        + apply sem_spec_lexp_instant; intros; destruct (Sem k n) as (?&?& Sem'); inv Sem'; eauto.
        + apply IHe1; intros; destruct (Sem k n) as (?&?& Sem'); inv Sem'; eauto.
        + apply IHe2; intros; destruct (Sem k n) as (?&?& Sem'); inv Sem'; eauto.
      - constructor; apply sem_spec_lexp_instant; intros; destruct (Sem k n) as (?&?& Sem'); inv Sem'; eauto.
    Qed.

    Corollary sem_spec_caexp:
      forall e ck,
        (forall k, exists bk vs, sem_caexp bk (Fh k) ck e vs) ->
        spec_cexp e.
    Proof.
      intros ** Sem.
      apply sem_spec_cexp_instant; intros.
      destruct (Sem k) as (?&?& Sem'); specialize (Sem' n); inv Sem'; eauto.
    Qed.

    Lemma sem_spec_lexps_instant:
      forall es,
        (forall k n, exists base vs, sem_lexps_instant base (restr_hist (Fh k) n) es vs) ->
        spec_lexps es.
    Proof.
      intros ** Sem; induction es; constructor.
      - apply sem_spec_lexp_instant; intros; destruct (Sem k n) as (?&?& Sem'); inv Sem'; eauto.
      - apply IHes; intros; destruct (Sem k n) as (?&?& Sem'); inv Sem'; eauto.
    Qed.

    Corollary sem_spec_laexps:
      forall es ck,
        (forall k, exists bk vss, sem_laexps bk (Fh k) ck es vss) ->
        spec_lexps es.
    Proof.
      intros ** Sem.
      apply sem_spec_lexps_instant; intros; destruct (Sem k) as (?&?& Sem'); specialize (Sem' n); inv Sem'; eauto.
    Qed.

    Ltac sem_spec H :=
      let k := fresh in
      let H' := fresh in
      match goal with
      | |- spec_var _ => apply sem_spec_var
      | |- spec_vars _ => apply sem_spec_vars
      | _: cexp |- spec_clock _ => eapply sem_spec_clock_caexp
      | _: lexp |- spec_clock _ => eapply sem_spec_clock_laexp
      | _: list lexp |- spec_clock _ => eapply sem_spec_clock_laexps
      | |- spec_cexp _ => eapply sem_spec_caexp
      | |- spec_lexp _ => eapply sem_spec_laexp
      | |- spec_lexps _ => eapply sem_spec_laexps
      end;
      try (intro k; destruct (H k) as (?&?& H'); inv H'; eauto).

    Lemma sem_spec_eq:
      forall P eq,
        (forall k, exists bk M, SemSB.sem_equation P bk (Fh k) M eq) ->
        spec_eq eq.
    Proof.
      intros ** Sem; destruct eq;  constructor (sem_spec Sem).
    Qed.

  End Choices.
  Hint Resolve reset_memories_spec sub_inst_reset_memories_path.

  Inductive reset_regs_instant (n: nat): bool -> SemSB.memories -> Prop :=
    reset_regs_instant_intro:
      forall M b,
        (forall x mvs,
            find_val x M = Some mvs ->
            b = true -> mvs.(SemSB.reset) n = true) ->
        (forall x M',
            sub_inst x M M' ->
            reset_regs_instant n b M') ->
        reset_regs_instant n b M.

  Lemma sub_inst_reset_regs_instant:
    forall bs M x M',
      (forall n, reset_regs_instant n (bs n) M) ->
      sub_inst x M M' ->
      forall n, reset_regs_instant n (bs n) M'.
  Proof.
    intros ** Rst Sub n.
    revert dependent M'; revert x.
    specialize (Rst n); induction Rst as [??? Inst IH].
    constructor.
    - intros; apply Inst in Sub.
      inv Sub; eauto.
    - intros; eapply IH; eauto.
  Qed.

  Lemma reset_regs_instant_spec:
    forall bs M,
      SemSB.reset_regs bs M <->
      forall n, reset_regs_instant n (bs n) M.
  Proof.
    split.
    - induction 1 as [?? Val ? IH]; intro; constructor.
      + intros; eapply Val; eauto.
      + intros; eapply IH; eauto.
    - induction M as [?? IH] using memory_ind'; intros Rst; constructor.
      + intros; specialize (Rst n); inv Rst; eauto.
      + intros ** Sub; pose proof Sub as Sub'.
        unfold sub_inst, find_inst in Sub.
        eapply Env.find_in, in_map with (f := snd) in Sub; simpl in Sub.
        eapply In_Forall in IH; eauto.
        apply IH.
        eapply sub_inst_reset_regs_instant; eauto.
  Qed.

  Corollary reset_regs_instant_spec':
    forall bs M n,
      SemSB.reset_regs bs M ->
      reset_regs_instant n (bs n) M.
  Proof.
    intros ** Rst.
    rewrite reset_regs_instant_spec in Rst; auto.
  Qed.

  Inductive same_skeleton: SemSB.memories -> SemSB.memories -> Prop :=
    same_skeleton_intro:
      forall M M',
        (forall x, find_val x M <> None -> find_val x M' <> None) ->
        (forall x M1,
            find_inst x M = Some M1 ->
            exists M2, find_inst x M' = Some M2
                  /\ same_skeleton M1 M2) ->
        same_skeleton M M'.

  Lemma same_skeleton_sub_inst:
    forall M M' x Mx Mx',
      same_skeleton M M' ->
      sub_inst x M Mx ->
      sub_inst x M' Mx' ->
      same_skeleton Mx Mx'.
  Proof.
    inversion_clear 1 as [??? Inst]; intros ** Sub Sub'.
    apply Inst in Sub as (? & Sub'' & ?).
    rewrite Sub' in Sub''; inv Sub''; auto.
  Qed.

  Lemma reset_memories_path_spec_instant':
    forall r Fm p r' M0 n M',
      same_skeleton M0 M' ->
      path_inst p (Fm (count r n)) = Some M' ->
      reset_regs_instant n r' M' ->
      reset_regs_instant n r' (reset_memories_path Fm r p M0).
  Proof.
    intros ** Same Sub RstSpec.
    inversion_clear Same as [?? FindVal FindInst].

    revert dependent p.
    revert dependent M'.
    induction M0 as [?? IH] using memory_ind'; intros.
    inversion_clear RstSpec as [?? Val Inst].
    constructor.
    - unfold reset_memories_path; intros y mvs Find' Rst; subst.
      rewrite find_val_mmapi in Find'.
      destruct (find_val y (Mnode xvs xms)) eqn: E; inv Find'.
      unfold reset_reset; simpl.
      rewrite Sub.
      destruct (find_val y M') eqn: E'.
      + erewrite Val; eauto 1.
        apply Bool.orb_true_r.
      + contradict E'; eapply FindVal; eauto;
          rewrite E; intro; discriminate.
    - intros ** Find.
      apply sub_inst_reset_memories_path' in Find as (M0' &?& Find); subst.
      unfold sub_inst in Find.
      pose proof Find as Find'.
      unfold sub_inst, find_inst in Find.
      apply Env.find_in, in_map with (f := snd) in Find; simpl in Find.
      eapply In_Forall in IH; eauto.
      assert (exists M'', find_inst x M' = Some M''
                     /\ same_skeleton M0' M'') as (M'' &?& Same)
          by (apply FindInst in Find' as (?&?&?); eauto).
      inv Same.
      eapply IH; eauto.
      eapply path_inst_last; eauto.
  Qed.

  Corollary reset_memories_path_sub_spec_instant':
    forall r Fm x r' M0 n M',
      same_skeleton M0 M' ->
      sub_inst x (Fm (count r n)) M' ->
      reset_regs_instant n r' M' ->
      reset_regs_instant n r' (reset_memories_path Fm r [x] M0).
  Proof.
    intros ** Same Sub RstSpec.
    eapply reset_memories_path_spec_instant'; eauto.
    simpl; rewrite Sub; auto.
  Qed.

  Lemma sem_var_instant_bl_vars:
    forall xs xs' xss Fh r n,
      (forall x k n,
          In x xs' ->
          exists v, PM.find x (restr_hist (Fh k) n) = Some v) ->
      incl xs xs' ->
      sem_vars (Fh (count r n)) xs (mask (all_absent (xss 0)) (count r n) r xss) ->
      Forall2 (sem_var_instant (restr_hist (reset_history Fh r (Fh 0)) n)) xs (xss n).
  Proof.
    intros ** SameDomFh Incl Sem.
    unfold mask in Sem; specialize (Sem n); simpl in *.
    rewrite <-EqNat.beq_nat_refl in Sem.
    induction Sem as [|x ??? Sem]; constructor; auto.
    - clear IHSem.
      inversion_clear Sem as [?? Find]; constructor.
      assert (exists v, PM.find x (restr_hist (Fh 0) n) = Some v)
        as (? & Find') by (apply SameDomFh, Incl; constructor; auto).
      unfold restr_hist, reset_history, PM.map in *.
      repeat rewrite PM.gmapi in *; rewrite option_map_map.
      destruct (PM.find x (Fh (count r n))); try discriminate.
      destruct (PM.find x (Fh 0)); try discriminate; auto.
    - apply IHSem; intros x' **.
      apply Incl; right; auto.
  Qed.

  Lemma sem_laexps_interp_mask:
    forall xss r Fh ck es k bk' ess,
      let H := reset_history Fh r (Fh 0) in
      let bk := clock_of' xss in
      spec_clock Fh ck ->
      spec_lexps Fh es ->
      (forall n, 0 < length (xss n)) ->
      clock_of (mask (all_absent (xss 0)) k r xss) bk' ->
      sem_laexps bk' (Fh k) ck es ess ->
      ess ≈ mask (all_absent (interp_laexps bk H ck es 0)) k r (interp_laexps bk H ck es).
  Proof.
    intros ** Length Clock Exps n.
    specialize (Exps n); simpl in Exps.
    destruct (EqNat.beq_nat k (count r n)) eqn: E.
    - apply EqNat.beq_nat_true in E; subst k.
      rewrite mask_transparent; auto.
      eapply interp_laexps_instant_sound, sem_laexps_instant_reset; eauto.
    - apply EqNat.beq_nat_false in E.
      specialize (Clock n).
      rewrite mask_opaque; rewrite mask_opaque in Clock; auto.
      inversion_clear Exps as [?????? SemCk|??? Eq].
      + assert (bk' n = false) as Hbk'.
        { apply Bool.not_true_is_false; intro Eq.
          apply Clock in Eq.
          specialize (Length 0); induction (xss 0); simpl in *; inv Eq; auto; omega.
        }
        rewrite Hbk' in *.
        contradict SemCk; apply not_subrate_clock.
      + rewrite Eq.
        unfold interp_laexps, lift, interp_laexps_instant.
        destruct (forallb (fun v : value => v ==b absent) (interp_lexps_instant (bk 0) (restr_hist H 0) es)
                          && negb (interp_clock_instant (bk 0) (restr_hist H 0) ck)
                  || forallb (fun v : value => v <>b absent) (interp_lexps_instant (bk 0) (restr_hist H 0) es)
                            && interp_clock_instant (bk 0) (restr_hist H 0) ck);
          unfold interp_lexps_instant; rewrite all_absent_map; auto.
        unfold all_absent at 3; rewrite all_absent_map; auto.
  Qed.

  Lemma sem_vars_interp_mask:
    forall r Fh xs k ess oss oss0,
      let H := reset_history Fh r (Fh 0) in
      sem_vars (Fh k) xs oss ->
      sem_vars (Fh 0) xs oss0 ->
      (forall n, absent_list (ess n) <-> absent_list (oss n)) ->
      (forall n, k <> count r n -> absent_list (oss n)) ->
      oss ≈ mask (all_absent (interp_vars H xs 0)) k r (interp_vars H xs).
  Proof.
    intros ** Vars Vars0 Same Abs n.
    specialize (Vars n); specialize (Vars0 n);
      specialize (Same n); (* specialize (Eess n) *) simpl in *.
    unfold mask in *.
    destruct (EqNat.beq_nat k (count r n)) eqn: E; simpl.
    - clear Same.
      revert Vars0; generalize (oss0 n).
      induction Vars as [|???? Var]; intros; inversion_clear Vars0 as [|???? Var0]; simpl; auto.
      f_equal; eauto.
      inversion_clear Var0 as [?? Find0]; inversion_clear Var as [?? Find].
      unfold interp_var_instant.
      subst H; unfold reset_history; unfold restr_hist, PM.map in *.
      rewrite 2 PM.gmapi; simpl.
      rewrite PM.gmapi in Find0.
      destruct (PM.find x (Fh 0)); inv Find0; simpl.
      rewrite PM.gmapi in Find.
      apply EqNat.beq_nat_true in E; subst k.
      destruct (PM.find x (Fh (count r n))); inv Find; auto.
    - specialize (Abs n).
      assert (absent_list (oss n)) as Abs'
          by (apply Abs, EqNat.beq_nat_false; auto).
      apply interp_vars_instant_sound in Vars as ->.
      clear - Abs'; induction xs; simpl; auto.
      inv Abs'; f_equal; auto.
  Qed.

  Lemma sub_inst_reset_memories:
    forall F F' r x,
      (forall k, sub_inst x (F k) (F' k)) ->
      sub_inst x (reset_memories F r (F 0)) (reset_memories F' r (F' 0)).
  Proof.
    intros ** Sub.
    pose proof (Sub 0) as Sub0.
    eapply (sub_inst_reset_memories_path F r _ []) in Sub0.
    unfold sub_inst, reset_memories.
    rewrite Sub0; f_equal; simpl.
    clear Sub0.
    generalize (@nil ident).
    induction (F' 0) as [?? IH] using memory_ind'; intros.
    unfold reset_memories_path.
    simpl. f_equal.
    - f_equal.
      extensionality y; extensionality mvs.
      f_equal.
      + extensionality n; unfold reset_content; simpl.
        now rewrite Sub.
      + extensionality n; unfold reset_reset; simpl.
        now rewrite Sub.
    - induction xms as [|(i & M')]; simpl; auto.
      inversion_clear IH as [|?? Eq]; f_equal; auto.
      f_equal.
      unfold reset_memories_path in Eq; auto.
  Qed.

  (* Lemma foo: *)
  (*   forall eqs M M', *)
  (*     SemSB.well_structured_memories eqs M -> *)
  (*     SemSB.well_structured_memories eqs M' -> *)
  (*     (* SemSB.sem_equation P bk H M e -> *) *)
  (*     (* SemSB.sem_equation P bk H M' e -> *) *)
  (*     same_skeleton M M'. *)
  (* Proof. *)
  (*   intros ** WS WS'. *)
  (*   revert dependent M'. *)
  (*   induction M using memory_ind'; intros. *)
  (*   constructor. *)
  (*   - intros x Find. *)
  (*     now apply WS, WS' in Find. *)
  (*   - intros ** Find'. *)
  (*     assert (find_inst x (Mnode xvs xms) <> None) as Find by (rewrite not_None_is_Some; eauto). *)
  (*     apply WS, WS' in Find. *)
  (*     apply not_None_is_Some in Find as (). *)
  (*     eexists; split; eauto. *)
  (*     unfold find_inst in Find'; *)
  (*       apply Env.find_in, in_map with (f := snd) in Find'; simpl in Find'. *)
  (*     eapply In_Forall in H; eauto. *)
  (*     apply H. *)
  (*     SearchAbout Forall In. *)
  (*     eauto. *)
  Definition gather_eq (acc: Env.t ident) (eq: SynSB.equation): Env.t ident :=
    match eq with
    | SynSB.EqDef _ _ _
    | SynSB.EqReset _ _ _ _
    | SynSB.EqFby _ _ _ _ => acc
    | SynSB.EqCall _ _ f i _ => Env.add i f acc
    end.

  Definition gather (eqs: list SynSB.equation) : Env.t ident :=
    fold_left gather_eq eqs [].

  Lemma fold_left_gather_eq_find:
    forall eqs e e' x,
      Env.find x e = Env.find x e' ->
      Env.find x (fold_left gather_eq eqs e) = Env.find x (fold_left gather_eq eqs e').
  Proof.
    Arguments Env.add: simpl never.
    unfold gather; induction eqs as [|eq]; simpl; auto; intros ** E.
    destruct eq; simpl; auto.
    apply IHeqs.
    destruct (ident_eqb x i1) eqn: Eq;
      [apply ident_eqb_eq in Eq; subst|apply ident_eqb_neq in Eq].
    - rewrite 2 Env.gss; auto.
    - rewrite 2 Env.gso; auto.
  Qed.

  Lemma gather_find:
    forall eqs e x,
      Env.find x e = None ->
      Env.find x (fold_left gather_eq eqs e) = Env.find x (gather eqs).
  Proof.
    intros ** E; apply fold_left_gather_eq_find.
    rewrite E; reflexivity.
  Qed.

  (* Lemma gather_find': *)
  (*   forall eqs e e' x, *)
  (*     (forall x, Env.find x (gather eqs) <> None -> Env.find x e' = None) -> *)
  (*     Env.find x (fold_left gather_eq eqs e') = Env.find x e' -> *)
  (*     Env.find x (fold_left gather_eq eqs e) = Env.find x e. *)
  (* Proof. *)
  (*   Arguments Env.add: simpl never. *)
  (*   unfold gather; induction eqs as [|eq]; simpl; intros ** Spec E; auto. *)
  (*   destruct eq; simpl in *; eauto. *)
  (*   erewrite IHeqs. *)
  (*   - erewrite IHeqs in E. *)
  (*     + destruct (ident_eqb x i1) eqn: Eq; *)
  (*         [apply ident_eqb_eq in Eq; subst|apply ident_eqb_neq in Eq]. *)
  (*       * assert (Env.find i1 (fold_left gather_eq eqs (Env.add i1 i0 [])) <> None). *)
  (*         { clear; induction eqs as [|eq]; simpl fold_left. *)
  (*           - rewrite Env.gss; intro; discriminate. *)
  (*           - destruct eq; simpl; auto. admit. *)
  (*         } *)
  (*         apply Spec in H. *)
  (*         rewrite Env.gss, H in E; discriminate. *)
  (*       * apply Env.gso; auto. *)
  (*     + instantiate (1 := e'). admit. *)
  (*     +  *)

  (*   - erewrite IHeqs with (e' := Env.add i1 i0 e') in E. *)
  (*     + admit. *)
  (*     + rewrite Env.gss. erewrite IHeqs. admit.   *)
  (*   - erewrite IHeqs with (e' := Env.add i1 i0 e'). *)
  (*     + apply Env.gso; auto. *)
  (*     + rewrite Env.gso; auto.  erewrite E. rewrite 2 Env.gso; auto.  *)
  (*   - apply IHeqs.  *)
  (*   eapply gather_find in E. *)
  (*   intros ** E. *)
  (*   destruct (Env.find x e). *)
  (*   - *)
  Lemma gather_find':
    forall eqs e x,
      Env.find x (gather eqs) = None ->
      Env.find x (fold_left gather_eq eqs e) = Env.find x e.
  Proof.
    unfold gather; induction eqs as [|eq]; simpl; intros ** E; auto.
    destruct eq; simpl in *; auto.
  Admitted.

  Lemma sub_inst_translate_sem_block:
    forall G f bl P' M xss oss x M',
      SemSB.sem_block (translate G) f M xss oss ->
      SynSB.find_block f (translate G) = Some (bl, P') ->
      sub_inst x M M' ->
      exists g xss' oss',
        SemSB.sem_block (translate G) g M' xss' oss'
        /\ Env.find x (gather bl.(SynSB.b_eqs)) = Some g.
  Proof.
    Arguments Env.add: simpl never.
    inversion_clear 1 as [????????? Find ????? Eqs WS]; intros ** Find' Sub.
    rewrite Find in Find'; inv Find'.
    apply find_block_translate in Find as (n & Find &?); subst; simpl in *.
    assert (find_inst x M <> None) as E by (rewrite not_None_is_Some; eauto).
    apply WS in E.
    unfold SemSB.insts in E.
    unfold translate_eqns, concatMap in *.
    clear WS.
    induction (n_eqs n) as [|eq].
    - contradict E; apply not_In_empty.
    - destruct eq; try destruct o as [()|]; unfold gather; simpl in *;
        inversion_clear Eqs as [|?? Heq Heqs]; auto.
      + set (y := hd default i) in *.
        inversion_clear Heqs as [|?? Heq'].
        inversion_clear Heq' as [| | |???????????? Sub'].
        destruct (ident_eqb x y) eqn: Eq;
          [apply ident_eqb_eq in Eq; subst|apply ident_eqb_neq in Eq].
        *{ unfold sub_inst in Sub'; rewrite Sub in Sub'; inv Sub'.
           do 3 eexists; split; eauto.
           rewrite gather_find'.
           - apply Env.gss.
           - admit.
         }
        *{ rewrite gather_find.
           - apply IHl; auto.
             apply SemSB.In_fold_left_inst_eq in E as [|E]; auto.
             rewrite 2 PSE.MP.Dec.F.add_neq_iff in E; auto.
             contradict E; apply not_In_empty.
           - rewrite Env.gso; auto.
         }
      + set (y := hd default i) in *.
        inversion_clear Heq as [| | |???????????? Sub'].
        destruct (ident_eqb x y) eqn: Eq;
          [apply ident_eqb_eq in Eq; subst|apply ident_eqb_neq in Eq].
        *{ unfold sub_inst in Sub'; rewrite Sub in Sub'; inv Sub'.
           do 3 eexists; split; eauto.
           rewrite gather_find'.
           - apply Env.gss.
           - admit.
         }
        *{ rewrite gather_find.
           - apply IHl; auto.
             apply SemSB.In_fold_left_inst_eq in E as [|E]; auto.
             rewrite PSE.MP.Dec.F.add_neq_iff in E; auto.
             contradict E; apply not_In_empty.
           - rewrite Env.gso; auto.
         }
  Qed.

  Lemma sem_block_same_skeleton:
    forall G M M' f xss oss xss' oss',
      (* Ordered_nodes G -> *)
      SemSB.sem_block (translate G) f M xss oss ->
      SemSB.sem_block (translate G) f M' xss' oss' ->
      same_skeleton M M'.
  Proof.
    induction M as [?? IH] using memory_ind'.
    intros ** Sem Sem'; pose proof Sem as Sem1; pose proof Sem' as Sem2;
      inversion_clear Sem as [????????? Find ????? Eqs WS];
      inversion_clear Sem' as [????????? Find' ????? Eqs' WS'].
    rewrite Find' in Find; inv Find.
    constructor.
    - intros x E.
      apply WS'.
      apply WS in E; auto.
    - intros ** E.
      pose proof E as E1.
      assert (find_inst x (Mnode xvs xms) <> None) as E' by (rewrite not_None_is_Some; eauto).
      apply WS, WS' in E'.
      apply not_None_is_Some in E' as ().
      eexists; split; eauto.
      unfold find_inst in E.
      apply Env.find_in, in_map with (f := snd) in E; simpl in E.
      eapply In_Forall in IH; eauto.
      eapply sub_inst_translate_sem_block in Sem1 as (?&?&?&?& Find1); eauto.
      eapply sub_inst_translate_sem_block in Sem2 as (?&?&?&?& Find2); eauto.
      rewrite Find1 in Find2; inv Find2.
      eauto.
  Qed.

  Lemma well_structured_reset_memories:
    forall Fm r M0 eqs,
    SemSB.well_structured_memories eqs M0 ->
    SemSB.well_structured_memories eqs (reset_memories Fm r M0).
  Proof.
    inversion_clear 1 as [Vals Insts].
    constructor; intro; unfold reset_memories, reset_memories_path.
    - rewrite find_val_mmapi, <-Vals.
      destruct (find_val x M0); simpl; split; auto; intros ** ?; discriminate.
    - rewrite find_inst_mmapi, <-Insts.
      destruct (find_inst x M0); simpl; split; auto; intros ** ?; discriminate.
  Qed.

  Ltac interp_sound n :=
    repeat match goal with
           | H: sem_var ?H' ?x ?vs |- _ =>
             specialize (H n); apply sem_var_instant_reset in H
           | H: sem_vars ?H' ?xs ?vss |- _ =>
             specialize (H n); apply sem_vars_instant_reset in H
           | H: sem_caexp ?bk ?H' ?c ?e ?vs |- _ =>
             specialize (H n); simpl in H; eapply sem_caexp_instant_reset in H; eauto
           | H: sem_laexp ?bk ?H' ?c ?e ?vs |- _ =>
             specialize (H n); simpl in H; eapply sem_laexp_instant_reset in H; eauto
           | H: sem_laexps ?bk ?H' ?c ?es ?vss |- _ =>
             specialize (H n); simpl in H; eapply sem_laexps_instant_reset in H; eauto
           end;
    unfold interp_var, interp_vars, interp_laexp, interp_laexps, interp_caexp, lift, lift';
    try erewrite <-interp_caexp_instant_sound;
    try erewrite <-interp_laexp_instant_sound;
    try erewrite <-interp_laexps_instant_sound;
    try erewrite <-interp_var_instant_sound;
    try erewrite <-interp_vars_instant_sound;
    eauto.

  (* Require Import Coq.Logic.ClassicalChoice. *)
  (* Require Import Coq.Logic.ConstructiveEpsilon. *)
  (* Require Import Coq.Logic.Epsilon. *)
  Require Import Coq.Logic.IndefiniteDescription.

  Theorem slices_sem_block:
    forall G f r xss oss Fm P,
      Ordered_nodes G ->
      (forall k,
          SemSB.sem_block (translate G) f (Fm k)
                          (mask (all_absent (xss 0)) k r xss)
                          (mask (all_absent (oss 0)) k r oss)
          /\ P k (Fm k)) ->
      SemSB.sem_block (translate G) f (reset_memories Fm r (Fm 0)) xss oss
      /\ forall k, P k (Fm k).
  Proof.
    intros ** Ord Sem.
    revert dependent f; revert xss oss r P Fm.
    induction G as [|node]; intros.
    destruct (Sem 0) as (Sem'); inv Sem';
      match goal with Hf: SynSB.find_block _ _ = _ |- _ => inversion Hf end.

    pose proof Ord as Ord'.
    inversion_clear Ord as [|?? Ord'' Hnneqs Hnn].

    assert (forall k, P k (Fm k)) as HP by (intro; destruct (Sem k); auto).

    split; auto.

    assert (exists bl P', SynSB.find_block f (translate (node :: G)) = Some (bl, P'))
      as (bl & P' & Find)
        by (destruct (Sem 0) as (Sem'); inv Sem'; eauto).

    assert (forall k k', same_skeleton (Fm k) (Fm k')) as SameSkeleton
        by (intros; pose proof (Sem k) as Sk; specialize (Sem k'); destruct Sk, Sem;
            eapply sem_block_same_skeleton (* with  (1 := Ord') *); eauto).

    assert (exists F, forall k, exists bk,
                   sem_vars (F k) (map fst (SynSB.b_in bl)) (mask (all_absent (xss 0)) k r xss)
                   /\ sem_vars (F k) (map fst (SynSB.b_out bl)) (mask (all_absent (oss 0)) k r oss)
                   /\ Forall (SemSB.sem_equation (translate (node :: G)) bk (F k) (Fm k)) (SynSB.b_eqs bl)
                   /\ clock_of (mask (all_absent (xss 0)) k r xss) bk
                   /\ SemSB.well_structured_memories (SynSB.b_eqs bl) (Fm k))
      as (Fh & Spec).
    { assert (forall k, exists H bk,
                   sem_vars H (map fst (SynSB.b_in bl)) (mask (all_absent (xss 0)) k r xss)
                   /\ sem_vars H (map fst (SynSB.b_out bl)) (mask (all_absent (oss 0)) k r oss)
                   /\ Forall (SemSB.sem_equation (translate (node :: G)) bk H (Fm k)) (SynSB.b_eqs bl)
                   /\ clock_of (mask (all_absent (xss 0)) k r xss) bk
                   /\ SemSB.well_structured_memories (SynSB.b_eqs bl) (Fm k))
        as Spec.
      { intro; destruct (Sem k) as (Sem'); inv Sem'.
        match goal with
          H: SynSB.find_block _ _ = _ |- _ => rewrite Find in H; inv H end.
        eauto 7.
      }
      now apply functional_choice in Spec.
    }

    assert (forall x k n,
               In x (map fst (SynSB.b_in bl) ++ map fst (SynSB.b_out bl)) ->
               exists v, PM.find x (restr_hist (Fh k) n) = Some v)
      as SameDomFh.
    { clear - Spec.
      intros ** Hin.
      apply in_app in Hin as [Hin|Hin].
      - destruct (Spec k) as (?& In & ?).
        specialize (In n); simpl in *.
        eapply Forall2_In_l in In as (?& Sem); eauto.
        inv Sem; eauto.
      - destruct (Spec k) as (?&?& Out &?).
        specialize (Out n); simpl in *.
        eapply Forall2_In_l in Out as (?& Sem); eauto.
        inv Sem; eauto.
    }

    eapply SemSB.SBlock with (H := reset_history Fh r (Fh 0)); eauto.
    - apply clock_of_equiv.
    - intro; destruct (Spec (count r n)) as (?& In & ?).
      eapply sem_var_instant_bl_vars; eauto.
      intros ? ?; rewrite in_app; auto.
    - intro; destruct (Spec (count r n)) as (?&?& Out &?).
      eapply sem_var_instant_bl_vars; eauto.
      intros ? ?; rewrite in_app; auto.
    - intro; destruct (Sem (count r n)) as (Sem'); inversion_clear Sem' as [???????????? Same].
      specialize (Same n); rewrite mask_transparent in Same; auto.
    - intro; destruct (Sem (count r n)) as (Sem'); inversion_clear Sem' as [????????????? Same].
      specialize (Same n); rewrite mask_transparent in Same; auto.
    - intro; destruct (Sem (count r n)) as (Sem'); inversion_clear Sem' as [?????????????? AbsAbs].
      specialize (AbsAbs n); rewrite 2 mask_transparent in AbsAbs; auto.
    - assert (forall n, 0 < length (xss n)) as Length.
      { clear - Sem.
        intro; destruct (Sem 0) as (Sem');
          inversion_clear Sem' as [?????????? Vars];
          specialize (Vars n); simpl in Vars.
        apply Forall2_length in Vars.
        rewrite mask_length in Vars.
        - rewrite <-Vars, map_length; apply SynSB.b_ingt0.
        - eapply wf_streams_mask.
          intro k'; destruct (Sem k') as (Sem');
            apply SemSB.sem_block_wf in Sem' as (); eauto.
      }

      assert (~ is_block_in (n_name node) (SynSB.b_eqs bl)) as NotIn.
      { pose proof Find as Find'. simpl in Find.
        destruct (ident_eqb (n_name node) f) eqn: E.
        - assert (n_name node = SynSB.b_name bl) as -> by (inv Find; auto).
          eapply find_block_not_is_block_in with (1 := Ord'); eauto.
        - eapply find_block_later_not_is_block_in; eauto.
      }

      assert (forall k, exists bk,
                   sem_vars (Fh k) (map fst (SynSB.b_in bl)) (mask (all_absent (xss 0)) k r xss)
                   /\ sem_vars (Fh k) (map fst (SynSB.b_out bl)) (mask (all_absent (oss 0)) k r oss)
                   /\ Forall (SemSB.sem_equation (translate (node :: G)) bk (Fh k) (Fm k)) (SynSB.b_eqs bl)
                   /\ clock_of (mask (all_absent (xss 0)) k r xss) bk) as Spec'
          by (intro; destruct (Spec k) as (?&?&?&?&?&?); eauto).
      clear Spec; rename Spec' into Spec.

      induction (SynSB.b_eqs bl) as [|eq ? IHeqs]; constructor; auto.
      + clear IHeqs.
        assert (forall k, exists bk, SemSB.sem_equation (translate (node :: G)) bk (Fh k) (Fm k) eq
                           /\ clock_of (mask (all_absent (xss 0)) k r xss) bk)
          as Spec'
            by (intros; destruct (Spec k) as (?&?&?& Heq &?); inv Heq; eauto).
        clear Spec.
        set (bk := clock_of' xss).
        set (H := reset_history Fh r (Fh 0)).

        assert (spec_eq Fh eq) as SpecEq
            by (eapply sem_spec_eq; intros; destruct (Spec' k) as (?&?&?); eauto).

        destruct eq; inv SpecEq.

        * apply SemSB.SEqDef with (xs := interp_caexp bk H c c0);
            intro; destruct (Spec' (count r n)) as (?& Heq &?); inv Heq;
              interp_sound n.

        *{ apply SemSB.SEqFby with (xs := interp_var H i) (ls := interp_laexp bk H c l0);
             try (intro; destruct (Spec' (count r n)) as (?& Heq &?); inv Heq; interp_sound n).
           assert (exists F, forall k, exists bk xs ls,
                          sem_var (Fh k) i xs
                          /\ sem_laexp bk (Fh k) c l0 ls
                          /\find_val i (Fm k) = Some (F k)
                          /\ (F k).(SemSB.content) 0 = sem_const c0
                          /\ (forall n,
                                match ls n with
                                | absent =>
                                  (F k).(SemSB.content) (S n) =
                                  (if (F k).(SemSB.reset) (S n) then sem_const c0 else (F k).(SemSB.content) n)
                                  /\ xs n = absent
                                | present v' =>
                                  (F k).(SemSB.content) (S n) =
                                  (if (F k).(SemSB.reset) (S n) then sem_const c0 else v')
                                  /\ xs n = present ((F k).(SemSB.content) n)
                                end)
                          /\ clock_of (mask (all_absent (xss 0)) k r xss) bk)
             as (Fmvs & Spec).
           { assert (forall k, exists mvs bk xs ls,
                          sem_var (Fh k) i xs
                          /\ sem_laexp bk (Fh k) c l0 ls
                          /\ find_val i (Fm k) = Some mvs
                          /\ mvs.(SemSB.content) 0 = sem_const c0
                          /\ (forall n,
                                match ls n with
                                | absent =>
                                  mvs.(SemSB.content) (S n) =
                                  (if mvs.(SemSB.reset) (S n) then sem_const c0 else mvs.(SemSB.content) n)
                                  /\ xs n = absent
                                | present v' =>
                                  mvs.(SemSB.content) (S n) =
                                  (if mvs.(SemSB.reset) (S n) then sem_const c0 else v')
                                  /\ xs n = present (mvs.(SemSB.content) n)
                                end)
                          /\ clock_of (mask (all_absent (xss 0)) k r xss) bk) as Spec.
             { intro; destruct (Spec' k) as (?& Heq &?); inversion_clear Heq as [|??????????? Fby| |]; inv Fby.
               eauto 10.
             }
             now apply functional_choice in Spec.
           }

           apply SemSB.mfby_intro with (mvs := reset_mvalues Fmvs r).
           - apply find_val_reset_memories.
             intro; destruct (Spec k) as (?&?&?&?); intuition.
           - simpl; destruct (r 0).
             + destruct (Spec 1) as (?&?&?&?); intuition.
             + destruct (Spec 0) as (?&?&?&?); intuition.
           - intro; destruct (Spec (count r n)) as (?&?&?&?&?&?&?& Heq &?).
             pose proof (reset_mvalues_spec _ _ _ _ _ _ _ _ _ Length Spec (S n)) as SpecMv.
             clear Spec.
             interp_sound n.
             specialize (Heq n).
             destruct (r (S n)) eqn: E; [rewrite SpecMv; auto|];
               simpl; rewrite E; simpl; auto.
             destruct (x1 n); intuition.
         }

        *{ assert (exists M0, sub_inst i0 (Fm 0) M0) as (M0 & Find0)
               by (destruct (Spec' 0) as (?& Heq & ?); inv Heq; eauto).
           apply SemSB.SEqReset with (rs := interp_var H i1) (M' := reset_memories_path Fm r [i0] M0).
           - intro; destruct (Spec' (count r n)) as (?& Heq &?); inv Heq; interp_sound n.
           - now apply sub_inst_reset_memories_path.
           - rewrite reset_regs_instant_spec.
             intro; destruct (Spec' (count r n)) as (?& Heq &?); inversion_clear Heq as [| |????????? Var|].
             eapply reset_memories_path_sub_spec_instant'; eauto.
             + eapply same_skeleton_sub_inst; eauto.
             + replace (reset_of (interp_var H i1) n) with (reset_of_value (interp_var H i1 n)); auto.
               interp_sound n.
               replace (reset_of_value (rs n)) with (reset_of rs n); auto.
               apply reset_regs_instant_spec'; auto.
         }

        *{ assert (exists F, forall k,
                        SemSB.sem_block (translate G) i0
                                        (F k)
                                        (mask (all_absent (interp_laexps bk H c l0 0)) k r (interp_laexps bk H c l0))
                                        (mask (all_absent (interp_vars H i 0)) k r (interp_vars H i))
                        /\ sub_inst i1 (Fm k) (F k)) as (F & Spec).
           { assert (forall k, exists M bk ess oss,
                          sem_laexps bk (Fh k) c l0 ess
                          /\ sub_inst i1 (Fm k) M
                          /\ SemSB.sem_block (translate (node :: G)) i0 M ess oss
                          /\ sem_vars (Fh k) i oss
                          /\ clock_of (mask (all_absent (xss 0)) k r xss) bk) as Spec.
             { intro; destruct (Spec' k) as (?& Heq & Clock);
                 inversion_clear Heq as [| | |???? M' ?????? Exps ? Block Vars]; eauto 9.
             }
             apply functional_choice in Spec as (F & Spec).
             exists F; intro; destruct (Spec k) as (?&?&?& Exps & ? & Block & Vars & ?).

             erewrite sem_laexps_interp_mask in Block; eauto.
             pose proof Block as Block'; inversion_clear Block' as [?????????????? Same].
             destruct (Spec' 0) as (?& Heq &?); inv Heq.
             erewrite sem_vars_interp_mask with (1 := Vars) (r := r) in Block; eauto.
             - split; auto.
               eapply sem_block_cons; eauto.
               intro E; apply NotIn; rewrite E; do 2 constructor.
             - intros ** E; apply Same.
               rewrite mask_opaque; auto.
               apply all_absent_spec.
           }
           edestruct (IHG Ord'' (interp_laexps bk H c l0) (interp_vars H i) r (fun k M => sub_inst i1 (Fm k) M))
             as (?& Sub); eauto.
           eapply SemSB.SEqCall with (M' := reset_memories F r (F 0))
                                     (ess := interp_laexps bk H c l0)
                                     (oss := interp_vars H i).
           - intro; destruct (Spec' (count r n)) as (?& Heq &?); inv Heq; interp_sound n.
           - now apply sub_inst_reset_memories.
           - apply sem_block_cons2; auto.
           - intro; destruct (Spec' (count r n)) as (?& Heq &?); inv Heq; interp_sound n.
         }

      + apply IHeqs.
        * intro E; apply NotIn; right; auto.
        * intro; destruct (Spec k) as (?&?&?& Heqs &?); inv Heqs; eauto.

    - destruct (Spec 0) as (?&?&?&?&?&?).
      apply well_structured_reset_memories; auto.
  Qed.

  Theorem reset_correctness:
    forall G f r xss oss,
      Ordered_nodes G ->
      (forall f xss oss,
          sem_node G f xss oss ->
          exists M, SemSB.sem_block (translate G) f M xss oss) ->
      sem_reset G f r xss oss ->
      exists M, SemSB.sem_block (translate G) f M xss oss
           /\ SemSB.reset_regs r M.
  Proof.
    intros ** Ord IHNode Sem.
    inversion_clear Sem as [???? Sem'].

    assert (exists F, forall k, SemSB.sem_block (translate G) f (F k)
                                      (mask (all_absent (xss 0)) k r xss)
                                      (mask (all_absent (oss 0)) k r oss))
      as (Fm & Sem).
    { assert (forall k, exists M', SemSB.sem_block (translate G) f M'
                                         (mask (all_absent (xss 0)) k r xss)
                                         (mask (all_absent (oss 0)) k r oss)) as SBsem
          by (intro; specialize (Sem' k); apply IHNode in Sem'; auto).

      (** Infinite Description  *)
      now apply functional_choice in SBsem.

      (** Epsilon  *)
      (* assert (inhabited memories) as I *)
      (*     by (constructor; exact (fun n => @empty_memory val)). *)
      (* exists (fun n => epsilon *)
      (*            I (fun M => msem_node G f (mask (all_absent (xs 0)) n r xs) M *)
      (*                               (mask (all_absent (ys 0)) n r ys))). *)
      (* intro; now apply epsilon_spec.  *)

      (** Constructive Epsilon  *)
      (* pose proof (constructive_ground_epsilon memories) as F. *)

      (** Classical Choice  *)
      (* now apply choice in Msem'.   *)
    }
    edestruct (slices_sem_block G f r xss oss Fm (fun _ _ => True)); eauto.
  Qed.

  Theorem correctness:
    forall G f xss oss,
      Welldef_global G ->
      sem_node G f xss oss ->
      exists M, SemSB.sem_block (translate G) f M xss oss.
  Proof.
    induction G as [|node].
    inversion 2;
      match goal with Hf: find_node _ [] = _ |- _ => inversion Hf end.
    intros ** WD Hsem.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [??????? Hfind ????? Heqs].
    pose proof (Welldef_global_Ordered_nodes _ WD) as Hord.
    pose proof (Welldef_global_cons _ _ WD) as WD'.
    pose proof (find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    simpl in Hfind.
    destruct (ident_eqb node.(n_name) f) eqn:Hnf.
    - assert (Hord':=Hord).
      inversion_clear Hord as [|? ? Hord'' Hnneqs Hnn].
      inv Hfind.
      eapply Forall_sem_equation_global_tl in Heqs; eauto.

      assert (forall f xss oss,
                 sem_node G f xss oss ->
                 exists M, SemSB.sem_block (translate G) f M xss oss)
        as IHG' by auto.

      assert (forall f r xss oss,
                 sem_reset G f r xss oss ->
                 exists M, SemSB.sem_block (translate G) f M xss oss
                      /\ SemSB.reset_regs r M)
        by (intros; apply reset_correctness; auto).

      assert (exists M', Forall (SemSB.sem_equation (translate G) bk H M') (translate_eqns n.(n_eqs))
                    /\ SemSB.well_structured_memories (translate_eqns n.(n_eqs)) M')
        as (M & Hmsem & WS)
          by (eapply equations_correctness; eauto;
              inv WD; eapply Is_well_sch_compat; eauto).

      exists M.
      econstructor; eauto.
      + simpl; now rewrite Hnf.
      + simpl; rewrite map_fst_idty; eauto.
      + simpl; rewrite map_fst_idty; eauto.
      + eapply sem_equation_cons; eauto.
      + auto.
    - apply ident_eqb_neq in Hnf.
      eapply sem_node_cons in Hsem; eauto.
      inv Hord.
      eapply IHG in Hsem as [M]; eauto.
      exists M.
      now eapply sem_block_cons2; eauto.
  Qed.
