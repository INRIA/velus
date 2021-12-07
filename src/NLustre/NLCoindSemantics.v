From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Setoid.
From Coq Require Import Morphisms.
From Coq Require Import Arith.EqNat.

From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import CoindStreams.

(** * The NLustre semantics *)

(**

  We provide a "standard" dataflow semantics relating an environment
  of streams to a stream of outputs.

 *)

Module Type NLCOINDSEMANTICS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import CESyn : CESYNTAX      Ids Op OpAux Cks)
       (Import Syn   : NLSYNTAX      Ids Op OpAux Cks CESyn)
       (Import Str   : COINDSTREAMS  Ids Op OpAux Cks)
       (Import Ord   : NLORDERED     Ids Op OpAux Cks CESyn Syn).

  Definition sem_clocked_var (H: history) (b: Stream bool) (x: ident) (ck: clock) : Prop :=
    (forall xs,
        sem_var H x xs ->
        exists bs,
          sem_clock H b ck bs
          /\ aligned xs bs)
    /\ (forall bs,
          sem_clock H b ck bs ->
          exists xs,
            sem_var H x xs).

  Definition sem_clocked_vars (H: history) (b: Stream bool) (xs: list (ident * clock)) : Prop :=
    Forall (fun xc => sem_clocked_var H b (fst xc) (snd xc)) xs.

  Inductive sem_exp: history -> Stream bool -> exp -> Stream svalue -> Prop :=
  | Sconst:
      forall H b c cs,
        cs ≡ const b c ->
        sem_exp H b (Econst c) cs
  | Senum:
      forall H b x ty cs,
        cs ≡ enum b x ->
        sem_exp H b (Eenum x ty) cs
  | Svar:
      forall H b x ty xs,
        sem_var H x xs ->
        sem_exp H b (Evar x ty) xs
  | Swhen:
      forall H b e x c es xs os,
        sem_exp H b e es ->
        sem_var H x xs ->
        when c es xs os ->
        sem_exp H b (Ewhen e x c) os
  | Sunop:
      forall H b op e ty es os,
        sem_exp H b e es ->
        lift1 op (typeof e) es os ->
        sem_exp H b (Eunop op e ty) os
  | Sbinop:
      forall H b op e1 e2 ty es1 es2 os,
        sem_exp H b e1 es1 ->
        sem_exp H b e2 es2 ->
        lift2 op (typeof e1) (typeof e2) es1 es2 os ->
        sem_exp H b (Ebinop op e1 e2 ty) os.

  Inductive sem_cexp: history -> Stream bool -> cexp -> Stream svalue -> Prop :=
  | Smerge:
      forall H b x tx es ty xs ess os,
        sem_var H x xs ->
        Forall2 (sem_cexp H b) es ess ->
        merge xs (combine (seq 0 (length ess)) ess) os ->
        sem_cexp H b (Emerge (x, tx) es ty) os
  | Scase:
      forall H b e es d xs ess os,
        sem_exp H b e xs ->
        Forall2 (fun oe => sem_cexp H b (or_default d oe)) es ess ->
        case xs (combine (seq 0 (length ess)) ess) None os ->
        sem_cexp H b (Ecase e es d) os
  | Sexp:
      forall H b e es,
        sem_exp H b e es ->
        sem_cexp H b (Eexp e) es.

  Section SemInd.

    Variable P_cexp: history -> Stream bool -> cexp -> Stream svalue -> Prop.

    Hypothesis MergeCase:
      forall H b x tx es ty xs ess os,
        sem_var H x xs ->
        Forall2 (sem_cexp H b) es ess ->
        Forall2 (P_cexp H b) es ess ->
        merge xs (combine (seq 0 (length ess)) ess) os ->
        P_cexp H b (Emerge (x, tx) es ty) os.

    Hypothesis CaseCase:
      forall H b e es d xs ess os,
        sem_exp H b e xs ->
        Forall2 (fun oe => sem_cexp H b (or_default d oe)) es ess ->
        Forall2 (fun oe => P_cexp H b (or_default d oe)) es ess ->
        case xs (combine (seq 0 (length ess)) ess) None os ->
        P_cexp H b (Ecase e es d) os.

    Hypothesis ExpCase:
      forall H b e es,
        sem_exp H b e es ->
        P_cexp H b (Eexp e) es.

    Fixpoint sem_cexp_ind2
             (H: history) (b: Stream bool) (e: cexp) (os: Stream svalue)
             (Sem: sem_cexp H b e os) {struct Sem}
      : P_cexp H b e os.
    Proof.
      destruct Sem; eauto.
      - eapply MergeCase; eauto.
        take (merge _ _ _) and clear it.
        take (Forall2 _ _ _) and induction it; constructor; auto.
      - eapply CaseCase; eauto.
        take (case _ _ _ _) and clear it.
        take (Forall2 _ _ _) and induction it; constructor; auto.
    Qed.

  End SemInd.

  CoInductive sem_annot {A} (sem: history -> Stream bool -> A -> Stream svalue -> Prop):
    history -> Stream bool -> clock -> A -> Stream svalue -> Prop :=
  | Stick:
      forall H b ck a e es bs,
        sem H b a (present e ⋅ es) ->
        sem_clock H b ck (true ⋅ bs) ->
        sem_annot sem (history_tl H) (tl b) ck a es ->
        sem_annot sem H b ck a (present e ⋅ es)
  | Sabs:
      forall H b ck a es bs,
        sem H b a (absent ⋅ es) ->
        sem_clock H b ck (false ⋅ bs) ->
        sem_annot sem (history_tl H) (tl b) ck a es ->
        sem_annot sem H b ck a (absent ⋅ es).

  Definition sem_aexp := sem_annot sem_exp.
  Definition sem_caexp := sem_annot sem_cexp.

  CoFixpoint reset1 (v0: value) (xs: Stream svalue) (rs: Stream bool) (doreset : bool) : Stream svalue :=
    match xs, rs, doreset with
    | absent ⋅ xs, false ⋅ rs, false => absent ⋅ (reset1 v0 xs rs false)
    | absent ⋅ xs, _ ⋅ rs, _ => absent ⋅ (reset1 v0 xs rs true)
    | present x ⋅ xs, false ⋅ rs, false => present x ⋅ (reset1 v0 xs rs false)
    | present x ⋅ xs, _ ⋅ rs, _ => present v0 ⋅ (reset1 v0 xs rs false)
    end.

  Definition reset (v0: value) (xs: Stream svalue) (rs: Stream bool) : Stream svalue :=
    reset1 v0 xs rs false.

  Lemma reset_false : forall v0 xs,
      reset v0 xs (Streams.const false) ≡ xs.
  Proof.
    cofix CoFix. intros *.
    unfold_Stv xs; constructor; simpl; auto.
    1,2:apply CoFix.
  Qed.

  Lemma reset1_fby : forall v0 v xs rs,
      reset1 v0 (sfby v xs) rs true ≡ reset1 v0 (sfby v0 xs) rs false.
  Proof.
    intros *.
    apply ntheq_eqst. intros n. revert n v0 v xs rs.
    induction n; intros *.
    1,2:unfold_Stv xs; unfold_Stv rs; simpl; auto.
    - do 2 rewrite Str_nth_S_tl; simpl.
      etransitivity. 2:symmetry. 1,2:eapply IHn.
    - do 2 rewrite Str_nth_S_tl; simpl.
      eapply IHn.
  Qed.

  Lemma reset1_absent : forall n v0 xs rs r,
      xs # n = absent ->
      (reset1 v0 xs rs r) # n = absent.
  Proof.
    induction n;
      (intros * Hx;
       unfold_Stv xs; unfold_Stv rs;
       repeat rewrite Str_nth_0_hd in *; repeat rewrite Str_nth_S_tl in *;
       simpl in *; try congruence; auto).
    1-3:destruct r; auto.
  Qed.

  Fact lt_S_inv : forall n m,
      n < S m ->
      (n < m \/ n = m).
  Proof.
    intros * Hlt.
    apply Lt.le_lt_or_eq, Lt.lt_n_Sm_le; auto.
  Qed.

  Lemma reset1_present1 : forall n k v0 xs rs x,
      k < n ->
      xs # k = present x ->
      (reset1 v0 xs rs true) # n = (reset1 v0 xs rs false) # n.
  Proof.
    induction n;
      (intros * Hk Hx;
       unfold_Stv xs; unfold_Stv rs;
       repeat rewrite Str_nth_0_hd in *; repeat rewrite Str_nth_S_tl in *;
       simpl in *; try congruence; auto).
    - inv Hk.
    - apply lt_S_inv in Hk as [?|?]; subst.
      + destruct k. rewrite Str_nth_0 in Hx; congruence.
        rewrite Str_nth_S in Hx.
        eapply IHn; [|eauto]. apply Nat.lt_succ_l; auto.
      + destruct n. rewrite Str_nth_0 in Hx; congruence.
        specialize (IHn n).
        eapply IHn; eauto.
  Qed.

  Lemma reset1_present2 : forall n v0 xs rs x,
      (forall k, k < n -> xs # k = absent) ->
      xs # n = present x ->
      (reset1 v0 xs rs true) # n = present v0.
  Proof.
    induction n;
      (intros * Hk Hx;
       unfold_Stv xs; unfold_Stv rs;
       repeat rewrite Str_nth_0_hd in *; repeat rewrite Str_nth_S_tl in *;
       simpl in *; try congruence; auto).
    - eapply IHn; eauto.
      intros ? Hkn. specialize (Hk (S k)).
      rewrite Str_nth_S in Hk. apply Hk, Lt.lt_n_S; auto.
    - eapply IHn; eauto.
      intros ? Hkn. specialize (Hk (S k)).
      rewrite Str_nth_S in Hk. apply Hk, Lt.lt_n_S; auto.
    - specialize (Hk 0 (Nat.lt_0_succ _)).
      rewrite Str_nth_0 in Hk. inv Hk.
    - specialize (Hk 0 (Nat.lt_0_succ _)).
      rewrite Str_nth_0 in Hk. inv Hk.
  Qed.

  Section NodeSemantics.

    Variable G: global.

    Inductive sem_equation: history -> Stream bool -> equation -> Prop :=
    | SeqDef:
        forall H b x ck e es,
          sem_caexp H b ck e es ->
          sem_var H x es ->
          sem_equation H b (EqDef x ck e)
    | SeqApp:
        forall H b xs ck f es xrs ys rs ess oss,
          Forall2 (sem_exp H b) es ess ->
          sem_clock H b ck (clocks_of ess) ->
          Forall2 (sem_var H) (List.map fst xrs) ys ->
          bools_ofs ys rs ->
          (forall k, sem_node f (List.map (maskv k rs) ess) (List.map (maskv k rs) oss)) ->
          Forall2 (sem_var H) xs oss ->
          sem_equation H b (EqApp xs ck f es xrs)
    | SeqFby:
        forall H b x ck c0 e xrs es os ys rs,
          sem_aexp H b ck e es ->
          Forall2 (sem_var H) (List.map fst xrs) ys ->
          sem_clocked_vars H b xrs ->
          bools_ofs ys rs ->
          os = reset (sem_const c0) (sfby (sem_const c0) es) rs ->
          sem_var H x os ->
          sem_equation H b (EqFby x ck c0 e xrs)

    with sem_node: ident -> list (Stream svalue) -> list (Stream svalue) -> Prop :=
      SNode:
        forall H f n xss oss,
          find_node f G = Some n ->
          Forall2 (sem_var H) (List.map fst n.(n_in)) xss ->
          Forall2 (sem_var H) (List.map fst n.(n_out)) oss ->
          sem_clocked_vars H (clocks_of xss) (idck n.(n_in)) ->
          Forall (sem_equation H (clocks_of xss)) n.(n_eqs) ->
          sem_node f xss oss.

  End NodeSemantics.

  Global Hint Constructors sem_equation : nlsem.

  Section SemInd.

    Variable G: global.

    Variable P_equation: history -> Stream bool -> equation -> Prop.
    Variable P_node: ident -> list (Stream svalue) -> list (Stream svalue) -> Prop.

    Hypothesis EqDefCase:
      forall H b x ck e es,
        sem_caexp H b ck e es ->
        sem_var H x es ->
        P_equation H b (EqDef x ck e).

    Hypothesis EqAppCase:
      forall H b xs ck f es xrs ys rs ess oss,
        Forall2 (sem_exp H b) es ess ->
        sem_clock H b ck (clocks_of ess) ->
        Forall2 (sem_var H) (List.map fst xrs) ys ->
        bools_ofs ys rs ->
        (forall k, sem_node G f (List.map (maskv k rs) ess) (List.map (maskv k rs) oss)
              /\ P_node f (List.map (maskv k rs) ess) (List.map (maskv k rs) oss)) ->
        Forall2 (sem_var H) xs oss ->
        P_equation H b (EqApp xs ck f es xrs).

    Hypothesis EqFbyCase:
      forall H b x ck c0 e xrs es os ys rs,
        sem_aexp H b ck e es ->
        Forall2 (sem_var H) (List.map fst xrs) ys ->
        sem_clocked_vars H b xrs ->
        bools_ofs ys rs ->
        os = reset (sem_const c0) (sfby (sem_const c0) es) rs ->
        sem_var H x os ->
        P_equation H b (EqFby x ck c0 e xrs).

    Hypothesis NodeCase:
      forall H f n xss oss,
        find_node f G = Some n ->
        Forall2 (sem_var H) (List.map fst n.(n_in)) xss ->
        Forall2 (sem_var H) (List.map fst n.(n_out)) oss ->
        sem_clocked_vars H (clocks_of xss) (idck n.(n_in)) ->
        Forall (sem_equation G H (clocks_of xss)) n.(n_eqs) ->
        Forall (P_equation H (clocks_of xss)) n.(n_eqs) ->
        P_node f xss oss.

    Fixpoint sem_equation_mult
             (H: history) (b: Stream bool) (e: equation)
             (Sem: sem_equation G H b e) {struct Sem}
      : P_equation H b e
    with sem_node_mult
           (f: ident) (xss oss: list (Stream svalue))
           (Sem: sem_node G f xss oss) {struct Sem}
         : P_node f xss oss.
    Proof.
      - destruct Sem; eauto.
      - destruct Sem; eauto.
        eapply NodeCase; eauto.
        match goal with H: Forall _ _ |- _ => induction H; auto end.
    Qed.

    Combined Scheme sem_equation_node_ind from
             sem_equation_mult, sem_node_mult.

  End SemInd.

  (** ** Properties of the [global] environment *)

  Lemma sem_node_cons2:
    forall enms nd nds f xs ys,
      Ordered_nodes (Global enms nds)
      -> sem_node (Global enms nds) f xs ys
      -> Forall (fun nd' : node => n_name nd <> n_name nd') nds
      -> sem_node (Global enms (nd::nds)) f xs ys.
  Proof.
    intros * Hord Hsem Hnin.
    assert (Hnin':=Hnin).
    revert Hnin'.
    induction Hsem as [
                     |
                     |
                     | bk f n xs ys Hfind Hinp Hout Hscvs Heqs IH]
      using sem_node_mult
      with (P_equation := fun bk H eq =>
                   ~Is_node_in_eq nd.(n_name) eq
                   -> sem_equation (Global enms (nd::nds)) bk H eq);
      try eauto using sem_equation; try intro Hb.
    - econstructor; eauto. intro k.
      take (forall k, _ /\ _) and specialize (it k) as []. auto.
    - assert (nd.(n_name) <> f) as Hnf.
      { intro Hnf; subst.
        eapply find_node_In in Hfind as (?&?); simpl in *.
        eapply Forall_forall in Hnin; [|eauto]. congruence. }
      econstructor; eauto.
      rewrite find_node_other; auto.
      apply Forall_impl_In with (2:=IH).
      intros eq Hin HH. apply HH; clear HH.
      destruct eq; try inversion 1; subst.
      pose proof Hin as Hsem; apply Forall_forall with (1:=Heqs)in Hsem.
      inversion_clear Hsem as [| ??????????????? Hsemn|].
      specialize (Hsemn 0).
      inversion_clear Hsemn as [ ? ? ? ? ? Hfind'].
      eapply find_node_In in Hfind' as (?&Hfind').
      apply Forall_forall with (1:=Hnin) in Hfind'. auto.
  Qed.

  Lemma sem_equation_cons2:
    forall enms nds b H eqs nd,
      Ordered_nodes (Global enms (nd::nds))
      -> Forall (sem_equation (Global enms nds) H b) eqs
      -> ~Is_node_in nd.(n_name) eqs
      -> Forall (sem_equation (Global enms (nd::nds)) H b) eqs.
  Proof.
    intros * Hord Hsem Hnini.
    induction eqs as [|eq eqs IH]; [now constructor|].
    apply Forall_cons2 in Hsem.
    destruct Hsem as [Heq Heqs].
    apply not_Is_node_in_cons in Hnini.
    destruct Hnini as [Hnini Hninis].
    apply IH with (2:=Hninis) in Heqs.
    constructor; [|now apply Heqs].
    destruct Heq (* as [|? ? ? ? ? ? ? ? ? ? ? ? ? Hsem|] *);
      try now eauto using sem_equation.
    econstructor; eauto using sem_equation.
    inversion_clear Hord as [|? ? (?&?) Hnn].
    intros. apply sem_node_cons2; eauto.
  Qed.

  Add Parametric Morphism : sem_var
      with signature Env.Equiv (@EqSt _) ==> eq ==> @EqSt svalue ==> Basics.impl
        as sem_var_EqSt.
  Proof.
    intros H H' EH x xs xs' E; intro Sem; inv Sem.
    eapply Env.Equiv_orel in EH. rewrite H1 in EH. inv EH. symmetry in H3.
    econstructor; eauto.
    transitivity xs; symmetry; auto.
    transitivity xs'0; symmetry; auto.
  Qed.

  Add Parametric Morphism k : (when k)
      with signature @EqSt svalue ==> @EqSt svalue ==> @EqSt svalue ==> Basics.impl
        as when_EqSt.
  Proof.
    cofix Cofix.
    intros cs cs' Ecs xs xs' Exs ys ys' Eys H.
    destruct cs' as [[]], xs' as [[]], ys' as [[]];
      inv H; inv Ecs; inv Exs; inv Eys; simpl in *;
        try discriminate.
      + constructor; eapply Cofix; eauto.
      + repeat (take (present _ = present _) and inv it).
        constructor; auto.
        eapply Cofix; eauto.
      + repeat (take (present _ = present _) and inv it).
        constructor.
        eapply Cofix; eauto.
  Qed.

  Add Parametric Morphism op t : (lift1 op t)
      with signature @EqSt svalue ==> @EqSt svalue ==> Basics.impl
        as lift1_EqSt.
  Proof.
    cofix Cofix.
    intros es es' Ees ys ys' Eys Lift.
    destruct es' as [[]], ys' as [[]];
      inversion Lift; inversion Eys; inversion Ees; simpl in *; subst ys es; try discriminate.
    - constructor; eapply Cofix; eauto.
    - repeat (take (present _ = present _) and inv it).
      constructor; auto.
      eapply Cofix; eauto.
  Qed.

  Add Parametric Morphism op t1 t2 : (lift2 op t1 t2)
      with signature @EqSt svalue ==> @EqSt svalue ==> @EqSt svalue ==> Basics.impl
        as lift2_EqSt.
  Proof.
    cofix Cofix.
    intros e1s e1s' Ee1s e2s e2s' Ee2s ys ys' Eys Lift.
    destruct e1s' as [[]], e2s' as [[]], ys' as [[]];
      inversion Lift; inversion Eys; inversion Ee1s; inversion Ee2s; simpl in *; subst ys e1s e2s; try discriminate.
    - constructor; eapply Cofix; eauto.
    - repeat (take (present _ = present _) and inv it).
      constructor; auto.
      eapply Cofix; eauto.
  Qed.

  Add Parametric Morphism : (const)
      with signature @EqSt bool ==> eq ==> @EqSt svalue
        as const_EqSt.
  Proof.
    cofix CoFix; intros b b' Eb.
    unfold_Stv b; unfold_Stv b';
      constructor; inv Eb; simpl in *; try discriminate; auto.
  Qed.

  Add Parametric Morphism : reset
      with signature @eq value ==> @EqSt svalue ==> @EqSt bool ==> @EqSt svalue
        as reset_EqSt.
  Proof.
    unfold reset. remember false as b. clear Heqb. revert b.
    cofix CoFix.
    intros * Heq1 * Heq2.
    unfold_St x; unfold_St x0; unfold_St y0; unfold_St y1.
    inv Heq1. inv Heq2. simpl in *; subst.
    destruct s0, b, b1; constructor; simpl; auto.
  Qed.

  Add Parametric Morphism : (enum)
      with signature @EqSt bool ==> eq ==> @EqSt svalue
        as enum_EqSt.
  Proof.
    cofix CoFix; intros b b' Eb.
    unfold_Stv b; unfold_Stv b';
      constructor; inv Eb; simpl in *; try discriminate; auto.
  Qed.

  Add Parametric Morphism : sem_exp
      with signature Env.Equiv (@EqSt _) ==> @EqSt bool ==> eq ==> @EqSt svalue ==> Basics.impl
        as sem_exp_morph.
  Proof.
    intros H H' EH b b' Eb e xs xs' Exs Sem.
    revert b' xs' Eb Exs; induction Sem.
    - intros. constructor.
      rewrite <-Eb.
      transitivity cs; auto.
      now symmetry.
    - intros. constructor.
      rewrite <-Eb.
      transitivity cs; auto.
      now symmetry.
    - econstructor; eauto.
      eapply sem_var_EqSt; eauto.
    - econstructor; eauto.
      apply IHSem; auto; try reflexivity.
      erewrite <-EH; eauto.
      now rewrite <-Exs.
    - econstructor; eauto.
      + apply IHSem; auto; reflexivity.
      + now rewrite <-Exs.
    - econstructor; eauto.
      + apply IHSem1; auto; reflexivity.
      + apply IHSem2; auto; reflexivity.
      + now rewrite <-Exs.
  Qed.

  Add Parametric Morphism : sem_cexp
      with signature Env.Equiv (@EqSt _) ==> @EqSt bool ==> eq ==> @EqSt svalue ==> Basics.impl
        as sem_cexp_morph.
  Proof.
    intros H H' EH b b' Eb e xs xs' Exs Sem.
    revert b' xs' Eb Exs; revert dependent xs;
      induction e using cexp_ind2; intros; inv Sem.
    - econstructor; eauto.
      + erewrite <-EH; eauto.
      + instantiate (1 := ess).
        take (merge _ _ _) and clear it.
        revert dependent ess; induction l; inversion_clear 1;
          constructor; take (Forall _ _) and inv it; auto.
        take (forall xs, sem_cexp _ _ _ _ -> _) and eapply it; eauto; reflexivity.
      + now rewrite <-Exs.
    - econstructor; eauto.
      + rewrite <-EH, <-Eb; eauto.
      + instantiate (1 := ess).
        take (case _ _ _ _) and clear it.
        revert dependent ess; induction l; inversion_clear 1;
          constructor; take (Forall _ _) and inv it; auto.
        take (forall xs, sem_cexp _ _ _ _ -> _) and eapply it; eauto; reflexivity.
      + now rewrite <-Exs.
    - constructor.
      now rewrite <-EH, <-Eb, <-Exs.
  Qed.

  Add Parametric Morphism A sem
    (sem_compat: Proper (Env.Equiv (@EqSt _) ==> @EqSt bool ==> eq ==> @EqSt svalue ==> Basics.impl) sem)
    : (@sem_annot A sem)
      with signature Env.Equiv (@EqSt _) ==> @EqSt bool ==> eq ==> eq ==> @EqSt svalue ==> Basics.impl
        as sem_annot_morph.
  Proof.
    revert sem_compat; cofix Cofix.
    intros sem_compat H H' EH b b' Eb ck e xs xs' Exs Sem.
    inv Sem; unfold_Stv xs'; inversion_clear Exs as [Eh Et];
      try discriminate.
    - econstructor.
      + simpl in *; now rewrite <-EH, <-Eh, <-Et, <-Eb.
      + rewrite <-EH, <-Eb; eauto.
      + inv Eb; eapply Cofix; eauto.
        eapply history_tl_Equiv; eauto.
    - econstructor.
      + simpl in *; now rewrite <-EH, <-Et, <-Eb.
      + rewrite <-EH, <-Eb; eauto.
      + inv Eb; eapply Cofix; eauto.
        eapply history_tl_Equiv; eauto.
  Qed.

  Add Parametric Morphism : sem_aexp
      with signature Env.Equiv (@EqSt _) ==> @EqSt bool ==> eq ==> eq ==> @EqSt svalue ==> Basics.impl
        as sem_aexp_morph.
  Proof.
    intros; eapply sem_annot_morph; eauto.
    solve_proper.
  Qed.

  Add Parametric Morphism : sem_caexp
      with signature Env.Equiv (@EqSt _) ==> @EqSt bool ==> eq ==> eq ==> @EqSt svalue ==> Basics.impl
        as sem_caexp_morph.
  Proof.
    intros; eapply sem_annot_morph; eauto.
    solve_proper.
  Qed.

  Add Parametric Morphism : count
      with signature @EqSt bool ==> @EqSt nat
        as count_EqSt.
  Proof.
    unfold count; generalize 0.
    cofix Cofix; intros n xs xs' Exs.
    unfold_Stv xs; unfold_Stv xs'; constructor; inv Exs;
      simpl in *; try discriminate; auto.
  Qed.

  Add Parametric Morphism H : (sem_clocked_var H)
      with signature @EqSt bool ==> eq ==> eq ==> Basics.impl
        as sem_clocked_var_morph.
  Proof.
    intros bs bs' E x ck (Sem & Sem'); split; now setoid_rewrite <-E.
  Qed.

  Add Parametric Morphism G H : (sem_equation G H)
      with signature @EqSt bool ==> eq ==> Basics.impl
        as mod_sem_equation_morph.
  Proof.
    unfold Basics.impl; intros b b' Eb e Sem.
    induction Sem; econstructor; eauto; try now rewrite <-Eb.
    - eapply Forall2_impl_In with (P := sem_exp H b); auto.
      intros; now rewrite <-Eb.
    - unfold sem_clocked_vars in *.
      eapply Forall_impl; [|eauto].
      intros; now rewrite <-Eb.
  Qed.

  Add Parametric Morphism H : (sem_clocked_vars H)
      with signature @EqSt bool ==> eq ==> Basics.impl
        as sem_clocked_vars_morph.
  Proof.
    intros bs bs' E xs Sem.
    induction Sem; constructor; auto.
    now rewrite <-E.
  Qed.

  Add Parametric Morphism G : (sem_node G)
      with signature eq ==> @EqSts svalue ==> @EqSts svalue ==> Basics.impl
        as mod_sem_node_morph.
  Proof.
    unfold Basics.impl; intros f xss xss' Exss yss yss' Eyss Sem.
    induction Sem.
    econstructor; eauto.
    + instantiate (1:=H).
      now rewrite <-Exss.
    + now rewrite <-Eyss.
    + now rewrite <-Exss.
    + apply Forall_impl with (P:=sem_equation G H (clocks_of xss)); auto.
      intro; now rewrite Exss.
  Qed.

End NLCOINDSEMANTICS.

Module NLCoindSemanticsFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS        Ids Op OpAux)
       (CESyn : CESYNTAX      Ids Op OpAux Cks)
       (Syn   : NLSYNTAX      Ids Op OpAux Cks CESyn)
       (Str   : COINDSTREAMS  Ids Op OpAux Cks)
       (Ord   : NLORDERED     Ids Op OpAux Cks CESyn Syn)
<: NLCOINDSEMANTICS Ids Op OpAux Cks CESyn Syn Str Ord.
  Include NLCOINDSEMANTICS Ids Op OpAux Cks CESyn Syn Str Ord.
End NLCoindSemanticsFun.
