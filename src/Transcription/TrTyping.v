From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import Transcription.Transcription.

From Velus Require Import Lustre.LTyping.
From Velus Require Import CoreExpr.CETyping.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.NLTyping.

From Coq Require Import String.
From Coq Require Import Permutation.

From Coq Require Import List.
Import List.ListNotations.

From compcert Require Import common.Errors.
Open Scope error_monad_scope.

(** * Typing Preservation for Transcription *)

Module Type TRTYPING
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import OpAux: OPERATORS_AUX Op)
       (L           : LSYNTAX  Ids Op)
       (Import CE   : CESYNTAX     Op)
       (NL          : NLSYNTAX Ids Op CE)
       (Import TR   : TRANSCRIPTION Ids Op OpAux L CE NL)
       (Ord         : NLORDERED Ids Op CE     NL)
       (LT          : LTYPING  Ids Op L)
       (CET         : CETYPING Ids Op CE)
       (NLT         : NLTYPING  Ids Op CE NL Ord CET).

  (* TODO: common? *)
  Ltac simpl_Foralls :=
    repeat
      match goal with
      | H: Forall _ [] |- _ => inv H
      | H: Forall _ [_] |- _ => inv H
      | H: Forall _ (_::_) |- _ => inv H
      | H: Forall2 _ [_] _ |- _ => inv H
      | H: Forall2 _ [] _ |- _ => inv H
      | H: Forall2 _ _ [_] |- _ => inv H
      | H: Forall2 _ _ [] |- _ => inv H
      end.

  Definition envs_eq (env : Env.t (type * clock))
             (tenv : list (ident * type)) :=
    forall (x : ident) (ty : type),
      In (x,ty) tenv <-> exists ck, Env.find x env = Some (ty,ck).

  Lemma wt_clock_l_ce :
    forall vars ck,
      LT.wt_clock vars ck -> CET.wt_clock vars ck.
  Proof.
    induction ck; intros * H; inv H; constructor; eauto.
  Qed.

  Lemma typeof_lexp :
    forall G vars e e' ty,
      to_lexp e = OK e' ->
      LT.wt_exp G vars e ->
      L.typeof e = [ty] ->
      typeof e' = ty.
  Proof.
    intros * Htr Hwt Hty. revert dependent e'. revert dependent ty.
    induction e using L.exp_ind2; intros; inv Htr; inv Hty; simpl; auto.
    - cases.
    - cases. now monadInv H0.
    - cases. now monadInv H0.
    - cases. inv H. monadInv H1. simpl in *. inv Hwt. simpl_Foralls.
      take (L.typesof _ = _) and inversion it as [Ht].
      rewrite app_nil_r in Ht.
      take ([_] = [_]) and inv it.
      eauto.
  Qed.

  Lemma typeofc_cexp :
    forall G vars e e' ty,
      to_cexp e = OK e' ->
      LT.wt_exp G vars e ->
      L.typeof e = [ty] ->
      CET.typeofc e' = ty.
  Proof.
    intros * Htr Hwt Hty. revert dependent e'. revert dependent ty.
    induction e using L.exp_ind2; intros; inv Htr; inv Hty; simpl; auto.
    - cases.
    - cases. monadInv H0. monadInv EQ. now simpl.
    - cases. monadInv H0. monadInv EQ. now simpl.
    - cases. monadInv H1. monadInv EQ. simpl in *. inv Hwt.
      take (L.typesof _ = _) and inversion it as [Ht].
      rewrite app_nil_r in Ht.
      take ([_] = [_]) and inv it.
      simpl_Foralls. eauto using typeof_lexp.
    - cases. monadInv H2. simpl_Foralls. inv Hwt.
      simpl in *. take ([_] = [_]) and inv it.
      rewrite app_nil_r in *. simpl_Foralls. eauto.
    - cases. monadInv H2. simpl_Foralls. inv Hwt.
      simpl in *. take ([_] = [_]) and inv it.
      rewrite app_nil_r in *. simpl_Foralls. eauto.
  Qed.

  Lemma wt_lexp :
    forall G vars e e',
      to_lexp e = OK e' ->
      LT.wt_exp G vars e ->
      CET.wt_lexp vars e'.
  Proof.
    intros * Htr Hwt. revert dependent e'.
    induction e using L.exp_ind2; intros; try (now inv Htr); inv Hwt.
    - inv Htr. now constructor.
    - monadInv Htr. constructor; eauto. eapply typeof_lexp in EQ as ->; eauto.
    - monadInv Htr. constructor; eauto.
      eapply typeof_lexp in EQ as ->; eauto.
      eapply typeof_lexp in EQ1 as ->; eauto.
    - inv Htr. cases. monadInv H1. inv H. inv H4. constructor; auto.
  Qed.

  Lemma wt_cexp :
    forall G vars e e',
      to_cexp e = OK e' ->
      LT.wt_exp G vars e ->
      CET.wt_cexp vars e'.
  Proof.
    intros * Htr Hwt. revert dependent e'.
    induction e using L.exp_ind2; intros; try (now inv Htr); inv Hwt.
    - inv Htr. now constructor.
    - monadInv Htr. constructor; eauto.
    - monadInv Htr. monadInv EQ. constructor.
      constructor; eauto using wt_lexp.
      eapply typeof_lexp in EQ0 as ->; eauto.
    - monadInv Htr. monadInv EQ. constructor.
      constructor; eauto using wt_lexp.
      eapply typeof_lexp in EQ0 as ->; eauto.
      eapply typeof_lexp in EQ as ->; eauto.
    - monadInv Htr. cases. monadInv EQ.
      constructor. simpl_Foralls. constructor; eauto using wt_lexp.
    - inv Htr. cases_eqn Hb. monadInv H2. simpl_Foralls.
      constructor; eauto.
      do 2 take (L.typesof _ = _) and inv it.
      rewrite app_nil_r in *.
      erewrite 2 typeofc_cexp; eauto.
    - inv Htr. cases_eqn Hb. monadInv H2. simpl_Foralls.
      constructor; eauto using wt_lexp, typeof_lexp.
      do 2 take (L.typesof _ = _) and inv it.
      rewrite app_nil_r in *.
      erewrite 2 typeofc_cexp; eauto.
  Qed.

  (* TODO: duplicated from Correctness *)
  Lemma ty_lexp :
    forall G env e e',
      LT.wt_exp G env e ->
      to_lexp e = OK e' ->
      L.typeof e = [CE.typeof e'].
  Proof.
    induction e using L.exp_ind2; intros * Hwt Htr; inv Htr.
    - now simpl.
    - destruct a. inv H0. now simpl.
    - destruct a. simpl. monadInv H0. now simpl.
    - destruct a. monadInv H0. now simpl.
    - cases. inv H. simpl. inv Hwt. inv H8. inv H6. monadInv H1.
      unfold L.typesof. unfold flat_map. simpl. rewrite app_nil_r.
      now apply H3.
  Qed.

  Lemma typeof_const :
    forall G vars e e' ty,
      to_constant e = OK e' ->
      LT.wt_exp G vars e ->
      L.typeof e = [ty] ->
      type_const e' = ty.
  Proof.
    induction e using L.exp_ind2; inversion 1; simpl; intros Hwt Hty.
    - now inv Hty.
    - cases. simpl_Foralls. inv H0. inv Hwt. simpl in Hty.
      rewrite app_nil_r in *. simpl_Foralls. eauto.
  Qed.

  Lemma wt_clock_free:
    forall vars ck,
      (forall i, Is_free_in_clock i ck ->
            In (i, bool_type) vars) <->
      LT.wt_clock vars ck.
  Proof.
    split.
    - intros * H. induction ck; constructor.
      + apply H. constructor.
      + apply IHck. intros. apply H. now constructor.
    - intros * Hwt i Hfr. induction Hfr. now inv Hwt.
      inv Hwt. inv Hfr; eauto.
  Qed.

  Lemma free_suffix_of_clock :
    forall x ck,
      InMembers x (suffix_of_clock ck []) ->
      Is_free_in_clock x ck.
  Proof.
    induction ck; simpl. tauto.
    intro Hmem.
    setoid_rewrite <- app_nil_l in Hmem at 2.
    rewrite suffix_of_clock_app, InMembers_app in Hmem. destruct Hmem.
    - constructor; auto.
    - simpl in H. intuition. subst. constructor.
  Qed.

  Lemma free_clock_of_suffix :
    forall i ck sfx,
      Is_free_in_clock i (clock_of_suffix sfx ck) ->
      Is_free_in_clock i ck \/ InMembers i sfx.
  Proof.
    intros * Hfr. revert dependent ck.
    induction sfx as [| []]; simpl; auto. intros.
    specialize (IHsfx _ Hfr) as [Hd|]; auto.
    inv Hd; auto.
  Qed.

  Lemma in_common_suffix :
    forall x sfx1 sfx2,
    InMembers x (common_suffix sfx1 sfx2) ->
    InMembers x sfx1.
  Proof.
    intros * Hmem.
    revert dependent sfx2. induction sfx1 as [|[]]; simpl; intros; auto.
    cases. inv Hmem; eauto.
  Qed.

  Lemma split_fold :
    forall i sfx sfxs,
    InMembers i (fold_left common_suffix sfxs sfx) ->
    InMembers i sfx \/ Exists (InMembers i) sfxs.
  Proof.
    intros * Hmem. revert dependent sfx.
    induction sfxs; simpl; intros * Hmem; auto.
    specialize (IHsfxs _ Hmem) as []; eauto using in_common_suffix.
  Qed.

  Lemma free_find_base_clock :
    forall i lck,
      Is_free_in_clock i (find_base_clock lck) ->
      Exists (Is_free_in_clock i) lck.
  Proof.
    intros * Hfr.
    unfold find_base_clock in Hfr. cases. induction lck; simpl in *.
    - rewrite clock_of_suffix_of_clock in Hfr. now constructor.
    - apply free_clock_of_suffix in Hfr as [Hfr | Hfr]; try inv Hfr.
      rewrite <- fold_left_map in Hfr, IHlck.
      apply split_fold in Hfr as [Hfr|Hfr];
        eauto using free_suffix_of_clock, in_common_suffix.
      right. right.
      apply Exists_exists in Hfr as (?& Hin &?).
      apply in_map_iff in Hin as (?&?&?). subst.
      eapply Exists_exists; eauto using free_suffix_of_clock.
  Qed.

  Lemma wc_find_base_clock :
    forall vars lck,
    Forall (LT.wt_clock vars) lck ->
    LT.wt_clock vars (find_base_clock lck).
  Proof.
    intros * Hwt.
    apply wt_clock_free. intros ? Hfr.
    apply free_find_base_clock in Hfr.
    apply Exists_exists in Hfr as (?& Hin & Hfr).
    pose proof (In_Forall _ _ _ Hwt Hin) as Wt.
    eapply wt_clock_free in Wt; eauto.
  Qed.

  Lemma wt_clockof :
    forall G vars e,
      LT.wt_exp G vars e ->
      Forall (LT.wt_clock vars) (L.clockof e).
  Proof.
    induction e using L.exp_ind2; simpl; intro Hwt; inv Hwt.
    - repeat constructor.
    - repeat constructor. unfold L.ckstream, stripname. simpl.
      now take (LT.wt_nclock _ _) and inv it.
    - repeat constructor. unfold L.ckstream, stripname. simpl.
      now take (LT.wt_nclock _ _) and inv it.
    - repeat constructor. unfold L.ckstream, stripname. simpl.
      now take (LT.wt_nclock _ _) and inv it.
    - rewrite Forall_map. rewrite Forall_map in H8.
      eapply Forall_impl_In; eauto. intros * Hin ?.
      eapply In_Forall in Hin; eauto. simpl in Hin.
      unfold L.ckstream, stripname. simpl in *. now inv Hin.
    - unfold L.ckstream, stripname. simpl in *.
      take (LT.wt_nclock _ _) and rename it into Hn. clear - Hn.
      induction (L.typesof es); simpl; auto. inv Hn. constructor; auto.
    - unfold L.ckstream, stripname. simpl in *.
      take (LT.wt_nclock _ _) and rename it into Hn. clear - Hn.
      induction (L.typesof ets); simpl; auto. inv Hn. constructor; auto.
    - unfold L.ckstream, stripname. simpl in *.
      take (LT.wt_nclock _ _) and rename it into Hn. clear - Hn.
      induction (L.typesof ets); simpl; auto. inv Hn. constructor; auto.
    - eapply Forall_map, Forall_impl_In; eauto. simpl. intros * ? Hn.
      unfold L.ckstream, stripname. now inv Hn.
  Qed.

  Lemma wt_equation :
    forall G P env envo vars e e',
      to_global G = OK P ->
      to_equation env envo e = OK e' ->
      (forall i ck, find_clock env i = OK ck -> LT.wt_clock vars ck) ->
      NoDup (fst e) ->
      LT.wt_equation G vars e ->
      NLT.wt_equation P vars e'.
  Proof.
    intros ????? [xs [|? []]] e' Hg Htr Henvs Hdup (Hwt & Hf2);
      try (inv Htr; cases; discriminate).
    destruct e; simpl in *.
    - cases. monadInv Htr. inv Hf2. constructor; eauto using wt_clock_l_ce.
    - cases. monadInv Htr. inv Hf2. monadInv EQ1. monadInv EQ0.
      constructor; eauto using wt_clock_l_ce. inversion_clear Hwt as [|?? Wt].
      inv Wt. constructor. constructor. assumption.
    - cases. monadInv Htr. inv Hf2. monadInv EQ1. monadInv EQ0.
      constructor; eauto using wt_clock_l_ce. inversion_clear Hwt as [|?? Wt].
      inv Wt. constructor. constructor; eauto using wt_lexp.
      eapply typeof_lexp in EQ1 as ->; eauto.
    - cases. monadInv Htr. inv Hf2. monadInv EQ1. monadInv EQ0.
      constructor; eauto using wt_clock_l_ce. inversion_clear Hwt as [|?? Wt].
      inv Wt. constructor. constructor; eauto using wt_lexp.
      eapply typeof_lexp in EQ1 as ->; eauto.
      eapply typeof_lexp in EQ0 as ->; eauto.
    - cases; monadInv Htr.
      simpl_Foralls. take (LT.wt_exp _ _ _) and inv it. simpl_Foralls.
      simpl in *. rewrite app_nil_r in *.
      take ([_] = _) and rewrite <- it in *.
      constructor; eauto using wt_clock_l_ce, wt_lexp.
      erewrite typeof_const; eauto.
      erewrite typeof_const; eauto. erewrite typeof_lexp; eauto.
    - cases; monadInv Htr; monadInv EQ1; try discriminate.
      monadInv EQ0.
      simpl_Foralls. take (LT.wt_exp _ _ _) and inv it. simpl_Foralls.
      take (L.typesof _ = _) and inversion it as [Ht].
      rewrite app_nil_r in Ht.
      constructor; eauto using wt_clock_l_ce; simpl in *.
      + eapply typeof_lexp in EQ1 as ->; eauto.
      + constructor. constructor; eauto using wt_lexp.
    - cases; monadInv Htr; monadInv EQ1; try discriminate.
      constructor; eauto using wt_clock_l_ce.
      + rewrite app_nil_r in *. simpl in *. simpl_Foralls. inv H1.
        simpl_Foralls.
        do 2 take (L.typesof _ = _) and inv it.
        rewrite app_nil_r in *.
        erewrite typeofc_cexp; eauto.
      + simpl_Foralls. take (LT.wt_exp _ _ _ ) and inv it. simpl_Foralls.
        constructor; eauto using wt_cexp.
        do 2 take (L.typesof _ = _) and inv it.
        rewrite app_nil_r in *.
        erewrite 2 typeofc_cexp; eauto.
    - cases; monadInv Htr; monadInv EQ1; try discriminate. simpl_Foralls.
      take (LT.wt_exp _ _ _) and inv it. simpl_Foralls.
      constructor; eauto using wt_clock_l_ce; simpl in *.
      + rewrite app_nil_r in *.
        erewrite typeofc_cexp; eauto.
      + constructor; eauto using wt_cexp, wt_lexp.
        erewrite typeof_lexp; eauto.
        rewrite app_nil_r in *.
        erewrite 2 typeofc_cexp; eauto.
    - simpl_Foralls. take (LT.wt_exp _ _ _) and inv it.
      eapply find_node_global in Hg as (?&?&?); eauto.
      rewrite app_nil_r in Hf2.
      cases; monadInv Htr.
      (* TODO: ici cases génère trois sous-buts alors que deux suffiraient...
         les deux denières puces sont identiques *)
      + inv Hf2. symmetry in H1. apply map_eq_nil in H1. subst.
        simpl_Foralls. pose proof (L.n_outgt0 n).
        symmetry in H1. apply length_zero_iff_nil in H1.
        intuition.
      + apply mmap_inversion in EQ.
        econstructor; eauto.
        ++ rewrite <- (to_node_out n); auto. rewrite Forall2_map_2 in Hf2.
           apply Forall2_forall. split.
           2:{ apply Forall2_length in Hf2. apply Forall2_length in H5.
               congruence. }
           intros * Hin.
           eapply Forall2_chain_In in Hin; eauto.
           now destruct Hin as (?&?& <-).
        ++ rewrite <- (to_node_in n); auto.
           clear - H2 H4 EQ.
           remember (L.n_in n). clear Heql0. revert dependent l0.
           revert dependent x0.
           induction l; intros; inv EQ; auto.
           inv H4; auto.
           simpl_Foralls. eapply ty_lexp in H1; eauto. simpl in *.
           rewrite H1 in H4. inv H4.
           constructor; eauto.
        ++ apply wt_clock_l_ce, wc_find_base_clock.
           clear - H2.
           induction l; simpl; auto. inv H2. apply Forall_app.
           eauto using wt_clockof.
        ++ clear H4. revert dependent l. induction x0; intros; auto.
           inv EQ. simpl_Foralls.
           constructor; eauto using wt_lexp.
      + apply mmap_inversion in EQ.
        econstructor; eauto.
        ++ rewrite <- (to_node_out n); auto. rewrite Forall2_map_2 in Hf2.
           apply Forall2_forall. split.
           2:{ apply Forall2_length in Hf2. apply Forall2_length in H5.
               congruence. }
           intros * Hin.
           eapply Forall2_chain_In in Hin; eauto.
           now destruct Hin as (?&?& <-).
        ++ rewrite <- (to_node_in n); auto.
           clear - H2 H4 EQ.
           remember (L.n_in n). clear Heql0. revert dependent l0.
           revert dependent x0.
           induction l; intros; inv EQ; auto.
           inv H4; auto.
           simpl_Foralls. eapply ty_lexp in H1; eauto. simpl in *.
           rewrite H1 in H4. inv H4.
           constructor; eauto.
        ++ apply wt_clock_l_ce, wc_find_base_clock.
           clear - H2.
           induction l; simpl; auto. inv H2. apply Forall_app.
           eauto using wt_clockof.
        ++ clear H4. revert dependent l. induction x0; intros; auto.
           inv EQ. simpl_Foralls.
           constructor; eauto using wt_lexp.
  Qed.

  (* TODO: move to Environment, duplicated from Correctness *)
  Lemma env_find_env_from_list':
    forall {A} x (v: A) xs s,
      Env.find x (Env.adds' xs s) = Some v
      -> In (x, v) xs \/ (~InMembers x xs /\ Env.find x s = Some v).
  Proof.
    induction xs as [|(x', v') xs IH]; simpl. now intuition.
    intros s Hfind. apply IH in Hfind as [|(Hnim & Hfind)]; auto.
    destruct (ident_eq_dec x' x).
    + subst. rewrite Env.gss in Hfind.
      injection Hfind. intro; subst; auto.
    + rewrite Env.gso in Hfind; intuition.
  Qed.

  (* TODO: duplicated from Correctness *)
  Lemma in_app_weak :
    forall {A} (x : A) l l',
      In x l -> In x (l ++ l').
  Proof.
    intros. apply in_app; auto.
  Qed.

  Lemma wt_clock_app :
    forall ck l l',
      LT.wt_clock l ck -> LT.wt_clock (l ++ l') ck.
  Proof.
    intros * Hwt.
    induction ck; auto with ltyping.
    constructor; inv Hwt; eauto using in_app_weak.
  Qed.

  Lemma wt_node :
    forall G P n n',
      to_node n = OK n' ->
      to_global G = OK P ->
      LT.wt_node G n ->
      NLT.wt_node P n'.
  Proof.
    intros * Htr Hg (Wti& Wto & Wtv & Hwt).
    tonodeInv Htr. unfold NLT.wt_node. simpl.
    pose proof (L.NoDup_vars_defined_n_eqs n) as Hdup.
    revert dependent x.
    induction (L.n_eqs n); intros; monadInv Hmmap.
    - now take (Coqlib.list_forall2 _ _ _) and inv it.
    - take (Coqlib.list_forall2 _ _ _) and inv it.
      inv Hwt. apply mmap_cons3 in Hmmap as [].
      simpl in Hdup. apply NoDup_app'_iff in Hdup as (?&?&?).
      constructor; auto. eapply wt_equation; eauto.

      intros i ck Hfind.
      unfold find_clock in Hfind.
      cases_eqn Hfind. inv Hfind.
      apply env_find_env_from_list' in Hfind0 as [Hin|[? Hfind]].
      pose proof (In_Forall _ _ _ Wtv Hin) as Wt. unfold dck in Wt.
      simpl in Wt. now setoid_rewrite Permutation_app_comm in Wt at 2.
      apply env_find_env_from_list' in Hfind as [Hin|[? Hfind]].
      pose proof (In_Forall _ _ _ Wti Hin) as Wt. unfold dck in Wt.
      simpl in Wt. unfold idty. rewrite map_app.
      eapply wt_clock_app in Wt; eauto.
      apply Env.from_list_find_In in Hfind as Hin.
      pose proof (In_Forall _ _ _ Wto Hin) as Wt. unfold dck in Wt.
      simpl in Wt. setoid_rewrite Permutation_app_comm at 2.
      eapply wt_clock_app in Wt; eauto. unfold idty.
      rewrite app_assoc, map_app. eauto.
  Qed.

  Lemma wt_transcription :
    forall G P,
      LT.wt_global G ->
      to_global G = OK P ->
      NLT.wt_global P.
  Proof.
    induction G as [| n]. inversion 2. constructor.
    intros * Hwt Htr. monadInv Htr. inversion H as [|?? n' ?? Hn]. subst.
    inversion_clear Hwt as [|???? Hf ].
    apply mmap_cons3 in Htr as [].
    constructor; eauto using wt_node.
    rewrite (to_node_name n n') in Hf; auto.
    clear - Hf Hn. induction Hn as [|m ? m']; auto. inv Hf.
    constructor; auto. rewrite <- (to_node_name m m'); auto.
  Qed.

End TRTYPING.

Module TrTypingFun
       (Ids  : IDS)
       (Op   : OPERATORS)
       (OpAux: OPERATORS_AUX Op)
       (L    : LSYNTAX  Ids Op)
       (CE   : CESYNTAX     Op)
       (NL   : NLSYNTAX Ids Op CE)
       (TR   : TRANSCRIPTION Ids Op OpAux L CE NL)
       (Ord  : NLORDERED Ids Op CE     NL)
       (LT   : LTYPING  Ids Op L)
       (CET  : CETYPING Ids Op CE)
       (NLT  : NLTYPING  Ids Op CE NL Ord CET)
<: TRTYPING Ids Op OpAux L CE NL TR Ord LT CET NLT.
  Include TRTYPING Ids Op OpAux L CE NL TR Ord LT CET NLT.
End TrTypingFun.
