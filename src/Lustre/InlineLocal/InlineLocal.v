From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import CommonTyping.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Fresh.
From Velus Require Import StaticEnv.
From Velus Require Import Lustre.LSyntax.

(** * Remove Local Blocks *)

Module Type INLINELOCAL
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv).

  (** ** Rename some variables *)

  Section rename.
    Variable sub : Env.t ident.

    Definition rename_var (x : ident) :=
      or_default x (Env.find x sub).

    Fixpoint rename_clock (ck : clock) :=
      match ck with
      | Cbase => Cbase
      | Con ck' x t => Con (rename_clock ck') (rename_var x) t
      end.

    Definition rename_nclock (nck : nclock) :=
      (rename_clock (fst nck), option_map rename_var (snd nck)).

    Definition rename_ann {A} (ann : (A * clock)) :=
      (fst ann, rename_clock (snd ann)).

    Fixpoint rename_exp (e : exp) :=
      match e with
      | Econst _ | Eenum _ _ => e
      | Evar x ann => Evar (rename_var x) (rename_ann ann)
      | Elast x ann => Elast (rename_var x) (rename_ann ann)
      | Eunop op e1 ann => Eunop op (rename_exp e1) (rename_ann ann)
      | Ebinop op e1 e2 ann => Ebinop op (rename_exp e1) (rename_exp e2) (rename_ann ann)
      | Eextcall f es (tyout, ck) => Eextcall f (map rename_exp es) (tyout, rename_clock ck)
      | Efby e0s e1s anns => Efby (map rename_exp e0s) (map rename_exp e1s) (map rename_ann anns)
      | Earrow e0s e1s anns => Earrow (map rename_exp e0s) (map rename_exp e1s) (map rename_ann anns)
      | Ewhen es (x, tx) t ann => Ewhen (map rename_exp es) (rename_var x, tx) t (rename_ann ann)
      | Emerge (x, ty) es ann => Emerge (rename_var x, ty) (map (fun '(i, es) => (i, map rename_exp es)) es) (rename_ann ann)
      | Ecase e es d ann =>
        Ecase (rename_exp e) (map (fun '(i, es) => (i, map rename_exp es)) es) (option_map (map rename_exp) d) (rename_ann ann)
      | Eapp f es er ann => Eapp f (map rename_exp es) (map rename_exp er) (map rename_ann ann)
      end.

    Definition rename_equation '(xs, es) : equation :=
      (map rename_var xs, map rename_exp es).

    (** *** Properties *)

    Lemma rename_ann_clock {A} : forall (ann : (A * clock)),
        snd (rename_ann ann) = rename_clock (snd ann).
    Proof. reflexivity. Qed.

    Corollary map_rename_ann_clock {A} : forall (anns : list (A * clock)),
        map snd (map rename_ann anns) = map rename_clock (map snd anns).
    Proof.
      induction anns; simpl; auto.
    Qed.

    Lemma map_rename_ann_type {A} : forall (anns : list (A * clock)),
        map fst (map rename_ann anns) = map fst anns.
    Proof.
      induction anns; simpl; auto.
    Qed.

  End rename.

  Section rename_clockof.

    Variable sub : Env.t ident.

    Lemma rename_exp_nclockof : forall e,
        nclockof (rename_exp sub e) = map (rename_nclock sub) (nclockof e).
    Proof.
      destruct e; destruct_conjs; simpl in *; rewrite ? map_map; auto.
    Qed.

    Corollary rename_exp_nclocksof : forall es,
        nclocksof (map (rename_exp sub) es) = map (rename_nclock sub) (nclocksof es).
    Proof.
      intros es.
      unfold nclocksof. rewrite 2 flat_map_concat_map, concat_map, 2 map_map.
      f_equal.
      eapply map_ext; intros. apply rename_exp_nclockof.
    Qed.

    Corollary rename_exp_clockof : forall e,
        clockof (rename_exp sub e) = map (rename_clock sub) (clockof e).
    Proof.
      intros.
      rewrite 2 clockof_nclockof, rename_exp_nclockof, 2 map_map; auto.
    Qed.

    Corollary rename_exp_clocksof : forall es,
        clocksof (map (rename_exp sub) es) = map (rename_clock sub) (clocksof es).
    Proof.
      intros es.
      unfold clocksof. rewrite 2 flat_map_concat_map, concat_map, 2 map_map.
      f_equal.
      eapply map_ext; intros. apply rename_exp_clockof.
    Qed.

  End rename_clockof.

  Section rename_typeof.

    Variable bck : clock.
    Variable sub : Env.t ident.

    Lemma rename_exp_typeof : forall e,
        typeof (rename_exp sub e) = typeof e.
    Proof.
      destruct e; destruct_conjs; simpl in *; rewrite ? map_map; auto.
    Qed.

    Corollary rename_exp_typesof : forall es,
        typesof (map (rename_exp sub) es) = typesof es.
    Proof.
      intros es.
      unfold typesof . rewrite 2 flat_map_concat_map, map_map.
      f_equal.
      eapply map_ext; intros. apply rename_exp_typeof.
    Qed.
  End rename_typeof.

  Section rename_empty.

    Fact rename_var_empty : forall x,
      rename_var (Env.empty _) x = x.
    Proof.
      intros. unfold rename_var.
      simpl. rewrite Env.gempty. reflexivity.
    Qed.

    Corollary rename_vars_empty : forall xs,
        map (rename_var (Env.empty _)) xs = xs.
    Proof.
      induction xs; simpl; f_equal; auto using rename_var_empty.
    Qed.

  End rename_empty.

  Lemma rename_var_IsLast sub Γ Γ' : forall x,
      (forall x y, Env.find x sub = Some y -> IsLast Γ x -> IsLast Γ' y) ->
      (forall x, Env.find x sub = None -> IsLast Γ x -> IsLast Γ' x) ->
      IsLast Γ x ->
      IsLast Γ' (rename_var sub x).
  Proof.
    unfold rename_var.
    intros * Sub NSub In.
    destruct (Env.find _ _) eqn:Hfind; simpl in *; eauto.
  Qed.

  (** ** More properties *)

  Fact not_in_union_rename2 : forall x sub ys zs,
      ~In x ys ->
      rename_var (Env.adds ys zs sub) x = rename_var sub x.
  Proof.
    unfold rename_var.
    intros * Hnin.
    destruct (Env.find x (Env.adds _ _ sub)) eqn:Hfind.
    - apply Env.find_adds'_In in Hfind as [Hfind|Hfind].
      + apply in_combine_l in Hfind. contradiction.
      + now rewrite Hfind.
    - apply Env.find_adds'_nIn in Hfind as (?&Hfind1).
      now rewrite Hfind1.
  Qed.

  Corollary not_in_union_map_rename2 : forall xs sub ys zs,
      Forall (fun x => ~In x ys) xs ->
      map (rename_var (Env.adds ys zs sub)) xs = map (rename_var sub) xs.
  Proof.
    induction xs; intros * Hf; inv Hf; simpl; f_equal; auto using not_in_union_rename2.
  Qed.

  Lemma disjoint_union_rename_var : forall (sub1: Env.t ident) xs ys x,
      (forall x, Env.In x sub1 -> ~In x xs) ->
      (forall x y, Env.MapsTo x y sub1 -> ~In y xs) ->
      rename_var (Env.from_list (combine xs ys)) (rename_var sub1 x) = rename_var (Env.adds xs ys sub1) x.
  Proof.
    unfold rename_var.
    intros * Hnin1 Hnin2.
    destruct (Env.find x (Env.adds _ _ _)) eqn:Hfind; simpl.
    - destruct (Env.find x sub1) eqn:Hfind1; simpl.
      + specialize (Hnin2 _ _ Hfind1).
        replace (Env.find i0 _) with (@None ident).
        2:{ symmetry. apply Env.find_adds'_nIn.
            rewrite Env.gempty. split; auto.
            contradict Hnin2. eauto using InMembers_In_combine. }
        simpl.
        setoid_rewrite Env.gsso' in Hfind. congruence.
        intros ?. eapply Hnin1; eauto using InMembers_In_combine. econstructor; eauto.
      + unfold Env.from_list.
        erewrite Env.find_gsss'_irrelevant; eauto. auto.
        apply Env.find_adds'_In in Hfind as [Hfind|Hfind]; try congruence.
        eauto using In_InMembers.
    - eapply Env.find_adds'_nIn in Hfind as (Hfind1&Hfind2).
      rewrite Hfind2; simpl.
      replace (Env.find x _) with (@None ident); auto.
      symmetry. apply Env.find_adds'_nIn.
      rewrite Env.gempty. auto.
  Qed.

  Corollary disjoint_union_rename_in_clock : forall (sub1: Env.t ident) xs ys ck,
      (forall x, Env.In x sub1 -> ~In x xs) ->
      (forall x y, Env.MapsTo x y sub1 -> ~In y xs) ->
      rename_clock (Env.from_list (combine xs ys)) (rename_clock sub1 ck) = rename_clock (Env.adds xs ys sub1) ck.
  Proof.
    intros * Hsub1 Hsub2.
    induction ck; simpl; auto.
    f_equal; auto using disjoint_union_rename_var.
  Qed.

  (** ** Inlining of local blocks *)

  Module Fresh := Fresh.Fresh(Ids).
  Import Fresh Notations Facts Tactics.

  (* Be your own, personal, monad *)
  Record reuse_st := {
      fresh_st: fresh_st local unit; (* We dont actually need to keep type information in here *)
      used: PS.t; (* Identifiers already used *)
    }.

  Definition Reuse A := reuse_st -> (A * reuse_st).

  Definition reuse_ident (x : ident) : Reuse ident :=
    fun st =>
      if PS.mem x st.(used) then
        let (y, st') := fresh_ident (Some x) tt st.(fresh_st) in
        (y, {| fresh_st := st'; used := st.(used) |})
      else
        (x, {| fresh_st := st.(fresh_st); used := PS.add x st.(used) |}).

  Section ret.
    Context {A : Type}.
    Definition ret (x : A) : Reuse A := fun st => (x, st).

    Fact ret_spec : forall a st,
        ret a st = (a, st).
    Proof.
      intros a st. reflexivity.
    Qed.
  End ret.

  Section bind.
    Context {A B : Type}.
    Definition bind (x : Reuse A) (k : A -> Reuse B) : Reuse B :=
      fun st => let '(a, st') := x st in k a st'.

    Lemma bind_spec : forall (x : Reuse A) (k : A -> Reuse B) st a' st'',
        (bind x k) st = (a', st'') <->
        exists a, exists st', (x st = (a, st') /\ k a st' = (a', st'')).
    Proof.
      intros x k st a' st''. split; intros.
      - unfold bind in H.
        destruct (x st) as [a st']. exists a. exists st'.
        split; auto.
      - destruct H as [a [st' [H1 H2]]]. unfold bind.
        rewrite H1. assumption.
    Qed.
  End bind.

  Section bind2.
    Context {A1 A2 B : Type}.
    Definition bind2 (x : Reuse (A1 * A2)) (k : A1 -> A2 -> Reuse B) : Reuse B :=
      fun st => let '((a1, a2), st') := x st in k a1 a2 st'.

    Lemma bind2_spec : forall (x : Reuse (A1 * A2)) (k : A1 -> A2 -> Reuse B) st a' st'',
        (bind2 x k) st = (a', st'') <->
          exists a1, exists a2, exists st', (x st = ((a1, a2), st') /\ k a1 a2 st' = (a', st'')).
    Proof.
      intros x k st a' st''. split; intros.
      - unfold bind2 in H.
        destruct (x st) as [[a1 a2] st']. exists a1. exists a2. exists st'.
        split; auto.
      - destruct H as [a1 [a2 [st' [H1 H2]]]]. unfold bind2.
        rewrite H1. assumption.
    Qed.
  End bind2.

  Definition st_In x (st : reuse_st) :=
    In x (st_ids (fresh_st st)) \/ PS.In x (used st).

  Definition st_valid (st : reuse_st) :=
    PS.For_all (AtomOrGensym switch_prefs) (used st).

  Definition st_follows (st1 st2 : reuse_st) :=
    st_follows (fresh_st st1) (fresh_st st2) /\ PS.Subset (used st1) (used st2).

  Global Instance st_follows_Reflexive : Reflexive st_follows.
  Proof. split; reflexivity. Qed.
  Global Instance st_follows_Transitive : Transitive st_follows.
  Proof. intros ??? (?&?) (?&?). split; etransitivity; eauto. Qed.

  Lemma st_follows_In : forall st1 st2,
      st_follows st1 st2 ->
      forall x, st_In x st1 -> st_In x st2.
  Proof.
    intros * (F1&F2) ? [In|In]; [left|right]; eauto.
    eapply incl_map; eauto using st_follows_incl.
  Qed.

  Declare Scope reuse_monad_scope.
  Notation "'do' X <- A ; B" :=
    (bind A (fun X => B))
      (at level 200, X name, A at level 100, B at level 200): reuse_monad_scope.
  Notation "'do' ( X , Y ) <- A ; B" :=
    (bind2 A (fun X Y => B))
      (at level 200, X name, Y name, A at level 100, B at level 200): reuse_monad_scope.
  Open Scope reuse_monad_scope.

  Ltac monadInv :=
    simpl in *;
    match goal with
    | H : context c [ret _ _] |- _ =>
        rewrite ret_spec in H
    | H : (_, _) = (_, _) |- _ =>
        inv H
    | H : bind _ _ _ = (_, _) |- _ =>
        apply bind_spec in H; destruct H as [? [? [? ?]]]; simpl in *
    | H : bind2 _ _ _ = (_, _) |- _ =>
        apply bind2_spec in H; destruct H as [? [? [? [? ?]]]]; simpl in *
    | |- context c [ret _ _] =>
        rewrite ret_spec
    | |- bind _ _ _ = (_, _) =>
        rewrite bind_spec; repeat esplit
    | |- bind2 _ _ _ = (_, _) =>
        rewrite bind2_spec; repeat esplit
    end.

  Section mmap.
    Context {A B : Type}.
    Variable k : A -> Reuse B.
    Fixpoint mmap a :=
      match a with
      | nil => ret nil
      | hd::tl => do a1 <- k hd;
                do a1s <- mmap tl;
                ret (a1::a1s)
      end.

    Fact mmap_values : forall a st a1s st',
        mmap a st = (a1s, st') ->
        Forall2 (fun a a1 => exists st'', exists st''', k a st'' = (a1, st''')) a a1s.
    Proof.
      induction a; intros st a1s st' Hfold; simpl in *; repeat monadInv.
      - constructor.
      - specialize (IHa _ _ _ H0).
        constructor; eauto.
    Qed.

    Fact mmap_st_valid : forall a a1s st st',
        mmap a st = (a1s, st') ->
        Forall (fun a => forall a1 st st', k a st = (a1, st') -> st_valid st -> st_valid st') a ->
        st_valid st ->
        st_valid st'.
    Proof.
      induction a; intros * Hmap F Val; inv F; repeat monadInv; eauto.
    Qed.

    Fact mmap_st_follows : forall a a1s st st',
        mmap a st = (a1s, st') ->
        Forall (fun a => forall a1 st st', k a st = (a1, st') -> st_follows st st') a ->
        st_follows st st'.
    Proof.
      induction a; intros * Hmap F; inv F; repeat monadInv; auto.
      - reflexivity.
      - etransitivity; eauto.
    Qed.

    Fact mmap_values_follows : forall a st a1s st',
        (forall a a1 st st', k a st = (a1, st') -> st_follows st st') ->
        mmap a st = (a1s, st') ->
        Forall2 (fun a a1 =>
                   exists st'' st''',
                     st_follows st st''
                     /\ st_follows st''' st'
                     /\ k a st'' = (a1, st''')) a a1s.
    Proof.
      induction a; intros * Follows Hfold; repeat monadInv.
      - constructor.
      - constructor.
        + do 2 esplit; split; [|split]. 3:eauto. reflexivity.
          eapply mmap_st_follows; eauto. simpl_Forall; eauto.
        + eapply IHa in H0; eauto.
          simpl_Forall.
          do 2 esplit; split; [|split]. 3:eauto. 2:eauto. etransitivity; eauto.
    Qed.

    Fact mmap_values' : forall a st a1s st',
        Forall (fun a => forall a1 st st', k a st = (a1, st') -> st_valid st -> st_valid st') a ->
        (forall a a1 st st', k a st = (a1, st') -> st_follows st st') ->
        mmap a st = (a1s, st') ->
        st_valid st ->
        Forall2 (fun a a1 =>
                   exists st'' st''',
                     st_valid st''
                     /\ st_follows st st''
                     /\ st_follows st''' st'
                     /\ k a st'' = (a1, st''')) a a1s.
    Proof.
      induction a; intros * Valid Follows Hfold V; inv Valid; repeat monadInv.
      - constructor.
      - constructor.
        + do 2 esplit; split; [|split; [|split]]. 1,4:eauto. reflexivity.
          eapply mmap_st_follows; eauto. simpl_Forall; eauto.
        + eapply IHa in H0; eauto.
          simpl_Forall.
          do 2 esplit; split; [|split; [|split]]. 1,4:eauto. 2:eauto. etransitivity; eauto.
    Qed.
  End mmap.

  Section mmap2.
    Context {A A1 A2 : Type}.
    Variable k : A -> Reuse (A1 * A2).
    Fixpoint mmap2 (a : list A) : Reuse (list A1 * list A2) :=
      match a with
      | nil => ret (nil, nil)
      | hd::tl => do (a1, a2) <- k hd;
                do (a1s, a2s) <- mmap2 tl;
                ret (a1::a1s, a2::a2s)
      end.

    Fact mmap2_values : forall a st a1s a2s st',
        mmap2 a st = (a1s, a2s, st') ->
        Forall3 (fun a a1 a2 => exists st'', exists st''', k a st'' = (a1, a2, st''')) a a1s a2s.
    Proof.
      induction a; intros st a1s a2s st' Hfold; simpl in *; repeat monadInv.
      - constructor.
      - specialize (IHa _ _ _ _ H0).
        constructor; eauto.
    Qed.

    Fact mmap2_st_valid : forall a a1s a2s st st',
        mmap2 a st = (a1s, a2s, st') ->
        Forall (fun a => forall a1 a2 st st', k a st = (a1, a2, st') -> st_valid st -> st_valid st') a ->
        st_valid st ->
        st_valid st'.
    Proof.
      induction a; intros a1s a2s st st' Hmap F; inv F; repeat monadInv; eauto.
    Qed.

    Fact mmap2_st_follows : forall a a1s a2s st st',
        mmap2 a st = (a1s, a2s, st') ->
        Forall (fun a => forall a1 a2 st st', k a st = (a1, a2, st') -> st_follows st st') a ->
        st_follows st st'.
    Proof.
      induction a; intros a1s a2s st st' Hmap F; inv F; repeat monadInv.
      - reflexivity.
      - etransitivity; eauto.
    Qed.

    Fact mmap2_values_follows : forall a st a1s a2s st',
        (forall a a1 a2 st st', k a st = (a1, a2, st') -> st_follows st st') ->
        mmap2 a st = (a1s, a2s, st') ->
        Forall3 (fun a a1 a2 =>
                   exists st'' st''',
                     st_follows st st''
                     /\ st_follows st''' st'
                     /\ k a st'' = (a1, a2, st''')) a a1s a2s.
    Proof.
      induction a; intros * Follows Hfold; simpl in *; repeat monadInv.
      - constructor.
      - constructor.
        + do 2 esplit; split; [|split]. 3:eauto. reflexivity.
          eapply mmap2_st_follows; eauto. simpl_Forall; eauto.
        + eapply IHa in H0; eauto.
          eapply Forall3_impl_In; [|eauto]. intros; destruct_conjs.
          do 2 esplit; split; [|split]. 3:eauto. 2:eauto. etransitivity; eauto.
    Qed.

    Fact mmap2_values' : forall a st a1s a2s st',
        Forall (fun a => forall a1 a2 st st', k a st = (a1, a2, st') -> st_valid st -> st_valid st') a ->
        (forall a a1 a2 st st', k a st = (a1, a2, st') -> st_follows st st') ->
        mmap2 a st = (a1s, a2s, st') ->
        st_valid st ->
        Forall3 (fun a a1 a2 =>
                   exists st'' st''',
                     st_valid st''
                     /\ st_follows st st''
                     /\ st_follows st''' st'
                     /\ k a st'' = (a1, a2, st''')) a a1s a2s.
    Proof.
      induction a; intros * Valid Follows Hfold V; inv Valid; repeat monadInv.
      - constructor.
      - constructor.
        + do 2 esplit; split; [|split; [|split]]. 1,4:eauto. reflexivity.
          eapply mmap2_st_follows; eauto. simpl_Forall; eauto.
        + eapply IHa in H0; eauto.
          eapply Forall3_impl_In; [|eauto]. intros; destruct_conjs.
          do 2 esplit; split; [|split; [|split]]. 1,4:eauto. 2:eauto. etransitivity; eauto.
    Qed.
  End mmap2.

  Fixpoint inlinelocal_block sub (blk : block) : Reuse (list decl * list block) :=
    match blk with
    | Beq eq => ret ([], [Beq (rename_equation sub eq)])
    | Blast x e => ret ([], [Blast (rename_var sub x) (rename_exp sub e)])
    | Breset blks er =>
        do (locs, blks') <- mmap2 (inlinelocal_block sub) blks;
        ret (concat locs, [Breset (concat blks') (rename_exp sub er)])
    | Blocal (Scope locs blks) =>
        let xs := map fst locs in
        do newlocs <- mmap reuse_ident xs;
        let sub' := Env.adds xs newlocs sub in
        let locs' := map (fun '(x, (ty, ck, cx, clx)) => (rename_var sub' x, (ty, (rename_clock sub' ck), cx, clx))) locs in
        do (locs1, blks') <- mmap2 (inlinelocal_block sub') blks;
        ret (locs'++concat locs1, concat blks')
    | _ => (* Should not happen *) ret ([], [blk])
    end.

  (** ** Wellformedness properties *)

  (** *** VarsDefinedComp *)

  Import Permutation.

  Fact mmap_vars_perm : forall (f : _ -> block -> Reuse (list decl * list block)) blks sub locs' blks' xs st st',
      Forall
        (fun blk => forall sub locs' blks' xs st st',
             noswitch_block blk ->
             VarsDefinedComp blk xs ->
             NoDupLocals (map fst (Env.elements sub) ++ xs) blk ->
             f sub blk st = (locs', blks', st') ->
             exists ys, Forall2 VarsDefinedComp blks' ys /\ Permutation (concat ys) (map (rename_var sub) xs ++ map fst locs')) blks ->
      Forall noswitch_block blks ->
      Forall2 VarsDefinedComp blks xs ->
      Forall (NoDupLocals (map fst (Env.elements sub) ++ concat xs)) blks ->
      mmap2 (f sub) blks st = (locs', blks', st') ->
      exists ys, Forall2 VarsDefinedComp (concat blks') ys /\ Permutation (concat ys) (map (rename_var sub) (concat xs) ++ map fst (concat locs')).
  Proof.
    induction blks; intros * Hf Hns Hvars Hnd Hnorm; inv Hf; inv Hns; inv Hvars; inv Hnd; repeat monadInv; simpl.
    - exists []. split; auto.
    - eapply H1 in H as (ys1&Hvars1&Hperm1); eauto.
      2:eapply NoDupLocals_incl; [|eauto]; solve_incl_app.
      eapply IHblks in H2 as (ys2&Hvars2&Hperm2); eauto. clear IHblks.
      2:simpl_Forall; intros; eapply NoDupLocals_incl; [|eauto]; solve_incl_app.
      exists (ys1 ++ ys2). split.
      + apply Forall2_app; auto.
      + rewrite concat_app, Hperm1, Hperm2. solve_Permutation_app.
  Qed.

  Lemma inlinelocal_block_vars_perm : forall blk sub locs' blks' xs st st',
      noswitch_block blk ->
      VarsDefinedComp blk xs ->
      NoDupLocals (map fst (Env.elements sub) ++ xs) blk ->
      inlinelocal_block sub blk st = (locs', blks', st') ->
      exists ys, Forall2 VarsDefinedComp blks' ys /\ Permutation (concat ys) (map (rename_var sub) xs ++ map fst locs').
  Proof.
    induction blk using block_ind2; intros * Hns Hvars Hnd Hdl;
      inv Hns; inv Hvars; inv Hnd; repeat monadInv.
    - (* equation *)
      destruct eq.
      repeat esplit; simpl; eauto using VarsDefinedComp with datatypes.
    - (* last *)
      simpl. repeat (econstructor; eauto).
    - (* reset *)
      eapply mmap_vars_perm in H0 as (ys1&Hvars1&Hperm1); eauto.
      do 2 esplit; eauto using VarsDefinedComp.
      simpl. now rewrite app_nil_r.
    - (* local *)
      repeat inv_scope. take (Permutation _ _) and rename it into Hperm.
      take (mmap2 _ _ _ = _) and eapply mmap_vars_perm in it as (ys1&Hvars1&Hperm1); eauto.
      2:{ simpl_Forall.
          eapply NoDupLocals_incl; [|eauto].
          rewrite <-app_assoc, Hperm.
          apply incl_app; try solve [solve_incl_app].
          intros ? Hin. simpl_In.
          eapply Env.elements_complete, Env.find_adds'_In in Hin0 as [Hfind|Hfind].
          - eapply in_combine_l in Hfind.
            rewrite 2 in_app_iff. auto.
          - eapply Env.elements_correct in Hfind.
            apply in_or_app, or_introl; solve_In.
      }
      rewrite Hperm, map_app in Hperm1.
      do 2 esplit; eauto. rewrite Hperm1, map_app, 2 map_map, <-app_assoc.
      erewrite not_in_union_map_rename2, map_ext with (l:=locs). reflexivity.
      + unfold decl. intros; destruct_conjs. reflexivity.
      + simpl_Forall. intros In. apply fst_InMembers in In.
        eapply H11; eauto with datatypes.
  Qed.

  (** *** LastsDefined *)

  Fact mmap_lasts_perm : forall (f : _ -> block -> Reuse (list decl * list block)) blks sub locs' blks' xs st st',
      Forall
        (fun blk => forall sub locs' blks' xs st st',
             noswitch_block blk ->
             LastsDefined blk xs ->
             NoDupLocals (map fst (Env.elements sub) ++ xs) blk ->
             f sub blk st = (locs', blks', st') ->
             exists ys, Forall2 LastsDefined blks' ys /\ Permutation (concat ys) (map (rename_var sub) xs ++ lasts_of_decls locs')) blks ->
      Forall noswitch_block blks ->
      Forall2 LastsDefined blks xs ->
      Forall (NoDupLocals (map fst (Env.elements sub) ++ concat xs)) blks ->
      mmap2 (f sub) blks st = (locs', blks', st') ->
      exists ys, Forall2 LastsDefined (concat blks') ys /\ Permutation (concat ys) (map (rename_var sub) (concat xs) ++ lasts_of_decls (concat locs')).
  Proof.
    induction blks; intros * Hf Hns Hlasts Hnd Hnorm; inv Hf; inv Hns; inv Hlasts; inv Hnd; repeat monadInv; simpl.
    - exists []. split; auto.
    - eapply H1 in H as (ys1&Hlasts1&Hperm1); eauto.
      2:eapply NoDupLocals_incl; [|eauto]; solve_incl_app.
      eapply IHblks in H2 as (ys2&Hlasts2&Hperm2); eauto. clear IHblks.
      2:simpl_Forall; intros; eapply NoDupLocals_incl; [|eauto]; solve_incl_app.
      exists (ys1 ++ ys2). split.
      + apply Forall2_app; auto.
      + rewrite concat_app, Hperm1, Hperm2. unfold lasts_of_decls. solve_Permutation_app.
  Qed.

  Lemma inlinelocal_block_lasts_perm : forall blk sub locs' blks' xs st st',
      noswitch_block blk ->
      LastsDefined blk xs ->
      NoDupLocals (map fst (Env.elements sub) ++ xs) blk ->
      inlinelocal_block sub blk st = (locs', blks', st') ->
      exists ys, Forall2 LastsDefined blks' ys /\ Permutation (concat ys) (map (rename_var sub) xs ++ lasts_of_decls locs').
  Proof.
    induction blk using block_ind2; intros * Hns Hlasts Hnd Hdl;
      inv Hns; inv Hlasts; inv Hnd; repeat monadInv.
    - (* equation *)
      destruct eq.
      repeat esplit; simpl; eauto using LastsDefined with datatypes.
    - (* last *)
      repeat (econstructor; eauto); simpl.
    - (* reset *)
      eapply mmap_lasts_perm in H0 as (ys1&Hlasts1&Hperm1); eauto.
      do 2 esplit; eauto using LastsDefined.
      simpl. now rewrite app_nil_r.
    - (* local *)
      repeat inv_scope. take (Permutation _ _) and rename it into Hperm.
      take (mmap2 _ _ _ = _) and eapply mmap_lasts_perm in it as (ys1&Hlasts1&Hperm1); eauto.
      2:{ simpl_Forall.
          eapply NoDupLocals_incl; [|eauto].
          rewrite <-app_assoc, Hperm.
          apply incl_app; try solve [solve_incl_app].
          intros ? Hin. simpl_In.
          eapply Env.elements_complete, Env.find_adds'_In in Hin0 as [Hfind|Hfind].
          - eapply in_combine_l in Hfind.
            rewrite 2 in_app_iff. auto.
          - eapply Env.elements_correct in Hfind.
            apply in_or_app, or_introl; solve_In.
          - apply incl_appr, incl_appr', lasts_of_decls_incl.
      }
      do 2 esplit; eauto. rewrite Hperm1, Hperm.
      unfold lasts_of_decls. rewrite ? map_filter_app, ? map_app, <- ? app_assoc.
      erewrite not_in_union_map_rename2, map_map_filter, map_filter_map, map_filter_ext with (xs:=locs). reflexivity.
      + unfold decl. intros; destruct_conjs.
        destruct o; simpl; auto.
      + simpl_Forall. intros In. apply fst_InMembers in In.
        eapply H11; eauto with datatypes.
  Qed.

  (** *** st_valid *)

  Lemma reuse_ident_st_valid : forall x y st st',
      AtomOrGensym switch_prefs x ->
      reuse_ident x st = (y, st') ->
      st_valid st ->
      st_valid st'.
  Proof.
    intros * At Reu V. unfold reuse_ident in *.
    cases_eqn EQ; inv_equalities; simpl.
    apply PS_For_all_add. split; auto.
  Qed.

  Corollary reuse_idents_st_valid : forall locs locs' st st',
      Forall (AtomOrGensym switch_prefs) locs ->
      mmap reuse_ident locs st = (locs', st') ->
      st_valid st ->
      st_valid st'.
  Proof.
    intros * At Map V.
    eapply mmap_st_valid; eauto. simpl_Forall; eauto using reuse_ident_st_valid.
  Qed.

  Lemma inlinelocal_block_st_valid : forall blk sub locs' blks' st st',
      GoodLocals switch_prefs blk ->
      inlinelocal_block sub blk st = (locs', blks', st') ->
      st_valid st ->
      st_valid st'.
  Proof.
    induction blk using block_ind2; intros * Good Il V; inv Good;
      repeat monadInv; auto.
    - (* reset *)
      eapply mmap2_st_valid; eauto.
      simpl_Forall; eauto.
    - (* local *)
      repeat inv_scope.
      eapply mmap2_st_valid; eauto using reuse_idents_st_valid. simpl_Forall; eauto.
  Qed.

  (** *** st_follows *)

  Lemma reuse_ident_st_follows : forall x y st st',
      reuse_ident x st = (y, st') ->
      st_follows st st'.
  Proof.
    intros * Reu. unfold reuse_ident in *.
    cases_eqn EQ; inv_equalities; split; try reflexivity; simpl.
    - eauto using fresh_ident_st_follows.
    - intros ??; eauto using PSF.add_2.
  Qed.

  Lemma inlinelocal_block_st_follows : forall blk sub locs' blks' st st',
      inlinelocal_block sub blk st = (locs', blks', st') ->
      st_follows st st'.
  Proof.
    induction blk using block_ind2; intros * Il; repeat monadInv; try reflexivity.
    - (* reset *)
      eapply mmap2_st_follows; eauto.
      simpl_Forall; eauto.
    - (* local *)
      etransitivity.
      + eapply mmap_st_follows; eauto. simpl_Forall; eauto using reuse_ident_st_follows.
      + eapply mmap2_st_follows; eauto.
        simpl_Forall; eauto.
  Qed.

  (** *** GoodLocals *)

  Lemma inlinelocal_block_GoodLocals : forall blk sub blks' locs' st st',
      noswitch_block blk ->
      inlinelocal_block sub blk st = (locs', blks', st') ->
      Forall (GoodLocals local_prefs) blks'.
  Proof.
    induction blk using block_ind2; intros * Hns Hdl; inv Hns; repeat monadInv.
    - (* equation *)
      repeat constructor.
    - (* last *)
      repeat constructor.
    - (* reset *)
      repeat constructor. apply Forall_concat.
      eapply mmap2_values, Forall3_ignore12 in H0. simpl_Forall.
      eapply H in H4; eauto. simpl_Forall; auto.
    - (* local *)
      apply Forall_concat.
      eapply mmap2_values, Forall3_ignore12 in H2. simpl_Forall.
      eapply H in H5; eauto. simpl_Forall; auto.
  Qed.

  Lemma reuse_idents_find {A} : forall (locs: list (ident * A)) locs' st st' sub x,
      NoDupMembers locs ->
      mmap reuse_ident (map fst locs) st = (locs', st') ->
      InMembers x locs ->
      exists st st' y,
        reuse_ident x st = (y, st')
        /\ Env.find x (Env.adds (map fst locs) locs' sub) = Some y.
  Proof.
    intros * ND Reuse In. apply fst_InMembers in In.
    eapply mmap_values, Forall2_forall2 in Reuse as (Len&Nth).
    eapply In_nth with (d:=xH) in In as (?&N&NthLocs); subst.
    setoid_rewrite Env.In_find_adds.
    2:now apply fst_NoDupMembers.
    2:{ erewrite <-combine_nth; [|eauto].
        eapply nth_In with (d:=(xH, xH)). now rewrite length_combine, <-Len, Nat.min_id. }
    specialize (Nth xH xH _ _ _ N eq_refl eq_refl) as (?&?&?).
    do 2 esplit; eauto.
  Qed.

  Lemma reuse_idents_find_follows {A} : forall (locs: list (ident * A)) locs' st st' x sub,
      NoDupMembers locs ->
      mmap reuse_ident (map fst locs) st = (locs', st') ->
      InMembers x locs ->
      exists st1 st1' y,
        st_follows st st1
        /\ st_follows st1' st'
        /\ reuse_ident x st1 = (y, st1')
        /\ Env.find x (Env.adds (map fst locs) locs' sub) = Some y.
  Proof.
    intros * ND Reuse In. apply fst_InMembers in In.
    eapply mmap_values_follows, Forall2_forall2 in Reuse as (Len&Nth); eauto using reuse_ident_st_follows.
    eapply In_nth with (d:=xH) in In as (?&N&NthLocs); subst.
    setoid_rewrite Env.In_find_adds.
    2:now apply fst_NoDupMembers.
    2:{ erewrite <-combine_nth; [|eauto].
        eapply nth_In with (d:=(xH, xH)). now rewrite length_combine, <-Len, Nat.min_id. }
    specialize (Nth xH xH _ _ _ N eq_refl eq_refl) as (?&?&?&?&?).
    do 2 esplit; eauto.
  Qed.

  Lemma reuse_idents_find' {A} : forall (locs: list (ident * A)) locs' st st' x sub,
      NoDupMembers locs ->
      Forall (AtomOrGensym switch_prefs) (map fst locs) ->
      mmap reuse_ident (map fst locs) st = (locs', st') ->
      st_valid st ->
      InMembers x locs ->
      exists st1 st1' y,
        st_valid st1
        /\ st_follows st st1
        /\ st_follows st1' st'
        /\ reuse_ident x st1 = (y, st1')
        /\ Env.find x (Env.adds (map fst locs) locs' sub) = Some y.
  Proof.
    intros * ND At Reuse V In. apply fst_InMembers in In.
    eapply mmap_values', Forall2_forall2 in Reuse as (Len&Nth); eauto using reuse_ident_st_follows.
    2:{ clear In. simpl_Forall; eauto using reuse_ident_st_valid. }
    eapply In_nth with (d:=xH) in In as (?&N&NthLocs); subst.
    setoid_rewrite Env.In_find_adds.
    2:now apply fst_NoDupMembers.
    2:{ erewrite <-combine_nth; [|eauto].
        eapply nth_In with (d:=(xH, xH)). now rewrite length_combine, <-Len, Nat.min_id. }
    specialize (Nth xH xH _ _ _ N eq_refl eq_refl) as (?&?&?&?&?&?).
    do 2 esplit; eauto 6.
  Qed.

  Lemma inlinelocal_block_AtomOrGensym : forall blk Γ sub blks' locs' st st',
      NoDupLocals Γ blk ->
      GoodLocals switch_prefs blk ->
      inlinelocal_block sub blk st = (locs', blks', st') ->
      Forall (fun '(x, _) => AtomOrGensym local_prefs x) locs'.
  Proof.
    induction blk using block_ind2; intros * ND Good Hdl; inv ND; inv Good; repeat monadInv; try constructor.
    - (* reset *)
      apply Forall_concat.
      eapply mmap2_values, Forall3_ignore13 in H0. simpl_Forall.
      eapply H in H5; eauto. simpl_Forall; auto.
    - (* local *)
      repeat inv_scope.
      apply Forall_app; split.
      + simpl_Forall. eapply reuse_idents_find in H0 as (?&?&?&Reu&Find); eauto using In_InMembers.
        unfold rename_var. erewrite Find. simpl.
        unfold reuse_ident in Reu. cases_eqn EQ; inv_equalities.
        * eapply fresh_ident_prefixed in EQ0 as (?&?&?); subst.
          right. do 2 esplit; eauto using PSF.add_1.
        * eauto using AtomOrGensym_add.
      + apply Forall_concat.
        eapply mmap2_values, Forall3_ignore13 in H3. simpl_Forall.
        eapply H in H4; eauto. simpl_Forall; auto.
  Qed.

  (** *** NoDupLocals *)

  Lemma inlinelocal_block_NoDupLocals xs : forall blk sub locs' blks' st st',
      noswitch_block blk ->
      inlinelocal_block sub blk st = (locs', blks', st') ->
      Forall (NoDupLocals xs) blks'.
  Proof.
    induction blk using block_ind2; intros * Hns Hdl; inv Hns; repeat monadInv; repeat constructor.
    - (* reset *)
      eapply mmap2_values, Forall3_ignore12 in H0.
      eapply Forall_concat. simpl_Forall.
      eapply H in H4; eauto. now simpl_Forall.
    - (* local *)
      eapply mmap2_values, Forall3_ignore12 in H2.
      eapply Forall_concat. simpl_Forall.
      eapply H in H5; eauto. now simpl_Forall.
  Qed.

  Lemma local_not_in_switch_prefs :
    ~PS.In local switch_prefs.
  Proof.
    unfold switch_prefs, auto_prefs, last_prefs, elab_prefs.
    rewrite ? PS.add_spec, PSF.singleton_iff.
    pose proof gensym_prefs_NoDup as Hnd. unfold gensym_prefs in Hnd.
    repeat rewrite NoDup_cons_iff in Hnd. destruct_conjs.
    intros Eq. repeat take (_ \/ _) and destruct it as [Eq|Eq]; eauto 8 with datatypes.
  Qed.

  Lemma reuse_ident_In : forall x y st st',
      reuse_ident x st = (y, st') ->
      PS.In x (used st').
  Proof.
    intros * Reu. unfold reuse_ident in *.
    cases_eqn EQ.
    inv Reu; eauto using PSF.add_1.
  Qed.

  Corollary reuse_idents_In : forall locs locs' st st',
    mmap reuse_ident locs st = (locs', st') ->
    Forall (fun x => PS.In x (used st')) locs.
  Proof.
    intros * Reu.
    eapply mmap_values_follows, Forall2_ignore2 in Reu; eauto using reuse_ident_st_follows.
    simpl_Forall.
    eapply H2, reuse_ident_In; eauto.
  Qed.

  Lemma reuse_ident_st_In : forall x y st st',
      reuse_ident x st = (y, st') ->
      st_In y st'.
  Proof.
    intros * Reu. unfold reuse_ident in *.
    cases_eqn EQ; inv_equalities.
    - left. eapply fresh_ident_Inids; eauto.
    - right. eauto using PSF.add_1.
  Qed.

  Corollary reuse_idents_st_In : forall locs locs' st st',
    mmap reuse_ident locs st = (locs', st') ->
    Forall (fun x => st_In x st') locs'.
  Proof.
    intros * Reu.
    eapply mmap_values_follows, Forall2_ignore1 in Reu; eauto using reuse_ident_st_follows.
    simpl_Forall.
    eapply reuse_ident_st_In in H3; eauto using st_follows_In.
  Qed.

  Lemma inlinelocal_block_st_In : forall blk Γ sub blks' locs' st st',
      NoDupLocals Γ blk ->
      inlinelocal_block sub blk st = (locs', blks', st') ->
      Forall (fun '(x, _) => st_In x st') locs'.
  Proof.
    induction blk using block_ind2; intros * ND IL; inv ND;
      repeat monadInv; try constructor.
    - (* reset *)
      eapply mmap2_values_follows, Forall3_ignore13 in H0; eauto using inlinelocal_block_st_follows.
      apply Forall_concat. simpl_Forall.
      eapply H in H6; eauto. simpl_Forall; eauto using st_follows_In.
    - (* local *)
      inv H2.
      apply Forall_app; split.
      + simpl_Forall.
        eapply reuse_idents_find_follows in H0 as (?&?&?&F1&F2&Reu&Find); eauto using In_InMembers.
        unfold rename_var. erewrite Find; eauto. simpl.
        eapply reuse_ident_st_In in Reu. eapply st_follows_In; [|eauto].
        etransitivity; eauto. eapply mmap2_st_follows; eauto. simpl_Forall; eauto using inlinelocal_block_st_follows.
      + eapply mmap2_values_follows, Forall3_ignore13 in H1; eauto using inlinelocal_block_st_follows.
        apply Forall_concat. simpl_Forall.
        eapply H in H9; eauto. simpl_Forall. eauto using st_follows_In.
  Qed.

  Lemma reuse_ident_st_nIn : forall x y st st',
      AtomOrGensym switch_prefs x ->
      st_valid st ->
      reuse_ident x st = (y, st') ->
      ~st_In y st.
  Proof.
    intros * At1 At2 Reu. unfold reuse_ident in *.
    cases_eqn EQ; inv_equalities.
    - intros [In|In].
      + eapply fresh_ident_nIn; eauto.
      + eapply At2 in In.
        eapply st_valid_AtomOrGensym_nIn; eauto using local_not_in_switch_prefs, fresh_ident_Inids.
    - apply PSE.mem_4 in EQ.
      contradict EQ. destruct EQ as [In|In]; auto.
      exfalso. eapply st_valid_AtomOrGensym_nIn; eauto using local_not_in_switch_prefs.
  Qed.

  Corollary reuse_idents_st_nIn : forall locs locs' st st',
      Forall (AtomOrGensym switch_prefs) locs ->
      st_valid st ->
      mmap reuse_ident locs st = (locs', st') ->
      Forall (fun y => ~st_In y st) locs'.
  Proof.
    intros * F V Map.
    eapply mmap_values', Forall2_ignore1 in Map; eauto using reuse_ident_st_follows.
    2:{ simpl_Forall; eauto using reuse_ident_st_valid. }
    simpl_Forall. eapply reuse_ident_st_nIn in H4; eauto using st_follows_In.
  Qed.

  Lemma inlinelocal_block_st_nIn : forall blk Γ sub blks' locs' st st',
      NoDupLocals Γ blk ->
      GoodLocals switch_prefs blk ->
      st_valid st ->
      inlinelocal_block sub blk st = (locs', blks', st') ->
      Forall (fun '(x, _) => ~ (st_In x st)) locs'.
  Proof.
    induction blk using block_ind2; intros * ND Good V IL; inv ND; inv Good;
      repeat monadInv; try constructor.
    - (* reset *)
      eapply mmap2_values', Forall3_ignore13 in H0; eauto using inlinelocal_block_st_follows.
      2:{ simpl_Forall; eauto using inlinelocal_block_st_valid. }
      apply Forall_concat. simpl_Forall.
      take (inlinelocal_block _ _ _ = _) and eapply H in it; eauto. simpl_Forall; eauto using st_follows_In.
    - (* local *)
      repeat inv_scope.
      apply Forall_app; split.
      + eapply Forall_forall. intros. simpl_In.
        eapply reuse_idents_find' in H0 as (?&?&?&V1&F1&F2&Reu&Find); eauto using In_InMembers.
        unfold rename_var. erewrite Find. simpl.
        simpl_Forall. eapply reuse_ident_st_nIn in Reu; eauto.
        contradict Reu; eauto using st_follows_In.
      + eapply mmap2_values', Forall3_ignore13 in H3; eauto using inlinelocal_block_st_follows, reuse_idents_st_valid.
        2:{ simpl_Forall; eauto using inlinelocal_block_st_valid. }
        apply Forall_concat. simpl_Forall.
        take (inlinelocal_block _ _ _ = _) and eapply H in it; eauto. simpl_Forall. contradict it.
        eapply st_follows_In; [|eauto].
        etransitivity; eauto. eapply mmap_st_follows; eauto. simpl_Forall; eauto using reuse_ident_st_follows.
  Qed.

  Corollary inlinelocal_blocks_st_nIn : forall blks Γ sub blks' locs' st st',
      Forall (NoDupLocals Γ) blks ->
      Forall (GoodLocals switch_prefs) blks ->
      st_valid st ->
      mmap2 (inlinelocal_block sub) blks st = (locs', blks', st') ->
      Forall (fun '(x, _) => ~ (st_In x st)) (concat locs').
  Proof.
    intros * ND Good V IL.
    eapply mmap2_values', Forall3_ignore13 in IL; eauto using inlinelocal_block_st_follows.
    2:{ simpl_Forall; eauto using inlinelocal_block_st_valid. }
    apply Forall_concat. simpl_Forall.
    take (inlinelocal_block _ _ _ = _) and eapply inlinelocal_block_st_nIn in it; eauto.
    simpl_Forall; eauto using st_follows_In.
  Qed.

  Corollary inlinelocal_block_nIn : forall blk sub xs locs' blks' st st',
      Forall (fun x => PS.In x (used st)) xs ->
      NoDupLocals xs blk ->
      GoodLocals switch_prefs blk ->
      st_valid st ->
      inlinelocal_block sub blk st = (locs', blks', st') ->
      Forall (fun '(x, _) => ~In x xs) locs'.
  Proof.
    intros * In ND Good Il V.
    eapply inlinelocal_block_st_nIn in Il; eauto.
    simpl_Forall. contradict Il. simpl_Forall. right; auto.
  Qed.

  Lemma mmap_inlinelocal_block_NoDupMembers : forall blks Γ sub locs' blks' st st',
      Forall
        (fun blk =>
           forall Γ sub locs' blks' st st',
             NoDupLocals Γ blk ->
             GoodLocals switch_prefs blk ->
             st_valid st ->
             inlinelocal_block sub blk st = (locs', blks', st') ->
             NoDupMembers locs') blks ->
      Forall (NoDupLocals Γ) blks ->
      Forall (GoodLocals switch_prefs) blks ->
      st_valid st ->
      mmap2 (inlinelocal_block sub) blks st = (locs', blks', st') ->
      NoDupMembers (concat locs').
  Proof.
    induction blks; intros * F ND Good V IL; inv F; inv ND; inv Good;
      repeat monadInv; simpl. constructor.
    apply NoDupMembers_app; eauto using inlinelocal_block_st_valid.
    - intros * In1 In2.
      eapply inlinelocal_blocks_st_nIn in H0; eauto using inlinelocal_block_st_valid.
      eapply inlinelocal_block_st_In in H; eauto.
      simpl_In. simpl_Forall. contradiction.
  Qed.

  Lemma reuse_idents_rename {A} sub : forall (locs : list (ident * A)) locs' st st',
      NoDupMembers locs ->
      mmap reuse_ident (map fst locs) st = (locs', st') ->
      map (rename_var (Env.adds (map fst locs) locs' sub)) (map fst locs) = locs'.
  Proof.
    intros * ND Map. eapply Forall2_eq, Forall2_forall2.
    assert (Map':=Map). eapply mmap_values, Forall2_forall2 in Map as (Len&F2).
    rewrite length_map. split; auto.
    intros * N Nth1 Nth2; subst.
    erewrite map_nth' with (d':=xH); eauto.
    unfold rename_var. setoid_rewrite Env.In_find_adds'. simpl; eauto.
    - now apply NoDup_NoDupMembers_combine, fst_NoDupMembers.
    - erewrite <-combine_nth; eauto. eapply nth_In.
      now rewrite length_combine, <-Len, Nat.min_id.
  Qed.

  Lemma reuse_idents_NoDup {A} : forall (locs : list (ident * A)) locs' st st',
      Forall (AtomOrGensym switch_prefs) (map fst locs) ->
      st_valid st ->
      mmap reuse_ident (map fst locs) st = (locs', st') ->
      NoDup locs'.
  Proof.
    induction locs; intros * At V Reu; inv At;
      repeat monadInv; constructor; eauto using reuse_ident_st_valid.
    - intros In.
      eapply reuse_ident_st_In in H as StIn.
      eapply reuse_idents_st_nIn in H0 as StIns; eauto using reuse_ident_st_valid.
      simpl_Forall. contradiction.
  Qed.

  Lemma inlinelocal_block_NoDupMembers : forall blk Γ sub locs' blks' st st',
      NoDupLocals Γ blk ->
      GoodLocals switch_prefs blk ->
      st_valid st ->
      inlinelocal_block sub blk st = (locs', blks', st') ->
      NoDupMembers locs'.
  Proof.
    induction blk using block_ind2; intros * ND Good V IL; inv ND; inv Good;
      repeat monadInv; try constructor.
    - (* reset *)
      eapply mmap_inlinelocal_block_NoDupMembers; eauto.
    - (* local *)
      repeat inv_scope.
      apply NoDupMembers_app.
      + erewrite fst_NoDupMembers, map_map, map_ext, <-map_map, reuse_idents_rename; eauto.
        2:intros; destruct_conjs; auto.
        eapply reuse_idents_NoDup; eauto.
      + eapply mmap_inlinelocal_block_NoDupMembers in H3; eauto using reuse_idents_st_valid.
      + intros * In1 In2. erewrite fst_InMembers, map_map, map_ext, <-map_map, reuse_idents_rename in In1; eauto.
        2:intros; destruct_conjs; auto.
        eapply inlinelocal_blocks_st_nIn in H3; eauto using reuse_idents_st_valid.
        eapply reuse_idents_st_In in H0.
        simpl_In. simpl_Forall. contradiction.
  Qed.

  (** *** No local block *)

  Lemma inlinelocal_block_nolocal : forall blk sub locs' blks' st st',
      noswitch_block blk ->
      inlinelocal_block sub blk st = (locs', blks', st') ->
      Forall nolocal_block blks'.
  Proof.
    induction blk using block_ind2; intros * Hns Hdl; inv Hns; repeat monadInv.
    - (* equation *)
      repeat constructor.
    - (* last *)
      repeat constructor.
    - (* reset *)
      repeat constructor.
      eapply mmap2_values, Forall3_ignore12 in H0.
      eapply Forall_concat. simpl_Forall.
      eapply H in H4; eauto. now simpl_Forall.
    - (* local *)
      eapply mmap2_values, Forall3_ignore12 in H2.
      eapply Forall_concat. simpl_Forall.
      eapply H in H5; eauto. now simpl_Forall.
  Qed.

  (** ** Transformation of node and program *)

  Program Definition inlinelocal_node (n: @node noswitch switch_prefs) : @node nolocal local_prefs :=
    let res := inlinelocal_block (Env.empty _)
                 (n_block n)
                 {| fresh_st := init_st; used := PSP.of_list (map fst (n_in n) ++ map fst (n_out n)) |} in
    {|
      n_name := (n_name n);
      n_hasstate := (n_hasstate n);
      n_in := (n_in n);
      n_out := (n_out n);
      n_block := Blocal (Scope (fst (fst res)) (snd (fst res)));
      n_ingt0 := (n_ingt0 n);
      n_outgt0 := (n_outgt0 n);
    |}.
  Next Obligation.
    pose proof (n_syn n) as Hns. inversion_clear Hns as [?? Hns1 (?&Hvars&Hperm)].
    pose proof (n_nodup n) as (_&Hndup).
    apply Permutation_map_inv in Hperm as (?&?&Hperm); subst.
    repeat esplit; eauto.
    destruct (inlinelocal_block _ _) as ((?&?)&?) eqn:Hdl.
    eapply inlinelocal_block_vars_perm in Hvars as (?&?&Hperm'); eauto.
    rewrite rename_vars_empty in Hperm'.
    2:{ rewrite Env.Props.P.elements_empty, <-Hperm. simpl.
        eapply NoDupLocals_incl; [|eauto]. solve_incl_app. }
    apply noswitch_VarsDefinedComp_VarsDefined.
    1:{ constructor. simpl_Forall; auto.
        eapply inlinelocal_block_nolocal in Hdl; eauto.
        simpl_Forall; eauto using nolocal_noswitch. }
    rewrite map_fst_senv_of_decls.
    do 4 econstructor; eauto.
    rewrite Hperm', <-Hperm. reflexivity.
  Qed.
  Next Obligation.
    pose proof (n_syn n) as Hsyn. inversion_clear Hsyn as [?? Hns1 _].
    pose proof (n_lastd n) as (?&Last&Perm).
    pose proof (n_nodup n) as (_&Hndup).
    repeat esplit; eauto.
    destruct (inlinelocal_block _ _) as ((?&?)&?) eqn:Hdl.
    eapply inlinelocal_block_lasts_perm in Hdl as (?&?&Hperm'); eauto.
    rewrite rename_vars_empty in Hperm'.
    2:{ rewrite Env.Props.P.elements_empty; simpl. rewrite Perm.
        eapply NoDupLocals_incl; [|eauto]. apply incl_appr, lasts_of_decls_incl. }
    do 2 constructor. do 2 esplit; eauto.
  Qed.
  Next Obligation.
    pose proof (n_good n) as (Hgood1&Hgood2&_).
    pose proof (n_nodup n) as (Hnd1&Hnd2).
    pose proof (n_syn n) as Hsyn. inversion_clear Hsyn as [?? Hns1 _].
    repeat rewrite app_nil_r.
    destruct (inlinelocal_block _ _) as ((?&?)&st') eqn:Hdl. simpl.
    split; auto. do 2 constructor; eauto.
    - eapply inlinelocal_block_NoDupLocals; eauto.
    - eapply inlinelocal_block_NoDupMembers in Hdl; eauto.
      intros ? In. apply In_of_list in In. now simpl_Forall.
    - intros * In1 In2.
      eapply inlinelocal_block_nIn in Hdl. 3-5:eauto.
      2:{ simpl_Forall. apply In_of_list. auto. }
      2:{ intros ? In. apply In_of_list in In. now simpl_Forall. }
      simpl_In. simpl_Forall. eauto.
  Qed.
  Next Obligation.
    pose proof (n_good n) as (Hgood1&Hgood2&Hatom).
    pose proof (n_nodup n) as (Hnd1&Hnd2).
    destruct (inlinelocal_block _ _) as ((?&?)&?) eqn:Hdl. simpl.
    pose proof (n_syn n) as Hsyn. inversion_clear Hsyn as [?? Hns1 Hns2].
    repeat split; eauto using Forall_AtomOrGensym_add.
    do 2 constructor.
    - eapply inlinelocal_block_AtomOrGensym in Hdl; eauto.
      simpl_Forall; auto.
    - eapply inlinelocal_block_GoodLocals; eauto.
  Qed.
  Next Obligation.
    pose proof (n_syn n) as Hsyn. inversion_clear Hsyn as [?? Hns1 (?&Hvars&Hperm)].
    pose proof (n_nodup n) as (_&Hndup).
    destruct (inlinelocal_block _ _) as ((?&?)&?) eqn:Hdl.
    repeat constructor.
    - eapply inlinelocal_block_nolocal; eauto.
    - eapply inlinelocal_block_vars_perm in Hvars as (?&?&Hperm'); eauto.
      rewrite rename_vars_empty in Hperm'.
      2:{ rewrite Env.Props.P.elements_empty, Hperm. simpl.
          eapply NoDupLocals_incl; [|eauto]. solve_incl_app. }
      do 2 econstructor; [|eauto].
      do 4 econstructor; eauto.
  Qed.

  Global Program Instance inlinelocal_node_transform_unit: TransformUnit (@node noswitch switch_prefs) node :=
    { transform_unit := inlinelocal_node }.

  Global Program Instance inlinelocal_global_without_units : TransformProgramWithoutUnits (@global noswitch switch_prefs) (@global nolocal local_prefs) :=
    { transform_program_without_units := fun g => Global g.(types) g.(externs) [] }.

  Definition inlinelocal_global : @global noswitch switch_prefs -> @global nolocal local_prefs :=
    transform_units.

  (** *** Equality of interfaces *)

  Lemma inlinelocal_global_iface_eq : forall G,
      global_iface_eq G (inlinelocal_global G).
  Proof.
    repeat split; auto.
    intros f. unfold find_node.
    destruct (find_unit f G) as [(?&?)|] eqn:Hfind; simpl.
    - setoid_rewrite find_unit_transform_units_forward; eauto.
      simpl. repeat constructor.
    - destruct (find_unit f (inlinelocal_global G)) as [(?&?)|] eqn:Hfind'; simpl; try constructor.
      eapply find_unit_transform_units_backward in Hfind' as (?&?&?&?); congruence.
  Qed.

  (* Additional properties *)

  Definition senv_of_anns (locs' : list (ident * ann)) : static_env :=
    map (fun '(x, (ty, ck)) => (x, (Build_annotation ty ck xH None))) locs'.
  Global Hint Unfold senv_of_anns : list.

  Fact senv_of_anns_app : forall locs1 locs2,
      senv_of_anns (locs1 ++ locs2) = senv_of_anns locs1 ++ senv_of_anns locs2.
  Proof.
    intros. apply map_app.
  Qed.

  Fact senv_of_anns_concat_incl Γ : forall locs locs',
      In locs locs' ->
      incl (Γ ++ senv_of_anns locs) (Γ ++ senv_of_anns (concat locs')).
  Proof.
    intros * In.
    now apply incl_appr', incl_map, incl_concat.
  Qed.
  Global Hint Resolve senv_of_anns_concat_incl : senv.

  Fact senv_of_decls_concat_incl Γ : forall locs locs',
      In locs locs' ->
      incl (Γ ++ senv_of_decls locs) (Γ ++ senv_of_decls (concat locs')).
  Proof.
    intros * In.
    now apply incl_appr', incl_map, incl_concat.
  Qed.
  Global Hint Resolve senv_of_decls_concat_incl : senv.

  Lemma reuse_ident_gensym : forall x y st st',
      reuse_ident x st = (y, st') ->
      y = x \/ exists n hint, y = gensym local hint n.
  Proof.
    intros * Reu.
    unfold reuse_ident in *. cases_eqn EQ; inv_equalities.
    - right. eapply Fresh.Ker.fresh_ident_prefixed in EQ0; eauto.
  Qed.

  Lemma reuse_idents_gensym {A} : forall (locs : list (ident * A)) locs' st st',
      mmap reuse_ident (map fst locs) st = (locs', st') ->
      Forall (fun x => InMembers x locs \/ exists n hint, x = gensym local hint n) locs'.
  Proof.
    intros * Map.
    eapply mmap_values, Forall2_ignore1 in Map. simpl_Forall.
    eapply reuse_ident_gensym in H1 as [|]; subst; eauto.
    - left. now apply fst_InMembers.
  Qed.

  Fact IsLast_sub1 : forall vars1 vars2 vars3 sub,
      (forall x, InMembers x vars1 -> ~InMembers x vars2) ->
      (forall x, Env.In x sub <-> InMembers x vars2) ->
      (forall x y, Env.find x sub = Some y -> IsLast vars2 x -> IsLast vars3 y) ->
      forall x y, Env.find x sub = Some y -> IsLast (vars1 ++ vars2) x -> IsLast (vars1 ++ vars3) y.
  Proof.
    intros * Hnd Hsubin Hsub * Hfind Hin.
    rewrite IsLast_app in *. destruct Hin as [Hin|Hin]; eauto.
    exfalso. inv Hin. eapply Hnd; eauto using In_InMembers.
    eapply Hsubin. econstructor; eauto.
  Qed.

  Fact IsLast_sub2 : forall vars1 vars2 vars3 sub,
      (forall x, Env.In x sub <-> InMembers x vars2) ->
      (forall x y, Env.find x sub = Some y -> IsLast vars2 x -> IsLast vars3 y) ->
      forall x, Env.find x sub = None -> IsLast (vars1 ++ vars2) x -> IsLast (vars1 ++ vars3) x.
  Proof.
    intros * Hsubin Hsub * Hfind Hin.
    rewrite IsLast_app in *. destruct Hin as [Hin|Hin]; eauto.
    exfalso. inv Hin. eapply In_InMembers, Hsubin in H as (?&?).
    congruence.
  Qed.

End INLINELOCAL.

Module InlineLocalFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       <: INLINELOCAL Ids Op OpAux Cks Senv Syn.
  Include INLINELOCAL Ids Op OpAux Cks Senv Syn.
End InlineLocalFun.
