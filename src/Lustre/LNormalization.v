(** * Fresh name generation *)

From Coq Require Import List Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Classes.RelationClasses.
Require Import Omega.
From Coq Require Import Program.Equality.

From Velus Require Import Common Ident.

Module Fresh.
  Import Classes.RelationClasses.

  (** The fresh monad (with memory) : generates new names and keeps
    a record of each name generated along with some information *)
  Definition fresh_st (B : Type) : Type := (ident * list (ident * B)).
  Definition Fresh (A B : Type) : Type := fresh_st B -> A * fresh_st B.

  (** Pure value *)
  Definition ret {A B} (a : A) : Fresh A B := fun st => (a, st).

  Section validity.
    Context {B : Type}.

    (** The state is valid if the next ident is greater than all generated idents,
    and if there is no duplicates in generated idents *)
    Definition fresh_st_valid (st : fresh_st B) : Prop :=
      let '(n, l) := st in
      Forall (fun '(x, _) => Pos.lt x n) l /\ NoDupMembers l.
  End validity.

  Section follows.
    Context {B : Type}.

    (** Smallest identifier defined in the state *)
    Definition smallest_ident (st : fresh_st B) : positive :=
      let (n, l) := st in
      fold_right Pos.min n (List.map fst l).

    (** The smallest ident of `st` is less or equal to the smallest
      ident of `st'` *)
    Definition fresh_st_follows (st st' : fresh_st B) :=
      incl (snd st) (snd st') /\
      Pos.le (smallest_ident st) (smallest_ident st').

    Global Instance st_follows_refl : Reflexive fresh_st_follows.
    Proof.
      intros st. unfold fresh_st_follows.
      split; reflexivity.
    Qed.

    Global Instance st_follows_trans : Transitive fresh_st_follows.
    Proof.
      unfold Transitive. intros.
      unfold fresh_st_follows in *.
      destruct H; destruct H0.
      split; etransitivity; eauto.
    Qed.
  End follows.

  Section fresh_ident.
    Context {B : Type}.

    (** The counter is incremented with each call to `fresh_name` *)
    Definition fresh_ident (b : B) : Fresh ident B :=
      fun '(n, l) => (n, (Pos.succ n, (cons (n, b) l))).

    Fact fresh_ident_st_valid :
      forall (b : B) res st st',
        fresh_ident b st = (res, st') ->
        fresh_st_valid st ->
        fresh_st_valid st'.
    Proof.
      intros b res st st' Hfresh Hvalid.
      destruct st as [n l]; destruct st' as [n' l'].
      simpl in Hfresh; inv Hfresh.
      destruct Hvalid.
      repeat constructor; auto.
      + apply Positive_as_DT.lt_succ_diag_r.
      + eapply Forall_impl; eauto.
        intros [x _] Hlt'.
        apply Positive_as_OT.lt_lt_succ; auto.
      + intro contra.
        induction l; inv H; simpl in *; auto.
        destruct a as [x ann].
        destruct contra; subst; inv H0; auto.
        apply Pos.lt_irrefl in H3; auto.
    Qed.

    Fact fresh_ident_st_follows :
      forall (b : B) res st st',
        fresh_ident b st = (res, st') ->
        fresh_st_follows st st'.
    Proof.
      intros b res st st' Hfresh.
      destruct st as [n l]; destruct st' as [n' l'].
      simpl in *; inv Hfresh; simpl.
      unfold fresh_st_follows, smallest_ident in *; simpl in *.
      split.
      - apply incl_tl. reflexivity.
      - induction l as [|[a ?]]; simpl in *.
        + rewrite Pos.min_glb_iff.
        split.
        * reflexivity.
        * apply Pos.lt_le_incl.
          apply Pos.lt_succ_diag_r.
        + rewrite Pos.min_glb_iff in *.
          destruct IHl as [IHl1 IHl2].
          split.
          * etransitivity; eauto.
            eapply Pos.le_min_r.
          * eapply Pos.min_le_compat_l; eauto.
    Qed.

    Fact fresh_ident_vars_perm : forall (b : B) id st st',
        fresh_ident b st = (id, st') ->
        Permutation (id::(map fst (snd st))) (map fst (snd st')).
    Proof.
      intros b id st st' Hfresh.
      destruct st; destruct st'; simpl in *.
      inv Hfresh. simpl. reflexivity.
    Qed.
  End fresh_ident.

  Section bind.
    Context {A A' B : Type}.

    Definition bind (x : Fresh A B) (k : A -> Fresh A' B) : Fresh A' B :=
      fun st => let '(a, st') := x st in k a st'.

    Lemma bind_inv : forall (x : Fresh A B) (k : A -> Fresh A' B) st a' st'',
        (bind x k) st = (a', st'') ->
        exists a, exists st', (x st = (a, st') /\ k a st' = (a', st'')).
    Proof.
      intros x k st a' st'' Hbind.
      unfold bind in Hbind.
      destruct (x st) as [a st']. exists a. exists st'.
      split; auto.
    Qed.
  End bind.

  Section bind2.
    Context {A1 A2 A' B : Type}.

    Definition bind2 (x: Fresh (A1 * A2) B) (k: A1 -> A2 -> Fresh A' B) : Fresh A' B :=
      fun n => let '((a1, a2), n') := x n in k a1 a2 n'.

    Lemma bind2_inv : forall (x : Fresh (A1 * A2) B) (k : A1 -> A2 -> Fresh A' B) st a' st'',
        (bind2 x k) st = (a', st'') ->
        exists a1, exists a2, exists st', (x st = ((a1, a2), st') /\ k a1 a2 st' = (a', st'')).
    Proof.
      intros x k st a' st'' Hbind.
      unfold bind2 in Hbind.
      destruct (x st) as [[a1 a2] st']. exists a1. exists a2. exists st'.
      split; auto.
    Qed.
  End bind2.

  Ltac inv_bind :=
    match goal with
    | H : ret _ _ = _ |- ?G =>
      unfold ret in H; inv H; simpl
    | H : bind _ _ _ = (_, _) |- _ =>
      apply bind_inv in H; destruct H as [? [? [? ?]]]; simpl
    | H : bind2 _ _ _ = (_, _) |- _ =>
      apply bind2_inv in H; destruct H as [? [? [? [? ?]]]]; simpl
    | |- ret _ _ = _ =>
      unfold ret; simpl
    | |- bind _ _ _ = (_, _) =>
      unfold bind; simpl
    | |- bind2 _ _ _ = (_, _, _) =>
      unfold bind2; simpl
    end.

  (** [do] notation, inspired by CompCert's error monad *)
  Notation "'do' X <- A ; B" :=
    (bind A (fun X => B))
      (at level 200, X ident, A at level 100, B at level 200): fresh_monad_scope.

  Notation "'do' ( X , Y ) <- A ; B" :=
    (bind2 A (fun X Y => B))
      (at level 200, X ident, Y ident, A at level 100, B at level 200): fresh_monad_scope.

  Section map_bind2.
    Context {A A1 A2 B : Type}.
    Variable k : A -> Fresh (A1 * A2) B.

    Open Scope list.
    Open Scope fresh_monad_scope.
    Fixpoint map_bind2 a :=
      match a with
      | nil => ret (nil, nil)
      | hd::tl => do (a1, a2) <- k hd;
                  do (a1s, a2s) <- map_bind2 tl;
                  ret (a1::a1s, a2::a2s)
      end.

    Fact map_bind2_values : forall a st a1s a2s st',
        map_bind2 a st = (a1s, a2s, st') ->
        Forall3 (fun a a1 a2 => exists st'', exists st''', k a st'' = (a1, a2, st''')) a a1s a2s.
    Proof.
      induction a; intros st a1s a2s st' Hfold; simpl in *.
      - inv Hfold. constructor.
      - repeat inv_bind.
        specialize (IHa _ _ _ _ H0).
        constructor; eauto.
    Qed.

    Fact map_bind2_st_valid : forall a a1s a2s st st',
        map_bind2 a st = (a1s, a2s, st') ->
        Forall (fun a => forall a1 a2 st st', k a st = (a1, a2, st') -> fresh_st_valid st -> fresh_st_valid st') a ->
        fresh_st_valid st ->
        fresh_st_valid st'.
    Proof.
      induction a; intros a1s a2s st st' Hmap Hforall Hvalid;
        simpl in *; repeat inv_bind; auto.
      inv Hforall. eapply IHa; eauto.
    Qed.

    Fact map_bind2_st_follows : forall a a1s a2s st st',
        map_bind2 a st = (a1s, a2s, st') ->
        Forall (fun a => forall a1 a2 st st', k a st = (a1, a2, st') -> fresh_st_follows st st') a ->
        fresh_st_follows st st'.
    Proof.
      induction a; intros a1s a2s st st' Hmap Hforall;
        simpl in *; repeat inv_bind; auto.
      - reflexivity.
      - inv Hforall.
        etransitivity; eauto.
    Qed.
  End map_bind2.

  Hint Resolve fresh_ident_st_follows.
  Hint Resolve fresh_ident_st_valid.
  Hint Resolve map_bind2_st_valid.
  Hint Resolve map_bind2_st_follows.
End Fresh.

(** * Normalization procedure *)

From Velus Require Import Operators Environment.
From Velus Require Import CoindStreams.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LTyping Lustre.LSemantics.

Local Set Warnings "-masking-absolute-name".
Module Type LNORMALIZATION
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Str : COINDSTREAMS Op OpAux)
       (Import Syn : LSYNTAX Ids Op)
       (Import Typ : LTYPING Ids Op Syn)
       (Import Lord : LORDERED Ids Op Syn)
       (Import Sem : LSEMANTICS Ids Op OpAux Syn Lord Str).
  Import List Fresh.

  (** All the indents currently used in the node *)
  Definition used_idents (n : node) : list ident :=
    reserved ++ map fst (n_in n ++ n_vars n ++ n_out n).

  Definition first_unused_ident (n : node) : ident :=
    ((fold_left Pos.max (used_idents n) xH) + 100)%positive.

  (** Some facts about getting the first unused ident *)

  Fact first_unused_ident_gt : forall n id,
      first_unused_ident n = id ->
      Forall (fun id' => (id' < id)%positive) (used_idents n).
  Proof.
    intros n id Hfirst.
    subst. unfold first_unused_ident.
    rewrite Forall_forall; intros x Hin.
    eapply Pos.le_lt_trans. 2: apply Pos.lt_add_r.
    apply max_fold_in; auto.
  Qed.

  (** Fresh ident generation keeping type annotations;
      also retaining if the var is an init var or not *)
  Definition FreshAnn A := Fresh A (ann * bool).

  Local Open Scope fresh_monad_scope.

  Definition hd_default (l : list exp) : exp :=
    hd (Econst (init_type bool_type)) l.

  Fixpoint idents_for_anns (anns : list ann) : FreshAnn (list (ident * ann)) :=
    match anns with
    | [] => ret []
    | hd::tl => do x <- fresh_ident (hd, false);
              do xs <- idents_for_anns tl;
              ret ((x, hd)::xs)
    end.

  Fact idents_for_anns_values : forall anns idents st st',
      idents_for_anns anns st = (idents, st') ->
      Forall2 (fun a '(id, a') => a = a') anns idents.
  Proof.
    induction anns; intros idents st st' Hanns; simpl in *.
    - inv Hanns. constructor.
    - repeat inv_bind.
      specialize (IHanns _ _ _ H0).
      constructor; eauto.
  Qed.

  (** Add some whens on top of an expression *)
  Fixpoint add_whens (e : exp) (ty : type) (cl : clock) :=
    match cl with
    | Cbase => e
    | Con cl' clid b => Ewhen [(add_whens e ty cl')] clid b ([ty], (cl, None))
    end.

  (** Generate an init equation for a given clock `cl`; if the init equation for `cl` already exists,
      just return the variable *)
  Definition init_var_for_clock (cl : nclock) : FreshAnn (ident * list equation) :=
    fun '(n, l) => match (find (fun '(_, ((_, cl'), isinit)) => isinit && (cl ==b cl'))) l with
                | Some (x, _) => ((x, []), (n, l))
                | None => ((n, [([n], [Efby [add_whens (Econst true_const) bool_type (fst cl)]
                                           [add_whens (Econst false_const) bool_type (fst cl)] [(bool_type, cl)]])]),
                          (Pos.succ n, (n, ((bool_type, cl), true))::l))
                end.

  (** Generate a if-then-else equation for (0 fby e), and return an expression using it *)
  Definition fby_iteexp (e0 : exp) (e : exp) (ann : ann) : FreshAnn (exp * list equation) :=
    let '(ty, cl) := ann in
    match e0 with
    | Econst c => ret (Efby [e0] [e] [ann], [])
    | _ => do (initid, eqs) <- init_var_for_clock cl;
          do px <- fresh_ident (ann, false);
          ret (Eite (Evar initid (bool_type, cl)) [e0] [Evar px ann] ([ty], cl),
               ([px], [Efby [Econst (init_type ty)] [e] [ann]])::eqs)
    end.

  Lemma fby_iteexp_spec : forall e0 e ty cl,
      (exists c, e0 = Econst c /\ fby_iteexp e0 e (ty, cl) = ret (Efby [e0] [e] [(ty, cl)], []))
      \/ fby_iteexp e0 e (ty, cl) = do (initid, eqs) <- init_var_for_clock cl;
                                   do px <- fresh_ident ((ty, cl), false);
                                   ret (Eite (Evar initid (bool_type, cl)) [e0] [Evar px (ty, cl)] ([ty], cl),
                                        ([px], [Efby [Econst (init_type ty)] [e] [(ty, cl)]])::eqs).
  Proof. destruct e0; eauto. Qed.

  (** Normalize a `fby inits es anns` expression, with inits and es already normalized *)
  Definition normalize_fby (inits : list exp) (es : list exp) (anns : list ann) : FreshAnn (list exp * list equation) :=
    do (es, eqs) <- map_bind2 (fun '((init, e), ann) => fby_iteexp init e ann) (combine (combine inits es) anns);
    ret (es, concat eqs).

  Definition normalize_reset (e : exp) : FreshAnn (exp * list equation) :=
    match e with
    | Evar v ann => ret (Evar v ann, [])
    | e => let ann := hd (bool_type, (Cbase, None)) (annot e) in
          do x <- fresh_ident (ann, false);
          ret (Evar x ann, ([x], [e])::[])
    end.

  Lemma normalize_reset_spec : forall e,
      (exists v, exists ann, e = Evar v ann /\ normalize_reset e = ret (Evar v ann, []))
      \/ normalize_reset e = let ann := hd (bool_type, (Cbase, None)) (annot e) in
                            do x <- fresh_ident (ann, false);
                            ret (Evar x ann, ([x], [e])::[]).
  Proof. destruct e; eauto. Qed.

  Fixpoint normalize_exp (is_control : bool) (e : exp) {struct e} : FreshAnn (list exp * list equation) :=
    let normalize_exps := fun es => do (es, eqs) <- map_bind2 (normalize_exp false) es; ret (concat es, concat eqs) in
    let normalize_controls := fun es => do (es, eqs) <- map_bind2 (normalize_exp true) es; ret (concat es, concat eqs) in
    match e with
    | Econst c => ret ([Econst c], [])
    | Evar v ann => ret ([Evar v ann], [])
    | Eunop op e1 ann =>
      do (e1', eqs) <- normalize_exp false e1;
      ret ([Eunop op (hd_default e1') ann], eqs)
    | Ebinop op e1 e2 ann =>
      do (e1', eqs1) <- normalize_exp false e1;
      do (e2', eqs2) <- normalize_exp false e2;
      ret ([Ebinop op (hd_default e1') (hd_default e2') ann], eqs1++eqs2)
    | Ewhen es clid b (tys, cl) =>
      do (es', eqs) <- normalize_exps es;
      ret (map (fun '(e, ty) => Ewhen [e] clid b ([ty], cl)) (combine es' tys), eqs)
    | Emerge clid es1 es2 (tys, cl) =>
      do (es1', eqs1) <- normalize_controls es1;
      do (es2', eqs2) <- normalize_controls es2;
      let merges := map (fun '((e1, e2), ty) => Emerge clid [e1] [e2] ([ty], cl)) (combine (combine es1' es2') tys) in
      if is_control then
        ret (merges, eqs1++eqs2)
      else
        do xs <- idents_for_anns (List.map (fun ty => (ty, cl)) tys);
        ret (List.map (fun '(id, ann) => Evar id ann) xs,
             (combine (List.map (fun '(id, _) => [id]) xs) (List.map (fun e => [e]) merges))++eqs1++eqs2)
    | Eite e es1 es2 (tys, cl) =>
      do (e', eqs0) <- normalize_exp false e;
      do (es1', eqs1) <- normalize_controls es1;
      do (es2', eqs2) <- normalize_controls es2;
      let ites := map (fun '((e1, e2), ty) => Eite (hd_default e') [e1] [e2] ([ty], cl)) (combine (combine es1' es2') tys) in
      if is_control then
        ret (ites, eqs0++eqs1++eqs2)
      else
        do xs <- idents_for_anns (List.map (fun ty => (ty, cl)) tys);
        ret (List.map (fun '(id, ann) => Evar id ann) xs,
             (combine (List.map (fun '(id, _) => [id]) xs) (List.map (fun e => [e]) ites))++eqs0++eqs1++eqs2)
    | Efby inits es anns =>
      do (inits', eqs1) <- normalize_exps inits;
      do (es', eqs2) <- normalize_exps es;
      do (fbys, eqs3) <- normalize_fby inits' es' anns;
      do xs <- idents_for_anns anns;
      ret (List.map (fun '(x, ann) => Evar x ann) xs,
           (List.map (fun '((x, _), fby) => ([x], [fby])) (combine xs fbys))++eqs1++eqs2++eqs3)
    | Eapp f es r anns =>
      do (r', eqs1) <- match r with
                      | Some er => do (er, eqs1) <- normalize_exp false er;
                                  do (er', eqs2) <- normalize_reset (hd_default er);
                                  ret (Some er', eqs1++eqs2)
                      | None => ret (None, [])
                      end;
      do (es', eqs2) <- normalize_exps es;
      do xs <- idents_for_anns anns;
      ret (List.map (fun '(id, ann) => Evar id ann) xs,
           (List.map fst xs, [Eapp f es' r' anns])::eqs1++eqs2)
    end.

  Definition normalize_exps (es : list exp) :=
    do (es, eqs) <- map_bind2 (normalize_exp false) es;
      ret (concat es, concat eqs).

  Definition normalize_rhs (keep_fby : bool) (e : exp) : FreshAnn (list exp * list equation) :=
    match e with
    | Eapp f es r anns =>
      do (r', eqs1) <- match r with
                      | Some er => do (er, eqs1) <- normalize_exp false er;
                                  do (er', eqs2) <- normalize_reset (hd_default er);
                                  ret (Some er', eqs1++eqs2)
                      | None => ret (None, [])
                      end;
      do (es', eqs2) <- normalize_exps es;
      ret ([Eapp f es' r' anns], eqs1++eqs2)
    | Efby inits es anns =>
      if keep_fby then
        do (inits', eqs1) <- normalize_exps inits;
        do (es', eqs2) <- normalize_exps es;
        do (fbys, eqs3) <- normalize_fby inits' es' anns;
        ret (fbys, eqs1++eqs2++eqs3)
      else normalize_exp true e
    | _ => normalize_exp true e
    end.
  Definition normalize_rhss (keep_fby : bool) (es : list exp) :=
    do (es, eqs) <- map_bind2 (normalize_rhs keep_fby) es; ret (concat es, concat eqs).

  Definition split_equation (eq : equation) : list equation :=
    let (xs, es) := eq in
    (fix aux (xs : list ident) (es : list exp) :=
       match es with
       | [] => []
       | hd::tl => let n := numstreams hd in
                  ((firstn n xs), [hd])::(aux (skipn n xs) tl)
       end) xs es.

  Definition normalize_equation (to_cut : list ident) (e : equation) : FreshAnn (list equation) :=
    let '(xs, es) := e in
    do (es', eqs) <- normalize_rhss (negb (existsb (fun x => existsb (fun c => Pos.eqb x c) to_cut) xs)) es;
    ret ((split_equation (xs, es'))++eqs).

  Fixpoint normalize_equations (to_cut : list ident) (eqs : list equation) : FreshAnn (list equation) :=
    match eqs with
    | [] => ret []
    | hd::tl => do eqs1 <- normalize_equation to_cut hd;
              do eqs2 <- normalize_equations to_cut tl;
              ret (eqs1++eqs2)
    end.

  Local Ltac solve_forall :=
    match goal with
    | H: Forall _ ?l |- Forall _ ?l =>
      eapply Forall_impl; [ | eapply H]; intros; simpl in *; eauto
    | _ => idtac
    end.

  (** ** Propagation of the st_valid property *)

  Fact idents_for_anns_st_valid : forall anns res st st',
      idents_for_anns anns st = (res, st') ->
      fresh_st_valid st ->
      fresh_st_valid st'.
  Proof.
    induction anns; intros res st st' Hidforanns Hvalid;
      simpl in *; repeat inv_bind.
    - assumption.
    - eapply IHanns; eauto.
  Qed.
  Hint Resolve idents_for_anns_st_valid.

  Fact init_var_for_clock_st_valid : forall cl res st st',
      init_var_for_clock cl st = (res, st') ->
      fresh_st_valid st ->
      fresh_st_valid st'.
  Proof.
    intros cl res [n l] st' Hinit Hvalid.
    unfold init_var_for_clock in Hinit.
    destruct (find (fun '(_, (_, cl', isinit)) => isinit && (cl ==b cl')) l).
    - destruct p. inv Hinit. assumption.
    - inv Hinit. destruct Hvalid as [Hlt Hndup].
      constructor.
      + constructor.
        * apply Pos.lt_succ_diag_r.
        * eapply Forall_impl; eauto.
          intros [x _] Hlt'. apply Pos.lt_lt_succ; auto.
      + constructor; auto.
        intro contra.
        induction l; inv Hlt; inv Hndup; simpl in *; auto.
        destruct contra; subst; auto.
        apply Pos.lt_irrefl in H1; auto.
  Qed.
  Hint Resolve init_var_for_clock_st_valid.

  Fact normalize_fby_st_valid : forall inits es anns res st st',
      normalize_fby inits es anns st = (res, st') ->
      fresh_st_valid st ->
      fresh_st_valid st'.
  Proof with eauto.
    intros inits es anns res st st' Hnorm Hfresh.
    unfold normalize_fby in Hnorm.
    repeat inv_bind.
    eapply map_bind2_st_valid; eauto.
    apply Forall_forall.
    intros [[i e] [ty cl]] HIn e' eq' st1 st1' Hfby Hst1.
    destruct (fby_iteexp_spec i e ty cl) as [[c [Hite1 Hite2]]|Hite]; subst.
    - rewrite Hite2 in Hfby; clear Hite2.
      inv Hfby. auto.
    - rewrite Hite in Hfby.
      repeat inv_bind...
  Qed.
  Hint Resolve normalize_fby_st_valid.

  Fact normalize_reset_st_valid : forall e res st st',
      normalize_reset e st = (res, st') ->
      fresh_st_valid st ->
      fresh_st_valid st'.
  Proof.
    intros e res st st' Hnorm Hvalid.
    destruct (normalize_reset_spec e) as [[v [ann [He Hnorm']]]|Hnorm']; subst;
      rewrite Hnorm' in Hnorm; clear Hnorm';
        simpl in *; repeat inv_bind; eauto.
  Qed.
  Hint Resolve normalize_reset_st_valid.

  Local Ltac solve_st_valid :=
    match goal with
    | H : map_bind2 _ _ _ = (_, _, ?st) |- fresh_st_valid ?st =>
      eapply map_bind2_st_valid; eauto; solve_forall
    | H : normalize_fby _ _ _ _ = (_, _, ?st) |- fresh_st_valid ?st =>
      eapply normalize_fby_st_valid; eauto
    | H : idents_for_anns _ _ = (_, ?st) |- fresh_st_valid ?st =>
      eapply idents_for_anns_st_valid; eauto
    end.

  Fact normalize_exp_st_valid : forall e is_control res st st',
      normalize_exp is_control e st = (res, st') ->
      fresh_st_valid st ->
      fresh_st_valid st'.
  Proof.
    induction e using exp_ind2; intros is_control res st st' Hnorm Hvalid;
      simpl in Hnorm.
    - (* const *)
      inv_bind; auto.
    - (* var *)
      inv_bind; auto.
    - (* unop *)
      repeat inv_bind; eauto.
    - (* binop *)
      repeat inv_bind; destruct x1; eauto.
    - (* fby *)
      repeat inv_bind; repeat solve_st_valid.
    - (* when *)
      destruct a.
      repeat inv_bind; repeat solve_st_valid.
    - (* merge *)
      destruct a.
      destruct is_control; repeat inv_bind; repeat solve_st_valid.
    - (* ite *)
      destruct a.
      destruct is_control; repeat inv_bind; repeat solve_st_valid.
    - (* app *)
      repeat inv_bind; repeat solve_st_valid;
        destruct ro; repeat inv_bind; eauto.
  Qed.
  Hint Resolve normalize_exp_st_valid.

  Fact normalize_rhs_st_valid : forall e keep_fby res st st',
      normalize_rhs keep_fby e st = (res, st') ->
      fresh_st_valid st ->
      fresh_st_valid st'.
  Proof.
    intros e keep_fby res st st' Hnorm Hfresh.
    destruct e; try (solve [eapply normalize_exp_st_valid; eauto]);
      simpl in Hnorm; unfold normalize_exps in *.
    - (* fby *)
      destruct keep_fby; repeat inv_bind;
        repeat solve_st_valid;
        eapply Forall_forall; intros; eauto.
    - (* app *)
      repeat inv_bind.
      repeat solve_st_valid.
      + eapply Forall_forall; intros; eauto.
      + destruct o; repeat inv_bind; eauto.
  Qed.
  Hint Resolve normalize_rhs_st_valid.

  Fact normalize_equation_st_valid : forall e to_cut res st st',
      normalize_equation to_cut e st = (res, st') ->
      fresh_st_valid st ->
      fresh_st_valid st'.
  Proof.
    intros [xs es] to_cut res st st' Hnorm Hvalid.
    simpl in *; unfold normalize_rhss in *; repeat inv_bind.
    eapply map_bind2_st_valid; eauto.
    apply Forall_forall. intros; eauto.
  Qed.
  Hint Resolve normalize_equation_st_valid.

  Fact normalize_equations_st_valid : forall eqs to_cut res st st',
      normalize_equations to_cut eqs st = (res, st') ->
      fresh_st_valid st ->
      fresh_st_valid st'.
  Proof.
    induction eqs; intros to_cut res st st' Hnorm Hvalid;
      simpl in *; repeat inv_bind.
    - assumption.
    - eapply IHeqs; eauto.
  Qed.

  (** ** Propagation of the st_follows property *)

  Fact idents_for_anns_st_follows : forall anns res st st',
      idents_for_anns anns st = (res, st') ->
      fresh_st_follows st st'.
  Proof.
    induction anns; intros res st st' Hidforanns;
      simpl in *; repeat inv_bind.
    - reflexivity.
    - etransitivity; eauto.
  Qed.
  Hint Resolve idents_for_anns_st_follows.

  Fact init_var_for_clock_st_follows : forall cl res st st',
      init_var_for_clock cl st = (res, st') ->
      fresh_st_follows st st'.
  Proof.
    intros cl res [n l] [n' l'] Hinit.
    unfold init_var_for_clock in Hinit.
    destruct (find (fun '(_, (_, cl', isinit)) => isinit && (cl ==b cl')) l).
    - destruct p. inv Hinit. reflexivity.
    - inv Hinit.
      unfold fresh_st_follows, smallest_ident in *; simpl in *.
      split.
      + apply incl_tl. reflexivity.
      + induction l as [|[a ?]]; simpl in *.
        * rewrite Pos.min_glb_iff.
          split.
          -- reflexivity.
          -- apply Pos.lt_le_incl.
             apply Pos.lt_succ_diag_r.
        * rewrite Pos.min_glb_iff in *.
          destruct IHl as [IHl1 IHl2].
          split.
          -- etransitivity; eauto.
             eapply Pos.le_min_r.
          -- eapply Pos.min_le_compat_l; eauto.
  Qed.
  Hint Resolve init_var_for_clock_st_follows.

  Fact fby_iteexp_st_follows : forall e0 e ann res st st',
      fby_iteexp e0 e ann st = (res, st') ->
      fresh_st_follows st st'.
  Proof.
    intros e0 e [ty cl] res st st' Hfby.
    destruct (fby_iteexp_spec e0 e ty cl) as [[? [? Hspec]]|Hspec]; subst;
      rewrite Hspec in Hfby; clear Hspec; repeat inv_bind.
    - reflexivity.
    - etransitivity; eauto.
  Qed.
  Hint Resolve fby_iteexp_st_follows.

  Fact normalize_fby_st_follows : forall inits es anns res st st',
      normalize_fby inits es anns st = (res, st') ->
      fresh_st_follows st st'.
  Proof.
    intros inits es anns res st st' Hnorm.
    unfold normalize_fby in Hnorm; repeat inv_bind.
    eapply map_bind2_st_follows; eauto.
    rewrite Forall_forall.
    intros [[i e] [ty cl]] HIn e' eq' st1 st1' Hfby. eauto.
  Qed.
  Hint Resolve normalize_fby_st_follows.

  Fact normalize_reset_st_follows : forall e res st st',
      normalize_reset e st = (res, st') ->
      fresh_st_follows st st'.
  Proof.
    intros e res st st' Hnorm.
    destruct (normalize_reset_spec e) as [[v [ann [He Hnorm']]]|Hnorm']; subst;
      simpl in *; repeat inv_bind.
    - reflexivity.
    - rewrite Hnorm' in Hnorm; clear Hnorm'.
      repeat inv_bind. eauto.
  Qed.
  Hint Resolve normalize_reset_st_follows.

  Local Ltac solve_st_follows :=
    match goal with
    | H : map_bind2 _ _ ?st = _ |- fresh_st_follows ?st _ =>
      etransitivity; [ eapply map_bind2_st_follows; eauto; solve_forall | ]
    | H : normalize_fby _ _ _ ?st = _ |- fresh_st_follows ?st _ =>
      etransitivity; [ eapply normalize_fby_st_follows; eauto | ]
    | H : normalize_reset _ ?st = _ |- fresh_st_follows ?st _ =>
      etransitivity; [ eapply normalize_reset_st_follows; eauto | ]
    | H : idents_for_anns _ ?st = _ |- fresh_st_follows ?st _ =>
      etransitivity; [ eapply idents_for_anns_st_follows; eauto | ]
    | |- fresh_st_follows ?st ?st =>
      reflexivity
    end.

  Fact normalize_exp_st_follows : forall e is_control res st st',
      normalize_exp is_control e st = (res, st') ->
      fresh_st_follows st st'.
  Proof.
    intros e.
    induction e using exp_ind2; intros is_control res st st' Hnorm;
      simpl in Hnorm.
    - (* const *)
      inv_bind; reflexivity.
    - (* var *)
      inv_bind; reflexivity.
    - (* unop *)
      repeat inv_bind; eauto.
    - (* binop *)
      repeat inv_bind; etransitivity; eauto.
    - (* fby *)
      repeat inv_bind; repeat solve_st_follows.
    - (* when *)
      destruct a.
      repeat inv_bind; repeat solve_st_follows.
    - (* merge *)
      destruct a.
      destruct is_control; repeat inv_bind; repeat solve_st_follows.
    - (* ite *)
      destruct a.
      destruct is_control; repeat inv_bind;
        (etransitivity; [ eapply IHe; eauto | repeat solve_st_follows ]).
    - (* app *)
      destruct ro; repeat inv_bind; repeat solve_st_follows;
        (etransitivity; [ eapply H; eauto | repeat solve_st_follows ]).
  Qed.
  Hint Resolve normalize_exp_st_follows.

  Corollary normalize_exps_st_follows : forall es res st st',
      normalize_exps es st = (res, st') ->
      fresh_st_follows st st'.
  Proof.
    intros es res st st' Hnorm.
    unfold normalize_exps in Hnorm. repeat inv_bind.
    eapply map_bind2_st_follows; eauto.
    rewrite Forall_forall; intros; eauto.
  Qed.

  Fact normalize_rhs_st_follows : forall e keep_fby res st st',
      normalize_rhs keep_fby e st = (res, st') ->
      fresh_st_follows st st'.
  Proof.
    intros e keep_fby res st st' Hnorm.
    destruct e; try (solve [eapply normalize_exp_st_follows; eauto]);
      simpl in Hnorm; unfold normalize_exps in *.
    - (* fby *)
      destruct keep_fby; repeat inv_bind;
        repeat solve_st_follows;
        eapply Forall_forall; intros; eauto.
    - (* app *)
      destruct o; repeat inv_bind.
      + etransitivity. eapply normalize_exp_st_follows; eauto. repeat solve_st_follows.
        eapply Forall_forall; intros; eauto.
      + repeat solve_st_follows.
        eapply Forall_forall; intros; eauto.
  Qed.
  Hint Resolve normalize_rhs_st_follows.

  Fact normalize_equation_st_follows : forall e to_cut res st st',
      normalize_equation to_cut e st = (res, st') ->
      fresh_st_follows st st'.
  Proof.
    intros [xs es] to_cut res st st' Hnorm.
    simpl in *; unfold normalize_rhss in *; repeat inv_bind.
    eapply map_bind2_st_follows; eauto.
    apply Forall_forall. intros; eauto.
  Qed.
  Hint Resolve normalize_equation_st_follows.

  Fact normalize_equations_st_follows : forall eqs to_cut res st st',
      normalize_equations to_cut eqs st = (res, st') ->
      fresh_st_follows st st'.
  Proof.
    induction eqs; intros to_cut res st st' Hnorm;
      simpl in *; repeat inv_bind.
    - reflexivity.
    - etransitivity; eauto.
  Qed.

  (** ** Length of normalized expression *)

  Ltac idents_for_anns_length :=
    match goal with
    | H : idents_for_anns ?anns _ = (?ids, _) |- length ?ids = length ?anns =>
      apply idents_for_anns_values in H;
      rewrite Forall2_forall2 in H; destruct H;
      auto
    | H : idents_for_anns (List.map _ ?anns) _ = (?ids, _) |- length ?ids = length ?anns =>
      apply idents_for_anns_values in H;
      rewrite Forall2_forall2 in H; destruct H;
      rewrite map_length in *; auto
    end.

  Ltac rewrite_Forall_forall :=
    match goal with
    | H : Forall _ _ |- _ =>
      rewrite Forall_forall in H
    | H : Forall2 _ _ _ |- _ =>
      rewrite Forall2_forall2 in H; destruct H
    | H : Forall3 _ _ _ _ |- _ =>
      rewrite Forall3_forall3 in H; destruct H as [? [? ?]]
    | |- Forall _ _ =>
      rewrite Forall_forall; intros; subst
    | |- Forall2 _ _ _ =>
      rewrite Forall2_forall2; repeat split; auto; intros; subst
    | |- Forall3 _ _ _ _ =>
      rewrite Forall3_forall3; repeat split; auto; intros; subst
    end.

  Fact map_bind2_length : forall is_control es es' eqs' st st',
      Forall2 (fun e es' => forall eqs' st st',
                   normalize_exp is_control e st = (es', eqs', st') ->
                   length es' = numstreams e) es es' ->
    map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
    length (concat es') = length (typesof es).
  Proof.
    intros is_control es es' eqs' st st' Hf Hmap.
    apply map_bind2_values in Hmap.
    unfold typesof. rewrite flat_map_concat_map.
    apply concat_length_eq.
    repeat rewrite_Forall_forall.
    + rewrite map_length; auto.
    + replace (length es') in *.
      specialize (H3 (hd_default []) a [] _ _ _ _ H4 eq_refl eq_refl eq_refl) as [? [? H3]].
      erewrite (map_nth' _ _ _ (hd_default [])); eauto.
      rewrite numstreams_length_typeof.
      eapply H0; eauto.
  Qed.

  Local Hint Resolve nth_In.
  Fact normalize_exp_length : forall G vars e is_control es' eqs' st st',
      wt_exp G vars e ->
      normalize_exp is_control e st = (es', eqs', st') ->
      length es' = numstreams e.
  Proof with eauto.
    intros G vars e.
    rewrite <- numstreams_length_typeof.
    induction e using exp_ind2; intros is_control es' eqs' st st' Hwt Hnorm;
      [| | | | | | destruct is_control | destruct is_control | ];
      simpl in *; inv Hwt; inv Hnorm; repeat inv_bind;
        repeat rewrite map_length in *; auto;
          try idents_for_anns_length.
    - (* when *)
      assert (length (concat x1) = length (typesof es)).
      { eapply map_bind2_length...
        eapply map_bind2_values in H0.
        repeat rewrite_Forall_forall.
        rewrite <- numstreams_length_typeof...
      }
      rewrite combine_length. rewrite H1.
      apply PeanoNat.Nat.min_id.
    - (* merge (control) *)
      assert (length (concat x3) = length (typesof ets)).
      { eapply map_bind2_length...
        eapply map_bind2_values in H1.
        repeat rewrite_Forall_forall.
        rewrite <- numstreams_length_typeof...
      }
      assert (length (concat x5) = length (typesof efs)).
      { eapply map_bind2_length...
        eapply map_bind2_values in H2.
        repeat rewrite_Forall_forall.
        rewrite <- numstreams_length_typeof...
      }
      repeat rewrite combine_length.
      replace (length (concat x3)).
      replace (length (concat x5)).
      rewrite H9.
      repeat rewrite PeanoNat.Nat.min_id. reflexivity.
    - (* ite (control) *)
      assert (length (concat x5) = length (typesof ets)).
      { eapply map_bind2_length...
        eapply map_bind2_values in H2.
        repeat rewrite_Forall_forall.
        rewrite <- numstreams_length_typeof...
      }
      assert (length (concat x7) = length (typesof efs)).
      { eapply map_bind2_length...
        eapply map_bind2_values in H3.
        repeat rewrite_Forall_forall.
        rewrite <- numstreams_length_typeof...
      }
      repeat rewrite combine_length.
      replace (length (concat x5)).
      replace (length (concat x7)).
      rewrite H10.
      repeat rewrite PeanoNat.Nat.min_id. reflexivity.
  Qed.

  Corollary map_bind2_normalize_exp_length : forall G vars is_control es es' eqs' st st',
      Forall (wt_exp G vars) es ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      length (concat es') = length (typesof es).
  Proof.
    intros G vars is_control es es' eqs' st st' Hf Hmap.
    eapply map_bind2_length; eauto.
    eapply map_bind2_values in Hmap.
    repeat rewrite_Forall_forall.
    eapply normalize_exp_length; eauto.
  Qed.

  Corollary normalize_exps_length : forall G vars es es' eqs' st st',
      Forall (wt_exp G vars) es ->
      normalize_exps es st = (es', eqs', st') ->
      length es' = length (typesof es).
  Proof.
    intros G vars es es' eqs' st st' Hwt Hnorm.
    unfold normalize_exps in Hnorm.
    repeat inv_bind.
    eapply map_bind2_normalize_exp_length; eauto.
  Qed.

  Fact normalize_fby_length : forall inits es anns es' eqs' st st',
      length inits = length anns ->
      length es = length anns ->
      normalize_fby inits es anns st = (es', eqs', st') ->
      length es' = length anns.
  Proof.
    intros inits es anns es' eqs' st st' Hlen1 Hlen2 Hnorm.
    unfold normalize_fby in Hnorm.
    repeat inv_bind.
    apply map_bind2_values in H.
    rewrite_Forall_forall; clear H0 H1.
    repeat rewrite combine_length in H.
    replace (length inits) in *.
    replace (length es) in *.
    repeat rewrite PeanoNat.Nat.min_id in H.
    auto.
  Qed.

  Fact normalize_rhs_length : forall G vars e keep_fby es' eqs' st st',
      wt_exp G vars e ->
      normalize_rhs keep_fby e st = (es', eqs', st') ->
      (length es' = 1 \/ length es' = numstreams e).
  Proof.
    intros G vars e keep_fby es' eqs' st st' Hwt Hnorm;
      destruct e; unfold normalize_rhs in Hnorm;
        try (solve [right; eapply normalize_exp_length; eauto]);
        try (destruct o); destruct keep_fby; repeat inv_bind; auto.
    - (* keep_fby = true *)
      right. inv Hwt.
      eapply normalize_fby_length; eauto.
      + eapply normalize_exps_length in H; eauto.
        replace (typesof l) in H.
        rewrite map_length in H.
        assumption.
      + eapply normalize_exps_length in H0; eauto.
        replace (typesof l0) in H0.
        rewrite map_length in H0.
        assumption.
    - (* keep_fby = false *)
      eapply normalize_exp_length in Hnorm; eauto.
  Qed.

  (** ** Preservation of typeof *)

  Fact normalize_exp_typeof : forall G vars e is_control es' eqs' st st',
      wt_exp G vars e ->
      normalize_exp is_control e st = (es', eqs', st')  ->
      typesof es' = typeof e.
  Proof.
    induction e; intros is_control es' eqs' st st' Hwt Hnorm;
      specialize (normalize_exp_length _ _ _ _ es' eqs' st st' Hwt Hnorm) as Hlength;
      simpl in *.
    - (* const *)
      repeat inv_bind; reflexivity.
    - (* var *)
      repeat inv_bind; reflexivity.
    - (* unop *)
      repeat inv_bind; reflexivity.
    - (* binop *)
      repeat inv_bind; reflexivity.
    - (* fby *)
      repeat inv_bind.
      apply idents_for_anns_values in H2.
      clear H1 Hwt; (induction H2; [ auto | destruct y; subst; simpl; f_equal; auto ]).
    - (* when *)
      destruct l0. repeat inv_bind.
      rewrite map_length in Hlength.
      assert (Forall2 (fun '(e, ty) ty' => typeof (Ewhen [e] i b ([ty], n)) = [ty']) (combine (concat x0) l0) l0) as Hf.
      { rewrite_Forall_forall.
        destruct nth eqn:Hnth; simpl; f_equal.
        destruct a.
        specialize (combine_length_r _ _ Hlength) as Hlen'.
        specialize (combine_nth_r _ _ n0 e0 t0 Hlen') as [d Hnth'].
        rewrite Hnth' in Hnth; inv Hnth.
        apply nth_indep; rewrite <- Hlength; auto.
      } clear Hwt.
      induction Hf; simpl; auto.
      destruct x; simpl in *. inv H0. f_equal; auto.
    - (* merge *)
      clear Hwt.
      destruct l1.
      destruct is_control; repeat inv_bind; rewrite map_length in *.
      + (* control *)
        assert (Forall2 (fun '(e1, e2, ty) ty' => typeof (Emerge i [e1] [e2] ([ty], n)) = [ty'])
                        (combine (combine (concat x2) (concat x4)) l1) l1) as Hf.
        { rewrite_Forall_forall.
          destruct (nth n0 _ a) eqn:Hnth. destruct p; simpl; f_equal.
          destruct a as [[d1 d2] d3].
          specialize (combine_length_r _ _ Hlength) as Hlen'.
          specialize (combine_nth_r _ _ n0 (d1, d2) d3 Hlen') as [d Hnth'].
          rewrite Hnth' in Hnth; inv Hnth.
          apply nth_indep; rewrite <- Hlength; auto.
        }
        induction Hf; simpl; auto.
        destruct x as [[e1 e2] a]. inv Hlength. simpl in *.
        inv H1. f_equal; auto.
      + (* exp *)
        apply idents_for_anns_values in H1.
        assert (Forall2 (fun ty '(id, a) => (typeof (Evar id a)) = [ty]) l1 x5) as Hf.
        { repeat rewrite_Forall_forall.
          destruct (nth _ _ b) eqn:Hnth; simpl. f_equal.
          rewrite map_length in *.
          specialize (H2 a0 b n0 _ _ H3 eq_refl eq_refl); rewrite Hnth in H2.
          symmetry in H2. erewrite map_nth' in H2; eauto.
          destruct a0; inv H2; simpl; eauto.
        }
        clear H1. induction Hf; simpl; auto.
        destruct y; simpl in *. inv Hlength. inv H1. f_equal; auto.
    - (* ite *)
      clear Hwt.
      destruct l1.
      destruct is_control; repeat inv_bind; rewrite map_length in *.
      + (* control *)
        assert (Forall2 (fun '(e1, e2, ty) ty' => typeof (Eite (hd_default x) [e1] [e2] ([ty], n)) = [ty'])
                        (combine (combine (concat x5) (concat x7)) l1) l1) as Hf.
        { rewrite_Forall_forall.
          destruct (nth n0 _ a) eqn:Hnth. destruct p; simpl; f_equal.
          destruct a as [[d1 d2] d3].
          specialize (combine_length_r _ _ Hlength) as Hlen'.
          specialize (combine_nth_r _ _ n0 (d1, d2) d3 Hlen') as [d Hnth'].
          rewrite Hnth' in Hnth; inv Hnth.
          apply nth_indep; rewrite <- Hlength; auto.
        }
        induction Hf; simpl; auto.
        destruct x2 as [[e1 e2] a]. inv Hlength. simpl in *.
        inv H2. f_equal; auto.
      + (* exp *)
        apply idents_for_anns_values in H2.
        assert (Forall2 (fun ty '(id, a) => (typeof (Evar id a)) = [ty]) l1 x8) as Hf.
        { repeat rewrite_Forall_forall.
          destruct (nth _ _ b) eqn:Hnth; simpl. f_equal.
          rewrite map_length in *.
          specialize (H3 a0 b n0 _ _ H4 eq_refl eq_refl); rewrite Hnth in H3.
          symmetry in H3. erewrite map_nth' in H3; eauto.
          destruct a0; inv H3; simpl; eauto.
        }
        clear H2. induction Hf; simpl; auto.
        destruct y; simpl in *. inv Hlength. inv H2. f_equal; auto.
    - (* app *)
      clear Hwt.
      repeat inv_bind.
      apply idents_for_anns_values in H1.
      induction H1; simpl in *; auto.
      destruct y; subst; simpl. inv Hlength. f_equal; auto.
  Qed.

  Corollary map_bind2_normalize_exp_typeof :
    forall G vars is_control es es' eqs' st st',
      Forall (wt_exp G vars) es ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      typesof (concat es') = typesof es.
  Proof.
    intros G vars is_control es es' a2s st st' Hwt Hmap.
    apply map_bind2_values in Hmap.
    induction Hmap.
    - constructor.
    - inv Hwt. simpl.
      destruct H as [? [? H]].
      specialize (normalize_exp_typeof _ _ _ _ _ _ _ _ H2 H) as Htypeof.
      unfold typesof in *.
      repeat rewrite flat_map_concat_map in *.
      rewrite map_app; rewrite concat_app.
      f_equal; eauto.
  Qed.

  Fact fby_iteexp_typeof : forall e0 e ann es' eqs' st st',
      fby_iteexp e0 e ann st = (es', eqs', st') ->
      typeof es' = [fst ann].
  Proof.
    intros e0 e ann es' eqs' st st' Hfby.
    destruct ann as [ty cl]; simpl.
    specialize (fby_iteexp_spec e0 e ty cl) as [[c [Heq Hspec]]|Hspec].
    - rewrite Hspec in Hfby; clear Hspec. inv Hfby. auto.
    - rewrite Hspec in Hfby; clear Hspec.
      repeat inv_bind. reflexivity.
  Qed.

  Fact normalize_fby_typeof : forall inits es anns es' eqs' st st',
      length inits = length anns ->
      length es = length anns ->
      normalize_fby inits es anns st = (es', eqs', st') ->
      typesof es' = List.map fst anns.
  Proof.
    intros inits es anns es' eqs' st st' Hlen1 Hlen2 Hnorm.
    specialize (normalize_fby_length _ _ _ _ _ _ _ Hlen1 Hlen2 Hnorm) as Hlen.
    unfold normalize_fby in Hnorm.
    repeat inv_bind.
    apply map_bind2_values in H.
    assert (Forall2 (fun e a => typeof e = [fst a]) es' anns) as Hf.
    { repeat rewrite_Forall_forall.
      rewrite <- H in H2.
      specialize (H1 (a, a, b) a [] _ _ _ _ H2 eq_refl eq_refl eq_refl); destruct H1 as [? [? ?]].
      destruct nth eqn:Hnth in H1. destruct p.
      apply fby_iteexp_typeof in H1.
      rewrite combine_nth in Hnth; auto.
      + inv Hnth. assumption.
      + rewrite combine_length.
        replace (length inits). replace (length es).
        apply PeanoNat.Nat.min_id.
    } clear H Hlen Hlen1 Hlen2.
    induction Hf; simpl; auto.
    rewrite H. simpl. f_equal; auto.
  Qed.

  Fact normalize_rhs_typeof : forall G vars e keep_fby es' eqs' st st',
      wt_exp G vars e ->
      normalize_rhs keep_fby e st = (es', eqs', st') ->
      typesof es' = typeof e.
  Proof.
    intros G vars e keep_fby es' eqs' st st' Hwt Hnorm.
    destruct e; unfold normalize_rhs in Hnorm;
      try (solve [eapply normalize_exp_typeof in Hnorm; eauto]).
    - (* fby *)
      destruct keep_fby.
      + repeat inv_bind. inv Hwt.
        eapply normalize_fby_typeof; eauto.
        * replace (length l1) with (length (typesof l)) by (rewrite H8; apply map_length).
          eapply normalize_exps_length; eauto.
        * replace (length l1) with (length (typesof l0)) by (rewrite H7; apply map_length).
          eapply normalize_exps_length; eauto.
      + eapply normalize_exp_typeof in Hnorm; eauto.
    - (* app *)
      destruct o; repeat inv_bind; apply app_nil_r.
  Qed.

  Corollary normalize_rhss_typeof : forall G vars es keep_fby es' eqs' st st',
      Forall (wt_exp G vars) es ->
      normalize_rhss keep_fby es st = (es', eqs', st') ->
      typesof es' = typesof es.
  Proof.
    intros G vars es keep_fby es' eqs' st st' Hf Hnorm.
    unfold normalize_rhss in Hnorm. repeat inv_bind.
    apply map_bind2_values in H.
    induction H; simpl in *.
    - reflexivity.
    - inv Hf.
      destruct H as [? [? H]]. eapply normalize_rhs_typeof in H; eauto.
      unfold typesof in*. rewrite flat_map_concat_map in *.
      rewrite map_app. rewrite concat_app.
      f_equal; auto.
  Qed.

  (** ** Propagation of the variable permutation property *)

  Fact idents_for_anns_vars_perm : forall anns ids st st',
      idents_for_anns anns st = (ids, st') ->
      Permutation ((map fst ids)++(map fst (snd st))) (map fst (snd st')).
  Proof.
    induction anns; intros ids st st' Hidents; simpl in Hidents; repeat inv_bind.
    - reflexivity.
    - apply fresh_ident_vars_perm in H.
      apply IHanns in H0.
      etransitivity. 2: eapply H0.
      etransitivity. eapply Permutation_middle.
      apply Permutation_app_head. assumption.
  Qed.

  Fact init_var_for_clock_vars_perm : forall cl id eqs st st',
      init_var_for_clock cl st = ((id, eqs), st') ->
      Permutation ((vars_defined eqs)++(map fst (snd st))) ((map fst (snd st'))).
  Proof.
    intros cl id eqs st st' Hinit.
    destruct st; destruct st'; simpl in *.
    destruct (find (fun '(_, (_, cl', isinit)) => isinit && (cl ==b cl')) l).
    - destruct p. inv Hinit. reflexivity.
    - inv Hinit; simpl. reflexivity.
  Qed.

  Fact map_bind2_vars_perm {A B} : forall (k : A -> FreshAnn (B * list equation)) es es' eqs' st st',
      map_bind2 k es st = (es', eqs', st') ->
      Forall (fun e => forall es' eqs' st st',
                  k e st = (es', eqs', st') ->
                  Permutation ((vars_defined eqs')++(map fst (snd st))) (map fst (snd st'))) es ->
      Permutation ((vars_defined (concat eqs'))++(map fst (snd st))) (map fst (snd st')).
  Proof.
    induction es; intros es' eqs' st st' Hmap Hf;
      simpl in *; repeat inv_bind.
    - reflexivity.
    - inv Hf.
      specialize (IHes _ _ _ _ H0 H4).
      specialize (H3 _ _ _ _ H).
      etransitivity. 2: apply IHes.
      unfold vars_defined in *. rewrite <- flat_map_app.
      rewrite <- app_assoc. rewrite Permutation_swap.
      apply Permutation_app_head. assumption.
  Qed.

  Fact normalize_fby_vars_perm : forall inits es anns es' eqs' st st',
      normalize_fby inits es anns st = ((es', eqs'), st') ->
      Permutation ((vars_defined eqs')++(map fst (snd st))) (map fst (snd st')).
  Proof.
    intros inits es anns es' eqs' st st' Hnorm.
    unfold normalize_fby in Hnorm; repeat inv_bind.
    eapply map_bind2_vars_perm. eapply H.
    apply Forall_forall; intros [[e0 e] [ty cl]] Hin; intros.
    destruct (fby_iteexp_spec e0 e ty cl) as [[c [Hc Hspec]]|Hspec];
      subst; rewrite Hspec in H0; clear Hspec; repeat inv_bind.
    - reflexivity.
    - apply fresh_ident_vars_perm in H1.
      etransitivity. 2 : apply H1.
      apply perm_skip.
      eapply init_var_for_clock_vars_perm; eauto.
  Qed.

  Fact normalize_reset_vars_perm : forall e e' eqs' st st',
      normalize_reset e st = ((e', eqs'), st') ->
      Permutation ((vars_defined eqs')++(map fst (snd st))) (map fst (snd st')).
  Proof.
    intros e e' eqs' st st' Hnorm.
    destruct (normalize_reset_spec e) as [[v [ann [Hv Hspec]]]| Hspec];
      subst; rewrite Hspec in Hnorm; clear Hspec.
    - inv_bind. reflexivity.
    - destruct (hd _ _); simpl in *. repeat inv_bind.
      eapply fresh_ident_vars_perm; eauto.
  Qed.

  Fact normalize_exp_vars_perm : forall G vars e is_control es' eqs' st st',
      wt_exp G vars e ->
      normalize_exp is_control e st = ((es', eqs'), st') ->
      Permutation ((vars_defined eqs')++(map fst (snd st))) (map fst (snd st')).
  Proof with eauto.
    induction e using exp_ind2; intros is_control e' eqs' st st' Hwt Hnorm;
      simpl in Hnorm; inv Hwt.
    - (* const *)
      repeat inv_bind...
    - (* var *)
      repeat inv_bind...
    - (* unop *)
      repeat inv_bind...
    - (* binop *)
      repeat inv_bind.
      unfold vars_defined in *; rewrite <- flat_map_app; rewrite <- app_assoc.
      apply IHe1 in H...
      apply IHe2 in H0...
      etransitivity. 2: eauto.
      rewrite Permutation_swap.
      apply Permutation_app_head...
    - (* fby *)
      repeat inv_bind.
      assert (length x5 = length x8) as Hlen58.
      { apply idents_for_anns_values in H9; rewrite Forall2_forall2 in H9; destruct H9 as [? _].
        apply normalize_fby_length in H3.
        replace (length x5)...
        + replace (length a) with (length (typesof e0s)) by (rewrite H7; apply map_length).
          eapply map_bind2_normalize_exp_length; eauto.
        + replace (length a) with (length (typesof es)) by (rewrite H6; apply map_length).
          eapply map_bind2_normalize_exp_length; eauto. }
      apply map_bind2_vars_perm in H1. 2: (rewrite Forall_forall in *; eauto).
      apply map_bind2_vars_perm in H2. 2: (rewrite Forall_forall in *; eauto).
      apply normalize_fby_vars_perm in H3.
      apply idents_for_anns_vars_perm in H9.
      unfold vars_defined in *. rewrite flat_map_concat_map in *.
      etransitivity. 2 : apply H9. clear H9.
      repeat rewrite map_app. rewrite map_map; simpl.
      replace (map (fun x => fst (let '(x0, _, fby) := x in ([x0], [fby]))) (combine x8 x5)) with (map (fun x => [fst x]) x8).
      2: { refine (list_ind2 (fun l1 l2 => _) _ _ x5 x8 Hlen58); simpl.
           + reflexivity.
           + intros. destruct b; simpl.
             f_equal. assumption. }
      repeat rewrite concat_app.
      replace (concat (map (fun x => [fst x]) x8)) with (map fst x8).
      2: { clear Hlen58. induction x8; simpl; f_equal; auto. }
      repeat rewrite <- app_assoc. apply Permutation_app_head.
      etransitivity. 2: eauto.
      rewrite app_assoc. rewrite Permutation_swap. apply Permutation_app_head.
      etransitivity. 2: eauto.
      rewrite <- app_assoc. rewrite Permutation_swap. apply Permutation_app_head.
      assumption.
    - (* when *)
      repeat inv_bind.
      eapply map_bind2_vars_perm...
      rewrite Forall_forall in *. intros...
    - (* merge *)
      destruct is_control; repeat inv_bind.
      + apply map_bind2_vars_perm in H1. 2: (rewrite Forall_forall in *; eauto).
        apply map_bind2_vars_perm in H2. 2: (rewrite Forall_forall in *; eauto).
        etransitivity. 2: apply H2.
        unfold vars_defined in *; rewrite <- flat_map_app; repeat rewrite <- app_assoc.
        rewrite Permutation_swap. apply Permutation_app_head.
        assumption.
      + unfold vars_defined; rewrite flat_map_concat_map.
        repeat rewrite map_app. repeat rewrite concat_app.
        rewrite combine_map_fst'.
        2: {
          repeat rewrite map_length. repeat rewrite combine_length.
          assert (length (concat x3) = length (typesof ets)) as Hlen3 by (eapply map_bind2_normalize_exp_length; eauto).
          assert (length (concat x7) = length (typesof efs)) as Hlen7 by (eapply map_bind2_normalize_exp_length; eauto).
          replace (typesof efs) in Hlen7.
          replace (length (concat x3)). replace (length (concat x7)).
          repeat rewrite PeanoNat.Nat.min_id.
          apply idents_for_anns_values in H3; rewrite Forall2_forall2 in H3; destruct H3 as [H3 _].
          rewrite map_length in H3... }
        apply map_bind2_vars_perm in H1. 2: (repeat rewrite_Forall_forall; eauto).
        apply map_bind2_vars_perm in H2. 2: (repeat rewrite_Forall_forall; eauto).
        apply idents_for_anns_vars_perm in H3.
        etransitivity. 2: eauto.
        replace (concat (map (fun '(id, _) => [id]) x6)) with (map fst x6).
        2: { clear H3. induction x6; try destruct a; simpl; f_equal; auto. }
        repeat rewrite <- app_assoc. apply Permutation_app_head.
        etransitivity. 2: eauto.
        unfold vars_defined in *; rewrite flat_map_concat_map in *.
        rewrite Permutation_swap. apply Permutation_app_head.
        assumption.
    - (* ite *)
      destruct is_control; repeat inv_bind.
      + apply map_bind2_vars_perm in H2. 2: (rewrite Forall_forall in *; eauto).
        apply map_bind2_vars_perm in H3. 2: (rewrite Forall_forall in *; eauto).
        apply IHe in H1; eauto.
        etransitivity. 2: eauto.
        unfold vars_defined in *; repeat rewrite <- flat_map_app.
        rewrite <- app_assoc. rewrite Permutation_swap.
        rewrite <- app_assoc. rewrite Permutation_swap. apply Permutation_app_head.
        etransitivity. 2: eauto.
        apply Permutation_app_head.
        assumption.
      + unfold vars_defined; rewrite flat_map_concat_map.
        repeat rewrite map_app. repeat rewrite concat_app.
        rewrite combine_map_fst'.
        2: {
          repeat rewrite map_length. repeat rewrite combine_length.
          assert (length (concat x5) = length (typesof ets)) as Hlen3 by (eapply map_bind2_normalize_exp_length; eauto).
          assert (length (concat x9) = length (typesof efs)) as Hlen7 by (eapply map_bind2_normalize_exp_length; eauto).
          replace (typesof efs) in Hlen7.
          replace (length (concat x5)). replace (length (concat x9)).
          repeat rewrite PeanoNat.Nat.min_id.
          apply idents_for_anns_values in H4; rewrite Forall2_forall2 in H4; destruct H4 as [H4 _].
          rewrite map_length in H4... }
        apply map_bind2_vars_perm in H2. 2: (repeat rewrite_Forall_forall; eauto).
        apply map_bind2_vars_perm in H3. 2: (repeat rewrite_Forall_forall; eauto).
        apply idents_for_anns_vars_perm in H4.
        apply IHe in H1; eauto.
        etransitivity. 2: eauto.
        replace (concat (map (fun '(id, _) => [id]) x8)) with (map fst x8).
        2: { clear H4. induction x8; try destruct a; simpl; f_equal; auto. }
        repeat rewrite <- app_assoc. apply Permutation_app_head.
        etransitivity. 2: eauto.
        unfold vars_defined in *; rewrite flat_map_concat_map in *.
        rewrite app_assoc. rewrite Permutation_swap. apply Permutation_app_head.
        etransitivity. 2: eauto.
        rewrite <- app_assoc. rewrite Permutation_swap. apply Permutation_app_head.
        assumption.
    - (* app *)
      repeat inv_bind.
      apply idents_for_anns_vars_perm in H2.
      apply map_bind2_vars_perm in H1. 2: (repeat rewrite_Forall_forall; eauto).
      etransitivity. 2: apply H2.
      rewrite <- app_assoc. apply Permutation_app_head.
      assumption.
    - (* app (reset) *)
      repeat inv_bind.
      apply idents_for_anns_vars_perm in H3.
      apply map_bind2_vars_perm in H2. 2: (repeat rewrite_Forall_forall; eauto).
      apply normalize_reset_vars_perm in H4.
      apply H in H1; eauto.
      etransitivity. 2: eauto.
      repeat rewrite <- app_assoc. apply Permutation_app_head.
      etransitivity. 2: eauto.
      unfold vars_defined in *. repeat rewrite flat_map_concat_map in *.
      repeat rewrite map_app in *. repeat rewrite concat_app in *.
      rewrite <- app_assoc. rewrite Permutation_swap.
      rewrite <- app_assoc. rewrite Permutation_swap. apply Permutation_app_head.
      etransitivity. 2: eauto.
      apply Permutation_app_head.
      assumption.
  Qed.

  Corollary normalize_exps_vars_perm : forall G vars es es' eqs' st st',
      Forall (wt_exp G vars) es ->
      normalize_exps es st = ((es', eqs'), st') ->
      Permutation ((vars_defined eqs')++(map fst (snd st))) (map fst (snd st')).
  Proof with eauto.
    intros G vars es es' eqs' st st' Hf Hnorm.
    unfold normalize_exps in Hnorm.
    repeat inv_bind.
    eapply map_bind2_vars_perm...
    repeat rewrite_Forall_forall.
    eapply normalize_exp_vars_perm...
  Qed.

  Fact normalize_rhs_vars_perm : forall G vars e keep_fby es' eqs' st st',
      wt_exp G vars e ->
      normalize_rhs keep_fby e st = ((es', eqs'), st') ->
      Permutation ((vars_defined eqs')++(map fst (snd st))) (map fst (snd st')).
  Proof with eauto.
    intros G vars e keep_fby es' eqs' st st' Hwt Hnorm.
    destruct e; unfold normalize_rhs in Hnorm;
      try (solve [eapply normalize_exp_vars_perm; eauto]); inv Hwt; repeat inv_bind.
    - (* fby *)
      destruct keep_fby.
      + repeat inv_bind.
        eapply normalize_exps_vars_perm in H...
        eapply normalize_exps_vars_perm in H0...
        eapply normalize_fby_vars_perm in H1.
        etransitivity. 2: eauto.
        unfold vars_defined in *. repeat rewrite flat_map_concat_map in *.
        repeat rewrite map_app. repeat rewrite concat_app.
        repeat (rewrite <- app_assoc; rewrite Permutation_swap).
        apply Permutation_app_head.
        etransitivity. 2: eauto.
        apply Permutation_app_head.
        assumption.
      + eapply normalize_exp_vars_perm; eauto.
        econstructor; eauto.
    - (* app *)
      eapply normalize_exps_vars_perm in H; eauto.
    - (* app (reset) *)
      eapply normalize_exp_vars_perm in H; eauto.
      eapply normalize_exps_vars_perm in H0; eauto.
      eapply normalize_reset_vars_perm in H1.
      etransitivity. 2: eauto.
      unfold vars_defined in *. repeat rewrite flat_map_concat_map in *.
      repeat rewrite map_app. repeat rewrite concat_app.
      repeat (rewrite <- app_assoc; rewrite Permutation_swap).
      rewrite Permutation_swap. apply Permutation_app_head.
      etransitivity. 2: eauto.
      rewrite Permutation_swap. apply Permutation_app_head.
      assumption.
  Qed.

  Corollary normalize_rhss_vars_perm : forall G vars es keep_fby es' eqs' st st',
      Forall (wt_exp G vars) es ->
      normalize_rhss keep_fby es st = ((es', eqs'), st') ->
      Permutation ((vars_defined eqs')++(map fst (snd st))) (map fst (snd st')).
  Proof.
    intros G vars es keep_fby es' eqs' st st' Hf Hnorm.
    unfold normalize_rhss in Hnorm.
    repeat inv_bind.
    eapply map_bind2_vars_perm in H; eauto.
    repeat rewrite_Forall_forall.
    eapply normalize_rhs_vars_perm; eauto.
  Qed.

  Fact split_equation_vars_defined : forall xs es,
      length xs = length (typesof es) ->
      vars_defined (split_equation (xs, es)) = vars_defined [(xs, es)].
  Proof.
    intros xs es; revert xs.
    induction es; intros xs Hwt; inv Hwt; simpl in *.
    - destruct xs; simpl in *; congruence.
    - specialize (IHes (skipn (numstreams a) xs)).
      rewrite IHes.
      + repeat rewrite app_nil_r. apply firstn_skipn.
      + rewrite app_length in H0. rewrite numstreams_length_typeof in H0.
        assert (length xs >= numstreams a) by omega.
        rewrite <- (firstn_skipn (numstreams a) xs) in H0.
        rewrite app_length in H0.
        rewrite firstn_length in H0.
        rewrite min_l in H0; omega.
  Qed.

  Corollary split_equations_vars_defined : forall eqs,
      Forall (fun '(xs, es) => length xs = length (typesof es)) eqs ->
      vars_defined (flat_map split_equation eqs) = vars_defined eqs.
  Proof.
    induction eqs; intro Hf; simpl in *; inv Hf.
    - reflexivity.
    - destruct a as [xs es]; simpl in H1.
      specialize (split_equation_vars_defined _ _ H1) as Heq.
      unfold vars_defined in *; repeat rewrite flat_map_concat_map in *.
      rewrite map_app. rewrite concat_app.
      f_equal; simpl in *; auto.
      rewrite app_nil_r in Heq. assumption.
  Qed.

  Fact normalize_equation_vars_perm : forall G vars eq to_cut eqs' st st',
      wt_equation G vars eq ->
      normalize_equation to_cut eq st = (eqs', st') ->
      Permutation ((vars_defined eqs')++(map fst (snd st))) ((vars_defined [eq])++(map fst (snd st'))).
  Proof.
    intros G vars eq to_cut eqs' st st' Hwt Hnorm.
    destruct eq; simpl in *.
    repeat inv_bind. destruct Hwt as [Hwt Hl].
    specialize (normalize_rhss_vars_perm _ _ _ _ _ _ _ _ Hwt H) as Hperm1.
    rewrite app_nil_r.
    assert (vars_defined (flat_map split_equation [(l, x)]) = vars_defined [(l, x)]) as Hxl.
    { apply split_equations_vars_defined.
      repeat constructor.
      rewrite Forall2_forall2 in Hl; destruct Hl as [Hlen _].
      rewrite Hlen.
      eapply normalize_rhss_typeof in H; eauto.
      congruence. }
    unfold vars_defined in *; repeat rewrite flat_map_concat_map in *.
    repeat rewrite map_app; repeat rewrite concat_app.
    repeat rewrite <- app_assoc.
    simpl in Hxl. repeat rewrite app_nil_r in Hxl.
    apply Permutation_app; auto.
    rewrite <- Hxl at 2. reflexivity.
  Qed.

  Corollary normalize_equations_vars_perm : forall G vars eqs to_cut eqs' st st',
      Forall (wt_equation G vars) eqs ->
      normalize_equations to_cut eqs st = (eqs', st') ->
      Permutation ((vars_defined eqs')++(map fst (snd st))) ((vars_defined eqs)++(map fst (snd st'))).
  Proof.
    induction eqs; intros to_cut eqs' st st' Hf Hnorm ;simpl in *; repeat inv_bind.
    - reflexivity.
    - inv Hf. eapply IHeqs in H0; eauto.
      eapply normalize_equation_vars_perm in H; eauto; simpl in *.
      unfold vars_defined in *; rewrite flat_map_concat_map in *.
      rewrite app_nil_r in *.
      repeat rewrite map_app in *. repeat rewrite concat_app in *.
      rewrite Permutation_app_comm. rewrite Permutation_swap.
      etransitivity.
      + rewrite app_assoc. eapply Permutation_app; eauto.
      + repeat rewrite <- app_assoc. apply Permutation_app_head.
        rewrite Permutation_app_comm. assumption.
  Qed.

  Definition normalize_equations' (to_cut : list ident) (eq : list equation) (st : fresh_st (ann * bool)) :
    { res | normalize_equations to_cut eq st = res }.
  Proof.
    remember (normalize_equations to_cut eq st) as eqs'.
    econstructor; eauto.
  Defined.

  (** Normalization of a full node *)
  Program Definition normalize_node (n : node) (Hwt : exists G, wt_node G n) : node :=
    let id0 := first_unused_ident n in
    let eqs := normalize_equations' (map fst (n_out n)) (n_eqs n) (id0, nil) in
    let nvars := (List.map (fun var => (fst var, (fst (fst (snd var)), (fst (snd (fst (snd var))))))) (snd (snd (proj1_sig eqs)))) in
    {| n_name := (n_name n);
       n_hasstate := (n_hasstate n);
       n_in := (n_in n);
       n_out := (n_out n);
       n_vars := (n_vars n)++nvars;
       n_eqs := fst (proj1_sig eqs);
       n_ingt0 := (n_ingt0 n);
       n_outgt0 := (n_outgt0 n);
    |}.
  Next Obligation.
    rename Hwt into G.
    destruct H as [_ [_ [_ Hwt]]].
    eapply normalize_equations_vars_perm with (st:=(first_unused_ident n, [])) in Hwt. 2: eapply surjective_pairing.
    specialize (n_defd n) as Hperm'.
    repeat rewrite map_app in *; rewrite map_map; simpl in *.
    rewrite app_nil_r in Hwt.
    etransitivity. apply Hwt.
    rewrite Permutation_app_comm. symmetry.
    rewrite <- app_assoc. rewrite Permutation_swap.
    eapply Permutation_app_head. symmetry. assumption.
  Qed.
  Next Obligation.
    remember (normalize_equations (map fst (n_out n)) (n_eqs n) (first_unused_ident n, [])) as res.
    assert (fresh_st_follows (first_unused_ident n, []) (snd res)) as Hfollows.
    { subst. eapply normalize_equations_st_follows. eapply surjective_pairing. }
    assert (fresh_st_valid (snd res)) as Hvalid.
    { subst. eapply normalize_equations_st_valid.
      eapply surjective_pairing.
      repeat constructor. }
    destruct res as [eqs [n' l]]. simpl in *.
    unfold fresh_st_follows in Hfollows; simpl in *. destruct Hfollows as [_ Hfollows].
    destruct Hvalid as [Hvalid1 Hvalid2].
    specialize (n_nodup n) as Hndup.
    specialize (first_unused_ident_gt n _ eq_refl) as Hfirst; unfold used_idents in *.
    rewrite Forall_forall in Hfirst. repeat rewrite map_app in Hfirst.
    rewrite fst_NoDupMembers in *.
    repeat rewrite map_app in *; rewrite map_map; simpl.
    rewrite NoDup_swap. rewrite <- app_assoc. rewrite NoDup_swap.
    apply NoDup_app'; auto.
    - rewrite <- fst_NoDupMembers. assumption.
    - rewrite NoDup_swap. assumption.
    - rewrite Forall_forall. intros x Hin.
      intro contra.
      assert (Pos.lt x (first_unused_ident n)).
      + eapply Hfirst.
        repeat (apply in_app_or in contra; destruct contra as [?|contra]);
          repeat (apply in_or_app; auto; try (left; assumption); right).
      + clear Hfirst.
        apply min_fold_in with (x0 := n') in Hin.
        apply (Pos.lt_irrefl x).
        eapply Pos.lt_le_trans; eauto.
        eapply Pos.le_trans; eauto.
  Qed.
  Admit Obligations.

  Fixpoint normalize_global (G : global) (Hwt: wt_global G) : global.
  Proof.
    destruct G as [|hd tl].
    - exact [].
    - refine ((normalize_node hd _)::(normalize_global tl _)).
      + eapply wt_find_node with (f:=n_name hd); simpl; eauto.
        destruct hd; simpl.
        rewrite ident_eqb_refl. reflexivity.
      + inv Hwt; auto.
  Defined.

  Ltac singleton_length :=
    simpl in *;
    match goal with
    | H : length ?x = 1 |- _ =>
      destruct x; simpl in H; try congruence;
      destruct x; simpl in H; try congruence;
      simpl in *; clear H
    end.

  Fact map_bind2_wt_exp {A A2 B} :
    forall G vars (k : A -> Fresh (list exp * A2) B) a es' a2s st st',
      map_bind2 k a st = (es', a2s, st') ->
      Forall (fun a => forall es' a2s st st',
                  k a st = (es', a2s, st') ->
                  Forall (wt_exp G vars) es') a ->
      Forall (wt_exp G vars) (concat es').
  Proof.
    intros G vars k a es' a2s st st' Hmap Hf.
    apply map_bind2_values in Hmap.
    induction Hmap; inv Hf.
    - constructor.
    - simpl. apply Forall_app.
      destruct H as [? [? H]].
      split; eauto.
  Qed.

  (** ** Preservation of good typing
      TODO is this necessary ? *)

  Fact idents_for_anns_wt : forall G vars anns ids st st',
      idents_for_anns anns st = (ids, st') ->
      Forall (fun '(ty, cl) => wt_nclock vars cl) anns ->
      Forall (wt_exp G (vars++(idty ids))) (map (fun '(x, ann) => Evar x ann) ids).
  Proof.
    induction anns; intros ids st st' Hidents Hf;
      simpl in *; repeat inv_bind.
    - constructor.
    - inv Hf. destruct a as [ty cl].
      specialize (IHanns x1 _ _ H0 H4).
      econstructor; eauto.
      + repeat constructor; simpl; auto.
        * apply in_or_app. right. constructor; auto.
        * eapply wt_nclock_incl; eauto.
          apply incl_appl. reflexivity.
      + eapply Forall_impl; [| eauto].
        intros. eapply wt_exp_incl; eauto.
        apply incl_app.
        * apply incl_appl. reflexivity.
        * apply incl_appr. apply incl_tl. reflexivity.
  Qed.

  Fact st_follows_incl {A1 A2 A3} : forall (st st' : fresh_st ((A1 * A2) * A3)),
      fresh_st_follows st st' ->
      incl (idty (idty (snd st))) (idty (idty (snd st'))).
  Proof.
    intros st st' [Hincl _].
    unfold incl in *. intros [id data] Hin.
    unfold idty in *.
    rewrite in_map_iff in *. destruct Hin as [x [H Hin]]; subst. inv H.
    exists x. split; auto.
    rewrite in_map_iff in *. destruct Hin as [x' [H Hin]]; subst.
    exists x'. eauto.
  Qed.

  Hint Constructors wt_exp.
  Fact normalize_exp_wt : forall G vars e is_control es' eqs' st st',
      wt_exp G vars e ->
      normalize_exp is_control e st = (es', eqs', st') ->
      Forall (wt_exp G (vars++(idty (idty (snd st'))))) es'. (* non mauvais invariant *)
  Proof.
    intros G vars e is_control es' eqs' st st' Hwt;
      revert is_control eqs' es' st st'.
    induction Hwt using wt_exp_ind2;
      intros is_control eqs' es' st st' Hnorm; simpl in *.
    - (* const *)
      repeat inv_bind; eauto.
    - (* var *)
      repeat inv_bind.
      repeat constructor.
      + apply in_or_app; auto.
      + eapply wt_nclock_incl; eauto.
        apply incl_appl. apply incl_refl.
    - (* unop *)
      repeat inv_bind.
      specialize (IHHwt _ _ _ _ _ H2).
      repeat constructor.
      specialize (normalize_exp_length _ _ _ _ _ _ _ _ Hwt H2) as Hlen.
      rewrite <- numstreams_length_typeof in Hlen.
      replace (typeof e) in *.
      singleton_length.
      inv IHHwt. econstructor; eauto.
      eapply normalize_exp_typeof in Hwt; eauto.
      simpl in *; rewrite app_nil_r in Hwt; rewrite Hwt; auto.
      eapply wt_nclock_incl; eauto.
      apply incl_appl; apply incl_refl.
    - (* binop *)
      repeat inv_bind.
      specialize (IHHwt1 _ _ _ _ _ H3).
      specialize (IHHwt2 _ _ _ _ _ H4).
      repeat constructor.
      specialize (normalize_exp_length _ _ _ _ _ _ _ _ Hwt1 H3) as Hlen1.
      specialize (normalize_exp_length _ _ _ _ _ _ _ _ Hwt2 H4) as Hlen2.
      rewrite <- numstreams_length_typeof in Hlen1.
      rewrite <- numstreams_length_typeof in Hlen2.
      replace (typeof e1) in *.
      replace (typeof e2) in *.
      repeat singleton_length.
      eapply normalize_exp_typeof in Hwt1; eauto.
      eapply normalize_exp_typeof in Hwt2; eauto.
      inv IHHwt1. inv IHHwt2. inv H8. inv H10.
      econstructor; eauto;
        simpl in *; rewrite app_nil_r in *;
          try rewrite Hwt1; try rewrite Hwt2; auto.
      + eapply wt_exp_incl; eauto.
        apply incl_app.
        * apply incl_appl; reflexivity.
        * apply incl_appr. eapply st_follows_incl; eauto.
      + eapply wt_nclock_incl; [| eauto].
        apply incl_appl; reflexivity.
    - (* fby *)
      repeat inv_bind.
      admit.
    - (* when *)
      repeat inv_bind.
      specialize (map_bind2_normalize_exp_length _ _ _ _ _ _ _ _ H H1) as Hlength.
      specialize (map_bind2_normalize_exp_typeof _ _ _ _ _ _ _ _ H H1) as Htypeof.
      admit.
  Admitted.

  Fact map_bind2_wt_eq {A A1 B} :
    forall G vars (k : A -> Fresh (A1 * list equation) B) a a1s eqs' st st',
      map_bind2 k a st = (a1s, eqs', st') ->
      Forall (fun a => forall a1 eqs' st st',
                  k a st = (a1, eqs', st') ->
                  Forall (wt_equation G vars) eqs') a ->
      Forall (wt_equation G vars) (concat eqs').
  Proof.
    intros G vars k a a1s eqs' st st' Hmap Hf.
    apply map_bind2_values in Hmap.
    induction Hmap; inv Hf.
    - constructor.
    - simpl. apply Forall_app.
      destruct H as [? [? H]].
      split; eauto.
  Qed.

  (* Fact normalize_fby_wt_eq : forall G vars e0s es anns es' eqs' st st', *)
  (*     normalize_fby e0s es anns st = (es', eqs', st') -> *)
  (*     Forall (wt_equation G vars) eqs'. *)
  (* Proof. *)
  (*   intros G vars e0s es anns es' eqs' st st' Hnorm. *)
  (*   unfold normalize_fby in Hnorm. repeat inv_bind. *)
  (*   eapply map_bind2_wt_eq; eauto. *)
  (*   rewrite Forall_forall; intros. destruct x as [[e0 e] [ty cl]]. *)
  (*   specialize (fby_iteexp_spec e0 e ty cl) as [[c [? Hfby]]|Hfby]; subst; rewrite Hfby in H1; clear Hfby; *)
  (*     repeat inv_bind. *)
  (*   - constructor. *)
  (*   - repeat constructor; simpl in *. *)
  (* Admitted. *)

  Fact normalize_exp_wt_eq : forall G vars e is_control es' eqs' st st',
      wt_exp G vars e ->
      normalize_exp is_control e st = (es', eqs', st') ->
      Forall (wt_equation G vars (* FIXME *)) eqs'.
  Proof.
    induction e using exp_ind2; intros is_control es' eqs' st st' Hwt Hnorm;
      inv Hwt; simpl in Hnorm; repeat inv_bind.
    - (* const *) constructor.
    - (* var *) constructor.
    - (* unop *) eauto.
    - (* binop *)
      rewrite Forall_app.
      split; eauto.
    - (* fby *)
      repeat rewrite Forall_app.
      repeat split; eauto;
        try (eapply map_bind2_wt_eq; eauto;
             rewrite Forall_forall in *;
             intros; eauto).
      admit. admit.
    - (* when *)
      eapply map_bind2_wt_eq; eauto.
      rewrite Forall_forall in *; intros; eauto.
    - (* merge *)
      destruct is_control; repeat inv_bind.
      + (* exp *)
        apply Forall_app; split;
          (eapply map_bind2_wt_eq; eauto;
           rewrite Forall_forall in *; intros; eauto).
      + (* control *)
        repeat rewrite Forall_app.
        repeat split;
          try (eapply map_bind2_wt_eq; eauto;
               rewrite Forall_forall in *; intros; eauto).
        admit.
  Admitted.

  (** Describe normalized nodes *)

  Inductive normalized_lexp : exp -> Prop :=
  | normalized_Econst : forall c, normalized_lexp (Econst c)
  | normalized_Evar : forall x ty cl, normalized_lexp (Evar x (ty, cl))
  | normalized_Eunop : forall op e1 ty cl,
      normalized_lexp e1 ->
      normalized_lexp (Eunop op e1 (ty, cl))
  | normalized_Ebinop : forall op e1 e2 ty cl,
      normalized_lexp e1 ->
      normalized_lexp e2 ->
      normalized_lexp (Ebinop op e1 e2 (ty, cl))
  | normalized_Ewhen : forall e x b ty cl,
      normalized_lexp e ->
      normalized_lexp (Ewhen [e] x b ([ty], cl)).

  Inductive normalized_cexp : exp -> Prop :=
  | normalized_Emerge : forall x et ef ty cl,
      normalized_cexp et ->
      normalized_cexp ef ->
      normalized_cexp (Emerge x [et] [ef] ([ty], cl))
  | normalized_Eite : forall e et ef ty cl,
      normalized_lexp e ->
      normalized_cexp et ->
      normalized_cexp ef ->
      normalized_cexp (Eite e [et] [ef] ([ty], cl))
    | normalized_lexp_cexp : forall e,
      normalized_lexp e ->
      normalized_cexp e.

  Inductive is_constant : exp -> Prop :=
  | constant_Econst : forall c,
      is_constant (Econst c)
  | constant_Ewhen : forall e x b ty cl,
      is_constant e ->
      is_constant (Ewhen [e] x b ([ty], cl)).

  Inductive normalized_equation : list ident -> equation -> Prop :=
  | normalized_eq_Eapp : forall out xs f es lann,
      Forall normalized_lexp es ->
      normalized_equation out (xs, [Eapp f es None lann])
  | normalized_eq_Eapp_reset : forall out xs f es x ty cl lann,
      Forall normalized_lexp es ->
      normalized_equation out (xs, [Eapp f es (Some (Evar x (ty, cl))) lann])
  | normalized_eq_Efby : forall out x e0 e ann,
      ~In x out ->
      is_constant e0 ->
      normalized_lexp e ->
      normalized_equation out ([x], [Efby [e0] [e] [ann]])
  | normalized_eq_cexp : forall out x e,
      normalized_cexp e ->
      normalized_equation out ([x], [e]).

  Definition normalized_node (n : node) :=
    Forall (normalized_equation (List.map fst (n_out n))) (n_eqs n).

  Hint Constructors is_constant normalized_lexp normalized_cexp normalized_equation.

  Fact normalized_lexp_numstreams : forall e,
      normalized_lexp e ->
      numstreams e = 1.
  Proof.
    induction e; intros Hnorm; inv Hnorm; reflexivity.
  Qed.

  Fact normalized_cexp_numstreams : forall e,
      normalized_cexp e ->
      numstreams e = 1.
  Proof.
    induction e; intros Hnorm; inv Hnorm;
      try apply normalized_lexp_numstreams in H; auto.
  Qed.

  Fact normalized_lexp_hd_default : forall es,
      Forall normalized_lexp es ->
      normalized_lexp (hd_default es).
  Proof.
    intros es Hf.
    destruct es; simpl.
    - constructor.
    - inv Hf; auto.
  Qed.

  Fact map_bind2_normalized_lexp {A A2} :
    forall (k : A -> FreshAnn ((list exp) * A2)) a es' a2s st st',
      map_bind2 k a st = (es', a2s, st') ->
      Forall (fun a => forall es' a2s st st',
                  k a st = (es', a2s, st') ->
                  Forall normalized_lexp es') a ->
      Forall normalized_lexp (concat es').
  Proof.
    intros k a eqs' a2s st st' Hmap Hf.
    apply map_bind2_values in Hmap.
    induction Hmap; simpl in *.
    - constructor.
    - destruct H as [? [? H]]. inv Hf.
      rewrite Forall_app.
      split; eauto.
  Qed.

  Fact map_bind2_normalized_cexp {A A2} :
    forall (k : A -> FreshAnn ((list exp) * A2)) a es' a2s st st',
      map_bind2 k a st = (es', a2s, st') ->
      Forall (fun a => forall es' a2s st st',
                  k a st = (es', a2s, st') ->
                  Forall normalized_cexp es') a ->
      Forall normalized_cexp (concat es').
  Proof.
    intros k a eqs' a2s st st' Hmap Hf.
    apply map_bind2_values in Hmap.
    induction Hmap; simpl in *.
    - constructor.
    - destruct H as [? [? H]]. inv Hf.
      rewrite Forall_app.
      split; eauto.
  Qed.

  Fact map_bind2_normalized_eq {A A1} :
    forall (k : A -> FreshAnn (A1 * (list equation))) a out a1s eqs' st st',
      map_bind2 k a st = (a1s, eqs', st') ->
      Forall (fun o => Pos.lt o (smallest_ident st)) out ->
      (forall a a1s eqs' st st', k a st = (a1s, eqs', st') -> fresh_st_follows st st') ->
      Forall (fun a => forall a1s eqs' st st',
                  k a st = (a1s, eqs', st') ->
                  Forall (fun o => Pos.lt o (smallest_ident st)) out ->
                  Forall (normalized_equation out) eqs') a ->
      Forall (normalized_equation out) (concat eqs').
  Proof.
    induction a; intros out a1s eqs' st st' Hmap Hlt Hfollows Hf;
      simpl in *; repeat inv_bind.
    - constructor.
    - inv Hf.
      rewrite Forall_app.
      split; eauto.
      eapply IHa; eauto.
      clear IHa H3 H4.
      specialize (Hfollows _ _ _ _ _ H) as [_ Hfollows].
      repeat rewrite_Forall_forall.
      eapply Pos.lt_le_trans; eauto.
  Qed.

  Fact add_whens_is_constant : forall ty cl e,
    is_constant e ->
    is_constant (add_whens e ty cl).
  Proof.
    induction cl; intros e Hcons; simpl.
    - assumption.
    - constructor. eauto.
  Qed.

  Fact add_whens_normalized_lexp : forall ty cl e,
      normalized_lexp e ->
      normalized_lexp (add_whens e ty cl).
  Proof.
    induction cl; intros e Hadd; simpl in Hadd.
    - assumption.
    - constructor. eauto.
  Qed.

  Hint Resolve in_combine_l in_combine_r.
  Hint Resolve normalized_lexp_hd_default.

  Lemma normalize_exp_normalized_lexp : forall e es' eqs' st st',
      normalize_exp false e st = (es', eqs', st') ->
      Forall normalized_lexp es'.
  Proof with eauto.
    induction e using exp_ind2; intros es' eqs' st st' Hnorm;
      simpl in Hnorm; repeat inv_bind; repeat constructor.
    - (* var *)
      destruct a...
    - (* unop *)
      destruct a...
    - (* binop *)
      destruct a. constructor...
    - (* fby *)
      repeat rewrite_Forall_forall.
      rewrite in_map_iff in H5. destruct H5 as [[? [? ?]] [? Hin]]; subst...
    - (* when *)
      destruct a. repeat inv_bind.
      apply map_bind2_normalized_lexp in H0...
      repeat rewrite_Forall_forall.
      rewrite in_map_iff in H1. destruct H1 as [[? ?] [? ?]]; subst...
    - (* merge *)
      destruct a. repeat inv_bind.
      repeat rewrite_Forall_forall.
      rewrite in_map_iff in H4. destruct H4 as [[? ?] [? ?]]; subst.
      destruct a...
    - (* ite *)
      destruct a. repeat inv_bind.
      repeat rewrite_Forall_forall.
      rewrite in_map_iff in H5. destruct H5 as [[? ?] [? ?]]; subst.
      destruct a...
    - (* app *)
      repeat rewrite_Forall_forall.
      rewrite in_map_iff in H4. destruct H4 as [[? ?] [? ?]]; subst.
      destruct a0...
  Qed.
  Hint Resolve normalize_exp_normalized_lexp.

  Lemma normalize_exp_normalized_cexp : forall e es' eqs' st st',
      normalize_exp true e st = (es', eqs', st') ->
      Forall normalized_cexp es'.
  Proof with eauto.
    induction e using exp_ind2; intros es' eqs' st st' Hnorm;
      simpl in Hnorm; repeat inv_bind; repeat constructor.
    - (* var *)
      destruct a...
    - (* unop *)
      destruct a...
    - (* binop *)
      destruct a. constructor...
    - (* fby *)
      repeat rewrite_Forall_forall.
      rewrite in_map_iff in H5. destruct H5 as [[? [? ?]] [? Hin]]; subst...
    - (* when *)
      destruct a. repeat inv_bind.
      apply map_bind2_normalized_lexp in H0; solve_forall.
      repeat rewrite_Forall_forall.
      rewrite in_map_iff in H1. destruct H1 as [[? ?] [? Hin]]; subst...
    - (* merge *)
      destruct a. repeat inv_bind.
      apply map_bind2_normalized_cexp in H1; solve_forall.
      apply map_bind2_normalized_cexp in H2; solve_forall.
      repeat rewrite_Forall_forall.
      rewrite in_map_iff in H3. destruct H3 as [[[? ?] ?] [? Hin]]; subst.
      constructor...
    - (* ite *)
      destruct a. repeat inv_bind.
      apply normalize_exp_normalized_lexp in H1.
      apply map_bind2_normalized_cexp in H2; solve_forall.
      apply map_bind2_normalized_cexp in H3; solve_forall.
      repeat rewrite_Forall_forall.
      rewrite in_map_iff in H4. destruct H4 as [[[? ?] ?] [? Hin]]; subst.
      constructor...
      apply normalized_lexp_hd_default. repeat rewrite_Forall_forall...
    - (* app *)
      repeat rewrite_Forall_forall.
      rewrite in_map_iff in H4. destruct H4 as [[? ?] [? ?]]; subst.
      destruct a0...
  Qed.

  Fact init_var_for_clock_normalized_eq : forall cl id eqs' out st st',
      init_var_for_clock cl st = (id, eqs', st') ->
      Forall (fun o => Pos.lt o (smallest_ident st)) out ->
      Forall (normalized_equation out) eqs'.
  Proof.
    intros cl id eqs' out [n l] st' Hinit Hlt.
    simpl in Hinit.
    destruct (find _ _).
    - destruct p. inv Hinit. constructor.
    - inv Hinit. repeat constructor.
      + simpl in Hlt.
        intros contra.
        rewrite_Forall_forall. apply Hlt in contra.
        specialize (min_fold_le (map fst l) id) as contra'.
        apply (Pos.lt_irrefl id).
        eapply Pos.lt_le_trans; eauto.
      + apply add_whens_is_constant. auto.
      + apply add_whens_normalized_lexp. auto.
  Qed.

  Fact fby_iteexp_normalized_eq : forall e0 e a e' eqs' out st st',
      fby_iteexp e0 e a st = (e', eqs', st') ->
      normalized_lexp e ->
      Forall (fun o => Pos.lt o (smallest_ident st)) out ->
      Forall (normalized_equation out) eqs'.
  Proof.
    intros e0 e [ty cl] e' eqs' out st st' Hfby He Hlt.
    specialize (fby_iteexp_spec e0 e ty cl) as [[? [? Hspec]]|Hspec]; subst;
      rewrite Hspec in Hfby; clear Hspec; repeat inv_bind.
    - constructor.
    - constructor.
      + constructor; auto.
        intro contra. rewrite_Forall_forall.
        apply Hlt in contra; clear Hlt.
        assert (fresh_st_follows st st') as Hfollows by (etransitivity; eauto).
        destruct Hfollows as [_ Hfollows].
        unfold fresh_ident in H0; destruct x1. inv H0.
        simpl in Hfollows.
        apply Pos.min_glb_l in Hfollows.
        apply (Pos.lt_irrefl x2).
        eapply Pos.lt_le_trans; eauto.
      + eapply init_var_for_clock_normalized_eq in H; eauto.
  Qed.

  Fact normalize_fby_normalized_eq : forall e0s es anns es' eqs' out st st',
      normalize_fby e0s es anns st = (es', eqs', st') ->
      Forall normalized_lexp es ->
      Forall (fun o => Pos.lt o (smallest_ident st)) out ->
      Forall (normalized_equation out) eqs'.
  Proof with eauto.
    intros e0s es anns es' eqs' out st st' Hnorm Hf Hlt.
    unfold normalize_fby in Hnorm.
    repeat inv_bind.
    - eapply map_bind2_normalized_eq...
      + intros. destruct a as [[e0 e] [ty cl]].
        eapply fby_iteexp_st_follows...
      + rewrite Forall_forall; intros.
        destruct x as [[e0 e] [ty cl]].
        eapply fby_iteexp_normalized_eq in H1...
        rewrite Forall_forall in Hf...
  Qed.

  Fact idents_for_anns_smallest_ident : forall anns ids st st',
      idents_for_anns anns st = (ids, st') ->
      Forall (fun id => Pos.le (smallest_ident st) id) (map fst ids).
  Proof.
    induction anns; intros ids st st' Hids;
      simpl in Hids; repeat inv_bind.
    - constructor.
    - destruct st as [n l]; simpl in H; inv H.
      constructor; eauto.
      + simpl. apply min_fold_le.
      + eapply IHanns in H0. solve_forall.
        clear H0.
        apply Pos.min_le in H. destruct H as [H|H].
        * etransitivity. eapply min_fold_le. eauto.
        * etransitivity; eauto. apply min_fold_eq.
          apply Pos.lt_le_incl. apply Pos.lt_succ_diag_r.
  Qed.

  Lemma normalize_exp_normalized_eq : forall e is_control es' eqs' out st st',
      normalize_exp is_control e st = (es', eqs', st') ->
      Forall (fun o => Pos.lt o (smallest_ident st)) out ->
      Forall (normalized_equation out) eqs'.
  Proof with eauto.
    induction e using exp_ind2; intros is_control es' eqs' out st st' Hnorm Hlt;
      simpl in Hnorm; repeat inv_bind; repeat constructor.
    - (* unop *) eauto.
    - (* binop *)
      apply Forall_app. split...
      apply normalize_exp_st_follows in H; destruct H.
      assert (Forall (fun o : positive => (o < smallest_ident x1)%positive) out) by (solve_forall; eapply Pos.lt_le_trans; eauto)...
    - (* fby *)
      repeat rewrite Forall_app. repeat split.
      + assert (fresh_st_follows st x1) as Hfollows1 by (eapply map_bind2_st_follows; eauto; solve_forall).
        assert (fresh_st_follows x1 x4) as Hfollows2 by (eapply map_bind2_st_follows; eauto; solve_forall).
        assert (fresh_st_follows x4 x7) as Hfollows3 by eauto.
        apply map_bind2_normalized_lexp in H1; [| solve_forall].
        apply map_bind2_normalized_lexp in H2; [| solve_forall].
        clear H H0.
        unfold normalize_fby in H3; repeat inv_bind. apply map_bind2_values in H.
        repeat rewrite_Forall_forall.
        rewrite in_map_iff in H5; destruct H5 as [[[? ?] ?] [? Hin]]; subst.
        specialize (in_combine_l _ _ _ _ Hin) as Hin2.
        apply in_combine_r in Hin.
        apply In_nth with (d:=(hd_default [])) in Hin; destruct Hin as [n [? ?]].
        replace (length x5) in H5.
        specialize (H3 (e, e, a0) (hd_default []) [] _ _ _ _ H5 eq_refl eq_refl eq_refl). destruct H3 as [? [? H3]].
        destruct (nth n _) as [[e0 e'] [ty cl]] eqn:Hnth.
        specialize (fby_iteexp_spec e0 e' ty cl) as [[? [? Hspec]]|Hspec]; subst;
          rewrite Hspec in H3; clear Hspec; repeat inv_bind.
        * rewrite <- H7. repeat constructor.
          -- intro contra. apply Hlt in contra.
             eapply idents_for_anns_smallest_ident in H4. rewrite Forall_forall in H4.
             assert (In i (map fst x8)) as Hin.
             { rewrite in_map_iff. exists (i, a0); auto. }
             apply H4 in Hin.
             destruct Hfollows1. destruct Hfollows2. destruct Hfollows3.
             apply (Pos.lt_irrefl i).
             eapply Pos.lt_le_trans; eauto.
             etransitivity; eauto.
             etransitivity; eauto.
             etransitivity; eauto.
          -- eapply nth_In in H5; rewrite Hnth in H5...
        * repeat constructor.
          eapply nth_In in H5; rewrite Hnth in H5...
      + eapply map_bind2_normalized_eq in H1... solve_forall.
      + eapply map_bind2_normalized_eq in H2...
        * eapply map_bind2_st_follows in H1; solve_forall.
          destruct H1 as [_ Hfollows].
          eapply Pos.lt_le_trans...
        * solve_forall.
      + eapply normalize_fby_normalized_eq in H3; eauto.
        * eapply map_bind2_normalized_lexp; eauto. solve_forall.
        * eapply map_bind2_st_follows in H1; solve_forall. destruct H1 as [_ H1].
          eapply map_bind2_st_follows in H2; solve_forall. destruct H2 as [_ H2].
          eapply Pos.lt_le_trans; eauto.
          etransitivity; eauto.
    - (* when *)
      destruct a. repeat inv_bind.
      eapply map_bind2_normalized_eq in H0; eauto. solve_forall.
    - (* merge *)
      destruct a; destruct is_control; repeat inv_bind;
        repeat rewrite Forall_app; repeat split.
      1,2,4,5: (eapply map_bind2_normalized_eq; eauto; solve_forall).
      1,2: (eapply map_bind2_st_follows in H1; eauto; solve_forall; destruct H1 as [_ Hfollows];
            eapply Pos.lt_le_trans; eauto).
      rewrite Forall_forall; intros [? ?] Hin. rewrite map_map in Hin; simpl in Hin.
      specialize (in_combine_l _ _ _ _ Hin) as Hin1.
      apply in_combine_r in Hin. rewrite in_map_iff in Hin; destruct Hin as [[[? ?] ?] [? Hin2]]; subst.
      rewrite in_map_iff in Hin1; destruct Hin1 as [[? ?] [? Hin1]]; subst.
      constructor. constructor.
      + eapply map_bind2_normalized_cexp in H1; eauto; solve_forall.
        rewrite Forall_forall in H1...
        eapply normalize_exp_normalized_cexp...
      + eapply map_bind2_normalized_cexp in H2; eauto; solve_forall.
        rewrite Forall_forall in H2...
        eapply normalize_exp_normalized_cexp...
    - destruct a; destruct is_control; repeat inv_bind;
        repeat rewrite Forall_app; repeat split.
      1,5: (eapply IHe; eauto).
      1,2,4,5: (eapply map_bind2_normalized_eq; eauto; solve_forall).
      1,2,3,4: (eapply normalize_exp_st_follows in H1; eauto; destruct H1 as [_ Hfollows1];
                eapply Pos.lt_le_trans; eauto).
      1,2: (eapply map_bind2_st_follows in H2; eauto; solve_forall; destruct H2 as [_ Hfollows2];
            etransitivity; eauto).
      rewrite Forall_forall; intros [? ?] Hin. rewrite map_map in Hin; simpl in Hin.
      specialize (in_combine_l _ _ _ _ Hin) as Hin1.
      apply in_combine_r in Hin. rewrite in_map_iff in Hin; destruct Hin as [[[? ?] ?] [? Hin2]]; subst.
      rewrite in_map_iff in Hin1; destruct Hin1 as [[? ?] [? Hin1]]; subst.
      constructor. constructor.
      + eapply normalized_lexp_hd_default.
        eapply normalize_exp_normalized_lexp...
      + eapply map_bind2_normalized_cexp in H2; eauto; solve_forall.
        rewrite Forall_forall in H2...
        eapply normalize_exp_normalized_cexp...
      + eapply map_bind2_normalized_cexp in H3; eauto; solve_forall.
        rewrite Forall_forall in H3...
        eapply normalize_exp_normalized_cexp...
    - (* app *)
      eapply map_bind2_normalized_lexp in H2; eauto; solve_forall.
      destruct ro; repeat inv_bind.
      + specialize (normalize_reset_spec (hd_default x2)) as [[? [? [? Hspec]]]|Hspec]; subst;
          rewrite Hspec in H4; clear Hspec; repeat inv_bind.
        * destruct x0...
        * destruct (hd _); simpl in *; repeat inv_bind...
      + constructor...
    - (* app (auxiliary equations) *)
      rewrite Forall_app. split.
      + destruct ro; repeat inv_bind; try constructor.
        eapply Forall_app. split...
        specialize (normalize_reset_spec (hd_default x2)) as [[? [? [? Hspec]]]|Hspec]; subst;
          rewrite Hspec in H4; clear Hspec; repeat inv_bind...
        destruct (hd _); simpl in *; repeat inv_bind.
        repeat constructor. apply normalized_lexp_hd_default...
      + destruct ro; repeat inv_bind;
          eapply map_bind2_normalized_eq; eauto; solve_forall.
        eapply normalize_exp_st_follows in H1; destruct H1.
        eapply normalize_reset_st_follows in H4; destruct H4.
        eapply Pos.lt_le_trans; eauto. etransitivity; eauto.
  Qed.
  Hint Resolve normalize_exp_normalized_eq.

  Corollary normalize_exps_normalized_lexp: forall es es' eqs' st st',
      normalize_exps es st = (es', eqs', st') ->
      Forall normalized_lexp es'.
  Proof.
    intros es es' eqs' st st' Hnorm.
    unfold normalize_exps in Hnorm. repeat inv_bind.
    apply map_bind2_normalized_lexp in H; auto.
    rewrite Forall_forall; intros; eauto.
  Qed.
  Hint Resolve normalize_exps_normalized_lexp.

  Corollary normalize_exps_normalized_eq : forall es es' eqs' out st st',
      normalize_exps es st = (es', eqs', st') ->
      Forall (fun o => Pos.lt o (smallest_ident st)) out ->
      Forall (normalized_equation out) eqs'.
  Proof.
    intros es es' eqs' out st st' Hnorm Hlt.
    unfold normalize_exps in Hnorm. repeat inv_bind.
    eapply map_bind2_normalized_eq in H; eauto.
    rewrite Forall_forall; intros; eauto.
  Qed.
  Hint Resolve normalize_exps_normalized_eq.

  (* Intermediary predicate for normalized rhs *)
  Inductive normalized_rhs : bool -> exp -> Prop :=
  | normalized_rhs_Eapp : forall f es lann keep_fby,
      Forall normalized_lexp es ->
      normalized_rhs keep_fby (Eapp f es None lann)
  | normalized_rhs_Eapp_reset : forall f es x ty cl lann keep_fby,
      Forall normalized_lexp es ->
      normalized_rhs keep_fby (Eapp f es (Some (Evar x (ty, cl))) lann)
  | normalized_rhs_Efby : forall e0 e ann,
      is_constant e0 ->
      normalized_lexp e ->
      normalized_rhs true (Efby [e0] [e] [ann])
  | normalized_rhs_cexp : forall e keep_fby,
      normalized_cexp e ->
      normalized_rhs keep_fby e.
  Hint Constructors normalized_rhs.

  Fact normalize_rhs_normalized_rhs : forall e keep_fby es' eqs' st st',
      normalize_rhs keep_fby e st = (es', eqs', st') ->
      Forall (normalized_rhs keep_fby) es'.
  Proof with eauto.
    intros e keep_fby es' eqs' st st' Hnorm.
    destruct e; unfold normalize_rhs in Hnorm;
      try (apply normalize_exp_normalized_cexp in Hnorm; solve_forall; auto).
    - (* fby *)
      destruct keep_fby; try (apply normalize_exp_normalized_cexp in Hnorm; solve_forall; auto).
      repeat inv_bind.
      apply normalize_exps_normalized_lexp in H.
      apply normalize_exps_normalized_lexp in H0.
      unfold normalize_fby in H1. repeat inv_bind.
      apply map_bind2_values in H1.
      repeat rewrite_Forall_forall.
      apply In_nth with (d:=(hd_default [])) in H4; destruct H4 as [n [Hn Hnth]].
      replace (length es') in Hn.
      specialize (H3 (x5, x5, (bool_type, (Cbase, None))) (hd_default []) [] _ _ _ _ Hn eq_refl eq_refl eq_refl).
      destruct H3 as [? [? H3]]. destruct (nth n _ _) as [[e0 e] [ty cl]] eqn:Hnth'.
      specialize (fby_iteexp_spec e0 e ty cl) as [[? [? Hspec]]|Hspec]; subst;
        rewrite Hspec in H3; clear Hspec; repeat inv_bind.
      + rewrite <- H5. repeat constructor.
        eapply nth_In in Hn. rewrite Hnth' in Hn...
      + repeat constructor.
        eapply nth_In in Hn. rewrite Hnth' in Hn...
    - (* app *)
      destruct o; repeat inv_bind...
      specialize (normalize_reset_spec (hd_default x4)) as [[? [[? ?] [? Hspec]]]|Hspec]; subst;
        rewrite Hspec in H1; clear Hspec; repeat inv_bind...
      destruct (hd _) as [? [ty cl]]; simpl in H1. repeat inv_bind...
  Qed.

  Corollary normalize_rhss_normalized_rhs : forall es keep_fby es' eqs' st st',
      normalize_rhss keep_fby es st = (es', eqs', st') ->
      Forall (normalized_rhs keep_fby) es'.
  Proof with eauto.
    intros es keep_fby es' eqs' st st' Hnorm.
    unfold normalize_rhss in Hnorm. repeat inv_bind.
    eapply map_bind2_values in H.
    induction H; simpl; try constructor.
    apply Forall_app. split; auto.
    destruct H as [? [? H]].
    eapply normalize_rhs_normalized_rhs; eauto.
  Qed.

  Fact normalize_rhs_normalized_eq : forall e keep_fby es' eqs' out st st',
      normalize_rhs keep_fby e st = (es', eqs', st') ->
      Forall (fun o => Pos.lt o (smallest_ident st)) out ->
      Forall (normalized_equation out) eqs'.
  Proof with eauto.
    intros e keep_fby es' eqs' out st st' Hnorm Hlt.
    destruct e; unfold normalize_rhs in Hnorm;
    try (eapply normalize_exp_normalized_eq in Hnorm; eauto).
    - (* fby *)
      destruct keep_fby; try (eapply normalize_exp_normalized_eq in Hnorm; eauto).
      simpl in Hnorm. repeat inv_bind.
      repeat rewrite Forall_app. repeat split...
      + eapply normalize_exps_normalized_eq; eauto; solve_forall.
        eapply normalize_exps_st_follows in H; destruct H as [_ Hfollows].
        eapply Pos.lt_le_trans...
      + unfold normalize_fby in H1. repeat inv_bind.
        eapply map_bind2_normalized_eq in H1; eauto; solve_forall.
        * eapply normalize_exps_st_follows in H; destruct H as [_ Hfollows1].
          eapply normalize_exps_st_follows in H0; destruct H0 as [_ Hfollows2].
          eapply Pos.lt_le_trans... etransitivity...
        * intros. destruct a as [[e0 e] ann]. apply fby_iteexp_st_follows in H2...
        * repeat rewrite_Forall_forall. destruct x5 as [[e0 e] [ty cl]].
          specialize (fby_iteexp_spec e0 e ty cl) as [[? [? Hspec]]|Hspec]; subst;
            rewrite Hspec in H3; clear Hspec; repeat inv_bind; inv H5.
          -- econstructor...
             ++ intro contra. apply H4 in contra.
                unfold fresh_ident in H6; destruct x9 as [n' l']. inv H6.
                eapply init_var_for_clock_st_follows in H3; destruct H3 as [_ Hfollows].
                simpl in Hfollows.
                eapply (Pos.lt_irrefl x10).
                eapply Pos.lt_le_trans...
                etransitivity...
                eapply min_fold_le.
             ++ eapply normalize_exps_normalized_lexp in H0. rewrite Forall_forall in H0...
          -- eapply init_var_for_clock_normalized_eq in H3; rewrite Forall_forall in *...
    - (* app *)
      simpl in Hnorm. destruct o; repeat inv_bind...
      rewrite <- app_assoc.
      repeat rewrite Forall_app. repeat split...
      specialize (normalize_reset_spec (hd_default x4)) as [[? [? [? Hspec]]]|Hspec]; subst;
        rewrite Hspec in H1; clear Hspec; repeat inv_bind.
      + constructor.
      + destruct (hd _ _); simpl in H1.
        repeat inv_bind. repeat constructor.
        apply normalized_lexp_hd_default...
      + eapply normalize_exps_normalized_eq in H0; eauto.
        apply normalize_exp_st_follows in H; destruct H as [_ Hfollows1].
        apply normalize_reset_st_follows in H1; destruct H1 as [_ Hfollows2].
        solve_forall.
        eapply Pos.lt_le_trans... etransitivity...
  Qed.
  Hint Resolve normalize_rhs_normalized_eq.

  Corollary normalize_rhss_normalized_eq : forall es keep_fby es' eqs' out st st',
      normalize_rhss keep_fby es st = (es', eqs', st') ->
      Forall (fun o => Pos.lt o (smallest_ident st)) out ->
      Forall (normalized_equation out) eqs'.
  Proof.
    intros es keep_fby es' eqs' out st st' Hnorm Hlt.
    unfold normalize_rhss in Hnorm; repeat inv_bind.
    eapply map_bind2_normalized_eq in H; eauto.
    rewrite Forall_forall; intros; eauto.
  Qed.
  Hint Resolve normalize_rhss_normalized_eq.

  Lemma normalize_equation_normalized_eq : forall G vars eq to_cut eqs' out st st',
      wt_equation G vars eq ->
      normalize_equation to_cut eq st = (eqs', st') ->
      Forall (fun o => Pos.lt o (smallest_ident st)) out ->
      incl out to_cut ->
      Forall (normalized_equation out) eqs'.
  Proof with eauto.
    intros G vars [xs es] to_cut eqs' out st st' Hwt Hnorm Hlt Hincl.
    unfold normalize_equation in Hnorm.
    repeat inv_bind.
    remember (negb (existsb (fun x : positive => existsb (fun c : positive => (x =? c)%positive) to_cut) xs)) as keep_fby.
    assert (keep_fby = true -> Forall (fun x => ~In x out) xs) as Hin.
    { intro Hkeep; subst.
      rewrite Bool.negb_true_iff in Hkeep. rewrite existsb_Forall in Hkeep.
      rewrite forallb_Forall in Hkeep. solve_forall.
      rewrite Bool.negb_true_iff in H0. rewrite existsb_Forall in H0.
      rewrite forallb_Forall in H0. rewrite Forall_forall in H0.
      intro contra. apply Hincl in contra.
      apply H0 in contra.
      rewrite Pos.eqb_refl in contra; simpl in contra. congruence.
    }
    clear Heqkeep_fby.
    rewrite Forall_app. split.
    - assert (length xs = length (typesof x)) as Hlen.
      { destruct Hwt as [Hwt1 Hwt2].
        eapply normalize_rhss_typeof in H; eauto.
        rewrite H.
        repeat rewrite_Forall_forall. auto. } clear Hwt.
      eapply normalize_rhss_normalized_rhs in H; eauto.
      revert xs Hin Hlen.
      induction H; intros xs Hin Hlen; constructor.
      + inv H...
        * destruct xs; simpl in *; try omega.
          constructor...
          specialize (Hin eq_refl). inv Hin. auto.
        * simpl in Hlen. rewrite app_length in Hlen.
          rewrite numstreams_length_typeof in Hlen.
          specialize (normalized_cexp_numstreams _ H1) as Hlen'.
          rewrite Hlen' in *. simpl.
          destruct xs... simpl in Hlen. omega.
      + eapply IHForall.
        * intro Hkeep. apply Hin in Hkeep.
          apply Forall_skipn...
        * rewrite skipn_length.
          rewrite Hlen. simpl. rewrite app_length.
          rewrite numstreams_length_typeof. omega.
    - eapply normalize_rhss_normalized_eq in H; eauto.
  Qed.

  Corollary normalize_equations_normalized_eq : forall G vars eqs to_cut eqs' out st st',
      Forall (wt_equation G vars) eqs ->
      normalize_equations to_cut eqs st = (eqs', st') ->
      Forall (fun o => Pos.lt o (smallest_ident st)) out ->
      incl out to_cut ->
      Forall (normalized_equation out) eqs'.
  Proof.
    induction eqs; intros to_cut eqs' out st st' Hf Hnorm Hlt Hincl;
      simpl in Hnorm; repeat inv_bind.
    - constructor.
    - inv Hf. apply Forall_app; split.
      + eapply normalize_equation_normalized_eq; eauto.
      + eapply normalize_equation_st_follows in H; destruct H as [_ Hfollows].
        eapply IHeqs; eauto. solve_forall.
        eapply Pos.lt_le_trans; eauto.
  Qed.

  Lemma normalize_node_normalized_node : forall n Hwt,
      normalized_node (normalize_node n Hwt).
  Proof.
    intros n [G Hwt].
    unfold normalize_node.
    unfold normalized_node; simpl.
    destruct Hwt as [_ [_ [_ Hwt]]].
    eapply normalize_equations_normalized_eq; eauto.
    - apply surjective_pairing.
    - simpl.
      specialize (first_unused_ident_gt n _ eq_refl) as Hgt.
      unfold used_idents in Hgt. repeat rewrite map_app in Hgt.
      repeat rewrite Forall_app in Hgt.
      destruct Hgt as [_ [_ [_ Hgt]]]. assumption.
    - reflexivity.
  Qed.
End LNORMALIZATION.

Module LNormalizationFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Str : COINDSTREAMS Op OpAux)
       (Syn : LSYNTAX Ids Op)
       (Typ : LTYPING Ids Op Syn)
       (Lord : LORDERED Ids Op Syn)
       (Sem : LSEMANTICS Ids Op OpAux Syn Lord Str)
       <: LNORMALIZATION Ids Op OpAux Str Syn Typ Lord Sem.
  Include LNORMALIZATION Ids Op OpAux Str Syn Typ Lord Sem.
End LNormalizationFun.
