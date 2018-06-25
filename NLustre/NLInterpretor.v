Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Coq.Sorting.Permutation.

Require Import Coq.FSets.FMapPositive.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.Ordered.
Require Import Velus.NLustre.Stream.
Require Import Velus.NLustre.NLSemantics.

(** * The NLustre semantics *)

(**

  We provide an interpretor for the semantics of NLustre.

 *)

Module Type NLINTERPRETOR
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Op)
       (Import Clks  : CLOCKS      Ids)
       (Import Syn   : NLSYNTAX    Ids Op Clks)
       (Import Str   : STREAM          Op OpAux)
       (Import Ord   : ORDERED     Ids Op Clks Syn)
       (Import Sem   : NLSEMANTICS Ids Op OpAux Clks Syn Str Ord).

  (** ** Instantaneous semantics *)

  Section InstantInterpretor.

    Variable base : bool.
    Variable R: R.

    Definition interp_var_instant (x: ident): value :=
      match PM.find x R with
      | Some v => v
      | None => absent
      end.

    Fixpoint interp_clock_instant (c: clock): bool :=
      match c with
      | Cbase =>
        base
      | Con c x b =>
        let cb := interp_clock_instant c in
        match interp_var_instant x with
        | present xv =>
          match val_to_bool xv with
          | Some b' =>
            cb && b' ==b b
          | None => false
          end
        | absent =>
          false
        end
      end.

    (* Inductive sem_clock_instant: clock -> bool -> Prop := *)
    (* | Sbase: *)
    (*     sem_clock_instant Cbase base *)
    (* | Son: *)
    (*     forall ck x c b, *)
    (*       sem_clock_instant ck true -> *)
    (*       sem_var_instant x (present c) -> *)
    (*       val_to_bool c = Some b -> *)
    (*       sem_clock_instant (Con ck x b) true *)
    (* | Son_abs1: *)
    (*     forall ck x c, *)
    (*       sem_clock_instant ck false -> *)
    (*       sem_var_instant x absent -> *)
    (*       sem_clock_instant (Con ck x c) false *)
    (* | Son_abs2: *)
    (*     forall ck x c b, *)
    (*       sem_clock_instant ck true -> *)
    (*       sem_var_instant x (present c) -> *)
    (*       val_to_bool c = Some b -> *)
    (*       sem_clock_instant (Con ck x (negb b)) false. *)

    Fixpoint interp_lexp_instant (e: lexp): value :=
      match e with
      | Econst c =>
        if base then present (sem_const c) else absent
      | Evar x _ =>
        interp_var_instant x
      | Ewhen e x b =>
        match interp_var_instant x, interp_lexp_instant e with
        | present xv, present ev =>
          match val_to_bool xv with
          | Some b' => if b ==b b' then present ev else absent
          | None => absent
          end
        | _, _ => absent
        end
      | Eunop op e _ =>
        match interp_lexp_instant e with
        | present v =>
          match sem_unop op v (typeof e) with
          | Some v' => present v'
          | None => absent
          end
        | absent => absent
        end
      | Ebinop op e1 e2 _ =>
        match interp_lexp_instant e1, interp_lexp_instant e2 with
        | present v1, present v2 =>
          match sem_binop op v1 (typeof e1) v2 (typeof e2) with
          | Some v => present v
          | None => absent
          end
        | _, _ => absent
        end
      end.

    Definition interp_lexps_instant (les: list lexp): list value :=
      map interp_lexp_instant les.

    (* Inductive sem_laexp_instant: clock -> lexp -> value -> Prop:= *)
    (* | SLtick: *)
    (*     forall ck le c, *)
    (*       sem_lexp_instant le (present c) -> *)
    (*       sem_clock_instant ck true -> *)
    (*       sem_laexp_instant ck le (present c) *)
    (* | SLabs: *)
    (*     forall ck le, *)
    (*       sem_lexp_instant le absent -> *)
    (*       sem_clock_instant ck false -> *)
    (*       sem_laexp_instant ck le absent. *)

    (* Inductive sem_laexps_instant: clock -> lexps -> list value -> Prop:= *)
    (* | SLticks: *)
    (*     forall ck ces cs vs, *)
    (*       vs = map present cs -> *)
    (*       sem_lexps_instant ces vs -> *)
    (*       sem_clock_instant ck true -> *)
    (*       sem_laexps_instant ck ces vs *)
    (* | SLabss: *)
    (*     forall ck ces vs, *)
    (*       vs = map (fun _ => absent) ces -> *)
    (*       sem_lexps_instant ces vs -> *)
    (*       sem_clock_instant ck false -> *)
    (*       sem_laexps_instant ck ces vs. *)

    Fixpoint interp_cexp_instant (e: cexp): value :=
      match e with
      | Emerge x t f =>
        match interp_var_instant x, interp_cexp_instant t, interp_cexp_instant f with
        | present xv, present tv, absent =>
          if xv ==b true_val then present tv else absent
        | present xv, absent, present fv =>
          if xv ==b false_val then present fv else absent
        | _, _, _ => absent
        end

      | Eite b t f =>
        match interp_lexp_instant b, interp_cexp_instant t, interp_cexp_instant f with
        | present bv, present tv, present fv =>
          match val_to_bool bv with
          | Some b' => present (if b' then tv else fv)
          | None => absent
          end
        | _, _, _ => absent
        end

      | Eexp e =>
        interp_lexp_instant e
      end.

    (* | Site_eq: *)
    (*     forall x t f c b ct cf, *)
    (*       sem_lexp_instant x (present c) -> *)
    (*       sem_cexp_instant t (present ct) -> *)
    (*       sem_cexp_instant f (present cf) -> *)
    (*       val_to_bool c = Some b -> *)
    (*       sem_cexp_instant (Eite x t f) (if b then present ct else present cf) *)
    (* | Site_abs: *)
    (*     forall b t f, *)
    (*       sem_lexp_instant b absent -> *)
    (*       sem_cexp_instant t absent -> *)
    (*       sem_cexp_instant f absent -> *)
    (*       sem_cexp_instant (Eite b t f) absent *)
    (* | Sexp: *)
    (*     forall e v, *)
    (*       sem_lexp_instant e v -> *)
    (*       sem_cexp_instant (Eexp e) v. *)

    (* Inductive sem_caexp_instant: clock -> cexp -> value -> Prop := *)
    (* | SCtick: *)
    (*     forall ck ce c, *)
    (*       sem_cexp_instant ce (present c) -> *)
    (*       sem_clock_instant ck true -> *)
    (*       sem_caexp_instant ck ce (present c) *)
    (* | SCabs: *)
    (*     forall ck ce, *)
    (*       sem_cexp_instant ce absent -> *)
    (*       sem_clock_instant ck false -> *)
    (*       sem_caexp_instant ck ce absent. *)

    (* Inductive rhs_absent_instant: equation -> Prop := *)
    (* | AEqDef: *)
    (*     forall x ck cae, *)
    (*       sem_caexp_instant ck cae absent -> *)
    (*       rhs_absent_instant (EqDef x ck cae) *)
    (* | AEqApp: *)
    (*     forall x f ck laes vs r, *)
    (*       sem_laexps_instant ck laes vs -> *)
    (*       Forall (fun c => c = absent) vs -> *)
    (*       rhs_absent_instant (EqApp x ck f laes r) *)
    (* | AEqFby: *)
    (*     forall x ck v0 lae, *)
    (*       sem_laexp_instant ck lae absent -> *)
    (*       rhs_absent_instant (EqFby x ck v0 lae). *)

    Lemma interp_var_instant_sound:
      forall x v,
        sem_var_instant R x v ->
        v = interp_var_instant x.
    Proof.
      unfold interp_var_instant; induction 1 as [?? H]; now rewrite H.
    Qed.

    Ltac rw_lexp_helper :=
      repeat match goal with
             | _: sem_var_instant R ?x ?v |- context[interp_var_instant ?x] =>
               erewrite <-(interp_var_instant_sound x v); eauto; simpl
             | H: val_to_bool ?x = _ |- context[val_to_bool ?x] =>
               rewrite H
             | H: sem_unop ?op ?c ?t = _ |- context[sem_unop ?op ?c ?t] =>
               rewrite H
             | H: sem_binop ?op ?c1 ?t1 ?c2 ?t2 = _ |- context[sem_binop ?op ?c1 ?t1 ?c2 ?t2] =>
               rewrite H
          end.

    Lemma interp_clock_instant_sound:
      forall c b,
        sem_clock_instant base R c b ->
        b = interp_clock_instant c.
    Proof.
      induction 1; auto; simpl; rw_lexp_helper;
        rewrite <-IHsem_clock_instant; destruct b; auto.
    Qed.

    Lemma interp_lexp_instant_sound:
      forall e v,
        sem_lexp_instant base R e v ->
        v = interp_lexp_instant e.
    Proof.
      induction 1; simpl;
        try rewrite <-IHsem_lexp_instant;
        try rewrite <-IHsem_lexp_instant1;
        try rewrite <-IHsem_lexp_instant2;
        rw_lexp_helper; auto;
          destruct b; auto.
    Qed.

    Lemma interp_lexps_instant_sound:
      forall es vs,
        sem_lexps_instant base R es vs ->
        vs = interp_lexps_instant es.
    Proof.
      induction 1; simpl; auto.
      f_equal; auto.
      now apply interp_lexp_instant_sound.
    Qed.

    Ltac rw_cexp_helper :=
      repeat (rw_lexp_helper;
              repeat match goal with
                     | _: sem_lexp_instant base R ?e ?v |- context[interp_lexp_instant ?e] =>
                       erewrite <-(interp_lexp_instant_sound e v); eauto; simpl
                     end).

    Lemma interp_cexp_instant_sound:
      forall e v,
        sem_cexp_instant base R e v ->
        v = interp_cexp_instant e.
    Proof.
      induction 1; simpl;
        try rewrite <-IHsem_cexp_instant;
        try rewrite <-IHsem_cexp_instant1;
        try rewrite <-IHsem_cexp_instant2;
        rw_cexp_helper;
        try rewrite equiv_decb_refl; auto;
          destruct b; auto.
    Qed.

  End InstantInterpretor.

  (** ** Liftings of instantaneous semantics *)

  Section LiftInterpretor.

    Variable bk : stream bool.
    Variable H: history.

    (* Definition restr H (n: nat): R := *)
    (*   PM.map (fun xs => xs n) H. *)
    (* Hint Unfold restr. *)

    (* Definition lift1 {A B} (f : A -> B) (s : stream A) : stream B *)
    (*     := fun n => f (s n). *)
    (* Hint Unfold lift1. *)

    Definition lift {A B} (interp: bool -> R -> A -> B) x: stream B :=
      fun n => interp (bk n) (restr H n) x.
    Hint Unfold lift.

    Definition interp_clock (ck: clock): stream bool :=
      lift interp_clock_instant ck.

    Definition interp_var (x: ident): stream value :=
      lift (fun base => interp_var_instant) x.

    (* Definition sem_vars H (x: idents)(xs: stream (list value)): Prop := *)
    (*   lift (fun base R => Forall2 (sem_var_instant R)) H x xs. *)

    (* Definition sem_laexp H ck (e: lexp)(xs: stream value): Prop := *)
    (*   lift (fun base R => sem_laexp_instant base R ck) H e xs. *)

    (* Definition sem_laexps *)
    (*     H (ck: clock)(e: lexps)(xs: stream (list value)): Prop := *)
    (*   lift (fun base R => sem_laexps_instant base R ck) H e xs. *)

    Definition interp_lexp (e: lexp): stream value :=
      lift interp_lexp_instant e.

    Definition interp_lexps (e: lexps): stream (list value) :=
      lift interp_lexps_instant e.

    Definition interp_lexps' (e: lexps): list (stream value) :=
      map interp_lexp e.

    Lemma interp_lexps'_sound:
      forall es ess,
        sem_lexps bk H es ess ->
        Forall2 (sem_lexp bk H) es (interp_lexps' es).
    Proof.
      induction es; intros ** Sem; simpl; auto.
      constructor.
      - intro n; specialize (Sem n); inv Sem.
        unfold interp_lexp, lift.
        erewrite <-interp_lexp_instant_sound; eauto.
      - eapply IHes.
        intro n; specialize (Sem n); inv Sem.
        instantiate (1 := fun n => tl (ess n)).
        simpl.
        rewrite <-H2; simpl; auto.
    Qed.

    (* Definition sem_caexp H ck (c: cexp)(xs: stream value): Prop := *)
    (*   lift (fun base R => sem_caexp_instant base R ck) H c xs. *)

    Definition interp_cexp (e: cexp): stream value :=
      lift interp_cexp_instant e.

    (* Definition sound {A B} H (x: A) (xs: stream B) *)
    (*            (sem: history -> A -> stream B -> Prop) *)
    (*            (interp: history -> A -> stream B) := *)
    (*   sem H x xs -> *)
    (*   forall n, interp H x n = xs n. *)

    (* Lemma lift_sound: *)
    (*   forall {A B} H (x: A) (xs: stream B) (sem: bool -> R -> A -> B -> Prop) (interp: bool -> R -> A -> B), *)
    (*     (forall b R v, sem b R x v -> v = interp b R x) -> *)
    (*     sound H x xs (Sem.lift bk sem) (lift interp). *)
    (* Proof. *)
    (*   unfold Sem.lift, lift; intros ** Sound Sem n. *)
    (*   now specialize (Sem n); apply Sound in Sem. *)
    (* Qed. *)

    (* Lemma interp_var_sound: *)
    (*   forall H x xs, *)
    (*     sound H x xs (sem_var bk) interp_var. *)
    (* Proof. *)
    (*   intros; apply lift_sound; intros. *)
    (*   now apply interp_var_instant_sound. *)
    (* Qed. *)

    (* Lemma interp_lexp_sound: *)
    (*   forall H e es, *)
    (*     sound H e es (sem_lexp bk) interp_lexp. *)
    (* Proof. *)
    (*   intros; apply lift_sound; intros. *)
    (*   now apply interp_lexp_instant_sound. *)
    (* Qed. *)

  End LiftInterpretor.

End NLINTERPRETOR.

(* Module NLSemanticsFun *)
(*        (Ids   : IDS) *)
(*        (Op    : OPERATORS) *)
(*        (OpAux : OPERATORS_AUX Op) *)
(*        (Clks  : CLOCKS    Ids) *)
(*        (Syn   : NLSYNTAX  Ids Op Clks) *)
(*        (Str   : STREAM        Op OpAux) *)
(*        (Ord   : ORDERED   Ids Op Clks Syn) *)
(*        <: NLSEMANTICS Ids Op OpAux Clks Syn Str Ord. *)
(*   Include NLSEMANTICS Ids Op OpAux Clks Syn Str Ord. *)
(* End NLSemanticsFun. *)
