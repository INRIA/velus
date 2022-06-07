From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import CommonTyping.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Fresh.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax.

(** * Functions to rename an expression and change its base clock *)

Module Type SUBCLOCK
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv).

  Section subclock.
    Variable base: clock.
    Variable sub : Env.t ident.

    Definition rename_var (x : ident) :=
      or_default x (Env.find x sub).

    Fixpoint subclock_clock (ck : clock) :=
      match ck with
      | Cbase => base
      | Con ck' x t => Con (subclock_clock ck') (rename_var x) t
      end.

    Definition subclock_nclock (nck : nclock) :=
      (subclock_clock (fst nck), option_map rename_var (snd nck)).

    Definition subclock_ann {A} (ann : (A * clock)) :=
      (fst ann, subclock_clock (snd ann)).

    Fixpoint add_whens (e : exp) (ty : type) (ck : clock) :=
      match ck with
      | Cbase => e
      | Con ck' ckid (tx, b) => Ewhen [(add_whens e ty ck')] (ckid, tx) b ([ty], ck)
      end.

    Fixpoint subclock_exp (e : exp) :=
      match e with
      | Econst c => add_whens e (Tprimitive (ctype_cconst c)) base
      | Eenum _ ty => add_whens e ty base
      | Evar x ann => Evar (rename_var x) (subclock_ann ann)
      | Elast x ann => Elast x (subclock_ann ann)
      | Eunop op e1 ann => Eunop op (subclock_exp e1) (subclock_ann ann)
      | Ebinop op e1 e2 ann => Ebinop op (subclock_exp e1) (subclock_exp e2) (subclock_ann ann)
      | Efby e0s e1s anns => Efby (map subclock_exp e0s) (map subclock_exp e1s) (map subclock_ann anns)
      | Earrow e0s e1s anns => Earrow (map subclock_exp e0s) (map subclock_exp e1s) (map subclock_ann anns)
      | Ewhen es (x, tx) t ann => Ewhen (map subclock_exp es) (rename_var x, tx) t (subclock_ann ann)
      | Emerge (x, ty) es ann => Emerge (rename_var x, ty) (map (fun '(i, es) => (i, map subclock_exp es)) es) (subclock_ann ann)
      | Ecase e es d ann =>
        Ecase (subclock_exp e) (map (fun '(i, es) => (i, map subclock_exp es)) es) (option_map (map subclock_exp) d) (subclock_ann ann)
      | Eapp f es er ann => Eapp f (map subclock_exp es) (map subclock_exp er) (map subclock_ann ann)
      end.

    Definition subclock_equation '(xs, es) : equation :=
      (map rename_var xs, map subclock_exp es).

    (** *** Properties *)

    Lemma subclock_ann_clock {A} : forall (ann : (A * clock)),
        snd (subclock_ann ann) = subclock_clock (snd ann).
    Proof. reflexivity. Qed.

    Corollary map_subclock_ann_clock {A} : forall (anns : list (A * clock)),
        map snd (map subclock_ann anns) = map subclock_clock (map snd anns).
    Proof.
      induction anns; simpl; auto.
    Qed.

    Lemma map_subclock_ann_type {A} : forall (anns : list (A * clock)),
        map fst (map subclock_ann anns) = map fst anns.
    Proof.
      induction anns; simpl; auto.
    Qed.

  End subclock.

  Section subclock_clockof.

    Variable bck : clock.
    Variable sub : Env.t ident.

    Lemma add_whens_clockof : forall e ty ck,
        clockof e = [Cbase] ->
        clockof (add_whens e ty ck) = [ck].
    Proof.
      intros * Hck.
      destruct ck as [|?? (?&?)]; simpl in *; auto.
    Qed.

    Lemma add_whens_nclockof : forall e ty ck,
        nclockof e = [(Cbase, None)] ->
        nclockof (add_whens e ty ck) = [(ck, None)].
    Proof.
      intros * Hck.
      destruct ck as [|?? (?&?)]; simpl in *; auto.
    Qed.

    Lemma subclock_exp_nclockof : forall e,
        nclockof (subclock_exp bck sub e) = map (subclock_nclock bck sub) (nclockof e).
    Proof.
      destruct e; destruct_conjs; simpl in *; auto.
      - (* const *)
        apply add_whens_nclockof; auto.
      - (* enum *)
        apply add_whens_nclockof; auto.
      - (* fby *)
        rewrite 2 map_map; auto.
      - (* arrow *)
        rewrite 2 map_map; auto.
      - (* when *)
        rewrite map_map; auto.
      - (* merge *)
        rewrite map_map; auto.
      - (* case *)
        rewrite map_map; auto.
      - (* app *)
        rewrite 2 map_map; auto.
    Qed.

    Corollary subclock_exp_nclocksof : forall es,
        nclocksof (map (subclock_exp bck sub) es) = map (subclock_nclock bck sub) (nclocksof es).
    Proof.
      intros es.
      unfold nclocksof. rewrite 2 flat_map_concat_map, concat_map, 2 map_map.
      f_equal.
      eapply map_ext; intros. apply subclock_exp_nclockof.
    Qed.

    Corollary subclock_exp_clockof : forall e,
        clockof (subclock_exp bck sub e) = map (subclock_clock bck sub) (clockof e).
    Proof.
      intros.
      rewrite 2 clockof_nclockof, subclock_exp_nclockof, 2 map_map; auto.
    Qed.

    Corollary subclock_exp_clocksof : forall es,
        clocksof (map (subclock_exp bck sub) es) = map (subclock_clock bck sub) (clocksof es).
    Proof.
      intros es.
      unfold clocksof. rewrite 2 flat_map_concat_map, concat_map, 2 map_map.
      f_equal.
      eapply map_ext; intros. apply subclock_exp_clockof.
    Qed.

  End subclock_clockof.

  Section subclock_typeof.

    Variable bck : clock.
    Variable sub : Env.t ident.

    Lemma add_whens_typeof : forall e ty ck,
        typeof e = [ty] ->
        typeof (add_whens e ty ck) = [ty].
    Proof.
      intros * Hty.
      destruct ck as [|?? (?&?)]; simpl in *; auto.
    Qed.

    Lemma subclock_exp_typeof : forall e,
        typeof (subclock_exp bck sub e) = typeof e.
    Proof.
      destruct e; destruct_conjs; simpl in *; auto.
      - (* const *)
        apply add_whens_typeof; auto.
      - (* enum *)
        apply add_whens_typeof; auto.
      - (* fby *)
        rewrite map_map; auto.
      - (* arrow *)
        rewrite map_map; auto.
      - (* app *)
        rewrite map_map; auto.
    Qed.

    Corollary subclock_exp_typesof : forall es,
        typesof (map (subclock_exp bck sub) es) = typesof es.
    Proof.
      intros es.
      unfold typesof . rewrite 2 flat_map_concat_map, map_map.
      f_equal.
      eapply map_ext; intros. apply subclock_exp_typeof.
    Qed.
  End subclock_typeof.

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

End SUBCLOCK.

Module SubClockFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       <: SUBCLOCK Ids Op OpAux Cks Senv Syn.
  Include SUBCLOCK Ids Op OpAux Cks Senv Syn.
End SubClockFun.
