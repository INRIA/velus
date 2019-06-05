From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Sorting.Permutation.

From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CETyping.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import CoreExpr.Stream.
From Velus Require Import CoreExpr.CESemantics.

(** * Interpreter for Core Expresssions *)

Module Type CEINTERPRETER
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Op)
       (Import CESyn : CESYNTAX        Op)
       (Import Str   : STREAM          Op OpAux)
       (Import CESem : CESEMANTICS Ids Op OpAux CESyn Str)
       (Import CETyp : CETYPING    Ids Op       CESyn)
       (Import CEClk : CECLOCKING  Ids Op       CESyn)
       (Import CEFree: CEISFREE    Ids Op       CESyn).

  (** ** Instantaneous semantics *)

  (** ** Instantaneous semantics *)

  Section InstantInterpreter.

    Variable base : bool.
    Variable R: env.

    Definition interp_var_instant (x: ident): option value :=
      Env.find x R.

    Definition interp_vars_instant (xs: list ident): option (list value) :=
      omap interp_var_instant xs.

    Fixpoint interp_clock_instant (c: clock) : option bool :=
      match c with
      | Cbase => Some base
      | Con c x b =>
        match interp_clock_instant c with
        | Some true => match interp_var_instant x with
                       | Some (present xv) =>
                         match val_to_bool xv with
                         | Some xb => Some (xb ==b b)
                         | None => None
                         end
                       | _ => None
                       end
        | Some false => match interp_var_instant x with
                        | Some absent => Some false
                        | _ => None
                        end
        | None => None
        end
      end.

     Fixpoint interp_lexp_instant (e: lexp) : option value :=
       match e with
       | Econst c => Some (if base then present (sem_const c) else absent)
       | Evar x _ => interp_var_instant x
       | Ewhen e x b =>
           match interp_var_instant x, interp_lexp_instant e with
           | Some (present xv), Some (present ev) =>
               option_map (fun b'=> if b' ==b b then present ev else absent)
                          (val_to_bool xv)
           | Some absent, Some absent => Some absent
           | _, _ => None
           end
       | Eunop op e _ =>
           match interp_lexp_instant e with
           | Some (present v) => option_map present (sem_unop op v (typeof e))
           | vo => vo
           end
       | Ebinop op e1 e2 _ =>
           match interp_lexp_instant e1, interp_lexp_instant e2 with
           | Some (present v1), Some (present v2) =>
               option_map present
                          (sem_binop op v1 (typeof e1) v2 (typeof e2))
           | Some absent, Some absent => Some absent
           | _, _ => None
           end
      end.

    Definition interp_lexps_instant (les: list lexp) : option (list value) :=
      omap interp_lexp_instant les.

    Fixpoint interp_cexp_instant (e: cexp) : option value :=
      match e with
      | Emerge x t f =>
        match interp_var_instant x with
        | Some (present xv) =>
          match val_to_bool xv, interp_cexp_instant t, interp_cexp_instant f with
          | Some true, Some (present tv), Some absent => Some (present tv)
          | Some false, Some absent, Some (present fv) => Some (present fv)
          | _, _, _ => None
          end
        | Some absent =>
          match interp_cexp_instant t, interp_cexp_instant f with
          | Some absent, Some absent => Some absent
          | _, _ => None
          end
        | None => None
        end
      | Eite b t f =>
        match interp_lexp_instant b, interp_cexp_instant t, interp_cexp_instant f with
        | Some (present bv), Some (present tv), Some (present fv) =>
          option_map (fun (b : bool) => if b then present tv else present fv)
                     (val_to_bool bv)
        | Some absent, Some absent, Some absent => Some absent
        | _, _, _ => None
        end
      | Eexp e => interp_lexp_instant e
      end.

    Lemma interp_var_instant_correct:
      forall x v,
        sem_var_instant R x v <-> interp_var_instant x = Some v.
    Proof. reflexivity. Qed.

    Lemma interp_vars_instant_correct:
      forall xs vs,
        sem_vars_instant R xs vs <-> interp_vars_instant xs = Some vs.
    Proof.
      unfold sem_vars_instant, interp_vars_instant.
      induction xs as [|x xs IH]. now split; inversion 1.
      destruct vs as [|v vs].
      - split; intro HH. now inv HH.
        simpl in HH.
        destruct (interp_var_instant x); [|discriminate].
        destruct (omap interp_var_instant xs); discriminate.
      - split; intro HH.
        + simpl. inversion_clear HH as [|???? Hsem FA2].
          apply IH in FA2. rewrite FA2.
          rewrite interp_var_instant_correct in Hsem. now rewrite Hsem.
        + simpl in HH.
          destruct (interp_var_instant x) eqn:Hsv; [|discriminate].
          rewrite <-interp_var_instant_correct in Hsv.
          destruct (omap interp_var_instant xs) eqn:Hxs; [|discriminate].
          inv HH. constructor; auto.
          now apply IH.
    Qed.          

    (* TODO: move me *)
    Lemma equiv_decb_negb:
      forall x, (x ==b negb x) = false.
    Proof. destruct x; simpl; auto. Qed.

    Lemma interp_clock_instant_correct:
      forall c b,
        sem_clock_instant base R c b <-> interp_clock_instant c = Some b.
    Proof.
      induction c as [|c IH].
      now simpl; split; inversion 1; eauto using sem_clock_instant.
      split; intro HH.
      - inv HH; simpl;
        repeat match goal with
               | H:sem_clock_instant _ _ _ _ |- _ => apply IH in H; rewrite H
               | H:sem_var_instant _ _ _ |- _ =>
                 rewrite interp_var_instant_correct in H; rewrite H
               | H:val_to_bool _ = _ |- _ =>
                 rewrite H, ?equiv_decb_refl, ?equiv_decb_negb
               end; auto.
      - inv HH.
        destruct (interp_clock_instant c) as [cb|] eqn:Hc; [|discriminate].
        destruct (interp_var_instant i) eqn:Hi; [|destruct cb; discriminate].
        apply interp_var_instant_correct in Hi.
        destruct cb.
        + destruct v as [|vc]; [discriminate|].
          destruct (val_to_bool vc) as [vcb|] eqn:Hvc; [|discriminate].
          match goal with H:Some _ = Some _ |- _ => inv H end.
          destruct vcb, b; unfold equiv_decb; simpl.
          * eapply Son; eauto; now apply IH.
          * assert (false = negb true) as Hf by auto.
            rewrite Hf at 1. eapply Son_abs2; eauto; now apply IH.
          * assert (true = negb false) as Hf by auto.
            rewrite Hf at 1. eapply Son_abs2; eauto; now apply IH.
          * eapply Son; eauto; now apply IH.
        + destruct v as [|vc]; [|discriminate].
          match goal with H:Some _ = Some _ |- _ => inv H end.
          eapply Son_abs1; auto. now apply IH.
    Qed.

    Lemma interp_lexp_instant_correct:
      forall e v,
        sem_lexp_instant base R e v <-> interp_lexp_instant e = Some v.
    Proof.
      induction e; simpl.
      - (* Econst *)
        split; inversion_clear 1; subst; eauto using sem_lexp_instant.
      - (* Evar *)
        setoid_rewrite <-interp_var_instant_correct.
        split; [inversion_clear 1|]; eauto using sem_lexp_instant.
      - (* Ewhen *)
        split; intro HH.
        + inv HH;
          repeat match goal with
                 | H:sem_var_instant _ _ _ |- _ =>
                   rewrite interp_var_instant_correct in H; rewrite H
                 | H:sem_lexp_instant _ _ _ _ |- _ =>
                   rewrite IHe in H; rewrite H
                 | H:val_to_bool _ = _ |- _ => rewrite H
                 end; simpl; rewrite ?equiv_decb_refl, ?equiv_decb_negb; auto.
        + destruct (interp_var_instant i) as [vi|] eqn:Hi; [|discriminate].
          apply interp_var_instant_correct in Hi.
          destruct (interp_lexp_instant e) as [ev|];
            [|destruct vi; discriminate].
          edestruct IHe as (N & IH); clear IHe N; specialize (IH eq_refl).
          destruct vi.
          now destruct ev; [inv HH; eauto using sem_lexp_instant|discriminate].
          destruct ev as [|ev]; [discriminate|].
          destruct (val_to_bool c) as [cb|] eqn:Hc; [|discriminate].
          simpl in *.
          destruct (cb ==b b) eqn:Hcb; inv HH;
            rewrite ?equiv_decb_equiv in Hcb; rewrite ?Hcb in *;
              eauto using sem_lexp_instant.
          assert (b = negb cb) as ->
              by (apply not_equiv_decb_equiv in Hcb;
                  destruct b, cb; auto; exfalso; now apply Hcb).
          eauto using sem_lexp_instant.
      - (* Eunop *)
        split; intro HH.
        + inv HH; repeat match goal with
                         | H:sem_lexp_instant _ _ _ _ |- _ =>
                           rewrite IHe in H; rewrite H
                         | H:sem_unop _ _ _ = _ |- _ => rewrite H
                         end; auto.
        + destruct (interp_lexp_instant e) as [ve|]; [|discriminate].
          edestruct IHe as (N & IH); clear IHe N; specialize (IH eq_refl).
          destruct ve.
          now inv HH; eauto using sem_lexp_instant.
          destruct (sem_unop u c (typeof e)) eqn:Hu; [|discriminate].
          inv HH; eauto using sem_lexp_instant.
      - (* Ebinop *)
        split; intro HH.
        + inv HH; repeat match goal with
                         | H:sem_lexp_instant _ _ _ _ |- _ =>
                           rewrite ?IHe1, ?IHe2 in H; rewrite H
                         | H:sem_binop _ _ _ _ _ = _ |- _ => rewrite H
                         end; auto.
        + destruct (interp_lexp_instant e1) as [ve1|]; [|discriminate].
          edestruct IHe1 as (N & IH1); clear N IHe1; specialize (IH1 eq_refl).
          destruct (interp_lexp_instant e2) as [ve2|]; [|destruct ve1; discriminate].
          edestruct IHe2 as (N & IH2); clear IHe2 N; specialize (IH2 eq_refl).
          destruct ve1 as [|v1], ve2 as [|v2]; try discriminate.
          now inv HH; eauto using sem_lexp_instant.
          destruct (sem_binop b v1 (typeof e1) v2 (typeof e2)) eqn:Hu; [|discriminate].
          inv HH; eauto using sem_lexp_instant.
    Qed.

    Lemma omap_interp_correct:
      forall {E V} sem interp,
        (forall (e : E) (v : V), sem e v <-> interp e = Some v) ->
        forall es vs,
          Forall2 sem es vs <-> omap interp es = Some vs.
    Proof.
      intros E V sem interp Hcor.
      induction es as [|e es IH]; simpl.
      now split; inversion_clear 1; [auto|constructor].
      split; intro HH.
      - inv HH.
        repeat match goal with
               | H:Forall2 _ _ _ |- _ => apply IH in H; rewrite H
               | H:sem _ _ |- _ => apply Hcor in H; rewrite H
               end; auto.
      - destruct (interp e) as [ev|] eqn:He; [|discriminate].
        apply Hcor in He.
        destruct (omap interp es) as [evs|]; [|discriminate].
        edestruct IH as (N & IH'); clear IH N; specialize (IH' eq_refl).
        inv HH; auto.
    Qed.

    Lemma interp_lexps_instant_correct:
      forall es vs,
        sem_lexps_instant base R es vs <-> interp_lexps_instant es = Some vs.
    Proof.
      apply omap_interp_correct.
      apply interp_lexp_instant_correct.
    Qed.

    Lemma interp_cexp_instant_correct:
      forall e v,
        sem_cexp_instant base R e v <-> interp_cexp_instant e = Some v.
    Proof.
      induction e.
      - (* Emerge *)
        split; intro HH.
        + inv HH; simpl;
            repeat match goal with
                   | H:sem_var_instant _ _ _ |- _ =>
                     rewrite interp_var_instant_correct in H; rewrite H
                   | H:sem_cexp_instant _ _ _ _ |- _ =>
                     rewrite ?IHe1, ?IHe2 in H; rewrite H
                   end;
            now rewrite ?val_to_bool_true, ?val_to_bool_false.
        + simpl in HH.
          destruct (interp_var_instant i) as [iv|] eqn:Hi; [|discriminate].
          destruct iv.
          * destruct (interp_cexp_instant e1) as [v1|]; [|discriminate].
            destruct v1; [|discriminate].
            destruct (interp_cexp_instant e2) as [v2|]; [|discriminate].
            destruct v2; [|discriminate].
            edestruct IHe1 as (N & IH1); clear IHe1 N; specialize (IH1 eq_refl).
            edestruct IHe2 as (N & IH2); clear IHe2 N; specialize (IH2 eq_refl).
            inv HH; eauto using sem_cexp_instant.
          * destruct (interp_cexp_instant e1) as [v1|] eqn:He1;
              destruct (val_to_bool c) eqn:Hc;
              try destruct b;
              try discriminate;
              try apply val_to_bool_true' in Hc;
              try apply val_to_bool_false' in Hc;
              (edestruct IHe1 as (N & IH1); clear IHe1 N; specialize (IH1 eq_refl));
              destruct (interp_cexp_instant e2) as [v2|] eqn:He2;
              try (edestruct IHe2 as (N & IH2); clear IHe2 N; specialize (IH2 eq_refl));
              subst;
              try destruct v1;
              try destruct v2;
              try discriminate;
              inv HH; eauto using sem_cexp_instant.
      - (* Eite *)
        split; intro HH.
        + inv HH; simpl;
            repeat match goal with
                   | H:sem_lexp_instant _ _ _ _ |- _ =>
                     rewrite interp_lexp_instant_correct in H; rewrite H
                   | H:sem_cexp_instant _ _ _ _ |- _ =>
                     rewrite ?IHe1, ?IHe2 in H; rewrite H
                   | H:val_to_bool _ = _ |- _ => rewrite H
                   end; try destruct b; auto.
        + simpl in HH.
          destruct (interp_lexp_instant l) as [iv|] eqn:Hi; [|discriminate].
          apply interp_lexp_instant_correct in Hi.
          destruct (interp_cexp_instant e1) as [v1|]; [|destruct iv; discriminate].
          destruct (interp_cexp_instant e2) as [v2|]; [|destruct iv, v1; discriminate].
          edestruct IHe1 as (N & IH1); clear IHe1 N; specialize (IH1 eq_refl).
          edestruct IHe2 as (N & IH2); clear IHe2 N; specialize (IH2 eq_refl).
          destruct iv; destruct v1, v2; try discriminate.
          now inv HH; eauto using sem_cexp_instant.
          destruct (val_to_bool c) eqn:Hc; [|discriminate].
          inv HH; eauto using sem_cexp_instant.
      - (* Eexp *)
        simpl. setoid_rewrite <-interp_lexp_instant_correct.
        split; intro HH; [now inv HH|now constructor].
    Qed.

    Definition interp_annotated_instant {E} (interp : E -> option value)
               (ck : clock) (e : E) : option value :=
      match interp_clock_instant ck, interp e with
      | Some true, Some (present v) => Some (present v)
      | Some false, Some absent => Some absent
      | _, _ => None
      end.

    Definition interp_laexp_instant ck e :=
      interp_annotated_instant interp_lexp_instant ck e.

    Definition interp_caexp_instant ck e :=
      interp_annotated_instant interp_cexp_instant ck e.

    Lemma interp_laexp_instant_correct:
      forall ck e v,
        sem_laexp_instant base R ck e v <-> interp_laexp_instant ck e = Some v.
    Proof.
      unfold interp_laexp_instant, interp_annotated_instant.
      split; intro HH.
      - inversion_clear HH as [??? Hs Hck|?? Hs Hck];
          apply interp_lexp_instant_correct in Hs as ->;
          now apply interp_clock_instant_correct in Hck as ->.
      - destruct (interp_clock_instant ck) eqn:Hck;
          try apply interp_clock_instant_correct in Hck;
          destruct (interp_lexp_instant e) as [ev|] eqn:He;
          try apply interp_lexp_instant_correct in He;
          try destruct b;
          try destruct ev;
          try discriminate;
          inv HH; now constructor.
    Qed.

    Lemma interp_caexp_instant_correct:
      forall ck e v,
        sem_caexp_instant base R ck e v <-> interp_caexp_instant ck e = Some v.
    Proof.
      unfold interp_caexp_instant, interp_annotated_instant.
      split; intro HH.
      - inversion_clear HH as [??? Hs Hck|?? Hs Hck];
          apply interp_cexp_instant_correct in Hs as ->;
          now apply interp_clock_instant_correct in Hck as ->.
      - destruct (interp_clock_instant ck) eqn:Hck;
          try apply interp_clock_instant_correct in Hck;
          destruct (interp_cexp_instant e) as [ev|] eqn:He;
          try apply interp_cexp_instant_correct in He;
          try destruct b;
          try destruct ev;
          try discriminate;
          inv HH; now constructor.
    Qed.

    (** Existence proofs *)
    
    Variable vars : list (ident * (type * clock)).
    Hypothesis NDvars : NoDupMembers vars.

    Inductive Ops_defined_in_lexp : lexp -> Prop :=
    | ODconst : forall c,
        Ops_defined_in_lexp (Econst c)
    | ODvar: forall x ty,
        Ops_defined_in_lexp (Evar x ty)
    | ODwhen : forall e x b,
        Ops_defined_in_lexp e ->
        Ops_defined_in_lexp (Ewhen e x b)
    | ODunop : forall op e ty,
        Ops_defined_in_lexp e ->
        (forall v, sem_lexp_instant base R e (present v) ->
                   sem_unop op v (typeof e) <> None) ->        
        Ops_defined_in_lexp (Eunop op e ty)
    | ODbinop: forall op e1 e2 ty,
        Ops_defined_in_lexp e1 ->
        Ops_defined_in_lexp e2 ->
        (forall v1 v2,
            sem_lexp_instant base R e1 (present v1) ->
            sem_lexp_instant base R e2 (present v2) ->
            sem_binop op v1 (typeof e1) v2 (typeof e2) <> None) ->
        Ops_defined_in_lexp (Ebinop op e1 e2 ty).

    Inductive Ops_defined_in_cexp : cexp -> Prop :=
    | ODmerge : forall x et ef,
        Ops_defined_in_cexp et ->
        Ops_defined_in_cexp ef ->
        Ops_defined_in_cexp (Emerge x et ef)
    | ODite : forall e et ef,
        Ops_defined_in_lexp e ->
        Ops_defined_in_cexp et ->
        Ops_defined_in_cexp ef ->
        Ops_defined_in_cexp (Eite e et ef)
    | ODexp : forall e,
        Ops_defined_in_lexp e ->
        Ops_defined_in_cexp (Eexp e).

    Definition var_inv (D : positive -> Prop) : Prop :=
      forall x, D x ->
                exists xv, sem_var_instant R x xv
                           /\ (exists xt xc cs,
                                  In (x, (xt, xc)) vars
                                  /\ sem_clock_instant base R xc cs
                                  /\ match xv with
                                     | absent => cs = false
                                     | present v => cs = true /\ wt_val v xt
                                     end).

    Lemma var_inv_weaken:
      forall (D1 D2 : positive -> Prop),
        var_inv D1 ->
        (forall x, D2 x -> D1 x) ->
        var_inv D2.
    Proof.
      intros D1 D2 I1 H12 x D2x.
      now apply H12, I1 in D2x.
    Qed.

    Local Ltac tidy_wt_wc :=
      repeat match goal with
             | H:In _ (idck vars) |- _ =>
               apply In_idck_exists in H as (xt' & I1'); clear H
             | H:In _ (idty vars) |- _ =>
               apply In_idty_exists in H as (xc' & I2'); clear H
             | H1:In (?x1, (?t1, ?c1)) vars, H2:In (?x2, (?t2, ?c2)) vars |- _ =>
               apply (NoDupMembers_det _ _ _ _ NDvars H1) in H2; inv H2
             end.

    (* TODO: Generalize and move to CESemantics? *)
    Local Ltac sem_det :=
      repeat match goal with
             | H1:sem_var_instant _ _ _, H2:sem_var_instant _ _ _ |- _ =>
               apply (sem_var_instant_det _ _ _ _ H1) in H2; subst
             | H1:sem_clock_instant _ _ _ _, H2:sem_clock_instant _ _ _ _ |- _ =>
               apply (sem_clock_instant_det _ _ _ _ _ H1) in H2; subst
             | H:present _ = present _ |- _ => inv H
             | H1:val_to_bool ?x = _, H2:val_to_bool ?x = _ |- _ =>
               rewrite H1 in H2; inv H2
             end.

    (* Exploit hypotheses of the forms: absent = absent <-> cks = false,
       present c = absent <-> cks = false, etc. *)      
    Local Ltac break_status_cks_iffs :=
      assert (forall v, present v <> absent) as Hpa by discriminate;
      repeat match goal with
             | H:?x = ?x <-> ?cks = ?b |- _ =>
               destruct H as (H & ?); specialize (H eq_refl)
             | H:present ?c = absent <-> ?cks = ?b |- _ =>
               apply not_iff_compat in H;
               rewrite Bool.not_false_iff_true in H;
               destruct H as (H & ?);
               specialize (H (Hpa _))
             | H:?x = ?x -> _ |- _ => specialize (H eq_refl)
             end; clear Hpa; subst.

    Lemma interp_clock_instant_good:
      forall ck,
        wt_clock (idty vars) ck ->
        wc_clock (idck vars) ck ->
        var_inv (fun x => Is_free_in_clock x ck) ->
        exists v, interp_clock_instant ck = Some v.
    Proof.
      induction ck as [|ck IH x]. now simpl; eauto.
      intros WT WC Inv.
      inv WT. inv WC.
      match goal with WT:wt_clock _ _, WC:wc_clock _ _ |- _ =>
                      specialize (IH WT WC) as (v & Hck) end.
      now eapply var_inv_weaken; [eassumption|simpl; auto].
      specialize (Inv x (FreeCon1 x _ _)) as (xv & Sx & (xt & xc & cs & I1 & I2 & I3)).
      simpl. setoid_rewrite Hck.
      tidy_wt_wc.
      apply interp_clock_instant_correct in I2.
      rewrite Hck in I2; inv I2.
      rewrite interp_var_instant_correct in Sx; rewrite Sx.
      destruct xv; [|destruct I3 as (Hcs & WTv)]; subst; eauto.
      apply wt_val_to_bool in WTv as (cb & WTv). rewrite WTv; eauto.
    Qed.

    Corollary sem_clock_instant_good:
      forall ck,
        wt_clock (idty vars) ck ->
        wc_clock (idck vars) ck ->
        var_inv (fun x => Is_free_in_clock x ck) ->
        exists v, sem_clock_instant base R ck v.
    Proof.
      setoid_rewrite interp_clock_instant_correct.
      auto using interp_clock_instant_good.
    Qed.

    Lemma sem_lexp_instant_clocked:
      forall e ck v,
        wc_lexp (idck vars) e ck ->
        var_inv (fun x => Is_free_in_lexp x e) ->
        sem_lexp_instant base R e v ->
        exists cks, sem_clock_instant base R ck cks
                    /\ (v = absent <-> cks = false).
    Proof.
      induction e; simpl; intros ck v WC Inv Se; inv WC.
      - (* Econst *)
        inv Se. exists base.
        split; eauto using sem_clock_instant.
        destruct base; intuition; discriminate.
      - (* Evar *)
        specialize (Inv i (FreeEvar i _))
          as (iv & Si & (it & ic & ics & I1 & I2 & I3)).
        inv Se. tidy_wt_wc. sem_det.
        exists ics. split; auto.
        destruct v; intuition; subst; try discriminate.
      - (* Ewhen *)
        inv Se; sem_det; try discriminate;
        repeat match goal with
               | H:sem_lexp_instant _ _ _ _, WC:wc_lexp _ e _ |- _ =>
                 eapply IHe with (1:=WC) in H as (cks & Scks & H); clear IHe
               | |- var_inv _ =>
                 now eapply var_inv_weaken; eauto; simpl; auto
               end; break_status_cks_iffs;
          eexists; (split; [eauto using sem_clock_instant|now intuition]).
      - (* Eunop *)
        assert (var_inv (fun x => Is_free_in_lexp x e)) as Inv'
          by (apply (var_inv_weaken _ _ Inv); auto).
        inv Se; match goal with
                | WC:wc_lexp _ _ _, H:sem_lexp_instant _ _ _ _ |- _ =>
                  specialize (IHe _ _ WC Inv' H)
                end; destruct IHe as (cks & Scks & H); break_status_cks_iffs;
          eexists; (split; [eauto using sem_clock_instant|now intuition]).
      - (* Ebinop *)
        assert (var_inv (fun x => Is_free_in_lexp x e1)) as Inv1
          by (apply (var_inv_weaken _ _ Inv); auto).
        assert (var_inv (fun x => Is_free_in_lexp x e2)) as Inv2
          by (apply (var_inv_weaken _ _ Inv); auto).
        inv Se; match goal with
                  WC:wc_lexp _ _ _, H:sem_lexp_instant _ _ _ _ |- _ =>
                  specialize (IHe1 _ _ WC Inv1 H) end;
        destruct IHe1 as (cks1 & Scks1 & H1);
        break_status_cks_iffs;
        eexists; (split; [eauto using sem_clock_instant|now intuition]).
    Qed.
      
    Lemma interp_lexp_instant_good:
      forall e ck,
        wt_lexp (idty vars) e ->
        wc_lexp (idck vars) e ck ->
        Ops_defined_in_lexp e ->
        var_inv (fun x => Is_free_in_lexp x e) ->
        exists v, interp_lexp_instant e = Some v.
    Proof.
      induction e; simpl; intros ck WT WC OD Inv.
      - (* Econst *) eauto.
      - (* Evar *)
        specialize (Inv i (FreeEvar i _)) as (v & Hsem & Inv).
        rewrite interp_var_instant_correct in Hsem. now eauto.
      - (* Ewhen *)
        inv WT. inv WC. inv OD.
        match goal with
          WT:wt_lexp _ _, WC:wc_lexp _ _ _, OD:Ops_defined_in_lexp _ |- _ =>
          specialize (IHe _ WT WC OD) as (ev & Hv) end.
        now eapply var_inv_weaken; [eassumption|simpl; auto].
        rewrite Hv.
        pose proof (Inv i (FreeEwhen2 _ i _))
          as (iv & Si & (it & ic & ics & I1 & I2 & I3)).
        tidy_wt_wc.
        rewrite interp_var_instant_correct in Si; rewrite Si.
        apply interp_lexp_instant_correct in Hv.
        eapply sem_lexp_instant_clocked in Hv as (cks & Hs & H); eauto.
        2:now eapply var_inv_weaken; [eassumption|simpl; auto].
        sem_det. destruct iv.
        + assert (ev = absent) by intuition. subst; eauto.
        + destruct I3 as (? & WT).
          assert (ev <> absent) as Habs by (subst; intuition).
          apply not_absent_present in Habs as (v & ->).
          apply wt_val_to_bool in WT as (? & ->). simpl; eauto.
      - (* Eunop *)
        inv WT. inv WC. inversion OD as [| | |??? ODe ODv|]; subst.
        match goal with WT:wt_lexp _ _, WC:wc_lexp _ _ _ |- _ =>
          specialize (IHe _ WT WC ODe) as (ev & Hv) end.
        now eapply var_inv_weaken; [eassumption|simpl; auto].
        rewrite Hv.
        apply interp_lexp_instant_correct in Hv.
        destruct ev; eauto.
        apply ODv, not_None_is_Some in Hv as (v & ->); simpl; eauto.
      - (* Ebinop *)
        inv WT. inversion WC as [| | | |????? WC1 WC2].
        inversion OD as [| | | |???? ODe1 ODe2 ODv]; subst.
        repeat match goal with WT:wt_lexp _ _, WC:wc_lexp _ _ _ |- _ =>
          specialize (IHe1 _ WT WC ODe1) as (ev1 & Hv1)
          || specialize (IHe2 _ WT WC ODe2) as (ev2 & Hv2) end;
          try (now eapply var_inv_weaken; [eassumption|simpl; auto]).
        rewrite Hv1, Hv2.
        apply interp_lexp_instant_correct in Hv1.
        apply interp_lexp_instant_correct in Hv2.
          eapply sem_lexp_instant_clocked in WC1 as (cks1 & Hs1 & HH1); eauto;
            [|now eapply var_inv_weaken; [eassumption|simpl; auto]];
          eapply sem_lexp_instant_clocked in WC2 as (cks2 & Hs2 & HH2); eauto;
            [|now eapply var_inv_weaken; [eassumption|simpl; auto]];
          sem_det.
        destruct ev1, ev2; eauto; break_status_cks_iffs; try discriminate.
        specialize (ODv _ _ Hv1 Hv2).
        apply not_None_is_Some in ODv as (v & ->).
        simpl; eauto.
    Qed.

    Corollary sem_lexp_instant_good:
      forall e ck,
        wt_lexp (idty vars) e ->
        wc_lexp (idck vars) e ck ->
        Ops_defined_in_lexp e ->
        var_inv (fun x => Is_free_in_lexp x e) ->
        exists v, sem_lexp_instant base R e v.
    Proof.
      setoid_rewrite interp_lexp_instant_correct.
      eauto using interp_lexp_instant_good.
    Qed.

    Lemma sem_cexp_instant_clocked:
      forall e ck v,
        wc_cexp (idck vars) e ck ->
        var_inv (fun x => Is_free_in_cexp x e) ->
        sem_cexp_instant base R e v ->
        exists cks, sem_clock_instant base R ck cks
                    /\ (v = absent <-> cks = false).
    Proof.
      induction e; simpl; intros ck v WC Inv Se;
        inversion WC as [???? Hin WC1 WC2|???? WCe WC1 WC2|?? WCe]; subst.
      - (* Emerge *)
        assert (var_inv (fun x=>Is_free_in_cexp x e1)) as Inv1
            by (eapply var_inv_weaken; [eauto|simpl; intuition]).
        assert (var_inv (fun x=>Is_free_in_cexp x e2)) as Inv2
            by (eapply var_inv_weaken with (1:=Inv); intuition).
        inv Se;
        repeat match goal with Se:sem_cexp_instant _ _ _ _ |- _ =>
          specialize (IHe1 _ _ WC1 Inv1 Se) as (cks1 & Sck1 & HH1)
                                               || specialize (IHe2 _ _ WC2 Inv2 Se) as (cks2 & Sck2 & HH2) end;
        break_status_cks_iffs.
        + inv Sck1. eexists; split; [eauto|now intuition].
          match goal with H1:negb _ = true, H2:false = negb _ |- _ =>
            rewrite H1 in H2; discriminate end.
        + inv Sck2. eexists; split; [eauto|now intuition].
          match goal with H1:negb _ = true, H2:negb _ = false |- _ =>
            rewrite H1 in H2; discriminate end.
        + inv Sck1.
          now eexists; split; [eauto|intuition].
          eexists false; split; [sem_det;discriminate|now intuition].
      - (* Eite *)
        assert (var_inv (fun x=>Is_free_in_cexp x e1)) as Inv1
            by (eapply var_inv_weaken; [eauto|simpl; intuition]).
        assert (var_inv (fun x=>Is_free_in_cexp x e2)) as Inv2
            by (eapply var_inv_weaken with (1:=Inv); intuition).
        inv Se;
        repeat match goal with Se:sem_cexp_instant _ _ _ _ |- _ =>
          specialize (IHe1 _ _ WC1 Inv1 Se) as (cks1 & Sck1 & HH1)
          || specialize (IHe2 _ _ WC2 Inv2 Se) as (cks2 & Sck2 & HH2) end;
        break_status_cks_iffs; eexists; split; eauto; try destruct b; intuition.
      - (* Eexp *)
        inversion_clear Se as [| | | | |?? He].
        apply (sem_lexp_instant_clocked _ _ _ WCe) in He as (cks & He & HH); eauto.
        now eapply var_inv_weaken with (1:=Inv); intuition.
    Qed.

    Lemma sem_lexp_instant_wt_val:
      forall e v,
        sem_lexp_instant base R e (present v) ->
        wt_lexp (idty vars) e ->
        var_inv (fun x => Is_free_in_lexp x e) ->
        wt_val v (typeof e).
    Proof.
      induction e; intros v Sv WT Inv.
      - (* Econst *)
        inv Sv. destruct base; [|discriminate].
        match goal with H:present _ = present _ |- _ => inv H end.
        apply wt_val_const.
      - (* Evar *)
        specialize (Inv i (FreeEvar i _))
          as (iv & Si & (it & ic & ics & I1 & I2 & I3)).
        inv Sv. sem_det. destruct I3 as (Hics & WTV).
        inv WT. now tidy_wt_wc.
      - (* Ewhen *)
        inv Sv. inv WT. apply IHe; auto.
        eapply var_inv_weaken; [eauto|now intuition].
      - (* Eunop *)
        inv Sv. inv WT. simpl.
        eapply pres_sem_unop; eauto.
        apply IHe; auto.
        eapply var_inv_weaken; [eauto|now intuition].
      - (* Ebinop *)
        inv Sv. inv WT. simpl.
        eapply pres_sem_binop; eauto.
        now apply IHe1; auto; eapply var_inv_weaken; [eauto|intuition].
        now apply IHe2; auto; eapply var_inv_weaken; [eauto|intuition].
    Qed.

    Lemma interp_cexp_instant_good:
      forall e ck,
        wt_cexp (idty vars) e ->
        wc_cexp (idck vars) e ck ->
        Ops_defined_in_cexp e ->
        var_inv (fun x => Is_free_in_cexp x e) ->
        exists v, interp_cexp_instant e = Some v.
    Proof.
      induction e; simpl; intros ck WT WC OD Inv;
        inversion_clear WT as [????? WT1 WT2|???? WTe WT1 WT2|? WTe];
        inversion_clear WC as [????? WC1 WC2|???? WCe WC1 WC2|?? WCe];
        inversion_clear OD as [??? ODe1 ODe2|??? ODe ODe1 ODe2|? ODe].
      - (* Emerge *)
        epose proof (var_inv_weaken _ (fun x=>Is_free_in_cexp x e1) Inv _) as Inv1.
        Unshelve. 2:now intuition.
        epose proof (var_inv_weaken _ (fun x=>Is_free_in_cexp x e2) Inv _) as Inv2.
        Unshelve. 2:now intuition.
        specialize (IHe1 _ WT1 WC1 ODe1 Inv1) as (v1 & IHe1).
        specialize (IHe2 _ WT2 WC2 ODe2 Inv2) as (v2 & IHe2).
        rewrite IHe1, IHe2.
        apply interp_cexp_instant_correct in IHe1.
        apply interp_cexp_instant_correct in IHe2.
        pose proof (Inv i (FreeEmerge_cond i _ _))
          as (iv & Si & (it & ic & ics & I1 & I2 & I3)).
        assert (Ii := Si). apply interp_var_instant_correct in Ii as ->.
        apply (sem_cexp_instant_clocked _ _ _ WC1 Inv1) in IHe1
          as (cks1 & Hck1 & HH1).
        apply (sem_cexp_instant_clocked _ _ _ WC2 Inv2) in IHe2
          as (cks2 & Hck2 & HH2).
        inv Hck1; inv Hck2; destruct iv, v1, v2; subst; eauto;
          break_status_cks_iffs;
          repeat match goal with H:_ /\ _ |- _ => destruct H end;
          subst; sem_det; try discriminate;
          repeat match goal with
                 | H:val_to_bool _ = _ |- _ => setoid_rewrite H; clear H
                 | Ht:negb _ = true, Hf:negb _ = false |- _ => rewrite Ht in Hf
                 end; eauto; discriminate.
      - (* Eite *)
        epose proof (var_inv_weaken _ (fun x=>Is_free_in_lexp x l) Inv _) as Inve.
        Unshelve. 2:now intuition.
        epose proof (var_inv_weaken _ (fun x=>Is_free_in_cexp x e1) Inv _) as Inv1.
        Unshelve. 2:now intuition.
        epose proof (var_inv_weaken _ (fun x=>Is_free_in_cexp x e2) Inv _) as Inv2.
        Unshelve. 2:now intuition.
        specialize (IHe1 _ WT1 WC1 ODe1 Inv1) as (v1 & IHe1).
        specialize (IHe2 _ WT2 WC2 ODe2 Inv2) as (v2 & IHe2).
        rewrite IHe1, IHe2.
        apply interp_cexp_instant_correct in IHe1.
        apply interp_cexp_instant_correct in IHe2.
        pose proof (interp_lexp_instant_good _ _ WTe WCe ODe Inve) as (v & He).
        rewrite He; apply interp_lexp_instant_correct in He.
        pose proof (sem_lexp_instant_clocked _ _ _ WCe Inve He) as (cks & Hck & HH).
        eapply sem_cexp_instant_clocked in IHe1 as (cks1 & Hck1 & HH1); eauto.
        eapply sem_cexp_instant_clocked in IHe2 as (cks2 & Hck2 & HH2); eauto.
        sem_det.
        destruct v; break_status_cks_iffs.
        + assert (v1 = absent) by intuition.
          assert (v2 = absent) by intuition.
          subst; eauto.
        + assert (v1 <> absent) as Hv1 by intuition.
          assert (v2 <> absent) as Hv2 by intuition.
          apply not_absent_present in Hv1 as (c1 & Hc1).
          apply not_absent_present in Hv2 as (c2 & Hc2).
          subst. apply sem_lexp_instant_wt_val in He; auto. rewrite H in He.
          apply wt_val_to_bool in He as (b & ->).
          destruct b; simpl; eauto.
      - (* Eexp *)
        eapply interp_lexp_instant_good; eauto.
        eapply var_inv_weaken; [eauto|now intuition].
    Qed.

    Corollary sem_cexp_instant_good:
      forall e ck,
        wt_cexp (idty vars) e ->
        wc_cexp (idck vars) e ck ->
        Ops_defined_in_cexp e ->
        var_inv (fun x => Is_free_in_cexp x e) ->
        exists v, sem_cexp_instant base R e v.
    Proof.
      setoid_rewrite interp_cexp_instant_correct.
      eauto using interp_cexp_instant_good.
    Qed.

    Lemma sem_cexp_instant_wt_val:
      forall e v,
        sem_cexp_instant base R e (present v) ->
        wt_cexp (idty vars) e ->
        var_inv (fun x => Is_free_in_cexp x e) ->
        wt_val v (typeofc e).
    Proof.
      induction e; intros v Sv WT Inv; simpl; inv WT.
      - (* Emerge *)
        inv Sv.
        now apply IHe1; auto; eapply var_inv_weaken; [eauto|intuition].
        match goal with H:typeofc _ = typeofc _ |- _ => rewrite H end.
        now apply IHe2; auto; eapply var_inv_weaken; [eauto|intuition].
      - (* Eite *)
        inv Sv.
        destruct b; match goal with H:present _ = present _ |- _ => inv H end.
        now apply IHe1; auto; eapply var_inv_weaken; [eauto|intuition].
        match goal with H:typeofc _ = typeofc _ |- _ => rewrite H end.
        now apply IHe2; auto; eapply var_inv_weaken; [eauto|intuition].
      - (* Eexp *)
        inv Sv. apply sem_lexp_instant_wt_val; auto.
        now eapply var_inv_weaken; [eauto|intuition].
    Qed.

    Lemma interp_laexp_instant_good:
      forall e ck,
        wt_lexp (idty vars) e ->
        wt_clock (idty vars) ck ->
        wc_lexp (idck vars) e ck ->
        wc_clock (idck vars )ck ->
        Ops_defined_in_lexp e ->
        var_inv (fun x => Is_free_in_lexp x e) ->
        var_inv (fun x => Is_free_in_clock x ck) ->
        exists v, interp_laexp_instant ck e = Some v.
    Proof.
      intros e ck WT WTc WC WCc OD Inv Invc.
      pose proof (interp_lexp_instant_good _ _ WT WC OD Inv) as (v & Iexp).
      unfold interp_laexp_instant, interp_annotated_instant.
      rewrite Iexp.
      apply interp_lexp_instant_correct in Iexp.
      eapply sem_lexp_instant_clocked in Iexp as (cks & Iclk & HH); eauto.
      apply interp_clock_instant_correct in Iclk as ->.
      destruct v; break_status_cks_iffs; eauto.
    Qed.

    Lemma interp_caexp_instant_good:
      forall e ck,
        wt_cexp (idty vars) e ->
        wt_clock (idty vars) ck ->
        wc_cexp (idck vars) e ck ->
        wc_clock (idck vars )ck ->
        Ops_defined_in_cexp e ->
        var_inv (fun x => Is_free_in_cexp x e) ->
        var_inv (fun x => Is_free_in_clock x ck) ->
        exists v, interp_caexp_instant ck e = Some v.
    Proof.
      intros e ck WT WTc WC WCc OD Inv Invc.
      pose proof (interp_cexp_instant_good _ _ WT WC OD Inv) as (v & Iexp).
      unfold interp_caexp_instant, interp_annotated_instant.
      rewrite Iexp.
      apply interp_cexp_instant_correct in Iexp.
      eapply sem_cexp_instant_clocked in Iexp as (cks & Iclk & HH); eauto.
      apply interp_clock_instant_correct in Iclk as ->.
      destruct v; break_status_cks_iffs; eauto.
    Qed.

    Lemma interp_lexps_instant_good:
      forall es cks,
        Forall (wt_lexp (idty vars)) es ->
        Forall2 (wc_lexp (idck vars)) es cks ->
        Forall Ops_defined_in_lexp es ->
        var_inv (fun x => Exists (Is_free_in_lexp x) es) ->
        exists vs, interp_lexps_instant es = Some vs.
    Proof.
      induction es as [|e es IH]. now exists [].
      intros cks WTs WCs ODs Invs.
      inversion_clear WTs as [|?? WT WTs'].
      inversion_clear WCs as [|???? WC WCs'].
      inversion_clear ODs as [|?? OD ODs'].
      assert (var_inv (fun x=>Is_free_in_lexp x e)) as Inv
          by (eapply var_inv_weaken; [eauto|now intuition]).
      assert (var_inv (fun x=>Exists (Is_free_in_lexp x) es)) as Invs'
          by (eapply (var_inv_weaken _ _ Invs); eauto).
      simpl.
      pose proof (interp_lexp_instant_good _ _ WT WC OD Inv) as (v & ->).
      specialize (IH _ WTs' WCs' ODs' Invs') as (vs & ->).
      eauto.
    Qed.

    Lemma sem_lexps_instant_wt_val:
      forall es vs,
        sem_lexps_instant base R es vs ->
        Forall (wt_lexp (idty vars)) es ->
        var_inv (fun x => Exists (Is_free_in_lexp x) es) ->
        Forall2 (fun e v => match v with
                            | present v => wt_val v (typeof e)
                            | absent => True
                            end) es vs.
    Proof.
      induction es as [|e es IH]. now inversion 1; subst; auto.
      intros vs Ses WTs Invs.
      inversion Ses as [|? v ?? Se Ses'].
      inversion_clear WTs as [|?? WT WTs']. subst.
      assert (var_inv (fun x => Is_free_in_lexp x e)) as Inv
          by (eapply var_inv_weaken; [eauto|now intuition]).
      assert (var_inv (fun x => Exists (Is_free_in_lexp x) es)) as Invs'
          by (eapply (var_inv_weaken _ _ Invs); eauto).
      constructor; auto. destruct v; auto.
      apply sem_lexp_instant_wt_val; auto.
    Qed.

  End InstantInterpreter.

End CEINTERPRETER.

Module CEInterpreterFun
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Op)
       (Import CESyn : CESYNTAX        Op)
       (Import Str   : STREAM          Op OpAux)
       (Import CESem : CESEMANTICS Ids Op OpAux CESyn Str)
       (Import CETyp : CETYPING    Ids Op       CESyn)
       (Import CEClk : CECLOCKING  Ids Op       CESyn)
       (Import CEFree: CEISFREE    Ids Op       CESyn)
       <: CEINTERPRETER Ids Op OpAux CESyn Str CESem CETyp CEClk CEFree.
  Include CEINTERPRETER Ids Op OpAux CESyn Str CESem CETyp CEClk CEFree.
End CEInterpreterFun.

