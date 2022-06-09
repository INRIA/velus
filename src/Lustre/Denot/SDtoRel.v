From Coq Require Import BinPos List.

From Velus Require Import Common Ident Environment Operators Clocks CoindStreams.
From Velus Require Import Lustre.StaticEnv Lustre.LSyntax Lustre.LOrdered Lustre.LSemantics Lustre.LTyping Lustre.LCausality.

From Velus Require Import Lustre.Denot.Cpo.

Close Scope equiv_scope. (* conflicting notation "==" *)
Import ListNotations.

Require Import Cpo_ext CommonDS SDfuns Denot Infty InftyProof.

Module Type SDTOREL
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Senv  : STATICENV     Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
       (Import Typ   : LTYPING       Ids Op OpAux Cks Senv Syn)
       (Import Caus  : LCAUSALITY    Ids Op OpAux Cks Senv Syn)
       (Import Lord  : LORDERED      Ids Op OpAux Cks Senv Syn)
       (Import Str   : COINDSTREAMS  Ids Op OpAux Cks)
       (Import Sem   : LSEMANTICS Ids Op OpAux Cks Senv Syn Lord Str)
       (Import Den   : LDENOT     Ids Op OpAux Cks Senv Syn Lord Str)
       (Import Inf   : LDENOTINF  Ids Op OpAux Cks Senv Syn Typ Caus Lord Str Den).

(* TODO: pour l'instant on se restreint aux cas suivants *)
Inductive restr_exp : exp -> Prop :=
| restr_Econst :
  forall c,
    restr_exp (Econst c)
| restr_Evar :
  forall x ann,
    restr_exp (Evar x ann)
| restr_Eunop :
  forall op e ann,
    restr_exp e ->
    restr_exp (Eunop op e ann)
| restr_Efby :
  forall e0s es anns,
    Forall restr_exp e0s ->
    Forall restr_exp es ->
    restr_exp (Efby e0s es anns)
(* | restr_Eapp : *)
(*   forall f es ers anns, *)
(*     Forall restr_exp es -> *)
(*     Forall restr_exp ers -> *)
(*     restr_exp (Eapp f es ers anns) *)
.

Inductive restr_block : block -> Prop :=
| restr_Beq :
  forall xs es,
    Forall restr_exp es ->
    restr_block (Beq (xs,es)).

Definition restr_node {PSyn prefs} (nd : @node PSyn prefs) : Prop :=
  restr_block nd.(n_block).


CoFixpoint DS_of_S {A} (s : Stream A) : DS A :=
  match s with
  | Streams.Cons a s => CONS a (DS_of_S s)
  end.

(** ** Correspondence of semantic predicate for streams functions *)

Definition sval_of_sampl : sampl value -> svalue :=
  fun v => match v with
        | pres v => present v
        | abs => absent
        | err e => absent
        end.

Definition S_of_DSv := S_of_DS sval_of_sampl.

Definition safe_val : sampl value -> Prop :=
  fun v => match v with
        | err _ => False
        | _ => True
        end.

Definition safe_DS : DS (sampl value) -> Prop := DSForall _ safe_val.

Lemma ok_const :
  forall c bs Hinf,
    S_of_DSv (sconst (Vscalar (sem_cconst c)) (DS_of_S bs)) Hinf ≡ const bs c.
Proof.
  intros.
  remember_st (S_of_DSv _ Hinf) as xs.
  remember_st (const bs c) as ys.
  revert_all.
  cofix Cof; intros * Eqx ? Eqy.
  destruct xs as [vx xs], ys as [vy ys], bs as [b bs].
  apply S_of_DS_Cons in Eqx as (x & tx & Hxs & Hxvx & itx & Eqx).
  setoid_rewrite unfold_Stream in Eqy.
  setoid_rewrite DS_inv in Hxs at 2; simpl in *.
  unfold sconst in *.
  rewrite MAP_map, ?map_eq_cons in Hxs.
  apply Con_eq_simpl in Hxs as [? Heq]; subst; simpl.
  inv Eqy; simpl in *; subst.
  constructor; simpl; cases.
  rewrite (ex_proj2 (S_of_DS_eq _ _ _ _ (symmetry Heq))) in Eqx; eauto.
Qed.

Lemma ok_fby1 :
  forall v (xs ys : DS (sampl value)),
    let rs := SDfuns.fby1 (Some v) xs ys in
    forall (xsi : infinite xs)
      (ysi : infinite ys)
      (rsi : infinite rs), (* obligé ? *)
      safe_DS xs ->
      safe_DS ys ->
      safe_DS rs ->
      fby1 v (S_of_DSv xs xsi) (S_of_DSv ys ysi) (S_of_DSv rs rsi).
Proof.
  intros.
  remember_st (S_of_DSv xs xsi) as xs'.
  remember_st (S_of_DSv ys ysi) as ys'.
  remember_st (S_of_DSv rs rsi) as rs'.
  revert_all.
  cofix Cof; intros * Sx Sy Sr ? Eqx ? Eqy ? Eqr.
  destruct xs' as [vx xs'], ys' as [vy ys'], rs' as [vr rs'].
  apply S_of_DS_Cons in Eqx as (x & tx & Hxs & Hxvx & itx & Eqx).
  apply S_of_DS_Cons in Eqy as (y & ty & Hys & Hyvy & ity & Eqy).
  apply S_of_DS_Cons in Eqr as (r & tr & Hrs & Hrvr & itr & Eqr).
  subst rs.
  rewrite Hxs, Hys, fby1_eq in Hrs.
  destruct x, y; simpl in *; subst.
  all: try apply Con_eq_simpl in Hrs as [? Heq]; subst; simpl.
  (* error cases *)
  all: rewrite Hxs, Hys in *.
  all: rewrite fby1_eq, ?fby1AP_eq in Sr, rsi.
  all: try (exfalso; inv Sx; inv Sy; assumption).
  all: apply DSForall_tl in Sx, Sy, Sr.
  2,3: rewrite DS_const_eq in Sr; inv Sr; now exfalso.
  all: constructor; rewrite fby1AP_eq in Heq.
  all: rewrite (ex_proj2 (S_of_DS_eq _ _ _ _ (symmetry Heq))) in Eqr; eauto.
Qed.

Lemma ok_fby :
  forall (xs ys : DS (sampl value)),
    let rs := SDfuns.fby xs ys in
    forall (xsi : infinite xs)
      (ysi : infinite ys)
      (rsi : infinite rs), (* obligé ?*)
      safe_DS xs ->
      safe_DS ys ->
      safe_DS rs ->
      fby (S_of_DSv xs xsi) (S_of_DSv ys ysi) (S_of_DSv rs rsi).
Proof.
  intros.
  remember_st (S_of_DSv xs xsi) as xs'.
  remember_st (S_of_DSv ys ysi) as ys'.
  remember_st (S_of_DSv rs rsi) as rs'.
  revert_all.
  cofix Cof; intros * Sx Sy Sr ? Eqx ? Eqy ? Eqr.
  destruct xs' as [vx xs'], ys' as [vy ys'], rs' as [vr rs'].
  apply S_of_DS_Cons in Eqx as (x & tx & Hxs & Hxvx & itx & Eqx).
  apply S_of_DS_Cons in Eqy as (y & ty & Hys & Hyvy & ity & Eqy).
  apply S_of_DS_Cons in Eqr as (r & tr & Hrs & Hrvr & itr & Eqr).
  subst rs.
  rewrite Hxs, Hys, fby_eq in Hrs.
  destruct x, y; simpl in *; subst.
  all: try apply Con_eq_simpl in Hrs as [? Heq]; subst; simpl.
  (* error cases *)
  all: rewrite Hxs, Hys in *.
  all: rewrite fby_eq, ?fbyA_eq, ?fby1AP_eq in Sr, rsi.
  all: try (exfalso; inv Sx; inv Sy; assumption).
  all: apply DSForall_tl in Sx, Sy, Sr.
  2,3: rewrite DS_const_eq in Sr; inv Sr; now exfalso.
  all: constructor; rewrite ?fbyA_eq, ?fby1AP_eq in Heq.
  all: rewrite (ex_proj2 (S_of_DS_eq _ _ _ _ (symmetry Heq))) in Eqr; eauto.
  rewrite <- Eqr, <- Eqx, <- Eqy.
  apply ok_fby1; auto.
Qed.


(** Général *)

(* TODO: err -> abs *)
Definition hist_of_env (env : DS_prod SI) (Hinf : all_infinite env) : Str.history :=
  fun x => Some (S_of_DSv (env x) (Hinf x)).


Lemma DS_of_S_inf : forall {A} (s : Stream A), infinite (DS_of_S s).
  cofix Cof.
  destruct s; constructor.
  - rewrite DS_inv; simpl; auto.
  - rewrite (DS_inv (DS_of_S (a ⋅ s))); simpl.
    rewrite rem_cons; auto.
Qed.

Definition sampl_of_sval : svalue -> sampl value :=
  fun v => match v with
        | present v => pres v
        | absent => abs
        end.

Definition env_of_list (l : list ident) (ss : list (Stream svalue)) : DS_prod SI :=
  fun x =>
    match assoc_ident x (combine l ss) with
    | Some s => DS_of_S (Streams.map sampl_of_sval s)
    | None => DS_const (err error_Ty)
    end.

Lemma env_of_list_inf :
  forall l ss, all_infinite (env_of_list l ss).
Proof.
  intros * x.
  unfold env_of_list.
  cases; auto using DS_of_S_inf, DS_const_inf.
Qed.

Definition list_of_hist (H : Str.history) (xs : list ident) : list (Stream svalue) :=
  CommonList.map_filter H xs.

Lemma list_of_hist_ok :
  forall env Henv l,
    let H := hist_of_env env Henv in
    Forall2 (sem_var H) l (list_of_hist H l).
Proof.
  induction l; simpl; constructor; auto.
  now econstructor; auto.
Qed.


(* TODO: move *)
Lemma denot_node_input :
  forall {PSyn prefs} (G : @global PSyn prefs)
    nd envI bs env x,
    wt_node G nd ->
    In x (List.map fst nd.(n_in)) ->
    denot_node nd envI bs env x = envI x.
Proof.
  intros * Hwt Hin.
  unfold denot_node, denot_block.
  destruct Hwt as (?&?&?& Hwt).
  cases. inv Hwt.
  eapply denot_equation_input; eauto.
Qed.

Lemma DS_of_S_of_DSv :
  forall s H,
    s ≡ S_of_DSv (DS_of_S (Streams.map sampl_of_sval s)) H.
Proof.
  intros.
  remember_st (S_of_DSv (DS_of_S (Streams.map sampl_of_sval s)) H) as t.
  revert_all.
  cofix Cof; intros s Hinf t Ht.
  destruct s, t.
  apply S_of_DS_Cons in Ht as (?&?& Hc &?&?& Ht).
  setoid_rewrite unfold_Stream in Hc.
  setoid_rewrite DS_inv in Hc.
  apply Con_eq_simpl in Hc as [].
  constructor; simpl.
  - subst; destruct s; auto.
  - unshelve eapply Cof.
    { setoid_rewrite unfold_Stream in Hinf.
      setoid_rewrite DS_inv in Hinf.
      simpl in Hinf; eauto using cons_infinite. }
    rewrite <- Ht.
    now apply _S_of_DS_eq.
Qed.

(* TODO: move *)
Lemma map_filter_Some :
  forall {A B} (f : A -> B) l,
    CommonList.map_filter (fun x => Some (f x)) l = List.map f l.
Proof.
  induction l; simpl; auto.
Qed.

(* TODO: move *)
Lemma map_EqSts_ext_in :
  forall (A B : Type)(f g:A->Stream B) l, (forall a, In a l -> f a ≡ g a) -> EqSts (List.map f l) (List.map g l).
Proof.
  intros A B f g l; induction l as [|? ? IHl]; simpl; constructor; auto.
  apply IHl; auto.
Qed.

(* TODO: move *)
Lemma assoc_ident_cons2 :
  forall {A} x y a (l : list (ident * A)),
    x <> y ->
    assoc_ident x ((y,a) :: l) = assoc_ident x l.
Proof.
  intros.
  unfold assoc_ident.
  simpl.
  destruct (ident_eqb y x) eqn:?; auto.
  rewrite ident_eqb_eq in *.
  congruence.
Qed.

(* TODO: move *)
Lemma assoc_ident_cons1 :
  forall {A} x a (l : list (ident * A)),
    assoc_ident x ((x,a) :: l) = Some a.
Proof.
  intros.
  unfold assoc_ident.
  simpl.
  now rewrite ident_eqb_refl.
Qed.

(* TODO: move *)
Lemma list_of_hist_of_list :
  forall l ss H,
    NoDup l ->
    length l = length ss ->
    EqSts (list_of_hist (hist_of_env (env_of_list l ss) H) l) ss.
Proof.
  unfold list_of_hist, hist_of_env.
  intros * Hd Hl.
  rewrite map_filter_Some.
  revert dependent ss.
  induction l; destruct ss; simpl; intros; try congruence; constructor.
  - setoid_rewrite _S_of_DS_eq.
    2: unfold env_of_list; simpl; rewrite assoc_ident_cons1; reflexivity.
    symmetry. apply DS_of_S_of_DSv.
  - inv Hd.
    erewrite map_EqSts_ext_in.
    apply IHl; auto.
    intros x Hx.
    apply _S_of_DS_eq.
    unfold env_of_list; simpl.
    rewrite assoc_ident_cons2; auto.
    intro. subst; auto.
 Unshelve. all:eauto using env_of_list_inf, DS_of_S_inf.
Qed.

(* TODO: move *)
Lemma env_of_list_ok :
  forall l ss HH,
    NoDup l ->
    length l = length ss ->
    Forall2 (sem_var (hist_of_env (env_of_list l ss) HH)) l ss.
Proof.
  intros * Hd Hl.
  pose proof (list_of_hist_of_list _ _ HH Hd Hl) as Hss.
  (* TODO: setoid déconne à plein régime, là! *)
  rewrite Forall2_EqSt_iff. 3: now rewrite <- Hss.
  2:{ intros ??????. subst.
      split; apply sem_var_morph; auto; try reflexivity.
      now symmetry. }
  eapply Forall2_impl_In; eauto using list_of_hist_ok.
Qed.

(* TODO: move *)
Import FunctionalEnvironment.FEnv.

Lemma _hist_of_env_eq :
  forall env Hinf env' Hinf',
    env == env' ->
    Equiv (EqSt (A:=svalue)) (hist_of_env env Hinf) (hist_of_env env' Hinf').
Proof.
  intros * Heq.
  unfold hist_of_env.
  constructor.
  apply _S_of_DS_eq.
  now rewrite <- PROJ_simpl, Heq, PROJ_simpl.
Qed.

(* TODO: move *)
Lemma all_infinite_Oeq_compat :
  forall env env',
    all_infinite env ->
    env == env' ->
    all_infinite env'.
Proof.
  unfold all_infinite.
  intros * Hi Heq x.
  now rewrite <- PROJ_simpl, <- Heq, PROJ_simpl.
Qed.

(* utilisation : edestruct (hist_of_env_eq env Hinf) as [Hinf' ->]. *)
Lemma hist_of_env_eq :
  forall env Hinf env',
    env == env' ->
    exists Hinf',
      Equiv (EqSt (A:=svalue)) (hist_of_env env Hinf) (hist_of_env env' Hinf').
Proof.
  intros * Heq.
  esplit.
  unshelve (rewrite _hist_of_env_eq; eauto; reflexivity).
  eapply all_infinite_Oeq_compat; eauto.
Qed.

(* TODO: move *)
Add Parametric Morphism : (@pair Str.history Str.history) with signature
        Equiv (EqSt (A:=svalue)) ==> Equiv (EqSt (A:=svalue)) ==> history_equiv
          as history_equiv_morph.
Proof.
  intros ??????.
  split; auto.
Qed.

Lemma nrem_inf_iff :
  forall {A} (s : DS A), (forall n, is_cons (nrem n s)) <-> infinite s.
Proof.
  split; auto using nrem_inf, inf_nrem.
Qed.

Lemma sconst_inf :
  forall {A} (c : A) bs,
    infinite bs ->
    infinite (sconst c bs).
Proof.
  setoid_rewrite <- nrem_inf_iff.
  intros.
  auto using is_consn_sconst.
Qed.

Lemma sunop_inf :
  forall {A B} (op : A -> option B) s,
    infinite s ->
    infinite (sunop op s).
Proof.
  setoid_rewrite <- nrem_inf_iff.
  intros.
  auto using is_consn_sunop.
Qed.

Lemma fby_inf :
  forall {A} (xs ys : DS (sampl A)),
    infinite xs ->
    infinite ys ->
    infinite (SDfuns.fby xs ys).
Proof.
  setoid_rewrite <- nrem_inf_iff.
  intros.
  auto using is_consn_fby.
Qed.

Lemma forall_nprod_const :
  forall (P : DS (sampl value) -> Prop) c n,
    P (DS_const c) ->
    forall_nprod P (nprod_const c n).
Proof.
  intros.
  apply forall_nprod_k; intros.
  now rewrite get_nth_const.
Qed.

  (* TODO: à mettre à la fin de Infty *)
Lemma infinite_exp :
  forall ins envI bs env,
    infinite bs ->
    all_infinite envI ->
    all_infinite env ->
    forall e,
    forall_nprod (@infinite _) (denot_exp ins e envI bs env).
Proof.
  intros * Hins Hinf Hbs.
  induction e using exp_ind2; intros; simpl; setoid_rewrite denot_exp_eq.
  (* cas restreints : *)
  all: try (simpl; now auto using forall_nprod_const, DS_const_inf).
  - (* const *)
    apply sconst_inf; auto.
  - (* var *)
    unfold all_infinite in *.
    cases_eqn HH; rewrite ?mem_ident_spec in HH; eauto.
  - (* unop *)
    assert (forall_nprod (@infinite _) (denot_exp ins e envI bs env0)) as He by eauto.
    revert He.
    generalize (denot_exp ins e envI bs env0).
    generalize (numstreams e).
    intros.
    cases; simpl; auto using sunop_inf, DS_const_inf.
  - (* fby *)
    assert (forall_nprod (@infinite _) (denot_exps ins e0s envI bs env0)) as He0s.
    { induction e0s; simpl_Forall; auto.
      setoid_rewrite denot_exps_eq; auto using forall_nprod_app. }
    assert (forall_nprod (@infinite _) (denot_exps ins es envI bs env0)) as Hes.
    { induction es; simpl_Forall; auto.
      setoid_rewrite denot_exps_eq; auto using forall_nprod_app. }
    revert He0s Hes.
    generalize (denot_exps ins e0s envI bs env0).
    generalize (denot_exps ins es envI bs env0).
    generalize (list_sum (List.map numstreams e0s)).
    generalize (list_sum (List.map numstreams es)).
    intros; unfold eq_rect_r, eq_rect, eq_sym.
    cases; subst; auto using forall_nprod_const, DS_const_inf, forall_nprod_lift2, fby_inf.
Qed.

Corollary infinite_exps :
  forall ins envI bs env,
    infinite bs ->
    all_infinite envI ->
    all_infinite env ->
    forall es,
    forall_nprod (@infinite _) (denot_exps ins es envI bs env).
Proof.
  induction es; simpl; auto.
  intros; simpl_Forall.
  setoid_rewrite denot_exps_eq.
  auto using forall_nprod_app, infinite_exp.
Qed.

Definition Ss_of_nprod {n} (np : nprod n) (Hinf : forall_nprod (@infinite _) np) : list (Stream svalue).
  induction n as [|[]].
  - exact [].
  - exact [S_of_DSv np Hinf].
  - exact (S_of_DSv (fst np) (proj1 Hinf) :: IHn (snd np) (proj2 Hinf)).
Defined.

(* TODO: move *)
Lemma S_of_DSv_eq :
  forall (s : DS (sampl value)) Hs t (Heq : s == t),
  exists Ht,
    S_of_DSv s Hs ≡ S_of_DSv t Ht.
Proof.
  esplit.
  apply (__S_of_DS_eq _ _ Hs _ Heq).
Qed.

Lemma ok_sem_exp :
  forall {PSyn prefs} (G : @global PSyn prefs),
  forall Γ ins equ envI bs Inf e Infe,
    wt_equation G Γ equ ->
    restr_exp e ->
    (* TODO: pourquoi denot_equation plutôt que node ? *)
    let env := (FIXP (DS_prod SI) (denot_equation ins equ envI (DS_of_S bs))) in
    sem_exp G (hist_of_env env Inf, empty _) bs e
      (Ss_of_nprod (denot_exp ins e envI (DS_of_S bs) env) Infe).
Proof.
  induction e using exp_ind2; intros * Hwt Hr; inv Hr; simpl.
  - (* const *)
    constructor.
    edestruct (S_of_DSv_eq _ Infe) as [Infe' ->].
    { rewrite denot_exp_eq. reflexivity. }
    apply ok_const.
  - (* var *)
    constructor; simpl.
    econstructor; unfold hist_of_env; eauto.
    apply _S_of_DS_eq.
    setoid_rewrite denot_exp_eq.
    cases_eqn HH; apply mem_ident_spec in HH.
    setoid_rewrite <- PROJ_simpl at 2.
    rewrite FIXP_eq, PROJ_simpl.
    erewrite denot_equation_input; eauto.
  - (* binop, TODO *)
    
Qed.


(* TODO: énoncer plutôt exist os, .. et faire ça dans la preuve ? *)
Lemma ok_node :
  forall {PSyn prefs} (G : @global PSyn prefs),
  forall (HasCausInj : forall (Γ : static_env) (x cx : ident), HasCaus Γ x cx -> x = cx),
  forall f (nd : node) ss,
    length nd.(n_in) = length ss ->
  forall (Hn : find_node f G = Some nd)
    (Hwt : wt_node G nd)
    (Hnc : node_causal nd)
    (Hre : restr_node nd)
  ,
    let envI := env_of_list (List.map fst nd.(n_in)) ss in
    let infI := env_of_list_inf (List.map fst nd.(n_in)) ss in
    let bs := DS_of_S (clocks_of ss) in
    let bsi := DS_of_S_inf (clocks_of ss) in
    let env := FIXP (DS_prod SI) (denot_node nd envI bs) in
    let infO := denot_inf G HasCausInj nd envI bs Hwt Hnc bsi infI in
    let H := hist_of_env env infO in
    let os := list_of_hist H (List.map fst nd.(n_out)) in
    sem_node G f ss os.
Proof.
  intros * Hl. intros.
  eapply Snode with (H := H); eauto using list_of_hist_ok.
  - subst H env0.
    pose proof nd.(n_nodup) as [ND].
    apply fst_NoDupMembers in ND.
    rewrite map_app in ND.
    eapply Forall2_impl_In, env_of_list_ok; eauto using NoDup_app_l.
    2: unfold idents; rewrite map_length; auto.
    intros x s Hx Hs Hv.
    inversion_clear Hv as [???? Hh Hu].
    unfold hist_of_env in *. inv Hh.
    rewrite Hu.
    eapply sem_var_intro, _S_of_DS_eq; auto.
    setoid_rewrite <- PROJ_simpl at 2.
    erewrite FIXP_eq, PROJ_simpl, denot_node_input; eauto.
    Unshelve. apply env_of_list_inf.
  - subst H.
    inversion Hre as [?? Hr Hb].
    edestruct (hist_of_env_eq env0 infO) as [Inf' ->].
    { subst env0. unfold denot_node, denot_block. rewrite <- Hb. reflexivity. }
    constructor.
    econstructor.
    + erewrite Forall2_map_2, <- Forall2_same, Forall_forall.
      intros e Hin.
      pose proof (Forall_In _ _ _ Hr Hin).
      subst bs.
      apply sem_exp_ok; auto.
    + 
    (* edestruct (hist_of_env_eq env0 infO) as [Inf' ->]. *)
    (* { subst env0. unfold denot_node, denot_block. rewrite <- Hb, FIXP_eq. reflexivity. } *)
    (* (* TODO: lemme *) *)
    (* pose (sss := List.map (fun e => *)
    (*                          Ss_of_nprod (denot_exp (List.map fst (n_in nd)) e envI bs env0) *)
    (*                            (infinite_exp _ _ _ _ bsi infI infO e)) es). *)
    (* constructor 1 with sss. *)
    (* + subst sss. *)
    (*   rewrite Forall2_map_2, <- Forall2_same. *)
    (*   remember (infinite_exp _ _ _ _ _ _ _) as HH. *)
Qed.



Definition nprod_inf n (np : nprod n) : Prop.
  induction n as [|[]]; simpl in *.
  - exact (infinite np).
  - exact (infinite np).
  - exact (infinite (fst np) /\ IHn (snd np)).
Defined.

Fixpoint nprod_inf' (n : nat) (np : nprod n) {struct n} : Prop :=
   match n as n return nprod n -> Prop with
   | 0 => fun np : nprod O => infinite np
   | S n0 =>
       match n0 as n0 return nprod (S n0) -> Prop with
       | O => fun np : nprod 1 => infinite np
       | S _ => fun np : nprod _ => infinite (fst np)
                                          /\ nprod_inf' n0 (snd np)
       end
   (* | 1 => fun np : nprod 1 => infinite np *)
   (* | S (S n) => fun np : nprod (S (S n)) => infinite (fst np) *)
   (*                              /\ nprod_inf' (S n) (snd np) *)
   (* | S n1 => *)
   (*     (fun (n2 : nat) (IHn : nprod (S n2) -> Prop) (np0 : nprod (S (S n2))) => *)
   (*      infinite (fst np0) /\ IHn (snd np0) : Prop) n1 *)
   (* end) n np *)
           (*   : forall n : nat, nprod n -> Prop *)
   end np.



Definition list_of_nprod n np : nprod_inf n np -> list (Stream svalue).
  induction n as [|[]]; simpl; intro Hinf.
  - exact ([S_of_DSv np Hinf]).
  - exact ([S_of_DSv np Hinf]).
  - exact ((S_of_DSv (fst np) (proj1 Hinf)) :: IHn _ (proj2 Hinf)).
Defined.

(* en principe on devrait pouvoir prouver : *)
Lemma denot_equation_infinite :
  forall (e : equation) bs,
    (* + hypothèse de causalité *)
    let env := FIXP _ (denot_equation e <___> bs) in
    all_infinite (fst e) env
    /\ Forall (fun e => nprod_inf _ (denot_exp e env bs)) (snd e).
Proof.
  (* la deuxième partie découle facilement de la première *)
Admitted.

Definition streams_of_env vars env (Hinf : all_infinite vars env) : list (ident * Stream svalue).
  (* refine (List.map (fun x => (x, S_of_DSv (env x) (Hinf x _))) vars). *)
  induction vars as [| x vars].
  - exact [].
  - apply List.cons.
    + exact (x, S_of_DSv (env x) (Hinf x (or_introl eq_refl))).
    + apply IHvars. firstorder.
Defined.

Definition hist_of_env vars env Hinf : Str.history :=
  Env.from_list (streams_of_env vars env Hinf).

Definition ok_var :
  forall vars env Hinf x (Hin : In x vars),
    sem_var (hist_of_env vars env Hinf) x (S_of_DSv (env x) (Hinf x Hin)).
Proof.
  intros.
  econstructor. (* 2: reflexivity. *)
  apply Env.find_2, Env.find_In_from_list.
Abort.



Definition list_of_nprod' n (np : nprod n) : list (DS (sampl value)).
  revert dependent n.
  fix f 1; intros.
  destruct n as [|n].
  - exact [].
  - specialize (f n).
    destruct n.
    + exact [np].
    + exact (f (snd np)).
Defined.

(* Fixpoint list_of_nprod n (np : nprod n) {struct n} : list (DS (sampl value)) := *)
(*   match n, np with *)
(*   | O, _ => [] *)
(*   | S O, s => [s] *)
(*   | S n, (s,t) => s :: list_of_nprod n t *)
(*   end. *)

Lemma test :
  forall PSyn prefs (G : @global PSyn prefs),
  forall (e : equation) bs (bsi : infinite bs),
    let env := FIXP _ (denot_equation e <___> bs) in
    forall Henv : all_infinite (fst e) env,
      (* TODO: all_safe *)
    let H := hist_of_env (fst e) env Henv in
    sem_equation G (H, Env.empty _) (S_of_DS id bs bsi) e.
Proof.
  intros.
  destruct e as (xs,es).
  (* pose (ss := denot_exps es env0 bs). *)
  pose (ss := List.map (fun e => list_of_nprod' _ (denot_exp e env0 bs)) es).
  econstructor; simpl in *.
  Search denot_node.
Qed.



End SDTOREL.
