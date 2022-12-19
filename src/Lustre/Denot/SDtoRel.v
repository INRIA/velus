From Coq Require Import BinPos List Permutation Morphisms.

From Velus Require Import Common Ident Environment Operators Clocks CoindStreams.
From Velus Require Import Lustre.StaticEnv Lustre.LSyntax Lustre.LOrdered Lustre.LSemantics Lustre.LTyping Lustre.LClocking Lustre.LCausality.

From Velus Require Import FunctionalEnvironment.
From Velus Require Import Lustre.Denot.Cpo.

Close Scope equiv_scope. (* conflicting notation "==" *)

Require Import Cpo_ext CommonDS SDfuns Denot Infty InftyProof Safe CommonList2.

Import List ListNotations.

Module Type SDTOREL
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Senv  : STATICENV     Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
       (Import Typ   : LTYPING       Ids Op OpAux Cks Senv Syn)
       (Import Cl    : LCLOCKING     Ids Op OpAux Cks Senv Syn)
       (Import Caus  : LCAUSALITY    Ids Op OpAux Cks Senv Syn)
       (Import Lord  : LORDERED      Ids Op OpAux Cks Senv Syn)
       (Import Str   : COINDSTREAMS  Ids Op OpAux Cks)
       (Import Sem   : LSEMANTICS Ids Op OpAux Cks Senv Syn Lord Str)
       (Import Den   : LDENOT     Ids Op OpAux Cks Senv Syn Lord)
       (Import Inf   : LDENOTINF  Ids Op OpAux Cks Senv Syn Typ Caus Lord Den)
       (Import Safe  : LDENOTSAFE Ids Op OpAux Cks Senv Syn Typ Cl Lord Den).

  (* TODO: trouver un moyen pour ne pas devoir ajouter ça *)
Global Add Parametric Morphism k t : (fun s => when k s t)
       with signature (@EqSt _) ==> (@EqSt _) ==> Basics.impl
         as  when_morph2.
Proof.
  intros ?? HH ?? -> ?.
  now rewrite <- HH.
Qed.

(* TODO: move to LSyntax? *)
Lemma n_NoDup_out :
  forall (n : node),
    NoDup (idents (n_out n)).
Proof.
  intro.
  destruct (n.(n_nodup)) as [ND _].
  apply fst_NoDupMembers in ND.
  rewrite map_app in ND.
  now apply NoDup_app_r in ND.
Qed.

(* TODO: move to LSyntax? *)
Lemma n_NoDup_in :
  forall (n : node),
    NoDup (idents (n_in n)).
Proof.
  intro.
  destruct (n.(n_nodup)) as [ND _].
  apply fst_NoDupMembers in ND.
  rewrite map_app in ND.
  now apply NoDup_app_l in ND.
Qed.

(* TODO: à terme, mettre dans LSemantics *)
Section Sem_absent.

(* TODO: move *)
Section FromLClockedSemantics.
Lemma clocks_of_false :
  forall ss,
    clocks_of (List.map (fun _ : Stream svalue => Streams.const absent) ss) ≡ Streams.const false.
Proof.
  intros *.
  eapply ntheq_eqst. intros n.
  rewrite clocks_of_nth, const_nth.
  induction ss; simpl; auto.
  rewrite const_nth; simpl; auto.
Qed.
Lemma clocks_of_false2 :
  forall n,
    clocks_of (repeat (Streams.const absent) n) ≡ Streams.const false.
Proof.
  intros.
  eapply ntheq_eqst. intro k.
  rewrite clocks_of_nth, const_nth.
  induction n; simpl; auto.
  rewrite const_nth; simpl; auto.
Qed.
Lemma fby_absent {A}:
  @fby A (Streams.const absent) (Streams.const absent) (Streams.const absent).
Proof.
  cofix CoFix.
  rewrite CommonStreams.const_Cons. constructor; auto.
Qed.
(* à adapter de ClockedSem.sem_node_ck_cons' *)
Corollary sem_node_cons' :
    forall (nd : node) nds types externs f xs ys,
      Ordered_nodes (Global types externs (nd::nds))
      -> sem_node (Global types externs nds) f xs ys
      -> nd.(n_name) <> f
      -> sem_node (Global types externs (nd::nds)) f xs ys.
Proof.
Admitted.

(* à adapter de ClockedSem.sem_block_ck_cons' *)
Lemma sem_block_cons' :
  forall (nd : node) nds types externs bck Hi bk,
    Ordered_nodes (Global types externs (nd::nds))
    -> sem_block (Global types externs nds) Hi bk bck
    -> ~Is_node_in_block nd.(n_name) bck
    -> sem_block (Global types externs (nd::nds)) Hi bk bck.
Proof.
Admitted.

End FromLClockedSemantics.

(* TODO: move? *)
Global Add Parametric Morphism {A} : (@repeat (Stream A))
    with signature (@EqSt A) ==> (@eq nat) ==> (@EqSts A)
      as repeat_morph.
Proof.
  intros * Heq n.
  induction n; simpl; constructor; eauto.
Qed.

(* Hypothèse d'induction sur les nœuds du programme *)
Definition sem_global_abs (G : global) :=
  forall f n,
    find_node f G = Some n ->
    let ss := repeat (Streams.const absent) (length (n_in n)) in
    let os := repeat (Streams.const absent) (length (n_out n)) in
    sem_node G f ss os.

Lemma sem_exp_absent :
  forall (G : global) Γ,
    sem_global_abs G ->
    forall e,
    restr_exp e ->
    wt_exp G Γ e ->
    let H := (fun _ => Some (Streams.const absent), FEnv.empty (Stream svalue)) in
    sem_exp G H (Streams.const false) e (repeat (Streams.const absent) (numstreams e)).
Proof.
  intros * HG.
  induction e using exp_ind2; intros Hr Hwt ?; inv Hr; inv Hwt.
  - (* Econst *)
    constructor.
    apply ntheq_eqst; intro.
    now rewrite const_nth', 2 const_nth.
  - (* Evar *)
    constructor; econstructor; now eauto.
  - (* Eunop *)
    take (typeof e = _) and rewrite <- length_typeof_numstreams, it in IHe.
    simpl in *; econstructor; eauto using Is_node_in_exp.
    eapply lift1_spec; intros.
    left. split; apply const_nth.
  - (* Efby *)
    apply Sfby with
      (s0ss := List.map (fun e => repeat (Streams.const absent) (numstreams e)) e0s)
      (sss := List.map (fun e => repeat (Streams.const absent) (numstreams e)) es); simpl.
    + clear H9 H10 H11.
      induction e0s; simpl in *; constructor; inv H; inv H4; inv H7; eauto.
    + clear H9 H10 H11.
      induction es; simpl in *; inv H0; inv H6; inv H8; constructor; auto.
    + rewrite <- 2 flat_map_concat_map, 2 flat_map_repeat.
      rewrite <- 2 annots_numstreams, <- 2 length_typesof_annots.
      take (typesof es = _) and rewrite it.
      take (typesof e0s = _) and rewrite it.
      rewrite map_length.
      apply Forall3_repeat, fby_absent.
  - (* Ewhen *)
    apply Swhen with
      (s := Streams.const absent)
      (ss := List.map (fun e => repeat (Streams.const absent) (numstreams e)) es); simpl.
    + rewrite Forall2_map_2. apply Forall2_same.
      apply Forall_impl_inside with (P := restr_exp) in H; auto.
      apply Forall_impl_inside with (P := wt_exp _ _) in H; auto.
    + econstructor; now eauto.
    + rewrite <- flat_map_concat_map, flat_map_repeat.
      rewrite <- annots_numstreams, <- length_typesof_annots.
      apply Forall2_repeat.
      apply when_spec. intros n.
      left. repeat split; apply const_nth.
  - (* Eapp *)
    eapply Sapp with
      (ss := List.map (fun e => repeat (Streams.const absent) (numstreams e)) es);
      simpl; eauto using bools_ofs_empty.
    + rewrite Forall2_map_2. apply Forall2_same.
      apply Forall_impl_inside with (P := restr_exp) in H; auto.
      apply Forall_impl_inside with (P := wt_exp _ _) in H; auto.
    + intro k.
      rewrite <- flat_map_concat_map, flat_map_repeat, 2 map_repeat.
      rewrite <- annots_numstreams, <- length_typesof_annots.
      eapply sem_node_morph in HG; eauto.
      (* in *)
      take (Forall2 _ _ (n_in n)) and apply Forall2_length in it as ->.
      destruct k;
        [now setoid_rewrite mask_false_0 | now setoid_rewrite mask_false_S].
      (* out *)
      take (Forall2 _ _ (n_out n)) and apply Forall2_length in it.
      setoid_rewrite it.
      destruct k;
        [now setoid_rewrite mask_false_0 | now setoid_rewrite mask_false_S].
Qed.

(* TODO: comprendre pourquoi on a besoin de ces deux cons-là *)
Global Instance Forall2_Proper A B :
  Proper ((eq ==> eq ==> Basics.impl) ==> eq ==> eq ==> Basics.impl)
    (Forall2(A:=A) (B:=B)).
Proof.
  repeat intro; subst.
  induction H2; constructor; auto.
  eapply H; eauto.
Qed.
Global Instance sem_exp_Proper (G : global) H :
  Proper (@EqSt bool ==> (@eq exp  ==> eq ==> Basics.impl))
    (sem_exp G H).
Proof.
  intros ?? Heq  ??? ??? Hsem; subst.
  now rewrite <- Heq.
Qed.

(***************************************
 avec Ordered_nodes ça semble impossible car on ne peut pas avoir
 wt_node à chaque fois
Voir avec Basile :
 pourquoi wt_global -> Ordered_nodes ?
On voudrait un wt_global plus faible mais plus
 facile à manipuler (pas de Forall' !!)
on réserve le Ordered_nodes pour les raisonnements inductifs
 *)
Lemma sem_global_absent :
  forall (G : global),
    restr_global G ->
    wt_global G ->
    sem_global_abs G.
Proof.
  intros [tys exts nds] Hr Hwt.
  induction nds as [| n' nds]; intros f n Hfind ??. inv Hfind.
  apply wt_global_wl_global in Hwt as Hord.
  apply wl_global_Ordered_nodes in Hord.
  destruct (ident_eq_dec f (n_name n')); subst.
  rewrite find_node_now in Hfind; auto; inv Hfind.
  { (* TODO: en extraire un lemme, mais comment ? *)
  subst ss os.
  eapply Snode with (H := fun _ => Some (Streams.const absent));
    eauto using find_node_now.
  + (* ins *)
    apply Forall2_forall2; unfold idents.
    rewrite map_length, repeat_length.
    split; intros; subst; auto.
    econstructor; eauto.
    rewrite nth_repeat_in; now auto.
  + (* outs *)
    apply Forall2_forall2; unfold idents.
    rewrite map_length, repeat_length.
    split; intros; subst; auto.
    econstructor; eauto.
    rewrite nth_repeat_in; now auto.
  + (* équation *)
    apply sem_block_cons'; eauto using find_node_not_Is_node_in, find_node_now.
    inv Hr. take (restr_node _) and inv it.
    apply wt_global_cons in Hwt as Hwt'.
    apply wt_global_uncons in Hwt as (?&?&?& Hwt).
    rewrite <- H in Hwt. inv Hwt.
    take (wt_equation _ _ _) and inv it.
    constructor.
    apply Seq with
      (ss := List.map (fun e => repeat (Streams.const absent) (numstreams e)) es); simpl.
    (* expressions *)
    rewrite clocks_of_false2.
    match goal with H:Forall (wt_exp _ ?Γ) _ |- _=> revert H; generalize Γ end.
    intros; clear dependent n.
    induction es; simpl_Forall; constructor; eauto.
    eapply sem_exp_absent; now eauto.
    (* variables *)
    assert (length xs = list_sum (List.map numstreams es)) as Hl.
    { rewrite <- annots_numstreams, <- length_typesof_annots.
      eauto using Forall2_length. }
    clear - Hl. revert dependent xs.
    induction es; simpl; intros.
    * destruct xs; simpl in *; auto; congruence.
    * apply length_app_decomp in Hl as (xs1 & xs2 & ? & Hl1 & Hl2); subst.
      apply Forall2_app; auto.
      rewrite <- Hl1; clear.
      induction xs1; simpl; constructor; auto.
      now econstructor.
  }
  rewrite find_node_other in Hfind; auto.
  inv Hr; apply wt_global_cons in Hwt.
  unfold sem_global_abs in IHnds.
  apply sem_node_cons'; eauto.
Qed.

End Sem_absent.



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

(* TODO: move *)
Lemma S_of_DSv_eq :
  forall (s : DS (sampl value)) Hs t (Heq : s == t),
  exists Ht,
    S_of_DSv s Hs ≡ S_of_DSv t Ht.
Proof.
  esplit.
  apply (__S_of_DS_eq _ _ Hs _ Heq).
Qed.

(** In the lext lemmas we use the method of coinduction loading from
    "Circular coinduction in Coq using bisimulation-up-to techniques" by
    Endrullis, Hendriks and Bodin.
    Their idea is to push computation/rewriting in the arguments of the
    coinductive predicate instead of performing it at top-level, which
    would breaks Coq guardedness condition. Thus, instead of proving
      forall xs ys, P xs ys
    we prove
      forall xs ys, forall xs' ys', xs ≡ xs' -> ys ≡ ys' -> P xs' ys'
 *)

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
  rewrite MAP_map, Cpo_streams_type.map_eq_cons in Hxs.
  apply Con_eq_simpl in Hxs as [? Heq]; subst; simpl.
  inv Eqy; simpl in *; subst.
  constructor; simpl; cases.
  rewrite (ex_proj2 (S_of_DS_eq _ _ _ _ (symmetry Heq))) in Eqx; eauto.
Qed.

Lemma ok_unop :
  forall op ty (xs : DS (sampl value)),
    let rs := sunop (fun v => sem_unop op v ty) xs in
    forall (xsi : infinite xs)
      (rsi : infinite rs),
      safe_DS rs ->
      lift1 op ty (S_of_DSv xs xsi) (S_of_DSv rs rsi).
Proof.
  intros.
  remember_st (S_of_DSv xs xsi) as xs'.
  remember_st (S_of_DSv rs rsi) as rs'.
  revert_all.
  cofix Cof; intros * Sr ? Eqx ? Eqr.
  destruct xs' as [vx xs'], rs' as [vr rs'].
  apply S_of_DS_Cons in Eqx as (x & tx & Hxs & Hxvx & itx & Eqx).
  apply S_of_DS_Cons in Eqr as (r & tr & Hrs & Hrvr & itr & Eqr).
  subst rs.
  rewrite Hxs, sunop_eq in Hrs, Sr.
  cases_eqn HH; simpl; try now inv Sr.
  all: apply Con_eq_simpl in Hrs as [? Heq]; subst; simpl.
  all: constructor; eauto.
  all: apply DSForall_tl in Sr.
  all: rewrite (ex_proj2 (S_of_DS_eq _ _ _ _ (symmetry Heq))) in Eqr; eauto.
Qed.

Lemma ok_fby1 :
  forall v (xs ys : DS (sampl value)),
    let rs := SDfuns.fby1 (Some v) xs ys in
    forall (xsi : infinite xs)
      (ysi : infinite ys)
      (rsi : infinite rs), (* obligé ? *)
      safe_DS rs ->
      fby1 v (S_of_DSv xs xsi) (S_of_DSv ys ysi) (S_of_DSv rs rsi).
Proof.
  intros.
  remember_st (S_of_DSv xs xsi) as xs'.
  remember_st (S_of_DSv ys ysi) as ys'.
  remember_st (S_of_DSv rs rsi) as rs'.
  revert_all.
  cofix Cof; intros * Sr ? Eqx ? Eqy ? Eqr.
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
  all: repeat apply DSForall_tl in Sr.
  all: try (rewrite DS_const_eq in Sr; inv Sr; now exfalso).
  all: constructor; rewrite fby1AP_eq in Heq.
  all: rewrite (ex_proj2 (S_of_DS_eq _ _ _ _ (symmetry Heq))) in Eqr; eauto.
Qed.

Lemma ok_fby :
  forall (xs ys : DS (sampl value)),
    let rs := SDfuns.fby xs ys in
    forall (xsi : infinite xs)
      (ysi : infinite ys)
      (rsi : infinite rs), (* obligé ?*)
      safe_DS rs ->
      fby (S_of_DSv xs xsi) (S_of_DSv ys ysi) (S_of_DSv rs rsi).
Proof.
  intros.
  remember_st (S_of_DSv xs xsi) as xs'.
  remember_st (S_of_DSv ys ysi) as ys'.
  remember_st (S_of_DSv rs rsi) as rs'.
  revert_all.
  cofix Cof; intros * Sr ? Eqx ? Eqy ? Eqr.
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
  all: repeat apply DSForall_tl in Sr.
  all: try (rewrite DS_const_eq in Sr; inv Sr; now exfalso).
  all: constructor; rewrite ?fbyA_eq, ?fby1AP_eq in Heq.
  all: rewrite (ex_proj2 (S_of_DS_eq _ _ _ _ (symmetry Heq))) in Eqr; eauto.
  rewrite <- Eqr, <- Eqx, <- Eqy.
  apply ok_fby1; auto.
Qed.

Lemma ok_when :
  forall k (xs cs : DS (sampl value)),
    let rs := swhenv k xs cs in
    forall (xsi : infinite xs)
      (csi : infinite cs)
      (rsi : infinite rs),
      safe_DS rs ->
      when k (S_of_DSv xs xsi) (S_of_DSv cs csi) (S_of_DSv rs rsi).
Proof.
  intros.
  remember_st (S_of_DSv xs xsi) as xs'.
  remember_st (S_of_DSv cs csi) as cs'.
  remember_st (S_of_DSv rs rsi) as rs'.
  revert_all.
  cofix Cof; intros * Sr ? Eqx ? Eqc ? Eqr.
  destruct xs' as [vx xs'], cs' as [vc cs'], rs' as [vr rs'].
  apply S_of_DS_Cons in Eqx as (x & tx & Hxs & Hxvx & itx & Eqx).
  apply S_of_DS_Cons in Eqc as (c & tc & Hcs & Hcvc & itc & Eqc).
  apply S_of_DS_Cons in Eqr as (r & tr & Hrs & Hrvr & itr & Eqr).
  subst rs.
  unfold swhenv in *; rewrite Hxs, Hcs, swhen_eq in Hrs.
  cases_eqn HH; simpl in *; subst; try take (Some _ = Some _) and inv it.
  all: try apply Con_eq_simpl in Hrs as [? Heq]; subst; simpl.
  (* error cases *)
  all: rewrite Hxs, Hcs in *.
  all: rewrite swhen_eq in Sr, rsi.
  all: repeat apply DSForall_tl in Sr.
  all: try (rewrite DS_const_eq in Sr; inv Sr; now exfalso).
  2: assert (k = e) by (now apply Nat.eqb_eq); subst.
  all: econstructor; auto using (proj1 (Nat.eqb_neq _ _)).
  all: rewrite (ex_proj2 (S_of_DS_eq _ _ _ _ (symmetry Heq))) in Eqr; eauto.
  all: cases; try easy; inv Sr; eauto.
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


(* TODO: move ou delete? *)
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

(* TODO: move ou delete? *)
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

(* TODO: move ou delete? *)
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

(* TODO: move ou delete? *)
Lemma _hist_of_env_eq :
  forall env Hinf env' Hinf',
    env == env' ->
    FEnv.Equiv (EqSt (A:=svalue)) (hist_of_env env Hinf) (hist_of_env env' Hinf').
Proof.
  intros * Heq.
  unfold hist_of_env.
  constructor.
  apply _S_of_DS_eq.
  now rewrite <- PROJ_simpl, Heq, PROJ_simpl.
Qed.

(* utilisation : edestruct (hist_of_env_eq env Hinf) as [Hinf' ->]. *)
(* TODO: move ou delete? *)
Lemma hist_of_env_eq :
  forall env Hinf env',
    env == env' ->
    exists Hinf',
      FEnv.Equiv (EqSt (A:=svalue)) (hist_of_env env Hinf) (hist_of_env env' Hinf').
Proof.
  intros * Heq.
  esplit.
  unshelve (rewrite _hist_of_env_eq; eauto; reflexivity).
  eapply all_infinite_Oeq_compat; eauto.
Qed.

Definition Ss_of_nprod {n} (np : @nprod (DS (sampl value)) n)
  (Hinf : forall_nprod (@infinite _) np) : list (Stream svalue).
  induction n as [|[]].
  - exact [].
  - exact [S_of_DSv np Hinf].
  - exact (S_of_DSv (fst np) (proj1 Hinf) :: IHn (snd np) (proj2 Hinf)).
Defined.

Lemma Ss_of_nprod_length :
  forall n (np : nprod n) infn,
    length (Ss_of_nprod np infn) = n.
Proof.
  clear.
  induction n as [|[]]; simpl; eauto.
Qed.

Lemma _Ss_of_nprod_eq :
  forall {n} (np np' : nprod n) Hinf Hinf',
    np == np' ->
    EqSts (Ss_of_nprod np Hinf) (Ss_of_nprod np' Hinf').
Proof.
  induction n as [|[]]; intros * Heq.
  - constructor.
  - constructor; auto.
    now apply _S_of_DS_eq.
  - apply Dprod_eq_elim_fst in Heq as ?.
    apply Dprod_eq_elim_snd in Heq as ?.
    constructor; simpl; eauto.
    apply _S_of_DS_eq. auto.
    apply IHn. auto.
Qed.

Lemma Ss_of_nprod_eq :
  forall {n} (np : nprod n) Hinf np',
    np == np' ->
    exists Hinf',
      EqSts (Ss_of_nprod np Hinf) (Ss_of_nprod np' Hinf').
Proof.
  intros * Heq.
  assert (forall_nprod (@infinite _) np') as H by now rewrite <- Heq.
  exists H. now apply _Ss_of_nprod_eq.
Qed.

Lemma Ss_of_nprod_nth :
  forall n (np : nprod n) Inf k d s (Hk : k < n),
    nth k (Ss_of_nprod np Inf) s ≡ S_of_DSv (get_nth k d np) (forall_nprod_k _ _ Inf k d Hk).
Proof.
  induction n as [|[]]; intros.
  - inv Hk.
  - assert (k = O) by lia; subst; simpl.
    now apply _S_of_DS_eq.
  - destruct k.
    + now apply _S_of_DS_eq.
    + unshelve rewrite (IHn (snd np) (proj2 Inf) k d s); auto with arith.
      now apply _S_of_DS_eq.
Qed.

Lemma _Ss_app :
  forall {n m} (np : nprod n) (mp : nprod m) Hnm Hn Hm,
    EqSts (Ss_of_nprod (nprod_app np mp) Hnm)
      ((Ss_of_nprod np Hn) ++ (Ss_of_nprod mp Hm)).
Proof.
  intros.
  induction n as [|[]]; intros; auto.
  - apply _Ss_of_nprod_eq; auto.
  - destruct m.
    + simpl. constructor; auto. now apply _S_of_DS_eq.
    + constructor.
      * now apply _S_of_DS_eq.
      * unshelve eapply IHn. split.
  - constructor. now apply _S_of_DS_eq.
    apply IHn.
Qed.

Lemma Ss_app :
  forall {n m} (np : nprod n) (mp : nprod m) Hnm,
  exists Hn Hm,
    EqSts (Ss_of_nprod (nprod_app np mp) Hnm)
      ((Ss_of_nprod np Hn) ++ (Ss_of_nprod mp Hm)).
Proof.
  intros.
  destruct (app_forall_nprod _ _ _ Hnm) as [Hn Hm].
  exists Hn,Hm.
  apply _Ss_app.
Qed.

Lemma Ss_exps :
  forall G ins envG envI bs env es Hinf Infe,
    EqSts (Ss_of_nprod (denot_exps G ins es envG envI bs env) Hinf)
      (flat_map (fun e => Ss_of_nprod (denot_exp G ins e envG envI bs env) (Infe e)) es).
Proof.
  induction es; intros; simpl.
  constructor.
  edestruct (Ss_of_nprod_eq _ Hinf) as [Inf' ->].
  { rewrite denot_exps_eq; reflexivity. }
  setoid_rewrite (ex_proj2 (ex_proj2 (Ss_app _ _ _))).
  apply app_EqSts; auto.
  now apply _Ss_of_nprod_eq.
Qed.


(** Hypothèse sur les entrées du nœud : elles doivent être bien typées
    et respecter leurs horloges vis-à-vis de leur déclaration *)
Definition correct_ins (n : node) envI bs :=
  let ins := List.map fst n.(n_in) in
  let Γ := senv_of_inout (n.(n_in) ++ n.(n_out)) in
  (* TODO: c'est compliqué à expliquer, (dérouler safe_env, inégalités, etc.)
     peut-on simplifier l'énoncé ? *)
  env_correct Γ ins envI bs 0.

Section Ok_exp.

Variables
  (G : global)
  (envG : Dprodi FI).

Hypothesis (Wtg : wt_global G).
Hypothesis (Wcg : wc_global G).
Hypothesis (Hrg : restr_global G).

Hypothesis InfG :
  forall envI f, all_infinite envI -> all_infinite (envG f envI).

(* hypothèse nécessaire pour appeler safe_exp...  *)
Hypothesis CorrectG :
    forall (f : ident) (envI : DS_prod SI),
      match find_node f G with
      | Some n =>
          let ins := idents n.(n_in) in
          let Γ := senv_of_inout (n.(n_in) ++ n.(n_out)) in
          forall bs,
            bss ins envI <= bs ->
            env_correct Γ ins envI bs 0 ->
            env_correct Γ ins envI bs (envG f envI)
      | _ => True
      end.

(* TODO: à raffiner *)
Hypothesis Hnode :
  forall f n (ss : nprod (length (n_in n))),
    find_node f G = Some n ->
    let ins := idents (n_in n) in
    let envI := env_of_ss ins ss in
    let os := ss_of_env (idents (n_out n)) (envG f envI) in
    correct_ins n envI (bss ins envI) ->
    forall infI infO,
      sem_node G f (Ss_of_nprod ss infI) (Ss_of_nprod os infO).

Definition hist_of_envs ins
  (envI : DS_prod SI) (InfI : all_infinite envI)
  (env : DS_prod SI) (Inf : all_infinite env) : Str.history :=
  fun x => Some (if mem_ident x ins
              then S_of_DSv (envI x) (InfI x)
              else S_of_DSv (env x) (Inf x)).

Lemma sem_hist_of_envs : forall ins envI InfI env Inf x Infx,
    sem_var (hist_of_envs ins envI InfI env Inf) x
      (S_of_DSv (denot_var ins envI env x) Infx).
Proof.
  intros.
  unfold hist_of_envs.
  econstructor; eauto.
  cases_eqn HH; apply _S_of_DS_eq.
  all: unfold denot_var; cases; congruence.
Qed.

Lemma _hist_of_envs_eq :
  forall ins envI HinfI env Hinf env' Hinf',
    env == env' ->
    FEnv.Equiv (EqSt (A:=svalue)) (hist_of_envs ins envI HinfI env Hinf) (hist_of_envs ins envI HinfI env' Hinf').
Proof.
  intros * Heq.
  unfold hist_of_envs.
  constructor.
  cases; apply _S_of_DS_eq; auto.
Qed.

(* utilisation : edestruct (hist_of_envs_eq env Hinf) as [Hinf' ->]. *)
Lemma hist_of_envs_eq :
  forall ins envI HinfI env Hinf env',
    env == env' ->
    exists Hinf',
    FEnv.Equiv (EqSt (A:=svalue)) (hist_of_envs ins envI HinfI env Hinf) (hist_of_envs ins envI HinfI env' Hinf').
Proof.
  intros * Heq.
  esplit.
  unshelve (rewrite _hist_of_envs_eq; eauto; reflexivity).
  eapply all_infinite_Oeq_compat; eauto.
Qed.

Lemma sem_var_ins : forall ins envI InfI env Inf x s,
    In x ins ->
    s ≡ S_of_DSv (envI x) (InfI x) ->
    sem_var (hist_of_envs ins envI InfI env Inf) x s.
Proof.
  intros * Hin Heq.
  econstructor; try reflexivity.
  cases_eqn Hmem; auto.
  now apply mem_ident_false in Hmem.
Qed.

Lemma sem_var_nins : forall ins envI InfI env Inf x s,
    ~ In x ins ->
    s ≡ S_of_DSv (env x) (Inf x) ->
    sem_var (hist_of_envs ins envI InfI env Inf) x s.
Proof.
  intros * Hin Heq.
  econstructor; try reflexivity.
  cases_eqn Hmem; auto.
  now apply mem_ident_spec in Hmem.
Qed.

Lemma denot_var_inf :
  forall ins envI env x,
    all_infinite envI ->
    all_infinite env ->
    infinite (denot_var ins envI env x).
Proof.
  unfold denot_var.
  intros; cases; eauto.
Qed.

Lemma env_of_ss_inf :
  forall l n (np : nprod n),
    forall_nprod (@infinite _) np ->
    all_infinite (env_of_ss l np).
Proof.
  clear.
  unfold env_of_ss.
  intros * ??.
  setoid_rewrite Dprodi_DISTR_simpl.
  cases_eqn HH.
  - apply forall_nprod_k_def; auto. apply DS_const_inf.
  - apply DS_const_inf.
Qed.

(** Deux tactiques bien pratiques pour la suite *)

(* C'est souvent une bonne idée de généraliser les termes [infinite_exp]
   car ça élimine une dépendance sur [denot_exp]. *)
Ltac gen_infinite_exp :=
  repeat (
  simpl; (* important, même si l'action n'est pas visible *)
  match goal with
  | |- context [ infinite_exp ?H1 ?H2 ?H3 ?H4 ?H5 ?H6 ?H7 ?H8 ?H9 ?H10 ?H11 ] =>
      generalize (infinite_exp H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)
  | |- context [ infinite_exps ?H1 ?H2 ?H3 ?H4 ?H5 ?H6 ?H7 ?H8 ?H9 ?H10 ?H11 ] =>
      generalize (infinite_exps H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)
  end).

(* Isole un terme [denot_exp ...] dans une égalisé [Hse] afin de pouvoir
   réécrire [denot_exp_eq] dedans, sans complications liées à S_of_DSv. *)
Ltac save_denot_exp se Hse :=
  gen_infinite_exp;
  match goal with
  | |- context [ ?f1 (?f2 (?f3 (?f4 (denot_exp ?e1 ?e2 ?e3) ?e4) ?e5) ?e6) ?e7 ] =>
      remember (f1 (f2 (f3 (f4 (denot_exp e1 e2 e3) e4) e5) e6) e7)
      as se eqn:Hse
  end.

(* Une fois [denot_exp] appliqué, on voit souvent apparaître [denot_exps]
   sur les sous-expressions. Si l'hypothèse de récurrence est déjà dégrossie,
   il peut être utile d'abstraire les sous-flots avec ça : *)
Ltac gen_sub_exps :=
  gen_infinite_exp;
  repeat match goal with
  | |- context [ ?f1 (?f2 (?f3 (?f4 (denot_exps ?e1 ?e2 ?e3) ?e4) ?e5) ?e6) ?e7 ] =>
      generalize (f1 (f2 (f3 (f4 (denot_exps e1 e2 e3) e4) e5) e6) e7)
  | |- context [ ?f1 (?f2 (?f3 (?f4 (denot_exp ?e1 ?e2 ?e3) ?e4) ?e5) ?e6) ?e7 ] =>
      generalize (f1 (f2 (f3 (f4 (denot_exp e1 e2 e3) e4) e5) e6) e7)
  end.

Lemma ok_sem_exp :
  forall Γ ins env Inf envI InfI bs,
    env_correct Γ ins envI (DS_of_S bs) env ->
    let H := hist_of_envs ins envI InfI env Inf in
    forall (e : exp) (Hwt : wt_exp G Γ e) (Hwc : wc_exp G Γ e) (Hr : restr_exp e),
      op_correct_exp G ins envG envI (DS_of_S bs) env e ->
      let ss := denot_exp G ins e envG envI (DS_of_S bs) env in
      let Infe := infinite_exp _ _ _ _ _ _ InfG (DS_of_S_inf _) InfI Inf _ in
      sem_exp G (H, FEnv.empty _) bs e (Ss_of_nprod ss Infe).
Proof.
  intros ?? env * Hc H.
  induction e using exp_ind2; intros * ??? Hoc ss Infe.
  all: inv Hr; subst ss; simpl.
  - (* Econst *)
    constructor.
    edestruct (S_of_DSv_eq _ Infe) as [Infe' ->].
    { rewrite denot_exp_eq. reflexivity. }
    apply ok_const.
  - (* Evar *)
    constructor; simpl.
    edestruct (S_of_DSv_eq _ Infe) as [Infe' ->].
    { rewrite denot_exp_eq. reflexivity. }
    apply sem_hist_of_envs.
  - (* Eunop *)
    eapply safe_exp in Hoc as Hs; eauto using restr_exp.
    apply wt_exp_wl_exp in Hwt as Hwl.
    inv Hwt. inv Hwc. inv Hoc. inv Hwl.
    edestruct (Ss_of_nprod_eq _ Infe) as [Hinf0 HH].
    { setoid_rewrite denot_exp_eq. reflexivity. }
    rewrite HH; clear HH.
    rewrite denot_exp_eq in Hs.
    revert Hinf0 IHe Hs; simpl.
    gen_sub_exps.
    take (numstreams e = 1) and rewrite it.
    take (typeof e = _) and rewrite it.
    econstructor; eauto using ok_unop.
  - (* Efby *)
    eapply safe_exp in Hoc as Hs; eauto using restr_exp.
    apply wt_exp_wl_exp in Hwt as Hwl.
    inv Hwt. inv Hwc. inv Hoc. inv Hwl.
    apply Forall_impl_inside with (P := wt_exp _ _) in H0, H1; auto.
    apply Forall_impl_inside with (P := wc_exp _ _) in H0, H1; auto.
    apply Forall_impl_inside with (P := restr_exp) in H0, H1; auto.
    apply Forall_impl_inside with (P := op_correct_exp _ _ _ _ _ _) in H0, H1; auto.
    econstructor; simpl in *.
    + erewrite Forall2_map_2, <- Forall2_same. apply H0.
    + erewrite Forall2_map_2, <- Forall2_same. apply H1.
    + rewrite <- 2 flat_map_concat_map.
      unshelve rewrite <- 2 Ss_exps; auto using DS_of_S_inf, infinite_exps.
      revert Infe Hs.
      save_denot_exp se Hse.
      setoid_rewrite denot_exp_eq in Hse; revert Hse; simpl.
      gen_sub_exps.
      rewrite annots_numstreams in *.
      unfold eq_rect_r, eq_rect, eq_sym.
      cases; intros; subst; try congruence.
      clear - Hs.
      induction (list_sum (map numstreams es)) as [|[]];
        eauto using Forall3_nil, Forall3_cons, ok_fby.
      inv Hs.
      constructor; [ simpl; now apply ok_fby | now apply IHn ].
  - (* Ewhen *)
    destruct x as [x ty].
    eapply safe_exp in Hoc as Hs; eauto using restr_exp.
    apply wt_exp_wl_exp in Hwt as Hwl.
    inv Hwt. inv Hwc. inv Hoc. inv Hwl.
    apply Forall_impl_inside with (P := wt_exp _ _) in H0; auto.
    apply Forall_impl_inside with (P := wc_exp _ _) in H0; auto.
    apply Forall_impl_inside with (P := restr_exp) in H0; auto.
    apply Forall_impl_inside with (P := op_correct_exp _ _ _ _ _ _) in H0; auto.
    econstructor; simpl.
    + erewrite Forall2_map_2, <- Forall2_same. apply H0.
    + unshelve apply sem_hist_of_envs; auto using denot_var_inf.
    + rewrite <- flat_map_concat_map.
      unshelve rewrite <- Ss_exps; auto using DS_of_S_inf, infinite_exps.
      revert Infe Hs.
      save_denot_exp se Hse.
      setoid_rewrite denot_exp_eq in Hse; revert Hse; simpl.
      gen_sub_exps.
      rewrite annots_numstreams in *.
      unfold eq_rect_r, eq_rect, eq_sym.
      cases; intros; subst; try congruence.
      clear - Hs.
      induction (list_sum (map numstreams es)) as [|[]]; eauto using Forall2, ok_when.
      inv Hs.
      constructor; [ now apply ok_when | now apply IHn ].
  - (* Eapp *)
    eapply safe_exp in Hoc as Hs; eauto using restr_exp.
    apply wt_exp_wl_exp in Hwt as Hwl.
    inv Hwt. inv Hwc. inv Hoc. inv Hwl.
    repeat take (find_node _ _ = _) and rewrite it in *.
    repeat take (Some _ = Some _) and inv it.
    apply Forall_impl_inside with (P := wt_exp _ _) in H0; auto.
    apply Forall_impl_inside with (P := wc_exp _ _) in H0; auto.
    apply Forall_impl_inside with (P := restr_exp) in H0; auto.
    apply Forall_impl_inside with (P := op_correct_exp _ _ _ _ _ _) in H0; auto.
    econstructor; eauto using Forall2_nil, bools_ofs_empty; simpl in *.
    { erewrite Forall2_map_2, <- Forall2_same. apply H0. }
    intros [].
    + (* k = 0, c'est intéressant *)
      setoid_rewrite masks_false_0.
      unshelve rewrite <- flat_map_concat_map, <- Ss_exps; auto using DS_of_S_inf, infinite_exps.
      revert Infe Hs.
      save_denot_exp se Hse.
      setoid_rewrite denot_exp_eq in Hse; revert Hse; simpl.
      (* on a besoin d'infos sur les flots des ss pour pouvoir utiliser Hnode *)
      edestruct safe_exps_ with (es := es) as (sTy & sCl & sEf); eauto.
      pose proof (nclocksof_sem G envG ins envI (DS_of_S bs) env es) as Ncs.
      revert sTy sCl sEf Ncs.
      gen_sub_exps.
      take (length (annots _) = _) and rewrite <- annots_numstreams, it.
      repeat take (find_node _ _ = _) and rewrite it.
      unfold eq_rect_r, eq_rect, eq_sym.
      cases; intros; subst; try setoid_rewrite map_length in n0; try congruence.
      apply Hnode; auto; unfold correct_ins.
      (* on montre que les entrées forment un environnement correct *)
      rewrite clocksof_nclocksof in sCl.
      eapply wc_find_node in Wcg as (?& Wcin &?&?); eauto.
      eapply safe_inst_in in sCl as Hec; eauto.
      apply env_correct_decompose in Hec as HH.
      destruct HH as (?&?&?).
      eapply bss_le_bs in Wcin as Hbs; eauto.
      (* et comme tout est infini, ça marche : *)
      apply infinite_le_eq in Hbs as -> ; auto using bss_inf, env_of_ss_inf.
    + (* k <> 0, on utilise sem_node_absent *)
      setoid_rewrite masks_false_S.
      pose proof (sem_global_absent G Hrg Wtg f n) as Hsem.
      eapply sem_node_morph in Hsem; eauto.
      * rewrite map_ignore, concat_length_sum, map_map.
        setoid_rewrite Ss_of_nprod_length.
        rewrite <- annots_numstreams.
        take (_ = length (n_in n)) and rewrite it.
        now apply Forall2_repeat.
      * rewrite map_ignore, Ss_of_nprod_length.
        take (_ = length (n_out n)) and rewrite it.
        now apply Forall2_repeat.
Qed.

End Ok_exp.

Theorem _ok_global :
  forall (HasCausInj : forall (Γ : static_env) (x cx : ident), HasCaus Γ x cx -> x = cx),
  forall G,
    restr_global G ->
    wt_global G ->
    wc_global G ->
    op_correct_glob G ->
    Forall node_causal (nodes G) ->
    forall f n (ss : nprod (length (n_in n))),
      find_node f G = Some n ->
      let ins := idents (n_in n) in
      let envI := env_of_ss ins ss in
      let os := ss_of_env (idents (n_out n)) (denot_global G f envI) in
      let bs := bss ins envI in
      correct_ins n envI bs ->
      forall InfSs InfO,
        sem_node G f (Ss_of_nprod ss InfSs) (Ss_of_nprod os InfO).
Proof.
  intros ?? Rg Wtg Wcg Ocg Causg ??? Hfind ???? Hins ??.
  unfold op_correct_glob in Ocg.
  assert (Ordered_nodes G) as Hord.
  now apply wl_global_Ordered_nodes, wt_global_wl_global.
  remember (denot_global G) as envG eqn:HG.
  assert (InfG : forall f envI,
             all_infinite envI ->
             all_infinite (envG f envI)).
  { subst envG. eauto using denot_inf. }
  assert (HenvG : forall f nd envI,
             find_node f G = Some nd ->
             envG f envI == FIXP _ (denot_node G nd envG envI)).
  { intros * Hf; subst.
    unfold denot_global.
    now rewrite <- PROJ_simpl, FIXP_eq, PROJ_simpl, denot_global_eq, Hf at 1. }
  clear HG.
  revert dependent n. revert f.
  destruct G as [tys exts nds].
  induction nds as [|a nds]; intros. inv Hfind.
  destruct (ident_eq_dec (n_name a) f); subst.
  - (* cas qui nous intéresse *)
    rewrite find_node_now in Hfind; inv Hfind; auto.
    inversion_clear Ocg as [|?? Hoc Hocs].
    (* TODO: peut-être plus direct que ça en instanciant sous Snode *)
    pose (InfI := env_of_ss_inf ins _ _ InfSs).
    pose (H := hist_of_envs ins envI InfI
                 (envG (n_name n) envI) (InfG _ _ InfI)).
    eapply Snode with (H := H); eauto using find_node_now.
    + (* sem_var in *)
      subst H envI.
      apply Forall2_forall2.
      split. { rewrite Ss_of_nprod_length. now setoid_rewrite map_length. }
      intros; subst.
      assert (Hlen := H).
      setoid_rewrite map_length in Hlen.
      apply sem_var_ins; auto using nth_In.
      unshelve rewrite Ss_of_nprod_nth; auto using errTy.
      apply _S_of_DS_eq.
      erewrite env_of_ss_nth; eauto.
      apply mem_nth_nth; auto using n_NoDup_in.
    + (* sem_var out *)
      subst H os.
      apply Forall2_forall2.
      split. { rewrite Ss_of_nprod_length. now setoid_rewrite map_length. }
      intros; subst.
      assert (Hlen := H).
      setoid_rewrite map_length in Hlen.
      apply sem_var_nins.
      { intro. eapply (not_in_out n); eauto using nth_In. }
      unshelve rewrite Ss_of_nprod_nth; auto using errTy.
      apply _S_of_DS_eq.
      erewrite nth_ss_of_env; eauto.
    + (* sem_block *)
      eapply wc_find_node in Wcg as HH; eauto using find_node_now.
      destruct HH as (?&?&?& Wcb).
      eapply wt_find_node in Wtg as HH; eauto using find_node_now.
      destruct HH as (?& (?&?&?& Wtb) & ?).
      unfold op_correct in Hoc.
      revert Hoc Wcb Wtb.
      inv Rg; take (restr_node _) and inv it; intros.
      (* inv Wcb. take (wc_equation _ _ _) and inv it. *)
      inv Wtb. take (wt_equation _ _ _) and inv it.
      set (G := Global tys exts (n :: nds)) in *.
      subst H.
      edestruct (hist_of_envs_eq ins) as [Inf2 ->].
      { rewrite HenvG; [|now apply find_node_now].
        rewrite FIXP_eq.
        rewrite <- HenvG; [| now apply find_node_now].
        rewrite denot_node_eq.
        unfold denot_block.
        take (_ = n_block _) and rewrite <- it.
        reflexivity. }
      assert (Hbs : infinite bs) by (apply bss_inf; auto).
      constructor; econstructor; simpl.
      * erewrite Forall2_map_2, <- Forall2_same, Forall_forall.
        admit.
        (* intros. *)
        (* unshelve eapply ok_sem_exp; eauto; try now eapply Forall_In; eauto. *)
        (* eapply safe_equ; eauto using NoDup_senv, Beq_out. *)
      * unshelve rewrite <- flat_map_concat_map, <- Ss_exps; simpl;
          auto using infinite_exps, infinite_exp.
        assert (length xs = list_sum (map numstreams es)). {
          rewrite <- annots_numstreams, <- length_typesof_annots.
          eauto using Forall2_length.
        }
      apply Forall2_forall2.
      split. { now rewrite Ss_of_nprod_length. }
      intros ?? k ?? Hk; intros; subst.
      rewrite Ss_of_nprod_nth.

(* Lemma sem_hist_of_envs' : forall ins envI InfI env Inf x xs Infx, *)
(*     xs == denot_var ins envI env x -> *)
(*     sem_var (hist_of_envs ins envI InfI env Inf) x (S_of_DSv xs Infx). *)
(* Proof. *)
(*   intros. *)
(*   edestruct (S_of_DSv_eq xs) as [Inf2 ->]; *)
(*     eauto using sem_hist_of_envs. *)
(* Qed. *)
      (* rewrite denot_equation_eq, mem_nth_nth; eauto 2 using NoDup_app_r. *)
      (* cases_eqn HH; try congruence. *)
      (* rewrite mem_ident_spec in *. *)
      (* exfalso; eapply NoDup_app_In; eauto using nth_In. *)
      (* Unshelve. eapply forall_nprod_k'; auto using infinite_exps; lia. *)
  - (* cas de récurrence *)
    rewrite find_node_other in Hfind; auto.
    apply sem_node_cons'; auto.
    apply IHnds; auto.
    + now inv Rg.
    + eauto using wt_global_cons.
    + eauto using wc_global_cons.
    + clear - Ocg Hord. inv Ocg.
      eapply Forall_impl_In; eauto.
      intros * Hin HH * Hins.
      eapply op_correct_cons in HH; eauto using Ordered_nodes_nin.
    + now inv Causg.
    + eauto using Ordered_nodes_cons.
    + intros f' ndf' envI' Hfind'.
      eapply find_node_uncons with (nd := a) in Hfind' as ?; auto.
      rewrite HenvG, <- denot_node_cons; eauto using find_node_later_not_Is_node_in.
Qed.
End SDTOREL.
