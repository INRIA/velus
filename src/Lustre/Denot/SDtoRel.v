From Coq Require Import BinPos List.

From Velus Require Import Common Ident Environment Operators Clocks CoindStreams.
From Velus Require Import Lustre.StaticEnv Lustre.LSyntax Lustre.LOrdered Lustre.LSemantics Lustre.LTyping Lustre.LClocking Lustre.LCausality.

From Velus Require Import Lustre.Denot.Cpo.

Close Scope equiv_scope. (* conflicting notation "==" *)
Import ListNotations.

Require Import Cpo_ext CommonDS SDfuns Denot Infty InftyProof Safe.

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
       (Import Den   : LDENOT     Ids Op OpAux Cks Senv Syn Str)
       (Import Inf   : LDENOTINF  Ids Op OpAux Cks Senv Syn Typ Caus Str Den)
       (Import Safe  : LDENOTSAFE Ids Op OpAux Cks Senv Syn Typ Cl Str Den).

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

Definition safe_DS : DS (sampl value) -> Prop := DSForall safe_val.



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
  rewrite MAP_map, ?map_eq_cons in Hxs.
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

(* (* TODO: move *) *)
(* Lemma DSForall_hd : forall {A} (P : A -> Prop) x xs, DSForall P (cons x xs) -> P x. *)
(* Proof. *)
(*   intros * Hf. *)
(*   now inv Hf. *)
(* Qed. *)

Lemma safe_fby1s_inv :
  forall b o s1 s2,
    let sf := SDfuns.fby1s b o s1 s2 in
    infinite sf -> (* sinon invalide avec [s1 = bot] et [s2 = const error] *)
    safe_DS sf ->
    forall s,
    s == s1 \/ s == s2 ->
    safe_DS s.
Abort.

Lemma fbys_inf_inv1 :
  forall {A} b (s1 s2 : DS (sampl A)),
    infinite (SDfuns.fbys b s1 s2) ->
    infinite s1.
Proof.
  intros * Hinf.
  remember s1 as ss eqn:Hss.
  apply Oeq_refl_eq in Hss.
  revert_all.
  cofix Cof; intros.
  constructor.
  -
Abort.

Lemma fbys_inf_inv2 :
  forall {A} b (s1 s2 : DS (sampl A)),
    infinite (SDfuns.fbys b s1 s2) ->
    infinite s2.
Proof.
Abort.

Lemma safe_fbys_inv :
  forall b s1 s2 s,
    let sf := SDfuns.fbys b s1 s2 in
    infinite sf -> (* sinon invalide avec [s1 = bot] et [s2 = const error] *)
    safe_DS sf ->
    s == s1 \/ s == s2 ->
    safe_DS s.
Proof.
  intros * Hinf Hsafe Hs.
  remember s as ss eqn:Hss.
  apply Oeq_refl_eq in Hss.
  revert_all.
  cofix Cof; intros; subst sf.
  destruct ss.
  - constructor. rewrite <- eqEps in *. eapply Cof; eauto.
  - assert (Hinf' := Hinf).
(*     destruct Hs as [Hs|Hs]; rewrite <- Hs in Hinf, Hinf', Hsafe; *)
(*       [apply fbys_inf_inv2, infinite_decomp in Hinf' as (?&?& Hs' &?) *)
(*       | apply fbys_inf_inv1, infinite_decomp in Hinf' as (?&?& Hs' &?)]; *)
(*       rewrite Hs' in Hinf, Hsafe. *)
(*     all: destruct b; rewrite ?fbysF_eq, ?fbysT_eq in Hsafe, Hinf; cases; *)
(*       try now rewrite DS_const_eq in Hsafe; apply DSForall_hd in Hsafe. *)
(*     all: rewrite ?fbysF_eq, ?fbysT_eq in Hsafe, Hinf; cases; *)
(*       try (now rewrite DS_const_eq in Hsafe; apply DSForall_hd in Hsafe); *)
(*       try (now rewrite DS_const_eq in Hsafe; apply DSForall_tl, DSForall_hd in Hsafe). *)
(*     all: try (constructor; simpl; [tauto|]). *)
(*     all: repeat apply DSForall_tl in Hsafe; repeat apply cons_infinite in Hinf. *)
(*     all: try (now eapply Cof; eauto). *)
(*     all: unfold fby1AP in *; eapply safe_fby1s_inv; try apply Hinf; auto. *)
(* Qed. *)
Abort.


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

(* TODO: move, ne pas trop utiliser parce que c'est merdique *)
Lemma Forall_impl_inside :
  forall {A} (P Q : A -> Prop) xs,
    (Forall (fun x => P x -> Q x) xs) ->
    Forall P xs ->
    Forall Q xs.
Proof.
  induction xs; auto.
  intros FPQ FP. inv FPQ. inv FP.
  constructor; auto.
Qed.

(* TODO: move, remplacer Forall3_EqSt *)
Global Add Parametric Morphism
  A B C (P: A -> B -> C -> Prop) eqA eqB eqC
  (P_compat:  Morphisms.Proper (eqA ==> eqB ==> eqC ==> Basics.impl) P)
  : (@Forall3 A B C P)
       with signature (Forall2 eqA) ==> (Forall2 eqB) ==> (Forall2 eqC) ==> Basics.impl
         as Forall3_morph.
Proof.
  unfold Morphisms.Proper, Morphisms.respectful, Basics.impl in *.
  induction x; intros x' Hx y y' Hy z z' Hz HF3.
  - inv HF3. simpl_Forall. constructor.
  - inv HF3. inv Hx. inv Hy. inv Hz.
    constructor; eauto.
Qed.

(* TODO: variante avec existentielle *)
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

(* TODO: utile ou pas ? *)
Add Parametric Morphism P n
  (P_compat:  Morphisms.Proper (Oeq (O := DS (sampl value)) ==> iff) P)
  : (forall_nprod P)
    with signature Oeq (O := nprod n) ==> iff
      as forall_nprod_morph.
Proof.
  unfold Morphisms.Proper, Morphisms.respectful, Basics.impl in *.
  intros * Heq.
  rewrite 2 forall_nprod_k_iff.
  split; intros.
  eapply P_compat; rewrite <- ?Heq; auto.
  eapply P_compat; rewrite ?Heq; auto.
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
  forall ins envI bs env es Hinf Infe,
    EqSts (Ss_of_nprod (denot_exps ins es envI bs env) Hinf)
      (flat_map (fun e => Ss_of_nprod (denot_exp ins e envI bs env) (Infe e)) es).
Proof.
  induction es; intros; simpl.
  constructor.
  edestruct (Ss_of_nprod_eq _ Hinf) as [Inf' ->].
  { rewrite denot_exps_eq; reflexivity. }
  setoid_rewrite (ex_proj2 (ex_proj2 (Ss_app _ _ _))).
  apply app_EqSts; auto.
  now apply _Ss_of_nprod_eq.
Qed.

(* TODO: partager, évidemment *)
Axiom restr_restr : forall e, Safe.restr_exp e <-> restr_exp e.

Theorem safe_exp :
  forall {PSyn prefs} (G : @global PSyn prefs),
  forall Γ ins e env envI bs,
    wt_exp G Γ e ->
    wc_exp G Γ e ->
    op_correct_exp ins envI bs env e ->
    (* safe_env env -> *)
    forall_nprod safe_DS (denot_exp ins e envI bs env).
Proof.
Abort.

(* TODO: sampl value -> evalue
   dans K : seulement des err_Op, Ty?
   dans SD : Ty, Cl
 *)
Lemma ok_sem_exp :
  forall {PSyn prefs} (G : @global PSyn prefs),
  forall Γ ins equ envI bs Inf (WT : wt_equation G Γ equ)
    (InfI : all_infinite envI),
    (* TODO: pourquoi denot_equation plutôt que node ? *)
    let env := (FIXP (DS_prod SI) (denot_equation ins equ envI (DS_of_S bs))) in
    forall (e : exp) (Hwt : wt_exp G Γ e) (Hwc : wc_exp G Γ e) (Hr : restr_exp e),
      op_correct_exp ins envI (DS_of_S bs) env e ->
      let ss := denot_exp ins e envI (DS_of_S bs) env in
      let Infe := infinite_exp _ _ _ _ (DS_of_S_inf _) InfI Inf _ in
      sem_exp G (hist_of_env env Inf, empty _) bs e (Ss_of_nprod ss Infe).
Proof.
  induction e using exp_ind2; intros ?? Hr Hoc ??; inv Hr; subst ss; simpl.
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
    unfold denot_var.
    cases_eqn HH; apply mem_ident_spec in HH.
    subst env0.
    setoid_rewrite <- PROJ_simpl at 2.
    rewrite FIXP_eq, PROJ_simpl.
    erewrite denot_equation_input; eauto.
  - (* unop *)
    eapply safe_exp in Hwc as Hs; eauto.
    3: rewrite restr_restr; now constructor.
    2: {
      (* TODO *)
    }
    destruct Hs as (_&_&Hsafe).
    apply wt_exp_wl_exp in Hwt as Hwl.
    inv Hwt. inv Hwc. inv Hoc. inv Hwl.
    edestruct (Ss_of_nprod_eq _ Infe) as [Hinf0 HH].
    { setoid_rewrite denot_exp_eq. reflexivity. }
    fold env0 in HH.
    rewrite HH; clear HH.
    rewrite denot_exp_eq in Hsafe.
    revert Hinf0 IHe Hsafe.
    simpl; fold env0.
    generalize (infinite_exp ins envI (DS_of_S bs) env0 (DS_of_S_inf bs) InfI Inf e).
    generalize (denot_exp ins e envI (DS_of_S bs) env0).
    take (numstreams e = 1) and rewrite it.
    take (typeof e = _) and rewrite it.
    econstructor; eauto using ok_unop.
  - (* fby *)
    pose proof (safe_exp _ _ _ _ _ _ _ Hwt Hwc Hoc) as Hsafe.
    apply wt_exp_wl_exp in Hwt as Hwl.
    inv Hwt. inv Hwc. inv Hoc. inv Hwl.
    (* TODO: mettre tout ça dans un seul prédicat ? *)
    (* wt *)
    apply Forall_impl_inside with (P := wt_exp _ _) in H, H0; auto.
    apply Forall_impl_inside with (P := wc_exp _ _) in H, H0; auto.
    apply Forall_impl_inside with (P := restr_exp) in H, H0; auto.
    apply Forall_impl_inside with (P := op_correct_exp _ _ _ _) in H, H0; auto.

    econstructor; simpl in *.
    + erewrite Forall2_map_2, <- Forall2_same. apply H.
    + erewrite Forall2_map_2, <- Forall2_same. apply H0.
    + rewrite <- 2 flat_map_concat_map.
      unshelve rewrite <- 2 Ss_exps; auto using DS_of_S_inf, infinite_exps.

      edestruct (Ss_of_nprod_eq _ Infe) as [Hinf0 HH].
      { setoid_rewrite denot_exp_eq. simpl. reflexivity. }
      fold env0 in HH. rewrite HH; clear HH.

      remember (infinite_exps ins _ _ _ _ _ _ e0s) as Hinf1 eqn:HH; clear HH.
      remember (infinite_exps ins _ _ _ _ _ _ es) as Hinf2 eqn:HH; clear HH.
      setoid_rewrite denot_exp_eq in Hsafe. simpl in Hsafe.
      revert Hinf0 Hinf1 Hinf2 Hsafe.
      fold env0.
      generalize (denot_exps ins e0s envI (DS_of_S bs) env0) as s0s.
      generalize (denot_exps ins es envI (DS_of_S bs) env0) as ss.
      intros.
      cases; try (rewrite annots_numstreams in *; congruence).
      unfold eq_rect_r, eq_rect in *; destruct e0, e; simpl in *.

      clear - Hsafe.
      induction (length a) as [|[]].
      * constructor.
      * constructor; auto using Forall3_nil, ok_fby.
      * destruct ss as [s ss], s0s as [s0 s0s].
        inv Hsafe.
        edestruct (Ss_of_nprod_eq _ Hinf0) as [Hinf0' ->].
        { rewrite lift2_simpl. reflexivity. }
        constructor; simpl in *; auto using ok_fby.
Qed.

(* TODO: move *)
(* FAUX *)
Lemma wc_equation_sub :
  forall {PSyn prefs} (G : @global PSyn prefs),
  forall Γ xs es,
    wc_equation G Γ (xs,es) ->
    Forall (wc_exp G Γ) es.
Proof.
  intros * Wc.
  inv Wc; auto.
  constructor; econstructor; eauto.
  rewrite Forall2_map_2 in H7.
  rewrite Forall2_map_2, Forall2_map_1.
  rewrite Forall3_map_1, Forall3_map_2 in H5.
  clear - H5 H7.
  induction H5; simpl_Forall; inv H7; constructor; auto.
  destruct x, y, p as [[]]; simpl in *.
  inv H; constructor; simpl in *; auto.
Abort.

(* TODO: move *)
Lemma sem_var_env :
  forall env Inf x xs Infx,
    xs == env x ->
    sem_var (hist_of_env env Inf) x (S_of_DSv xs Infx).
Proof.
  unfold hist_of_env.
  econstructor; eauto.
  now apply _S_of_DS_eq.
Qed.

(* TODO: move *)
Lemma nth_Ss_of_nprod :
  forall {n} (np : nprod n) Infn k Infk a,
    k < n ->
    nth k (Ss_of_nprod np Infn) a ≡ S_of_DSv (get_nth np k) Infk.
Proof.
  induction n as [|[]]; intros * Hk; auto.
  - inv Hk.
  - simpl; cases; simpl; try lia.
    apply _S_of_DS_eq; auto.
  - destruct np as (s,np).
    destruct k.
    + apply _S_of_DS_eq; auto.
    + apply IHn; lia.
Qed.


(* TODO: move *)
(* https://stackoverflow.com/questions/73155085/coq-rewriting-under-a-pointwise-relation *)
Import Morphisms.
Add Parametric Morphism : sem_var
    with signature Equiv (@EqSt _) ==> pointwise_relation _ (pointwise_relation _ iff)
      as sem_var_morph_pointwise.
Proof.
  split; now rewrite H.
Qed.

(* TODO: move *)
Lemma Ss_of_nprod_length :
  forall {n} (np : nprod n) Inf,
    length (Ss_of_nprod np Inf) = n.
Proof.
  induction n as [|[]]; simpl; eauto.
Qed.

(* TODO: move *)
Lemma nodup_equation :
  forall {PSyn prefs} (n : @node PSyn prefs),
    match n_block n with
    | Beq (xs, _) => NoDup (List.map fst n.(n_in) ++ xs)
    | _ => True (* TODO *)
    end.
Proof.
  destruct n; simpl in *.
  destruct n_defd0 as (xs & Vd & Hxs).
  destruct n_nodup0 as [ND].
  cases; simpl in *.
  inversion Vd; subst.
  now rewrite Hxs, <- map_app, <- fst_NoDupMembers.
Qed.

(* TODO: énoncer plutôt exist os, .. et faire ça dans la preuve ? *)
Lemma ok_sem_node :
  forall {PSyn prefs} (G : @global PSyn prefs),
  forall (HasCausInj : forall (Γ : static_env) (x cx : ident), HasCaus Γ x cx -> x = cx),
  forall f (nd : node) ss,
    length nd.(n_in) = length ss ->
  forall (Hn : find_node f G = Some nd)
    (Hwt : wt_node G nd)
    (Hwc : wc_node G nd)
    (Hnc : node_causal nd)
    (Hre : restr_node nd)
  ,
    let ins := List.map fst nd.(n_in) in
    let outs := List.map fst nd.(n_out) in
    let envI := env_of_list ins ss in
    let infI := env_of_list_inf ins ss in
    let bs := DS_of_S (clocks_of ss) in
    let env := FIXP (DS_prod SI) (denot_node nd envI bs) in
    let bsi := DS_of_S_inf (clocks_of ss) in
    let infO := denot_inf G HasCausInj nd envI bs Hwt Hnc bsi infI in
    let H := hist_of_env env infO in
    let os := list_of_hist H outs in
    op_correct ins envI bs env nd ->
    sem_node G f ss os.
Proof.
  intros * Hl. intros until os. intro Hop.
  eapply Snode with (H := H); eauto using list_of_hist_ok.
  - subst H env0.
    pose proof nd.(n_nodup) as [ND _].
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
  - clear os. subst H.
    inversion Hwt as (_&_&_& Wtb).
    destruct Hwc as (_&_& Wcb).
    unfold op_correct in Hop.
    pose proof (nodup_equation nd) as NDi.
    inversion Hre as [?? Hr Hb]; rewrite <- Hb in *.
    subst env0.
    edestruct (hist_of_env_eq _ infO) as [Inf2 ->];
      unfold denot_node, denot_block in *; rewrite <- Hb in *; try reflexivity.
    inv Wcb. inv Wtb.
    take (wc_equation _ _ _) and inversion it; subst. {(*FIXME*) inv Hr. inv H9. }
    take (wt_equation _ _ _) and inversion it.
    constructor; econstructor.
    + erewrite Forall2_map_2, <- Forall2_same, Forall_forall.
      intros.
      unshelve eapply ok_sem_exp; eauto; eapply Forall_In; eauto.
    + unshelve rewrite <- flat_map_concat_map, <- Ss_exps; simpl;
        auto using DS_of_S_inf, infinite_exps.
      edestruct (hist_of_env_eq _ Inf2) as [Inf3 ->].
      { rewrite FIXP_eq. reflexivity. }
      assert (length xs = list_sum (List.map numstreams es)). {
        rewrite <- annots_numstreams, <- length_typesof_annots.
        eauto using Forall2_length.
      }
      apply Forall2_forall2.
      split. { now rewrite Ss_of_nprod_length. }
      intros ?? k ?? Hk; intros; subst.
      rewrite nth_Ss_of_nprod; [|lia].
      apply sem_var_env.
      rewrite denot_equation_eq, mem_nth_nth; eauto 2 using NoDup_app_r.
      cases_eqn HH; try congruence.
      rewrite mem_ident_spec in *.
      exfalso; eapply NoDup_app_In; eauto using nth_In.
      Unshelve. eapply forall_nprod_k'; auto using infinite_exps; lia.
Qed.

End SDTOREL.
