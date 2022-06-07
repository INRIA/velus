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


CoFixpoint DS_of_S {A} (s : Stream A) : DS A :=
  match s with
  | Streams.Cons a s => CONS a (DS_of_S s)
  end.

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

Lemma env_of_list_inf_in :
  forall l ss, all_infinite_in l (env_of_list l ss).
Proof.
  intros * x Hin.
  unfold env_of_list.
  cases; auto using DS_of_S_inf, DS_const_inf.
Qed.

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
    restr_node nd ->
    In x (List.map fst nd.(n_in)) ->
    denot_node nd envI bs env x = envI x.
Proof.
  intros * Hwt Hr Hin.
  unfold denot_node, denot_block.
  destruct Hwt as (?&?&?& Hwt).
  inv Hr. destruct Hwt eqn:HH; try congruence.
  take (Beq _ = Beq _) and inv it.
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
    let infI := env_of_list_inf_in (List.map fst nd.(n_in)) ss in
    let bs := DS_of_S (clocks_of ss) in
    let bsi := DS_of_S_inf (clocks_of ss) in
    let env := FIXP (DS_prod SI) (denot_node nd envI bs) in
    let infO := denot_inf_all G HasCausInj nd envI bs Hre Hwt Hnc bsi infI in
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
  - (* TODO *)
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
  Opaque denot_equation.
  intros.
  destruct e as (xs,es).
  (* pose (ss := denot_exps es env0 bs). *)
  pose (ss := List.map (fun e => list_of_nprod' _ (denot_exp e env0 bs)) es).
  econstructor; simpl in *.
  Search denot_node.
Qed.



End SDTOREL.
