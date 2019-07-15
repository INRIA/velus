From compcert Require Import cfrontend.ClightBigstep.
From compcert Require Import cfrontend.Clight.
From compcert Require Import cfrontend.Ctypes.
From compcert Require Import lib.Integers.
From compcert Require Import lib.Maps.
From compcert Require Import lib.Coqlib.
From compcert Require Errors.
From compcert Require Import common.Separation.
From compcert Require Import common.Values.
From compcert Require Import common.Memory.
From compcert Require Import common.Events.
From compcert Require Import common.Globalenvs.
From compcert Require Import common.Behaviors.

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Memory.
From Velus Require Import Ident.
From Velus Require Import Traces.

From Velus Require Import Common.CompCertLib.
From Velus Require Import ObcToClight.MoreSeparation.
From Velus Require Import ObcToClight.SepInvariant.
From Velus Require Import ObcToClight.Generation.
From Velus Require Import ObcToClight.Interface.

From Coq Require Import Program.Tactics.
From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import ZArith.BinInt.
From Coq Require Import Omega.
From Coq Require Import Sorting.Permutation.

From Velus Require Import Instantiator.
Import Obc.Typ.
Import Obc.Syn.
Import Obc.Sem.
Import Obc.Inv.
Import OpAux.

Open Scope list_scope.
Open Scope sep_scope.
Open Scope Z.
Hint Constructors Clight.eval_lvalue Clight.eval_expr.
Hint Resolve  Clight.assign_loc_value.

Hint Resolve Z.divide_refl.

Ltac contr := match goal with
              | H: ?x <> ?x |- _ => contradict H; auto
              | _ => auto; try discriminate; try contradiction
              end.

Ltac destruct_list_tac l x y xs :=
  let l' := fresh "l" in
  destruct l as [|x l']; [|destruct l' as [|y xs]].
Ltac destruct_list_eqn_tac l x y xs E :=
  let l' := fresh in
  destruct l as [|x l'] eqn: E; [|destruct l' as [|y xs]].
Tactic Notation "destruct_list" constr(L)
       "as" simple_intropattern(x) simple_intropattern(y) simple_intropattern(xs) :=
  destruct_list_tac L x y xs.
Tactic Notation "destruct_list" constr(L)
       "as" simple_intropattern(x) simple_intropattern(y) simple_intropattern(xs)
       ":" ident(E) :=
  destruct_list_eqn_tac L x y xs E.
Tactic Notation "destruct_list" constr(L) :=
  let x := fresh "x" in
  let y := fresh "y" in
  let xs := fresh "xs" in
  destruct_list L as x y xs.
Tactic Notation "destruct_list" constr(L) ":" ident(E) :=
  let x := fresh "x" in
  let y := fresh "y" in
  let xs := fresh "xs" in
  destruct_list L as x y xs : E.

Lemma Int_Ptrofs_max_unsigned:
  Int.max_unsigned <= Ptrofs.max_unsigned.
Proof.
  unfold Int.max_unsigned, Ptrofs.max_unsigned.
  unfold Int.modulus, Ptrofs.modulus.
  unfold Int.wordsize, Ptrofs.wordsize.
  unfold Wordsize_32.wordsize, Wordsize_Ptrofs.wordsize.
  destruct Archi.ptr64; [|reflexivity].
  simpl. omega.
Qed.

Lemma type_eq_refl:
  forall {A} t (T F: A),
    (if type_eq t t then T else F) = T.
Proof.
  intros.
  destruct (type_eq t t) as [|Neq]; contr.
Qed.

Lemma eq_key_equiv:
  forall k x k' x',
    M.eq_key (elt:=ident) (k, x) (k', x') <-> k = k'.
Proof.
  intros (x1, x2) x3 (x'1, x'2) x'3.
  unfold M.eq_key, M.Raw.Proofs.PX.eqk; simpl; split; intro H.
  - destruct H; subst; auto.
  - inv H; split; auto.
Qed.

Lemma setoid_in_key:
  forall l k x,
    SetoidList.InA (M.eq_key (elt:=ident)) (k, x) l <-> InMembers k l.
Proof.
  induction l as [|(k', x')]; split; intros Hin; try inv Hin.
  - constructor.
    now rewrite <-eq_key_equiv with (x:=x) (x':=x').
  - destruct (IHl k x); apply inmembers_cons; auto.
  - constructor.
    now apply eq_key_equiv.
  - destruct (IHl k x); apply SetoidList.InA_cons; right; auto.
Qed.

Lemma eq_key_elt_equiv:
  forall k x k' x',
    M.eq_key_elt (elt:=ident) (k, x) (k', x') <-> (k, x) = (k', x').
Proof.
  intros (x1, x2) x3 (x'1, x'2) x'3.
  unfold M.eq_key_elt, M.Raw.Proofs.PX.eqke; simpl; split; intro H.
  - destruct H as [[]]; subst; auto.
  - inv H; split; auto.
Qed.

Lemma setoid_in_key_elt:
  forall l k x,
    SetoidList.InA (M.eq_key_elt (elt:=ident)) (k, x) l <-> In (k, x) l.
Proof.
  induction l as [|(k', x')]; split; intros Hin; try inv Hin.
  - constructor.
    symmetry; now rewrite <-eq_key_elt_equiv.
  - destruct (IHl k x); apply in_cons; auto.
  - constructor.
    now apply eq_key_elt_equiv.
  - destruct (IHl k x); apply SetoidList.InA_cons; right; auto.
Qed.

Lemma setoid_nodup:
  forall l,
    SetoidList.NoDupA (M.eq_key (elt:=ident)) l <-> NoDupMembers l.
Proof.
  induction l as [|(k, x)]; split; intro Nodup; inv Nodup; constructor.
  - now rewrite <-setoid_in_key with (x:=x).
  - now rewrite <-IHl.
  - now rewrite setoid_in_key.
  - now rewrite IHl.
Qed.

Lemma MapsTo_add_same:
  forall m o f (c c': ident),
    M.MapsTo (o, f) c (M.add (o, f) c' m) ->
    c = c'.
Proof.
  intros * Hin.
  assert (M.E.eq (o, f) (o, f)) as E by reflexivity.
  pose proof (@M.add_1 _ m (o, f) (o, f) c' E) as Hin'.
  apply M.find_1 in Hin; apply M.find_1 in Hin'.
  rewrite Hin in Hin'; inv Hin'; auto.
Qed.

Lemma MapsTo_add_empty:
  forall o f o' f' c c',
    M.MapsTo (o, f) c (M.add (o', f') c' (M.empty ident)) ->
    o = o' /\ f = f' /\ c = c'.
Proof.
  intros * Hin.
  destruct (M.E.eq_dec (o', f') (o, f)) as [[E1 E2]|E1]; simpl in *.
  - subst. repeat split; auto.
    eapply MapsTo_add_same; eauto.
  - apply M.add_3 in Hin; simpl; auto.
    apply M.find_1 in Hin; discriminate.
Qed.

Lemma In_rec_instance_methods_In_insts:
  forall s m o fid cid p insts mems vars,
    wt_stmt p insts mems vars s ->
    M.MapsTo (o, fid) cid (rec_instance_methods s m) ->
    (forall o f c, M.MapsTo (o, f) c m -> In (o, c) insts) ->
    In (o, cid) insts.
Proof.
  induction s; intros * Wt Hin H; inv Wt; simpl in *; eauto.
  destruct_list i; eauto.
  destruct (M.E.eq_dec (i1, i2) (o, fid)) as [[E1 E2]|E1]; simpl in *.
  - subst.
    apply MapsTo_add_same in Hin; subst; assumption.
  - apply M.add_3 in Hin; eauto.
Qed.

Lemma In_instance_methods_In_insts:
  forall f o fid cid p insts mems,
    wt_method p insts mems f ->
    M.MapsTo (o, fid) cid (instance_methods f) ->
    In (o, cid) insts.
Proof.
  unfold wt_method, instance_methods.
  intros.
  eapply In_rec_instance_methods_In_insts; eauto.
  intros o' f' c' Hin.
  apply M.find_1 in Hin; discriminate.
Qed.

Lemma In_rec_instance_methods:
  forall s m o fid cid p insts mems vars,
    wt_stmt p insts mems vars s ->
    NoDupMembers insts ->
    In (o, cid) insts ->
    (M.MapsTo (o, fid) cid (rec_instance_methods s m) <->
     M.MapsTo (o, fid) cid (rec_instance_methods s (@M.empty ident))
     \/ M.MapsTo (o, fid) cid m).
Proof.
  induction s; simpl; intros * Wt Nodup Ho; split; intros * Hin;
    inv Wt; try now right.
  - destruct Hin as [H|]; auto; apply M.find_1 in H; discriminate.
  - destruct Hin as [H|]; auto; apply M.find_1 in H; discriminate.
  - rewrite IHs2, IHs1 in Hin; eauto.
    rewrite IHs2; eauto.
    destruct Hin as [|[|]]; auto.
  - erewrite IHs2 in Hin; eauto.
    rewrite IHs2, IHs1; eauto.
    destruct Hin as [[|]|]; auto.
  - rewrite IHs2, IHs1 in Hin; eauto.
    rewrite IHs2; eauto.
    destruct Hin as [|[|]]; auto.
  - rewrite IHs2 in Hin; eauto.
    rewrite IHs2, IHs1; eauto.
    destruct Hin as [[|]|]; auto.
  - destruct_list i; eauto.
    destruct (M.E.eq_dec (i1, i2) (o, fid)) as [[E1 E2]|E1]; simpl in *.
    + subst.
      apply MapsTo_add_same in Hin; subst.
      left; apply M.add_1; auto.
    + right; eapply M.add_3; eauto; simpl; auto.
  - destruct_list i; eauto.
    + destruct Hin as [Hin|Hin]; eauto.
      apply M.find_1 in Hin; discriminate.
    + destruct Hin as [Hin|Hin]; auto.
      apply M.find_1 in Hin; discriminate.
    + destruct Hin as [Hin|Hin].
      * apply MapsTo_add_empty in Hin; destruct Hin as (? & ? & ?); subst.
        apply M.add_1; auto.
      *{ destruct (M.E.eq_dec (i1, i2) (o, fid)) as [[E1 E2]|E1]; simpl in *.
         - subst.
           app_NoDupMembers_det.
           apply M.add_1; auto.
         - apply M.add_2; auto.
       }
  - destruct Hin; auto; apply M.find_1 in H; discriminate.
Qed.

Remark elements_empty:
  M.elements (@M.empty ident) = [].
Proof.
  unfold M.elements, M.empty; simpl.
  auto.
Qed.

Remark Forall_add:
  forall x y a m P,
    Forall P (M.elements m) ->
    P ((x, y), a) ->
    Forall P (M.elements (elt:=ident) (M.add (x, y) a m)).
Proof.
  intros * Hm H.
  rewrite Forall_forall in *.
  intros ((x', y'), a') Hin.
  apply setoid_in_key_elt, M.elements_2 in Hin.
  destruct (M.E.eq_dec (x, y) (x', y')) as [E|E].
  - destruct E; simpl in *; subst.
    apply MapsTo_add_same in Hin.
    now subst.
  - apply M.add_3 in Hin; auto.
    apply M.elements_1, setoid_in_key_elt in Hin; auto.
Qed.

Lemma valid_rec_instance_methods:
  forall s m p insts mems vars,
    wt_stmt p insts mems vars s ->
    Forall (fun xt => valid (fst xt)) insts ->
    Forall (fun xt => valid (fst (fst xt))) (M.elements m) ->
    Forall (fun xt => valid (fst (fst xt))) (M.elements (rec_instance_methods s m)).
Proof.
  induction s; simpl; inversion 1; intros * Valid_insts ?; eauto.
  destruct_list i; auto.
  apply Forall_add; auto.
  eapply Forall_forall with (x := (i1, i0)) in Valid_insts; eauto.
Qed.

Lemma valid_instance_methods:
  forall f m p c,
    wt_class p c ->
    find_method f c.(c_methods) = Some m ->
    Forall (fun xt => valid (fst (fst xt))) (M.elements (instance_methods m)).
Proof.
  unfold instance_methods; intros * WT Find.
  inversion_clear WT as [? WTm].
  apply find_method_In in Find.
  eapply Forall_forall in WTm; eauto.
  eapply valid_rec_instance_methods; eauto.
  - apply c_good.
  - now rewrite elements_empty.
Qed.

Lemma NoDupMembers_make_out_vars:
   forall f m p c,
    wt_class p c ->
    find_method f c.(c_methods) = Some m ->
    NoDupMembers (make_out_vars (instance_methods m)).
Proof.
  intros * WT Find.
  unfold make_out_vars.
  assert (NoDupMembers (M.elements (elt:=ident) (instance_methods m))) as Nodup
      by (rewrite <-setoid_nodup; apply M.elements_3w).
  pose proof (valid_instance_methods _ _ _ _ WT Find) as Valid.
  induction (M.elements (elt:=ident) (instance_methods m)) as [|((o, f'), c')];
    simpl; inversion_clear Nodup as [|? ? ? Notin Nodup'];
      inversion_clear Valid; constructor; auto.
  intro Hin; apply Notin.
  rewrite fst_InMembers, map_map, in_map_iff in Hin.
  destruct Hin as (((o', f''), c'') & Eq & Hin); simpl in *.
  apply prefix_out_injective in Eq; auto; destruct Eq; subst.
  - eapply In_InMembers; eauto.
  - change o' with (fst (fst (o', f'', c''))).
    eapply Forall_forall in Hin; eauto; apply Hin.
Qed.

Remark translate_param_fst:
  forall xs, map fst (map translate_param xs) = map fst xs.
Proof.
  intro; rewrite map_map.
  induction xs as [|(x, t)]; simpl; auto.
  now rewrite IHxs.
Qed.

Remark translate_obj_fst:
  forall objs, map fst (map translate_obj objs) = map fst objs.
Proof.
  intro; rewrite map_map.
  induction objs as [|(o, k)]; simpl; auto.
  now rewrite IHobjs.
Qed.

Lemma NoDupMembers_make_members:
  forall c, NoDupMembers (make_members c).
Proof.
  intro; unfold make_members.
  pose proof (c_nodup c) as Nodup.
  rewrite fst_NoDupMembers.
  rewrite map_app.
  now rewrite translate_param_fst, translate_obj_fst.
Qed.
Hint Resolve NoDupMembers_make_members.

Lemma glob_bind_vardef_fst:
  forall xs env volatile,
    map fst (map (vardef env volatile) (map glob_bind xs)) =
    map (fun xt => glob_id (fst xt)) xs.
Proof.
  induction xs as [|(x, t)]; simpl; intros; auto.
  now rewrite IHxs.
Qed.

Lemma NoDup_glob_id:
  forall {A} (xs: list (ident * A)),
    NoDupMembers xs ->
    Forall (fun x => valid (fst x)) xs ->
    NoDup (map (fun xt => glob_id (fst xt)) xs).
Proof.
  induction xs as [|(x, t)]; simpl;
    inversion_clear 1 as [|? ? ? Notin];
    inversion_clear 1; constructor; auto.
  rewrite in_map_iff; intros ((x', t') & E & Hin); apply Notin.
  simpl in E; apply glob_id_injective in E; auto.
  - subst x'.
    eapply In_InMembers; eauto.
  - eapply Forall_forall in Hin; eauto.
    now simpl in Hin.
Qed.

Lemma NoDup_funs:
  forall prog,
    wt_program prog ->
    NoDup (map fst (concat (map (make_methods (rev prog)) (rev prog)))).
Proof.
  unfold make_methods.
  intros * Wt.
  remember prog as prog'.
  pattern prog' at 2.
  rewrite Heqprog' at 1.
  rewrite Heqprog' in Wt.
  clear Heqprog'.
  unfold program in *.
  induction prog as [|c]; simpl.
  - constructor.
  - inversion_clear Wt as [|? ? ? ? Nodup]; simpl in Nodup;
      inversion_clear Nodup as [|? ? Notinc].
    rewrite map_app, concat_app, map_app. simpl.
    rewrite app_nil_r, map_map, Permutation_app_comm.
    apply NoDup_app'; auto.
    + simpl.
      pose proof (c_nodupm c) as Nodup.
      induction (c_methods c) as [|m]; simpl;
        inversion_clear Nodup as [|? ? Notin]; constructor; auto.
      rewrite in_map_iff; intros (m' & E & Hin); apply Notin.
      pose proof (c_good c).
      apply prefix_fun_injective in E; try tauto; destruct E as [? E]; rewrite <-E.
      rewrite in_map_iff; exists m'; auto.
    + induction (c_methods c) as [|m]; simpl; auto.
      constructor; auto.
      rewrite in_map_iff; intros ((x, d) & E & Hin).
      simpl in E; subst x.
      apply in_concat in Hin; destruct Hin as (l' & Hin' & Hin).
      rewrite in_map_iff in Hin; destruct Hin as (c' & E & Hin); subst l'.
      rewrite in_map_iff in Hin'; destruct Hin' as (m' & E & Hin').
      unfold translate_method in E; inversion E as [[Eq E']]; clear E E'.
      pose proof (c_good c); pose proof (c_good c').
      apply prefix_fun_injective in Eq; try tauto.
      destruct Eq as [Eq].
      apply Notinc.
      rewrite <- Eq.
      now apply in_map, in_rev.
Qed.

Lemma prefixed_funs:
  forall prog f,
    In f (map fst (concat (map (make_methods prog) prog))) ->
    prefixed_fun f.
Proof.
  unfold make_methods.
  intros * Hin.
  remember prog as prog'.
  pattern prog' at 2 in Hin.
  rewrite Heqprog' in Hin at 1; simpl in Hin.
  clear Heqprog'.
  induction prog as [|c]; simpl in *; contr.
  rewrite in_map_iff in Hin; destruct Hin as ((f', d) & E & Hin); simpl in E; subst f'.
  rewrite in_app_iff in Hin; destruct Hin as [Hin|Hin].
  - rewrite in_map_iff in Hin; destruct Hin as (m & E & Hin).
    unfold translate_method in E; inv E; eauto; constructor.
  - apply in_map with (f:=fst) in Hin; auto.
Qed.

Lemma glob_not_in_prefixed:
  forall (xs: list (ident * type)) ps,
    Forall prefixed ps ->
    Forall (fun x => valid (fst x)) xs ->
    Forall (fun z => ~ In z ps) (map (fun xt => glob_id (fst xt)) xs).
Proof.
  induction xs as [|(x, t)]; simpl; intros * Pref Valid; auto.
  inv Valid. constructor; auto.
  intro Hin.
  eapply Forall_forall in Pref; eauto.
  contradict Pref; apply glob_id_not_prefixed; auto.
Qed.

Lemma NoDupMembers_glob:
  forall (ys xs: list (ident * type)),
    NoDupMembers (xs ++ ys) ->
    Forall (fun x => valid (fst x)) (xs ++ ys) ->
    Forall (fun z => ~ In z (map (fun xt => glob_id (fst xt)) xs))
           (map (fun xt => glob_id (fst xt)) ys).
Proof.
  induction ys as [|(y, t)]; simpl; intros * Nodup Valid; auto.
  rewrite NoDupMembers_app_cons in Nodup; destruct Nodup as [Notin Nodup];
    rewrite Forall_app in Valid; destruct Valid as [Validxs Validys];
      rewrite Forall_cons2 in Validys; destruct Validys as [Validy Validys].
  constructor; auto.
  - rewrite in_map_iff; intros ((x, t') & E & Hin).
    simpl in E; apply glob_id_injective in E; auto.
    + subst y.
      apply Notin.
      apply InMembers_app; left; eapply In_InMembers; eauto.
    + eapply Forall_forall in Hin; eauto; now simpl in Hin.
  - apply IHys; auto.
    rewrite Forall_app; split; auto.
Qed.

Lemma self_not_out: self <> out.
Proof.
  intro Eq.
  pose proof reserved_nodup as Nodup.
  unfold reserved in Nodup.
  inversion Nodup as [|? ? Notin]; subst; clear Nodup.
  rewrite Eq in Notin.
  contradict Notin; apply in_eq.
Qed.

Lemma InMembers_rec_instance_methods_temp:
  forall x s prog e,
    InMembers x (Env.elements (rec_instance_methods_temp prog s e)) <->
    InMembers x (Env.elements (rec_instance_methods_temp prog s (Env.empty type)))
    \/ InMembers x (Env.elements e).
Proof.
  induction s; simpl; split; intros Hin; contr; try tauto.
  - rewrite IHs2, IHs1 in *; tauto.
  - rewrite IHs2, IHs1 in *; tauto.
  - rewrite IHs2, IHs1 in *; tauto.
  - rewrite IHs2, IHs1 in *; tauto.
  - destruct (find_class i0 prog) as [(?, ?)|]; simpl in Hin; contr.
    destruct (find_method i2 (c_methods c)); simpl in Hin; contr.
    destruct_list i; simpl in Hin; contr.
    destruct_list (m_out m) as (?, ?) ? ?; simpl in Hin; contr.
    rewrite <-Env.In_Members, Env.Props.P.F.add_in_iff in Hin.
    rewrite <-Env.In_Members, Env.Props.P.F.add_in_iff.
    destruct Hin; try tauto.
    right; rewrite <-Env.In_Members; auto.
  - destruct Hin as [Hin|Hin].
    + destruct (find_class i0 prog) as [(?, ?)|]; simpl in Hin; contr.
      destruct (find_method i2 (c_methods c)); simpl in Hin; contr.
      destruct_list i; simpl in Hin; contr.
      destruct_list (m_out m) as (?, ?) ? ?; simpl in Hin; contr.
      rewrite <-Env.In_Members, Env.Props.P.F.add_in_iff in Hin.
      rewrite <-Env.In_Members, Env.Props.P.F.add_in_iff.
      destruct Hin as [|Hin]; try tauto.
      rewrite Env.In_Members in Hin; contr.
    + destruct (find_class i0 prog) as [(?, ?)|]; auto.
      destruct (find_method i2 (c_methods c)); auto.
      destruct_list i; auto.
      destruct_list (m_out m) as (?, ?) ? ?; auto.
      rewrite <-Env.In_Members in Hin.
      rewrite <-Env.In_Members, Env.Props.P.F.add_in_iff.
      tauto.
Qed.

Lemma make_out_temps_prefixed:
  forall x prog m,
    InMembers x (make_out_temps (instance_methods_temp prog m)) ->
    prefixed x.
Proof.
  unfold make_out_temps, instance_methods_temp.
  intros * Hin.
  induction (m_body m); simpl in *; contr.
  - rewrite InMembers_translate_param_idem in *.
    rewrite InMembers_rec_instance_methods_temp in Hin.
    destruct Hin; auto.
  - rewrite InMembers_translate_param_idem in *.
    rewrite InMembers_rec_instance_methods_temp in Hin.
    destruct Hin; auto.
  - destruct (find_class i0 prog) as [(?, ?)|]; simpl in Hin; contr.
    destruct (find_method i2 (c_methods c)); simpl in Hin; contr.
    destruct_list i; simpl in Hin; contr.
    destruct_list (m_out m0) as (?, ?) ? ?; simpl in Hin; contr.
    rewrite InMembers_translate_param_idem, <-Env.In_Members, Env.Props.P.F.add_in_iff in Hin.
    destruct Hin as [|Hin].
    + subst; constructor.
    + rewrite Env.In_Members in Hin.
      simpl in Hin; contr.
Qed.

Section PRESERVATION.

  Variable main_node : ident.

  Variable prog: program.
  Variable tprog: Clight.program.
  Variable do_sync: bool.
  Variable all_public: bool.

  Let tge := Clight.globalenv tprog.
  Let gcenv := Clight.genv_cenv tge.

  Hypothesis TRANSL: translate do_sync all_public main_node prog = Errors.OK tprog.
  Hypothesis WT: wt_program prog.

  Lemma build_check_size_env_ok:
    forall types gvars gvars_vol defs public main p,
      make_program' types gvars gvars_vol defs public main = Errors.OK p ->
      build_composite_env types = Errors.OK p.(prog_comp_env)
      /\ check_size_env p.(prog_comp_env) types = Errors.OK tt.
  Proof.
    unfold make_program'; intros.
    destruct (build_composite_env' types) as [[gce ?]|?]; try discriminate.
    destruct (check_size_env gce types) eqn: E; try discriminate.
    destruct u; inv H; simpl; split; auto.
  Qed.

  Lemma build_ok:
    forall types gvars gvars_vol defs public main p,
      make_program' types gvars gvars_vol defs public main = Errors.OK p ->
      build_composite_env types = Errors.OK p.(prog_comp_env).
  Proof.
    intros * H.
    apply (proj1 (build_check_size_env_ok _ _ _ _ _ _ _ H)).
  Qed.

  Lemma check_size_env_ok:
    forall types gvars gvars_vol defs public main p,
      make_program' types gvars gvars_vol defs public main = Errors.OK p ->
      check_size_env p.(prog_comp_env) types = Errors.OK tt.
  Proof.
    intros * H.
    apply (proj2 (build_check_size_env_ok _ _ _ _ _ _ _ H)).
  Qed.

  Lemma check_size_ok:
    forall ce types,
      check_size_env ce types = Errors.OK tt ->
      Forall (fun t => match t with
                         Ctypes.Composite id _ _ _ => check_size ce id = Errors.OK tt
                       end) types.
  Proof.
    intros * H.
    induction types as [|(id, su, m, attr) types IH]; auto.
    simpl in H.
    destruct (check_size ce id) eqn: E; try discriminate; destruct u; simpl in H.
    constructor; auto.
  Qed.

  Ltac inv_trans_tac H En Estep Ereset s f E :=
    match type of H with
      translate ?b ?a ?n ?p = Errors.OK ?tp =>
      unfold translate in H;
      destruct (find_class n p) as [(c, cls)|] eqn: En; try discriminate;
      destruct (find_method step c.(c_methods)) eqn: Estep; try discriminate;
      destruct (find_method reset c.(c_methods)) eqn: Ereset; try discriminate;
      destruct (split (map (translate_class (rev p)) (rev p))) as (s, f) eqn: E
    end.

  Tactic Notation "inv_trans" ident(H) "as" ident(En) ident(Estep) ident(Ereset) "with" ident(s) ident(f) ident(E) :=
    inv_trans_tac H En Estep Ereset s f E.
  Tactic Notation "inv_trans" ident(H) "as" ident(En) ident(Estep) ident(Ereset) "with" ident(s) ident(f) :=
    inv_trans H as En Estep Ereset with s f E.
  Tactic Notation "inv_trans" ident(H) "as" ident(En) ident(Estep) ident(Ereset) :=
    inv_trans H as En Estep Ereset with s f.
  Tactic Notation "inv_trans" ident(H) "with" ident(s) ident(f) ident(E) :=
    inv_trans H as En Estep Ereset with s f E.
  Tactic Notation "inv_trans" ident(H) "with" ident(s) ident(f) :=
    inv_trans H as En Estep Ereset with s f E.
  Tactic Notation "inv_trans" ident(H) :=
    inv_trans H as En Estep Ereset.

  Lemma Consistent: composite_env_consistent gcenv.
  Proof.
    inv_trans TRANSL.
    apply build_ok in TRANSL.
    apply build_composite_env_consistent in TRANSL; auto.
  Qed.
  Hint Resolve Consistent.

  Opaque sepconj.

  Inductive occurs_in: stmt -> stmt -> Prop :=
  | occurs_refl: forall s,
      occurs_in s s
  | occurs_ite: forall s e s1 s2,
      occurs_in s s1 \/ occurs_in s s2 ->
      occurs_in s (Ifte e s1 s2)
  | occurs_comp: forall s s1 s2,
      occurs_in s s1 \/ occurs_in s s2 ->
      occurs_in s (Comp s1 s2).
  Hint Resolve occurs_refl.

  Remark occurs_in_ite:
    forall e s1 s2 s,
      occurs_in (Ifte e s1 s2) s ->
      occurs_in s1 s /\ occurs_in s2 s.
  Proof.
    intros * Occurs.
    induction s; inversion_clear Occurs as [|? ? ? ? [Hs1|Hs2]|? ? ? [Hs1|Hs2]];
      split; constructor; ((left; now apply IHs1) || (right; now apply IHs2) || idtac).
    - left; auto.
    - right; auto.
  Qed.

  Remark occurs_in_comp:
    forall s1 s2 s,
      occurs_in (Comp s1 s2) s ->
      occurs_in s1 s /\ occurs_in s2 s.
  Proof.
    intros * Occurs.
    induction s; inversion_clear Occurs as [|? ? ? ? [Hs1|Hs2]|? ? ? [Hs1|Hs2]];
      split; constructor; ((left; now apply IHs1) || (right; now apply IHs2) || idtac).
    - left; auto.
    - right; auto.
  Qed.
  Hint Resolve occurs_in_ite occurs_in_comp.

  Lemma occurs_in_wt:
    forall s s' p insts mems vars,
      wt_stmt p insts mems vars s ->
      occurs_in s' s ->
      wt_stmt p insts mems vars s'.
  Proof.
    induction s; intros * Wt Occ;
      inv Wt; inversion_clear Occ as [|? ? ? ? [?|?]|? ? ? [?|?]];
        try econstructor; eauto.
  Qed.

  Lemma occurs_in_instance_methods:
    forall ys clsid o fid es f p insts mems,
      wt_method p insts mems f ->
      NoDupMembers insts ->
      occurs_in (Call ys clsid o fid es) (m_body f) ->
      (1 < length ys)%nat ->
      M.MapsTo (o, fid) clsid (instance_methods f).
  Proof.
    unfold instance_methods, wt_method.
    intros * Wt Nodup Occurs Length.
    induction (m_body f);
      inversion Occurs as [|? ? ? ? [Hs1|Hs2]|? ? ? [Hs1|Hs2]];
      inversion Wt; subst; simpl.
    - rewrite In_rec_instance_methods; eauto.
      eapply occurs_in_wt in Hs1; eauto.
      inv Hs1; assumption.
    - rewrite In_rec_instance_methods; eauto.
      eapply occurs_in_wt in Hs2; eauto.
      inv Hs2; assumption.
    - rewrite In_rec_instance_methods; eauto.
      eapply occurs_in_wt in Hs1; eauto.
      inv Hs1; assumption.
    - rewrite In_rec_instance_methods; eauto.
      eapply occurs_in_wt in Hs2; eauto.
      inv Hs2; assumption.
    - destruct i as [|i is]; try destruct is.
      + contradict Length; apply lt_n_0.
      + contradict Length; simpl; apply lt_irrefl.
      + apply M.add_1; auto.
  Qed.

  Lemma prog_defs_norepet:
    list_norepet (map fst (prog_defs tprog)).
  Proof.
    inv_trans TRANSL with structs funs Eq.
    unfold make_program' in TRANSL.
    destruct (build_composite_env' (concat structs)) as [(ce, P)|];
      try discriminate.
    destruct (check_size_env ce (concat structs)); try discriminate.
    unfold translate_class in Eq.
    apply split_map in Eq; destruct Eq as [? Funs].
    inversion_clear TRANSL; simpl.
    rewrite 4 map_app, <-app_assoc, <-NoDup_norepet.
    repeat rewrite glob_bind_vardef_fst; simpl.
    assert ( ~ In (glob_id self)
               (map (fun xt => glob_id (fst xt)) (m_out m) ++
                map (fun xt => glob_id (fst xt)) (m_in m) ++
                map fst (concat funs) ++
                map fst
                ((if do_sync
                  then [(sync_id, make_sync); (main_sync_id, make_main do_sync main_node m)]
                  else [])
                   ++ [(main_id, make_main false main_node m)]))) as Notin_self.
    { pose proof (m_notreserved self m (in_eq self _)) as Res; unfold meth_vars in Res.
      repeat rewrite in_app_iff, in_map_iff; simpl;
        intros [((x, t) & E & Hin)
               |[((x, t) & E & Hin)
                |[((x, t) & E & Hin)
                 |Hin]]];
        try simpl in E.
      - apply glob_id_injective in E.
        + subst x.
          apply In_InMembers in Hin.
          apply Res; now repeat (rewrite InMembers_app; right).
        + apply (m_good_out m (x, t)); auto.
        + apply self_valid.
      - apply glob_id_injective in E.
        + subst x.
          apply In_InMembers in Hin.
          apply Res; now rewrite InMembers_app; left.
        + apply (m_good_in m (x, t)); auto.
        + apply self_valid.
      - subst x.
        apply in_map with (f:=fst) in Hin.
        subst funs. apply prefixed_funs, prefixed_fun_prefixed in Hin.
        contradict Hin; apply glob_id_not_prefixed.
        apply self_valid.
      - destruct do_sync; simpl in Hin.
        + destruct Hin as [Hin|[Hin|[Hin|]]]; contr;
            try (apply pos_of_str_injective in Hin;
                 unfold self in Hin; rewrite pos_to_str_equiv in Hin;
                 inv Hin).
        + destruct Hin as [Hin|]; contr.
          apply pos_of_str_injective in Hin;
            unfold self in Hin; rewrite pos_to_str_equiv in Hin;
              inv Hin.
    }
    assert (NoDup (map (fun xt => glob_id (fst xt)) (m_out m) ++
                   map (fun xt => glob_id (fst xt)) (m_in m) ++
                   map fst (concat funs) ++
                   map fst
                   ((if do_sync
                     then [(sync_id, make_sync); (main_sync_id, make_main do_sync main_node m)]
                     else [])
                      ++ [(main_id, make_main false main_node m)]))) as Nodup.
    { assert (Forall (fun x : ident * type => valid (fst x)) (m_out m)) as Valid_out
        by (rewrite Forall_forall; intros (x, t) ?; apply (m_good_out m (x, t)); auto).
      assert (Forall (fun x : ident * type => valid (fst x)) (m_in m)) as Valid_in
        by (rewrite Forall_forall; intros (x, t) ?; apply (m_good_in m (x, t)); auto).
      assert (NoDup (map (fun xt => glob_id (fst xt)) (m_out m))) as Hm_out
          by (apply NoDup_glob_id; auto; apply m_nodupout).
      assert (NoDup (map (fun xt => glob_id (fst xt)) (m_in m))) as Hm_in
          by (apply NoDup_glob_id; auto; apply m_nodupin).
      assert (NoDup (map fst (concat funs))) by (rewrite Funs; now apply NoDup_funs).
      assert (Forall (fun z  => ~ In z (map fst (concat funs)))
                     (map (fun xt => glob_id (fst xt)) (m_in m))) as Hin_not_funs.
      { apply glob_not_in_prefixed; auto.
        apply Forall_forall; intros * Hin.
        apply prefixed_fun_prefixed; subst funs.
        now apply prefixed_funs in Hin.
      }
      assert (Forall (fun z => ~ In z (map fst (concat funs)))
                     (map (fun xt => glob_id (fst xt)) (m_out m))) as Hout_not_funs.
      { apply glob_not_in_prefixed; auto.
        apply Forall_forall; intros * Hin.
        apply prefixed_fun_prefixed; subst funs.
        now apply prefixed_funs in Hin.
      }
      assert (Forall (fun z => ~ In z (map (fun xt => glob_id (fst xt)) (m_in m)))
                     (map (fun xt => glob_id (fst xt)) (m_out m))) as Hout_not_in.
      { apply NoDupMembers_glob.
        - pose proof (m_nodupvars m) as Nodup.
          rewrite Permutation_app_comm, <-app_assoc in Nodup.
          now apply NoDupMembers_app_r in Nodup; rewrite Permutation_app_comm in Nodup.
        - rewrite Forall_app; split; auto.
      }
      destruct do_sync; simpl;
        try change [sync_id; main_sync_id; main_id] with ([sync_id]++[main_sync_id]++[main_id]);
        repeat apply NoDup_app'; repeat apply Forall_not_In_app;
          repeat apply Forall_not_In_singleton;
          ((repeat constructor; auto)
           || (intros [E|]; contr;
              apply pos_of_str_injective in E; inv E)
           || (intro Hin; subst funs; apply prefixed_funs in Hin;
              inversion Hin as [? ? E];
              unfold prefix_fun, fun_id in E;
              apply pos_of_str_injective in E; rewrite pos_to_str_equiv in E;
              inv E)
           || (match goal with
                |- ~ In _ (map (fun xt => glob_id (fst xt)) ?xs) =>
                clear Notin_self Hm_out Hm_in Hin_not_funs Hout_not_funs Hout_not_in;
                induction xs as [|(x, t)]; simpl; auto;
                intros [Hin|Hin]; contr
              end)
           || auto);
          try (eapply main_not_glob; now eauto);
          try (eapply sync_not_glob; now eauto);
          try (eapply main_sync_not_glob; now eauto);
          try (inv Valid_in; now apply IHl);
          try (inv Valid_out; now apply IHl).
    }
    repeat constructor; auto.
  Qed.
  Hint Resolve prog_defs_norepet.

  Section ClassProperties.
    Variables (ownerid: ident) (owner: class) (prog': program).
    Hypothesis Findcl: find_class ownerid prog = Some (owner, prog').

    Lemma make_members_co:
      exists co,
        gcenv ! ownerid = Some co
        /\ co_su co = Struct
        /\ co_members co = make_members owner
        /\ attr_alignas (co_attr co) = None
        /\ NoDupMembers (co_members co)
        /\ co.(co_sizeof) <= Int.max_unsigned.
    Proof.
      inv_trans TRANSL with structs funs E.
      pose proof (find_class_name _ _ _ _ Findcl); subst.
      apply build_check_size_env_ok in TRANSL; destruct TRANSL as [? SIZE].
      assert (In (Composite (c_name owner) Struct (make_members owner) noattr) (concat structs)).
      { unfold translate_class in E.
        apply split_map in E.
        destruct E as [Structs].
        unfold make_struct in Structs.
        apply find_class_In, in_rev in Findcl.
        apply in_map with (f:=fun c => Composite (c_name c) Struct (make_members c) noattr :: make_out c)
          in Findcl.
        apply in_concat' with (Composite (c_name owner) Struct (make_members owner) noattr :: make_out owner).
        - apply in_eq.
        - now rewrite Structs.
      }
      edestruct build_composite_env_charact as (co & Hco & Hmembers & Hattr & ?); eauto.
      exists co; repeat split; auto.
      - rewrite Hattr; auto.
      - rewrite Hmembers. apply NoDupMembers_make_members.
      - eapply check_size_ok, Forall_forall in SIZE; eauto; simpl in SIZE.
        unfold check_size in SIZE; rewrite Hco in SIZE.
        destruct (co_sizeof co <=? Int.max_unsigned) eqn: Le; contr.
        rewrite Zle_is_le_bool; auto.
    Qed.

    Section MethodProperties.
      Variables (callerid: ident) (caller: method).
      Hypothesis Findmth: find_method callerid owner.(c_methods) = Some caller.

      Section OutStruct.
        Hypothesis Length: (1 < length caller.(m_out))%nat.

        Lemma global_out_struct:
          exists co,
            gcenv ! (prefix_fun (c_name owner) (m_name caller)) = Some co
            /\ co.(co_su) = Struct
            /\ co.(co_members) = map translate_param caller.(m_out)
            /\ co.(co_attr) = noattr
            /\ NoDupMembers (co_members co)
            /\ co.(co_sizeof) <= Int.max_unsigned.
        Proof.
          inv_trans TRANSL with structs funs E.
          apply build_check_size_env_ok in TRANSL; destruct TRANSL as [? SIZE].
          assert (In (Composite
                        (prefix_fun (c_name owner) (m_name caller))
                        Struct
                        (map translate_param caller.(m_out))
                        noattr) (concat structs)).
          { unfold translate_class in E.
            apply split_map in E.
            destruct E as [Structs].
            unfold make_out in Structs.
            apply find_class_In, in_rev in Findcl.
            apply in_map with (f:=fun c => make_struct c :: filter_out (map (translate_out c) (c_methods c)))
              in Findcl.
            apply find_method_In in Findmth.
            assert (In (translate_out owner caller) (filter_out (map (translate_out owner) (c_methods owner))))
              as Hin.
            { unfold filter_out.
              rewrite filter_In; split.
              - apply in_map; auto.
              - unfold translate_out.
                destruct_list caller.(m_out); simpl; auto; try contradict Length; simpl.
                + apply lt_n_0.
                + apply lt_irrefl.
            }
            unfold translate_out at 1 in Hin.
            eapply in_concat_cons; eauto.
            rewrite Structs; eauto.
          }
          edestruct build_composite_env_charact as (co & Hco & Hmembers & ? & ?); eauto.
          exists co; repeat (split; auto).
          - rewrite Hmembers, fst_NoDupMembers, translate_param_fst, <- fst_NoDupMembers.
            apply (m_nodupout caller).
          - eapply check_size_ok, Forall_forall in SIZE; eauto; simpl in SIZE.
            unfold check_size in SIZE; rewrite Hco in SIZE.
            destruct (co_sizeof co <=? Int.max_unsigned) eqn: Le; contr.
            rewrite Zle_is_le_bool; auto.
        Qed.

        Remark output_match:
          forall outco,
            gcenv ! (prefix_fun (c_name owner) (m_name caller)) = Some outco ->
            map translate_param caller.(m_out) = outco.(co_members).
        Proof.
          intros * Houtco.
          edestruct global_out_struct as (outco' & Houtco' & Eq); eauto.
          rewrite Houtco in Houtco'; now inv Houtco'.
        Qed.

      End OutStruct.

      Lemma well_formed_instance_methods:
        forall o fid cid,
          In (o, cid) owner.(c_objs) ->
          M.MapsTo (o, fid) cid (instance_methods caller) ->
          exists c cls callee,
            find_class cid prog = Some (c, cls)
            /\ find_method fid (c_methods c) = Some callee
            /\ (1 < length callee.(m_out))%nat.
      Proof.
        intros * Ho Hin.
        pose proof (find_class_name _ _ _ _ Findcl) as Eq.
        pose proof (find_method_name _ _ _ Findmth) as Eq'.
        edestruct wt_program_find_class as [WT']; eauto.
        eapply wt_class_find_method in WT'; eauto.
        unfold instance_methods in Hin.
        unfold wt_method in WT'.
        pose proof (c_nodupobjs owner).
        induction (m_body caller); simpl in *;
          try (apply M.find_1 in Hin; discriminate); inv WT'.
        - rewrite In_rec_instance_methods in Hin; eauto. destruct Hin.
          + apply IHs2; auto.
          + apply IHs1; auto.
        - rewrite In_rec_instance_methods in Hin; eauto. destruct Hin.
          + apply IHs2; auto.
          + apply IHs1; auto.
        - destruct_list i.
          + apply M.find_1 in Hin; contr.
          + apply M.find_1 in Hin; contr.
          + destruct (M.E.eq_dec (i1, i2) (o, fid)) as [[E1 E2]|E1]; simpl in *.
            *{ subst.
               apply MapsTo_add_same in Hin; subst.
               exists cls, p', fm; repeat split; auto.
               - apply find_class_sub in Findcl.
                 eapply find_class_sub_same; eauto.
               - destruct_list fm.(m_out).
                 + inv H10.
                 + inv H10; inv H13.
                 + simpl; omega.
             }
            * apply M.add_3, M.find_1 in Hin; simpl; auto; discriminate.
      Qed.

      Lemma methods_corres:
        exists loc_f f,
          Genv.find_symbol tge (prefix_fun ownerid callerid) = Some loc_f
          /\ Genv.find_funct_ptr tge loc_f = Some (Internal f)
          /\ f.(fn_params) = (self, type_of_inst_p owner.(c_name))
                              :: match caller.(m_out) with
                                 | [] | [_] => map translate_param caller.(m_in)
                                 | _ => (out, type_of_inst_p (prefix_fun owner.(c_name) caller.(m_name)))
                                         :: (map translate_param caller.(m_in))
                                 end
          /\ f.(fn_return) = match caller.(m_out) with
                            | [(_, t)] => cltype t
                            | _ => Tvoid
                            end
          /\ f.(fn_callconv) = AST.cc_default
          /\ f.(fn_vars) = make_out_vars (instance_methods caller)
          /\ f.(fn_temps) = match caller.(m_out) with
                            | [yt] => [translate_param yt]
                            | _ => []
                           end
                             ++ make_out_temps (instance_methods_temp (rev prog) caller)
                             ++ map translate_param caller.(m_vars)
          /\ list_norepet (var_names f.(fn_params))
          /\ list_norepet (var_names f.(fn_vars))
          /\ list_disjoint (var_names f.(fn_params)) (var_names f.(fn_temps))
          /\ f.(fn_body) = match caller.(m_out) with
                          | [yt] => return_some (translate_stmt (rev prog) owner caller caller.(m_body)) (make_in_arg yt)
                          | _ => return_none (translate_stmt (rev prog) owner caller caller.(m_body))
                          end.
      Proof.
        pose proof prog_defs_norepet as Norepet.
        inv_trans TRANSL with structs funs E.
        pose proof (find_class_name _ _ _ _ Findcl);
          pose proof (find_method_name _ _ _ Findmth); subst.
        assert ((AST.prog_defmap tprog) ! (prefix_fun owner.(c_name) caller.(m_name)) =
                Some (snd (translate_method (rev prog) owner caller))) as Hget.
        { unfold translate_class in E.
          apply split_map in E.
          destruct E as [? Funs].
          unfold make_methods in Funs.
          apply find_class_In in Findcl.
          apply in_rev, in_map with (f:=fun c => map (translate_method (rev prog) c) (c_methods c))
            in Findcl.
          apply find_method_In in Findmth.
          apply in_map with (f:=translate_method (rev prog) owner) in Findmth.
          eapply in_concat' in Findmth; eauto.
          rewrite <-Funs in Findmth.
          unfold make_program' in TRANSL.
          destruct (build_composite_env' (concat structs)) as [(ce, P)|]; contr.
          destruct (check_size_env ce (concat structs)); contr.
          unfold AST.prog_defmap; simpl.
          apply PTree_Properties.of_list_norepet; auto.
          inversion_clear TRANSL.
          apply in_cons, in_app; right; apply in_app; left.
          unfold translate_method in Findmth; auto.
        }
        apply Genv.find_def_symbol in Hget.
        destruct Hget as (loc_f & Findsym & Finddef).
        simpl in Finddef.
        unfold fundef in Finddef.
        assert (list_norepet (var_names ((self, type_of_inst_p owner.(c_name))
                                           :: (out, type_of_inst_p (prefix_fun owner.(c_name) caller.(m_name)))
                                           :: (map translate_param caller.(m_in))
               ))) as H1.
        { unfold var_names.
          rewrite <-NoDup_norepet, <-fst_NoDupMembers.
          constructor.
          - intro Hin; simpl in Hin; destruct Hin as [Eq|Hin].
            + now apply self_not_out.
            + apply (m_notreserved self caller).
              * apply in_eq.
              * apply InMembers_app; left.
                rewrite fst_InMembers, translate_param_fst, <-fst_InMembers in Hin; auto.
          - constructor.
            + intro Hin.
              apply (m_notreserved out caller).
              * apply in_cons, in_eq.
              * apply InMembers_app; left.
                rewrite fst_InMembers, translate_param_fst, <-fst_InMembers in Hin; auto.
            + pose proof (m_nodupvars caller) as Nodup.
              apply NoDupMembers_app_l in Nodup.
              rewrite fst_NoDupMembers, translate_param_fst, <-fst_NoDupMembers; auto.
        }
        assert (list_norepet (var_names ((self, type_of_inst_p owner.(c_name))
                                           :: (map translate_param caller.(m_in))
               ))).
        { unfold var_names.
          rewrite <-NoDup_norepet, <-fst_NoDupMembers, cons_is_app.
          unfold var_names in H1.
          rewrite <-NoDup_norepet, <-fst_NoDupMembers, cons_is_app in H1.
          eapply NoDupMembers_remove_1; eauto.
        }
        assert (list_norepet (var_names (make_out_vars (instance_methods caller)))).
        { unfold var_names.
          rewrite <-NoDup_norepet, <-fst_NoDupMembers.
          eapply NoDupMembers_make_out_vars; eauto.
          eapply wt_program_find_class; eauto.
        }
        assert (NoDupMembers (m_in caller ++ Env.elements (instance_methods_temp (rev prog) caller) ++ m_vars caller)) as Nodup'.
        { pose proof (m_nodupvars caller) as Nodup.
          apply NoDupMembers_app.
          - apply NoDupMembers_app_l in Nodup; auto.
          - apply NoDupMembers_app.
            + apply Env.NoDupMembers_elements.
            + apply NoDupMembers_app_r, NoDupMembers_app_l in Nodup; auto.
            + intros x Hin.
              pose proof (make_out_temps_prefixed x (rev prog) caller) as Pref.
              unfold make_out_temps in Pref;
                rewrite InMembers_translate_param_idem in Pref.
              apply Pref, (m_notprefixed x caller) in Hin.
              unfold meth_vars in Hin; repeat rewrite NotInMembers_app in Hin; tauto.
          - intros x Hin.
            rewrite NotInMembers_app; split.
            * apply (NoDupMembers_app_InMembers x) in Nodup; auto.
              apply NotInMembers_app in Nodup; tauto.
            * pose proof (make_out_temps_prefixed x (rev prog) caller) as Pref.
              unfold make_out_temps in Pref;
                rewrite InMembers_translate_param_idem in Pref.
              intro Hin'; apply Pref, (m_notprefixed x caller) in Hin'.
              unfold meth_vars in Hin'; repeat rewrite NotInMembers_app in Hin'.
              contradict Hin; tauto.
        }

        assert (~In self (var_names (make_out_temps (instance_methods_temp (rev prog) caller) ++ map translate_param (m_vars caller)))).
        { unfold var_names; rewrite <-fst_InMembers, NotInMembers_app; split; simpl.
          - rewrite InMembers_translate_param_idem.
            intro Hin.
            apply (m_notreserved self caller).
            + apply in_eq.
            + unfold meth_vars. repeat rewrite InMembers_app; tauto.
          - intro Hin. apply make_out_temps_prefixed in Hin.
            apply self_not_prefixed; auto.
        }

        assert (list_disjoint (var_names ((self, type_of_inst_p owner.(c_name))
                                           :: (out, type_of_inst_p (prefix_fun owner.(c_name) caller.(m_name)))
                                           :: (map translate_param caller.(m_in))))
                              (var_names (make_out_temps (instance_methods_temp (rev prog) caller)
                                                         ++ map translate_param caller.(m_vars)))).
        { repeat apply list_disjoint_cons_l; auto.
          - apply NoDupMembers_disjoint.
            pose proof (m_nodupvars caller) as Nodup.
            unfold make_out_temps.
            rewrite fst_NoDupMembers; repeat rewrite map_app; repeat rewrite translate_param_fst.
            simpl; rewrite <-2map_app, <-fst_NoDupMembers; auto.
          - unfold var_names; rewrite <-fst_InMembers, NotInMembers_app; split; simpl.
            + rewrite InMembers_translate_param_idem.
              intro Hin.
              apply (m_notreserved out caller).
              * apply in_cons, in_eq.
              * unfold meth_vars. repeat rewrite InMembers_app; tauto.
            + intro Hin. apply make_out_temps_prefixed in Hin.
              apply out_not_prefixed; auto.
        }
        assert (list_disjoint (var_names ((self, type_of_inst_p owner.(c_name))
                                            :: (map translate_param caller.(m_in))))
                              (var_names (make_out_temps (instance_methods_temp (rev prog) caller)
                                                         ++ map translate_param caller.(m_vars)))).
         { repeat apply list_disjoint_cons_l; auto.
           apply NoDupMembers_disjoint.
           pose proof (m_nodupvars caller) as Nodup.
           unfold make_out_temps.
           rewrite fst_NoDupMembers; repeat rewrite map_app; repeat rewrite translate_param_fst.
           simpl; rewrite <-2map_app, <-fst_NoDupMembers; auto.
         }

        destruct_list caller.(m_out) as (y, t) ? ? : Out.
        - set (f:= {|
                    fn_return := Tvoid;
                    fn_callconv := AST.cc_default;
                    fn_params := (self, type_of_inst_p (c_name owner)) :: map translate_param (m_in caller);
                    fn_vars := make_out_vars (instance_methods caller);
                    fn_temps := make_out_temps (instance_methods_temp (rev prog) caller)
                                ++ map translate_param (m_vars caller);
                    fn_body := return_none (translate_stmt (rev prog) owner caller (m_body caller)) |})
            in Finddef.
          exists loc_f, f.
          try repeat split; auto.
          change (Genv.find_funct_ptr tge loc_f) with (Genv.find_funct_ptr (Genv.globalenv tprog) loc_f).
          unfold Genv.find_funct_ptr.
          change (Genv.find_def (Genv.globalenv tprog) loc_f)
          with ((@Genv.find_def Clight.fundef Ctypes.type
                                (@Genv.globalenv Clight.fundef Ctypes.type (@program_of_program function tprog)) loc_f)).
          now rewrite Finddef.
        - set (f:= {|
                    fn_return := cltype t;
                    fn_callconv := AST.cc_default;
                    fn_params := (self, type_of_inst_p (c_name owner))
                                   :: map translate_param (m_in caller);
                    fn_vars := make_out_vars (instance_methods caller);
                    fn_temps := translate_param (y, t)
                                :: make_out_temps (instance_methods_temp (rev prog) caller) ++
                                   map translate_param (m_vars caller);
                    fn_body := return_some (translate_stmt (rev prog) owner caller (m_body caller))
                                           (make_in_arg (y, t)) |})
            in Finddef.
          exists loc_f, f.
          try repeat split; auto.
          change (Genv.find_funct_ptr tge loc_f) with (Genv.find_funct_ptr (Genv.globalenv tprog) loc_f).
          unfold Genv.find_funct_ptr.
          change (Genv.find_def (Genv.globalenv tprog) loc_f)
          with ((@Genv.find_def Clight.fundef Ctypes.type
                                (@Genv.globalenv Clight.fundef Ctypes.type (@program_of_program function tprog)) loc_f)).
          now rewrite Finddef.
          simpl in *.
          apply list_disjoint_cons_r; auto.
          intros [Eq|Hin].
          + apply (m_notreserved y caller).
            * rewrite <-Eq; apply in_eq.
            * unfold meth_vars; repeat rewrite InMembers_app.
              rewrite Out; right; right; apply inmembers_eq.
          + pose proof (m_nodupvars caller) as Nodup.
            unfold var_names in Hin. rewrite <-fst_InMembers, InMembers_translate_param_idem in Hin.
            apply (NoDupMembers_app_InMembers y) in Nodup; auto.
            apply Nodup; rewrite InMembers_app, Out; right; apply inmembers_eq.

        - set (f:= {|
                    fn_return := Tvoid;
                    fn_callconv := AST.cc_default;
                    fn_params := (self, type_of_inst_p (c_name owner))
                                   :: (out, type_of_inst_p (prefix_fun (c_name owner) (m_name caller)))
                                   :: map translate_param (m_in caller);
                    fn_vars := make_out_vars (instance_methods caller);
                    fn_temps := make_out_temps (instance_methods_temp (rev prog) caller) ++
                                map translate_param (m_vars caller);
                    fn_body := return_none (translate_stmt (rev prog) owner caller (m_body caller)) |})
            in Finddef.
          exists loc_f, f.
          try repeat split; auto.
          change (Genv.find_funct_ptr tge loc_f) with (Genv.find_funct_ptr (Genv.globalenv tprog) loc_f).
          unfold Genv.find_funct_ptr.
          change (Genv.find_def (Genv.globalenv tprog) loc_f)
          with ((@Genv.find_def Clight.fundef Ctypes.type
                                (@Genv.globalenv Clight.fundef Ctypes.type (@program_of_program function tprog)) loc_f)).
          now rewrite Finddef.
      Qed.

    End MethodProperties.
  End ClassProperties.

  Hint Resolve make_members_co.

  Lemma param_chunk:
    forall m x t,
      In (x, t) (map translate_param m.(m_out)) ->
      exists chunk : AST.memory_chunk,
        access_mode t = By_value chunk /\
        (align_chunk chunk | alignof gcenv t).
  Proof.
    intros * Hinxt.
    unfold translate_param in Hinxt.
    apply in_map_iff in Hinxt;
      destruct Hinxt as ((x', t') & Eq & Hinxt); inv Eq.
    destruct t'; simpl.
    - destruct i, s; econstructor; split; eauto.
    - econstructor; split; eauto.
    - destruct f; econstructor; split; eauto;
        try match goal with |- (align_chunk AST.Mfloat64 | align_attr noattr 8) =>
                            exists 2; auto end.
  Qed.
  Hint Resolve param_chunk.

  Lemma instance_methods_caract:
    forall ownerid owner prog' callerid caller,
      find_class ownerid prog = Some (owner, prog') ->
      find_method callerid owner.(c_methods) = Some caller ->
      Forall (fun xt => sizeof tge (snd xt) <= Int.max_unsigned /\
                        (exists (id : AST.ident) (co : composite),
                            snd xt = Tstruct id noattr /\
                            gcenv ! id = Some co /\
                            co_su co = Struct /\
                            NoDupMembers (co_members co) /\
                            (forall (x' : AST.ident) (t' : Ctypes.type),
                                In (x', t') (co_members co) ->
                                exists chunk : AST.memory_chunk,
                                  access_mode t' = By_value chunk /\
                                  (align_chunk chunk | alignof gcenv t'))))
             (make_out_vars (instance_methods caller)).
  Proof.
    intros * Findcl Findmth.
    edestruct wt_program_find_class as [WT']; eauto.
    eapply wt_class_find_method in WT'; eauto.
    induction_list (make_out_vars (instance_methods caller)) as [|(inst, t)] with vars; simpl; auto.
    constructor; auto.
    assert (In (inst, t) (make_out_vars (instance_methods caller))) as Hin
        by (rewrite Hvars; apply in_app; left; apply in_app; right; apply in_eq).
    unfold make_out_vars in Hin; apply in_map_iff in Hin;
      destruct Hin as (((o, fid), cid) & E & Hin); inversion E; subst inst t; clear E.
    rewrite <-setoid_in_key_elt in Hin; apply M.elements_2 in Hin.
    assert (In (o, cid) (c_objs owner)) by (eapply In_instance_methods_In_insts; eauto).
    edestruct well_formed_instance_methods as (c & cls & callee & Findc & Findcallee & Notnil); eauto.
    clear IHvars.
    pose proof (find_class_name _ _ _ _ Findc);
      pose proof (find_method_name _ _ _ Findcallee); subst.
    clear Findmth.
    edestruct global_out_struct as (co & Hco & ? & Hmembers & ? & ? & ?);
      try reflexivity; eauto.
    split.
    * simpl; change (prog_comp_env tprog) with gcenv.
      rewrite Hco; auto.
    * exists (prefix_fun (c_name c) (m_name callee)), co.
      repeat split; auto.
      rewrite Hmembers; eauto.
  Qed.

  Lemma type_pres:
    forall c m e, Clight.typeof (translate_exp c m e) = cltype (typeof e).
  Proof.
    induction e as [| |cst| | |]; simpl; auto.
    - destruct_list m.(m_out); auto.
      case_eq (mem_assoc_ident i (x :: y :: xs)); simpl;
        intro H; rewrite H; auto.
    - destruct cst; simpl; reflexivity.
    - destruct u; auto.
  Qed.

  Lemma acces_cltype:
    forall t, access_mode (cltype t) = By_value (type_chunk t).
  Proof.
    destruct t;
      (destruct i, s || destruct f || idtac); reflexivity.
  Qed.

  Hint Resolve wt_val_load_result acces_cltype.
  Hint Constructors wt_stmt.

  Definition c_state := (Clight.env * Clight.temp_env)%type.

  Definition subrep_inst (xbt: ident * (block * Ctypes.type)) :=
    let '(_, (b, t)) := xbt in
    match t with
    | Tstruct id _ =>
      match gcenv ! id with
      | Some co =>
        blockrep gcenv vempty (co_members co) b
      | None => sepfalse
      end
    | _ => sepfalse
    end.

  Definition subrep_inst_env e (xt: ident * Ctypes.type) :=
    let (x, t) := xt in
    match e ! x with
    | Some (b, Tstruct id _ as t') =>
      if (type_eq t t') then
        match gcenv ! id with
        | Some co =>
          blockrep gcenv vempty (co_members co) b
        | None => sepfalse
        end
      else sepfalse
    | _ => sepfalse
    end.

  Definition drop_block (xbt: ident * (block * Ctypes.type)) :=
    let '(x, (b, t)) := xbt in
    (x, t).

  Definition subrep (f: method) (e: Clight.env) :=
    sepall (subrep_inst_env e)
           (make_out_vars (instance_methods f)).

  Lemma subrep_eqv:
    forall f e,
      Permutation (make_out_vars (instance_methods f))
                  (map drop_block (PTree.elements e)) ->
      subrep f e <-*-> sepall subrep_inst (PTree.elements e).
  Proof.
    intros * Permut.
    unfold subrep.
    rewrite Permut.
    clear Permut.
    induction_list (PTree.elements e) as [|(x, (b, t))] with elems;
      simpl; auto.
    apply sepconj_eqv.
    - assert (e ! x = Some (b, t)) as Hx
          by (apply PTree.elements_complete; rewrite Helems;
              apply in_app; left; apply in_app; right; apply in_eq).
      rewrite Hx; auto.
      destruct t; auto.
      now rewrite type_eq_refl.
    - eapply IHelems; eauto.
  Qed.

  Definition range_inst (xbt: ident * (block * Ctypes.type)):=
    let '(x, (b, t)) := xbt in
    range b 0 (Ctypes.sizeof tge t).

  Definition range_inst_env e x :=
    match e ! x with
    | Some (b, t) => range b 0 (Ctypes.sizeof tge t)
    | None => sepfalse
    end.

  Definition subrep_range (e: Clight.env) :=
    sepall range_inst (PTree.elements e).

  Lemma subrep_range_eqv:
    forall e,
      subrep_range e <-*->
                   sepall (range_inst_env e) (map fst (PTree.elements e)).
  Proof.
    intro e.
    unfold subrep_range.
    induction_list (PTree.elements e) as [|(x, (b, t))] with elems; auto; simpl.
    apply sepconj_eqv.
    - unfold range_inst_env.
      assert (In (x, (b, t)) (PTree.elements e)) as Hin
          by (rewrite Helems; apply in_or_app; left; apply in_or_app; right; apply in_eq).
      apply PTree.elements_complete in Hin.
      now rewrite Hin.
    - apply IHelems.
  Qed.

  Remark decidable_footprint_subrep_inst:
    forall x, decidable_footprint (subrep_inst x).
  Proof.
    intros (x, (b, t)).
    simpl; destruct t; auto. now destruct gcenv ! i.
  Qed.

  Lemma decidable_subrep:
    forall f e, decidable_footprint (subrep f e).
  Proof.
    intros.
    unfold subrep.
    induction (make_out_vars (instance_methods f)) as [|(x, t)]; simpl; auto.
    apply decidable_footprint_sepconj; auto.
    destruct (e ! x) as [(b, t')|]; auto.
    destruct t'; auto.
    destruct (type_eq t (Tstruct i a)); auto.
    now destruct (gcenv ! i).
  Qed.

  Remark footprint_perm_subrep_inst:
    forall x b lo hi,
      footprint_perm (subrep_inst x) b lo hi.
  Proof.
    intros (x, (b, t)) b' lo hi.
    simpl; destruct t; auto. now destruct gcenv ! i.
  Qed.

  Remark disjoint_footprint_range_inst:
    forall l b lo hi,
      ~ InMembers b (map snd l) ->
      disjoint_footprint (range b lo hi) (sepall range_inst l).
  Proof.
    induction l as [|(x, (b', t'))]; simpl;
      intros b lo hi Notin.
    - apply sepemp_disjoint.
    - rewrite disjoint_footprint_sepconj; split.
      + intros blk ofs Hfp Hfp'.
        apply Notin.
        left.
        simpl in *.
        destruct Hfp', Hfp.
        now transitivity blk.
      + apply IHl.
        intro; apply Notin; now right.
  Qed.

  Hint Resolve decidable_footprint_subrep_inst decidable_subrep footprint_perm_subrep_inst.

  Lemma range_wand_equiv:
    forall e,
      Forall (fun xt: ident * Ctypes.type =>
                exists id co,
                  snd xt = Tstruct id noattr
                  /\ gcenv ! id = Some co
                  /\ co_su co = Struct
                  /\ NoDupMembers (co_members co)
                  /\ forall x' t',
                      In (x', t') (co_members co) ->
                      exists chunk : AST.memory_chunk,
                        access_mode t' = By_value chunk /\
                        (align_chunk chunk | alignof gcenv t'))
             (map drop_block (PTree.elements e)) ->
      NoDupMembers (map snd (PTree.elements e)) ->
      subrep_range e <-*->
                   sepall subrep_inst (PTree.elements e)
                   ** (sepall subrep_inst (PTree.elements e) -* subrep_range e).
  Proof.
    unfold subrep_range.
    intros * Forall Nodup.
    split.
    2: now (rewrite sep_unwand; auto).
    induction (PTree.elements e) as [|(x, (b, t))]; simpl in *.
    - rewrite <-hide_in_sepwand; auto.
      now rewrite <-sepemp_right.
    - inversion_clear Forall as [|? ? Hidco Forall']; subst;
        rename Forall' into Forall.
      destruct Hidco as (id & co & Ht & Hco & ? & ? & ?); simpl in Ht.
      inversion_clear Nodup as [|? ? ? Notin Nodup'].
      rewrite Ht, Hco.
      rewrite sep_assoc.
      rewrite IHl at 1; auto.
      rewrite <-unify_distinct_wands; auto.
      + repeat rewrite <-sep_assoc.
        apply sep_imp'; auto.
        rewrite sep_comm, sep_assoc, sep_swap.
        apply sep_imp'; auto.
        simpl range_inst.
        rewrite <-range_imp_with_wand; auto.
        simpl.
        change ((prog_comp_env tprog) ! id) with (gcenv ! id).
        rewrite Hco.
        eapply blockrep_empty; eauto.
      + now apply disjoint_footprint_range_inst.
      + simpl. change ((prog_comp_env tprog) ! id) with (gcenv ! id); rewrite Hco.
        rewrite blockrep_empty; eauto.
        reflexivity.
      + apply subseteq_footprint_sepall.
        intros (x', (b', t')) Hin; simpl.
        assert (In (x', t') (map drop_block l))
          by (change (x', t') with (drop_block (x', (b', t'))); apply in_map; auto).
        eapply Forall_forall in Forall; eauto.
        simpl in Forall.
        destruct Forall as (id' & co' & Ht' & Hco' & ? & ? & ?).
        rewrite Ht', Hco'. simpl.
        change ((prog_comp_env tprog) ! id') with (gcenv ! id').
        rewrite Hco'.
        rewrite blockrep_empty; eauto.
        reflexivity.
  Qed.

  Definition varsrep (f: method) (ve: venv) (le: temp_env) :=
    pure (Forall (fun (xty: ident * Ctypes.type) =>
                    let (x, _) := xty in
                    match le ! x with
                    | Some v => match_value ve x v
                    | None => False
                    end) (map translate_param (f.(m_in) ++ f.(m_vars)))).

  Lemma varsrep_any_empty:
    forall f ve le,
      varsrep f ve le -*> varsrep f vempty le.
  Proof.
    intros.
    apply pure_imp; intro H.
    induction (map translate_param (m_in f ++ m_vars f)) as [|(x, t)]; auto.
    inv H; constructor; auto.
    destruct (le ! x); try contradiction.
    now rewrite match_value_empty.
  Qed.

  Definition match_out
             (c: class) (f: method) (ve: venv) (le: temp_env)
             (outb_co: option (block * composite)): massert :=
    match f.(m_out) with
    | [] => sepemp
    | [(x, _)] => pure (le ! x = Some match Env.find x ve with Some v => v | None => Vundef end)
    | _ =>
      match outb_co with
        | Some (outb, outco) =>
          pure (le ! out = Some (Vptr outb Ptrofs.zero))
          ** pure (gcenv ! (prefix_fun c.(c_name) f.(m_name)) = Some outco)
          ** blockrep gcenv ve outco.(co_members) outb
        | None => sepfalse
      end
    end.

  Lemma match_out_nil:
    forall c f ve le m outb_co P,
      f.(m_out) = [] ->
      (m |= match_out c f ve le outb_co ** P <-> m |= P).
  Proof.
    intros * Nil.
    unfold match_out; split; intros * H; rewrite Nil in *.
    - rewrite sepemp_left; auto.
    - rewrite <-sepemp_left; auto.
  Qed.

  Lemma match_out_singleton:
  forall c f ve le m outb_co x t P,
      f.(m_out) = [(x, t)] ->
      (m |= match_out c f ve le outb_co ** P <->
       m |= P /\ le ! x = Some match Env.find x ve with Some v => v | None => Vundef end).
  Proof.
    intros * Sing.
    unfold match_out; split; intros * H; rewrite Sing in *;
      rewrite sep_pure in *; tauto.
  Qed.

  Lemma match_out_notnil:
    forall c f ve le m outb_co P,
      (1 < length f.(m_out))%nat ->
      (m |= match_out c f ve le outb_co ** P <->
       exists outb outco,
         outb_co = Some (outb, outco)
         /\ m |= blockrep gcenv ve outco.(co_members) outb ** P
         /\ le ! out = Some (Vptr outb Ptrofs.zero)
         /\ gcenv ! (prefix_fun c.(c_name) f.(m_name)) = Some outco).
  Proof.
    intros * Length.
    unfold match_out; split; intros * H; destruct_list f.(m_out) as (?, ?) ? ?;
    ((now contradict Length; simpl; apply lt_irrefl)
     || (now contradict Length; simpl; apply lt_n_0)
     || idtac).
    - destruct outb_co as [(?, ?)|].
      + repeat rewrite sep_assoc in H; repeat rewrite sep_pure in H.
        do 3 econstructor; tauto.
      + apply sep_proj1 in H; contradiction.
    - destruct H as (? & ? & H & ?).
      rewrite H; repeat rewrite sep_assoc; repeat rewrite sep_pure; tauto.
  Qed.

  Definition match_states
             (c: class) (f: method) (S: menv * venv) (CS: c_state)
             (sb: block) (sofs: ptrofs) (outb_co: option (block * composite)): massert :=
    let (e, le) := CS in
    let (me, ve) := S in
    pure (wt_env ve (meth_vars f))
         ** pure (wt_mem me prog c)
         ** pure (le ! self = Some (Vptr sb sofs))
         ** pure (forall x b t, e ! x = Some (b, t) -> exists o f, x = prefix_out o f)
         ** pure (0 <= Ptrofs.unsigned sofs)
         ** pure (struct_in_bounds gcenv 0 Ptrofs.max_unsigned (Ptrofs.unsigned sofs) (make_members c))
         ** staterep gcenv prog c.(c_name) me sb (Ptrofs.unsigned sofs)
         ** match_out c f ve le outb_co
         ** subrep f e
         ** varsrep f ve le
         ** (subrep f e -* subrep_range e).

  Lemma match_states_conj:
    forall c f me ve e le m sb sofs outb_co P,
      m |= match_states c f (me, ve) (e, le) sb sofs outb_co ** P <->
      m |= staterep gcenv prog c.(c_name) me sb (Ptrofs.unsigned sofs)
          ** match_out c f ve le outb_co
          ** subrep f e
          ** varsrep f ve le
          ** (subrep f e -* subrep_range e)
          ** P
      /\ struct_in_bounds gcenv 0 Ptrofs.max_unsigned (Ptrofs.unsigned sofs) (make_members c)
      /\ wt_env ve (meth_vars f)
      /\ wt_mem me prog c
      /\ le ! self = Some (Vptr sb sofs)
      /\ (forall x b t, e ! x = Some (b, t) -> exists o f, x = prefix_out o f)
      /\ 0 <= Ptrofs.unsigned sofs.
  Proof.
    unfold match_states; split; intros * H.
    - repeat rewrite sep_assoc in H; repeat rewrite sep_pure in H; tauto.
    - repeat rewrite sep_assoc; repeat rewrite sep_pure; tauto.
  Qed.

  Remark existsb_In:
    forall f x ty,
      existsb (fun out => ident_eqb (fst out) x) f.(m_out) = true ->
      In (x, ty) (meth_vars f) ->
      In (x, ty) f.(m_out).
  Proof.
    intros * E ?.
    apply existsb_exists in E.
    destruct E as ((x' & ty') & Hin & E).
    rewrite ident_eqb_eq in E; simpl in E; subst.
    pose proof (m_nodupvars f) as Nodup.
    assert (In (x, ty') (meth_vars f))
      by (now apply in_or_app; right; apply in_or_app; right).
    now app_NoDupMembers_det.
  Qed.

  Remark not_existsb_In:
    forall f x ty,
      existsb (fun out => ident_eqb (fst out) x) f.(m_out) = false ->
      ~ In (x, ty) f.(m_out).
  Proof.
    intros * E Hin.
    apply not_true_iff_false in E.
    apply E.
    apply existsb_exists.
    exists (x, ty); split; auto; simpl.
    apply ident_eqb_refl.
  Qed.

  Remark not_existsb_InMembers:
    forall f x ty,
      existsb (fun out => ident_eqb (fst out) x) f.(m_out) = false ->
      In (x, ty) (meth_vars f) ->
      ~ InMembers x f.(m_out).
  Proof.
    intros * E ? Hin.
    apply not_true_iff_false in E.
    apply E.
    apply existsb_exists.
    exists (x, ty); split; simpl.
    - apply InMembers_In in Hin.
      destruct Hin as [ty' Hin].
      assert (In (x, ty') (meth_vars f))
        by (now apply in_or_app; right; apply in_or_app; right).
      pose proof (m_nodupvars f).
      now app_NoDupMembers_det.
    - apply ident_eqb_refl.
  Qed.

  Section ExprCorrectness.
    Variables (ownerid: ident) (owner: class) (prog': program) (callerid: ident) (caller: method).
    Hypothesis Findcl: find_class ownerid prog = Some (owner, prog').
    Hypothesis Findmth: find_method callerid owner.(c_methods) = Some caller.

    Section OutField.
      Variables (m: Mem.mem) (ve: venv) (outb: block) (outco: composite)
                (P: massert) (le: temp_env) (x: ident) (ty: type).
      Hypothesis Houtco: gcenv ! (prefix_fun owner.(c_name) caller.(m_name)) = Some outco.
      Hypothesis Hout: le ! out = Some (Vptr outb Ptrofs.zero).
      Hypothesis Hrep: m |= blockrep gcenv ve outco.(co_members) outb ** P.
      Hypothesis Hin: In (x, ty) (meth_vars caller).
      Hypothesis Length: (1 < length caller.(m_out))%nat.

      Lemma evall_out_field:
        forall e,
          existsb (fun out => ident_eqb (fst out) x) caller.(m_out) = true ->
          exists d,
            eval_lvalue tge e le m (deref_field out (prefix_fun (c_name owner) (m_name caller)) x (cltype ty))
                        outb (Ptrofs.add Ptrofs.zero (Ptrofs.repr d))
            /\ field_offset gcenv x (co_members outco) = Errors.OK d.
      Proof.
        intros * E.
        eapply existsb_In in E; eauto.
        apply in_map with (f:=translate_param) in E.
        erewrite output_match in E; eauto.
        edestruct blockrep_field_offset as (d & Hoffset & ?); eauto.
        exists d; split; auto.
        eapply eval_Efield_struct; eauto.
        - eapply eval_Elvalue; eauto.
          now apply deref_loc_copy.
        - simpl; unfold type_of_inst; eauto.
      Qed.

      Lemma eval_out_field:
        forall e v,
          mem_assoc_ident x (m_out caller) = true ->
          Env.find x ve = Some v ->
          eval_expr tge e le m (deref_field out (prefix_fun (c_name owner) (m_name caller)) x (cltype ty)) v.
      Proof.
        intros.
        edestruct evall_out_field with (e:=e) as (? & ? & ?); eauto.
        eapply eval_Elvalue; eauto.
        rewrite Ptrofs.add_zero_l.
        eapply blockrep_deref_mem; eauto.
        erewrite <-output_match; eauto.
        rewrite in_map_iff.
        exists (x, ty); split; auto.
        apply existsb_In; auto.
      Qed.
    End OutField.

    Lemma eval_temp_var:
      forall ve e le m x ty v P,
        m |= varsrep caller ve le ** P ->
        In (x, ty) (meth_vars caller) ->
        mem_assoc_ident x (m_out caller) = false ->
        Env.find x ve = Some v ->
        eval_expr tge e le m (Etempvar x (cltype ty)) v.
    Proof.
      intros * Hrep Hvars E ?.
      apply sep_proj1, sep_pure' in Hrep.
      apply eval_Etempvar.
      apply mem_assoc_ident_false with (t:=ty) in E.
      unfold meth_vars in Hvars.
      rewrite app_assoc in Hvars.
      eapply not_In2_app in E; eauto.
      apply in_map with (f:=translate_param) in E.
      eapply Forall_forall in Hrep; eauto.
      simpl in Hrep.
      destruct (le ! x);
        [now app_match_find_var_det | contradiction].
    Qed.

    Section SelfField.
      Variables (m: Mem.mem) (me: menv) (outco: composite) (sb: block) (sofs: ptrofs) (P: massert)
                (le: temp_env) (x: ident) (ty: type).
      Hypothesis Hrep: m |= staterep gcenv prog owner.(c_name) me sb (Ptrofs.unsigned sofs) ** P.
      Hypothesis Hsofs: 0 <= Ptrofs.unsigned sofs.
      Hypothesis Hbounds: struct_in_bounds gcenv 0 Ptrofs.max_unsigned (Ptrofs.unsigned sofs) (make_members owner).
      Hypothesis Get_self: le ! self = Some (Vptr sb sofs).
      Hypothesis Hmems: In (x, ty) owner.(c_mems).

      Lemma evall_self_field:
        forall e, exists d,
            eval_lvalue tge e le m (deref_field self (c_name owner) x (cltype ty))
                        sb (Ptrofs.add sofs (Ptrofs.repr d))
            /\ field_offset gcenv x (make_members owner) = Errors.OK d
            /\ 0 <= d <= Ptrofs.max_unsigned.
      Proof.
        intros.
        pose proof (find_class_name _ _ _ _ Findcl); subst.
        edestruct make_members_co as (? & Hco & ? & Eq & ? & ?); eauto.
        rewrite staterep_skip in Hrep; eauto.
        edestruct staterep_field_offset as (d & ? & ?); eauto.
        exists d; split; [|split]; auto.
        - eapply eval_Efield_struct; eauto.
          + eapply eval_Elvalue; eauto.
            now apply deref_loc_copy.
          + simpl; unfold type_of_inst; eauto.
          + now rewrite Eq.
        - split.
          + eapply field_offset_in_range'; eauto.
          + omega.
      Qed.

      Lemma eval_self_field:
        forall e v,
          find_val x me = Some v ->
          access_mode (cltype ty) = By_value (type_chunk ty) ->
          eval_expr tge e le m (deref_field self (c_name owner) x (cltype ty)) v.
      Proof.
        intros.
        edestruct evall_self_field as (? & ? & Hoffset & (? & ?)); eauto.
        eapply eval_Elvalue; eauto.
        rewrite staterep_skip in Hrep; eauto.
        eapply staterep_deref_mem; eauto.
        rewrite Ptrofs.unsigned_repr; auto.
      Qed.

      Lemma eval_self_inst:
        forall e o c',
          In (o, c') (c_objs owner) ->
          exists d,
            eval_expr tge e le m (ptr_obj owner.(c_name) c' o) (Vptr sb (Ptrofs.add sofs (Ptrofs.repr d)))
            /\ field_offset gcenv o (make_members owner) = Errors.OK d
            /\ 0 <= Ptrofs.unsigned sofs + d <= Ptrofs.max_unsigned.
      Proof.
        intros * Hin.
        pose proof (find_class_name _ _ _ _ Findcl); subst.
        edestruct make_members_co as (? & Hco & ? & Eq & ? & ?); eauto.
        rewrite staterep_skip in Hrep; eauto.
        destruct (struct_in_bounds_sizeof _ _ _ Hco).
        edestruct wt_program_find_class as [[Find]]; eauto.
        eapply Forall_forall in Find; eauto; simpl in Find.
        apply not_None_is_Some in Find.
        destruct Find as [(?, ?)]; eauto.
        edestruct struct_in_struct_in_bounds' as (d & ? & Struct); eauto.
        exists d; split; [|split]; auto.
        + apply eval_Eaddrof.
          eapply eval_Efield_struct; eauto.
          * eapply eval_Elvalue; eauto.
            now apply deref_loc_copy.
          * simpl; unfold type_of_inst; eauto.
          * now rewrite Eq.
        + destruct Struct.
          split; try omega.
          apply (Z.le_le_add_le 0 (sizeof_struct (globalenv tprog) 0 (make_members c))); try omega.
          apply sizeof_struct_incr.
      Qed.
    End SelfField.

    Lemma evall_inst_field:
      forall x ty e le m o oblk instco ve P,
        m |= blockrep gcenv ve instco.(co_members) oblk ** P ->
        e ! o = Some (oblk, type_of_inst (prefix_fun ownerid callerid)) ->
        gcenv ! (prefix_fun ownerid callerid) = Some instco ->
        In (x, ty) caller.(m_out) ->
        (1 < length (m_out caller))%nat ->
        exists d,
          eval_lvalue tge e le m (Efield (Evar o (type_of_inst (prefix_fun ownerid callerid))) x (cltype ty))
                      oblk (Ptrofs.add Ptrofs.zero (Ptrofs.repr d))
          /\ field_offset tge x instco.(co_members) = Errors.OK d
          /\ 0 <= d <= Int.max_unsigned.
    Proof.
      intros ????????????? Hin ?.
      pose proof (find_class_name _ _ _ _ Findcl);
        pose proof (find_method_name _ _ _ Findmth); subst.
      apply in_map with (f:=translate_param) in Hin.
      erewrite output_match in Hin; eauto.
      edestruct blockrep_field_offset as (d & Hoffset & ?); eauto.
      exists d; split; [|split]; auto.
      eapply eval_Efield_struct; eauto.
      - eapply eval_Elvalue; eauto.
        now apply deref_loc_copy.
      - simpl; unfold type_of_inst; eauto.
    Qed.

    Lemma pres_sem_exp':
      forall c vars me ve e v,
        wt_mem me prog c ->
        wt_env ve vars ->
        wt_exp c.(c_mems) vars e ->
        exp_eval me ve e v ->
        wt_valo v (typeof e).
    Proof.
      intros * WT_mem ? ? ?.
      inv WT_mem.
      eapply pres_sem_expo with (vars:=vars); eauto.
    Qed.
    Hint Resolve pres_sem_exp'.

    Lemma expr_eval_simu:
      forall me ve e le m sb sofs outb_co P ex v,
        m |= staterep gcenv prog owner.(c_name) me sb (Ptrofs.unsigned sofs)
            ** match_out owner caller ve le outb_co
            ** subrep caller e
            ** varsrep caller ve le
            ** P ->
        wt_env ve (meth_vars caller) ->
        wt_mem me prog owner ->
        le ! self = Some (Vptr sb sofs) ->
        0 <= Ptrofs.unsigned sofs ->
        wt_exp owner.(c_mems) (meth_vars caller) ex ->
        exp_eval me ve ex (Some v) ->
        Clight.eval_expr tge e le m (translate_exp owner caller ex) v.
    Proof.
      intros * Hrep ? ? ? ? WF EV;
        revert v EV; induction ex as [x| |cst|op| |]; intros v EV;
          inv EV; inv WF.

      (* Var x ty : "x" *)
      - simpl; destruct (mem_assoc_ident x caller.(m_out)) eqn:E.
        + rewrite sep_swap in Hrep.
          destruct_list caller.(m_out) as (?, ?) (?, ?) ? : Out.
          * simpl in E; discriminate.
          * simpl in E; apply orb_true_iff in E; destruct E as [E|]; try discriminate.
            apply ident_eqb_eq in E; subst x.
            econstructor.
            rewrite match_out_singleton in Hrep; eauto.
            destruct Hrep as (? & Eq); destruct (Env.find i ve); contr;
              rewrite Eq; auto.
          * simpl in *; rewrite E.
            assert (1 < length caller.(m_out))%nat by (rewrite Out; simpl; omega).
            rewrite match_out_notnil in Hrep; auto; destruct Hrep as (? & ? & ? & ? & ? & ?).
            eapply eval_out_field; eauto;
            rewrite Out; auto.
        + rewrite sep_swap4 in Hrep.
          destruct_list caller.(m_out) : Out; simpl in E; try rewrite E;
            eapply eval_temp_var; eauto; now rewrite Out.

      (* State x ty : "self->x" *)
      - eapply eval_self_field; eauto.

      (* Const c ty : "c" *)
      - destruct cst; constructor.

      (* Unop op e ty : "op e" *)
      - destruct op; simpl in *; econstructor; eauto.
        + rewrite type_pres.
          erewrite sem_unary_operation_any_mem; eauto.
          eapply wt_val_not_vundef_nor_vptr; eauto.
        + rewrite type_pres.
          match goal with
            H: match Ctyping.check_cast ?x ?y with _ => _ end = _ |- _ =>
            destruct (Ctyping.check_cast x y); inv H
          end.
          erewrite sem_cast_any_mem; eauto.
          eapply wt_val_not_vundef_nor_vptr; eauto.

      (* Binop op e1 e2 : "e1 op e2" *)
      - simpl in *. unfold translate_binop.
        econstructor; eauto.
        rewrite 2 type_pres.
        erewrite sem_binary_operation_any_cenv_mem; eauto;
          eapply wt_val_not_vundef_nor_vptr; eauto.

      (* Valid ex *)
      - auto.
    Qed.

    Lemma exp_eval_valid_s:
      forall c vars me ve es vs,
        wt_mem me prog c ->
        wt_env ve vars ->
        Forall (wt_exp c.(c_mems) vars) es ->
        Forall2 (exp_eval me ve) es vs ->
        Forall2 (fun e v => wt_valo v (typeof e)) es vs.
    Proof.
      induction es, vs; intros ?? Wt Ev; inv Wt; inv Ev; eauto.
    Qed.

    Lemma exp_eval_lr:
      forall c vars me ve e v,
        wt_mem me prog c ->
        wt_env ve vars ->
        wt_exp c.(c_mems) vars e ->
        exp_eval me ve e (Some v) ->
        v = Val.load_result (type_chunk (typeof e)) v.
    Proof.
      intros.
      apply wt_val_load_result; eauto.
    Qed.

    Lemma exprs_eval_simu:
      forall me ve es es' vs e le m sb sofs outb_co P,
        m |= staterep gcenv prog owner.(c_name) me sb (Ptrofs.unsigned sofs)
            ** match_out owner caller ve le outb_co
            ** subrep caller e
            ** varsrep caller ve le
            ** P ->
        wt_env ve (meth_vars caller) ->
        wt_mem me prog owner ->
        le ! self = Some (Vptr sb sofs) ->
        0 <= Ptrofs.unsigned sofs ->
        Forall (wt_exp owner.(c_mems) (meth_vars caller)) es ->
        Forall2 (fun e v => exp_eval me ve e (Some v)) es vs ->
        es' = map (translate_exp owner caller) es ->
        Clight.eval_exprlist tge e le m es'
                             (list_type_to_typelist (map Clight.typeof es')) vs.
    Proof.
      Hint Constructors Clight.eval_exprlist.
      intros ????????????????? WF EV ?; subst es';
        induction EV; inv WF; econstructor;
          ((eapply expr_eval_simu; eauto) || (rewrite type_pres; apply sem_cast_same; eauto) || auto).
    Qed.
  End ExprCorrectness.

  Hint Resolve pres_sem_exp' expr_eval_simu exp_eval_lr exp_eval_valid_s.

  Remark eval_exprlist_app:
    forall e le m es es' vs vs',
      Clight.eval_exprlist tge e le m es
                           (list_type_to_typelist (map Clight.typeof es)) vs ->
      Clight.eval_exprlist tge e le m es'
                           (list_type_to_typelist (map Clight.typeof es')) vs' ->
      Clight.eval_exprlist tge e le m (es ++ es')
                           (list_type_to_typelist (map Clight.typeof (es ++ es'))) (vs ++ vs').
  Proof.
    induction es; intros * Ev Ev'; inv Ev; auto.
    repeat rewrite <-app_comm_cons.
    simpl; econstructor; eauto.
  Qed.

  Lemma varsrep_corres_out:
    forall f ve le x t v,
      In (x, t) (m_out f) ->
      varsrep f ve le -*> varsrep f (Env.add x v ve) le.
  Proof.
    intros * Hin.
    unfold varsrep.
    rewrite pure_imp.
    intro Hforall.
    assert (~InMembers x (f.(m_in) ++ f.(m_vars))) as Notin.
    { pose proof (m_nodupvars f) as Nodup.
      rewrite app_assoc, Permutation_app_comm in Nodup.
      apply In_InMembers in Hin.
      eapply NoDupMembers_app_InMembers; eauto.
    }
    induction (m_in f ++ m_vars f) as [|(x', t')]; simpl in *; eauto.
    inv Hforall.
    constructor.
    - destruct le ! x'; auto.
      rewrite match_value_add; auto.
    - apply IHl; auto.
  Qed.

  Lemma varsrep_add:
    forall f ve le x v,
      varsrep f ve le -*> varsrep f (Env.add x v ve) (PTree.set x v le).
  Proof.
    intros.
    unfold varsrep.
    rewrite pure_imp.
    intro Hforall.
    induction (m_in f ++ m_vars f) as [|(x', t')]; simpl in *; auto.
    inv Hforall.
    constructor.
    - destruct (ident_eqb x' x) eqn: Eq.
      + apply ident_eqb_eq in Eq.
        subst x'.
        rewrite PTree.gss.
        unfold match_value.
        now rewrite Env.gss.
      + apply ident_eqb_neq in Eq.
        rewrite PTree.gso; auto.
        now rewrite match_value_add.
    - now apply IHl.
  Qed.

  Lemma varsrep_add':
    forall f ve le x v y v',
      ~ InMembers y (m_in f ++ m_vars f) ->
      varsrep f ve le -*> varsrep f (Env.add x v ve) (PTree.set x v (PTree.set y v' le)).
  Proof.
    intros * Notin.
    transitivity (varsrep f ve (PTree.set y v' le)).
    - unfold varsrep.
      rewrite pure_imp.
      intro Hforall.
      induction (m_in f ++ m_vars f) as [|(x', t')]; simpl in *; auto.
      inv Hforall.
      apply Decidable.not_or in Notin; destruct Notin.
      constructor.
      + rewrite PTree.gso; auto.
      + now apply IHl.
    - apply varsrep_add.
  Qed.

  Lemma varsrep_add'':
    forall f ve le x v y v',
      ~ InMembers y (m_in f ++ m_vars f) ->
      x <> y ->
      varsrep f (Env.add x v ve) le -*> varsrep f (Env.add x v ve) (PTree.set y v' le).
  Proof.
    intros * Notin ?.
    unfold varsrep.
    rewrite pure_imp.
    intro Hforall.
    induction (m_in f ++ m_vars f) as [|(x', t')]; simpl in *; auto.
    inv Hforall.
    apply Decidable.not_or in Notin; destruct Notin.
    constructor.
    - rewrite PTree.gso; auto.
    - now apply IHl.
  Qed.

 Lemma varsrep_add''':
    forall f ve le x v,
      ~ InMembers x (m_in f ++ m_vars f) ->
      varsrep f ve le -*> varsrep f ve (PTree.set x v le).
  Proof.
    intros * Notin.
    unfold varsrep.
    rewrite pure_imp.
    intro Hforall.
    induction (m_in f ++ m_vars f) as [|(x', t')]; simpl in *; auto.
    inv Hforall.
    apply Decidable.not_or in Notin; destruct Notin.
    constructor.
    - rewrite PTree.gso; auto.
    - now apply IHl.
  Qed.

  Section MatchStatesAssign.
    Variables (ownerid: ident) (owner: class) (prog': program) (callerid: ident) (caller: method).
    Hypothesis Findowner: find_class ownerid prog = Some (owner, prog').
    Hypothesis Findcaller: find_method callerid owner.(c_methods) = Some caller.

    Section OutField.
      Variables (m: Mem.mem) (ve: venv) (outb_co: option (block * composite)) (P: massert)
                (le: temp_env) (x: ident) (ty: type).
      Hypothesis Hrep: m |= match_out owner caller ve le outb_co ** varsrep caller ve le ** P.
      Hypothesis Hvars: In (x, ty) (meth_vars caller).

      Lemma match_states_assign_out:
        forall v d outb outco,
          outb_co = Some (outb, outco) ->
          field_offset gcenv x (co_members outco) = Errors.OK d ->
          access_mode (cltype ty) = By_value (type_chunk ty) ->
          v = Values.Val.load_result (type_chunk ty) v ->
          mem_assoc_ident x (m_out caller) = true ->
          (1 < length (m_out caller))%nat ->
          exists m', Memory.Mem.storev (type_chunk ty) m (Vptr outb (Ptrofs.repr d)) v = Some m'
                /\ m' |= match_out owner caller (Env.add x v ve) le outb_co
                       ** varsrep caller (Env.add x v ve) le
                       ** P .
      Proof.
        intros * Hout Hoffset Haccess Hlr E Length.

        unfold mem_assoc_ident in E; eapply existsb_In in E; eauto.
        rewrite match_out_notnil in Hrep; auto.
        destruct Hrep as (outb' & outco' & Hout' & Hrep' & ? & Hco); clear Hrep; rename Hrep' into Hrep.
        rewrite Hout' in Hout; inversion Hout; subst outb' outco'.
        pose proof (output_match _ _ _ Findowner _ _ Findcaller Length _ Hco) as Eq.
        pose proof E as Hin; apply in_map with (f:=translate_param) in Hin;
          rewrite Eq in Hin; eauto.
        pose proof (m_nodupvars caller) as Nodup.

        (* get the updated memory *)
        rewrite sep_swap in Hrep.
        apply sepall_in in Hin.
        destruct Hin as [ws [ys [Hys Heq]]].
        unfold blockrep in Hrep.
        rewrite Heq in Hrep; simpl in *.
        rewrite Hoffset, Haccess, sep_assoc, sep_swap in Hrep.
        eapply Separation.storev_rule' with (v:=v) in Hrep; eauto with mem.
        destruct Hrep as (m' & ? & Hrep'); clear Hrep; rename Hrep' into Hrep.
        exists m'; split; auto.
        rewrite match_out_notnil; auto.
        do 3 econstructor; eauto. split; auto.
        unfold blockrep.
        rewrite Heq, Hoffset, Haccess, sep_assoc.
        rewrite sep_swap23.
        eapply sep_imp; eauto.
        - unfold hasvalue'.
          unfold match_value; simpl.
          rewrite Env.gss.
          now rewrite <-Hlr.
        - apply sep_imp'.
          + eapply varsrep_corres_out; eauto.
          + apply sep_imp'; auto.
            do 2 apply NoDupMembers_app_r in Nodup.
            rewrite fst_NoDupMembers, <-translate_param_fst, <-fst_NoDupMembers in Nodup; auto.
            rewrite Eq, Hys in Nodup.
            apply NoDupMembers_app_cons in Nodup.
            destruct Nodup as (Notin & Nodup).
            rewrite sepall_swapp; eauto.
            intros (x' & t') Hin.
            rewrite match_value_add; auto.
            intro; subst x'.
            apply Notin.
            eapply In_InMembers; eauto.
      Qed.

      Lemma match_states_assign_out_singleton:
        forall v,
          m_out caller = [(x, ty)] ->
          m |= match_out owner caller (Env.add x v ve) (PTree.set x v le) outb_co
              ** varsrep caller (Env.add x v ve) (PTree.set x v le)
              ** P .
      Proof.
        intros * E.
        rewrite match_out_singleton in *; eauto.
        destruct Hrep; split.
        - eapply sep_imp; eauto.
          apply varsrep_add.
        - now rewrite PTree.gss, Env.gss.
      Qed.

      Lemma match_states_assign_tempvar:
        forall v,
          mem_assoc_ident x (m_out caller) = false ->
          m |= match_out owner caller (Env.add x v ve) (PTree.set x v le) outb_co
              ** varsrep caller (Env.add x v ve) (PTree.set x v le)
              ** P.
      Proof.
        intros * E.
        eapply sep_imp; eauto.
        - unfold match_out; destruct_list (m_out caller) as (?, ?) (?, ?) ? : Hout; auto.
          + rewrite pure_imp.
            intro Eq.
            destruct (ident_eqb i x) eqn: Eix.
            * apply ident_eqb_eq in Eix.
              subst i.
              now rewrite PTree.gss, Env.gss.
            * apply ident_eqb_neq in Eix.
              now rewrite PTree.gso, Env.gso; auto.
          + destruct outb_co as [(outb, outco)|]; auto.
            repeat apply sep_imp'; auto.
            * rewrite pure_imp.
              intro Eq.
              rewrite PTree.gso; auto.
              apply Forall_forall with (1 := m_good caller) in Hvars.
              intro; subst.
              unfold ValidId, NotReserved, reserved in Hvars.
              destruct Hvars as [NotRes].
              apply NotRes; simpl; auto.
            * unfold blockrep in *.
              rewrite sepall_swapp; eauto.
              intros (x', t') Hx'.
              rewrite match_value_add; auto.
              unfold mem_assoc_ident in E.
              rewrite <-Hout in E; eapply not_existsb_InMembers in E; eauto.
              apply In_InMembers in Hx'.
              intro Hxx'; subst x.
              apply E.
              rewrite fst_InMembers, <-translate_param_fst, <-fst_InMembers; auto.
              assert (1 < length caller.(m_out))%nat by (rewrite Hout; simpl; omega).
              rewrite match_out_notnil in Hrep; auto; destruct Hrep as (? & ? & E' & ? & ? & ?).
              inv E'.
              erewrite output_match; eauto.
        - apply sep_imp'; auto.
          apply varsrep_add.
      Qed.
    End OutField.

    Lemma match_states_assign_state:
      forall m me sb sofs P x ty v d,
        m |= staterep gcenv prog owner.(c_name) me sb (Ptrofs.unsigned sofs) ** P ->
        In (x, ty) owner.(c_mems) ->
        field_offset gcenv x (make_members owner) = Errors.OK d ->
        v = Values.Val.load_result (type_chunk ty) v ->
        exists m',
          Memory.Mem.storev (type_chunk ty) m (Vptr sb (Ptrofs.repr (Ptrofs.unsigned sofs + d))) v = Some m'
          /\ m' |= staterep gcenv prog owner.(c_name) (add_val x v me) sb (Ptrofs.unsigned sofs) ** P.
    Proof.
      intros * Hrep Hmems Hoffset Hlr.

      (* get the updated memory *)
      apply sepall_in in Hmems.
      destruct Hmems as [ws [ys [Hys Heq]]].
      rewrite staterep_skip in Hrep; eauto.
      simpl staterep in Hrep.
      unfold staterep_mems in Hrep.
      rewrite ident_eqb_refl, Heq, Hoffset in Hrep.
      rewrite 2 sep_assoc in Hrep.
      eapply Separation.storev_rule' with (v:=v) in Hrep; eauto with mem.
      destruct Hrep as (m' & ? & Hrep).
      exists m'; split; auto.
      rewrite staterep_skip; eauto.
      simpl staterep.
      unfold staterep_mems.
      rewrite ident_eqb_refl, Heq, Hoffset.
      rewrite 2 sep_assoc.
      eapply sep_imp; eauto.
      - unfold hasvalue'.
        unfold match_value; simpl.
        rewrite Env.gss.
        now rewrite <-Hlr.
      - apply sep_imp'; auto.
        pose proof (c_nodupmems owner) as Nodup.
        rewrite Hys in Nodup.
        apply NoDupMembers_app_cons in Nodup.
        destruct Nodup as (Notin & Nodup).
        rewrite sepall_swapp; eauto.
        intros (x' & t') Hin.
        unfold add_val; simpl.
        rewrite match_value_add; auto.
        intro; subst x'.
        apply Notin.
        eapply In_InMembers; eauto.
    Qed.

    Lemma exec_assign:
      forall callee e1 le1 m1 c prog' o f clsid
        ve ve' sb sofs outb_co binst instco P y x t v,
        find_class clsid prog = Some (c, prog') ->
        find_method f c.(c_methods) = Some callee ->
        le1 ! self = Some (Vptr sb sofs) ->
        In (x, t) callee.(m_out) ->
        In (y, t) (meth_vars caller) ->
        (1 < length (m_out callee))%nat ->
        y <> self ->
        wt_val v t ->
        m1 |= blockrep gcenv (Env.add x v ve') instco.(co_members) binst
              ** match_out owner caller ve le1 outb_co
              ** varsrep caller ve le1
              ** P ->
        e1 ! (prefix_out o f) = Some (binst, type_of_inst (prefix_fun clsid f)) ->
        gcenv ! (prefix_fun clsid f) = Some instco ->
        exists le2 m2,
          exec_stmt tge (function_entry2 tge) e1 le1 m1
                    (assign y (cltype t) (c_name owner) caller
                            (Efield (Evar (prefix_out o f) (type_of_inst (prefix_fun clsid f))) x (cltype t)))
                    E0 le2 m2 Out_normal
          /\ m2 |= blockrep gcenv (Env.add x v ve') instco.(co_members) binst
                   ** match_out owner caller (Env.add y v ve) le2 outb_co
                   ** varsrep caller (Env.add y v ve) le2
                   ** P
          /\ le2 ! self = Some (Vptr sb sofs).
    Proof.
      intros * Findc Findcallee Hself Hinx Hiny Length
             Notself Valid Hrep Hinst Hinstco.
      pose proof (find_class_name _ _ _ _ Findc) as Eq.
      pose proof (find_method_name _ _ _ Findcallee) as Eq'.
      edestruct (evall_inst_field _ _ _ _ _ Findc Findcallee x t e1 le1) as
          (dx & Ev_x & Hoffset_x & ?); eauto.
      assert (eval_expr tge e1 le1 m1
                        (Efield (Evar (prefix_out o f)
                                      (type_of_inst (prefix_fun clsid f))) x (cltype t)) v).
      { eapply eval_Elvalue; eauto.
        eapply blockrep_deref_mem; eauto.
        - rewrite <-Eq, <-Eq' in Hinstco.
          apply in_map with (f:=translate_param) in Hinx.
          erewrite output_match in Hinx; eauto.
        - rewrite Env.gss; auto.
        - rewrite Ptrofs.unsigned_zero; simpl.
          rewrite Ptrofs.unsigned_repr; auto.
      }
      unfold assign.
      destruct_list caller.(m_out) as (x', t') (x'', t'') outs : Houts.
      - do 2 econstructor; split; [|split].
        + econstructor; eauto.
        + rewrite sep_swap, match_out_nil in *; auto.
          eapply sep_imp; eauto.
          apply sep_imp'; auto.
          apply varsrep_add.
        + rewrite PTree.gso; auto.
      - do 2 econstructor; split; [|split].
        + econstructor; eauto.
        + rewrite sep_swap, match_out_singleton in *; eauto.
          destruct Hrep; split.
          * eapply sep_imp; eauto.
            apply sep_imp'; auto.
            apply varsrep_add.
          *{ destruct (ident_eqb y x') eqn: Eyx'.
             - apply ident_eqb_eq in Eyx'.
               subst x'.
               rewrite PTree.gss, Env.gss; auto.
             - apply ident_eqb_neq in Eyx'.
               rewrite PTree.gso, Env.gso; auto.
           }
        + rewrite PTree.gso; auto.
      - assert (1 < length (m_out caller))%nat by (rewrite Houts; simpl; omega).
        rewrite sep_swap in Hrep.
        pose proof Hrep as Hrep'.
        rewrite match_out_notnil in Hrep; auto.
        destruct Hrep as (? & ? & ? & Hrep & ? & ?).
        destruct (mem_assoc_ident y (m_out caller)) eqn: E; rewrite Houts in E; rewrite E.
        + rewrite <-Houts in E.
          edestruct evall_out_field with (1:=Findowner) (2:=Findcaller) (x:=y) as (? & ? & ?); eauto.
          rewrite sep_swap23 in Hrep'.
          edestruct match_states_assign_out with (x:=y) (v:=v)
            as (m2 & Store & Hm2); eauto.
          rewrite sep_swap23, sep_swap in Hm2.
          exists le1, m2; split; [|split]; auto.
          econstructor; eauto.
          * eapply sem_cast_same; eauto.
          *{ eapply assign_loc_value; eauto.
             - eapply acces_cltype; eauto.
             - rewrite Ptrofs.add_zero_l; auto.
           }
        + do 2 econstructor; split; [|split].
          * econstructor; eauto.
          *{ rewrite sep_swap, sep_swap23.
             rewrite sep_swap23 in Hrep'.
             rewrite <-Houts in E.
             eapply match_states_assign_tempvar; eauto.
           }
          * rewrite PTree.gso; auto.
    Qed.

    Definition outrep
               (f: ident) (outs: list (ident * type)) (flds: members)
               (rvs: list val) (le: temp_env)
               (ve: venv) (b: block): massert :=
      match outs, rvs with
      | [],       []  => sepemp
      | [(y, _)], [v] => pure (le ! (prefix f y) = Some v)
      | outs,     rvs => blockrep gcenv (Env.adds (map fst outs) rvs ve) flds b
      end.

    Lemma exec_funcall_assign:
      forall callee ys e1 le1 m1 c prog' o f clsid
        ve ve' sb sofs outb_co rvs binst instco P,
        find_class clsid prog = Some (c, prog') ->
        find_method f c.(c_methods) = Some callee ->
        NoDup ys ->
        Forall2 (fun y xt => In (y, snd xt) (meth_vars caller)) ys
                callee.(m_out) ->
        le1 ! self = Some (Vptr sb sofs) ->
        m1 |= outrep f callee.(m_out) instco.(co_members) rvs le1 ve' binst
              ** match_out owner caller ve le1 outb_co
              ** varsrep caller ve le1
              ** P ->
        Forall2 (fun rv xt => wt_val rv (snd xt)) rvs callee.(m_out) ->
        e1 ! (prefix_out o f) = Some (binst, type_of_inst (prefix_fun clsid f)) ->
        gcenv ! (prefix_fun clsid f) = Some instco ->
        exists le2 m2,
          exec_stmt tge (function_entry2 tge) e1 le1 m1
                    match ys, callee.(m_out) with
                    | [], [] => Sskip
                    | [y], [(y', t)] =>
                      let c_t := cltype t in
                      assign y c_t owner.(c_name) caller (Clight.Etempvar (prefix f y') c_t)
                    | _, outs =>
                      funcall_assign ys owner.(c_name) caller (prefix_out o f)
                                                       (type_of_inst (prefix_fun clsid f)) outs
                    end
                    E0 le2 m2 Out_normal
          /\ m2 |= outrep f callee.(m_out) instco.(co_members) rvs le2 ve' binst
                  ** match_out owner caller (Env.adds ys rvs ve) le2 outb_co
                  ** varsrep caller (Env.adds ys rvs ve) le2
                  ** P
          /\ le2 ! self = Some (Vptr sb sofs).
    Proof.
      unfold funcall_assign.
      intros * Findc Findcallee Nodup Incl
             Hself Hrep Valids Hinst Hinstco.
      assert (length ys = length callee.(m_out)) as Length1
          by (eapply Forall2_length; eauto).
      assert (length rvs = length callee.(m_out)) as Length2
          by (eapply Forall2_length; eauto).

      (* revert ve ve' le1 m1 ys rvs Hself Hrep Incl Length1 Length2 Nodup Valids.  *)
      pose proof (m_nodupvars callee) as Nodup'.
      do 2 apply NoDupMembers_app_r in Nodup'.
      destruct_list callee.(m_out) as (y', ty) (y'', ty') callee_outs : Outs;
        destruct_list ys as y z ys';
        destruct_list rvs as v v' vs';
        try discriminate.

      - (* no callee output *)
        simpl; do 2 econstructor; split; eauto.
        econstructor.

      - (* single callee output y *)
        inversion_clear Incl as [|? ? ? ? Hin].
        assert (y <> self).
        { apply In_InMembers in Hin.
          intro Eq; apply (m_notreserved y caller); auto.
          subst; apply in_eq.
        }
        assert (y <> prefix f y').
        { apply In_InMembers in Hin.
          intro.
          apply (m_notprefixed y caller); auto.
          subst; constructor.
        }
        unfold assign.
        unfold Env.adds; simpl fold_right.
        destruct_list caller.(m_out) as (x, t) (?, ?) caller_outs : Hout; simpl in Hrep.
        + (* no caller output *)
          rewrite sep_pure in Hrep; destruct Hrep as [? Hrep].
          do 2 econstructor; split.
          * do 2 econstructor; eauto.
          *{ simpl; rewrite sep_pure; split; [split|].
             - rewrite PTree.gso; auto.
             - rewrite match_out_nil in *; auto.
               eapply sep_imp; eauto.
               apply varsrep_add.
             - rewrite PTree.gso; auto.
           }
        + (* single caller output *)
          rewrite sep_pure in Hrep; destruct Hrep as [? Hrep].
          do 2 econstructor; split.
          * do 2 econstructor; eauto.
          *{ simpl; rewrite sep_pure; split; [split|].
             - rewrite PTree.gso; auto.
             - rewrite match_out_singleton in *; eauto.
               destruct Hrep; split.
               + eapply sep_imp; eauto.
                 apply varsrep_add.
               + destruct (ident_eqb y x) eqn: Eq.
                 * apply ident_eqb_eq in Eq.
                   subst y.
                   rewrite PTree.gss, Env.gss; auto.
                 * apply ident_eqb_neq in Eq.
                   rewrite PTree.gso, Env.gso; auto.
             - rewrite PTree.gso; auto.
           }
        + (* multiple caller output *)
          rewrite sep_pure in Hrep; destruct Hrep as [? Hrep].
          assert (1 < length caller.(m_out))%nat by (rewrite Hout; simpl; omega).
          destruct (mem_assoc_ident y (m_out caller)) eqn: E;
            rewrite Hout in E; rewrite E.
          *{ (* y ∈ caller output *)
             pose proof Hrep as Hrep'.
             rewrite match_out_notnil in Hrep; auto.
             destruct Hrep as (? & ? & ? & Hrep & ? & ?).
             rewrite <-Hout in E.
             edestruct evall_out_field with (1:=Findowner) (2:=Findcaller) (x:=y) as (? & ? & ?); eauto.
             inv Valids.
             edestruct match_states_assign_out with (v:=v)
               as (m2 & Store & Hm2); eauto.
             exists le1, m2; split; [|split]; auto.
             - econstructor; eauto.
               eapply sem_cast_same; eauto.
               eapply assign_loc_value; eauto.
               + eapply acces_cltype; eauto.
               + rewrite Ptrofs.add_zero_l; auto.
             - simpl; rewrite sep_pure; auto.
           }
           *{ (* y ∉ caller output *)
              do 2 econstructor; split.
              - do 2 econstructor; eauto.
              - simpl; rewrite sep_pure; split; [split|].
                + rewrite PTree.gso; auto.
                + rewrite <-Hout in E. eapply match_states_assign_tempvar; eauto.
                + rewrite PTree.gso; auto.
             }

      - (* multiple callee output *)
        inversion Length1 as (Length1'); clear Length1; rename Length1' into Length1.
        inversion Length2 as (Length2'); clear Length2; rename Length2' into Length2.
        inversion_clear Nodup as [|? ? Notin Nodup'']; inversion_clear Nodup'' as [|? ? Notinz Nodup].
        inversion_clear Nodup' as [|? ? ? Notin' Nodup'']; inversion_clear Nodup'' as [|? ? ? Notiny'' Nodup'].
        rewrite not_in_cons in Notin; destruct Notin as [? Notiny].
        rewrite NotInMembers_cons in Notin'; simpl in Notin'; destruct Notin' as [Notiny'].
        inversion_clear Incl as [|? ? ? ? Hvars Incl'];
          rename Incl' into Incl; simpl in Hvars.
        inversion_clear Incl as [|? ? ? ? Hvars' Incl'];
          rename Incl' into Incl; simpl in Hvars'.
        inversion_clear Valids as [|? ? ? ? Valid' Valids'];
          rename Valids' into Valids; simpl in Valid'.
        inversion_clear Valids as [|? ? ? ? Valid'' Valids'];
          rename Valids' into Valids; simpl in Valid''.
        assert (In (y', ty) callee.(m_out)) as Hin
            by (rewrite Outs; apply in_eq).
        assert (1 < length (m_out callee))%nat as Length by (rewrite Outs; simpl; omega).
        pose proof (find_class_name _ _ _ _ Findc) as Eq.
        pose proof (find_method_name _ _ _ Findcallee) as Eq'.
        assert (In (y'', ty') callee.(m_out)) as Hin'
            by (rewrite Outs; apply in_cons, in_eq).
        rewrite <-Eq, <-Eq' in Hinstco.
        pose proof (output_match _ _ _ Findc _ _ Findcallee Length _ Hinstco) as Eq_instco.
        assert (y <> self).
        { apply In_InMembers in Hvars.
          intro HEq; apply (m_notreserved y caller); auto.
          subst; apply in_eq.
        }
        assert (z <> self).
        { apply In_InMembers in Hvars'.
          intro HEq; apply (m_notreserved z caller); auto.
          subst; apply in_eq.
        }

        assert (exists (le2 : temp_env) (m2 : mem),
                   exec_stmt tge (function_entry2 tge) e1 le1 m1
                             (fold_right
                                (fun (y0 : ident * (AST.ident * type)) (s : statement) =>
                                   let '(y1, (y'0, ty0)) := y0 in
                                   Ssequence
                                     (assign y1 (cltype ty0) (c_name owner) caller
                                             (Efield (Evar (prefix_out o f) (type_of_inst (prefix_fun clsid f))) y'0 (cltype ty0))) s) Sskip
                                (combine [y; z] [(y', ty); (y'', ty')])) E0 le2 m2 Out_normal /\
                   m2 |= blockrep gcenv (Env.adds (y' :: y'' :: map fst callee_outs) (v :: v' :: vs') ve')
                                  (co_members instco) binst
                         ** match_out owner caller (Env.adds [y; z] [v; v'] ve) le2 outb_co
                         ** varsrep caller (Env.adds [y; z] [v; v'] ve) le2 ** P
                   /\ le2 ! self = Some (Vptr sb sofs)) as Hexec.
        { simpl.
          rewrite Eq, Eq' in Hinstco.
          simpl in Hrep.
          rewrite Env.adds_cons_cons in Hrep; try rewrite not_in_cons, <-fst_InMembers; auto.
          edestruct exec_assign with (y:=y) (t:=ty) as (le2 & m2 & ? & Hm2 & ?); eauto.
          rewrite Env.adds_cons_cons in Hm2; try rewrite <-fst_InMembers; auto.
          rewrite Env.add_comm in Hm2; auto.
          edestruct exec_assign with (y:=z) (t:=ty') as (le3 & m3 & ? & Hm3 & ?); eauto.
          exists le3, m3; split; [|split]; auto.
          - change E0 with (Eapp E0 (Eapp E0 E0)).
            do 2 (eapply exec_Sseq_1; eauto).
            econstructor.
          - eapply sep_imp; eauto.
            rewrite 2 Env.adds_cons_cons, Env.add_comm; auto.
            + rewrite <-fst_InMembers; auto.
            + rewrite not_in_cons, <-fst_InMembers; auto.
        }

        assert (forall x, In x callee_outs -> In x callee.(m_out)) as Ind_imp.
        { intros * Hin_outs.
          rewrite Outs.
          do 2 apply in_cons; auto.
        }
        clear Outs.
        simpl.
        destruct Hexec as (le' & m' & Hexec & Hm' & Hself').
        simpl in Hexec.
        assert (exists le2 m2,
                   exec_stmt tge (function_entry2 tge) e1 le' m'
                             (fold_right
                                (fun (y0 : ident * (AST.ident * type)) (s : statement) =>
                                   let '(y1, (y'0, ty0)) := y0 in
                                   Ssequence
                                     (assign y1 (cltype ty0) (c_name owner) caller
                                             (Efield (Evar (prefix_out o f) (type_of_inst (prefix_fun clsid f))) y'0 (cltype ty0))) s)
                                Sskip (combine ys' callee_outs)) E0 le2 m2 Out_normal
                   /\ m2 |= blockrep gcenv (Env.adds (y' :: y'' :: map fst callee_outs) (v :: v' :: vs') ve') (co_members instco) binst
                        ** match_out owner caller (Env.adds (y :: z :: ys') (v :: v' :: vs') ve) le2 outb_co
                        ** varsrep caller (Env.adds (y :: z :: ys') (v :: v' :: vs') ve) le2
                        ** P
                   /\ le2 ! self = Some (Vptr sb sofs))
          as Exec_Ind.
        { clear Hrep Hexec.
          revert dependent m'; revert dependent le'.
          revert ve ve' ys' vs' Length1 Length2 Incl Nodup Valids Notiny Notinz.
          induction callee_outs as [|(O, T)];
            destruct ys' as [|Y], vs' as [|V];
            eauto; contr.
          - simpl; do 2 econstructor; split; eauto.
            econstructor.
          - intros.
            assert (Y <> self).
            { inversion_clear Incl as [|? ? ? ? HinY].
              apply In_InMembers in HinY.
              intro HEq; apply (m_notreserved Y caller); auto.
              subst; apply in_eq.
            }
            apply not_in_cons in Notiny; destruct Notiny.
            apply not_in_cons in Notinz; destruct Notinz.
            rewrite Eq, Eq' in *; clear Eq Eq'.
            inv Length1; inv Length2.
            apply NotInMembers_cons in Notiny'; simpl in Notiny'; destruct Notiny'.
            apply NotInMembers_cons in Notiny''; simpl in Notiny''; destruct Notiny''.
            inv Nodup; inv Incl; inv Valids; inv Nodup'.
            assert (In (O, T) callee.(m_out)) as Hin_OT by (apply Ind_imp, in_eq).
            simpl in Hm'.
            assert (Env.adds (y' :: y'' :: O :: map fst callee_outs) (v :: v' :: V :: vs') ve' =
                    Env.adds (O :: y' :: y'' :: map fst callee_outs) (V :: v :: v' :: vs') ve') as Comm.
            { unfold Env.adds; simpl; f_equal.
              rewrite Env.add_comm; auto; f_equal.
              rewrite Env.add_comm; auto.
            }
            rewrite Comm, Env.adds_cons_cons in Hm'; try rewrite 2 not_in_cons, <-fst_InMembers; auto.
            edestruct exec_assign with (y:=Y) as (le3 & m3 & ? & Hm3 & ?); eauto.
            clear Hm'.
            assert (forall x : ident * type, In x callee_outs -> In x (m_out callee))
              by (intros; apply Ind_imp, in_cons; auto).
            pose proof Env.adds_cons_cons (y' :: y'' :: map fst callee_outs) O V (v :: v' :: vs') ve' as Comm'.
            (* unfold Env.adds in Comm'; simpl in Comm'. *)
            rewrite <-Comm' in Hm3; try rewrite 2 not_in_cons, <-fst_InMembers; auto.
            assert (Env.add Y V (Env.add z v' (Env.add y v ve)) = Env.add z v' (Env.add y v (Env.add Y V ve)))
              as Comm''.
            { rewrite Env.add_comm; auto.
              f_equal.
              rewrite Env.add_comm; auto.
            }
            unfold Env.adds in Hm3; simpl in Hm3.
            rewrite Comm'' in Hm3.
            unfold Env.adds in IHcallee_outs; simpl in IHcallee_outs.
            edestruct IHcallee_outs as (le2 & m2 & ? & ? & ?); eauto.
            exists le2, m2; split; [|split]; auto.
            * simpl.
              change E0 with (Eapp E0 E0).
              eapply exec_Sseq_1; eauto.
            * simpl.
              assert (Env.adds (y :: z :: Y :: ys') (v :: v' :: V :: vs') ve =
                      Env.adds (Y :: y :: z :: ys') (V :: v :: v' :: vs') ve) as ->.
              { unfold Env.adds; simpl.
                symmetry; rewrite Env.add_comm; auto.
                f_equal.
                rewrite Env.add_comm; auto.
              }
              eapply sep_imp; eauto.
              rewrite Comm; unfold Env.adds; simpl; auto.
        }

        clear Hrep Hm'.
        destruct Exec_Ind as (le2 & m2 & ? & Hm2 & ?).
        exists le2, m2; split; [|split]; auto.
        + do 2 match goal with
                 H: exec_stmt _ _ _ _ _ (Ssequence _ _) _ _ _ _ |- _ =>
                 inversion H; contr;
                   edestruct Eapp_E0_inv; eauto;
                     subst; subst
               end.
          match goal with
            H: exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ => inv H
          end.
          repeat eapply exec_Sseq_1; eauto.
    Qed.

  End MatchStatesAssign.

  Lemma set_comm:
    forall {A} x x' (v v': A) m,
      x <> x' ->
      PTree.set x v (PTree.set x' v' m) = PTree.set x' v' (PTree.set x v m).
  Proof.
    induction x, x', m; simpl; intro Neq;
      ((f_equal; apply IHx; intro Eq; apply Neq; now inversion Eq) || now contradict Neq).
  Qed.

  Remark bind_parameter_temps_cons:
    forall x t xs v vs le le',
      bind_parameter_temps ((x, t) :: xs) (v :: vs) le = Some le' ->
      list_norepet (var_names ((x, t) :: xs)) ->
      PTree.get x le' = Some v.
  Proof.
    induction xs as [|[x' t']]; destruct vs;
      intros * Bind Norep; inversion Bind as [Bind'].
    - apply PTree.gss.
    - inversion_clear Norep as [|? ? Notin Norep'].
      apply not_in_cons in Notin; destruct Notin as [? Notin].
      eapply IHxs; eauto.
      + simpl.
        erewrite set_comm in Bind'; eauto.
      + constructor.
        * apply Notin.
        * inversion_clear Norep' as [|? ? ? Norep''].
          apply Norep''.
  Qed.

  Remark bind_parameter_temps_comm:
    forall xs vs s ts o to vself vout x t v le le',
      x <> o ->
      x <> s ->
      (bind_parameter_temps ((s, ts) :: (o, to) :: (x, t) :: xs) (vself :: vout :: v :: vs) le = Some le' <->
       bind_parameter_temps ((x, t) :: (s, ts) :: (o, to) :: xs) (v :: vself :: vout :: vs) le = Some le').
  Proof.
    destruct xs as [|(y, ty)], vs; split; intros * Bind; inv Bind; simpl.
    - f_equal. rewrite (set_comm s x); auto.
      apply set_comm; auto.
    - f_equal. rewrite (set_comm x o); auto.
      f_equal. apply set_comm; auto.
    - do 2 f_equal. rewrite (set_comm s x); auto.
      apply set_comm; auto.
    - do 2 f_equal. rewrite (set_comm x o); auto.
      f_equal. apply set_comm; auto.
  Qed.

  Remark bind_parameter_temps_comm_noout:
    forall xs vs s ts vself x t v le le',
      x <> s ->
      (bind_parameter_temps ((s, ts) :: (x, t) :: xs) (vself :: v :: vs) le = Some le' <->
       bind_parameter_temps ((x, t) :: (s, ts) :: xs) (v :: vself :: vs) le = Some le').
  Proof.
    destruct xs as [|(y, ty)], vs; split; intros * Bind; inv Bind; simpl.
    - f_equal. rewrite (set_comm s x); auto.
    - f_equal. rewrite (set_comm s x); auto.
    - do 2 f_equal. rewrite (set_comm s x); auto.
    - do 2 f_equal. rewrite (set_comm s x); auto.
  Qed.

  Remark bind_parameter_temps_conservation:
    forall xs vs x v le le',
      ~ InMembers x xs ->
      le ! x = v ->
      bind_parameter_temps xs vs le = Some le' ->
      le' ! x = v.
  Proof.
    induction xs as [|(x', t')]; destruct vs;
      intros * Notin Hin Bind; inversion Bind.
    - subst; auto.
    - apply NotInMembers_cons in Notin; destruct Notin.
      clear Bind; eapply IHxs with (le:=PTree.set x' v le); eauto.
      rewrite PTree.gso; auto.
  Qed.

  Remark bind_parameter_temps_implies':
    forall xs vs s ts vself o to vout le le',
      s <> o ->
      ~ InMembers s xs ->
      ~ InMembers o xs ->
      bind_parameter_temps ((s, ts) :: (o, to) :: xs)
                           (vself :: vout :: vs) le = Some le' ->
      le' ! s = Some vself /\ le' ! o = Some vout.
  Proof.
    induction xs as [|(x', t')]; destruct vs;
      intros * Neq Notin_s Notin_o Bind.
    - inv Bind.
      split.
      + now rewrite PTree.gso, PTree.gss.
      + now rewrite PTree.gss.
    - inv Bind.
    - inv Bind.
    - rewrite bind_parameter_temps_comm in Bind.
      + remember ((s, ts)::(o, to)::xs) as xs' in Bind.
        remember (vself::vout::vs) as vs' in Bind.
        unfold bind_parameter_temps in Bind.
        fold Clight.bind_parameter_temps in Bind.
        rewrite Heqxs', Heqvs' in Bind; clear Heqxs' Heqvs'.
        eapply IHxs; eauto; eapply NotInMembers_cons; eauto.
      + intro Eq.
        apply Notin_o.
        subst o. apply inmembers_eq.
      + intro Eq.
        apply Notin_s.
        subst s. apply inmembers_eq.
  Qed.

  Remark bind_parameter_temps_implies'_noout:
    forall xs vs s ts vself le le',
      ~ InMembers s xs ->
      bind_parameter_temps ((s, ts) :: xs)
                           (vself :: vs) le = Some le' ->
      le' ! s = Some vself.
  Proof.
    induction xs as [|(x', t')]; destruct vs;
      intros ???? Neq Notin_s Bind.
    - inv Bind.
      now rewrite PTree.gss.
    - inv Bind.
    - inv Bind.
    - rewrite bind_parameter_temps_comm_noout in Bind.
      + remember ((s, ts)::xs) as xs' in Bind.
        remember (vself::vs) as vs' in Bind.
        unfold bind_parameter_temps in Bind.
        fold Clight.bind_parameter_temps in Bind.
        rewrite Heqxs', Heqvs' in Bind; clear Heqxs' Heqvs'.
        eapply IHxs; eauto; eapply NotInMembers_cons; eauto.
      + intro Eq.
        apply Notin_s.
        subst s. apply inmembers_eq.
  Qed.

  Remark bind_parameter_temps_cons':
    forall xs vs x ty v le le',
      ~ InMembers x xs ->
      bind_parameter_temps xs vs le = Some le' ->
      bind_parameter_temps ((x, ty) :: xs) (v :: vs) le = Some (PTree.set x v le').
  Proof.
    induction xs as [|(x', t')], vs; simpl;
      intros ????? Notin Bind; try discriminate.
    - now inversion Bind.
    - simpl in IHxs.
      rewrite set_comm.
      + apply IHxs; auto.
      + intro; apply Notin; now left.
  Qed.

  Remark bind_parameter_temps_exists:
    forall xs s o ys vs ts to sptr optr,
      s <> o ->
      NoDupMembers xs ->
      ~ InMembers s xs ->
      ~ InMembers o xs ->
      ~ InMembers s ys ->
      ~ InMembers o ys ->
      length xs = length vs ->
      exists le',
        bind_parameter_temps ((s, ts) :: (o, to) :: xs)
                             (sptr :: optr :: vs)
                             (create_undef_temps ys) = Some le'
        /\ Forall (fun xty : ident * Ctypes.type =>
                    let (x, _) := xty in
                    match le' ! x with
                    | Some v => match_value (Env.adds (map fst xs) vs vempty) x v
                    | None => False
                    end) (xs ++ ys).
  Proof.
    induction xs as [|(x, ty)]; destruct vs;
      intros * Hso Nodup Nos Noo Nos' Noo' Hlengths; try discriminate.
    - simpl; econstructor; split; auto.
      unfold match_value, Env.adds; simpl.
      induction ys as [|(y, t)]; simpl; auto.
      assert (y <> s) by (intro; subst; apply Nos'; apply inmembers_eq).
      assert (y <> o) by (intro; subst; apply Noo'; apply inmembers_eq).
      constructor.
      + rewrite Env.gempty.
        do 2 (rewrite PTree.gso; auto).
        now rewrite PTree.gss.
      + apply NotInMembers_cons in Nos'; destruct Nos' as [Nos'].
        apply NotInMembers_cons in Noo'; destruct Noo' as [Noo'].
        specialize (IHys Nos' Noo').
        eapply Forall_impl_In; eauto.
        intros (y', t') Hin Hmatch.
        assert (y' <> s) by (intro; subst; apply Nos'; eapply In_InMembers; eauto).
        assert (y' <> o) by (intro; subst; apply Noo'; eapply In_InMembers; eauto).
        rewrite 2 PTree.gso in *; auto.
        destruct (ident_eqb y' y) eqn: E.
        * apply ident_eqb_eq in E; subst y'.
          rewrite PTree.gss.
          now rewrite Env.gempty.
        * apply ident_eqb_neq in E.
          now rewrite PTree.gso.
    - inv Hlengths; inv Nodup.
      edestruct IHxs with (s:=s) (ts:=ts) (o:=o) (to:=to) (sptr:=sptr) (optr:=optr)
        as (le' & Bind & ?); eauto.
      + eapply NotInMembers_cons; eauto.
      + eapply NotInMembers_cons; eauto.
      + assert (x <> s) by (intro; subst; apply Nos; apply inmembers_eq).
        assert (x <> o) by (intro; subst; apply Noo; apply inmembers_eq).
        exists (PTree.set x v le'); split.
        * rewrite bind_parameter_temps_comm; auto.
          apply bind_parameter_temps_cons'; auto.
          simpl; intros [|[|]]; auto.
        *{ rewrite <-app_comm_cons.
           constructor.
           - rewrite PTree.gss.
             unfold match_value; simpl; rewrite Env.find_gsss; auto.
             now rewrite <-fst_InMembers.
           - eapply Forall_impl_In; eauto.
             intros (x', t') Hin MV.
             destruct (ident_eqb x' x) eqn: E.
             + rewrite ident_eqb_eq in E; subst x'.
               rewrite PTree.gss; unfold match_value; simpl; rewrite Env.find_gsss; auto.
               now rewrite <-fst_InMembers.
             + rewrite ident_eqb_neq in E.
               rewrite PTree.gso; auto.
               destruct le' ! x'; try contradiction.
               unfold match_value in *; simpl.
               rewrite Env.find_gsso; auto.
         }
  Qed.

  Remark bind_parameter_temps_exists_noout:
    forall xs s ys vs ts sptr,
      NoDupMembers xs ->
      ~ InMembers s xs ->
      ~ InMembers s ys ->
      length xs = length vs ->
      exists le',
        bind_parameter_temps ((s, ts) :: xs)
                             (sptr :: vs)
                             (create_undef_temps ys) = Some le'
        /\ Forall (fun xty : ident * Ctypes.type =>
                    let (x, _) := xty in
                    match le' ! x with
                    | Some v => match_value (Env.adds (map fst xs) vs vempty) x v
                    | None => False
                    end) (xs ++ ys).
  Proof.
    induction xs as [|(x, ty)]; destruct vs;
      intros * Nodup Nos Nos' Hlengths; try discriminate.
    - simpl; econstructor; split; auto.
      unfold match_value, Env.adds; simpl.
      induction ys as [|(y, t)]; simpl; auto.
      assert (y <> s) by (intro; subst; apply Nos'; apply inmembers_eq).
      constructor.
      + rewrite Env.gempty, PTree.gso, PTree.gss; auto.
      + apply NotInMembers_cons in Nos'; destruct Nos' as [Nos'].
        specialize (IHys Nos').
        eapply Forall_impl_In; eauto.
        intros (y', t') Hin Hmatch.
        assert (y' <> s) by (intro; subst; apply Nos'; eapply In_InMembers; eauto).
        rewrite PTree.gso in *; auto.
        destruct (ident_eqb y' y) eqn: E.
        * apply ident_eqb_eq in E; subst y'.
          rewrite PTree.gss.
          now rewrite Env.gempty.
        * apply ident_eqb_neq in E.
          now rewrite PTree.gso.
    - inv Hlengths; inv Nodup.
      edestruct IHxs with (s:=s) (ts:=ts) (sptr:=sptr)
        as (le' & Bind & ?); eauto.
      + eapply NotInMembers_cons; eauto.
      + assert (x <> s) by (intro; subst; apply Nos; apply inmembers_eq).
        exists (PTree.set x v le'); split.
        * rewrite bind_parameter_temps_comm_noout; auto.
          apply bind_parameter_temps_cons'; auto.
          simpl; intros [|]; auto.
        *{ rewrite <-app_comm_cons.
           constructor.
           - rewrite PTree.gss.
             simpl.
             unfold match_value; rewrite Env.find_gsss; auto.
             rewrite <-fst_InMembers; auto.
           - eapply Forall_impl_In; eauto.
             intros (x', t') Hin MV.
             destruct (ident_eqb x' x) eqn: E.
             + rewrite ident_eqb_eq in E; subst x'.
               rewrite PTree.gss; unfold match_value; simpl.
               rewrite Env.find_gsss; auto.
               rewrite <-fst_InMembers; auto.
             + rewrite ident_eqb_neq in E.
               rewrite PTree.gso.
               destruct le' ! x'; try contradiction.
               unfold match_value; simpl; rewrite Env.find_gsso; auto.
               auto.
         }
  Qed.

  Remark alloc_implies:
    forall vars x b t e m e' m',
      ~ InMembers x vars ->
      alloc_variables tge (PTree.set x (b, t) e) m vars e' m' ->
      e' ! x = Some (b, t).
  Proof.
    induction vars as [|(x', t')]; intros * Notin H;
      inversion_clear H as [|? ? ? ? ? ? ? ? ? ? Halloc]; subst.
    - apply PTree.gss.
    - rewrite <-set_comm in Halloc.
      + eapply IHvars; eauto.
        eapply NotInMembers_cons; eauto.
      + intro; subst x; apply Notin; apply inmembers_eq.
  Qed.

  Remark In_drop_block:
    forall elts x t,
      In (x, t) (map drop_block elts) ->
      exists b, In (x, (b, t)) elts.
  Proof.
    induction elts as [|(x', (b', t'))]; simpl; intros * Hin.
    - contradiction.
    - destruct Hin as [Eq|Hin].
      + inv Eq.
        exists b'; now left.
      + apply IHelts in Hin.
        destruct Hin as [b Hin].
        exists b; now right.
  Qed.

  Remark drop_block_In:
    forall elts x b t,
      In (x, (b, t)) elts ->
      In (x, t) (map drop_block elts).
  Proof.
    induction elts as [|(x', (b', t'))]; simpl; intros * Hin.
    - contradiction.
    - destruct Hin as [Eq|Hin].
      + inv Eq.
        now left.
      + apply IHelts in Hin.
        now right.
  Qed.

  Remark alloc_In:
    forall vars e m e' m',
      alloc_variables tge e m vars e' m' ->
      NoDupMembers vars ->
      (forall x t,
          In (x, t) (map drop_block (PTree.elements e')) <->
          (In (x, t) (map drop_block (PTree.elements e)) /\ (forall t', In (x, t') vars -> t = t'))
          \/ In (x, t) vars).
  Proof.
    intro vars.
    induction_list vars as [|(y, ty)] with vars'; intros * Alloc Nodup x t;
      inv Alloc; inv Nodup.
    - split; simpl.
      + intros. left; split; auto.
        intros; contradiction.
      + intros [[? ?]|?]; auto.
        contradiction.
    - edestruct IHvars' with (x:=x) (t:=t) as [In_Or Or_In]; eauto.
      clear IHvars'.
      split.
      + intro Hin.
        apply In_Or in Hin.
        destruct Hin as [[Hin Ht]|?].
        *{ destruct (ident_eqb x y) eqn: E.
           - apply ident_eqb_eq in E.
             subst y.
             apply In_drop_block in Hin.
             destruct Hin as [b Hin].
             apply PTree.elements_complete in Hin.
             rewrite PTree.gss in Hin.
             inv Hin.
             right; apply in_eq.
           - apply ident_eqb_neq in E.
             apply In_drop_block in Hin.
             destruct Hin as [b Hin].
             apply PTree.elements_complete in Hin.
             rewrite PTree.gso in Hin; auto.
             apply PTree.elements_correct in Hin.
             left; split.
             + eapply drop_block_In; eauto.
             + intros t' [Eq|Hin'].
               * inv Eq. now contradict E.
               * now apply Ht.

         }
        * right; now apply in_cons.
      + intros [[Hin Ht]|Hin]; apply Or_In.
        *{ left; split.
           - destruct (ident_eqb x y) eqn: E.
             + apply ident_eqb_eq in E.
               subst y.
               apply drop_block_In with (b:=b1).
               apply PTree.elements_correct.
               rewrite PTree.gss.
               repeat f_equal.
               symmetry; apply Ht.
               apply in_eq.
             + apply ident_eqb_neq in E.
               apply In_drop_block in Hin.
               destruct Hin as [b Hin].
               apply drop_block_In with (b:=b).
               apply PTree.elements_correct.
               rewrite PTree.gso; auto.
               now apply PTree.elements_complete.
           - intros.
             apply Ht.
             now apply in_cons.
         }
        *{ inversion_clear Hin as [Eq|?].
           - inv Eq.
             left; split.
             + apply drop_block_In with (b:=b1).
               apply PTree.elements_correct.
               now rewrite PTree.gss.
             + intros * Hin.
               contradict Hin.
               apply NotInMembers_NotIn; auto.
           - now right.
         }
  Qed.

  Remark alloc_mem_vars:
    forall vars e m e' m' P,
      m |= P ->
      NoDupMembers vars ->
      Forall (fun xt => sizeof tge (snd xt) <= Ptrofs.max_unsigned) vars ->
      alloc_variables tge e m vars e' m' ->
      m' |= sepall (range_inst_env e') (var_names vars) ** P.
  Proof.
    induction vars as [|(y, t)];
      intros * Hrep Nodup Forall Alloc;
      inv Alloc; subst; simpl.
    - now rewrite <-sepemp_left.
    - inv Nodup; inv Forall.
      unfold range_inst_env at 1.
      erewrite alloc_implies; eauto.
      rewrite sep_assoc, sep_swap.
      eapply IHvars; eauto.
      eapply alloc_rule; eauto; try omega.
      transitivity Ptrofs.max_unsigned; auto.
      unfold Ptrofs.max_unsigned.
      omega.
  Qed.

  Remark alloc_permutation:
    forall vars m e' m',
      alloc_variables tge empty_env m vars e' m' ->
      NoDupMembers vars ->
      Permutation vars (map drop_block (PTree.elements e')).
  Proof.
    intros * Alloc Nodup.
    pose proof (alloc_In _ _ _ _ _ Alloc) as H.
    apply NoDup_Permutation.
    - apply NoDupMembers_NoDup; auto.
    - pose proof (PTree.elements_keys_norepet e') as Norep.
      clear H.
      induction (PTree.elements e') as [|(x, (b, t))]; simpl in *; constructor.
      + inversion_clear Norep as [|? ? Notin Norep'].
        clear IHl.
        induction l as [|(x', (b', t'))]; simpl in *.
        * intro; contradiction.
        *{ intros [Eq | Hin].
           - inv Eq. apply Notin. now left.
           - inv Norep'. apply IHl; auto.
         }
      + inversion_clear Norep as [|? ? Notin Norep'].
        apply IHl; auto.
    - intros (x, t).
      specialize (H Nodup x t).
      intuition.
  Qed.

  Lemma Permutation_set:
    forall {A B} x (a:A) (b:B) e,
      ~InMembers x (PTree.elements e) ->
      Permutation (PTree.elements (PTree.set x (a, b) e))
                  ((x, (a, b)) :: PTree.elements e).
  Proof.
    intros * Hin.
    apply NoDup_Permutation.
    - apply NoDup_map_inv with (f:=fst).
      apply NoDup_norepet.
      apply PTree.elements_keys_norepet.
    - constructor.
      now apply NotInMembers_NotIn.
      apply NoDup_map_inv with (f:=fst).
      apply NoDup_norepet.
      apply PTree.elements_keys_norepet.
    - intro y. destruct y as [y y'].
      split; intro HH.
      + apply PTree.elements_complete in HH.
        rewrite PTree.gsspec in HH.
        destruct (peq y x).
        * injection HH; intro; subst; now constructor.
        * apply PTree.elements_correct in HH; now constructor 2.
      + apply in_inv in HH.
        destruct HH as [HH|HH].
        * destruct y' as [y' y''].
          injection HH; intros; subst.
          apply PTree.elements_correct.
          rewrite PTree.gsspec.
          now rewrite peq_true.
        * apply PTree.elements_correct.
          rewrite PTree.gso.
          now apply PTree.elements_complete.
          intro Heq; rewrite Heq in *.
          apply Hin.
          apply In_InMembers with (1:=HH).
  Qed.

  Lemma set_nodupmembers:
    forall x (e: Clight.env) b1 t,
      NoDupMembers (map snd (PTree.elements e)) ->
      ~InMembers x (PTree.elements e) ->
      ~InMembers b1 (map snd (PTree.elements e)) ->
      NoDupMembers (map snd (PTree.elements (PTree.set x (b1, t) e))).
  Proof.
    intros * Nodup Notin Diff.
    assert (Permutation (map snd (PTree.elements (PTree.set x (b1, t) e)))
                        ((b1, t) :: (map snd (PTree.elements e)))) as Perm.
    { change (b1, t) with (snd (x, (b1, t))).
      rewrite <-map_cons.
      now apply Permutation_map, Permutation_set.
    }
    rewrite Perm.
    simpl; constructor; auto.
  Qed.

  Remark alloc_nodupmembers:
    forall vars e m e' m',
      alloc_variables tge e m vars e' m' ->
      NoDupMembers vars ->
      NoDupMembers (map snd (PTree.elements e)) ->
      Forall (fun xv => ~InMembers (fst xv) (PTree.elements e)) vars ->
      (forall b, InMembers b (map snd (PTree.elements e)) -> Mem.valid_block m b) ->
      NoDupMembers (map snd (PTree.elements e')).
  Proof.
    induction vars as [|(x, t)]; intros * Alloc Nodupvars Nodup Forall Valid;
      inversion Nodupvars as [|? ? ? Notin Nodupvars']; clear Nodupvars;
        inversion Alloc as [|? ? ? ? ? ? ? ? ? Hmem Alloc']; clear Alloc;
          inversion Forall as [|? ? Hnin Hforall]; clear Forall; subst; auto.
    apply IHvars with (e:=PTree.set x (b1, t) e) (m:=m1) (m':=m'); auto.
    - apply set_nodupmembers; auto.
      intros Hinb.
      apply Valid in Hinb.
      eapply Mem.valid_not_valid_diff; eauto.
      eapply Mem.fresh_block_alloc; eauto.
    - clear IHvars Alloc'.
      induction vars as [|(x', t')]; constructor;
        inv Hforall; inv Nodupvars'; apply NotInMembers_cons in Notin; destruct Notin.
      + rewrite Permutation_set; auto.
        apply NotInMembers_cons; split; auto.
      + apply IHvars; auto.
    - intros b Hinb.
      destruct (eq_block b b1) as [Eq|Neq].
      + subst b1; eapply Mem.valid_new_block; eauto.
      + assert (InMembers b (map snd (PTree.elements e))) as Hin.
        { apply InMembers_snd_In in Hinb; destruct Hinb as (x' & t' & Hin).
          apply (In_InMembers_snd x' _ t').
          apply PTree.elements_complete in Hin.
          destruct (ident_eqb x x') eqn: E.
          - apply ident_eqb_eq in E; subst x'.
            rewrite PTree.gss in Hin.
            inv Hin. now contradict Neq.
          - apply ident_eqb_neq in E.
            rewrite PTree.gso in Hin; auto.
            now apply PTree.elements_correct.
        }
        apply Valid in Hin.
        eapply Mem.valid_block_alloc; eauto.
  Qed.

  Remark alloc_exists:
    forall vars e m,
      NoDupMembers vars ->
      exists e' m',
        alloc_variables tge e m vars e' m'.
  Proof.
    induction vars as [|(x, t)]; intros * Nodup.
    - exists e, m; constructor.
    - inv Nodup.
      destruct (Mem.alloc m 0 (Ctypes.sizeof gcenv t)) as (m1 & b) eqn: Eq.
      edestruct IHvars with (e:=PTree.set x (b, t) e) (m:=m1)
        as (e' & m' & Halloc); eauto.
      exists e', m'; econstructor; eauto.
  Qed.

  Remark Permutation_fst:
    forall vars elems,
      Permutation vars elems ->
      Permutation (var_names vars) (map fst elems).
  Proof.
    intros * Perm.
    induction Perm; simpl; try constructor; auto.
    transitivity (map fst l'); auto.
  Qed.

  Remark map_fst_drop_block:
    forall elems,
      map fst (map drop_block elems) = map fst elems.
  Proof.
    induction elems as [|(x, (b, t))]; simpl; auto.
    now f_equal.
  Qed.

  Lemma alloc_result:
    forall f m P,
      let vars := instance_methods f in
      Forall (fun xt: positive * Ctypes.type =>
                sizeof tge (snd xt) <= Ptrofs.max_unsigned
                /\ exists (id : AST.ident) (co : composite),
                  snd xt = Tstruct id noattr
                  /\ gcenv ! id = Some co
                  /\ co_su co = Struct
                  /\ NoDupMembers (co_members co)
                  /\ (forall (x' : AST.ident) (t' : Ctypes.type),
                         In (x', t') (co_members co) ->
                         exists chunk : AST.memory_chunk,
                           access_mode t' = By_value chunk
                           /\ (align_chunk chunk | alignof gcenv t')))
             (make_out_vars vars) ->
      NoDupMembers (make_out_vars vars) ->
      m |= P ->
      exists e' m',
        alloc_variables tge empty_env m (make_out_vars vars) e' m'
        /\ (forall x b t, e' ! x = Some (b, t) -> exists o f, x = prefix_out o f)
        /\ m' |= subrep f e'
               ** (subrep f e' -* subrep_range e')
               ** P.
  Proof.
    intros * Hforall Nodup Hrep; subst.
    rewrite <-Forall_Forall' in Hforall; destruct Hforall.
    pose proof (alloc_exists _ empty_env m Nodup) as Alloc.
    destruct Alloc as (e' & m' & Alloc).
    eapply alloc_mem_vars in Hrep; eauto.
    pose proof Alloc as Perm.
    apply alloc_permutation in Perm; auto.
    exists e', m'; split; [auto|split].
    - intros * Hget.
      apply PTree.elements_correct in Hget.
      apply in_map with (f:=drop_block) in Hget.
      apply Permutation_sym in Perm.
      rewrite Perm in Hget.
      unfold make_out_vars in Hget; simpl in Hget.
      apply in_map_iff in Hget.
      destruct Hget as (((o, f'), c) & Eq & Hget).
      inv Eq. now exists o, f'.
    - pose proof Perm as Perm_fst.
      apply Permutation_fst in Perm_fst.
      rewrite map_fst_drop_block in Perm_fst.
      rewrite Perm_fst in Hrep.
      rewrite <-subrep_range_eqv in Hrep.
      repeat rewrite subrep_eqv; auto.
      rewrite range_wand_equiv in Hrep.
      + now rewrite sep_assoc in Hrep.
      + eapply Permutation_Forall; eauto.
      + eapply alloc_nodupmembers; eauto.
        * unfold PTree.elements; simpl; constructor.
        * unfold PTree.elements; simpl.
          clear H H0 Nodup Alloc Perm Perm_fst.
          induction (make_out_vars vars); constructor; auto.
        * intros * Hin.
          unfold PTree.elements in Hin; simpl in Hin.
          contradiction.
  Qed.

  Lemma compat_funcall_pres:
    forall f sb sofs ob ob_co vs c prog' prog'' o owner d me tself tout callee_id callee instco m P,
      let vargs := Vptr sb (Ptrofs.add sofs (Ptrofs.repr d))
                        :: match callee.(m_out) with
                           | [] | [_] => vs
                           | _ => Vptr ob Ptrofs.zero :: vs
                           end
      in
      c.(c_name) <> owner.(c_name) ->
      In (o, c.(c_name)) owner.(c_objs) ->
      field_offset gcenv o (make_members owner) = Errors.OK d ->
      0 <= (Ptrofs.unsigned sofs) + d <= Ptrofs.max_unsigned ->
      0 <= Ptrofs.unsigned sofs ->
      find_class owner.(c_name) prog = Some (owner, prog') ->
      find_class c.(c_name) prog = Some (c, prog'') ->
      find_method callee_id c.(c_methods) = Some callee ->
      length f.(fn_params) = length vargs ->
      fn_params f = (self, tself)
                      :: match callee.(m_out) with
                         | [] | [_] => map translate_param callee.(m_in)
                         | _ => (out, tout) :: map translate_param callee.(m_in)
                         end ->
      fn_vars f = make_out_vars (instance_methods callee) ->
      fn_temps f = match callee.(m_out) with
                   | [yt] => [translate_param yt]
                   | _ => []
                   end
                     ++ make_out_temps (instance_methods_temp (rev prog) callee)
                     ++ map translate_param callee.(m_vars) ->
      list_norepet (var_names f.(fn_params)) ->
      list_norepet (var_names f.(fn_vars)) ->
      match callee.(m_out) with
      | [] | [_] => True
      | _ =>
        ob_co = Some (ob, instco)
        /\ gcenv ! (prefix_fun c.(c_name) callee.(m_name)) = Some instco
      end ->
      m |= staterep gcenv prog owner.(c_name) me sb (Ptrofs.unsigned sofs)
          ** match callee.(m_out) with
             | [] | [_] => sepemp
             | _ => blockrep gcenv vempty instco.(co_members) ob
             end
          ** P ->
      exists e_fun le_fun m_fun ws xs,
        bind_parameter_temps f.(fn_params) vargs (create_undef_temps f.(fn_temps)) = Some le_fun
        /\ alloc_variables tge empty_env m f.(fn_vars) e_fun m_fun
        /\ (forall x b t, e_fun ! x = Some (b, t) -> exists o f, x = prefix_out o f)
        /\ le_fun ! self = Some (Vptr sb (Ptrofs.add sofs (Ptrofs.repr d)))
        /\ c_objs owner = ws ++ (o, c.(c_name)) :: xs
        /\ m_fun |= sepall (staterep_mems gcenv owner me sb (Ptrofs.unsigned sofs)) (c_mems owner)
                  ** staterep gcenv prog c.(c_name)
                              (match find_inst o me with Some om => om | None => mempty end)
                              sb (Ptrofs.unsigned (Ptrofs.add sofs (Ptrofs.repr d)))
                  ** sepall (staterep_objs gcenv prog' owner me sb (Ptrofs.unsigned sofs)) (ws ++ xs)
                  ** match_out c callee (Env.adds (map fst callee.(m_in)) vs vempty) le_fun ob_co
                  ** subrep callee e_fun
                  ** (subrep callee e_fun -* subrep_range e_fun)
                  ** varsrep callee (Env.adds (map fst callee.(m_in)) vs vempty) le_fun
                  ** P
        /\ 0 <= Ptrofs.unsigned (Ptrofs.add sofs (Ptrofs.repr d)) <= Ptrofs.max_unsigned.
  Proof.
    intros * ? Hin Offs ? ? Findowner Findc Hcallee Hlengths
           Hparams Hvars Htemps Norep_par Norep_vars Hinstco Hrep.
    subst vargs; rewrite Hparams, Hvars, Htemps in *.
    assert (~ InMembers self (meth_vars callee)) as Notin_s
        by apply m_notreserved, in_eq.
    assert (~ InMembers out (meth_vars callee)) as Notin_o
        by apply m_notreserved, in_cons, in_eq.
    assert (~ InMembers self (map translate_param (m_in callee))).
    { unfold meth_vars in Notin_s; apply NotInMembers_app in Notin_s.
      rewrite fst_InMembers, translate_param_fst, <-fst_InMembers; tauto.
    }
    assert (~ InMembers self (map translate_param (m_out callee))).
    { unfold meth_vars in Notin_s; repeat rewrite NotInMembers_app in Notin_s.
      rewrite fst_InMembers, translate_param_fst, <-fst_InMembers; tauto.
    }
    assert (~ InMembers out (map translate_param (m_in callee))).
    { unfold meth_vars in Notin_o; apply NotInMembers_app in Notin_o.
      rewrite fst_InMembers, translate_param_fst, <-fst_InMembers; tauto.
    }
    assert (~ InMembers self (map translate_param (m_vars callee))).
    { unfold meth_vars in Notin_s; rewrite Permutation_app_comm, <-app_assoc in Notin_s;
        apply NotInMembers_app in Notin_s.
      rewrite fst_InMembers, translate_param_fst, <-fst_InMembers; tauto.
    }
    assert (~ InMembers out (map translate_param (m_vars callee))).
    { unfold meth_vars in Notin_o; rewrite Permutation_app_comm, <-app_assoc in Notin_o;
        apply NotInMembers_app in Notin_o.
      rewrite fst_InMembers, translate_param_fst, <-fst_InMembers; tauto.
    }
    assert (~ InMembers self (make_out_temps (instance_methods_temp (rev prog) callee))).
    { intro Hin_s.
      apply make_out_temps_prefixed in Hin_s.
      apply self_not_prefixed; auto.
    }
    assert (~ InMembers out (make_out_temps (instance_methods_temp (rev prog) callee))).
    { intro Hin_o.
      apply make_out_temps_prefixed in Hin_o.
      apply out_not_prefixed; auto.
    }
    assert (0 <= d <= Ptrofs.max_unsigned) by
        (split; [eapply field_offset_in_range'; eauto | omega]).
    assert (NoDupMembers (map translate_param (m_in callee))).
    { pose proof (m_nodupvars callee) as Nodup.
      rewrite Permutation_app_comm in Nodup.
      apply NoDupMembers_app_r in Nodup.
      rewrite fst_NoDupMembers, translate_param_fst, <-fst_NoDupMembers; auto.
    }
    assert (Forall (fun xt => sizeof tge (snd xt) <= Int.max_unsigned /\
                           (exists (id : AST.ident) (co : composite),
                               snd xt = Tstruct id noattr /\
                               gcenv ! id = Some co /\
                               co_su co = Struct /\
                               NoDupMembers (co_members co) /\
                               (forall (x' : AST.ident) (t' : Ctypes.type),
                                   In (x', t') (co_members co) ->
                                   exists chunk : AST.memory_chunk,
                                     access_mode t' = By_value chunk /\
                                     (align_chunk chunk | alignof gcenv t'))))
                   (make_out_vars (instance_methods callee)))
      by (eapply instance_methods_caract; eauto).
    assert (NoDupMembers (make_out_vars (instance_methods callee)))
      by (unfold var_names in Norep_vars; now rewrite fst_NoDupMembers, NoDup_norepet).
    assert (0 <= Ptrofs.unsigned (Ptrofs.add sofs (Ptrofs.repr d)) <= Ptrofs.max_unsigned)
      by (split; unfold Ptrofs.add; repeat (rewrite Ptrofs.unsigned_repr; auto); omega).
    assert (exists ws xs,
               c_objs owner = ws ++ (o, c_name c) :: xs /\
               staterep gcenv prog (c_name owner) me sb (Ptrofs.unsigned sofs) -*>
               sepall (staterep_mems gcenv owner me sb (Ptrofs.unsigned sofs)) (c_mems owner)
                       ** staterep gcenv prog (c_name c) match find_inst o me with
                                                         | Some om => om
                                                         | None => mempty
                                                         end sb (Ptrofs.unsigned (Ptrofs.add sofs (Ptrofs.repr d)))
               ** sepall (staterep_objs gcenv prog' owner me sb (Ptrofs.unsigned sofs)) (ws ++ xs))
      as Hwsxs.
    { pose proof Hin as Hin'.
      apply sepall_in in Hin.
      destruct Hin as (ws & xs & Hin & Heq).
      exists ws, xs; split; auto.
      edestruct find_class_app with (1:=Findowner)
        as (pre_prog & Hprog & FindNone); eauto.
      rewrite Hprog in WT.
      eapply wt_program_not_class_in in WT; eauto.
      rewrite staterep_skip; eauto.
      simpl.
      rewrite ident_eqb_refl.
      apply sep_imp'; auto.
      rewrite Heq, Offs.
      apply sep_imp'; auto.
      unfold instance_match.
      erewrite <-staterep_skip_cons; eauto.
      erewrite <-staterep_skip_app; eauto.
      rewrite <-Hprog.
      unfold Ptrofs.add; repeat (rewrite Ptrofs.unsigned_repr; auto).
    }
    destruct Hwsxs as (ws & xs & ? & ?).

    destruct_list (m_out callee) as (y, t) ? ? : E.
    - edestruct
        (bind_parameter_temps_exists_noout (map translate_param callee.(m_in)) self
                                           (make_out_temps (instance_methods_temp (rev prog) callee)
                                                           ++ map translate_param callee.(m_vars)) vs
                                           tself (Vptr sb (Ptrofs.add sofs (Ptrofs.repr d))))
        as (le_fun & Bind & Hinputs); eauto.
      + rewrite NotInMembers_app; auto.
      + edestruct (alloc_result callee) as (e_fun & m_fun & ? & ? & Hm_fun); eauto.
        assert (le_fun ! self = Some (Vptr sb (Ptrofs.add sofs (Ptrofs.repr d)))) by
            (eapply (bind_parameter_temps_implies'_noout (map translate_param (m_in callee))); eauto).
        simpl.
        exists e_fun, le_fun, m_fun, ws, xs;
          split; [|split; [|split; [|split; [|split; [|split]]]]]; auto.
        rewrite sep_swap34, sep_swap23, sep_swap, match_out_nil in *; auto.
        rewrite <-sepemp_left in Hm_fun.
        rewrite <- 4 sep_assoc; rewrite sep_swap.
        rewrite translate_param_fst in Hinputs.
        apply sep_pure; split.
        * rewrite map_app; repeat rewrite Forall_app in *; repeat rewrite Forall_app in Hinputs.
          tauto.
        * rewrite sep_assoc, sep_swap, sep_assoc, sep_swap23, sep_swap.
          eapply sep_imp; eauto.
          apply sep_imp'; auto.
          apply sep_imp'; auto.
          rewrite sep_assoc, sep_swap; auto.

    - edestruct
        (bind_parameter_temps_exists_noout (map translate_param callee.(m_in)) self
                                           (translate_param (y, t) ::
                                                            make_out_temps (instance_methods_temp (rev prog) callee)
                                                            ++ map translate_param callee.(m_vars)) vs
                                           tself (Vptr sb (Ptrofs.add sofs (Ptrofs.repr d))))
        as (le_fun & Bind & Hinputs); eauto.
      + rewrite cons_is_app. repeat rewrite NotInMembers_app; tauto.
      + edestruct (alloc_result callee) as (e_fun & m_fun & ? & ? & Hm_fun); eauto.
        assert (le_fun ! self = Some (Vptr sb (Ptrofs.add sofs (Ptrofs.repr d)))) by
            (eapply (bind_parameter_temps_implies'_noout (map translate_param (m_in callee))); eauto).
        simpl.
        exists e_fun, le_fun, m_fun, ws, xs;
          split; [|split; [|split; [|split; [|split; [|split]]]]]; auto.
        rewrite sep_swap34, sep_swap23, sep_swap, match_out_singleton,
        sep_swap, sep_swap23, sep_swap34 in *; eauto.
        split; auto.
        *{ rewrite <- 4 sep_assoc; rewrite sep_swap.
           rewrite translate_param_fst in Hinputs.
           apply sep_pure; split.
           - rewrite map_app; simpl in Hinputs; rewrite Forall_app, Forall_cons2, Forall_app in Hinputs.
             rewrite Forall_app; tauto.
           - rewrite sep_assoc, sep_swap, sep_assoc, sep_swap23, sep_assoc, sep_swap34, sep_swap23, sep_swap.
             eapply sep_imp; eauto.
             apply sep_imp'; auto.
             rewrite <-sepemp_left.
             rewrite <-sep_assoc.
             apply sep_imp'; auto.
         }
        *{ pose proof (m_nodupvars callee) as Nodup.
           rewrite Permutation_app_comm, <-app_assoc, E in Nodup.
           apply NoDupMembers_app_r in Nodup.
           rewrite <-cons_is_app in Nodup.
           inversion_clear Nodup as [|? ? ? Notin].
           rewrite fst_InMembers in Notin.
           rewrite Env.gsso, Env.gempty; auto.
           rewrite <-fst_InMembers in Notin.
           eapply bind_parameter_temps_conservation; eauto.
           - apply NotInMembers_cons; split.
             + rewrite InMembers_translate_param_idem; auto.
             + simpl in *; auto.
           - simpl; apply PTree.gss.
         }

    - edestruct
        (bind_parameter_temps_exists (map translate_param callee.(m_in)) self out
                                     (make_out_temps (instance_methods_temp (rev prog) callee)
                                                     ++ map translate_param callee.(m_vars)) vs
                                     tself tout (Vptr sb (Ptrofs.add sofs (Ptrofs.repr d))) (Vptr ob Ptrofs.zero))
      with (1:=self_not_out) as (le_fun & Bind & Hinputs); eauto.
      + rewrite NotInMembers_app; auto.
      + rewrite NotInMembers_app; auto.
      + simpl in Hlengths. inversion Hlengths; eauto.
      + edestruct (alloc_result callee) as (e_fun & m_fun & ? & ? & Hm_fun); eauto.
        edestruct (bind_parameter_temps_implies' (map translate_param (m_in callee)))
        with (1:=self_not_out) as (? & ?); eauto.
        exists e_fun, le_fun, m_fun, ws, xs;
          split; [|split; [|split; [|split; [|split; [|split]]]]]; auto.
        assert (1 < length (m_out callee))%nat by (rewrite E; simpl; omega).
        destruct Hinstco.
        rewrite sep_swap34, sep_swap23, sep_swap, match_out_notnil,
        sep_swap, sep_swap23, sep_swap34 in *; auto.
        exists ob, instco; split; [|split]; auto.
        rewrite <- 5 sep_assoc; rewrite sep_swap.
        rewrite translate_param_fst in Hinputs.
        apply sep_pure; split.
        * rewrite map_app; repeat rewrite Forall_app in Hinputs; rewrite Forall_app; intuition.
        * rewrite sep_assoc, sep_swap, sep_assoc, sep_swap23, sep_swap.
          eapply sep_imp; eauto.
          apply sep_imp'; auto.
          rewrite sep_swap, <-sep_assoc.
          apply sep_imp'; auto.
          rewrite 2 sep_assoc.
          apply sep_imp'; auto.
          rewrite <-translate_param_fst.
          erewrite <-output_match; eauto.
          apply blockrep_nodup.
          pose proof (m_nodupvars callee) as Nodup.
          rewrite app_assoc, Permutation_app_comm, app_assoc, Permutation_app_comm in Nodup.
          apply NoDupMembers_app_r in Nodup; rewrite Permutation_app_comm in Nodup.
          rewrite <-map_app, fst_NoDupMembers, translate_param_fst, <-fst_NoDupMembers; auto.
  Qed.

  Remark type_pres':
    forall f c caller es,
      Forall2 (fun e x => typeof e = snd x) es f.(m_in) ->
      type_of_params (map translate_param f.(m_in)) =
      list_type_to_typelist (map Clight.typeof (map (translate_exp c caller) es)).
  Proof.
    intro f.
    induction (m_in f) as [|(x, t)]; intros * Heq;
      inversion_clear Heq as [|? ? ? ? Ht]; simpl; auto.
    f_equal.
    - simpl in Ht; rewrite <-Ht.
      now rewrite type_pres.
    - now apply IHl.
  Qed.

  Lemma free_exists:
    forall e m P,
      m |= subrep_range e ** P ->
      exists m',
        Mem.free_list m (blocks_of_env tge e) = Some m'
        /\ m' |= P.
  Proof.
    intro e.
    unfold subrep_range, blocks_of_env.
    induction (PTree.elements e) as [|(x,(b,ty))];
      simpl; intros * Hrep.
    - exists m; split; auto.
      now rewrite sepemp_left.
    - rewrite sep_assoc in Hrep.
      apply free_rule in Hrep.
      destruct Hrep as (m1 & Hfree & Hm1).
      rewrite Hfree.
      now apply IHl.
  Qed.

  Lemma subrep_extract:
    forall f f' e m o c' P,
      m |= subrep f e ** P ->
      M.MapsTo (o, f') c' (instance_methods f) ->
      exists b co ws xs,
        e ! (prefix_out o f') = Some (b, type_of_inst (prefix_fun c' f'))
        /\ gcenv ! (prefix_fun c' f') = Some co
        /\ make_out_vars (instance_methods f) = ws ++ (prefix_out o f', type_of_inst (prefix_fun c' f')) :: xs
        /\ m |= blockrep gcenv vempty (co_members co) b
              ** sepall (subrep_inst_env e) (ws ++ xs)
              ** P.
  Proof.
    intros * Hrep Hin.
    unfold subrep, subrep_inst in *.
    assert (In (prefix_out o f', type_of_inst (prefix_fun c' f')) (make_out_vars (instance_methods f))) as Hin'.
    { apply M.elements_1, setoid_in_key_elt in Hin.
      apply in_map with
      (f:=fun x => let '(o0, f0, cid) := x in (prefix_out o0 f0, type_of_inst (prefix_fun cid f0))) in Hin.
      unfold make_out_vars; auto.
    }
    clear Hin.
    apply sepall_in in Hin'; destruct Hin' as (ws & xs & Hin & Heq).
    repeat rewrite Heq in Hrep.
    pose proof Hrep as Hrep'.
    do 2 apply sep_proj1 in Hrep.
    unfold subrep_inst_env in *.
    destruct e ! (prefix_out o f'); [|contradict Hrep].
    destruct p as (oblk, t).
    destruct t; try now contradict Hrep.
    destruct (type_eq (type_of_inst (prefix_fun c' f')) (Tstruct i a)) as [Eq|]; [|contradict Hrep].
    unfold type_of_inst in Eq.
    inv Eq.
    destruct gcenv ! (prefix_fun c' f'); [|contradict Hrep].
    rewrite sep_assoc in Hrep'.
    exists oblk, c, ws, xs; split; auto.
  Qed.

  Lemma stmt_call_eval_sub_prog:
    forall p p' me clsid f vs ome rvs,
      stmt_call_eval p me clsid f vs ome rvs ->
      wt_program p' ->
      sub_prog p p' ->
      stmt_call_eval p' me clsid f vs ome rvs.
  Proof.
    intros * Ev ? ?.
    induction Ev.
    econstructor; eauto.
    eapply find_class_sub_same; eauto.
  Qed.
  Hint Resolve stmt_call_eval_sub_prog.

  Lemma stmt_eval_sub_prog:
    forall p p' me ve s S,
      stmt_eval p me ve s S ->
      wt_program p' ->
      sub_prog p p' ->
      stmt_eval p' me ve s S.
  Proof.
    intros * Ev ? ?.
    induction Ev; econstructor; eauto.
  Qed.
  Hint Resolve stmt_eval_sub_prog.

  Program Definition empty_co: composite :=
    {|
      co_su := Struct;
      co_members := [];
      co_attr := noattr;
      co_sizeof := 0;
      co_alignof := 1;
      co_rank := 0
    |}.
  Next Obligation.
    exists 0%nat; now rewrite two_power_nat_O.
  Defined.
  Next Obligation.
    apply Z.divide_0_r.
  Defined.

  Section CORRECTNESS.

    Hypothesis SPEC_IO:
      forall ome ome' clsid f vos rvos,
        Forall (fun vo => vo <> None) vos ->
        stmt_call_eval prog ome clsid f vos ome' rvos ->
        Forall (fun x => x <> None) rvos.

    Hypothesis NO_NAKED_VARS: Forall_methods (fun m => No_Naked_Vars m.(m_body)) prog.

    Theorem correctness:
      (forall p me1 ve1 s S2,
          stmt_eval p me1 ve1 s S2 ->
          sub_prog p prog ->
          forall c prog' f
            (Occurs: occurs_in s (m_body f))
            (NNaked: No_Naked_Vars s)
            (WF    : wt_stmt prog c.(c_objs) c.(c_mems) (meth_vars f) s)
            (Find  : find_class c.(c_name) prog = Some (c, prog'))
            (Hf    : find_method f.(m_name) c.(c_methods) = Some f),
          forall e1 le1 m1 sb sofs outb_co P
            (MS: m1 |= match_states c f (me1, ve1) (e1, le1) sb sofs outb_co ** P),
          exists le2 m2,
            exec_stmt tge (function_entry2 tge) e1 le1 m1
                      (translate_stmt (rev prog) c f s) E0 le2 m2 Out_normal
            /\ m2 |= match_states c f S2 (e1, le2) sb sofs outb_co ** P)
      /\
      (forall p me1 clsid fid ovs me2 rvs,
          stmt_call_eval p me1 clsid fid ovs me2 rvs ->
          sub_prog p prog ->
          forall owner c caller callee prog' prog'' me ve e1 le1 m1 o cf ptr_f sb
            d sofs outb_co outb_callee outco_callee vs P,
            let oty := type_of_inst (prefix_fun clsid fid) in
            ovs = map Some vs ->
            find_class owner.(c_name) prog = Some (owner, prog'') ->
            find_method caller.(m_name) owner.(c_methods) = Some caller ->
            find_class clsid prog = Some (c, prog') ->
            find_method fid c.(c_methods) = Some callee ->
            m1 |= staterep gcenv prog owner.(c_name) me sb (Ptrofs.unsigned sofs)
                                                     ** match_out owner caller ve le1 outb_co
                                                     ** subrep caller e1
                                                     ** varsrep caller ve le1
                                                     ** P ->
            struct_in_bounds gcenv 0 Ptrofs.max_unsigned (Ptrofs.unsigned sofs) (make_members owner) ->
            wt_env (Env.adds (map fst (m_in callee)) vs vempty) (meth_vars callee) ->
            wt_mem me1 prog' c ->
            Forall2 (fun v (xt : ident * type) => wt_val v (snd xt)) vs (m_in callee) ->
            Globalenvs.Genv.find_symbol tge (prefix_fun clsid fid) = Some ptr_f ->
            Globalenvs.Genv.find_funct_ptr tge ptr_f = Some (Ctypes.Internal cf) ->
            length cf.(fn_params) = (match callee.(m_out) with
                                     | [] | [_] => 1
                                     | _ => 2
                                     end + length vs)%nat ->
            me1 = match find_inst o me with Some om => om | None => mempty end ->
            match callee.(m_out) with
            | [] | [_] => True
            | _ => e1 ! (prefix_out o fid) = Some (outb_callee, oty)
            end ->
            In (o, clsid) owner.(c_objs) ->
            match callee.(m_out) with
            | [] | [_] => True
            | _ => M.MapsTo (o, fid) clsid (instance_methods caller)
            end ->
            field_offset gcenv o (make_members owner) = Errors.OK d ->
            0 <= Ptrofs.unsigned sofs + d <= Ptrofs.max_unsigned ->
            0 <= Ptrofs.unsigned sofs ->
            match callee.(m_out) with
            | [] | [_] => True
            | _ => gcenv ! (prefix_fun clsid fid) =  Some outco_callee
            end ->
            wt_stmt prog c.(c_objs) c.(c_mems) (meth_vars callee) callee.(m_body) ->
            eval_expr tge e1 le1 m1 (ptr_obj owner.(c_name) clsid o) (Vptr sb (Ptrofs.add sofs (Ptrofs.repr d))) ->
            exists m2 ws xs,
              eval_funcall tge (function_entry2 tge) m1 (Internal cf)
                           (Vptr sb (Ptrofs.add sofs (Ptrofs.repr d))
                                 :: match callee.(m_out) with
                                   | [] | [_] => vs
                                   | _ => Vptr outb_callee Ptrofs.zero :: vs
                                   end) E0 m2
                           match rvs with
                           | [Some v] => v
                           | _ => Vundef
                           end
              /\ make_out_vars (instance_methods caller) =
                ws ++ match callee.(m_out) with
                      | [] | [_] => xs
                      | _ => (prefix_out o fid, type_of_inst (prefix_fun clsid fid)) :: xs
                      end
              /\ m2 |= staterep gcenv prog owner.(c_name) (add_inst o me2 me) sb (Ptrofs.unsigned sofs)
                                                         ** match_out owner caller ve le1 outb_co
                                                         ** match callee.(m_out) with
                                                            | [] => sepemp
                                                            | [(x, _)] => sepemp
                                                            | _ => blockrep gcenv (Env.adds_opt (map fst callee.(m_out)) rvs vempty) outco_callee.(co_members) outb_callee
                                                            end
                                                         ** sepall (subrep_inst_env e1) (ws ++ xs)
                                                         ** varsrep caller ve le1
                                                         ** P).
    Proof.
      apply stmt_eval_call_ind; intros until 1;
        [| |intros Evs ? Hrec_eval ??? owner ? caller
         |intros HS1 ? HS2|intros Hbool ? Hifte|
         |rename H into Find; intros Findmeth ? StEval Hrec_exec Findvars Sub;
          intros ???????????????????????? Findowner ? Find' Findmeth' Hrep Hbounds
                 ? WTmem ? Hgetptrf Hgetcf ? Findout
                 Houtb_callee ? Hin Offs ?? Houtco_callee ??]; intros;
          try inversion WF as [?? Hvars|? ? Hin| |
                               |????? callee ?? Hin Find' Findmeth ? Incl|];
          try (rewrite match_states_conj in MS;
               destruct MS as (Hrep & Hbounds & WT_env & WT_mem & Hself & He & ?));
          subst.

      (* Assign x e : "x = e" *)
      - edestruct pres_sem_stmt with (5:=WF); eauto.
        assert (~ InMembers self (meth_vars f))
          by apply m_notreserved, in_eq.

        (* get the 'self' variable left value evaluation *)
        simpl translate_stmt; unfold assign.
        destruct_list f.(m_out) as (?, ?) ? ? : Out.

        + exists (PTree.set x v le1), m1; split.
          * eapply ClightBigstep.exec_Sset; eauto.
          *{ rewrite match_states_conj; split; [|repeat (split; auto)].
             - rewrite sep_swap4, sep_swap, match_out_nil in *; auto.
               eapply sep_imp; eauto.
               apply varsrep_add.
             - rewrite PTree.gso; auto.
               eapply In_InMembers, InMembers_neq in Hvars; eauto.
           }

        + exists (PTree.set x v le1), m1; split.
          * eapply ClightBigstep.exec_Sset; eauto.
          *{ rewrite match_states_conj; split; [|repeat (split; auto)].
             - rewrite sep_swap4, sep_swap, match_out_singleton in *; eauto.
               destruct Hrep; split.
               + eapply sep_imp; eauto.
                 apply varsrep_add.
               + destruct (ident_eqb x i) eqn: Eq.
                 * apply ident_eqb_eq in Eq.
                   subst x; rewrite PTree.gss, Env.gss; auto.
                 * apply ident_eqb_neq in Eq.
                   rewrite PTree.gso, Env.gso; auto.
             - rewrite PTree.gso; auto.
               eapply In_InMembers, InMembers_neq in Hvars; eauto.
           }

        + assert (1 < length f.(m_out))%nat by (rewrite Out; simpl; omega).
          destruct (mem_assoc_ident x (m_out f)) eqn: E; rewrite <-Out, E.

          *{ (* get the 'out' variable left value evaluation *)
              pose proof Hrep as Hrep'.
              rewrite sep_swap, match_out_notnil in Hrep; auto; destruct Hrep as (? & ? & ? & ? & ? & ?).
              edestruct evall_out_field with (e:=e1) as (? & ? & ?); eauto.

              (* get the updated memory *)
              rewrite sep_swap, sep_swap34, sep_swap23 in Hrep'.
              edestruct match_states_assign_out with (v:=v) as (m2 & ? & Hm2); eauto.
              (* rewrite sep_swap23, sep_swap, sep_swap34 in Hrep. *)
              rewrite sep_swap23, sep_swap, sep_swap34 in Hrep'.

              exists le1, m2; split; auto.
              - eapply ClightBigstep.exec_Sassign; eauto.
                + rewrite type_pres; eapply sem_cast_same; eauto.
                + eapply assign_loc_value.
                  * simpl; eauto.
                  * rewrite Ptrofs.add_zero_l; auto.
              - rewrite match_states_conj.
                rewrite sep_swap, sep_swap34, sep_swap23.
                repeat (split; auto).
            }

          *{ exists (PTree.set x v le1), m1; split.
             - eapply ClightBigstep.exec_Sset; eauto.
             - rewrite match_states_conj; split; [|repeat (split; auto)].
               + rewrite sep_swap, sep_swap34, sep_swap23 in *.
                 eapply match_states_assign_tempvar; eauto.
               + rewrite PTree.gso; auto.
                 eapply In_InMembers, InMembers_neq in Hvars; eauto.
           }

      (* AssignSt x e : "self->x = e"*)
      - edestruct pres_sem_stmt with (5:=WF); eauto.

        edestruct evall_self_field with (e:=e1) as (? & ? & Hoffset & ?); eauto.

        (* get the updated memory *)
        edestruct match_states_assign_state as (m2 & ? & ?); eauto.

        exists le1, m2; split.
        + eapply ClightBigstep.exec_Sassign; eauto.
          * rewrite type_pres; apply sem_cast_same; eauto.
          *{ eapply assign_loc_value.
             - simpl; eauto.
             - unfold Ptrofs.add.
               rewrite Ptrofs.unsigned_repr; auto.
           }
        + rewrite match_states_conj; repeat (split; auto).


      (* Call [y1; ...; yn] clsid o f [e1; ... ;em] : "clsid_f(&(self->o), &o, e1, ..., em); y1 = o.y1; ..." *)
      - (* get the Clight corresponding function *)
        edestruct pres_sem_stmt with (5:=WF) as (?& WT_env'); eauto.

        edestruct methods_corres
          as (ptr_f & cf & ? & ? & Hparams & Hreturn & Hcc & ?); eauto.

        pose proof (find_class_name _ _ _ _ Find') as Eq.
        pose proof (find_method_name _ _ _ Findmeth) as Eq'.
        subst.

        (* the *self parameter *)
        edestruct eval_self_inst with (1:=Find) (e:=e1) as (d & Eval_self & Offs & Bounds); eauto.

        (* recursive funcall evaluation *)
        assert (wt_mem match find_inst o me with
                       | Some om => om
                       | None => mempty
                       end p' cls).
        { inversion_clear WT_mem as [? ? ? ? Hinst].
          eapply Forall_forall in Hinst; eauto.
          inversion_clear Hinst as [? ? ? ? Hinst'|? ? ? ? ? ? ? Hinst' Find''];
            simpl in Hinst'; rewrite Hinst'.
          - apply wt_mempty.
          - simpl in Find''; rewrite Find'' in Find'; inv Find'; auto.
        }

        assert (length es = length (map translate_param (m_in callee))).
        { rewrite list_length_map.
          eapply Forall2_length; eauto.
        }
        assert (length (fn_params cf) = (match m_out callee with
                                         | [] | [_] => 1
                                         | _ :: _ => 2
                                         end + length vos)%nat) as Length_i.
        { symmetry; erewrite <-Forall2_length; eauto.
          rewrite Hparams; destruct_list callee.(m_out); simpl; repeat f_equal; auto.
        }

        assert (wt_stmt prog (c_objs cls) (c_mems cls) (meth_vars callee) (m_body callee)).
        { destruct wt_program_find_class with (2:=Find') as [WT']; auto.
          eapply wt_class_find_method in WT'; eauto.
          unfold wt_method in WT'.
          eapply wt_stmt_sub, find_class_sub; eauto.
        }

        assert (length ys = length callee.(m_out)) as Hys_out by
              (eapply Forall2_length; eauto).

        assert (forall v, le1 = set_opttemp None v le1) as E by reflexivity.

        assert (Genv.find_funct tge (Vptr ptr_f Ptrofs.zero) = Some (Internal cf)).
        { unfold Genv.find_funct.
          destruct (Ptrofs.eq_dec Ptrofs.zero Ptrofs.zero) as [|Neq]; auto.
          exfalso; apply Neq; auto.
        }
        edestruct find_class_rev as (? & Find''); eauto.

        edestruct pres_sem_stmt_call with (2:=Find') as (WT_omenv & WT_val); eauto.
        clear WT_omenv.
        assert (length rvos = length callee.(m_out)) as Hrvs_out by
              (eapply Forall2_length; eauto).

        assert (Forall2 (fun vo xt => wt_valo vo (snd xt)) vos (m_in callee)) as WT_val_i; eauto.
        assert (wt_env (Env.adds_opt (map fst (m_in callee)) vos vempty) (meth_vars callee)) as WT_env_i; eauto.
        inversion_clear NNaked as [| | |????? Spec| |].
        eapply no_vars_in_args_spec in Spec; eauto.
        assert (exists vs, vos = map Some vs) as (vs & ?) by (eapply not_None_is_Some_Forall; eauto).
        assert (exists rvs, rvos = map Some rvs) as (rvs & ?) by (eapply not_None_is_Some_Forall; eauto).
        subst; clear Spec.
        rewrite map_length in Length_i.
        assert (NoDup (map fst (m_in callee))) by apply fst_NoDupMembers, m_nodupin.
        rewrite Env.adds_opt_is_adds in WT_env_i; auto.
        pose proof WT_val_i; rewrite Forall2_map_1 in WT_val_i; simpl in WT_val_i.
        rewrite Forall2_map_2 in Evs.

        destruct_list (m_out callee) as (x', t') x'' outs : Out;
          destruct_list ys as y y' ys' : Hys; destruct_list rvs  as v v' rvs': Hrvs;
            simpl in Hys_out; simpl in Hrvs_out; try discriminate.
        + edestruct Hrec_eval with (owner:=owner) (e1:=e1) (m1:=m1) (le1:=le1) (outb_co:=outb_co)
            as (m2 & xs & ws & ? & Heq & Hm2); eauto.
          * rewrite Out; auto.
          * rewrite Out; auto.
          * rewrite Out; auto.
          * rewrite Out; auto.
          *{ clear Hrec_eval.
             exists le1, m2; split; auto.
             - simpl.
               unfold binded_funcall.
               rewrite Find'', Findmeth, Out; auto.
               erewrite E.
               eapply exec_Scall; eauto.
               + reflexivity.
               + simpl.
                 eapply eval_Elvalue.
                 *{ apply eval_Evar_global; eauto.
                    rewrite <-not_Some_is_None.
                    intros (b, t) Hget.
                    apply He in Hget; destruct Hget as (o' & f' & Eqpref).
                    unfold prefix_fun, prefix_out in Eqpref.
                    apply prefix_injective in Eqpref; destruct Eqpref.
                    - apply fun_not_out; auto.
                    - apply fun_id_valid.
                    - apply out_valid.
                  }
                 * apply deref_loc_reference; auto.
               + rewrite Out.
                 apply find_method_In in Findmeth.
                 econstructor; eauto.
                 eapply exprs_eval_simu with (1:=Find); eauto.
               + simpl.
                 unfold type_of_function;
                   rewrite Hparams, Hreturn, Hcc; simpl; repeat f_equal.
                 apply type_pres'; auto.
             - rewrite sep_swap3, Out, <-sepemp_left in Hm2.
               rewrite match_states_conj; split; [|repeat (split; auto)].
               subst; rewrite Env.updates_nil_l.
               rewrite sep_swap.
               rewrite Out in Heq; rewrite <-Heq in Hm2; auto.
           }

        + inv Incl.
          assert ((PTree.set (prefix (m_name callee) x') v le1) ! self = Some (Vptr sb sofs)).
          { rewrite PTree.gso; auto.
            intro Eq; apply self_not_prefixed; rewrite Eq; constructor.
          }
          edestruct eval_self_inst with (1:=Find) (e:=e1) (le:=PTree.set (prefix (m_name callee) x') v le1)
            as (d' & Eval_self' & Offs' & Bounds'); eauto.
          rewrite Offs in Offs'; inversion Offs'; subst d'.
          clear Offs' Bounds'.
          assert (~ InMembers (prefix (m_name callee) x') (m_in caller ++ m_vars caller)).
          {
            intro Hin'.
            apply (m_notprefixed (prefix (m_name callee) x') caller); auto.
            - constructor.
            - unfold meth_vars. repeat rewrite InMembers_app; rewrite InMembers_app in Hin'; tauto.
          }
          assert (self <> y).
          { intro Eq.
            apply (m_notreserved y caller).
            - unfold reserved; rewrite Eq; apply in_eq.
            - eapply In_InMembers; eauto.
          }
          edestruct Hrec_eval with (owner:=owner) (e1:=e1) (m1:=m1)
                                   (le1:=PTree.set (prefix (m_name callee) x') v le1)
                                   (outb_co:=outb_co)
            as (m2 & xs & ws & ? & Heq & Hm2); eauto; clear Hrec_eval.
          *{ rewrite sep_swap in *.
             destruct_list caller.(m_out) as (y', ?) ? ? : Outs.
             - rewrite match_out_nil in *; auto.
               eapply sep_imp; eauto.
               apply sep_imp'; auto.
               apply sep_imp'; eauto.
               apply varsrep_add'''; auto.
             - rewrite match_out_singleton in *; eauto;
                 destruct Hrep as (Hrep & ?); split.
               + eapply sep_imp; eauto.
                 repeat apply sep_imp'; auto.
                 apply varsrep_add'''; auto.
               + rewrite PTree.gso; auto.
                 intro.
                 apply (m_notprefixed y' caller).
                 * subst; constructor.
                 * unfold meth_vars; rewrite Outs; repeat rewrite InMembers_app; do 2 right; apply inmembers_eq.
             - assert (1 < length caller.(m_out))%nat by (rewrite Outs; simpl; omega).
               rewrite match_out_notnil in *; auto;
                 destruct Hrep as (? & ? & ? & Hrep & ? & ?);
                 do 2 econstructor; split; [|split; [|split]]; eauto.
               + eapply sep_imp; eauto.
                 repeat apply sep_imp'; auto.
                 apply varsrep_add'''; auto.
               + rewrite PTree.gso; auto.
                 intro Eq; apply out_not_prefixed; rewrite Eq; constructor.
           }
          * rewrite Out; auto.
          * rewrite Out; auto.
          * rewrite Out; auto.
          * rewrite Out; auto.
          *{ assert (exists m3 le3,
                        exec_stmt tge (function_entry2 tge) e1 (PTree.set (prefix (m_name callee) x') v le1) m2
                                  (assign y (cltype t') (c_name owner) caller (Etempvar (prefix (m_name callee) x') (cltype t')))
                                  E0 le3 m3 Out_normal
                        /\ m3 |= match_states owner caller (add_inst o ome' me, Env.adds [y] [v] ve) (e1, le3) sb sofs outb_co ** P) as Hexec.
             { rewrite Out, <-sepemp_left in Hm2.
               unfold assign; destruct_list caller.(m_out) as (?, ?) ? ? : Outs'.
               - do 2 econstructor; split.
                 + repeat econstructor.
                   simpl; rewrite PTree.gss; eauto.
                 + rewrite match_states_conj; split; [|repeat (split; auto)].
                   *{ rewrite sep_swap, match_out_nil in *; auto.
                      eapply sep_imp; eauto.
                      apply sep_imp'; auto.
                      - unfold subrep.
                        rewrite Heq, Out; auto.
                      - apply sep_imp'; auto.
                        unfold Env.adds; simpl.
                        apply varsrep_add; auto.
                    }
                   * rewrite PTree.gso; auto.
               - do 2 econstructor; split.
                 + repeat econstructor.
                   simpl; rewrite PTree.gss; eauto.
                 + rewrite match_states_conj; split; [|repeat (split; auto)].
                   *{ rewrite sep_swap, match_out_singleton in *; eauto.
                      destruct Hm2 as (Hm2 & ?); split.
                      - eapply sep_imp; eauto.
                        apply sep_imp'; auto.
                        + unfold subrep.
                          rewrite Heq, Out; auto.
                        + apply sep_imp'; auto.
                          unfold Env.adds; simpl.
                          apply varsrep_add; auto.
                      - unfold Env.adds; simpl.
                        destruct (ident_eqb i y) eqn: Eq.
                        + apply ident_eqb_eq in Eq.
                          subst i.
                          rewrite PTree.gss, Env.gss; auto.
                        + apply ident_eqb_neq in Eq.
                          rewrite PTree.gso, Env.gso; auto.
                    }
                   * rewrite PTree.gso; auto.
               - destruct (mem_assoc_ident y caller.(m_out)) eqn:E'; rewrite <-Outs', E'.
                 + inv WT_val.
                   rewrite sep_swap, sep_swap34, sep_swap23 in Hm2.
                   assert (1 < length caller.(m_out))%nat by (rewrite Outs'; simpl; omega).
                   pose proof Hm2 as Hm2'; rewrite match_out_notnil in Hm2'; auto;
                     destruct Hm2' as (? & ? & ? & ? & ? & ?).
                   edestruct evall_out_field with (le:=PTree.set (prefix (m_name callee) x') v le1)
                                                  (1:=Find) (2:=Hf) as (? & ? & ?); eauto.
                   edestruct match_states_assign_out with (1:=Find) (2:=Hf) (x:=y) as (m3 & ? & Hm3); eauto.
                   exists m3, (PTree.set (prefix (m_name callee) x') v le1); split.
                   *{ econstructor; eauto.
                      - econstructor; rewrite PTree.gss; eauto.
                      - apply sem_cast_same; auto.
                      - econstructor; eauto.
                        + simpl; eauto.
                        + rewrite Ptrofs.add_zero_l; auto.
                    }
                   * rewrite match_states_conj; split; [|repeat (split; auto)].
                     rewrite sep_swap.
                     rewrite match_out_notnil in *; auto;
                       destruct Hm3 as (? & ? & ? & Hm3 & ? & ?);
                       do 2 econstructor; split; [|split; [|split]]; eauto.
                     unfold Env.adds; simpl.
                     rewrite sep_swap34, sep_swap23.
                     eapply sep_imp; eauto.
                     repeat apply sep_imp'; auto.
                     unfold subrep.
                     rewrite Heq, Out; auto.
                 + do 2 econstructor; split.
                   * repeat econstructor.
                     rewrite PTree.gss; eauto.
                   *{ rewrite match_states_conj; split; [|repeat (split; auto)].
                      - rewrite sep_swap, sep_swap34, sep_swap23 in Hm2.
                        eapply match_states_assign_tempvar in Hm2; eauto.
                        unfold Env.adds; simpl.
                        rewrite sep_swap23, sep_swap, sep_swap34 in Hm2.
                        eapply sep_imp; eauto.
                        repeat apply sep_imp'; auto.
                        unfold subrep.
                        rewrite Heq, Out; auto.
                      - rewrite PTree.gso; auto.
                    }
             }

             destruct Hexec as (m3 & le3 & ? & ?).
             exists le3, m3; split; auto.
             simpl.
             unfold binded_funcall.
             rewrite Find'', Findmeth, Out; auto.
             change E0 with (Eapp E0 E0).
             eapply exec_Sseq_1 with (m1:=m2); eauto.
             change (PTree.set (prefix (m_name callee) x') v le1) with
                 (set_opttemp (Some (prefix (m_name callee) x')) v le1).
             eapply exec_Scall; eauto.
             - reflexivity.
             - simpl.
               eapply eval_Elvalue.
               + apply eval_Evar_global; eauto.
                 rewrite <-not_Some_is_None.
                 intros (b, t) Hget.
                 apply He in Hget; destruct Hget as (o' & f' & Eqpref).
                 unfold prefix_fun, prefix_out in Eqpref.
                 apply prefix_injective in Eqpref; destruct Eqpref.
                 * apply fun_not_out; auto.
                 * apply fun_id_valid.
                 * apply out_valid.
               + apply deref_loc_reference; auto.
             - rewrite Out.
               apply find_method_In in Findmeth.
               econstructor; eauto.
               eapply exprs_eval_simu with (1:=Find); eauto.
             - simpl.
               unfold type_of_function;
                 rewrite Hparams, Hreturn, Hcc; simpl; repeat f_equal.
               apply type_pres'; auto.
           }

        + (* the *out parameter *)
          rewrite sep_swap3 in Hrep.
          edestruct wt_program_find_class with (2:=Find) as [WT'']; eauto.
          eapply wt_class_find_method in WT''; eauto.
          pose proof (c_nodupobjs owner) as Nodup.
          eapply occurs_in_instance_methods in Occurs; eauto; try (simpl; omega).
          (* clear WT' Nodup. *)
          edestruct subrep_extract as (oblk & outco_callee & ? & ? & Hoblk & Houtco_callee & ?); eauto.
          rewrite sep_swap3 in Hrep.
          edestruct Hrec_eval with (owner:=owner) (e1:=e1) (m1:=m1) (le1:=le1) (outb_co:=outb_co)
            as (m2 & xs & ws & ? & Heq & Hm2); eauto.
          * rewrite Out; eauto.
          * rewrite Out; eauto.
          * rewrite Out; eauto.
          * rewrite Out; eauto.
          *{ (* output assignments *)
              clear Hrec_eval.
              rewrite Out, <-Out in Hm2.
              edestruct pres_sem_stmt_call with (2:=Find') as (?& WT_val_o); eauto.
              rewrite Forall2_map_1 in WT_val_o; simpl in WT_val_o.
              rewrite sep_swap3, sep_swap45, sep_swap34 in Hm2.
              assert (NoDup (map fst (m_out callee))) by apply fst_NoDupMembers, m_nodupout.
              rewrite Env.adds_opt_is_adds in Hm2; auto.
              rewrite <-Out in Incl.
              edestruct exec_funcall_assign with (1:=Find) (ys:=ys) (m1:=m2)
                as (le3 & m3 & Hexec & Hm3 & ?) ; eauto.
              - rewrite Hys; auto.
              - rewrite Hys; auto.
              - unfold outrep; rewrite Out, <-Out; eauto.
              - rewrite Hys in Hexec.
                exists le3, m3; split; auto.
                + simpl.
                  unfold binded_funcall.
                  rewrite Find'', Findmeth, Out; auto.
                  change E0 with (Eapp E0 E0).
                  eapply exec_Sseq_1 with (m1:=m2); eauto.
                  eapply exec_Scall; eauto.
                  * reflexivity.
                  *{ simpl.
                     eapply eval_Elvalue.
                     - apply eval_Evar_global; eauto.
                       rewrite <-not_Some_is_None.
                       intros (b, t) Hget.
                       apply He in Hget; destruct Hget as (o' & f' & Eqpref).
                       unfold prefix_fun, prefix_out in Eqpref.
                       apply prefix_injective in Eqpref; destruct Eqpref.
                       + apply fun_not_out; auto.
                       + apply fun_id_valid.
                       + apply out_valid.
                     - apply deref_loc_reference; auto.
                   }
                  * apply find_method_In in Findmeth.
                    rewrite Out.
                    do 2 (econstructor; eauto).
                    eapply exprs_eval_simu with (1:=Find); eauto.
                  * simpl.
                    unfold type_of_function;
                      rewrite Hparams, Hreturn, Hcc; simpl; repeat f_equal.
                    apply type_pres'; auto.
                  * simpl; rewrite <-Out; auto.
                + rewrite Env.updates_is_adds; auto.
                  rewrite Env.updates_is_adds in WT_env'; auto.
                  rewrite match_states_conj; split; [|repeat (split; auto)].
                  rewrite sep_swap34.
                  rewrite Out, Hys, sep_swap4 in Hm3.
                  eapply sep_imp; eauto.
                  apply sep_imp'; auto.
                  apply sep_imp'; auto.
                  rewrite <-sep_assoc.
                  apply sep_imp'; auto.
                  unfold subrep.
                  rewrite Out in Heq.
                  rewrite (sepall_breakout _ _ _ _ (subrep_inst_env e1) Heq).
                  apply sep_imp'; auto.
                  unfold subrep_inst_env.
                  rewrite Hoblk.
                  unfold type_of_inst.
                  rewrite Houtco_callee.
                  rewrite type_eq_refl.
                  apply blockrep_any_empty.
            }

      (* Comp s1 s2 : "s1; s2" *)
      - edestruct pres_sem_stmt with (5:=WF); eauto.

        apply occurs_in_comp in Occurs.
        inv NNaked.
        edestruct HS1; destruct_conjs; eauto.
        + rewrite match_states_conj. repeat (split; eauto).
        + edestruct HS2; destruct_conjs; eauto.
          do 2 econstructor; split; [|eassumption].
          change E0 with (Eapp E0 E0).
          eapply exec_Sseq_1; eauto.

      (* Ifte e s1 s2 : "if e then s1 else s2" *)
      - edestruct pres_sem_stmt with (5:=WF); eauto.

        apply occurs_in_ite in Occurs.
        inv NNaked.
        edestruct Hifte; destruct_conjs; eauto; (try now destruct b).
        + rewrite match_states_conj.
          repeat (split; eauto).
        + do 2 econstructor; split; eauto.
          eapply exec_Sifthenelse with (b:=b); eauto.
          *{ erewrite type_pres; eauto.
             match goal with H: typeof cond = bool_type |- _ => rewrite H end.
             unfold Cop.bool_val; simpl.
             destruct (val_to_bool v) eqn: E.
             - rewrite Hbool in E.
               destruct b.
               + apply val_to_bool_true' in E; subst; simpl.
                 rewrite Int.eq_false; auto.
                 apply Int.one_not_zero.
               + apply val_to_bool_false' in E; subst; simpl.
                 rewrite Int.eq_true; auto.
             - discriminate.
           }
          * destruct b; eauto.

      (* Skip : "skip" *)
      - exists le1, m1; split.
        + eapply exec_Sskip.
        + rewrite match_states_conj; repeat (split; auto).

      (* funcall *)
      - pose proof (find_class_sub_same _ _ _ _ _ Find WT Sub) as Find''.
        rewrite Find' in Find''; inversion Find''; subst prog'0 cls; clear Find''.
        rewrite Findmeth in Findmeth'; inversion Findmeth'; subst fm; clear Findmeth'.

        assert (Forall2 (fun vo xt => wt_valo vo (snd xt)) (map Some vs) (m_in callee))
          by (rewrite Forall2_map_1; auto).
        edestruct pres_sem_stmt_call as [? WT_val]; eauto using stmt_call_eval.

        assert (No_Naked_Vars (m_body callee)).
        { apply find_method_In in Findmeth.
          apply find_class_In in Find.
          inv Sub.
          apply Forall_app in NO_NAKED_VARS as (?& NO_NAKED_VARS).
          do 2 eapply Forall_forall in NO_NAKED_VARS; eauto.
        }
        assert (NoDup (map fst (m_in callee))) by apply fst_NoDupMembers, m_nodupin.

        assert (exists rvs, rvos = map Some rvs) as (rvs & ?).
        { apply not_None_is_Some_Forall; eapply SPEC_IO.
          2: eauto using stmt_call_eval.
          clear; induction vs; simpl; constructor; auto; discriminate.
        }
        subst.

        (* get the clight function *)
        edestruct methods_corres
          as (ptr_f' & cf' & Hgetptrf' & Hgetcf' & ? & Hret & ? & ? & ? & ? & ? & ? & Htr); eauto.
        rewrite Hgetptrf' in Hgetptrf; inversion Hgetptrf; subst ptr_f'; clear Hgetptrf.
        rewrite Hgetcf' in Hgetcf; inversion Hgetcf; subst cf'; clear Hgetcf.

        pose proof (find_class_name _ _ _ _ Find) as Eq.
        pose proof (find_method_name _ _ _ Findmeth) as Eq'.
        rewrite <-Eq, <-Eq' in *.

        edestruct find_class_app with (1:=Findowner)
          as (pre_prog & Hprog & FindNone); eauto.
        assert (c_name c <> c_name owner)
          by (rewrite Hprog in WT; eapply wt_program_not_same_name;
              eauto using (wt_program_app _ _ WT)).

        pose proof (find_class_sub _ _ _ _ Find') as Hsub.

        assert (field_type o (make_members owner) = Errors.OK (Tstruct (c_name c) noattr)).
        { apply in_field_type; auto.
          apply in_app; right.
          apply in_map_iff.
          exists (o, c_name c); split; auto.
        }
        assert (length rvs = length callee.(m_out))
          by (now apply Forall2_length in WT_val; rewrite <-WT_val, map_length).

        destruct_list (m_out callee) as (x, t) ? outs : Out;
          destruct_list rvs as v v' rvs' : Hrvs; contr.
        + edestruct (compat_funcall_pres cf sb sofs outb_callee None vs)
            as (e_fun & le_fun & m_fun & ws' & xs' & Bind & Alloc & He_fun & ? & Hobjs & Hm_fun & ? & ?);
            eauto; simpl; auto.
          * rewrite Out; auto.
          * rewrite Out; eauto.
          * rewrite Out; eauto.
          * rewrite Out; eauto.
          * rewrite Out, sep_swap, <-sepemp_left; eauto.
          *{ specialize (Hrec_exec Hsub c).
             edestruct Hrec_exec with (le1:=le_fun) (e1:=e_fun) (m1:=m_fun)
               as (? & m_fun' & ? & MS'); eauto.
             - eapply wt_mem_sub in WTmem; eauto.
               inversion_clear WTmem.
               edestruct make_members_co as (instco' & ? & ? & Hmembers & ?); eauto.
               edestruct field_offset_type; eauto.
               eapply struct_in_struct_in_bounds in Hbounds; eauto.
               rewrite Hmembers in Hbounds.
               rewrite match_states_conj; split; [|split; [|repeat split; eauto]].
               + simpl.
                 rewrite Env.adds_opt_is_adds; auto.
                 rewrite sep_swap, sep_swap34, sep_swap23, sep_swap45, sep_swap34,
                 <-sep_assoc, <-sep_assoc, sep_swap45, sep_swap34, sep_swap23,
                 sep_swap45, sep_swap34, sep_assoc, sep_assoc in Hm_fun; eauto.
               + edestruct field_offset_in_range; eauto.
                 destruct Hbounds; split; try omega.
                 unfold Ptrofs.add.
                 repeat (rewrite Ptrofs.unsigned_repr; auto); split; try omega.
             - rewrite match_states_conj in MS'; destruct MS' as (Hm_fun' & ?).
               rewrite sep_swap23, sep_swap5, sep_swap in Hm_fun'.
               rewrite <-sep_assoc, sep_unwand in Hm_fun'; auto.
               edestruct free_exists as (m_fun'' & Hfree & Hm_fun''); eauto.
               exists m_fun'', [], (make_out_vars (instance_methods caller)); split; [|split]; eauto.
               + eapply eval_funcall_internal; eauto.
                 * rewrite Out in Bind; constructor; eauto.
                 * rewrite Htr.
                   change E0 with (Eapp E0 E0).
                   eapply exec_Sseq_1; eauto;
                     apply exec_Sreturn_none.
                 * rewrite Hret; reflexivity.
               + simpl.
                 rewrite match_out_nil in Hm_fun''; auto.
                 rewrite sep_swap5.
                 rewrite <- 3 sep_assoc in Hm_fun''; rewrite sep_swap4 in Hm_fun'';
                   rewrite 3 sep_assoc in Hm_fun''.
                 unfold varsrep in *; rewrite sep_pure in *.
                 destruct Hm_fun'' as (Hpure & Hm_fun''); split; auto.
                 rewrite sep_swap3, sep_pure in Hm_fun''.
                 destruct Hm_fun'' as (Hpure' & Hm_fun'').
                 rewrite sep_swap, <-sepemp_left.
                 rewrite sep_swap.
                 eapply sep_imp; eauto.
                 apply sep_imp'; auto.
                 rewrite <- 2 sep_assoc.
                 apply sep_imp'; auto.
                 rewrite staterep_skip with (c:=owner); eauto. simpl.
                 rewrite ident_eqb_refl. rewrite sep_assoc, sep_swap2.
                 apply sep_imp'; auto.
                 rewrite sepall_breakout with (ys:=c_objs owner); eauto; simpl.
                 apply sep_imp'.
                 * rewrite Offs.
                   unfold instance_match, find_inst, add_inst; simpl.
                   rewrite Env.gss.
                   rewrite Hprog in WT; eapply wt_program_not_class_in in WT; eauto.
                   rewrite <-staterep_skip_cons with (prog:=prog'') (cls:=owner); eauto.
                   rewrite <-staterep_skip_app with (prog:=owner :: prog''); eauto.
                   rewrite <-Hprog.
                   unfold Ptrofs.add.
                   assert (0 <= d <= Ptrofs.max_unsigned)
                     by (split; [eapply field_offset_in_range'; eauto | omega]).
                   repeat (rewrite Ptrofs.unsigned_repr; auto).
                 *{ unfold staterep_objs.
                    apply sepall_swapp.
                    intros (i, k) Hini.
                    destruct (field_offset gcenv i (make_members owner)); auto.
                    unfold instance_match, find_inst, add_inst; simpl.
                    destruct (ident_eqb i o) eqn: E.
                    - exfalso.
                      apply ident_eqb_eq in E; subst i.
                      pose proof (c_nodupobjs owner) as Nodup.
                      rewrite Hobjs in Nodup.
                      rewrite NoDupMembers_app_cons in Nodup.
                      destruct Nodup as [Notin Nodup].
                      apply Notin.
                      eapply In_InMembers; eauto.
                    - apply ident_eqb_neq in E.
                      rewrite Env.gso; auto.
                  }
           }

        + edestruct (compat_funcall_pres cf sb sofs outb_callee None vs)
            as (e_fun & le_fun & m_fun & ws' & xs' & Bind & Alloc & He_fun & ? & Hobjs & Hm_fun & ? & ?);
            eauto; simpl; auto.
          * rewrite Out; auto.
          * rewrite Out; eauto.
          * rewrite Out; eauto.
          * rewrite Out; eauto.
          * rewrite Out, sep_swap, <-sepemp_left; eauto.
          *{ specialize (Hrec_exec Hsub c).
             edestruct Hrec_exec with (le1:=le_fun) (e1:=e_fun) (m1:=m_fun)
               as (? & m_fun' & ? & MS'); eauto.
             - eapply wt_mem_sub in WTmem; eauto.
               inversion_clear WTmem.
               edestruct make_members_co as (instco' & ? & ? & Hmembers & ?); eauto.
               edestruct field_offset_type; eauto.
               eapply struct_in_struct_in_bounds in Hbounds; eauto.
               rewrite Hmembers in Hbounds.
               rewrite match_states_conj; split; [|split; [|repeat split; eauto]].
               + simpl.
                 rewrite Env.adds_opt_is_adds; auto.
                 rewrite sep_swap, sep_swap34, sep_swap23, sep_swap45, sep_swap34,
                 <-sep_assoc, <-sep_assoc, sep_swap45, sep_swap34, sep_swap23,
                 sep_swap45, sep_swap34, sep_assoc, sep_assoc in Hm_fun; eauto.
               + edestruct field_offset_in_range; eauto.
                 destruct Hbounds; split; try omega.
                 unfold Ptrofs.add.
                 repeat (rewrite Ptrofs.unsigned_repr; auto); split; try omega.
             - rewrite match_states_conj in MS'; destruct MS' as (Hm_fun' & ?).
               rewrite sep_swap23, sep_swap5, sep_swap in Hm_fun'.
               rewrite <-sep_assoc, sep_unwand in Hm_fun'; auto.
               edestruct free_exists as (m_fun'' & Hfree & Hm_fun''); eauto.
               exists m_fun'', [], (make_out_vars (instance_methods caller)); split; [|split]; eauto.
               + eapply eval_funcall_internal; eauto.
                 * rewrite Out in Bind; constructor; eauto.
                 * rewrite Htr.
                   change E0 with (Eapp E0 E0).
                   eapply exec_Sseq_1; eauto;
                     apply exec_Sreturn_some.
                   rewrite sep_swap, match_out_singleton in Hm_fun'; eauto;
                     destruct Hm_fun' as (Hm_fun' & Hfind).
                   inversion_clear Findvars as [|? ? ? ? Hfind'].
                   rewrite Hfind' in Hfind.
                   econstructor; eauto.
                 *{ rewrite Hret. simpl.
                    split.
                    - destruct t; simpl; intro; contr.
                    -  inversion_clear WT_val; apply sem_cast_same; auto.
                  }
               + simpl.
                 rewrite match_out_singleton in Hm_fun''; eauto;
                   destruct Hm_fun'' as (Hm_fun'' & ?).
                 rewrite sep_swap5.
                 rewrite <- 3 sep_assoc in Hm_fun''; rewrite sep_swap4 in Hm_fun'';
                   rewrite 3 sep_assoc in Hm_fun''.
                 unfold varsrep in *; rewrite sep_pure in *.
                 destruct Hm_fun'' as (Hpure & Hm_fun''); split; auto.
                 rewrite sep_swap3, sep_pure in Hm_fun''.
                 destruct Hm_fun'' as (Hpure' & Hm_fun'').
                 rewrite sep_swap, <-sepemp_left.
                 rewrite sep_swap.
                 eapply sep_imp; eauto.
                 apply sep_imp'; auto.
                 rewrite <- 2 sep_assoc.
                 apply sep_imp'; auto.
                 rewrite staterep_skip with (c:=owner); eauto. simpl.
                 rewrite ident_eqb_refl. rewrite sep_assoc, sep_swap2.
                 apply sep_imp'; auto.
                 rewrite sepall_breakout with (ys:=c_objs owner); eauto; simpl.
                 apply sep_imp'.
                 * rewrite Offs.
                   unfold instance_match, find_inst, add_inst; simpl.
                   rewrite Env.gss.
                   rewrite Hprog in WT; eapply wt_program_not_class_in in WT; eauto.
                   rewrite <-staterep_skip_cons with (prog:=prog'') (cls:=owner); eauto.
                   rewrite <-staterep_skip_app with (prog:=owner :: prog''); eauto.
                   rewrite <-Hprog.
                   unfold Ptrofs.add.
                   assert (0 <= d <= Ptrofs.max_unsigned)
                     by (split; [eapply field_offset_in_range'; eauto | omega]).
                   repeat (rewrite Ptrofs.unsigned_repr; auto).
                 *{ unfold staterep_objs.
                    apply sepall_swapp.
                    intros (i, k) Hini.
                    destruct (field_offset gcenv i (make_members owner)); auto.
                    unfold instance_match, find_inst, add_inst; simpl.
                    destruct (ident_eqb i o) eqn: E.
                    - exfalso.
                      apply ident_eqb_eq in E; subst i.
                      pose proof (c_nodupobjs owner) as Nodup.
                      rewrite Hobjs in Nodup.
                      rewrite NoDupMembers_app_cons in Nodup.
                      destruct Nodup as [Notin Nodup].
                      apply Notin.
                      eapply In_InMembers; eauto.
                    - apply ident_eqb_neq in E.
                      rewrite Env.gso; auto.
                  }
           }

        + assert (1 < length callee.(m_out))%nat by (rewrite Out; simpl; omega).
          (* extract the out structure *)
          rewrite sep_swap23, sep_swap in Hrep.
          eapply subrep_extract in Hrep; eauto.
          destruct Hrep as (outb_callee' & outco_callee' & ws & xs & Houtb_callee' & Houtco_callee' & ? & Hrep).
          rewrite Houtco_callee' in Houtco_callee; inversion Houtco_callee;
            subst outco_callee'; clear Houtco_callee.
          rewrite Houtb_callee' in Houtb_callee; inversion Houtb_callee;
            subst outb_callee'; clear Houtb_callee.
          rewrite sep_swap23, sep_swap in Hrep.
          edestruct (compat_funcall_pres cf sb sofs outb_callee (Some (outb_callee, outco_callee)) vs)
            as (e_fun & le_fun & m_fun & ws' & xs' & Bind & Alloc & He_fun & ? & Hobjs & Hm_fun & ? & ?);
            eauto; auto.
          * rewrite Out; auto.
          * rewrite Out; eauto.
          * rewrite Out; eauto.
          * rewrite Out; split; eauto.
          * rewrite sep_swap, Out, sep_swap; eauto.
          *{ specialize (Hrec_exec Hsub c).
             edestruct Hrec_exec with (le1:=le_fun) (e1:=e_fun) (m1:=m_fun)
               as (? & m_fun' & ? & MS'); eauto.
             - eapply wt_mem_sub in WTmem; eauto.
               inversion_clear WTmem.
               edestruct make_members_co as (instco' & ? & ? & Hmembers & ?); eauto.
               edestruct field_offset_type; eauto.
               eapply struct_in_struct_in_bounds in Hbounds; eauto.
               rewrite Hmembers in Hbounds.
               rewrite match_states_conj; split; [|split; [|repeat split; eauto]].
               + simpl.
                 rewrite Env.adds_opt_is_adds; auto.
                 rewrite sep_swap, sep_swap34, sep_swap23, sep_swap45, sep_swap34,
                 <-sep_assoc, <-sep_assoc, sep_swap45, sep_swap34, sep_swap23,
                 sep_swap45, sep_swap34, sep_assoc, sep_assoc in Hm_fun; eauto.
               + edestruct field_offset_in_range; eauto.
                 destruct Hbounds; split; try omega.
                 unfold Ptrofs.add.
                 repeat (rewrite Ptrofs.unsigned_repr; auto); split; try omega.
             - rewrite match_states_conj in MS'; destruct MS' as (Hm_fun' & ?).
               rewrite sep_swap23, sep_swap5, sep_swap in Hm_fun'.
               rewrite <-sep_assoc, sep_unwand in Hm_fun'; auto.
               edestruct free_exists as (m_fun'' & Hfree & Hm_fun''); eauto.
               exists m_fun'', ws, xs; split; [|split]; eauto.
               + eapply eval_funcall_internal; eauto.
                 * rewrite Out in Bind; constructor; eauto.
                 * rewrite Htr.
                   change E0 with (Eapp E0 E0).
                   eapply exec_Sseq_1; eauto.
                   apply exec_Sreturn_none.
                 * rewrite Hret; reflexivity.
               + rewrite match_out_notnil in Hm_fun''; auto;
                   destruct Hm_fun'' as (? & ? & E & Hm_fun'' & ? & ?).
                 symmetry in E; inversion E; subst outb_callee outco_callee.
                 rewrite sep_swap5.
                 rewrite <- 3 sep_assoc in Hm_fun''; rewrite sep_swap5 in Hm_fun'';
                   rewrite 3 sep_assoc in Hm_fun''.
                 unfold varsrep in *; rewrite sep_pure in *.
                 destruct Hm_fun'' as (Hpure & Hm_fun''); split; auto.
                 rewrite sep_swap5, sep_pure in Hm_fun''.
                 destruct Hm_fun'' as (Hpure' & Hm_fun'').
                 rewrite sep_swap23, sep_swap.
                 eapply sep_imp; eauto.
                 apply sep_imp'; auto.
                 apply sep_imp'; auto.
                 * erewrite <-output_match; eauto.
                   rewrite <-translate_param_fst, Out.
                   apply blockrep_findvars.
                   rewrite translate_param_fst; auto.
                 *{ rewrite staterep_skip with (c:=owner); eauto. simpl.
                    rewrite ident_eqb_refl. rewrite sep_assoc, sep_swap3.
                    apply sep_imp'; auto.
                    rewrite sepall_breakout with (ys:=c_objs owner); eauto; simpl.
                    rewrite sep_assoc.
                    apply sep_imp'.
                    - rewrite Offs.
                      unfold instance_match, find_inst, add_inst; simpl.
                      rewrite Env.gss.
                      rewrite Hprog in WT; eapply wt_program_not_class_in in WT; eauto.
                      rewrite <-staterep_skip_cons with (prog:=prog'') (cls:=owner); eauto.
                      rewrite <-staterep_skip_app with (prog:=owner :: prog''); eauto.
                      rewrite <-Hprog.
                      unfold Ptrofs.add.
                      assert (0 <= d <= Ptrofs.max_unsigned)
                        by (split; [eapply field_offset_in_range'; eauto | omega]).
                      repeat (rewrite Ptrofs.unsigned_repr; auto).
                    - apply sep_imp'; auto.
                      unfold staterep_objs.
                      apply sepall_swapp.
                      intros (i', k) Hini.
                      destruct (field_offset gcenv i' (make_members owner)); auto.
                      unfold instance_match, find_inst, add_inst; simpl.
                      destruct (ident_eqb i' o) eqn: E'.
                      + exfalso.
                        apply ident_eqb_eq in E'; subst i'.
                        pose proof (c_nodupobjs owner) as Nodup.
                        rewrite Hobjs in Nodup.
                        rewrite NoDupMembers_app_cons in Nodup.
                        destruct Nodup as [Notin Nodup].
                        apply Notin.
                        eapply In_InMembers; eauto.
                      + apply ident_eqb_neq in E'.
                        rewrite Env.gso; auto.
                  }
           }
           Grab Existential Variables.
           eauto.
           eauto.
           eauto.
           eauto.
           exact empty_co.
           eauto.
           eauto.
           exact empty_co.
    Qed.

    Lemma stmt_correctness:
      forall p me1 ve1 s S2,
        stmt_eval p me1 ve1 s S2 ->
        sub_prog p prog ->
        forall c prog' f
          (Occurs: occurs_in s (m_body f))
          (NNaked: No_Naked_Vars s)
          (WF    : wt_stmt prog c.(c_objs) c.(c_mems) (meth_vars f) s)
          (Find  : find_class c.(c_name) prog = Some (c, prog'))
          (Hf    : find_method f.(m_name) c.(c_methods) = Some f),
        forall e1 le1 m1 sb sofs outb_co P
          (MS: m1 |= match_states c f (me1, ve1) (e1, le1) sb sofs outb_co ** P),
        exists le2 m2,
          exec_stmt tge (function_entry2 tge) e1 le1 m1
                    (translate_stmt (rev prog) c f s) E0 le2 m2 Out_normal
          /\ m2 |= match_states c f S2 (e1, le2) sb sofs outb_co ** P.
    Proof. eapply (proj1 correctness); eauto. Qed.

    Lemma make_program_defs:
      forall types gvars gvars_vol defs public main p,
        make_program' types gvars gvars_vol defs public main = Errors.OK p ->
        exists gce,
          build_composite_env types = Errors.OK gce
          /\ p.(AST.prog_defs) = map (vardef gce false) gvars ++ map (vardef gce true) gvars_vol ++ defs.
    Proof.
      unfold make_program'; intros.
      destruct (build_composite_env' types) as [[gce ?]|?]; try discriminate.
      destruct (check_size_env gce types) eqn: E; try discriminate.
      destruct u; inv H; simpl; eauto.
    Qed.

    Lemma compat_auto_funcall_pres:
      forall f sb ob vs c prog' me tself tout callee_id callee instco m ob_co P,
        let vargs := Vptr sb Ptrofs.zero
                          :: match callee.(m_out) with
                            | [] | [_] => vs
                            | _ => Vptr ob Ptrofs.zero :: vs
                            end
        in
        find_class c.(c_name) prog = Some (c, prog') ->
        find_method callee_id c.(c_methods) = Some callee ->
        length f.(fn_params) = length vargs ->
        fn_params f = (self, tself)
                        :: match callee.(m_out) with
                          | [] | [_] => map translate_param callee.(m_in)
                          | _ => (out, tout) :: map translate_param callee.(m_in)
                          end ->
        fn_vars f = make_out_vars (instance_methods callee) ->
        fn_temps f = match callee.(m_out) with
                     | [yt] => [translate_param yt]
                     | _ => []
                     end
                       ++ make_out_temps (instance_methods_temp (rev prog) callee)
                       ++ map translate_param callee.(m_vars) ->
        list_norepet (var_names f.(fn_params)) ->
        list_norepet (var_names f.(fn_vars)) ->
        match callee.(m_out) with
        | [] | [_] => True
        | _ =>
          ob_co = Some (ob, instco)
          /\ gcenv ! (prefix_fun c.(c_name) callee.(m_name)) = Some instco
        end ->
        m |= staterep gcenv prog c.(c_name) me sb Z0
                                            ** match callee.(m_out) with
                                               | [] | [_] => sepemp
                                               | _ => blockrep gcenv vempty instco.(co_members) ob
                                               end
                                            ** P ->
        exists e_fun le_fun m_fun,
          bind_parameter_temps f.(fn_params) vargs (create_undef_temps f.(fn_temps)) = Some le_fun
          /\ alloc_variables tge empty_env m f.(fn_vars) e_fun m_fun
          /\ (forall x b t, e_fun ! x = Some (b, t) -> exists o f, x = prefix_out o f)
          /\ le_fun ! self = Some (Vptr sb Ptrofs.zero)
          /\ m_fun |= staterep gcenv prog c.(c_name) me sb Z0
                      ** match_out c callee (Env.adds (map fst callee.(m_in)) vs vempty) le_fun ob_co
                      ** subrep callee e_fun
                      ** (subrep callee e_fun -* subrep_range e_fun)
                      ** varsrep callee (Env.adds (map fst callee.(m_in)) vs vempty) le_fun
                      ** P.
    Proof.
      intros * Findc Hcallee Hlengths
             Hparams Hvars Htemps Norep_par Norep_vars Hinstco Hrep.
      subst vargs; rewrite Hparams, Hvars, Htemps in *.
      assert (~ InMembers self (meth_vars callee)) as Notin_s
          by apply m_notreserved, in_eq.
      assert (~ InMembers out (meth_vars callee)) as Notin_o
          by apply m_notreserved, in_cons, in_eq.
      assert (~ InMembers self (map translate_param (m_in callee))).
      { unfold meth_vars in Notin_s; apply NotInMembers_app in Notin_s.
        rewrite fst_InMembers, translate_param_fst, <-fst_InMembers; tauto.
      }
      assert (~ InMembers self (map translate_param (m_out callee))).
      { unfold meth_vars in Notin_s; repeat rewrite NotInMembers_app in Notin_s.
        rewrite fst_InMembers, translate_param_fst, <-fst_InMembers; tauto.
      }
      assert (~ InMembers out (map translate_param (m_in callee))).
      { unfold meth_vars in Notin_o; apply NotInMembers_app in Notin_o.
        rewrite fst_InMembers, translate_param_fst, <-fst_InMembers; tauto.
      }
      assert (~ InMembers self (map translate_param (m_vars callee))).
      { unfold meth_vars in Notin_s; rewrite Permutation_app_comm, <-app_assoc in Notin_s;
          apply NotInMembers_app in Notin_s.
        rewrite fst_InMembers, translate_param_fst, <-fst_InMembers; tauto.
      }
      assert (~ InMembers out (map translate_param (m_vars callee))).
      { unfold meth_vars in Notin_o; rewrite Permutation_app_comm, <-app_assoc in Notin_o;
          apply NotInMembers_app in Notin_o.
        rewrite fst_InMembers, translate_param_fst, <-fst_InMembers; tauto.
      }
      assert (~ InMembers self (make_out_temps (instance_methods_temp (rev prog) callee))).
      { intro Hin_s.
        apply make_out_temps_prefixed in Hin_s.
        apply self_not_prefixed; auto.
      }
      assert (~ InMembers out (make_out_temps (instance_methods_temp (rev prog) callee))).
      { intro Hin_o.
        apply make_out_temps_prefixed in Hin_o.
        apply out_not_prefixed; auto.
      }

      assert (NoDupMembers (map translate_param (m_in callee))).
      { pose proof (m_nodupvars callee) as Nodup.
        rewrite Permutation_app_comm in Nodup.
        apply NoDupMembers_app_r in Nodup.
        rewrite fst_NoDupMembers, translate_param_fst, <-fst_NoDupMembers; auto.
      }
      assert (Forall (fun xt => sizeof tge (snd xt) <= Int.max_unsigned /\
                             (exists (id : AST.ident) (co : composite),
                                 snd xt = Tstruct id noattr /\
                                 gcenv ! id = Some co /\
                                 co_su co = Struct /\
                                 NoDupMembers (co_members co) /\
                                 (forall (x' : AST.ident) (t' : Ctypes.type),
                                     In (x', t') (co_members co) ->
                                     exists chunk : AST.memory_chunk,
                                       access_mode t' = By_value chunk /\
                                       (align_chunk chunk | alignof gcenv t'))))
                     (make_out_vars (instance_methods callee)))
        by (eapply instance_methods_caract; eauto).
      assert (NoDupMembers (make_out_vars (instance_methods callee)))
        by (unfold var_names in Norep_vars; now rewrite fst_NoDupMembers, NoDup_norepet).

      destruct_list (m_out callee) as (y, t) ? ? : E.
      - edestruct
          (bind_parameter_temps_exists_noout (map translate_param callee.(m_in)) self
                                             (make_out_temps (instance_methods_temp (rev prog) callee)
                                                             ++ map translate_param callee.(m_vars)) vs
                                             tself (Vptr sb Ptrofs.zero))
          as (le_fun & Bind & Hinputs); eauto.
        + rewrite NotInMembers_app; auto.
        + edestruct (alloc_result callee) as (e_fun & m_fun & ? & ? & Hm_fun); eauto.
          assert (le_fun ! self = Some (Vptr sb Ptrofs.zero)) by
              (eapply (bind_parameter_temps_implies'_noout (map translate_param (m_in callee))); eauto).
          exists e_fun, le_fun, m_fun;
            split; [|split; [|split; [|split]]]; auto.
          rewrite sep_swap4, <-sepemp_left in Hm_fun.
          rewrite sep_swap, match_out_nil; auto.
          rewrite <- 2 sep_assoc, sep_swap.
          rewrite translate_param_fst in Hinputs.
          apply sep_pure; split; auto.
          * rewrite map_app; simpl in Hinputs; repeat rewrite Forall_app in Hinputs.
            rewrite Forall_app; tauto.
          * rewrite sep_assoc, sep_swap, sep_assoc; auto.

      - edestruct
          (bind_parameter_temps_exists_noout (map translate_param callee.(m_in)) self
                                             (translate_param (y, t) ::
                                                              make_out_temps (instance_methods_temp (rev prog) callee)
                                                              ++ map translate_param callee.(m_vars)) vs
                                             tself (Vptr sb Ptrofs.zero))
          as (le_fun & Bind & Hinputs); eauto.
        + rewrite cons_is_app. repeat rewrite NotInMembers_app; tauto.
        + edestruct (alloc_result callee) as (e_fun & m_fun & ? & ? & Hm_fun); eauto.
          assert (le_fun ! self = Some (Vptr sb Ptrofs.zero)) by
              (eapply (bind_parameter_temps_implies'_noout (map translate_param (m_in callee))); eauto).
          simpl.
          exists e_fun, le_fun, m_fun;
            split; [|split; [|split; [|split]]]; auto.
          rewrite sep_swap4, <-sepemp_left in Hm_fun.
          rewrite sep_swap, match_out_singleton; eauto; split.
          *{ rewrite <- 2 sep_assoc, sep_swap.
             rewrite translate_param_fst in Hinputs.
             apply sep_pure; split; auto.
             - rewrite map_app; simpl in Hinputs; rewrite Forall_app, Forall_cons2, Forall_app in Hinputs.
               rewrite Forall_app; tauto.
             - rewrite sep_assoc, sep_swap, sep_assoc; auto.
           }
          *{ pose proof (m_nodupvars callee) as Nodup.
             rewrite Permutation_app_comm, <-app_assoc, E in Nodup.
             apply NoDupMembers_app_r in Nodup.
             rewrite <-cons_is_app in Nodup.
             inversion_clear Nodup as [|? ? ? Notin].
             rewrite fst_InMembers in Notin.
             rewrite Env.gsso, Env.gempty; auto.
             rewrite <-fst_InMembers in Notin.
             eapply bind_parameter_temps_conservation; eauto.
             - apply NotInMembers_cons; split.
               + rewrite InMembers_translate_param_idem; auto.
               + simpl in *; auto.
             - simpl; apply PTree.gss.
           }

      - destruct Hinstco.
        edestruct
          (bind_parameter_temps_exists (map translate_param callee.(m_in)) self out
                                       (make_out_temps (instance_methods_temp (rev prog) callee)
                                                       ++ map translate_param callee.(m_vars)) vs
                                       tself tout (Vptr sb Ptrofs.zero) (Vptr ob Ptrofs.zero))
          with (1:=self_not_out) as (le_fun & Bind & Hinputs); eauto.
        + rewrite NotInMembers_app; auto.
        + rewrite NotInMembers_app; auto.
        + simpl in Hlengths. inversion Hlengths; eauto.
        + edestruct (alloc_result callee) as (e_fun & m_fun & ? & ? & Hm_fun); eauto.
          edestruct (bind_parameter_temps_implies' (map translate_param (m_in callee)))
            with (1:=self_not_out) as (? & ?); eauto.
          exists e_fun, le_fun, m_fun;
            split; [|split; [|split; [|split]]]; auto.
          assert (1 < length callee.(m_out))%nat by (rewrite E; simpl; omega).
          rewrite sep_swap, match_out_notnil; auto;
            do 2 econstructor; split; [|split]; eauto.
          rewrite sep_swap, <- 3 sep_assoc, sep_swap.
          rewrite translate_param_fst in Hinputs.
          apply sep_pure; split; auto.
          * rewrite map_app; simpl in Hinputs; repeat rewrite Forall_app in Hinputs.
            rewrite Forall_app; tauto.
          * rewrite sep_assoc, sep_swap, sep_assoc, sep_swap23, sep_swap.
            eapply sep_imp; eauto.
            apply sep_imp'; auto.
            rewrite sep_assoc.
            apply sep_imp'; auto.
            apply sep_imp'; auto.
            rewrite <-translate_param_fst.
            erewrite <-output_match; eauto.
            apply blockrep_nodup.
            pose proof (m_nodupvars callee) as Nodup.
            rewrite app_assoc, Permutation_app_comm, app_assoc, Permutation_app_comm in Nodup.
            apply NoDupMembers_app_r in Nodup; rewrite Permutation_app_comm in Nodup.
            rewrite <-map_app, fst_NoDupMembers, translate_param_fst, <-fst_NoDupMembers; auto.
    Qed.

    Lemma corres_auto_funcall:
      forall me1 clsid fid vs me2 rvs c callee cf ptr_f prog' m1 sb outb outco P,
        let oty := type_of_inst (prefix_fun clsid fid) in
        stmt_call_eval prog me1 clsid fid (map Some vs) me2 (map Some rvs) ->
        find_class clsid prog = Some (c, prog') ->
        find_method fid c.(c_methods) = Some callee ->
        m1 |= staterep gcenv prog c.(c_name) me1 sb Z0
                                             ** match callee.(m_out) with
                                                | [] | [_] => sepemp
                                                | _ => blockrep gcenv vempty outco.(co_members) outb
                                                end
                                             ** P ->
        wt_mem me1 prog' c ->
        Forall2 (fun (v : val) (xt : ident * type) => wt_val v (snd xt)) vs (m_in callee) ->
        Globalenvs.Genv.find_symbol tge (prefix_fun clsid fid) = Some ptr_f ->
        Globalenvs.Genv.find_funct_ptr tge ptr_f = Some (Ctypes.Internal cf) ->
        length cf.(fn_params) = (match callee.(m_out) with
                                 | [] | [_] => 1
                                 | _ => 2
                                 end + length vs)%nat ->
        match callee.(m_out) with
        | [] | [_] => True
        | _ => gcenv ! (prefix_fun clsid fid) = Some outco
        end ->
        wt_stmt prog c.(c_objs) c.(c_mems) (meth_vars callee) callee.(m_body) ->
        exists m2,
          eval_funcall tge (function_entry2 tge) m1 (Internal cf)
                       (Vptr sb Ptrofs.zero
                             :: match callee.(m_out) with
                               | [] | [_] => vs
                               | _ => Vptr outb Ptrofs.zero :: vs
                               end) E0 m2
                       match rvs with
                       | [v] => v
                       | _ => Vundef
                       end
          /\ m2 |= staterep gcenv prog c.(c_name) me2 sb Z0
                                                 ** match callee.(m_out) with
                                                    | [] | [_] => sepemp
                                                    | _ => blockrep gcenv (Env.adds (map fst callee.(m_out)) rvs vempty) outco.(co_members) outb
                                                    end
                                                 ** P.
    Proof.
      intros ????????????????? Heval Findc Findm Hm1 Wtmem ? Hgetptrf Hgetcf ? ? ?.

      edestruct pres_sem_stmt_call with (6:=Heval) as (? & WT_val); eauto; try rewrite Forall2_map_1; auto.
      inversion_clear Heval as [??????????? Findc' Findm' ? Hev Hvars].
      rewrite Findc' in Findc; inv Findc;
        rewrite Findm' in Findm; inv Findm.
      assert (sub_prog prog' prog) by (eapply find_class_sub; eauto).
      eapply stmt_eval_sub_prog in Hev; eauto.
      eapply wt_mem_sub in Wtmem; eauto; inv Wtmem.

      (* get the clight function *)
      edestruct methods_corres
        as (ptr_f' & cf' & Hgetptrf' & Hgetcf' & Hparams & Hret & ? & ? & ? & ? & ? & ? & Htr); eauto.
      rewrite Hgetptrf' in Hgetptrf; inv Hgetptrf;
        rewrite Hgetcf' in Hgetcf; inv Hgetcf.

      pose proof (find_class_name _ _ _ _ Findc') as Eq;
        pose proof (find_method_name _ _ _ Findm') as Eq';
        rewrite <-Eq, <-Eq' in *.

      assert (length (fn_params cf) =
              length (Vptr sb Ptrofs.zero :: match m_out callee with
                                         | [] | [_] => vs
                                         | _ :: _ => Vptr outb Ptrofs.zero :: vs
                                         end))
        by (destruct_list callee.(m_out); simpl; auto).
      assert (length rvs = length callee.(m_out))
        by (now apply Forall2_length in Hvars; rewrite 2 map_length in Hvars).

      assert (NoDup (map fst (m_in callee))) by apply fst_NoDupMembers, m_nodupin.

      edestruct compat_auto_funcall_pres with (vs:=vs) (2:=Findm')
        as (e & le & m & ? & ? & ? & ? & Hm); eauto; simpl; auto.
      - destruct_list callee.(m_out); auto.
      - edestruct stmt_correctness with (p:=prog) (s:=callee.(m_body)) as (le' & m' & Hexec & MS); eauto.
        + apply find_class_In in Findc'; apply find_method_In in Findm'.
          do 2 eapply Forall_forall in NO_NAKED_VARS; eauto.
        + rewrite match_states_conj; split; [|split; [|repeat split; eauto]].
          * rewrite Env.adds_opt_is_adds; auto.
            rewrite Ptrofs.unsigned_zero, sep_swap45; eauto.
          * rewrite Ptrofs.unsigned_zero. split; try omega.
            simpl.
            edestruct make_members_co as (co & Hco & Hsu & Hmb & ? & ? & Hbound); eauto.
            transitivity co.(co_sizeof); auto.
            erewrite co_consistent_sizeof; eauto.
            rewrite Hsu, Hmb.
            apply align_le.
            erewrite co_consistent_alignof; eauto.
            apply alignof_composite_pos.
          * apply wt_env_params; rewrite Forall2_map_1; auto.
          * rewrite Ptrofs.unsigned_zero; omega.
        + rewrite match_states_conj in MS; destruct MS as (Hm_fun' & ?).
          rewrite sep_swap23, sep_swap5, sep_swap in Hm_fun'.
          rewrite <-sep_assoc, sep_unwand in Hm_fun'; auto.
          edestruct free_exists as (m_fun'' & Hfree & Hm_fun''); eauto.
          exists m_fun''; split.
          *{ destruct_list callee.(m_out) as (?, ?)  ? ? : Out; destruct_list rvs; contr.
             - eapply eval_funcall_internal; eauto.
               + constructor; eauto.
               + rewrite Htr.
                 change E0 with (Eapp E0 E0).
                 eapply exec_Sseq_1; eauto.
                 apply exec_Sreturn_none.
               + rewrite Hret; reflexivity.
             - eapply eval_funcall_internal; eauto.
               + constructor; eauto.
               + rewrite Htr.
                 change E0 with (Eapp E0 E0).
                 eapply exec_Sseq_1; eauto.
                 apply exec_Sreturn_some.
                 rewrite sep_swap, match_out_singleton in Hm_fun'; eauto;
                   destruct Hm_fun' as (Hm_fun' & Find').
                 inversion_clear Hvars as [|? ? ? ? Find]; rewrite Find in Find'.
                 econstructor; eauto.
               + rewrite Hret; simpl; split.
                 * destruct t; intro; contr.
                 * inversion_clear WT_val; apply sem_cast_same; auto.
             - eapply eval_funcall_internal; eauto.
               + constructor; eauto.
               + rewrite Htr.
                 change E0 with (Eapp E0 E0).
                 eapply exec_Sseq_1; eauto.
                 apply exec_Sreturn_none.
               + rewrite Hret; reflexivity.
           }
          *{ rewrite sep_swap.
             destruct_list (m_out callee) as (?, ?) ? ? : Out.
             - rewrite 2 sep_drop in Hm_fun''.
               rewrite <-sepemp_left; auto.
             - rewrite 2 sep_drop in Hm_fun''.
               rewrite <-sepemp_left; auto.
             - assert (1 < length callee.(m_out))%nat by (rewrite Out; simpl; omega).
               rewrite match_out_notnil in Hm_fun''; auto; destruct Hm_fun'' as (? & ? & E & Hm_fun'' & ? & ?).
               inversion E; subst outb outco.
               eapply sep_imp; eauto.
               + rewrite <-Out.
                 erewrite <-output_match; eauto.
                 rewrite <-translate_param_fst.
                 rewrite <-Env.adds_opt_is_adds.
                 * apply blockrep_findvars.
                   rewrite translate_param_fst, Out; auto.
                 * rewrite translate_param_fst.
                   apply fst_NoDupMembers, m_nodupout.
               + rewrite sep_drop; apply sep_imp'; auto.
           }
    Qed.

    Definition is_volatile (xt: ident * type) :=
      let (x, t) := xt in
      exists b, Genv.find_symbol (globalenv tprog) (glob_id x) = Some b
           /\ Genv.block_is_volatile (globalenv tprog) b = true.

    Lemma find_main:
      forall m P,
        m |= P ->
        exists c_main prog_main m_reset m_step,
          find_class main_node prog = Some (c_main, prog_main)
          /\ find_method reset c_main.(c_methods) = Some m_reset
          /\ find_method step c_main.(c_methods) = Some m_step
          /\ Forall is_volatile m_step.(m_in)
          /\ Forall is_volatile m_step.(m_out)
          /\ exists b,
              Genv.find_symbol tge tprog.(Ctypes.prog_main) = Some b
              /\ exists main,
                Genv.find_funct_ptr tge b = Some (Ctypes.Internal main)
                /\ main.(fn_return) = type_int32s
                /\ main.(fn_callconv) = AST.cc_default
                /\ main.(fn_params) = []
                /\ main.(fn_vars) = match m_out m_step with
                                   | [] | [_] => []
                                   | _ :: _ => [(prefix out step, type_of_inst (prefix_fun main_node step))]
                                   end
                /\ main.(fn_temps) = map translate_param
                                        (match m_out m_step with
                                         | [yt] => [yt]
                                         | _ => []
                                         end ++ m_in m_step)
                /\ main.(fn_body) = main_body false main_node m_step
                /\ match m_out m_step with
                  | [] | [_] => True
                  | _ =>
                    exists m' step_b,
                    alloc_variables tge empty_env m main.(fn_vars)
                                                           (PTree.set (prefix out step) (step_b, type_of_inst (prefix_fun main_node step))
                                                                      empty_env) m'
                    /\ exists step_co,
                        gcenv ! (prefix_fun main_node step) = Some step_co
                        /\ m' |= blockrep gcenv vempty step_co.(co_members) step_b
                                                                           ** P
                  end.
    Proof.
      intros * Hm.
      pose proof prog_defs_norepet. pose proof global_out_struct as GOS.
      pose proof make_members_co as MMC. pose proof Consistent.
      inv_trans TRANSL as En Estep Ereset with structs funs E.
      unfold make_program' in TRANSL.
      destruct (build_composite_env' (concat structs)) as [(ce, ?)|]; try discriminate.
      destruct (check_size_env ce (concat structs)); try discriminate.
      do 4 econstructor; repeat (split; eauto).
      - inversion TRANSL.
        apply Forall_forall.
        intros (x, t) Hin.
        set (ty := merge_attributes (cltype t) (mk_attr true None)).
        assert ((AST.prog_defmap tprog) ! (glob_id x) =
                Some (@AST.Gvar Clight.fundef _
                                (AST.mkglobvar ty [AST.Init_space (Ctypes.sizeof ce ty)] false true)))
          as Hget.
        subst ty.
        { unfold AST.prog_defmap; simpl.
          apply PTree_Properties.of_list_norepet; auto.
          inversion_clear TRANSL; auto; simpl.
          rewrite map_app.
          apply in_cons, in_app; left; apply in_app; right.
          apply in_map_iff.
          exists (glob_id x, cltype t); split; auto.
          apply in_map_iff.
          exists (x, t); split; auto.
        }
        apply Genv.find_def_symbol in Hget.
        destruct Hget as (b & Findsym & Finddef).
        unfold is_volatile.
        exists b; split; auto.
        unfold Genv.block_is_volatile, Genv.find_var_info.
        change (@Genv.find_def Clight.fundef Ctypes.type (genv_genv (globalenv tprog)) b)
          with (@Genv.find_def Clight.fundef Ctypes.type (@Genv.globalenv Clight.fundef Ctypes.type
                                                                          (@program_of_program function tprog)) b).
        rewrite Finddef; auto.

      - inversion TRANSL.
        apply Forall_forall.
        intros (x, t) Hin.
        set (ty := merge_attributes (cltype t) (mk_attr true None)).
        assert ((AST.prog_defmap tprog) ! (glob_id x) =
                Some (@AST.Gvar Clight.fundef _
                                (AST.mkglobvar ty [AST.Init_space (Ctypes.sizeof ce ty)] false true)))
          as Hget.
        subst ty.
        { unfold AST.prog_defmap; simpl.
          apply PTree_Properties.of_list_norepet; auto.
          inversion_clear TRANSL; auto; simpl.
          rewrite map_app.
          apply in_cons, in_app; left; apply in_app; left.
          apply in_map_iff.
          exists (glob_id x, cltype t); split; auto.
          apply in_map_iff.
          exists (x, t); split; auto.
        }
        apply Genv.find_def_symbol in Hget.
        destruct Hget as (b & Findsym & Finddef).
        unfold is_volatile.
        exists b; split; auto.
        unfold Genv.block_is_volatile, Genv.find_var_info.
        change (@Genv.find_def Clight.fundef Ctypes.type (genv_genv (globalenv tprog)) b)
          with (@Genv.find_def Clight.fundef Ctypes.type (@Genv.globalenv Clight.fundef Ctypes.type
                                                                          (@program_of_program function tprog)) b).
        rewrite Finddef; auto.

      - assert ((AST.prog_defmap tprog) ! main_id = Some (make_main false main_node m0)
                /\ tprog.(Ctypes.prog_main) = main_id)
          as [Hget Hmain_id].
        { unfold AST.prog_defmap; simpl; split;
            [apply PTree_Properties.of_list_norepet; auto|];
            inversion_clear TRANSL; auto.
          apply in_cons, in_app; right; apply in_app; right.
          destruct do_sync; [do 2 apply in_cons|]; apply in_eq.
        }
        rewrite Hmain_id.
        apply Genv.find_def_symbol in Hget.
        destruct Hget as (b & Findsym & Finddef).
        exists b; split; auto; econstructor; repeat split; eauto.
        + change (Genv.find_funct_ptr tge b) with (Genv.find_funct_ptr (Genv.globalenv tprog) b).
          unfold Genv.find_funct_ptr.
          unfold Clight.fundef in Finddef.
          now rewrite Finddef.
        + eauto.
        + eauto.
        + eauto.
        + eauto.
        + eauto.
        + eauto.
        + simpl.
          destruct_list m0.(m_out) : Out; auto.
          assert (1 < length m0.(m_out))%nat by (rewrite Out; simpl; omega).
          destruct (Mem.alloc m 0 (sizeof tge (type_of_inst (prefix_fun main_node step))))
            as (m', step_b) eqn: AllocStep.
          exists m', step_b; split.
          * repeat (econstructor; eauto).
          * edestruct GOS with (2:=Estep) as (step_co & Hsco & ? & Hms & ? & ? & ?); eauto.
            edestruct MMC as (co & Hco & ? & ? & ? & ? & ?); eauto.
            exists step_co.
            pose proof (find_class_name _ _ _ _ En) as Eq;
              pose proof (find_method_name _ _ _ Estep) as Eq';
              rewrite Eq, Eq' in *.
            split; auto.
            change (gcenv ! (prefix_fun main_node step))
              with ((prog_comp_env tprog) ! (prefix_fun main_node step)) in Hsco.
            assert (sizeof tge (type_of_inst (prefix_fun main_node step)) <= Int.modulus)
              by (simpl; rewrite Hsco; transitivity Int.max_unsigned;
                  auto; unfold Int.max_unsigned; omega).
            eapply alloc_rule in AllocStep; eauto; try omega.
            eapply sep_imp; eauto.
            simpl; rewrite Hsco; eapply blockrep_empty; eauto.
            rewrite Hms; eauto.
    Qed.

    Lemma find_self: exists sb, Genv.find_symbol tge (glob_id self) = Some sb.
    Proof.
      inv_trans TRANSL with structs funs Eq.
      unfold make_program' in TRANSL.
      destruct (build_composite_env' (concat structs)) as [(ce, ?)|]; try discriminate.
      destruct (check_size_env ce (concat structs)); try discriminate.
      unfold translate_class in Eq.
      apply split_map in Eq; destruct Eq as [? Funs].
      eapply Genv.find_symbol_exists.
      inversion_clear TRANSL as [Htprog]; simpl.
      now left.
    Qed.

    Lemma init_mem:
      exists m sb,
        Genv.init_mem tprog = Some m
        /\ Genv.find_symbol tge (glob_id self) = Some sb
        /\ m |= staterep gcenv prog main_node mempty sb Z0.
    Proof.
      clear SPEC_IO NO_NAKED_VARS. pose proof find_self as FS.
      pose proof prog_defs_norepet. pose proof make_members_co as MMC.
      pose proof Consistent as C.
      inv_trans TRANSL as En Estep Ereset with structs funs E.
      pose proof (build_ok _ _ _ _ _ _ _ TRANSL) as Hbuild.
      pose proof TRANSL as TRANSL'.
      apply make_program_defs in TRANSL'; destruct TRANSL' as (gce & Hbuild' & Eq).
      rewrite Hbuild in Hbuild'; inv Hbuild'.
      destruct Genv.init_mem_exists with (p:=tprog) as (m' & Initmem).
      - rewrite Eq; clear Eq.
        simpl.
        intros * [Hinv|Hinv].
        + inv Hinv; simpl; split.
          * split; auto; apply Z.divide_0_r.
          * intros * Hinio; simpl in Hinio;
              destruct Hinio; [discriminate|contradiction].
        + repeat rewrite in_app in Hinv;
            destruct Hinv as [Hinv|[Hinv|[Hinv|Hinv]]]; try now inv Hinv.
          *{ clear TRANSL.
             induction (map glob_bind (m_out m) ++ map glob_bind (m_in m)) as [|(x, t)].
             - contradict Hinv.
             - destruct Hinv as [Hinv|]; auto.
               inv Hinv; simpl; split.
               + split; auto; apply Z.divide_0_r.
               + intros * Hinio; simpl in Hinio;
                   destruct Hinio; [discriminate|contradiction].
           }
          *{ clear En Hbuild WT.
             remember prog as prog1.
             replace (translate_class (rev prog1)) with (translate_class (rev prog)) in E
               by now rewrite <-Heqprog1.
             clear Heqprog1 TRANSL MMC.
             revert structs funs E Hinv.
             induction prog1 as [|c' prog']; intros * E Hinv; simpl in E.
             - inv E; simpl in Hinv; contradiction.
             - rewrite map_app in E; simpl in E; rewrite split_last in E.
               destruct (split (map (translate_class (rev prog)) (rev prog'))) as (g, d) eqn: Egd; inv E.
               rewrite concat_app in Hinv; simpl in Hinv; rewrite app_nil_r in Hinv;
                 apply in_app in Hinv; destruct Hinv as [|Hinv]; eauto.
               unfold make_methods in Hinv.
               induction (c_methods c'); simpl in Hinv; try contradiction.
               destruct Hinv as [Hinv|]; auto.
               unfold translate_method in Hinv.
               destruct_list (m_out a) as (?, ?) ? ?; inv Hinv.
           }
          * destruct do_sync; try now inv Hinv.
            rewrite cons_is_app, in_app in Hinv.
            destruct Hinv as [[Hinv|Hinv]|[Hinv|Hinv]]; try inv Hinv.
      - exists m'.
        destruct FS as (sb & find_step).
        exists sb; split; [|split]; auto.
        assert (NoDupMembers tprog.(AST.prog_defs)) as Nodup
            by (rewrite fst_NoDupMembers, NoDup_norepet; auto).
        pose proof (init_grange _ _ Nodup Initmem) as Hgrange.
        unfold make_program' in TRANSL.
        destruct (build_composite_env' (concat structs)) as [(ce, ?)|]; try discriminate.
        destruct (check_size_env ce (concat structs)) eqn: Check_size; try discriminate.
        unfold translate_class in E.
        apply split_map in E; destruct E as [? Funs].
        inversion TRANSL as [Htprog].
        rewrite <-Htprog in Hgrange at 2.
        simpl in Hgrange.
        change (Genv.find_symbol tge (glob_id self) = Some sb)
          with (Genv.find_symbol (Genv.globalenv tprog) (glob_id self) = Some sb) in find_step.
        rewrite find_step in Hgrange.
        rewrite <-Zplus_0_r_reverse in Hgrange.
        rewrite Zmax_left in Hgrange;
          [|destruct (ce ! main_node); try omega; apply co_sizeof_pos].
        apply sep_proj1 in Hgrange.
        rewrite sepemp_right in *.
        eapply sep_imp; eauto.
        rewrite pure_sepwand.
        + unfold Genv.perm_globvar. simpl.
          transitivity (range_w sb 0 (sizeof gcenv (type_of_inst main_node))).
          * unfold sizeof. simpl.
            change (gcenv ! main_node) with (tprog.(prog_comp_env) ! main_node).
            rewrite <-Htprog; auto.
          * apply range_staterep; auto.
            intro En'; rewrite En' in En; discriminate.
        + edestruct MMC as (co & Find_main & ? & ? & ? & ? & ?); eauto.
          change (gcenv ! main_node) with (tprog.(prog_comp_env) ! main_node) in Find_main.
          rewrite <-Htprog in Find_main; simpl in Find_main.
          rewrite Find_main.
          transitivity Int.max_unsigned; auto; unfold Int.max_unsigned; omega.
    Qed.

    Section Init.
      Variables (c_main: class) (prog_main: program) (m_reset m_step: method).
      Hypothesis Find: find_class main_node prog = Some (c_main, prog_main).
      Hypothesis Findreset: find_method reset c_main.(c_methods) = Some m_reset.
      Hypothesis Findstep: find_method step c_main.(c_methods) = Some m_step.

      (* XXX: to be discharged from generation function *)
      Hypothesis Reset_in_spec: m_reset.(m_in) = [].
      Hypothesis Reset_out_spec: m_reset.(m_out) = [].
      Hypothesis Step_in_spec: m_step.(m_in) <> [].
      Hypothesis Step_out_spec: m_step.(m_out) <> [].

      Hypothesis Step_in: Forall is_volatile m_step.(m_in).
      Hypothesis Step_out: Forall is_volatile m_step.(m_out).

      Variables (rst_ptr stp_ptr: block) (reset_f step_f: function).
      Hypothesis Getreset_s: Genv.find_symbol tge (prefix_fun main_node reset) = Some rst_ptr.
      Hypothesis Getreset_f: Genv.find_funct_ptr tge rst_ptr = Some (Internal reset_f).
      Hypothesis Getstep_s: Genv.find_symbol tge (prefix_fun main_node step) = Some stp_ptr.
      Hypothesis Getstep_f: Genv.find_funct_ptr tge stp_ptr = Some (Internal step_f).

      Variables (main_b: block) (main_f: function) (sb step_b: block)
                (step_co: composite).
      Hypothesis Find_s_main: Genv.find_symbol tge tprog.(Ctypes.prog_main) = Some main_b.
      Hypothesis Findmain: Genv.find_funct_ptr tge main_b = Some (Ctypes.Internal main_f).
      Hypothesis Caractmain: main_f.(fn_return) = type_int32s
                             /\ main_f.(fn_callconv) = AST.cc_default
                             /\ main_f.(fn_params) = []
                             /\ main_f.(fn_vars) = match m_out m_step with
                                                  | [] | [_] => []
                                                  | _ :: _ => [(prefix out step, type_of_inst (prefix_fun main_node step))]
                                                  end
                             /\ main_f.(fn_temps) = map translate_param
                                                       (match m_out m_step with
                                                        | [yt] => [yt]
                                                        | _ => []
                                                        end ++ m_in m_step)
                             /\ main_f.(fn_body) = main_body false main_node m_step.

      Hypothesis Getstep_co: match m_step.(m_out) with
                             | [] | [_] => True
                             | _ => gcenv ! (prefix_fun main_node step) = Some step_co
                             end.

      Variables (m0 m1: Mem.mem).
      Hypothesis Initmem: Genv.init_mem tprog = Some m0.

      Let e1 := match m_step.(m_out) with
                | [] | [_] => empty_env
                | _ => PTree.set (prefix out step) (step_b, type_of_inst (prefix_fun main_node step))
                                empty_env
                end.
      Hypothesis Alloc: alloc_variables tge empty_env m0 main_f.(fn_vars) e1 m1.

      Hypothesis find_step: Genv.find_symbol (Genv.globalenv tprog) (glob_id self) = Some sb.

      Variable P: massert.

      Hypothesis Hm0: m1 |= staterep gcenv prog main_node mempty sb Z0
                         ** match m_step.(m_out) with
                            | [] | [_] => sepemp
                            | _ => blockrep gcenv vempty step_co.(co_members) step_b
                            end
                         ** P.

      Variable me0: menv.
      Hypothesis ResetNode: stmt_call_eval prog mempty c_main.(c_name) m_reset.(m_name) [] me0 [].

      Let le_main := create_undef_temps main_f.(fn_temps).

      Lemma entry_main:
        function_entry2 (globalenv tprog) main_f [] m0 e1 le_main m1.
      Proof.
        destruct Caractmain as (Hret & Hcc & Hparams & Hvars & Htemps & Hbody).
        econstructor; eauto.
        - rewrite Hvars.
          unfold var_names.
          rewrite <-NoDup_norepet, <-fst_NoDupMembers.
          destruct_list m_step.(m_out); repeat constructor; auto.
        - rewrite Hparams; constructor.
        - rewrite Hparams, Htemps; simpl.
          intros ? ? Hx; contradiction.
        - unfold le_main; rewrite Hparams, Htemps; simpl; auto.
      Qed.

      Lemma match_states_main_after_reset:
        exists m2,
          eval_funcall tge (function_entry2 tge) m1 (Internal reset_f)
                       [Vptr sb Ptrofs.zero] E0 m2 Vundef
          /\ m2 |= staterep gcenv prog c_main.(c_name) me0 sb 0
                                                      ** match m_step.(m_out) with
                                                         | [] | [_] => sepemp
                                                         | _ => blockrep gcenv vempty step_co.(co_members) step_b
                                                         end
                                                      ** P.
      Proof.
        pose proof methods_corres as MC.
        pose proof corres_auto_funcall as CAF.
        pose proof (find_class_name _ _ _ _ Find) as Eq;
          pose proof (find_method_name _ _ _ Findreset) as Eq';
          rewrite <-Eq, <-Eq' in *.
        edestruct MC with (2:=Findreset)
          as (ptr & f & Get_s & Get_f & Hp & ? & ? & ? & ? & ? & ? & ?); eauto.
        rewrite Getreset_s in Get_s; inversion Get_s; subst ptr;
          rewrite Getreset_f in Get_f; inversion Get_f; subst f.
        edestruct CAF with (3:=Findreset) (vs := @nil val) (rvs := @nil val)
          as (m'' & ? & Hm''); eauto.
        - rewrite Reset_out_spec, sep_swap, <-sepemp_left; eauto.
        - rewrite Reset_in_spec; auto.
        - rewrite Hp, Reset_in_spec, Reset_out_spec; auto.
        - rewrite Reset_out_spec; auto.
        - edestruct wt_program_find_class as [WT_main]; eauto.
          eapply wt_stmt_sub with (prog':=prog_main); eauto.
          + eapply wt_class_find_method with (2:=Findreset); auto.
          + eapply find_class_sub; eauto.
        - rewrite Reset_out_spec in *.
          exists m''; split; auto.
          rewrite sep_swap, <-sepemp_left in Hm''; auto.

          Grab Existential Variables.
          eauto.
          eauto.
      Qed.

      Lemma match_states_main_after_step:
        forall m' P me me' vs rvs,
          stmt_call_eval prog me c_main.(c_name) m_step.(m_name) (map Some vs) me' (map Some rvs) ->
          m' |= staterep gcenv prog c_main.(c_name) me sb 0
                                                    ** match m_step.(m_out) with
                                                       | [] | [_] => sepemp
                                                       | _ => blockrep gcenv vempty step_co.(co_members) step_b
                                                       end
                                                    ** P ->
          wt_mem me prog_main c_main ->
          wt_vals vs m_step.(m_in) ->
          exists m'',
            eval_funcall tge (function_entry2 tge) m' (Internal step_f)
                         (Vptr sb Ptrofs.zero
                               :: match m_step.(m_out) with
                                 | [] | [_] => vs
                                 | _ => Vptr step_b Ptrofs.zero :: vs
                                 end) E0 m''
                         match rvs with
                         | [v] => v
                         | _ => Vundef
                         end

            /\ m'' |= staterep gcenv prog c_main.(c_name) me' sb 0
                                                         ** match m_step.(m_out) with
                                                            | [] | [_] => sepemp
                                                            | _ => blockrep gcenv (Env.adds (map fst m_step.(m_out)) rvs vempty) step_co.(co_members) step_b
                                                            end
                                                         ** P.
      Proof.
        pose proof methods_corres as MC.
        pose proof corres_auto_funcall as CAF.
        intros.
        pose proof (find_class_name _ _ _ _ Find) as Eq;
          pose proof (find_method_name _ _ _ Findstep) as Eq';
          rewrite <-Eq, <-Eq' in *.
        edestruct MC with (2:=Findstep)
          as (ptr & f & Get_s & Get_f & Hp & ? & ? & ? & ? & ? & ? & ?); eauto.
        rewrite Getstep_s in Get_s; inversion Get_s; subst ptr;
          rewrite Getstep_f in Get_f; inversion Get_f; subst f.
        edestruct CAF with (3:=Findstep) as (m'' & ? & Hm''); eauto.
        - destruct_list m_step.(m_out); rewrite Hp; simpl; rewrite map_length;
            symmetry; erewrite Forall2_length; eauto.
        - edestruct wt_program_find_class as [WT_main]; eauto.
          eapply wt_stmt_sub with (prog':=prog_main); eauto.
          + eapply wt_class_find_method with (2:=Findstep); auto.
          + eapply find_class_sub; eauto.
      Qed.


      (*****************************************************************)
      (** Trace semantics of reads and writes to volatiles             *)
      (*****************************************************************)

      Lemma exec_read:
        forall cs le m,
          wt_vals cs m_step.(m_in) ->
          exists le', (* XXX: not any le': the one that contains [cs] *)
            exec_stmt (globalenv tprog) (function_entry2 (globalenv tprog)) e1 le m
                      (load_in m_step.(m_in))
                      (load_events cs m_step.(m_in))
                      le' m Out_normal
            /\ Forall2 (fun v xt => le' ! (fst xt) = Some v) cs m_step.(m_in)
            /\ (forall x, ~ InMembers x m_step.(m_in) -> le' ! x = le ! x).
      Proof.
        clear Caractmain Step_in_spec.
        pose proof (m_nodupin m_step) as Hnodup.
        pose proof (m_good_in m_step) as Good.

        induction m_step.(m_in) as [|(x, t)]; simpl;
          intros * Hwt;
          inversion_clear Hwt as [| v ? vs ? Hwt_v Hwts ];
          inversion_clear Hnodup.
        - (* Case: m_step.(m_in) ~ [] *)
          rewrite load_events_nil.
          repeat econstructor; auto.
        - (* Case: m_step.(m_in) ~ xt :: xts *)
          inversion_clear Step_in as [|? ? Findx].
          destruct Findx as (bx & Findx & Volx).
          rewrite load_events_cons.

          assert (exists le',
                     exec_stmt (globalenv tprog) (function_entry2 (globalenv tprog)) e1 le m
                               (Sbuiltin (Some x) (AST.EF_vload (type_chunk t))
                                         (Ctypes.Tcons (Tpointer (cltype t) noattr) Ctypes.Tnil)
                                         [Eaddrof (Evar (glob_id x) (cltype t)) (Tpointer (cltype t) noattr)])
                               [load_event_of_val v (x, t)] le' m Out_normal
                     /\ le' ! x = Some v
                     /\ forall y, y <> x -> le' ! y = le ! y)
            as (le' & Hload & Hgss_le' & Hgso_le').
          {
            exists (set_opttemp (Some x) v le).
            repeat split;
              [
              | now apply  PTree.gss
              | now intros; eapply PTree.gso ].
            econstructor.
            - econstructor; eauto using eval_exprlist.
              + apply eval_Eaddrof, eval_Evar_global; eauto.
                rewrite <-not_Some_is_None.
                intros (b, t') Hget.
                subst e1.
                assert (glob_id x <> self) by (eapply self_not_glob; eauto).
                destruct_list m_step.(m_out).
                * rewrite PTree.gempty in Hget; auto; try discriminate.
                * rewrite PTree.gempty in Hget; auto; try discriminate.
                *{ rewrite PTree.gso, PTree.gempty in Hget; auto; try discriminate.
                   intro E; apply (glob_id_not_prefixed x).
                   - apply (Good (x, t)), in_eq.
                   - rewrite E; constructor.
                 }
              + unfold Cop.sem_cast; simpl; eauto.
            - constructor.
              unfold load_event_of_val; simpl.
              rewrite wt_val_load_result with (ty:=t); auto.
              apply volatile_load_vol; auto.
              apply eventval_of_val_match; auto.
          }

          assert (forall x0 : ident * type, In x0 l -> ValidId x0)
            by (intros; apply Good, in_cons; auto).
          edestruct IHl with (le := le') as (le'' & ? & Hgss & Hgso); eauto.

          exists le''.
          repeat split.
          + eapply exec_Sseq_1; eauto.
          + econstructor; eauto.
            rewrite Hgso; auto.
          + intros * Hnot_in.
            apply Decidable.not_or in Hnot_in as [? ?].
            rewrite Hgso; auto.
      Qed.

      Lemma exec_write:
        forall vs ve le m,
          wt_vals vs m_step.(m_out) ->
          m |= match m_step.(m_out), vs with
               | [], [] => sepemp
               | [(y, _)], [v] => pure (le ! y = Some v)
               | _, _ => blockrep gcenv (Env.adds (map fst m_step.(m_out)) vs ve) (co_members step_co) step_b
               end
            ** P ->
          exec_stmt (globalenv tprog) (function_entry2 (globalenv tprog)) e1 le m
                    (write_out main_node m_step.(m_out))
                    (store_events vs m_step.(m_out))
                    le m Out_normal.
      Proof.
        pose proof global_out_struct as GOS.
        intros * WT_vals Hrep.
        assert (length vs = length m_step.(m_out)) as Length by (eapply Forall2_length; eauto).
        (* XXX: factorize proof (& code) with [exec_read] *)
        destruct_list m_step.(m_out) as (y, t) (y', t') outs : Out;
          destruct_list vs as v v' vs' : Vs; contr.

        - unfold write_out.
          inversion_clear Step_out as [|? ? Findy].
          destruct Findy as (b_y & Findy & Voly).
          inversion_clear WT_vals.
          eapply exec_Sbuiltin with (vres:=Vundef).
          + repeat
              match goal with
              | |- eval_exprlist _ _ _ _ _ _ _ => econstructor
              end.
            * econstructor.
              apply eval_Evar_global; eauto.
              rewrite <-not_Some_is_None.
              intros (b, t'') Hget.
              subst e1.
              rewrite PTree.gempty in Hget; contr.
            * reflexivity.
            * econstructor.
              apply sep_pure in Hrep; destruct Hrep as (Hpure & Hrep).
              change val with Values.val in Hpure.
              rewrite Hpure; eauto.
            * eapply sem_cast_same; eauto.
          + constructor.
            apply volatile_store_vol; auto; simpl.
            rewrite <-wt_val_load_result; auto.
            apply eventval_of_val_match; auto.

        - assert (1 < length m_step.(m_out))%nat by (rewrite Out; simpl; omega).
          clear Caractmain Step_out_spec Hm0.

          pose proof (m_nodupout m_step) as Hnodup.

          pose proof (find_class_name _ _ _ _ Find) as Eq;
            pose proof (find_method_name _ _ _ Findstep) as Eq';
            rewrite <-Eq, <-Eq' in *.

          assert (e1 ! (prefix out step)
                  = Some (step_b, type_of_inst (prefix_fun main_node step))) as Findstr
              by (subst e1; rewrite PTree.gss; auto).
          rewrite <-Eq, <-Eq' in Findstr.

          edestruct GOS with (2:=Findstep)
            as (step_co' & Hrco & ? & Hmr & ? & ? & ?); eauto.
          rewrite Getstep_co in Hrco; inversion Hrco; subst step_co'.

          (* This induction is tricky: [co_members step_co ~ m_out m_step]
           is fixed across the induction while we are going down inside
           [m_out m_step]. The following assertion allows us to get back
           into [co_members] whenever necessary. *)

          assert (Hfield_offs: forall x ty,
                     In (x, ty) (map translate_param (m_out m_step)) ->
                     In (x, ty) (co_members step_co))
            by now rewrite Hmr.

          unfold write_out.

          rewrite <-Vs, <-Out in *.
          clear Vs.
          pose proof (m_good_out m_step) as Good.
          revert ve vs Hrep Hnodup Hfield_offs Findstr Step_out Eq Eq' Length WT_vals Good.
          generalize m_step.(m_out) as xts.
          clear - Getstep_co.

          induction xts as [|(x, t) xts]; destruct vs; contr;
            intros; eauto using exec_stmt.

          inversion_clear Hnodup as [|? ? ? Notin].
          inversion_clear Step_out as [|? ? Findx].
          destruct Findx as (bx & Findx & Volx).
          inversion_clear WT_vals.

          rewrite store_events_cons.
          eapply exec_Sseq_1 with (le1 := le); eauto.
          + eapply exec_Sbuiltin with (vres:=Vundef).
            *{ repeat
                 match goal with
                 | |- eval_exprlist _ _ _ _ _ _ _ => econstructor
                 end.
               - econstructor.
                 apply eval_Evar_global; eauto.
                 rewrite <-not_Some_is_None.
                 intros (b, t'') Hget.
                 subst e1.
                 rewrite PTree.gso, PTree.gempty in Hget.
                 + discriminate.
                 + intro E; apply (glob_id_not_prefixed x).
                   * apply (Good (x, t)), in_eq.
                   * rewrite E; constructor.
               - reflexivity.
               - assert (In (x, cltype t) (co_members step_co))
                   by now eapply Hfield_offs; econstructor; eauto.

                 edestruct blockrep_field_offset as (? & ? & ? & ?); eauto.

                 eapply eval_Elvalue; eauto.
                 + eapply eval_Efield_struct; eauto.
                   *{ eapply eval_Elvalue; eauto.
                      - constructor;
                          rewrite <- Eq'; eauto.
                      - now apply deref_loc_copy.
                    }
                   * unfold type_of_inst; simpl; rewrite Eq'; eauto.
                 + simpl; eapply blockrep_deref_mem; eauto.
                   * simpl; apply Env.find_gsss.
                     now rewrite <-fst_InMembers.
                   * rewrite Ptrofs.unsigned_zero; simpl.
                     rewrite Ptrofs.unsigned_repr; auto.
               - eapply sem_cast_same; eauto.
             }
            * constructor.
              apply volatile_store_vol; auto.
              rewrite <-wt_val_load_result; auto.
              apply eventval_of_val_match; auto.

          + eapply IHxts with (ve:=Env.add x v ve); eauto.
            * intros.
              eapply Hfield_offs. constructor 2; auto.
            * intros; apply Good, in_cons; auto.
      Qed.

      (*****************************************************************)
      (** Clight version of Corr.dostep'                               *)
      (*****************************************************************)

      Section dostep.

        Variables ins outs: Str.stream (list val).
        Variables xs ys: list (ident * type).

        Hypothesis Hwt_ins: forall n, wt_vals (ins n) m_step.(m_in).
        Hypothesis Hwt_outs: forall n, wt_vals (outs n) m_step.(m_out).

        (** This coinductive predicate describes the logical behavior of
          the [while] loop. *)

        CoInductive dostep : nat -> mem -> Prop
          := Step :
               forall n me me',
                 eval_funcall tge (function_entry2 tge) me (Internal step_f)
                              (Vptr sb Ptrofs.zero
                                    :: match m_step.(m_out) with
                                       | []  | [_] => ins n
                                       | _ => Vptr step_b Ptrofs.zero :: (ins n)
                                       end) E0 me'
                              match outs n with
                              | [v] => v
                              | _ => Vundef
                              end
                 ->
                 me' |= match m_step.(m_out) with
                        | [] | [_] => sepemp
                        | _ => blockrep gcenv (Env.adds (map fst (m_out m_step))
                                                        (outs n) vempty)
                                        (co_members step_co) step_b
                        end
                     ** P ->
                 dostep (S n) me' ->
                 dostep n me.

        Section Dostep_coind.

          Variable t: genv.
          Variable R: nat -> mem -> Prop.

          Hypothesis StepCase: forall n me,
              R n me ->
              exists me',
                eval_funcall tge (function_entry2 tge) me (Internal step_f)
                             (Vptr sb Ptrofs.zero
                                   :: match m_step.(m_out) with
                                      | [] | [_] => ins n
                                      | _ => Vptr step_b Ptrofs.zero :: (ins n)
                                      end) E0 me'
                             match outs n with
                             | [v] => v
                             | _ => Vundef
                             end
                /\ me' |= match m_step.(m_out) with
                          | [] | [_] => sepemp
                          | _ => blockrep gcenv (Env.adds (map fst (m_out m_step)) (outs n) vempty)
                                          (co_members step_co) step_b
                          end
                       ** P
                /\ R (S n) me'.

          Lemma dostep_coind:
            forall n me,
              R n me  -> dostep n me.
          Proof.
            cofix COINDHYP.
            intros ? ? HR.
            pose proof (StepCase _ _ HR) as Hstep.
            simpl in *; decompose record Hstep; subst.
            econstructor; eauto.
          Qed.

        End Dostep_coind.

        Definition mInit := m1.

        Hypothesis WT_mem: wt_mem me0 prog_main c_main.
        Hypothesis LoopCall: loop_call prog (c_name c_main) step
                                       (fun n => map Some (ins n)) (fun n => map Some (outs n)) 0 me0.

        Lemma dostep_imp:
          wt_program prog ->
          exists m0,
            eval_funcall tge (function_entry2 tge) mInit (Internal reset_f)
                         [Vptr sb Ptrofs.zero] E0 m0 Vundef
            /\ dostep 0 m0.
        Proof.
          intros Hwt_prog (* Hwt_mem Hdostep *).

          (* Initialisation *)
          edestruct match_states_main_after_reset as (mem0 & ? & Hmem0).
          eexists; split; eauto.
          (* rewrite <- sep_assoc, sep_swap, sep_assoc, sep_swap in Hmem0. *)

          (* Coinduction *)
          set (R := fun n (m: mem) =>
                      exists me,
                        loop_call prog (c_name c_main) step
                                  (fun n => map Some (ins n)) (fun n => map Some (outs n)) n me
                        /\ wt_mem me prog_main c_main
                        /\ m
                             |= staterep gcenv prog (c_name c_main) me sb 0
                             ** match m_step.(m_out) with
                                | [] | [_] => sepemp
                                | _ => blockrep gcenv vempty (co_members step_co) step_b
                                end
                             ** P).
          apply dostep_coind with (R := R);
            unfold R.
          - (* clear - Hwt_ins Hwt_prog WT_mem m_step Find Findstep. *)
            pose proof match_states_main_after_step as MSMAS.

            intros n meN (? & Hdostep & Hwt & Hblock).
            destruct Hdostep as [n menvN menvSn (* cins couts *) Hstmt Hdostep].
            specialize Hwt_ins with n.

            assert (c_name c_main = main_node) as <-
                by now eapply find_class_name; eauto.

            assert (m_step.(m_name) = step) as Hstep
                by now eapply find_method_name; eauto.

            assert (exists meSn,
                       eval_funcall tge (function_entry2 tge) meN
                                    (Internal step_f)
                                    (Vptr sb Ptrofs.zero
                                          :: match m_step.(m_out) with
                                             | [] | [_] => ins n
                                             | _ => Vptr step_b Ptrofs.zero :: (ins n)
                                             end)
                                    E0 meSn
                                    match outs n with
                                    | [v] => v
                                    | _ => Vundef
                                    end
                       /\ meSn
                            |= staterep gcenv prog (c_name c_main) menvSn sb 0
                            ** match m_step.(m_out) with
                               | [] | [_] => sepemp
                               | _ => blockrep gcenv (Env.adds (map fst (m_out m_step)) (outs n) vempty)
                                               (co_members step_co) step_b
                               end
                            ** P)
              as (meSn & ? & Hblock_step).
            {
              eapply MSMAS; eauto. rewrite Hstep; auto.
            }

            exists meSn.

            assert (meSn |= match m_step.(m_out) with
                            | [] | [_] => sepemp
                            | _ => blockrep gcenv (Env.adds (map fst (m_out m_step)) (outs n) vempty)
                                            (co_members step_co) step_b
                            end
                         ** P)
              by (apply sep_drop in Hblock_step; auto).

            assert (wt_mem menvSn prog_main c_main)
              by (edestruct pres_sem_stmt_call as (? & ?); eauto; rewrite Forall2_map_1; auto).

            assert (meSn
                      |= staterep gcenv prog (c_name c_main) menvSn sb 0
                      ** match m_step.(m_out) with
                         | [] | [_] => sepemp
                         | _ => blockrep gcenv vempty (co_members step_co) step_b
                         end
                      ** P).
            {
              eapply sep_imp.
              - eapply Hblock_step.
              - auto.
              - destruct_list m_step.(m_out); eauto.
                rewrite blockrep_any_empty; auto.
            }

            repeat (split; eauto).

          - now exists me0; repeat (split; auto).
        Qed.

        (*    End dostep'. *)

        (*****************************************************************)
        (** Correctness of the main loop                                 *)
        (*****************************************************************)

        Lemma exec_body:
          forall n meN le,
            dostep n meN ->
            exists leSn meSn,
              exec_stmt (globalenv tprog) (function_entry2 (globalenv tprog)) e1 le meN
                        (main_loop_body false main_node m_step)
                        (load_events (ins n) (m_in m_step)
                                     ++ E0
                                     ++ store_events (outs n) (m_out m_step))
                        leSn meSn Out_normal
              /\ dostep (S n) meSn.
        Proof.
          intros * Hdostep.

          destruct Hdostep as [n meN meSn Hvals_in Hvals_out Hfuncall].

          (* load in *)
          edestruct exec_read
            with (le := le)(m := meN)
            as (le1 & Hload & Hgss_le1 & Hgso_le1); eauto.

          assert (eval_exprlist (globalenv tprog) e1 le1 meN
                                (Eaddrof (Evar (glob_id self) (type_of_inst main_node)) (type_of_inst_p main_node)
                                         :: match m_step.(m_out) with
                                            | [] | [_] => map make_in_arg (m_in m_step)
                                            | _ => Eaddrof (Evar (prefix out step)
                                                                 (type_of_inst (prefix_fun main_node step)))
                                                           (pointer_of (type_of_inst (prefix_fun main_node step)))
                                                           :: map make_in_arg (m_in m_step)
                                            end)
                                (Ctypes.Tcons
                                   (type_of_inst_p main_node)
                                   match m_step.(m_out) with
                                   | [] | [_] => list_type_to_typelist (map Clight.typeof (map make_in_arg (m_in m_step)))
                                   | _ => Ctypes.Tcons
                                            (pointer_of (type_of_inst (prefix_fun main_node step)))
                                            (list_type_to_typelist
                                               (map Clight.typeof (map make_in_arg (m_in m_step))))
                                   end)
                                (Vptr sb Ptrofs.zero
                                      :: match m_step.(m_out) with
                                         | [] | [_] => ins n
                                         | _ => Vptr step_b Ptrofs.zero :: (ins n)
                                         end)).
          {
            assert (forall vs,
                       wt_vals vs m_step.(m_in) ->
                       Forall2 (fun v xt => le1 ! (fst xt) = Some v) vs m_step.(m_in) ->
                       eval_exprlist (globalenv tprog) e1 le1 meN
                                     (map make_in_arg m_step.(m_in))
                                     (list_type_to_typelist
                                        (map Clight.typeof (map make_in_arg (m_in m_step))))
                                     vs).
            {
              clear.
              induction m_step.(m_in) as [|(x, t)];
                intros ? Hvals_in;
                inversion_clear Hvals_in as [| cin ? cins];
                intro Hdef;
                inversion_clear Hdef;
                simpl in *;
                eauto using eval_exprlist.
              apply eval_Econs with (v1 := cin)(v2 := cin).
              econstructor; eauto.
              now apply sem_cast_same.
              apply IHl; eauto.
            }
            destruct_list m_step.(m_out).
            - econstructor; eauto.
              + econstructor.
                apply eval_Evar_global; eauto.
                rewrite PTree.gempty; auto.
              + constructor.
            - econstructor; eauto.
              + econstructor.
                apply eval_Evar_global; eauto.
                rewrite PTree.gempty; auto.
              + constructor.
            - econstructor.
              + econstructor.
                apply eval_Evar_global; eauto.
                rewrite <-not_Some_is_None.
                intros (b, t'') Hget.
                subst e1.
                rewrite PTree.gso, PTree.gempty in Hget.
                * discriminate.
                *{ intro E; apply (glob_id_not_prefixed self).
                   - apply self_valid.
                   - rewrite E; constructor.
                 }
              + constructor.
              + repeat (econstructor; eauto).
                subst e1. rewrite PTree.gss; auto.
          }

          assert (length (outs n) = length m_step.(m_out))
            by (specialize (Hwt_outs n); eapply Forall2_length; eauto).

          (* call step *)
          assert (exists le2,
                     exec_stmt (globalenv tprog) (function_entry2 (globalenv tprog)) e1 le1 meN
                               (step_call main_node (map make_in_arg (m_in m_step)) (m_out m_step)) E0
                               le2 meSn Out_normal
                     /\ match m_step.(m_out), outs n with
                        | [(x, _)], [v] => le2 ! x = Some v
                        | _, _ => True
                        end)
            as (le2 & Hcall & ?).
          { edestruct methods_corres with (2:=Findstep)
              as (ptr & f & Get_s & Get_f & Hp_stp & Hr_stp & Hcc_stp
                  & ? & ? & ? & ? & ? & Htr_stp); eauto.
            rewrite Getstep_s in Get_s; inversion Get_s; subst ptr;
              rewrite Getstep_f in Get_f; inversion Get_f; subst f.
            unfold step_call.
            destruct_list m_step.(m_out) as (?, ?) ? ? : Out.
            - eexists; split; auto;
                eapply exec_Scall; simpl; eauto; simpl.
              + eapply eval_Elvalue.
                * apply eval_Evar_global; eauto.
                  rewrite PTree.gempty; auto.
                * apply deref_loc_reference; auto.
              + unfold Genv.find_funct. auto.
              + assert (c_name c_main = main_node) as <-
                    by now eapply find_class_name; eauto.
                assert (m_step.(m_name) = step) as Hstep
                    by now eapply find_method_name; eauto.
                simpl; unfold type_of_function;
                  rewrite Hp_stp, Hr_stp, Hcc_stp; simpl; repeat f_equal.
                clear.
                induction (m_in m_step) as [|(x, t)]; simpl; auto.
                rewrite IHl; auto.
            - eexists; split.
              + eapply exec_Scall; simpl; eauto; simpl.
                *{ eapply eval_Elvalue.
                   - apply eval_Evar_global; eauto.
                     rewrite PTree.gempty; auto.
                   - apply deref_loc_reference; auto.
                 }
                * unfold Genv.find_funct. auto.
                * assert (c_name c_main = main_node) as <-
                      by now eapply find_class_name; eauto.
                  assert (m_step.(m_name) = step) as Hstep
                      by now eapply find_method_name; eauto.
                  simpl; unfold type_of_function;
                    rewrite Hp_stp, Hr_stp, Hcc_stp; simpl; repeat f_equal.
                  clear.
                  induction (m_in m_step) as [|(x, t)]; simpl; auto.
                  rewrite IHl; auto.
              + destruct_list (outs n); contr.
                simpl; rewrite PTree.gss; auto.
            - eexists; split; auto;
                eapply exec_Scall; simpl; eauto; simpl.
              + eapply eval_Elvalue.
                *{ apply eval_Evar_global; eauto.
                   rewrite <-not_Some_is_None.
                   intros (b, t') Hget.
                   subst e1.
                   rewrite PTree.gso, PTree.gempty in Hget.
                   - discriminate.
                   - intro E; apply prefix_injective in E.
                     + destruct E as [E].
                       contradict E; apply fun_not_out.
                     + apply fun_id_valid.
                     + apply out_valid.
                 }
                * apply deref_loc_reference; auto.
              + unfold Genv.find_funct. auto.
              + assert (c_name c_main = main_node) as <-
                    by now eapply find_class_name; eauto.
                assert (m_step.(m_name) = step) as <-
                    by now eapply find_method_name; eauto.
                simpl; unfold type_of_function;
                  rewrite Hp_stp, Hr_stp, Hcc_stp; simpl; repeat f_equal.
                clear.
                induction (m_in m_step) as [|(x, t)]; simpl; auto.
                rewrite IHl; auto.
          }
          eexists le2, meSn; split; auto.
          repeat eapply exec_Sseq_1; eauto.
          eapply exec_write; eauto.
          destruct_list m_step.(m_out) as (?, ?) ? ?; destruct_list (outs n);
            contr; eauto.
          apply sep_pure; split; auto.
          rewrite sepemp_left; auto.
        Qed.

        Definition transl_trace (n: nat): traceinf' :=
          trace_step m_step ins outs Step_in_spec Step_out_spec Hwt_ins Hwt_outs n.

        Lemma dostep_loop:
          forall n meInit le me,
            wt_mem meInit prog_main c_main ->
            dostep n me ->
            execinf_stmt (globalenv tprog) (function_entry2 (globalenv tprog)) e1 le me
                         (main_loop false main_node m_step)
                         (traceinf_of_traceinf' (transl_trace n)).
        Proof.
          cofix COINDHYP.
          intros ????? Hdostep.
          destruct exec_body with (1:=Hdostep) (le:=le) as (? & ? & ? & ?).
          unfold transl_trace, trace_step; rewrite unfold_mk_trace.
          eapply execinf_Sloop_loop with (out1 := Out_normal);
            eauto using out_normal_or_continue, exec_stmt.
        Qed.

        Lemma exec_reset:
          exists m2,
            exec_stmt (globalenv tprog) (function_entry2 (globalenv tprog)) e1
                      le_main m1 (reset_call (c_name c_main)) E0
                      le_main m2 Out_normal
            /\ dostep 0 m2.
        Proof.
          pose proof methods_corres as MC.
          destruct dostep_imp as (m2 & Heval & Step); auto.
          change (eval_funcall tge (function_entry2 tge) m0 (Internal reset_f)
                               [Vptr sb Ptrofs.zero] E0 m2 Vundef)
            with (eval_funcall (globalenv tprog) (function_entry2 (globalenv tprog)) m0 (Internal reset_f)
                               [Vptr sb Ptrofs.zero] E0 m2 Vundef) in Heval.
          pose proof (find_class_name _ _ _ _ Find) as Eq;
            pose proof (find_method_name _ _ _ Findreset) as Eq';
            rewrite <-Eq, <-Eq' in *.
          edestruct MC with (2:=Findreset)
            as (ptr & f & Get_s & Get_f & Hp_rst & Hr_rst & Hcc_rst
                & ? & ? & ? & ? & ? & Htr_rst); eauto.
          rewrite Getreset_s in Get_s; inversion Get_s; subst ptr;
            rewrite Getreset_f in Get_f; inversion Get_f; subst f.
          exists m2; split; auto.
          unfold reset_call.
          rewrite <-Eq'.
          change le_main with (set_opttemp None Vundef le_main) at 2.
          econstructor; simpl; eauto.
          - eapply eval_Elvalue.
            + apply eval_Evar_global; eauto.
              rewrite <-not_Some_is_None.
              intros (b, t) Hget.
              subst e1.
              destruct_list m_step.(m_out).
              * rewrite PTree.gempty in Hget; discriminate.
              * rewrite PTree.gempty in Hget; discriminate.
              *{ rewrite PTree.gso, PTree.gempty in Hget.
                 - discriminate.
                 - intro E; apply prefix_injective in E.
                   + destruct E as [E].
                     contradict E; apply fun_not_out.
                   + apply fun_id_valid.
                   + apply out_valid.
               }
            + apply deref_loc_reference; auto.
          - apply find_method_In in Findreset.
            do 2 (econstructor; eauto).
            apply eval_Evar_global; auto.
            rewrite <-not_Some_is_None.
            intros (b, t) Hget.
            subst e1.
            destruct_list m_step.(m_out).
            + rewrite PTree.gempty in Hget; discriminate.
            + rewrite PTree.gempty in Hget; discriminate.
            + rewrite PTree.gso, PTree.gempty in Hget.
              * discriminate.
              *{ intro E; apply (glob_id_not_prefixed self).
                 - apply self_valid.
                 - rewrite E; constructor.
               }
          - unfold Genv.find_funct. auto.
          - simpl; unfold type_of_function;
              rewrite Hp_rst, Hr_rst, Hcc_rst; simpl; repeat f_equal.
            + rewrite Reset_in_spec; auto.
              rewrite Reset_out_spec; auto.
            + rewrite Reset_out_spec; auto.
        Qed.

        Lemma main_inf:
          evalinf_funcall (globalenv tprog) (function_entry2 (globalenv tprog)) m0
                          (Internal main_f) [] (traceinf_of_traceinf' (transl_trace 0)).
        Proof.
          pose proof exec_reset as ER. pose proof entry_main as EM.
          pose proof dostep_loop as DSL.
          pose proof (find_class_name _ _ _ _ Find) as Eq;
            pose proof (find_method_name _ _ _ Findreset) as Eq';
            rewrite <-Eq, <-Eq' in *.
          destruct Caractmain as (? & ? & ? & ? & ? & Hbody).
          destruct ER as (? & ? & ?); auto.
          econstructor; eauto.
          rewrite <-E0_left_inf, Hbody.
          eapply execinf_Sseq_1, execinf_Sseq_2; eauto.
        Qed.

        Let after_loop := Kseq (Sreturn (Some cl_zero)) Kstop.

        Lemma reactive_loop:
          forall n m le,
            dostep n m ->
            Smallstep.forever_reactive (step_fe function_entry2) (globalenv tprog)
                                       (Clight.State main_f (main_loop false main_node m_step) after_loop e1 le m)
                                       (traceinf_of_traceinf' (transl_trace n)).
        Proof.
          unfold transl_trace, trace_step.
          cofix COINDHYP.
          intros * Hdostep'.
          edestruct exec_body with (1:=Hdostep') as (? & ? & Exec_body & ?).
          eapply exec_stmt_steps in Exec_body.
          destruct Exec_body as (? & Star_body & Out_body).
          unfold main_loop_body in Star_body.
          rewrite unfold_mk_trace.

          econstructor; simpl.

          (* eapply Smallstep.star_forever_reactive. *)
          - eapply Smallstep.star_step.
            + eapply step_loop.
            + eapply Smallstep.star_right with (t2:=E0); auto.
              *{ eapply Smallstep.star_right with (t2:=E0); auto.
                 - eapply Star_body.
                 - inversion_clear Out_body.
                   apply step_skip_or_continue_loop1; auto.
               }
              * apply step_skip_loop2.
            + simpl; rewrite 2 E0_right; auto.
          - intro Evts.
            apply app_eq_nil in Evts; destruct Evts.
            apply (load_events_not_E0 ins (m_in m_step) Step_in_spec Hwt_ins n); auto.
          - apply COINDHYP; auto.
        Qed.

        Lemma reacts:
          program_behaves (semantics2 tprog) (Reacts (traceinf_of_traceinf' (transl_trace 0))).
        Proof.
          pose proof entry_main as EM.
          destruct Caractmain as (Hret & Hcc & Hparams & ? & ? & Hbody).

          destruct exec_reset as (? & Exec_reset & ?).
          eapply exec_stmt_steps in Exec_reset.
          destruct Exec_reset as (? & Star_reset & Out_reset).

          pose proof reactive_loop as RL.
          pose proof (find_class_name _ _ _ _ Find) as Eq;
            pose proof (find_method_name _ _ _ Findreset) as Eq';
            rewrite <-Eq, <-Eq' in *.
          econstructor.
          - econstructor; eauto.
            simpl; unfold type_of_function; auto.
            rewrite Hparams, Hret, Hcc; auto.
          -
            econstructor.
            rewrite <-E0_left_inf.
            eapply Smallstep.star_forever_reactive.
            + eapply Smallstep.star_step with (t1:=E0) (t2:=E0); auto.
              * eapply step_internal_function. eapply EM.
              *{ eapply Smallstep.star_step with (t1:=E0) (t2:=E0); auto.
                 - rewrite Hbody.
                   apply step_seq.
                 - eapply Smallstep.star_step with (t1:=E0) (t2:=E0); auto.
                   + apply step_seq.
                   + eapply Smallstep.star_right with (t1:=E0) (t2:=E0); auto.
                     * eapply Star_reset.
                     * inversion_clear Out_reset.
                       apply step_skip_seq.
               }
            + apply RL with (le:=le_main) in H1.
              unfold after_loop, step_fe in H1. auto.
        Qed.

      End dostep.

    End Init.

    Theorem reacts':
      forall me0 ins outs c_main prog_main m_step m_reset,
        stmt_call_eval prog mempty (c_name c_main) (m_name m_reset) [] me0 [] ->
        wt_mem me0 prog_main c_main ->
        loop_call prog (c_name c_main) step (fun n => map Some (ins n)) (fun n => map Some (outs n)) 0 me0 ->
        find_class main_node prog = Some (c_main, prog_main) ->
        find_method reset (c_methods c_main) = Some m_reset ->
        find_method step (c_methods c_main) = Some m_step ->
        m_in m_reset = [] ->
        m_out m_reset = [] ->
        forall (Step_in_spec: m_in m_step <> []) (Step_out_spec: m_out m_step <> [])
          (Hwt_in: forall n : nat, wt_vals (ins n) (m_in m_step))
          (Hwt_out: forall n : nat, wt_vals (outs n) (m_out m_step)),
          program_behaves (semantics2 tprog)
                          (Reacts
                             (traceinf_of_traceinf'
                                (transl_trace m_step Step_in_spec Step_out_spec ins outs Hwt_in Hwt_out 0))).
    Proof.
      intros until m_reset; intros ? ? ? Findmain Findreset Findstep.
      destruct init_mem as (m0 & sb & Initmem & find_step & Hrep).
      edestruct (find_main m0 _ Hrep) as
          (c_main' & prog_main' & m_reset' & m_step' & Findmain' & Findreset' & Findstep' & ? & ? &
           ? & ? & ? & ? & ? & ? & ? & Hvars & ?  & Hbody & Hmout).
      rewrite Findmain' in Findmain; inv Findmain; subst.
      rewrite Findreset' in Findreset; rewrite Findstep' in Findstep; inv Findreset; inv Findstep; subst.
      edestruct methods_corres with (2:=Findreset')
        as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?); eauto.
      edestruct methods_corres with (2:=Findstep')
        as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?); eauto.
      intros.
      case_eq (m_out m_step).
      - intros Out; rewrite Out in *.
        eapply reacts with (m_reset:=m_reset) (m_step:=m_step);
          try rewrite Out; eauto.
        + repeat split; auto.
        + rewrite Hvars; econstructor.
        + erewrite <-sepemp_left, <-sepemp_right; eauto.
      - intros (x', t') xs Out.
        destruct xs; rewrite Out in *.
        + eapply reacts with (m_reset:=m_reset) (m_step:=m_step);
            try rewrite Out; eauto.
          * repeat split; auto.
          * rewrite Hvars; econstructor.
          * erewrite <-sepemp_left, <-sepemp_right; eauto.
        + destruct Hmout as (? & ? & ? & ? & ? & ?).
          eapply reacts; eauto; try rewrite Out; eauto.
          * repeat split; try rewrite Out; auto.
          * erewrite sep_swap, <-sepemp_right; eauto.

            Grab Existential Variables.
            exact empty_co.
            eauto.
            exact empty_co.
            eauto.
    Qed.

    End CORRECTNESS.

End PRESERVATION.
