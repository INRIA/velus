From Coq Require Import ZArith.

From compcert Require Import common.Errors.
From compcert Require Import common.Globalenvs.
From compcert Require Import lib.Coqlib.
From compcert Require Import lib.Maps.
From compcert Require Import lib.Integers.
From compcert Require Import cfrontend.Ctypes.
From compcert Require Import cfrontend.Clight.

From Velus Require Import Common.
From Velus Require Import Common.CompCertLib.
From Velus Require Import Ident.
From Velus Require Import Environment.
From Velus Require Import ObcToClight.Generation.
From Velus Require Import ObcToClight.Interface.

Import Obc.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Open Scope Z.

(** Properties  *)

Module MProps := FMapFacts.Properties(M).
Import MProps.

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
  induction prog as [|c]; simpl in *; try contradiction.
  rewrite in_map_iff in Hin; destruct Hin as ((f', d) & E & Hin); simpl in E; subst f'.
  rewrite in_app_iff in Hin; destruct Hin as [Hin|Hin].
  - rewrite in_map_iff in Hin; destruct Hin as (m & E & Hin).
    unfold translate_method in E; inv E; eauto; constructor.
  - apply in_map with (f:=fst) in Hin; auto.
Qed.

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

Lemma InMembers_rec_instance_methods_temp:
  forall x s prog e,
    InMembers x (Env.elements (rec_instance_methods_temp prog s e)) <->
    InMembers x (Env.elements (rec_instance_methods_temp prog s (Env.empty type)))
    \/ InMembers x (Env.elements e).
Proof.
  induction s; simpl; split; intros Hin; try contradiction; try tauto.
  - rewrite IHs2, IHs1 in *; tauto.
  - rewrite IHs2, IHs1 in *; tauto.
  - rewrite IHs2, IHs1 in *; tauto.
  - rewrite IHs2, IHs1 in *; tauto.
  - destruct (find_class i0 prog) as [(?, ?)|]; auto.
    destruct (find_method i2 (c_methods c)); simpl in Hin; auto.
    destruct_list i; simpl in Hin; auto.
    destruct_list (m_out m) as (?, ?) ? ?; simpl in Hin; auto.
    rewrite <-Env.In_Members, Env.Props.P.F.add_in_iff in Hin.
    rewrite <-Env.In_Members, Env.Props.P.F.add_in_iff.
    destruct Hin; try tauto.
    right; rewrite <-Env.In_Members; auto.
  - destruct Hin as [Hin|Hin].
    + destruct (find_class i0 prog) as [(?, ?)|]; simpl in Hin; try contradiction.
      destruct (find_method i2 (c_methods c)); simpl in Hin; try contradiction.
      destruct_list i; simpl in Hin; try contradiction.
      destruct_list (m_out m) as (?, ?) ? ?; simpl in Hin; try contradiction.
      rewrite <-Env.In_Members, Env.Props.P.F.add_in_iff in Hin.
      rewrite <-Env.In_Members, Env.Props.P.F.add_in_iff.
      destruct Hin as [|Hin]; try tauto.
      rewrite Env.In_Members in Hin; try contradiction.
    + destruct (find_class i0 prog) as [(?, ?)|]; auto.
      destruct (find_method i2 (c_methods c)); auto.
      destruct_list i; auto.
      destruct_list (m_out m) as (?, ?) ? ?; auto.
      rewrite <-Env.In_Members in Hin.
      rewrite <-Env.In_Members, Env.Props.P.F.add_in_iff.
      tauto.
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

Lemma NoDup_funs:
  forall prog,
    wt_program prog ->
    NoDup (map fst (concat (map (make_methods prog) prog))).
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
  - inversion_clear Wt as [|? ? ? ? Nodup].
    rewrite map_app, map_map; simpl.
    apply NoDup_app'; auto.
    + simpl.
      pose proof (c_nodupm c) as Nodup'.
      induction (c_methods c) as [|m]; simpl;
        inversion_clear Nodup' as [|? ? Notin]; constructor; auto.
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
      eapply Forall_forall in Hin; eauto.
      congruence.
Qed.

Lemma InMembers_translate_param_idem:
  forall o xs,
    InMembers o (map translate_param xs) = InMembers o xs.
Proof.
  induction xs as [|x xs IH]; auto.
  destruct x. simpl. rewrite IH. reflexivity.
Qed.

Lemma make_out_temps_prefixed:
  forall x prog m,
    InMembers x (make_out_temps (instance_methods_temp prog m)) ->
    prefixed x.
Proof.
  unfold make_out_temps, instance_methods_temp.
  intros * Hin.
  induction (m_body m); simpl in *; try contradiction.
  - rewrite InMembers_translate_param_idem in *.
    rewrite InMembers_rec_instance_methods_temp in Hin.
    destruct Hin; auto.
  - rewrite InMembers_translate_param_idem in *.
    rewrite InMembers_rec_instance_methods_temp in Hin.
    destruct Hin; auto.
  - destruct (find_class i0 prog) as [(?, ?)|]; simpl in Hin; try contradiction.
    destruct (find_method i2 (c_methods c)); simpl in Hin; try contradiction.
    destruct_list i; simpl in Hin; try contradiction.
    destruct_list (m_out m0) as (?, ?) ? ?; simpl in Hin; try contradiction.
    rewrite InMembers_translate_param_idem, <-Env.In_Members, Env.Props.P.F.add_in_iff in Hin.
    destruct Hin as [|Hin].
    + subst; constructor.
    + rewrite Env.In_Members in Hin.
      simpl in Hin; try contradiction.
Qed.

Lemma build_check_size_env_ok:
  forall types gvars gvars_vol defs public main p,
    make_program' types gvars gvars_vol defs public main = OK p ->
    build_composite_env types = OK p.(prog_comp_env)
    /\ check_size_env p.(prog_comp_env) types = OK tt.
Proof.
  unfold make_program'; intros.
  destruct (build_composite_env' types) as [[gce ?]|?]; try discriminate.
  destruct (check_size_env gce types) eqn: E; try discriminate.
  destruct u; inv H; simpl; split; auto.
Qed.

Corollary build_ok:
  forall types gvars gvars_vol defs public main p,
    make_program' types gvars gvars_vol defs public main = OK p ->
    build_composite_env types = OK p.(prog_comp_env).
Proof.
  intros * H.
  apply (proj1 (build_check_size_env_ok _ _ _ _ _ _ _ H)).
Qed.

Corollary check_size_env_ok:
  forall types gvars gvars_vol defs public main p,
    make_program' types gvars gvars_vol defs public main = OK p ->
    check_size_env p.(prog_comp_env) types = OK tt.
Proof.
  intros * H.
  apply (proj2 (build_check_size_env_ok _ _ _ _ _ _ _ H)).
Qed.

Lemma check_size_ok:
  forall ce types,
    check_size_env ce types = OK tt ->
    Forall (fun t => match t with
                    Composite id _ _ _ => check_size ce id = OK tt
                  end) types.
Proof.
  intros * H.
  induction types as [|(id, su, m, attr) types IH]; auto.
  simpl in H.
  destruct (check_size ce id) eqn: E; try discriminate; destruct u; simpl in H.
  constructor; auto.
Qed.

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

Lemma type_pres_var:
  forall c m x t,
    Clight.typeof (translate_var c m x t) = cltype t.
Proof.
  intros; unfold translate_var; cases.
Qed.
Hint Resolve type_pres_var.

Lemma type_pres:
  forall c m e, Clight.typeof (translate_exp c m e) = cltype (typeof e).
Proof.
  induction e as [| |cst| | |]; simpl; auto.
  - destruct cst; simpl; reflexivity.
  - destruct u; auto.
Qed.
Hint Resolve type_pres.

Remark types_pres':
  forall f es,
    Forall2 (fun e x => Clight.typeof e = cltype (snd x)) es f.(m_in) ->
    type_of_params (map translate_param f.(m_in)) =
    list_type_to_typelist (map Clight.typeof es).
Proof.
  intro f.
  induction (m_in f) as [|(x, t)]; intros * Heq;
    inversion_clear Heq as [|? ? ? ? Ht]; simpl; auto.
  f_equal.
  - simpl in Ht; rewrite <-Ht; auto.
  - now apply IHl.
Qed.

Corollary types_pres:
  forall f c caller es,
    Forall2 (fun e x => typeof e = snd x) es f.(m_in) ->
    type_of_params (map translate_param f.(m_in)) =
    list_type_to_typelist (map Clight.typeof (map (translate_exp c caller) es)).
Proof.
  intros * Hes.
  apply types_pres'.
  rewrite Forall2_map_1.
  induction Hes as [|? (?&?)]; constructor;
    simpl in *; subst; auto.
Qed.

Lemma type_of_params_make_in_arg:
  forall xs,
    type_of_params (map translate_param xs) =
    list_type_to_typelist (map Clight.typeof (map make_in_arg xs)).
Proof.
  unfold translate_param, make_in_arg.
  induction xs as [|(x, t)]; simpl; auto.
  f_equal; auto.
Qed.

Lemma NoDupMembers_translate_param:
  forall f,
    NoDupMembers (map translate_param (m_in f)).
Proof.
  intro.
  unfold translate_param.
  pose proof (m_nodupin f) as Nodup.
  induction Nodup as [|??? Notin]; simpl; constructor; auto.
  intro Hin; apply Notin.
  apply InMembers_In in Hin as (?& Hin).
  apply in_map_iff in Hin as ((?&?) & E &?); inv E.
  eapply In_InMembers; eauto.
Qed.
Hint Resolve NoDupMembers_translate_param.

Lemma reserved_not_in_translate_param_meth_vars:
  forall f x,
    In x reserved ->
    ~ InMembers x (map translate_param (meth_vars f)).
Proof.
  intros ?? ? Hin.
  apply InMembers_In in Hin as (?&Hin).
  apply in_map_iff in Hin as ((?&?)&E&?); inv E.
  eapply (m_notreserved x); auto.
  eapply In_InMembers; eauto.
Qed.
Hint Resolve reserved_not_in_translate_param_meth_vars.

Corollary self_not_in_translate_param_in:
  forall f,
    ~ InMembers self (map translate_param (m_in f)).
Proof.
  intros.
  eapply NotInMembers_app; eauto; rewrite <-map_app.
  eapply reserved_not_in_translate_param_meth_vars; auto.
Qed.
Hint Resolve self_not_in_translate_param_in.

Corollary out_not_in_translate_param_in:
  forall f,
    ~ InMembers out (map translate_param (m_in f)).
Proof.
  intros.
  eapply NotInMembers_app; eauto; rewrite <-map_app.
  eapply reserved_not_in_translate_param_meth_vars; auto.
Qed.
Hint Resolve out_not_in_translate_param_in.

Corollary self_not_in_translate_param_vars:
  forall f,
    ~ InMembers self (map translate_param (m_vars f)).
Proof.
  intros.
  pose proof (reserved_not_in_translate_param_meth_vars f self) as Nin.
  intro Hin; apply Nin; auto.
  do 2  setoid_rewrite map_app.
  rewrite 2 InMembers_app; auto.
Qed.
Hint Resolve self_not_in_translate_param_vars.

Corollary out_not_in_translate_param_vars:
  forall f,
    ~ InMembers out (map translate_param (m_vars f)).
Proof.
  intros.
  pose proof (reserved_not_in_translate_param_meth_vars f out) as Nin.
  intro Hin; apply Nin; auto.
  do 2  setoid_rewrite map_app.
  rewrite 2 InMembers_app; auto.
Qed.
Hint Resolve out_not_in_translate_param_vars.

Lemma self_not_in_temps:
  forall prog f,
    ~ InMembers self (make_out_temps (instance_methods_temp prog f) ++ map translate_param (m_vars f)).
Proof.
  intros; apply NotInMembers_app; split; auto.
  intro Hin; apply make_out_temps_prefixed in Hin; auto.
Qed.
Hint Resolve self_not_in_temps.

Lemma out_not_in_temps:
  forall prog f,
    ~ InMembers out (make_out_temps (instance_methods_temp prog f) ++ map translate_param (m_vars f)).
Proof.
  intros; apply NotInMembers_app; split; auto.
  intro Hin; apply make_out_temps_prefixed in Hin; auto.
Qed.
Hint Resolve out_not_in_temps.

Lemma c_objs_field_offset:
  forall ge o c cls,
    In (o, c) cls.(c_objs) ->
    exists d, field_offset ge o (make_members cls) = Errors.OK d.
Proof.
  intros * Hin.
  unfold field_offset.
  cut (forall ofs, exists d,
            field_offset_rec ge o (make_members cls) ofs = Errors.OK d); auto.
  unfold make_members.
  apply in_split in Hin.
  destruct Hin as (ws & xs & Hin).
  rewrite Hin, map_app, map_cons.
  rewrite app_assoc.
  generalize (map translate_param cls.(c_mems) ++ map translate_obj ws).
  generalize (map translate_obj xs).
  clear Hin ws xs.
  intros ws xs.
  induction xs as [|x xs IH]; intros ofs.
  - simpl. setoid_rewrite peq_true. now eexists.
  - destruct x as (x, ty).
    destruct (ident_eq_dec o x) as [He|Hne].
    + simpl. rewrite He, peq_true. now eexists.
    + simpl. rewrite peq_false with (1:=Hne). apply IH.
Qed.

Lemma field_translate_mem_type:
  forall prog clsnm cls prog',
    find_class clsnm prog = Some (cls, prog') ->
    forall x ty,
      In (x, ty) cls.(c_mems) ->
      field_type x (make_members cls) = Errors.OK (cltype ty).
Proof.
  intros * Hfind ? ? Hin.
  apply in_field_type; auto.
  unfold make_members, translate_param. apply in_app_iff.
  left. rewrite in_map_iff.
  exists (x, ty); split; auto.
Qed.

Lemma field_translate_obj_type:
  forall prog clsnm cls prog',
    find_class clsnm prog = Some (cls, prog') ->
    forall o c,
      In (o, c) cls.(c_objs) ->
      field_type o (make_members cls) = Errors.OK (type_of_inst c).
Proof.
  intros * Hfind ? ? Hin.
  apply in_field_type; auto.
  unfold make_members. apply in_app_iff. right.
  apply in_map_iff. exists (o, c); auto.
Qed.

Remark eval_exprlist_app:
  forall tge e le m es es' vs vs',
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

Definition wf_struct (ge: composite_env) '((x, t): ident * Ctypes.type) : Prop :=
  exists id co,
    t = Tstruct id noattr
    /\ ge ! id = Some co
    /\ co_su co = Struct
    /\ NoDupMembers (co_members co)
    /\ forall x' t', In (x', t') (co_members co) ->
               exists chunk, access_mode t' = By_value chunk
                        /\ (Memdata.align_chunk chunk | alignof ge t').

Ltac contr := match goal with
              | H: ?x <> ?x |- _ => contradict H; auto
              | _ => auto; try discriminate; try contradiction
              end.

Definition case_out {A} (m: method) (anil: A) (asing: ident -> type -> A) (a: list (ident * type) -> A) : A :=
  match m.(m_out) with
  | [] => anil
  | [(x, t)] => asing x t
  | outs => a outs
  end.

Section MethodSpec.

  Variable (c: class) (f: method).

  Definition method_spec (prog: program) (fd: function) : Prop :=
    let f_out_param := case_out f
                                []
                                (fun _ _ => [])
                                (fun _ => [(out, type_of_inst_p (prefix_fun c.(c_name) f.(m_name)))]) in
    let f_return := case_out f
                             Tvoid
                             (fun _ t => cltype t)
                             (fun _ => Tvoid) in
    let f_temp_out := case_out f
                               []
                               (fun x t => [translate_param (x, t)])
                               (fun _ => []) in
    let f_body := return_with (translate_stmt prog c f f.(m_body))
                              (case_out f
                                        None
                                        (fun x t => Some (make_in_arg (x, t)))
                                        (fun _ => None)) in
    fd.(fn_params) = (self, type_of_inst_p c.(c_name))
                       :: f_out_param
                       ++ map translate_param f.(m_in)
    /\ fd.(fn_return) = f_return
    /\ fd.(fn_callconv) = AST.cc_default
    /\ fd.(fn_vars) = make_out_vars (instance_methods f)
    /\ fd.(fn_temps) = f_temp_out
                        ++ make_out_temps (instance_methods_temp prog f)
                        ++ map translate_param f.(m_vars)
    /\ list_norepet (var_names fd.(fn_params))
    /\ list_norepet (var_names fd.(fn_vars))
    /\ list_disjoint (var_names fd.(fn_params)) (var_names fd.(fn_temps))
    /\ fd.(fn_body) = f_body.

  Lemma method_spec_eq:
    forall prog fd1 fd2,
      method_spec prog fd1 ->
      method_spec prog fd2 ->
      fd1 = fd2.
  Proof.
    unfold method_spec; destruct fd1, fd2; simpl;
      intros; intuition; f_equal; congruence.
  Qed.

  Variable (ownerid cid: ident) (owner: class) (prog prog' prog'': program) (fid: ident).
  Hypothesis (Findowner : find_class ownerid prog = Some (owner, prog'))
             (Findcl    : find_class cid prog' = Some (c, prog''))
             (Findmth   : find_method fid c.(c_methods) = Some f)
             (WTp       : wt_program prog).

  Lemma instance_methods_temp_find_class:
    instance_methods_temp prog' f = instance_methods_temp prog f.
  Proof.
    assert (wt_method prog'' c.(c_objs) c.(c_mems) f) as WT.
    { eapply wt_class_find_method; eauto.
      eapply wt_program_find_class; eauto.
      eapply find_class_chained; eauto.
    }
    unfold instance_methods_temp.
    unfold wt_method in WT.
    generalize (Env.empty type).
    induction f.(m_body);
      inversion_clear WT as [| | | |????????? Findcl' Findmth'|]; intro; simpl; auto.
    - rewrite IHs1; auto.
    - rewrite IHs1; auto.
    - assert (wt_program prog') by (eapply wt_program_find_class; eauto).
      do 2 (erewrite find_class_chained, Findmth'; eauto).
      erewrite find_class_chained; eauto.
  Qed.

  Lemma translate_stmt_find_class:
    translate_stmt prog' c f (m_body f) = translate_stmt prog c f (m_body f).
  Proof.
     assert (wt_method prog'' c.(c_objs) c.(c_mems) f) as WT.
    { eapply wt_class_find_method; eauto.
      eapply wt_program_find_class; eauto.
      eapply find_class_chained; eauto.
    }
    unfold wt_method in WT.
    induction (m_body f);
     inversion_clear WT as [| | | |????????? Findcl' Findmth'|]; simpl; auto.
    - now rewrite IHs1, IHs2.
    - now rewrite IHs1, IHs2.
    - assert (wt_program prog') by (eapply wt_program_find_class; eauto).
      unfold binded_funcall.
      do 2 (erewrite find_class_chained, Findmth'; eauto).
      erewrite find_class_chained; eauto.
  Qed.

  Lemma method_spec_find_class:
    forall fd,
      method_spec prog' fd <-> method_spec prog fd.
  Proof.
    intros; unfold method_spec.
    rewrite instance_methods_temp_find_class, translate_stmt_find_class;
      reflexivity.
  Qed.

End MethodSpec.

Ltac inv_trans_tac H En Estep Ereset s f E :=
  match type of H with
    translate ?b ?a ?n ?p = Errors.OK ?tp =>
    unfold translate in H;
    destruct (find_class n p) as [(c, cls)|] eqn: En; try discriminate;
    destruct (find_method step c.(c_methods)) eqn: Estep; try discriminate;
    destruct (find_method reset c.(c_methods)) eqn: Ereset; try discriminate;
    destruct (split (map (translate_class p) p)) as (s, f) eqn: E
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

Section TranslateOk.

  Variable main_node : ident.

  Variable prog: program.
  Variable tprog: Clight.program.
  Variable do_sync: bool.
  Variable all_public: bool.

  Let tge := globalenv tprog.
  Let gcenv := genv_cenv tge.

  Hypothesis TRANSL: translate do_sync all_public main_node prog = Errors.OK tprog.
  Hypothesis WT: wt_program prog.

  Lemma find_self:
    exists sb, Genv.find_symbol tge (glob_id self) = Some sb.
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

  Lemma Consistent:
    composite_env_consistent gcenv.
  Proof.
    inv_trans TRANSL.
    apply build_ok in TRANSL.
    apply build_composite_env_consistent in TRANSL; auto.
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
          rewrite Permutation.Permutation_app_comm, <-app_assoc in Nodup.
          now apply NoDupMembers_app_r in Nodup; rewrite Permutation.Permutation_app_comm in Nodup.
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
        apply find_class_In in Findcl.
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
            apply find_class_In in Findcl.
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
          /\ method_spec owner caller prog f.
      Proof.
        unfold method_spec.
        pose proof prog_defs_norepet as Norepet.
        inv_trans TRANSL with structs funs E.
        pose proof (find_class_name _ _ _ _ Findcl);
          pose proof (find_method_name _ _ _ Findmth); subst.
        assert ((AST.prog_defmap tprog) ! (prefix_fun owner.(c_name) caller.(m_name)) =
                Some (snd (translate_method prog owner caller))) as Hget.
        { unfold translate_class in E.
          apply split_map in E.
          destruct E as [? Funs].
          unfold make_methods in Funs.
          apply find_class_In in Findcl.
          apply in_map with (f:=fun c => map (translate_method prog c) (c_methods c))
            in Findcl.
          apply find_method_In in Findmth.
          apply in_map with (f:=translate_method prog owner) in Findmth.
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
        assert (NoDupMembers (m_in caller ++ Env.elements (instance_methods_temp prog caller)
                                   ++ m_vars caller)) as Nodup'.
        { pose proof (m_nodupvars caller) as Nodup.
          apply NoDupMembers_app.
          - apply NoDupMembers_app_l in Nodup; auto.
          - apply NoDupMembers_app.
            + apply Env.NoDupMembers_elements.
            + apply NoDupMembers_app_r, NoDupMembers_app_l in Nodup; auto.
            + intros x Hin.
              pose proof (make_out_temps_prefixed x prog caller) as Pref.
              unfold make_out_temps in Pref;
                rewrite InMembers_translate_param_idem in Pref.
              apply Pref, (m_notprefixed x caller) in Hin.
              unfold meth_vars in Hin; repeat rewrite NotInMembers_app in Hin; tauto.
          - intros x Hin.
            rewrite NotInMembers_app; split.
            * apply (NoDupMembers_app_InMembers x) in Nodup; auto.
              apply NotInMembers_app in Nodup; tauto.
            * pose proof (make_out_temps_prefixed x prog caller) as Pref.
              unfold make_out_temps in Pref;
                rewrite InMembers_translate_param_idem in Pref.
              intro Hin'; apply Pref, (m_notprefixed x caller) in Hin'.
              unfold meth_vars in Hin'; repeat rewrite NotInMembers_app in Hin'.
              contradict Hin; tauto.
        }

        assert (~In self (var_names (make_out_temps (instance_methods_temp prog caller)
                                                    ++ map translate_param (m_vars caller)))).
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
                              (var_names (make_out_temps (instance_methods_temp prog caller)
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
                              (var_names (make_out_temps (instance_methods_temp prog caller)
                                                         ++ map translate_param caller.(m_vars)))).
         { repeat apply list_disjoint_cons_l; auto.
           apply NoDupMembers_disjoint.
           pose proof (m_nodupvars caller) as Nodup.
           unfold make_out_temps.
           rewrite fst_NoDupMembers; repeat rewrite map_app; repeat rewrite translate_param_fst.
           simpl; rewrite <-2map_app, <-fst_NoDupMembers; auto.
         }
         unfold case_out in *.

        destruct_list caller.(m_out) as (y, t) ? ? : Out.
        - set (f:= {|
                    fn_return := Tvoid;
                    fn_callconv := AST.cc_default;
                    fn_params := (self, type_of_inst_p (c_name owner)) :: map translate_param (m_in caller);
                    fn_vars := make_out_vars (instance_methods caller);
                    fn_temps := make_out_temps (instance_methods_temp prog caller)
                                ++ map translate_param (m_vars caller);
                    fn_body := return_with (translate_stmt prog owner caller (m_body caller)) None |})
            in Finddef.
          exists loc_f, f.
          try repeat split; auto.
          change (Genv.find_funct_ptr tge loc_f) with (Genv.find_funct_ptr (Genv.globalenv tprog) loc_f).
          unfold Genv.find_funct_ptr.
          now setoid_rewrite Finddef.
        - set (f:= {|
                    fn_return := cltype t;
                    fn_callconv := AST.cc_default;
                    fn_params := (self, type_of_inst_p (c_name owner))
                                   :: map translate_param (m_in caller);
                    fn_vars := make_out_vars (instance_methods caller);
                    fn_temps := translate_param (y, t)
                                :: make_out_temps (instance_methods_temp prog caller) ++
                                   map translate_param (m_vars caller);
                    fn_body := return_with (translate_stmt prog owner caller (m_body caller))
                                           (Some (make_in_arg (y, t))) |})
            in Finddef.
          exists loc_f, f.
          try repeat split; auto.
          change (Genv.find_funct_ptr tge loc_f) with (Genv.find_funct_ptr (Genv.globalenv tprog) loc_f).
          unfold Genv.find_funct_ptr.
          now setoid_rewrite Finddef.
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
                    fn_temps := make_out_temps (instance_methods_temp prog caller) ++
                                map translate_param (m_vars caller);
                    fn_body := return_with (translate_stmt prog owner caller (m_body caller)) None |})
            in Finddef.
          exists loc_f, f.
          try repeat split; auto.
          change (Genv.find_funct_ptr tge loc_f) with (Genv.find_funct_ptr (Genv.globalenv tprog) loc_f).
          unfold Genv.find_funct_ptr.
          now setoid_rewrite Finddef.
      Qed.

    End MethodProperties.
  End ClassProperties.

  Lemma instance_methods_caract:
    forall ownerid owner prog' callerid caller,
      find_class ownerid prog = Some (owner, prog') ->
      find_method callerid owner.(c_methods) = Some caller ->
      Forall (fun xt => sizeof tge (snd xt) <= Int.max_unsigned /\ wf_struct gcenv xt)
             (make_out_vars (instance_methods caller)).
  Proof.
    intros * Findcl Findmth.
    edestruct wt_program_find_class as [WT']; eauto.
    eapply wt_class_find_method in WT'; eauto.
    apply Forall_forall; intros (?&?) Hin.
    unfold make_out_vars in Hin; apply in_map_iff in Hin;
      destruct Hin as (((o, fid), cid) & E & Hin); inv E.
    rewrite <-setoid_in_key_elt in Hin; apply M.elements_2 in Hin.
    assert (In (o, cid) (c_objs owner)) by (eapply In_instance_methods_In_insts; eauto).
    edestruct well_formed_instance_methods as (c & cls & callee & Findc & Findcallee & Notnil); eauto.
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
      rewrite Hmembers.
      intros * Hinxt; unfold translate_param in Hinxt.
      apply in_map_iff in Hinxt;
        destruct Hinxt as ((x, t) & Eq & Hinxt); inv Eq; eauto.
  Qed.
  Lemma find_main_class_sig: {c_prog_main | find_class main_node prog = Some c_prog_main}.
  Proof.
    pose proof TRANSL as Trans; inv_trans Trans as En Estep Ereset with structs funs E; eauto.
  Qed.

  Definition c_main   : class := fst (proj1_sig find_main_class_sig).
  Definition prog_main: program := snd (proj1_sig find_main_class_sig).

  Definition find_main_class: find_class main_node prog = Some (c_main, prog_main).
  Proof.
    unfold c_main, prog_main; destruct find_main_class_sig as ((?&?)&?); simpl; auto.
  Qed.

  Lemma find_main_step_sig: {m_step | find_method step c_main.(c_methods) = Some m_step}.
  Proof.
    pose proof TRANSL as Trans; inv_trans Trans as En Estep Ereset with structs funs E.
    rewrite find_main_class in En; inv En; eauto.
  Qed.

  Lemma find_main_reset_sig: {m_reset | find_method reset c_main.(c_methods) = Some m_reset}.
  Proof.
    pose proof TRANSL as Trans; inv_trans Trans as En Estep Ereset with structs funs E.
    rewrite find_main_class in En; inv En; eauto.
  Qed.

  Definition main_step : method := proj1_sig find_main_step_sig.
  Definition main_reset: method := proj1_sig find_main_reset_sig.

  Definition find_main_step : find_method step c_main.(c_methods) = Some main_step := proj2_sig find_main_step_sig.
  Definition find_main_reset: find_method reset c_main.(c_methods) = Some main_reset := proj2_sig find_main_reset_sig.

  Lemma TranslateClasses: {structs_funs | split (map (translate_class prog) prog) = structs_funs}.
  Proof.
    pose proof TRANSL as Trans; inv_trans Trans as En Estep Ereset with structs funs E; eauto.
  Qed.

  Definition structs: list (list composite_definition) := fst (proj1_sig TranslateClasses).
  Definition funs   : list (list (ident * AST.globdef _ _)) := snd (proj1_sig TranslateClasses).

  Lemma tprog_defs:
    let ce := globalenv tprog in
    tprog.(prog_defs) = map (vardef ce false) [(glob_id self, type_of_inst main_node)] ++
                            map (vardef ce true) (map glob_bind (m_out main_step) ++
                                                      map glob_bind (m_in main_step)) ++
                            concat funs ++
                            (if do_sync
                             then [(sync_id, make_sync);
                                     (main_sync_id, make_main do_sync main_node main_step)]
                             else []) ++
                            [(main_id, make_main false main_node main_step)].
  Proof.
    pose proof TRANSL as Trans; inv_trans Trans as En Estep Ereset with structs funs E.
    intro; subst ce tge.
    unfold TranslateOk.funs; rewrite (proj2_sig TranslateClasses) in E.
    destruct (proj1_sig TranslateClasses); inv E; simpl snd.
    rewrite find_main_class in En; inv En.
    rewrite find_main_step in Estep; inv Estep.
    unfold make_program' in Trans.
    destruct (build_composite_env' (concat structs)) as [(ce, ?)|]; try discriminate.
    destruct (check_size_env ce (concat structs)); try discriminate.
    inversion Trans; eauto.
  Qed.

  Definition is_volatile (xt: ident * type) :=
    let (x, t) := xt in
    exists b, Genv.find_symbol (globalenv tprog) (glob_id x) = Some b
         /\ Genv.block_is_volatile (globalenv tprog) b = true.

  Lemma in_vardef_is_volatile:
    forall x t,
      In ((vardef (globalenv tprog) true) (glob_bind (x, t))) tprog.(prog_defs) ->
      is_volatile (x, t).
  Proof.
    intros * Hin.
    set (ty := merge_attributes (cltype t) (mk_attr true None)).
    assert ((AST.prog_defmap tprog) ! (glob_id x) =
            Some (@AST.Gvar Clight.fundef _
                            (AST.mkglobvar ty [AST.Init_space (Ctypes.sizeof (globalenv tprog) ty)] false true)))
        as Hget.
    { subst ty.
      unfold AST.prog_defmap; simpl.
      apply PTree_Properties.of_list_norepet; eauto using prog_defs_norepet.
    }
    apply Genv.find_def_symbol in Hget as (b & Findsym & Finddef).
    unfold is_volatile.
    exists b; split; auto.
    unfold Genv.block_is_volatile, Genv.find_var_info.
    setoid_rewrite Finddef; auto.
  Qed.

  Lemma volatile_step_in:
    Forall is_volatile main_step.(m_in).
  Proof.
    apply Forall_forall; intros (x, t) Hin.
    eapply in_vardef_is_volatile; rewrite tprog_defs; simpl.
    rewrite map_app.
    apply in_cons, in_app; left; apply in_app; right.
    apply in_map_iff.
    exists (glob_id x, cltype t); split; auto.
    apply in_map_iff.
    exists (x, t); split; auto.
  Qed.

  Lemma volatile_step_out:
    Forall is_volatile main_step.(m_out).
  Proof.
    apply Forall_forall; intros (x, t) Hin.
    apply in_vardef_is_volatile; rewrite tprog_defs; simpl.
    rewrite map_app.
    apply in_cons, in_app; left; apply in_app; left.
    apply in_map_iff.
    exists (glob_id x, cltype t); split; auto.
    apply in_map_iff.
    exists (x, t); split; auto.
  Qed.

  Lemma tprog_main_id:
    Ctypes.prog_main tprog = main_id.
  Proof.
    pose proof TRANSL as Trans; inv_trans Trans as En Estep Ereset with structs funs E.
    unfold make_program' in Trans.
    destruct (build_composite_env' (concat structs)) as [(ce, ?)|]; try discriminate.
    destruct (check_size_env ce (concat structs)); try discriminate.
    inv Trans; auto.
  Qed.

  Let out_step   := prefix out step.
  Let t_out_step := type_of_inst (prefix_fun main_node step).

  Definition main_f: function :=
    {|
      fn_return := type_int32s;
      fn_callconv := AST.cc_default;
      fn_params := [];
      fn_vars := case_out main_step
                          []
                          (fun _ _ => [])
                          (fun _ => [(out_step, t_out_step)]);
      fn_temps := map translate_param
                      (case_out main_step
                                []
                                (fun y t => [(y, t)])
                                (fun _ => [])  ++ m_in main_step);
      fn_body := main_body false main_node main_step;
    |}.

  Remark norepet_vars_main:
    list_norepet (var_names (fn_vars main_f)).
  Proof.
    simpl; unfold case_out; cases; simpl; auto using list_norepet.
  Qed.

  Remark norepet_params_main:
    list_norepet (var_names (fn_params main_f)).
  Proof.
    simpl; constructor.
  Qed.

  Remark disjoint_params_temps_main:
    list_disjoint (var_names (fn_params main_f)) (var_names (fn_temps main_f)).
  Proof.
    apply NoDupMembers_disjoint; simpl; unfold case_out.
    destruct_list (m_out main_step) as (?,?) (?,?) ? : Hout; simpl app;
      rewrite fst_NoDupMembers, translate_param_fst, <-fst_NoDupMembers;
      auto using m_nodupin.
    constructor; auto using m_nodupin.
    pose proof (m_nodupvars main_step) as Nodup.
    rewrite Permutation.Permutation_app_comm in Nodup.
    eapply NoDupMembers_app_InMembers; eauto.
    apply InMembers_app; right; rewrite Hout; constructor; auto.
  Qed.

  Lemma well_initialized:
    forall id v,
      In (id, AST.Gvar v) (AST.prog_defs tprog) ->
      Genv.init_data_list_aligned 0 (AST.gvar_init v)
      /\ (forall i ofs,
            In (AST.Init_addrof i ofs) (AST.gvar_init v) ->
            exists b, Genv.find_symbol (Genv.globalenv tprog) i = Some b).
  Proof.
    inv_trans TRANSL as En Estep Ereset with structs funs E.
    pose proof (build_ok _ _ _ _ _ _ _ TRANSL) as Hbuild.
    apply make_program_defs in TRANSL; destruct TRANSL as (gce & Hbuild' & Eq); clear TRANSL.
    rewrite Hbuild in Hbuild'; inv Hbuild'.
    rewrite Eq; clear Eq.
    simpl; intros * [Hinv|Hinv].
    - inv Hinv; simpl; split.
      + split; auto; apply Z.divide_0_r.
      + intros * Hinio; simpl in Hinio;
          destruct Hinio; [discriminate|contradiction].
    - repeat rewrite in_app in Hinv;
        destruct Hinv as [Hinv|[Hinv|[Hinv|Hinv]]]; try now inv Hinv.
      + induction (map glob_bind (m_out m) ++ map glob_bind (m_in m)) as [|(x, t)].
        * contradict Hinv.
        * destruct Hinv as [Hinv|]; auto.
          inv Hinv; simpl; split.
          -- split; auto; apply Z.divide_0_r.
          -- intros * Hinio; simpl in Hinio;
               destruct Hinio; [discriminate|contradiction].
      + clear En Hbuild WT.
        remember prog as prog1.
        replace (translate_class prog1) with (translate_class prog) in E
          by now rewrite <-Heqprog1.
        clear Heqprog1.
        revert structs funs E Hinv.
        induction prog1 as [|c' prog']; intros * E Hinv; simpl in E.
        * inv E; simpl in Hinv; contradiction.
        * destruct (split (map (translate_class prog) prog')) as (g, d) eqn: Egd; inv E.
          simpl in Hinv.
          apply in_app in Hinv; destruct Hinv as [Hinv|]; eauto.
          unfold make_methods in Hinv.
          induction (c_methods c'); simpl in Hinv; try contradiction.
          destruct Hinv as [Hinv|]; auto.
          unfold translate_method in Hinv.
          destruct_list (m_out a) as (?, ?) ? ?; inv Hinv.
           (* - rewrite map_app in E; simpl in E; rewrite split_last in E. *)
           (*   destruct (split (map (translate_class (rev prog)) (rev prog'))) as (g, d) eqn: Egd; inv E. *)
           (*   rewrite concat_app in Hinv; simpl in Hinv; rewrite app_nil_r in Hinv; *)
           (*     apply in_app in Hinv; destruct Hinv as [|Hinv]; eauto. *)
           (*   unfold make_methods in Hinv. *)
           (*   induction (c_methods c'); simpl in Hinv; try contradiction. *)
           (*   destruct Hinv as [Hinv|]; auto. *)
           (*   unfold translate_method in Hinv. *)
           (*   destruct_list (m_out a) as (?, ?) ? ?; inv Hinv. *)

    + destruct do_sync; try now inv Hinv.
          rewrite cons_is_app, in_app in Hinv.
          destruct Hinv as [[Hinv|Hinv]|[Hinv|Hinv]]; try inv Hinv.
  Qed.

  Lemma find_main_ptr:
    exists b,
      Genv.find_symbol tge main_id = Some b
      /\ Genv.find_funct_ptr tge b = Some (Ctypes.Internal main_f).
  Proof.
    assert ((AST.prog_defmap tprog) ! main_id = Some (make_main false main_node main_step)) as Hget.
    { unfold AST.prog_defmap; apply PTree_Properties.of_list_norepet.
      - eapply prog_defs_norepet; eauto.
      - setoid_rewrite tprog_defs; eauto.
        apply in_cons, in_app; right; apply in_app; right.
        generalize do_sync; intro; cases; [do 2 apply in_cons|]; apply in_eq.
    }
    apply Genv.find_def_symbol in Hget as (b & Findsym & Finddef).
    exists b; split; auto.
    unfold Genv.find_funct_ptr; subst tge; setoid_rewrite Finddef.
    unfold main_f; unfold case_out; simpl; repeat f_equal; cases.
  Qed.

End TranslateOk.

Hint Resolve Consistent prog_defs_norepet make_members_co.
Hint Resolve norepet_vars_main norepet_params_main disjoint_params_temps_main.
