From Coq Require Import ZArith.

From compcert Require Import common.Errors.
From compcert Require Import common.Globalenvs.
From compcert Require Import lib.Coqlib.
From compcert Require Import lib.Maps.
From compcert Require Import lib.Integers.
From compcert Require Import cfrontend.Ctypes.
From compcert Require Import cfrontend.Clight.
From compcert Require Import cfrontend.ClightBigstep.

From Velus Require Import Common.
From Velus Require Import CommonTyping.
From Velus Require Import Common.CompCertLib.
From Velus Require Import Ident.
From Velus Require Import Environment.
From Velus Require Import ObcToClight.Generation.
From Velus Require Import ObcToClight.Interface.

Import OpAux.
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
  - destruct (IHl k x); apply InMembers_cons; auto.
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
  apply F.add_mapsto_iff in Hin as [[[]]|[[]]]; simpl in *; auto.
Qed.

Lemma MapsTo_add_empty:
  forall o f o' f' c c',
    M.MapsTo (o, f) c (M.add (o', f') c' (M.empty ident)) ->
    o = o' /\ f = f' /\ c = c'.
Proof.
  intros * Hin.
  apply F.add_mapsto_iff in Hin as [[[]]|[? Hin]]; simpl in *; auto.
  apply F.empty_mapsto_iff in Hin; contradiction.
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
  apply F.add_mapsto_iff in Hin as [[[]]|[? Hin]]; simpl in *; subst; auto.
  apply M.elements_1, setoid_in_key_elt in Hin; auto.
Qed.

Remark translate_param_fst:
  forall xs, map fst (map translate_param xs) = map fst xs.
Proof.
  intro; rewrite map_map.
  induction xs as [|(x, t)]; simpl; auto.
Qed.

Remark translate_obj_fst:
  forall objs, map fst (map translate_obj objs) = map fst objs.
Proof.
  intro; rewrite map_map.
  induction objs as [|(o, k)]; simpl; auto.
Qed.

Lemma NoDupMembers_make_members : forall c,
    NoDupMembers (map (fun '(y, t) => (y, translate_type t)) (c_mems c) ++ map translate_obj (c_objs c)).
Proof.
  intro; unfold make_members.
  pose proof (c_nodup c) as Nodup.
  rewrite fst_NoDupMembers.
  rewrite map_app.
  now rewrite translate_param_fst, translate_obj_fst.
Qed.
Global Hint Resolve NoDupMembers_make_members : clight.

Corollary NoDupMembers_make_members' : forall c,
    NoDup (map name_member (make_members c)).
Proof.
  intro. unfold make_members.
  rewrite mk_members_names, <-fst_NoDupMembers; eauto with clight.
Qed.
Global Hint Resolve NoDupMembers_make_members' : clight.

Lemma glob_bind_vardef_fst:
  forall xs env volatile,
    map fst (map (vardef env volatile) (map glob_bind xs)) =
    map (fun xt => prefix_glob (fst xt)) xs.
Proof.
  induction xs as [|(x, t)]; simpl; intros; auto.
Qed.

Lemma NoDup_prefix_glob:
  forall {A} (xs: list (ident * A)),
    NoDupMembers xs ->
    NoDup (map (fun xt => prefix_glob (fst xt)) xs).
Proof.
  induction xs as [|(x, t)]; intros Hnd; simpl;
    inv Hnd; constructor; auto.
  rewrite in_map_iff; intros ((x', t') & E & Hin).
  simpl in E; apply prefix_glob_injective in E; subst.
  eapply H1, In_InMembers; eauto.
Qed.

Lemma prefixed_funs:
  forall prog f,
    In f (map fst (concat (map (make_methods prog) prog.(classes)))) ->
    exists m c, f = prefix_fun m c.
Proof.
  unfold make_methods.
  intros * Hin.
  induction (classes prog) as [|c]; simpl in *; try contradiction.
  rewrite in_map_iff in Hin; destruct Hin as ((f', d) & E & Hin); simpl in E; subst f'.
  rewrite in_app_iff in Hin; destruct Hin as [Hin|Hin].
  - rewrite in_map_iff in Hin; destruct Hin as (m & E & Hin).
    unfold translate_method in E; inv E; eauto.
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
    InMembers x (Env.elements (rec_instance_methods_temp prog e s)) <->
    InMembers x (Env.elements (rec_instance_methods_temp prog (Env.empty _) s))
    \/ InMembers x (Env.elements e).
Proof.
  induction s using stmt_ind2'; simpl; intros; try tauto.
  - revert e0; revert dependent s.
    take (Forall _ _) and induction it as [|[|] ??? IH]; simpl in *; intros; auto.
    rewrite IH, IHs; auto; symmetry; rewrite IH, IHs; auto; tauto.
  - rewrite IHs2, IHs1; symmetry; rewrite IHs2; tauto.
  - destruct (find_class c prog) as [(cls, ?)|]; [|rewrite Env.Props.P.elements_empty; intuition].
    destruct (find_method f (c_methods cls)); [|rewrite Env.Props.P.elements_empty; intuition].
    destruct_list ys; simpl; try tauto.
    destruct_list (m_out m) as (?, ?) ? ?; simpl; try tauto.
    rewrite <- 3 Env.In_Members, 2 Env.Props.P.F.add_in_iff, Env.Props.P.F.empty_in_iff; tauto.
Qed.

Lemma InMembers_rec_extcalls_temp:
  forall x s e,
    InMembers x (Env.elements (rec_extcalls_temp e s)) <->
    InMembers x (Env.elements (rec_extcalls_temp (Env.empty _) s))
    \/ InMembers x (Env.elements e).
Proof.
  induction s using stmt_ind2'; simpl; intros; try tauto.
  - revert e0; revert dependent s.
    take (Forall _ _) and induction it as [|[|] ??? IH]; simpl in *; intros; auto.
    rewrite IH, IHs; auto; symmetry; rewrite IH, IHs; auto; tauto.
  - rewrite IHs2, IHs1; symmetry; rewrite IHs2; tauto.
  - rewrite <- 3 Env.In_Members, 2 Env.Props.P.F.add_in_iff, Env.Props.P.F.empty_in_iff; tauto.
Qed.

Lemma In_rec_instance_methods_In_insts:
  forall s m o fid cid p insts mems vars,
    wt_stmt p insts mems vars s ->
    M.MapsTo (o, fid) cid (rec_instance_methods m s) ->
    (forall o f c, M.MapsTo (o, f) c m -> In (o, c) insts) ->
    In (o, cid) insts.
Proof.
  induction s using stmt_ind2'; intros * Wt Hin Spec; inv Wt; simpl in *; eauto.
  - revert dependent m; revert dependent s.
    take (length _ = _) and clear it; induction ss as [|[|] ? IH]; simpl in *; intros; eauto;
      take (Forall _ (_ :: _)) and inv it; eauto.
    eapply IH; eauto.
  - destruct_list ys; eauto.
    apply F.add_mapsto_iff in Hin as [[[]]|[]]; simpl in *; subst; eauto.
Qed.

Lemma In_instance_methods_In_insts:
  forall f o fid cid p insts mems,
    wt_method p insts mems f ->
    M.MapsTo (o, fid) cid (instance_methods f) ->
    In (o, cid) insts.
Proof.
  unfold wt_method, instance_methods.
  intros * (?&?) ?.
  eapply In_rec_instance_methods_In_insts; eauto.
  intros o' f' c' Hin.
  apply M.find_1 in Hin; discriminate.
Qed.

Lemma In_rec_instance_methods:
  forall s m o fid cid p insts mems vars,
    wt_stmt p insts mems vars s ->
    NoDupMembers insts ->
    In (o, cid) insts ->
    (M.MapsTo (o, fid) cid (rec_instance_methods m s) <->
     M.MapsTo (o, fid) cid (rec_instance_methods (M.empty _) s)
     \/ M.MapsTo (o, fid) cid m).
Proof.
  induction s using stmt_ind2'; simpl; intros * Wt Nodup Ho; inv Wt;
    try (rewrite F.empty_mapsto_iff; tauto).
  - revert m; revert dependent s.
    take (length _ = _) and clear it;
      induction ss as [|[|] ? IH]; simpl in *; intros; eauto;
        take (Forall _ (_ :: _)) and inv it; eauto.
    rewrite IH, IHs; eauto; symmetry; rewrite IH; auto; tauto.
  - rewrite IHs2, IHs1; eauto; symmetry; rewrite IHs2, IHs1; eauto; tauto.
  - destruct_list ys;
    try (rewrite F.empty_mapsto_iff; tauto).
    rewrite 2 F.add_mapsto_iff, F.empty_mapsto_iff; simpl; split; try tauto.
    intros [|Hin]; try tauto.
    destruct (M.E.eq_dec (i, f) (o, fid)) as [[]|]; simpl in *; try tauto.
    subst; app_NoDupMembers_det; tauto.
Qed.

Lemma In_rec_instance_methods_temp_find_method :
  forall s m fid p,
    Env.In fid (rec_instance_methods_temp p m s) ->
    (Env.In fid m -> exists cls c p' fm cid' o,
        find_class cls p = Some (c, p') /\
        find_method cid' c.(c_methods) = Some fm /\
        fid = prefix_temp cid' o) ->
    exists cls c p' fm cid' o,
      find_class cls p = Some (c, p') /\
      find_method cid' c.(c_methods) = Some fm /\
      fid = prefix_temp cid' o.
Proof.
  induction s using stmt_ind2'; intros * Hin Hfind; simpl in *; eauto.
  - revert m Hin Hfind; revert dependent s.
    induction ss as [|[|] ? IH]; simpl in *; intros; eauto;
      inv H; eauto.
  - destruct (find_class _ _) eqn:Hclass; eauto. destruct p0.
    destruct (find_method _ _) eqn:Hmethod; eauto.
    destruct_list ys; eauto.
    destruct_list (m_out m0); eauto. 1,2:destruct x0; eauto.
    apply Env.Props.P.F.add_in_iff in Hin as [?|?]; subst; eauto 10.
Qed.

Corollary In_instance_methods_temp_find_method :
  forall m fid p,
    Env.In fid (instance_methods_temp p m) ->
    exists cls c p' fm cid' o,
      find_class cls p = Some (c, p') /\
      find_method cid' c.(c_methods) = Some fm /\
      fid = prefix_temp cid' o.
Proof.
  unfold instance_methods_temp.
  intros.
  eapply In_rec_instance_methods_temp_find_method; eauto.
  intros Hin.
  rewrite Env.Props.P.F.empty_in_iff in Hin. inv Hin.
Qed.

Lemma In_fold_left_rec_instance_methods:
  forall ss o fid cid p insts mems m vars,
    (forall s, In (Some s) ss -> wt_stmt p insts mems vars s) ->
    NoDupMembers insts ->
    In (o, cid) insts ->
    M.MapsTo (o, fid) cid (fold_left (fun m => or_default_with m (rec_instance_methods m)) ss m) <->
    M.MapsTo (o, fid) cid m
    \/ exists s, In (Some s) ss
           /\ M.MapsTo (o, fid) cid (rec_instance_methods (M.empty _) s).
Proof.
  induction ss as [|os]; simpl; intros * WTss Nodup Hin.
  - split; auto; intros [|[?[]]]; auto; contradiction.
  - rewrite IHss; eauto.
    destruct os; simpl in *.
    + rewrite In_rec_instance_methods; eauto.
      split; intros [Hin'|Hin']; auto.
      * destruct Hin'; eauto.
      * destruct Hin' as (?&?&?); eauto.
      * destruct Hin' as (?&[E|]&?); eauto.
        inv E; auto.
    + split; intros [Hin'|Hin']; auto.
      * destruct Hin' as (?&?&?); eauto.
      * destruct Hin' as (?&[|]&?); eauto.
        discriminate.
Qed.

Corollary In_fold_left_rec_instance_methods':
  forall ss o fid cid p insts mems vars,
    (forall s, In (Some s) ss -> wt_stmt p insts mems vars s) ->
    NoDupMembers insts ->
    In (o, cid) insts ->
    M.MapsTo (o, fid) cid (fold_left (fun m => or_default_with m (rec_instance_methods m)) ss (M.empty _)) <->
    exists s, In (Some s) ss
         /\ M.MapsTo (o, fid) cid (rec_instance_methods (M.empty _) s).
Proof.
  intros.
  rewrite In_fold_left_rec_instance_methods, F.empty_mapsto_iff; eauto; tauto.
Qed.

Lemma In_rec_instance_methods_find_method :
  forall s m o fid cid p (insts : list (ident * ident)) mems vars,
    wt_stmt p insts mems vars s ->
    M.MapsTo (o, fid) cid (rec_instance_methods m s) ->
    (M.MapsTo (o, fid) cid m -> exists c p' fm,
          find_class cid p = Some (c, p') /\
          find_method fid c.(c_methods) = Some fm /\
          InMembers o insts) ->
    exists c p' fm,
      find_class cid p = Some (c, p') /\
      find_method fid c.(c_methods) = Some fm /\
      InMembers o insts.
Proof.
  induction s using stmt_ind2'; intros * Wt Hin Hfind; inv Wt; simpl in *; eauto.
  - clear H4 H5 H6. revert m Hin Hfind; revert dependent s.
    induction ss as [|[|] ? IH]; simpl in *; intros; inv H; eauto 12.
  - destruct_list ys; eauto.
    destruct (M.E.eq_dec (i, f) (o, fid)) as [[E1 E2]|E1]; simpl in *; subst.
    + apply MapsTo_add_same in Hin; subst.
      repeat eexists; eauto.
      eapply In_InMembers; eauto.
    + apply M.add_3 in Hin; eauto.
Qed.

Corollary In_instance_methods_find_method :
  forall f o fid cid p insts mems,
    wt_method p insts mems f ->
    M.MapsTo (o, fid) cid (instance_methods f) ->
    exists c p' fm,
      find_class cid p = Some (c, p') /\
      find_method fid c.(c_methods) = Some fm /\
      InMembers o insts.
Proof.
  unfold wt_method, instance_methods.
  intros * (?&?) ?.
  eapply In_rec_instance_methods_find_method; eauto.
  intros Hin.
  apply M.find_1 in Hin; discriminate.
Qed.

Lemma In_instance_methods_atom:
  forall f o fid cid p insts mems,
    wt_method p insts mems f ->
    M.MapsTo (o, fid) cid (instance_methods f) ->
    atom fid.
Proof.
  intros * Hwt Hin.
  eapply In_instance_methods_find_method in Hin as (?&?&m&_&Hfind&_); eauto.
  eapply find_method_name in Hfind.
  pose proof (m_good m) as (_&?). congruence.
Qed.

Corollary atom_instance_methods:
  forall f m p c,
    wt_class p c ->
    find_method f c.(c_methods) = Some m ->
    Forall (fun xt => atom (snd (fst xt))) (M.elements (instance_methods m)).
Proof.
  intros * Hwt Hfind.
  inversion_clear Hwt as [_ Hwtm].
  eapply Forall_forall in Hwtm. 2:eapply find_method_In; eauto.
  eapply Forall_forall. intros ((o&fid)&cid) Hin; simpl.
  eapply In_instance_methods_atom; eauto.
  eapply M.elements_2, SetoidList.In_InA; eauto.
  apply eqke_equiv.
Qed.

Lemma In_instance_methods_atom':
  forall f o fid cid p insts mems prefs,
    Forall (AtomOrGensym prefs) (map fst insts) ->
    wt_method p insts mems f ->
    M.MapsTo (o, fid) cid (instance_methods f) ->
    AtomOrGensym prefs o.
Proof.
  intros * Hatom Hwt Hin.
  eapply In_instance_methods_find_method in Hin as (?&?&m&_&_&Hinm); eauto.
  eapply InMembers_In in Hinm as (?&Hin).
  rewrite Forall_map in Hatom.
  eapply Forall_forall in Hin; eauto. eauto.
Qed.

Corollary atom_instance_methods':
  forall f m p c,
    wt_class p c ->
    find_method f c.(c_methods) = Some m ->
    Forall (fun xt => (AtomOrGensym (PSP.of_list gensym_prefs)) (fst (fst xt))) (M.elements (instance_methods m)).
Proof.
  intros * Hwt Hfind.
  inversion_clear Hwt as [_ Hwtm].
  eapply Forall_forall in Hwtm. 2:eapply find_method_In; eauto.
  eapply Forall_forall. intros ((o&fid)&cid) Hin; simpl.
  pose proof (c_good c) as (Good&_).
  eapply In_instance_methods_atom'; [eauto|eauto|].
  eapply M.elements_2, SetoidList.In_InA; eauto.
  apply eqke_equiv.
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
  pose proof (atom_instance_methods _ _ _ _ WT Find) as Atom.
  pose proof (atom_instance_methods' _ _ _ _ WT Find) as Atom'.
  induction (M.elements (elt:=ident) (instance_methods m)) as [|((o, f'), c')];
    simpl; inversion_clear Nodup as [|? ? ? Notin Nodup'];
      inversion_clear Atom; inversion_clear Atom';
        constructor; auto.
  intro Hin; apply Notin.
  rewrite fst_InMembers, map_map, in_map_iff in Hin.
  destruct Hin as (((o', f''), c'') & Eq & Hin); simpl in *.
  apply prefix_out_injective in Eq; auto; destruct Eq; subst.
  eapply In_InMembers; eauto.
Qed.

Lemma NoDup_funs:
  forall prog,
    wt_program prog ->
    NoDup (map fst (concat (map (make_methods (rev_prog prog)) (rev_prog prog).(classes)))).
Proof.
  unfold make_methods.
  intros * Wt; simpl.
  rewrite rev_tr_spec.
  unfold wt_program, CommonTyping.wt_program in Wt; simpl in *.
  induction (classes prog) as [|c]; simpl; auto using NoDup.
  inversion_clear Wt as [|?? []].
  rewrite map_app, concat_app, map_app; simpl.
  rewrite app_nil_r, map_map, Permutation.Permutation_app_comm.
  apply NoDup_app'; auto.
  - simpl.
    pose proof (c_nodupm c) as Nodup.
    induction (c_methods c) as [|m]; simpl;
      inversion_clear Nodup as [|? ? Notin]; constructor; auto.
    rewrite in_map_iff; intros (m' & E & Hin); apply Notin.
    pose proof (c_good c).
    apply prefix_fun_injective in E; try tauto; destruct E as [E ?]; rewrite <-E.
    rewrite in_map_iff; exists m'; auto.
  - induction (c_methods c) as [|m]; simpl; auto.
    constructor; auto.
    rewrite in_map_iff; intros ((y, d) & E & Hin).
    simpl in E; subst.
    apply in_concat in Hin; destruct Hin as (l' & Hin' & Hin).
    apply in_map_iff in Hin' as (c' & E & Hin'); subst l'.
    apply in_map_iff in Hin as (m' & E & Hin).
    unfold translate_method in E; inversion E as [[Eq E']]; clear E E'.
    pose proof (c_good c); pose proof (c_good c').
    apply prefix_fun_injective in Eq; try tauto.
    destruct Eq as [Eq].
    apply in_rev in Hin'.
    eapply Forall_forall in Hin'; eauto.
    congruence.
Qed.

Lemma InMembers_translate_param_idem:
  forall o xs,
    InMembers o (map translate_param xs) = InMembers o xs.
Proof.
  induction xs as [|x xs IH]; auto.
  destruct x. simpl. rewrite IH. reflexivity.
Qed.

Lemma make_out_temps_instance_prefixed:
  forall x prog m,
    InMembers x (make_out_temps (instance_methods_temp prog m)) ->
    exists m c, x = prefix_temp m c.
Proof.
  unfold make_out_temps, instance_methods_temp.
  cut (forall x prog m e,
          (InMembers x (Env.elements e) -> exists m c, x = prefix_temp m c) ->
          InMembers x (Env.elements (rec_instance_methods_temp prog e (m_body m))) ->
          exists m c, x = prefix_temp m c);
    [setoid_rewrite InMembers_translate_param_idem; intros * H * ?;
     eapply H; eauto; rewrite Env.Props.P.elements_empty; simpl; contradiction|].
  intros ???; induction (m_body m) using stmt_ind2'; simpl in *; auto.
  - revert dependent s.
    take (Forall _ _) and induction it as [|[|]]; auto. intros; simpl in *. eapply IHit in H1; eauto.
  - intros * ? Hin; apply InMembers_rec_instance_methods_temp in Hin as [|]; eauto.
    apply (IHs2 (Env.empty _)); auto.
    rewrite Env.Props.P.elements_empty; simpl; contradiction.
  - intros * ? Hin.
    destruct (find_class c prog) as [(cls, ?)|]; simpl in Hin; auto.
    destruct (find_method f (c_methods cls)); simpl in Hin; auto.
    destruct_list ys; simpl in Hin; auto.
    destruct_list (m_out m0) as (?, ?) ? ?; simpl in Hin; try auto.
    rewrite <-Env.In_Members, Env.Props.P.F.add_in_iff in Hin.
    destruct Hin as [|Hin].
    + rewrite <- H0; eauto.
    + rewrite Env.In_Members in Hin.
      eauto.
Qed.

Lemma make_out_temps_extcall_prefixed:
  forall x m,
    InMembers x (make_out_temps (extcalls_temp m)) ->
    exists c, x = prefix temp c.
Proof.
  unfold make_out_temps, extcalls_temp.
  cut (forall x m e,
          (InMembers x (Env.elements e) -> exists c, x = prefix temp c) ->
          InMembers x (Env.elements (rec_extcalls_temp e (m_body m))) ->
          exists c, x = prefix temp c);
    [setoid_rewrite InMembers_translate_param_idem; intros * H *;
     eapply H; eauto; rewrite Env.Props.P.elements_empty; simpl; contradiction|].
  intros ??; induction (m_body m) using stmt_ind2'; simpl in *; auto.
  - revert dependent s.
    take (Forall _ _) and induction it as [|[|]]; auto. intros; simpl in *. eapply IHit in H1; eauto.
  - intros * ? Hin; apply InMembers_rec_extcalls_temp in Hin as [|]; eauto.
    apply (IHs2 (Env.empty _)); auto.
    rewrite Env.Props.P.elements_empty; simpl; contradiction.
  - intros * ? Hin.
    rewrite <-Env.In_Members, Env.Props.P.F.add_in_iff, Env.In_Members in Hin.
    destruct Hin as [|]; subst; eauto.
Qed.

Lemma build_check_size_env_ok:
  forall types gvars gvars_vol defs public main p,
    make_program' types gvars gvars_vol defs public main = OK p ->
    build_composite_env types = OK p.(prog_comp_env)
    /\ check_size_env p.(prog_comp_env) types = OK tt.
Proof.
  unfold make_program'; intros.
  destruct (build_composite_env' types0) as [[gce ?]|?]; try discriminate.
  destruct (check_size_env gce types0) eqn: E; try discriminate.
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

Lemma check_size_env_spec:
  forall ce types,
    check_size_env ce types = OK tt <->
    Forall (fun t => match t with
                       Composite id _ _ _ => check_size_co ce id = OK tt
                     end) types.
Proof.
  intros; unfold check_size_env; rewrite iter_error_ok.
  induction types0 as [|[]]; simpl; split; auto;
    inversion_clear 1; constructor; auto; apply IHtypes0; auto.
Qed.

Lemma make_program_defs:
  forall types gvars gvars_vol defs public main p,
    make_program' types gvars gvars_vol defs public main = OK p ->
    exists gce,
      build_composite_env types = OK gce
      /\ p.(AST.prog_defs) = map (vardef gce false) gvars ++ map (vardef gce true) gvars_vol ++ defs.
Proof.
  unfold make_program'; intros.
  destruct (build_composite_env' types0) as [[gce ?]|?]; try discriminate.
  destruct (check_size_env gce types0) eqn: E; try discriminate.
  destruct u; inv H; simpl; eauto.
Qed.

Lemma type_pres_var:
  forall c m x t,
    Clight.typeof (translate_var c m x t) = translate_type t.
Proof.
  intros; unfold translate_var; cases.
Qed.
Global Hint Resolve type_pres_var : clight.

Lemma type_pres:
  forall c m e p Γm Γv,
    wt_exp p Γm Γv e ->
    Clight.typeof (translate_exp c m e) = translate_type (typeof e).
Proof.
  induction e as [| | |cst| | |]; simpl; auto with clight.
  - inversion_clear 1; destruct tn; auto.
  - destruct cst; simpl; reflexivity.
  - destruct u; auto.
Qed.
Global Hint Resolve type_pres : clight.

Corollary types_pres:
  forall tys c caller es p Γm Γv,
    Forall (wt_exp p Γm Γv) es ->
    Forall2 (fun e ty => typeof e = ty) es tys ->
    map Clight.typeof (map (translate_exp c caller) es) = map translate_type tys.
Proof.
  intros * WT Hes.
  induction Hes; inv WT; simpl; auto.
  f_equal; eauto with clight.
Qed.

Remark types_pres':
  forall f es,
    Forall2 (fun e x => Clight.typeof e = translate_type (snd x)) es f.(m_in) ->
    type_of_params (map translate_param f.(m_in)) =
    list_type_to_typelist (map Clight.typeof es).
Proof.
  intro f.
  induction (m_in f) as [|(x, t)]; intros * Heq;
    inversion_clear Heq as [|? ? ? ? Ht]; simpl; auto.
  f_equal; auto.
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
Global Hint Resolve NoDupMembers_translate_param : clight.

Lemma AtomOrGensym_inv : forall prefs pref x,
    AtomOrGensym (PSP.of_list prefs) (prefix pref x) ->
    In pref prefs.
Proof.
  intros * [?|(?&?&?&?&Heq)].
  - exfalso. eapply prefix_not_atom; eauto.
  - eapply prefix_gensym_injective in Heq; subst.
    rewrite ps_of_list_In in H; auto.
Qed.

Lemma obc2c_not_in_translate_param_in:
  forall f x,
    ~ InMembers (prefix obc2c x) (map translate_param (m_in f)).
Proof.
  intros.
  rewrite InMembers_translate_param_idem.
  intro Hin. eapply InMembers_In in Hin as (?&Hin). eapply m_good_in in Hin.
  apply AtomOrGensym_inv in Hin; eauto with ident.
Qed.
Global Hint Resolve obc2c_not_in_translate_param_in : clight.

Lemma temp_not_in_translate_param_in:
  forall f x,
    ~ InMembers (prefix temp x) (map translate_param (m_in f)).
Proof.
  intros.
  rewrite InMembers_translate_param_idem.
  intro Hin. eapply InMembers_In in Hin as (?&Hin). eapply m_good_in in Hin.
  apply AtomOrGensym_inv in Hin; eauto with ident.
Qed.
Global Hint Resolve temp_not_in_translate_param_in : clight.

Lemma obc2c_not_in_translate_param_vars:
  forall f x,
    ~ InMembers (prefix obc2c x) (map translate_param (m_vars f)).
Proof.
  intros.
  rewrite InMembers_translate_param_idem.
  intro Hin. eapply InMembers_In in Hin as (?&Hin). eapply m_good_vars in Hin.
  apply AtomOrGensym_inv in Hin; eauto with ident.
Qed.
Global Hint Resolve obc2c_not_in_translate_param_vars : clight.

Lemma obc2c_not_in_temps:
  forall prog f x,
    ~ InMembers (prefix obc2c x) (make_out_temps (instance_methods_temp prog f)
                                    ++ make_out_temps (extcalls_temp f)
                                    ++ map translate_param (m_vars f)).
Proof.
  intros; repeat (apply NotInMembers_app; split); auto with clight.
  - intro Hin'. apply make_out_temps_extcall_prefixed in Hin' as (?&Hpre).
    eapply prefix_injective in Hpre as (Eq&_).
    contradict Eq. prove_str_to_pos_neq.
  - intro Hin'. apply make_out_temps_instance_prefixed in Hin' as (?&?&Hpre).
    eapply prefix_injective in Hpre as (Eq&_).
    contradict Eq. prove_str_to_pos_neq.
Qed.
Global Hint Resolve obc2c_not_in_temps : clight.

Lemma c_objs_field_offset:
  forall ge o c cls,
    In (o, c) cls.(c_objs) ->
    exists d, field_offset ge o (make_members cls) = OK d.
Proof.
  intros * Hin.
  unfold field_offset.
  cut (forall ofs, exists d,
            field_offset_rec ge o (make_members cls) ofs = OK d); auto.
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
      field_type x (make_members cls) = OK (translate_type ty).
Proof.
  intros * Hfind ? ? Hin.
  apply in_field_type; auto with clight.
  unfold make_members, translate_param. apply in_app_iff.
  left. rewrite in_map_iff.
  exists (x, ty); split; auto.
Qed.

Lemma field_translate_obj_type:
  forall prog clsnm cls prog',
    find_class clsnm prog = Some (cls, prog') ->
    forall o c,
      In (o, c) cls.(c_objs) ->
      field_type o (make_members cls) = OK (type_of_inst c).
Proof.
  intros * Hfind ? ? Hin.
  apply in_field_type; auto with clight.
  unfold make_members. apply in_app_iff. right.
  apply in_map_iff. exists (o, c); auto.
Qed.

Remark eval_exprlist_app:
  forall tge e le m es es' vs vs',
    eval_exprlist tge e le m es
                  (list_type_to_typelist (map Clight.typeof es)) vs ->
    eval_exprlist tge e le m es'
                  (list_type_to_typelist (map Clight.typeof es')) vs' ->
    eval_exprlist tge e le m (es ++ es')
                  (list_type_to_typelist (map Clight.typeof (es ++ es'))) (vs ++ vs').
Proof.
  induction es; intros * Ev Ev'; inv Ev; auto.
    repeat rewrite <-app_comm_cons.
    simpl; econstructor; eauto.
Qed.

Fact exec_seq_assoc:
  forall ge fe e le m t le' m' out s1 s2 s3,
    exec_stmt ge fe e le m (Ssequence s1 (Ssequence s2 s3)) t le' m' out <->
    exec_stmt ge fe e le m (Ssequence (Ssequence s1 s2) s3) t le' m' out.
Proof.
  split; inversion_clear 1;
    try match goal with H: context [Ssequence _ _] |- _ => inv H end;
    eauto using exec_stmt.
  - rewrite <-Events.Eapp_assoc; eauto using exec_stmt.
  - rewrite Events.Eapp_assoc; eauto using exec_stmt.
  - contradiction.
Qed.

Fact exec_seq_skip_l:
  forall ge fe e le m t le' m' out s,
    exec_stmt ge fe e le m (Ssequence Sskip s) t le' m' out <->
    exec_stmt ge fe e le m s t le' m' out.
Proof.
  split.
  - inversion_clear 1; match goal with H: context [Sskip] |- _ => inv H end; auto.
    contradiction.
  - intros; rewrite <- (Events.E0_left t); eauto using exec_stmt.
Qed.

Fact exec_seq_skip_r:
  forall ge fe e le m t le' m' out s,
    exec_stmt ge fe e le m (Ssequence s Sskip) t le' m' out <->
    exec_stmt ge fe e le m s t le' m' out.
Proof.
  split.
  - inversion_clear 1; try match goal with H: context [Sskip] |- _ => inv H end; auto.
    now rewrite Events.E0_right.
  - intros; destruct out0.
    + apply exec_Sseq_2; auto; discriminate.
    + apply exec_Sseq_2; auto; discriminate.
    + rewrite <- (Events.E0_right t); eauto using exec_stmt.
    + apply exec_Sseq_2; auto; discriminate.
Qed.

Definition ls_hd (ls: labeled_statements) : option (option Z * statement) :=
  match ls with
  | LSnil => None
  | LScons z s _ => Some (z, s)
  end.

Lemma make_labeled_statements_aux_cons:
  forall ls z os ss,
    let (ls', z') := make_labeled_statements_aux ls z ss in
    make_labeled_statements_aux ls z (os :: ss) =
    (or_default_with ls' (fun s => LScons (Some z') (Ssequence s Sbreak) ls') os, Z.pred z').
Proof.
  intros.
  destruct (make_labeled_statements_aux ls z ss) eqn: E.
  simpl; rewrite E; auto.
Qed.

Definition make_labeled_statements_aux' (ls: labeled_statements) (n: nat) (ss: list (option statement)): labeled_statements :=
  fold_right2 (fun i os ls => or_default_with ls (fun s => LScons (Some (Z.of_nat i)) (Ssequence s Sbreak) ls) os)
              ls (seq n (length ss)) ss.

Lemma make_labeled_statements_aux'_cons:
  forall ls n os ss,
    make_labeled_statements_aux' ls n (os :: ss) =
    or_default_with (make_labeled_statements_aux' ls (S n) ss)
                    (fun s => LScons (Some (Z.of_nat n)) (Ssequence s Sbreak) (make_labeled_statements_aux' ls (S n) ss))
                    os.
Proof. reflexivity. Qed.

Lemma make_labeled_statements_aux_spec:
  forall ss ls n,
    make_labeled_statements_aux ls (Z.pred (Z.of_nat (n + length ss))) ss =
    (make_labeled_statements_aux' ls n ss, Z.pred (Z.of_nat n)).
Proof.
  unfold make_labeled_statements_aux', make_labeled_statements_aux.
  induction ss as [|os]; intros; simpl; auto.
  - now rewrite <-plus_n_O.
  - rewrite Nat.add_succ_r, <-Nat.add_succ_l, IHss.
    replace (Z.pred (Z.of_nat (S n))) with (Z.of_nat n); auto.
    lia.
Qed.

Corollary fst_make_labeled_statements_aux_spec:
  forall ss ls,
    fst (make_labeled_statements_aux ls (Z.pred (Z.of_nat (length ss))) ss) =
    make_labeled_statements_aux' ls 0 ss.
Proof.
  intros; rewrite <-(plus_O_n (length ss)), make_labeled_statements_aux_spec; auto.
Qed.

Lemma select_switch_case_make_labeled_statements_aux'_Lt:
  forall ss m n ls,
    (n < m)%nat ->
    (forall m, (n <= m)%nat -> select_switch_case (Z.of_nat m) ls = None) ->
    select_switch_case (Z.of_nat n) (make_labeled_statements_aux' ls m ss) = None.
Proof.
  induction ss as [|os]; intros * Lt Hls; auto.
  rewrite make_labeled_statements_aux'_cons.
  destruct os; simpl; eauto.
  rewrite zeq_false; try lia; eauto.
Qed.

Lemma select_switch_case_make_labeled_statements_aux'_None:
  forall ss m n ls,
    nth_error ss n = Some None ->
    (forall n, (m <= n)%nat -> select_switch_case (Z.of_nat n) ls = None) ->
    select_switch_case (Z.of_nat (m + n)) (make_labeled_statements_aux' ls m ss) = None.
Proof.
  induction ss as [|os]; intros * Nth Hls.
  - rewrite nth_error_nil in Nth; discriminate.
  - rewrite make_labeled_statements_aux'_cons; simpl.
    destruct n; simpl in *.
    + inv Nth; simpl.
      apply select_switch_case_make_labeled_statements_aux'_Lt; try lia.
      intros; apply Hls; lia.
    + destruct os; simpl; rewrite Nat.add_succ_r, <-Nat.add_succ_l.
      * rewrite zeq_false; try lia.
        apply IHss; auto.
        intros; apply Hls; lia.
      * apply IHss; auto.
        intros; apply Hls; lia.
Qed.

Lemma select_switch_case_make_labeled_statements_aux'_Some:
  forall ss m n ls s,
    nth_error ss n = Some (Some s) ->
    exists ls',
      select_switch_case (Z.of_nat (m + n)) (make_labeled_statements_aux' ls m ss) =
      Some (LScons (Some (Z.of_nat (m + n))) (Ssequence s Sbreak) ls').
Proof.
  induction ss as [|os]; intros * Nth.
  - rewrite nth_error_nil in Nth; discriminate.
  - rewrite make_labeled_statements_aux'_cons; simpl.
    destruct n; simpl in *.
    + inv Nth; simpl.
      rewrite <-plus_n_O, zeq_true; eauto.
    + destruct os; simpl; rewrite Nat.add_succ_r, <-Nat.add_succ_l; auto.
      rewrite zeq_false; try lia; auto.
Qed.

Lemma select_switch_default_make_labeled_statements_aux':
  forall ss ls n,
    select_switch_default ls = ls ->
    select_switch_default (make_labeled_statements_aux' ls n ss) = ls.
Proof.
  induction ss as [|os]; intros; auto.
  rewrite make_labeled_statements_aux'_cons.
  destruct os; simpl; auto.
Qed.

Lemma select_switch_make_labeled_statements_aux'_spec:
  forall ss m n ls os,
    nth_error ss n = Some os ->
    (forall n, (m <= n)%nat -> select_switch_case (Z.of_nat n) ls = None) ->
    select_switch_default ls = ls ->
    let ls' := select_switch (Z.of_nat (m + n)) (make_labeled_statements_aux' ls m ss) in
    or_default_with (ls' = ls)
                    (fun s => exists ls'', ls' = LScons (Some (Z.of_nat (m + n))) (Ssequence s Sbreak) ls'')
                    os.
Proof.
  intros.
  destruct os; simpl; subst ls'; unfold select_switch.
  - edestruct select_switch_case_make_labeled_statements_aux'_Some as [? ->]; eauto.
  - rewrite select_switch_case_make_labeled_statements_aux'_None; auto.
    apply select_switch_default_make_labeled_statements_aux'; auto.
Qed.

Lemma select_branch:
  forall branches default n os,
    nth_error branches n = Some os ->
    let ls := seq_of_labeled_statement
                (select_switch (Z.of_nat n) (make_labeled_statements branches default))
    in
    or_default_with (ls = Ssequence default Sskip)
                    (fun s => exists s', ls = Ssequence (Ssequence s Sbreak) s')
                    os.
Proof.
  intros * Nth.
  unfold make_labeled_statements.
  rewrite Nat2Z.inj_pred.
  - rewrite fst_make_labeled_statements_aux_spec.
    pose proof Nth as Hin.
    eapply (select_switch_make_labeled_statements_aux'_spec _ 0) in Nth; simpl in *.
    + destruct os; simpl in *.
      * destruct Nth as [? ->]; simpl; eauto.
      * rewrite Nth; simpl; auto.
    + cases.
    + cases.
  - destruct branches; simpl in *; try lia.
    rewrite nth_error_nil in Nth; discriminate.
Qed.

Corollary select_branch_Some:
  forall branches default n s,
    nth_error branches n = Some (Some s) ->
    exists s',
      seq_of_labeled_statement
        (select_switch (Z.of_nat n) (make_labeled_statements branches default))
      = Ssequence (Ssequence s Sbreak) s'.
Proof.
  intros * Nth; eapply select_branch in Nth; simpl in Nth; eauto.
Qed.

Lemma select_branch_None:
  forall branches default n,
    nth_error branches n = Some None ->
    seq_of_labeled_statement
      (select_switch (Z.of_nat n) (make_labeled_statements branches default))
    = Ssequence default Sskip.
Proof.
  intros * Nth; eapply select_branch in Nth; eauto.
Qed.

Lemma funcall_assign_spec:
  forall ge fe e le m t le' m' out owner caller xs o tyo outs,
    exec_stmt ge fe e le m
              (funcall_assign owner caller xs o tyo outs)
              t le' m' out
    <->
    exec_stmt ge fe e le m
              (fold_right2
                 (fun y '(y', ty) s =>
                    let ty := translate_type ty in
                    let assign_out := assign owner caller y ty (Efield (Evar o tyo) y' ty) in
                    Ssequence assign_out s)
                 Sskip xs outs)
              t le' m' out.
Proof.
  unfold funcall_assign; intros.
  cut (forall s,
          exec_stmt ge fe e le m
                    (fold_left2
                       (fun s y '(y', ty) =>
                          Ssequence s (assign owner caller y (translate_type ty) (Efield (Evar o tyo) y' (translate_type ty))))
                       xs outs s)
                    t le' m' out0 <->
          exec_stmt ge fe e le m
                    (Ssequence s (fold_right2
                                    (fun y '(y', ty) s =>
                                       Ssequence (assign owner caller y (translate_type ty) (Efield (Evar o tyo) y' (translate_type ty))) s)
                                    Sskip xs outs))
                    t le' m' out0).
  { intros ->; now rewrite exec_seq_skip_l. }
  revert xs.
  induction outs as [|[]], xs; simpl; intros; try (rewrite exec_seq_skip_r; reflexivity).
  rewrite IHouts, exec_seq_assoc; reflexivity.
Qed.

Lemma load_in_spec:
  forall ge fe e le m t le' m' out ins,
    exec_stmt ge fe e le m (load_in ins) t le' m' out <->
    exec_stmt ge fe e le m
              (fold_right
                 (fun '(x, t) s =>
                    let typtr := Tpointer (translate_type t) noattr in
                    let load := Sbuiltin (Some x) (AST.EF_vload (type_to_chunk t))
                                         (Tcons typtr Tnil)
                                         [Eaddrof (Evar (prefix_glob x) (translate_type t)) typtr]
                    in Ssequence load s)
                 Sskip ins)
              t le' m' out.
Proof.
  unfold load_in; intros.
  cut (forall s,
          exec_stmt ge fe e le m
                    (fold_left
                       (fun s '(x, t0) =>
                          Ssequence
                            s
                            (Sbuiltin (Some x) (AST.EF_vload (type_to_chunk t0))
                                      (Tcons (Tpointer (translate_type t0) noattr) Tnil)
                                      [Eaddrof (Evar (prefix_glob x) (translate_type t0))
                                               (Tpointer (translate_type t0) noattr)]))
                       ins s)
                    t le' m' out0 <->
          exec_stmt ge fe e le m
                    (Ssequence s (fold_right
                                    (fun '(x, t0) s =>
                                       Ssequence
                                         (Sbuiltin (Some x) (AST.EF_vload (type_to_chunk t0))
                                                   (Tcons (Tpointer (translate_type t0) noattr) Tnil)
                                                   [Eaddrof (Evar (prefix_glob x) (translate_type t0))
                                                            (Tpointer (translate_type t0) noattr)]) s)
                                    Sskip ins))
                    t le' m' out0).
  { intros ->; now rewrite exec_seq_skip_l. }
  induction ins as [|[]]; simpl; intros; try (rewrite exec_seq_skip_r; reflexivity).
  rewrite IHins, exec_seq_assoc; reflexivity.
Qed.

Lemma write_multiple_outs_spec:
  forall ge fe e le m t le' m' out node outs,
    exec_stmt ge fe e le m (write_multiple_outs node outs) t le' m' out <->
    exec_stmt ge fe e le m
              (let out_struct := prefix Ids.out step in
               let t_struct := type_of_inst (prefix_fun step node) in
               fold_right
                 (fun '(x, t) s =>
                    let typtr := Tpointer (translate_type t) noattr in
                    let write := Sbuiltin None (AST.EF_vstore (type_to_chunk t))
                                          (Tcons typtr (Tcons (translate_type t) Tnil))
                                          [Eaddrof (Evar (prefix_glob x) (translate_type t)) typtr;
                                          Efield (Evar out_struct t_struct) x (translate_type t)]
                    in Ssequence write s)
                 Sskip outs)
              t le' m' out.
Proof.
  unfold write_multiple_outs; intros.
  cut (forall s,
          exec_stmt ge fe e le m
                    (fold_left
                       (fun s '(x, t0) =>
                          Ssequence
                            s
                            (Sbuiltin None (AST.EF_vstore (type_to_chunk t0))
                                      (Tcons (Tpointer (translate_type t0) noattr)
                                             (Tcons (translate_type t0) Tnil))
                                      [Eaddrof (Evar (prefix_glob x) (translate_type t0))
                                               (Tpointer (translate_type t0) noattr);
                                       Efield (Evar (prefix out step)
                                                    (type_of_inst (prefix_fun step node)))
                                              x (translate_type t0)]))
                       outs s)
                    t le' m' out0 <->
          exec_stmt ge fe e le m
                    (Ssequence s (fold_right
                                    (fun '(x, t0) s =>
                                       Ssequence
                                         (Sbuiltin None (AST.EF_vstore (type_to_chunk t0))
                                                   (Tcons (Tpointer (translate_type t0) noattr)
                                                          (Tcons (translate_type t0) Tnil))
                                                   [Eaddrof (Evar (prefix_glob x) (translate_type t0))
                                                            (Tpointer (translate_type t0) noattr);
                                                    Efield (Evar (prefix out step)
                                                                 (type_of_inst (prefix_fun step node)))
                                                           x (translate_type t0)]) s)
                                    Sskip outs))
                    t le' m' out0).
  { intros ->; now rewrite exec_seq_skip_l. }
  induction outs as [|[]]; simpl; intros; try (rewrite exec_seq_skip_r; reflexivity).
  rewrite IHouts, exec_seq_assoc; reflexivity.
Qed.

Definition wf_struct (ge: composite_env) '((x, t): ident * Ctypes.type) : Prop :=
  exists id co,
    t = Tstruct id noattr
    /\ ge ! id = Some co
    /\ co_su co = Struct
    /\ (exists flds, co_members co = mk_members flds)
    /\ NoDup (map name_member (co_members co))
    /\ forall x' t', In (Member_plain x' t') (co_members co) ->
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
                                (fun _ => [(prefix obc2c out, type_of_inst_p (prefix_fun f.(m_name) c.(c_name)))]) in
    let f_return := case_out f
                             Tvoid
                             (fun _ t => translate_type t)
                             (fun _ => Tvoid) in
    let f_temp_out := case_out f
                               []
                               (fun x t => [translate_param (x, t)])
                               (fun _ => []) in
    let f_body := return_with (translate_stmt (rev_prog prog) c f f.(m_body))
                              (case_out f
                                        None
                                        (fun x t => Some (make_in_arg (x, t)))
                                        (fun _ => None)) in
    fd.(fn_params) = (prefix obc2c self, type_of_inst_p c.(c_name))
                       :: f_out_param
                       ++ map translate_param f.(m_in)
    /\ fd.(fn_return) = f_return
    /\ fd.(fn_callconv) = AST.cc_default
    /\ fd.(fn_vars) = make_out_vars (instance_methods f)
    /\ fd.(fn_temps) = f_temp_out
                        ++ make_out_temps (instance_methods_temp (rev_prog prog) f)
                        ++ make_out_temps (extcalls_temp f)
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
    instance_methods_temp (rev_prog prog') f = instance_methods_temp (rev_prog prog) f.
  Proof.
    assert (wt_method prog'' c.(c_objs) c.(c_mems) f) as WT.
    { eapply wt_class_find_method; eauto.
      eapply wt_program_find_unit; eauto.
      eapply wt_program_find_unit_chained; eauto.
    }
    unfold instance_methods_temp.
    destruct WT as (WT &?).
    generalize (Env.empty type) as e.
    induction f.(m_body) using stmt_ind2';
      inversion_clear WT as [| | | |????????? Findcl' Findmth'| |]; simpl; auto.
    - revert dependent s.
      take (length _ = _) and clear it; induction ss as [|[|] ? IH]; simpl in *; intros; auto;
        take (Forall _ (_ :: _)) and inv it; eauto.
      rewrite IH, IHs; eauto.
    - setoid_rewrite IHs1; auto.
    - assert (wt_program prog') by (eapply wt_program_find_unit; eauto).
      assert (wt_program prog'') by (eapply wt_program_find_unit; eauto).
      assert (find_class c0 prog' = Some (cls, p')) as Find1 by (eapply wt_program_find_unit_chained; eauto).
      assert (find_class c0 prog = Some (cls, p')) as Find2 by (eapply wt_program_find_unit_chained; eauto).
      apply find_class_rev in Find1 as (?& ->); eauto.
      apply find_class_rev in Find2 as (?& ->); eauto.
  Qed.

  Lemma translate_stmt_find_class:
    translate_stmt (rev_prog prog') c f (m_body f) = translate_stmt (rev_prog prog) c f (m_body f).
  Proof.
     assert (wt_method prog'' c.(c_objs) c.(c_mems) f) as WT.
    { eapply wt_class_find_method; eauto.
      eapply wt_program_find_unit; eauto.
      eapply wt_program_find_unit_chained; eauto.
    }
    destruct WT as (WT &?).
    induction (m_body f) using stmt_ind2';
      inversion_clear WT as [| | | |????????? Findcl' Findmth'| |]; simpl; auto.
    - unfold make_labeled_statements.
      rewrite IHs; auto.
      assert (map (Datatypes.option_map (translate_stmt (rev_prog prog') c f)) ss =
              map (Datatypes.option_map (translate_stmt (rev_prog prog) c f)) ss) as ->; auto.
      take (length _ = _) and clear it; induction ss as [|[|] ? IH]; auto; simpl in *;
        take (Forall _ (_ :: _)) and inv it; f_equal; auto.
      f_equal; auto.
    - now rewrite IHs1, IHs2.
    - assert (wt_program prog') by (eapply wt_program_find_unit; eauto).
      unfold binded_funcall.
      assert (find_class c0 prog' = Some (cls, p')) as Find1 by (eapply wt_program_find_unit_chained; eauto).
      assert (find_class c0 prog = Some (cls, p')) as Find2 by (eapply wt_program_find_unit_chained; eauto).
      apply find_class_rev in Find1 as (?& ->); eauto.
      apply find_class_rev in Find2 as (?& ->); eauto.
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

Fact bind_inversion : forall {A B} (f : res A) (g : A -> res B) (y : B),
    (do X <- f; g X) = OK y ->
    { x : A | f = OK x /\ g x = OK y }.
Proof.
  intros * Hbind.
  destruct f; simpl in *; try congruence. eauto.
Qed.

Ltac inv_trans_tac H Eexterns En Estep Ereset Eenums structs funs E :=
  match type of H with
    translate _ _ (Some ?f) ?p = OK _ =>
    let c := fresh "c" in
    let p' := fresh p in
    unfold translate in H;
    apply bind_inversion in H as ([] & Eexterns & H);
    apply bind_inversion in H as ([] & Etypes & H);
    destruct (split (map (translate_class (rev_prog p)) (rev_prog p).(classes))) as (structs, funs) eqn: E;
    destruct (find_class f p) as [(c, p')|] eqn: En; try discriminate;
    destruct (find_method step c.(c_methods)) eqn: Estep; try discriminate;
    destruct (find_method reset c.(c_methods)) eqn: Ereset; try discriminate;
    destruct (check_size_enums p) as [[]|] eqn: Eenums; simpl in *; try discriminate;
    rewrite <-app_assoc in H
  end.

Tactic Notation "inv_trans" ident(H) "as" ident(Eexterns) ident(En) ident(Estep) ident(Ereset) ident(Eenums) "with" ident(s) ident(f) ident(E) :=
  inv_trans_tac H Eexterns En Estep Ereset Eenums s f E.
Tactic Notation "inv_trans" ident(H) "as" ident(Eexterns) ident(En) ident(Estep) ident(Ereset) ident(Eenums) "with" ident(s) ident(f) :=
  inv_trans H as Eexterns En Estep Ereset Eenums with s f E.
Tactic Notation "inv_trans" ident(H) "as" ident(Eexterns) ident(En) ident(Estep) ident(Ereset) ident(Eenums) :=
  inv_trans H as Eexterns En Estep Ereset Eenums with s f.
Tactic Notation "inv_trans" ident(H) "with" ident(s) ident(f) ident(E) :=
  inv_trans H as Eexterns En Estep Ereset Eenums with s f E.
Tactic Notation "inv_trans" ident(H) "with" ident(s) ident(f) :=
  inv_trans H as Eexterns En Estep Ereset Eenums with s f E.
Tactic Notation "inv_trans" ident(H) :=
  inv_trans H as Eexterns En Estep Ereset Enums.

Section check_externs.

  Lemma check_externs_atom : forall prog,
      check_externs prog = OK tt ->
      Forall atom (map fst prog.(externs)).
  Proof.
    unfold check_externs.
    intros * Hc; monadInv Hc.
    repeat cases_eqn Hf; repeat take (_ = OK _) and inv it.
    take (forallb is_atom _ = _) and apply forallb_Forall in it.
    simpl_Forall. now apply is_atom_spec.
  Qed.

  Lemma check_externs_NoDup : forall prog,
      check_externs prog = OK tt ->
      NoDupMembers prog.(externs).
  Proof.
    unfold check_externs.
    intros * Hc; monadInv Hc.
    repeat cases_eqn Hf; repeat take (_ = OK _) and inv it.
    take (check_nodup _ = _) and (apply check_nodup_correct, fst_NoDupMembers in it); auto.
  Qed.

  Lemma check_externs_reserved : forall prog id,
      check_externs prog = OK tt ->
      In id (map fst prog.(externs)) ->
      id <> sync_id /\ id <> main_sync_id /\ id <> main_proved_id /\ id <> main_id.
  Proof.
    unfold check_externs.
    intros * Hc Hin; monadInv Hc; simpl_In.
    repeat cases_eqn Hf; repeat take (_ = OK _) and inv it.
    repeat (take (_ || _ = false) and apply orb_false_iff in it as (?&?)).
    repeat (take (mem_assoc_ident _ _ = _) and eapply mem_assoc_ident_false with (t:=(l, c)) in it).
    repeat split; intro contra; subst; eauto.
  Qed.

End check_externs.

Opaque check_externs.

Section TranslateOk.

  Variable main_node : ident.

  Variable prog: program.
  Variable tprog: Clight.program.
  Variable do_sync: bool.
  Variable all_public: bool.

  Let tge := globalenv tprog.
  Let gcenv := genv_cenv tge.

  Hypothesis TRANSL: translate do_sync all_public (Some main_node) prog = OK tprog.

  Lemma check_size_enums_spec:
    Forall (fun tn => check_size_enum tn = OK tt) prog.(types).
  Proof.
    inv_trans TRANSL.
    apply iter_error_ok; auto.
  Qed.

  Lemma externs_In : forall f tyin tyout,
      In (f, (tyin, tyout)) (externs prog) ->
      In (f, AST.Gfun
               (External (AST.EF_external
                            (pos_to_str f)
                            {| AST.sig_args := map typ_of_type (map cltype tyin); AST.sig_res := rettype_of_type (cltype tyout); AST.sig_cc := AST.cc_default |})
                  (list_type_to_typelist (map cltype tyin))
                  (cltype tyout) AST.cc_default)) (AST.prog_defs tprog).
  Proof.
    intros * Hin.
    inv_trans TRANSL with s f' E. unfold make_program' in *.
    destruct (build_composite_env' _) as [(?&?)|]; try congruence.
    monadInv TRANSL; simpl.
    repeat rewrite in_app_iff. right. right. left.
    solve_In.
  Qed.

  Hypothesis WT: wt_program prog.

  Lemma find_self:
    exists sb, Genv.find_symbol tge (prefix_glob (prefix self main_id)) = Some sb.
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
    rewrite 5 map_app, <-app_assoc, <-NoDup_norepet.
    repeat rewrite glob_bind_vardef_fst; simpl.
    assert ( ~ In (prefix_glob (prefix self main_id))
               (map (fun xt => prefix_glob (fst xt)) (m_out m) ++
                map (fun xt => prefix_glob (fst xt)) (m_in m) ++
                map fst (map (fun '(f, (tyin, tyout)) => translate_external f tyin tyout) (externs prog)) ++
                map fst (concat funs) ++
                map fst
                ((if do_sync
                  then [(sync_id, make_sync); (main_sync_id, make_main true main_node m)]
                  else [])
                   ++ [(main_proved_id, make_main false main_node m);
                       (main_id, make_entry_point do_sync)]))) as Notin_self.
    { repeat rewrite in_app_iff, in_map_iff; simpl;
        intros [((x, t) & E & Hin)
               |[((x, t) & E & Hin)
               |[((x, t) & E & Hin)
                |[((x, t) & E & Hin)
                 |Hin]]]];
        try simpl in E.
      - apply prefix_glob_injective in E; auto; subst.
        apply m_good_out, AtomOrGensym_inv in Hin; auto with ident.
      - apply prefix_glob_injective in E; auto; subst.
        apply m_good_in, AtomOrGensym_inv in Hin; auto with ident.
      - subst; simpl_In.
        apply check_externs_atom in Eexterns. simpl_Forall.
        eapply prefix_not_atom, Eexterns.
      - subst x.
        apply in_map with (f:=fst) in Hin.
        subst funs. apply prefixed_funs in Hin as (?&?&Hpre).
        unfold prefix_glob.
        apply prefix_injective in Hpre as (?&?); auto with ident.
      - destruct do_sync; simpl in Hin.
        + destruct Hin as [Hin|[Hin|[Hin|[Hin|]]]]; contr.
          * eapply sync_not_glob; eauto.
          * eapply main_sync_not_glob; eauto.
          * eapply main_proved_not_glob; eauto.
          * eapply main_not_glob; eauto.
        + destruct Hin as [Hin|[Hin|]]; contr.
          * eapply main_proved_not_glob; eauto.
          * eapply main_not_glob; eauto.
    }
    assert (NoDup (map (fun xt => prefix_glob (fst xt)) (m_out m) ++
                   map (fun xt => prefix_glob (fst xt)) (m_in m) ++
                   map fst (map (fun '(f, (tyin, tyout)) => translate_external f tyin tyout) (externs prog)) ++
                   map fst (concat funs) ++
                   map fst
                   ((if do_sync
                     then [(sync_id, make_sync); (main_sync_id, make_main true main_node m)]
                     else [])
                      ++ [(main_proved_id, make_main false main_node m);
                          (main_id, make_entry_point do_sync)]))) as Nodup.
    { assert (Forall (fun x => AtomOrGensym (PSP.of_list gensym_prefs) (fst x)) (m_out m)) as Atom_out
        by (rewrite Forall_forall; intros (x, t) ?; apply (m_good_out m (x, t)); auto).
      assert (Forall (fun x => AtomOrGensym (PSP.of_list gensym_prefs) (fst x)) (m_in m)) as Atom_in
        by (rewrite Forall_forall; intros (x, t) ?; apply (m_good_in m (x, t)); auto).
      assert (NoDup (map (fun xt => prefix_glob (fst xt)) (m_out m))) as Hm_out.
      { apply NoDup_prefix_glob; auto. apply m_nodupout. }
      assert (NoDup (map (fun xt => prefix_glob (fst xt)) (m_in m))) as Hm_in.
      { apply NoDup_prefix_glob; auto. apply m_nodupin. }
      assert (NoDup (map fst (concat funs))) by (rewrite Funs; now apply NoDup_funs).
      assert (Forall (fun z  => ~ In z (map fst (concat funs)))
                     (map (fun xt => prefix_glob (fst xt)) (m_in m))) as Hin_not_funs.
      { apply glob_not_in_prefixed; auto.
        apply Forall_forall; intros * Hin; subst.
        now apply prefixed_funs in Hin; auto. }
      assert (Forall (fun z => ~ In z (map fst (concat funs)))
                     (map (fun xt => prefix_glob (fst xt)) (m_out m))) as Hout_not_funs.
      { apply glob_not_in_prefixed; auto.
        apply Forall_forall; intros * Hin; subst.
        now apply prefixed_funs in Hin. }
      assert (Forall (fun z => ~ In z (map (fun xt => prefix_glob (fst xt)) (m_in m)))
                     (map (fun xt => prefix_glob (fst xt)) (m_out m))) as Hout_not_in.
      { apply NoDupMembers_glob.
        pose proof (m_nodupvars m) as Nodup.
        rewrite Permutation.Permutation_app_comm, <-app_assoc in Nodup.
        now apply NoDupMembers_app_r in Nodup; rewrite Permutation.Permutation_app_comm in Nodup.
      }
      apply check_externs_atom in Eexterns as Hatoms.
      destruct do_sync; simpl;
        repeat match goal with |- context [?x :: _ :: _] => rewrite (cons_is_app x) end;
        repeat apply NoDup_app'; repeat apply Forall_not_In_app;
          repeat apply Forall_not_In_singleton; auto; try now repeat constructor; auto.
      all:try (rewrite In_singleton; prove_str_to_pos_neq).
      all:try (apply fst_NoDupMembers, NoDupMembers_map; auto using check_externs_NoDup;
               intros; destruct_conjs; auto).
      all:simpl_Forall.
      all:try (intro contra; subst;
               simpl_In; try (take (In _ (concat _)) and apply in_concat in it as (?&?&?)); simpl_In;
               unfold prefix_glob, prefix_fun in *; simpl_Forall).
      all:try (solve [eapply sync_not_glob; eauto]
               || solve [eapply main_sync_not_glob; eauto]
               || solve [eapply main_proved_not_glob; eauto]
               || solve [eapply main_not_glob; eauto]
               || solve [eapply prefix_not_atom; eauto]
               || solve [eapply prefix_not_atom; take (prefix _ _ = _) and rewrite it; eauto with ident]
               || idtac).
      all:eapply check_externs_reserved in Eexterns as (?&?&?&?); [|solve_In]; simpl in *; congruence.
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
        /\ NoDup (map name_member (co_members co))
        /\ co.(co_sizeof) <= Ptrofs.max_unsigned.
    Proof.
      inv_trans TRANSL with structs funs E.
      edestruct find_unit_In as [? Hin]; eauto; subst.
      apply build_check_size_env_ok in TRANSL as [? SIZE].
      assert (In (Composite (c_name owner) Struct (make_members owner) noattr) (concat structs)).
      { unfold translate_class in E.
        apply split_map in E as [Structs].
        unfold make_struct in Structs.
        apply in_rev in Hin.
        apply in_map with (f:=fun c => Composite (c_name c) Struct (make_members c) noattr :: make_out c)
          in Hin.
        rewrite <-rev_tr_spec in Hin.
        apply in_concat' with (Composite (c_name owner) Struct (make_members owner) noattr :: make_out owner).
        - apply in_eq.
        - now rewrite Structs.
      }
      edestruct build_composite_env_charact as (co & Hco & Hmembers & Hattr & ?); eauto.
      exists co; repeat split; auto.
      - rewrite Hattr; auto.
      - rewrite Hmembers. apply NoDupMembers_make_members'.
      - eapply check_size_env_spec, Forall_forall in SIZE; eauto; simpl in SIZE.
        unfold check_size_co in SIZE; rewrite Hco in SIZE.
        cases_eqn Le.
        rewrite Zle_is_le_bool; auto.
    Qed.

    Section MethodProperties.
      Variables (callerid: ident) (caller: method).
      Hypothesis Findmth: find_method callerid owner.(c_methods) = Some caller.

      Section OutStruct.
        Hypothesis Length: (1 < length caller.(m_out))%nat.

        Lemma global_out_struct:
          exists co,
            gcenv ! (prefix_fun callerid ownerid) = Some co
            /\ co.(co_su) = Struct
            /\ co.(co_members) = mk_members (map translate_param caller.(m_out))
            /\ co.(co_attr) = noattr
            /\ NoDup (map name_member (co_members co))
            /\ co.(co_sizeof) <= Ptrofs.max_unsigned.
        Proof.
          inv_trans TRANSL with structs funs E.
          apply build_check_size_env_ok in TRANSL; destruct TRANSL as [? SIZE].
          assert (In (Composite
                        (prefix_fun callerid ownerid)
                        Struct
                        (mk_members (map translate_param caller.(m_out)))
                        noattr) (concat structs)).
          { unfold translate_class in E.
            apply split_map in E.
            destruct E as [Structs].
            unfold make_out in Structs.
            edestruct find_unit_In as [Eq Hin]; eauto.
            apply in_rev in Hin.
            apply in_map with (f:=fun c => make_struct c :: filter_out (map (translate_out c) (c_methods c)))
              in Hin.
            rewrite <-rev_tr_spec in Hin.
            pose proof Findmth.
            apply find_method_In in Findmth.
            assert (In (translate_out owner caller) (filter_out (map (translate_out owner) (c_methods owner))))
              as Hin'.
            { unfold filter_out.
              rewrite filter_In; split.
              - apply in_map; auto.
              - unfold translate_out.
                destruct_list caller.(m_out); simpl; auto; try contradict Length; simpl.
                1,2:lia.
            }
            unfold translate_out at 1 in Hin'; setoid_rewrite Eq in Hin';
              erewrite find_method_name in Hin'; eauto.
            eapply in_concat_cons; eauto.
            rewrite Structs; eauto.
          }
          edestruct build_composite_env_charact as (co & Hco & Hmembers & ? & ?); eauto.
          exists co; repeat (split; auto).
          - rewrite Hmembers. rewrite mk_members_names, translate_param_fst, <-fst_NoDupMembers.
            apply (m_nodupout caller).
          - eapply check_size_env_spec, Forall_forall in SIZE; eauto; simpl in SIZE.
            unfold check_size_co in SIZE; rewrite Hco in SIZE.
            cases_eqn Le.
            rewrite Zle_is_le_bool; auto.
        Qed.

        Remark output_match:
          forall outco,
            gcenv ! (prefix_fun callerid ownerid) = Some outco ->
            mk_members (map translate_param caller.(m_out)) = outco.(co_members).
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
        edestruct find_unit_In as [Eq]; eauto.
        pose proof (find_method_name _ _ _ Findmth) as Eq'.
        edestruct wt_program_find_unit as [WT']; eauto.
        eapply wt_class_find_method in WT'; eauto.
        unfold instance_methods in Hin.
        destruct WT' as (WT' &?).
        pose proof (c_nodupobjs owner).
        induction (m_body caller) using stmt_ind2'; simpl in *;
          try (apply M.find_1 in Hin; discriminate); inv WT'.
        - rewrite In_fold_left_rec_instance_methods in Hin; eauto.
          destruct Hin as [|(?& Hin &?)]; auto.
          pose proof Hin.
          eapply Forall_forall in Hin; eauto; simpl in Hin; eauto.
        - rewrite In_rec_instance_methods in Hin; eauto. destruct Hin.
          + apply IHs2; auto.
          + apply IHs1; auto.
        - destruct_list ys.
          + apply M.find_1 in Hin; contr.
          + apply M.find_1 in Hin; contr.
          + apply F.add_mapsto_iff in Hin as [[[]]|[? Maps]]; simpl in *; subst.
            * exists cls, p', fm; repeat split; auto.
              -- apply find_unit_suffix in Findcl.
                 eapply find_unit_suffix_same; eauto.
              -- repeat (take (Forall2 _ (_ :: _) _) and inv it); simpl; lia.
            * rewrite F.empty_mapsto_iff in Maps; contradiction.
      Qed.

      Lemma methods_corres:
        exists loc_f f,
          Genv.find_symbol tge (prefix_fun callerid ownerid) = Some loc_f
          /\ Genv.find_funct_ptr tge loc_f = Some (Internal f)
          /\ method_spec owner caller prog f.
      Proof.
        unfold method_spec.
        pose proof prog_defs_norepet as Norepet.
        inv_trans TRANSL with structs funs E.
        edestruct find_unit_In as [? Hin]; eauto;
          pose proof (find_method_name _ _ _ Findmth); subst.
       assert ((AST.prog_defmap tprog) ! (prefix_fun caller.(m_name) owner.(c_name)) =
                Some (snd (translate_method (rev_prog prog) owner caller))) as Hget.
        { unfold translate_class in E.
          apply split_map in E.
          destruct E as [? Funs].
          unfold make_methods in Funs.
          apply in_rev, in_map with (f:=fun c => map (translate_method (rev_prog prog) c) (c_methods c))
            in Hin.
          apply find_method_In in Findmth.
          apply in_map with (f:=translate_method (rev_prog prog) owner) in Findmth.
          eapply in_concat' in Findmth; eauto.
          simpl in Funs; rewrite rev_tr_spec in Funs.
          setoid_rewrite <-Funs in Findmth.
          unfold make_program' in TRANSL.
          destruct (build_composite_env' (concat structs)) as [(ce, P)|]; contr.
          destruct (check_size_env ce (concat structs)); contr.
          unfold AST.prog_defmap; simpl.
          apply PTree_Properties.of_list_norepet; auto.
          inversion_clear TRANSL.
          apply in_cons. rewrite 3 in_app_iff. right; right; left.
          unfold translate_method in Findmth; auto.
        }
        apply Genv.find_def_symbol in Hget.
        destruct Hget as (loc_f & Findsym & Finddef).
        simpl in Finddef.
        unfold fundef in Finddef.
        assert (list_norepet (var_names ((prefix obc2c self, type_of_inst_p owner.(c_name))
                                           :: (prefix obc2c out, type_of_inst_p (prefix_fun caller.(m_name) owner.(c_name)))
                                           :: (map translate_param caller.(m_in))
               ))) as H1.
        { unfold var_names.
          rewrite <-NoDup_norepet, <-fst_NoDupMembers.
          repeat constructor; auto with clight.
          - intro Hin'; simpl in Hin'; destruct Hin' as [Eq|Hin'].
            + eapply prefix_injective in Eq as (_&Eq).
              contradict Eq. prove_str_to_pos_neq.
            + pose proof (m_good_in caller) as Good.
              rewrite InMembers_translate_param_idem in Hin'.
              apply InMembers_In in Hin' as (?&Hin').
              apply Good, AtomOrGensym_inv in Hin'; auto with ident.
        }
        assert (list_norepet (var_names ((prefix obc2c self, type_of_inst_p owner.(c_name))
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
          eapply wt_program_find_unit; eauto.
        }
        assert (NoDupMembers (m_in caller ++ Env.elements (instance_methods_temp (rev_prog prog) caller)
                                   ++ m_vars caller)) as Nodup'.
        { pose proof (m_nodupvars caller) as Nodup.
          apply NoDupMembers_app.
          - apply NoDupMembers_app_l in Nodup; auto.
          - apply NoDupMembers_app.
            + apply Env.NoDupMembers_elements.
            + apply NoDupMembers_app_r, NoDupMembers_app_l in Nodup; auto.
            + intros x Hin'.
              rewrite <- Env.In_Members in Hin'.
              eapply In_instance_methods_temp_find_method in Hin' as (?&c'&_&m'&?&?&_&Hmethod&?); subst.
              eapply find_method_name in Hmethod; subst.
              specialize (m_good m') as (_&Ha).
              specialize (m_good caller) as (Hvars&_). rewrite Forall_map in Hvars.
              repeat rewrite Forall_app in Hvars. destruct Hvars as (_&Hvars&_).
              intro contra. apply InMembers_In in contra as (?&Hin').
              eapply Forall_forall in Hin'; eauto.
              apply AtomOrGensym_inv in Hin'; auto with ident.
          - intros x Hin'.
            rewrite NotInMembers_app; split.
            * apply (NoDupMembers_app_InMembers x) in Nodup; auto.
              apply NotInMembers_app in Nodup; tauto.
            * intro Hin''.
              rewrite <- Env.In_Members in Hin''.
              eapply In_instance_methods_temp_find_method in Hin'' as (?&c'&_&m'&?&?&_&Hmethod&?); subst.
              eapply find_method_name in Hmethod; subst.
              specialize (m_good m') as (_&Ha).
              specialize (m_good caller) as (Hvars&_). rewrite Forall_map in Hvars.
              repeat rewrite Forall_app in Hvars. destruct Hvars as (Hvars&_&_).
              apply InMembers_In in Hin' as (?&Hin').
              eapply Forall_forall in Hin'; eauto.
              apply AtomOrGensym_inv in Hin'; auto with ident.
        }

        assert (forall x, ~In (prefix obc2c x) (var_names (make_out_temps (instance_methods_temp (rev_prog prog) caller)
                                                        ++ make_out_temps (extcalls_temp caller)
                                                        ++ map translate_param (m_vars caller)))).
        { intros ? contra.
          eapply obc2c_not_in_temps, fst_InMembers, contra. }

        assert (list_disjoint (var_names ((prefix obc2c self, type_of_inst_p owner.(c_name))
                                           :: (prefix obc2c out, type_of_inst_p (prefix_fun caller.(m_name) owner.(c_name)))
                                           :: (map translate_param caller.(m_in))))
                              (var_names (make_out_temps (instance_methods_temp (rev_prog prog) caller)
                                            ++ make_out_temps (extcalls_temp caller)
                                            ++ map translate_param caller.(m_vars)))).
        { repeat apply list_disjoint_cons_l; simpl; auto.
          intros ?? Hin1 Hin2 ?; subst; simpl_In.
          rewrite 2 in_app_iff in Hin0. destruct Hin0 as [Hin0|[Hin0|Hin0]]; apply In_InMembers in Hin0.
          - apply make_out_temps_instance_prefixed in Hin0 as (?&?&?); subst.
            eapply temp_not_in_translate_param_in. rewrite InMembers_translate_param_idem.
            eapply In_InMembers, Hin1.
          - apply make_out_temps_extcall_prefixed in Hin0 as (?&?); subst.
            eapply temp_not_in_translate_param_in. rewrite InMembers_translate_param_idem.
            eapply In_InMembers, Hin1.
          - rewrite InMembers_translate_param_idem in Hin0.
            pose proof (m_nodupvars caller) as Nodup.
            eapply NoDupMembers_app_InMembers; eauto using In_InMembers. apply InMembers_app; auto.
        }
        assert (list_disjoint (var_names ((prefix obc2c self, type_of_inst_p owner.(c_name))
                                            :: (map translate_param caller.(m_in))))
                              (var_names (make_out_temps (instance_methods_temp (rev_prog prog) caller)
                                          ++ make_out_temps (extcalls_temp caller)
                                          ++ map translate_param caller.(m_vars)))).
        { repeat apply list_disjoint_cons_l; simpl; auto.
          intros ?? Hin1 Hin2 ?; subst; simpl_In.
          rewrite 2 in_app_iff in Hin0. destruct Hin0 as [Hin0|[Hin0|Hin0]]; apply In_InMembers in Hin0.
          - apply make_out_temps_instance_prefixed in Hin0 as (?&?&?); subst.
            eapply temp_not_in_translate_param_in. rewrite InMembers_translate_param_idem.
            eapply In_InMembers, Hin1.
          - apply make_out_temps_extcall_prefixed in Hin0 as (?&?); subst.
            eapply temp_not_in_translate_param_in. rewrite InMembers_translate_param_idem.
            eapply In_InMembers, Hin1.
          - rewrite InMembers_translate_param_idem in Hin0.
            pose proof (m_nodupvars caller) as Nodup.
            eapply NoDupMembers_app_InMembers; eauto using In_InMembers. apply InMembers_app; auto.
        }
        unfold case_out in *.

        destruct_list caller.(m_out) as (y, t) ? ? : Out.
        - set (f:= {|
                    fn_return := Tvoid;
                    fn_callconv := AST.cc_default;
                    fn_params := (prefix obc2c self, type_of_inst_p (c_name owner)) :: map translate_param (m_in caller);
                    fn_vars := make_out_vars (instance_methods caller);
                    fn_temps := make_out_temps (instance_methods_temp (rev_prog prog) caller)
                                ++ make_out_temps (extcalls_temp caller)
                                ++ map translate_param (m_vars caller);
                    fn_body := return_with (translate_stmt (rev_prog prog) owner caller (m_body caller)) None |})
            in Finddef.
          exists loc_f, f.
          try repeat split; auto.
          change (Genv.find_funct_ptr tge loc_f) with (Genv.find_funct_ptr (Genv.globalenv tprog) loc_f).
          unfold Genv.find_funct_ptr.
          now setoid_rewrite Finddef.

        - set (f:= {|
                    fn_return := translate_type t;
                    fn_callconv := AST.cc_default;
                    fn_params := (prefix obc2c self, type_of_inst_p (c_name owner))
                                   :: map translate_param (m_in caller);
                    fn_vars := make_out_vars (instance_methods caller);
                    fn_temps := translate_param (y, t)
                                :: make_out_temps (instance_methods_temp (rev_prog prog) caller)
                                ++ make_out_temps (extcalls_temp caller)
                                ++ map translate_param (m_vars caller);
                    fn_body := return_with (translate_stmt (rev_prog prog) owner caller (m_body caller))
                                           (Some (make_in_arg (y, t))) |})
            in Finddef.
          exists loc_f, f.
          try repeat split; auto.
          change (Genv.find_funct_ptr tge loc_f) with (Genv.find_funct_ptr (Genv.globalenv tprog) loc_f).
          unfold Genv.find_funct_ptr.
          now setoid_rewrite Finddef.
          simpl in *.
          apply list_disjoint_cons_r; auto.
          intros [Eq|Hin'].
          + pose proof (m_good_out caller (y, t)) as Good; subst.
            apply AtomOrGensym_inv in Good; auto with ident.
            rewrite Out. left; auto.
          + pose proof (m_nodupvars caller) as Nodup.
            unfold var_names in Hin'. rewrite <-fst_InMembers, InMembers_translate_param_idem in Hin'.
            apply (NoDupMembers_app_InMembers y) in Nodup; auto.
            apply Nodup; rewrite InMembers_app, Out; right; apply InMembers_eq.

        - set (f:= {|
                    fn_return := Tvoid;
                    fn_callconv := AST.cc_default;
                    fn_params := (prefix obc2c self, type_of_inst_p (c_name owner))
                                   :: (prefix obc2c out, type_of_inst_p (prefix_fun caller.(m_name) owner.(c_name)))
                                   :: map translate_param (m_in caller);
                    fn_vars := make_out_vars (instance_methods caller);
                    fn_temps := make_out_temps (instance_methods_temp (rev_prog prog) caller)
                                ++ make_out_temps (extcalls_temp caller)
                                ++ map translate_param (m_vars caller);
                    fn_body := return_with (translate_stmt (rev_prog prog) owner caller (m_body caller)) None |})
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
      Forall (fun xt => sizeof tge (snd xt) <= Ptrofs.max_unsigned /\ wf_struct gcenv xt)
             (make_out_vars (instance_methods caller)).
  Proof.
    intros * Findcl Findmth.
    edestruct wt_program_find_unit as [WT']; eauto.
    eapply wt_class_find_method in WT'; eauto.
    apply Forall_forall; intros (?&?) Hin.
    unfold make_out_vars in Hin; apply in_map_iff in Hin;
      destruct Hin as (((o, fid), cid) & E & Hin); inv E.
    rewrite <-setoid_in_key_elt in Hin; apply M.elements_2 in Hin.
    assert (In (o, cid) (c_objs owner)) by (eapply In_instance_methods_In_insts; eauto).
    edestruct well_formed_instance_methods as (c & cls & callee & Findc & Findcallee & Notnil); eauto.
    edestruct find_unit_In; eauto;
      pose proof (find_method_name _ _ _ Findcallee); subst.
    clear Findmth.
    edestruct global_out_struct as (co & Hco & ? & Hmembers & ? & ? & ?);
      try reflexivity; eauto.
    split.
    * simpl; change (prog_comp_env tprog) with gcenv.
      setoid_rewrite Hco; auto.
    * exists (prefix_fun (m_name callee) (c_name c)), co.
      repeat split; eauto.
      rewrite Hmembers.
      intros * Hinxt; unfold translate_param in Hinxt.
      apply in_map_iff in Hinxt as ((x, t) & Eq & Hinxt); inv Eq; eauto.
      apply in_map_iff in Hinxt as ((x, t) & Eq & Hinxt); inv Eq; eauto with clight.
  Qed.

  Lemma find_main_class_sig: {c_prog_main | find_class main_node prog = Some c_prog_main}.
  Proof.
    pose proof TRANSL as Trans; inv_trans Trans; eauto.
  Qed.

  Definition c_main   : class := fst (proj1_sig find_main_class_sig).
  Definition prog_main: program := snd (proj1_sig find_main_class_sig).

  Definition find_main_class: find_class main_node prog = Some (c_main, prog_main).
  Proof.
    unfold c_main, prog_main; destruct find_main_class_sig as ((?&?)&?); simpl; auto.
  Qed.

  Lemma find_main_step_sig: {m_step | find_method step c_main.(c_methods) = Some m_step}.
  Proof.
    pose proof TRANSL as Trans; inv_trans Trans as Eexterns En Estep Ereset Eenums with structs funs E.
    rewrite find_main_class in En; inv En; eauto.
  Qed.

  Lemma find_main_reset_sig: {m_reset | find_method reset c_main.(c_methods) = Some m_reset}.
  Proof.
    pose proof TRANSL as Trans; inv_trans Trans as Eexterns En Estep Ereset Eenums with structs funs E.
    rewrite find_main_class in En; inv En; eauto.
  Qed.

  Definition main_step : method := proj1_sig find_main_step_sig.
  Definition main_reset: method := proj1_sig find_main_reset_sig.

  Definition find_main_step : find_method step c_main.(c_methods) = Some main_step := proj2_sig find_main_step_sig.
  Definition find_main_reset: find_method reset c_main.(c_methods) = Some main_reset := proj2_sig find_main_reset_sig.

  Lemma TranslateClasses:
    {structs_funs | split (map (translate_class (rev_prog prog)) (rev_prog prog).(classes)) = structs_funs}.
  Proof.
    pose proof TRANSL as Trans; inv_trans Trans; eauto.
  Qed.

  Definition structs: list (list composite_definition) := fst (proj1_sig TranslateClasses).
  Definition funs   : list (list (ident * AST.globdef _ _)) := snd (proj1_sig TranslateClasses).

  Lemma tprog_defs:
    let ce := globalenv tprog in
    tprog.(prog_defs) = map (vardef ce false) [(prefix_glob (prefix self main_id), type_of_inst main_node)] ++
                            map (vardef ce true) (map glob_bind (m_out main_step) ++
                                                      map glob_bind (m_in main_step)) ++
                            map (fun '(f, (tyin, tyout)) => translate_external f tyin tyout) (externs prog) ++
                            concat funs ++
                            (if do_sync
                             then [(sync_id, make_sync);
                                     (main_sync_id, make_main true main_node main_step)]
                             else []) ++
                            [(main_proved_id, make_main false main_node main_step);
                            (main_id, make_entry_point do_sync)].
  Proof.
    pose proof TRANSL as Trans; inv_trans Trans as Eexterns En Estep Ereset Eenums with structs funs E.
    unfold TranslateOk.funs. setoid_rewrite (proj2_sig TranslateClasses) in E.
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
    exists b, Genv.find_symbol (globalenv tprog) (prefix_glob x) = Some b
         /\ Genv.block_is_volatile (globalenv tprog) b = true.

  Lemma in_vardef_is_volatile:
    forall x t,
      In ((vardef (globalenv tprog) true) (glob_bind (x, t))) tprog.(prog_defs) ->
      is_volatile (x, t).
  Proof.
    intros * Hin.
    set (ty := merge_attributes (translate_type t) (mk_attr true None)).
    assert ((AST.prog_defmap tprog) ! (prefix_glob x) =
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
    exists (prefix_glob x, translate_type t); split; auto.
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
    exists (prefix_glob x, translate_type t); split; auto.
    apply in_map_iff.
    exists (x, t); split; auto.
  Qed.

  Lemma tprog_main_proved_id:
    Ctypes.prog_main tprog = main_proved_id.
  Proof.
    pose proof TRANSL as Trans; inv_trans Trans as Eexterns En Estep Ereset Eenums with structs funs E.
    unfold make_program' in Trans.
    destruct (build_composite_env' (concat structs)) as [(ce, ?)|]; try discriminate.
    destruct (check_size_env ce (concat structs)); try discriminate.
    inv Trans; auto.
  Qed.

  Let out_step   := prefix out step.
  Let t_out_step := type_of_inst (prefix_fun step main_node).

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
    inv_trans TRANSL as Eexterns En Estep Ereset Eenums with structs funs E.
    pose proof (build_ok _ _ _ _ _ _ _ TRANSL) as Hbuild.
    apply make_program_defs in TRANSL; destruct TRANSL as (gce & Hbuild' & Eq); clear TRANSL.
    rewrite Hbuild in Hbuild'; inv Hbuild'.
    setoid_rewrite Eq; clear Eq.
    simpl; intros * [Hinv|Hinv].
    - inv Hinv; simpl; split.
      + split; auto; apply Z.divide_0_r.
      + intros * Hinio; simpl in Hinio;
          destruct Hinio; [discriminate|contradiction].
    - repeat rewrite in_app in Hinv;
        destruct Hinv as [Hinv|[Hinv|[Hinv|[Hinv|[Hinv|Hinv]]]]]; try now inv Hinv.
      + induction (map glob_bind (m_out m) ++ map glob_bind (m_in m)) as [|(x, t)].
        * contradict Hinv.
        * destruct Hinv as [Hinv|]; auto.
          inv Hinv; simpl; split.
          -- split; auto; apply Z.divide_0_r.
          -- intros * Hinio; simpl in Hinio;
               destruct Hinio; [discriminate|contradiction].
      + simpl_In.
      + clear En Hbuild WT.
        remember prog as prog1.
        replace (translate_class (rev_prog prog1)) with (translate_class (rev_prog prog)) in E
          by now rewrite <-Heqprog1.
        clear Heqprog1.
        revert structs funs E Hinv.
        simpl.
        setoid_rewrite rev_tr_spec.
        induction prog1.(classes) as [|c' prog']; intros * E Hinv; simpl in E.
        * inv E; simpl in Hinv; contradiction.
        * rewrite map_app in E; simpl in E; rewrite split_last in E.
          destruct (split (map (translate_class (rev_prog prog)) (rev prog'))) as (g, d) eqn: Egd; inv E.
          rewrite concat_app in Hinv; simpl in Hinv; rewrite app_nil_r in Hinv;
            apply in_app in Hinv; destruct Hinv as [|Hinv]; eauto.
          unfold make_methods in Hinv.
          induction (c_methods c'); simpl in Hinv; try contradiction.
          destruct Hinv as [Hinv|]; auto.
          unfold translate_method in Hinv.
          destruct_list (m_out a) as (?, ?) ? ?; inv Hinv.
    + destruct do_sync; try now inv Hinv.
      rewrite cons_is_app, in_app in Hinv.
      destruct Hinv as [[Hinv|Hinv]|[Hinv|Hinv]]; try inv Hinv.
  Qed.

  Lemma find_main_ptr:
    exists b,
      Genv.find_symbol tge main_proved_id = Some b
      /\ Genv.find_funct_ptr tge b = Some (Ctypes.Internal main_f).
  Proof.
    assert ((AST.prog_defmap tprog) ! main_proved_id = Some (make_main false main_node main_step)) as Hget.
    { unfold AST.prog_defmap; apply PTree_Properties.of_list_norepet.
      - eapply prog_defs_norepet; eauto.
      - setoid_rewrite tprog_defs; eauto.
        apply in_cons. rewrite 3 in_app_iff. do 3 right.
        generalize do_sync; intro; cases; [do 2 apply in_cons|]; apply in_eq.
    }
    apply Genv.find_def_symbol in Hget as (b & Findsym & Finddef).
    exists b; split; auto.
    unfold Genv.find_funct_ptr; subst tge; setoid_rewrite Finddef.
    unfold main_f; unfold case_out; simpl; repeat f_equal; cases.
  Qed.

End TranslateOk.

Global Hint Resolve Consistent prog_defs_norepet make_members_co : clight.
Global Hint Resolve norepet_vars_main norepet_params_main disjoint_params_temps_main : clight.
