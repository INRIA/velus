From compcert Require Import common.Separation.
From compcert Require Import common.Values.
From compcert Require Import common.Memdata.
From compcert Require Import common.Memory.
From compcert Require common.Errors.
From compcert Require Import cfrontend.Ctypes.
From compcert Require Import cfrontend.Clight.
From compcert Require Import lib.Maps.
From compcert Require Import lib.Coqlib.
From compcert Require Import lib.Integers.

From Velus Require Import Common.
From Velus Require Import Common.CompCertLib.
From Velus Require Import Ident.
From Velus Require Import Environment.
From Velus Require Import Memory.

From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import ZArith.BinInt.

From Coq Require Import Program.Tactics.

From Velus Require Import ObcToClight.MoreSeparation.
From Velus Require Import ObcToClight.Generation.
From Velus Require Import ObcToClight.GenerationProperties.
From Velus Require Import ObcToClight.Interface.

Import Obc.Syn.
Import Obc.Sem.
Import Obc.Typ.

Open Scope list.
Open Scope sep_scope.
Open Scope Z.

Definition match_value (e: Env.t val) (x: ident) (v': val) : Prop :=
  match Env.find x e with
  | None => True
  | Some v => v' = v
  end.

Lemma match_value_empty:
  forall x, match_value (Env.empty _) x = (fun _ => True).
Proof.
  intro. unfold match_value.
  rewrite Env.gempty; auto.
Qed.

Lemma match_value_add:
  forall x x' v e,
    x <> x' ->
    match_value (Env.add x' v e) x = match_value e x.
Proof.
  intros * Hneq.
  unfold match_value. simpl.
  rewrite Env.gso with (1:=Hneq).
  reflexivity.
Qed.

Remark match_find_var_det:
  forall ve x v1 v2,
    match_value ve x v1 ->
    Env.find x ve = Some v2 ->
    v1 = v2.
Proof.
  unfold match_value; simpl.
  intros * Hm Hf.
  now rewrite Hf in Hm.
Qed.

Ltac app_match_find_var_det :=
  match goal with
  | H1: Env.find ?x ?ve = Some ?v1,
        H2: match_value ?ve ?x ?v2 |- _ =>
    assert (v2 = v1) by (apply (match_find_var_det _ _ _ _ H2 H1)); subst v1; clear H2
  end.

Section Staterep.
  Variable ge : composite_env.

  Definition staterep_mems (cls: class) (me: menv) (b: block) (ofs: Z) '((x, ty): ident * type) :=
    match field_offset ge x (make_members cls) with
    | Errors.OK d =>
	    contains_w (type_chunk ty) b (ofs + d) (match_value me.(values) x)
    | Errors.Error _ => sepfalse
    end.

  Fixpoint staterep
           (p: program) (clsnm: ident) (me: menv) (b: block) (ofs: Z): massert :=
    match p with
    | nil => sepfalse
    | cls :: p' =>
      if ident_eqb clsnm cls.(c_name)
      then
        sepall (staterep_mems cls me b ofs) cls.(c_mems)
        **
        sepall (fun '((i, c): ident * ident) =>
                  match field_offset ge i (make_members cls) with
                  | Errors.OK d =>
                    staterep p' c (instance_match i me) b (ofs + d)
                  | Errors.Error _ => sepfalse
                  end) cls.(c_objs)
      else staterep p' clsnm me b ofs
    end.

  Definition staterep_objs (p: program) (cls: class) (me: menv) (b: block) (ofs: Z) '((i, c): ident * ident) : massert :=
    match field_offset ge i (make_members cls) with
    | Errors.OK d =>
      staterep p c (instance_match i me) b (ofs + d)
    | Errors.Error _ => sepfalse
    end.

  Lemma staterep_objs_not_in:
    forall objs p cls me i me_i b ofs,
      ~ InMembers i objs ->
      sepall (staterep_objs p cls me b ofs) objs <-*->
      sepall (staterep_objs p cls (add_inst i me_i me) b ofs) objs.
  Proof.
    induction objs as [|(o, c)]; intros * Hnin; simpl; auto.
    apply NotInMembers_cons in Hnin as (?&?).
    apply sepconj_morph_2; auto.
    cases.
    unfold instance_match; rewrite find_inst_gso; auto.
  Qed.

  Lemma staterep_cons:
    forall cls prog clsnm me b ofs,
      clsnm = cls.(c_name) ->
      staterep (cls :: prog) clsnm me b ofs <-*->
      sepall (staterep_mems cls me b ofs) cls.(c_mems)
      ** sepall (staterep_objs prog cls me b ofs) cls.(c_objs).
  Proof.
    intros * Hnm.
    apply ident_eqb_eq in Hnm.
    simpl; rewrite Hnm; reflexivity.
  Qed.

  Lemma staterep_skip_cons:
    forall cls prog clsnm me b ofs,
      clsnm <> cls.(c_name) ->
      staterep (cls :: prog) clsnm me b ofs <-*-> staterep prog clsnm me b ofs.
  Proof.
    intros * Hnm.
    apply ident_eqb_neq in Hnm.
    simpl; rewrite Hnm; reflexivity.
  Qed.

  Lemma staterep_skip_app:
    forall clsnm prog oprog me b ofs,
      find_class clsnm oprog = None ->
      staterep (oprog ++ prog) clsnm me b ofs <-*-> staterep prog clsnm me b ofs.
  Proof.
    intros * Hnin.
    induction oprog as [|cls oprog IH].
    - rewrite app_nil_l. reflexivity.
    - apply find_class_none in Hnin; destruct Hnin.
      rewrite <-app_comm_cons.
      rewrite staterep_skip_cons; auto.
  Qed.

  Remark staterep_skip:
    forall c clsnm prog prog' me b ofs,
      find_class clsnm prog = Some (c, prog') ->
      staterep prog c.(c_name) me b ofs <-*->
      staterep (c :: prog') c.(c_name) me b ofs.
  Proof.
    intros * Find.
    pose proof (find_class_name _ _ _ _ Find); subst.
    pose proof (find_class_app _ _ _ _ Find) as (? & Hprog & FindNone).
    rewrite Hprog.
    rewrite staterep_skip_app; auto.
  Qed.

  Lemma decidable_footprint_staterep:
    forall p clsnm me b ofs,
      decidable_footprint (staterep p clsnm me b ofs).
  Proof.
    induction p as [|cls p' IH]; [now auto|].
    intros; simpl.
    destruct (ident_eqb clsnm (c_name cls));
      [|now apply IH].
    apply decidable_footprint_sepconj;
      apply decidable_footprint_sepall;
      (intro x; destruct x as [x ty]; simpl;
       destruct (field_offset ge x (make_members cls))); auto.
  Qed.

  Lemma footprint_perm_staterep:
    forall p clsnm me b ofs b' lo hi,
      footprint_perm_w (staterep p clsnm me b ofs) b' lo hi.
  Proof.
    induction p as [|cls p' IH]; [now auto|].
    intros; simpl.
    destruct (ident_eqb clsnm (c_name cls));
      [|now apply IH].
    apply footprint_perm_sepconj;
      apply footprint_perm_sepall;
      (intro x; destruct x as [x ty]; simpl;
       destruct (field_offset ge x (make_members cls))); auto.
  Qed.

  Hint Resolve decidable_footprint_staterep footprint_perm_staterep.

End Staterep.

(** The struct_in_bounds predicate.

    TODO: add explanatory text. *)

Section StructInBounds.
  Variable env : composite_env.
  Hypothesis env_consistent: composite_env_consistent env.

  Definition struct_in_bounds (min max ofs: Z) (flds: Ctypes.members) :=
    min <= ofs /\ ofs + sizeof_struct env 0 flds <= max.

  Lemma struct_in_bounds_sizeof:
    forall id co,
      env!id = Some co ->
      struct_in_bounds 0 (sizeof_struct env 0 (co_members co)) 0 (co_members co).
  Proof.
    intros. unfold struct_in_bounds. auto with zarith.
  Qed.

  Lemma struct_in_bounds_weaken:
    forall min' max' min max ofs flds,
      struct_in_bounds min max ofs flds ->
      min' <= min ->
      max <= max' ->
      struct_in_bounds min' max' ofs flds.
  Proof.
    unfold struct_in_bounds. destruct 1; intros. auto with zarith.
  Qed.

  Lemma struct_in_bounds_field:
    forall min max ofs flds id d,
      struct_in_bounds min max ofs flds ->
      field_offset env id flds = Errors.OK d ->
      min <= ofs + d <= max.
  Proof.
    unfold struct_in_bounds.
    intros * (Hmin & Hmax) Hfo.
    destruct (field_offset_type _ _ _ _ Hfo) as (ty & Hft).
    destruct (field_offset_in_range _ _ _ _ _ Hfo Hft) as (H0d & Hsize).
    split; auto with zarith.
    apply Z.le_trans with (2:=Hmax).
    apply Z.add_le_mono; auto with zarith.
    apply Z.le_trans with (2:=Hsize).
    rewrite Zplus_0_r_reverse at 1.
    auto using (Z.ge_le _ _ (sizeof_pos env ty)) with zarith.
  Qed.

  Lemma struct_in_struct_in_bounds:
    forall min max ofs flds id sid d co a,
      struct_in_bounds min max ofs flds ->
      field_offset env id flds = Errors.OK d ->
      field_type id flds = Errors.OK (Tstruct sid a) ->
      env!sid = Some co ->
      co_su co = Struct ->
      struct_in_bounds min max (ofs + d) (co_members co).
  Proof.
    unfold struct_in_bounds.
    intros * (Hmin & Hmax) Hfo Hft Henv Hsu.
    apply field_offset_in_range with (1:=Hfo) in Hft.
    destruct Hft as (Hd0 & Hsizeof).
    split; auto with zarith.
    apply Zplus_le_compat_l with (p:=ofs) in Hsizeof.
    apply Z.le_trans with (1:=Hsizeof) in Hmax.
    apply Z.le_trans with (2:=Hmax).
    simpl; rewrite Henv, Z.add_assoc.
    apply Z.add_le_mono_l.
    specialize (env_consistent _ _ Henv).
    rewrite (co_consistent_sizeof _ _ env_consistent), Hsu.
    apply align_le.
    destruct (co_alignof_two_p co) as (n & H2p).
    rewrite H2p.
    apply two_power_nat_pos.
  Qed.

End StructInBounds.

Section StateRepProperties.

  Variable prog: program.
  Variable gcenv: composite_env.

  Hypothesis gcenv_consistent: composite_env_consistent gcenv.

  Hypothesis make_members_co:
    forall clsnm cls prog',
      find_class clsnm prog = Some (cls, prog') ->
      (exists co, gcenv!clsnm = Some co
             /\ co_su co = Struct
             /\ co_members co = make_members cls
             /\ attr_alignas (co_attr co) = None
             /\ NoDupMembers (co_members co)
             /\ co.(co_sizeof) <= Ptrofs.max_unsigned).

  Lemma struct_in_struct_in_bounds':
    forall min max ofs clsid cls o c cls' prog' prog'',
      wt_program prog ->
      find_class clsid prog = Some (cls, prog') ->
      struct_in_bounds gcenv min max ofs (make_members cls) ->
      In (o, c) cls.(c_objs) ->
      find_class c prog' = Some (cls', prog'') ->
      exists d, field_offset gcenv o (make_members cls) = Errors.OK d
           /\ struct_in_bounds gcenv min max (ofs + d) (make_members cls').
  Proof.
    intros * WTp Hfc Hsb Hin Hfc'.
    destruct (c_objs_field_offset gcenv _ _ _ Hin) as (d & Hfo).
    exists d; split; auto.
    destruct (make_members_co _ _ _ Hfc)
      as (cls_co & Hg & Hsu & Hmem & Hattr & Hndup).
    rewrite <-Hmem in *.
    eapply find_class_chained with (1:=WTp) (2:=Hfc) in Hfc'.
    destruct (make_members_co _ _ _ Hfc')
      as (cls'_co & Hg' & Hsu' & Hmem' & Hattr' & Hndup').
    rewrite <-Hmem' in *.
    pose proof (field_offset_type _ _ _ _ Hfo) as Hty.
    destruct Hty as (ty & Hty).
    eapply struct_in_struct_in_bounds with (a:=noattr); eauto.
    clear make_members_co.
    (* Show that the field_type is a Tstruct *)
    pose proof cls.(c_nodup) as Hnodup.
    rewrite Permutation.Permutation_app_comm in Hnodup.
    assert (~InMembers o cls.(c_mems)) as Hnmem.
    { apply In_InMembers in Hin.
      apply NoDup_app_In with (x:=o) in Hnodup.
      now rewrite fst_InMembers; auto.
      now rewrite fst_InMembers in Hin. }
    apply NoDup_app_weaken in Hnodup.
    revert Hnodup Hty Hin. rewrite Hmem. unfold make_members.
    rewrite field_type_skip_app.
    2:now rewrite InMembers_translate_param_idem.
    clear.
    induction cls.(c_objs) as [|x xs IH]; [now inversion 1|].
    destruct x as [o' c'].
    destruct (ident_eq_dec o o') as [He|Hne].
    - simpl. rewrite He, peq_true. intros Hnodup ? Hoc.
      destruct Hoc as [Hoc|Hin].
      + injection Hoc; intros R1; rewrite <-R1. reflexivity.
      + inv Hnodup.
        match goal with H:~In _ _ |- _ => contradiction H end.
        apply fst_InMembers. now apply In_InMembers in Hin.
    - simpl; rewrite peq_false; auto.
      intros Hnodup Hft Hin.
      destruct Hin; auto.
      now injection H; intros R1 R2; rewrite <-R1,<-R2 in *; contradiction Hne.
      inv Hnodup; auto.
  Qed.

  Hint Resolve Z.divide_trans.

  Lemma range_staterep:
    forall b clsnm,
      wt_program prog ->
      find_class clsnm prog <> None ->
      range_w b 0 (sizeof gcenv (type_of_inst clsnm)) -*>
      staterep gcenv prog clsnm mempty b 0.
  Proof.
    intros * WTp Hfind.
    (* Weaken the goal for proof by induction. *)
    cut (forall lo,
           (alignof gcenv (type_of_inst clsnm) | lo) ->
           massert_imp (range_w b lo (lo + sizeof gcenv (type_of_inst clsnm)))
                       (staterep gcenv prog clsnm mempty b lo)).
    now intro HH; apply HH; apply Z.divide_0_r.

    (* Setup an induction on prog. *)
    revert clsnm Hfind.
    remember prog as prog1.
    assert (WTp' := WTp).
    rewrite Heqprog1 in make_members_co, WTp.
    assert (suffix prog1 prog) as Hsub
        by now rewrite Heqprog1.
    clear (* TRANSL *) Heqprog1.
    induction prog1 as [|cls prog' IH]; intros clsnm Hfind lo Halign.
    now apply not_None_is_Some in Hfind; destruct Hfind; discriminate.
    inversion_clear WTp' as [|? ? WTc WTp'' Hnodup]; subst.

    (* Staterep looks for the named class: found now or later? *)
    destruct (ident_eqb cls.(c_name) clsnm) eqn:Hclsnm.

    - (* Exploit make_members_co for the named class. *)
      apply not_None_is_Some in Hfind.
      destruct Hfind as ((cls', prog'') & Hfind).
      assert (find_class clsnm prog = Some (cls', prog'')) as Hprog
          by apply find_class_sub_same with (1:=Hfind) (2:=WTp) (3:=Hsub).
      destruct (make_members_co _ _ _ Hprog)
        as (co & Hg & Hsu & Hmem & Hattr & Hndup & ?).

      (* find_class succeeds for clsnm (deliberately after previous step). *)
      simpl in Hfind. rewrite Hclsnm in Hfind.
      injection Hfind; intros He1 He2; rewrite <-He1, <-He2 in *.
      clear Hfind He1 He2.

      (* Develop some facts about member alignment. *)
      pose proof (co_members_alignof _ _ (gcenv_consistent _ _ Hg) Hattr)
        as Hcoal.
      rewrite Hmem in Hcoal. unfold make_members in Hcoal.
      apply Forall_app in Hcoal. destruct Hcoal as [Hcoal1 Hcoal2].
      simpl in Halign. rewrite Hg, align_noattr in Halign.
      assert (Hndup':=Hndup). rewrite Hmem in Hndup'.

      (* Massage the goal into two parallel parts: for locals and instances. *)
      simpl. unfold staterep_mems.
      rewrite ident_eqb_sym in Hclsnm.
      rewrite Hclsnm, Hg, <-Hmem.
      rewrite split_range_fields
      with (1:=gcenv_consistent) (2:=Hg) (3:=Hsu) (4:=Hndup).
      rewrite Hmem at 2. unfold make_members.
      rewrite sepall_app.
      apply sep_imp'.

      + (* Divide up the memory sub-block for cls.(c_mems). *)
        pose proof (field_translate_mem_type _ _ _ _ Hprog) as Htype.
        clear Hcoal2.
        induction cls.(c_mems) as [|m ms]; auto.
        apply Forall_cons2 in Hcoal1.
        destruct Hcoal1 as [Hcoal1 Hcoal2].
        apply sep_imp'; auto with datatypes.
        destruct m; simpl.
        destruct (field_offset gcenv i (co_members co)) eqn:Hfo; auto.
        rewrite match_value_empty, sizeof_translate_chunk; eauto.
        apply range_contains'; auto with mem.
        apply field_offset_aligned with (ty:=cltype t) in Hfo.
        now apply Z.divide_add_r; eauto.
        rewrite <-Hmem in Htype. apply Htype; auto with datatypes.

      + (* Divide up the memory sub-block for cls.(c_objs). *)
        pose proof (field_translate_obj_type _ _ _ _ Hprog) as Htype.
        rewrite <-Hmem in Htype.
        destruct WTc as [Ho Hm]; clear Hm.
        induction cls.(c_objs) as [|o os]; auto.
        simpl. apply sep_imp'.
        2:now inv Ho; apply Forall_cons2 in Hcoal2; intuition.
        apply Forall_forall with (x:=o) in Ho; auto with datatypes.
        destruct o as [o c].
        apply Forall_cons2 in Hcoal2.
        destruct Hcoal2 as [Hcoal2 Hcoal3].
        specialize (Htype o c (in_eq _ _)).
        clear IHos Hcoal1 Hcoal3 os.
        simpl in *.
        destruct (field_offset gcenv o (co_members co)) eqn:Hfo; auto.
        rewrite instance_match_empty.
        specialize (IH WTp'' (suffix_cons _ _ _ Hsub) c Ho (lo + z)%Z).
        apply not_None_is_Some in Ho.
        destruct Ho as ((c' & prog''') & Ho).
        assert (find_class c prog = Some (c', prog''')) as Hcin'
            by apply find_class_sub_same with (1:=Ho) (2:=WTp)
                                              (3:=suffix_cons _ _ _ Hsub).
        destruct (make_members_co _ _ _ Hcin')
          as (co' & Hg' & Hsu' & Hmem' & Hattr' & Hnodup').
        rewrite Hg', align_noattr in *.
        apply IH.
        apply Z.divide_add_r; eauto.
        eapply field_offset_aligned in Hfo; eauto.
        apply Z.divide_trans with (2:=Hfo).
        simpl. rewrite Hg', align_noattr.
        apply Z.divide_refl.
    - simpl in Hfind.
      rewrite Hclsnm in Hfind.
      specialize (IH WTp'' (suffix_cons _ _ _ Hsub) clsnm Hfind lo Halign).
      rewrite ident_eqb_sym in Hclsnm.
      apply ident_eqb_neq in Hclsnm.
      rewrite staterep_skip_cons with (1:=Hclsnm).
      apply IH.
  Qed.

  Lemma staterep_deref_mem:
    forall cls prog' m me b ofs x ty d v P,
      m |= staterep gcenv (cls :: prog') cls.(c_name) me b ofs ** P ->
      In (x, ty) cls.(c_mems) ->
      find_val x me = Some v ->
      field_offset gcenv x (make_members cls) = Errors.OK d ->
      Clight.deref_loc (cltype ty) m b (Ptrofs.repr (ofs + d)) v.
  Proof.
    intros * Hm Hin Hv Hoff.
    apply sep_proj1 in Hm.
    simpl in Hm. rewrite ident_eqb_refl in Hm.
    apply sep_proj1 in Hm.
    apply sepall_in in Hin.
    destruct Hin as [ws [xs [Hsplit Hin]]].
    rewrite Hin in Hm. clear Hsplit Hin.
    apply sep_proj1 in Hm. clear ws xs.
    unfold staterep_mems in Hm.
    rewrite Hoff in Hm. clear Hoff.
    apply loadv_rule in Hm; auto with mem.
    destruct Hm as [v' [Hloadv Hmatch]].
    unfold match_value in Hmatch.
    unfold find_val in Hv; simpl in Hv.
    rewrite Hv in Hmatch; clear Hv.
    rewrite Hmatch in Hloadv; clear Hmatch.
    apply Clight.deref_loc_value with (2:=Hloadv); auto.
  Qed.

  Lemma staterep_field_offset:
    forall m me cls prog b ofs x ty P,
      m |= staterep gcenv (cls :: prog) cls.(c_name) me b ofs ** P ->
      In (x, ty) (c_mems cls) ->
      exists d, field_offset gcenv x (make_members cls) = Errors.OK d
           /\ 0 <= ofs + d <= Ptrofs.max_unsigned.
  Proof.
    intros * Hm Hin.
    Opaque sepconj. simpl in Hm. Transparent sepconj.
    rewrite ident_eqb_refl in Hm.
    do 2 apply sep_proj1 in Hm.
    apply sepall_in in Hin; destruct Hin as [ws [xs [Hsplit Hin]]].
    rewrite Hin in Hm. clear Hsplit Hin.
    apply sep_proj1 in Hm.
    clear ws xs.
    unfold staterep_mems in Hm.
    destruct (field_offset gcenv x (make_members cls)).
    + exists z; split; auto.
      eapply contains_no_overflow; eauto.
    + contradict Hm.
  Qed.

  Lemma staterep_extract:
    forall cid c prog' me b ofs m i c' P,
      find_class cid prog = Some (c, prog') ->
      (In (i, c') c.(c_objs)
       /\ m |= staterep gcenv prog cid me b ofs ** P)
      <-> exists objs objs' d,
          c.(c_objs) = objs ++ (i, c') :: objs'
          /\ field_offset gcenv i (make_members c) = Errors.OK d
          /\ m |= staterep gcenv prog' c' (instance_match i me) b (ofs + d)
                  ** sepall (staterep_mems gcenv c me b ofs) c.(c_mems)
                  ** sepall (staterep_objs gcenv prog' c me b ofs) (objs ++ objs')
                  ** P.
  Proof.
    intros * Find.
    pose proof Find as Fcid; apply find_class_name in Fcid; subst.
    rewrite staterep_skip, staterep_cons, sep_assoc; eauto.
    split.
    - intros (Hin & Hmem).
      apply sepall_in in Hin as (objs & objs' & E & Hp).
      rewrite Hp, sep_assoc, sep_swap in Hmem.
      unfold staterep_objs at 1 in Hmem.
      destruct (field_offset gcenv i (make_members c)) as [d|].
      + exists objs, objs', d; intuition.
      + destruct Hmem; contradiction.
    - intros (objs & objs' & d & E & Hofs & Hmem).
      split.
      + rewrite E; apply in_app; right; left; auto.
      + rewrite (sepall_breakout (c_objs c)), sep_assoc, sep_swap; eauto.
        unfold staterep_objs at 1.
        rewrite Hofs; auto.
  Qed.

  Lemma staterep_chained:
    forall prog' cid c prog'' me ownerid owner sb sofs,
      wt_program prog ->
      find_class ownerid prog = Some (owner, prog') ->
      find_class cid prog' = Some (c, prog'') ->
      staterep gcenv prog' cid me sb sofs <-*->
      staterep gcenv prog cid me sb sofs.
  Proof.
    clear gcenv_consistent make_members_co.
    induction prog as [|cl]; intros * WT Findowner Findcl.
    - inv Findowner.
    - simpl in Findowner.
      cases_eqn E.
      + inv Findowner.
        inv WT.
        erewrite <- (find_class_name cid); eauto.
        apply find_class_In in Findcl.
        eapply Forall_forall in Findcl; eauto; simpl in Findcl.
        rewrite staterep_skip_cons; auto.
      + inv WT.
        rewrite IHp; eauto.
        eapply find_class_chained in Findcl; eauto.
        erewrite <- (find_class_name cid); eauto.
        apply find_class_In in Findcl.
        eapply Forall_forall in Findcl; eauto; simpl in Findcl.
        rewrite staterep_skip_cons; eauto.
  Qed.

End StateRepProperties.

Section BlockRep.
  Variable ge : composite_env.
  Hypothesis ge_consistent : composite_env_consistent ge.

  (* TODO: name predicate "blockrep" and write sepall blockrep xs *)
  Definition blockrep (ve: venv) (flds: members) (b: block) : massert :=
    sepall (fun xty : ident * Ctypes.type =>
              let (x, ty) := xty in
              match field_offset ge x flds, access_mode ty with
              | Errors.OK d, By_value chunk =>
                contains chunk b d (match_value ve x)
              | _, _ => sepfalse
              end) flds.

  Lemma blockrep_deref_mem:
    forall m ve co b x ty d v P,
      m |= blockrep ve (co_members co) b ** P ->
      In (x, ty) (co_members co) ->
      Env.find x ve = Some v ->
      field_offset ge x (co_members co) = Errors.OK d ->
      Clight.deref_loc ty m b (Ptrofs.repr d) v.
  Proof.
    intros * Hm Hin Hv Hoff.
    unfold blockrep in Hm.
    apply sepall_in in Hin.
    destruct Hin as [ws [xs [Hsplit Hin]]].
    rewrite Hin in Hm. clear Hsplit Hin.
    do 2 apply sep_proj1 in Hm. clear ws xs.
    rewrite Hoff in Hm. clear Hoff.
    destruct (access_mode ty) eqn:Haccess; try contradiction.
    apply loadv_rule in Hm; auto with mem.
    destruct Hm as [v' [Hloadv Hmatch]].
    unfold match_value in Hmatch.
    rewrite Hv in Hmatch. clear Hv.
    rewrite Hmatch in Hloadv. clear Hmatch.
    apply Clight.deref_loc_value with (1:=Haccess) (2:=Hloadv).
  Qed.

  Lemma footprint_perm_blockrep:
    forall ve flds b b' lo hi,
      footprint_perm (blockrep ve flds b) b' lo hi.
  Proof.
    intros. apply footprint_perm_sepall.
    intros x b'' lo' hi'.
    destruct x as [x ty].
    destruct (field_offset ge x flds).
    2:now apply footprint_perm_sepfalse.
    destruct (access_mode ty);
      try apply footprint_perm_sepfalse.
    apply footprint_perm_contains.
  Qed.

  Lemma footprint_decidable_blockrep:
    forall ve flds b,
      decidable_footprint (blockrep ve flds b).
  Proof.
    intros. apply decidable_footprint_sepall.
    intro x; destruct x as [x ty].
    destruct (field_offset ge x flds).
    2:now apply decidable_footprint_sepfalse.
    destruct (access_mode ty);
      try apply decidable_footprint_sepfalse.
    apply decidable_footprint_contains.
  Qed.

  Lemma blockrep_empty':
    forall flds b,
      NoDupMembers flds ->
      (forall x ty, In (x, ty) flds ->
               exists chunk, access_mode ty = By_value chunk
                        /\ (Memdata.align_chunk chunk | alignof ge ty)) ->
      sepall (field_range ge flds b 0) flds <-*-> blockrep vempty flds b.
  Proof.
    intros * Hndups Hchunk.
    unfold blockrep.
    apply sepall_swapp.
    intros fld Hin.
    destruct fld as [x ty].
    unfold field_range'.
    destruct (field_offset ge x flds) eqn:Hoff.
    2:reflexivity.
    apply field_offset_aligned with (ty:=ty) in Hoff.
    2:apply in_field_type with (1:=Hndups) (2:=Hin).
    destruct (Hchunk _ _ Hin) as [chunk [Haccess Halign]].
    rewrite Haccess.
    split; [split|split].
    - intros m Hr.
      rewrite match_value_empty.
      apply range_contains'; auto with mem.
      now apply Zdivides_trans with (1:=Halign) (2:=Hoff).
      erewrite <-sizeof_by_value with (1:=Haccess); eauto.
    - simpl. now rewrite sizeof_by_value with (1:=Haccess).
    - rewrite match_value_empty, sizeof_by_value with (1:=Haccess), Z.add_0_l.
      intros. now apply contains_range' in H.
      (* NB: requires "new" definition of contains *)
    - simpl. now rewrite sizeof_by_value with (1:=Haccess).
  Qed.

  Lemma blockrep_empty:
    forall nm co b,
      ge!nm = Some co ->
      co_su co = Struct ->
      NoDupMembers (co_members co) ->
      (forall x ty, In (x, ty) (co_members co) ->
               exists chunk, access_mode ty = By_value chunk
                        /\ (Memdata.align_chunk chunk | alignof ge ty)) ->
      range b 0 (co_sizeof co) -*> blockrep vempty (co_members co) b.
  Proof.
    intros * Hco Hstruct Hndups Hchunk.
    rewrite split_range_fields
    with (1:=ge_consistent) (2:=Hco) (3:=Hstruct) (4:=Hndups).
    rewrite blockrep_empty' with (1:=Hndups) (2:=Hchunk).
    reflexivity.
  Qed.

  Lemma blockrep_any_empty:
    forall flds ve b,
      blockrep ve flds b -*> blockrep vempty flds b.
  Proof.
    intros flds ve b.
    apply sepall_weakenp.
    intros f Hin.
    destruct f as [x ty].
    destruct (field_offset ge x flds); try reflexivity.
    destruct (access_mode ty); try reflexivity.
    apply contains_imp.
    intros. now rewrite match_value_empty.
  Qed.

  Lemma match_value_adds_gso:
    forall x xs vs ve,
      ~In x xs ->
      NoDup xs ->
      match_value (Env.adds xs vs ve) x = match_value ve x.
  Proof.
    induction xs as [|x' xs IH]; auto.
    intros vs ve Hnin Hndp.
    apply not_in_cons in Hnin as (Hxx' & Hnin).
    inv Hndp.
    destruct vs as [|v vs]; auto.
    rewrite Env.adds_cons_cons, match_value_add; auto.
  Qed.

  Lemma blockrep_nodup:
    forall (xs: list (ident * type)) vs flds ve ob,
      NoDup (map fst xs ++ map fst flds) ->
      blockrep ve flds ob <-*-> blockrep (Env.adds (map fst xs) vs ve) flds ob.
  Proof.
    intros * Nodup.
    unfold blockrep.
    apply sepall_swapp.
    intros (x, t) Hin.
    destruct (field_offset ge x flds); auto.
    destruct (access_mode t); auto.
    assert (~In x (map fst xs)) as Hnxs
        by (rewrite Permutation.Permutation_app_comm in Nodup;
            apply in_map with (f := fst) in Hin;
            eapply NoDup_app_In in Nodup; eauto).
    intros; erewrite match_value_adds_gso; auto.
    eapply NoDup_app_weaken; eauto.
  Qed.

  Lemma blockrep_findvars:
    forall ve xs vs b,
      Forall2 (fun x v => Env.find x ve = v) (map fst xs) vs ->
      blockrep ve xs b -*> blockrep (Env.adds_opt (map fst xs) vs vempty) xs b.
  Proof.
    unfold Env.adds_opt; simpl.
    intros * Findvars.
    unfold blockrep.
    apply sepall_weakenp.
    intros (x, t) Hin.
    destruct (field_offset ge x xs); auto.
    destruct (access_mode t); auto.
    apply contains_imp.
    apply In_InMembers in Hin.
    intros v Hmv.
    revert vs Findvars.
    induction xs as [|(x', t')], vs; simpl; intro Findvars;
      try (now inversion Hin).
    inversion_clear Findvars as [|? ? ? ? Find Findvars'].
    unfold match_value.
    destruct (ident_eqb x x') eqn: E.
    - apply ident_eqb_eq in E; subst x'.
      destruct o.
      + rewrite Env.gss; auto.
        now apply match_find_var_det with (1:=Hmv).
      + destruct (InMembers_dec x xs AST.ident_eq) as [Hin'|Hni].
        * specialize (IHxs Hin' _ Findvars'). unfold match_value; auto.
        * revert Hni. clear. revert vs. induction xs.
          now simpl; rewrite Env.gempty.
          intros vs Hnm. simpl.
          apply NotInMembers_cons in Hnm as (Hnm & Hne).
          destruct vs; simpl; try rewrite Env.gempty; auto.
          specialize (IHxs vs Hnm).
          destruct o; simpl; auto.
          rewrite Env.gso; auto.
    - apply ident_eqb_neq in E.
      destruct Hin as [Eq|?].
      + inv Eq; now contradict E.
      + destruct o.
        * rewrite Env.gso; auto.
          apply IHxs; auto.
        * apply IHxs; auto.
  Qed.

  Lemma blockrep_field_offset:
    forall m ve flds b P,
      m |= blockrep ve flds b ** P ->
      forall x ty,
        In (x, ty) flds ->
        exists d, field_offset ge x flds = Errors.OK d
             /\ 0 <= d <= Ptrofs.max_unsigned.
  Proof.
    intros * Hm ? ? Hin.
    unfold blockrep in Hm.
    apply sepall_in in Hin.
    destruct Hin as [ws [xs [Hsplit Hin]]].
    rewrite Hin in Hm. clear Hsplit Hin.
    do 2 apply sep_proj1 in Hm. clear ws xs.
    destruct (field_offset ge x flds), (access_mode ty);
      try now contradict Hm.
    exists z; split; auto.
    eapply contains_no_overflow; eauto.
  Qed.

  Lemma blockrep_add:
    forall outb ve x v xs flds,
      ~ InMembers x xs ->
      map translate_param xs = flds ->
      blockrep ve flds outb -*>
      blockrep (Env.add x v ve) flds outb.
  Proof.
    intros * Hnin Eq; unfold blockrep.
    rewrite sepall_swapp; eauto.
    intros (x', t') Hx'.
    rewrite match_value_add; auto.
    apply In_InMembers in Hx'.
    intro Hxx'; subst x.
    apply Hnin.
    rewrite fst_InMembers, <-translate_param_fst, <-fst_InMembers; auto.
    now rewrite Eq.
  Qed.

End BlockRep.

Hint Resolve footprint_perm_blockrep footprint_decidable_blockrep.

Section SubRep.

  Variable ge : composite_env.

  Definition blockrep_of (id: ident) (b: block): massert :=
    match ge ! id with
    | Some co =>
      blockrep ge vempty (co_members co) b
    | None => sepfalse
    end.

  Definition subrep_inst '((_, (b, t)): ident * (block * Ctypes.type)): massert :=
    match t with
    | Tstruct id _ => blockrep_of id b
    | _ => sepfalse
    end.

  Definition subrep_inst_env (e: Clight.env) '((x, t): ident * Ctypes.type): massert :=
    match e ! x with
    | Some (b, Tstruct id _ as t') =>
      if type_eq t t' then blockrep_of id b else sepfalse
    | _ => sepfalse
    end.

  Definition subrep (f: method) (e: Clight.env) : massert :=
    sepall (subrep_inst_env e)
           (make_out_vars (instance_methods f)).

  Lemma subrep_eqv:
    forall f e,
      Permutation.Permutation (make_out_vars (instance_methods f))
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

  Definition range_inst '((_, (b, t)): ident * (block * Ctypes.type)) : massert :=
    range b 0 (Ctypes.sizeof ge t).

  Definition range_inst_env (e: Clight.env) (x: ident) : massert :=
    match e ! x with
    | Some (b, t) => range b 0 (Ctypes.sizeof ge t)
    | None => sepfalse
    end.

  Definition subrep_range (e: Clight.env) : massert :=
    sepall range_inst (PTree.elements e).

  Lemma subrep_range_eqv:
    forall e,
      subrep_range e <-*-> sepall (range_inst_env e) (map fst (PTree.elements e)).
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
    simpl; destruct t; auto.
    unfold blockrep_of; now destruct ge ! i.
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
    unfold blockrep_of; now destruct (ge ! i).
  Qed.

  Remark footprint_perm_subrep_inst:
    forall x b lo hi,
      footprint_perm (subrep_inst x) b lo hi.
  Proof.
    intros (x, (b, t)) b' lo hi.
    simpl; destruct t; auto; unfold blockrep_of; now destruct ge ! i.
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
      composite_env_consistent ge ->
      Forall (wf_struct ge) (map drop_block (PTree.elements e)) ->
      NoDupMembers (map snd (PTree.elements e)) ->
      subrep_range e <-*->
      sepall subrep_inst (PTree.elements e)
      ** (sepall subrep_inst (PTree.elements e) -* subrep_range e).
  Proof.
    unfold subrep_range.
    intros * Consistent Forall Nodup.
    split.
    2: now rewrite sep_unwand; auto.
    induction (PTree.elements e) as [|(x, (b, t))]; simpl in *.
    - rewrite <-hide_in_sepwand; auto.
      now rewrite <-sepemp_right.
    - inversion_clear Forall as [|? ? Hidco Forall']; subst;
        rename Forall' into Forall.
      destruct Hidco as (id & co & Ht & Hco & ? & ? & ?); simpl in Ht.
      inversion_clear Nodup as [|? ? ? Notin Nodup'].
      unfold blockrep_of.
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
        rewrite Hco.
        eapply blockrep_empty; eauto.
      + now apply disjoint_footprint_range_inst.
      + simpl; rewrite Hco.
        rewrite blockrep_empty; eauto.
        reflexivity.
      + apply subseteq_footprint_sepall.
        intros (x', (b', t')) Hin; simpl.
        assert (In (x', t') (map drop_block l))
          by (change (x', t') with (drop_block (x', (b', t'))); apply in_map; auto).
        eapply Forall_forall in Forall; eauto.
        simpl in Forall.
        destruct Forall as (id' & co' & Ht' & Hco' & ? & ? & ?).
        unfold blockrep_of.
        rewrite Ht', Hco'. simpl.
        rewrite Hco'.
        rewrite blockrep_empty; eauto.
        reflexivity.
  Qed.

  Lemma subrep_extract:
    forall f f' e m o c' P,
      M.MapsTo (o, f') c' (instance_methods f) ->
      m |= subrep f e ** P <->
      exists b co ws xs,
        e ! (prefix_out o f') = Some (b, type_of_inst (prefix_fun c' f'))
        /\ ge ! (prefix_fun c' f') = Some co
        /\ make_out_vars (instance_methods f) = ws ++ (prefix_out o f', type_of_inst (prefix_fun c' f')) :: xs
        /\ m |= blockrep ge vempty (co_members co) b
              ** sepall (subrep_inst_env e) (ws ++ xs)
              ** P.
  Proof.
    intros * Hin.
    unfold subrep.
    assert (In (prefix_out o f', type_of_inst (prefix_fun c' f'))
               (make_out_vars (instance_methods f))) as Hin'.
    { apply M.elements_1, setoid_in_key_elt in Hin.
      apply in_map with
      (f:=fun x => let '(o0, f0, cid) := x in (prefix_out o0 f0, type_of_inst (prefix_fun cid f0))) in Hin.
      unfold make_out_vars; auto.
    }
    clear Hin.
    split.
    - apply sepall_in in Hin'; destruct Hin' as (ws & xs & Hin & Heq).
      rewrite Heq, sep_assoc.
      intro Hmem.
      unfold subrep_inst_env at 1 in Hmem.
      destruct e ! (prefix_out o f') as [(oblk, t)|]; [|destruct Hmem; contradiction].
      destruct t; try (destruct Hmem; contradiction).
      destruct (type_eq (type_of_inst (prefix_fun c' f')) (Tstruct i a)) as [Eq|]; [|destruct Hmem; contradiction].
      unfold type_of_inst in Eq.
      inv Eq.
      unfold blockrep_of in *.
      destruct ge ! (prefix_fun c' f'); [|destruct Hmem; contradiction].
      exists oblk, c, ws, xs; intuition.
    - intros (oblk & c & ws' & xs' & He & Hge & Eq &?).
      (* rewrite Eq. *)
      rewrite sepall_breakout, sep_assoc; eauto.
      eapply sep_imp; eauto.
      unfold subrep_inst_env.
      rewrite He; unfold type_of_inst; rewrite type_eq_refl.
      unfold blockrep_of; rewrite Hge; auto.
  Qed.

End SubRep.

Lemma free_exists:
  forall ge e m P,
    let gcenv := Clight.genv_cenv ge in
    m |= subrep_range gcenv e ** P ->
    exists m',
      Mem.free_list m (blocks_of_env ge e) = Some m'
      /\ m' |= P.
Proof.
  Opaque sepconj.
  intros ge e.
  unfold subrep_range, blocks_of_env.
  induction (PTree.elements e) as [|(x,(b,ty))];
    simpl; intros * Hrep.
  - exists m; split; auto.
    now rewrite sepemp_left.
  - rewrite sep_assoc in Hrep.
    apply free_rule in Hrep as (m1 & Hfree & Hm1).
    rewrite Hfree.
    now apply IHl.
Qed.

Definition varsrep (f: method) (ve: venv) (le: temp_env) : massert :=
  pure (Forall (fun '((x, ty): ident * Ctypes.type) =>
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
    rewrite app_assoc, Permutation.Permutation_app_comm in Nodup.
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

Definition find_or_vundef (x: ident) (ve: venv) : val :=
  match Env.find x ve with
  | Some v => v
  | None => Vundef
  end.

Definition var_ptr (b: block) : val :=
  Vptr b Ptrofs.zero.

Section MatchStates.

  Variable ge : composite_env.

  Definition match_out
             (c: class) (f: method) (ve: venv) (le: temp_env)
             (outb_co: option (block * composite)) : massert :=
    case_out f
             sepemp
             (fun x _ => pure (le ! x = Some (find_or_vundef x ve)))
             (fun _ => match outb_co with
                    | Some (outb, outco) =>
                      pure (le ! out = Some (var_ptr outb))
                      ** pure (ge ! (prefix_fun c.(c_name) f.(m_name)) = Some outco)
                      ** blockrep ge ve outco.(co_members) outb
                    | None => sepfalse
                    end).

  Lemma match_out_add_prefix:
    forall c f ve le outb_co f' x v,
      match_out c f ve le outb_co <-*-> match_out c f ve (PTree.set (prefix f' x) v le) outb_co.
  Proof.
    intros.
    unfold match_out, case_out.
    destruct_list (m_out f) as (?,?) (?,?) ? : Hout; auto.
    - rewrite PTree.gso; auto.
      intro; subst.
      eapply (m_notprefixed (prefix f' x)); auto using prefixed.
      unfold meth_vars; rewrite Hout.
      rewrite 2 InMembers_app; right; right; constructor; auto.
    - cases.
      rewrite PTree.gso; auto.
      intro E; apply out_not_prefixed; rewrite E; auto using prefixed.
  Qed.

  Lemma match_out_nil:
    forall c f ve le outb_co,
      f.(m_out) = [] ->
      match_out c f ve le outb_co <-*-> sepemp.
  Proof.
    intros * Nil.
    unfold match_out, case_out; rewrite Nil; auto.
  Qed.

  Lemma match_out_singleton:
    forall c f ve le m outb_co x t P,
      f.(m_out) = [(x, t)] ->
      (m |= match_out c f ve le outb_co ** P <->
       m |= P /\ le ! x = Some (find_or_vundef x ve)).
  Proof.
    intros * Sing.
    unfold match_out, case_out; split; intros * H; rewrite Sing in *;
      rewrite sep_pure in *; tauto.
  Qed.

  Lemma match_out_notnil:
    forall c f ve le m outb_co P,
      (1 < length f.(m_out))%nat ->
      (m |= match_out c f ve le outb_co ** P <->
       exists outb outco,
         outb_co = Some (outb, outco)
         /\ m |= blockrep ge ve outco.(co_members) outb ** P
         /\ le ! out = Some (var_ptr outb)
         /\ ge ! (prefix_fun c.(c_name) f.(m_name)) = Some outco).
  Proof.
    intros * Length.
    unfold match_out, case_out; split; intros * H;
      destruct_list f.(m_out) as (?, ?) ? ?;
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

  Definition prefix_out_env (e: Clight.env) : Prop :=
    forall x b t,
      e ! x = Some (b, t) ->
      exists o f, x = prefix_out o f.

  Definition bounded_struct_of_class (c: class) (sofs: ptrofs) : Prop :=
    struct_in_bounds ge 0 Ptrofs.max_unsigned (Ptrofs.unsigned sofs) (make_members c).

  Lemma bounded_struct_of_class_ge0:
    forall c sofs,
      bounded_struct_of_class c sofs ->
      0 <= Ptrofs.unsigned sofs.
  Proof.
    unfold bounded_struct_of_class, struct_in_bounds; tauto.
  Qed.
  Hint Resolve bounded_struct_of_class_ge0.

  Definition match_self (p: program) (c: class) (me: menv) (le: Clight.temp_env) (sb: block) (sofs: ptrofs) : massert :=
    pure (le ! self = Some (Vptr sb sofs))
    ** pure (bounded_struct_of_class c sofs)
    ** staterep ge p c.(c_name) me sb (Ptrofs.unsigned sofs).

  Lemma match_self_conj:
    forall m p c me le sb sofs P,
      m |= match_self p c me le sb sofs ** P
      <-> m |= staterep ge p c.(c_name) me sb (Ptrofs.unsigned sofs) ** P
        /\ le ! self = Some (Vptr sb sofs)
        /\ bounded_struct_of_class c sofs.
  Proof.
    unfold match_self; split; intros * H.
    - repeat rewrite sep_assoc in H; repeat rewrite sep_pure in H; tauto.
    - repeat rewrite sep_assoc; repeat rewrite sep_pure; tauto.
  Qed.

  Definition match_outs (f: method) (e: Clight.env) : massert :=
    pure (prefix_out_env e)
    ** subrep ge f e
    ** (subrep ge f e -* subrep_range ge e).

  Definition match_states
             (p: program) (c: class) (f: method) '((me, ve): menv * venv)
             '((e, le): Clight.env * Clight.temp_env)
             (sb: block) (sofs: ptrofs) (outb_co: option (block * composite)): massert :=
    pure (wt_state p me ve c (meth_vars f))
    ** match_self p c me le sb sofs
    ** match_out c f ve le outb_co
    ** match_outs f e
    ** varsrep f ve le.

  Lemma match_states_conj:
    forall p c f me ve e le m sb sofs outb_co P,
      m |= match_states p c f (me, ve) (e, le) sb sofs outb_co ** P <->
      m |= staterep ge p c.(c_name) me sb (Ptrofs.unsigned sofs)
           ** match_out c f ve le outb_co
           ** subrep ge f e
           ** (subrep ge f e -* subrep_range ge e)
           ** varsrep f ve le
           ** P
      /\ bounded_struct_of_class c sofs
      /\ wt_state p me ve c (meth_vars f)
      /\ le ! self = Some (Vptr sb sofs)
      /\ prefix_out_env e.
  Proof.
    unfold match_states, match_self, match_outs; split; intros * H.
    - repeat rewrite sep_assoc in H; repeat rewrite sep_pure in H.
      rewrite sep_swap3, sep_pure, sep_swap in H; tauto.
    - repeat rewrite sep_assoc; repeat rewrite sep_pure.
      rewrite sep_swap3, sep_pure, sep_swap; tauto.
  Qed.

  Lemma match_states_wt_state:
    forall p c f me ve e le m sb sofs outb_co P,
      m |= match_states p c f (me, ve) (e, le) sb sofs outb_co ** P ->
      wt_state p me ve c (meth_vars f).
  Proof.
    setoid_rewrite match_states_conj; tauto.
  Qed.

  Section MatchStatesPreservation.

    (*****************************************************************)
    (** various basic 'Hoare triples' for memory assignments        **)
    (*****************************************************************)

    Variable
      (** Obc program  *)
      (prog     : program)

      (** Obc class *)
      (ownerid  : ident)     (owner  : class)     (prog' : program)

      (** Obc method *)
      (callerid : ident)     (caller : method)

      (** Obc state *)
      (me       : menv)      (ve     : venv)

      (** Clight state *)
      (m        : Mem.mem)   (e      : Clight.env) (le   : temp_env)

      (** Clight self structure *)
      (sb       : block)     (sofs   : ptrofs)

      (** Clight output structure *)
      (outb_co  : option (block * composite))

      (** frame *)
      (P        : massert).

    Hypothesis (Findcl      : find_class ownerid prog = Some (owner, prog'))
               (Findmth     : find_method callerid owner.(c_methods) = Some caller)
               (OutputMatch : forall outco, (1 < length (m_out caller))%nat ->
                                       ge ! (prefix_fun (c_name owner) (m_name caller)) = Some outco ->
                                       map translate_param caller.(m_out) = outco.(co_members))
               (Hmem        : m |= match_states prog owner caller (me, ve) (e, le) sb sofs outb_co
                                   ** P).

    Variable (v : val) (x : ident) (ty : type).

    Hypothesis (WTv : wt_val v ty).

    Lemma match_out_assign_gt1_mem:
      forall m1 P1,
        In (x, ty) caller.(m_out) ->
        (1 < length (m_out caller))%nat ->
        m1 |= match_out owner caller ve le outb_co ** P1 ->
        exists m2 b co d,
          outb_co = Some (b, co)
          /\ field_offset ge x (co_members co) = Errors.OK d
          /\ Clight.assign_loc ge (cltype ty) m1 b (Ptrofs.repr d) v m2
          /\ m2 |= match_out owner caller (Env.add x v ve) le outb_co ** P1.
    Proof.
      clear Hmem; intros * Hin Len Hmem.
      apply match_out_notnil in Hmem as (b & co & Hout & Hrep &?& Hco); auto.
      apply in_map with (f:=translate_param) in Hin.
      erewrite OutputMatch in Hin; eauto.
      pose proof (m_nodupvars caller) as Nodup.
      edestruct blockrep_field_offset as (d & Hofs & ?); eauto.

      (* get the updated memory *)
      apply sepall_in in Hin as [ws [ys [Hys Heq]]].
      unfold blockrep in Hrep.
      Local Opaque sepconj match_states.
      rewrite Heq in Hrep; simpl in *.
      rewrite Hofs, cltype_access_by_value, sep_assoc in Hrep.
      eapply Separation.storev_rule' with (v:=v) in Hrep as (m' & ? & Hrep); eauto with mem.
      exists m', b, co, d; intuition; eauto using assign_loc.
      rewrite match_out_notnil; auto.
      exists b, co; split; intuition.
      unfold blockrep.
      rewrite Heq, Hofs, cltype_access_by_value, sep_assoc.
      eapply sep_imp; eauto.
      - unfold hasvalue, match_value; simpl.
        rewrite Env.gss.
        now rewrite <-wt_val_load_result.
      - apply sep_imp'; auto.
        do 2 apply NoDupMembers_app_r in Nodup.
        rewrite fst_NoDupMembers, <-translate_param_fst, <-fst_NoDupMembers in Nodup; auto.
        erewrite OutputMatch, Hys in Nodup; auto.
        apply NoDupMembers_app_cons in Nodup.
        destruct Nodup as (Notin & Nodup).
        rewrite sepall_swapp; eauto.
        intros (x' & t') Hin.
        rewrite match_value_add; auto.
        intro; subst x'.
        apply Notin.
        eapply In_InMembers; eauto.
    Qed.

    Lemma match_out_assign_singleton_mem:
      m_out caller = [(x, ty)] ->
      match_out owner caller ve le outb_co -*>
      match_out owner caller (Env.add x v ve) (PTree.set x v le) outb_co.
    Proof.
      intros Eq.
      unfold match_out, case_out; rewrite Eq.
      unfold find_or_vundef; now rewrite PTree.gss, Env.gss.
    Qed.

    Lemma match_out_assign_var_mem:
      forall m1 P1,
        ~ InMembers x (m_out caller) ->
        In (x, ty) (meth_vars caller) ->
        m1 |= match_out owner caller ve le outb_co ** P1 ->
        match_out owner caller ve le outb_co -*>
        match_out owner caller (Env.add x v ve) (PTree.set x v le) outb_co.
    Proof.
      clear Hmem; intros * Hnin Hin Hmem.
      unfold match_out, case_out in *; destruct_list (m_out caller) as (?, ?) (?, ?) ? : Hout; auto.
      - apply pure_imp.
        unfold find_or_vundef.
        assert (i <> x) by (intro; subst; apply Hnin; constructor; auto).
        now rewrite PTree.gso, Env.gso.
      - destruct outb_co as [(outb, outco)|]; auto.
        repeat apply sep_imp'; auto.
        + apply pure_imp.
          rewrite PTree.gso; auto.
          intro; subst; apply (m_notreserved out caller).
          * right; constructor; auto.
          * eapply In_InMembers; eauto.
        + rewrite 2 sep_assoc, 2 sep_pure in Hmem.
          destruct Hmem as (?&?&?).
          eapply blockrep_add; eauto.
          apply OutputMatch; auto; simpl; omega.
    Qed.

    Lemma match_states_assign_state_mem:
      In (x, ty) owner.(c_mems) ->
      exists m' d,
        field_offset ge x (make_members owner) = Errors.OK d
        /\ Clight.assign_loc ge (cltype ty) m sb (Ptrofs.repr (Ptrofs.unsigned sofs + d)) v m'
        /\ m' |= match_states prog owner caller (add_val x v me, ve) (e, le) sb sofs outb_co
                ** P.
    Proof.
      intros Hin.
      apply match_states_conj in Hmem as (Hmem & ?&?&?).
      rewrite staterep_skip in Hmem; eauto.
      edestruct staterep_field_offset as (d & Hofs &?); eauto.

      (* get the updated memory *)
      pose proof Hin.
      apply sepall_in in Hin as [ws [ys [Hys Heq]]].
      simpl staterep in Hmem.
      unfold staterep_mems in Hmem.
      rewrite ident_eqb_refl, Heq, Hofs, 2 sep_assoc in Hmem.
      eapply Separation.storev_rule' with (v:=v) in Hmem as (m' & ? & Hmem);
        eauto with mem.
      exists m', d; intuition; eauto using assign_loc.
      apply match_states_conj; intuition; eauto.
      rewrite staterep_skip; eauto.
      simpl staterep.
      unfold staterep_mems.
      rewrite ident_eqb_refl, Heq, Hofs, 2 sep_assoc.
      eapply sep_imp; eauto.
      - unfold hasvalue'.
        unfold match_value; simpl.
        rewrite Env.gss.
        now rewrite <-wt_val_load_result.
      - repeat apply sep_imp'; auto.
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

  End MatchStatesPreservation.

End MatchStates.


Section FunctionEntry.

  (*****************************************************************)
  (** results about allocation of the environment and temporary   **)
  (** environment at function entry                               **)
  (*****************************************************************)

  (* Variable ge: genv. *)
  (* Let gcenv := Clight.genv_cenv ge. *)

  (* Hypothesis Consistent : composite_env_consistent gcenv. *)

  Remark bind_parameter_temps_exists:
    forall xs s ts o to ys vs sptr optr,
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
        /\ Forall (fun '(x, ty) =>
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
          apply bind_parameter_temps_cons; auto.
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
    forall xs s ts ys vs sptr,
      NoDupMembers xs ->
      ~ InMembers s xs ->
      ~ InMembers s ys ->
      length xs = length vs ->
      exists le',
        bind_parameter_temps ((s, ts) :: xs)
                             (sptr :: vs)
                             (create_undef_temps ys) = Some le'
        /\ Forall (fun '(x, ty) =>
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
          apply bind_parameter_temps_cons; auto.
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

  Remark alloc_mem_vars:
    forall ge vars e m e' m' P,
      let gcenv := Clight.genv_cenv ge in
      m |= P ->
      NoDupMembers vars ->
      Forall (fun xt => sizeof gcenv (snd xt) <= Ptrofs.max_unsigned) vars ->
      alloc_variables ge e m vars e' m' ->
      m' |= sepall (range_inst_env gcenv e') (var_names vars) ** P.
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

  Lemma alloc_result:
    forall ge f m P,
      let vars := instance_methods f in
      let gcenv := Clight.genv_cenv ge in
      composite_env_consistent ge ->
      Forall (fun xt => sizeof ge (snd xt) <= Ptrofs.max_unsigned /\ wf_struct gcenv xt)
             (make_out_vars vars) ->
      NoDupMembers (make_out_vars vars) ->
      m |= P ->
      exists e' m',
        alloc_variables ge empty_env m (make_out_vars vars) e' m'
        /\ prefix_out_env e'
        /\ m' |= subrep gcenv f e'
               ** (subrep gcenv f e' -* subrep_range gcenv e')
               ** P.
  Proof.
    intros * Consistent Hforall Nodup Hrep; subst.
    rewrite <-Forall_Forall' in Hforall; destruct Hforall.
    pose proof (alloc_exists ge _ empty_env m Nodup) as (e' & m' & Alloc).
    eapply alloc_mem_vars in Hrep; eauto.
    pose proof Alloc as Perm.
    apply alloc_permutation in Perm; auto.
    exists e', m'; split; [auto|split].
    - intros ??? Hget.
      apply PTree.elements_correct in Hget.
      apply in_map with (f:=drop_block) in Hget.
      apply Permutation.Permutation_sym in Perm.
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
      rewrite range_wand_equiv in Hrep; eauto.
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

  (*****************************************************************)
  (** 'Hoare triple' for function entry, depending on the number  **)
  (** of outputs (and inputs, consequently):                      **)
  (**   0 and 1: no 'out' pointer parameter, we only need         **)
  (**            staterep for the sub-state, and we get           **)
  (**            match_states in the callee                       **)
  (**   1 < n  : 'out' pointer parameter, we need both            **)
  (**            staterep for the sub-state and blockrep for the  **)
  (**            output structure, we get match_states in the     **)
  (**            callee                                           **)
  (*****************************************************************)

  Variable (main_node  : ident)
           (prog       : program)
           (tprog      : Clight.program)
           (do_sync    : bool)
           (all_public : bool).
  Let tge              := Clight.globalenv tprog.
  Let gcenv            := Clight.genv_cenv tge.

  Hypothesis (TRANSL : translate do_sync all_public main_node prog = Errors.OK tprog)
             (WT     : wt_program prog).

  Lemma function_entry_match_states:
    forall cid c prog' fid f fd me vs,
      method_spec c f prog fd ->
      find_class cid prog = Some (c, prog') ->
      find_method fid c.(c_methods) = Some f ->
      Datatypes.length (m_in f) = Datatypes.length vs ->
      wt_mem me prog c ->
      Forall2 (fun v xt => wt_val v (snd xt)) vs (m_in f) ->
      case_out f
               (forall m sb sofs P,
                   bounded_struct_of_class gcenv c sofs ->
                   m |= staterep gcenv prog cid me sb (Ptrofs.unsigned sofs) ** P ->
                   exists e_f le_f m_f,
                     function_entry2 tge fd (Vptr sb sofs :: vs) m e_f le_f m_f
                     /\ m_f |= match_states gcenv prog c f (me, Env.adds (map fst f.(m_in)) vs vempty) (e_f, le_f) sb sofs None
                              ** P)
               (fun _ _ =>
                  forall m sb sofs P,
                    bounded_struct_of_class gcenv c sofs ->
                    m |= staterep gcenv prog cid me sb (Ptrofs.unsigned sofs) ** P ->
                    exists e_f le_f m_f,
                      function_entry2 tge fd (Vptr sb sofs :: vs) m e_f le_f m_f
                      /\ m_f |= match_states gcenv prog c f (me, Env.adds (map fst f.(m_in)) vs vempty) (e_f, le_f) sb sofs None
                               ** P)
               (fun _ =>
                  forall m sb sofs instb instco P,
                   bounded_struct_of_class gcenv c sofs ->
                   m |= staterep gcenv prog cid me sb (Ptrofs.unsigned sofs)
                        ** blockrep gcenv vempty (co_members instco) instb
                        ** P ->
                   gcenv ! (prefix_fun cid fid) = Some instco ->
                   exists e_f le_f m_f,
                     function_entry2 tge fd (Vptr sb sofs :: var_ptr instb :: vs) m e_f le_f m_f
                     /\ m_f |= match_states gcenv prog c f (me, Env.adds (map fst f.(m_in)) vs vempty) (e_f, le_f) sb sofs (Some (instb, instco))
                              ** P).
  Proof.
    intros * Spec Findcl Findmth Len WTmem WTvs.

    assert (NoDupMembers (make_out_vars (instance_methods f)))
      by (eapply NoDupMembers_make_out_vars; eauto; eapply wt_program_find_class; eauto).
    assert (Forall (fun xt => sizeof tge (snd xt) <= Ptrofs.max_unsigned /\ wf_struct gcenv xt)
                   (make_out_vars (instance_methods f)))
      by (eapply instance_methods_caract; eauto).
    assert (Datatypes.length (map translate_param (m_in f)) = Datatypes.length vs)
      by (rewrite map_length; auto).
    assert (wt_state prog me vempty c (meth_vars f)) by (split; eauto).
    assert (NoDup (map fst (m_in f))) by (apply fst_NoDupMembers, m_nodupin).
    assert (Forall2 (fun y xt => In (y, snd xt) (meth_vars f)) (map fst (m_in f)) (m_in f))
      by (apply Forall2_map_1, Forall2_same, Forall_forall; intros (x, t) Hin; simpl; apply in_app; auto).

    unfold method_spec, case_out in *.
    subst gcenv tge.
    destruct_list (m_out f) as (a,ta) (?,?) ? : Hout; simpl in Spec;
      destruct Spec as (P_f &?&?&?& T_f &?&?&?&?); intros * ? Hmem; try intros Hinstco.

    (* no output *)
    - (* get the allocated environment and memory *)
      edestruct alloc_result as (e_f & m_f &?&?&?); eauto.

      (* get the temporaries *)
      edestruct
        (bind_parameter_temps_exists_noout (map translate_param f.(m_in))
                                           self (type_of_inst_p (c_name c))
                                           (make_out_temps (instance_methods_temp prog f)
                                                           ++ map translate_param (m_vars f))
                                           vs (Vptr sb sofs)) as (le_f & Bind & Vars); eauto.
      assert (le_f ! self = Some (Vptr sb sofs))
        by (eapply bind_parameter_temps_implies in Bind; eauto).
      setoid_rewrite <-P_f in Bind.

      exists e_f, le_f, m_f; split.
      + constructor; auto; try congruence.
      + apply match_states_conj; intuition; eauto using m_nodupvars.
        erewrite find_class_name; eauto.
        rewrite sep_swap, match_out_nil, <-sepemp_left, sep_swap, sep_swap23,
        sep_swap34, sep_swap23, sep_swap; auto.
        apply sep_pure; split; auto.
        rewrite map_app.
        rewrite translate_param_fst in Vars.
        rewrite 2 Forall_app in Vars; rewrite Forall_app; tauto.

    (* one output *)
    - assert (self <> a)
        by (intro; subst; eapply (m_notreserved self); auto;
            do 2 setoid_rewrite InMembers_app; rewrite Hout;
            right; right; constructor; auto).

      (* get the allocated environment and memory *)
      edestruct alloc_result as (e_f & m_f &?&?&?); eauto.

      (* get the temporaries (+ the local return temporary) *)
      edestruct
        (bind_parameter_temps_exists_noout (map translate_param f.(m_in))
                                           self (type_of_inst_p (c_name c))
                                           ((a, cltype ta) :: make_out_temps (instance_methods_temp prog f)
                                                           ++ map translate_param (m_vars f))
                                           vs (Vptr sb sofs)) as (le_f & Bind & Vars);
        eauto; try eapply NotInMembers_cons; eauto.
      assert (le_f ! a = Some (find_or_vundef a (Env.adds (map fst (m_in f)) vs vempty))).
      { assert (~ In a (map fst (m_in f))).
        { rewrite <-fst_InMembers.
          pose proof (m_nodupvars f) as Nodup.
          intro; eapply NoDupMembers_app_InMembers; eauto.
          apply InMembers_app; rewrite Hout; right; constructor; auto.
        }
        eapply bind_parameter_temps_conservation; eauto.
        - eapply NotInMembers_cons; split; eauto.
          rewrite fst_InMembers, translate_param_fst; auto.
        - simpl; rewrite PTree.gss.
          unfold find_or_vundef; rewrite Env.gsso, Env.gempty; auto.
      }
      assert (le_f ! self = Some (Vptr sb sofs))
        by (eapply bind_parameter_temps_implies in Bind; eauto).
      setoid_rewrite <-P_f in Bind.

      exists e_f, le_f, m_f; split.
      + constructor; auto; congruence.
      + apply match_states_conj; intuition; eauto using m_nodupvars.
        erewrite find_class_name; eauto.
        rewrite sep_swap, match_out_singleton, sep_swap, sep_swap23,
        sep_swap34, sep_swap23, sep_swap; eauto.
        setoid_rewrite sep_pure; split; [split|]; auto.
        rewrite map_app.
        rewrite translate_param_fst in Vars.
        rewrite Forall_app, Forall_cons2, Forall_app in Vars.
        rewrite Forall_app; tauto.

    (* multiple outputs *)
    - assert (1 < Datatypes.length (m_out f))%nat
        by (rewrite Hout; simpl; omega).

      (* get the allocated environment and memory *)
      edestruct alloc_result as (e_f & m_f &?&?&?); eauto.

      (* get the temporaries *)
      edestruct
        (bind_parameter_temps_exists (map translate_param f.(m_in)) self (type_of_inst_p (c_name c))
                                     out (type_of_inst_p (prefix_fun (c_name c) (m_name f)))
                                     (make_out_temps (instance_methods_temp prog f)
                                                     ++ map translate_param f.(m_vars))
                                     vs (Vptr sb sofs) (var_ptr instb)) as (le_f & Bind & Vars); eauto.
      assert (le_f ! self = Some (Vptr sb sofs) /\ le_f ! out = Some (var_ptr instb)) as (?&?)
          by (eapply bind_parameter_temps_implies_two in Bind; eauto).
      setoid_rewrite <-P_f in Bind; setoid_rewrite <-T_f in Bind.

      exists e_f, le_f, m_f; split.
      + constructor; auto; congruence.
      + apply match_states_conj; intuition; eauto using m_nodupvars.
        erewrite find_class_name; eauto.
        erewrite <-(find_class_name cid), <-(find_method_name fid) in Hinstco; eauto.
        rewrite sep_swap, match_out_notnil; auto.
        exists instb, instco; intuition; auto.
        rewrite sep_swap23, sep_swap, sep_swap34, sep_swap23, sep_swap34,
        sep_swap45, sep_swap34, sep_swap23, sep_swap.
        setoid_rewrite sep_pure; split.
        * rewrite map_app.
          rewrite translate_param_fst in Vars.
          rewrite 2 Forall_app in Vars.
          rewrite Forall_app; tauto.
        * eapply sep_imp; eauto.
          repeat apply sep_imp'; auto.
          rewrite blockrep_nodup; eauto.
          erewrite <-output_match; eauto.
          rewrite translate_param_fst.
          eapply NoDup_app_weaken.
          rewrite Permutation.Permutation_app_comm, NoDup_swap, <-2 map_app.
          apply fst_NoDupMembers, m_nodupvars.
  Qed.

End FunctionEntry.

Hint Resolve match_states_wt_state bounded_struct_of_class_ge0.
