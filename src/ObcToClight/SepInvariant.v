From compcert Require Import common.Separation.
From compcert Require Import common.Values.
From compcert Require Import common.Memdata.
From compcert Require Import common.Memory.
From compcert Require Import common.Globalenvs.
From compcert Require common.Errors.
From compcert Require Import cfrontend.Ctypes.
From compcert Require Import cfrontend.Clight.
From compcert Require Import lib.Maps.
From compcert Require Import lib.Coqlib.
From compcert Require Import lib.Integers.

From Velus Require Import Common.
From Velus Require Import Common.CommonTyping.
From Velus Require Import Common.CompCertLib.
From Velus Require Import Ident.
From Velus Require Import Environment.
From Velus Require Import VelusMemory.

From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import ZArith.BinInt.

(* From Coq Require Import Program.Tactics. *)

From Velus Require Import ObcToClight.MoreSeparation.
From Velus Require Import ObcToClight.Generation.
From Velus Require Import ObcToClight.GenerationProperties.
From Velus Require Import ObcToClight.Interface.

Import OpAux.
Import ComTyp.

Import Obc.Syn.
Import Obc.Sem.
Import Obc.Typ.

Open Scope list.
Open Scope sep_scope.
Open Scope Z.

Definition match_value (ov: option value) (v: cvalue) :=
  or_default_with True (fun v' => v = value_to_cvalue v') ov.

Definition match_var (ve: venv) (le: temp_env) (x: ident) : Prop :=
  or_default_with False (match_value (Env.find x ve)) (le ! x).

Section Staterep.
  Variable ge : composite_env.

  Definition staterep_mems (cls: class) (me: menv) (b: block) (ofs: Z) '((x, ty): ident * type) :=
    match field_offset ge x (make_members cls) with
    | Errors.OK d =>
	    contains_w (type_to_chunk ty) b (ofs + fst d) (match_value (find_val x me))
    | Errors.Error _ => sepfalse
    end.

  Definition find_class_dec (f: ident) (p: program) : option { cl_p' | find_class f p = Some cl_p'}.
  Proof.
    destruct (find_class f p) as [[c p']|].
    - left; exists (c, p'); auto.
    - right.
  Defined.

  Lemma find_class_dec_spec_None:
    forall f p,
      find_class_dec f p = None <-> find_class f p = None.
  Proof.
    intros.
    unfold find_class_dec.
    destruct (find_class f p) as [[]|]; split; auto; discriminate.
  Qed.

  Definition staterep
             (p: program) (clsnm: ident) (me: menv) (b: block) (ofs: Z): massert.
  Proof.
    refine (@Wf.Fix _ (fun x y => ltsuffix_prog (fst x) (fst y)) _ (fun _ => massert)
                    (fun '(p, (clsnm, me, ofs)) staterep =>
                       match find_class_dec clsnm p with
                       | None => sepfalse
                       | Some (exist _ cl_p' E) =>
                         let (cl ,p') := cl_p' in
                         sepall (staterep_mems cl me b ofs) cl.(c_mems)
                         **
                         sepall (fun '((i, c): ident * ident) =>
                                   match field_offset ge i (make_members cl) with
                                   | Errors.OK d =>
                                     staterep (snd cl_p', (c, instance_match i me, ofs + fst d)) _
                                   | Errors.Error _ => sepfalse
                                   end) cl.(c_objs)
                       end) (p, (clsnm, me, ofs))).
    - pose proof ltsuffix_prog_wf as WF.
      eapply Wf.measure_wf in WF; eauto.
    - destruct cl_p'; simpl; eapply find_unit_ltsuffix_prog; eauto.
  Defined.

  Definition staterep_objs
             (p: program) (cls: class) (me: menv) (b: block) (ofs: Z) '((i, c): ident * ident) : massert :=
    match field_offset ge i (make_members cls) with
    | Errors.OK d =>
      staterep p c (instance_match i me) b (ofs + fst d)
    | Errors.Error _ => sepfalse
    end.

  Lemma staterep_def:
    forall p clsnm me b ofs,
      staterep p clsnm me b ofs =
      or_default_with sepfalse
                      (fun '(cl, p') =>
                         sepall (staterep_mems cl me b ofs) cl.(c_mems)
                         ** sepall (staterep_objs p' cl me b ofs) cl.(c_objs))
                      (find_class clsnm p).
  Proof.
    intros; unfold or_default_with, staterep_objs, staterep at 1.
    rewrite Fix_eq.
    - pose proof (find_class_dec_spec_None clsnm p) as E.
      destruct (find_class_dec clsnm p) as [[[] ->]|].
      + f_equal.
      + destruct E as [->]; auto.
    - intros (p' &(( clsnm' & me')& ofs')) ???.
      destruct (find_class_dec clsnm' p') as [[[]]|]; auto.
      f_equal.
      induction (c_objs c) as [|[]]; simpl; auto.
      f_equal; auto.
      cases.
  Qed.

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

  Lemma staterep_chained_in_objs:
    forall p f cl p' i g me b ofs,
      wt_program p ->
      find_class f p = Some (cl, p') ->
      In (i, g) cl.(c_objs) ->
      staterep p' g me b ofs <-*-> staterep p g me b ofs.
  Proof.
    intros * WTp Find Hin.
    rewrite 2 staterep_def.
    erewrite wt_program_find_class_chained_in_objs; eauto.
  Qed.

  Lemma decidable_footprint_staterep:
    forall p clsnm me b ofs,
      decidable_footprint (staterep p clsnm me b ofs).
  Proof.
    induction p using program_ind.
    setoid_rewrite staterep_def; intros.
    destruct (find_class clsnm p) as [[]|] eqn: Find; simpl; auto with sep.
    apply decidable_footprint_sepconj;
      apply decidable_footprint_sepall;
      intros (x,?); simpl; cases; eauto with sep.
  Qed.

  Lemma footprint_perm_staterep:
    forall p clsnm me b ofs b' lo hi,
      footprint_perm_w (staterep p clsnm me b ofs) b' lo hi.
  Proof.
    induction p using program_ind.
    setoid_rewrite staterep_def; intros.
    destruct (find_class clsnm p) as [[]|] eqn: Find; simpl; auto with sep.
    apply footprint_perm_sepconj;
      apply footprint_perm_sepall;
      intros (x,?); simpl; cases; eauto with sep.
  Qed.

End Staterep.

(** The struct_in_bounds predicate.

    TODO: add explanatory text. *)

Section StructInBounds.
  Variable env : composite_env.
  Hypothesis env_consistent: composite_env_consistent env.

  Definition struct_in_bounds (min max ofs: Z) (flds: Ctypes.members) :=
    min <= ofs /\ ofs + sizeof_struct env flds <= max.

  Lemma struct_in_bounds_sizeof:
    forall id co,
      env!id = Some co ->
      struct_in_bounds 0 (sizeof_struct env (co_members co)) 0 (co_members co).
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
      struct_in_bounds min max ofs (mk_members flds) ->
      field_offset env id (mk_members flds) = Errors.OK d ->
      min <= ofs + fst d <= max.
  Proof.
    unfold struct_in_bounds.
    intros * (Hmin & Hmax) Hfo.
    destruct (field_offset_type _ _ _ _ Hfo) as (ty & Hft). destruct d.
    pose proof (field_offset_mk_members _ _ _ _ _ Hfo); subst.
    destruct (field_offset_in_range _ _ _ _ _ Hfo Hft) as (H0d & Hsize).
    simpl in *.
    split; auto; try lia.
    etransitivity; eauto.
    apply Z.add_le_mono; auto with zarith.
    apply Z.le_trans with (2:=Hsize).
    rewrite Zplus_0_r_reverse at 1.
    auto using (Z.ge_le _ _ (sizeof_pos env ty)) with zarith.
  Qed.

  Lemma struct_in_struct_in_bounds:
    forall min max ofs flds id sid d co a,
      struct_in_bounds min max ofs (mk_members flds) ->
      field_offset env id (mk_members flds) = Errors.OK d ->
      field_type id (mk_members flds) = Errors.OK (Tstruct sid a) ->
      env!sid = Some co ->
      co_su co = Struct ->
      struct_in_bounds min max (ofs + fst d) (co_members co).
  Proof.
    unfold struct_in_bounds.
    intros * (Hmin & Hmax) Hfo Hft Henv Hsu. destruct d.
    pose proof (field_offset_mk_members _ _ _ _ _ Hfo); subst.
    apply field_offset_in_range with (1:=Hfo) in Hft.
    destruct Hft as (Hd0 & Hsizeof).
    simpl in *. split; try lia.
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
             /\ NoDup (map name_member (co_members co))
             /\ co.(co_sizeof) <= Ptrofs.max_unsigned).

  Lemma struct_in_struct_in_bounds':
    forall min max ofs clsid cls o c cls' prog' prog'',
      wt_program prog ->
      find_class clsid prog = Some (cls, prog') ->
      struct_in_bounds gcenv min max ofs (make_members cls) ->
      In (o, c) cls.(c_objs) ->
      find_class c prog' = Some (cls', prog'') ->
      exists d, field_offset gcenv o (make_members cls) = Errors.OK d
           /\ struct_in_bounds gcenv min max (ofs + fst d) (make_members cls').
  Proof.
    intros * WTp Hfc Hsb Hin Hfc'.
    destruct (c_objs_field_offset gcenv _ _ _ Hin) as (d & Hfo).
    exists d; split; auto.
    destruct (make_members_co _ _ _ Hfc)
      as (cls_co & Hg & Hsu & Hmem & Hattr & Hndup).
    rewrite <-Hmem in *.
    eapply wt_program_find_unit_chained with (1:=WTp) (2:=Hfc) in Hfc'.
    destruct (make_members_co _ _ _ Hfc')
      as (cls'_co & Hg' & Hsu' & Hmem' & Hattr' & Hndup').
    rewrite <-Hmem' in *. destruct d.
    pose proof (field_offset_type _ _ _ _ Hfo) as (ty & Hty).
    eapply struct_in_struct_in_bounds with (a:=noattr); eauto.
    2:setoid_rewrite <-Hmem; eauto. rewrite Hmem in Hsb; auto.
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

  Hint Resolve Z.divide_trans : zarith.

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
    induction prog as [? IH] using program_ind; intros ??? Halign.
    apply not_None_is_Some in Hfind as ((cls', prog'') & Hfind).

    (* Exploit make_members_co for the named class. *)
    destruct (make_members_co _ _ _ Hfind)
      as (co & Hg & Hsu & Hmem & Hattr & Hndup & ?).

    (* Develop some facts about member alignment. *)
    pose proof (co_members_alignof _ _ _ Hmem (gcenv_consistent _ _ Hg) Hattr)
      as Hcoal.
    rewrite Hmem in Hcoal. unfold make_members in Hcoal.
    apply Forall_map, Forall_app in Hcoal as [Hcoal1 Hcoal2].
    simpl in Halign. rewrite Hg, align_noattr in Halign.
    assert (Hndup':=Hndup). rewrite Hmem in Hndup'.

    (* Massage the goal into two parallel parts: for locals and instances. *)
    rewrite staterep_def, Hfind; simpl.
    unfold staterep_mems, staterep_objs.
    rewrite Hg, <-Hmem.
    erewrite split_range_fields. 2-6:eauto.
    rewrite sepall_app.
    apply sep_imp'.

    - (* Divide up the memory sub-block for cls.(c_mems). *)
      pose proof (field_translate_mem_type _ _ _ _ Hfind) as Htype.
      rewrite Hmem; unfold make_members.
      rewrite sepall_map. apply sepall_weakenp.
      intros (?&?) Hin; simpl.
      destruct (field_offset gcenv _ _) eqn:Hfo; auto.
      setoid_rewrite Env.gempty.
      rewrite sizeof_translate_type_chunk; eauto.
      apply range_contains'; auto with mem. destruct p0.
      eapply field_offset_aligned' in Hfo; eauto.
      apply Z.divide_add_r; eauto using Z.divide_trans with clight.
      rewrite Forall_map in Hcoal1. eapply Forall_forall in Hcoal1; eauto; simpl in *.
      etransitivity; eauto with zarith clight.

    - (* Divide up the memory sub-block for cls.(c_objs). *)
      pose proof (field_translate_obj_type _ _ _ _ Hfind) as Htype.
      rewrite <-Hmem in Htype.
      edestruct wt_program_find_unit as [WTc WTp']; eauto.
      destruct WTc as [Ho Hm]; clear Hm.
      rewrite Hmem; unfold make_members.
      rewrite sepall_map. apply sepall_weakenp.
      intros (?&?) Hin; simpl.
      destruct (field_offset gcenv _ _) eqn:Hfo; auto.
      rewrite instance_match_empty.
      specialize (Htype i i0 Hin).
      assert (forall clsnm cls prog',
                 find_class clsnm prog'' = Some (cls, prog') ->
                 exists co : composite,
                   gcenv ! clsnm = Some co /\
                     co_su co = Struct /\
                     co_members co = make_members cls /\
                     attr_alignas (co_attr co) = None /\
                     NoDup (map name_member (co_members co)) /\
                     co_sizeof co <= Ptrofs.max_unsigned) as make_members_co'.
      { intros; eapply make_members_co.
        eapply wt_program_find_unit_chained; eauto.
      }
      eapply Forall_forall in Ho; eauto.
      assert (Hfind':=Ho). apply not_None_is_Some in Hfind' as ((c' & prog''') & Hfind').
      destruct (make_members_co' _ _ _ Hfind')
        as (co' & Hg' & Hsu' & Hmem' & Hattr' & Hnodup').
      simpl in *. rewrite Hg'.
      eapply IH with (lo:=lo + fst p0) in make_members_co'; eauto.
      rewrite Hg' in make_members_co'; eauto.
      rewrite Forall_map in Hcoal2. eapply Forall_forall in Hcoal2; eauto; simpl in *.
      apply Z.divide_add_r; eauto using Z.divide_trans.
      destruct p0. eapply field_offset_aligned' in Hfo; eauto. 2:rewrite Hmem in Htype; eauto.
      simpl in *.
      rewrite Hg', align_noattr in *; auto with zarith.
  Qed.

  Opaque sepconj.

  Lemma staterep_deref_mem:
    forall clsnm c prog prog' m me b ofs x ty d v P,
      find_class clsnm prog = Some (c, prog') ->
      m |= staterep gcenv prog clsnm  me b ofs ** P ->
      In (x, ty) c.(c_mems) ->
      find_val x me = Some v ->
      field_offset gcenv x (make_members c) = Errors.OK d ->
      Clight.deref_loc (translate_type ty) m b (Ptrofs.repr (ofs + fst d)) Full (value_to_cvalue v).
  Proof.
    intros * Find Hm Hin Hv Hoff.
    rewrite staterep_def, Find in Hm; simpl in Hm.
    do 2 apply sep_proj1 in Hm.
    apply sepall_in in Hin as [ws [xs [Hsplit Hin]]].
    rewrite Hin in Hm. clear Hsplit Hin.
    apply sep_proj1 in Hm. clear ws xs.
    unfold staterep_mems in Hm.
    rewrite Hoff in Hm. clear Hoff.
    apply loadv_rule in Hm; auto with mem.
    destruct Hm as [v' [Hloadv Hmatch]].
    unfold match_value in Hmatch.
    rewrite Hv in Hmatch; clear Hv.
    rewrite Hmatch in Hloadv; clear Hmatch.
    apply Clight.deref_loc_value with (2:=Hloadv); auto with clight.
  Qed.

  Lemma staterep_field_offset:
    forall m me c prog' cls prog b ofs x ty P,
      find_class c prog = Some (cls, prog') ->
      m |= staterep gcenv prog c me b ofs ** P ->
      In (x, ty) (c_mems cls) ->
      exists d, field_offset gcenv x (make_members cls) = Errors.OK d
           /\ 0 <= ofs + fst d <= Ptrofs.max_unsigned.
  Proof.
    intros * Find Hm Hin.
    rewrite staterep_def, Find in Hm; simpl in Hm.
    do 2 apply sep_proj1 in Hm.
    apply sepall_in in Hin as [ws [xs [Hsplit Hin]]].
    rewrite Hin in Hm. clear Hsplit Hin.
    apply sep_proj1 in Hm.
    clear ws xs.
    unfold staterep_mems in Hm.
    destruct (field_offset gcenv x (make_members cls)).
    - exists p; split; auto.
      eapply contains_no_overflow; eauto.
    - contradict Hm.
  Qed.

  Lemma staterep_extract:
    forall cid c prog' me b ofs m i c' P,
      wt_program prog ->
      find_class cid prog = Some (c, prog') ->
      (In (i, c') c.(c_objs)
       /\ m |= staterep gcenv prog cid me b ofs ** P)
      <-> exists objs objs' d,
          c.(c_objs) = objs ++ (i, c') :: objs'
          /\ field_offset gcenv i (make_members c) = Errors.OK d
          /\ m |= staterep gcenv prog c' (instance_match i me) b (ofs + fst d)
                  ** sepall (staterep_mems gcenv c me b ofs) c.(c_mems)
                  ** sepall (staterep_objs gcenv prog c me b ofs) (objs ++ objs')
                  ** P.
  Proof.
    clear make_members_co.
    intros * WT Find.
    rewrite staterep_def, Find; simpl.
    rewrite sep_assoc; split.
    - intros (Hin & Hmem).
      pose proof Hin.
      apply sepall_in in Hin as (objs & objs' & E & Hp).
      rewrite Hp, sep_assoc, sep_swap in Hmem.
      unfold staterep_objs at 1 in Hmem.
      destruct (field_offset gcenv i (make_members c)) as [d|];
        [|apply sepconj_sepfalse in Hmem; contradiction].
      exists objs, objs', d; intuition.
      erewrite <-staterep_chained_in_objs; eauto.
      eapply sep_imp; eauto.
      repeat apply sep_imp'; auto.
      apply sepall_weakenp; intros (i' & c'') Hin'; unfold staterep_objs.
      cases.
      assert (In (i', c'') (c_objs c)) as Hin
          by (rewrite E, in_app, in_cns; rewrite in_app in Hin'; tauto).
      erewrite staterep_chained_in_objs; eauto.
    - intros (objs & objs' & d & E & Hofs & Hmem).
      split.
      + rewrite E; apply in_app; right; left; auto.
      + rewrite (sepall_breakout (c_objs c)), sep_assoc, sep_swap; eauto.
        unfold staterep_objs at 1.
        rewrite Hofs; auto.
        assert (In (i, c') (c_objs c))
          by (rewrite E, in_app; right; apply in_eq).
        erewrite staterep_chained_in_objs; eauto.
        eapply sep_imp; eauto.
        repeat apply sep_imp'; auto.
        apply sepall_weakenp; intros (i' & c'') Hin'; unfold staterep_objs.
        cases.
        assert (In (i', c'') (c_objs c)) as Hin
            by (rewrite E, in_app, in_cns; rewrite in_app in Hin'; tauto).
        erewrite <-staterep_chained_in_objs; eauto.
  Qed.

End StateRepProperties.

Section Fieldsrep.
  Variable ge : composite_env.
  Hypothesis ge_consistent : composite_env_consistent ge.

  Definition fieldrep (ve: venv) (flds: members) (b: block) '((x, ty) : ident * Ctypes.type) : massert :=
    match field_offset ge x flds, access_mode ty with
    | Errors.OK d, By_value chunk =>
      contains chunk b (fst d) (match_value (Env.find x ve))
    | _, _ => sepfalse
    end.

  Definition fieldsrep (ve: venv) (ms : members) (b: block) : massert :=
    sepall (fun m => fieldrep ve ms b (name_member m, type_member m)) ms.

  Lemma fieldsrep_deref_mem:
    forall m ve flds b x ty d v P,
      m |= fieldsrep ve flds b ** P ->
      In (Member_plain x ty) flds ->
      Env.find x ve = Some v ->
      field_offset ge x flds = Errors.OK d ->
      Clight.deref_loc ty m b (Ptrofs.repr (fst d)) Full (value_to_cvalue v).
  Proof.
    intros * Hm Hin Hv Hoff.
    unfold fieldsrep in Hm.
    apply sepall_in in Hin.
    destruct Hin as [ws [xs [Hsplit Hin]]].
    rewrite Hin in Hm. clear Hsplit Hin.
    do 2 apply sep_proj1 in Hm. clear ws xs.
    unfold fieldrep in Hm; simpl in Hm; rewrite Hoff in Hm. clear Hoff.
    destruct (access_mode ty) eqn:Haccess; try contradiction.
    apply loadv_rule in Hm; auto with mem.
    destruct Hm as [v' [Hloadv Hmatch]].
    unfold match_value in Hmatch.
    rewrite Hv in Hmatch. clear Hv.
    rewrite Hmatch in Hloadv. clear Hmatch.
    apply Clight.deref_loc_value with (1:=Haccess) (2:=Hloadv).
  Qed.

  Lemma footprint_perm_fieldsrep:
    forall ve flds b b' lo hi,
      footprint_perm (fieldsrep ve flds b) b' lo hi.
  Proof.
    intros. apply footprint_perm_sepall.
    intros x b'' lo' hi'.
    unfold fieldrep.
    destruct (field_offset ge (name_member x) flds).
    2:now apply footprint_perm_sepfalse.
    destruct (access_mode (type_member x));
      try apply footprint_perm_sepfalse.
    apply footprint_perm_contains.
  Qed.

  Lemma footprint_decidable_fieldsrep:
    forall ve flds b,
      decidable_footprint (fieldsrep ve flds b).
  Proof.
    intros. apply decidable_footprint_sepall.
    intro m; unfold fieldrep.
    destruct (field_offset ge (name_member m) flds).
    2:now apply decidable_footprint_sepfalse.
    destruct (access_mode (type_member m));
      try apply decidable_footprint_sepfalse.
    apply decidable_footprint_contains.
  Qed.

  Lemma fieldsrep_empty':
    forall flds b,
      NoDupMembers flds ->
      (forall x ty, In (x, ty) flds ->
               exists chunk, access_mode ty = By_value chunk
                        /\ (Memdata.align_chunk chunk | alignof ge ty)) ->
      sepall (field_range ge flds b 0) flds <-*-> fieldsrep vempty (mk_members flds) b.
  Proof.
    intros * Hndups Hchunk.
    unfold fieldsrep.
    unfold mk_members. rewrite sepall_map.
    apply sepall_swapp.
    intros (x&ty) Hin.
    unfold mk_members, field_range', fieldrep. simpl.
    destruct (field_offset ge x _) as [(?&?)|] eqn:Hoff.
    2:reflexivity.
    apply field_offset_aligned' with (ty:=ty) in Hoff.
    2:apply in_field_type with (1:=Hndups) (2:=Hin).
    destruct (Hchunk _ _ Hin) as [chunk [Haccess Halign]].
    rewrite Haccess.
    split; [split|split].
    - intros m Hr.
      rewrite Env.gempty.
      apply range_contains'; auto with mem.
      now apply Z.divide_trans with (1:=Halign) (2:=Hoff).
      erewrite <-sizeof_by_value with (1:=Haccess); eauto.
    - simpl. now rewrite sizeof_by_value with (1:=Haccess).
    - simpl. rewrite sizeof_by_value with (1:=Haccess); eauto.
      intros. now apply contains_range' in H.
      (* NB: requires "new" definition of contains *)
    - simpl. now rewrite sizeof_by_value with (1:=Haccess).
  Qed.

  Lemma fieldsrep_empty:
    forall nm co flds b,
      ge!nm = Some co ->
      co_su co = Struct ->
      co_members co = mk_members flds ->
      NoDup (map name_member (co_members co)) ->
      (forall x ty, In (Member_plain x ty) (co_members co) ->
               exists chunk, access_mode ty = By_value chunk
                        /\ (Memdata.align_chunk chunk | alignof ge ty)) ->
      range b 0 (co_sizeof co) -*> fieldsrep vempty (co_members co) b.
  Proof.
    intros * Hco Hstruct Hmem Hndups Hchunk.
    rewrite split_range_fields
    with (1:=ge_consistent) (2:=Hco) (3:=Hstruct) (4:=Hmem) (5:=Hndups).
    erewrite Hmem, fieldsrep_empty'. reflexivity.
    - rewrite Hmem, mk_members_names, <-fst_NoDupMembers in Hndups; auto.
    - intros. eapply Hchunk.
      rewrite Hmem. eapply in_map_iff; do 2 esplit; eauto. auto.
  Qed.

  Lemma fieldsrep_any_empty:
    forall flds ve b,
      fieldsrep ve flds b -*> fieldsrep vempty flds b.
  Proof.
    intros flds ve b.
    apply sepall_weakenp.
    intros f Hin. unfold fieldrep.
    destruct (field_offset ge (name_member f) flds); try reflexivity.
    destruct (access_mode (type_member f)); try reflexivity.
    apply contains_imp.
    intros. now rewrite Env.gempty.
  Qed.

  Lemma fieldsrep_nodup:
    forall (xs: list (ident * type)) vs flds ve ob,
      NoDup (map fst xs ++ map name_member flds) ->
      fieldsrep ve flds ob <-*-> fieldsrep (Env.adds (map fst xs) vs ve) flds ob.
  Proof.
    intros * Nodup.
    unfold fieldsrep.
    apply sepall_swapp.
    intros ? Hin; unfold fieldrep.
    destruct (field_offset ge (name_member x) flds); auto.
    destruct (access_mode (type_member x)); auto.
    assert (~In (name_member x) (map fst xs)) as Hnxs.
    { rewrite Permutation.Permutation_app_comm in Nodup.
      eapply NoDup_app_In in Nodup; eauto. eapply in_map_iff; eauto. }
    rewrite Env.gsso; auto.
  Qed.

  Lemma fieldsrep_field_offset:
    forall m ve flds b P,
      m |= fieldsrep ve (mk_members flds) b ** P ->
      forall x ty,
        In (x, ty) flds ->
        exists d, field_offset ge x (mk_members flds) = Errors.OK d
             /\ 0 <= fst d <= Ptrofs.max_unsigned.
  Proof.
    intros * Hm ? ? Hin.
    unfold fieldsrep in Hm.
    assert (In (Member_plain x ty) (mk_members flds)) as Hin'.
    { eapply in_map_iff; do 2 esplit; eauto. auto. }
    apply sepall_in in Hin' as [ws [xs [Hsplit Hin']]].
    rewrite Hin' in Hm. clear Hsplit Hin'.
    do 2 apply sep_proj1 in Hm. clear ws xs; unfold fieldrep in *.
    simpl in Hm.
    destruct (field_offset ge x (mk_members flds)), (access_mode ty);
      try now contradict Hm.
    exists p; split; auto.
    eapply contains_no_overflow; eauto.
  Qed.

  Lemma fieldsrep_add:
    forall outb ve x v flds,
      ~ InMembers x flds ->
      fieldsrep ve (mk_members flds) outb -*>
      fieldsrep (Env.add x v ve) (mk_members flds) outb.
  Proof.
    intros * Hnin; unfold fieldsrep, fieldrep.
    rewrite sepall_swapp; eauto.
    intros ? Hx'; simpl.
    rewrite Env.gso; auto.
    apply in_map_iff in Hx' as ((?&?)&?&Hin); subst; simpl in *.
    eapply In_InMembers in Hin.
    intro Hxx'; subst x.
    contradiction.
  Qed.

End Fieldsrep.

Global Hint Resolve footprint_perm_fieldsrep footprint_decidable_fieldsrep : sep.

Section SubRep.

  Variable ge : composite_env.

  Definition fieldsrep_of (id: ident) (b: block): massert :=
    match ge ! id with
    | Some co =>
      fieldsrep ge vempty (co_members co) b
    | None => sepfalse
    end.

  Definition subrep_inst '((_, (b, t)): ident * (block * Ctypes.type)): massert :=
    match t with
    | Tstruct id _ => fieldsrep_of id b
    | _ => sepfalse
    end.

  Definition subrep_inst_env (e: Clight.env) '((x, t): ident * Ctypes.type): massert :=
    match e ! x with
    | Some (b, Tstruct id _ as t') =>
      if type_eq t t' then fieldsrep_of id b else sepfalse
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
    simpl; destruct t; auto with sep.
    unfold fieldsrep_of; destruct ge ! i; auto with sep.
  Qed.

  Lemma decidable_subrep:
    forall f e, decidable_footprint (subrep f e).
  Proof.
    intros.
    unfold subrep.
    induction (make_out_vars (instance_methods f)) as [|(x, t)]; simpl; auto with sep.
    apply decidable_footprint_sepconj; auto.
    destruct (e ! x) as [(b, t')|]; auto with sep.
    destruct t'; auto with sep.
    destruct (type_eq t (Tstruct i a)); auto with sep.
    unfold fieldsrep_of; destruct (ge ! i); auto with sep.
  Qed.

  Remark footprint_perm_subrep_inst:
    forall x b lo hi,
      footprint_perm (subrep_inst x) b lo hi.
  Proof.
    intros (x, (b, t)) b' lo hi.
    simpl; destruct t; auto with sep.
    unfold fieldsrep_of; destruct ge ! i; auto with sep.
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

  Hint Resolve decidable_footprint_subrep_inst decidable_subrep footprint_perm_subrep_inst : sep.

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
    2: now rewrite sep_unwand; auto with sep.
    induction (PTree.elements e) as [|(x, (b, t))]; simpl in *.
    - rewrite <-hide_in_sepwand; auto with sep.
      now rewrite <-sepemp_right.
    - inversion_clear Forall as [|? ? Hidco Forall']; subst;
        rename Forall' into Forall.
      destruct Hidco as (id & co & Ht & Hco & ? & (?&?) & Hnd & Hchunk); simpl in Ht.
      inversion_clear Nodup as [|? ? ? Notin Nodup'].
      unfold fieldsrep_of.
      rewrite Ht, Hco.
      rewrite sep_assoc.
      rewrite IHl at 1; auto.
      rewrite <-unify_distinct_wands; auto.
      + repeat rewrite <-sep_assoc.
        apply sep_imp'; auto.
        rewrite sep_comm, sep_assoc, sep_swap.
        apply sep_imp'; auto.
        rewrite <-range_imp_with_wand; auto with sep.
        simpl.
        rewrite Hco.
        eapply fieldsrep_empty; eauto.
      + now apply disjoint_footprint_range_inst.
      + simpl; rewrite Hco.
        rewrite fieldsrep_empty; eauto.
        reflexivity.
      + apply subseteq_footprint_sepall.
        intros (x', (b', t')) Hin; simpl.
        assert (In (x', t') (map drop_block l))
          by (change (x', t') with (drop_block (x', (b', t'))); apply in_map; auto).
        eapply Forall_forall in Forall; eauto.
        simpl in Forall.
        destruct Forall as (id' & co' & Ht' & Hco' & ? & (?&?) & ? & ?).
        unfold fieldsrep_of.
        rewrite Ht', Hco'. simpl.
        rewrite Hco'.
        rewrite fieldsrep_empty; eauto.
        reflexivity.
  Qed.

  Lemma subrep_extract:
    forall f f' e m o c' P,
      M.MapsTo (o, f') c' (instance_methods f) ->
      m |= subrep f e ** P <->
      exists b co ws xs,
        e ! (prefix_out f' o) = Some (b, type_of_inst (prefix_fun f' c'))
        /\ ge ! (prefix_fun f' c') = Some co
        /\ make_out_vars (instance_methods f) = ws ++ (prefix_out f' o, type_of_inst (prefix_fun f' c')) :: xs
        /\ m |= fieldsrep ge vempty (co_members co) b
              ** sepall (subrep_inst_env e) (ws ++ xs)
              ** P.
  Proof.
    intros * Hin.
    unfold subrep.
    assert (In (prefix_out f' o, type_of_inst (prefix_fun f' c'))
               (make_out_vars (instance_methods f))) as Hin'.
    { apply M.elements_1, setoid_in_key_elt in Hin.
      apply in_map with
      (f:=fun x => let '(o0, f0, cid) := x in (prefix_out f0 o0, type_of_inst (prefix_fun f0 cid))) in Hin.
      unfold make_out_vars; auto.
    }
    clear Hin.
    split.
    - apply sepall_in in Hin'; destruct Hin' as (ws & xs & Hin & Heq).
      rewrite Heq, sep_assoc.
      intro Hmem.
      unfold subrep_inst_env at 1 in Hmem.
      destruct e ! (prefix_out f' o) as [(oblk, t)|]; [|destruct Hmem; contradiction].
      destruct t; try (destruct Hmem; contradiction).
      destruct (type_eq (type_of_inst (prefix_fun f' c')) (Tstruct i a)) as [Eq|]; [|destruct Hmem; contradiction].
      unfold type_of_inst in Eq.
      inv Eq.
      unfold fieldsrep_of in *.
      destruct ge ! (prefix_fun f' c'); [|destruct Hmem; contradiction].
      exists oblk, c, ws, xs; intuition.
    - intros (oblk & c & ws' & xs' & He & Hge & Eq &?).
      (* rewrite Eq. *)
      rewrite sepall_breakout, sep_assoc; eauto.
      eapply sep_imp; eauto.
      unfold subrep_inst_env.
      rewrite He; unfold type_of_inst; rewrite type_eq_refl.
      unfold fieldsrep_of; rewrite Hge; auto.
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
  pure (Forall (match_var ve le) (map fst (f.(m_in) ++ f.(m_vars)))).

Lemma varsrep_any_empty:
  forall f ve le,
    varsrep f ve le -*> varsrep f vempty le.
Proof.
  intros.
  apply pure_imp; intro H.
  induction (map fst (m_in f ++ m_vars f)) as [|x]; auto.
  inv H; constructor; auto.
  unfold match_var in *; destruct (le ! x); try contradiction.
  now rewrite Env.gempty.
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
  unfold match_var in *.
  inv Hforall.
  constructor.
  - destruct le ! x'; auto.
    rewrite Env.gso; auto.
  - apply IHl; auto.
Qed.

Lemma varsrep_add:
  forall f ve le x v,
    varsrep f ve le -*>
    varsrep f (Env.add x v ve) (PTree.set x (value_to_cvalue v) le).
Proof.
  intros.
  unfold varsrep.
  rewrite pure_imp.
  intro Hforall.
  induction (m_in f ++ m_vars f) as [|(x', t')]; simpl in *; auto.
  inv Hforall.
  unfold match_var in *.
  constructor.
  - destruct (ident_eqb x' x) eqn: Eq.
    + apply ident_eqb_eq in Eq.
      subst x'.
      rewrite PTree.gss.
      unfold match_value.
      now rewrite Env.gss.
    + apply ident_eqb_neq in Eq.
      rewrite PTree.gso; auto.
      now rewrite Env.gso.
  - now apply IHl.
Qed.

Lemma varsrep_add':
  forall f ve le x v y v',
    ~ InMembers y (m_in f ++ m_vars f) ->
    varsrep f ve le -*>
    varsrep f (Env.add x v ve) (PTree.set x (value_to_cvalue v) (PTree.set y v' le)).
Proof.
  intros * Notin.
  transitivity (varsrep f ve (PTree.set y v' le)).
  - unfold varsrep.
    rewrite pure_imp.
    intro Hforall.
    induction (m_in f ++ m_vars f) as [|(x', t')]; simpl in *; auto.
    inv Hforall.
    apply Decidable.not_or in Notin; destruct Notin.
    unfold match_var in *.
    constructor.
    + rewrite PTree.gso; auto.
    + now apply IHl.
  - apply varsrep_add.
Qed.

Lemma varsrep_add'':
  forall f ve le x v y v',
    ~ InMembers y (m_in f ++ m_vars f) ->
    x <> y ->
    varsrep f (Env.add x v ve) le -*>
    varsrep f (Env.add x v ve) (PTree.set y v' le).
Proof.
  intros * Notin ?.
  unfold varsrep.
  rewrite pure_imp.
  intro Hforall.
  induction (m_in f ++ m_vars f) as [|(x', t')]; simpl in *; auto.
  inv Hforall.
  apply Decidable.not_or in Notin; destruct Notin.
  unfold match_var in *.
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
  unfold match_var in *.
  constructor.
  - rewrite PTree.gso; auto.
  - now apply IHl.
Qed.

Definition var_ptr (b: block) : val :=
  Vptr b Ptrofs.zero.

Section MatchStates.

  Variable ge : composite_env.

  Definition outputrep
             (c: class) (f: method) (ve: venv) (le: temp_env)
             (outb_co: option (block * composite)) : massert :=
    case_out f
             sepemp
             (fun x _ => pure (match_var ve le x))
             (fun _ => match outb_co with
                    | Some (outb, outco) =>
                      pure (le ! (prefix obc2c out) = Some (var_ptr outb))
                      ** pure (ge ! (prefix_fun f.(m_name) c.(c_name)) = Some outco)
                      ** fieldsrep ge ve outco.(co_members) outb
                    | None => sepfalse
                    end).

  Lemma outputrep_add_prefix:
    forall c f ve le outb_co x v,
      outputrep c f ve le outb_co <-*-> outputrep c f ve (PTree.set (prefix temp x) v le) outb_co.
  Proof.
    intros *.
    unfold outputrep, case_out.
    destruct_list (m_out f) as (?,?) (?,?) ? : Hout; auto.
    - unfold match_var; rewrite PTree.gso; auto.
      intro; subst.
      pose proof (m_good_out f) as Good.
      assert (In (prefix temp x, t) (m_out f)) as Hin.
      { rewrite Hout. left; auto. }
      apply Good, AtomOrGensym_inv in Hin; auto with ident.
    - cases.
      rewrite PTree.gso; eauto.
      eapply prefix_injective'. left. prove_str_to_pos_neq.
  Qed.

  Lemma outputrep_nil:
    forall c f ve le outb_co,
      f.(m_out) = [] ->
      outputrep c f ve le outb_co <-*-> sepemp.
  Proof.
    intros * Nil.
    unfold outputrep, case_out; rewrite Nil; auto.
  Qed.

  Lemma outputrep_singleton:
    forall c f ve le m outb_co x t P,
      f.(m_out) = [(x, t)] ->
      (m |= outputrep c f ve le outb_co ** P <->
       m |= P /\ match_var ve le x).
  Proof.
    intros * Sing.
    unfold outputrep, case_out; split; intros * H; rewrite Sing in *;
      rewrite sep_pure in *; tauto.
  Qed.

  Lemma outputrep_notnil:
    forall c f ve le m outb_co P,
      (1 < length f.(m_out))%nat ->
      (m |= outputrep c f ve le outb_co ** P <->
       exists outb outco,
         outb_co = Some (outb, outco)
         /\ m |= fieldsrep ge ve outco.(co_members) outb ** P
         /\ le ! (prefix obc2c out) = Some (var_ptr outb)
         /\ ge ! (prefix_fun f.(m_name) c.(c_name)) = Some outco).
  Proof.
    intros * Length.
    unfold outputrep, case_out; split; intros * H;
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
  Hint Resolve bounded_struct_of_class_ge0 : clight.

  Definition selfrep (p: program) (c: class) (me: menv) (le: Clight.temp_env) (sb: block) (sofs: ptrofs) : massert :=
    pure (le ! (prefix obc2c self) = Some (Vptr sb sofs))
    ** pure (bounded_struct_of_class c sofs)
    ** staterep ge p c.(c_name) me sb (Ptrofs.unsigned sofs).

  Lemma selfrep_conj:
    forall m p c me le sb sofs P,
      m |= selfrep p c me le sb sofs ** P
      <-> m |= staterep ge p c.(c_name) me sb (Ptrofs.unsigned sofs) ** P
        /\ le ! (prefix obc2c self) = Some (Vptr sb sofs)
        /\ bounded_struct_of_class c sofs.
  Proof.
    unfold selfrep; split; intros * H.
    - repeat rewrite sep_assoc in H; repeat rewrite sep_pure in H; tauto.
    - repeat rewrite sep_assoc; repeat rewrite sep_pure; tauto.
  Qed.

  Definition outputsrep (f: method) (e: Clight.env) : massert :=
    pure (prefix_out_env e)
    ** subrep ge f e
    ** (subrep ge f e -* subrep_range ge e).

  Definition match_states
             (p: program) (c: class) (f: method) '((me, ve): menv * venv)
             '((e, le): Clight.env * Clight.temp_env)
             (sb: block) (sofs: ptrofs) (outb_co: option (block * composite)): massert :=
    pure (wt_state p me ve c (meth_vars f))
    ** selfrep p c me le sb sofs
    ** outputrep c f ve le outb_co
    ** outputsrep f e
    ** varsrep f ve le.

  Lemma match_states_conj:
    forall p c f me ve e le m sb sofs outb_co P,
      m |= match_states p c f (me, ve) (e, le) sb sofs outb_co ** P <->
      m |= staterep ge p c.(c_name) me sb (Ptrofs.unsigned sofs)
           ** outputrep c f ve le outb_co
           ** subrep ge f e
           ** (subrep ge f e -* subrep_range ge e)
           ** varsrep f ve le
           ** P
      /\ bounded_struct_of_class c sofs
      /\ wt_state p me ve c (meth_vars f)
      /\ le ! (prefix obc2c self)= Some (Vptr sb sofs)
      /\ prefix_out_env e.
  Proof.
    unfold match_states, selfrep, outputsrep; split; intros * H.
    - repeat rewrite sep_assoc in H; repeat rewrite sep_pure in H.
      rewrite sep_swap3, sep_pure, sep_swap in H. tauto.
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
               (OutputMatch : forall outco , (1 < length (m_out caller))%nat ->
                                        ge ! (prefix_fun callerid ownerid) = Some outco ->
                                        mk_members (map translate_param caller.(m_out)) = outco.(co_members)).

    Variable (v : value) (x : ident) (ty : type).

    Hypothesis (WTv : wt_value v ty).

    Lemma outputrep_assign_gt1_mem:
      In (x, ty) caller.(m_out) ->
      (1 < length (m_out caller))%nat ->
      m |= outputrep owner caller ve le outb_co ** P ->
      exists m' b co d,
        outb_co = Some (b, co)
        /\ field_offset ge x (co_members co) = Errors.OK d
        /\ Clight.assign_loc ge (translate_type ty) m b (Ptrofs.repr (fst d)) Full (value_to_cvalue v) m'
        /\ m' |= outputrep owner caller (Env.add x v ve) le outb_co ** P.
    Proof.
      intros * Hin Len Hmem.
      apply outputrep_notnil in Hmem as (b & co & Hout & Hrep &?& Hco); auto.
      erewrite find_class_name, find_method_name in Hco; eauto.
      apply in_map with (f:=translate_param) in Hin.
      pose proof (m_nodupvars caller) as Nodup.

      (* get the updated memory *)
      apply sepall_in in Hin as [ws [ys [Hys Heq]]].
      unfold fieldsrep in Hrep.
      Local Opaque sepconj match_states.
      rewrite <-OutputMatch in Hrep; eauto. unfold mk_members in Hrep. rewrite sepall_map, Heq in Hrep; simpl in *.
      destruct (field_offset ge x _) as [d|] eqn: Hofs; rewrite sep_assoc in Hrep;
        try (destruct Hrep; contradiction).
      rewrite translate_type_access_by_value in Hrep.
      eapply Separation.storev_rule' with (v:=value_to_cvalue v) in Hrep
        as (m' & ? & Hrep); eauto with mem.
      exists m', b, co, d; intuition; eauto using assign_loc with clight.
      rewrite <-OutputMatch; eauto.
      rewrite outputrep_notnil; auto.
      erewrite find_class_name, find_method_name; eauto.
      exists b, co; split; intuition.
      unfold fieldsrep, fieldrep.
      rewrite <-OutputMatch; eauto. unfold mk_members. rewrite sepall_map, Heq; simpl. rewrite Hofs, translate_type_access_by_value, sep_assoc.
      eapply sep_imp; eauto.
      - unfold hasvalue, match_value; simpl.
        rewrite Env.gss, <-wt_value_load_result; auto.
      - apply sep_imp'; auto.
        do 2 apply NoDupMembers_app_r in Nodup.
        rewrite fst_NoDupMembers, <-translate_param_fst, <-fst_NoDupMembers in Nodup; auto.
        erewrite Hys in Nodup; auto.
        apply NoDupMembers_app_cons in Nodup.
        destruct Nodup as (Notin & Nodup).
        rewrite sepall_swapp; eauto.
        intros (x' & t') Hin.
        rewrite Env.gso; auto.
        simpl; intro; subst x'.
        apply Notin.
        eapply In_InMembers; eauto.
    Qed.

    Lemma outputrep_assign_singleton_mem:
      m_out caller = [(x, ty)] ->
      outputrep owner caller ve le outb_co -*>
      outputrep owner caller (Env.add x v ve) (PTree.set x (value_to_cvalue v) le) outb_co.
    Proof.
      intros Eq.
      unfold outputrep, case_out; rewrite Eq.
      unfold match_var; now rewrite PTree.gss, Env.gss.
    Qed.

    Lemma outputrep_assign_var_mem:
      ~ InMembers x (m_out caller) ->
      In (x, ty) (meth_vars caller) ->
      m |= outputrep owner caller ve le outb_co ** P ->
      m |= outputrep owner caller (Env.add x v ve) (PTree.set x (value_to_cvalue v) le) outb_co ** P.
    Proof.
      intros * Hnin Hin Hmem.
      eapply sep_imp; eauto.
      unfold outputrep, case_out in *; destruct_list (m_out caller) as (?, ?) (?, ?) ? : Hout; auto.
      - apply pure_imp.
        assert (i <> x) by (intro; subst; apply Hnin; constructor; auto).
        unfold match_var; now rewrite PTree.gso, Env.gso.
      - erewrite find_class_name, find_method_name in*; eauto.
        destruct outb_co as [(outb, outco)|]; auto.
        repeat apply sep_imp'; auto.
        + apply pure_imp.
          rewrite PTree.gso; auto.
          intro; subst; eapply In_InMembers, m_AtomOrGensym, AtomOrGensym_inv in Hin; eauto with ident.
        + rewrite 2 sep_assoc, 2 sep_pure in Hmem.
          destruct Hmem as (?&?&?).
          erewrite <-OutputMatch; eauto; try (simpl; lia).
          eapply fieldsrep_add; eauto.
          rewrite InMembers_translate_param_idem; auto.
    Qed.

    Lemma match_states_assign_state_mem:
      m |= match_states prog owner caller (me, ve) (e, le) sb sofs outb_co
           ** P ->
      In (x, ty) owner.(c_mems) ->
      exists m' d,
        field_offset ge x (make_members owner) = Errors.OK d
        /\ Clight.assign_loc ge (translate_type ty) m sb
                            (Ptrofs.repr (Ptrofs.unsigned sofs + fst d)) Full (value_to_cvalue v) m'
        /\ m' |= match_states prog owner caller (add_val x v me, ve) (e, le) sb sofs outb_co
                ** P.
    Proof.
      intros Hmem Hin.
      apply match_states_conj in Hmem as (Hmem & ?&?&?).
      erewrite find_class_name in Hmem; eauto.

      (* get the updated memory *)
      pose proof Hin.
      rewrite staterep_def, Findcl in Hmem; simpl in Hmem.
      apply sepall_in in Hin as [ws [ys [Hys Heq]]].
      unfold staterep_mems in Hmem.
      rewrite Heq in Hmem.
      destruct (field_offset ge x (make_members owner)) as [d|] eqn: Hofs; rewrite 2 sep_assoc in Hmem;
        try (destruct Hmem; contradiction).
      eapply Separation.storev_rule' with (v := value_to_cvalue v) in Hmem as (m' & ? & Hmem);
        eauto with mem.
      exists m', d; intuition; eauto using assign_loc with clight.
      apply match_states_conj; intuition; eauto with obctyping.
      erewrite find_class_name; eauto.
      rewrite staterep_def, Findcl; simpl.
      unfold staterep_mems.
      erewrite Heq, Hofs, 2 sep_assoc; eauto.
      eapply sep_imp; eauto.
      - unfold hasvalue'.
        rewrite find_val_gss.
        now rewrite <-wt_value_load_result.
      - repeat apply sep_imp'; auto.
        pose proof (c_nodupmems owner) as Nodup.
        rewrite Hys in Nodup.
        apply NoDupMembers_app_cons in Nodup.
        destruct Nodup as (Notin & Nodup).
        rewrite sepall_swapp; eauto.
        intros (x' & t') Hin.
        rewrite find_val_gso; auto.
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
                             (sptr :: optr :: map value_to_cvalue vs)
                             (create_undef_temps ys) = Some le'
        /\ Forall (match_var (Env.adds (map fst xs) vs vempty) le')
                 (map fst (xs ++ ys)).
  Proof.
    unfold match_var.
    induction xs as [|(x, ty)]; destruct vs;
      intros * Hso Nodup Nos Noo Nos' Noo' Hlengths; try discriminate.
    - simpl; econstructor; split; auto.
      unfold match_value, Env.adds; simpl.
      induction ys as [|(y, t)]; simpl; auto.
      assert (y <> s) by (intro; subst; apply Nos'; apply InMembers_eq).
      assert (y <> o) by (intro; subst; apply Noo'; apply InMembers_eq).
      constructor.
      + rewrite Env.gempty.
        do 2 (rewrite PTree.gso; auto).
        now rewrite PTree.gss.
      + apply NotInMembers_cons in Nos'; destruct Nos' as [Nos'].
        apply NotInMembers_cons in Noo'; destruct Noo' as [Noo'].
        specialize (IHys Nos' Noo').
        eapply Forall_impl_In; eauto; simpl.
        intros y' Hin Hmatch.
        assert (y' <> s) by (intro; subst; apply Nos'; eapply fst_InMembers; eauto).
        assert (y' <> o) by (intro; subst; apply Noo'; eapply fst_InMembers; eauto).
        rewrite 2 PTree.gso in *; auto.
        destruct (ident_eqb y' y) eqn: E.
        * apply ident_eqb_eq in E; subst y'.
          rewrite PTree.gss.
          now rewrite Env.gempty.
        * apply ident_eqb_neq in E.
          rewrite PTree.gso; auto.
    - inv Hlengths; inv Nodup.
      edestruct IHxs with (s:=s) (ts:=ts) (o:=o) (to:=to) (sptr:=sptr) (optr:=optr)
        as (le' & Bind & ?); eauto.
      + eapply NotInMembers_cons; eauto.
      + eapply NotInMembers_cons; eauto.
      + assert (x <> s) by (intro; subst; apply Nos; apply InMembers_eq).
        assert (x <> o) by (intro; subst; apply Noo; apply InMembers_eq).
        exists (PTree.set x (value_to_cvalue v) le'); split.
        * simpl map; rewrite bind_parameter_temps_comm; auto.
          apply bind_parameter_temps_cons; auto.
          simpl; intros [|[|]]; auto.
        * rewrite <-app_comm_cons.
          constructor.
          -- rewrite PTree.gss.
             unfold match_value; simpl; rewrite Env.find_gsss; simpl; auto.
             now rewrite <-fst_InMembers.
          -- eapply Forall_impl_In; eauto; simpl.
             intros x' Hin MV.
             destruct (ident_eq_dec x' x).
             ++ subst x'.
                rewrite PTree.gss; unfold match_value; simpl; rewrite Env.find_gsss; simpl; auto.
                now rewrite <-fst_InMembers.
             ++ rewrite PTree.gso; auto.
                unfold or_default_with.
                cases_eqn E; setoid_rewrite E in MV; simpl in *; try contradiction.
                unfold match_value in *; simpl.
                rewrite Env.find_gsso; auto; simpl; auto.
  Qed.

  Remark bind_parameter_temps_exists_noout:
    forall xs s ts ys vs sptr,
      NoDupMembers xs ->
      ~ InMembers s xs ->
      ~ InMembers s ys ->
      length xs = length vs ->
      exists le',
        bind_parameter_temps ((s, ts) :: xs)
                             (sptr :: map value_to_cvalue vs)
                             (create_undef_temps ys) = Some le'
        /\ Forall (match_var (Env.adds (map fst xs) vs vempty) le') (map fst (xs ++ ys)).
  Proof.
    unfold match_var.
    induction xs as [|(x, ty)]; destruct vs;
      intros * Nodup Nos Nos' Hlengths; try discriminate.
    - simpl; econstructor; split; auto.
      unfold match_value, Env.adds; simpl.
      induction ys as [|(y, t)]; simpl; auto.
      assert (y <> s) by (intro; subst; apply Nos'; apply InMembers_eq).
      constructor.
      + rewrite Env.gempty, PTree.gso, PTree.gss; simpl; auto.
      + apply NotInMembers_cons in Nos'; destruct Nos' as [Nos'].
        specialize (IHys Nos').
        eapply Forall_impl_In; eauto; simpl.
        intros y' Hin Hmatch.
        assert (y' <> s) by (intro; subst; apply Nos'; eapply fst_InMembers; eauto).
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
      + assert (x <> s) by (intro; subst; apply Nos; apply InMembers_eq).
        exists (PTree.set x (value_to_cvalue v) le'); split.
        * simpl map; rewrite bind_parameter_temps_comm_noout; auto.
          apply bind_parameter_temps_cons; auto.
          simpl; intros [|]; auto.
        * rewrite <-app_comm_cons.
          constructor.
          -- rewrite PTree.gss.
             simpl.
             unfold match_value; rewrite Env.find_gsss; simpl; auto.
             rewrite <-fst_InMembers; auto.
          -- eapply Forall_impl_In; eauto; simpl.
             intros x' Hin MV.
             destruct (ident_eq_dec x' x).
             ++ subst x'.
                rewrite PTree.gss; unfold match_value; simpl.
                rewrite Env.find_gsss; simpl; auto.
                rewrite <-fst_InMembers; auto.
             ++ rewrite PTree.gso; auto.
                unfold or_default_with.
                cases_eqn E; setoid_rewrite E in MV; simpl in *; try contradiction.
                unfold match_value; simpl; rewrite Env.find_gsso; auto.
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
      eapply alloc_rule; eauto; try lia.
      etransitivity; eauto.
      unfold Ptrofs.max_unsigned; lia.
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
      inv Eq. now exists f', o.
    - pose proof Perm as Perm_fst.
      apply Permutation_fst in Perm_fst.
      rewrite map_fst_drop_block in Perm_fst.
      rewrite Perm_fst in Hrep.
      rewrite <-subrep_range_eqv in Hrep.
      repeat rewrite subrep_eqv; auto.
      rewrite range_wand_equiv in Hrep; eauto.
      + now rewrite sep_assoc in Hrep.
      + eapply Permutation_Forall; eauto.
      + eapply alloc_NoDupMembers; eauto.
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
  (**            staterep for the sub-state and fieldsrep for the **)
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

  Hypothesis (TRANSL : translate do_sync all_public (Some main_node) prog = Errors.OK tprog)
             (WT     : wt_program prog).

  Lemma function_entry_match_states:
    forall cid c prog' fid f fd me vs,
      let vs' := map value_to_cvalue vs in
      method_spec c f prog fd ->
      find_class cid prog = Some (c, prog') ->
      find_method fid c.(c_methods) = Some f ->
      wt_memory me prog c.(c_mems) c.(c_objs) ->
      Forall2 (fun v xt => wt_value v (snd xt)) vs (m_in f) ->
      case_out f
               (forall m sb sofs P,
                   bounded_struct_of_class gcenv c sofs ->
                   m |= staterep gcenv prog cid me sb (Ptrofs.unsigned sofs) ** P ->
                   exists e_f le_f m_f,
                     function_entry2 tge fd (Vptr sb sofs :: vs') m e_f le_f m_f
                     /\ m_f |= match_states gcenv prog c f (me, Env.adds (map fst f.(m_in)) vs vempty) (e_f, le_f) sb sofs None
                              ** P)
               (fun _ _ =>
                  forall m sb sofs P,
                    bounded_struct_of_class gcenv c sofs ->
                    m |= staterep gcenv prog cid me sb (Ptrofs.unsigned sofs) ** P ->
                    exists e_f le_f m_f,
                      function_entry2 tge fd (Vptr sb sofs :: vs') m e_f le_f m_f
                      /\ m_f |= match_states gcenv prog c f (me, Env.adds (map fst f.(m_in)) vs vempty) (e_f, le_f) sb sofs None
                               ** P)
               (fun _ =>
                  forall m sb sofs instb instco P,
                   bounded_struct_of_class gcenv c sofs ->
                   m |= staterep gcenv prog cid me sb (Ptrofs.unsigned sofs)
                        ** fieldsrep gcenv vempty (co_members instco) instb
                        ** P ->
                   gcenv ! (prefix_fun fid cid) = Some instco ->
                   exists e_f le_f m_f,
                     function_entry2 tge fd (Vptr sb sofs :: var_ptr instb :: vs') m e_f le_f m_f
                     /\ m_f |= match_states gcenv prog c f (me, Env.adds (map fst f.(m_in)) vs vempty) (e_f, le_f) sb sofs
                                (Some (instb, instco))
                              ** P).
  Proof.
    intros * Spec Findcl Findmth WTmem WTvs.

    assert (NoDupMembers (make_out_vars (instance_methods f)))
      by (eapply NoDupMembers_make_out_vars; eauto; eapply wt_program_find_unit; eauto).
    assert (Forall (fun xt => sizeof tge (snd xt) <= Ptrofs.max_unsigned /\ wf_struct gcenv xt)
                   (make_out_vars (instance_methods f)))
      by (eapply instance_methods_caract; eauto).
    assert (Datatypes.length (map translate_param (m_in f)) = Datatypes.length vs)
      by (symmetry; rewrite map_length; eapply Forall2_length; eauto).
    assert (wt_state prog me vempty c (meth_vars f)) by (split; eauto with typing obctyping).
    assert (NoDup (map fst (m_in f))) by (apply fst_NoDupMembers, m_nodupin).
    assert (Forall2 (fun y xt => In (y, snd xt) (meth_vars f)) (map fst (m_in f)) (m_in f))
      by (apply Forall2_map_1, Forall2_same, Forall_forall; intros (x, t) Hin; simpl; apply in_app; auto).

    unfold method_spec, case_out in *.
    subst gcenv tge.
    destruct_list (m_out f) as (a,ta) (?,?) ? : Hout; simpl in Spec;
      destruct Spec as (P_f &?&?&?& T_f &?&?&?&?); intros * ? Hmem; try intros Hinstco.

    (* no output *)
    - (* get the allocated environment and memory *)
      edestruct alloc_result as (e_f & m_f &?&?&?); eauto with clight.

      (* get the temporaries *)
      edestruct
        (bind_parameter_temps_exists_noout (map translate_param f.(m_in))
                                           (prefix obc2c self) (type_of_inst_p (c_name c))
                                           (make_out_temps (instance_methods_temp (rev_prog prog) f)
                                              ++ make_out_temps (extcalls_temp f)
                                              ++ map translate_param (m_vars f))
                                           vs (Vptr sb sofs)) as (le_f & Bind & Vars); eauto with clight.
      assert (le_f ! (prefix obc2c self) = Some (Vptr sb sofs))
        by (eapply bind_parameter_temps_implies in Bind; eauto with clight).
      setoid_rewrite <-P_f in Bind.

      exists e_f, le_f, m_f; split.
      + constructor; auto; try congruence.
        rewrite T_f; auto.
      + apply match_states_conj; intuition; eauto using m_nodupvars with obctyping.
        erewrite find_class_name, sep_swap, outputrep_nil, <-sepemp_left, sep_swap, sep_swap23,
        sep_swap34, sep_swap23, sep_swap; eauto.
        apply sep_pure; split; auto.
        repeat rewrite map_app in *.
        repeat rewrite translate_param_fst in Vars.
        rewrite 3 Forall_app in Vars; rewrite Forall_app; tauto.

    (* one output *)
    - assert (prefix obc2c self <> a).
      { intro contra; subst.
        pose proof (m_good_out f) as Good. rewrite Hout in Good.
        assert (In (prefix obc2c self, ta) [(prefix obc2c self, ta)]) as Hin by (left; auto).
        apply Good, AtomOrGensym_inv in Hin; auto with ident. }

      (* get the allocated environment and memory *)
      edestruct alloc_result as (e_f & m_f &?&?&?); eauto with clight.

      (* get the temporaries (+ the local return temporary) *)
      edestruct
        (bind_parameter_temps_exists_noout (map translate_param f.(m_in))
                                           (prefix obc2c self) (type_of_inst_p (c_name c))
                                           ((a, translate_type ta) ::
                                              make_out_temps (instance_methods_temp (rev_prog prog) f)
                                              ++ make_out_temps (extcalls_temp f)
                                              ++ map translate_param (m_vars f))
                                           vs (Vptr sb sofs)) as (le_f & Bind & Vars);
        eauto with clight; try eapply NotInMembers_cons; eauto with clight.
      assert (le_f ! (prefix obc2c self) = Some (Vptr sb sofs))
        by (eapply bind_parameter_temps_implies in Bind; eauto with clight).
      setoid_rewrite <-P_f in Bind.

      exists e_f, le_f, m_f; split.
      + constructor; auto; try congruence.
        rewrite T_f; auto.
      + apply match_states_conj; intuition; eauto using m_nodupvars with obctyping.
        erewrite find_class_name, sep_swap, outputrep_singleton, sep_swap, sep_swap23,
        sep_swap34, sep_swap23, sep_swap; eauto.
        repeat rewrite map_app, map_cons, 2 map_app in *.
        repeat rewrite translate_param_fst in Vars.
        rewrite Forall_app, Forall_cons2, 2 Forall_app in Vars.
        setoid_rewrite sep_pure; split; [split|]; auto; try tauto.
        rewrite map_app, Forall_app; tauto.

    (* multiple outputs *)
    - assert (1 < Datatypes.length (m_out f))%nat
        by (rewrite Hout; simpl; lia).

      assert (prefix obc2c self <> prefix obc2c out) as Hnso
          by (apply prefix_injective'; right; prove_str_to_pos_neq).

      (* get the allocated environment and memory *)
      edestruct alloc_result as (e_f & m_f &?&?&?); eauto with clight.

      (* get the temporaries *)
      edestruct
        (bind_parameter_temps_exists (map translate_param f.(m_in)) (prefix obc2c self) (type_of_inst_p (c_name c))
                                     (prefix obc2c out) (type_of_inst_p (prefix_fun (m_name f) (c_name c)))
                                     (make_out_temps (instance_methods_temp (rev_prog prog) f)
                                        ++ make_out_temps (extcalls_temp f)
                                        ++ map translate_param f.(m_vars))
                                     vs (Vptr sb sofs) (var_ptr instb)) as (le_f & Bind & Vars); eauto with clight.
      assert (le_f ! (prefix obc2c self) = Some (Vptr sb sofs) /\ le_f ! (prefix obc2c out) = Some (var_ptr instb)) as (?&?)
          by (eapply bind_parameter_temps_implies_two in Bind; eauto with clight).
      setoid_rewrite <-P_f in Bind; setoid_rewrite <-T_f in Bind.

      exists e_f, le_f, m_f; split.
      + constructor; auto; congruence.
      + apply match_states_conj; intuition; eauto using m_nodupvars with obctyping.
        erewrite find_class_name, sep_swap, outputrep_notnil; eauto.
        erewrite find_class_name, find_method_name; eauto.
        exists instb, instco; intuition; auto.
        rewrite sep_swap23, sep_swap, sep_swap34, sep_swap23, sep_swap34,
        sep_swap45, sep_swap34, sep_swap23, sep_swap.
        setoid_rewrite sep_pure; split.
        * repeat rewrite map_app in *.
          repeat rewrite translate_param_fst in Vars.
          rewrite 3 Forall_app in Vars.
          rewrite Forall_app; tauto.
        * eapply sep_imp; eauto.
          repeat apply sep_imp'; auto.
          apply fieldsrep_nodup; eauto.
          erewrite <-output_match; eauto.
          rewrite mk_members_names, translate_param_fst.
          eapply NoDup_app_weaken.
          rewrite Permutation.Permutation_app_comm, NoDup_swap, <-2 map_app.
          apply fst_NoDupMembers, m_nodupvars.
  Qed.

End FunctionEntry.

Section MainProgram.

  Variable (main_node  : ident)
           (prog       : program)
           (tprog      : Clight.program)
           (do_sync    : bool)
           (all_public : bool).
  Let tge              := Clight.globalenv tprog.
  Let gcenv            := Clight.genv_cenv tge.

  Hypothesis (TRANSL : translate do_sync all_public (Some main_node) prog = Errors.OK tprog)
             (WT     : wt_program prog).

  Let out_step   := prefix out step.
  Let t_out_step := type_of_inst (prefix_fun step main_node).

  Let main_step := main_step _ _ _ _ _ TRANSL.
  Let main_f    := main_f _ _ _ _ _ TRANSL.

  Lemma main_with_output_structure:
    forall m P,
      (1 < length (m_out main_step))%nat ->
      m |= P ->
      exists m' step_b step_co,
        alloc_variables tge empty_env m (fn_vars main_f)
                        (PTree.set out_step (step_b, t_out_step) empty_env) m'
        /\ gcenv ! (prefix_fun step main_node) = Some step_co
        /\ m' |= fieldsrep gcenv vempty step_co.(co_members) step_b ** P.
  Proof.
    intros * Len Hm.
    subst main_step main_f.
    simpl; unfold case_out.
    destruct_list (m_out (GenerationProperties.main_step _ _ _ _ _ TRANSL)) as (?,?) (?,?) ? : Out;
      try (simpl in Len; lia).

    (* get the allocated memory *)
    destruct (Mem.alloc m 0 (sizeof tge (type_of_inst (prefix_fun step main_node))))
      as (m', step_b) eqn: AllocStep.

    (* get the out struct *)
    pose proof (find_main_class _ _ _ _ _ TRANSL) as Find_main.
    pose proof (find_main_step _ _ _ _ _ TRANSL) as Find_step.
    rewrite <-Out in Len.
    edestruct global_out_struct as (step_co & Hsco & ? & Hms & ? & ? & ?); eauto.

    exists m', step_b, step_co; intuition.
    - repeat (econstructor; eauto).
    - assert (sizeof tge (type_of_inst (prefix_fun step main_node)) <= Ptrofs.modulus)
        by (simpl; setoid_rewrite Hsco; transitivity Ptrofs.max_unsigned;
            auto; unfold Ptrofs.max_unsigned; lia).
      eapply alloc_rule in AllocStep; eauto; try reflexivity.
      eapply sep_imp; eauto.
      simpl; setoid_rewrite Hsco; eapply fieldsrep_empty; eauto.
      + eapply Consistent; eauto.
      + rewrite Hms; eauto.
        intros * Hin; apply in_map_iff in Hin as ((?&?)& E' & Hin); inv E'.
        apply in_map_iff in Hin as ((?&?)& E' &?); inversion E'; eauto with clight.
  Qed.

  Lemma init_mem:
    exists m sb,
      Genv.init_mem tprog = Some m
      /\ Genv.find_symbol tge (prefix_glob (prefix self main_id)) = Some sb
      /\ m |= staterep gcenv prog main_node mempty sb Z0.
  Proof.
    destruct Genv.init_mem_exists with (p:=tprog) as (m' & Initmem);
      eauto using well_initialized.

    pose proof TRANSL as Trans.
    inv_trans Trans as Eexterns En Estep Ereset Eenums with structs funs E.

    exists m'.
    edestruct find_self as (sb & find_step); eauto.
    exists sb; split; [|split]; auto.
    assert (NoDupMembers tprog.(AST.prog_defs)) as Nodup
        by (rewrite fst_NoDupMembers, NoDup_norepet; eapply prog_defs_norepet; eauto).
    pose proof (init_grange _ _ Nodup Initmem) as Hgrange.
    unfold make_program' in Trans.
    destruct (build_composite_env' (concat structs)) as [(ce, ?)|]; try discriminate.
    destruct (check_size_env ce (concat structs)) eqn: Check_size; try discriminate.
    unfold translate_class in E.
    apply split_map in E; destruct E as [? Funs].
    inversion Trans as [Htprog].
    rewrite <-Htprog in Hgrange at 2.
    simpl in Hgrange.
    setoid_rewrite find_step in Hgrange.
    rewrite <-Zplus_0_r_reverse in Hgrange.
    rewrite Zmax_left in Hgrange;
      [|destruct (ce ! main_node); try lia; apply co_sizeof_pos].
    apply sep_proj1 in Hgrange.
    rewrite sepemp_right in *.
    eapply sep_imp; eauto.
    rewrite pure_sepwand.
    - unfold Genv.perm_globvar; simpl.
      transitivity (range_w sb 0 (sizeof gcenv (type_of_inst main_node))).
      + unfold sizeof; simpl.
        subst gcenv tge.
        setoid_rewrite <-Htprog; auto.
      + apply range_staterep; eauto.
        * eapply Consistent; eauto.
        * eapply make_members_co; eauto.
        * intro En'; rewrite En' in En; discriminate.
    - edestruct make_members_co as (co & Find_main & ? & ? & ? & ? & ?); eauto.
      subst gcenv tge.
      rewrite <-Htprog in Find_main; simpl in Find_main.
      rewrite Find_main.
      transitivity Ptrofs.max_unsigned; auto; unfold Ptrofs.max_unsigned; lia.
  Qed.

End MainProgram.

Global Hint Resolve match_states_wt_state bounded_struct_of_class_ge0 : clight.
