Require Import common.Separation.
Require Import common.Values.
Require common.Errors.
Require Import cfrontend.Ctypes.
Require Import lib.Maps.
Require Import lib.Coqlib.
Require Import lib.Integers.

Require Import Rustre.Common.
Require Import Rustre.RMemory.

Require Import List.
Require Import ZArith.BinInt.

Require Import Program.Tactics.

Require Import Rustre.Obc.Syntax.
Require Import Rustre.Obc.Semantics.
Require Import Rustre.Obc.Typing.
Require Import Rustre.ObcToClight.MoreSeparation.  
Require Import Rustre.ObcToClight.Translation.
Require Import Rustre.Ident.
Require Import Rustre.ObcToClight.Interface.

Module Export Sem := SemanticsFun Ids Op OpAux Syn.
Module Export Typ := Typing Ids Op OpAux Syn Sem.

Open Scope list.
Open Scope sep_scope.
Open Scope Z.

Definition match_value (e: PM.t val) (x: ident) (v': val) : Prop :=
  match PM.find x e with
  | None => True
  | Some v => v' = v
  end.

Lemma match_value_empty:
  forall x, match_value (PM.empty val) x = (fun _ => True).
Proof.
  intro. unfold match_value.
  rewrite PM.gempty; auto.
Qed.

Lemma match_value_add:
  forall x x' v e,
    x <> x' ->
    match_value (PM.add x' v e) x = match_value e x.
Proof.
  intros ** Hneq.
  unfold match_value. simpl.
  rewrite PM.gso with (1:=Hneq).
  reflexivity.
Qed.

Remark match_find_var_det:
  forall ve x v1 v2,
    match_value ve x v1 ->
    PM.find x ve = Some v2 ->
    v1 = v2.
Proof.
  unfold match_value; simpl.
  intros ** Hm Hf.
  now rewrite Hf in Hm.
Qed.

Ltac app_match_find_var_det :=
  match goal with
  | H1: PM.find ?x ?ve = Some ?v1,
        H2: match_value ?ve ?x ?v2 |- _ =>
    assert (v2 = v1) by (apply (match_find_var_det _ _ _ _ H2 H1)); subst v1; clear H2
  end.

Definition instance_match (me: heap) (i: ident): heap :=
  match mfind_inst i me with
  | None => hempty
  | Some i => i
  end.

Lemma instance_match_empty:
  forall x, instance_match hempty x = hempty.
Proof.
  intros. unfold instance_match, mfind_inst; simpl.
  now rewrite PM.gempty. 
Qed.

Remark field_offset_rec_in_range':
  forall gcenv flds x ofs pos,
    field_offset_rec gcenv x flds pos = Errors.OK ofs ->
    pos <= ofs.
Proof.
  induction flds as [|[i t]]; simpl; intros.
  - discriminate.
  - destruct (AST.ident_eq x i); intros.
    + inv H. apply align_le. apply alignof_pos.
    + specialize (IHflds _ _ _ H). eapply Zle_trans; eauto.
      apply Zle_trans with (align pos (alignof gcenv t)).
      * apply align_le. apply alignof_pos.
      * generalize (sizeof_pos gcenv t). omega.
Qed.

Remark field_offset_in_range':
  forall gcenv flds x ofs,
    field_offset gcenv x flds = Errors.OK ofs ->
    0 <= ofs.
Proof.
  unfold field_offset; intros.
  eapply field_offset_rec_in_range'; eauto.
Qed.

Section Staterep.
  Variable ge : composite_env.

  Definition staterep_mems (cls: class) (me: heap) (b: block) (ofs: Z) (xty: ident * type) :=
    let (x, ty) := xty in
    match field_offset ge x (make_members cls) with
    | Errors.OK d =>
	  contains (type_chunk ty) b (ofs + d) (match_value me.(mm_values) x)
    | Errors.Error _ => sepfalse
    end.

  Fixpoint staterep
           (p: program) (clsnm: ident) (me: heap) (b: block) (ofs: Z): massert :=
    match p with
    | nil => sepfalse
    | cls :: p' =>
      if ident_eqb clsnm cls.(c_name)
      then
        sepall (staterep_mems cls me b ofs) cls.(c_mems)
        **
        sepall (fun (o: ident * ident) =>
                  let (i, c) := o in
                  match field_offset ge i (make_members cls) with
                  | Errors.OK d =>
                    staterep p' c (instance_match me i) b (ofs + d)
                  | Errors.Error _ => sepfalse
                  end) cls.(c_objs)
      else staterep p' clsnm me b ofs
    end.

  Definition staterep_objs (p': program) (cls: class) (me: heap) (b: block) (ofs: Z) (o: ident * ident) :=
    let (i, c) := o in
    match field_offset ge i (make_members cls) with
    | Errors.OK d =>
      staterep p' c (instance_match me i) b (ofs + d)
    | Errors.Error _ => sepfalse
    end.

  Lemma staterep_skip_cons:
    forall cls prog clsnm me b ofs,
      clsnm <> cls.(c_name) ->
      staterep (cls :: prog) clsnm me b ofs <-*-> staterep prog clsnm me b ofs.
  Proof.
    intros ** Hnm.
    apply ident_eqb_neq in Hnm.
    simpl; rewrite Hnm; reflexivity.
  Qed.

  Lemma staterep_skip_app:
    forall clsnm prog oprog me b ofs,
      find_class clsnm oprog = None ->
      staterep (oprog ++ prog) clsnm me b ofs <-*-> staterep prog clsnm me b ofs.
  Proof.
    intros ** Hnin.
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
    intros ** Find.
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
      footprint_perm (staterep p clsnm me b ofs) b' lo hi.
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

Lemma ident_eqb_sym:
  forall x y, ident_eqb x y = ident_eqb y x.
Proof Pos.eqb_sym.

Lemma two_power_nat_le_divides:
  forall m n,
    two_power_nat m <= two_power_nat n ->
    (two_power_nat m | two_power_nat n).
Proof.
  intros m n HH.
  repeat rewrite two_power_nat_equiv in HH.
  rewrite <-Z.pow_le_mono_r_iff in HH; intuition.
  apply Z.le_exists_sub in HH.
  destruct HH as [p [HH1 HH2]].
  rewrite <-(nat_of_Z_eq p) in HH1; [|now apply Z.le_ge].
  apply Zdivide_intro with (q:=two_power_nat (nat_of_Z p)).
  repeat rewrite two_power_nat_equiv.
  rewrite <-Z.pow_add_r; intuition.
  rewrite HH1.
  reflexivity.
Qed.

Lemma two_power_nat_max:
  forall m n,
    (two_power_nat m | Z.max (two_power_nat m) (two_power_nat n)).
Proof.
  intros m n.
  rewrite Zmax_spec.
  destruct (zlt (two_power_nat n) (two_power_nat m)).
  apply Z.divide_refl.
  apply two_power_nat_le_divides.
  now apply Z.ge_le.
Qed.

Lemma co_members_alignof:
  forall env co,
    composite_consistent env co ->
    attr_alignas (co_attr co) = None ->
    Forall (fun x => (alignof env (snd x) | co_alignof co)) (co_members co).
Proof.
  intros env co Henv Hattr.
  rewrite co_consistent_alignof with (1:=Henv).
  unfold align_attr.
  rewrite Hattr; clear Hattr.
  induction (co_members co) as [|m ms IH]; [now trivial|].
  destruct (alignof_composite_two_p env ms) as [n Hms].
  simpl. rewrite Hms in *; clear Hms.
  destruct m as [x ty].
  destruct (alignof_two_p env ty) as [m Hty].
  rewrite Hty.
  constructor.
  - simpl. rewrite Hty. now apply two_power_nat_max.
  - apply Forall_impl with (2:=IH).
    destruct a as [x' ty']. simpl.
    intro HH. apply Z.divide_trans with (1:=HH).
    rewrite Z.max_comm. apply two_power_nat_max.
Qed.

Lemma align_noattr:
  forall a, align_attr noattr a = a.
Proof.
  intros. unfold noattr. reflexivity.
Qed.

Lemma in_field_type:
  forall xs x ty,
    NoDupMembers xs ->
    In (x, ty) xs ->
    field_type x xs = Errors.OK ty.
Proof.
  intros xs x ty Hndup Hin.
  induction xs as [|x' xs IH]; [now inversion Hin|].
  destruct x' as [x' ty'].
  apply nodupmembers_cons in Hndup.
  destruct Hndup as [? Hndup].
  inversion Hin as [Heq|Heq].
  - injection Heq; intros; subst.
    simpl. rewrite peq_true. reflexivity.
  - simpl. rewrite peq_false.
    + now apply IH with (1:=Hndup) (2:=Heq).
    + intro; subst.
      apply NotInMembers_NotIn in Heq; intuition.
Qed.

Lemma sizeof_translate_chunk:
  forall gcenv t,
    Ctypes.access_mode (cltype t) = Ctypes.By_value (type_chunk t) ->
    sizeof gcenv (cltype t) = Memdata.size_chunk (type_chunk t).
Proof.
  destruct t;
  (destruct i, s || destruct f || idtac);
  (discriminates || contradiction || auto).
Qed.

Lemma align_chunk_divides_alignof_type:
  forall gcenv t,
    Ctypes.access_mode (cltype t) = Ctypes.By_value (type_chunk t) ->
    (Memdata.align_chunk (type_chunk t) | alignof gcenv (cltype t)).
Proof.
  destruct t;
  (destruct i, s || destruct f || idtac);
  (discriminates || contradiction || auto);
  simpl; try rewrite align_noattr; auto using Z.divide_refl.
Qed.

Lemma in_translate_param_chunked:
  forall ge (flds: list (ident * Ctypes.type)) x ty,
    Ctypes.access_mode (cltype ty) = Ctypes.By_value (type_chunk ty) ->
    In (x, cltype ty) flds ->
    exists chunk,
      access_mode (cltype ty) = By_value chunk
      /\ (Memdata.align_chunk chunk | alignof ge (cltype ty)).
Proof.
  intros ** ? Hin.
  exists (type_chunk ty).
  split; auto.
  now apply align_chunk_divides_alignof_type.
Qed.


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

  Lemma field_offset_type:
    forall id flds d,
      field_offset env id flds = Errors.OK d ->
      exists ty, field_type id flds = Errors.OK ty.
  Proof.
    unfold field_offset.
    intros until d.
    cut (forall ofs, field_offset_rec env id flds ofs = Errors.OK d ->
                     exists ty, field_type id flds = Errors.OK ty); eauto.
    induction flds as [|(id', ty') flds IH]; intros ofs Hfo; [now inv Hfo|].
    simpl.
    destruct (ident_eq_dec id id') as [He|Hne].
    - rewrite He, peq_true. now exists ty'.
    - simpl in Hfo.
      rewrite peq_false in *; auto.
      destruct (IH _ Hfo) as (ty & Hft).
      exists ty; assumption.
  Qed.
  
  Lemma struct_in_bounds_field:
    forall min max ofs flds id d,
      struct_in_bounds min max ofs flds ->
      field_offset env id flds = Errors.OK d ->
      min <= ofs + d <= max.
  Proof.
    unfold struct_in_bounds.
    intros ** (Hmin & Hmax) Hfo.
    destruct (field_offset_type _ _ _ Hfo) as (ty & Hft).
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
    intros ** (Hmin & Hmax) Hfo Hft Henv Hsu.
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

(* TODO: move into Obc/Syntax.v *)
Lemma find_class_chained:
  forall prog c1 c2 cls prog' cls' prog'',
    wt_program prog ->
    find_class c1 prog = Some (cls, prog') ->
    find_class c2 prog' = Some (cls', prog'') ->
    find_class c2 prog = Some (cls', prog'').
Admitted.

Section StateRepProperties.

  Variable main_node : ident.
  Variable prog: program.
  Variable tprog: Clight.program.

  Let tge := Clight.globalenv tprog.
  Let gcenv := Clight.genv_cenv tge.

  Hypothesis TRANSL: translate prog main_node = Errors.OK tprog.
  Hypothesis gcenv_consistent: composite_env_consistent gcenv.

  Hypothesis make_members_co:
    forall clsnm cls prog',
      find_class clsnm prog = Some (cls, prog') ->
      (exists co, gcenv!clsnm = Some co
             /\ co_su co = Struct
             /\ co_members co = make_members cls
             /\ attr_alignas (co_attr co) = None
             /\ NoDupMembers (co_members co)).

  Lemma c_objs_field_offset:
    forall o c cls,
      In (o, c) cls.(c_objs) ->
      exists d, field_offset gcenv o (make_members cls) = Errors.OK d.
  Proof.
    intros ** Hin.
    unfold field_offset.
    cut (forall ofs, exists d,
         field_offset_rec gcenv o (make_members cls) ofs = Errors.OK d); auto.
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
    intros ** WTp Hfc Hsb Hin Hfc'.
    destruct (c_objs_field_offset _ _ _ Hin) as (d & Hfo).
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
    rewrite Hmem.
    unfold make_members.
    admit.
  Qed.
  
  Lemma field_translate_mem_type:
    forall prog clsnm cls prog',
      find_class clsnm prog = Some (cls, prog') ->
      NoDupMembers (make_members cls) ->
      forall x ty,
        In (x, ty) cls.(c_mems) ->
        field_type x (make_members cls) = Errors.OK (cltype ty).
  Proof.
    intros ** Hfind Hndup ? ? Hin.
    apply in_field_type with (1:=Hndup).
    unfold make_members, translate_param. apply in_app_iff.
    left. rewrite in_map_iff.
    exists (x, ty); split; auto.
  Qed.

  Lemma field_translate_obj_type:
    forall prog clsnm cls prog',
      find_class clsnm prog = Some (cls, prog') ->
      NoDupMembers (make_members cls) ->
      forall o c,
        In (o, c) cls.(c_objs) ->
        field_type o (make_members cls) = Errors.OK (type_of_inst c).
  Proof.
    intros ** Hfind Hndup ? ? Hin.
    apply in_field_type with (1:=Hndup).
    unfold make_members. apply in_app_iff. right.
    apply in_map_iff. exists (o, c); auto.
  Qed.

  Hint Resolve Zdivide_trans
               align_chunk_divides_alignof_type
               access_mode_cltype : clalign.

  Lemma range_staterep:
    forall b clsnm,
      wt_program prog ->
      find_class clsnm prog <> None ->
      range b 0 (sizeof gcenv (type_of_inst clsnm)) -*>
            staterep gcenv prog clsnm hempty b 0.
  Proof.
    intros ** WTp Hfind.
    (* Weaken the goal for proof by induction. *)
    cut (forall lo,
           (alignof gcenv (type_of_inst clsnm) | lo) ->
           massert_imp (range b lo (lo + sizeof gcenv (type_of_inst clsnm)))
                       (staterep gcenv prog clsnm hempty b lo)).
    now intro HH; apply HH; apply Z.divide_0_r.

    (* Setup an induction on prog. *)
    revert clsnm Hfind.
    remember prog as prog1.
    assert (WTp' := WTp).
    rewrite Heqprog1 in make_members_co, WTp.
    assert (sub_prog prog1 prog) as Hsub
        by now rewrite Heqprog1.
    clear TRANSL Heqprog1.
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
        as (co & Hg & Hsu & Hmem & Hattr & Hndup).

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
        pose proof (field_translate_mem_type _ _ _ _ Hprog Hndup') as Htype.
        clear Hcoal2.
        induction cls.(c_mems) as [|m ms]; auto.
        apply Forall_cons2 in Hcoal1.
        destruct Hcoal1 as [Hcoal1 Hcoal2].
        apply sep_imp'; auto with datatypes.
        destruct m; simpl. 
        destruct (field_offset gcenv i (co_members co)) eqn:Hfo; auto.
        rewrite match_value_empty, sizeof_translate_chunk; eauto with clalign.
        apply range_contains'.
        apply field_offset_aligned with (ty:=cltype t) in Hfo.
        now apply Z.divide_add_r; eauto with clalign.
        rewrite <-Hmem in Htype. apply Htype; auto with datatypes.

      + (* Divide up the memory sub-block for cls.(c_objs). *)
        pose proof (field_translate_obj_type _ _ _ _ Hprog Hndup') as Htype.
        rewrite <-Hmem in Htype.
        destruct WTc as [Ho Hm]; clear Hm.
        induction cls.(c_objs) as [|o os]; auto.
        simpl. apply sep_imp'.
        2:now inv Ho; apply Forall_cons2 in Hcoal2; intuition.
        apply In_Forall with (x:=o) in Ho; auto with datatypes.
        destruct o as [o c].
        apply Forall_cons2 in Hcoal2.
        destruct Hcoal2 as [Hcoal2 Hcoal3].
        specialize (Htype o c (in_eq _ _)).
        clear IHos Hcoal1 Hcoal3 os.
        simpl in *.
        destruct (field_offset gcenv o (co_members co)) eqn:Hfo; auto.
        rewrite instance_match_empty.
        specialize (IH WTp'' (sub_prog_cons _ _ _ Hsub) c Ho (lo + z)%Z).
        apply not_None_is_Some in Ho.
        destruct Ho as ((c' & prog''') & Ho).
        assert (find_class c prog = Some (c', prog''')) as Hcin'
            by apply find_class_sub_same with (1:=Ho) (2:=WTp)
                                              (3:=sub_prog_cons _ _ _ Hsub).
        destruct (make_members_co _ _ _ Hcin')
          as (co' & Hg' & Hsu' & Hmem' & Hattr' & Hnodup').
        rewrite Hg', align_noattr in *.
        apply IH.
        apply Z.divide_add_r; eauto with clalign.
        eapply field_offset_aligned in Hfo; eauto.
        apply Zdivide_trans with (2:=Hfo).
        simpl. rewrite Hg', align_noattr.
        apply Z.divide_refl.
    - simpl in Hfind.
      rewrite Hclsnm in Hfind.
      specialize (IH WTp'' (sub_prog_cons _ _ _ Hsub) clsnm Hfind lo Halign).
      rewrite ident_eqb_sym in Hclsnm.
      apply ident_eqb_neq in Hclsnm.
      rewrite staterep_skip_cons with (1:=Hclsnm).
      apply IH.
  Qed.

  Lemma staterep_deref_mem:
    forall cls prog' m me b ofs x ty d v P,
      access_mode (cltype ty) = By_value (type_chunk ty) ->
      m |= staterep gcenv (cls::prog') cls.(c_name) me b ofs ** P ->
      In (x, ty) cls.(c_mems) ->
      mfind_mem x me = Some v ->
      field_offset gcenv x (make_members cls) = Errors.OK d ->
      Clight.deref_loc (cltype ty) m b (Int.repr (ofs + d)) v.
  Proof.
    intros ** Hty Hm Hin Hv Hoff.
    apply sep_proj1 in Hm.
    simpl in Hm. rewrite ident_eqb_refl in Hm.
    apply sep_proj1 in Hm.
    apply sepall_in in Hin.
    destruct Hin as [ws [xs [Hsplit Hin]]].
    rewrite Hin in Hm. clear Hsplit Hin.
    apply sep_proj1 in Hm. clear ws xs.
    unfold staterep_mems in Hm.
    rewrite Hoff in Hm. clear Hoff.
    apply loadv_rule in Hm.
    destruct Hm as [v' [Hloadv Hmatch]].
    unfold match_value in Hmatch.
    unfold mfind_mem in Hv; simpl in Hv.
    rewrite Hv in Hmatch; clear Hv.
    rewrite Hmatch in Hloadv; clear Hmatch.
    apply Clight.deref_loc_value with (2:=Hloadv); auto.
  Qed.

  Lemma staterep_assign_mem:
    forall P cls prog' m m' me b ofs x ty d v,
      (P me -*> P (madd_mem x v me)) ->
      access_mode (cltype ty) = By_value (type_chunk ty) ->
      NoDup cls.(c_objs) ->
      NoDupMembers cls.(c_mems) ->
      m |= staterep gcenv (cls::prog') cls.(c_name) me b ofs ** P me ->
      In (x, ty) cls.(c_mems) ->
      field_offset gcenv x (make_members cls) = Errors.OK d ->
      v = Values.Val.load_result (type_chunk ty) v ->
      Clight.assign_loc gcenv (cltype ty) m b (Int.repr (ofs + d)) v m' ->
      m' |= staterep gcenv (cls::prog') cls.(c_name) (madd_mem x v me) b ofs
               ** P (madd_mem x v me).
  Proof.
    intros ** HPimp Hty Hcls Hmem Hm Hin Hoff Hlr Hal.
    rewrite <-HPimp; clear HPimp.
    Opaque sepconj. simpl in *. Transparent sepconj.
    rewrite ident_eqb_refl in *.
    rewrite sep_assoc. rewrite sep_assoc in Hm.
    apply sepall_in in Hin.
    destruct Hin as [ws [xs [Hsplit Hin]]].
    rewrite Hsplit in Hmem.
    rewrite Hin in Hm. rewrite sep_assoc in Hm.
    rewrite Hin. rewrite sep_assoc.
    unfold staterep_mems in *.
    rewrite Hoff in *.
    rewrite sep_swap2.
    rewrite sepall_switchp
    with (f':=fun xty : ident * type =>
                let (x0, ty0) := xty in
                match field_offset gcenv x0 (make_members cls) with
                | Errors.OK d0 =>
                  contains (type_chunk ty0) b (ofs + d0)
                           (match_value (mm_values me) x0)
                | Errors.Error _ => sepfalse
                end) at 1.
    - rewrite <-sep_swap2.
      eapply storev_rule2 with (1:=Hm).
      + unfold match_value. simpl.
        rewrite PM.gss. symmetry; exact Hlr.
      + clear Hlr. inversion Hal as [? ? ? Haccess|? ? ? ? Haccess].
        * rewrite Hty in Haccess.
          injection Haccess. intro; subst. assumption.
        * rewrite Hty in Haccess. discriminate.
    - apply NoDupMembers_remove_1 in Hmem.
      apply NoDupMembers_NoDup with (1:=Hmem).
    - intros x' Hin'; destruct x' as [x' ty'].
      unfold madd_mem; simpl.
      rewrite match_value_add; [reflexivity|].
      apply NoDupMembers_app_cons in Hmem.
      destruct Hmem as [Hmem].
      apply In_InMembers in Hin'.
      intro Heq. apply Hmem. rewrite Heq in Hin'.
      assumption.
  Qed.

  Lemma staterep_field_offset:
    forall m me cls prog b ofs x ty P,
      m |= staterep gcenv (cls :: prog) cls.(c_name) me b ofs ** P ->
      In (x, ty) (c_mems cls) ->
      exists d, field_offset gcenv x (make_members cls) = Errors.OK d
           /\ 0 <= ofs + d <= Int.max_unsigned.
  Proof.
    intros ** Hm Hin.
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
   
  (* Lemma staterep_inst_offset: *)
  (*   forall m me cls p b ofs o c P, *)
  (*     m |= staterep gcenv (cls :: p) cls.(c_name) me b ofs ** P -> *)
  (*     0 <= ofs -> *)
  (*     In (o, c) (c_objs cls) -> *)
  (*     exists d, field_offset gcenv o (make_members cls) = Errors.OK d *)
  (*          /\ 0 <= ofs + d <= Int.max_unsigned. *)
  (* Proof. *)
  (*   Opaque sepconj. *)
  (*   intros ** Hm ? Hin. *)
  (*   apply sep_proj1 in Hm. *)
  (*   simpl in Hm. rewrite ident_eqb_refl in Hm. *)
  (*   apply sep_proj2 in Hm. *)
  (*   apply sepall_in in Hin; destruct Hin as [ws [xs [Hsplit Hin]]]. *)
  (*   rewrite Hin in Hm. clear Hsplit Hin. *)
  (*   apply sep_proj1 in Hm. *)
  (*   clear ws xs. *)
  (*   destruct (field_offset gcenv o (make_members cls)) eqn: E. *)
  (*   2: contradict Hm. *)
  (*   exists z; split; auto. *)
  (*   apply field_offset_in_range' in E. *)
  (*   revert c me o z Hm E. *)
  (*   induction p as [|c']; intros ** Hm E; simpl in Hm. *)
  (*   1: contradiction. *)
  (*   destruct (ident_eqb c (c_name c')). *)
  (*   - destruct (c_mems c') as [|(x, ?)] eqn: Mems; simpl in Hm. *)
  (*     + destruct (c_objs c') as [|(o', ?)] eqn: Objs; simpl in Hm. *)
  (*       * admit. *)
  (*       * apply sep_drop, sep_pick1 in Hm. *)
  (*         destruct (field_offset gcenv o' (make_members c')) eqn: E'. *)
  (*         2: contradict Hm. *)
  (*         apply field_offset_in_range' in E'. *)
  (*         rewrite <-Z.add_assoc in Hm. *)
  (*         edestruct IHp; eauto; omega. *)
  (*     + apply sep_proj1, sep_proj1 in Hm. *)
  (*       destruct (field_offset gcenv x (make_members c')) eqn: E'. *)
  (*       2: contradict Hm. *)
  (*       apply contains_no_overflow in Hm. *)
  (*       apply field_offset_in_range' in E'. *)
  (*       destruct Hm; omega. *)
  (*   - eapply IHp; eauto. *)
  (* Qed. *)

End StateRepProperties.

Section BlockRep.
  Variable ge : composite_env.
  Hypothesis ge_consistent : composite_env_consistent ge.

  (* TODO: name predicate "blockrep" and write sepall blockrep xs *)
  Definition blockrep (ve: stack) (flds: members) (b: block) : massert :=
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
      PM.find x ve = Some v ->
      field_offset ge x (co_members co) = Errors.OK d ->
      Clight.deref_loc ty m b (Int.repr d) v.
  Proof.
    intros ** Hm Hin Hv Hoff.
    unfold blockrep in Hm.
    apply sepall_in in Hin.
    destruct Hin as [ws [xs [Hsplit Hin]]].
    rewrite Hin in Hm. clear Hsplit Hin.
    do 2 apply sep_proj1 in Hm. clear ws xs.
    rewrite Hoff in Hm. clear Hoff.
    destruct (access_mode ty) eqn:Haccess; try contradiction.
    apply loadv_rule in Hm.
    destruct Hm as [v' [Hloadv Hmatch]].
    unfold match_value in Hmatch.
    rewrite Hv in Hmatch. clear Hv.
    rewrite Hmatch in Hloadv. clear Hmatch.
    apply Clight.deref_loc_value with (1:=Haccess) (2:=Hloadv).
  Qed.

  Lemma blockrep_assign_mem:
    forall P co m m' ve b d x v ty chunk,
      NoDupMembers (co_members co) ->
      m |= blockrep ve (co_members co) b ** P ve ->
      In (x, ty) (co_members co) ->
      field_offset ge x (co_members co) = Errors.OK d ->
      access_mode ty = By_value chunk ->
      v = Val.load_result chunk v ->
      Clight.assign_loc ge ty m b (Integers.Int.repr d) v m' ->
      massert_imp (P ve) (P (PM.add x v ve)) ->
      m' |= blockrep (PM.add x v ve) (co_members co) b ** P (PM.add x v ve).
  Proof.
    Opaque sepconj.
    intros ** Hndup Hm Hin Hoff Haccess Hlr Hal HP.
    apply sepall_in in Hin.
    destruct Hin as [ws [xs [Hsplit Hin]]].
    unfold blockrep in *.
    rewrite Hin in Hm. rewrite sep_assoc in Hm.
    rewrite Hin. rewrite sep_assoc.
    rewrite Hoff in *.
    rewrite sep_swap2.
    rewrite Haccess in *.
    rewrite Hsplit in Hndup.
    rewrite sepall_swapp.
    - rewrite <-sep_swap2.
      rewrite HP in Hm.
      eapply storev_rule2 with (1:=Hm).
      + unfold match_value. rewrite PM.gss. symmetry. exact Hlr.
      + inversion Hal as [? ? ? Haccess'|]; rewrite Haccess in *.
        * injection Haccess'. intro HR; rewrite <-HR in *; assumption.
        * discriminate.
    - intros x' Hin'; destruct x' as [x' ty'].
      rewrite match_value_add; [reflexivity|].
      apply NoDupMembers_app_cons in Hndup.
      destruct Hndup as [Hndup].
      apply In_InMembers in Hin'.
      intro Heq. apply Hndup. rewrite Heq in Hin'.
      assumption.
  Qed.

  Lemma sizeof_by_value:
    forall ty chunk,
      access_mode ty = By_value chunk ->
      sizeof ge ty = Memdata.size_chunk chunk.
  Proof.
    destruct ty; try (intros; discriminate);
      [destruct i, s, a|destruct s, a|destruct f, a|];
      injection 1; intros; subst; reflexivity.
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
      massert_eqv (sepall (field_range ge flds b 0) flds)
                  (blockrep (PM.empty val) flds b).
  Proof.
    intros ** Hndups Hchunk.
    unfold blockrep.
    apply sepall_swapp.
    intros fld Hin.
    destruct fld as [x ty].
    unfold field_range.
    destruct (field_offset ge x flds) eqn:Hoff.
    2:reflexivity.
    apply field_offset_aligned with (ty:=ty) in Hoff.
    2:apply in_field_type with (1:=Hndups) (2:=Hin).
    destruct (Hchunk _ _ Hin) as [chunk [Haccess Halign]].
    rewrite Haccess.
    split; [split|split].
    - intros m Hr.
      rewrite match_value_empty.
      apply range_contains'.
      now apply Zdivides_trans with (1:=Halign) (2:=Hoff).
      rewrite <-sizeof_by_value with (1:=Haccess).
      assumption.
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
      massert_imp (range b 0 (co_sizeof co))
                  (blockrep (PM.empty val) (co_members co) b).
  Proof.
    intros ** Hco Hstruct Hndups Hchunk.
    rewrite split_range_fields
    with (1:=ge_consistent) (2:=Hco) (3:=Hstruct) (4:=Hndups).
    rewrite blockrep_empty' with (1:=Hndups) (2:=Hchunk).
    reflexivity.
  Qed.

  Lemma blockrep_any_empty:
    forall flds ve b,
      blockrep ve flds b -*> blockrep sempty flds b.
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

  Lemma blockrep_nodup:
    forall xs vs flds ve ob,
      NoDupMembers (xs ++ flds) ->
      blockrep ve flds ob <-*-> blockrep (adds (map fst xs) vs ve) flds ob.
  Proof.
    intros ** Nodup.
    unfold blockrep.
    apply sepall_swapp.
    intros (x, t) Hin.
    destruct (field_offset ge x flds); auto.
    destruct (access_mode t); auto.
    revert vs ve.
    induction xs as [|(x', t')], vs; unfold adds in *; simpl; auto.
    rewrite <-app_comm_cons, nodupmembers_cons in Nodup.
    destruct Nodup as [Notin Nodup].
    intro ve.
    unfold match_value in *.
    rewrite PM.gso.
    + apply IHxs; auto.
    + intro; subst; apply Notin.
      rewrite InMembers_app; right.
      eapply In_InMembers; eauto.
  Qed.

  Lemma blockrep_findvars:
    forall ve xs vs b,
      Forall2 (fun x v => PM.find x ve = Some v) (map fst xs) vs ->
      blockrep ve xs b -*> blockrep (adds (map fst xs) vs sempty) xs b.
    Proof.
      unfold  adds; simpl.
      intros ** Findvars.
      unfold blockrep.
      apply sepall_weakenp.
      intros (x, t) Hin.
      destruct (field_offset ge x xs); auto.
      destruct (access_mode t); auto.
      apply contains_imp.
      unfold match_value.
      intros v Findx.
      revert vs Findvars.
      induction xs as [|(x', t')], vs; simpl; intro Findvars;
      try (rewrite PM.gempty; auto).
      inversion Findvars as [|y ? ys ? Find Findvars']; subst; clear Findvars.
      destruct (split xs) as (g, d).
      simpl in *.
      destruct (ident_eqb x x') eqn: E.
      - apply ident_eqb_eq in E; subst x'.
        rewrite Find in Findx.
        rewrite PM.gss; auto.
      - apply ident_eqb_neq in E.
        destruct Hin as [Eq|?].
        + inv Eq; now contradict E.
        + rewrite PM.gso.
          apply IHxs; auto.
          exact E.
    Qed.

  Lemma blockrep_field_offset:
    forall m ve flds b x ty P,
      m |= blockrep ve flds b ** P ->
      In (x, ty) flds ->
      exists d, field_offset ge x flds = Errors.OK d
           /\ 0 <= d <= Int.max_unsigned.
  Proof.
    intros ** Hm Hin.
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

End BlockRep.

Hint Resolve footprint_perm_blockrep footprint_decidable_blockrep.

