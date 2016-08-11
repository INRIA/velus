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
Require Import LibTactics.

Require Import Sep Syn Sem Tra.

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
  forall me ve x v1 v2,
    match_value ve x v1 ->
    find_var (me, ve) x v2 ->
    v1 = v2.
Proof.
  unfold match_value, find_var; simpl.
  intros ** Hm Hf.
  destruct (PM.find x ve).
  - subst; inverts* Hf.
  - discriminate.
Qed.

Definition instance_match (me: menv) (i: ident): menv :=
  match mfind_inst i me with
  | None => m_empty
  | Some i => i
  end.

Lemma instance_match_empty:
  forall x, instance_match m_empty x = m_empty.
Proof.
  intros. unfold instance_match, mfind_inst; simpl.
  rewrite PM.gempty. reflexivity.
Qed.

Section Staterep.
  Variable ge : composite_env.

  Definition staterep_mems (cls: class) (me: menv) (b: block) (ofs: Z) (xty: ident * typ) :=
    let (x, ty) := xty in
    match field_offset ge x (make_members cls) with
    | Errors.OK d =>
	  contains (chunk_of_type ty) b (ofs + d) (match_value me.(mm_values) x)
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
        sepall (fun (o: ident * ident) =>
                  let (i, c) := o in
                  match field_offset ge i (make_members cls) with
                  | Errors.OK d =>
                    staterep p' c (instance_match me i) b (ofs + d)
                  | Errors.Error _ => sepfalse
                  end) cls.(c_objs)
      else staterep p' clsnm me b ofs
    end.

  Definition staterep_objs (p': program) (cls: class) (me: menv) (b: block) (ofs: Z) (o: ident * ident) :=
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
    introv Find.
    forwards ?: find_class_name Find; subst.
    forwards (? & Hprog & FindNone): find_class_app Find.
    rewrite Hprog.
    rewrite* staterep_skip_app.
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
    Forall (fun (x: ident * type) =>
              (alignof env (snd x) | co_alignof co))
           (co_members co).
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
    Ctypes.access_mode t = Ctypes.By_value (chunk_of_type t) ->
    sizeof gcenv t = Memdata.size_chunk (chunk_of_type t).
Proof.
  destruct t;
  (destruct i, s || destruct f || idtac);
  (discriminates || contradiction || auto).
Qed.

Lemma align_chunk_divides_alignof_type:
  forall gcenv t,
    Ctypes.access_mode t = Ctypes.By_value (chunk_of_type t) ->
    (Memdata.align_chunk (chunk_of_type t) | alignof gcenv t).
Proof.
  destruct t;
  (destruct i, s || destruct f || idtac);
  (discriminates || contradiction || auto);
  simpl; try rewrite align_noattr; simpl.
Admitted.

Lemma in_translate_param_chunked:
  forall ge (flds: list (ident * typ)) x ty,
    Ctypes.access_mode ty = Ctypes.By_value (chunk_of_type ty) ->
    In (x, ty) flds ->
    exists chunk,
      access_mode ty = By_value chunk
      /\ (Memdata.align_chunk chunk | alignof ge ty).
Proof.
  intros ** ? Hin.
  exists (chunk_of_type ty).
  split*.
  now apply align_chunk_divides_alignof_type.
Qed.

Section StateRepProperties.

  Variable main_node : ident.
  Variable prog: program.
  Variable tprog: Clight.program.

  Let tge := Clight.globalenv tprog.
  Let gcenv := Clight.genv_cenv tge.

  Definition pointer_of_node node := pointer_of (type_of_inst node).

  Hypothesis TRANSL: translate prog main_node = Errors.OK tprog.
  Hypothesis main_node_exists: find_class main_node prog <> None.

  Lemma make_members_co:
    forall clsnm cls prog',
      find_class clsnm prog = Some (cls, prog') ->
      (exists co, gcenv!clsnm = Some co
             /\ co_su co = Struct
             /\ co_members co = make_members cls
             /\ attr_alignas (co_attr co) = None
             /\ NoDupMembers (co_members co)).
  Proof.
    unfold translate in TRANSL.
    apply not_None_is_Some in main_node_exists.
    destruct main_node_exists as [[maincls prog'] Hfind_main].
    rewrite Hfind_main in TRANSL.
    destruct (map (translate_class prog) prog) as [|cls clss] eqn:Hmap.
    - apply map_eq_nil in Hmap.
      rewrite Hmap in Hfind_main; simpl in *; discriminate.
    -
  Admitted.

  Lemma field_translate_mem_type:
    forall clsnm cls prog',
      find_class clsnm prog = Some (cls, prog') ->
      NoDupMembers (make_members cls) ->
      forall x ty,
        In (x, ty) cls.(c_mems) ->
        field_type x (make_members cls) = Errors.OK ty.
  Proof.
    introv Hfind Hndup Hin.
    apply in_field_type with (1:=Hndup).
    unfold make_members. apply in_app_iff. now left.
  Qed.

  Lemma field_translate_obj_type:
    forall clsnm cls prog',
      find_class clsnm prog = Some (cls, prog') ->
      NoDupMembers (make_members cls) ->
      forall o c,
        In (o, c) cls.(c_objs) ->
        field_type o (make_members cls) = Errors.OK (type_of_inst c).
  Proof.
    introv Hfind Hndup Hin.
    apply in_field_type with (1:=Hndup).
    unfold make_members. apply in_app_iff. right.
    apply in_map_iff. exists* (o, c).
  Qed.

  (* TODO: Construct a global environment of structs for a given program. *)

  Lemma gcenv_consistent:
    composite_env_consistent gcenv.
  Admitted.

  Lemma range_staterep:
    forall b clsnm,
      WelldefClasses prog ->
      find_class clsnm prog <> None ->
      range b 0 (sizeof gcenv (type_of_inst clsnm)) -*>
            staterep gcenv prog clsnm m_empty b 0.
  Proof.
    introv Hwdef Hfind.
    cut (forall lo,
           (alignof gcenv (type_of_inst clsnm) | lo) ->
           massert_imp (range b lo (lo + sizeof gcenv (type_of_inst clsnm)))
                       (staterep gcenv prog clsnm m_empty b lo)).
    - intro HH; apply HH; apply Z.divide_0_r.
    - clear main_node_exists TRANSL.

      revert clsnm Hfind.
      induction prog as [|cls prog' IH]; intros clsnm Hfind lo.
      + apply not_None_is_Some in Hfind.
        destruct Hfind. discriminate.
      + intro Halign.
        inversion Hwdef as [|? ? Hwdef']; subst.

        assert (find_class clsnm prog = Some (cls, prog')) as Hprog.
        admit.
        (* TODO: need to link prog to (possibly reversed) translation *)

        pose proof (make_members_co _ _ _ Hprog) as Hmco.
        destruct Hmco as [co [Hg [Hsu [Hmem [Hattr Hndup]]]]].

        pose proof (co_members_alignof _ _ (gcenv_consistent _ _ Hg) Hattr)
          as Hcoal.
        rewrite Hmem in Hcoal.
        unfold make_members in Hcoal.
        apply Forall_app in Hcoal.
        destruct Hcoal as [Hcoal1 Hcoal2].
        simpl in Halign.
        rewrite Hg in Halign.
        rewrite align_noattr in Halign.
        assert (Hndup':=Hndup). rewrite Hmem in Hndup'.

        simpl.
        unfold staterep_mems.
        destruct (ident_eqb clsnm cls.(c_name)) eqn:Hclsnm.
        *{ rewrite Hg.
           rewrite <-Hmem.
           rewrite split_range_fields
           with (1:=gcenv_consistent) (2:=Hg) (3:=Hsu) (4:=Hndup).
           unfold field_range. (* try to do without unfolding here *)
           rewrite Hmem at 1.
           unfold make_members.
           rewrite sepall_app.

           apply sep_imp'.

           - pose proof (field_translate_mem_type _ _ _ Hprog Hndup') as Htype.
             clear Hcoal2.

             induction (c_mems cls); auto.
             apply Forall_cons2 in Hcoal1.
             destruct Hcoal1 as [Hcoal1 Hcoal2].

             apply sep_imp'.
             + destruct a.
               destruct (field_offset gcenv i (co_members co)) eqn:Hfo; auto.
               rewrite match_value_empty.
               rewrite sizeof_translate_chunk.
               *{ apply range_contains'.
                  specialize (Htype i t).
                  rewrite <-Hmem in Htype.
                  apply field_offset_aligned with (ty:=t) in Hfo.
                  - simpl in Hcoal1.
                    apply Z.divide_add_r.
                    + apply Zdivide_trans with (2:=Halign).
                      apply Zdivide_trans with (2:=Hcoal1).
                      apply align_chunk_divides_alignof_type.
                      admit.
                    + apply Zdivide_trans with (2:=Hfo).
                      apply align_chunk_divides_alignof_type.
                      admit.
                  - apply Htype; constructor; reflexivity.
                }
               * admit.
             + apply IHl.
               * apply Hcoal2.
               * intros; apply Htype; constructor (assumption).

           - pose proof (field_translate_obj_type _ _ _ Hprog Hndup') as Htype.
             rewrite <-Hmem in Htype.

             induction (c_objs cls); auto.
             simpl.
             apply sep_imp'.
             + clear IHl.

               destruct a as [o c].
               assert (find_class c prog' <> None) as Hcin
                   by (eapply H1; econstructor; eauto).
               clear H1 Hcoal1.

               apply Forall_cons2 in Hcoal2.
               destruct Hcoal2 as [Hcoal2 Hcoal3].

               specialize (Htype o c (in_eq _ _)).
               clear Hcoal3 l.

               simpl.
               destruct (field_offset gcenv o (co_members co)) eqn:Hfo; auto.
               rewrite instance_match_empty.
               specialize (IH Hwdef' c Hcin (lo + z)%Z).

               apply not_None_is_Some in Hcin.
               destruct Hcin as ((c' & prog'') & Hcin).
               assert (find_class c prog = Some (c', prog'')) as Hcin'.
               admit. (* TODO: make_members_co should be more flexible. *)

               assert (Hcin'' := Hcin').
               apply make_members_co in Hcin'.
               destruct Hcin' as [? [? [? [? [? ?]]]]].
               rewrite H.

               simpl in IH.
               rewrite H in IH.
               apply IH.

               simpl in Hcoal2.
               rewrite align_noattr in Hcoal2.
               rewrite H in Hcoal2.

               rewrite align_noattr.
               apply Z.divide_add_r.
               * apply Zdivide_trans with (1:=Hcoal2).
                 assumption.

               * simpl in Htype.
                 eapply field_offset_aligned in Hfo.
                 2:apply Htype.
                 apply Zdivide_trans with (2:=Hfo).
                 simpl. rewrite H, align_noattr.
                 apply Z.divide_refl.
             + apply IHl.
               * clear IHl. intros o c' Hin.
                 apply H1 with (o:=o). constructor (assumption).
               * simpl in Hcoal2. apply Forall_cons2 in Hcoal2.
               destruct Hcoal2 as [Hcoal2 Hcoal3]. exact Hcoal3.
               * intros o c Hin. apply Htype. constructor (assumption).
         }

        * rewrite Hg.
          simpl in Hfind.
          rewrite ident_eqb_sym in Hclsnm.
          rewrite Hclsnm in Hfind.
          specialize (IH Hwdef' clsnm Hfind lo).
          simpl in IH.
          rewrite Hg in IH.
          apply IH.
          rewrite align_noattr.
          assumption.
  Qed.

  Lemma staterep_deref_mem:
    forall cls prog' m me ve b ofs x ty d v P,
      access_mode ty = By_value (chunk_of_type ty) ->
      m |= staterep gcenv (cls::prog') cls.(c_name) me b ofs ** P ->
      In (x, ty) cls.(c_mems) ->
      find_field (me, ve) x v ->
      field_offset gcenv x (make_members cls) = Errors.OK d ->
      Clight.deref_loc ty m b (Int.repr (ofs + d)) v.
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
    unfold find_field, mfind_mem in Hv; simpl in Hv.
    rewrite Hv in Hmatch. clear Hv.
    rewrite Hmatch in Hloadv. clear Hmatch.
    apply Clight.deref_loc_value with (2:=Hloadv); auto.
  Qed.

  Lemma staterep_assign_mem:
    forall P cls prog' m m' me b ofs x ty d v,
      (P me -*> P (madd_mem x v me)) ->
      access_mode ty = By_value (chunk_of_type ty) ->
      NoDup cls.(c_objs) ->
      NoDupMembers cls.(c_mems) ->
      m |= staterep gcenv (cls::prog') cls.(c_name) me b ofs ** P me ->
      In (x, ty) cls.(c_mems) ->
      field_offset gcenv x (make_members cls) = Errors.OK d ->
      v = Values.Val.load_result (chunk_of_type ty) v ->
      Clight.assign_loc gcenv ty m b (Int.repr (ofs + d)) v m' ->
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
    with (f':=fun xty : ident * typ =>
                let (x0, ty0) := xty in
                match field_offset gcenv x0 (make_members cls) with
                | Errors.OK d0 =>
                  contains (chunk_of_type ty0) b (ofs + d0)
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
      unfold update_field, madd_mem; simpl.
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
    introv Hm Hin.
    Opaque sepconj. simpl in Hm. Transparent sepconj.
    rewrite ident_eqb_refl in Hm.
    do 2 apply sep_proj1 in Hm.
    apply sepall_in in Hin; destruct Hin as [ws [xs [Hsplit Hin]]].
    rewrite Hin in Hm. clear Hsplit Hin.
    apply sep_proj1 in Hm.
    clear ws xs.
    unfold staterep_mems in Hm.
    destruct (field_offset gcenv x (make_members cls)).
    + exists z; split*.
      apply* contains_no_overflow.
    + contradict Hm.
  Qed.

  Lemma staterep_inst_offset:
    forall m me cls prog b ofs o c P,
      m |= staterep gcenv (cls :: prog) cls.(c_name) me b ofs ** P ->
      In (o, c) (c_objs cls) ->
      exists d, field_offset gcenv o (make_members cls) = Errors.OK d.
  Proof.
    introv Hm Hin.
    apply sep_proj1 in Hm.
    simpl in Hm. rewrite ident_eqb_refl in Hm.
    apply sep_proj2 in Hm.
    apply sepall_in in Hin; destruct Hin as [ws [xs [Hsplit Hin]]].
    rewrite Hin in Hm. clear Hsplit Hin.
    apply sep_proj1 in Hm.
    clear ws xs.
    destruct (field_offset gcenv o (make_members cls)).
    + exists z; split*.
    + contradict Hm.
  Qed.

End StateRepProperties.

Section BlockRep.
  Variable ge : composite_env.
  Hypothesis ge_consistent : composite_env_consistent ge.

  (* TODO: name predicate "blockrep" and write sepall blockrep xs *)
  Definition blockrep (ve: venv) (flds: members) (b: block) : massert :=
    sepall (fun xty : ident * type =>
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

  Hint Resolve footprint_perm_blockrep footprint_decidable_blockrep.

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
      blockrep ve flds b -*> blockrep v_empty flds b.
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
      blockrep ve flds ob <-*-> blockrep (adds xs vs ve) flds ob.
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
    + apply* IHxs.
    + intro; subst; apply Notin.
      rewrite InMembers_app; right.
      eapply In_InMembers; eauto.
  Qed.

    Lemma blockrep_findvars:
    forall S xs vs b,
      find_vars S xs vs ->
      blockrep (snd S) xs b -*> blockrep (adds xs vs v_empty) xs b.
    Proof.
      destruct S as (?, ve); unfold find_vars, find_var, adds; simpl.
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
      induction xs as [|(x', t')], vs; simpl; intro Findvars.
      - rewrite* PM.gempty.
      - rewrite* PM.gempty.
      - rewrite* PM.gempty.
      - inversion Findvars as [|y ? ys ? Find Findvars' Heq]; subst; clear Findvars.
        destruct (split xs) as (g, d).
        simpl in *; inverts Heq.
        destruct (ident_eqb x x') eqn: E.
        + apply ident_eqb_eq in E; subst x'.
          rewrite Find in Findx.
          rewrite PM.gss; auto.
        + apply ident_eqb_neq in E.
          destruct Hin as [Eq|?].
          * inverts Eq; now contradict E.
          * rewrite* PM.gso.
            apply* IHxs.
    Qed.

  Lemma blockrep_field_offset:
    forall m ve flds b x ty P,
      m |= blockrep ve flds b ** P ->
      In (x, ty) flds ->
      exists d, field_offset ge x flds = Errors.OK d
           /\ 0 <= d <= Int.max_unsigned.
  Proof.
    introv Hm Hin.
    unfold blockrep in Hm.
    apply sepall_in in Hin.
    destruct Hin as [ws [xs [Hsplit Hin]]].
    rewrite Hin in Hm. clear Hsplit Hin.
    do 2 apply sep_proj1 in Hm. clear ws xs.
    destruct (field_offset ge x flds).
    - exists* z; split*.
      destruct (access_mode ty).
      + apply* contains_no_overflow.
      + contradict Hm.
      + contradict Hm.
      + contradict Hm.
    - contradict Hm.
  Qed.

End BlockRep.
