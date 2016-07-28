Require Import common.Separation.
Require Import common.Values.
Require Import common.Errors.
Require Import cfrontend.Ctypes.
Require Import lib.Maps.
Require Import lib.Coqlib.
Require Import lib.Integers.

Require Import Rustre.Common.
Require Import Rustre.RMemory.
Require Import Syn Sem Tra.

Require Import List.
Require Import ZArith.BinInt.

Require Import Program.Tactics.
Require Import LibTactics.

Open Scope list.
Open Scope sep_scope.
Open Scope Z.

Notation "m -*> m'" := (massert_imp m m') (at level 70, no associativity) : sep_scope.
Notation "m <-*-> m'" := (massert_eqv m m') (at level 70, no associativity) : sep_scope.

Lemma storev_rule':
  forall chunk m m' b ofs v (spec1 spec: val -> Prop) P,
    m |= contains chunk b ofs spec1 ** P ->
    spec (Val.load_result chunk v) ->
    Memory.Mem.storev chunk m (Vptr b (Int.repr ofs)) v = Some m' ->
    m' |= contains chunk b ofs spec ** P.
Proof.
  intros ** Hm Hspec Hstore.
  apply storev_rule with (1:=Hm) in Hspec.
  destruct Hspec as [m'' [Hmem Hspec]].
  rewrite Hmem in Hstore. injection Hstore.
  intro; subst. assumption.
Qed.

(* Introduce sepall *)

Program Definition sepemp: massert :=  pure True.

Lemma sepemp_disjoint:
  forall P, disjoint_footprint P sepemp.
Proof.
  unfold disjoint_footprint. auto.
Qed.

Lemma sepemp_right:
  forall P,
    P <-*-> (P ** sepemp).
Proof.
  split; split; simpl; try (auto using sepemp_disjoint); intuition.
Qed.

Lemma sepemp_left:
  forall P,
    P <-*-> (sepemp ** P).
Proof.
  intros. rewrite sep_comm. rewrite <-sepemp_right. reflexivity.
Qed.

Program Definition sepfalse: massert :=
  {| m_pred := fun m => False;
     m_footprint := fun b ofs => True |}.
Next Obligation.
  contradiction.
Defined.

Section Sepall.
  Context {A: Type}.

  Fixpoint sepall (p: A -> massert) (xs: list A) : massert :=
    match xs with
    | nil => sepemp
    | x::xs => p x ** sepall p xs
    end.

  Lemma sepall_cons:
    forall p x xs,
      sepall p (x::xs) <-*-> p x ** sepall p xs.
  Proof.
    constructor; constructor; trivial.
  Qed.

  Lemma sepall_app:
    forall p xs ys,
      sepall p (xs ++ ys) <-*-> sepall p xs ** sepall p ys.
  Proof.
    induction xs.
    - intros. 
      rewrite sep_comm.
      rewrite <-sepemp_right.
      reflexivity.
    - intros.
      simpl.
      rewrite sep_assoc.
      rewrite IHxs.
      reflexivity.
  Qed.

  Lemma sepall_breakout:
    forall ys ws x xs p,
      ys = ws ++ x :: xs ->
      sepall p ys <-*-> p x ** sepall p (ws ++ xs).
  Proof.
    intros ** Hys.
    rewrite sepall_app.
    rewrite sep_swap.
    rewrite <-sepall_cons.
    rewrite <-sepall_app.
    rewrite <-Hys.
    reflexivity.
  Qed.

  Lemma sepall_in:
    forall x ys,
      In x ys ->
      exists ws xs,
        ys = ws ++ x :: xs
        /\ (forall p,
              sepall p ys <-*-> p x ** sepall p (ws ++ xs)).
  Proof.
    intros x ys Hin.
    apply in_split in Hin.
    destruct Hin as [ws [xs Hys]].
    exists ws xs.
    split; auto. 
    intro p. apply sepall_breakout with (1:=Hys).
  Qed.

  Lemma sepall_sepfalse:
    forall m p xs,
      m |= sepall p xs ->
      (forall x, In x xs -> p x <> sepfalse).
  Proof.
    intros m p xs Hall x Hin Hp.
    apply sepall_in in Hin.
    destruct Hin as [ws [ys [Hys Heq]]].
    rewrite Heq in Hall.
    apply sep_comm in Hall.
    apply sep_drop in Hall.
    rewrite Hp in Hall.
    destruct Hall.
  Qed.

  Lemma sepall_switchp:
    forall f f' xs,
      List.NoDup xs ->
      (forall x, In x xs -> f x = f' x) ->
      sepall f xs <-*-> sepall f' xs.
  Proof.
    induction xs as [|x xs IH].
    reflexivity.
    intros Hdup Hin.
    inversion_clear Hdup.
    repeat rewrite sepall_cons.
    rewrite Hin; [|now apply in_eq].
    rewrite IH; [reflexivity|assumption|].
    intros; apply Hin. constructor (assumption).
  Qed.

End Sepall.

Section SplitRange.
  Variable env: composite_env.
  Variable id: ident.
  Variable co: composite.

  Hypothesis Henv: Ctypes.composite_env_consistent env.
  Hypothesis Hco: env!id = Some co.
  Hypothesis Hstruct: co_su co = Struct.

  Lemma split_range_fields':
    forall b lo,
      NoDupMembers (co_members co) ->
      range b lo (lo + sizeof_struct env 0 (co_members co)) -*>
            sepall (fun (fld: ident * type) =>
                      let (id, ty) := fld in
                      match field_offset env id (co_members co) with
                      | OK ofs  => range b (lo + ofs) (lo + ofs + sizeof env ty)
                      | Error _ => sepfalse
                      end) (co_members co).
  Proof.
    intros b lo Hndup.
    cut (forall cur,
            massert_imp
              (range b (lo + cur)
                       (lo + sizeof_struct env cur (co_members co)))
              (sepall (fun fld : ident * type =>
                         let (id0, ty) := fld in
                         match field_offset_rec env id0 (co_members co) cur with
                         | OK ofs => range b (lo + ofs) (lo + ofs + sizeof env ty)
                         | Error _ => sepfalse
                         end) (co_members co))).
    - intro HH.
      specialize HH with 0. rewrite Z.add_0_r in HH.
      apply HH.
    - induction (co_members co) as [|x xs IH]; [now constructor|].
      destruct x as [id' ty'].
      apply nodupmembers_cons in Hndup.
      destruct Hndup as [Hnin Hndup].
      specialize (IH Hndup).
      intro cur.
      Opaque sepconj. simpl.
      rewrite peq_true.
      erewrite sepall_switchp.
      2:now apply NoDupMembers_NoDup.
      + rewrite range_split'
        with (mid:=lo + (align cur (alignof env ty') + sizeof env ty')).
        * apply sep_imp'.
          2:now apply IH.
          rewrite range_split'
          with (mid:=lo + align cur (alignof env ty')).
          rewrite sep_drop. rewrite Z.add_assoc. reflexivity.
          split.
          now apply Z.add_le_mono_l; apply align_le; apply alignof_pos.
          apply Z.add_le_mono_l.
          rewrite <-Z.add_0_r at 1. apply Z.add_le_mono_l.
          apply Z.ge_le. apply sizeof_pos.
        * split.
          2:now apply Z.add_le_mono_l; apply sizeof_struct_incr.
          apply Z.add_le_mono_l.
          rewrite <-Z.add_0_r at 1. apply Z.add_le_mono.
          apply align_le. apply alignof_pos.
          apply Z.ge_le. apply sizeof_pos.
      + intros fld Hin.
        destruct fld.
        rewrite peq_false.
        reflexivity.
        intro Heq; subst.
        apply Hnin.
        eapply In_InMembers; eassumption.
  Qed.

  (* A useful lemma for accessing a struct through its fields. It is an
     implication rather than an equivalence since information about
     inter-field padding is lost. It is thus not possible to recover the
     range from the sepall, which may inhibit reasoning about By_copy
     assignments of complete records. *)
  Lemma split_range_fields:
    forall b lo,
      NoDupMembers (co_members co) ->
      range b lo (lo + co_sizeof co) -*>
            sepall (fun (fld: ident * type) =>
                      let (id, ty) := fld in
                      match field_offset env id (co_members co) with
                      | OK ofs  => range b (lo + ofs) (lo + ofs + sizeof env ty)
                      | Error _ => sepfalse
                      end) (co_members co).
  Proof.
    intros b lo Hndup.
    apply Henv in Hco.
    rewrite (co_consistent_sizeof _ _ Hco).
    rewrite (co_consistent_alignof _ _ Hco).
    rewrite Hstruct.
    simpl.
    rewrite range_split'
    with (mid:=lo + sizeof_struct env 0 (co_members co)).
    - rewrite sep_comm. rewrite sep_drop.
      apply split_range_fields' with (1:=Hndup).
    - split.
      * rewrite <-Z.add_0_r at 1.
        apply Z.add_le_mono_l.
        apply sizeof_struct_incr.
      * apply Z.add_le_mono_l.
        apply align_le.
        apply alignof_composite_pos.
  Qed.

End SplitRange.

Definition match_value (e: PM.t val) (x: ident) (v': val) : Prop :=
  match PM.find x e with
  | None => True
  | Some v => v' = v
  end.

(* Definition match_var (S: state) := *)
(*   match_value (snd S). *)

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

Ltac app_match_find_var_det :=
  match goal with
  | H1: find_var (?me, ?ve) ?x ?v1,
        H2: match_value ?ve ?x ?v2 |- _ =>
    assert (v2 = v1) by (applys* match_find_var_det H2 H1); subst v1; clear H2
  end.

(* Definition match_field (me: menv) := *)
(*   match_value me.(mm_values). *)

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

  Fixpoint staterep
           (p: program) (clsnm: ident) (me: menv) (b: block) (ofs: Z): massert :=
    match p with
    | nil => sepfalse
    | cls :: p' =>
      if ident_eqb clsnm cls.(c_name)
      then
        sepall (fun (xty: ident * typ) =>
                  let (x, ty) := xty in
                  match field_offset ge x (make_members cls) with
                  | OK d =>
	                contains (chunk_of_type ty) b (ofs + d) (match_value me.(mm_values) x)
                  | Error _ => sepfalse
                  end) cls.(c_mems)
        **
        sepall (fun (o: ident * ident) =>
                  let (i, c) := o in
                  match field_offset ge i (make_members cls) with
                  | OK d =>
                    staterep p' c (instance_match me i) b (ofs + d)
                  | Error _ => sepfalse
                  end) cls.(c_objs)
      else staterep p' clsnm me b ofs
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
      ~ClassIn clsnm oprog ->
      staterep (oprog ++ prog) clsnm me b ofs <-*-> staterep prog clsnm me b ofs.
  Proof.
    intros ** Hnin.
    induction oprog as [|cls oprog IH].
    - rewrite app_nil_l. reflexivity.
    - apply NotClassIn in Hnin. destruct Hnin.
      rewrite <-app_comm_cons.
      rewrite staterep_skip_cons; auto.
  Qed.
  
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
    field_type x xs = OK ty.
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
        field_type x (make_members cls) = OK ty.
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
        field_type o (make_members cls) = OK (type_of_inst c).
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
        destruct (ident_eqb clsnm cls.(c_name)) eqn:Hclsnm.
        *{ rewrite Hg.
           rewrite <-Hmem.
           rewrite split_range_fields
           with (1:=gcenv_consistent) (2:=Hg) (3:=Hsu) (4:=Hndup).
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
               assert (ClassIn c prog') as Hcin
                   by (eapply H1; econstructor; eauto).
               clear H1 Hcoal1.

               apply Forall_cons2 in Hcoal2.
               destruct Hcoal2 as [Hcoal2 Hcoal3].
               
               specialize (Htype o c (in_eq _ _)).
               clear Hcoal3 l.

               simpl.
               destruct (field_offset gcenv o (co_members co)) eqn:Hfo; auto.
               rewrite instance_match_empty.
               apply ClassIn_find_class in Hcin.
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
    forall cls prog' m me ve b ofs x ty d v,
      access_mode ty = By_value (chunk_of_type ty) ->
      m |= staterep gcenv (cls::prog') cls.(c_name) me b ofs ->
      In (x, ty) cls.(c_mems) ->
      find_field (me, ve) x v ->
      field_offset gcenv x (make_members cls) = OK d ->
      Clight.deref_loc ty m b (Int.repr (ofs + d)) v.
  Proof.
    intros ** Hty Hm Hin Hv Hoff.
    simpl in Hm. rewrite ident_eqb_refl in Hm.
    apply sep_proj1 in Hm.
    apply sepall_in in Hin.
    destruct Hin as [ws [xs [Hsplit Hin]]].
    rewrite Hin in Hm. clear Hsplit Hin.
    apply sep_proj1 in Hm. clear ws xs.
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
      access_mode ty = By_value (chunk_of_type ty) ->
      NoDup cls.(c_objs) ->
      NoDupMembers cls.(c_mems) ->
      m |= staterep gcenv (cls::prog') cls.(c_name) me b ofs ** P ->
      In (x, ty) cls.(c_mems) ->
      field_offset gcenv x (make_members cls) = OK d ->
      v = Values.Val.load_result (chunk_of_type ty) v ->
      Clight.assign_loc gcenv ty m b (Int.repr (ofs + d)) v m' ->
      m' |= staterep gcenv (cls::prog') cls.(c_name) (madd_mem x v me) b ofs ** P.
  Proof.
    Opaque sepconj.
    intros ** Hty Hcls Hmem Hm Hin Hoff Hlr Hal.
    simpl in *. rewrite ident_eqb_refl in *.
    rewrite sep_assoc. rewrite sep_assoc in Hm.
    apply sepall_in in Hin.
    destruct Hin as [ws [xs [Hsplit Hin]]].
    rewrite Hsplit in Hmem.
    rewrite Hin in Hm. rewrite sep_assoc in Hm.
    rewrite Hin. rewrite sep_assoc.
    rewrite Hoff in *.
    rewrite sep_swap2.
    rewrite sepall_switchp
    with (f':=fun xty : ident * typ =>
                let (x0, ty0) := xty in
                match field_offset gcenv x0 (make_members cls) with
                | OK d0 =>
                  contains (chunk_of_type ty0) b (ofs + d0)
                           (match_value (mm_values me) x0)
                | Error _ => sepfalse
                end).
    - rewrite <-sep_swap2.
      eapply storev_rule' with (1:=Hm).
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
    forall m me cls prog b ofs x ty,
      m |= staterep gcenv (cls :: prog) cls.(c_name) me b ofs ->
      In (x, ty) (c_mems cls) ->
      exists d, field_offset gcenv x (make_members cls) = OK d
           /\ 0 <= ofs + d <= Int.max_unsigned.
  Proof.
    introv Hm Hin.
    simpl in Hm. rewrite ident_eqb_refl in Hm.
    apply sep_proj1 in Hm.
    apply sepall_in in Hin; destruct Hin as [ws [xs [Hsplit Hin]]].
    rewrite Hin in Hm. clear Hsplit Hin.
    apply sep_proj1 in Hm.
    clear ws xs.
    destruct (field_offset gcenv x (make_members cls)).
    + exists z; split*.
      apply* contains_no_overflow.
    + contradict Hm.
  Qed.

  Lemma staterep_inst_offset:
    forall m me cls prog b ofs o c,
      m |= staterep gcenv (cls :: prog) cls.(c_name) me b ofs ->
      In (o, c) (c_objs cls) ->
      exists d, field_offset gcenv o (make_members cls) = OK d.
  Proof.
    introv Hm Hin.
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

  Definition blockrep (ve: venv) (flds: members) (b: block) : massert :=
    sepall (fun xty : ident * type =>
              let (x, ty) := xty in
              match field_offset ge x flds, access_mode ty with
              | OK d, By_value chunk =>
                contains chunk b d (match_value ve x)
              | _, _ => sepfalse
              end) flds.

  Lemma blockrep_deref_mem:
    forall m me ve co b x ty d v,
      m |= blockrep ve (co_members co) b ->
      In (x, ty) (co_members co) ->
      find_var (me, ve) x v ->
      field_offset ge x (co_members co) = OK d ->
      Clight.deref_loc ty m b (Int.repr d) v.
  Proof.
    intros ** Hm Hin Hv Hoff.
    unfold blockrep in Hm.
    apply sepall_in in Hin.
    destruct Hin as [ws [xs [Hsplit Hin]]].
    rewrite Hin in Hm. clear Hsplit Hin.
    apply sep_proj1 in Hm. clear ws xs.
    rewrite Hoff in Hm. clear Hoff.
    destruct (access_mode ty) eqn:Haccess; try contradiction.
    apply loadv_rule in Hm.
    destruct Hm as [v' [Hloadv Hmatch]].
    unfold match_value in Hmatch.
    unfold find_var in Hv; simpl in Hv.
    rewrite Hv in Hmatch. clear Hv.
    rewrite Hmatch in Hloadv. clear Hmatch.
    apply Clight.deref_loc_value with (1:=Haccess) (2:=Hloadv).
  Qed.

  Lemma blockrep_assign_mem:
    forall P co m m' ve b d x v ty chunk,
      NoDupMembers (co_members co) ->
      m |= blockrep ve (co_members co) b ** P ->
      In (x, ty) (co_members co) ->
      field_offset ge x (co_members co) = OK d ->
      access_mode ty = By_value chunk ->
      v = Val.load_result chunk v ->
      Clight.assign_loc ge ty m b (Int.repr d) v m' ->
      m' |= blockrep (PM.add x v ve) (co_members co) b ** P.
  Proof.
    Opaque sepconj.
    intros ** Hndup Hm Hin Hoff Haccess Hlr Hal.
    apply sepall_in in Hin.
    destruct Hin as [ws [xs [Hsplit Hin]]].
    unfold blockrep in *.
    rewrite Hin in Hm. rewrite sep_assoc in Hm.
    rewrite Hin. rewrite sep_assoc.
    rewrite Hoff in *.
    rewrite sep_swap2.
    rewrite Haccess in *.
    rewrite Hsplit in Hndup.
    rewrite sepall_switchp
    with (f':=fun xty : ident * type =>
            let (x0, ty0) := xty in
            match field_offset ge x0 (co_members co), access_mode ty0 with
            | OK d0, By_value chunk =>
              contains chunk b d0 (match_value ve x0)
            | _, _ => sepfalse
            end).
    - rewrite <-sep_swap2.
      eapply storev_rule' with (1:=Hm).
      + unfold match_value. rewrite PM.gss. symmetry; exact Hlr.
      + inversion Hal as [? ? ? Haccess'|]; rewrite Haccess in *.
        * injection Haccess'. intro HR; rewrite <-HR in *; assumption.
        * discriminate.
    - apply NoDupMembers_remove_1 in Hndup.
      apply NoDupMembers_NoDup with (1:=Hndup).
    - intros x' Hin'; destruct x' as [x' ty'].
      rewrite match_value_add; [reflexivity|].
      apply NoDupMembers_app_cons in Hndup.
      destruct Hndup as [Hndup].
      apply In_InMembers in Hin'.
      intro Heq. apply Hndup. rewrite Heq in Hin'.
      assumption.
  Qed.

  Lemma blockrep_field_offset:
    forall m ve flds b x ty,
      m |= blockrep ve flds b ->
      In (x, ty) flds ->
      exists d, field_offset ge x flds = OK d.
  Proof.
    introv Hm Hin.
    unfold blockrep in Hm.
    apply sepall_in in Hin.
    destruct Hin as [ws [xs [Hsplit Hin]]].
    rewrite Hin in Hm. clear Hsplit Hin.
    apply sep_proj1 in Hm. clear ws xs.
    destruct (field_offset ge x flds).
    - exists* z.
    - contradict Hm.
  Qed.
  
End BlockRep.