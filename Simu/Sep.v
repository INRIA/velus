Require Import common.Separation.
Require Import common.Values.
Require Import common.Errors.
Require Import cfrontend.Ctypes.
Require Import lib.Maps.
Require Import lib.Coqlib.

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
    Memory.Mem.storev chunk m (Vptr b (Integers.Int.repr ofs)) v = Some m' ->
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

Definition chunk_of_type ty := AST.chunk_of_type (Ctypes.typ_of_type ty).

Definition match_value (e: PM.t val) (x: ident) (v': val) : Prop :=
  match PM.find x e with
  | None => True
  | Some v => v = v'
  end.

Definition match_var (S: state) :=
  match_value (snd S).

Definition match_field (S: state) :=
  match_value (fst S).(mm_values).

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

Definition instance_match (S: state) (i: ident): state :=
  (match mfind_inst i (fst S) with
  | None => m_empty
  | Some i => i
  end, snd S).


Lemma instance_match_empty:
  forall x ve, instance_match (m_empty, ve) x = (m_empty, ve).
Proof.
  intros. unfold instance_match, mfind_inst; simpl.
  rewrite PM.gempty. reflexivity.
Qed.

Section Staterep.
  Variable ge : composite_env.

  Fixpoint staterep' (p: list class) (clsnm: ident) (S: state)
                    (b: block) (ofs: Z): massert :=
    match p with
    | nil => sepfalse
    | cls :: p' =>
      if ident_eqb clsnm cls.(c_name)
      then
        sepall (fun (xty: ident * typ) =>
                  let (x, ty) := xty in
                  match field_offset ge x (make_members cls) with
                  | OK d =>
	                contains (chunk_of_type ty) b (ofs + d) (match_field S x)
                  | Error _ => sepfalse
                  end) cls.(c_mems)
        **
        sepall (fun (o: ident * ident) =>
                  let (i, c) := o in
                  match field_offset ge i (make_members cls) with
                  | OK d =>
                    staterep' p' c (instance_match S i) b (ofs + d)
                  | Error _ => sepfalse
                  end) cls.(c_objs)
      else staterep' p' clsnm S b ofs
    end.

  Definition staterep (p: program) := staterep' p.(p_classes). 

   Lemma staterep_skip_cons':
    forall cls prog clsnm me b ofs,
      clsnm <> cls.(c_name) ->
      staterep' (cls :: prog) clsnm me b ofs <-*-> staterep' prog clsnm me b ofs.
  Proof.
    intros ** Hnm.
    apply ident_eqb_neq in Hnm.
    simpl; rewrite Hnm; reflexivity.
  Qed.
  
  Lemma staterep_skip_cons:
    forall cls prog prog' clsnm me b ofs,
      clsnm <> cls.(c_name) ->
      prog'.(p_classes) = cls :: prog.(p_classes) ->
      staterep prog' clsnm me b ofs <-*-> staterep prog clsnm me b ofs.
  Proof.
    intros ** Hnm Eq.
    destruct prog'.
    simpl in Eq; subst.
    unfold staterep.
    now apply staterep_skip_cons'.    
  Qed.

  Lemma staterep_skip_app:
    forall clsnm prog oprog prog' me b ofs,
      ~ClassIn clsnm oprog ->
      prog'.(p_classes) = oprog ++ prog.(p_classes) ->
      staterep prog' clsnm me b ofs <-*-> staterep prog clsnm me b ofs.
  Proof.
    intros ** Hnin Eq.
    destruct prog'.
    simpl in Eq; subst.
    unfold staterep; simpl.
    induction oprog as [|cls oprog IH].
    - rewrite app_nil_l. reflexivity.
    - apply NotClassIn in Hnin. destruct Hnin.
      rewrite <-app_comm_cons.
      rewrite staterep_skip_cons'; auto.
      apply IH; auto.
      apply WelldefClasses_cons' with cls.
      now rewrite app_comm_cons.      
  Qed.

End Staterep.

Section BlockRep.
  Variable ge : composite_env.

  Definition blockrep (S: state) (flds: members) (b: block) : massert :=
    sepall (fun xty : ident * type =>
              let (x, ty) := xty in
              match field_offset ge x flds, access_mode ty with
              | OK d, By_value chunk =>
                contains chunk b d (match_var S x)
              | _, _ => sepfalse
              end) flds.
  
End BlockRep.

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

Definition valid_val (v: val) (t: typ): Prop :=
    Ctypes.access_mode t = Ctypes.By_value (chunk_of_type t)
    /\ v <> Values.Vundef
    /\ Values.Val.has_type v (Ctypes.typ_of_type t).

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
