Require Import common.Separation.
Require Import common.Values.
Require Import common.Errors.
Require Import cfrontend.Ctypes.
Require Import lib.Maps.
Require Import lib.Coqlib.

Require Import Rustre.Common.
Require Import Syn Sem.

Require Import List.
Require Import ZArith.BinInt.

Open Scope list.
Open Scope sep_scope.
Open Scope Z.

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
    massert_eqv P (P ** sepemp).
Proof.
  split; split; simpl; try (auto using sepemp_disjoint); intuition.
Qed.

Lemma sepemp_left:
  forall P,
    massert_eqv P (sepemp ** P).
Proof.
  intros. rewrite sep_comm. rewrite <-sepemp_right. reflexivity.
Qed.

Program Definition sepfalse: massert := {| m_pred := fun m => False;
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
      massert_eqv (sepall p (x::xs))
                  (p x ** sepall p xs).
  Proof.
    constructor; constructor; trivial.
  Qed.

  Lemma sepall_app:
    forall p xs ys,
      massert_eqv (sepall p (xs ++ ys))
                  (sepall p xs ** sepall p ys).
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
      massert_eqv (sepall p ys) (p x ** sepall p (ws ++ xs)).
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
               massert_eqv (sepall p ys)
                           (p x ** sepall p (ws ++ xs))).
  Proof.
    intros x ys Hin.
    apply in_split in Hin.
    destruct Hin as [ws [xs Hys]].
    exists ws, xs.
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
      massert_eqv (sepall f xs) (sepall f' xs).
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
      massert_imp (range b lo (lo + sizeof_struct env 0 (co_members co)))
                  (sepall (fun (fld: ident * type) =>
                             let (id, ty) := fld in
                             match field_offset env id (co_members co) with
                             | OK ofs  => range b (lo + ofs) (lo + ofs + sizeof env ty)
                             | Error _ => sepfalse
                             end) (co_members co)).
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
      massert_imp (range b lo (lo + co_sizeof co))
                  (sepall (fun (fld: ident * type) =>
                      let (id, ty) := fld in
                      match field_offset env id (co_members co) with
                      | OK ofs  => range b (lo + ofs) (lo + ofs + sizeof env ty)
                      | Error _ => sepfalse
                      end) (co_members co)).
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

Section Staterep.
  Variable ge : composite_env.

  Fixpoint staterep (p: program) (clsnm: ident) (me: menv)
                    (b: block) (ofs: Z) : massert :=
    match p with
    | nil => sepfalse
    | cls::p' =>
      if ident_eqb clsnm cls.(c_name)
      then
        sepall (fun (xty: ident * typ) =>
                  let (x, ty) := xty in
                  match field_offset ge x (make_members cls) with
                  | OK d =>
	            Separation.contains (chunk_of_type ty) b (ofs + d)
                                        (match_value x me.(mm_values))
                  | Error _ => sepfalse
                  end) cls.(c_mems)
        **
        sepall (fun (o: obj_dec) =>
                  let i := obj_inst o in
                  match field_offset ge i (make_members cls) with
                  | OK d =>
                    staterep p' o.(obj_class) (instance_match i me) b (ofs + d)
                  | Error _ => sepfalse
                  end) cls.(c_objs)
      else staterep p' clsnm me b ofs
    end.

  Lemma staterep_skip_cons:
    forall cls prog clsnm me b ofs,
      clsnm <> cls.(c_name) ->
      massert_eqv (staterep (cls::prog) clsnm me b ofs)
                  (staterep prog clsnm me b ofs).
  Proof.
    intros ** Hnm.
    apply ident_eqb_neq in Hnm.
    simpl; rewrite Hnm.
    reflexivity.
  Qed.

  Lemma staterep_skip_app:
    forall clsnm prog oprog me b ofs,
      ~ClassIn clsnm oprog ->
      massert_eqv (staterep (oprog ++ prog) clsnm me b ofs)
                  (staterep prog clsnm me b ofs).
  Proof.
    intros ** Hnin.
    induction oprog as [|cls oprog IH].
    - rewrite app_nil_l. reflexivity.
    - apply NotClassIn in Hnin. destruct Hnin.
      rewrite <-app_comm_cons.
      rewrite staterep_skip_cons; auto.
  Qed.

End Staterep.