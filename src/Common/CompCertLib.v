From Velus Require Import Common.

From compcert Require Import lib.Coqlib.
From compcert Require Import lib.Maps.
From compcert Require Import cfrontend.Clight.
From compcert Require Import cfrontend.Ctypes.
From compcert Require Import lib.Integers.
From compcert Require Import common.Values.
From compcert Require Import common.Errors.
From compcert Require Import common.Memory.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Classes.RelationClasses.

Open Scope error_monad_scope.

(* Extensions to CompCert libraries. *)

(** Conversions. *)

Lemma NoDup_norepet:
  forall {A} (l: list A),
    NoDup l <-> list_norepet l.
Proof.
  induction l; split; constructor.
  - now inversion H.
  - apply IHl; now inversion H.
  - now inversion H.
  - apply IHl; now inversion H.
Qed.

Lemma NoDupMembers_disjoint:
  forall l1 l2,
    NoDupMembers (l1 ++ l2) ->
    list_disjoint (var_names l1) (var_names l2).
Proof.
  unfold list_disjoint, var_names.
  intros l1 l2 H x y Hx Hy.
  apply in_map_iff in Hx; destruct Hx as ((x', tx) & Ex & Hx);
    apply in_map_iff in Hy; destruct Hy as ((y', ty) & Ey & Hy);
      simpl in *; subst.
  intro E; subst.
  apply in_split in Hx; destruct Hx as (lx & lx' & Hx);
    apply in_split in Hy; destruct Hy as (ly & ly' & Hy);
      subst.
  rewrite <-app_assoc in H.
  apply NoDupMembers_app_r in H.
  rewrite <-app_comm_cons, NoDupMembers_cons_inv in H.
  destruct H as [Notin]; apply Notin.
  apply InMembers_app; right; apply InMembers_app; right; apply InMembers_eq.
Qed.

Lemma list_drop_skipn:
  forall {A} (xs: list A) n,
    Coqlib.list_drop n xs = skipn n xs.
Proof.
  induction xs, n; simpl; auto.
Qed.

Lemma list_forall2_Forall2:
  forall {A B} P (xs: list A) (ys: list B),
    Coqlib.list_forall2 P xs ys <-> Forall2 P xs ys.
Proof.
  induction xs as [|x xs IH].
  now split; inversion 1; auto using Coqlib.list_forall2_nil.
  split; intro HH; inversion_clear HH; constructor; auto; apply IH; auto.
Qed.

(** The error monad. *)

Section Mmaps.

  Context {A B S: Type}.

  Definition mmaps (f: S -> A -> res (S * B)) : S -> list A -> res (S * list B) :=
    fix mmaps (s: S) (xs: list A) {struct xs} : res (S * list B) :=
      match xs with
      | nil => OK (s, nil)
      | x :: xs' => do (s', y) <- f s x;
                    do (s'', ys) <- mmaps s' xs';
                    OK (s'', y :: ys)
      end.

  Lemma mmaps_spec:
    forall (P: S -> S -> B -> Prop) (R: S -> S -> Prop)
           (I: list B -> Prop) (IS: S -> Prop)
           (f: S -> A -> res (S * B)) xs ys s s',
      mmaps f s xs = OK (s', ys) ->
      Reflexive R ->
      Transitive R ->
      I [] ->
      IS s ->
      (forall s s' y, P s s' y ->
                         (forall r,  R r  s  -> P r s' y)
                      /\ (forall t', R s' t' -> P s t' y)) ->
      (forall x y s s',
          In x xs ->
          IS s ->
          f s x = OK (s', y) ->
          P s s' y /\ R s s' /\ IS s') ->
      (forall y ys s s' s'',
          P s s' y ->
          Forall (P s' s'') ys ->
          R s s' ->
          R s' s'' ->
          I ys ->
          I (y :: ys)) ->
      Forall (P s s') ys /\ R s s' /\ I ys /\ IS s'.
  Proof.
    intros P R I IS f xs ys s s' Hmm HRefl HTrans HInil HIS0 HPR Hf HPI.
    revert xs ys s s' Hf Hmm HIS0.
    induction xs as [|x xs IH]; simpl.
    now inversion_clear 2; auto.
    intros ys s s' Hf Hmm HIS.
    monadInv Hmm.
    match goal with H:f _ _ = OK (_, ?w) |- _ =>
      rename w into y; apply Hf in H; try destruct H as (HP & HR' & HIS'); auto end.
    match goal with H:mmaps _ ?s _ = OK (_, ?ws) |- _ =>
      rename s into t, ws into ys; apply IH in H;
        try destruct H as (Hfa & HR & HI & HIS'') end; auto.
    2: now intros; eapply Hf; eauto.
    pose proof (HTrans _ _ _ HR' HR).
    repeat split; eauto.
    constructor.
    now apply HPR in HP; destruct HP; auto.
    apply Forall_forall.
    intros y' Hin.
    apply Forall_forall with (1:=Hfa) in Hin.
    apply HPR in Hin.
    destruct Hin as (HP1 & HP2).
    now apply HP1.
  Qed.

  Lemma mmaps_weak_spec:
    forall (I: S -> Prop) (R: B -> Prop)
           (f: S -> A -> res (S * B)) xs s ys s',
      mmaps f s xs = OK (s', ys) ->
      I s ->
      (forall x s y s',
          I s ->
          In x xs ->
          f s x = OK (s', y) ->
          I s' /\ R y) ->
      I s' /\ Forall R ys.
  Proof.
    induction xs as [|x xs IH]; simpl; intros * Hmm HI Hone; monadInv Hmm.
    now auto.
    match goal with Hf:f _ _ = OK _ |- _ =>
      apply Hone with (1:=HI) in Hf; auto; destruct Hf end.
    rewrite Forall_cons2, (and_comm (R x1)), <-and_assoc; eauto.
  Qed.

  Lemma mmaps_weak_spec':
  forall (R: B -> Prop)
         (f: S -> A -> res (S * B)) xs s ys s',
    mmaps f s xs = OK (s', ys) ->
    (forall x s y s',
        In x xs ->
        f s x = OK (s', y) ->
        R y) ->
    Forall R ys.
  Proof.
    intros * Hmm Hy.
    eapply mmaps_weak_spec with (I:=fun s=>True);
      eauto using Forall_forall.
  Qed.

End Mmaps.

Definition mfoldl {A B: Type} (f: A -> B -> res A) : A -> list B -> res A :=
  fix mfoldl s xs {struct xs} :=
    match xs with
    | nil => OK s
    | x :: xs' => do s' <- f s x;
                    mfoldl s' xs'
    end.

Section IterError.

  Context {A: Type}.
  Variable f: A -> res unit.

  Definition iter_error: list A -> res unit :=
    mfoldl (fun _ a => f a) tt.

  Lemma iter_error_ok:
    forall l,
      iter_error l = OK tt <->
      Forall (fun a => f a = OK tt) l.
  Proof.
    unfold iter_error.
    induction l; simpl.
    - intuition.
    - split; intros H.
      + monadInv H.
        take (unit) and destruct it.
        constructor; auto.
        apply IHl; auto.
      + inversion_clear H as [|?? E].
        rewrite E; simpl.
        apply IHl; auto.
  Qed.

End IterError.

Lemma OK_OK:
  forall {A} (x: A) y,
    OK x = OK y <-> x = y.
Proof.
  intros; split; intro HH; subst; auto. now monadInv HH.
Qed.

Definition mmapacc {A S T: Type} (acc: S -> T -> S) (f: A -> res T)
  : S -> list A -> res S :=
  fix mmapacc (s: S) (xs: list A) {struct xs} : res S :=
    match xs with
    | nil => OK s
    | x :: xs' => do r <- f x;
                    mmapacc (acc s r) xs'
    end.

Lemma mmap_skipn:
  forall {A B} (f: A -> res B) xs ys n,
    mmap f xs = OK ys ->
    mmap f (skipn n xs) = OK (skipn n ys).
Proof.
  induction xs as [|x xs IH].
  now inversion_clear 1; setoid_rewrite skipn_nil; auto.
  intros ys n Hmm.
  simpl in *. monadInv Hmm.
  destruct n; simpl.
  2:now apply IH.
  rewrite EQ; rewrite EQ1. auto.
Qed.

Open Scope nat.

Lemma mmapacc_plus_shift:
  forall {A} f (xs: list A) m1 m2 n,
    mmapacc plus f (m1 + m2) xs = OK n ->
    mmapacc plus f m1 xs = OK (n - m2) /\ m2 <= n.
Proof.
  induction xs as [|x xs IH]; intros m1 m2 n Hm; simpl in *; monadInv Hm.
  now subst; rewrite OK_OK; lia.
  rewrite EQ. simpl.
  rewrite Nat.add_comm, Nat.add_assoc, (Nat.add_comm x0 m1) in EQ0.
  apply IH in EQ0. auto.
Qed.

(** More monad syntax and tactics *)

Definition bind22 {A B C D: Type} (f: res (A * (B * C))) (g: A -> B -> C -> res D) : res D :=
  match f with
  | OK (x, (y, z)) => g x y z
  | Error msg => Error msg
  end.

Module DoNotation.

  Notation "'do' ( X , ( Y , Z ) ) <- A ; B" :=
    (bind22 A (fun X Y Z => B))
      (at level 200, X name, Y name, Z name, A at level 100, B at level 200)
    : error_monad_scope.

End DoNotation.

Remark bind22_inversion:
  forall {A B C D: Type} (f: res (A*(B*C))) (g: A -> B -> C -> res D) {z: D},
    bind22 f g = OK z ->
    exists w, exists x, exists y, f = OK (w, (x, y)) /\ g w x y = OK z.
Proof.
  intros until z. destruct f; simpl.
  repeat destruct p; simpl; intros. exists a; exists b; exists c; auto.
  intros; discriminate.
Qed.

(* Duplicate the tactic from CompCert/common/Errors and add a case
     for bind22. *)
Ltac monadInv2 H :=
  match type of H with
  | (OK _ = OK _) =>
    inversion H; clear H; try subst
  | (Error _ = OK _) =>
    discriminate
  | (bind ?F ?G = OK ?X) =>
    let x := fresh "x" in (
      let EQ1 := fresh "EQ" in (
        let EQ2 := fresh "EQ" in (
          destruct (bind_inversion F G H) as [x [EQ1 EQ2]];
          clear H;
          try (monadInv2 EQ2))))
  | (bind2 ?F ?G = OK ?X) =>
    let x1 := fresh "x" in (
      let x2 := fresh "x" in (
        let EQ1 := fresh "EQ" in (
          let EQ2 := fresh "EQ" in (
            destruct (bind2_inversion F G H) as [x1 [x2 [EQ1 EQ2]]];
            clear H;
            try (monadInv2 EQ2)))))
  | (bind22 ?F ?G = OK ?X) =>
    let x1 := fresh "x" in (
      let x2 := fresh "x" in (
        let x3 := fresh "x" in (
          let EQ1 := fresh "EQ" in (
            let EQ2 := fresh "EQ" in (
              destruct (bind22_inversion F G H) as [x1 [x2 [x3 [EQ1 EQ2]]]];
              clear H;
              try (monadInv2 EQ2))))))
  | (match ?X with left _ => _ | right _ => assertion_failed end = OK _) =>
    destruct X; [try (monadInv2 H) | discriminate]
  | (match (negb ?X) with true => _ | false => assertion_failed end = OK _) =>
    destruct X as [] eqn:?; [discriminate | try (monadInv2 H)]
  | (match ?X with true => _ | false => assertion_failed end = OK _) =>
    destruct X as [] eqn:?; [try (monadInv2 H) | discriminate]
  | (mmap ?F ?L = OK ?M) =>
    generalize (mmap_inversion F L H); intro
  end.

Close Scope nat.
Close Scope error_monad_scope.

Lemma Int_Ptrofs_max_unsigned:
  Int.max_unsigned <= Ptrofs.max_unsigned.
Proof.
  unfold Int.max_unsigned, Ptrofs.max_unsigned.
  unfold Int.modulus, Ptrofs.modulus.
  unfold Int.wordsize, Ptrofs.wordsize.
  unfold Wordsize_32.wordsize, Wordsize_Ptrofs.wordsize.
  destruct Archi.ptr64; [|reflexivity].
  simpl. lia.
Qed.

Lemma type_eq_refl:
  forall {A} t (T F: A),
    (if type_eq t t then T else F) = T.
Proof.
  intros.
  destruct (type_eq t t) as [|Neq]; congruence.
Qed.

Definition mk_members (flds : list (AST.ident * type)) : members :=
  List.map (fun '(x, ty) => Member_plain x ty) flds.

Lemma mk_members_names : forall flds,
    map name_member (mk_members flds) = map fst flds.
Proof.
  intros.
  unfold mk_members.
  rewrite map_map. eapply map_ext; eauto.
  intros (?&?); auto.
Qed.

Remark field_offset_rec_mk_members : forall env id flds k ofs bf,
    field_offset_rec env id (mk_members flds) k = OK (ofs, bf) ->
    bf = Full.
Proof.
  induction flds as [|(?&?)]; simpl; intros * Hf.
  - discriminate.
  - destruct (AST.ident_eq _ _); simpl; subst.
    + inv Hf; auto.
    + eapply IHflds; eauto.
Qed.

Corollary field_offset_mk_members : forall env id flds ofs bf,
    field_offset env id (mk_members flds) = OK (ofs, bf) ->
    bf = Full.
Proof.
  intros * Hf.
  apply field_offset_rec_mk_members in Hf; auto.
Qed.

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
  rewrite <- (Z2Nat.id p) in HH1; eauto.
  apply Zdivide_intro with (q:=two_power_nat (Z.to_nat p)).
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
  forall env co flds,
    co_members co = mk_members flds ->
    composite_consistent env co ->
    attr_alignas (co_attr co) = None ->
    Forall (fun x => (alignof env (type_member x) | co_alignof co)) (co_members co).
Proof.
  intros * Hmk Henv Hattr.
  rewrite co_consistent_alignof with (1:=Henv). clear Henv.
  unfold align_attr.
  rewrite Hmk, Hattr. clear Hmk.
  induction flds as [|(?&?) flds IH]; simpl; auto.
  (* induction (co_members co) as [|a ms IH]; [now trivial|]. *)
  destruct (alignof_composite_two_p env (mk_members flds)) as [n Hms].
  simpl. rewrite Hms in *; clear Hms.
  (* destruct m as [x ty]. *)
  destruct (alignof_two_p env t) as [m Hty].
  rewrite Hty.
  constructor.
  - simpl. rewrite Hty.
    now apply two_power_nat_max.
  - apply Forall_impl with (2:=IH).
    intros a HH. apply Z.divide_trans with (1:=HH).
    rewrite Z.max_comm.
    apply two_power_nat_max.
Qed.

Lemma align_noattr:
  forall a, align_attr noattr a = a.
Proof.
  intros. unfold noattr. reflexivity.
Qed.

Lemma in_field_type:
  forall xs x ty,
    NoDupMembers xs ->
    In (x,ty) xs ->
    field_type x (mk_members xs) = Errors.OK ty.
Proof.
  intros xs x ty Hndup Hin.
  induction xs as [|x' xs IH]; [now inversion Hin|].
  destruct x' as [x' ty'].
  apply NoDupMembers_cons_inv in Hndup as [? Hndup].
  inversion Hin as [Heq|Heq].
  - injection Heq; intros; subst.
    simpl. rewrite peq_true. reflexivity.
  - simpl. rewrite peq_false.
    + now apply IH with (1:=Hndup) (2:=Heq).
    + intro; subst.
      apply NotInMembers_NotIn in Heq; intuition.
Qed.

Lemma field_offset_type:
  forall ge id ms d,
    field_offset ge id ms = Errors.OK d ->
    exists ty, field_type id ms = Errors.OK ty.
Proof.
  unfold field_offset.
  intros until d.
  cut (forall ofs, field_offset_rec ge id ms ofs = Errors.OK d ->
              exists ty, field_type id ms = Errors.OK ty); eauto.
  induction ms as [|? flds IH]; intros ofs Hfo; [now inv Hfo|].
  simpl in *.
  destruct (AST.ident_eq id (name_member a)) as [He|Hne]; eauto.
Qed.

Remark field_offset_aligned':
  forall gcenv id flds ofs ty bf,
    field_offset gcenv id (mk_members flds) = OK (ofs, bf) ->
    field_type id (mk_members flds) = OK ty ->
    (alignof gcenv ty | ofs).
Proof.
  intros.
  assert (bf = Full) by (eapply field_offset_mk_members; eauto); subst.
  eapply field_offset_aligned; eauto.
Qed.

Remark field_offset_in_range':
  forall gcenv flds x ofs bf,
    field_offset gcenv x (mk_members flds) = Errors.OK (ofs,bf) ->
    0 <= ofs.
Proof.
  intros * Hfield.
  assert (bf = Full) by (eapply field_offset_mk_members; eauto); subst.
  destruct (field_offset_type _ _ _ _ Hfield) as (?&Hty).
  eapply field_offset_in_range in Hfield as (?&_); eauto.
Qed.

Lemma field_type_skip_app:
  forall x ws xs,
    ~InMembers x ws ->
    field_type x (mk_members (ws ++ xs)) = field_type x (mk_members xs).
Proof.
  induction ws as [|w ws IH]; auto.
  intros xs Hnin.
  apply NotInMembers_cons in Hnin.
  destruct Hnin as (Hnin & Hx).
  destruct w. simpl.
  rewrite peq_false; auto.
Qed.

Lemma sizeof_by_value:
  forall ge ty chunk,
    access_mode ty = By_value chunk ->
    sizeof ge ty = Memdata.size_chunk chunk.
Proof.
  destruct ty; try (intros; discriminate);
    [destruct i, s, a|destruct s, a|destruct f, a|];
    injection 1; intros; subst; reflexivity.
Qed.
Global Hint Resolve sizeof_by_value : compcert.

Lemma sizeof_struct_pos:
  forall env ms,
    0 <= sizeof_struct env ms.
Proof.
  unfold sizeof_struct; intros.
  unfold bytes_of_bits.
  assert (0 <= bitsizeof_struct env 0 ms).
  2:{ apply Z.div_pos; lia. }
  apply bitsizeof_struct_incr.
Qed.

Lemma set_comm:
  forall {A} x x' (v v': A) m,
    x <> x' ->
    PTree.set x v (PTree.set x' v' m) = PTree.set x' v' (PTree.set x v m).
Proof.
  intros * Neq.
  apply PTree.extensionality.
  intro p.
  destruct (Pos.eq_dec p x); subst.
  now rewrite PTree.gss, PTree.gso, PTree.gss.
  destruct (Pos.eq_dec p x'); subst.
  now rewrite PTree.gss, PTree.gso, PTree.gss.
  now rewrite 4 PTree.gso.
Qed.

(* Remark bind_parameter_temps_cons: *)
(*   forall x t xs v vs le le', *)
(*     bind_parameter_temps ((x, t) :: xs) (v :: vs) le = Some le' -> *)
(*     list_norepet (var_names ((x, t) :: xs)) -> *)
(*     PTree.get x le' = Some v. *)
(* Proof. *)
(*   induction xs as [|[x' t']]; destruct vs; *)
(*     intros * Bind Norep; inversion Bind as [Bind']. *)
(*   - apply PTree.gss. *)
(*   - inversion_clear Norep as [|? ? Notin Norep']. *)
(*     apply not_in_cons in Notin; destruct Notin as [? Notin]. *)
(*     eapply IHxs; eauto. *)
(*     + simpl. *)
(*       erewrite set_comm in Bind'; eauto. *)
(*     + constructor. *)
(*       * apply Notin. *)
(*       * inversion_clear Norep' as [|? ? ? Norep'']. *)
(*         apply Norep''. *)
(* Qed. *)

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

Remark bind_parameter_temps_cons:
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

Remark bind_parameter_temps_implies_two:
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
      subst o. apply InMembers_eq.
    + intro Eq.
      apply Notin_s.
      subst s. apply InMembers_eq.
Qed.

Remark bind_parameter_temps_implies:
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
      subst s. apply InMembers_eq.
Qed.


Remark alloc_implies:
  forall tge vars x b t e m e' m',
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
    + intro; subst x; apply Notin; apply InMembers_eq.
Qed.

Definition drop_block '((x, (_, t)): ident * (block * Ctypes.type)) : (ident * Ctypes.type) :=
  (x, t).

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
  forall tge vars e m e' m',
    alloc_variables tge e m vars e' m' ->
    NoDupMembers vars ->
    (forall x t,
        In (x, t) (map drop_block (PTree.elements e')) <->
        (In (x, t) (map drop_block (PTree.elements e)) /\ (forall t', In (x, t') vars -> t = t'))
        \/ In (x, t) vars).
Proof.
  intros tge vars.
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

Remark alloc_permutation:
  forall tge vars m e' m',
    alloc_variables tge empty_env m vars e' m' ->
    NoDupMembers vars ->
    Permutation.Permutation vars (map drop_block (PTree.elements e')).
Proof.
  intros * Alloc Nodup.
  pose proof (alloc_In _ _ _ _ _ _ Alloc) as H.
  apply Permutation.NoDup_Permutation.
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
    Permutation.Permutation (PTree.elements (PTree.set x (a, b) e))
                            ((x, (a, b)) :: PTree.elements e).
Proof.
  intros * Hin.
  apply Permutation.NoDup_Permutation.
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

Lemma set_NoDupMembers:
  forall x (e: Clight.env) b1 t,
    NoDupMembers (map snd (PTree.elements e)) ->
    ~InMembers x (PTree.elements e) ->
    ~InMembers b1 (map snd (PTree.elements e)) ->
    NoDupMembers (map snd (PTree.elements (PTree.set x (b1, t) e))).
Proof.
  intros * Nodup Notin Diff.
  assert (Permutation.Permutation (map snd (PTree.elements (PTree.set x (b1, t) e)))
                                  ((b1, t) :: (map snd (PTree.elements e)))) as Perm.
  { change (b1, t) with (snd (x, (b1, t))).
    rewrite <-map_cons.
    now apply Permutation.Permutation_map, Permutation_set.
  }
  rewrite Perm.
  simpl; constructor; auto.
Qed.

Remark alloc_NoDupMembers:
  forall tge vars e m e' m',
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
  - apply set_NoDupMembers; auto.
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
  forall tge vars e m,
    NoDupMembers vars ->
    exists e' m',
      alloc_variables tge e m vars e' m'.
Proof.
  induction vars as [|(x, t)]; intros * Nodup.
  - exists e, m; constructor.
  - inv Nodup.
    destruct (Mem.alloc m 0 (Ctypes.sizeof tge t)) as (m1 & b) eqn: Eq.
    edestruct IHvars with (e:=PTree.set x (b, t) e) (m:=m1)
      as (e' & m' & Halloc); eauto.
    exists e', m'; econstructor; eauto.
Qed.

Remark Permutation_fst:
  forall vars elems,
    Permutation.Permutation vars elems ->
    Permutation.Permutation (var_names vars) (map fst elems).
Proof.
  intros * Perm.
  induction Perm; simpl; try constructor; auto.
  transitivity (map fst l'); auto.
Qed.

Remark map_fst_drop_block:
  forall elems,
    map fst (map drop_block elems) = map fst elems.
Proof.
  induction elems as [|(x, (b, t))]; simpl; auto with datatypes.
Qed.

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
