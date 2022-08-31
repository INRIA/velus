From Coq Require Import BinPos.
From Velus Require Import Lustre.Denot.Cpo.
Require Import Cpo_ext.

(** * Streams operations for the Lustre synchronous semantics *)

Inductive error :=
| error_Ty  (* method not undersood error, memory corruption (no typing yet)    TODO: change name*)
| error_Cl  (* runtime scheduling error *)
| error_Op  (* opérateur (débordement, div par 0, undef, etc.) *)
.

Inductive sampl (A : Type) : Type :=
| abs
| pres (a: A)
| err  (e : error).

Arguments abs  {A}.
Arguments pres {A} a.
Arguments err  {A} e.

(* réécritures nécessaires dans ce fichier, cpodb est trop lourde... *)
Local Hint Rewrite
     ford_fcont_shift_simpl
     curry_Curry
     Curry_simpl
     fcont_comp_simpl
     fcont_comp2_simpl
     fcont_comp4_simpl
     SND_simpl Snd_simpl
     FST_simpl Fst_simpl
     DSCASE_simpl
     DScase_cons
     @zip_eq
  : localdb.

(** *** unop and binop are in a separate section to ease their usage by other
    primitives *)
Section Sunop_binop.

  Context {A B D : Type}.

  Definition sunop (uop : A -> option B) : DS (sampl A) -C-> DS (sampl B) :=
    MAP (fun x => match x with
               | pres v =>
                   match uop v with
                   | Some y => pres y
                   | None => err error_Op
                   end
               | abs => abs
               | err e => err e
               end).

  Lemma sunop_eq : forall uop u U,
      sunop uop (cons u U)
      == cons match u with
           | pres u => match uop u with
                      | Some v => pres v
                      | None => err error_Op
                      end
           | abs => abs
           | err e => err e
           end (sunop uop U).
  Proof.
    intros.
    unfold sunop.
    rewrite MAP_map, map_eq_cons.
    destruct u; auto.
  Qed.

  Definition sbinop (bop : A -> B -> option D) :
    DS (sampl A) -C-> DS (sampl B) -C-> DS (sampl D) :=
    curry
      (MAP (fun '(va,vb) =>
           match va, vb with
           | err e, _ => err e
           | _, err e => err e
           | abs, abs => abs
           | pres a, pres b =>
               match bop a b with
               | Some v => pres v
               | None => err error_Op
               end
           | _, _ => err error_Cl
           end) @_ (ZIP pair @2_ FST _ _) (SND _ _ )).

  Lemma sbinop_eq : forall bop u U v V,
      sbinop bop (cons u U) (cons v V)
      == cons match u, v with
           | err e, _ => err e
           | _, err e => err e
           | abs, abs => abs
           | pres a, pres b =>
               match bop a b with
               | Some v => pres v
               | None => err error_Op
               end
           | _, _ => err error_Cl
        end (sbinop bop U V).
  Proof.
    intros.
    unfold sbinop.
    autorewrite with localdb using (simpl (snd _); simpl (fst _)).
    rewrite MAP_map, map_eq_cons.
    destruct u; auto.
  Qed.

End Sunop_binop.


Section SStream_functions.

  Context {A B : Type}.

  (** Rythm of constants if given by the base clock as an argument *)
  Definition sconst (v : A) : DS bool -C-> DS (sampl A) :=
    MAP (fun c : bool => if c then pres v else abs).

  (** fby1 is defined by means of two mutually recursive functions, see
      [fby1APf_eq] and [fby1f_eq] above for explanation *)
  Definition fby1sf :
    (bool -O-> option A -O-> DS (sampl A) -C-> DS (sampl A) -C-> DS (sampl A)) -C->
    (bool -O-> option A -O-> DS (sampl A) -C-> DS (sampl A) -C-> DS (sampl A)).
    apply ford_fcont_shift.
    intros [].
    - (* true : fby1A/P *)
      apply ford_fcont_shift. intro ov.
      apply curry, curry.
      eapply (fcont_comp2 (DSCASE _ _)).
      2: exact (SND _ _).
      apply ford_fcont_shift.
      intro y.
      apply curry.
      match goal with
      | |- _ (_ (Dprod ?pl ?pr) _) =>
          pose (fby1 := fcont_ford_shift _ _ _ ((FST _ _ @_ FST _ _ @_ (FST pl pr))) false);
          (* pose (fby1 := fcont_ford_shift _ _ _ fby1v v); *)
          pose (xs := (SND _ _ @_ FST _ _ @_ FST pl pr));
          pose (ys' := SND pl pr)
      end.
      refine match ov, y with
        | Some v, abs
        | None, pres v => (fcont_ford_shift _ _ _ fby1 (Some v) @3_ ID _) xs ys'
        | _, err _ => CTE _ _ (DS_const y)
        | _, _ => CTE _ _ (DS_const (err error_Cl))
      end.
    - (* false : fby1 *)
      apply ford_fcont_shift. intro ov.
      apply curry, curry.
      eapply (fcont_comp2 (DSCASE _ _)).
      2: exact (SND _ _ @_ FST _ _).
      apply ford_fcont_shift.
      intro x.
      apply curry.
      match goal with
      | |- _ (_ (Dprod ?pl ?pr) _) =>
          pose (fby1AP := fcont_ford_shift _ _ _ ((FST _ _ @_ FST _ _ @_ (FST pl pr))) true);
          pose (ys := (SND _ _ @_ FST pl pr));
          pose (xs' := SND pl pr)
      end.
      refine match ov, x with
        | Some v, pres _ => CONS (pres v) @_ ((fcont_ford_shift _ _ _ fby1AP None @3_ ID _) xs' ys)
        | Some v, abs => CONS abs @_ ((fcont_ford_shift _ _ _ fby1AP (Some v) @3_ ID _) xs' ys)
        | _, err _ => CTE _ _ (DS_const x)
        | _, _ => CTE _ _ (DS_const (err error_Cl))
      end.
  Defined.

  Lemma fby1APf_eq : forall F ov xs y ys,
      fby1sf F true ov xs (cons y ys)
      == match ov, y with
         | Some v, abs
         | None, pres v => F false (Some v) xs ys
         | _, err _ => DS_const y
         | _, _ => DS_const (err error_Cl)
         end.
  Proof.
    intros.
    unfold fby1sf.
    autorewrite with localdb using (simpl (snd _); simpl (fst _)).
    destruct ov,y; auto.
  Qed.

  Lemma fby1f_eq : forall F ov x xs ys,
      fby1sf F false ov (cons x xs) ys
      == match ov, x with
         | Some v, pres _ => cons (pres v) (F true None xs ys)
         | Some v, abs => cons abs (F true (Some v) xs ys)
         | _, err _ => DS_const x
         | _, _ => DS_const (err error_Cl)
         end.
  Proof.
    intros.
    unfold fby1sf.
    autorewrite with localdb using (simpl (snd _); simpl (fst _)).
    destruct ov,x; auto.
  Qed.

  Definition fby1s : (bool -O-> option A -O-> DS (sampl A) -C-> DS (sampl A) -C-> DS (sampl A)) :=
    FIXP _ fby1sf.

  Definition fby1AP : option A -O-> DS (sampl A) -C-> DS (sampl A) -C-> DS (sampl A) := fby1s true.
  Definition fby1 : option A -O-> DS (sampl A) -C-> DS (sampl A) -C-> DS (sampl A) := fby1s false.

  Lemma fby1AP_eq : forall ov xs y ys,
      fby1AP ov xs (cons y ys)
      == match ov,y with
         | Some v, abs
         | None, pres v => fby1 (Some v) xs ys
         | _, err _ => DS_const y
         | _, _ => DS_const (err error_Cl)
         end.
  Proof.
    intros.
    unfold fby1AP, fby1s.
    assert (Heq:=FIXP_eq fby1sf).
    rewrite (ford_eq_elim (ford_eq_elim Heq true)).
    now rewrite fby1APf_eq.
  Qed.

  Lemma fby1_eq : forall ov x xs ys,
      fby1 ov (cons x xs) ys
      == match ov, x with
         | Some v, abs => cons abs (fby1AP (Some v) xs ys)
         | Some v, pres _ => cons (pres v) (fby1AP None xs ys)
         | _, err _ => DS_const x
         | _, _ => DS_const (err error_Cl)
         end.
  Proof.
    intros.
    unfold fby1, fby1s.
    assert (Heq:=FIXP_eq fby1sf).
    rewrite (ford_eq_elim (ford_eq_elim Heq false)).
    now rewrite fby1f_eq.
  Qed.

  Lemma fby1AP_cons :
    forall ov xs ys,
      is_cons (fby1AP ov xs ys) ->
      is_cons ys.
  Proof.
    unfold fby1AP, fby1s.
    intros * Hc.
    rewrite ford_eq_elim with (n := ov) in Hc. (* WTF *)
    2: apply ford_eq_elim; rewrite FIXP_eq; reflexivity.
    now apply DScase_is_cons in Hc.
  Qed.

  Lemma fby1_cons :
    forall ov xs ys,
      is_cons (fby1 ov xs ys) ->
      is_cons xs.
  Proof.
    unfold fby1, fby1s.
    intros * Hc.
    rewrite ford_eq_elim with (n := ov) in Hc. (* WTF *)
    2: apply ford_eq_elim; rewrite FIXP_eq; reflexivity.
    now apply DScase_is_cons in Hc.
  Qed.

  (* pour définir fbyA/fby mutuellement récursives on utilise un
     commutateur booléen *)
  Definition fbysf :
    (bool -O-> DS (sampl A) -C-> DS (sampl A) -C-> DS (sampl A)) -C->
    (bool -O-> DS (sampl A) -C-> DS (sampl A) -C-> DS (sampl A)).
    apply ford_fcont_shift.
    intros [].
    - (* true : fbyA *)
      apply curry, curry.
      eapply (fcont_comp2 (DSCASE _ _)).
      2: exact (SND _ _).
      apply ford_fcont_shift.
      intro x.
      apply curry.
      match goal with
      | |- _ (_ (Dprod ?pl ?pr) _) =>
          pose (fby := fcont_ford_shift _ _ _ ((FST _ _ @_ FST _ _ @_ (FST pl pr))) false);
          pose (xs := (SND _ _ @_ FST _ _ @_ FST pl pr));
          pose (ys' := SND pl pr)
      end.
      refine match x with
        | abs => (fby @3_ ID _) xs ys'
        | err _ => CTE _ _ (DS_const x)
        | pres _ => CTE _ _ (DS_const (err error_Cl))
      end.
    - (* false : fby *)
      apply curry, curry.
      eapply (fcont_comp2 (DSCASE _ _)).
      2: exact (SND _ _ @_ FST _ _).
      apply ford_fcont_shift.
      intro x.
      apply curry.
      match goal with
      | |- _ (_ (Dprod ?pl ?pr) _) =>
          pose (fbyA := fcont_ford_shift _ _ _ ((FST _ _ @_ FST _ _ @_ (FST pl pr))) true);
          pose (ys := (SND _ _ @_ FST pl pr));
          pose (xs' := SND pl pr)
      end.
      refine match x with
        | abs => CONS abs @_ ((fbyA @3_ ID _) xs' ys)
        | pres v => CONS (pres v) @_ ((fby1AP None @2_ xs') ys)
        | err _ => CTE _ _ (DS_const x)
      end.
  Defined.

  Lemma fbyAf_eq : forall F xs y ys,
      fbysf F true xs (cons y ys)
      == match y with
         | abs => F false xs ys
         | err _ => DS_const y
         | pres _ => DS_const (err error_Cl)
         end.
  Proof.
    intros.
    unfold fbysf.
    autorewrite with localdb using (simpl (snd _); simpl (fst _)).
    destruct y; auto.
  Qed.

  Lemma fbyf_eq : forall F x xs ys,
      fbysf F false (cons x xs) ys
      == match x with
         | abs => cons abs (F true xs ys)
         | pres v => cons x (fby1AP None xs ys)
         | err _ => DS_const x
         end.
  Proof.
    intros.
    unfold fbysf.
    autorewrite with localdb using (simpl (snd _); simpl (fst _)).
    setoid_rewrite fcont_comp_simpl.
    destruct x. 1,3: auto.
    (* TODO: pourquoi auto ne fonctionne pas ici ?? *)
    now autorewrite with localdb using (simpl (snd _); simpl (fst _)).
  Qed.

  Definition fbys : (bool -O-> DS (sampl A) -C-> DS (sampl A) -C-> DS (sampl A)) :=
    FIXP _ fbysf.

  Lemma fbysF_eq : forall x xs ys,
      fbys false (cons x xs) ys
      == match x with
         | abs => cons abs (fbys true xs ys)
         | pres v => cons x (fby1AP None xs ys)
         | err _ => DS_const x
         end.
  Proof.
    intros.
    unfold fbys.
    assert (Heq:=FIXP_eq fbysf).
    rewrite (ford_eq_elim (ford_eq_elim Heq false) (cons x xs)).
    now rewrite <- fbyf_eq.
  Qed.

  Lemma fbysT_eq : forall xs y ys,
      fbys true xs (cons y ys)
      == match y with
         | abs => fbys false xs ys
         | err _ => DS_const y
         | pres _ => DS_const (err error_Cl)
         end.
  Proof.
    intros.
    unfold fbys.
    assert (Heq:=FIXP_eq fbysf).
    rewrite (ford_eq_elim (ford_eq_elim Heq true) xs).
    now rewrite <- fbyAf_eq.
  Qed.

  Definition fbyA : DS (sampl A) -C-> DS (sampl A) -C-> DS (sampl A) := fbys true.
  Definition fby : DS (sampl A) -C-> DS (sampl A) -C-> DS (sampl A) := fbys false.

  Lemma fbyA_eq : forall xs y ys,
      fbyA xs (cons y ys)
      == match y with
         | abs => fby xs ys
         | err _ => DS_const y
         | pres _ => DS_const (err error_Cl)
         end.
  Proof.
    intros.
    unfold fbyA, fbys.
    assert (Heq:=FIXP_eq fbysf).
    rewrite (ford_eq_elim Heq).
    now rewrite fbyAf_eq.
  Qed.

  Lemma fby_eq : forall x xs ys,
      fby (cons x xs) ys
      == match x with
         | abs => cons abs (fbyA xs ys)
         | pres v => cons x (fby1AP None xs ys)
         | err _ => DS_const x
         end.
  Proof.
    intros.
    unfold fby, fbys.
    assert (Heq:=FIXP_eq fbysf).
    rewrite (ford_eq_elim Heq).
    now rewrite fbyf_eq.
  Qed.

  Lemma fbyA_cons :
    forall xs ys,
      is_cons (fbyA xs ys) ->
      is_cons ys.
  Proof.
    unfold fbyA, fbys.
    intros * Hc.
    rewrite ford_eq_elim with (n := true) in Hc.
    2: rewrite FIXP_eq; reflexivity.
    now apply DScase_is_cons in Hc.
  Qed.

  Lemma fby_cons :
    forall xs ys,
      is_cons (fby xs ys) ->
      is_cons xs.
  Proof.
    unfold fby, fbys.
    intros * Hc.
    rewrite ford_eq_elim with (n := false) in Hc. (* WTF *)
    2: rewrite FIXP_eq; reflexivity.
    now apply DScase_is_cons in Hc.
  Qed.

  (* Definition swhenf : *)
  (*   (DS (sampl bool * sampl A) -C-> DS (sampl A)) -C-> *)
  (*   DS (sampl bool * sampl A) -C-> DS (sampl A). *)
  (*   apply curry. *)
  (*   apply (fcont_comp2 (DSCASE (sampl bool * sampl A) (sampl A))). *)
  (*   2:exact (SND _ _). *)
  (*   apply ford_fcont_shift. intros (vc,vx). *)
  (*   apply curry. *)
  (*   match goal with *)
  (*   | |- _ (_ (Dprod ?pl ?pr) _) => *)
  (*       pose (f := (FST _ _ @_ (FST pl pr))); *)
  (*       pose (CX := SND pl pr) *)
  (*   end. *)
  (*   destruct vc as [|c], vx as [|x]. *)
  (*   (* asynchronous cases *) *)
  (*   2,3: apply CTE, DS_bot. *)
  (*   (* absent *) *)
  (*   apply (CONS absent @_ (f @2_ ID _) CX). *)
  (*   (* present *) *)
  (*   destruct c. *)
  (*   (* - true *) *)
  (*   apply (CONS (present x) @_ (f @2_ ID _) CX). *)
  (*   (* - false *) *)
  (*   apply (CONS absent @_ (f @2_ ID _) CX). *)
  (* Defined. *)

  (* Lemma swhenf_eq : forall f c x CX, *)
  (*     swhenf f (cons (c, x) CX) *)
  (*     = match c, x with *)
  (*       | present true, present x => cons (present x) (f CX) *)
  (*       | present false, present x => cons absent (f CX) *)
  (*       | absent, absent => cons absent (f CX) *)
  (*       | _, _ => 0 *)
  (*       end. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold swhenf. *)
  (*   rewrite curry_Curry, Curry_simpl. *)
  (*   setoid_rewrite DSCASE_simpl. *)
  (*   setoid_rewrite DScase_cons. *)
  (*   destruct c as [|[]], x; now simpl. *)
  (* Qed. *)

  (* Definition swhen : DS (sampl bool) -C-> DS (sampl A) -C-> DS (sampl A) := *)
  (*   curry (FIXP _ swhenf @_ (ZIP pair @2_ FST _ _) (SND _ _ )). *)

  (* Lemma swhen_eq : forall c C x X, *)
  (*     swhen (cons c C) (cons x X) *)
  (*     == match c, x with *)
  (*        | present true, present x => cons (present x) (swhen C X) *)
  (*        | present false, present x => cons absent (swhen C X) *)
  (*        | absent, absent => cons absent (swhen C X) *)
  (*        | _, _ => 0 *)
  (*        end. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold swhen. *)
  (*   autorewrite with localdb using (simpl (snd _); simpl (fst _)). *)
  (*   rewrite FIXP_eq at 1. *)
  (*   now rewrite swhenf_eq. *)
  (* Qed. *)

  (* Definition smergef : *)
  (*   (DS (sampl bool * sampl A * sampl A) -C-> DS (sampl A)) *)
  (*   -C-> DS (sampl bool * sampl A * sampl A) -C-> DS (sampl A). *)
  (*   apply curry. *)
  (*   apply (fcont_comp2 (DSCASE (sampl bool * sampl A * sampl A) (sampl A))). *)
  (*   2:exact (SND _ _). *)
  (*   apply ford_fcont_shift. intros ((vc & v1) & v2). *)
  (*   apply curry. *)
  (*   match goal with *)
  (*   | |- _ (_ (Dprod ?pl ?pr) _) => *)
  (*       pose (f := (FST _ _ @_ (FST pl pr))); *)
  (*       pose (CUV := SND pl pr) *)
  (*   end. *)
  (*   destruct vc as [|[]]. *)
  (*   - (* absent clock *) *)
  (*     destruct v1, v2. *)
  (*     (* asynchronous cases *) *)
  (*     2,3,4: apply CTE, DS_bot. *)
  (*     apply (CONS absent @_ (f @2_ ID _) CUV). *)
  (*   - (* true *) *)
  (*     destruct v1 as [|v1], v2. *)
  (*     (* asynchronous cases *) *)
  (*     1,2,4: apply CTE, DS_bot. *)
  (*     apply (CONS (present v1) @_ (f @2_ ID _) CUV). *)
  (*   - (* false *) *)
  (*     destruct v1, v2 as [|v2]. *)
  (*     (* asynchronous cases *) *)
  (*     1,3,4: apply CTE, DS_bot. *)
  (*     apply (CONS (present v2) @_ (f @2_ ID _) CUV). *)
  (* Defined. *)

  (* Lemma smergef_eq : forall f c x y CXY, *)
  (*     smergef f (cons (c, x, y) CXY) *)
  (*     = match c, x, y with *)
  (*       | present true, present x, absent => cons (present x) (f CXY) *)
  (*       | present false, absent, present y => cons (present y) (f CXY) *)
  (*       | absent, absent, absent => cons absent (f CXY) *)
  (*       | _, _, _ => 0 *)
  (*       end. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold smergef. *)
  (*   rewrite curry_Curry, Curry_simpl. *)
  (*   setoid_rewrite DSCASE_simpl. *)
  (*   setoid_rewrite DScase_cons. *)
  (*   destruct c as [|[]], x, y; now simpl. *)
  (* Qed. *)

  (* Definition smerge : *)
  (*   DS (sampl bool) -C-> DS (sampl A) -C-> DS (sampl A) -C-> DS (sampl A) := *)
  (*   curry (curry (FIXP _ smergef @_ *)
  (*                      ((ZIP pair @2_ *)
  (*                            ((ZIP pair @2_ (FST _ _ @_  FST _ _)) *)
  (*                               (SND _ _ @_ FST _ _))) *)
  (*                         (SND _ _)))). *)


  (* Lemma smerge_eq : forall c C x X y Y, *)
  (*     smerge (cons c C) (cons x X) (cons y Y) *)
  (*     == match c, x, y with *)
  (*        | present true, present x, absent => cons (present x) (smerge C X Y) *)
  (*        | present false, absent, present y => cons (present y) (smerge C X Y) *)
  (*        | absent, absent, absent => cons absent (smerge C X Y) *)
  (*        | _, _, _ => 0 *)
  (*        end. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold smerge. *)
  (*   autorewrite with localdb using (simpl (snd _); simpl (fst _)). *)
  (*   rewrite FIXP_eq at 1. *)
  (*   now rewrite smergef_eq. *)
  (* Qed. *)

  (* Definition sitef : *)
  (*   (DS (sampl bool * sampl A * sampl A) -C-> DS (sampl A)) *)
  (*   -C-> DS (sampl bool * sampl A * sampl A) -C-> DS (sampl A). *)
  (*   apply curry. *)
  (*   apply (fcont_comp2 (DSCASE (sampl bool * sampl A * sampl A) (sampl A))). *)
  (*   2:exact (SND _ _). *)
  (*   apply ford_fcont_shift. intros ((vc & v1) & v2). *)
  (*   apply curry. *)
  (*   match goal with *)
  (*   | |- _ (_ (Dprod ?pl ?pr) _) => *)
  (*       pose (f := (FST _ _ @_ (FST pl pr))); *)
  (*       pose (CUV := SND pl pr) *)
  (*   end. *)
  (*   destruct vc as [|[]]. *)
  (*   - (* absent clock *) *)
  (*     destruct v1, v2. *)
  (*     (* asynchronous cases *) *)
  (*     2,3,4: apply CTE, DS_bot. *)
  (*     apply (CONS absent @_ (f @2_ ID _) CUV). *)
  (*   - (* true *) *)
  (*     destruct v1 as [|v1], v2. *)
  (*     (* asynchronous cases *) *)
  (*     1,2,3: apply CTE, DS_bot. *)
  (*     apply (CONS (present v1) @_ (f @2_ ID _) CUV). *)
  (*   - (* false *) *)
  (*     destruct v1, v2 as [|v2]. *)
  (*     (* asynchronous cases *) *)
  (*     1,2,3: apply CTE, DS_bot. *)
  (*     apply (CONS (present v2) @_ (f @2_ ID _) CUV). *)
  (* Defined. *)

  (* Lemma sitef_eq : forall f c x y CXY, *)
  (*     sitef f (cons (c, x, y) CXY) *)
  (*     = match c, x, y with *)
  (*       | present true, present x, present y => cons (present x) (f CXY) *)
  (*       | present false, present x, present y => cons (present y) (f CXY) *)
  (*       | absent, absent, absent => cons absent (f CXY) *)
  (*       | _, _, _ => 0 *)
  (*       end. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold sitef. *)
  (*   rewrite curry_Curry, Curry_simpl. *)
  (*   setoid_rewrite DSCASE_simpl. *)
  (*   setoid_rewrite DScase_cons. *)
  (*   destruct c as [|[]], x, y; now simpl. *)
  (* Qed. *)

  (* Definition site : *)
  (*   DS (sampl bool) -C-> DS (sampl A) -C-> DS (sampl A) -C-> DS (sampl A) := *)
  (*   curry (curry (FIXP _ sitef @_ *)
  (*                      ((ZIP pair @2_ *)
  (*                            ((ZIP pair @2_ (FST _ _ @_  FST _ _)) *)
  (*                               (SND _ _ @_ FST _ _))) *)
  (*                         (SND _ _)))). *)

  (* Lemma site_eq : forall c C x X y Y, *)
  (*     site (cons c C) (cons x X) (cons y Y) *)
  (*     == match c, x, y with *)
  (*       | present true, present x, present y => cons (present x) (site C X Y) *)
  (*       | present false, present x, present y => cons (present y) (site C X Y) *)
  (*       | absent, absent, absent => cons absent (site C X Y) *)
  (*       | _, _, _ => 0 *)
  (*       end. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold site. *)
  (*   autorewrite with localdb using (simpl (snd _); simpl (fst _)). *)
  (*   rewrite FIXP_eq at 1. *)
  (*   now rewrite sitef_eq. *)
  (* Qed. *)

  (* Definition sarrowf : (DS (sampl A) -C-> DS (sampl A) -C-> DS (sampl A)) -C-> *)
  (*                      DS (sampl A) -C-> DS (sampl A) -C-> DS (sampl A). *)
  (*   apply curry. *)
  (*   apply curry. *)
  (*   eapply (fcont_comp2 (DSCASE (sampl A) (sampl A))). *)
  (*   2: exact (SND _ _ @_ FST _ _). *)
  (*   apply ford_fcont_shift. intro vx. *)
  (*   apply curry. *)
  (*   eapply (fcont_comp2 (DSCASE (sampl A) (sampl A))). *)
  (*   2: exact (SND _ _ @_ FST _ _). *)
  (*   apply ford_fcont_shift. intro vy. *)
  (*   apply curry. *)
  (*   destruct vx as [|x], vy as [|y]. *)
  (*   (* non-synchronous cases *) *)
  (*   2,3: apply CTE, DS_bot. *)
  (*   (* absent *) *)
  (*   apply (fcont_comp ((CONS absent))). *)
  (*   exact ((AP _ _ @3_ (FST _ _ @_ FST _ _ @_ FST _ _ @_ FST _ _)) *)
  (*            (SND _ _ @_ FST _ _) (SND _ _)). *)
  (*   (* present *) *)
  (*   apply (fcont_comp (CONS (present x))). *)
  (*   apply uncurry, uncurry, CTE, (sbinop (fun x y => y)). *)
  (* Defined. *)

  (* Definition sarrow : DS (sampl A) -C-> DS (sampl A) -C-> DS (sampl A) := *)
  (*   FIXP _ sarrowf. *)

  (* Definition sarrowf_eq : forall f x xs y ys, *)
  (*     sarrowf f (cons x xs) (cons y ys) *)
  (*     = match x, y with *)
  (*       | present x, present y => cons (present x) (sbinop (fun x y => y) xs ys) *)
  (*       | absent, absent => cons absent (f xs ys) *)
  (*       | _, _ => 0 *)
  (*       end. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold sarrowf. *)
  (*   autorewrite with localdb using (simpl (snd _); simpl (fst _)). *)
  (*   setoid_rewrite fcont_comp_simpl. *)
  (*   destruct x, y; *)
  (*     now autorewrite with localdb using (simpl (snd _); simpl (fst _)). *)
  (* Qed. *)

  (* Lemma sarrow_eq : forall x y xs ys, *)
  (*     sarrow (cons x xs) (cons y ys) *)
  (*     == match x, y with *)
  (*        | present x, present y => cons (present x) (sbinop (fun x y => y) xs ys) *)
  (*        | absent, absent => cons absent (sarrow xs ys) *)
  (*        | _, _ => 0 *)
  (*        end. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold sarrow. *)
  (*   assert (Heq:=FIXP_eq sarrowf). *)
  (*   rewrite (fcont_eq_elim Heq). *)
  (*   now rewrite sarrowf_eq. *)
  (* Qed. *)

End SStream_functions.


(* (* Première tentative de définition du sreset, pour des fontions avec exactement *)
(*    un flot en entrée et un en sortie. La définition générale, qui requiert les *)
(*    définitions de syntaxe, est donnée dans SD.v. *) *)
(* Section Simple_sreset. *)

(*   Context {A B : Type}. *)

(*   (* we do not need the clocks of X and R to be aligned *) *)
(*   (* let rec reset_aux f R X Y = *)
(*      match hd R with *)
(*      | present true -> reset_aux f (Cons (present false) (tl R)) X (f X) *)
(*      | _ -> Cons (hd Y) (reset_aux f (tl R) (tl X) (tl Y)) *)
(*    *) *)
(*   (* TODO: c'est moins restrictif que dans resetf_aux (version Kahnienne): *)
(*      resetf_aux commence par lire R avant de brancher, donc X et Y n'avanceront *)
(*      pas si R n'arrive pas (absent). Il faudra sans doute faire un cas pour *)
(*      absent. *)
(*    *) *)
(*   Definition sresetf_aux : *)
(*     ((DS (sampl A) -C-> DS (sampl B)) -C-> *)
(*      DS (sampl bool) -C-> DS (sampl A) -C-> DS (sampl B) -C-> DS (sampl B)) -C-> *)
(*     (DS (sampl A) -C-> DS (sampl B)) -C-> *)
(*     DS (sampl bool) -C-> DS (sampl A) -C-> DS (sampl B) -C-> DS (sampl B). *)
(*     do 4 apply curry. *)
(*     match goal with *)
(*     | |- _ (_ (Dprod ?pl ?pr) _) => *)
(*         pose (reset := FST _ _ @_ (FST _ _ @_ (FST _ _ @_ (FST pl pr)))); *)
(*         pose (f := SND _ _ @_ (FST _ _ @_ (FST _ _ @_ (FST pl pr)))); *)
(*         pose (R := SND _ _ @_ (FST _ _ @_ (FST pl pr))); *)
(*         pose (X := SND _ _ @_ (FST pl pr)); *)
(*         pose (Y := SND pl pr); *)
(*         idtac *)
(*     end. *)
(*     apply (fcont_comp2 (DSCASE (sampl bool) _)). 2: exact R. *)
(*     apply ford_fcont_shift; intro vr; apply curry. *)
(*     destruct vr as [|[]] eqn:?. *)
(*     - (* vr = absent *) *)
(*       eapply fcont_comp. 2: apply FST. *)
(*       exact ((APP _ @2_ Y) ((AP _ _ @5_ reset) f (REM _ @_ R) (REM _ @_ X) *)
(*                                                (REM _ @_ Y))). *)
(*     - (* vr = present true *) *)
(*       eapply fcont_comp. 2: apply FST. *)
(*       exact ((AP _ _ @5_ reset) f (CONS (present false) @_ (REM _ @_ R)) *)
(*                                 X ((AP _ _ @2_ f) X)). *)
(*     - (* vr = present false *) *)
(*       eapply fcont_comp. 2: apply FST. *)
(*       exact ((APP _ @2_ Y) ((AP _ _ @5_ reset) f (REM _ @_ R) (REM _ @_ X) *)
(*                                                (REM _ @_ Y))). *)
(*   Defined. *)

(*   Definition sreset_aux : *)
(*     (DS (sampl A) -C-> DS (sampl B)) -C-> *)
(*     DS (sampl bool) -C-> DS (sampl A) -C-> DS (sampl B) -C-> DS (sampl B) := *)
(*     FIXP _ sresetf_aux. *)

(*   Lemma sresetf_aux_eq : forall F f vr R X Y, *)
(*       sresetf_aux F f (cons vr R) X Y == *)
(*         match vr with *)
(*         | present true => F f (cons (present false) R) X (f X) *)
(*         | _ => app Y (F f R (rem X) (rem Y)) *)
(*         end. *)
(*   Proof. *)
(*     intros. *)
(*     unfold sresetf_aux. *)
(*     setoid_rewrite fcont_comp_simpl. *)
(*     rewrite fcont_comp2_simpl. *)
(*     rewrite DSCASE_simpl. *)
(*     setoid_rewrite DScase_cons. *)
(*     destruct vr as [|[]]; cbn; now autorewrite with localdb. *)
(*   Qed. *)

(*   Lemma sreset_aux_eq : forall f vr R X Y, *)
(*       sreset_aux f (cons vr R) X Y == *)
(*         match vr with *)
(*         | present true => sreset_aux f (cons (present false) R) X (f X) *)
(*         | _ => app Y (sreset_aux f R (rem X) (rem Y)) *)
(*         end. *)
(*   Proof. *)
(*     intros. *)
(*     assert (Heq:=FIXP_eq sresetf_aux). *)
(*     rewrite Heq at 1. *)
(*     now rewrite sresetf_aux_eq. *)
(*   Qed. *)

(*   (** - let sreset f R X = sreset_aux f R X (f X) *) *)
(*   Definition sreset : (DS (sampl A) -C-> DS (sampl B)) -C-> *)
(*                       DS (sampl bool) -C-> DS (sampl A) -C-> DS (sampl B). *)
(*     do 2 apply curry. *)
(*     match goal with *)
(*     | |- _ (_ (Dprod ?pl ?pr) _) => *)
(*         pose (f := FST _ _ @_ (FST pl pr)); *)
(*         pose (R := SND _ _ @_ (FST pl pr)); *)
(*         pose (X := SND pl pr); *)
(*         idtac *)
(*     end. *)
(*     exact ((sreset_aux @4_ f) R X ((AP _ _ @2_ f) X)). *)
(*   Defined. *)

(*   Lemma sreset_eq : forall f R X, *)
(*       sreset f R X == sreset_aux f R X (f X). *)
(*   Proof. *)
(*     intros. *)
(*     unfold sreset. *)
(*     now autorewrite with localdb. *)
(*   Qed. *)

(* End Simple_sreset. *)
