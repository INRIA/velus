From Coq Require Import BinPos List.
Import List ListNotations.
From Velus Require Import CommonTactics.
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
     fcont_comp3_simpl
     fcont_comp4_simpl
     SND_simpl Snd_simpl
     FST_simpl Fst_simpl
     DSCASE_simpl
     DScase_cons
     @zip_cons
  : localdb.


(** *** abstract_clock as defined in Vélus, considering errors as absences *)
Section Abstract_clock.

  Context {A I : Type}.

  Definition AC : DS (sampl A) -C-> DS bool :=
    MAP (fun v => match v with pres _ => true | _ => false end).

  Lemma AC_cons :
    forall u U,
      AC (cons u U) == cons match u with
                         | pres _ => true
                         | _ => false
                         end (AC U).
  Proof.
    intros.
    unfold AC.
    rewrite MAP_map, map_eq_cons.
    destruct u; auto.
  Qed.

  Lemma AC_is_cons :
    forall U, is_cons (AC U) <-> is_cons U.
  Proof.
    split; eauto using map_is_cons, is_cons_map.
  Qed.

  Lemma first_AC :
    forall s, first (AC s) == AC (first s).
  Proof.
    intros; apply first_map.
  Qed.

  Lemma rem_AC :
    forall s, rem (AC s) == AC (rem s).
  Proof.
    intros; apply rem_map.
  Qed.

  (** equivalent of [clocks_of] *)
  Fixpoint bss (ins : list I) : DS_prod (fun _ => sampl A) -C-> DS bool :=
    match ins with
    | [] => CTE _ _ (DS_const false)
    | x :: nil => AC @_ PROJ _ x
    | x :: ins => (ZIP orb @2_ (AC @_ PROJ _ x)) (bss ins)
    end.

  Lemma bss_cons :
    forall x l env,
      bss (x :: l) env == ZIP orb (AC (env x)) (bss l env).
  Proof.
    destruct l; simpl; auto.
    intro env.
    autorewrite with cpodb.
    rewrite zip_comm, zip_const; auto using Bool.orb_comm.
    unfold AC.
    now rewrite 3 MAP_map, map_comp.
  Qed.

  Lemma bss_cons2 :
    forall x y l env,
      bss (x :: y :: l) env = ZIP orb (AC (env x)) (bss (y :: l) env).
  Proof.
    trivial.
  Qed.

  Lemma bss_inf :
    forall l env,
      all_infinite env ->
      infinite (bss l env).
  Proof.
    induction l as [|?[]]; simpl; intros * Hinf.
    - apply DS_const_inf.
    - autorewrite with cpodb.
      apply map_inf, Hinf.
    - autorewrite with cpodb.
      apply zip_inf; auto.
      apply map_inf, Hinf.
  Qed.

  Lemma bss_switch_env :
    forall l env env',
      (forall x, In x l -> env x == env' x) ->
      bss l env == bss l env'.
  Proof.
    induction l as [|x []]; intros * Heq; auto.
    - simpl; autorewrite with cpodb.
      rewrite (Heq x); simpl; auto.
    - simpl; autorewrite with cpodb.
      rewrite (Heq x), IHl; simpl in *; eauto.
  Qed.

  Lemma rem_bss :
    forall l env,
      rem (bss l env) == bss l (REM_env env).
  Proof.
    induction l; intros.
    - simpl.
      autorewrite with cpodb.
      now rewrite DS_const_eq, rem_cons at 1.
    - now rewrite 2 bss_cons, rem_zip, rem_AC, IHl.
  Qed.

End Abstract_clock.


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

  Lemma is_cons_sbinop : forall bop U V,
      is_cons U /\ is_cons V ->
      is_cons (sbinop bop U V).
  Proof.
    intros * []; unfold sbinop.
    autorewrite with cpodb.
    now apply is_cons_map, is_cons_zip.
  Qed.

  Lemma sbinop_is_cons : forall bop U V,
      is_cons (sbinop bop U V) ->
      is_cons U /\ is_cons V.
  Proof.
    unfold sbinop; intros *.
    autorewrite with cpodb; intros.
    now apply map_is_cons, zip_is_cons in H.
  Qed.

End Sunop_binop.


Section SStream_functions.

  Context {A B : Type}.

  (** Rythm of constants if given by the base clock as an argument *)
  Definition sconst (v : A) : DS bool -C-> DS (sampl A) :=
    MAP (fun c : bool => if c then pres v else abs).

  Lemma AC_sconst :
    forall c bs,
      AC (sconst c bs) == bs.
  Proof.
    intros.
    unfold AC, sconst.
    rewrite 2 MAP_map, map_comp.
    eapply DS_bisimulation_allin1
      with (R := fun U V => U == map _ V).
    3: eauto.
    { now intros ????? <- <-. }
    intros U V Hc Hu. rewrite Hu in *.
    split.
    - destruct Hc as [Hc|Hc]. apply map_is_cons in Hc.
      all: apply is_cons_elim in Hc as (?&?&Hv).
      all: rewrite Hv, map_eq_cons, 2 first_cons; destruct x; auto.
    - now rewrite rem_map.
  Qed.

  (** fby1 is defined by means of two mutually recursive functions, see
      [fby1APf_eq] and [fby1f_eq] above for explanation
      That is why we keep an option in fby1, even if it is always called
      with (Some _).
   *)
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
    pose proof (ford_eq_elim (ford_eq_elim Heq true)) as ->.
    rewrite fby1APf_eq.
    unfold fby1, fby1s; auto.
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
    rewrite fby1f_eq.
    unfold fby1AP, fby1s; auto.
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
    pose proof (ford_eq_elim (ford_eq_elim Heq false) (cons x xs)) as ->.
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
    pose proof (ford_eq_elim (ford_eq_elim Heq true) xs) as ->.
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


  Section When_Case.

  Variable enumtag : Type.
  Variable tag_of_val : B -> option enumtag.
  Variable tag_eqb : enumtag -> enumtag -> bool.

  Hypothesis tag_eqb_eq : forall t1 t2, tag_eqb t1 t2 = true <-> t1 = t2.

  Lemma tag_eqb_refl : forall t, tag_eqb t t = true.
  Proof. intro; now apply tag_eqb_eq. Qed.

  Lemma tag_eqb_neq : forall t1 t2, tag_eqb t1 t2 = false <-> t1 <> t2.
  Proof.
    intros.
    destruct (tag_eqb _ _) eqn:HH.
    - firstorder; congruence.
    - firstorder; intros HHH%tag_eqb_eq; congruence.
  Qed.

  Definition swhenf (k : enumtag) :
    (DS (sampl A * sampl B) -C-> DS (sampl A)) -C->
    (DS (sampl A * sampl B) -C-> DS (sampl A)).
    apply curry.
    apply (fcont_comp2 (DSCASE (sampl A * sampl B) (sampl A))).
    2:exact (SND _ _).
    apply ford_fcont_shift. intros (vx,vc).
    apply curry.
    match goal with
    | |- _ (_ (Dprod ?pl ?pr) _) =>
        pose (f := (FST _ _ @_ (FST pl pr)));
        pose (XC := SND pl pr)
    end.
    exact match vx, vc with
    | abs, abs => CONS abs @_ (f @2_ ID _) XC
    | pres x, pres c =>
        match tag_of_val c with
        | None => CTE _ _ (DS_const (err error_Ty))
        | Some t =>
            if tag_eqb k t
            then CONS (pres x) @_ (f @2_ ID _) XC
            else CONS abs @_ (f @2_ ID _) XC
        end
    | err e, _
    | _, err e => CTE _ _ (DS_const (err e))
    | _, _ => CTE _ _ (DS_const (err error_Cl))
    end.
  Defined.

  Lemma swhenf_eq : forall k f x c XC,
      swhenf k f (cons (x, c) XC)
      = match x, c with
        | abs, abs => cons abs (f XC)
        | pres x, pres c =>
            match tag_of_val c with
            | None => DS_const (err error_Ty)
            | Some t =>
                if tag_eqb k t
                then cons (pres x) (f XC)
                else cons abs (f XC)
            end
        | err e, _ | _, err e => DS_const (err e)
        | _, _ => DS_const (err error_Cl)
        end.
  Proof.
    intros.
    unfold swhenf.
    rewrite curry_Curry, Curry_simpl.
    setoid_rewrite DSCASE_simpl.
    setoid_rewrite DScase_cons.
    destruct x, c; simpl; auto.
    destruct (tag_of_val _); auto.
    destruct (tag_eqb _ _); auto.
  Qed.

  Definition swhen (k : enumtag) : DS (sampl A) -C-> DS (sampl B) -C-> DS (sampl A) :=
    curry (FIXP _ (swhenf k) @_ (ZIP pair @2_ FST _ _) (SND _ _ )).

  Lemma swhen_eq : forall k c C x X,
      swhen k (cons x X) (cons c C)
      == match x, c with
        | abs, abs => cons abs (swhen k X C)
        | pres x, pres c =>
            match tag_of_val c with
            | None => DS_const (err error_Ty)
            | Some t =>
                if tag_eqb k t
                then cons (pres x) (swhen k X C)
                else cons abs (swhen k X C)
            end
        | err e, _ | _, err e => DS_const (err e)
        | _, _ => DS_const (err error_Cl)
        end.
  Proof.
    intros.
    unfold swhen.
    autorewrite with localdb using (simpl (snd _); simpl (fst _)).
    rewrite FIXP_eq at 1.
    now rewrite swhenf_eq.
  Qed.

  Lemma swhen_cons :
    forall k xs cs,
      is_cons (swhen k xs cs) ->
      is_cons xs /\ is_cons cs.
  Proof.
    intros *.
    unfold swhen.
    rewrite FIXP_eq; autorewrite with cpodb; simpl.
    intros Hc. apply DScase_is_cons in Hc.
    setoid_rewrite SND_PAIR_simpl in Hc.
    eapply zip_is_cons; eauto.
  Qed.

  (** Le cas du merge/case est plus délicat car il opère sur une liste
      (nprod) de flots. On utilise pour ça [nprod_Foldi], qui effectue
      un fold_right sur la liste combinée des flots et des informations
      de tag. (quel flot correspond à quel tag ?).
   *)

  (* TODO: move, déjà présent dans Vélus... *)
  Definition or_default {A} (d: A) (o: option A) : A :=
    match o with Some a => a | None => d end.

  Definition is_tag (i : enumtag) (x : sampl B) : sampl bool :=
    match x with
    | pres v => or_default (err error_Ty)
                 (option_map (fun j => pres (tag_eqb i j)) (tag_of_val v))
    (* TODO: comment faire ces deux cas en un seul ? *)
    | abs => abs
    | err e => err e
    end.

  (* Selon le statut de la condition, on initialise l'accumulateur du
     fold_right avec [abs] ou [error_Ty]. *)
  Definition defcon (c : sampl B) : sampl A :=
    match c with
    | abs => abs
    | pres _ => err error_Ty
    | err e => err e
    end.

  (* La fonction qu'on va passer à fold_right pour calculer le merge :
     - si la condition est [pres i], on part de [error_Ty] et on
       espère que le flot de tag i soit présent et les autre absents;
     - si la condition est [abs], on part de [abs] et on vérifie que
       tous les flots sont absents. *)
  (* j/x : tag/flot examinés dans la liste, c : condition, a : accumulateur *)
  Definition fmerge (j : enumtag) (c : sampl B) (x a : sampl A) :=
    match is_tag j c, a, x with
    | abs, abs, abs => abs
    | pres true, err error_Ty, pres v => pres v
    | pres false, a, abs => a
    | _,_,_ => err error_Cl
    end.

  Definition smerge (l : list enumtag) :
    DS (sampl B) -C-> @nprod (DS (sampl A)) (length l) -C-> DS (sampl A).
    eapply fcont_comp2.
    apply nprod_Foldi.
    2: apply (MAP defcon).
    apply ford_fcont_shift; intro j.
    apply (ZIP3 (fmerge j)).
  Defined.

  Lemma smerge_eq :
    forall l C np,
      smerge l C np = nprod_Foldi l (fun j => ZIP3 (fmerge j) C) (map defcon C) np.
  Proof.
    trivial.
  Qed.

  (* Une définition alternative du merge est la suivante, avec
     accumulateur initial [abs]. Elle est plus simple mais ne permet pas
     d'exclure le cas où une branche est manquante (c = pres j mais j∉l).

   Definition fmerge (c : sampl B) :=
    fun '(j, x) (a : sampl A) =>
      match is_tag j c, a, x with
      | abs, abs, abs => abs
      | pres true, abs, pres v => pres v
      | pres false, a, abs => a
      | _,_,_ => err error_Cl
      end.
   *)

  Lemma smerge_is_cons :
    forall l C np,
      l <> [] ->
      is_cons (smerge l C np) ->
      is_cons C /\ forall_nprod (@is_cons _) np.
  Proof.
    induction l as [|? []].
    - congruence.
    - intros * _.
      rewrite smerge_eq, Foldi_cons.
      intros (?& Hc &?) % zip3_is_cons.
      split; auto.
    - intros * _.
      rewrite smerge_eq, Foldi_cons.
      intros (?&? & Hc) % zip3_is_cons.
      apply (IHl C (nprod_tl np)) in Hc as []; try congruence.
      do 2 (split; auto).
  Qed.

  Lemma is_cons_smerge :
    forall l cs xs,
      is_cons cs ->
      forall_nprod (@is_cons _) xs ->
      is_cons (smerge l cs xs).
  Proof.
    intros * Hc Hx.
    rewrite smerge_eq.
    eapply forall_nprod_Foldi in Hx; eauto using is_cons_DS_const.
    simpl; intros.
    now apply is_cons_zip3.
  Qed.

  Lemma rem_smerge :
    forall l C np,
      rem (smerge l C np)
      == smerge l (rem C) (lift (REM _) np).
  Proof.
    induction l; intros.
    - now rewrite 2 smerge_eq, 2 Foldi_nil, rem_map.
    - rewrite 2 smerge_eq, 2 Foldi_cons, <- 2 smerge_eq.
      now rewrite rem_zip3, lift_hd, lift_tl, IHl.
  Qed.

  Lemma smerge_cons :
    forall l c cs np,
    forall (Hc : forall_nprod (@is_cons _) np),
      smerge l (cons c cs) np
      == cons (fold_right (fun '(j,x) => fmerge j c x) (defcon c)
                 (combine l (nprod_hds np Hc)))
           (smerge l cs (lift (REM _) np)).
  Proof.
    intros.
    apply first_rem_eq.
    - rewrite first_cons, smerge_eq, Foldi_fold_right.
      revert dependent np; clear.
      induction l; intros.
      + simpl. now rewrite first_map, first_cons, map_eq_cons, map_bot.
      + simpl.
        rewrite first_zip3, first_cons, (IHl _ (forall_nprod_tl _ _ Hc)).
        clear IHl.
        destruct (@is_cons_elim _ (nprod_hd np)) as (x &?& Heq).
        { now apply forall_nprod_hd in Hc. }
        remember (projT1 _) as y eqn:Hy.
        assert (x = y); subst.
        { destruct (uncons _) as (?&?& Hd); simpl.
          apply decomp_eqCon in Hd; rewrite Hd in Heq.
          now apply Con_eq_simpl in Heq. }
        rewrite Heq, first_cons, zip3_cons, zip3_bot1 at 1; auto.
    - now rewrite rem_smerge, 2 rem_cons.
  Qed.

  (** Caractérisation de [fmerge] itéré sur la têtes des flots *)
  Section fmerge_spec.

  Lemma fmerge_abs :
    forall (l : list (enumtag * sampl A)) c,
      fold_right (fun '(j,x) => fmerge j c x) (defcon c) l = abs ->
      c = abs /\ Forall (fun '(j, x) => x = abs) l.
  Proof.
    induction l as [|[]]; simpl; intros c Hf.
    { destruct c; simpl in Hf; auto; congruence. }
    unfold fmerge at 1 in Hf.
    destruct c as [|k|]; simpl in Hf; try congruence.
    - split; auto.
      destruct (fold_right _ _ _) eqn:HH, s; try congruence.
      apply IHl in HH as []; auto.
    - unfold or_default, option_map in Hf.
      destruct (tag_of_val _); try congruence.
      destruct (tag_eqb _ _), (fold_right _ _ _) as [| |[]] eqn:HH, s; try congruence.
      apply IHl in HH as []; auto.
  Qed.

  (* en cours de calcul, ça vaut error_Ty si la bonne branche n'est
     pas encore atteinte *)
  Lemma fmerge_pres_abs :
    forall (l : list (enumtag * sampl A)) i,
      let c := pres i in
      fold_right (fun '(j, x) => fmerge j c x) (defcon c) l = err error_Ty ->
      Forall (fun '(j, x) => x = abs) l.
  Proof.
    induction l as [|[]]; simpl; intros i Hf; auto.
    unfold fmerge in Hf at 1.
    destruct (is_tag e _) as [|[]|]; try congruence.
    all: destruct (fold_right _ _ _) as [| |[]] eqn:HH, s; try congruence.
    all: constructor; eauto.
  Qed.

  Lemma fmerge_pres :
    forall (l : list (enumtag * sampl A)) c v,
      fold_right (fun '(j, x) => fmerge j c x) (defcon c) l = pres v ->
      exists vc i,
        c = pres vc
        /\ tag_of_val vc = Some i
        /\ Exists (fun '(j, x) => j = i /\ x = pres v) l
        /\ Forall (fun '(j, x) => j <> i -> x = abs) l.
  Proof.
    induction l as [|[i s]]; simpl; intros * Hf.
    { destruct c; simpl in Hf; congruence. }
    unfold fmerge at 1 in Hf.
    destruct c as [|k|]; simpl in Hf; try congruence.
    { destruct (fold_right _ _ _) eqn:HH, s; congruence. }
    unfold or_default, option_map in Hf.
    destruct (tag_of_val k) as [t|] eqn:Hk; try congruence.
    exists k, t; do 2 split; auto.
    destruct (tag_eqb _ _) eqn:Ht.
    - (* on y est *)
      apply tag_eqb_eq in Ht; subst.
      destruct (fold_right _ _ _) as [| |[]] eqn:HH, s; inversion Hf; subst.
      split; constructor; auto; try congruence.
      eapply fmerge_pres_abs, Forall_impl in HH; eauto.
      intros []; congruence.
    - (* c'est pour plus tard *)
      destruct s; try congruence.
      apply IHl in Hf as (vc & k' & Hk' & Ht' &?&?).
      inversion Hk'; subst.
      rewrite Hk in *; inversion Ht'; split; auto.
  Qed.

  Lemma fmerge_abs_ok :
    forall (l : list enumtag) (ss : list (sampl A)),
      let c := abs in
      Forall (eq abs) ss ->
      fold_right (fun '(j, x) => fmerge j c x) (defcon c) (combine l ss) = abs.
  Proof.
    induction l; intros * Heq; auto.
    destruct ss; auto.
    inversion_clear Heq; subst; simpl.
    rewrite IHl; auto.
  Qed.

  (* si les horloges des ss respectent leur tag, le résultat est correct *)
  Lemma fmerge_pres_ok :
    forall (l : list enumtag) (ss : list (sampl A)) vt i,
      let c := pres vt in
      tag_of_val vt = Some i ->
      NoDup l ->
      Forall2 (fun j x => match x with
                       | pres _ => j = i
                       | abs => j <> i
                       | err _ => False
                       end) l ss ->
      In i l ->
      exists v, fold_right (fun '(j, x) => fmerge j c x) (defcon c) (combine l ss) = pres v.
  Proof.
    intros * Hv Nd Hf.
    (* il faut renforcer un peu l'invariant : *)
    enough ((In i l ->
             exists v, fold_right (fun '(j, x) => fmerge j c x)
                    (defcon c) (combine l ss) = pres v)
            /\ (~ In i l ->
               fold_right (fun '(j, x) => fmerge j c x)
                 (defcon c) (combine l ss) = err error_Ty)); [ tauto|].
    revert dependent ss.
    subst c; simpl.
    induction l; simpl; intros; try tauto.
    destruct ss as [| s ss]; inversion_clear Hf.
    inversion_clear Nd.
    edestruct IHl as [Hin Hnin]; eauto; clear IHl.
    simpl; unfold fmerge at 1 3; simpl.
    unfold or_default, option_map.
    rewrite Hv.
    split.
    - intros [| Ini]; subst.
      + destruct s; try tauto.
        rewrite tag_eqb_refl.
        setoid_rewrite Hnin; eauto.
      + destruct s; subst; try tauto.
        rewrite (proj2 (tag_eqb_neq a i)); eauto.
    - intro Nin.
      rewrite (proj2 (tag_eqb_neq a i)); auto.
      destruct s; subst; tauto.
  Qed.

  End fmerge_spec.

  (** Le scase ressemble au smerge mais vérifie que tous les flots sont
      sur la même horloge que la condition cf. fcase.
      On peut gérer le cas par défaut (lorsqu'une branche est volontairement
      omise) en modifiant la valeur initiale de l'accumulateur du foldi :
      sans branche par défaut, on initialise à [abs/error_Ty] comme dans smerge,
      et sinon on part de la valeur par défaut, après l'avoir synchronisée
      avec la condition cf. [defcon2].
   *)

  (* remarque : on ne détecte pas la redondance de tag *)
  Definition fcase (j : enumtag) (c : sampl B) (x a : sampl A) :=
    match is_tag j c, a, x with
    | abs, abs, abs => abs
    | _, abs, _ => err error_Cl
    | pres true, err error_Ty, pres v => pres v (* trouvé *)
    | pres true, pres _, pres v => pres v (* écrase la branche par défaut *)
    | pres false, a, pres _ => a (* horloge du case *)
    | _,_,_ => err error_Cl
    end.

  (* sans branche par défaut, on initialise l'accumulateur avec [defcon] *)
  Definition scase (l : list enumtag) :
    DS (sampl B) -C-> @nprod (DS (sampl A)) (length l) -C-> DS (sampl A).
    eapply fcont_comp2.
    apply nprod_Foldi.
    2: apply (MAP defcon).
    apply ford_fcont_shift; intro j.
    apply (ZIP3 (fcase j)).
  Defined.

  Lemma scase_eq :
    forall l C np,
      scase l C np = nprod_Foldi l (fun j => ZIP3 (fcase j) C) (map defcon C) np.
  Proof.
    trivial.
  Qed.

  (* on vérifie que la valeur par défaut [v] est bien synchronisée avec
     la condition avant d'en faire la valeur initiale de l'accumulateur *)
  Definition defcon2 (c : sampl B) (v : sampl A) : sampl A :=
    match c, v with
    | abs, abs => abs
    | pres _, pres x => pres x
    | _, _ => err error_Cl
    end.

  (* avec une branche par défaut, on utilise [defcon2] pour l'initialisation *)
  Definition scase_def_ (l : list enumtag) :
    (* flot de condition -> flot par defaut -> flots des branches -> résultat *)
    DS (sampl B) -C-> DS (sampl A) -C-> @nprod (DS (sampl A)) (length l) -C-> DS (sampl A).
    apply curry.
    eapply fcont_comp2.
    eapply nprod_Foldi.
    2: apply (uncurry (ZIP defcon2)).
    apply ford_fcont_shift; intro j.
    apply (ZIP3 (fcase j) @_ FST _ _).
  Defined.

  Lemma scase_def__eq :
    forall l cs ds np,
      scase_def_ l cs ds np =
        nprod_Foldi l (fun j => ZIP3 (fcase j) cs) (ZIP defcon2 cs ds) np.
  Proof.
    trivial.
  Qed.

  (* wrapper pour [scase_def_], qui permet son utilisation avec des
     fonctions telles que [lift_nprod] (on charge le 2ème argument) *)
  Definition scase_def (l : list enumtag) :
    DS (sampl B) -C-> @nprod (DS (sampl A)) (S (length l)) -C-> DS (sampl A).
    apply curry.
    refine ((scase_def_ l @3_ FST _ _) _ _).
    - exact (nprod_hd @_ SND _ _).
    - exact (nprod_tl @_ SND _ _).
  Defined.

  Lemma scase_def_eq :
    forall l cs ds np,
      scase_def l cs (nprod_cons ds np) = scase_def_ l cs ds np.
  Proof.
    intros.
    unfold scase_def.
    autorewrite with localdb.
    destruct l; auto.
  Qed.

  Lemma scase_is_cons :
    forall l C np,
      l <> [] ->
      is_cons (scase l C np) ->
      is_cons C /\ forall_nprod (@is_cons _) np.
  Proof.
    induction l as [|? []].
    - congruence.
    - intros * _.
      rewrite scase_eq, Foldi_cons.
      intros (?& Hc &?) % zip3_is_cons.
      split; auto.
    - intros * _.
      rewrite scase_eq, Foldi_cons.
      intros (?&? & Hc) % zip3_is_cons.
      apply (IHl C (nprod_tl np)) in Hc as []; try congruence.
      do 2 (split; auto).
  Qed.

  Lemma is_cons_scase :
    forall l cs xs,
      is_cons cs ->
      forall_nprod (@is_cons _) xs ->
      is_cons (scase l cs xs).
  Proof.
    intros * Hc Hx.
    rewrite scase_eq.
    eapply forall_nprod_Foldi in Hx; eauto.
    simpl; intros.
    now apply is_cons_zip3.
  Qed.

  Lemma rem_scase :
    forall l C np,
      rem (scase l C np)
      == scase l (rem C) (lift (REM _) np).
  Proof.
    induction l; intros.
    - now rewrite 2 scase_eq, 2 Foldi_nil, rem_map.
    - rewrite 2 scase_eq, 2 Foldi_cons, <- 2 scase_eq.
      now rewrite rem_zip3, lift_hd, lift_tl, IHl.
  Qed.

  Lemma scase_cons :
    forall l c cs np,
    forall (Hc : forall_nprod (@is_cons _) np),
      scase l (cons c cs) np
      == cons (fold_right (fun '(j,x) => fcase j c x) (defcon c)
                 (combine l (nprod_hds np Hc)))
           (scase l cs (lift (REM _) np)).
  Proof.
    intros.
    apply first_rem_eq.
    - rewrite first_cons, scase_eq, Foldi_fold_right.
      revert dependent np; clear.
      induction l; intros.
      + simpl. now rewrite first_map, first_cons, map_eq_cons, map_bot.
      + simpl.
        rewrite first_zip3, first_cons, (IHl _ (forall_nprod_tl _ _ Hc)).
        clear IHl.
        destruct (@is_cons_elim _ (nprod_hd np)) as (x &?& Heq).
        { now apply forall_nprod_hd in Hc. }
        remember (projT1 _) as y eqn:Hy.
        assert (x = y); subst.
        { destruct (uncons _) as (?&?& Hd); simpl.
          apply decomp_eqCon in Hd; rewrite Hd in Heq.
          now apply Con_eq_simpl in Heq. }
        rewrite Heq, first_cons, zip3_cons, zip3_bot1 at 1; auto.
    - now rewrite rem_scase, 2 rem_cons.
  Qed.

  Lemma scase_def__is_cons :
    forall l cs ds np,
      l <> [] ->
      is_cons (scase_def_ l cs ds np) ->
      is_cons cs /\ is_cons ds /\ forall_nprod (@is_cons _) np.
  Proof.
    induction l as [|? []].
    - congruence.
    - intros * _.
      rewrite scase_def__eq, Foldi_cons.
      intros (?& Hc & HH) % zip3_is_cons.
      rewrite Foldi_nil in HH.
      apply zip_is_cons in HH.
      tauto.
    - intros * _.
      rewrite scase_def__eq, Foldi_cons.
      intros (?&? & Hc) % zip3_is_cons.
      apply (IHl cs ds (nprod_tl np)) in Hc as (?&?&?); try congruence.
      do 2 (split; eauto using hd_tl_forall).
  Qed.

  Lemma scase_def_is_cons :
    forall l cs dnp,
      l <> [] ->
      is_cons (scase_def l cs dnp) ->
      is_cons cs /\ forall_nprod (@is_cons _) dnp.
  Proof.
    intros *.
    rewrite (nprod_hd_tl dnp), scase_def_eq.
    intros * ? Hc.
    eapply scase_def__is_cons in Hc as (?&?&?);
      eauto using forall_nprod_cons.
  Qed.

  Lemma is_cons_scase_def_ :
    forall l cs ds xs,
      is_cons cs ->
      is_cons ds ->
      forall_nprod (@is_cons _) xs ->
      is_cons (scase_def_ l cs ds xs).
  Proof.
    intros * Hc Hd Hx.
    rewrite scase_def__eq.
    eapply forall_nprod_Foldi in Hx; eauto using is_cons_zip.
    simpl; intros.
    now apply is_cons_zip3.
  Qed.

  Lemma is_cons_scase_def :
    forall l cs dxs,
      is_cons cs ->
      forall_nprod (@is_cons _) dxs ->
      is_cons (scase_def l cs dxs).
  Proof.
    intros * Hc Hdx.
    rewrite (nprod_hd_tl dxs), scase_def_eq in *.
    apply forall_nprod_cons_iff in Hdx as [].
    apply is_cons_scase_def_; auto.
  Qed.

  Lemma rem_scase_def_ :
    forall l cs ds np,
      rem (scase_def_ l cs ds np)
      == scase_def_ l (rem cs) (rem ds) (lift (REM _) np).
  Proof.
    induction l; intros.
    - now rewrite 2 scase_def__eq, 2 Foldi_nil, rem_zip.
    - rewrite 2 scase_def__eq, 2 Foldi_cons, <- 2 scase_def__eq.
      now rewrite rem_zip3, lift_hd, lift_tl, IHl.
  Qed.

  Lemma rem_scase_def :
    forall l cs dnp,
      rem (scase_def l cs dnp)
      == scase_def l (rem cs) (lift (REM _) dnp).
  Proof.
    intros.
    now rewrite (nprod_hd_tl dnp), scase_def_eq, rem_scase_def_,
      lift_cons, <- scase_def_eq.
  Qed.

  Lemma scase_def__cons :
    forall l c cs d ds np,
    forall (Hc : forall_nprod (@is_cons _) np),
      scase_def_ l (cons c cs) (cons d ds) np
      == cons (fold_right (fun '(j,x) => fcase j c x) (defcon2 c d)
                 (combine l (nprod_hds np Hc)))
           (scase_def_ l cs ds (lift (REM _) np)).
  Proof.
    intros.
    apply first_rem_eq.
    - rewrite first_cons, scase_def__eq, Foldi_fold_right.
      revert dependent np; clear.
      induction l; intros.
      + simpl. now rewrite first_zip, 2 first_cons, zip_cons, zip_bot1.
      + simpl.
        rewrite first_zip3, first_cons, (IHl _ (forall_nprod_tl _ _ Hc)).
        clear IHl.
        destruct (@is_cons_elim _ (nprod_hd np)) as (x &?& Heq).
        { now apply forall_nprod_hd in Hc. }
        remember (projT1 _) as y eqn:Hy.
        assert (x = y); subst.
        { destruct (uncons _) as (?&?& Hd); simpl.
          apply decomp_eqCon in Hd; rewrite Hd in Heq.
          now apply Con_eq_simpl in Heq. }
        rewrite Heq, first_cons, zip3_cons, zip3_bot1 at 1; auto.
    - now rewrite rem_scase_def_, 3 rem_cons.
  Qed.

  (** Caractérisation de [fcase] itéré sur la têtes des flots *)
  Section fcase_spec.

  Lemma fcase_abs :
    forall (l : list (enumtag * sampl A)) c a,
      l <> [] ->
      fold_right (fun '(j,x) => fcase j c x) a l = abs ->
      c = abs /\ a = abs /\ Forall (fun '(j, x) => x = abs) l.
  Proof.
    induction l as [|[][|l]]; simpl; intros c a Hnil Hf; try congruence.
    - unfold fcase at 1, is_tag, or_default, option_map in Hf.
      cases_eqn HH; subst; congruence.
    - unfold fcase at 1, is_tag, or_default, option_map in Hf.
      cases_eqn HH; subst; try congruence.
      edestruct IHl as (?&?&?); now eauto.
  Qed.

  (* en cours de calcul, ça vaut error_Ty si la bonne branche n'est *)
  (* pas encore atteinte *)
  Lemma fcase_pres_abs :
    forall (l : list (enumtag * sampl A)) i,
      let c := pres i in
      fold_right (fun '(j, x) => fcase j c x) (defcon c) l = err error_Ty ->
      Forall (fun '(j, x) => is_tag j c = pres false /\ exists v, x = pres v) l.
  Proof.
    induction l as [|[]]; simpl; intros i Hf; auto.
    unfold fcase in Hf at 1.
    unfold is_tag, or_default, option_map in *.
    cases_eqn HH; subst.
    take (Some _ = Some _) and inv it.
    take (err _ = err _) and inv it.
    constructor; eauto.
    eapply IHl, Forall_impl in HH1; eauto.
    intros []; cases; congruence.
  Qed.

  Lemma fcase_pres :
    forall (l : list (enumtag * sampl A)) c v,
      fold_right (fun '(j, x) => fcase j c x) (defcon c) l = pres v ->
      exists vc i,
        c = pres vc
        /\ tag_of_val vc = Some i
        /\ List.Exists (fun '(j, x) => j = i /\ x = pres v) l
        /\ List.Forall (fun '(j, x) => exists v, x = pres v) l.
  Proof.
    induction l as [|[i s]]; simpl; intros * Hf.
    { destruct c; simpl in Hf; congruence. }
    unfold fcase at 1 in Hf.
    unfold is_tag, or_default, option_map in Hf.
    cases_eqn HH; subst.
    all: repeat take (pres _ = pres _) and inv it.
    all: repeat take (Some _ = Some _) and inv it.
    all: try take (tag_eqb _ _ = true) and apply tag_eqb_eq in it; subst.
    - eapply IHl in HH1 as (?&?& Hinv & Hv &?&?); inv Hinv.
      rewrite Hv in *; take (Some _ = Some _) and inv it.
      do 2 esplit; repeat split; eauto.
    - apply fcase_pres_abs in HH1.
      do 2 esplit; repeat split; eauto.
      constructor; eauto.
      eapply Forall_impl; eauto; now intros [].
    - eapply IHl in HH1 as (?&?& Hinv &?&?&?); inv Hinv.
      do 2 esplit; repeat split; eauto.
  Qed.

  Lemma fcase_pres2 :
    forall (l : list (enumtag * sampl A)) c d v,
      l <> [] ->
      fold_right (fun '(j, x) => fcase j c x) (defcon2 c d) l = pres v ->
      exists vc vd i,
        c = pres vc
        /\ tag_of_val vc = Some i
        /\ d = pres vd
        /\ List.Forall (fun '(j, x) => exists v, x = pres v) l
        /\ (* cas 1 : i trouvé dans la liste *)
          (List.Exists (fun '(j, x) => j = i /\ x = pres v) l
           \/ (* cas 2 : on utilise la valeur par défaut *)
             (List.Forall (fun '(j, x) => j <> i) l /\ vd = v)).
  Proof.
    induction l as [|[i s1][|[j s2]]]; simpl; intros * Nnil Hf. congruence.
    - clear IHl.
      unfold fcase, is_tag, or_default, option_map in Hf.
      cases_eqn HH; subst; inv Hf; simpl in *; cases.
      all: repeat take (Some _ = Some _) and inv it.
      all: repeat take (pres _ = pres _) and inv it.
      + apply tag_eqb_eq in H0; subst; eauto 13.
      + apply tag_eqb_neq in H0; subst; eauto 13.
    - simpl in IHl.
      unfold fcase at 1, is_tag, or_default, option_map in Hf.
      cases_eqn HH; subst; try congruence; inv Hf.
      all: repeat take (Some _ = Some _) and inv it.
      + (* écrasé *)
        apply tag_eqb_eq in H0; subst.
        eapply IHl in HH1 as (?&?&?&?&?&?&?&?); subst; try congruence; eauto 13.
      + (* error_Ty, impossible *)
        clear - HH1; exfalso.
        unfold fcase at 1 in HH1.
        cases_eqn HH; subst; inv HH1.
        simpl in *; cases; clear HH.
        all: induction l; simpl in *; cases; try congruence.
        all: unfold fcase at 1, is_tag, or_default, option_map in HH2; cases.
      + (* plus tard *)
        apply tag_eqb_neq in H0.
        eapply IHl in HH1 as (?&?&?&?&?&?&?& FE); subst; try congruence.
        repeat take (pres _ = pres _) and inv it.
        destruct FE as [|[]]; subst; eauto 12.
        repeat esplit; eauto; right; split; auto.
        constructor; congruence.
  Qed.

  Lemma fcase_pres_ok :
    forall (l : list enumtag) (ss : list (sampl A)) vt i,
      tag_of_val vt = Some i ->
      Forall (fun x => match x with
                    | pres _ => True
                    | _ => False
                    end) ss ->
      length l = length ss ->
      In i l ->
      exists v, fold_right (fun '(j, x) => fcase j (pres vt) x) (err error_Ty) (combine l ss) = pres v.
  Proof.
    intros * Hv Hf Hl.
    enough ((In i l ->
             exists v, fold_right (fun '(j, x) => fcase  j (pres vt) x)
                    (err error_Ty) (combine l ss) = pres v)
            /\ ((exists v, fold_right (fun '(j, x) => fcase j (pres vt) x)
                       (err error_Ty) (combine l ss) = pres v)
               \/ (fold_right (fun '(j, x) => fcase j (pres vt) x)
                    (err error_Ty) (combine l ss) = err error_Ty))); [ tauto|].
    revert dependent ss.
    induction l as [|j l]; simpl; intros * Hf Hl.
    { split; eauto; tauto. }
    destruct ss as [|[] ss]; simpl in *; inv Hf; try lia.
    destruct (IHl ss) as [Hfin Hfnin]; auto.
    split.
    - unfold fcase at 1; simpl.
      rewrite Hv; simpl.
      intros [|Hin]; subst.
      + rewrite tag_eqb_refl.
        destruct Hfnin as [[]|]; cases; try congruence; eauto.
      + destruct Hfin as (?& ->); cases; eauto.
    - unfold fcase at 1 3, is_tag, or_default, option_map.
      destruct Hfnin as [[? ->]| ->]; cases_eqn HH; subst; eauto; congruence.
  Qed.

  Lemma fcase_def_pres_ok :
    forall (l : list enumtag) (ss : list (sampl A)) vt vd i,
      tag_of_val vt = Some i ->
      Forall (fun x => match x with
                    | pres _ => True
                    | _ => False
                    end) ss ->
      exists v, fold_right (fun '(j, x) => fcase j (pres vt) x) (pres vd) (combine l ss) = pres v.
  Proof.
    induction l; simpl; intros * Ht Hf; eauto.
    destruct ss as [|[] ss]; inv Hf; try tauto; simpl; eauto.
    unfold fcase at 1; simpl.
    rewrite Ht; simpl.
    edestruct IHl as (?& ->); cases; eauto.
  Qed.

  Lemma fcase_abs_ok :
    forall (l : list enumtag) (ss : list (sampl A)),
      Forall (eq abs) ss ->
      fold_right (fun '(j, x) => fcase j abs x) abs (combine l ss) = abs.
  Proof.
    induction l; intros * Heq; auto.
    destruct ss; auto.
    inversion_clear Heq; subst; simpl.
    rewrite IHl; auto.
  Qed.

  End fcase_spec.


  (** In this section we use the same function to denote the merge and
      case operators. Notably, we do not try to detect all errors (wrong clocks,
      error in sub-expressions, etc.).
      It gives a nice definition with functional environments but is is very
      unlikely to work well in proofs of SDtoRel.

      TODO question légitime : pourquoi on ne ferait pas comme ça ?
      c'est pénible pour les raisonnements plus tard (pas d'inversion possible)
      mais c'est plus simple à exprimer ici, et le résultat final devrait être
      le même : si bien cadencé, alors on a la sémantique relationnelle.
      Le fait que sbinop/swhen produise des erreurs parce qu'il n'y a pas le
      choix justifie-t-il la production d'erreurs dans le merge/case ?
      -> "pour faire pareil" n'est sans doute pas un bon argument
   *)
  Section Case_Noerr.

  (* a [case] operator for exactly one stream per tag *)
  Definition scase1_noerrf :
    (DS (sampl B) -C-> Dprodi (fun _ : enumtag => DS (sampl A)) -C-> DS (sampl A)) -C->
    (DS (sampl B) -C-> Dprodi (fun _ : enumtag => DS (sampl A)) -C-> DS (sampl A)).
    apply curry, curry.
    eapply (fcont_comp2 (DSCASE _ _)).
    2: exact (SND _ _ @_ FST _ _).
    apply ford_fcont_shift; intro b.
    apply curry.
    match goal with
    | |- _ (_ (Dprod ?pl ?pr) _) =>
        pose (f := (FST _ _ @_ FST _ _ @_ (FST pl pr)))
        ; pose (XB := SND pl pr)
        ; pose (ENV := SND _ _ @_ FST pl pr)
    end.
    refine match b with
    | abs => CONS abs @_ (f @3_ ID _) XB (DMAPi (fun _ => @REM (sampl A)) @_ ENV)
    | pres vb =>
        match tag_of_val vb with
        | None => CTE _ _ (DS_const (err error_Ty))
        | Some t => (APP _ @2_ PROJ _ t @_ ENV) ((f @3_ ID _) XB (DMAPi (fun _ => @REM (sampl A)) @_ ENV))
        end
    | err e => CTE _ _ (DS_const (err e))
      end.
  Defined.

  Lemma scase1_noerrf_eq : forall f c C (env : Dprodi (fun _ : enumtag => DS (sampl A))),
      scase1_noerrf f (cons c C) env
      = match c with
        | abs => cons abs (f C (DMAPi (fun _ => @REM (sampl A)) env))
        | pres b =>
            match tag_of_val b with
            | None => DS_const (err error_Ty)
            | Some t => app (env t) (f C (DMAPi (fun _ => @REM (sampl A)) env))
            end
        | err e => DS_const (err e)
        end.
  Proof.
    intros.
    unfold scase1_noerrf.
    autorewrite with localdb using (simpl (snd _); simpl (fst _)).
    destruct c; auto.
    destruct (tag_of_val a); auto.
  Qed.

  Definition scase1_noerr : DS (sampl B) -C-> Dprodi (fun _ : enumtag => DS (sampl A)) -C-> DS (sampl A) :=
    FIXP _ scase1_noerrf.

  Lemma scase1_noerr_eq : forall c C (env : Dprodi (fun _ : enumtag => DS (sampl A))),
      scase1_noerr (cons c C) env
      == match c with
        | abs => cons abs (scase1_noerr C (DMAPi (fun _ => @REM (sampl A)) env))
        | pres b =>
            match tag_of_val b with
            | None => DS_const (err error_Ty)
            | Some t => app (env t) (scase1_noerr C (DMAPi (fun _ => @REM (sampl A)) env))
            end
        | err e => DS_const (err e)
        end.
  Proof.
    intros.
    assert (Heq:=FIXP_eq scase1_noerrf).
    pose proof (ford_eq_elim (ford_eq_elim Heq (cons c C)) env) as HH.
    now rewrite <- scase1_noerrf_eq.
  Qed.

  (* now we lift it to exactly [n] streams per tag *)
  Definition scase_noerr {n} :
    DS (sampl B) -C-> Dprodi (fun _ => @nprod (DS (sampl A)) n)
                 -C-> @nprod (DS (sampl A)) n :=
    curry ((llift_env scase1_noerr @2_ FST _ _) (SND _ _)).

  End Case_Noerr.

  End When_Case.

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


(* reset sur les fonctions d'environnement *)
Section Sreset.

  Context {I A : Type}.
  Definition SI := fun _ : I => sampl A.

  Definition sresetf_aux :
    (* la fonctionnelle : *)
    ((DS_prod SI -C-> DS_prod SI) -C-> DS bool -C-> DS_prod SI -C-> DS_prod SI -C-> DS_prod SI) -C->
    (* les arguments *)
    (DS_prod SI -C-> DS_prod SI) -C-> DS bool -C-> DS_prod SI -C-> DS_prod SI -C-> DS_prod SI.

    do 4 apply curry.
    match goal with
    | |- _ (_ (Dprod ?pl ?pr) _) =>
        (* fonctionnelle *)
        pose (reset := FST _ _ @_ (FST _ _ @_ (FST _ _ @_ (FST pl pr))));
        (* fonction à réinitialiser *)
        pose (f := SND _ _ @_ (FST _ _ @_ (FST _ _ @_ (FST pl pr))));
        (* flot du reset, booléens *)
        pose (R := SND _ _ @_ (FST _ _ @_ (FST pl pr)));
        (* environnement des entrées (arguments de f) à faire progresser *)
        pose (X := SND _ _ @_ (FST pl pr));
        (* sorties déjà calculées, à faire progresser aussi *)
        pose (Y := SND pl pr);
        idtac
    end.

    (* on décrit l'environnement pour chaque variable *)
    apply Dprodi_DISTR; intro x.
    refine ((DSCASE bool _ @2_ _) R).
    apply ford_fcont_shift; intro r.

    (* on dégage (tl R) du contexte pour pouvoir utiliser nos alias : *)
    refine (curry (_ @_ FST _ _)).

    (* on teste la condition booléenne *)
    destruct r eqn:?.
    (* signal reçu *)
    exact (PROJ _ x @_ ((AP _ _ @5_ reset) f
             (CONS false @_ (REM _ @_ R))
             X ((AP _ _ @2_ f) X))).
    (* pas de reset *)
    exact ((APP _ @2_ PROJ _ x @_ Y)
             (PROJ _ x @_
                ((AP _ _ @5_ reset)
                   f (REM _ @_ R) (REM_env @_ X) (REM_env @_ Y)))).
  Defined.

  Lemma sresetf_aux_eq : forall F f r R X Y,
      sresetf_aux F f (cons r R) X Y ==
        if r
        then F f (cons false R) X (f X)
        else APP_env Y (F f R (REM_env X) (REM_env Y)).
  Proof.
    intros.
    apply Oprodi_eq_intro; intro i.
    unfold sresetf_aux.
    autorewrite with localdb.
    setoid_rewrite Dprodi_DISTR_simpl.
    setoid_rewrite DSCASE_simpl.
    setoid_rewrite DScase_cons.
    destruct r; cbn; now autorewrite with localdb.
  Qed.

  Lemma is_cons_sresetf_aux :
    forall F f R X Y x,
      is_cons (sresetf_aux F f R X Y x) ->
      is_cons R.
  Proof.
    unfold sresetf_aux.
    intros * Hc.
    now apply DScase_is_cons in Hc.
  Qed.

  Definition sreset_aux :
    (DS_prod SI -C-> DS_prod SI) -C-> DS bool -C-> DS_prod SI -C-> DS_prod SI -C-> DS_prod SI :=
    FIXP _ sresetf_aux.

  Lemma sreset_aux_eq : forall f r R X Y,
      sreset_aux f (cons r R) X Y ==
        if r
        then sreset_aux f (cons false R) X (f X)
        else APP_env Y (sreset_aux f R (REM_env X) (REM_env Y)).
  Proof.
    intros.
    assert (Heq:=FIXP_eq sresetf_aux).
    rewrite <- sresetf_aux_eq, <- Heq; auto.
  Qed.

  Lemma is_cons_sreset_aux :
    forall f R X Y x,
      is_cons (sreset_aux f R X Y x) ->
      is_cons R.
  Proof.
    unfold sreset_aux.
    intros * Hc.
    rewrite <- PROJ_simpl, FIXP_eq, PROJ_simpl in Hc.
    now apply DScase_is_cons in Hc.
  Qed.

  (* on n'échantillonne pas la condition de reset pour des questions
     de commodité dans les preuves *)
  Definition sreset :
    (DS_prod SI -C-> DS_prod SI) -C-> DS bool -C-> DS_prod SI -C-> DS_prod SI.
    apply curry, curry.
    match goal with
    | |- _ (_ (Dprod ?pl ?pr) _) =>
        pose (f := FST _ _ @_ (FST pl pr));
        pose (R := SND _ _ @_ (FST pl pr));
        pose (X := SND pl pr);
        idtac
    end.
    exact ((sreset_aux @4_ f) R X ((AP _ _ @2_ f) X)).
  Defined.

  Lemma sreset_eq : forall f R X,
      sreset f R X == sreset_aux f R X (f X).
  Proof.
    intros.
    unfold sreset.
    now autorewrite with localdb.
  Qed.

End Sreset.
