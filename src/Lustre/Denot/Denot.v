From Coq Require Import BinPos List.

From Velus Require Import Common Ident Operators Clocks CoindStreams.
From Velus Require Import Lustre.StaticEnv Lustre.LSyntax Lustre.LOrdered Lustre.LSemantics Lustre.LTyping.

From Cpo Require Import Cpo_def Cpo_streams_type Systems.

Close Scope equiv_scope. (* conflicting notation "==" *)
Import ListNotations.

Require Import Cpo_ext.
Require Import SDfuns.

Module Type LDENOT
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Senv  : STATICENV     Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
       (* (Import Typ   : LTYPING       Ids Op OpAux Cks Senv Syn) *)
       (Import Lord  : LORDERED      Ids Op OpAux Cks Senv Syn)
       (Import Str   : COINDSTREAMS  Ids Op OpAux Cks).


(* TODO: pour l'instant on se restreint aux cas suivants *)
Inductive restr_exp : exp -> Prop :=
| restr_Econst :
  forall c,
    restr_exp (Econst c)
| restr_Evar :
  forall x ann,
    restr_exp (Evar x ann)
| restr_Eunop :
  forall op e ann,
    restr_exp e ->
    restr_exp (Eunop op e ann)
| restr_Efby :
  forall e0s es anns,
    Forall restr_exp e0s ->
    Forall restr_exp es ->
    restr_exp (Efby e0s es anns)
(* | restr_Eapp : *)
(*   forall f es ers anns, *)
(*     Forall restr_exp es -> *)
(*     Forall restr_exp ers -> *)
(*     restr_exp (Eapp f es ers anns) *)
.

Section EXP.

(* Context {PSyn : block -> Prop}. *)
(* Context {prefs : PS.t}. *)
(* Parameter G : @global PSyn prefs. *)

Fixpoint nprod (n : nat) : cpo :=
  match n with
  | O => DS (sampl value) (* filled with error_Ty *)
  | 1 => DS (sampl value)
  | S n => Dprod (DS (sampl value)) (nprod n)
  end.

(* TODO: helper lemma ? *)
Definition nprod_app : forall n p, nprod n -C-> nprod p -C-> nprod (n + p).
  induction n as [|[]]; intro p.
  - exact (CURRY _ _ _ (SND _ _ )).
  - destruct p.
    + exact (CTE _ _).
    + exact (PAIR _ _).
  - apply curry.
    exact ((PAIR _ _ @2_ (FST _ _ @_ FST _ _))
             ((IHn p @2_ (SND _ _ @_ FST _ _)) (SND _ _))).
Defined.

Fixpoint lift (F : forall D, DS (sampl D) -C-> DS (sampl D)) n {struct n} : nprod n -C-> nprod n :=
  match n with
  | O => ID _
  | S n =>
      match n return nprod n -C-> nprod n -> nprod (S n) -C-> nprod (S n) with
      | O => fun _ => F _
      | S _ => fun fn => PROD_map (F _) fn
      end (lift F n)
  end.

Definition lift2
  (F : forall A : Type, DS (sampl A) -C-> DS (sampl A) -C-> DS (sampl A)) n :
  nprod n -C-> nprod n -C-> nprod n.
  induction n as [|[]].
  - exact 0. (* ? *)
  - exact (F _).
  - apply curry.
    apply (fcont_comp2 (PAIR _ _)).
    exact ((F _ @2_ (FST _ _ @_ FST _ _ )) (FST _ _ @_ SND _ _ )).
    exact ((IHn @2_ (SND _ _ @_ FST _ _ )) (SND _ _ @_ SND _ _ )).
Defined.

Lemma lift2_simpl :
  forall F n u U v V,
    lift2 F (S (S n)) (u, U) (v, V) = (F _ u v, lift2 F (S n) U V).
Proof.
  trivial.
Qed.

Fixpoint nprod_const (c : sampl value) n {struct n} : nprod n :=
  match n with
  | O => DS_const (err error_Ty)
  | S n =>
      match n return nprod n -> nprod (S n) with
      | O => fun _ => DS_const c
      | S m => fun np => (DS_const c, np)
      end (nprod_const c n)
  end.

(* Variable vars : list (ident * (type * clock)). *)

(* (* TODO: raffiner *) *)
(* Definition type_vars (x : ident) : Type := *)
(*   if existsb (ident_eqb x) (List.map fst vars) *)
(*   then sampl value *)
(*   else unit. *)

Definition SI := fun _ : ident => sampl value.
Definition denot_exp (e : exp) : DS_prod SI -C-> DS bool -C-> nprod (numstreams e).
  apply curry.
  revert e.
  fix denot_exp 1.
  intro e.
  destruct e eqn:He; simpl (nprod _).
  - (* Econst *)
    exact (sconst (Vscalar (sem_cconst c)) @_ SND _ _).
  - (* Eenum *)
    exact (CTE _ _ 0).
  - (* Evar *)
    exact (PROJ _ i @_ FST _ _).
  - (* Elast *)
    exact (CTE _ _ 0).
  - (* Eunop *)
    specialize (denot_exp e0) as fe.
    destruct (numstreams e0) as [|[]].
    (* pas le bon nombre de flots: *)
    1,3: exact (CTE _ _ (DS_const (err error_Ty))).
    destruct (typeof e0) as [|ty []].
    (* pas le bon nombre de flots: *)
    1,3: exact (CTE _ _ (DS_const (err error_Ty))).
    exact (sunop (fun v => sem_unop u v ty) @_ fe).
  - (* Ebinop *)
    exact (CTE _ _ 0).
  - (* Efby *)
    rename l into e0s.
    rename l0 into es.
    rename l1 into anns.
    clear He.
    (* vérifier le typage *)
    destruct (Nat.eq_dec
                (list_sum (List.map numstreams e0s))
                (list_sum (List.map numstreams es))) as [Heq|].
    destruct (Nat.eq_dec
                (length anns)
                (list_sum (List.map numstreams es))
             ) as [->|].
    (* si les tailles ne correspondent pas : *)
    2,3: exact (CTE _ _ (nprod_const (err error_Ty) _)).
    (* calculer les flots de e0s *)
    assert (Dprod (DS_prod SI) (DS bool) -C-> nprod (list_sum (List.map numstreams e0s))) as s0s.
    { clear Heq. induction e0s as [|a]; simpl (list_sum _).
      + exact (CTE _ _ (DS_const (err error_Ty))).
      + exact ((nprod_app _ _ @2_ (denot_exp a)) IHe0s). }
    (* calculer les flots de es *)
    assert (Dprod (DS_prod SI) (DS bool) -C-> nprod (list_sum (List.map numstreams es))) as ss.
    { clear Heq. induction es as [|a]; simpl (list_sum _).
      + exact (CTE _ _ (DS_const (err error_Ty))).
      + exact ((nprod_app _ _ @2_ (denot_exp a)) IHes). }
    rewrite Heq in s0s.
    exact ((lift2 (@SDfuns.fby) _ @2_ s0s) ss).
  - (* Earrow *)
    exact (CTE _ _ 0).
  - (* Ewhen *)
    exact (CTE _ _ 0).
  - (* Emerge *)
    exact (CTE _ _ 0).
  - (* Ecase *)
    exact (CTE _ _ 0).
  - (* Eapp *)
    exact (CTE _ _ 0).
Defined.

Ltac forward_apply A :=
  match type of A with
  | ?B -> ?C =>
      assert C; [ apply A |]
  end.

Definition denot_exps (es : list exp) :
  DS_prod SI -C-> DS bool -C-> nprod (list_sum (List.map numstreams es)).
  apply curry.
  induction es as [|a]; simpl (list_sum _).
  + exact (CTE _ _ (DS_const (err error_Ty))).
  + exact ((nprod_app _ _ @2_ uncurry (denot_exp a)) IHes).
Defined.

Lemma denot_exps_eq :
  forall e es env bs,
    denot_exps (e :: es) env bs
    == nprod_app _ _ (denot_exp e env bs) (denot_exps es env bs).
Proof.
  trivial.
Qed.

Definition nprod_add : forall n m : nat, nprod n -> nprod m -> nprod n :=
  fun n m =>
    match Nat.eq_dec n m with
    | left a =>
        eq_rect_r (fun n0 : nat => nprod n0 -> nprod m -> nprod n0)
          (fun mm => lift2 (@fby) m mm ) a
    | right b => fun (_ : nprod n) (_ : nprod m) => nprod_const abs n
    end.

Lemma denot_exp_eq :
  forall e env bs,
    denot_exp e env bs =
      match e return nprod (numstreams e) with
      | Econst c => sconst (Vscalar (sem_cconst c)) bs
      | Evar x _ => env x
      | Eunop op e an =>
          let se := denot_exp e env bs in
          match numstreams e as n return nprod n -> nprod 1 with
          | 1 => fun se =>
              match typeof e with
              | [ty] => sunop (fun v => sem_unop op v ty) se
              | _ => DS_const (err error_Ty)
              end
          | _ => fun _ => DS_const (err error_Ty)
          end se
      (* | Ebinop _ _ _ op e1 e2 => *)
      (*     binop (denot_lbinop op) (denot_exp e1 genv env bs) (denot_exp e2 genv env bs) *)
      | Efby e0s es an =>
          let s0s := denot_exps e0s env bs in
          let ss := denot_exps es env bs in
          let n := (list_sum (List.map numstreams e0s)) in
          let m := (list_sum (List.map numstreams es)) in
          match Nat.eq_dec n m, Nat.eq_dec (length an) n with
          | left eqm, left eqan =>
              eq_rect_r nprod (lift2 (@SDfuns.fby) _ s0s (eq_rect_r nprod ss eqm)) eqan
          | _, _ => nprod_const (err error_Ty) _
          end
      (* | Earrow _ e0 e => *)
      (*     lift2 s (@arrow) _ (denot_exp e0 genv env bs) (denot_exp e genv env bs) *)
      (* | Epair _ _ e1 e2 => *)
      (*     PAIR_flat s _ _ (denot_exp e1 genv env bs) (denot_exp e2 genv env bs) *)
      (* | Ewhen _ x vd e => *)
      (*     llift s _ (@when) _ (denot_var s thisd x vd env) (denot_exp e genv env bs) *)
      (* | Emerge _ x vd eT eF => *)
      (*     llift2 s _ (@merge) _ (denot_var s thisd x vd env) *)
      (*       (denot_exp eT genv env bs) (denot_exp eF genv env bs) *)
      (* | Eite _ e eT eF => *)
      (*     llift2 s _ (@ite) _ (denot_exp e genv env bs) *)
      (*       (denot_exp eT genv env bs) (denot_exp eF genv env bs) *)
      (* | Eapp _ _ f fd e => denot_app s gd f fd genv (denot_exp e genv env bs) *)
      (* | Ereset _ _ f fd e er => *)
      (*     reset (denot_app s gd f fd genv) *)
                          (*       (denot_exp er genv env bs) (denot_exp e genv env bs) *)
      | _ => 0
      end.
(* Proof. *)
(*   destruct e; auto. *)
(*   - intros. *)
(*     rewrite unfolding_lemma. *)
(*     cbn. *)
(*     simpl. *)
(*     unfold denot_exp at 1. *)
(*     fold (denot_exp e). *)

(*     generalize (denot_exp e env0 bs) as ss. *)
(*     destruct (numstreams e) as [|[]]; auto. *)
(*     unfold denot_exp; simpl. *)
(*     autorewrite with cpodb using (simpl (snd _); simpl (fst _)). *)
(*     cbn. *)
(*     destruct (numstreams e). *)
  (* Qed. *)
  Admitted.

(* obtenir le premier élément *)
Definition nprod_fst {n} : nprod n -C-> DS (sampl value) :=
  match n with
  | O => CTE _ _ (DS_const (err error_Ty))
  | 1 => ID _
  | (S n) => FST _ _
  end.

(* jeter le premier élément *)
Definition nprod_skip {n} : nprod (S n) -C-> nprod n :=
  match n with
  | O => CTE _ _ (DS_const (err error_Ty))
  | (S n) => SND _ _
  end.

Definition denot_equation (e : equation) : DS_prod SI -C-> DS bool -C-> DS_prod SI.
  destruct e as (xs,es).
  (* vérification des tailles *)
  destruct (Nat.eq_dec
              (length xs)
              (list_sum (List.map numstreams es))
           ) as [Heq|].
  2:{ apply curry, Dprodi_DISTR.
      exact (fun _ => CTE _ _ (DS_const (err error_Ty))). }
  pose proof (ss := Uncurry _ _ _ (denot_exps es)).
  apply curry, Dprodi_DISTR.
  intro x.
  revert Heq ss.
  generalize (list_sum (List.map numstreams es)) as n; intros.
  eapply fcont_comp2.
  2: exact (FST _ _).
  2: exact ss.
  clear ss.
  apply curry.
  revert dependent n.
  induction xs as [| y xs]; intros.
  - exact (PROJ _ x @_ FST _ _).
  - destruct (ident_eq_dec x y).
    + exact (nprod_fst @_ SND _ _).
    + eapply fcont_comp.
      * exact (IHxs (length xs) eq_refl).
      * inv Heq.
        exact (PROD_map (ID _) nprod_skip).
Defined.


Section Equation_spec.

(* retourne l'indice de l'élément dans la liste *)
Fixpoint mem_nth (l : list ident) (x : ident) : option nat :=
  match l with
  | [] => None
  | y :: l =>
      if ident_eq_dec x y then Some O
      else option_map S (mem_nth l x)
  end.

(* (* donne le p-ème flot de np ou DS_const (err error_Ty)  *) *)
Fixpoint get_nth {n} (np : nprod n) (p : nat) {struct p} : DS (sampl value) :=
  match p with
  | O => nprod_fst np
  | S p => match n return nprod n -> _ with
          | O => fun _ => DS_const (err error_Ty)
          | S _ => fun np => get_nth (nprod_skip np) p
          end np
  end.

(* TODO: move *)
Lemma Dprodi_DISTR_simpl :
  forall (I:Type) (Di:I->cpo) (D:cpo) (f: Dprodi (fun i => D -C-> Di i)) (d : D) (i : I),
    Dprodi_DISTR I Di D f d i == f i d.
Proof.
  trivial.
Qed.
(* Global *) Hint Rewrite Dprodi_DISTR_simpl : cpodb.
(* TODO: move *)
Hint Rewrite PROD_map_simpl ID_simpl Id_simpl : cpodb.

Lemma denot_equation_eq :
  forall xs es env bs x,
    denot_equation (xs,es) env bs x
    == if Nat.eq_dec (length xs) (list_sum (List.map numstreams es))
       then
         let ss := denot_exps es env bs in
         match mem_nth xs x with
         | None => env x
         | Some n => get_nth ss n
         end
       else DS_const (err error_Ty).
Proof.
  intros.
  unfold denot_equation.
  destruct (Nat.eq_dec (length xs) (list_sum (List.map numstreams es))) as [Heq|]; auto.
  autorewrite with cpodb using (simpl (snd _); simpl (fst _)).
  (* TODO: pourquoi ça ne fonctionne pas mieux que ça ?  : *)
  rewrite (Dprodi_DISTR_simpl _ (DS_fam SI)).
  autorewrite with cpodb using (simpl (snd _); simpl (fst _)).
  generalize (denot_exps es env0 bs).
  revert Heq.
  generalize (list_sum (List.map numstreams es)).
  induction xs; intros; simpl; auto.
  destruct (ident_eq_dec x a); auto.
  destruct Heq; simpl.
  autorewrite with cpodb using (simpl (snd _); simpl (fst _)).
  rewrite IHxs.
  destruct (mem_nth xs x); auto.
Qed.

End Equation_spec.

(* (* 1ère version : construction directe de l'environnement en parcourant *)
(*  l'équation *) *)
(*     Definition denot_equation' (e : equation) : *)
(*       DS_prod type_vars -C-> DS bool -C-> DS_prod type_vars. *)
(*       destruct e as (xs,es). *)
(*       (* vérification des tailles *) *)
(*       destruct (Nat.eq_dec *)
(*                   (length xs) *)
(*                   (list_sum (List.map numstreams es)) *)
(*                ) as [Heq|]. *)
(*       (* 2: exact (CTE _ _ 0). (* TODO : error_Ty *) *) *)
(*       2:{ (* TODO: plus joli *) *)
(*         apply curry, Dprodi_DISTR. *)
(*         intro. apply CTE. unfold type_vars. simpl. *)
(*         cases. exact (DS_const (err error_Ty)). exact (DS_const tt). } *)
(*       (* calcul des expressions *) *)
(*       apply curry. *)
(*       assert (Dprod (DS_prod type_vars) (DS bool) -C-> nprod (list_sum (List.map numstreams es))) as ss. *)
(*       { clear Heq. induction es as [|a]; simpl (list_sum _). *)
(*         + exact (CTE _ _ (DS_const tt)). *)
(*         + exact ((nprod_app _ _ @2_ (uncurry (denot_exp a))) IHes). } *)
(*       (* on construit le produit variable par variable *) *)
(*       apply Dprodi_DISTR. *)
(*       intro x. *)
(*       destruct (existsb (ident_eqb x) (List.map fst vars)) eqn:Hx. *)
(*       2:{ unfold DS_fam, type_vars at 2. *)
(*           rewrite Hx. *)
(*           exact (CTE _ _ (DS_const tt)). (* TODO: plutôt error_Ty ? *) *)
(*       } *)
(*       (* si la variable apparaît dans xs on prend la valeur calculée, *)
(*          sinon celle de l'environment *) *)
(*       remember (list_sum (List.map numstreams es)) as n eqn:Hn. clear Hn. *)
(*       revert dependent n. *)
(*       induction xs as [| y xs]; intros. *)
(*       - exact (PROJ _ x @_ FST _ _). *)
(*       - destruct n. inversion Heq. *)
(*         destruct (ident_eqb x y). *)
(*         + (* on prend l'expression *) *)
(*           unfold DS_fam, type_vars at 2. rewrite Hx. *)
(*           eapply fcont_comp. 2: apply ss. *)
(*           destruct n. *)
(*           * exact (ID _). *)
(*           * exact (FST _ _). *)
(*         + (* on passe à la suite *) *)
(*           inversion Heq; subst. *)
(*           eapply IHxs; eauto. *)
(*           eapply fcont_comp. 2: apply ss. *)
(*           destruct (length xs). *)
(*           * exact (CTE _ _ (DS_const tt)). *)
(*           * exact (SND _ _). *)
(*     Defined. *)

End EXP.


(** ** Infinity of streams obtained by denot_equation  *)

(** Definition and specification of [nrem] : [n] applications of [rem].
    It is useful to show the productivity of stream functions.
    A function [f] of a stream [xs] is producive/length-preserving if
    for all n, [is_cons (nrem n xs)] implies [is_cons (n_rem n (f xs))].
 *)
Section Nrem.

  Context {A : Type}.

  Fixpoint nrem (n : nat) (xs : DS A) : DS A :=
    match n with
    | O => xs
    | S n => nrem n (rem xs)
    end.

  Lemma nrem_inf :
    forall (s : DS A), (forall n, is_cons (nrem n s)) -> infinite s.
  Proof.
    cofix Cof; intros * Hc.
    constructor.
    - apply (Hc O).
    - apply Cof.
      intro n.
      apply (Hc (S n)).
  Qed.

  Lemma is_consn_DS_const :
    forall (c : A) n,
      is_cons (nrem n (DS_const c)).
  Proof.
    induction n; simpl; rewrite DS_const_eq, ?rem_cons; auto.
  Qed.

  Lemma nrem_rem :
    forall (s : DS A) n,
      nrem n (rem s) == rem (nrem n s).
  Proof.
    intros.
    revert s.
    induction n; simpl; auto.
  Qed.

  Lemma is_consn_S :
    forall (s : DS A) n,
      is_cons (nrem (S n) s) -> is_cons (nrem n s).
  Proof.
    induction n; simpl; auto.
    rewrite nrem_rem.
    auto using is_cons_rem.
  Qed.

  Lemma is_consn_is_cons :
    forall (s : DS A) n,
      is_cons (nrem n s) -> is_cons s.
  Proof.
    induction n; simpl; auto.
    rewrite nrem_rem.
    auto using is_cons_rem.
  Qed.

  Lemma nrem_eq_compat : forall n (s t:DS A), s==t -> nrem n s == nrem n t.
  Proof.
    induction n; simpl; auto.
  Qed.

  Global Add Parametric Morphism n : (nrem n)
      with signature (@Oeq (DS A)) ==> (@Oeq (DS A)) as nrem_eq_compat_morph.
  Proof.
    exact (@nrem_eq_compat n).
  Qed.

End Nrem.

Lemma nrem_map :
  forall {A B} (f : A -> B) n xs,
    nrem n (map f xs) == map f (nrem n xs).
Proof.
  induction n; simpl; intros; auto.
  rewrite rem_map; auto.
Qed.

Module Alt_inf.
  (** example of usage *)
  Definition alt : DS bool := FIXP _ (CONS true @_ MAP negb).
  Lemma alt_inf : infinite alt.
  Proof.
    apply nrem_inf.
    induction n; simpl.
    - unfold alt.
      rewrite FIXP_eq.
      autorewrite with cpodb; auto.
    - unfold alt in *.
      rewrite FIXP_eq.
      autorewrite with cpodb.
      rewrite nrem_map; auto.
  Qed.
End Alt_inf.


(** ** Productivity of stream operators *)
Section Ncons_ops.

Context {A : Type}.

Ltac solve_err :=
  try match goal with
    | |- context [ DS_const _ ] =>
        repeat rewrite DS_const_eq, rem_cons;
        now auto using is_cons_DS_const, is_consn_DS_const
    end.

Lemma is_consn_S_fby1 :
  forall n v (xs ys : DS (sampl A)),
    is_cons (nrem (S n) xs) ->
    is_cons (nrem n ys) ->
    is_cons (nrem (S n) (fby1 v xs ys)).
Proof.
  induction n; simpl; intros * Hx Hy.
  - apply is_cons_rem in Hx as (?&?&?&->).
    apply is_cons_elim in Hy as (?&?&->).
    rewrite fby1_eq.
    cases; solve_err; rewrite fby1AP_eq.
    all: cases; solve_err; rewrite fby1_eq.
    all: cases; solve_err; autorewrite with cpodb; auto.
  - apply is_consn_is_cons in Hx as Hc.
    apply is_cons_rem in Hc as (x2 & x3 & xs' & Hc).
    apply rem_eq_cons in Hc as (x1 & Hc).
    apply is_consn_is_cons in Hy as Hd.
    apply is_cons_rem in Hd as (y1 & y2 & ys' & Hd).
    rewrite Hc, Hd, fby1_eq, 2 rem_cons in *.
    cases; solve_err; rewrite fby1AP_eq; autorewrite with cpodb.
    all: cases; solve_err.
    all: apply IHn; simpl; autorewrite with cpodb; auto using is_consn_S.
Qed.

Lemma is_consn_S_fby :
  forall n (xs ys : DS (sampl A)),
    is_cons (nrem (S n) xs) ->
    is_cons (nrem n ys) ->
    is_cons (nrem (S n) (fby xs ys)).
Proof.
  induction n; simpl; intros * Hx Hy.
  - apply is_cons_rem in Hx as (?&?&?&->).
    apply is_cons_elim in Hy as (?&?&->).
    rewrite fby_eq.
    cases; solve_err; rewrite ?fbyA_eq, ?fby1AP_eq.
    all: cases; solve_err; rewrite ?fby_eq, ?fby1_eq.
    all: cases; solve_err; autorewrite with cpodb; auto.
  - apply is_consn_is_cons in Hx as Hc.
    apply is_cons_rem in Hc as (x2 & x3 & xs' & Hc).
    apply rem_eq_cons in Hc as (x1 & Hc).
    apply is_consn_is_cons in Hy as Hd.
    apply is_cons_rem in Hd as (y1 & y2 & ys' & Hd).
    rewrite Hc, Hd, fby_eq, 2 rem_cons in *.
    cases; solve_err; rewrite ?fbyA_eq, ?fby1AP_eq.
    all: autorewrite with cpodb; cases; solve_err.
    + apply IHn; simpl; autorewrite with cpodb; auto using is_consn_S.
    + apply is_consn_S_fby1; simpl; now autorewrite with cpodb.
Qed.

Lemma is_consn_sunop :
  forall {A B} (f : A -> option B) s n,
    is_cons (nrem n s) ->
    is_cons (nrem n (sunop f s)).
Proof.
  intros.
  unfold sunop.
  rewrite MAP_map, nrem_map.
  now apply is_cons_map.
Qed.

Lemma is_consn_sconst :
  forall {A} (c : A) bs n,
    is_cons (nrem n bs) ->
    is_cons (nrem n (sconst c bs)).
Proof.
  intros.
  unfold sconst.
  rewrite MAP_map, nrem_map.
  now apply is_cons_map.
Qed.

End Ncons_ops.


End LDENOT.

Module LDenotFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS        Ids Op OpAux)
       (Senv  : STATICENV     Ids Op OpAux Cks)
       (Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
       (Lord  : LORDERED      Ids Op OpAux Cks Senv Syn)
       (Str   : COINDSTREAMS  Ids Op OpAux Cks)
<: LDENOT Ids Op OpAux Cks Senv Syn Lord Str.
  Include LDENOT Ids Op OpAux Cks Senv Syn Lord Str.
End LDenotFun.
