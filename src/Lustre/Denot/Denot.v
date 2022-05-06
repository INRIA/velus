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

Definition SI := fun _ : ident => sampl value.

Definition denot_exp (e : exp) : DS_prod SI -C-> DS bool -C-> nprod (numstreams e).
  revert e.
  fix denot_exp 1.
  intro e.
  destruct e eqn:He; simpl (nprod _).
  - (* Econst *)
    exact (CTE _ _ (sconst (Vscalar (sem_cconst c)))).
  - (* Eenum *)
    exact (CTE _ _ 0).
  - (* Evar *)
    exact (CTE _ _ @_ PROJ (DS_fam SI) i).
  - (* Elast *)
    exact (CTE _ _ 0).
  - (* Eunop *)
    apply curry.
    eapply fcont_comp. 2: apply (uncurry (denot_exp e0)).
    destruct (numstreams e0) as [|[]].
    (* pas le bon nombre de flots: *)
    1,3: apply CTE, (DS_const (err error_Ty)).
    destruct (typeof e0) as [|ty []].
    (* pas le bon nombre de flots: *)
    1,3: apply CTE, (DS_const (err error_Ty)).
    exact (sunop (fun v => sem_unop u v ty)).
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
                (list_sum (List.map numstreams e0s))
             ) as [->|].
    (* si les tailles ne correspondent pas : *)
    2,3: apply CTE, CTE, (nprod_const (err error_Ty) _).
    (* calculer les flots de e0s *)
    assert (DS_prod SI -C-> DS bool -C-> nprod (list_sum (List.map numstreams e0s))) as s0s.
    { clear Heq.
      apply curry.
      induction e0s as [|a]; simpl (list_sum _).
      + exact (CTE _ _ (DS_const (err error_Ty))).
      + exact ((nprod_app _ _ @2_ uncurry (denot_exp a)) IHe0s). }
    (* calculer les flots de es *)
    assert (DS_prod SI -C-> DS bool -C-> nprod (list_sum (List.map numstreams es))) as ss.
    { clear Heq.
      apply curry.
      induction es as [|a]; simpl (list_sum _).
      + exact (CTE _ _ (DS_const (err error_Ty))).
      + exact ((nprod_app _ _ @2_ uncurry (denot_exp a)) IHes). }
    rewrite <- Heq in ss.
    exact (curry ((lift2 (@SDfuns.fby) _ @2_ uncurry s0s) (uncurry ss))).
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
Proof.
  destruct e; auto; intros env bs.
  - (* Eunop *)
    unfold denot_exp at 1.
    fold (denot_exp e).
    autorewrite with cpodb using (simpl (fst _); simpl (snd _)).
    generalize (denot_exp e env bs) as ss.
    generalize (numstreams e) as ne.
    destruct ne as [|[]]; intros; auto.
    destruct (typeof e) as [|? []]; auto.
  - (* Efby*)
    rename l into e0s.
    rename l0 into es.
    rename l1 into a.
    unfold denot_exp at 1.
    destruct
      (Nat.eq_dec (list_sum (List.map numstreams e0s)) (list_sum (List.map numstreams es))) as [E1|],
      (Nat.eq_dec (length a) (list_sum (List.map numstreams e0s))) as [E2|]; auto.
    (* FIXME: (denot_exps e0s) et (denot_exps es) apparaissent sous forme déroulée
       à gauche de l'égalité car [denot_exps] n'existait pas encore lors de la définition
       de [denot_exp]. Coq n'arrive pas à les enrouler avec [fold (denot_exps e0s)] et
       [fold (denot_exps es)]. On doit l'aider avec la tactique suivante.
     *)
    do 2 match goal with
     | |- context [ curry (list_rect ?A ?B ?C ?D) ] =>
         change (curry (list_rect A B C D)) with (denot_exps D);
         generalize (denot_exps D); intro (* pour pouvoir détruire E1 et E2 *)
      end.
    now destruct E1, E2.
Qed.


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
  intros ?? env ??.
  unfold denot_equation.
  destruct (Nat.eq_dec (length xs) (list_sum (List.map numstreams es))) as [Heq|]; auto.
  (* FIXME: pourquoi faut-il ajouter ça ? *)
  Local Hint Rewrite (Dprodi_DISTR_simpl _ (DS_fam SI)) : cpodb.
  autorewrite with cpodb using (simpl (snd _); simpl (fst _)).
  generalize (denot_exps es env bs).
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
