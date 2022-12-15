From Coq Require Import BinPos List.

From Velus Require Import Common Ident Operators Clocks CoindStreams.
From Velus Require Import Lustre.StaticEnv Lustre.LSyntax Lustre.LSemantics Lustre.LOrdered.

From Velus Require Import Lustre.Denot.Cpo.

Close Scope equiv_scope. (* conflicting notation "==" *)
Import ListNotations.

Require Import Cpo_ext CommonList2.
Require Import SDfuns.

Module Type LDENOT
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Senv  : STATICENV     Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
       (Import Lord  : LORDERED      Ids Op OpAux Cks Senv Syn).

(* TODO: faire ça partout !! *)
Context {PSyn : block -> Prop}.
Context {Prefs : PS.t}.
Definition node := @node PSyn Prefs.
Definition global := @global PSyn Prefs.

(** We always use this specialized version of mem_nth *)
(* TODO: c'est vraiment une bonne idée de redéfinir des trucs, comme ça ? *)
Definition mem_nth := mem_nth ident ident_eq_dec.

Definition errTy : DS (sampl value) := DS_const (err error_Ty).

(** ** Denotational environments (local & program-wide) *)
Section Denot_env.

Definition SI := fun _ : ident => sampl value.
Definition FI := fun _ : ident => (DS_prod SI -C-> DS_prod SI).

(** build and environment from a tuple of streams, with names given in [l] *)
Definition env_of_ss (l : list ident) {n} : nprod n -C-> DS_prod SI :=
  Dprodi_DISTR _ _ _
    (fun x => match mem_nth l x with
           | Some n => get_nth n errTy
           | None => CTE _ _ errTy
           end).

(** extract a typle from an environment  *)
Definition ss_of_env (l : list ident) : DS_prod SI -C-> @nprod (DS (sampl value)) (length l).
  induction l as [| x []].
  - apply CTE, errTy.
  - apply (PROJ _ x).
  - apply ((PAIR _ _ @2_ PROJ _ x) IHl).
Defined.

Lemma env_of_ss_nth :
  forall l n (np : nprod n) k x,
    mem_nth l x = Some k ->
    env_of_ss l np x = get_nth k errTy np.
Proof.
  unfold env_of_ss.
  intros.
  setoid_rewrite Dprodi_DISTR_simpl.
  cases. now inv H. congruence.
Qed.

Lemma nth_ss_of_env :
  forall d d' l env k,
    k < length l ->
    get_nth k d' (ss_of_env l env) = env (nth k l d).
Proof.
  induction l as [|? []]; intros * Hl.
  - inv Hl.
  - destruct k; auto. simpl in *; lia.
  - destruct k; simpl; auto.
    setoid_rewrite IHl; now auto with arith.
Qed.

Lemma forall_env_of_ss :
  forall (P : DS (sampl value) -> Prop) l {n} (ss : nprod n),
    P errTy ->
    forall_nprod P ss ->
    forall x, P (env_of_ss l ss x).
Proof.
  intros.
  unfold env_of_ss.
  cbn; cases.
  destruct (Nat.lt_ge_cases n0 n).
  - apply forall_nprod_k; auto.
  - rewrite get_nth_err; auto.
Qed.


Lemma forall_ss_of_env :
  forall (P : DS (sampl value) -> Prop) l env,
    (forall x, P (env x)) ->
    forall_nprod P (ss_of_env l env).
Proof.
  induction l as [|? []]; intros * Hp; eauto.
  - now simpl.
  - apply Hp.
  - constructor.
    + apply Hp.
    + apply IHl, Hp.
Qed.

(* version plus forte mais moins pratique à utiliser *)
Lemma forall_ss_of_env' :
  forall (P : DS (sampl value) -> Prop) l env,
    (forall x, In x l -> P (env x)) ->
    forall_nprod P (ss_of_env l env).
Proof.
  induction l as [|? []]; intros * Hp; eauto.
  - now simpl.
  - apply Hp; now constructor.
  - constructor.
    + apply Hp. now constructor.
    + apply IHl. clear - Hp. firstorder.
Qed.

End Denot_env.


Section Denot_node.

Variable (G : global).


(* l'opérateur swhen spécialisé aux Velus.Op.value *)
Definition swhenv :=
  let get_tag := fun v => match v with Venum t => Some t | _ => None end in
  @swhen value value enumtag get_tag Nat.eqb.

Definition denot_exp_ (ins : list ident)
  (e : exp) :
  (* (nodes * inputs * base clock * env) -> streams *)
  Dprod (Dprod (Dprod (Dprodi FI) (DS_prod SI)) (DS bool)) (DS_prod SI) -C-> @nprod (DS (sampl value)) (numstreams e).
  set (ctx := Dprod _ _).
  epose (denot_var :=
       fun x => if mem_ident x ins
             then PROJ (DS_fam SI) x @_ SND _ _ @_ FST _ _ @_ FST _ _
             else PROJ (DS_fam SI) x @_ SND _ _).
  revert e.
  fix denot_exp 1.
  intro e.
  destruct e eqn:He; simpl (nprod _).
  - (* Econst *)
    apply (sconst (Vscalar (sem_cconst c)) @_ SND _ _ @_ FST _ _).
  - (* Eenum *)
    apply CTE, errTy.
  - (* Evar *)
    exact (denot_var i).
  - (* Elast *)
    apply CTE, errTy.
  - (* Eunop *)
    eapply fcont_comp. 2: apply (denot_exp e0).
    destruct (numstreams e0) as [|[]].
    (* pas le bon nombre de flots: *)
    1,3: apply CTE, errTy.
    destruct (typeof e0) as [|ty []].
    (* pas le bon nombre de flots: *)
    1,3: apply CTE, errTy.
    exact (sunop (fun v => sem_unop u v ty)).
  - (* Ebinop *)
    apply CTE, errTy.
  - (* Eextcall *)
    apply CTE, errTy.
  - (* Efby *)
    rename l into e0s, l0 into es, l1 into anns.
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
    2,3: apply CTE, (nprod_const errTy).
    (* calculer les flots de e0s *)
    eassert (ctx -C-> nprod (list_sum (List.map numstreams e0s))) as s0s.
    { clear Heq.
      induction e0s as [|a].
      + exact (CTE _ _ errTy).
      + exact ((nprod_app @2_ (denot_exp a)) IHe0s). }
    (* calculer les flots de e0s *)
    eassert (ctx -C-> nprod (list_sum (List.map numstreams es))) as ss.
    { clear Heq.
      induction es as [|a].
      + exact (CTE _ _ errTy).
      + exact ((nprod_app @2_ (denot_exp a)) IHes). }
    (* calculer les flots de es *)
    rewrite <- Heq in ss.
    exact ((lift2 (SDfuns.fby) @2_ s0s) ss).
  - (* Earrow *)
    apply CTE, (nprod_const errTy).
  - (* Ewhen *)
    rename l into es.
    destruct l0 as (tys,ck).
    destruct p as (i,ty). clear He.
    destruct (Nat.eq_dec
                (length tys)
                (list_sum (List.map numstreams es))
             ) as [->|].
    2: apply CTE, (nprod_const errTy).
    eassert (ctx -C-> nprod (list_sum (List.map numstreams es))) as ss.
    { induction es as [|a].
      + exact (CTE _ _ errTy).
      + exact ((nprod_app @2_ (denot_exp a)) IHes). }
    exact ((llift (swhenv e0) @2_ ss) (denot_var i)).
  - (* Emerge *)
    apply CTE, (nprod_const errTy).
  - (* Ecase *)
    apply CTE, (nprod_const errTy).
  - (* Eapp *)
    rename l into es, l0 into er, l1 into anns.
    clear He.
    destruct (find_node i G) as [n|].
    destruct (Nat.eq_dec (length anns) (length (idents n.(n_out)))) as [->|].
    2,3: apply CTE, (nprod_const errTy).
    (* dénotation du nœud *)
    pose (f := PROJ _ i @_ FST _ _ @_ FST _ _ @_ FST _ _ : ctx -C-> FI i).
    (* calcul des es *)
    eassert (ctx -C-> nprod (list_sum (List.map numstreams es))) as ss.
    { induction es as [|a].
      + exact (CTE _ _ errTy).
      + exact ((nprod_app @2_ (denot_exp a)) IHes). }
    (* chaînage *)
    exact ((ss_of_env (idents (n_out n))
              @_ (f @2_ ID ctx) (env_of_ss (idents (n_in n)) @_ ss))).
Defined.

Definition denot_exp (ins : list ident) (e : exp) :
  (* (nodes * inputs * base clock * env) -> streams *)
  Dprodi FI -C-> DS_prod SI -C-> DS bool -C-> DS_prod SI -C-> nprod (numstreams e) :=
  curry (curry (curry (denot_exp_ ins e))).

Definition denot_exps_ (ins : list ident) (es : list exp) :
  Dprod (Dprod (Dprod (Dprodi FI) (DS_prod SI)) (DS bool)) (DS_prod SI) -C->
  @nprod (DS (sampl value)) (list_sum (List.map numstreams es)).
  induction es as [|a].
  + exact (CTE _ _ errTy).
  + exact ((nprod_app @2_ (denot_exp_ ins a)) IHes).
Defined.

Definition denot_exps (ins : list ident) (es : list exp) :
  Dprodi FI -C-> DS_prod SI -C-> DS bool -C-> DS_prod SI -C-> nprod (list_sum (List.map numstreams es)) :=
  curry (curry (curry (denot_exps_ ins es))).

Lemma denot_exps_eq :
  forall ins e es envG envI bs env,
    denot_exps ins (e :: es) envG envI bs env
    = nprod_app (denot_exp ins e envG envI bs env) (denot_exps ins es envG envI bs env).
Proof.
  trivial.
Qed.

Lemma denot_exps_nil :
  forall ins envG envI bs env,
    denot_exps ins [] envG envI bs env = errTy.
Proof.
  trivial.
Qed.

Lemma denot_exps_1 :
  forall ins e envG envI bs env,
    list_of_nprod (denot_exps ins [e] envG envI bs env)
    = list_of_nprod (denot_exp ins e envG envI bs env).
Proof.
  intros.
  rewrite denot_exps_eq.
  setoid_rewrite list_of_nprod_app.
  simpl.
  now rewrite app_nil_r.
Qed.

Definition denot_var ins envI env x : DS (sampl value) :=
  if mem_ident x ins then envI x else env x.

(* TODO: wrapper pour tests d'égalité des longueurs *)
Lemma denot_exp_eq :
  forall ins e envG envI bs env,
    denot_exp ins e envG envI bs env =
      match e return nprod (numstreams e) with
      | Econst c => sconst (Vscalar (sem_cconst c)) bs
      | Evar x _ => denot_var ins envI env x
      | Eunop op e an =>
          let se := denot_exp ins e envG envI bs env in
          match numstreams e as n return nprod n -> nprod 1 with
          | 1 => fun se =>
              match typeof e with
              | [ty] => sunop (fun v => sem_unop op v ty) se
              | _ => errTy
              end
          | _ => fun _ => errTy
          end se
      (* | Ebinop _ _ _ op e1 e2 => *)
      (*     binop (denot_lbinop op) (denot_exp e1 genv env bs) (denot_exp e2 genv env bs) *)
      | Efby e0s es an =>
          let s0s := denot_exps ins e0s envG envI bs env in
          let ss := denot_exps ins es envG envI bs env in
          let n := (list_sum (List.map numstreams e0s)) in
          let m := (list_sum (List.map numstreams es)) in
          match Nat.eq_dec n m, Nat.eq_dec (length an) n with
          | left eqm, left eqan =>
              eq_rect_r nprod (lift2 (SDfuns.fby) s0s (eq_rect_r nprod ss eqm)) eqan
          | _, _ => nprod_const errTy _
          end
      (* | Earrow _ e0 e => *)
      (*     lift2 s (@arrow) _ (denot_exp e0 genv env bs) (denot_exp e genv env bs) *)
      (* | Epair _ _ e1 e2 => *)
      (*     PAIR_flat s _ _ (denot_exp e1 genv env bs) (denot_exp e2 genv env bs) *)
      | Ewhen es (x,_) k (tys,_) =>
          let ss := denot_exps ins es envG envI bs env in
          match Nat.eq_dec (length tys) (list_sum (List.map numstreams es)) with
          | left eqn =>
              eq_rect_r nprod (llift (swhenv k) ss (denot_var ins envI env x)) eqn
          | _ => nprod_const errTy _
          end
      | Eapp f es _ an =>
          let ss := denot_exps ins es envG envI bs env in
          match find_node f G with
          | Some n =>
              match Nat.eq_dec (length an) (length (idents n.(n_out))) with
              | left eqan =>
                  eq_rect_r nprod
                    (ss_of_env (idents n.(n_out)) (envG f (env_of_ss (idents n.(n_in)) ss)))
                    eqan
              | _ => nprod_const errTy _
              end
          | _ => nprod_const errTy _
          end
      (* | Emerge _ x vd eT eF => *)
      (*     llift2 s _ (@merge) _ (denot_var s thisd x vd env) *)
      (*       (denot_exp eT genv env bs) (denot_exp eF genv env bs) *)
      (* | Eite _ e eT eF => *)
      (*     llift2 s _ (@ite) _ (denot_exp e genv env bs) *)
      (*       (denot_exp eT genv env bs) (denot_exp eF genv env bs) *)
      (* | Ereset _ _ f fd e er => *)
      (*     reset (denot_app s gd f fd genv) *)
                          (*       (denot_exp er genv env bs) (denot_exp e genv env bs) *)
      | _ => nprod_const errTy _
      end.
Proof.
  destruct e; auto; intros envG envI bs env.
  - (* Evar *)
    unfold denot_exp, denot_exp_, denot_var at 1.
    cases.
  - (* Eunop *)
    unfold denot_exp, denot_exp_ at 1.
    fold (denot_exp_ ins e).
    autorewrite with cpodb using (simpl (fst _); simpl (snd _)).
    generalize (denot_exp_ ins e) as ss.
    generalize (numstreams e) as ne.
    destruct ne as [|[]]; intros; auto.
    destruct (typeof e) as [|? []]; auto.
  - (* Efby*)
    rename l into e0s, l0 into es, l1 into a.
    unfold denot_exp, denot_exp_ at 1.
    destruct
      (Nat.eq_dec (list_sum (List.map numstreams e0s)) (list_sum (List.map numstreams es))) as [E1|],
        (Nat.eq_dec (length a) (list_sum (List.map numstreams e0s))) as [E2|]; auto.
    unfold denot_exps.
    (* FIXME: (denot_exps_ e0s) et (denot_exps_ es) apparaissent sous forme déroulée
       à gauche de l'égalité car [denot_exps] n'existait pas encore lors de la définition
       de [denot_exp_]. Coq n'arrive pas à les enrouler avec [fold (denot_exps_ e0s)] et
       [fold (denot_exps_ es)]. On doit l'aider avec la tactique suivante.
     *)
    do 2 match goal with
     | |- context [  (list_rect ?A ?B ?C ?D) ] =>
         change (list_rect A B C D) with (denot_exps_ ins D);
         generalize (denot_exps_ ins D); intro (* pour pouvoir détruire E1 et E2 *)
      end.
    now destruct E1, E2.
  - (* Ewhen *)
    destruct l0 as (tys,?).
    destruct p as (i,?).
    unfold denot_exp, denot_exp_, denot_var at 1.
    (* unfold denot_exp, denot_exp_ at 1. *)
    destruct (Nat.eq_dec _ _) as [E|]; auto.
    unfold denot_exps.
    match goal with
     | |- context [  (list_rect ?A ?B ?C ?D) ] =>
         change (list_rect A B C D) with (denot_exps_ ins D);
         generalize (denot_exps_ ins D); intro (* pour pouvoir détruire E1 et E2 *)
    end.
    unfold eq_rect_r, eq_rect, eq_sym; cases.
  - (* Eapp *)
    rename l into es, l0 into er, l1 into anns, i into f.
    unfold denot_exp, denot_exp_ at 1.
    destruct (find_node f G) as [n|]; auto.
    destruct (Nat.eq_dec _ _); auto.
    unfold denot_exps.
    match goal with
     | |- context [  (list_rect ?A ?B ?C ?D) ] =>
         change (list_rect A B C D) with (denot_exps_ ins D);
         generalize (denot_exps_ ins D); intro (* pour pouvoir détruire E1 et E2 *)
    end.
    generalize (ss_of_env (idents (n_out n))).
    unfold eq_rect_r, eq_rect, eq_sym; cases.
Qed.

Global Opaque denot_exp.

(* TODO: comprendre pourquoi on ne peut pas faire les deux en un ?????? *)
Global Add Parametric Morphism ins : (denot_var ins)
    with signature @Oeq (DS_prod SI) ==> @eq (DS_prod SI) ==> @eq ident ==> @Oeq (DS (sampl value))
      as denot_var_morph1.
Proof.
  unfold denot_var.
  intros; cases.
Qed.
Global Add Parametric Morphism ins : (denot_var ins)
    with signature @eq (DS_prod SI) ==> @Oeq (DS_prod SI) ==> @eq ident ==> @Oeq (DS (sampl value))
      as denot_var_morph2.
Proof.
  unfold denot_var.
  intros; cases.
Qed.

Definition denot_equation (ins : list ident) (e : equation) :
  Dprodi FI -C-> DS_prod SI -C-> DS bool -C-> DS_prod SI -C-> DS_prod SI.
  destruct e as (xs,es).
  (* vérification des tailles *)
  destruct (Nat.eq_dec
              (length xs)
              (list_sum (List.map numstreams es))
           ) as [Heq|].
  2:{ apply curry, curry, curry, Dprodi_DISTR.
      exact (fun _ => CTE _ _ errTy). }
  pose proof (ss := denot_exps_ ins es).
  apply curry, curry, curry, Dprodi_DISTR.
  intro x.
  destruct (mem_ident x ins).
  (* si x est une entrée *)
  exact (PROJ (DS_fam SI) x @_ SND _ _ @_ FST _ _ @_ FST _ _).
  (* x est un indice dans l'environment des sorties. S'il apparaît dans
     les xs on le met à jour, sinon on regarde dans l'environnement *)
  revert Heq ss.
  generalize (list_sum (List.map numstreams es)) as n; intros.
  (* on ne garde que env et ss (pas les entrées) *)
  eapply fcont_comp2.
  2: exact (SND _ _).
  2: exact ss.
  clear ss.
  apply curry.
  revert dependent n.
  (* TODO: on considère que toutes les sorties sont définies dans
     cette équation. L'alternative est de garder la liste des sorties
     et de faire deux cas lorsque la variable n'appartient pas à xs :
     - si la varible est une sortie : retrouner (env x)
     - sinon, renvoyer error_Ty *)
  induction xs as [| y xs]; intros.
  - exact (CTE _ _ errTy).
  - destruct (ident_eq_dec x y).
    + exact (nprod_fst errTy @_ SND _ _).
    + eapply fcont_comp.
      * exact (IHxs (length xs) eq_refl).
      * inv Heq.
        exact (PROD_map (ID _) nprod_skip).
Defined.

Section Equation_spec.

Lemma denot_equation_eq :
  forall ins xs es envG envI bs env x,
    denot_equation ins (xs,es) envG envI bs env x
    = if Nat.eq_dec (length xs) (list_sum (List.map numstreams es))
      then
        if mem_ident x ins then envI x else
         let ss := denot_exps ins es envG envI bs env in
         match mem_nth xs x with
         | None => errTy
         | Some n => get_nth n errTy ss
         end
       else errTy.
Proof.
  intros ?????? env ?.
  unfold denot_equation, denot_exps.
  destruct (Nat.eq_dec (length xs) (list_sum (List.map numstreams es))) as [Heq|]; auto.
  (* FIXME: pourquoi faut-il ajouter ça ? *)
  Local Hint Rewrite (Dprodi_DISTR_simpl _ (DS_fam SI)) : cpodb.
  autorewrite with cpodb using (simpl (snd _); simpl (fst _)).
  destruct (mem_ident x ins); auto.
  autorewrite with cpodb using (simpl (snd _); simpl (fst _)).
  generalize (denot_exps_ ins es).
  revert Heq.
  generalize (list_sum (List.map numstreams es)).
  induction xs; intros; simpl; auto.
  destruct (ident_eq_dec x a); auto.
  destruct Heq; simpl.
  autorewrite with cpodb using (simpl (snd _); simpl (fst _)).
  rewrite IHxs with (t := nprod_skip @_ t).
  destruct (mem_nth xs x); auto.
Qed.

Global Opaque denot_equation.

Lemma denot_equation_input :
  forall e ins envG envI bs env x,
    wl_equation G e ->
    In x ins ->
    denot_equation ins e envG envI bs env x = envI x.
Proof.
  intros * Hwt Hx.
  apply mem_ident_spec in Hx.
  destruct e as (xs,es).
  destruct Hwt as [? Hwt].
  rewrite annots_numstreams in Hwt.
  rewrite denot_equation_eq.
  cases_eqn HH; congruence.
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
(*         cases. exact errTy. exact (DS_const tt). } *)
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

Definition denot_block (ins : list ident) (b : block) :
  Dprodi FI -C-> DS_prod SI -C-> DS bool -C-> DS_prod SI -C-> DS_prod SI :=
  match b with
  | Beq e => denot_equation ins e
  | _ => curry (curry (curry (SND _ _ @_ FST _ _ @_ FST _ _))) (* garder les entrées *)
  end.

Definition denot_node (n : node) :
  (* envG -> envI -> env -> env *)
  Dprodi FI -C-> DS_prod SI -C-> DS_prod SI -C-> DS_prod SI.
  apply curry.
  refine ((denot_block (idents n.(n_in)) n.(n_block) @3_ _) _ _).
  - exact (FST _ _). (* envG *)
  - exact (SND _ _). (* envI *)
  - exact (bss (idents n.(n_in)) @_ SND _ _).
Defined.

Lemma denot_node_eq : forall n envG envI,
    let ins := idents n.(n_in) in
    denot_node n envG envI = denot_block ins n.(n_block) envG envI (bss ins envI).
Proof.
  trivial.
Qed.

Lemma denot_node_input :
  forall nd envG envI env x,
    wl_node G nd ->
    In x (List.map fst nd.(n_in)) ->
    denot_node nd envG envI env x = envI x.
Proof.
  intros * Hwl Hin.
  unfold denot_node, denot_block.
  inv Hwl; auto.
  autorewrite with cpodb.
  eapply denot_equation_input; eauto.
Qed.

End Denot_node.


Section Global.

  Definition env_err_ty : DS_prod SI := fun _ => errTy.

  Definition denot_global_ (G : global) : Dprodi FI -C-> Dprodi FI.
    apply Dprodi_DISTR; intro f.
    destruct (find_node f G).
    - exact (curry (FIXP _ @_ (denot_node G n @2_ FST _ _) (SND _ _))).
    - apply CTE, CTE, env_err_ty.
  Defined.

  Lemma denot_global_eq :
    forall G envG f envI,
      denot_global_ G envG f envI =
        match find_node f G with
        | Some n => FIXP _ (denot_node G n envG envI)
        | None => env_err_ty
        end.
  Proof.
    intros.
    unfold denot_global_.
    autorewrite with cpodb.
    cases.
  Qed.

  Definition denot_global (G : global) : Dprodi FI :=
    FIXP _ (denot_global_ G).

End Global.

Section Temp.

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
| restr_Ewhen :
  forall es x k anns,
    Forall restr_exp es ->
    restr_exp (Ewhen es x k anns)
| restr_Eapp :
  forall f es anns,
    (* TODO: reset *)
    Forall restr_exp es ->
    restr_exp (Eapp f es [] anns)
.

Inductive restr_block : block -> Prop :=
| restr_Beq :
  forall xs es,
    Forall restr_exp es ->
    restr_block (Beq (xs,es)).

Definition restr_node (nd : node) : Prop :=
  restr_block nd.(n_block).

Definition restr_global (g : global) : Prop :=
  Forall restr_node g.(nodes).

End Temp.


(** Here we show that a node can be removed from the environment if it
    is not evaluated during the computations. *)
Section Denot_cons.

Lemma denot_exp_cons :
  forall nd nds tys exts
    ins envG envI bs env e,
    ~ Is_node_in_exp nd.(n_name) e ->
    denot_exp (Global tys exts nds) ins e envG envI bs env
    == denot_exp (Global tys exts (nd :: nds)) ins e envG envI bs env.
Proof.
  Ltac solve_nin Hnin :=
    let H := fresh in
    intro H; apply Hnin; constructor; auto.
  (* TODO: utiliser ça partout, vraiment ! *)
  Ltac gen_denot :=
    repeat match goal with
      | |- context [ denot_exp ?a ?b ?c ] => generalize (denot_exp a b c)
      | |- context [ denot_exps ?a ?b ?c ] => generalize (denot_exps a b c)
      end.
  induction e using exp_ind2; intro Hnin.
  all: setoid_rewrite denot_exp_eq; auto.
  - (* unop *)
    revert IHe.
    gen_denot.
    cases; simpl; intros.
    rewrite IHe; auto.
    intro H; apply Hnin; constructor; auto.
  - (* fby *)
    assert (denot_exps (Global tys exts nds) ins e0s envG envI bs env
            == denot_exps (Global tys exts (nd::nds)) ins e0s envG envI bs env) as He0s.
    { induction e0s. trivial.
      inv H.
      (* TODO: faire mieux, cette preuve est un enfer *)
      rewrite 2 denot_exps_eq.
      apply nprod_app_Oeq_compat.
      - apply H3. solve_nin Hnin.
      - apply IHe0s; auto.
        intro HH; inv HH. apply Hnin. constructor.
        destruct H2; eauto using Exists_cons_tl. }
    assert (denot_exps (Global tys exts nds) ins es envG envI bs env
            == denot_exps (Global tys exts (nd::nds)) ins es envG envI bs env) as Hes.
    { induction es. trivial.
      inv H0.
      (* TODO: faire mieux, cette preuve est un enfer *)
      rewrite 2 denot_exps_eq.
      apply nprod_app_Oeq_compat.
      - apply H3. solve_nin Hnin.
      - apply IHes; auto.
        intro HH; inv HH. apply Hnin. constructor.
        destruct H2; eauto using Exists_cons_tl. }
    revert He0s Hes; simpl; unfold eq_rect_r, eq_rect, eq_sym.
    gen_denot; cases.
  - (* when *)
    assert (denot_exps (Global tys exts nds) ins es envG envI bs env
            == denot_exps (Global tys exts (nd::nds)) ins es envG envI bs env) as Hes.
    { induction es. trivial.
      inv H.
      (* TODO: faire mieux, cette preuve est un enfer *)
      rewrite 2 denot_exps_eq.
      apply nprod_app_Oeq_compat.
      - apply H2. solve_nin Hnin.
      - apply IHes; auto.
        intro HH; inv HH. apply Hnin.
        constructor; eauto using Exists_cons_tl. }
    revert Hes; simpl; unfold eq_rect_r, eq_rect, eq_sym.
    gen_denot; cases.
  - (* eapp, seul cas intéressant *)
    simpl.
    destruct (ident_eq_dec nd.(n_name) f) as [|Hf]; subst.
    { (* si oui, contradiction *)
      destruct Hnin. apply INEapp2. }
    rewrite (find_node_other _ _ _ _ _ Hf).
    assert (denot_exps (Global tys exts nds) ins es envG envI bs env
            == denot_exps (Global tys exts (nd::nds)) ins es envG envI bs env) as Hes.
    { induction es. trivial.
      inv H.
      (* TODO: faire mieux, cette preuve est un enfer *)
      rewrite 2 denot_exps_eq.
      apply nprod_app_Oeq_compat.
      - apply H3. solve_nin Hnin.
      - apply IHes; auto.
        intro HH; inv HH; auto.
        apply Hnin; constructor.
        destruct H2; eauto using Exists_cons_tl.
    }
    revert Hes; simpl; unfold eq_rect_r, eq_rect, eq_sym.
    gen_denot; cases.
    now intros ?? ->.
Qed.

Lemma denot_node_cons :
  forall n nd nds tys exts,
    ~ Is_node_in_block nd.(n_name) n.(n_block) ->
    denot_node (Global tys exts nds) n
    == denot_node (Global tys exts (nd :: nds)) n.
Proof.
  intros * Hnin.
  unfold denot_node, denot_block.
  destruct n.(n_block).
  2-5: trivial.
  destruct e as (xs,es).
  apply fcont_eq_intro; intro envG.
  apply fcont_eq_intro; intro envI.
  apply fcont_eq_intro; intro bs.
  apply Oprodi_eq_intro; intro x.
  autorewrite with cpodb.
  setoid_rewrite denot_equation_eq.
  cases_eqn HH; simpl.
  apply (get_nth_Oeq_compat _ _ errTy).
  clear - Hnin.
  induction es. reflexivity.
  rewrite 2 denot_exps_eq.
  apply nprod_app_Oeq_compat.
  - apply denot_exp_cons. intro.
    apply Hnin. constructor. now constructor.
  - apply IHes. intro H. inv H.
    apply Hnin. constructor.
    unfold Is_node_in_eq in *; eauto using Exists_cons_tl.
Qed.

(* Lemma denot_global_cons_ : *)
(*   forall nd nds tys f envG, *)
(*     Ordered_nodes (Global tys (nd :: nds)) -> *)
(*     nd.(n_name) <> f -> *)
(*     denot_global_ (Global tys (nd::nds)) envG f *)
(*     == denot_global_ (Global tys nds) envG f. *)
(* Proof. *)
(*   intros * Hord Hneq. *)
(*   apply fcont_eq_intro; intro envI. *)
(*   rewrite 2 denot_global_eq, (find_node_other _ _ _ _ Hneq). *)
(*   destruct (find_node _ _) eqn:Hfind. 2: auto. *)
(*   rewrite <- denot_node2_cons; eauto using find_node_later_not_Is_node_in. *)
(* Qed. *)

End Denot_cons.


End LDENOT.

Module LDenotFun
  (Ids   : IDS)
  (Op    : OPERATORS)
  (OpAux : OPERATORS_AUX Ids Op)
  (Cks   : CLOCKS        Ids Op OpAux)
  (Senv  : STATICENV     Ids Op OpAux Cks)
  (Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
  (Lord  : LORDERED      Ids Op OpAux Cks Senv Syn)
<: LDENOT Ids Op OpAux Cks Senv Syn Lord.
  Include LDENOT Ids Op OpAux Cks Senv Syn Lord.
End LDenotFun.
