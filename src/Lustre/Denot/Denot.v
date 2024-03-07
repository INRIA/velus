From Coq Require Import BinPos List.

From Velus Require Import Common Ident Operators Clocks CoindStreams.
From Velus Require Import Lustre.StaticEnv Lustre.LSyntax Lustre.LSemantics Lustre.LOrdered.
From Velus Require Import Lustre.Denot.Cpo.

Close Scope equiv_scope. (* conflicting notation "==" *)
Import ListNotations.

Require Import CommonList2.
Require Import SDfuns.

Module Type LDENOT
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Senv  : STATICENV     Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
       (Import Lord  : LORDERED      Ids Op OpAux Cks Senv Syn).

Context {PSyn : list decl -> block -> Prop} {Prefs : PS.t}.
Definition node := @node PSyn Prefs.
Definition global := @global PSyn Prefs.

(* TODO: move somewhere else? *)
Section LSyntax_facts.

(* TODO: définition un peu foireuse, qui doit correspondre aux
   inversions de wt_block... *)
Definition get_locals (blk : block) : static_env :=
  match blk with
  | Blocal (Scope vars _) => senv_of_decls vars
  | _ => []
  end.

Lemma NoDup_senv_loc :
  forall (nd : node) vars blks,
    n_block nd = Blocal (Scope vars blks) ->
    NoDupMembers (senv_of_ins (n_in nd) ++ senv_of_decls (n_out nd) ++ senv_of_decls vars).
Proof.
  intros * Hn.
  pose proof (n_nodup nd) as [Nd Ndl].
  rewrite Hn in Ndl; inv Ndl.
  take (NoDupScope _ _ _) and inversion_clear it as [???? ndm Hf].
  rewrite fst_NoDupMembers, 2 map_app, map_fst_senv_of_ins, 2 map_fst_senv_of_decls.
  rewrite app_assoc.
  apply fst_NoDupMembers in ndm.
  apply NoDup_app'_iff; repeat split; auto.
  setoid_rewrite fst_InMembers in Hf.
  simpl_Forall.
  contradict Hf; eauto.
Qed.

Corollary NoDup_iol :
  forall (n : node),
    NoDupMembers (senv_of_ins (n_in n) ++ senv_of_decls (n_out n) ++ get_locals (n_block n)).
Proof.
  intros.
  pose proof (node_NoDupMembers n) as ND.
  destruct (n_block n) eqn:Hn; simpl; try rewrite app_nil_r; auto.
  destruct s.
  apply NoDup_senv_loc in Hn; auto.
Qed.

(** Chercher les variables à gauche des équations dans les blocks *)
Definition get_defined (blk : block) : list ident :=
  match blk with
  | Beq (xs,es) => xs
  | _ => []
  end.

(** Et dans les nœuds  *)
Definition get_defined_node (n : node) : list ident :=
  match n_block n with
  | Blocal (Scope _ blks) => flat_map get_defined blks
  | _ => []
  end.

Lemma NoDup_get_defined :
  forall (nd : node) vars blks,
    n_block nd = Blocal (Scope vars blks) ->
    NoDup (flat_map get_defined blks ++ List.map fst (n_in nd)).
Proof.
  intros * Hn.
  apply NoDup_senv_loc in Hn as ndm.
  pose proof (n_defd nd) as (outs & Vd & Perm).
  rewrite Hn in Vd.
  inv Vd. Syn.inv_scope.
  rename x into xs.
  rewrite Perm in H0.
  rewrite <- H0 in ndm.
  clear - ndm H.
  apply fst_NoDupMembers in ndm.
  rewrite Permutation.Permutation_app_comm, map_app, map_fst_senv_of_ins in ndm.
  induction H; simpl in *; auto.
  rewrite map_app, <- app_assoc in *.
  apply NoDup_app'; eauto using NoDup_app_r.
  - apply NoDup_app_l in ndm.
    inv H; simpl; auto using NoDup.
    cases; simpl in *; now subst.
  - apply Forall_forall; intros i Hin.
    inv H; simpl in *; auto.
    cases; simpl in *; subst.
    eapply NoDup_app_In in ndm; eauto.
    contradict ndm.
    clear - ndm H0.
    induction H0; simpl in *; auto.
    rewrite map_app, 2 in_app_iff in *.
    inv H; simpl in *; cases; simpl in *; subst; firstorder.
Qed.

Corollary NoDup_get_defined_node :
  forall (nd : node), NoDup (get_defined_node nd ++ List.map fst (n_in nd)).
Proof.
  intros.
  pose proof (Ndin := node_NoDup_in nd).
  unfold get_defined_node.
  cases_eqn Hn; subst.
  eapply NoDup_get_defined; eauto.
Qed.

Lemma get_defined_node_incl :
  forall (n : node),
    incl (get_defined_node n)
      (List.map fst (n_out n) ++ List.map fst (get_locals (n_block n))).
Proof.
  unfold get_defined_node.
  intro n.
  pose proof (n_defd n) as (xs & Vd & Perm).
  cases_eqn Hn; subst; simpl; try now (intros ? []).
  inv Vd.
  take (VarsDefinedScope _ _ _) and inversion_clear it as [??? (xs' & Vd' & Perm')].
  clear Hn.
  rewrite Perm in Perm'.
  clear - Vd' Perm'.
  apply (Permutation.Permutation_map fst) in Perm'.
  revert Perm'.
  rewrite map_app, 2 map_fst_senv_of_decls.
  generalize (List.map fst (n_out n) ++ List.map fst l).
  intros l' ?; clear l n.
  assert (Hincl : incl (List.map fst (concat xs')) l').
  { intros x Hin; rewrite Perm' in Hin; auto. }
  clear Perm'; revert Hincl; revert l'.
  induction Vd'; simpl; intros l1. { now intros ? []. }
  unfold incl in *.
  rewrite map_app.
  setoid_rewrite in_app_iff.
  intros Hincl a [Hin|Hin]; eauto.
  destruct x; simpl in *; try now inv Hin.
  destruct e as (xs,es).
  inv H; simpl in *; subst; auto.
Qed.

End LSyntax_facts.

(** We always use this specialized version of mem_nth *)
(* TODO: c'est vraiment une bonne idée de redéfinir des trucs, comme ça ? *)
Definition mem_nth := mem_nth ident ident_eq_dec.

Definition errTy : DS (sampl value) := DS_const (err error_Ty).

(** ** Denotational environments (local & program-wide) *)
Section Denot_env.

Definition SI := fun _ : ident => sampl value.
Definition FI := fun _ : ident => (DS_prod SI -C-> DS_prod SI).

Definition err_env : DS_prod SI := fun _ => errTy.

(** build an environment from a tuple of streams, with names given in [l] *)
Definition env_of_np (l : list ident) {n} : nprod n -C-> DS_prod SI :=
  Dprodi_DISTR _ _ _
    (fun x => match mem_nth l x with
           | Some n => get_nth n errTy
           | None => 0
           end).

Lemma env_of_np_eq :
  forall l n (ss : nprod n) x,
    env_of_np l ss x =
      match mem_nth l x with
      | Some n => get_nth n errTy ss
      | None => 0
      end.
Proof.
  unfold env_of_np.
  intros.
  setoid_rewrite Dprodi_DISTR_simpl.
  cases.
Qed.

Lemma env_of_np_tl :
  forall l n (np : nprod (S n)) x y,
    x <> y ->
    env_of_np (y :: l) np x == env_of_np l (nprod_tl np) x.
Proof.
  clear.
  intros.
  rewrite 2 env_of_np_eq; simpl.
  destruct (ident_eq_dec x y); try congruence.
  destruct (mem_nth l x); auto.
Qed.

Lemma env_of_np_nth :
  forall l n (np : nprod n) k x,
    mem_nth l x = Some k ->
    env_of_np l np x = get_nth k errTy np.
Proof.
  unfold env_of_np.
  intros.
  setoid_rewrite Dprodi_DISTR_simpl.
  cases. now inv H. congruence.
Qed.

(* Lemma env_of_np_inf : *)
(*   forall l n (np : nprod n), *)
(*     forall_nprod (@infinite _) np -> *)
(*     all_infinite (env_of_np l np). *)
(* Proof. *)
(*   clear. *)
(*   unfold env_of_np. *)
(*   intros * ??. *)
(*   setoid_rewrite Dprodi_DISTR_simpl. *)
(*   cases_eqn HH. *)
(*   - apply forall_nprod_k_def; auto. apply DS_const_inf. *)
(*   - apply DS_const_inf. *)
(* Qed. *)

Lemma forall_env_of_np :
  forall (P : DS (sampl value) -> Prop) l {n} (ss : nprod n),
    P errTy ->
    P 0 ->
    forall_nprod P ss ->
    forall x, P (env_of_np l ss x).
Proof.
  intros.
  unfold env_of_np.
  cbn; cases.
  destruct (Nat.lt_ge_cases n0 n).
  - apply forall_nprod_k; auto.
  - rewrite get_nth_err; auto.
Qed.

(** extract a tuple from an environment  *)
Definition np_of_env (l : list ident) : DS_prod SI -C-> @nprod (DS (sampl value)) (length l).
  induction l as [| x l].
  - apply CTE, 0.
  - exact ((nprod_cons @2_ PROJ _ x) IHl).
Defined.

Lemma nth_np_of_env :
  forall d d' l env k,
    k < length l ->
    get_nth k d' (np_of_env l env) = env (nth k l d).
Proof.
  induction l as [|? []]; intros * Hl.
  - inv Hl.
  - destruct k; auto. simpl in *; lia.
  - destruct k; simpl; auto.
    setoid_rewrite IHl; now auto with arith.
Qed.

Lemma forall_np_of_env :
  forall (P : DS (sampl value) -> Prop) l env,
    (forall x, P (env x)) ->
    forall_nprod P (np_of_env l env).
Proof.
  induction l as [|? []]; intros * Hp; eauto.
  - now simpl.
  - apply Hp.
  - constructor.
    + apply Hp.
    + apply IHl, Hp.
Qed.

(* version plus forte mais moins pratique à utiliser *)
Lemma forall_np_of_env' :
  forall (P : DS (sampl value) -> Prop) l env,
    (forall x, In x l -> P (env x)) ->
    forall_nprod P (np_of_env l env).
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

(* TODO: c'est un test, bouger!! *)
Section Nprod_Fold.

  Context {A B : cpo}.

  Fixpoint nprod_Fold {n} : (B -C-> A -C-> A) -C-> A -C-> @nprod B n -C-> A.
    destruct n.
    - apply CTE, CTE.
    - apply curry, curry.
      refine ((ID _ @3_ _) _ _).
      + exact ((FST _ _ @_ FST _ _)).
      + exact (nprod_hd @_ SND _ _).
      + exact ((nprod_Fold n @3_ FST _ _ @_ FST _ _) (SND _ _ @_ FST _ _) (nprod_tl @_ SND _ _)).
  Defined.

  Lemma Fold_eq :
    forall F a n (np : nprod (S n)),
      nprod_Fold F a np = F (nprod_hd np) (nprod_Fold F a (nprod_tl np)).
  Proof.
    trivial.
  Qed.

End Nprod_Fold.


Definition sbool_of : DS (sampl value) -C-> DS bool :=
  MAP (fun v => match v with
             | pres (Venum 1) => true
             | _ => false
             end).

Definition sbools_of {n} : @nprod (DS (sampl value)) n -C-> DS bool :=
  nprod_Fold (ZIP orb) (DS_const false) @_ lift sbool_of.

(* l'opérateur swhen spécialisé aux Velus.Op.value *)
Definition swhenv :=
  let get_tag := fun v => match v with Venum t => Some t | _ => None end in
  @swhen value value enumtag get_tag Nat.eqb.

(* idem pour smerge *)
Definition smergev :=
  let get_tag := fun v => match v with Venum t => Some t | _ => None end in
  @smerge value value enumtag get_tag Nat.eqb.

Definition scasev :=
  let get_tag := fun v => match v with Venum t => Some t | _ => None end in
  @scase value value enumtag get_tag Nat.eqb.

Definition scase_defv :=
  let get_tag := fun v => match v with Venum t => Some t | _ => None end in
  @scase_def value value enumtag get_tag Nat.eqb.

(** On définit tout de suite [denot_exps_] en fonction de [denot_exp_]
    pour simplifier le raisonnement dans denot_exp_eq *)
Section Denot_exps.

  Hypothesis denot_exp_ :
    forall e : exp,
      Dprod (Dprod (Dprodi FI) (DS_prod SI)) (DS_prod SI) -C->
      @nprod (DS (sampl value)) (numstreams e).

  Definition denot_exps_ (es : list exp) :
    Dprod (Dprod (Dprodi FI) (DS_prod SI)) (DS_prod SI) -C->
    @nprod (DS (sampl value)) (list_sum (List.map numstreams es)).
    induction es as [|a].
    + exact 0.
    + exact ((nprod_app @2_ (denot_exp_ a)) IHes).
  Defined.

  (* vérifie que chaque sous-liste d'expressions calcule exactement n flots et
   retourne un produit d'éléments de type (nprod n) *)
  (* FIXME: ess n'a pas le type list(list exp) car ça empêche la décroissance
   syntaxique lors de son appel dans denot_exp_ *)
  Definition denot_expss_ {A} (ess : list (A * list exp)) (n : nat) :
    Dprod (Dprod (Dprodi FI) (DS_prod SI)) (DS_prod SI) -C->
    @nprod (@nprod (DS (sampl value)) n) (length ess).
    induction ess as [|[? es]].
    + exact 0.
    + destruct (Nat.eq_dec (list_sum (List.map numstreams es)) n) as [<-|].
      * exact ((nprod_cons @2_ (denot_exps_ es)) IHess).
      * exact 0.
  Defined.

End Denot_exps.


Definition denot_exp_ (ins : list ident)
  (e : exp) :
  (* (nodes * inputs * env) -> streams *)
  Dprod (Dprod (Dprodi FI) (DS_prod SI)) (DS_prod SI) -C->
  @nprod (DS (sampl value)) (numstreams e).

  set (ctx := Dprod _ _).
  epose (denot_var :=
       fun x => if mem_ident x ins
             then PROJ (DS_fam SI) x @_ SND _ _ @_ FST _ _
             else PROJ (DS_fam SI) x @_ SND _ _).
  revert e.
  fix denot_exp_ 1.
  intro e.
  destruct e eqn:He; simpl (nprod _).
  - (* Econst *)
    apply (sconst (Vscalar (sem_cconst c)) @_ bss ins @_ SND _ _ @_ FST _ _).
  - (* Eenum *)
    apply (sconst (Venum e0) @_ bss ins @_ SND _ _ @_ FST _ _).
  - (* Evar *)
    exact (denot_var i).
  - (* Elast *)
    apply CTE, 0.
  - (* Eunop *)
    eapply fcont_comp. 2: apply (denot_exp_ e0).
    destruct (numstreams e0) as [|[]].
    (* pas le bon nombre de flots: *)
    1,3: apply CTE, errTy.
    destruct (typeof e0) as [|ty []].
    1,3: apply CTE, errTy.
    exact (sunop (fun v => sem_unop u v ty)).
  - (* Ebinop *)
    eapply fcont_comp2.
    3: apply (denot_exp_ e0_2).
    2: apply (denot_exp_ e0_1).
    destruct (numstreams e0_1) as [|[]], (numstreams e0_2) as [|[]].
    (* pas le bon nombre de flots: *)
    1-4,6-9: apply curry, CTE, errTy.
    destruct (typeof e0_1) as [|ty1 []], (typeof e0_2) as [|ty2 []].
    1-4,6-9: apply curry, CTE, errTy.
    exact (sbinop (fun v1 v2 => sem_binop b v1 ty1 v2 ty2)).
  - (* Eextcall *)
    apply CTE, 0.
  - (* Efby *)
    rename l into e0s, l0 into es, l1 into anns.
    clear He.
    pose (s0s := denot_exps_ denot_exp_ e0s).
    pose (ss := denot_exps_ denot_exp_ es).
    (* vérifier le typage *)
    destruct (Nat.eq_dec
                (list_sum (List.map numstreams es))
                (list_sum (List.map numstreams e0s))
             ) as [Heq1|].
    destruct (Nat.eq_dec
                (list_sum (List.map numstreams e0s))
                (length anns)
             ) as [Heq2|].
    (* si les tailles ne correspondent pas : *)
    2,3: apply CTE, (nprod_const _ errTy).
    rewrite Heq1 in ss.
    rewrite <- Heq2.
    exact ((lift2 (SDfuns.fby) @2_ s0s) ss).
  - (* Earrow *)
    apply CTE, 0.
  - (* Ewhen *)
    rename l into es.
    destruct l0 as (tys,ck).
    destruct p as (i,ty). clear He.
    destruct (Nat.eq_dec
                (list_sum (List.map numstreams es))
                (length tys)
             ) as [<-|].
    2: apply CTE, (nprod_const _ errTy).
    pose (ss := denot_exps_ denot_exp_ es).
    exact ((llift (swhenv e0) @2_ ss) (denot_var i)).
  - (* Emerge *)
    rename l into ies.
    destruct l0 as (tys,ck).
    destruct p as [i ty].
    (* on calcule (length tys) flots pour chaque liste de sous-expressions *)
    pose (ses := denot_expss_ denot_exp_ ies (length tys)).
    rewrite <- (map_length fst) in ses.
    exact ((lift_nprod @_ (smergev (List.map fst ies)) @2_ denot_var i) ses).
  - (* Ecase *)
    rename l into ies.
    destruct l0 as (tys,ck).
    (* on calcule (length tys) flots pour chaque liste de sous-expressions *)
    pose (ses := denot_expss_ denot_exp_ ies (length tys)).
    rewrite <- (map_length fst) in ses.
    destruct o as [d_es|].
    + (* avec une branche par défaut *)
      revert ses.
      destruct (Nat.eq_dec
                  (list_sum (List.map numstreams d_es))
                  (length tys)
               ) as [<-|].
      2: apply CTE, CTE, (nprod_const _ errTy).
      intro ses.
      refine ((_ @2_ (denot_exp_ e0)) ((nprod_cons @2_ denot_exps_ denot_exp_ d_es) ses)).
      destruct (numstreams e0) as [|[]].
      1,3: apply CTE, CTE, (nprod_const _ errTy).
      exact (lift_nprod @_ scase_defv (List.map fst ies)).
    + (* case total *)
      (* condition, branches *)
      refine ((_ @2_ (denot_exp_ e0)) ses).
      destruct (numstreams e0) as [|[]].
      1,3: apply CTE, CTE, (nprod_const _ errTy).
      exact (lift_nprod @_ (scasev (List.map fst ies))).
  - (* Eapp *)
    rename l into es, l0 into er, l1 into anns.
    clear He.
    destruct (find_node i G) as [n|].
    destruct (Nat.eq_dec (length (List.map fst n.(n_out))) (length anns)) as [<-|].
    2,3: apply CTE, (nprod_const _ errTy).
    (* dénotation du nœud *)
    pose (f := PROJ _ i @_ FST _ _ @_ FST _ _ : ctx -C-> FI i).
    pose (ss := denot_exps_ denot_exp_ es).
    pose (rs := denot_exps_ denot_exp_ er).
    (* chaînage *)
    refine
      (np_of_env (List.map fst (n_out n)) @_
         (sreset @3_ f) (sbools_of @_ rs) (env_of_np (idents (n_in n)) @_ ss)).
Defined.

Definition denot_exp (ins : list ident) (e : exp) :
  (* (nodes * inputs * env) -> streams *)
  Dprodi FI -C-> DS_prod SI -C-> DS_prod SI -C-> nprod (numstreams e) :=
  curry (curry (denot_exp_ ins e)).

Definition denot_exps (ins : list ident) (es : list exp) :
  Dprodi FI -C-> DS_prod SI -C-> DS_prod SI -C-> nprod (list_sum (List.map numstreams es)) :=
  curry (curry (denot_exps_ (denot_exp_ ins) es)).

Lemma denot_exps_eq :
  forall ins e es envG envI env,
    denot_exps ins (e :: es) envG envI env
    = nprod_app (denot_exp ins e envG envI env) (denot_exps ins es envG envI env).
Proof.
  reflexivity.
Qed.

Lemma forall_denot_exps :
  forall (P : DS (sampl value) -> Prop) ins es envG envI env,
    forall_nprod P (denot_exps ins es envG envI env)
    <-> Forall (fun e => forall_nprod P (denot_exp ins e envG envI env)) es.
Proof.
  induction es; intros; simpl; split; auto.
  - intro Hs. setoid_rewrite denot_exps_eq in Hs.
    apply app_forall_nprod in Hs as [].
    constructor; auto.
    now apply IHes.
  - intro Hs. inv Hs.
    setoid_rewrite denot_exps_eq.
    apply forall_nprod_app; auto.
    now apply IHes.
Qed.

Definition denot_expss {A} (ins : list ident) (ess : list (A * list exp)) (n : nat) :
  Dprodi FI -C-> DS_prod SI -C-> DS_prod SI -C->
  @nprod (@nprod (DS (sampl value)) n) (length ess) :=
  curry (curry (denot_expss_ (denot_exp_ ins) ess n)).

Lemma denot_expss_eq :
  forall A ins (x : A) es ess envG envI env n,
    denot_expss ins ((x,es) :: ess) n envG envI env
    = match Nat.eq_dec (list_sum (List.map numstreams es)) n with
      | left eqn =>
          nprod_cons
            (eq_rect _ nprod (denot_exps ins es envG envI env) _ eqn)
            (denot_expss ins ess n envG envI env)
      | _ => 0
      end.
Proof.
  intros.
  unfold denot_expss, denot_expss_, denot_exps at 1.
  simpl (list_rect _ _ _ _).
  generalize (denot_exps_ (denot_exp_ ins) es); intro.
  cases; auto.
  destruct e; cases.
Qed.

Lemma denot_expss_nil :
  forall A ins n envG envI env,
    @denot_expss A ins [] n envG envI env == 0.
Proof.
  reflexivity.
Qed.

(* TODO: move if useful *)
Lemma forall_nprod_bot :
  forall D n (P : _ -> Prop),
    P 0 ->
    @forall_nprod D P n 0.
Proof.
  induction n as [|[]]; intros; try split; auto.
  now apply IHn.
Qed.

Lemma forall_denot_expss :
  forall A ins (ess : list (A * list exp)) n envG envI env (P : nprod n -> Prop),
    Forall (fun es =>
              match Nat.eq_dec (list_sum (List.map numstreams es)) n with
              | left eqn =>
                  P (eq_rect _ nprod (denot_exps ins es envG envI env) n eqn)
              | _ => P 0
              end) (List.map snd ess) ->
    forall_nprod P (denot_expss ins ess n envG envI env).
Proof.
  induction ess as [|[]]; intros * Hf; inv Hf.
  - simpl; auto.
  - rewrite denot_expss_eq.
    unfold eq_rect in *.
    cases; eauto using forall_nprod_cons, forall_nprod_bot.
Qed.

Lemma forall_forall_denot_expss :
  forall A ins (ess : list (A * list exp)) n envG envI env (P : DS (sampl value) -> Prop),
    P 0 ->
    Forall (fun es => forall_nprod P (denot_exps ins (snd es) envG envI env)) ess ->
    forall_nprod (forall_nprod P) (denot_expss ins ess n envG envI env).
Proof.
  induction ess as [|[]]; intros * Herr Hf; inv Hf.
  - simpl; auto.
  - rewrite denot_expss_eq.
    unfold eq_rect in *.
    cases; eauto using forall_nprod_cons, forall_nprod_bot.
Qed.

Lemma Forall_denot_expss :
  forall A P ins (es : list (A * list exp)) n envG envI env,
    Forall (fun es => length (annots (snd es)) = n) es ->
    forall_nprod (forall_nprod P) (denot_expss ins es n envG envI env)
    <-> Forall (fun l => Forall (fun e => forall_nprod P (denot_exp ins e envG envI env)) l) (List.map snd es).
Proof.
  clear.
  induction es as [|[i es] ess]; intros * Hl.
  - repeat constructor.
  - inv Hl.
    rewrite denot_expss_eq.
    unfold eq_rect; cases.
    + (* sans erreurs *)
      simpl (Forall _ _).
      rewrite Forall_cons2.
      rewrite <- (IHess (list_sum (List.map numstreams es))); auto.
      setoid_rewrite forall_nprod_cons_iff.
      now rewrite <- forall_denot_exps.
    + now rewrite annots_numstreams in n.
Qed.

Lemma denot_exps_nil :
  forall ins envG envI env,
    denot_exps ins [] envG envI env = 0.
Proof.
  reflexivity.
Qed.

Lemma denot_exps_1 :
  forall ins e envG envI env,
    list_of_nprod (denot_exps ins [e] envG envI env)
    = list_of_nprod (denot_exp ins e envG envI env).
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
  forall ins e envG envI env,
    denot_exp ins e envG envI env =
      match e return nprod (numstreams e) with
      | Econst c => sconst (Vscalar (sem_cconst c)) (bss ins envI)
      | Eenum c _ => sconst (Venum c) (bss ins envI)
      | Evar x _ => denot_var ins envI env x
      | Eunop op e an =>
          let se := denot_exp ins e envG envI env in
          match numstreams e as n return nprod n -> nprod 1 with
          | 1 => fun se =>
              match typeof e with
              | [ty] => sunop (fun v => sem_unop op v ty) se
              | _ => errTy
              end
          | _ => fun _ => errTy
          end se
      | Ebinop op e1 e2 an =>
          let se1 := denot_exp ins e1 envG envI env in
          let se2 := denot_exp ins e2 envG envI env in
          match numstreams e1 as n1, numstreams e2 as n2
                return nprod n1 -> nprod n2 -> nprod 1 with
          | 1,1 => fun se1 se2 =>
               match typeof e1, typeof e2 with
               | [ty1],[ty2] => sbinop (fun v1 v2 => sem_binop op v1 ty1 v2 ty2) se1 se2
               | _,_ => errTy
               end
          | _,_ => fun _ _ => errTy
          end se1 se2
      | Efby e0s es an =>
          let s0s := denot_exps ins e0s envG envI env in
          let ss := denot_exps ins es envG envI env in
          let n := (list_sum (List.map numstreams e0s)) in
          let m := (list_sum (List.map numstreams es)) in
          match Nat.eq_dec m n, Nat.eq_dec n (length an) with
          | left eqm, left eqan =>
              eq_rect _ nprod (lift2 (SDfuns.fby) s0s (eq_rect _ nprod ss _ eqm)) _ eqan
          | _, _ => nprod_const _ errTy
          end
      (* | Earrow _ e0 e => *)
      (*     lift2 s (@arrow) _ (denot_exp e0 genv env bs) (denot_exp e genv env bs) *)
      (* | Epair _ _ e1 e2 => *)
      (*     PAIR_flat s _ _ (denot_exp e1 genv env bs) (denot_exp e2 genv env bs) *)
      | Ewhen es (x,_) k (tys,_) =>
          let ss := denot_exps ins es envG envI env in
          match Nat.eq_dec (list_sum (List.map numstreams es)) (length tys) with
          | left eqn =>
              eq_rect _ nprod (llift (swhenv k) ss (denot_var ins envI env x)) _ eqn
          | _ => nprod_const _ errTy
          end
      | Emerge (x,_) ies (tys,_) =>
          let ss := denot_expss ins ies (length tys) envG envI env in
          let ss := eq_rect_r nprod ss (map_length _ _) in
          lift_nprod (smergev (List.map fst ies) (denot_var ins envI env x)) ss
      | Ecase ec ies None (tys,_) =>
          let ss := denot_expss ins ies (length tys) envG envI env in
          let ss := eq_rect_r nprod ss (map_length _ _) in
          let cs := denot_exp ins ec envG envI env in
          match numstreams ec as n return nprod n -> _ with
          | 1 => fun cs => lift_nprod (scasev (List.map fst ies) cs) ss
          | _ => fun _ => nprod_const _ errTy
          end cs
      | Ecase ec ies (Some eds) (tys,_) =>
          let ss := denot_expss ins ies (length tys) envG envI env in
          let ss := eq_rect_r nprod ss (map_length _ _) in (* branches *)
          let cs := denot_exp ins ec envG envI env in (* condition *)
          let ds := denot_exps ins eds envG envI env in (* défaut *)
          match numstreams ec as n, Nat.eq_dec (list_sum (List.map numstreams eds)) (length tys) return nprod n -> _ with
          | 1, left eqm =>
              fun cs => lift_nprod (scase_defv (List.map fst ies) cs)
                       (nprod_cons (eq_rect _ nprod ds _ eqm) ss)
          | _,_ => fun _ => nprod_const _ errTy
          end cs
      | Eapp f es er an =>
          let ss := denot_exps ins es envG envI env in
          let rs := denot_exps ins er envG envI env in
          match find_node f G with
          | Some n =>
              match Nat.eq_dec (length (List.map fst n.(n_out))) (length an) with
              | left eqan =>
                  eq_rect _ nprod
                    (np_of_env (List.map fst n.(n_out)) (sreset (envG f) (sbools_of rs) (env_of_np (idents n.(n_in)) ss)))
                    _ eqan
              | _ => nprod_const _ errTy
              end
          | _ => nprod_const _ errTy
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
      | _ => 0
      end.
Proof.
  (* Le système se sent obligé de dérouler deux fois [denot_exp_] lors
     d'un appel à [unfold] et c'est très pénible.
     Cette tactique permet de le renrouler. *)
  Ltac fold_denot_exps_ ins :=
    repeat
      match goal with
      | |- context [ denot_exps_ ?A ] =>
          change A with (denot_exp_ ins)
      | |- context [ denot_expss_ ?A ] =>
          change A with (denot_exp_ ins)
      end.

  (* On doit souvent abstraire la définition des sous-flots
     pour pouvoir détruire les prédicats d'égalité sous les [eq_rect] etc.
     Cette tactique le fait automatiquement. *)
  Ltac gen_denot_sub_exps :=
    repeat
      match goal with
      | |- context [ denot_exp_ ?A ?B ] =>
          generalize (denot_exp_ A B); intro
      | |- context [ denot_exps_ ?A ?B ] =>
          generalize (denot_exps_ A B); intro
      | |- context [ denot_expss_ ?A ?B ] =>
          generalize (denot_expss_ A B); intro
      end.

  destruct e; auto; intros envG envI env.
  - (* Evar *)
    unfold denot_exp, denot_exp_, denot_var at 1.
    cases.
  - (* Eunop *)
    unfold denot_exp, denot_exp_ at 1.
    fold (denot_exp_ ins e).
    generalize (denot_exp_ ins e) as ss.
    generalize (numstreams e) as ne.
    destruct ne as [|[]]; intros; auto.
    destruct (typeof e) as [|? []]; auto.
  - (* Ebinop *)
    unfold denot_exp, denot_exp_ at 1.
    fold (denot_exp_ ins e1) (denot_exp_ ins e2).
    generalize (denot_exp_ ins e1) as ss1.
    generalize (denot_exp_ ins e2) as ss2.
    generalize (numstreams e1) as ne1.
    generalize (numstreams e2) as ne2.
    destruct ne1 as [|[]], ne2 as [|[]]; intros; auto.
    destruct (typeof e1) as [|?[]], (typeof e2) as [|?[]]; auto.
  - (* Efby*)
    unfold denot_exp, denot_exps, denot_exp_ at 1.
    fold_denot_exps_ ins.
    unfold eq_rect.
    gen_denot_sub_exps.
    cases; simpl; cases.
  - (* Ewhen *)
    destruct l0 as (tys,?).
    destruct p as (i,?).
    unfold denot_exp, denot_exps, denot_exp_ at 1.
    fold_denot_exps_ ins.
    gen_denot_sub_exps.
    unfold denot_var, eq_rect.
    cases; simpl; cases.
  - (* Emerge *)
    destruct l0 as (tys,?).
    destruct p as (i,ty).
    unfold denot_exp, denot_exp_, denot_exps, denot_expss at 1.
    fold_denot_exps_ ins.
    gen_denot_sub_exps.
    unfold denot_var, eq_rect_r, eq_rect, eq_sym.
    cases.
  - (* Ecase *)
    destruct l0 as (tys,?).
    destruct o.
    + (* defaut *)
      unfold denot_exp, denot_exp_, denot_exps, denot_expss at 1.
      fold_denot_exps_ ins.
      gen_denot_sub_exps.
      unfold eq_rect_r, eq_rect, eq_sym.
      cases; simpl; cases.
    + (* total *)
      unfold denot_exp, denot_exp_, denot_exps, denot_expss at 1.
      fold_denot_exps_ ins.
      gen_denot_sub_exps.
      unfold eq_rect_r, eq_rect, eq_sym.
      cases.
  - (* Eapp *)
    rename l into es, l0 into er, l1 into anns, i into f.
    unfold denot_exp, denot_exps, denot_exp_ at 1.
    fold_denot_exps_ ins.
    gen_denot_sub_exps.
    cases.
    generalize (np_of_env (List.map fst (n_out n))); intro.
    unfold eq_rect.
    simpl; destruct e.
    rewrite 3 curry_Curry, 3 Curry_simpl, fcont_comp_simpl.
    reflexivity.
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

Lemma denot_var_inf :
  forall ins envI env x,
    all_infinite envI ->
    all_infinite env ->
    infinite (denot_var ins envI env x).
Proof.
  unfold denot_var.
  intros; cases; eauto.
Qed.

Lemma denot_var_nins :
  forall ins envI env x,
    ~ In x ins ->
    denot_var ins envI env x = env x.
Proof.
  unfold denot_var.
  intros.
  destruct (mem_ident x ins) eqn:Hmem; auto.
  now apply mem_ident_spec in Hmem.
Qed.

(* Definition denot_equation (ins : list ident) (e : equation) : *)
(*   Dprodi FI -C-> DS_prod SI -C-> DS bool -C-> DS_prod SI -C-> DS_prod SI. *)
(*   destruct e as (xs,es). *)
(*   pose proof (ss := denot_exps_ (denot_exp_ ins) es). *)
(*   apply curry, curry, curry, Dprodi_DISTR. *)
(*   intro x. *)
(*   destruct (mem_ident x ins). *)
(*   (* si x est une entrée *) *)
(*   exact (PROJ (DS_fam SI) x @_ SND _ _ @_ FST _ _ @_ FST _ _). *)
(*   (* sinon on le prend dans les ss *) *)
(*   exact (PROJ (DS_fam SI) x @_ env_of_np xs @_ ss). *)
(* Defined. *)

(* Section Equation_spec. *)

(* Lemma denot_equation_Oeq : *)
(*   forall ins xs es envG envI bs env, *)
(*     denot_equation ins (xs,es) envG envI bs env *)
(*     == denot_var ins envI (env_of_np xs (denot_exps ins es envG envI bs env)). *)
(* Proof. *)
(*   intros. *)
(*   apply Oprodi_eq_intro; intro x. *)
(*   unfold denot_equation, denot_var. *)
(*   Local Hint Rewrite (Dprodi_DISTR_simpl _ (DS_fam SI)) : cpodb. *)
(*   autorewrite with cpodb using (simpl (snd _); simpl (fst _)). *)
(*   cases. *)
(* Qed. *)

(* (* parfois plut utile car c'est une égalité *) *)
(* Lemma denot_equation_eq : *)
(*   forall ins xs es envG envI bs env x, *)
(*     denot_equation ins (xs,es) envG envI bs env x *)
(*     = denot_var ins envI (env_of_np xs (denot_exps ins es envG envI bs env)) x. *)
(* Proof. *)
(*   intros. *)
(*   unfold denot_equation, denot_var. *)
(*   Local Hint Rewrite (Dprodi_DISTR_simpl _ (DS_fam SI)) : cpodb. *)
(*   autorewrite with cpodb using (simpl (snd _); simpl (fst _)). *)
(*   cases. *)
(* Qed. *)

(* Global Opaque denot_equation. *)

(* Lemma denot_equation_input : *)
(*   forall e ins envG envI bs env x, *)
(*     wl_equation G e -> *)
(*     In x ins -> *)
(*     denot_equation ins e envG envI bs env x = envI x. *)
(* Proof. *)
(*   intros * Hwt Hx. *)
(*   apply mem_ident_spec in Hx. *)
(*   destruct e as (xs,es). *)
(*   destruct Hwt as [? Hwt]. *)
(*   rewrite annots_numstreams in Hwt. *)
(*   rewrite denot_equation_eq. *)
(*   unfold denot_var. *)
(*   cases; congruence. *)
(* Qed. *)

(* End Equation_spec. *)

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

(** [env_of_np_ext xs ss env] binds xs to ss in env *)
(* TODO: move ?? *)
Definition env_of_np_ext (l : list ident) {n} : nprod n -C-> DS_prod SI -C-> DS_prod SI :=
  curry (Dprodi_DISTR _ _ _
           (fun x => match mem_nth l x with
                  | Some n => get_nth n errTy @_ FST _ _
                  | None => PROJ _ x @_ SND _ _
                  end)).

Lemma env_of_np_ext_eq :
  forall l n (np : nprod n) env x,
    env_of_np_ext l np env x
    = match mem_nth l x with
      | Some n => get_nth n errTy np
      | None => env x
      end.
Proof.
  unfold env_of_np_ext.
  intros.
  autorewrite with cpodb.
  cases.
Qed.

(* signature : envG -> envI -> env -> env_acc -> env
    on utilise les 4 premiers arguments pour évaluer les expressions,
    et on ajoute les nouvelles associations à l'accumulateur *)
Definition denot_block (ins : list ident) (b : block) :
  Dprodi FI -C-> DS_prod SI -C-> DS_prod SI -C-> DS_prod SI -C-> DS_prod SI :=
  curry (curry (curry
    match b with
    | Beq (xs,es) => ((env_of_np_ext xs @2_
                        uncurry (uncurry (denot_exps ins es)) @_ FST _ _)
                       (SND _ _))
    | _ =>  SND _ _ (* garder l'accumulateur *)
    end)).

Lemma denot_block_eq :
  forall ins b envG envI env env_acc,
    denot_block ins b envG envI env env_acc
    = match b with
      | Beq (xs,es) => env_of_np_ext xs (denot_exps ins es envG envI env) env_acc
      | _ => env_acc
      end.
Proof.
  unfold denot_block; intros; cases.
Qed.

(* un genre de (fold denot_block) sur blks *)
Definition denot_blocks (ins : list ident) (blks : list block) :
  (*  envG -> envI -> env -> env *)
  Dprodi FI -C-> DS_prod SI -C-> DS_prod SI -C-> DS_prod SI.
  apply curry, curry.
  revert blks; fix denot_blocks 1.
  intros [| blk blks].
  - apply CTE, 0.
  - refine ((ID _ @2_ uncurry (uncurry (denot_block ins blk))) (denot_blocks blks)).
Defined.

Lemma denot_blocks_eq :
  forall ins envG envI env blks,
    denot_blocks ins blks envG envI env
    = fold_right (fun blk => denot_block ins blk envG envI env) 0 blks.
Proof.
  induction blks; simpl; auto.
  unfold denot_blocks at 1.
  setoid_rewrite <- IHblks.
  reflexivity.
Qed.

Corollary denot_blocks_eq_cons :
  forall ins envG envI env blk blks,
    denot_blocks ins (blk :: blks) envG envI env
    = denot_block ins blk envG envI env
        (denot_blocks ins blks envG envI env).
Proof.
  reflexivity.
Qed.

Definition denot_top_block (ins : list ident) (b : block) :
  (* envG -> envI -> env -> env *)
  Dprodi FI -C-> DS_prod SI -C-> DS_prod SI -C-> DS_prod SI :=
  match b with
  | Blocal (Scope _ blks) => denot_blocks ins blks
  | _ => 0
  end.

Lemma denot_top_block_eq :
  forall ins blk envG envI env,
    denot_top_block ins blk envG envI env
    = match blk with
      | Blocal (Scope _ blks) => denot_blocks ins blks envG envI env
      | _ => 0
      end.
Proof.
  intros.
  unfold denot_top_block.
  cases.
Qed.

Definition denot_node (n : node) :
  (* envG -> envI -> env -> env *)
  Dprodi FI -C-> DS_prod SI -C-> DS_prod SI -C-> DS_prod SI.
  apply curry.
  refine ((denot_top_block (List.map fst n.(n_in)) n.(n_block) @2_ _) _).
  - exact (FST _ _). (* envG *)
  - exact (SND _ _). (* envI *)
Defined.

Lemma denot_node_eq : forall n envG envI,
    let ins := List.map fst n.(n_in) in
    denot_node n envG envI = denot_top_block ins n.(n_block) envG envI.
Proof.
  reflexivity.
Qed.

(* (* inutile en fait ??? *) *)
(* Lemma denot_node_input : *)
(*   forall nd envG envI env x, *)
(*     wl_node G nd -> *)
(*     In x (List.map fst nd.(n_in)) -> *)
(*     denot_node nd envG envI env x = envI x. *)
(* Proof. *)
(*   intros * Hwl Hin. *)
(*   unfold denot_node, denot_block. *)
(*   inversion_clear Hwl as (?& Hwl'). *)
(*   inv Hwl'; auto. *)
(*   autorewrite with cpodb. *)
(*   simpl. cases. *)
(*   eapply denot_equation_input; eauto. *)
(* Qed. *)

End Denot_node.

(** After rewriting [denot_exp_eq] we often need to destruct [numstreams _]
    or [Nat.eq_dec _ _]. It does not work directly in general because
    the type of the denotation of subterms depends on these values.
    One way solve the problem is to revert the hypotheses and
    generalize the results of [denot_exp, denot_exps, denot_expss] on subterms
    with the following tactic.
 *)
(* remarque : un [simpl] avant [gen_sub_exps] peur être nécessaire, même si
   l'effet n'est pas visible *)
Ltac gen_sub_exps :=
  repeat match goal with
  | |- context [ ?f1 (?f2 (?f3 (denot_expss ?e1 ?e2 ?e3 ?e4) ?e5) ?e6) ?e7 ] =>
      generalize (f1 (f2 (f3 (denot_expss e1 e2 e3 e4) e5) e6) e7)
  | |- context [ ?f1 (?f2 (?f3 (denot_exps ?e1 ?e2 ?e3) ?e4) ?e5) ?e6 ] =>
      generalize (f1 (f2 (f3 (denot_exps e1 e2 e3) e4) e5) e6)
  | |- context [ ?f1 (?f2 (?f3 (denot_exp ?e1 ?e2 ?e3) ?e4) ?e5) ?e6 ] =>
      generalize (f1 (f2 (f3 (denot_exp e1 e2 e3) e4) e5) e6)
    end.


Section Global.

  Definition denot_global_ (G : global) : Dprodi FI -C-> Dprodi FI.
    apply Dprodi_DISTR; intro f.
    destruct (find_node f G).
    - exact (curry (FIXP _ @_ (denot_node G n @2_ FST _ _) (SND _ _))).
    - apply CTE, CTE, 0.
  Defined.

  Lemma denot_global_eq :
    forall G envG f envI,
      denot_global_ G envG f envI =
        match find_node f G with
        | Some n => FIXP _ (denot_node G n envG envI)
        | None => 0
        end.
  Proof.
    intros.
    unfold denot_global_.
    autorewrite with cpodb.
    cases.
  Qed.

  Definition denot_global G : Dprodi FI :=
    FIXP _ (denot_global_ G).

End Global.


Lemma denot_in :
  forall G f n,
    find_node f G = Some n ->
    forall envI x,
      In x (List.map fst (n_in n)) ->
      denot_global G f envI x == 0.
Proof.
  intros * Hfind * Hin.
  pose proof (Hnin := NoDup_get_defined_node n).
  unfold denot_global, get_defined_node in *.
  rewrite <- PROJ_simpl, <- PROJ_simpl, FIXP_eq, PROJ_simpl, PROJ_simpl.
  rewrite denot_global_eq, Hfind.
  rewrite <- PROJ_simpl, FIXP_eq, denot_node_eq, denot_top_block_eq, PROJ_simpl at 1.
  cases.
  remember (FIXP _ _) as envG eqn:HH; clear HH.
  remember (FIXP _ _) as env eqn:HH; clear HH.
  induction l0 as [| blk blks]; auto.
  simpl in Hnin; rewrite <- app_assoc in Hnin.
  rewrite denot_blocks_eq_cons, denot_block_eq.
  cases; simpl in Hnin.
  rewrite env_of_np_ext_eq.
  cases_eqn Hmem; eauto 3 using NoDup_app_r; exfalso.
  eapply NoDup_app_In; eauto using mem_nth_In, in_or_app.
Qed.

Lemma not_out_bot :
  forall G f n,
    find_node f G = Some n ->
    forall envI x,
      ~ In x (List.map fst (n_out n)) ->
      ~ In x (List.map fst (get_locals (n_block n))) ->
      denot_global G f envI x == 0.
Proof.
  intros * Hfind * Nout Nloc.
  assert (Hnin: ~ In x (get_defined_node n)).
  { intros Hin%get_defined_node_incl%in_app_iff; tauto. }
  clear Nout Nloc.
  unfold get_defined_node, denot_global, get_locals in *.
  rewrite <- PROJ_simpl, <- PROJ_simpl, FIXP_eq, PROJ_simpl, PROJ_simpl.
  rewrite denot_global_eq, Hfind.
  rewrite <- PROJ_simpl, FIXP_eq, PROJ_simpl.
  rewrite denot_node_eq, denot_top_block_eq.
  cases.
  remember (FIXP _ _) as envG eqn:HH; clear HH.
  remember (FIXP _ _) as env eqn:HH; clear HH.
  induction l0 as [| blk blks']; auto.
  simpl in Hnin; rewrite in_app_iff in Hnin.
  rewrite denot_blocks_eq_cons, denot_block_eq.
  cases_eqn HH; subst.
  rewrite env_of_np_ext_eq.
  cases_eqn Hmem; exfalso.
  apply mem_nth_In in Hmem; auto.
Qed.

(** *** Here we show that a node can be removed from the environment
    if it is not evaluated during the computations. *)
Section Denot_cons.

Lemma denot_exps_hyp :
  forall G G' ins es envG envI env,
    Forall (fun e => denot_exp G ins e envG envI env ==
                    denot_exp G' ins e envG envI env) es ->
    denot_exps G ins es envG envI env ==
      denot_exps G' ins es envG envI env.
Proof.
  induction es; intros * Heq. trivial.
  inversion Heq.
  rewrite 2 denot_exps_eq.
  apply nprod_app_Oeq_compat; auto.
Qed.

Lemma denot_exp_cons :
  forall nd nds tys exts
    ins envG envI env e,
    ~ Is_node_in_exp nd.(n_name) e ->
    denot_exp (Global tys exts nds) ins e envG envI env
    == denot_exp (Global tys exts (nd :: nds)) ins e envG envI env.
Proof.
  induction e using exp_ind2; intro Hnin.
  all: setoid_rewrite denot_exp_eq; auto 1.
  - (* unop *)
    revert IHe.
    gen_sub_exps.
    cases; simpl; intros.
    rewrite IHe; auto.
    intro H; apply Hnin; constructor; auto.
  - (* binop *)
    revert IHe1 IHe2.
    gen_sub_exps.
    cases; simpl; intros.
    rewrite IHe1, IHe2; auto.
    all: intro H; apply Hnin; constructor; auto.
  - (* fby *)
    assert (denot_exps (Global tys exts nds) ins e0s envG envI env
            == denot_exps (Global tys exts (nd::nds)) ins e0s envG envI env) as He0s.
    { apply denot_exps_hyp.
      simpl_Forall.
      apply H; contradict Hnin.
      constructor; left; solve_Exists. }
    assert (denot_exps (Global tys exts nds) ins es envG envI env
            == denot_exps (Global tys exts (nd::nds)) ins es envG envI env) as Hes.
    { apply denot_exps_hyp.
      simpl_Forall.
      apply H0; contradict Hnin.
      constructor; right; solve_Exists. }
    revert He0s Hes; simpl; unfold eq_rect.
    gen_sub_exps; cases.
  - (* when *)
    assert (denot_exps (Global tys exts nds) ins es envG envI env
            == denot_exps (Global tys exts (nd::nds)) ins es envG envI env) as Hes.
    { apply denot_exps_hyp.
      simpl_Forall.
      apply H; contradict Hnin.
      constructor; solve_Exists. }
    revert Hes; simpl; unfold eq_rect.
    gen_sub_exps; cases.
  - (* merge *)
    destruct a as [tyss c].
    assert (denot_expss (Global tys exts nds) ins es (length tyss) envG envI env
            == denot_expss (Global tys exts (nd::nds)) ins es (length tyss) envG envI env) as Hess.
    { induction es as [| [i es] ies]. trivial.
      inv H.
      assert (denot_exps (Global tys exts nds) ins es envG envI env
              == denot_exps (Global tys exts (nd::nds)) ins es envG envI env) as Hes.
      { apply denot_exps_hyp.
        simpl_Forall.
        apply H2; contradict Hnin.
        constructor; solve_Exists. }
      rewrite 2 denot_expss_eq.
      revert Hes; unfold eq_rect.
      destruct (Nat.eq_dec _ _); try trivial.
      rewrite IHies; cases; auto.
      contradict Hnin; inv Hnin.
      constructor; now right. }
    revert Hess; simpl; unfold eq_rect_r, eq_rect, eq_sym.
    gen_sub_exps; cases.
  - (* case *)
    destruct a as [tyss c].
    assert (denot_expss (Global tys exts nds) ins es (length tyss) envG envI env
            == denot_expss (Global tys exts (nd::nds)) ins es (length tyss) envG envI env) as Hess.
    { induction es as [| [i es] ies]. trivial.
      inv H.
      assert (denot_exps (Global tys exts nds) ins es envG envI env
              == denot_exps (Global tys exts (nd::nds)) ins es envG envI env) as Hes.
      { apply denot_exps_hyp.
        simpl_Forall.
        apply H3; contradict Hnin.
        constructor; right; left; solve_Exists. }
      rewrite 2 denot_expss_eq.
      revert Hes; unfold eq_rect.
      destruct (Nat.eq_dec _ _); try trivial.
      rewrite IHies; cases; auto.
      contradict Hnin; inv Hnin.
      destruct H2 as [|[]]; constructor; auto. }
    revert Hess; simpl; unfold eq_rect_r, eq_rect, eq_sym.
    revert IHe.
    gen_sub_exps.
    intros; destruct d as [esd|]; cases.
    + (* défaut *)
      assert (denot_exps (Global tys exts nds) ins esd envG envI env
              == denot_exps (Global tys exts (nd::nds)) ins esd envG envI env) as Hesd.
      { apply denot_exps_hyp.
        simpl_Forall.
        apply H0; contradict Hnin.
        constructor; right; right; esplit; split; eauto; solve_Exists. }
      rewrite Hesd, IHe; auto.
      contradict Hnin.
      constructor; auto.
    + (* total *)
      rewrite IHe; auto.
      contradict Hnin.
      constructor; auto.
  - (* eapp, seul cas intéressant *)
    simpl.
    destruct (ident_eq_dec nd.(n_name) f) as [|Hf]; subst.
    { (* si oui, contradiction *)
      contradict Hnin. apply INEapp2. }
    rewrite (find_node_other _ _ _ _ _ Hf).
    assert (denot_exps (Global tys exts nds) ins es envG envI env
            == denot_exps (Global tys exts (nd::nds)) ins es envG envI env) as Hes.
    { apply denot_exps_hyp.
      simpl_Forall.
      apply H; contradict Hnin.
      constructor; left; solve_Exists. }
    assert (denot_exps (Global tys exts nds) ins er envG envI env
            == denot_exps (Global tys exts (nd::nds)) ins er envG envI env) as Her.
    { apply denot_exps_hyp.
      simpl_Forall.
      apply H0; contradict Hnin.
      constructor; right; solve_Exists. }
    revert Hes Her; simpl; unfold eq_rect.
    gen_sub_exps; cases.
    now intros ???? -> ->.
Qed.

Corollary denot_exps_cons :
  forall nd nds tys exts
    ins envG envI env es,
    ~ (List.Exists (Is_node_in_exp nd.(n_name)) es) ->
    denot_exps (Global tys exts nds) ins es envG envI env
    == denot_exps (Global tys exts (nd :: nds)) ins es envG envI env.
Proof.
  induction es; intros Hnin.
  - now rewrite 2 denot_exps_nil.
  - rewrite 2 denot_exps_eq.
    apply nprod_app_Oeq_compat; auto using denot_exp_cons.
Qed.

Lemma denot_block_cons :
  forall nd nds tys exts
    ins envG envI env env_acc blk,
    ~ Is_node_in_block (n_name nd) blk ->
    denot_block (Global tys exts nds) ins blk envG envI env env_acc
    == denot_block (Global tys exts (nd :: nds)) ins blk envG envI env env_acc.
Proof.
  intros * Hnin.
  rewrite 2 denot_block_eq.
  cases.
  rewrite denot_exps_cons; auto.
  contradict Hnin.
  constructor; auto.
Qed.

Corollary denot_blocks_cons :
  forall nd nds tys exts
    ins envG envI env blks,
    ~ (List.Exists (Is_node_in_block (n_name nd)) blks) ->
    denot_blocks (Global tys exts nds) ins blks envG envI env
    == denot_blocks (Global tys exts (nd :: nds)) ins blks envG envI env.
Proof.
  intros * Hnin.
  rewrite 2 denot_blocks_eq.
  induction blks; simpl. reflexivity.
  rewrite IHblks.
  apply denot_block_cons.
  all: contradict Hnin; auto.
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
  1-5: trivial.
  destruct s as [vars blks]; simpl.
  apply fcont_eq_intro; intro envG.
  apply fcont_eq_intro; intro envI.
  apply fcont_eq_intro; intro env.
  autorewrite with cpodb; simpl.
  apply denot_blocks_cons.
  contradict Hnin.
  now constructor; constructor.
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
