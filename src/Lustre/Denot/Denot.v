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

Context {Prefs : PS.t}.

(* [nolocal] pour des variables locales à top-level seulement
   et pas de last dans les variables de sortie
   FIXME: c'est ce qu'il y avait dans Vélus avant le commit 2370699a
 *)
Inductive nolocal_top_block : block -> Prop :=
| NLtop : forall locs blks,
    Forall (fun '(_, (_, _, _, o)) => o = None) locs ->
    Forall nolocal_block blks ->
    nolocal_top_block (Blocal (Scope locs blks)).
Inductive nolocal : list decl -> block -> Prop :=
  | NLnode : forall out blk,
      Forall (fun '(_, (_, _, _, o)) => o = None) out ->
      nolocal_top_block blk ->
      (exists xs, VarsDefinedComp blk xs /\ Permutation.Permutation xs (List.map fst out)) ->
      nolocal out blk.

Definition node := @node nolocal Prefs.
Definition global := @global nolocal Prefs.

(** We always use this specialized version of mem_nth *)
(* TODO: c'est vraiment une bonne idée de redéfinir des trucs, comme ça ? *)
Definition mem_nth := mem_nth ident ident_eq_dec.

Definition errTy : DS (sampl value) := DS_const (err error_Ty).
Definition abss  : DS (sampl value) := DS_const abs.


(** ** Denotational environments (local & program-wide) *)
Section Denot_env.

Definition SI := fun _ : ident => sampl value.
Definition FI := fun _ : ident => (DS_prod SI -C-> DS_prod SI).

Definition err_env : DS_prod SI := fun _ => errTy.
Definition abs_env : DS_prod SI := fun _ => abss.

(** build an environment from a tuple of streams, with names given in [l] *)
Definition env_of_np (l : list ident) {n} : nprod n -C-> DS_prod SI :=
  Dprodi_DISTR _ _ _
    (fun x => match mem_nth l x with
           | Some n => get_nth n errTy
           | None => CTE _ _ abss
           end).

Lemma env_of_np_eq :
  forall l n (ss : nprod n) x,
    env_of_np l ss x =
      match mem_nth l x with
      | Some n => get_nth n errTy ss
      | None => abss
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

Lemma env_of_np_inf :
  forall l n (np : nprod n),
    forall_nprod (@infinite _) np ->
    all_infinite (env_of_np l np).
Proof.
  clear.
  unfold env_of_np.
  intros * ??.
  setoid_rewrite Dprodi_DISTR_simpl.
  cases_eqn HH.
  - apply forall_nprod_k_def; auto. apply DS_const_inf.
  - apply DS_const_inf.
Qed.

Lemma forall_env_of_np :
  forall (P : DS (sampl value) -> Prop) l {n} (ss : nprod n),
    P errTy ->
    P abss ->
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
  - apply CTE, abss.
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
      Dprod (Dprod (Dprod (Dprodi FI) (DS_prod SI)) (DS bool)) (DS_prod SI) -C->
      @nprod (DS (sampl value)) (numstreams e).

  Definition denot_exps_ (es : list exp) :
    Dprod (Dprod (Dprod (Dprodi FI) (DS_prod SI)) (DS bool)) (DS_prod SI) -C->
    @nprod (DS (sampl value)) (list_sum (List.map numstreams es)).
    induction es as [|a].
    + exact (CTE _ _ abss).
    + exact ((nprod_app @2_ (denot_exp_ a)) IHes).
  Defined.

  (* vérifie que chaque sous-liste d'expressions calcule exactement n flots et
   retourne un produit d'éléments de type (nprod n) *)
  (* FIXME: ess n'a pas le type list(list exp) car ça empêche la décroissance
   syntaxique lors de son appel dans denot_exp_ *)
  Definition denot_expss_ {A} (ess : list (A * list exp)) (n : nat) :
    Dprod (Dprod (Dprod (Dprodi FI) (DS_prod SI)) (DS bool)) (DS_prod SI) -C->
    @nprod (@nprod (DS (sampl value)) n) (length ess).
    induction ess as [|[? es]].
    + exact (CTE _ _ (nprod_const (nprod_const abss _) _)).
    + destruct (Nat.eq_dec (list_sum (List.map numstreams es)) n) as [<-|].
      * exact ((nprod_cons @2_ (denot_exps_ es)) IHess).
      * exact (CTE _ _ (nprod_const (nprod_const abss _) _)).
  Defined.

End Denot_exps.


Definition denot_exp_ (ins : list ident)
  (e : exp) :
  (* (nodes * inputs * base clock * env) -> streams *)
  Dprod (Dprod (Dprod (Dprodi FI) (DS_prod SI)) (DS bool)) (DS_prod SI) -C->
  @nprod (DS (sampl value)) (numstreams e).

  set (ctx := Dprod _ _).
  epose (denot_var :=
       fun x => if mem_ident x ins
             then PROJ (DS_fam SI) x @_ SND _ _ @_ FST _ _ @_ FST _ _
             else PROJ (DS_fam SI) x @_ SND _ _).
  revert e.
  fix denot_exp_ 1.
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
    apply CTE, errTy.
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
    2,3: apply CTE, (nprod_const errTy).
    rewrite Heq1 in ss.
    rewrite <- Heq2.
    exact ((lift2 (SDfuns.fby) @2_ s0s) ss).
  - (* Earrow *)
    apply CTE, (nprod_const errTy).
  - (* Ewhen *)
    rename l into es.
    destruct l0 as (tys,ck).
    destruct p as (i,ty). clear He.
    destruct (Nat.eq_dec
                (list_sum (List.map numstreams es))
                (length tys)
             ) as [<-|].
    2: apply CTE, (nprod_const errTy).
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
      2: apply CTE, CTE, (nprod_const errTy).
      intro ses.
      refine ((_ @2_ (denot_exp_ e0)) ((nprod_cons @2_ denot_exps_ denot_exp_ d_es) ses)).
      destruct (numstreams e0) as [|[]].
      1,3: apply CTE, CTE, (nprod_const errTy).
      exact (lift_nprod @_ scase_defv (List.map fst ies)).
    + (* case total *)
      (* condition, branches *)
      refine ((_ @2_ (denot_exp_ e0)) ses).
      destruct (numstreams e0) as [|[]].
      1,3: apply CTE, CTE, (nprod_const errTy).
      exact (lift_nprod @_ (scasev (List.map fst ies))).
  - (* Eapp *)
    rename l into es, l0 into er, l1 into anns.
    clear He.
    destruct (find_node i G) as [n|].
    destruct (Nat.eq_dec (length (List.map fst n.(n_out))) (length anns)) as [<-|].
    2,3: apply CTE, (nprod_const errTy).
    (* dénotation du nœud *)
    pose (f := PROJ _ i @_ FST _ _ @_ FST _ _ @_ FST _ _ : ctx -C-> FI i).
    pose (ss := denot_exps_ denot_exp_ es).
    pose (rs := denot_exps_ denot_exp_ er).
    (* chaînage *)
    refine
      (np_of_env (List.map fst (n_out n)) @_
         (sreset @3_ f) (sbools_of @_ rs) (env_of_np (idents (n_in n)) @_ ss)).
Defined.

Definition denot_exp (ins : list ident) (e : exp) :
  (* (nodes * inputs * base clock * env) -> streams *)
  Dprodi FI -C-> DS_prod SI -C-> DS bool -C-> DS_prod SI -C-> nprod (numstreams e) :=
  curry (curry (curry (denot_exp_ ins e))).

Definition denot_exps (ins : list ident) (es : list exp) :
  Dprodi FI -C-> DS_prod SI -C-> DS bool -C-> DS_prod SI -C-> nprod (list_sum (List.map numstreams es)) :=
  curry (curry (curry (denot_exps_ (denot_exp_ ins) es))).

Lemma denot_exps_eq :
  forall ins e es envG envI bs env,
    denot_exps ins (e :: es) envG envI bs env
    = nprod_app (denot_exp ins e envG envI bs env) (denot_exps ins es envG envI bs env).
Proof.
  trivial.
Qed.

Lemma forall_denot_exps :
  forall (P : DS (sampl value) -> Prop) ins es envG envI bs env,
    forall_nprod P (denot_exps ins es envG envI bs env)
    <-> Forall (fun e => forall_nprod P (denot_exp ins e envG envI bs env)) es.
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
  Dprodi FI -C-> DS_prod SI -C-> DS bool -C-> DS_prod SI -C->
  @nprod (@nprod (DS (sampl value)) n) (length ess) :=
  curry (curry (curry (denot_expss_ (denot_exp_ ins) ess n))).

Lemma denot_expss_eq :
  forall A ins (x : A) es ess envG envI bs env n,
    denot_expss ins ((x,es) :: ess) n envG envI bs env
    = match Nat.eq_dec (list_sum (List.map numstreams es)) n with
      | left eqn =>
          nprod_cons
            (eq_rect _ nprod (denot_exps ins es envG envI bs env) _ eqn)
            (denot_expss ins ess n envG envI bs env)
      | _ => nprod_const (nprod_const abss _) _
      end.
Proof.
  intros.
  unfold denot_expss, denot_expss_, denot_exps at 1.
  simpl (list_rect _ _ _ _).
  generalize (denot_exps_ (denot_exp_ ins) es); intro.
  cases; auto.
  destruct e; cases.
Qed.

Lemma forall_denot_expss :
  forall A ins (ess : list (A * list exp)) n envG envI bs env (P : nprod n -> Prop),
    Forall (fun es =>
              match Nat.eq_dec (list_sum (List.map numstreams es)) n with
              | left eqn =>
                  P (eq_rect _ nprod (denot_exps ins es envG envI bs env) n eqn)
              | _ => P (nprod_const abss n)
              end) (List.map snd ess) ->
    forall_nprod P (denot_expss ins ess n envG envI bs env).
Proof.
  induction ess as [|[]]; intros * Hf; inv Hf.
  - simpl; auto.
  - rewrite denot_expss_eq.
    unfold eq_rect in *.
    cases; eauto using forall_nprod_const, forall_nprod_cons.
Qed.

Lemma forall_forall_denot_expss :
  forall A ins (ess : list (A * list exp)) n envG envI bs env (P : DS (sampl value) -> Prop),
    P abss ->
    Forall (fun es => forall_nprod P (denot_exps ins (snd es) envG envI bs env)) ess ->
    forall_nprod (forall_nprod P) (denot_expss ins ess n envG envI bs env).
Proof.
  induction ess as [|[]]; intros * Herr Hf; inv Hf.
  - simpl; auto.
  - rewrite denot_expss_eq.
    unfold eq_rect in *.
    cases; eauto using forall_nprod_const, forall_nprod_cons.
Qed.

Lemma Forall_denot_expss :
  forall A P ins (es : list (A * list exp)) n envG envI bs env,
    Forall (fun es => length (annots (snd es)) = n) es ->
    forall_nprod (forall_nprod P) (denot_expss ins es n envG envI bs env)
    <-> Forall (fun l => Forall (fun e => forall_nprod P (denot_exp ins e envG envI bs env)) l) (List.map snd es).
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
  forall ins envG envI bs env,
    denot_exps ins [] envG envI bs env = abss.
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
      | Ebinop op e1 e2 an =>
          let se1 := denot_exp ins e1 envG envI bs env in
          let se2 := denot_exp ins e2 envG envI bs env in
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
          let s0s := denot_exps ins e0s envG envI bs env in
          let ss := denot_exps ins es envG envI bs env in
          let n := (list_sum (List.map numstreams e0s)) in
          let m := (list_sum (List.map numstreams es)) in
          match Nat.eq_dec m n, Nat.eq_dec n (length an) with
          | left eqm, left eqan =>
              eq_rect _ nprod (lift2 (SDfuns.fby) s0s (eq_rect _ nprod ss _ eqm)) _ eqan
          | _, _ => nprod_const errTy _
          end
      (* | Earrow _ e0 e => *)
      (*     lift2 s (@arrow) _ (denot_exp e0 genv env bs) (denot_exp e genv env bs) *)
      (* | Epair _ _ e1 e2 => *)
      (*     PAIR_flat s _ _ (denot_exp e1 genv env bs) (denot_exp e2 genv env bs) *)
      | Ewhen es (x,_) k (tys,_) =>
          let ss := denot_exps ins es envG envI bs env in
          match Nat.eq_dec (list_sum (List.map numstreams es)) (length tys) with
          | left eqn =>
              eq_rect _ nprod (llift (swhenv k) ss (denot_var ins envI env x)) _ eqn
          | _ => nprod_const errTy _
          end
      | Emerge (x,_) ies (tys,_) =>
          let ss := denot_expss ins ies (length tys) envG envI bs env in
          let ss := eq_rect_r nprod ss (map_length _ _) in
          lift_nprod (smergev (List.map fst ies) (denot_var ins envI env x)) ss
      | Ecase ec ies None (tys,_) =>
          let ss := denot_expss ins ies (length tys) envG envI bs env in
          let ss := eq_rect_r nprod ss (map_length _ _) in
          let cs := denot_exp ins ec envG envI bs env in
          match numstreams ec as n return nprod n -> _ with
          | 1 => fun cs => lift_nprod (scasev (List.map fst ies) cs) ss
          | _ => fun _ => nprod_const errTy _
          end cs
      | Ecase ec ies (Some eds) (tys,_) =>
          let ss := denot_expss ins ies (length tys) envG envI bs env in
          let ss := eq_rect_r nprod ss (map_length _ _) in (* branches *)
          let cs := denot_exp ins ec envG envI bs env in (* condition *)
          let ds := denot_exps ins eds envG envI bs env in (* défaut *)
          match numstreams ec as n, Nat.eq_dec (list_sum (List.map numstreams eds)) (length tys) return nprod n -> _ with
          | 1, left eqm =>
              fun cs => lift_nprod (scase_defv (List.map fst ies) cs)
                       (nprod_cons (eq_rect _ nprod ds _ eqm) ss)
          | _,_ => fun _ => nprod_const errTy _
          end cs
      | Eapp f es er an =>
          let ss := denot_exps ins es envG envI bs env in
          let rs := denot_exps ins er envG envI bs env in
          match find_node f G with
          | Some n =>
              match Nat.eq_dec (length (List.map fst n.(n_out))) (length an) with
              | left eqan =>
                  eq_rect _ nprod
                    (np_of_env (List.map fst n.(n_out)) (sreset (envG f) (sbools_of rs) (env_of_np (idents n.(n_in)) ss)))
                    _ eqan
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
  - (* Ebinop *)
    unfold denot_exp, denot_exp_ at 1.
    fold (denot_exp_ ins e1) (denot_exp_ ins e2).
    autorewrite with cpodb using (simpl (fst _); simpl (snd _)).
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
    autorewrite with cpodb.
    simpl; destruct e.
    now autorewrite with cpodb.
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

(* signature : envG -> envI -> bs -> env -> env_acc -> env
    on utilise les 4 premiers arguments pour évaluer les expressions,
    et on ajoute les nouvelles associations à l'accumulateur *)
Definition denot_block (ins : list ident) (b : block) :
  Dprodi FI -C-> DS_prod SI -C-> DS bool -C-> DS_prod SI -C-> DS_prod SI -C-> DS_prod SI :=
  curry (curry (curry (curry
    match b with
    | Beq (xs,es) => ((env_of_np_ext xs @2_
                        uncurry (uncurry (uncurry (denot_exps ins es))) @_ FST _ _)
                       (SND _ _))
    | _ =>  SND _ _ (* garder l'accumulateur *)
    end))).

Lemma denot_block_eq :
  forall ins b envG envI bs env env_acc,
    denot_block ins b envG envI bs env env_acc
    = match b with
      | Beq (xs,es) => env_of_np_ext xs (denot_exps ins es envG envI bs env) env_acc
      | _ => env_acc
      end.
Proof.
  unfold denot_block; intros; cases.
Qed.

(* un genre de (fold denot_block) sur blks *)
Definition denot_blocks (ins : list ident) (blks : list block) :
  (*  envG -> envI -> bs -> env -> env *)
  Dprodi FI -C-> DS_prod SI -C-> DS bool -C-> DS_prod SI -C-> DS_prod SI.
  apply curry, curry, curry.
  revert blks; fix denot_blocks 1.
  intros [| blk blks].
  - apply (CTE _ _ abs_env).
  - refine ((ID _ @2_ uncurry (uncurry (uncurry (denot_block ins blk)))) (denot_blocks blks)).
Defined.

Lemma denot_blocks_eq :
  forall ins envG envI bs env blks,
    denot_blocks ins blks envG envI bs env
    = fold_right (fun blk => denot_block ins blk envG envI bs env) abs_env blks.
Proof.
  induction blks; simpl; auto.
  unfold denot_blocks at 1.
  setoid_rewrite <- IHblks.
  reflexivity.
Qed.

Corollary denot_blocks_eq_cons :
  forall ins envG envI bs env blk blks,
    denot_blocks ins (blk :: blks) envG envI bs env
    = denot_block ins blk envG envI bs env
        (denot_blocks ins blks envG envI bs env).
Proof.
  trivial.
Qed.

Definition denot_top_block (ins : list ident) (b : block) :
  (* envG -> envI -> bs -> env -> env *)
  Dprodi FI -C-> DS_prod SI -C-> DS bool -C-> DS_prod SI -C-> DS_prod SI :=
  match b with
  | Blocal (Scope _ blks) => denot_blocks ins blks
  | _ => curry (curry (curry (SND _ _ @_ FST _ _ @_ FST _ _))) (* garder les entrées *)
  end.

Lemma denot_top_block_eq :
  forall ins blk envG envI bs env,
    denot_top_block ins blk envG envI bs env
    = match blk with
      | Blocal (Scope _ blks) => denot_blocks ins blks envG envI bs env
      | _ => envI
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
  refine ((denot_top_block (List.map fst n.(n_in)) n.(n_block) @3_ _) _ _).
  - exact (FST _ _). (* envG *)
  - exact (SND _ _). (* envI *)
  - exact (bss (List.map fst n.(n_in)) @_ SND _ _).
Defined.

Lemma denot_node_eq : forall n envG envI,
    let ins := List.map fst n.(n_in) in
    denot_node n envG envI = denot_top_block ins n.(n_block) envG envI (bss ins envI).
Proof.
  trivial.
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
  | |- context [ ?f1 (?f2 (?f3 (?f4 (denot_expss ?e1 ?e2 ?e3 ?e4) ?e5) ?e6) ?e7) ?e8 ] =>
      generalize (f1 (f2 (f3 (f4 (denot_expss e1 e2 e3 e4) e5) e6) e7) e8)
  | |- context [ ?f1 (?f2 (?f3 (?f4 (denot_exps ?e1 ?e2 ?e3) ?e4) ?e5) ?e6) ?e7 ] =>
      generalize (f1 (f2 (f3 (f4 (denot_exps e1 e2 e3) e4) e5) e6) e7)
  | |- context [ ?f1 (?f2 (?f3 (?f4 (denot_exp ?e1 ?e2 ?e3) ?e4) ?e5) ?e6) ?e7 ] =>
      generalize (f1 (f2 (f3 (f4 (denot_exp e1 e2 e3) e4) e5) e6) e7)
    end.


Section Global.

  Definition denot_global_ (G : global) : Dprodi FI -C-> Dprodi FI.
    apply Dprodi_DISTR; intro f.
    destruct (find_node f G).
    - exact (curry (FIXP _ @_ (denot_node G n @2_ FST _ _) (SND _ _))).
    - apply CTE, CTE, err_env.
  Defined.

  Lemma denot_global_eq :
    forall G envG f envI,
      denot_global_ G envG f envI =
        match find_node f G with
        | Some n => FIXP _ (denot_node G n envG envI)
        | None => err_env
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
| restr_Binop :
  forall op e1 e2 ann,
    restr_exp e1 ->
    restr_exp e2 ->
    restr_exp (Ebinop op e1 e2 ann)
| restr_Efby :
  forall e0s es anns,
    Forall restr_exp e0s ->
    Forall restr_exp es ->
    restr_exp (Efby e0s es anns)
| restr_Ewhen :
  forall es x k anns,
    Forall restr_exp es ->
    restr_exp (Ewhen es x k anns)
| restr_Emerge :
  forall x ess a,
    Forall (Forall restr_exp) (List.map snd ess) ->
    restr_exp (Emerge x ess a)
| restr_Ecase :
  forall e ess a,
    restr_exp e ->
    Forall (Forall restr_exp) (List.map snd ess) ->
    restr_exp (Ecase e ess None a)
| restr_Ecase_def :
  forall e ess des a,
    restr_exp e ->
    Forall (Forall restr_exp) (List.map snd ess) ->
    Forall restr_exp des ->
    restr_exp (Ecase e ess (Some des) a)
| restr_Eapp :
  forall f es er anns,
    Forall restr_exp es ->
    Forall restr_exp er ->
    restr_exp (Eapp f es er anns)
.

Inductive restr_block : block -> Prop :=
| restr_Beq :
  forall xs es,
    Forall restr_exp es ->
    restr_block (Beq (xs,es)).

Inductive restr_top_block : block -> Prop :=
| restr_Blocal :
  forall vars blks,
    Forall restr_block blks ->
    restr_top_block (Blocal (Scope vars blks)).

Definition restr_node (nd : node) : Prop :=
  restr_top_block nd.(n_block).

Definition restr_global (g : global) : Prop :=
  Forall restr_node g.(nodes).

End Temp.


(** *** Here we show that a node can be removed from the environment
    if it is not evaluated during the computations. *)
Section Denot_cons.

Lemma denot_exps_hyp :
  forall G G' ins es envG envI bs env,
    Forall (fun e => denot_exp G ins e envG envI bs env ==
                    denot_exp G' ins e envG envI bs env) es ->
    denot_exps G ins es envG envI bs env ==
      denot_exps G' ins es envG envI bs env.
Proof.
  induction es; intros * Heq. trivial.
  inversion Heq.
  rewrite 2 denot_exps_eq.
  apply nprod_app_Oeq_compat; auto.
Qed.

Lemma denot_exp_cons :
  forall nd nds tys exts
    ins envG envI bs env e,
    ~ Is_node_in_exp nd.(n_name) e ->
    denot_exp (Global tys exts nds) ins e envG envI bs env
    == denot_exp (Global tys exts (nd :: nds)) ins e envG envI bs env.
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
    assert (denot_exps (Global tys exts nds) ins e0s envG envI bs env
            == denot_exps (Global tys exts (nd::nds)) ins e0s envG envI bs env) as He0s.
    { apply denot_exps_hyp.
      simpl_Forall.
      apply H; contradict Hnin.
      constructor; left; solve_Exists. }
    assert (denot_exps (Global tys exts nds) ins es envG envI bs env
            == denot_exps (Global tys exts (nd::nds)) ins es envG envI bs env) as Hes.
    { apply denot_exps_hyp.
      simpl_Forall.
      apply H0; contradict Hnin.
      constructor; right; solve_Exists. }
    revert He0s Hes; simpl; unfold eq_rect.
    gen_sub_exps; cases.
  - (* when *)
    assert (denot_exps (Global tys exts nds) ins es envG envI bs env
            == denot_exps (Global tys exts (nd::nds)) ins es envG envI bs env) as Hes.
    { apply denot_exps_hyp.
      simpl_Forall.
      apply H; contradict Hnin.
      constructor; solve_Exists. }
    revert Hes; simpl; unfold eq_rect.
    gen_sub_exps; cases.
  - (* merge *)
    destruct a as [tyss c].
    assert (denot_expss (Global tys exts nds) ins es (length tyss) envG envI bs env
            == denot_expss (Global tys exts (nd::nds)) ins es (length tyss) envG envI bs env) as Hess.
    { induction es as [| [i es] ies]. trivial.
      inv H.
      assert (denot_exps (Global tys exts nds) ins es envG envI bs env
              == denot_exps (Global tys exts (nd::nds)) ins es envG envI bs env) as Hes.
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
    assert (denot_expss (Global tys exts nds) ins es (length tyss) envG envI bs env
            == denot_expss (Global tys exts (nd::nds)) ins es (length tyss) envG envI bs env) as Hess.
    { induction es as [| [i es] ies]. trivial.
      inv H.
      assert (denot_exps (Global tys exts nds) ins es envG envI bs env
              == denot_exps (Global tys exts (nd::nds)) ins es envG envI bs env) as Hes.
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
      assert (denot_exps (Global tys exts nds) ins esd envG envI bs env
              == denot_exps (Global tys exts (nd::nds)) ins esd envG envI bs env) as Hesd.
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
    assert (denot_exps (Global tys exts nds) ins es envG envI bs env
            == denot_exps (Global tys exts (nd::nds)) ins es envG envI bs env) as Hes.
    { apply denot_exps_hyp.
      simpl_Forall.
      apply H; contradict Hnin.
      constructor; left; solve_Exists. }
    assert (denot_exps (Global tys exts nds) ins er envG envI bs env
            == denot_exps (Global tys exts (nd::nds)) ins er envG envI bs env) as Her.
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
    ins envG envI bs env es,
    ~ (List.Exists (Is_node_in_exp nd.(n_name)) es) ->
    denot_exps (Global tys exts nds) ins es envG envI bs env
    == denot_exps (Global tys exts (nd :: nds)) ins es envG envI bs env.
Proof.
  induction es; intros Hnin.
  - now rewrite 2 denot_exps_nil.
  - rewrite 2 denot_exps_eq.
    apply nprod_app_Oeq_compat; auto using denot_exp_cons.
Qed.

Lemma denot_block_cons :
  forall nd nds tys exts
    ins envG envI bs env env_acc blk,
    ~ Is_node_in_block (n_name nd) blk ->
    denot_block (Global tys exts nds) ins blk envG envI bs env env_acc
    == denot_block (Global tys exts (nd :: nds)) ins blk envG envI bs env env_acc.
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
    ins envG envI bs env blks,
    ~ (List.Exists (Is_node_in_block (n_name nd)) blks) ->
    denot_blocks (Global tys exts nds) ins blks envG envI bs env
    == denot_blocks (Global tys exts (nd :: nds)) ins blks envG envI bs env.
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
