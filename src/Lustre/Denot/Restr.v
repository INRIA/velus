From Coq Require Import List Permutation.
From Velus Require Import Common Ident Operators Clocks StaticEnv FunctionalEnvironment LSyntax.
Require Import CommonList2.

Import ListNotations.

(** * La restriction syntaxique actuelle du modèle dénotationnel *)

Module Type LRESTR
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Senv  : STATICENV     Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX       Ids Op OpAux Cks Senv).

Inductive restr_exp : exp -> Prop :=
| restr_Econst :
  forall c,
    restr_exp (Econst c)
| restr_Eenum :
  forall c ty,
    restr_exp (Eenum c ty)
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

(** naturellement [Syn.nolocal_block]  *)
Inductive restr_block : block -> Prop :=
| restr_Beq :
  forall xs es,
    Forall restr_exp es ->
    restr_block (Beq (xs,es)).

(** encode en même temps [Syn.nolocal_top_block] *)
Inductive restr_top_block : block -> Prop :=
| restr_Blocal :
  forall locs blks,
    Forall restr_block blks ->
    Forall (fun '(_, (_, _, _, o)) => o = None) locs ->
    restr_top_block (Blocal (Scope locs blks)).


(** encode en même temps [Syn.nolocal] pour des variables locales
 à top-level seulement et pas de last dans les variables de sortie
 FIXME: c'est ce qu'il y avait dans Vélus avant le commit 2370699a *)
Inductive restr_node {PSyn Prefs} : @node PSyn Prefs -> Prop :=
| restr_N :
  forall nd,
    Forall (fun '(_, (_, _, _, o)) => o = None) nd.(n_out) ->
    restr_top_block nd.(n_block) ->
    (exists xs, VarsDefinedComp nd.(n_block) xs /\ Permutation xs (map fst nd.(n_out))) ->
    restr_node nd.

Definition restr_global {PSyn Prefs} (G : @global PSyn Prefs) : Prop :=
  Forall restr_node G.(nodes).

Lemma restr_global_find :
  forall {PSyn Prefs} (G : @global PSyn Prefs) f n,
    restr_global G ->
    find_node f G = Some n ->
    restr_node n.
Proof.
  destruct G as [?? nds].
  induction nds; simpl; intros * Hr Hf; inv Hf; inv Hr.
  apply find_node_cons in H0 as [[]|[]]; subst; eauto.
Qed.


(** Procédure de décision pour établir l'appartenance à la restriction *)

Fixpoint check_exp (e : exp) :=
  match e with
  | Econst _ => true
  | Eenum _ _ => true
  | Evar _ _ => true
  | Elast _ _ => false (* restr *)
  | Eunop op e ann => check_exp e
  | Ebinop op e1 e2 ann => check_exp e1 && check_exp e2
  | Eextcall _ _ _ => false (* restr *)
  | Efby e0s es ann => forallb check_exp e0s && forallb check_exp es
  | Earrow e0s es ann => false (* restr *)
  | Ewhen es _ t ann => forallb check_exp es
  | Emerge _ ess ann => forallb (fun '(t,es) => forallb check_exp es) ess
  | Ecase e ess None ann => check_exp e && forallb (fun '(t,es) => forallb check_exp es) ess
  | Ecase e ess (Some des) ann => check_exp e && forallb (fun '(t,es) => forallb check_exp es) ess && forallb check_exp des
  | Eapp f es er ann => forallb check_exp es && forallb check_exp er
  end.

Definition check_block b :=
  match b with
  | Beq (_, es) => forallb check_exp es
  | _ => false
  end.

Definition check_top_block b :=
  match b with
  | Blocal (Scope locs blks) =>
      forallb check_block blks
      && forallb (fun '(_, (_, _, _, o)) => isNone o) locs
  | _ => false
  end.

Definition check_node {PSyn Prefs} (n : @node PSyn Prefs) :=
  check_top_block (n_block n)
  && forallb (fun '(_, (_, _, _, o)) => isNone o) (n_out n).

Definition check_global {PSyn Prefs} (G : @global PSyn Prefs) := forallb check_node (nodes G).


(** Correction de la procédure *)

Lemma check_exp_ok : forall e, check_exp e = true -> restr_exp e.
Proof.
  induction e using exp_ind2; simpl; intro Hc; try congruence.
  - constructor.
  - constructor.
  - constructor.
  - constructor; auto.
  - apply andb_prop in Hc as []; constructor; auto.
  - apply andb_prop in Hc as [F1 F2].
    apply forallb_Forall in F1, F2.
    constructor; simpl_Forall; auto.
  - apply forallb_Forall in Hc.
    constructor; simpl_Forall; auto.
  - apply forallb_Forall in Hc.
    constructor; simpl_Forall.
    eapply forallb_Forall, Forall_forall in Hc; eauto.
  - destruct d; simpl in H0.
    + apply andb_prop in Hc as [F1 F3].
      apply andb_prop in F1 as [F1 F2].
      apply forallb_Forall in F2,F3.
      constructor; simpl_Forall; auto.
      eapply forallb_Forall, Forall_forall in F2; eauto.
    + apply andb_prop in Hc as [F1 F2].
      apply forallb_Forall in F2.
      constructor; simpl_Forall; auto.
      eapply forallb_Forall, Forall_forall in F2; eauto.
  - (* Eapp *)
    apply andb_prop in Hc as [F1 F2].
    apply forallb_Forall in F1, F2.
    constructor; simpl_Forall; auto.
Qed.

Lemma check_block_ok : forall b, check_block b = true -> restr_block b.
Proof.
  destruct b; simpl; intros * Hc; try congruence.
  destruct e.
  constructor.
  eapply forallb_Forall in Hc.
  simpl_Forall; auto using check_exp_ok.
Qed.

Lemma check_top_block_ok : forall b, check_top_block b = true -> restr_top_block b.
Proof.
  destruct b; simpl; intros * Hc; try congruence.
  destruct s.
  apply andb_prop in Hc as [F1 F2].
  apply forallb_Forall in F1, F2.
  constructor.
  - simpl_Forall; auto using check_block_ok.
  - simpl_Forall; destruct o; now simpl in *.
Qed.

Lemma check_node_ok {PSyn Prefs} :
  forall (n : @node PSyn Prefs), check_node n = true -> restr_node n.
Proof.
  intros * Hc.
  apply andb_prop in Hc as [Hc F2].
  apply forallb_Forall in F2.
  constructor; auto using check_top_block_ok.
  - simpl_Forall; destruct o; now simpl in *.
  - pose proof (n_defd n) as (xs & Vd & Perm).
    apply check_top_block_ok in Hc.
    revert Vd.
    inversion_clear Hc as [??? Hnoloc].
    intro; inv Vd; inv H1.
    destruct H4 as (xss & Vds & Perm2).
    exists (map fst xs); split.
    constructor; constructor.
    exists (map (map fst) xss); split.
    + simpl_Forall.
      take (restr_block _) and inv it.
      take (VarsDefined _ _) and inv it.
      simpl in *; subst; constructor.
    + apply (Permutation_map fst) in Perm2; revert Perm2.
      now rewrite concat_map, map_app, map_fst_senv_of_decls.
    + apply (Permutation_map fst) in Perm; revert Perm.
      now rewrite map_fst_senv_of_decls.
Qed.

Lemma check_global_ok {PSyn Prefs} :
  forall (G : @global PSyn Prefs), check_global G = true -> restr_global G.
Proof.
  intros * Hc; red.
  eapply forallb_Forall in Hc.
  simpl_Forall; auto using check_node_ok.
Qed.

(* Lemma locals_restr_blocks : *)
(*   forall (blks : list block), *)
(*     Forall restr_block blks -> *)
(*     flat_map idcaus_of_locals blks = []. *)
(* Proof. *)
(*   induction 1 as [|?? Hr]; auto; now inv Hr. *)
(* Qed. *)

(* Lemma get_idcaus_locals {PSyn Prefs} : *)
(*   forall (nd : node), *)
(*     restr_node nd -> *)
(*     map fst (get_locals (n_block nd)) = map snd (idcaus_of_locals (n_block nd)). *)
(* Proof. *)
(*   intros * Hr. *)
(*   inversion_clear Hr as [?? Hrtb (xs & Vd & Perm)]. *)
(*   inv Hrtb; simpl. *)
(*   rewrite locals_restr_blocks, app_nil_r, *)
(*     <- idcaus_of_decls_map, map_fst_senv_of_decls; auto. *)
(* Qed. *)

(* Fixpoint get_defined (blk : block) : list ident := *)
(*   match blk with *)
(*   | Beq (xs,es) => xs *)
(*   | Blocal (Scope vars blks) => flat_map get_defined blks *)
(*   | _ => [] *)
(*   end. *)

(* Lemma NoDup_vars_ins : *)
(*   forall {PSyn Prefs} (nd : @node PSyn Prefs), *)
(*   forall vars blks, *)
(*     Forall restr_block blks -> *)
(*     n_block nd = Blocal (Scope vars blks) -> *)
(*     NoDup (flat_map get_defined blks ++ List.map fst (n_in nd)). *)
(* Proof. *)
(*   intros * Hr Hn. *)
(*   apply NoDup_senv_loc in Hn as ndm. *)
(*   pose proof (n_defd nd) as (outs & Vd & Perm). *)
(*   rewrite Hn in Vd. *)
(*   inv Vd. Syn.inv_scope. *)
(*   rewrite Perm in H0. *)
(*   assert (Permutation (List.map fst (concat x)) (flat_map get_defined blks)) as <-. *)
(*   { clear - H Hr. *)
(*     induction H; inv Hr; simpl; auto. *)
(*     rewrite map_app. *)
(*     apply Permutation_app; auto. *)
(*     take (restr_block _) and inv it. *)
(*     inv H; simpl in *; subst. *)
(*     reflexivity. *)
(*   } *)
(*   rewrite Permutation_app_comm, H0, <- map_fst_senv_of_ins, <- map_app. *)
(*   now rewrite <- fst_NoDupMembers. *)
(* Qed. *)

(* Lemma nin_defined : *)
(*   forall {PSyn Prefs} (n : @node PSyn Prefs), *)
(*   forall vars blks x, *)
(*     n_block n = Blocal (Scope vars blks) -> *)
(*     In x (List.map fst (senv_of_decls (n_out n) ++ senv_of_decls vars)) -> *)
(*     List.Exists (Is_defined_in (Var x)) blks. *)
(* Proof. *)
(*   intros * Hn Hxin. *)
(*   pose proof (n_nodup n) as (Nd & Ndl). *)
(*   pose proof (n_defd n) as (?& Vd & Perm). *)
(*   rewrite Hn in Vd, Ndl. *)
(*   inv Ndl; take (NoDupScope _ _ _) and inv it. *)
(*   inv Vd; Syn.inv_scope. *)
(*   eapply Forall_VarsDefined_Is_defined; eauto. *)
(*   + take (Permutation (concat _) _) and rewrite it. *)
(*     take (Permutation x0 _) and rewrite it. *)
(*     rewrite map_app, 2 map_fst_senv_of_decls. *)
(*     simpl_Forall. *)
(*     eapply NoDupLocals_incl; eauto. *)
(*     solve_incl_app. *)
(*   + take (Permutation (concat _) _) and rewrite it. *)
(*     take (Permutation x0 _) and rewrite it. *)
(*     rewrite fst_InMembers; auto. *)
(* Qed. *)

End LRESTR.

Module RestrFun
  (Ids   : IDS)
  (Op    : OPERATORS)
  (OpAux : OPERATORS_AUX Ids Op)
  (Cks   : CLOCKS        Ids Op OpAux)
  (Senv  : STATICENV     Ids Op OpAux Cks)
  (Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
<: LRESTR Ids Op OpAux Cks Senv Syn.
  Include LRESTR Ids Op OpAux Cks Senv Syn.
End RestrFun.
