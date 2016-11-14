Require Import Rustre.Common.
Require Import Rustre.Ident.
Require Import Rustre.ObcToClight.Translation.

Require Import common.Errors.
Require Import common.Events.
Require Import cfrontend.Clight.
Require Import cfrontend.ClightBigstep.

Require Import Rustre.Instantiator.
Import DF.Syn.
Import WeFDec.
Import DF.Mem.
Import Obc.Syn.
Import Fus.
Import Trans.
Import Corr.
Import Typ.
Require Import ObcToClight.Correctness.

Require Import String.

Open Scope error_monad_scope.

Definition is_well_sch (res: res unit) (n: node) :=
  match res with
  | OK _ =>
    let eqs := n.(n_eqs) in
    let ni := List.map fst n.(n_in) in
    if well_sch (memories eqs) ni eqs then OK tt
    else Error (Errors.msg ("node " ++ pos_to_str n.(n_name) ++ " is not well scheduled."))
  | _ => res
  end.

Definition fuse_method (m: method): method :=
  match m with
    mk_method name ins vars out body nodup good =>
    mk_method name ins vars out (fuse body) nodup good 
  end.

Lemma map_m_name_fuse_methods:
  forall methods,
    List.map m_name (List.map fuse_method methods) = List.map m_name methods.
Proof.
  intro ms; induction ms as [|m ms]; auto.
  simpl. rewrite IHms.
  now destruct m.
Qed.
  
Lemma NoDup_m_name_fuse_methods:
  forall methods,
    List.NoDup (List.map m_name methods) ->
    List.NoDup (List.map m_name (List.map fuse_method methods)).
Proof.
  intros; now rewrite map_m_name_fuse_methods.
Qed.

Definition fuse_class (c: class): class :=
  match c with
    mk_class name mems objs methods nodup nodupm =>
    mk_class name mems objs (List.map fuse_method methods) nodup
             (NoDup_m_name_fuse_methods _ nodupm)
  end.

Definition compile (g: global) (main_node: ident) :=
  do _ <- (List.fold_left is_well_sch g (OK tt));
  ObcToClight.Translation.translate ((* List.map fuse_class *) (Trans.translate g)) main_node.

Lemma soundness:
  forall G P main ins outs,
    DF.WeF.Welldef_global G ->
    DF.Typ.wt_global G ->
    DF.Sem.sem_node G main (fun n => List.map (fun c => DF.Str.present (Interface.Op.sem_const c)) (ins n))
                    (fun n => List.map (fun c => DF.Str.present (Interface.Op.sem_const c)) (outs n)) ->
    compile G main = OK P ->
    exists T, bigstep_program_diverges function_entry2 P T.
Proof.
  intros ** Comp.
  edestruct dostep'_correct as (me0 & Heval & Step); eauto.
  unfold compile in Comp.
  destruct (List.fold_left is_well_sch G (OK tt)); try discriminate; simpl in Comp.
  pose proof Comp.
  unfold Translation.translate in Comp.
  destruct (find_class main (translate G)) as [(c_main, prog_main)|] eqn: Emain; try discriminate.
  destruct (find_method Ids.step (c_methods c_main)) as [m_step|] eqn: Estep; try discriminate.
  destruct (find_method Ids.reset (c_methods c_main)) as [m_reset|] eqn: Ereset; try discriminate.
  pose proof (find_class_name _ _ _ _ Emain) as Eq;
    pose proof (find_method_name _ _ _ Estep) as Eq';
    pose proof (find_method_name _ _ _ Ereset) as Eq'';
    rewrite <-Eq, <-Eq'' in Heval; rewrite <-Eq in Step.
  edestruct find_class_translate as (main_node & ? & Hmain); eauto.
  rewrite Hmain in Ereset, Estep.
  pose proof (exists_reset_method main_node) as Ereset'.
  rewrite Ereset in Ereset'.
  inv Ereset'.
  econstructor; eapply diverges' with (me0:=me0); eauto. 
  - apply translate_wt; auto.
  - admit.

  Grab Existential Variables.
  + admit.
  + admit.
  + apply find_method_stepm_out in Estep.
    pose proof (n_outgt0 main_node) as Hout.
    rewrite Estep; intro E; rewrite E in Hout; simpl in Hout.
    eapply Lt.lt_irrefl; eauto.
  + apply find_method_stepm_in in Estep.
    pose proof (n_ingt0 main_node) as Hin.
    rewrite Estep; intro E; rewrite E in Hin; simpl in Hin.
    eapply Lt.lt_irrefl; eauto.
Qed.