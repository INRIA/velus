Require Import Coq.FSets.FMapPositive.
Require Import PArith.
Require Import Rustre.Common.
Require Import Rustre.Minimp.Syntax.
Require Import Rustre.Dataflow.Syntax.
Require Import Rustre.Dataflow.Memories.

Require Import List.
Require Import Coq.Lists.List.
Import List.ListNotations.
Open Scope positive.
Open Scope list.

(** * Translation *)

(** ** Identification of node instances *)

(** 

Each node application in CoreDF turns into a method call in the
imperative setting. This means that, upon initializing a node, one
must declare a new instance for each its application.

Remark: it is necessary to distinguish different instantiations of the
same node (i.e., different objects of the same class). This is done in
Auger's thesis in the language LSNI, where node applications are
assigned unique identifiers. His context is richer, in particular,
because the result of a node application may be assigned to a
pattern-tuple containing multiple identifiers.

Here, we take advantage of the fact that the result of a node
application is assigned to a single variable. We use the name of that
variable to identify the instance.  *)

Module Type TRANSLATION
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import SynDF : Rustre.Dataflow.Syntax.SYNTAX Ids Op)
       (Import SynMP : Rustre.Minimp.Syntax.SYNTAX Ids Op OpAux).

  (* definition is needed in signature *)
  Definition gather_eq
             (acc: list ident * list (ident * ident)) (eq: equation) :=
    match eq with
    | EqDef _ _ _     => acc
    | EqApp x _ f _ _ => (fst acc, (x, f) :: snd acc)
    | EqFby x _ _ _ => (x::fst acc, snd acc)
    end.

  (* definition is needed in signature *)
  Definition gather_eqs
             (eqs: list equation) : list ident * list (ident * ident) :=
    List.fold_left gather_eq eqs ([], []).

  (** ** Translation *)

  Section Translate.

    Variable memories : PS.t.

    (* =tovar= *)
    Definition tovar (xt: ident * typ) : exp :=
      let (x, ty) := xt in
      if PS.mem x memories then State x ty else Var x ty.
    (* =end= *)

    (* =control= *)
    (* definition is needed in signature *)
    Fixpoint Control (ck: clock) (s: stmt) : stmt :=
      match ck with
      | Cbase => s
      | Con ck x true  => Control ck (Ifte (tovar (x, bool_typ)) s Skip)
      | Con ck x false => Control ck (Ifte (tovar (x, bool_typ)) Skip s)
      end.
    (* =end= *)

    (* =translate_lexp= *)
    (* definition is needed in signature *)
    Fixpoint translate_lexp (e : lexp) : exp :=
      match e with
      | Econst c => Const c
      | Evar x ty => tovar (x, ty)
      | Ewhen e c x => translate_lexp e
      | Eunop op e ty => Unop op (translate_lexp e) ty
      | Ebinop op e1 e2 ty => Binop op (translate_lexp e1) (translate_lexp e2) ty
      end.
    (* =end= *)

    (* =translate_cexp= *)
    (* definition is needed in signature *)
    Fixpoint translate_cexp (x: ident) (e: cexp) : stmt :=
      match e with
      | Emerge y ty t f => Ifte (tovar (y, ty))
                                (translate_cexp x t)
                                (translate_cexp x f)
      | Eite b t f => Ifte (translate_lexp b)
                           (translate_cexp x t)
                           (translate_cexp x f)
      | Eexp l => Assign x (translate_lexp l)
      end.
    (* =end= *)

    (* =translate_eqn= *)
    (* definition is needed in signature *)
    Definition translate_eqn (eqn: equation) : stmt :=
      match eqn with
      | EqDef x ck ce => Control ck (translate_cexp x ce)
      | EqApp x ck f les ty =>
          Control ck (Call [(x, ty)] f x step (List.map translate_lexp les))
      | EqFby x ck v le => Control ck (AssignSt x (translate_lexp le))
      end.
    (* =end= *)

  (*   (** Remark: eqns ordered in reverse order of execution for coherence with *)
  (*      [Is_well_sch]. *) *)

    (* =translate_eqns= *)
    (* definition is needed in signature *)
    Definition translate_eqns (eqns: list equation) : stmt :=
      List.fold_left (fun i eq => Comp (translate_eqn eq) i) eqns Skip.
    (* =end= *)

  End Translate.

  (* =translate_reset_eqn= *)
  (* definition is needed in signature *)
  Definition translate_reset_eqn (s: stmt) (eqn: equation) : stmt :=
    match eqn with
    | EqDef _ _ _ => s
    | EqFby x _ c0 _  => Comp (AssignSt x (Const c0)) s
    | EqApp x _ f _ _ => Comp (Call [] f x reset []) s
    end.
  (* =end= *)

  (* =translate_reset_eqns= *)
  (* definition is needed in signature *)
  Definition translate_reset_eqns (eqns: list equation): stmt :=
    List.fold_left translate_reset_eqn eqns Skip.
  (* =end= *)

  (* definition is needed in signature *)
  Definition ps_from_list (l: list ident) : PS.t :=
    List.fold_left (fun s i=>PS.add i s) l PS.empty.

  Hint Constructors NoDupMembers VarsDeclared.
  
  Program Definition reset_method (eqns: list equation): method :=
    {| m_name := reset;
       m_in   := [];
       m_vars := [];
       m_out  := [];
       m_body := translate_reset_eqns eqns;
       m_nodupvars := _;
       m_varsdecl  := _;
       m_good      := _
    |}.
  Next Obligation.
    unfold translate_reset_eqns.
    cut(forall s,
           VarsDeclared [] s ->
           VarsDeclared [] (List.fold_left translate_reset_eqn eqns s)); auto.
    induction eqns as [|eq eqns]; auto.
    destruct eq; auto;
      simpl; intros; apply IHeqns.
    (* TODO: get auto to solve this goal completely *)
    - constructor; auto.
      constructor; auto.
      apply List.incl_refl.
    - constructor; auto.
      constructor; auto.
      constructor; auto.
  Qed.
  
(*
  Lemma blah:
    forall eqs,
      MemsDeclared (fst_gather_eqs eqs) (reset_method eqs).(m_body).


    (* TODO: MemsDeclared mems (reset_method eqns).(m_body) *)
    (* TODO: InstanceDeclared objs (reset_method eqns).(m_body) *)

    (* TODO: Then tackle the trickier step method *)
 *)
  
  (* =translate_node= *)
  (* definition is needed in signature *)
  Program Definition translate_node (n: node) : class :=
    let (memids, dobjs) := gather_eqs n.(n_eqs) in
    let mems := ps_from_list memids in
    let (dmems, dvars) := partition (fun x=>PS.mem (fst x) mems) n.(n_vars) in
    {| c_name    := n.(n_name);
       c_mems    := dmems;
       c_objs    := dobjs;
       c_methods := [ {| m_name := step;
                         m_in   := n.(n_in);
                         m_vars := dvars;
                         m_out  := [n.(n_out)];
                         m_body := translate_eqns mems n.(n_eqs);
                         m_nodupvars := _;
                         m_varsdecl  := _;
                         m_good      := _
                      |};
                      reset_method n.(n_eqs) ];
       c_nodupmems := _;
       c_nodupobjs := _;
       
       c_memsdecl := _;
       c_instdecl := _
    |}.
  (* =end= *)
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.

  (* =translate= *)
  (* definition is needed in signature *)
  Definition translate (G: global) : program :=
    List.map translate_node G.
  (* =end= *)
    
  Lemma translate_node_name:
    forall n, (translate_node n).(c_name) = n.(n_name).
  Proof.
    destruct n.
    unfold translate_node.
    simpl.
    (* TODO: There must be a better way! *)
    destruct (gather_eqs n_eqs0).
    destruct (partition (fun x => PS.mem (fst x) (ps_from_list l)) n_vars0).
    reflexivity.
  Qed.
  
  Lemma exists_step_method:
    forall node,
    exists stepm,
      find_method step (translate_node node).(c_methods) = Some stepm.
  Proof.
    intro node.
    unfold translate_node.
    destruct (gather_eqs node.(n_eqs)).
    destruct (partition (fun x => PS.mem (fst x) (ps_from_list l))
                        node.(n_vars)).
    simpl. rewrite ident_eqb_refl. eauto.
  Qed.

  Lemma exists_reset_method:
    forall node,
      find_method reset (translate_node node).(c_methods)
      = Some (reset_method node.(n_eqs)).
  Proof.
    intro node.
    unfold translate_node.
    destruct (gather_eqs node.(n_eqs)).
    destruct (partition (fun x => PS.mem (fst x) (ps_from_list l))
                        node.(n_vars)).
    simpl.
    assert (ident_eqb step reset = false) as Hsr.
    apply ident_eqb_neq.
    apply PositiveOrder.neq_sym. apply reset_not_step.
    now rewrite Hsr, ident_eqb_refl.
  Qed.

  Lemma find_method_stepm:
    forall node stepm,
      find_method step (translate_node node).(c_methods) = Some stepm ->
      stepm.(m_out) = [node.(n_out)].
  Proof.
    intros node stepm.
    unfold translate_node.
    destruct (gather_eqs node.(n_eqs)).
    destruct (partition (fun x => PS.mem (fst x) (ps_from_list l))
                        node.(n_vars)).
    simpl. rewrite ident_eqb_refl.
    injection 1.
    intro HH; rewrite <-HH.
    reflexivity.
  Qed.
  
  (* (** ** Properties *) *)

  (* Lemma ps_from_list_pre_spec: *)
  (*   forall x l S, (List.In x l \/ PS.In x S) *)
  (*            <-> *)
  (*            PS.In x (List.fold_left (fun s i=>PS.add i s) l S). *)
  (* Proof. *)
  (*   induction l as [|l ls IH]. *)
  (*   - firstorder. *)
  (*   - split; intro HH. *)
  (*     + firstorder. *)
  (*     + apply IH in HH. *)
  (*       destruct HH as [HH|HH]; try apply PS.add_spec in HH; firstorder. *)
  (* Qed. *)

  (* Lemma ps_from_list_spec: *)
  (*   forall x l, List.In x l <-> PS.In x (ps_from_list l). *)
  (* Proof. *)
  (*   unfold ps_from_list. *)
  (*   intros. *)
  (*   rewrite <- ps_from_list_pre_spec with (S:=PS.empty). *)
  (*   split; try intros [H | H]; try tauto. *)
  (*   apply not_In_empty in H; contradiction. *)
  (* Qed. *)
  
End TRANSLATION.

Module TranslationFun
       (Import Ids : IDS)
       (Import Op  : OPERATORS)
       (Import OpAux: OPERATORS_AUX Op)
       (Import SynDF : Rustre.Dataflow.Syntax.SYNTAX Ids Op)
       (Import SynMP : Rustre.Minimp.Syntax.SYNTAX Ids Op OpAux)
       <: TRANSLATION Ids Op OpAux SynDF SynMP.

  Include TRANSLATION Ids Op OpAux SynDF SynMP. 
  
End TranslationFun.

