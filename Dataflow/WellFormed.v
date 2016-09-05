Require Import Rustre.Common.
Require Import Rustre.Dataflow.Syntax.
Require Import Rustre.Dataflow.IsFree.
Require Import Rustre.Dataflow.IsVariable.
Require Import Rustre.Dataflow.IsDefined.
Require Import Rustre.Dataflow.Memories.
Require Import Rustre.Dataflow.Ordered.
Require Import Rustre.Dataflow.NoDup.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

(** * Well formed CoreDF programs *)

Module Type WELLFORMED
       (Import Ids : IDS)
       (Import Op  : OPERATORS)
       (Import Syn : SYNTAX Ids Op)
       (Import IsF : ISFREE Ids Op Syn)
       (Import Ord : ORDERED Ids Op Syn)
       (Import Mem : MEMORIES Ids Op Syn)
       (Import IsD : ISDEFINED Ids Op Syn Mem)
       (Import IsV : ISVARIABLE Ids Op Syn Mem IsD)
       (Import NoD : NODUP Ids Op Syn Mem IsD IsV).

  Section IsWellSch.

    Variable memories : PS.t.
    Variable arg: list ident.

    (**

A list of equations is well scheduled if 
  - the free stack variables ([~PS.In _ memories]) are defined before
    (i.e. in [eqs]), or they belong to the input argument
  - the free memory variables ([PS.In _ memories]) have not been
    re-assigned before (i.e. in [eqs])
  - the variable defined by an equation must be defined for the first
    time

Remark: we assume that the list of equations is in reverse order: the
first equation to execute should be the last in the list.

     *)
    (* =Is_well_sch= *)
    Inductive Is_well_sch : list equation -> Prop :=
    | WSchNil: Is_well_sch nil
    | WSchEq: forall eq eqs,
        Is_well_sch eqs ->
        (forall i, Is_free_in_eq i eq ->
              (PS.In i memories -> ~Is_defined_in_eqs i eqs)
              /\ (~PS.In i memories -> Is_variable_in_eqs i eqs \/ In i arg)) ->
        (forall i, Is_defined_in_eq i eq -> ~Is_defined_in_eqs i eqs) ->
        Is_well_sch (eq :: eqs).
    (* =end= *)

  End IsWellSch.

  (**

A CoreDF program is well defined if 
  - Each node is well-defined, that is
    - Each input arguments' name is distinct
    - The equations are well scheduled
    - The input variables are not redefined by the equations
    - The output variable is indeed defined by the equations
  - Every node call points to a previously-defined node
  - Each of the nodes' name is distinct

   *)

  Inductive Welldef_global : list node -> Prop :=
  | WGnil:
      Welldef_global []
  | WGcons:
      forall nd nds,
        Welldef_global nds ->
        let eqs := nd.(n_eqs) in
        let ni := map fst nd.(n_in) in
        let no := fst nd.(n_out) in
        NoDup ni
        -> Is_well_sch (memories eqs) ni eqs
        -> ~Exists (fun ni => Is_defined_in_eqs ni eqs) ni
        -> Is_variable_in_eqs no eqs
        -> ~Is_node_in nd.(n_name) eqs
        -> (forall f, Is_node_in f eqs -> find_node f nds <> None)
        -> List.Forall (fun nd'=> nd.(n_name) <> nd'.(n_name)) nds
        -> Welldef_global (nd::nds).
  
  (** ** Properties of [Is_well_sch] *)

  Hint Constructors Is_well_sch.

  Lemma Is_well_sch_NoDup_defs:
    forall mems argIn eqs,
      Is_well_sch mems argIn eqs
      -> NoDup_defs eqs.
  Proof.
    induction eqs as [|eq eqs IH]; [now constructor|].
    inversion_clear 1; destruct eq; constructor; try apply IH; auto; try apply H2; constructor.
  Qed.

  Lemma Is_well_sch_cons:
    forall m argIn eq eqs, Is_well_sch m argIn (eq :: eqs) -> Is_well_sch m argIn eqs.
  Proof. inversion 1; auto. Qed.

  Lemma Is_well_sch_free_variable:
    forall argIn x eq eqs mems,
      Is_well_sch mems argIn (eq :: eqs)
      -> Is_free_in_eq x eq
      -> ~ PS.In x mems
      -> Is_variable_in_eqs x eqs \/ In x argIn.
  Proof.
    intros argIn x eq eqs mems Hwsch Hfree Hnim.
    destruct eq;
      inversion_clear Hwsch;
      inversion_clear Hfree as [? ? ? ? Hc | ? ? ? ? ? Hc | ? ? ? ? ? Hc]; 
      subst; intuition;
      match goal with
      | H: context[ Is_variable_in_eqs _ _ \/ In _ _] |- _ =>
        eapply H; eauto
      end.
  Qed.

  Lemma Is_well_sch_free_variable_in_mems:
    forall argIn y eq eqs mems,
      Is_well_sch mems argIn (eq :: eqs)
      -> Is_free_in_eq y eq
      -> PS.In y mems
      -> ~Is_defined_in_eqs y eqs.
  Proof.
    intros argIn x eq eqs mems Hwsch Hfree Hnim.
    destruct eq;
      inversion_clear Hwsch;
      inversion_clear Hfree as [? ? ? ? Hc | ? ? ? ? ? Hc | ? ? ? ? ? Hc];
      match goal with
      | H: context[In _ _ ] |- _ => eapply H
      end;
      auto.
  Qed.

  (* Lemma Is_wsch_is_defined_in: *)
  (*   forall x eq eqs mems argIn, *)
  (*     Is_well_sch mems argIn (eq :: eqs) -> *)
  (*     Is_defined_in_eqs x (eq :: eqs) -> *)
  (*     Is_defined_in_eq x eq *)
  (*     \/ (~Is_defined_in_eq x eq /\ Is_defined_in_eqs x eqs). *)
  (* Proof. *)
  (*   intros x eq eqs mems argIn Hwsch Hdef. *)
  (*   apply Exists_cons in Hdef. *)
  (*   destruct (Is_defined_in_eq_dec x eq); intuition. *)
  (* Qed. *)

  (** ** Properties of [Welldef_global] *)

  Lemma Welldef_global_cons:
    forall node G,
      Welldef_global (node::G) -> Welldef_global G.
  Proof.
    inversion 1; assumption.
  Qed.

  (* TODO: Write a function 'welldef_global' to decide this. *)

  Lemma Welldef_global_Ordered_nodes:
    forall G, Welldef_global G -> Ordered_nodes G.
  Proof.
    induction G as [|node G IH]; [constructor|].
    intro Hwdef.
    constructor.
    - apply IH; apply Welldef_global_cons with (1:=Hwdef).
    - intros f Hini.
      inversion Hwdef.
      split; [ intro; subst | ];
      repeat match goal with
             | eqs:=n_eqs node |- _ => unfold eqs in *; clear eqs
                  | H1:~Is_node_in _ _, H2:Is_node_in _ _ |- False => contradiction
                  | H1: Is_node_in _ _,
                        H2: context[Is_node_in _ _ -> find_node _ _ <> None] |- _ =>
                    apply H2 in H1; apply find_node_Exists in H1; exact H1
             end.
    - inversion Hwdef; assumption.
  Qed.

  (* Lemma Welldef_global_app: *)
  (*   forall G G', Welldef_global (G ++ G') -> Welldef_global G'. *)
  (* Proof. *)
  (*   intros G G' Hwdef. *)
  (*   induction G as [|g G IH]; [now apply Hwdef|]. *)
  (*   rewrite <- List.app_comm_cons in Hwdef. *)
  (*   apply Welldef_global_cons in Hwdef. *)
  (*   apply IH. *)
  (*   apply Hwdef. *)
  (* Qed. *)

  (* Lemma Welldef_global_input_not_Is_defined_in: *)
  (*   forall f G fnode, *)
  (*     Welldef_global G *)
  (*     -> find_node f G = Some fnode *)
  (*     -> ~ Exists (fun ni => Is_defined_in_eqs ni fnode.(n_eqs)) *)
  (*         (map fst fnode.(n_input)). *)
  (* Proof. *)
  (*   induction G as [|node G IH]; [inversion_clear 2|]. *)
  (*   intros fnode HWdef Hfnode. *)
  (*   apply find_node_split in Hfnode. *)
  (*   destruct Hfnode as [bG [aG HnG]]. *)
  (*   rewrite HnG in HWdef; clear HnG. *)
  (*   apply Welldef_global_app in HWdef. *)
  (*   inversion_clear HWdef. *)
  (*   easy. *)
  (* Qed. *)

  (* Lemma Welldef_global_output_Is_variable_in: *)
  (*   forall f G fnode, *)
  (*     Welldef_global G *)
  (*     -> find_node f G = Some fnode *)
  (*     -> Is_variable_in_eqs (fst fnode.(n_output)) fnode.(n_eqs). *)
  (* Proof. *)
  (*   induction G as [|node G IH]; [inversion_clear 2|]. *)
  (*   intros fnode HWdef Hfnode. *)
  (*   apply find_node_split in Hfnode. *)
  (*   destruct Hfnode as [bG [aG HnG]]. *)
  (*   rewrite HnG in HWdef; clear HnG. *)
  (*   apply Welldef_global_app in HWdef. *)
  (*   inversion_clear HWdef. *)
  (*   assumption. *)
  (* Qed. *)
End WELLFORMED.

Module WellFormedFun
       (Import Ids : IDS)
       (Import Op  : OPERATORS)
       (Import Syn : SYNTAX Ids Op)
       (Import IsF : ISFREE Ids Op Syn)
       (Import Ord : ORDERED Ids Op Syn)
       (Import Mem : MEMORIES Ids Op Syn)
       (Import IsD : ISDEFINED Ids Op Syn Mem)
       (Import IsV : ISVARIABLE Ids Op Syn Mem IsD)
       (Import NoD : NODUP Ids Op Syn Mem IsD IsV)
       <: WELLFORMED Ids Op Syn IsF Ord Mem IsD IsV NoD.

  Include WELLFORMED Ids Op Syn IsF Ord Mem IsD IsV NoD.
  
End WellFormedFun.

