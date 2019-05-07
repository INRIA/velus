Require Import Velus.Common.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import PArith.
Require Import Coq.Sorting.Permutation.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

(** * The Lustre dataflow language *)

Module Type LSYNTAX
       (Import Ids  : IDS)
       (Import Op   : OPERATORS).

  (** ** Expressions *)

  (* Type and clock annotations *)
  Definition ann : Type := (type * nclock)%type.
  Definition lann : Type := (list type * nclock)%type.

  (*
    Annotated AST.

    (`Basic') Lustre does not have tuples. We work with flattened
    flow lists. The type of annotation depends on which
    forms of flow list may be produced by a given construction:
    -  ann:       single flow only (var, unop, binop)
    - lann:       multiple synchronized flows (fby, when, merge, ifte)
    - list ann:   multiple flows (app)
   *)

  Inductive exp : Type :=
  | Econst : const -> exp
  | Evar   : ident -> ann -> exp
  | Eunop  : unop -> exp -> ann -> exp
  | Ebinop : binop -> exp -> exp -> ann -> exp

  | Efby   : list exp -> list exp -> list ann -> exp
  | Ewhen  : list exp -> ident -> bool -> lann -> exp
  | Emerge : ident -> list exp -> list exp -> lann -> exp
  | Eite   : exp -> list exp -> list exp -> lann -> exp

  | Eapp   : ident -> list exp -> list ann -> exp.

  Implicit Type e: exp.

  (** ** Equations *)

  Definition equation : Type := (idents * list exp)%type.

  Implicit Type eqn: equation.

  (** ** Node *)

  Fixpoint numstreams (e: exp) : nat :=
    match e with
    | Econst c => 1
    | Efby _ _ anns
    | Eapp _ _ anns => length anns
    | Evar _ _
    | Eunop _ _ _
    | Ebinop _ _ _ _ => 1
    | Ewhen _ _ _  (tys, _)
    | Emerge _ _ _ (tys, _)
    | Eite _ _ _   (tys, _) => length tys
    end.

  (* Annotation (homogenized). *)

  Fixpoint annot (e: exp): list (type * nclock) :=
    match e with
    | Econst c => [(type_const c, Cstream Sbase)]
    | Efby _ _ anns
    | Eapp _ _ anns => anns
    | Evar _ ann
    | Eunop _ _ ann
    | Ebinop _ _ _ ann => [ann]
    | Ewhen _ _ _  (tys, ck)
    | Emerge _ _ _ (tys, ck)
    | Eite _ _ _   (tys, ck) => map (fun ty=> (ty, ck)) tys
    end.

  Definition annots (es: list exp): list (type * nclock) :=
    flat_map annot es.

  Fixpoint typeof (e: exp): list type :=
    match e with
    | Econst c => [type_const c]
    | Efby _ _ anns
    | Eapp _ _ anns => map fst anns
    | Evar _ ann
    | Eunop _ _ ann
    | Ebinop _ _ _ ann => [fst ann]
    | Ewhen _ _ _ anns
    | Emerge _ _ _ anns
    | Eite _ _ _ anns => fst anns
    end.

  Definition typesof (es: list exp): list type :=
    flat_map typeof es.

  Definition ckstream {A} (ann: A * nclock): sclock := stripname (snd ann).

  Definition is_ckstream {A} (ann: A * nclock): Prop :=
    match snd ann with
    | Cstream _ => True
    | Cnamed _ _ => False
    end.

  Fixpoint clockof (e: exp): list sclock :=
    match e with
    | Econst c => [Sbase]
    | Efby _ _ anns
    | Eapp _ _ anns => map ckstream anns
    | Evar _ ann
    | Eunop _ _ ann
    | Ebinop _ _ _ ann => [ckstream ann]
    | Ewhen _ _ _ anns
    | Emerge _ _ _ anns
    | Eite _ _ _ anns => map (fun _ => ckstream anns) (fst anns)
    end.

  Definition clocksof (es: list exp): list sclock :=
    flat_map clockof es.

  Fixpoint nclockof (e: exp): list nclock :=
    match e with
    | Econst c => [Cstream Sbase]
    | Efby _ _ anns
    | Eapp _ _ anns => map snd anns
    | Evar _ ann
    | Eunop _ _ ann
    | Ebinop _ _ _ ann => [snd ann]
    | Ewhen _ _ _ anns
    | Emerge _ _ _ anns
    | Eite _ _ _ anns => map (fun _ => snd anns) (fst anns)
    end.

  Definition nclocksof (es: list exp): list nclock :=
    flat_map nclockof es.

  Definition vars_defined (eqs: list equation) : idents :=
    flat_map fst eqs.

  Record node : Type :=
    mk_node {
        n_name     : ident;
        n_hasstate : bool;
        n_in       : list (ident * (type * clock));
        n_out      : list (ident * (type * clock));
        n_vars     : list (ident * (type * clock));
        n_eqs      : list equation;

        n_ingt0    : 0 < length n_in;
        n_outgt0   : 0 < length n_out;
        n_defd     : Permutation (vars_defined n_eqs)
                                 (map fst (n_vars ++ n_out));
        n_nodup    : NoDupMembers (n_in ++ n_vars ++ n_out);
        n_good     : Forall NotReserved (n_in ++ n_vars ++ n_out)
      }.

  (** ** Program *)

  Definition global := list node.

  Implicit Type G: global.

  (* definition is needed in signature *)
  Definition find_node (f : ident) : global -> option node :=
    List.find (fun n=> ident_eqb n.(n_name) f).

  Hint Unfold is_ckstream : lclocking.

  (** Structural properties *)

  (* TODO: custom induction scheme for expression... *)

  Section exp_ind2.

    Variable P : exp -> Prop.

    Hypothesis EconstCase:
      forall c,
        P (Econst c).

    Hypothesis EvarCase:
      forall x a,
        P (Evar x a).

    Hypothesis EunopCase:
      forall op e a,
        P (Eunop op e a).

    Hypothesis EbinopCase:
      forall op e1 e2 a,
        P (Ebinop op e1 e2 a).

    Hypothesis EfbyCase:
      forall e0s es a,
        Forall P es ->
        P (Efby e0s es a).

    Hypothesis EwhenCase:
      forall es x b a,
        Forall P es ->
        P (Ewhen es x b a).

    Hypothesis EmergeCase:
      forall x ets efs a,
        Forall P ets ->
        Forall P efs ->
        P (Emerge x ets efs a).

    Hypothesis EiteCase:
      forall e ets efs a,
        P e ->
        Forall P ets ->
        Forall P efs ->
        P (Eite e ets efs a).

    Hypothesis EappCase:
      forall f es a,
        Forall P es ->
        P (Eapp f es a).

    Local Ltac SolveForall :=
      match goal with
      | |- Forall ?P ?l => induction l; auto
      | _ => idtac
      end.

    Fixpoint exp_ind2 (e: exp) : P e.
    Proof.
      destruct e.
      - apply EconstCase; auto.
      - apply EvarCase; auto.
      - apply EunopCase; auto.
      - apply EbinopCase; auto.
      - apply EfbyCase; SolveForall.
      - apply EwhenCase; SolveForall.
      - apply EmergeCase; SolveForall.
      - apply EiteCase; SolveForall; auto.
      - apply EappCase; SolveForall.
    Qed.

  End exp_ind2.

  (** clocksof *)

  Lemma In_clocksof:
    forall sck es,
      In sck (clocksof es) ->
      exists e, In e es /\ In sck (clockof e).
  Proof.
    induction es as [|e es IH]. now inversion 1.
    simpl. rewrite in_app.
    destruct 1 as [Hin|Hin].
    now eauto with datatypes.
    apply IH in Hin. destruct Hin as (e' & Hin1 & Hin2).
    eauto with datatypes.
  Qed.

  (** nclockof and nclocksof *)

  Lemma clockof_nclockof:
    forall e,
      clockof e = map stripname (nclockof e).
  Proof.
    destruct e; simpl; unfold ckstream; try rewrite map_map; auto.
  Qed.

  Lemma clocksof_nclocksof:
    forall es,
      clocksof es = map stripname (nclocksof es).
  Proof.
    induction es as [|e es IH]; auto; simpl.
    now rewrite map_app, IH, <-clockof_nclockof.
  Qed.

  Lemma Is_index_in_nclocks_Cstream:
    forall i e,
      Is_index_in_nclocks i (map Cstream (clockof e)) ->
      Is_index_in_nclocks i (nclockof e).
  Proof.
    intros * Hii.
    rewrite clockof_nclockof, map_map in Hii.
    unfold Is_index_in_nclocks in Hii.
    induction (nclockof e) as [|nck ncks IH];
      inversion_clear Hii as [? ? Hi|].
    2:now constructor 2; apply IH.
    constructor.
    destruct nck; inversion_clear Hi;
      auto using Is_index_in_nclock.
  Qed.

  (* Tidy up: we don't need two lemmas *)
  Lemma Is_index_in_nclocks_stripname_nclockof:
    forall i e sclk,
      Is_index_in_nclocks i [Cstream sclk] ->
      map stripname (nclockof e) = [sclk] ->
      Is_index_in_nclocks i (nclockof e).
  Proof.
    intros * Hii Hmap.
    inversion_clear Hii as [? ? Hii'|? ? Hii']; inv Hii'.
    destruct (nclockof e) as [|nck ncks]. discriminate.
    destruct ncks. 2:discriminate.
    constructor. destruct nck; inv Hmap; now constructor.
  Qed.

  Lemma Is_index_in_nclock_stripname_nclockof:
    forall i e sclk,
      Is_index_in_nclock i (Cstream sclk) ->
      map stripname (nclockof e) = [sclk] ->
      Is_index_in_nclocks i (nclockof e).
  Proof.
    intros * Hii Hmap.
    inv Hii.
    destruct (nclockof e) as [|nck ncks]. discriminate.
    destruct ncks. 2:discriminate.
    constructor. destruct nck; inv Hmap; now constructor.
  Qed.

  Lemma In_nclocksof:
    forall nck es,
      In nck (nclocksof es) ->
      exists e, In e es /\ In nck (nclockof e).
  Proof.
    induction es as [|e es IH]. now inversion 1.
    simpl; rewrite in_app.
    destruct 1 as [Hin|Hin]; eauto with datatypes.
    apply IH in Hin. destruct Hin as (e' & Hin1 & Hin2).
    eauto with datatypes.
  Qed.

  Lemma is_ckstream_NoDup_indexes:
    forall {A} anns,
      Forall (@is_ckstream A) anns ->
      indexes (map snd anns) = [].
  Proof.
    induction anns as [|(?, nck) anns IH]; auto.
    inversion_clear 1. destruct nck; auto.
    match goal with H:is_ckstream _ |- _ => inv H end.
  Qed.

  (** vars_defined *)

  Lemma NoDup_vars_defined_n_eqs:
    forall n,
      NoDup (vars_defined n.(n_eqs)).
  Proof.
    intro n.
    rewrite n.(n_defd).
    apply fst_NoDupMembers.
    apply (NoDupMembers_app_r _ _ n.(n_nodup)).
  Qed.

  (** find_node *)

  Lemma find_node_Exists:
    forall f G, find_node f G <> None <-> List.Exists (fun n=> n.(n_name) = f) G.
  Proof.
    intros f G.
    setoid_rewrite find_Exists.
    now setoid_rewrite BinPos.Pos.eqb_eq.
  Qed.

  Lemma find_node_tl:
    forall f node G,
      node.(n_name) <> f
      -> find_node f (node::G) = find_node f G.
  Proof.
    intros f node G Hnf.
    unfold find_node. unfold List.find at 1.
    apply Pos.eqb_neq in Hnf. unfold ident_eqb.
    now rewrite Hnf.
  Qed.

  Lemma find_node_other:
    forall f node G node',
      node.(n_name) <> f
      -> (find_node f (node::G) = Some node'
         <-> find_node f G = Some node').
  Proof.
    intros f node G node' Hnf.
    apply BinPos.Pos.eqb_neq in Hnf.
    simpl. unfold ident_eqb.
    now rewrite Hnf.
  Qed.

  Lemma find_node_split:
    forall f G node,
      find_node f G = Some node
      -> exists bG aG,
        G = bG ++ node :: aG.
  Proof.
    unfold find_node.
    intros * Hf. now apply find_split in Hf.
  Qed.

End LSYNTAX.

Module LSyntaxFun
       (Ids  : IDS)
       (Op   : OPERATORS) <: LSYNTAX Ids Op.
  Include LSYNTAX Ids Op.
End LSyntaxFun.
