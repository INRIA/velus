From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Coq Require Import PArith.
From Coq Require Import Sorting.Permutation.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

(** * The Lustre dataflow language *)

Module Type LSYNTAX
       (Import Ids  : IDS)
       (Import Op   : OPERATORS).

  (** ** Expressions *)

  (*
    Annotated AST.

    (`Basic') Lustre does not have tuples. We work with flattened
    flow lists. The type of annotation depends on which
    forms of flow list may be produced by a given construction:
    -  ann:       single flow only (var, unop, binop)
    - lann:       multiple synchronized flows (fby, when, merge, ifte)
    - list ann:   multiple flows (app)
   *)

  (* Type and clock annotations *)
  Definition ann : Type := (type * nclock)%type.
  Definition lann : Type := (list type * nclock)%type.

  Inductive exp : Type :=
  | Econst : const -> exp
  | Evar   : ident -> ann -> exp
  | Eunop  : unop -> exp -> ann -> exp
  | Ebinop : binop -> exp -> exp -> ann -> exp

  | Efby   : list exp -> list exp -> list ann -> exp
  | Ewhen  : list exp -> ident -> bool -> lann -> exp
  | Emerge : ident -> list exp -> list exp -> lann -> exp
  | Eite   : exp -> list exp -> list exp -> lann -> exp

  | Eapp   : ident -> list exp -> option exp -> list ann -> exp.

  Implicit Type e: exp.

  (** ** Equations *)

  Definition equation : Type := (list ident * list exp)%type.

  Implicit Type eqn: equation.

  (** ** Node *)

  Fixpoint numstreams (e: exp) : nat :=
    match e with
    | Econst c => 1
    | Efby _ _ anns
    | Eapp _ _ _ anns => length anns
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
    | Econst c => [(type_const c, (Cbase, None))]
    | Efby _ _ anns
    | Eapp _ _ _ anns => anns
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
    | Eapp _ _ _ anns => map fst anns
    | Evar _ ann
    | Eunop _ _ ann
    | Ebinop _ _ _ ann => [fst ann]
    | Ewhen _ _ _ anns
    | Emerge _ _ _ anns
    | Eite _ _ _ anns => fst anns
    end.

  Definition typesof (es: list exp): list type :=
    flat_map typeof es.

  Definition clock_of_nclock {A} (ann: A * nclock): clock := stripname (snd ann).
  Definition stream_name {A} (ann: A * nclock) : option ident := snd (snd ann).

  Definition unnamed_stream {A} (ann: A * nclock): Prop := snd (snd ann) = None.

  Fixpoint clockof (e: exp): list clock :=
    match e with
    | Econst c => [Cbase]
    | Efby _ _ anns
    | Eapp _ _ _ anns => map clock_of_nclock anns
    | Evar _ ann
    | Eunop _ _ ann
    | Ebinop _ _ _ ann => [clock_of_nclock ann]
    | Ewhen _ _ _ anns
    | Emerge _ _ _ anns
    | Eite _ _ _ anns => map (fun _ => clock_of_nclock anns) (fst anns)
    end.

  Definition clocksof (es: list exp): list clock :=
    flat_map clockof es.

  Fixpoint nclockof (e: exp): list nclock :=
    match e with
    | Econst c => [(Cbase, None)]
    | Efby _ _ anns
    | Eapp _ _ _ anns => map snd anns
    | Evar _ ann
    | Eunop _ _ ann
    | Ebinop _ _ _ ann => [snd ann]
    | Ewhen _ _ _ anns
    | Emerge _ _ _ anns
    | Eite _ _ _ anns => map (fun _ => snd anns) (fst anns)
    end.

  Definition nclocksof (es: list exp): list nclock :=
    flat_map nclockof es.

  Definition vars_defined (eqs: list equation) : list ident :=
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
        n_good     :  Forall ValidId (n_in ++ n_vars ++ n_out)
                      /\ valid n_name
      }.

  (** ** Program *)

  Definition global := list node.

  Implicit Type G: global.

  (* definition is needed in signature *)
  Definition find_node (f : ident) : global -> option node :=
    List.find (fun n=> ident_eqb n.(n_name) f).

  (** Structural properties *)

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
        P e ->
        P (Eunop op e a).

    Hypothesis EbinopCase:
      forall op e1 e2 a,
        P e1 ->
        P e2 ->
        P (Ebinop op e1 e2 a).

    Hypothesis EfbyCase:
      forall e0s es a,
        Forall P e0s ->
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
      forall f es ro a,
        (match ro with None => True | Some r => P r end) ->
        Forall P es ->
        P (Eapp f es ro a).

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
      - destruct o; apply EappCase; SolveForall; auto.
    Qed.

  End exp_ind2.

  (** annots *)

  Fact length_annot_numstreams : forall e,
      length (annot e) = numstreams e.
  Proof.
    destruct e; simpl; auto.
    - destruct l0. apply map_length.
    - destruct l1. apply map_length.
    - destruct l1. apply map_length.
  Qed.

  (** typesof *)

  Fact typeof_annot : forall e,
      typeof e = map fst (annot e).
  Proof.
    destruct e; simpl; try reflexivity.
    - destruct l0; simpl.
      rewrite map_map; simpl.
      symmetry. apply map_id.
    - destruct l1; simpl.
      rewrite map_map; simpl.
      symmetry. apply map_id.
    - destruct l1; simpl.
      rewrite map_map; simpl.
      symmetry. apply map_id.
  Qed.

  Corollary length_typeof_numstreams : forall e,
      length (typeof e) = numstreams e.
  Proof.
    intros.
    rewrite typeof_annot.
    rewrite map_length.
    apply length_annot_numstreams.
  Qed.

  Fact typesof_annots : forall es,
      typesof es = map fst (annots es).
  Proof.
    induction es; simpl.
    - reflexivity.
    - rewrite map_app.
      f_equal; auto. apply typeof_annot.
  Qed.

  Corollary length_typesof_annots : forall es,
      length (typesof es) = length (annots es).
  Proof.
    intros es.
    rewrite typesof_annots.
    apply map_length.
  Qed.

  Fact typeof_concat_typesof : forall l,
      concat (map typeof (concat l)) = concat (map typesof l).
  Proof.
    intros l.
    unfold typesof.
    induction l; simpl.
    - reflexivity.
    - rewrite map_app. rewrite concat_app.
      rewrite flat_map_concat_map. f_equal; eauto.
  Qed.

  (** clocksof *)

  Fact clockof_annot : forall e,
      clockof e = map fst (map snd (annot e)).
  Proof.
    destruct e; simpl; try unfold clock_of_nclock, stripname; simpl; try reflexivity.
    - rewrite map_map. reflexivity.
    - destruct l0; simpl.
      repeat rewrite map_map.
      reflexivity.
    - destruct l1; simpl.
      repeat rewrite map_map.
      reflexivity.
    - destruct l1; simpl.
      repeat rewrite map_map.
      reflexivity.
    - rewrite map_map. reflexivity.
  Qed.

  Corollary length_clockof_numstreams : forall e,
      length (clockof e) = numstreams e.
  Proof.
    intros.
    rewrite clockof_annot.
    repeat rewrite map_length.
    apply length_annot_numstreams.
  Qed.

  Fact clocksof_annots : forall es,
      clocksof es = map fst (map snd (annots es)).
  Proof.
    induction es; simpl.
    - reflexivity.
    - repeat rewrite map_app.
      f_equal; auto. apply clockof_annot.
  Qed.

  Corollary length_clocksof_annots : forall es,
      length (clocksof es) = length (annots es).
  Proof.
    intros es.
    rewrite clocksof_annots. rewrite map_map.
    apply map_length.
  Qed.

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
    destruct e; simpl; unfold clock_of_nclock; try rewrite map_map; auto.
  Qed.

  Lemma clocksof_nclocksof:
    forall es,
      clocksof es = map stripname (nclocksof es).
  Proof.
    induction es as [|e es IH]; auto; simpl.
    now rewrite map_app, IH, <-clockof_nclockof.
  Qed.

  (*
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
   *)

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

  (** Interface equivalence between nodes *)

  Section interface_eq.

    (** Nodes are equivalent if their interface are equivalent,
        that is if they have the same identifier and the same
        input/output types *)
    Definition node_iface_eq n n' : Prop :=
      n.(n_name) = n'.(n_name) /\
      n.(n_hasstate) = n'.(n_hasstate) /\
      n.(n_in) = n'.(n_in) /\
      n.(n_out) = n'.(n_out).

    Fact node_iface_eq_refl : Reflexive node_iface_eq.
    Proof.
      intros n. repeat split.
    Qed.

    Fact node_iface_eq_sym : Symmetric node_iface_eq.
    Proof.
      intros n n' H.
      destruct H as [? [? [? ?]]].
      repeat split; symmetry; assumption.
    Qed.

    Fact node_iface_eq_trans : Transitive node_iface_eq.
    Proof.
      intros n1 n2 n3 H12 H23.
      destruct H12 as [? [? [? ?]]].
      destruct H23 as [? [? [? ?]]].
      repeat split; etransitivity; eauto.
    Qed.

    Global Instance node_iface_eq_eq : Equivalence node_iface_eq.
    Proof.
      constructor.
      - exact node_iface_eq_refl.
      - exact node_iface_eq_sym.
      - exact node_iface_eq_trans.
    Qed.

    (** Globals are equivalent if they contain equivalent nodes *)
    Definition global_iface_eq G G' : Prop :=
      forall f, orel node_iface_eq (find_node f G) (find_node f G').

    Fact global_eq_refl : Reflexive global_iface_eq.
    Proof.
      intros G f. reflexivity.
    Qed.

    Fact global_eq_sym : Symmetric global_iface_eq.
    Proof.
      intros G G' Heq f.
      specialize (Heq f).
      symmetry. assumption.
    Qed.

    Fact global_eq_trans : Transitive global_iface_eq.
    Proof.
      intros G1 G2 G3 Heq12 Heq23 f.
      specialize (Heq12 f). specialize (Heq23 f).
      etransitivity; eauto.
    Qed.

    Global Instance global_iface_eq_eq : Equivalence global_iface_eq.
    Proof.
      unfold global_iface_eq.
      constructor.
      - exact global_eq_refl.
      - exact global_eq_sym.
      - exact global_eq_trans.
    Qed.

    Fact global_iface_eq_cons : forall G G' n n',
        global_iface_eq G G' ->
        n.(n_name) = n'.(n_name) ->
        n.(n_hasstate) = n'.(n_hasstate) ->
        n.(n_in) = n'.(n_in) ->
        n.(n_out) = n'.(n_out) ->
        global_iface_eq (n::G) (n'::G').
    Proof.
      intros G G' n n' Heq Hname Hstate Hin Hout f.
      destruct (Pos.eq_dec (n_name n) f) eqn:Hname'.
      - subst. simpl. rewrite <- Hname.
        repeat rewrite ident_eqb_refl.
        right. repeat split; auto.
      - repeat rewrite find_node_tl; auto.
        congruence.
    Qed.

    Fact global_iface_eq_find : forall G G' f n,
        global_iface_eq G G' ->
        find_node f G = Some n ->
        exists n', (find_node f G' = Some n' /\
               node_iface_eq n n').
    Proof.
      intros G G' f n Hglob Hfind.
      specialize (Hglob f).
      inv Hglob; try congruence.
      rewrite Hfind in H. inv H.
      exists sy. auto.
    Qed.

  End interface_eq.

End LSYNTAX.

Module LSyntaxFun
       (Ids  : IDS)
       (Op   : OPERATORS) <: LSYNTAX Ids Op.
  Include LSYNTAX Ids Op.
End LSyntaxFun.
