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
  | Earrow : list exp -> list exp -> list ann -> exp
  (* | Epre   : list exp -> list ann -> exp *)
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
    | Earrow _ _ anns
    (* | Epre _ anns *)
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
    | Earrow _ _ anns
    (* | Epre _ anns *)
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
    | Earrow _ _ anns
    (* | Epre _ anns *)
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
    | Earrow _ _ anns
    (* | Epre _ anns *)
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
    | Earrow _ _ anns
    (* | Epre _ anns *)
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

  Definition anon_streams (anns : list ann) :=
    map_filter (fun '(ty, (cl, name)) => match name with
                                      | None => None
                                      | Some x => Some (x, (ty, cl))
                                      end) anns.

  Fixpoint fresh_in (e : exp) : list (ident * (type * clock)) :=
    match e with
    | Econst _ => []
    | Evar _ _ => []
    | Eunop _ e _ => fresh_in e
    | Ebinop _ e1 e2 _ => (fresh_in e1)++(fresh_in e2)
    | Efby e0s es _
    | Earrow e0s es _ => concat (map fresh_in e0s)++concat (map fresh_in es)
    | Ewhen es _ _ _ (* | Epre es _ *) => concat (map fresh_in es)
    | Emerge _ ets efs _ => concat (map fresh_in ets)++concat (map fresh_in efs)
    | Eite e ets efs _ => (fresh_in e)++concat (map fresh_in ets)++concat (map fresh_in efs)
    | Eapp _ es None anns => concat (map fresh_in es)++anon_streams anns
    | Eapp _ es (Some r) anns => concat (map fresh_in es)++fresh_in r++anon_streams anns
    end.

  Definition fresh_ins (es : list exp) : list (ident * (type * clock)) :=
    concat (map fresh_in es).

  Definition anon_in (e : exp) : list (ident * (type * clock)) :=
    match e with
    | Eapp _ es None _ => fresh_ins es
    | Eapp _ es (Some r) _ => fresh_ins es++fresh_in r
    | e => fresh_in e
    end.

  Definition anon_ins (es : list exp) : list (ident * (type * clock)) :=
    concat (map anon_in es).

  Definition anon_in_eq (eq : equation) : list (ident * (type * clock)) :=
    anon_ins (snd eq).

  Definition anon_in_eqs (eqs : list equation) : list (ident * (type * clock)) :=
    concat (map anon_in_eq eqs).

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
        n_nodup    : NoDupMembers (n_in ++ n_vars ++ n_out ++ anon_in_eqs n_eqs);
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

    Hypothesis EarrowCase:
      forall e0s es a,
        Forall P e0s ->
        Forall P es ->
        P (Earrow e0s es a).

    (* Hypothesis EpreCase: *)
    (*   forall es a, *)
    (*     Forall P es -> *)
    (*     P (Epre es a). *)

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
      - apply EarrowCase; SolveForall.
      (* - apply EpreCase; SolveForall. *)
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
    - rewrite map_map. reflexivity.
    (* - rewrite map_map. reflexivity. *)
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

  Fact clockof_concat_clocksof : forall l,
      concat (map clockof (concat l)) = concat (map clocksof l).
  Proof.
    intros l.
    unfold clocksof.
    induction l; simpl.
    - reflexivity.
    - rewrite map_app, concat_app, flat_map_concat_map.
      f_equal; eauto.
  Qed.

  (** nclockof and nclocksof *)

  Fact nclockof_annot : forall e,
      nclockof e = map snd (annot e).
  Proof.
    destruct e; simpl; try reflexivity.
    - destruct l0; simpl.
      repeat rewrite map_map.
      reflexivity.
    - destruct l1; simpl.
      repeat rewrite map_map.
      reflexivity.
    - destruct l1; simpl.
      repeat rewrite map_map.
      reflexivity.
  Qed.

  Corollary length_nclockof_numstreams : forall e,
      length (nclockof e) = numstreams e.
  Proof.
    intros.
    rewrite nclockof_annot.
    repeat rewrite map_length.
    apply length_annot_numstreams.
  Qed.

  Fact nclocksof_annots : forall es,
      nclocksof es = map snd (annots es).
  Proof.
    induction es; simpl.
    - reflexivity.
    - repeat rewrite map_app.
      f_equal; auto. apply nclockof_annot.
  Qed.

  Lemma clockof_nclockof:
    forall e,
      clockof e = map stripname (nclockof e).
  Proof.
    destruct e; simpl; unfold clock_of_nclock; try rewrite map_map; auto.
  Qed.

  Lemma nclockof_length :
    forall e, length (nclockof e) = length (clockof e).
  Proof.
    intros e. rewrite clockof_nclockof, map_length; auto.
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

  Corollary In_snd_nclocksof:
    forall n es,
      In n (map snd (nclocksof es)) ->
      exists e, In e es /\ In n (map snd (nclockof e)).
  Proof.
    intros * Hin. apply in_map_iff in Hin as (?&?&Hin).
    apply In_nclocksof in Hin as (e&?&?).
    exists e. split; auto. apply in_map_iff; eauto.
  Qed.

  (** fresh_in and anon_in specification and properties *)

  Lemma anon_in_fresh_in : forall e,
      incl (anon_in e) (fresh_in e).
  Proof.
    destruct e; simpl; try reflexivity.
    destruct o; try rewrite app_assoc; apply incl_appl; reflexivity.
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

  Lemma fresh_ins_nil:
    forall e es,
      fresh_ins (e::es) = [] ->
      fresh_in e = [].
  Proof.
    intros e es Hfresh.
    unfold fresh_ins in Hfresh; simpl in Hfresh.
    apply app_eq_nil in Hfresh as [? _]; auto.
  Qed.

  Lemma find_node_In : forall G n,
      In n G ->
      NoDup (map n_name G) ->
      find_node (n_name n) G = Some n.
  Proof.
    intros * Hin Hndup.
    induction G; inv Hin; simpl in *.
    - destruct ident_eqb eqn:Hident; auto.
      rewrite ident_eqb_neq in Hident; congruence.
    - inv Hndup. destruct ident_eqb eqn:Hident; auto.
      exfalso. rewrite ident_eqb_eq in Hident.
      apply H2. rewrite Hident, in_map_iff.
      exists n; auto.
  Qed.

  Lemma find_node_incl : forall f G G' n,
      incl G G' ->
      NoDup (map n_name G) ->
      NoDup (map n_name G') ->
      find_node f G = Some n ->
      find_node f G' = Some n.
  Proof.
    intros * Hincl Hndup1 Hndup2 Hfind.
    induction G; simpl in *; try congruence.
    apply incl_cons' in Hincl as [Hin Hincl].
    destruct ident_eqb eqn:Hident.
    - clear IHG Hincl. rewrite ident_eqb_eq in Hident; subst.
      inv Hfind. apply find_node_In; auto.
    - clear Hin. inv Hndup1.
      specialize (IHG Hincl H2 Hfind); auto.
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

  (** ** Property of length in expressions; is implied by wc and wt *)

  Inductive wl_exp : global -> exp -> Prop :=
  | wl_Const : forall G c,
      wl_exp G (Econst c)
  | wl_Evar : forall G x a,
      wl_exp G (Evar x a)
  | wl_Eunop : forall G op e a,
      wl_exp G e ->
      numstreams e = 1 ->
      wl_exp G (Eunop op e a)
  | wl_Ebinop : forall G op e1 e2 a,
      wl_exp G e1 ->
      wl_exp G e2 ->
      numstreams e1 = 1 ->
      numstreams e2 = 1 ->
      wl_exp G (Ebinop op e1 e2 a)
  | wl_Efby : forall G e0s es anns,
      Forall (wl_exp G) e0s ->
      Forall (wl_exp G) es ->
      length (annots e0s) = length anns ->
      length (annots es) = length anns ->
      wl_exp G (Efby e0s es anns)
  | wl_Earrow : forall G e0s es anns,
      Forall (wl_exp G) e0s ->
      Forall (wl_exp G) es ->
      length (annots e0s) = length anns ->
      length (annots es) = length anns ->
      wl_exp G (Earrow e0s es anns)
  (* | wl_Epre : forall G es anns, *)
  (*     Forall (wl_exp G) es -> *)
  (*     length (annots es) = length anns -> *)
  (*     wl_exp G (Epre es anns) *)
  | wl_Ewhen : forall G es x b tys nck,
      Forall (wl_exp G) es ->
      length (annots es) = length tys ->
      wl_exp G (Ewhen es x b (tys, nck))
  | wl_Emerge : forall G x ets efs tys nck,
      Forall (wl_exp G) ets ->
      Forall (wl_exp G) efs ->
      length (annots ets) = length tys ->
      length (annots efs) = length tys ->
      wl_exp G (Emerge x ets efs (tys, nck))
  | wl_Eifte : forall G e ets efs tys nck,
      wl_exp G e ->
      Forall (wl_exp G) ets ->
      Forall (wl_exp G) efs ->
      numstreams e = 1 ->
      length (annots ets) = length tys ->
      length (annots efs) = length tys ->
      wl_exp G (Eite e ets efs (tys, nck))
  | wl_Eapp : forall G f n es anns,
      Forall (wl_exp G) es ->
      find_node f G = Some n ->
      length (annots es) = length (n_in n) ->
      length anns = length (n_out n) ->
      wl_exp G (Eapp f es None anns)
  | wl_EappReset : forall G f n es r anns,
      wl_exp G r ->
      Forall (wl_exp G) es ->
      numstreams r = 1 ->
      find_node f G = Some n ->
      length (annots es) = length (n_in n) ->
      length anns = length (n_out n) ->
      wl_exp G (Eapp f es (Some r) anns).

  Definition wl_equation G (eq : equation) :=
    let (xs, es) := eq in
    Forall (wl_exp G) es /\ length xs = length (annots es).

  Definition wl_node G (n : node) :=
    Forall (wl_equation G) (n_eqs n).

  Inductive wl_global : global -> Prop :=
  | wlg_nil:
      wl_global []
  | wlg_cons: forall n ns,
      wl_global ns ->
      wl_node ns n ->
      wl_global (n::ns).

  Definition global_wl := { G : global | wl_global G}.
  Definition proj1_global (G : global_wl) := proj1_sig G.
  Coercion proj1_global : global_wl >-> global.

  (** *** fresh_in, anon_in properties *)

  Fact fresh_in_incl : forall e es,
      In e es ->
      incl (fresh_in e) (fresh_ins es).
  Proof.
    intros e es Hin.
    unfold fresh_ins. apply incl_concat_map; auto.
  Qed.

  Fact anon_in_incl : forall e es,
      In e es ->
      incl (anon_in e) (anon_ins es).
  Proof.
    intros e es Hin.
    unfold anon_ins. apply incl_concat_map; auto.
  Qed.

  Fact anon_in_eq_incl : forall eq eqs,
      In eq eqs ->
      incl (anon_in_eq eq) (anon_in_eqs eqs).
  Proof.
    intros e es Hin.
    unfold anon_in_eqs. apply incl_concat_map; auto.
  Qed.

  Fact InMembers_fresh_in : forall x e es,
      In e es ->
      InMembers x (fresh_in e) ->
      InMembers x (fresh_ins es).
  Proof.
    intros * Hin Hinm.
    eapply fresh_in_incl, incl_map with (f:=fst) in Hin.
    rewrite fst_InMembers in *. eauto.
  Qed.

  Fact InMembers_anon_in : forall x e es,
      In e es ->
      InMembers x (anon_in e) ->
      InMembers x (anon_ins es).
  Proof.
    intros * Hin Hinm.
    eapply anon_in_incl, incl_map with (f:=fst) in Hin.
    rewrite fst_InMembers in *. eauto.
  Qed.

  Fact InMembers_anon_in_eq : forall x eq eqs,
      In eq eqs ->
      InMembers x (anon_in_eq eq) ->
      InMembers x (anon_in_eqs eqs).
  Proof.
    intros * Hin Hinm.
    eapply anon_in_eq_incl, incl_map with (f:=fst) in Hin.
    rewrite fst_InMembers in *. eauto.
  Qed.

  Fact Ino_In_anon_streams : forall x anns,
      Ino x (map (fun x => snd (snd x)) anns) ->
      InMembers x (anon_streams anns).
  Proof.
    intros x anns H.
    rewrite Ino_In, in_map_iff in H; destruct H as [[? [? ?]] [? ?]]; simpl in *; subst.
    rewrite fst_InMembers, in_map_iff.
    exists (x, (t, c)); split; auto.
    eapply map_filter_In; eauto.
  Qed.

  Fact NoDupMembers_fresh_in : forall e es,
      In e es ->
      NoDupMembers (fresh_ins es) ->
      NoDupMembers (fresh_in e).
  Proof.
    intros * Hin Hndup.
    unfold fresh_ins in *.
    induction es; inv Hin; simpl in Hndup.
    - apply NoDupMembers_app_l in Hndup; auto.
    - apply NoDupMembers_app_r in Hndup; auto.
  Qed.

  Corollary NoDupMembers_fresh_in' : forall vars e es,
      In e es ->
      NoDupMembers (vars ++ fresh_ins es) ->
      NoDupMembers (vars ++ fresh_in e).
  Proof.
    intros * Hin Hndup.
    apply NoDupMembers_app.
    - apply NoDupMembers_app_l in Hndup; auto.
    - apply NoDupMembers_app_r in Hndup; auto.
      eapply NoDupMembers_fresh_in; eauto.
    - intros x HIn contra.
      eapply NoDupMembers_app_InMembers in Hndup; eauto.
      eapply InMembers_fresh_in in contra; eauto.
  Qed.

  Fact NoDupMembers_anon_in : forall e es,
      In e es ->
      NoDupMembers (anon_ins es) ->
      NoDupMembers (anon_in e).
  Proof.
    intros * Hin Hndup.
    unfold anon_ins in *.
    induction es; inv Hin; simpl in Hndup.
    - apply NoDupMembers_app_l in Hndup; auto.
    - apply NoDupMembers_app_r in Hndup; auto.
  Qed.

  Corollary NoDupMembers_anon_in' : forall vars e es,
      In e es ->
      NoDupMembers (vars ++ anon_ins es) ->
      NoDupMembers (vars ++ anon_in e).
  Proof.
    intros * Hin Hndup.
    apply NoDupMembers_app.
    - apply NoDupMembers_app_l in Hndup; auto.
    - apply NoDupMembers_app_r in Hndup; auto.
      eapply NoDupMembers_anon_in; eauto.
    - intros x HIn contra.
      eapply NoDupMembers_app_InMembers in Hndup; eauto.
      eapply InMembers_anon_in in contra; eauto.
  Qed.

  Fact NoDupMembers_anon_in_eq : forall eq eqs,
      In eq eqs ->
      NoDupMembers (anon_in_eqs eqs) ->
      NoDupMembers (anon_in_eq eq).
  Proof.
    intros * Hin Hndup.
    unfold fresh_ins in *.
    induction eqs; inv Hin; simpl in Hndup.
    - apply NoDupMembers_app_l in Hndup; auto.
    - apply NoDupMembers_app_r in Hndup; auto.
  Qed.

  Corollary NoDupMembers_anon_in_eq' : forall vars eq eqs,
      In eq eqs ->
      NoDupMembers (vars ++ anon_in_eqs eqs) ->
      NoDupMembers (vars ++ anon_in_eq eq).
  Proof.
    intros * Hin Hndup.
    apply NoDupMembers_app.
    - apply NoDupMembers_app_l in Hndup; auto.
    - apply NoDupMembers_app_r in Hndup; auto.
      eapply NoDupMembers_anon_in_eq; eauto.
    - intros x HIn contra.
      eapply NoDupMembers_app_InMembers in Hndup; eauto.
      eapply InMembers_anon_in_eq in contra; eauto.
  Qed.

  (** *** Additional properties *)

  Lemma node_NoDup : forall n,
      NoDup (map fst (n_in n ++ n_vars n ++ n_out n)).
  Proof.
    intros n.
    rewrite <- fst_NoDupMembers.
    specialize (n_nodup n) as Hnd.
    repeat rewrite app_assoc in *.
    apply NoDupMembers_app_l in Hnd; auto.
  Qed.

  Lemma in_vars_defined_NoDup : forall n,
      NoDup (map fst (n_in n) ++ vars_defined (n_eqs n)).
  Proof.
    intros n.
    destruct n; simpl. clear - n_nodup0 n_defd0.
    rewrite n_defd0. rewrite <- map_app, <- fst_NoDupMembers.
    repeat rewrite app_assoc in *. apply NoDupMembers_app_l in n_nodup0; auto.
  Qed.

  Corollary NoDup_vars_defined_n_eqs:
    forall n,
      NoDup (vars_defined n.(n_eqs)).
  Proof.
    intros n.
    specialize (in_vars_defined_NoDup n) as Hnd.
    apply NoDup_app_r in Hnd; auto.
  Qed.

End LSYNTAX.

Module LSyntaxFun
       (Ids  : IDS)
       (Op   : OPERATORS) <: LSYNTAX Ids Op.
  Include LSYNTAX Ids Op.
End LSyntaxFun.
