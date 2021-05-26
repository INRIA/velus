From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import CommonTyping.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Coq Require Import PArith.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Setoid Morphisms.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

(** * The Lustre dataflow language *)

Module Type LSYNTAX
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks  : CLOCKS Ids Op OpAux).

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

  Definition idents xs := List.map (@fst ident (type * clock)) xs.

  Inductive exp : Type :=
  | Econst : cconst -> exp
  | Eenum  : enumtag -> type -> exp
  | Evar   : ident -> ann -> exp
  | Eunop  : unop -> exp -> ann -> exp
  | Ebinop : binop -> exp -> exp -> ann -> exp
  | Efby   : list exp -> list exp -> list exp -> list ann -> exp
  | Earrow : list exp -> list exp -> list exp -> list ann -> exp
  | Ewhen  : list exp -> ident -> enumtag -> lann -> exp
  | Emerge : ident * type -> list (list exp) -> lann -> exp
  | Ecase  : exp -> list (option (list exp)) -> list exp -> lann -> exp
  | Eapp   : ident -> list exp -> list exp -> list ann -> exp.

  Implicit Type e: exp.

  (** ** Equations *)

  Definition equation : Type := (list ident * list exp)%type.

  Implicit Type eqn: equation.

  (** ** Node *)

  Fixpoint numstreams (e: exp) : nat :=
    match e with
    | Econst _ | Eenum _ _ => 1
    | Efby _ _ _ anns
    | Earrow _ _ _ anns
    | Eapp _ _ _ anns => length anns
    | Evar _ _
    | Eunop _ _ _
    | Ebinop _ _ _ _ => 1
    | Ewhen _ _ _  (tys, _)
    | Emerge _ _ (tys, _)
    | Ecase _ _ _ (tys, _) => length tys
    end.

  (* Annotation (homogenized). *)

  Fixpoint annot (e: exp): list (type * nclock) :=
    match e with
    | Econst c => [(Tprimitive (ctype_cconst c), (Cbase, None))]
    | Eenum _ ty => [(ty, (Cbase, None))]
    | Efby _ _ _ anns
    | Earrow _ _ _ anns
    | Eapp _ _ _ anns => anns
    | Evar _ ann
    | Eunop _ _ ann
    | Ebinop _ _ _ ann => [ann]
    | Ewhen _ _ _  (tys, ck)
    | Emerge _ _ (tys, ck)
    | Ecase _ _ _ (tys, ck) => map (fun ty=> (ty, ck)) tys
    end.

  Definition annots (es: list exp): list (type * nclock) :=
    flat_map annot es.

  Fixpoint typeof (e: exp): list type :=
    match e with
    | Econst c => [Tprimitive (ctype_cconst c)]
    | Eenum _ ty => [ty]
    | Efby _ _ _ anns
    | Earrow _ _ _ anns
    | Eapp _ _ _ anns => map fst anns
    | Evar _ ann
    | Eunop _ _ ann
    | Ebinop _ _ _ ann => [fst ann]
    | Ewhen _ _ _ anns
    | Emerge _ _ anns
    | Ecase _ _ _ anns => fst anns
    end.

  Definition typesof (es: list exp): list type :=
    flat_map typeof es.

  Definition clock_of_nclock {A} (ann: A * nclock): clock := stripname (snd ann).
  Definition stream_name {A} (ann: A * nclock) : option ident := snd (snd ann).

  Definition unnamed_stream {A} (ann: A * nclock): Prop := snd (snd ann) = None.

  Fixpoint clockof (e: exp): list clock :=
    match e with
    | Econst _ | Eenum _ _ => [Cbase]
    | Efby _ _ _ anns
    | Earrow _ _ _ anns
    | Eapp _ _ _ anns => map clock_of_nclock anns
    | Evar _ ann
    | Eunop _ _ ann
    | Ebinop _ _ _ ann => [clock_of_nclock ann]
    | Ewhen _ _ _ anns
    | Emerge _ _ anns
    | Ecase _ _ _ anns => map (fun _ => clock_of_nclock anns) (fst anns)
    end.

  Definition clocksof (es: list exp): list clock :=
    flat_map clockof es.

  Fixpoint nclockof (e: exp): list nclock :=
    match e with
    | Econst _ | Eenum _ _ => [(Cbase, None)]
    | Efby _ _ _ anns
    | Earrow _ _ _ anns
    | Eapp _ _ _ anns => map snd anns
    | Evar _ ann
    | Eunop _ _ ann
    | Ebinop _ _ _ ann => [snd ann]
    | Ewhen _ _ _ anns
    | Emerge _ _ anns
    | Ecase _ _ _ anns => map (fun _ => snd anns) (fst anns)
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
    let fresh_ins := flat_map fresh_in in
    match e with
    | Econst _ | Eenum _ _ => []
    | Evar _ _ => []
    | Eunop _ e _ => fresh_in e
    | Ebinop _ e1 e2 _ => fresh_in e1 ++ fresh_in e2
    | Efby e0s es er _
    | Earrow e0s es er _ =>
      fresh_ins e0s ++ fresh_ins es ++ fresh_ins er
    | Ewhen es _ _ _ => fresh_ins es
    | Emerge _ es _ => flat_map fresh_ins es
    | Ecase e es d _ => fresh_in e ++ flat_map (or_default_with [] fresh_ins) es ++ fresh_ins d
    | Eapp _ es er anns => fresh_ins es ++ fresh_ins er ++ anon_streams anns
    end.

  Definition fresh_ins (es : list exp) : list (ident * (type * clock)) :=
    flat_map fresh_in es.

  Definition anon_in (e : exp) : list (ident * (type * clock)) :=
    match e with
    | Eapp _ es er _ => fresh_ins es++fresh_ins er
    | e => fresh_in e
    end.

  Definition anon_ins (es : list exp) : list (ident * (type * clock)) :=
    flat_map anon_in es.

  Definition anon_in_eq (eq : equation) : list (ident * (type * clock)) :=
    anon_ins (snd eq).

  Definition anon_in_eqs (eqs : list equation) : list (ident * (type * clock)) :=
    flat_map anon_in_eq eqs.


  Record node {prefs : PS.t} : Type :=
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
        n_good     :  Forall (AtomOrGensym prefs) (map fst (n_in ++ n_vars ++ n_out ++ anon_in_eqs n_eqs)) /\ atom n_name
      }.

  Instance node_unit {prefs} : ProgramUnit (@node prefs) :=
    { name := n_name; }.

  (** ** Program *)

  Record global {prefs} :=
    Global {
        enums : list (ident * nat);
        nodes : list (@node prefs);
      }.
  Arguments Global {_}.

  Program Instance global_program {prefs} : Program (@node prefs) global :=
    { units := nodes;
      update := fun g => Global g.(enums) }.

  Section find_node.
    Context {prefs : PS.t}.

    Definition find_node (f: ident) (G: @global prefs) :=
      option_map fst (find_unit f G).

    Lemma find_node_Exists:
      forall f G, find_node f G <> None <-> List.Exists (fun n=> f = n.(n_name)) (nodes G).
    Proof.
      intros f G.
      unfold find_node.
      now rewrite option_map_None, find_unit_Exists.
    Qed.

    Lemma find_node_now:
      forall f n G enums,
        n.(n_name) = f ->
        find_node f (Global enums (n::G)) = Some n.
    Proof.
      intros * Heq; subst.
      unfold find_node, find_unit; simpl.
      destruct (ident_eq_dec _ _); simpl; congruence.
    Qed.

    Lemma find_node_other:
      forall f n G enums,
        n.(n_name) <> f ->
        find_node f (Global enums (n::G)) = find_node f (Global enums G).
    Proof.
      intros * Hnf.
      unfold find_node. f_equal.
      eapply find_unit_other; eauto.
      now intros ?.
    Qed.

    Lemma find_node_cons f (a : @node prefs) enums nds n :
      find_node f (Global enums (a :: nds)) = Some n ->
      (f = n_name a /\ a = n) \/
      (f <> n_name a /\ find_node f (Global enums nds) = Some n).
    Proof.
      unfold find_node. intros Hfind.
      apply option_map_inv in Hfind as ((?&?)&Hfind&?); subst.
      eapply CommonProgram.find_unit_cons in Hfind as [(?&?)|(?&?)]; try reflexivity.
      - inv H0. eauto.
      - simpl in *. right.
        rewrite H0; auto.
    Qed.

  End find_node.

  Lemma equiv_program_enums {prefs} : forall (G G' : @global prefs),
      equiv_program G G' ->
      enums G = enums G'.
  Proof.
    intros * Heq.
    specialize (Heq []); inv Heq; auto.
  Qed.

  Corollary suffix_enums {prefs} : forall (G G' : @global prefs),
      suffix G G' ->
      enums G = enums G'.
  Proof.
    intros * Suff. inv Suff.
    apply equiv_program_enums; auto.
  Qed.

  (** Structural properties *)

  Section exp_ind2.

    Variable P : exp -> Prop.

    Hypothesis EconstCase:
      forall c,
        P (Econst c).

    Hypothesis EenumCase:
      forall k ty,
        P (Eenum k ty).

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
      forall e0s es er a,
        Forall P e0s ->
        Forall P es ->
        Forall P er ->
        P (Efby e0s es er a).

    Hypothesis EarrowCase:
      forall e0s es er a,
        Forall P e0s ->
        Forall P es ->
        Forall P er ->
        P (Earrow e0s es er a).

    Hypothesis EwhenCase:
      forall es x b a,
        Forall P es ->
        P (Ewhen es x b a).

    Hypothesis EmergeCase:
      forall x es a,
        Forall (Forall P) es ->
        P (Emerge x es a).

    Hypothesis EcaseCase:
      forall e es d a,
        P e ->
        Forall (LiftO True (Forall P)) es ->
        Forall P d ->
        P (Ecase e es d a).

    Hypothesis EappCase:
      forall f es er a,
        Forall P es ->
        Forall P er ->
        P (Eapp f es er a).

    Local Ltac SolveForall :=
      match goal with
      | |- Forall ?P ?l => induction l; auto
      | _ => idtac
      end.

    Fixpoint exp_ind2 (e: exp) : P e.
    Proof.
      destruct e.
      - apply EconstCase; auto.
      - apply EenumCase; auto.
      - apply EvarCase; auto.
      - apply EunopCase; auto.
      - apply EbinopCase; auto.
      - apply EfbyCase; SolveForall; auto.
      - apply EarrowCase; SolveForall; auto.
      - apply EwhenCase; SolveForall.
      - apply EmergeCase; SolveForall.
        constructor; auto. SolveForall.
      - apply EcaseCase; auto. 2:SolveForall.
        SolveForall. constructor; auto.
        destruct a; simpl. SolveForall. constructor.
      - apply EappCase; SolveForall; auto.
    Qed.

  End exp_ind2.

  (** annots *)

  Fact length_annot_numstreams : forall e,
      length (annot e) = numstreams e.
  Proof.
    destruct e; simpl; auto.
    - destruct l0. apply map_length.
    - destruct l0. apply map_length.
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
    - destruct l0; simpl.
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
    - destruct l0; simpl.
      repeat rewrite map_map.
      reflexivity.
    - destruct l0; simpl.
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
    - destruct l0; simpl.
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

  Corollary length_nclocksof_annots : forall es,
      length (nclocksof es) = length (annots es).
  Proof.
    intros es.
    rewrite nclocksof_annots.
    apply map_length.
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
    rewrite app_assoc; apply incl_appl; reflexivity.
  Qed.

  Corollary anon_ins_fresh_ins : forall es,
      incl (anon_ins es) (fresh_ins es).
  Proof.
    intros.
    unfold anon_ins, fresh_ins.
    induction es; simpl.
    - reflexivity.
    - apply incl_app; [apply incl_appl|apply incl_appr]; auto using anon_in_fresh_in.
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

  (** Interface equivalence between nodes *)

  Section interface_eq.
    Context {prefs1 prefs2 : PS.t}.

    (** Nodes are equivalent if their interface are equivalent,
        that is if they have the same identifier and the same
        input/output types *)
    Definition node_iface_eq (n : @node prefs1) (n' : @node prefs2) : Prop :=
      n.(n_name) = n'.(n_name) /\
      n.(n_hasstate) = n'.(n_hasstate) /\
      n.(n_in) = n'.(n_in) /\
      n.(n_out) = n'.(n_out).

    (** Globals are equivalent if they contain equivalent nodes *)
    Definition global_iface_eq (G : @global prefs1) (G' : @global prefs2) : Prop :=
      enums G = enums G' /\
      forall f, orel2 node_iface_eq (find_node f G) (find_node f G').

    Lemma global_iface_eq_nil : forall enums,
        global_iface_eq (Global enums []) (Global enums []).
    Proof.
      unfold global_iface_eq, find_node.
      constructor; auto.
      intros *; simpl. constructor.
    Qed.

    Lemma global_iface_eq_cons : forall enums nds nds' n n',
        global_iface_eq (Global enums nds) (Global enums nds') ->
        n.(n_name) = n'.(n_name) ->
        n.(n_hasstate) = n'.(n_hasstate) ->
        n.(n_in) = n'.(n_in) ->
        n.(n_out) = n'.(n_out) ->
        global_iface_eq (Global enums (n::nds)) (Global enums (n'::nds')).
    Proof.
      intros * (?&Heq) Hname Hstate Hin Hout.
      constructor; auto. intros ?.
      destruct (Pos.eq_dec (n_name n) f); subst.
      - simpl. repeat rewrite find_node_now; auto.
        repeat constructor; auto.
      - repeat rewrite find_node_other; auto.
        congruence.
    Qed.

    Lemma global_iface_eq_find : forall G G' f n,
        global_iface_eq G G' ->
        find_node f G = Some n ->
        exists n', (find_node f G' = Some n' /\
               node_iface_eq n n').
    Proof.
      intros G G' f n (_&Hglob) Hfind.
      specialize (Hglob f).
      inv Hglob; try congruence.
      rewrite Hfind in H. inv H.
      exists sy. auto.
    Qed.

  End interface_eq.

  Fact node_iface_eq_refl {prefs} : Reflexive (@node_iface_eq prefs prefs).
  Proof.
    intros n. repeat split.
  Qed.

  Fact node_iface_eq_sym {p1 p2} : forall (n1 : @node p1) (n2 : @node p2),
      node_iface_eq n1 n2 ->
      node_iface_eq n2 n1.
  Proof.
    intros * (?&?&?&?).
    constructor; auto.
  Qed.

  Fact node_iface_eq_trans {p1 p2 p3} : forall (n1 : @node p1) (n2 : @node p2) (n3 : @node p3),
      node_iface_eq n1 n2 ->
      node_iface_eq n2 n3 ->
      node_iface_eq n1 n3.
  Proof.
    intros n1 n2 n3 H12 H23.
    destruct H12 as [? [? [? ?]]].
    destruct H23 as [? [? [? ?]]].
    repeat split; etransitivity; eauto.
  Qed.

  Fact global_eq_refl {prefs} : Reflexive (@global_iface_eq prefs prefs).
  Proof.
    intros G. split; intros; try reflexivity.
    destruct (find_node f G); constructor.
    apply node_iface_eq_refl.
  Qed.

  Fact global_iface_eq_sym {p1 p2} : forall (G1 : @global p1) (G2 : @global p2),
      global_iface_eq G1 G2 ->
      global_iface_eq G2 G1.
  Proof.
    intros * H12.
    inv H12. constructor; auto.
    intros f. specialize (H0 f).
    inv H0; constructor; auto.
    apply node_iface_eq_sym; auto.
  Qed.

  Fact global_iface_eq_trans {p1 p2 p3} : forall (n1 : @global p1) (n2 : @global p2) (n3 : @global p3),
      global_iface_eq n1 n2 ->
      global_iface_eq n2 n3 ->
      global_iface_eq n1 n3.
  Proof.
    intros n1 n2 n3 H12 H23.
    destruct H12 as [? H12].
    destruct H23 as [? H23].
    split; try congruence.
    intros f. specialize (H12 f). specialize (H23 f).
    inv H12; inv H23; try congruence; constructor.
    rewrite <-H2 in H4. inv H4.
    eapply node_iface_eq_trans; eauto.
  Qed.

  (** ** Property of length in expressions; is implied by wc and wt *)

  Inductive wl_exp {prefs} : (@global prefs) -> exp -> Prop :=
  | wl_Const : forall G c,
      wl_exp G (Econst c)
  | wl_Enum : forall G k ty,
      wl_exp G (Eenum k ty)
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
  | wl_Efby : forall G e0s es er anns,
      Forall (wl_exp G) e0s ->
      Forall (wl_exp G) es ->
      Forall (wl_exp G) er ->
      length (annots e0s) = length anns ->
      length (annots es) = length anns ->
      Forall (fun e => numstreams e = 1) er ->
      wl_exp G (Efby e0s es er anns)
  | wl_Earrow : forall G e0s es er anns,
      Forall (wl_exp G) e0s ->
      Forall (wl_exp G) es ->
      Forall (wl_exp G) er ->
      length (annots e0s) = length anns ->
      length (annots es) = length anns ->
      Forall (fun e => numstreams e = 1) er ->
      wl_exp G (Earrow e0s es er anns)
  | wl_Ewhen : forall G es x b tys nck,
      Forall (wl_exp G) es ->
      length (annots es) = length tys ->
      wl_exp G (Ewhen es x b (tys, nck))
  | wl_Emerge : forall G x es tys nck,
      es <> nil ->
      Forall (Forall (wl_exp G)) es ->
      Forall (fun es => length (annots es) = length tys) es ->
      wl_exp G (Emerge x es (tys, nck))
  | wl_Ecase : forall G e brs d tys nck,
      wl_exp G e ->
      numstreams e = 1 ->
      brs <> nil ->
      (forall es, In (Some es) brs -> Forall (wl_exp G) es) ->
      (forall es, In (Some es) brs -> length (annots es) = length tys) ->
      Forall (wl_exp G) d ->
      length (annots d) = length tys ->
      wl_exp G (Ecase e brs d (tys, nck))
  | wl_Eapp : forall G f n es er anns,
      Forall (wl_exp G) es ->
      Forall (wl_exp G) er ->
      Forall (fun e => numstreams e = 1) er ->
      find_node f G = Some n ->
      length (annots es) = length (n_in n) ->
      length anns = length (n_out n) ->
      wl_exp G (Eapp f es er anns).

  Definition wl_equation {prefs} (G : @global prefs) (eq : equation) :=
    let (xs, es) := eq in
    Forall (wl_exp G) es /\ length xs = length (annots es).

  Definition wl_node {prefs} (G : @global prefs) (n : @node prefs) :=
    Forall (wl_equation G) (n_eqs n).

  Definition wl_global {prefs} : @global prefs -> Prop :=
    wt_program wl_node.

  (** *** fresh_in, anon_in properties *)

  Fact fresh_in_incl : forall e es,
      In e es ->
      incl (fresh_in e) (fresh_ins es).
  Proof.
    intros e es Hin.
    unfold fresh_ins.
    rewrite flat_map_concat_map.
    apply incl_concat_map; auto.
  Qed.

  Fact anon_in_incl : forall e es,
      In e es ->
      incl (anon_in e) (anon_ins es).
  Proof.
    intros e es Hin.
    unfold anon_ins.
    rewrite flat_map_concat_map.
    apply incl_concat_map; auto.
  Qed.

  Fact anon_in_eq_incl : forall eq eqs,
      In eq eqs ->
      incl (anon_in_eq eq) (anon_in_eqs eqs).
  Proof.
    intros e es Hin.
    unfold anon_in_eqs.
    rewrite flat_map_concat_map.
    apply incl_concat_map; auto.
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

  Lemma node_NoDup {prefs} : forall (n : @node prefs),
      NoDup (map fst (n_in n ++ n_vars n ++ n_out n)).
  Proof.
    intros n.
    rewrite <- fst_NoDupMembers.
    specialize (n_nodup n) as Hnd.
    repeat rewrite app_assoc in *.
    apply NoDupMembers_app_l in Hnd; auto.
  Qed.

  Lemma in_vars_defined_NoDup {prefs} : forall (n : @node prefs),
      NoDup (map fst (n_in n) ++ vars_defined (n_eqs n)).
  Proof.
    intros n.
    destruct n; simpl. clear - n_nodup0 n_defd0.
    rewrite n_defd0. rewrite <- map_app, <- fst_NoDupMembers.
    repeat rewrite app_assoc in *. apply NoDupMembers_app_l in n_nodup0; auto.
  Qed.

  Corollary NoDup_vars_defined_n_eqs {prefs} : forall (n : @node prefs),
      NoDup (vars_defined n.(n_eqs)).
  Proof.
    intros n.
    specialize (in_vars_defined_NoDup n) as Hnd.
    apply NoDup_app_r in Hnd; auto.
  Qed.

  Instance vars_defined_Proper:
    Proper (@Permutation equation ==> @Permutation ident)
           vars_defined.
  Proof.
    intros eqs eqs' Hperm; subst.
    unfold vars_defined. rewrite Hperm. reflexivity.
  Qed.

  Fact vars_defined_app : forall eqs1 eqs2,
      vars_defined (eqs1++eqs2) = vars_defined eqs1 ++ vars_defined eqs2.
  Proof.
    intros.
    unfold vars_defined. rewrite flat_map_app; auto.
  Qed.
End LSYNTAX.

Module LSyntaxFun
       (Ids      : IDS)
       (Op       : OPERATORS)
       (OpAux    : OPERATORS_AUX Ids Op)
       (Cks      : CLOCKS Ids Op OpAux) <: LSYNTAX Ids Op OpAux Cks.
  Include LSYNTAX Ids Op OpAux Cks.
End LSyntaxFun.
