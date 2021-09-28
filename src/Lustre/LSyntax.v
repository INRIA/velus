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

  Definition idents xs := List.map (@fst ident (type * clock * ident)) xs.

  Inductive exp : Type :=
  | Econst : cconst -> exp
  | Eenum  : enumtag -> type -> exp
  | Evar   : ident -> ann -> exp
  | Eunop  : unop -> exp -> ann -> exp
  | Ebinop : binop -> exp -> exp -> ann -> exp
  | Efby   : list exp -> list exp -> list ann -> exp
  | Earrow : list exp -> list exp -> list ann -> exp
  | Ewhen  : list exp -> ident -> enumtag -> lann -> exp
  | Emerge : ident * type -> list (enumtag * list exp) -> lann -> exp
  | Ecase  : exp -> list (enumtag * list exp) -> option (list exp) -> lann -> exp
  | Eapp   : ident -> list exp -> list exp -> list ann -> exp.

  Implicit Type e: exp.

  (** ** Equations *)

  Definition equation : Type := (list ident * list exp)%type.

  Implicit Type eqn: equation.

  (** ** Blocks *)

  Inductive block : Type :=
  | Beq : equation -> block
  | Breset : list block -> exp -> block
  | Blocal : list (ident * (type * clock * ident)) -> list block -> block.

  (** ** Node *)

  Fixpoint numstreams (e: exp) : nat :=
    match e with
    | Econst _ | Eenum _ _ => 1
    | Efby _ _ anns
    | Earrow _ _ anns
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
    | Efby _ _ anns
    | Earrow _ _ anns
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
    | Efby _ _ anns
    | Earrow _ _ anns
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
    | Efby _ _ anns
    | Earrow _ _ anns
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
    | Efby _ _ anns
    | Earrow _ _ anns
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

  Fixpoint vars_defined (d : block) :=
    match d with
    | Beq eq => fst eq
    | Breset blocks _ => flat_map vars_defined blocks
    | Blocal locals blocks =>
      List.filter (fun x => negb (mem_assoc_ident x locals))
                  (flat_map vars_defined blocks)
    end.

  Inductive VarsDefined : block -> list ident -> Prop :=
  | LVDeq : forall eq, VarsDefined (Beq eq) (fst eq)
  | LVDreset : forall blocks er xs,
      Forall2 VarsDefined blocks xs ->
      VarsDefined (Breset blocks er) (concat xs)
  | LVDlocal : forall locs blocks xs ys,
      Forall2 VarsDefined blocks xs ->
      Permutation (map fst locs ++ ys) (concat xs) ->
      VarsDefined (Blocal locs blocks) ys.

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
    | Efby e0s es _
    | Earrow e0s es _ =>
      fresh_ins e0s ++ fresh_ins es
    | Ewhen es _ _ _ => fresh_ins es
    | Emerge _ es _ => flat_map (fun es => fresh_ins (snd es)) es
    | Ecase e es d _ => fresh_in e ++ flat_map (fun es => fresh_ins (snd es)) es ++ or_default_with [] fresh_ins d
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

  Fixpoint local_anon_in_block (d : block) : list (ident * (type * clock)) :=
    match d with
    | Beq eq => anon_in_eq eq
    | Breset blks er => (flat_map local_anon_in_block blks)++(fresh_in er)
    | Blocal _ _ => []
    end.

  Fixpoint anon_in_block (blk : block) : list (ident * (type * clock)) :=
    match blk with
    | Beq eq => anon_in_eq eq
    | Breset blks er => (flat_map anon_in_block blks)++(fresh_in er)
    | Blocal _ blks => flat_map anon_in_block blks
    end.

  Fixpoint locals (d : block) : list (ident * (type * clock * ident)) :=
    match d with
    | Beq _ => []
    | Breset blocks _ => flat_map locals blocks
    | Blocal loc blocks => loc ++ (flat_map locals blocks)
    end.

  (** Shadowing is prohibited *)
  Inductive NoDupLocals : list ident -> block -> Prop :=
  | NDLeq : forall env eq, NoDupLocals env (Beq eq)
  | NDLreset : forall env blocks er,
      Forall (NoDupLocals env) blocks ->
      NoDupLocals env (Breset blocks er)
  | NDLlocal : forall env locs blocks,
      Forall (NoDupLocals (env++map fst locs)) blocks ->
      NoDupMembers locs ->
      (forall x, InMembers x locs -> ~In x env) ->
      NoDupLocals env (Blocal locs blocks).

  Inductive GoodLocals (prefs : PS.t) : block -> Prop :=
  | GoodEq : forall eq,
      GoodLocals prefs (Beq eq)
  | GoodReset : forall blks er,
      Forall (GoodLocals prefs) blks ->
      GoodLocals prefs (Breset blks er)
  | GoodLocal : forall locs blks,
      Forall (AtomOrGensym prefs) (map fst locs) ->
      Forall (GoodLocals prefs) blks ->
      GoodLocals prefs (Blocal locs blks).

  Record node {PSyn : block -> Prop} {prefs : PS.t} : Type :=
    mk_node {
        n_name     : ident;
        n_hasstate : bool;
        n_in       : list (ident * (type * clock * ident));
        n_out      : list (ident * (type * clock * ident));
        n_block    : block;

        n_ingt0    : 0 < length n_in;
        n_outgt0   : 0 < length n_out;
        n_defd     : exists xs, VarsDefined n_block xs /\ Permutation xs (map fst n_out);
        n_nodup    : NoDupMembers (idty (n_in ++ n_out) ++ anon_in_block n_block) /\
                     NoDupLocals (map fst (n_in ++ n_out) ++ map fst (anon_in_block n_block)) n_block;
        n_good     : Forall (AtomOrGensym prefs) (map fst (n_in ++ n_out) ++ map fst (anon_in_block n_block))
                     /\ GoodLocals prefs n_block
                     /\ atom n_name;
        n_syn      : PSyn n_block;
      }.

  Instance node_unit {PSyn prefs} : ProgramUnit (@node PSyn prefs) :=
    { name := n_name; }.

  (** ** Program *)

  Record global {PSyn prefs} :=
    Global {
        enums : list (ident * nat);
        nodes : list (@node PSyn prefs);
      }.
  Arguments Global {_ _}.

  Program Instance global_program {PSyn prefs} : Program (@node PSyn prefs) global :=
    { units := nodes;
      update := fun g => Global g.(enums) }.

  Section find_node.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.

    Definition find_node (f: ident) (G: @global PSyn prefs) :=
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

    Lemma find_node_cons f (a : @node PSyn prefs) enums nds n :
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

  Lemma equiv_program_enums {PSyn prefs} : forall (G G' : @global PSyn prefs),
      equiv_program G G' ->
      enums G = enums G'.
  Proof.
    intros * Heq.
    specialize (Heq []); inv Heq; auto.
  Qed.

  Corollary suffix_enums {PSyn prefs} : forall (G G' : @global PSyn prefs),
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
      forall e0s es a,
        Forall P e0s ->
        Forall P es ->
        P (Efby e0s es a).

    Hypothesis EarrowCase:
      forall e0s es a,
        Forall P e0s ->
        Forall P es ->
        P (Earrow e0s es a).

    Hypothesis EwhenCase:
      forall es x b a,
        Forall P es ->
        P (Ewhen es x b a).

    Hypothesis EmergeCase:
      forall x es a,
        Forall (fun es => Forall P (snd es)) es ->
        P (Emerge x es a).

    Hypothesis EcaseCase:
      forall e es d a,
        P e ->
        Forall (fun es => Forall P (snd es)) es ->
        LiftO True (Forall P) d ->
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
      - apply EcaseCase; auto.
        + SolveForall. constructor; auto. SolveForall.
        + destruct o; simpl; auto. SolveForall.
      - apply EappCase; SolveForall; auto.
    Qed.

  End exp_ind2.

  Section block_ind2.

    Variable P : block -> Prop.

    Hypothesis BeqCase:
      forall eq,
        P (Beq eq).

    Hypothesis BresetCase:
      forall blocks er,
        Forall P blocks ->
        P (Breset blocks er).

    Hypothesis BlocalCase:
      forall locs blocks,
        Forall P blocks ->
        P (Blocal locs blocks).

    Fixpoint block_ind2 (d: block) : P d.
    Proof.
      destruct d.
      - apply BeqCase; auto.
      - apply BresetCase; induction l; auto.
      - apply BlocalCase; induction l0; auto.
    Qed.

  End block_ind2.

  (** annots *)

  Fact length_annot_numstreams : forall e,
      length (annot e) = numstreams e.
  Proof.
    destruct e; simpl; auto.
    - destruct l0. apply map_length.
    - destruct l0. apply map_length.
    - destruct l0. apply map_length.
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
    - destruct l0; simpl.
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
    - destruct l0; simpl.
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
    - destruct l0; simpl.
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
    Context {PSyn1 PSyn2 : block -> Prop}.
    Context {prefs1 prefs2 : PS.t}.

    (** Nodes are equivalent if their interface are equivalent,
        that is if they have the same identifier and the same
        input/output types *)
    Definition node_iface_eq (n : @node PSyn1 prefs1) (n' : @node PSyn2 prefs2) : Prop :=
      n.(n_name) = n'.(n_name) /\
      n.(n_hasstate) = n'.(n_hasstate) /\
      n.(n_in) = n'.(n_in) /\
      n.(n_out) = n'.(n_out).

    (** Globals are equivalent if they contain equivalent nodes *)
    Definition global_iface_eq (G : @global PSyn1 prefs1) (G' : @global PSyn2 prefs2) : Prop :=
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

  Fact node_iface_eq_refl {PSyn prefs} : Reflexive (@node_iface_eq PSyn _ prefs _).
  Proof.
    intros n. repeat split.
  Qed.

  Fact node_iface_eq_sym {P1 P2 p1 p2} : forall (n1 : @node P1 p1) (n2 : @node P2 p2),
      node_iface_eq n1 n2 ->
      node_iface_eq n2 n1.
  Proof.
    intros * (?&?&?&?).
    constructor; auto.
  Qed.

  Fact node_iface_eq_trans {P1 P2 P3 p1 p2 p3} : forall (n1 : @node P1 p1) (n2 : @node P2 p2) (n3 : @node P3 p3),
      node_iface_eq n1 n2 ->
      node_iface_eq n2 n3 ->
      node_iface_eq n1 n3.
  Proof.
    intros n1 n2 n3 H12 H23.
    destruct H12 as [? [? [? ?]]].
    destruct H23 as [? [? [? ?]]].
    repeat split; etransitivity; eauto.
  Qed.

  Fact global_eq_refl {PSyn prefs} : Reflexive (@global_iface_eq PSyn _ prefs _).
  Proof.
    intros G. split; intros; try reflexivity.
    destruct (find_node f G); constructor.
    apply node_iface_eq_refl.
  Qed.

  Fact global_iface_eq_sym {P1 P2 p1 p2} : forall (G1 : @global P1 p1) (G2 : @global P2 p2),
      global_iface_eq G1 G2 ->
      global_iface_eq G2 G1.
  Proof.
    intros * H12.
    inv H12. constructor; auto.
    intros f. specialize (H0 f).
    inv H0; constructor; auto.
    apply node_iface_eq_sym; auto.
  Qed.

  Fact global_iface_eq_trans {P1 P2 P3 p1 p2 p3} : forall (n1 : @global P1 p1) (n2 : @global P2 p2) (n3 : @global P3 p3),
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

  Inductive wl_exp {PSyn prefs} : (@global PSyn prefs) -> exp -> Prop :=
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
  | wl_Ewhen : forall G es x b tys nck,
      Forall (wl_exp G) es ->
      length (annots es) = length tys ->
      wl_exp G (Ewhen es x b (tys, nck))
  | wl_Emerge : forall G x es tys nck,
      es <> nil ->
      Forall (fun es => Forall (wl_exp G) (snd es)) es ->
      Forall (fun es => length (annots (snd es)) = length tys) es ->
      wl_exp G (Emerge x es (tys, nck))
  | wl_Ecase : forall G e es d tys nck,
      wl_exp G e ->
      numstreams e = 1 ->
      es <> nil ->
      Forall (fun es => Forall (wl_exp G) (snd es)) es ->
      Forall (fun es => length (annots (snd es)) = length tys) es ->
      (forall d0, d = Some d0 -> Forall (wl_exp G) d0) ->
      (forall d0, d = Some d0 -> length (annots d0) = length tys) ->
      wl_exp G (Ecase e es d (tys, nck))
  | wl_Eapp : forall G f n es er anns,
      Forall (wl_exp G) es ->
      Forall (wl_exp G) er ->
      Forall (fun e => numstreams e = 1) er ->
      find_node f G = Some n ->
      length (annots es) = length (n_in n) ->
      length anns = length (n_out n) ->
      wl_exp G (Eapp f es er anns).

  Definition wl_equation {PSyn prefs} (G : @global PSyn prefs) (eq : equation) :=
    let (xs, es) := eq in
    Forall (wl_exp G) es /\ length xs = length (annots es).

  Inductive wl_block {PSyn prefs} (G : @global PSyn prefs) : block -> Prop :=
  | wl_Beq : forall eq,
      wl_equation G eq ->
      wl_block G (Beq eq)
  | wl_Breset : forall blocks er,
      Forall (wl_block G) blocks ->
      wl_exp G er ->
      numstreams er = 1 ->
      wl_block G (Breset blocks er)
  | wl_Blocal : forall locs blocks,
      Forall (wl_block G) blocks ->
      wl_block G (Blocal locs blocks).

  Definition wl_node {PSyn prefs} (G : @global PSyn prefs) (n : @node PSyn prefs) :=
    wl_block G (n_block n).

  Definition wl_global {PSyn prefs} : @global PSyn prefs -> Prop :=
    wt_program wl_node.

  (** ** Limiting the variables appearing in expression, equation or block to an environnement *)

  Inductive wx_exp (vars : list ident) : exp -> Prop :=
  | wx_Const : forall c,
      wx_exp vars (Econst c)
  | wx_Enum : forall k ty,
      wx_exp vars (Eenum k ty)
  | wx_Evar : forall x a,
      In x vars ->
      wx_exp vars (Evar x a)
  | wx_Eunop : forall op e a,
      wx_exp vars e ->
      wx_exp vars (Eunop op e a)
  | wx_Ebinop : forall op e1 e2 a,
      wx_exp vars e1 ->
      wx_exp vars e2 ->
      wx_exp vars (Ebinop op e1 e2 a)
  | wx_Efby : forall e0s es anns,
      Forall (wx_exp vars) e0s ->
      Forall (wx_exp vars) es ->
      wx_exp vars (Efby e0s es anns)
  | wx_Earrow : forall e0s es anns,
      Forall (wx_exp vars) e0s ->
      Forall (wx_exp vars) es ->
      wx_exp vars (Earrow e0s es anns)
  | wx_Ewhen : forall es x b tys nck,
      In x vars ->
      Forall (wx_exp vars) es ->
      wx_exp vars (Ewhen es x b (tys, nck))
  | wx_Emerge : forall x tx es tys nck,
      In x vars ->
      Forall (fun es => Forall (wx_exp vars) (snd es)) es ->
      wx_exp vars (Emerge (x, tx) es (tys, nck))
  | wx_Ecase : forall e es d tys nck,
      wx_exp vars e ->
      Forall (fun es => Forall (wx_exp vars) (snd es)) es ->
      (forall d0, d = Some d0 -> Forall (wx_exp vars) d0) ->
      wx_exp vars (Ecase e es d (tys, nck))
  | wx_Eapp : forall f es er anns,
      Forall (wx_exp vars) es ->
      Forall (wx_exp vars) er ->
      wx_exp vars (Eapp f es er anns).

  Definition wx_equation vars (eq : equation) :=
    let (xs, es) := eq in
    Forall (wx_exp vars) es /\ incl xs vars.

  Inductive wx_block : list ident -> block -> Prop :=
  | wx_Beq : forall vars eq,
      wx_equation vars eq ->
      wx_block vars (Beq eq)
  | wx_Breset : forall vars blks er,
      Forall (wx_block vars) blks ->
      wx_exp vars er ->
      wx_block vars (Breset blks er)
  | wx_Blocal : forall vars locs blks,
      Forall (wx_block (vars++map fst locs)) blks ->
      wx_block vars (Blocal locs blks).

  Definition wx_node {PSyn prefs} (n : @node PSyn prefs) :=
    wx_block (map fst (n_in n ++ n_out n)) (n_block n).

  Definition wx_global {PSyn prefs} (G: @global PSyn prefs) : Prop :=
    Forall wx_node (nodes G).

  Section wx_incl.

    Hint Constructors wx_exp wx_block.

    Lemma wx_exp_incl : forall env env' e,
      incl env env' ->
      wx_exp env e ->
      wx_exp env' e.
    Proof.
      induction e using exp_ind2; intros * Hincl Hwx; inv Hwx; auto.
      - (* fby *)
        constructor; rewrite Forall_forall in *; eauto.
      - (* arrow *)
        constructor; rewrite Forall_forall in *; eauto.
      - (* when *)
        constructor; rewrite Forall_forall in *; eauto.
      - (* merge *)
        constructor; rewrite Forall_forall in *; eauto.
        intros ? Hin. specialize (H _ Hin). specialize (H4 _ Hin).
        rewrite Forall_forall in *; eauto.
      - (* case *)
        constructor; eauto.
        + eapply Forall_impl_In; [|eauto]; intros (?&?) ??.
          eapply Forall_impl_In; [|eauto]; intros.
          do 2 (eapply Forall_forall in H; eauto).
        + intros ??; subst; simpl in *.
          eapply Forall_impl_In; [|eauto]; intros.
          eapply Forall_forall in H7; eauto.
      - (* app *)
        constructor; rewrite Forall_forall in *; eauto.
    Qed.

    Lemma wx_equation_incl : forall env env' equ,
        incl env env' ->
        wx_equation env equ ->
        wx_equation env' equ.
    Proof.
      intros ?? (xs&es) Hincl (Hes&Hxs).
      split.
      - rewrite Forall_forall in *. intros.
        eapply wx_exp_incl; eauto.
      - etransitivity; eauto.
    Qed.

    Lemma wx_block_incl : forall env env' blk,
        incl env env' ->
        wx_block env blk ->
        wx_block env' blk.
    Proof.
      intros *. revert env env'.
      induction blk using block_ind2; intros * Hincl Hwx; inv Hwx.
      - (* equation *)
        constructor. eapply wx_equation_incl; eauto.
      - (* reset *)
        constructor; rewrite Forall_forall in *; eauto.
        eapply wx_exp_incl; eauto.
      - (* local *)
        constructor; rewrite Forall_forall in *; intros.
        eapply H; eauto using incl_appl'.
    Qed.
  End wx_incl.

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

  Fact InMembers_anon_in_block : forall x d blocks,
      In d blocks ->
      InMembers x (anon_in_block d) ->
      InMembers x (flat_map anon_in_block blocks).
  Proof.
    intros * Hin Hinm.
    rewrite fst_InMembers in *.
    eapply incl_map; eauto.
    rewrite flat_map_concat_map.
    apply incl_concat_map; auto.
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
    eapply NoDupMembers_flat_map, Forall_forall in Hndup; eauto.
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
    eapply NoDupMembers_flat_map, Forall_forall in Hndup; eauto.
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

  Fact NoDupMembers_anon_in_block : forall d blocks,
      In d blocks ->
      NoDupMembers (flat_map anon_in_block blocks) ->
      NoDupMembers (anon_in_block d).
  Proof.
    intros * Hin Hndup.
    eapply NoDupMembers_flat_map, Forall_forall in Hndup; eauto.
  Qed.

  Corollary NoDupMembers_anon_in_block' : forall vars d blocks,
      In d blocks ->
      NoDupMembers (vars ++ flat_map anon_in_block blocks) ->
      NoDupMembers (vars ++ anon_in_block d).
  Proof.
    intros * Hin Hndup.
    apply NoDupMembers_app.
    - apply NoDupMembers_app_l in Hndup; auto.
    - apply NoDupMembers_app_r in Hndup; auto.
      eapply NoDupMembers_anon_in_block; eauto.
    - intros x HIn contra.
      eapply NoDupMembers_app_InMembers in Hndup; eauto.
      eapply InMembers_anon_in_block in contra; eauto.
  Qed.

  (** *** Additional properties *)

  Lemma NoDupLocals_incl : forall blk xs xs',
      incl xs xs' ->
      NoDupLocals xs' blk ->
      NoDupLocals xs blk.
  Proof.
    induction blk using block_ind2; intros * Hincl Hnd; inv Hnd.
    - (* eq *)
      constructor.
    - (* reset *)
      constructor.
      rewrite Forall_forall in *; eauto.
    - (* local *)
      constructor; auto.
      + rewrite Forall_forall in *; intros; eauto.
        eapply H; eauto using incl_appl'.
      + intros * Hin. contradict H5; eauto.
  Qed.

  Corollary node_NoDupLocals {PSyn prefs} : forall (n : @node PSyn prefs),
      NoDupLocals (map fst (n_in n ++ n_out n)) (n_block n).
  Proof.
    intros *.
    pose proof (n_nodup n) as (_&Hnd).
    eapply NoDupLocals_incl; eauto.
    solve_incl_app.
  Qed.

  Add Parametric Morphism : NoDupLocals
      with signature @Permutation _ ==> eq ==> Basics.impl
        as NoDupLocals_Permutation.
  Proof.
    intros * Hperm ? Hnd.
    eapply NoDupLocals_incl; eauto.
    rewrite Hperm. reflexivity.
  Qed.

  Lemma NoDupLocals_incl' prefs npref : forall blk xs ys,
      ~PS.In npref prefs ->
      GoodLocals prefs blk ->
      (forall x, In x ys -> In x xs \/ exists id hint, x = gensym npref hint id) ->
      NoDupLocals xs blk ->
      NoDupLocals ys blk.
  Proof.
    induction blk using block_ind2;
      intros * Hnin Hgood Hin Hnd; inv Hgood; inv Hnd.
    - (* equation *) constructor.
    - (* reset *)
      constructor. rewrite Forall_forall in *; eauto.
    - (* local *)
      constructor; auto.
      + rewrite Forall_forall in *. intros ? Hblk.
        eapply H; [eauto|eauto|eauto| |eauto].
        intros ? Hx. rewrite in_app_iff in *. destruct Hx as [Hx|Hx]; auto.
        apply Hin in Hx as [?|?]; auto.
      + intros ? Hinm. specialize (H7 _ Hinm) as Hx.
        contradict Hx. apply Hin in Hx as [?|(?&?&Hpref)]; auto; subst. exfalso.
        eapply Forall_forall in H2. 2:(rewrite <- fst_InMembers; eauto).
        inv H2.
        * apply gensym_not_atom in H0; auto.
        * destruct H0 as (?&Hpsin&?&?&Heq).
          eapply gensym_injective in Heq as (?&?); subst. contradiction.
  Qed.

  Lemma node_NoDup {PSyn prefs} : forall (n : @node PSyn prefs),
      NoDup (map fst (n_in n ++ n_out n)).
  Proof.
    intros n.
    rewrite <- fst_NoDupMembers.
    specialize (n_nodup n) as (Hnd&_).
    repeat rewrite app_assoc in *.
    apply NoDupMembers_app_l in Hnd; auto.
    now rewrite NoDupMembers_idty in Hnd.
  Qed.

  Lemma AtomOrGensym_add : forall pref prefs xs,
      Forall (AtomOrGensym prefs) xs ->
      Forall (AtomOrGensym (PS.add pref prefs)) xs.
  Proof.
    intros * Hat.
    eapply Forall_impl; [|eauto].
    intros ? [?|(pref'&?&?)]; [left|right]; subst; auto.
    exists pref'. auto using PSF.add_2.
  Qed.

  Lemma GoodLocals_add : forall p prefs blk,
      GoodLocals prefs blk ->
      GoodLocals (PS.add p prefs) blk.
  Proof.
    induction blk using block_ind2; intros * Hgood; inv Hgood.
    - (* equation *)
      constructor; eauto using AtomOrGensym_add.
    - (* reset *)
      constructor; eauto using AtomOrGensym_add.
      rewrite Forall_forall in *; eauto.
    - (* locals *)
      constructor; eauto using AtomOrGensym_add.
      rewrite Forall_forall in *; eauto.
  Qed.

  Lemma VarsDefined_vars_defined : forall blk xs,
      NoDupLocals xs blk ->
      VarsDefined blk xs ->
      Permutation xs (vars_defined blk).
  Proof.
    induction blk using block_ind2; intros * Hnd Hvars; inv Hnd; inv Hvars; simpl in *.
    - (* equation *)
      reflexivity.
    - (* reset *)
      induction H4; inv H; inv H2; simpl in *; auto.
      apply Permutation_app; [eapply H5|eapply IHForall2]; eauto.
      2:eapply Forall_impl; [|eauto]; intros.
      1,2:(eapply NoDupLocals_incl; [|eauto]; solve_incl_app).
    - (* local *)
      assert (Permutation (concat xs0) (flat_map vars_defined blocks)) as Hperm.
      { rewrite Permutation_app_comm in H7.
        assert (Forall (NoDupLocals (concat xs0)) blocks) as Hnd.
        { eapply Forall_impl; [|eauto]. intros.
          rewrite <-H7. eapply NoDupLocals_incl; [|eauto]; solve_incl_app. }
        clear - H Hnd H3.
        induction H3; inv H; inv Hnd; simpl in *; auto.
        apply Permutation_app; [eapply H4|eapply IHForall2]; eauto.
        2:eapply Forall_impl; [|eauto]; intros.
        1,2:(eapply NoDupLocals_incl; [|eauto]; solve_incl_app).
      }
      rewrite <-Hperm, <-H7, <-filter_app, filter_nil, filter_idem; auto.
      + eapply Forall_forall; intros ? Hin.
        eapply Bool.negb_true_iff.
        destruct (mem_assoc_ident x locs) eqn:Hmem; auto.
        exfalso. eapply mem_assoc_ident_true in Hmem as (ty&Hin').
        eapply H5; eauto using In_InMembers.
      + eapply Forall_forall; intros ? Hin.
        apply fst_InMembers, InMembers_In in Hin as (?&?).
        eapply Bool.negb_false_iff; simpl.
        destruct (mem_assoc_ident x locs) eqn:Hmem; auto.
        exfalso. eapply mem_assoc_ident_false in Hmem; eauto.
  Qed.

  Corollary VarsDefined_flat_map_vars_defined : forall blks xs,
      Forall (NoDupLocals (concat xs)) blks ->
      Forall2 VarsDefined blks xs ->
      Permutation (concat xs) (flat_map vars_defined blks).
  Proof.
    intros * Hnd Hvars.
    induction Hvars; inv Hnd; simpl in *; auto.
    apply Permutation_app; [eapply VarsDefined_vars_defined|eapply IHHvars]; eauto.
    2:eapply Forall_impl; [|eauto]; intros.
    1,2:(eapply NoDupLocals_incl; [|eauto]; solve_incl_app).
  Qed.

  Lemma vars_defined_Perm {PSyn prefs} : forall (n : @node PSyn prefs),
      Permutation (vars_defined (n_block n)) (map fst (n_out n)).
  Proof.
    intros n. destruct n; simpl. clear - n_nodup0 n_defd0.
    destruct n_defd0 as (?&Hvars&Hperm). destruct n_nodup0 as (_&Hnd).
    rewrite <-Hperm. symmetry. eapply VarsDefined_vars_defined; eauto.
    eapply NoDupLocals_incl; [|eauto].
    rewrite Hperm. solve_incl_app.
  Qed.

  Lemma local_anon_in_block_incl : forall blk,
      incl (local_anon_in_block blk) (anon_in_block blk).
  Proof.
    induction blk using block_ind2; simpl.
    - (* equation *)
      reflexivity.
    - (* reset *)
      apply incl_app; [apply incl_appl|apply incl_appr; reflexivity].
      intros ??. apply in_flat_map in H0 as (?&?&?).
      rewrite Forall_forall in *.
      apply in_flat_map; do 2 esplit; eauto.
      eapply H; eauto.
    - (* local *)
      apply incl_nil'.
  Qed.

  Corollary local_anons_in_block_incl : forall blks,
      incl (flat_map local_anon_in_block blks) (flat_map anon_in_block blks).
  Proof.
    intros ?? Hin. apply in_flat_map in Hin as (?&?&?).
    apply in_flat_map; do 2 esplit; eauto.
    eapply local_anon_in_block_incl; eauto.
  Qed.

  Fact local_anons_in_block_NoDupMembers' : forall blks,
      Forall (fun blk : block => NoDupMembers (anon_in_block blk) -> NoDupMembers (local_anon_in_block blk)) blks ->
      NoDupMembers (flat_map anon_in_block blks) ->
      NoDupMembers (flat_map local_anon_in_block blks).
  Proof.
    intros * Hf Hnd.
    induction blks; inv Hf; simpl in *; auto.
    apply NoDupMembers_app; eauto using NoDupMembers_app_l, NoDupMembers_app_r.
    intros ? Hin contra.
    eapply InMembers_incl in Hin; eauto using local_anon_in_block_incl.
    eapply InMembers_incl in contra; eauto using local_anons_in_block_incl.
    eapply NoDupMembers_app_InMembers in Hnd; eauto.
  Qed.

  Lemma local_anon_in_block_NoDupMembers : forall blk,
      NoDupMembers (anon_in_block blk) ->
      NoDupMembers (local_anon_in_block blk).
  Proof.
    induction blk using block_ind2; intros * Hnd; simpl in *; auto.
    - (* reset *)
      eapply NoDupMembers_app; eauto using NoDupMembers_app_l, NoDupMembers_app_r, local_anons_in_block_NoDupMembers'.
      intros ? Hinm.
      eapply NoDupMembers_app_InMembers in Hnd; eauto using InMembers_incl, local_anons_in_block_incl.
    - (* locals *)
      constructor.
  Qed.

  Corollary local_anons_in_block_NoDupMembers : forall blks,
      NoDupMembers (flat_map anon_in_block blks) ->
      NoDupMembers (flat_map local_anon_in_block blks).
  Proof.
    intros * Hnd.
    eapply local_anons_in_block_NoDupMembers'; eauto.
    eapply Forall_forall; intros; eauto using local_anon_in_block_NoDupMembers.
  Qed.

  Lemma GoodLocals_locals prefs : forall blk,
      GoodLocals prefs blk ->
      Forall (AtomOrGensym prefs) (map fst (locals blk)).
  Proof.
    induction blk using block_ind2; intros * Hgood; inv Hgood; simpl; auto.
    - (* reset *)
      rewrite flat_map_concat_map, concat_map.
      eapply Forall_concat, Forall_map, Forall_map.
      rewrite Forall_forall in *; eauto.
    - (* locals *)
      rewrite map_app, Forall_app; split; auto.
      rewrite flat_map_concat_map, concat_map.
      eapply Forall_concat, Forall_map, Forall_map.
      rewrite Forall_forall in *; eauto.
  Qed.

  (** ** Specifications of some subset of the language *)

  (** *** Without local blocks *)

  Inductive nolocal_block : block -> Prop :=
  | NLeq : forall eq, nolocal_block (Beq eq)
  | NLreset : forall blks er,
      Forall nolocal_block blks ->
      nolocal_block (Breset blks er).

  Inductive nolocal_top_block : block -> Prop :=
  | NLnode : forall locs blks,
      Forall nolocal_block blks ->
      nolocal_top_block (Blocal locs blks).

  Lemma nolocal_block_local_anon_idem : forall blk,
      nolocal_block blk ->
      local_anon_in_block blk = anon_in_block blk.
  Proof.
    induction blk using block_ind2; intros * Hnl; inv Hnl; simpl.
    - (* equation *)
      reflexivity.
    - f_equal; auto.
      rewrite 2 flat_map_concat_map. f_equal.
      eapply map_ext_in; intros.
      rewrite Forall_forall in *; eauto.
  Qed.

  Corollary nolocal_block_local_anons_idem : forall blks,
      Forall nolocal_block blks ->
      flat_map local_anon_in_block blks = flat_map anon_in_block blks.
  Proof.
    intros * Hnl.
    rewrite 2 flat_map_concat_map. f_equal.
    eapply map_ext_in; intros.
    rewrite Forall_forall in *.
    eapply nolocal_block_local_anon_idem; eauto.
  Qed.

End LSYNTAX.

Module LSyntaxFun
       (Ids      : IDS)
       (Op       : OPERATORS)
       (OpAux    : OPERATORS_AUX Ids Op)
       (Cks      : CLOCKS Ids Op OpAux) <: LSYNTAX Ids Op OpAux Cks.
  Include LSYNTAX Ids Op OpAux Cks.
End LSyntaxFun.
