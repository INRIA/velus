From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import CommonTyping.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.StaticEnv.
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
       (Import Cks  : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks).

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
  Definition ann : Type := (type * clock)%type.
  Definition lann : Type := (list type * clock)%type.

  Global Hint Unfold ann lann : conjs.

  Definition idents xs := List.map (@fst ident (type * clock * ident)) xs.

  Inductive exp : Type :=
  | Econst : cconst -> exp
  | Eenum  : enumtag -> type -> exp
  | Evar   : ident -> ann -> exp
  | Elast  : ident -> ann -> exp
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
  | Bswitch : exp -> list (enumtag * list block) -> block
  | Blocal : list (ident * (type * clock * ident * option (exp * ident))) -> list block -> block.

  (** ** Node *)

  Definition numstreams (e: exp) : nat :=
    match e with
    | Econst _ | Eenum _ _ => 1
    | Efby _ _ anns
    | Earrow _ _ anns
    | Eapp _ _ _ anns => length anns
    | Evar _ _
    | Elast _ _
    | Eunop _ _ _
    | Ebinop _ _ _ _ => 1
    | Ewhen _ _ _  (tys, _)
    | Emerge _ _ (tys, _)
    | Ecase _ _ _ (tys, _) => length tys
    end.

  (* Annotation (homogenized). *)

  Definition annot (e: exp): list (type * clock) :=
    match e with
    | Econst c => [(Tprimitive (ctype_cconst c), Cbase)]
    | Eenum _ ty => [(ty, Cbase)]
    | Efby _ _ anns
    | Earrow _ _ anns
    | Eapp _ _ _ anns => anns
    | Evar _ ann
    | Elast _ ann
    | Eunop _ _ ann
    | Ebinop _ _ _ ann => [ann]
    | Ewhen _ _ _  (tys, ck)
    | Emerge _ _ (tys, ck)
    | Ecase _ _ _ (tys, ck) => map (fun ty=> (ty, ck)) tys
    end.

  Definition annots (es: list exp): list (type * clock) :=
    flat_map annot es.

  Definition typeof (e: exp): list type :=
    match e with
    | Econst c => [Tprimitive (ctype_cconst c)]
    | Eenum _ ty => [ty]
    | Efby _ _ anns
    | Earrow _ _ anns
    | Eapp _ _ _ anns => map fst anns
    | Elast _ ann
    | Evar _ ann
    | Eunop _ _ ann
    | Ebinop _ _ _ ann => [fst ann]
    | Ewhen _ _ _ anns
    | Emerge _ _ anns
    | Ecase _ _ _ anns => fst anns
    end.

  Definition typesof (es: list exp): list type :=
    flat_map typeof es.

  Definition clockof (e: exp): list clock :=
    match e with
    | Econst _ | Eenum _ _ => [Cbase]
    | Efby _ _ anns
    | Earrow _ _ anns
    | Eapp _ _ _ anns => map snd anns
    | Evar _ ann
    | Elast _ ann
    | Eunop _ _ ann
    | Ebinop _ _ _ ann => [snd ann]
    | Ewhen _ _ _ anns
    | Emerge _ _ anns
    | Ecase _ _ _ anns => map (fun _ => snd anns) (fst anns)
    end.

  Definition clocksof (es: list exp): list clock :=
    flat_map clockof es.

  Definition nclockof (e: exp): list nclock :=
    match e with
    | Econst _ | Eenum _ _ => [(Cbase, None)]
    | Efby _ _ anns
    | Earrow _ _ anns
    | Eapp _ _ _ anns => map (fun ann => (snd ann, None)) anns
    | Evar x ann => [(snd ann, Some x)]
    | Elast x ann => [(snd ann, None)]
    | Eunop _ _ ann
    | Ebinop _ _ _ ann => [(snd ann, None)]
    | Ewhen _ _ _ anns
    | Emerge _ _ anns
    | Ecase _ _ _ anns => map (fun _ => (snd anns, None)) (fst anns)
    end.

  Definition nclocksof (es: list exp): list nclock :=
    flat_map nclockof es.

  (** ** Variables defined by a block *)

  (** `x ` is defined by `blk` *)
  Inductive Is_defined_in (x : ident) : block -> Prop :=
  | DefEq : forall xs es,
      In x xs ->
      Is_defined_in x (Beq (xs, es))
  | DefReset : forall blks er,
      Exists (Is_defined_in x) blks ->
      Is_defined_in x (Breset blks er)
  | DefSwitch : forall ec branches,
      Exists (fun blks => Exists (Is_defined_in x) (snd blks)) branches ->
      Is_defined_in x (Bswitch ec branches)
  | DefLocal : forall locs blks,
      Exists (Is_defined_in x) blks ->
      ~InMembers x locs ->
      Is_defined_in x (Blocal locs blks).

  (** Compute the variables defined by a block *)
  Fixpoint vars_defined (d : block) :=
    match d with
    | Beq eq => ps_from_list (fst eq)
    | Breset blocks _ => PSUnion (map vars_defined blocks)
    | Bswitch _ branches =>
      PSUnion (map (fun blks => PSUnion (map vars_defined (snd blks))) branches)
    | Blocal locals blocks =>
      PS.filter (fun x => negb (mem_assoc_ident x locals))
                (PSUnion (map vars_defined blocks))
    end.

  (** Check that the variables defined by `blk` are indeed `xs` *)
  Inductive VarsDefined : block -> list ident -> Prop :=
  | LVDeq : forall eq, VarsDefined (Beq eq) (fst eq)
  | LVDreset : forall blocks er xs,
      Forall2 VarsDefined blocks xs ->
      VarsDefined (Breset blocks er) (concat xs)
  | LVDswitch : forall ec branches ys,
      branches <> [] ->
      Forall (fun blks => exists xs, Forall2 VarsDefined (snd blks) xs /\ Permutation (concat xs) ys) branches ->
      VarsDefined (Bswitch ec branches) ys
  | LVDlocal : forall locs blocks xs ys,
      Forall2 VarsDefined blocks xs ->
      Permutation (map fst locs ++ ys) (concat xs) ->
      VarsDefined (Blocal locs blocks) ys.

  Ltac inv_VarsDefined :=
    repeat
      match goal with
      | H:Forall2 VarsDefined ?blks _, Hin: In _ ?blks |- _ =>
          let xs := fresh "xs" in
          let Hinxs := fresh "Hinxs" in
          let Hdef := fresh "Hdef" in
          eapply Forall2_ignore2, Forall_forall in H as (xs&Hinxs&Hdef); [|eapply Hin]
      | H:Forall2 VarsDefined _ ?xs, Hin: In _ ?xs |- _ =>
          let blk := fresh "blk" in
          let Hinblks := fresh "Hinblks" in
          let Hdef := fresh "Hdef" in
          eapply Forall2_ignore1, Forall_forall in H as (blk&Hinblks&Hdef); [|eapply Hin]
      | H:Forall (fun _ => exists _, Forall2 VarsDefined _ _ /\ Permutation _ _) ?brs, Hin: In _ ?brs |- _ =>
          let Hvars := fresh "Hvars" in
          let Hperm := fresh "Hperm" in
          eapply Forall_forall in H as (?&Hvars&Hperm); [|eapply Hin]
      end.

  Fixpoint locals (d : block) : list (ident * (ident * option ident)) :=
    match d with
    | Beq _ => []
    | Breset blocks _ => flat_map locals blocks
    | Bswitch _ branches => flat_map (fun blks => flat_map locals (snd blks)) branches
    | Blocal loc blocks => map (fun '(x, (_, _, cx, o)) => (x, (cx, option_map snd o))) loc ++ (flat_map locals blocks)
    end.

  (** ** Shadowing is prohibited *)

  Inductive NoDupLocals : list ident -> block -> Prop :=
  | NDLeq : forall env eq, NoDupLocals env (Beq eq)
  | NDLreset : forall env blocks er,
      Forall (NoDupLocals env) blocks ->
      NoDupLocals env (Breset blocks er)
  | NDLswitch : forall env ec branches,
      Forall (fun blks => Forall (NoDupLocals env) (snd blks)) branches ->
      NoDupLocals env (Bswitch ec branches)
  | NDLlocal : forall env locs blocks,
      Forall (NoDupLocals (env++map fst locs)) blocks ->
      NoDupMembers locs ->
      (forall x, InMembers x locs -> ~In x env) ->
      NoDupLocals env (Blocal locs blocks).

  (** ** All the locals must be well-formed *)

  Inductive GoodLocals (prefs : PS.t) : block -> Prop :=
  | GoodEq : forall eq,
      GoodLocals prefs (Beq eq)
  | GoodReset : forall blks er,
      Forall (GoodLocals prefs) blks ->
      GoodLocals prefs (Breset blks er)
  | GoodSwitch : forall ec branches,
      Forall (fun blks => Forall (GoodLocals prefs) (snd blks)) branches ->
      GoodLocals prefs (Bswitch ec branches)
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
        n_nodup    : NoDupMembers (n_in ++ n_out) /\
                     NoDupLocals (map fst (n_in ++ n_out)) n_block;
        n_good     : Forall (AtomOrGensym prefs) (map fst (n_in ++ n_out))
                     /\ GoodLocals prefs n_block
                     /\ atom n_name;
        n_syn      : PSyn n_block;
      }.

  Global Instance node_unit {PSyn prefs} : ProgramUnit (@node PSyn prefs) :=
    { name := n_name; }.

  (** ** Program *)

  Record global {PSyn prefs} :=
    Global {
        enums : list (ident * nat);
        nodes : list (@node PSyn prefs);
      }.
  Arguments Global {_ _}.

  Global Program Instance global_program {PSyn prefs} : Program (@node PSyn prefs) global :=
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

    Hypothesis ElastCase:
      forall x a,
        P (Elast x a).

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
      - apply ElastCase; auto.
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

    Hypothesis BswitchCase:
      forall ec branches,
        Forall (fun blks => Forall P (snd blks)) branches ->
        P (Bswitch ec branches).

    Hypothesis BlocalCase:
      forall locs blocks,
        Forall P blocks ->
        P (Blocal locs blocks).

    Fixpoint block_ind2 (d: block) : P d.
    Proof.
      destruct d.
      - apply BeqCase; auto.
      - apply BresetCase; induction l; auto.
      - apply BswitchCase; induction l; constructor; auto. induction (snd a); auto.
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
      clockof e = map snd (annot e).
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

  Corollary length_clockof_numstreams : forall e,
      length (clockof e) = numstreams e.
  Proof.
    intros.
    rewrite clockof_annot.
    repeat rewrite map_length.
    apply length_annot_numstreams.
  Qed.

  Fact clocksof_annots : forall es,
      clocksof es = map snd (annots es).
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
    rewrite clocksof_annots.
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
      map fst (nclockof e) = map snd (annot e).
  Proof.
    destruct e; simpl; try reflexivity.
    3-5:destruct l0; simpl.
    1-6:repeat rewrite map_map; simpl; auto.
  Qed.

  Corollary length_nclockof_numstreams : forall e,
      length (nclockof e) = numstreams e.
  Proof.
    intros.
    erewrite <-map_length, nclockof_annot, map_length.
    apply length_annot_numstreams.
  Qed.

  Fact nclocksof_annots : forall es,
      map fst (nclocksof es) = map snd (annots es).
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
    erewrite <-map_length, nclocksof_annots, map_length. auto.
  Qed.

  Lemma clockof_nclockof:
    forall e,
      clockof e = map stripname (nclockof e).
  Proof.
    destruct e; simpl; try rewrite map_map; auto.
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
  | wl_Elast : forall G x a,
      wl_exp G (Elast x a)
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
  | wl_Bswitch : forall ec branches,
      wl_exp G ec ->
      numstreams ec = 1 ->
      branches <> nil ->
      Forall (fun blks => Forall (wl_block G) (snd blks)) branches ->
      wl_block G (Bswitch ec branches)
  | wl_Blocal : forall locs blocks,
      Forall (wl_block G) blocks ->
      Forall (fun '(_, (_,_,_,o)) => LiftO True (fun '(e, _) => wl_exp G e /\ numstreams e = 1) o) locs ->
      wl_block G (Blocal locs blocks).

  Definition wl_node {PSyn prefs} (G : @global PSyn prefs) (n : @node PSyn prefs) :=
    wl_block G (n_block n).

  Definition wl_global {PSyn prefs} : @global PSyn prefs -> Prop :=
    wt_program wl_node.

  (** ** Limiting the variables appearing in expression, equation or block to an environnement *)

  Inductive wx_clock (vars : list ident) : clock -> Prop :=
  | wx_Cbase : wx_clock vars Cbase
  | wx_Con : forall ck x tx,
      wx_clock vars ck ->
      In x vars ->
      wx_clock vars (Con ck x tx).

  Inductive wx_exp (Γ : static_env) : exp -> Prop :=
  | wx_Const : forall c,
      wx_exp Γ (Econst c)
  | wx_Enum : forall k ty,
      wx_exp Γ (Eenum k ty)
  | wx_Evar : forall x a,
      IsVar Γ x ->
      wx_exp Γ (Evar x a)
  | wx_Elast : forall x ty ck,
      IsLast Γ x ->
      wx_exp Γ (Elast x (ty, ck))
  | wx_Eunop : forall op e a,
      wx_exp Γ e ->
      wx_exp Γ (Eunop op e a)
  | wx_Ebinop : forall op e1 e2 a,
      wx_exp Γ e1 ->
      wx_exp Γ e2 ->
      wx_exp Γ (Ebinop op e1 e2 a)
  | wx_Efby : forall e0s es anns,
      Forall (wx_exp Γ) e0s ->
      Forall (wx_exp Γ) es ->
      wx_exp Γ (Efby e0s es anns)
  | wx_Earrow : forall e0s es anns,
      Forall (wx_exp Γ) e0s ->
      Forall (wx_exp Γ) es ->
      wx_exp Γ (Earrow e0s es anns)
  | wx_Ewhen : forall es x b tys nck,
      IsVar Γ x ->
      Forall (wx_exp Γ) es ->
      wx_exp Γ (Ewhen es x b (tys, nck))
  | wx_Emerge : forall x tx es tys nck,
      IsVar Γ x ->
      Forall (fun es => Forall (wx_exp Γ) (snd es)) es ->
      wx_exp Γ (Emerge (x, tx) es (tys, nck))
  | wx_Ecase : forall e es d tys nck,
      wx_exp Γ e ->
      Forall (fun es => Forall (wx_exp Γ) (snd es)) es ->
      (forall d0, d = Some d0 -> Forall (wx_exp Γ) d0) ->
      wx_exp Γ (Ecase e es d (tys, nck))
  | wx_Eapp : forall f es er anns,
      Forall (wx_exp Γ) es ->
      Forall (wx_exp Γ) er ->
      wx_exp Γ (Eapp f es er anns).

  Definition wx_equation Γ (eq : equation) :=
    let (xs, es) := eq in
    Forall (wx_exp Γ) es /\ Forall (IsVar Γ) xs.

  Inductive wx_block : static_env -> block -> Prop :=
  | wx_Beq : forall Γ eq,
      wx_equation Γ eq ->
      wx_block Γ (Beq eq)
  | wx_Breset : forall Γ blks er,
      Forall (wx_block Γ) blks ->
      wx_exp Γ er ->
      wx_block Γ (Breset blks er)
  | wc_Bswitch : forall Γ ec branches,
      wx_exp Γ ec ->
      Forall (fun blks => Forall (wx_block Γ) (snd blks)) branches ->
      wx_block Γ (Bswitch ec branches)
  | wx_Blocal : forall Γ Γ' locs blks,
      Γ' = Γ ++ senv_of_locs locs ->
      Forall (wx_block Γ') blks ->
      Forall (fun '(_, (_,_,_,o)) => LiftO True (fun '(e, _) => wx_exp Γ' e) o) locs ->
      wx_block Γ (Blocal locs blks).

  Definition wx_node {PSyn prefs} (n : @node PSyn prefs) :=
    wx_block (senv_of_inout (n_in n ++ n_out n)) (n_block n).

  Definition wx_global {PSyn prefs} (G: @global PSyn prefs) : Prop :=
    Forall wx_node (nodes G).

  Section wx_incl.

    Hint Constructors wx_exp wx_block : core.

    Lemma wx_exp_incl : forall Γ Γ' e,
        (forall x, IsVar Γ x -> IsVar Γ' x) ->
        (forall x, IsLast Γ x -> IsLast Γ' x) ->
        wx_exp Γ e ->
        wx_exp Γ' e.
    Proof.
      induction e using exp_ind2; intros * Hincl1 Hincl2 Hwx; inv Hwx; eauto with senv.
      - (* fby *)
        constructor; simpl_Forall; auto.
      - (* arrow *)
        constructor; simpl_Forall; auto.
      - (* when *)
        constructor; simpl_Forall; eauto.
      - (* merge *)
        constructor; simpl_Forall; eauto.
      - (* case *)
        constructor; eauto.
        + simpl_Forall; eauto.
        + intros ??; subst; simpl in *.
          simpl_Forall; eauto.
          eapply Forall_forall in H7; eauto.
      - (* app *)
        constructor; simpl_Forall; eauto.
    Qed.

    Lemma wx_equation_incl : forall Γ Γ' equ,
        (forall x, IsVar Γ x -> IsVar Γ' x) ->
        (forall x, IsLast Γ x -> IsLast Γ' x) ->
        wx_equation Γ equ ->
        wx_equation Γ' equ.
    Proof.
      intros ?? (xs&es) Hincl1 Hincl2 (Hes&Hxs).
      split.
      - simpl_Forall.
        eapply wx_exp_incl; eauto.
      - simpl_Forall. eauto.
    Qed.

    Lemma wx_block_incl : forall Γ Γ' blk,
        (forall x, IsVar Γ x -> IsVar Γ' x) ->
        (forall x, IsLast Γ x -> IsLast Γ' x) ->
        wx_block Γ blk ->
        wx_block Γ' blk.
    Proof.
      intros *. revert Γ Γ'.
      induction blk using block_ind2; intros * Hincl1 Hincl2 Hwx; inv Hwx.
      - (* equation *)
        constructor. eapply wx_equation_incl; eauto.
      - (* reset *)
        constructor; simpl_Forall; eauto.
        eapply wx_exp_incl; eauto.
      - (* switch *)
        constructor.
        + eapply wx_exp_incl; eauto.
        + simpl_Forall; eauto.
      - (* local *)
        assert (forall x, IsVar (Γ ++ senv_of_locs locs) x -> IsVar (Γ' ++ senv_of_locs locs) x) as Hincl1'.
        { intros * Hv. rewrite IsVar_app in *. destruct Hv; eauto. }
        assert (forall x, IsLast (Γ ++ senv_of_locs locs) x -> IsLast (Γ' ++ senv_of_locs locs) x) as Hincl2'.
        { intros * Hv. rewrite IsLast_app in *. destruct Hv; eauto. }
        econstructor; simpl_Forall; eauto.
        destruct o as [(?&?)|]; simpl in *; auto.
        eapply wx_exp_incl; eauto.
    Qed.
  End wx_incl.

  (* Lemma wx_clock_Is_free_in : forall vars ck x, *)
  (*     wx_clock vars ck -> *)
  (*     Is_free_in_clock x ck -> *)
  (*     In x vars. *)
  (* Proof. *)
  (*   induction ck; intros * Hwx Hfree; inv Hwx; inv Hfree; eauto. *)
  (* Qed. *)

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
      constructor. simpl_Forall; eauto.
    - (* switch *)
      constructor. simpl_Forall; eauto.
    - (* local *)
      constructor; auto.
      + simpl_Forall.
        eapply H; eauto using incl_appl'.
      + intros * Hin ?. eapply H5; eauto.
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
      constructor. simpl_Forall; eauto.
    - (* switch *)
      constructor. simpl_Forall; eauto.
    - (* local *)
      constructor; auto.
      + simpl_Forall.
        eapply H; [eauto|eauto| |eauto].
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
    apply n_nodup.
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
      simpl_Forall; eauto.
    - (* switch *)
      constructor; eauto using AtomOrGensym_add.
      simpl_Forall; eauto.
    - (* locals *)
      constructor; eauto using AtomOrGensym_add.
      simpl_Forall; eauto.
  Qed.

  Lemma GoodLocals_locals prefs : forall blk,
      GoodLocals prefs blk ->
      Forall (AtomOrGensym prefs) (map fst (locals blk)).
  Proof.
    induction blk using block_ind2; intros * Hgood; inv Hgood; simpl; auto.
    - (* reset *)
      rewrite flat_map_concat_map, concat_map.
      eapply Forall_concat.
      simpl_Forall; eauto.
      eapply Forall_forall in H; eauto. solve_In.
    - (* switch *)
      rewrite flat_map_concat_map, Forall_map.
      apply Forall_concat, Forall_map, Forall_forall; intros (?&?) Hin.
      rewrite flat_map_concat_map. apply Forall_concat, Forall_map, Forall_forall; intros.
      do 2 (eapply Forall_forall in H; eauto). do 2 (eapply Forall_forall in H1; eauto).
      eapply Forall_map; eauto.
    - (* locals *)
      rewrite map_app, Forall_app; split; auto.
      + erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
      + rewrite flat_map_concat_map, concat_map.
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
      Forall (fun '(_, (_, _, _, o)) => o = None) locs ->
      Forall nolocal_block blks ->
      nolocal_top_block (Blocal locs blks).

  (** *** Without switches *)

  Inductive noswitch_block : block -> Prop :=
  | NSeq : forall eq, noswitch_block (Beq eq)
  | NSreset : forall blks er,
      Forall noswitch_block blks ->
      noswitch_block (Breset blks er)
  | NSlocal : forall locs blks,
      Forall (fun '(_, (_, _, _, o)) => o = None) locs ->
      Forall noswitch_block blks ->
      noswitch_block (Blocal locs blks).

  (** *** Without last *)

  Inductive nolast_block : block -> Prop :=
  | NLaeq : forall eq, nolast_block (Beq eq)
  | NLareset : forall blks er,
      Forall nolast_block blks ->
      nolast_block (Breset blks er)
  | NLaswitch : forall ec branches,
      Forall (fun blks => Forall nolast_block (snd blks)) branches ->
      nolast_block (Bswitch ec branches)
  | NLalocal : forall locs blks,
      Forall (fun '(_, (_, _, _, o)) => o = None) locs ->
      Forall nolast_block blks ->
      nolast_block (Blocal locs blks).

  (** Inclusion of these properties *)

  Fact noswitch_nolast : forall blk,
      noswitch_block blk ->
      nolast_block blk.
  Proof.
    induction blk using block_ind2; intros * Hns;
      inv Hns; constructor; simpl_Forall; eauto.
  Qed.

  Fact nolocal_noswitch : forall blk,
      nolocal_block blk ->
      noswitch_block blk.
  Proof.
    induction blk using block_ind2; intros * Hns;
      inv Hns; constructor; simpl_Forall; eauto.
  Qed.

  (** *** Some more properties *)

  Lemma VarsDefined_Is_defined : forall blk xs x,
      NoDupLocals xs blk ->
      VarsDefined blk xs ->
      In x xs ->
      Is_defined_in x blk.
  Proof.
    induction blk using block_ind2; intros * Hnd Hvars Hin; inv Hnd; inv Hvars.
    - (* equation *)
      destruct eq; simpl in *. constructor; auto.
    - (* reset *)
      constructor.
      eapply in_concat in Hin as (?&Hin1&Hin2). inv_VarsDefined.
      solve_Exists. simpl_Forall.
      eapply H. 2,3:eauto.
      eapply NoDupLocals_incl; [|eauto]; auto using incl_concat.
    - (* switch *)
      constructor.
      inv H; try congruence. inv H2. inv H5. clear H1 H7 H8.
      destruct H4 as (?&Hvars&Hperm).
      left.
      rewrite <-Hperm in Hin. eapply in_concat in Hin as (?&Hin1&Hin2). inv_VarsDefined.
      solve_Exists. simpl_Forall.
      eapply H0. 2,3:eauto.
      eapply NoDupLocals_incl; [|eauto]. rewrite <-Hperm; auto using incl_concat.
    - (* local *)
      econstructor.
      2:{ intros contra. eapply H5; eauto. }
      assert (In x (concat xs0)) as Hin' by (rewrite <-H7; auto using in_or_app).
      apply in_concat in Hin' as (?&Hin1&Hin2). inv_VarsDefined.
      solve_Exists. simpl_Forall.
      eapply H. 2,3:eauto.
      eapply NoDupLocals_incl; [|eauto].
      rewrite Permutation_app_comm, H7; auto using incl_concat.
  Qed.

  Corollary Forall_VarsDefined_Is_defined : forall blks xs x,
      Forall (NoDupLocals (concat xs)) blks ->
      Forall2 (VarsDefined) blks xs ->
      In x (concat xs) ->
      Exists (Is_defined_in x) blks.
  Proof.
    intros * Hnd Hvars Hin.
    apply in_concat in Hin as (?&Hin1&Hin2). inv_VarsDefined.
    simpl_Forall. solve_Exists.
    eapply VarsDefined_Is_defined in Hdef; eauto.
    eapply NoDupLocals_incl; [|eauto]. apply incl_concat; auto.
  Qed.

  Lemma VarsDefined_Is_defined' : forall blk xs x,
      NoDupLocals xs blk ->
      VarsDefined blk xs ->
      Is_defined_in x blk ->
      In x xs.
  Proof.
    induction blk using block_ind2; intros * Hnd Hvars Hin; inv Hnd; inv Hvars; inv Hin.
    - (* equation *)
      auto.
    - (* reset *)
      simpl_Exists. inv_VarsDefined. simpl_Forall.
      eapply in_concat. repeat esplit; eauto.
      eapply H. 2,3:eauto.
      eapply NoDupLocals_incl; [|eauto]; auto using incl_concat.
    - (* switch *)
      rename H1 into Hdef. simpl_Exists.
      simpl_Forall. inv_VarsDefined.
      take (Permutation _ _) and rewrite <-it. eapply in_concat. repeat esplit; eauto.
      eapply H; eauto.
      eapply NoDupLocals_incl; [|eauto].
      take (Permutation _ _) and rewrite <-it; auto using incl_concat.
    - (* local *)
      simpl_Exists. inv_VarsDefined. simpl_Forall.
      eapply H in Hdef; eauto.
      2:{ eapply NoDupLocals_incl; [|eauto].
          rewrite Permutation_app_comm, H7; auto using incl_concat. }
      assert (In x (concat xs0)) as Hin' by (eapply in_concat; eauto).
      rewrite <-H7, in_app_iff in Hin'. destruct Hin'; auto.
      exfalso. apply H8, fst_InMembers; auto.
  Qed.

  Lemma Is_defined_in_wx_In : forall blk env x,
      wx_block env blk ->
      Is_defined_in x blk ->
      InMembers x env.
  Proof.
    induction blk using block_ind2; intros * Hwx Hdef; inv Hwx; inv Hdef.
    - (* equation *)
      destruct H1; auto. simpl_Forall. inv H1; auto.
    - (* reset *)
      simpl_Exists; simpl_Forall; eauto.
    - (* switch *)
      simpl_Exists; simpl_Forall; eauto.
    - (* local *)
      simpl_Exists; simpl_Forall.
      eapply H, InMembers_app in H2 as [|]. 3:eauto. 1,2:eauto.
      exfalso. apply H3, InMembers_senv_of_locs; auto.
  Qed.

  Corollary Exists_Is_defined_in_wx_In : forall blks env x,
      Forall (wx_block env) blks ->
      Exists (Is_defined_in x) blks ->
      InMembers x env.
  Proof.
    intros * Hf Hex.
    simpl_Exists; simpl_Forall; eauto using Is_defined_in_wx_In.
  Qed.

  Lemma Is_defined_in_vars_defined : forall x blk,
      Is_defined_in x blk ->
      PS.In x (vars_defined blk).
  Proof.
    induction blk using block_ind2; intros * Hin; simpl in *.
    - (* equation *)
      inv Hin; auto.
      now rewrite ps_from_list_In.
    - (* reset *)
      inv Hin. simpl_Exists.
      eapply In_In_PSUnion; eauto. 2:eapply in_map_iff; eauto.
      simpl_Forall; eauto.
    - (* switch *)
      inv Hin. rename H1 into Hin. simpl_Exists.
      do 2 (eapply In_In_PSUnion; [|eapply in_map_iff; eauto]).
      simpl_Forall; eauto.
    - (* local *)
      inv Hin.
      eapply PSF.filter_3. intros ???; subst; auto.
      + simpl_Exists.
        eapply In_In_PSUnion; eauto. 2:eapply in_map_iff; eauto.
        simpl_Forall; eauto.
      + eapply Bool.negb_true_iff.
        eapply Bool.not_true_iff_false. intro contra.
        apply H3.
        eapply mem_assoc_ident_true in contra as ((?&?)&?); eauto using In_InMembers.
  Qed.

  Lemma vars_defined_Is_defined_in : forall x blk,
      PS.In x (vars_defined blk) ->
      Is_defined_in x blk.
  Proof.
    induction blk using block_ind2; intros * Hin; simpl in *.
    - (* equation *)
      destruct eq. rewrite ps_from_list_In in Hin.
      now constructor.
    - (* reset *)
      apply PSUnion_In_In in Hin as (?&Hin1&Hin2). eapply in_map_iff in Hin1 as (?&?&?); subst.
      simpl_Forall.
      constructor. solve_Exists.
    - (* switch *)
      apply PSUnion_In_In in Hin as (?&Hin1&Hin2). eapply in_map_iff in Hin1 as (?&?&?); subst.
      apply PSUnion_In_In in Hin2 as (?&Hin2&Hin3). eapply in_map_iff in Hin2 as (?&?&?); subst.
      simpl_Forall.
      constructor. solve_Exists.
    - (* local *)
      eapply PS.filter_spec in Hin as (Hin&Hassoc). 2:intros ?? Heq; inv Heq; auto.
      apply PSUnion_In_In in Hin as (?&Hin1&Hin2). eapply in_map_iff in Hin1 as (?&?&?); subst.
      simpl_Forall.
      econstructor. solve_Exists.
      intros contra. eapply InMembers_In in contra as (?&?).
      eapply Bool.negb_true_iff, mem_assoc_ident_false in Hassoc; eauto.
  Qed.

End LSYNTAX.

Module LSyntaxFun
       (Ids      : IDS)
       (Op       : OPERATORS)
       (OpAux    : OPERATORS_AUX Ids Op)
       (Cks      : CLOCKS Ids Op OpAux)
       (Senv     : STATICENV Ids Op OpAux Cks) <: LSYNTAX Ids Op OpAux Cks Senv.
  Include LSYNTAX Ids Op OpAux Cks Senv.
End LSyntaxFun.
