From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import CommonTyping.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import FunctionalEnvironment.
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
  | Eextcall: ident -> list exp -> (ctype * clock) -> exp
  | Efby   : list exp -> list exp -> list ann -> exp
  | Earrow : list exp -> list exp -> list ann -> exp
  | Ewhen  : list exp -> (ident * type) -> enumtag -> lann -> exp
  | Emerge : ident * type -> list (enumtag * list exp) -> lann -> exp
  | Ecase  : exp -> list (enumtag * list exp) -> option (list exp) -> lann -> exp
  | Eapp   : ident -> list exp -> list exp -> list ann -> exp.

  Implicit Type e: exp.

  (** ** Equations *)

  Definition equation : Type := (list ident * list exp)%type.

  Implicit Type eqn: equation.

  (** ** Blocks *)

  Definition transition : Type := exp * (enumtag * bool). (* condition, new state, with or without reset *)

  (* Scope

    Contains local variable definitions.
    It is defined generically in order to factorize related definitions and proofs.
    Scope can appear under local blocks, and under state machines branches.
    The parameter A is usually a list of blocks (as well as a list of transitions in the state-machine case).

    Local variables are declared with:
    - typing and clocking annotations (provided by the programmer)
    - a causality label (added by elaboration) that is used to build the dependency graph of the node
    - if the variable is defined by last, the last expression and a causality label for the last variable
   *)
  Definition decl : Type := ident * (type * clock * ident * option ident).
  Inductive scope A :=
  | Scope : list decl -> A -> scope A.
  Arguments Scope {_}.

  (* Switch and state machine branches

     Declare new causality annotations (since each branch its own causality sub-graph)
   *)
  Inductive branch A :=
  | Branch : list (ident * ident) -> A -> branch A.
  Arguments Branch {_}.

  Inductive auto_type := Weak | Strong.

  Inductive block : Type :=
  | Beq : equation -> block
  | Blast : ident -> exp -> block
  | Breset : list block -> exp -> block
  | Bswitch : exp -> list (enumtag * branch (list block)) -> block
  (* For automatons : initially, states. We also need the base clock of the state-machine for clock-checking *)
  | Bauto : auto_type -> clock -> list (exp * enumtag) * enumtag ->
            list ((enumtag * ident) * branch (list transition * scope (list block * list transition))) -> block
  | Blocal : scope (list block) -> block.

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
    | Ebinop _ _ _ _
    | Eextcall _ _ _ => 1
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
    | Eextcall _ _ (cty, ck) => [(Tprimitive cty, ck)]
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
    | Eextcall _ _ (cty, _) => [Tprimitive cty]
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
    | Eextcall _ _ (_, ck) => [ck]
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
    | Eextcall _ _ (_, ck) => [(ck, None)]
    | Ewhen _ _ _ anns
    | Emerge _ _ anns
    | Ecase _ _ _ anns => map (fun _ => (snd anns, None)) (fst anns)
    end.

  Definition nclocksof (es: list exp): list nclock :=
    flat_map nclockof es.

  (** ** Variables defined by a block *)

  (** `x ` is defined by `blk` *)
  Inductive Is_defined_in_scope {A} (Pdef : A -> Prop) : var_last -> scope A -> Prop :=
  | DefScope : forall x locs blks,
      Pdef blks ->
      ~InMembers (var_last_ident x) locs ->
      Is_defined_in_scope Pdef x (Scope locs blks).

  Inductive Is_defined_in_branch {A} (Pdef : A -> Prop) : branch A -> Prop :=
    | DefBranch : forall caus blks,
        Pdef blks ->
        Is_defined_in_branch Pdef (Branch caus blks).

  Inductive Is_defined_in : var_last -> block -> Prop :=
  | DefEq : forall x xs es,
      In x xs ->
      Is_defined_in (Var x) (Beq (xs, es))
  | DefLast : forall x e,
      Is_defined_in (Last x) (Blast x e)
  | DefReset : forall x blks er,
      Exists (Is_defined_in x) blks ->
      Is_defined_in x (Breset blks er)
  | DefSwitch : forall x ec branches,
      Exists (fun blks => Is_defined_in_branch (Exists (Is_defined_in (Var x))) (snd blks)) branches ->
      Is_defined_in (Var x) (Bswitch ec branches)
  | DefAuto : forall x ini states type ck,
      Exists (fun blks => Is_defined_in_branch (fun blks => Is_defined_in_scope (fun blks => Exists (Is_defined_in (Var x)) (fst blks)) (Var x) (snd blks)) (snd blks)) states ->
      Is_defined_in (Var x) (Bauto type ck ini states)
  | DefLocal : forall x scope,
      Is_defined_in_scope (Exists (Is_defined_in x)) x scope ->
      Is_defined_in x (Blocal scope).

  Definition vars_defined_scope {A} f_vd (s : scope A) :=
    let '(Scope locs blks) := s in
    PS.filter (fun x => negb (mem_assoc_ident x locs)) (f_vd blks).

  Definition vars_defined_branch {A} (f_vd : A -> PS.t) (s : branch A) :=
    let '(Branch caus blks) := s in f_vd blks.

  Fixpoint vars_defined (d : block) :=
    match d with
    | Beq eq => ps_from_list (fst eq)
    | Blast _ _ => PS.empty
    | Breset blocks _ => PSUnion (map vars_defined blocks)
    | Bswitch _ branches =>
      PSUnion (map (fun '(_, blks) => vars_defined_branch (fun blks => PSUnion (map vars_defined blks)) blks) branches)
    | Bauto _ _ _ states =>
      PSUnion (map (fun '(_, br) => vars_defined_branch (fun '(_, blks) => vars_defined_scope (fun '(blks, _) => PSUnion (map vars_defined blks)) blks) br) states)
    | Blocal scope =>
        vars_defined_scope (fun blks => PSUnion (map vars_defined blks)) scope
    end.

  (** Check that the variables defined by `blk` are indeed `xs` *)

  Inductive VarsDefinedScope {A} (P_vd : A -> static_env -> Prop) : scope A -> static_env -> Prop :=
  | LVDscope : forall locs blks ys,
      P_vd blks (ys ++ senv_of_decls locs) ->
      VarsDefinedScope P_vd (Scope locs blks) ys.

  Inductive VarsDefinedBranch {A} (P_vd : A -> static_env -> Prop) : branch A -> static_env -> Prop :=
  | LVDbranch : forall caus blks ys ys' ysl,
      Permutation (ys'++ysl) ys ->
      (forall x, IsVar ysl x -> IsLast ysl x) ->
      P_vd blks ys' ->
      incl (map fst caus) (map fst ys) ->
      VarsDefinedBranch P_vd (Branch caus blks) ys.

  Inductive VarsDefined : block -> static_env -> Prop :=
  | VDeq : forall ys eq,
      map fst ys = fst eq ->
      VarsDefined (Beq eq) ys
  | VDlast : forall x e, VarsDefined (Blast x e) []
  | VDreset : forall blocks er xs,
      Forall2 VarsDefined blocks xs ->
      VarsDefined (Breset blocks er) (concat xs)
  | VDswitch : forall ec branches ys,
      branches <> [] ->
      Forall (fun blks => VarsDefinedBranch
                         (fun blks ys => exists xs, Forall2 VarsDefined blks xs
                                            /\ Permutation (concat xs) ys) (snd blks) ys) branches ->
      Forall (fun '(y, _) => Is_defined_in (Var y) (Bswitch ec branches)) ys ->
      VarsDefined (Bswitch ec branches) ys
  | VDauto : forall ini states type ck ys,
      states <> [] ->
      Forall (fun blks => VarsDefinedBranch
                         (fun blks ys => VarsDefinedScope
                                        (fun blks ys => exists xs, Forall2 VarsDefined (fst blks) xs
                                                           /\ Permutation (concat xs) ys)
                                        (snd blks) ys)
                         (snd blks) ys) states ->
      Forall (fun '(y, _) => Is_defined_in (Var y) (Bauto type ck ini states)) ys ->
      VarsDefined (Bauto type ck ini states) ys
  | VDlocal : forall scope ys,
      VarsDefinedScope (fun blks ys => exists xs, Forall2 VarsDefined blks xs /\ Permutation (concat xs) ys) scope ys ->
      VarsDefined (Blocal scope) ys.

  Inductive VarsDefinedCompScope {A} (P_vd : A -> list ident -> Prop) : scope A -> list ident -> Prop :=
  | LVDCscope : forall locs blks ys,
      P_vd blks (ys ++ map fst locs) ->
      VarsDefinedCompScope P_vd (Scope locs blks) ys.

  Inductive VarsDefinedCompBranch {A} (P_vd : A -> list ident -> Prop) : branch A -> list ident -> Prop :=
  | LVDCbranch : forall caus blks ys,
      P_vd blks ys ->
      incl (map fst caus) ys ->
      VarsDefinedCompBranch P_vd (Branch caus blks) ys.

  Inductive VarsDefinedComp : block -> list ident -> Prop :=
  | LVDCeq : forall eq, VarsDefinedComp (Beq eq) (fst eq)
  | VDClast : forall x e, VarsDefinedComp (Blast x e) []
  | LVDCreset : forall blocks er xs,
      Forall2 VarsDefinedComp blocks xs ->
      VarsDefinedComp (Breset blocks er) (concat xs)
  | LVDCswitch : forall ec branches ys,
      branches <> [] ->
      Forall (fun blks => VarsDefinedCompBranch
                         (fun blks ys => exists xs, Forall2 VarsDefinedComp blks xs
                                            /\ Permutation (concat xs) ys) (snd blks) ys) branches ->
      VarsDefinedComp (Bswitch ec branches) ys
  | LVDCauto : forall ini states type ck ys,
      states <> [] ->
      Forall (fun blks => VarsDefinedCompBranch
                         (fun blks ys => VarsDefinedCompScope
                                        (fun blks ys => exists xs, Forall2 VarsDefinedComp (fst blks) xs
                                                           /\ Permutation (concat xs) ys)
                                        (snd blks) ys)
                         (snd blks) ys) states ->
      VarsDefinedComp (Bauto type ck ini states) ys
  | LVDClocal : forall scope ys,
      VarsDefinedCompScope (fun blks ys => exists xs, Forall2 VarsDefinedComp blks xs /\ Permutation (concat xs) ys) scope ys ->
      VarsDefinedComp (Blocal scope) ys.

  Ltac inv_VarsDefined :=
    repeat
      match goal with
      | H:exists _, Forall2 _ _ _ /\ Permutation _ _ |- _ =>
          let Hvars := fresh "Hvars" in
          let Hperm := fresh "Hperm" in
          destruct H as (?&Hvars&Hperm)
      | H:Forall2 _ ?blks _, Hin: In _ ?blks |- _ =>
          let xs := fresh "xs" in
          let Hinxs := fresh "Hinxs" in
          let Hdef := fresh "Hdef" in
          eapply Forall2_ignore2, Forall_forall in H as (xs&Hinxs&Hdef); [|eapply Hin]
      | H:Forall2 _ _ ?xs, Hin: In _ ?xs |- _ =>
          let blk := fresh "blk" in
          let Hinblks := fresh "Hinblks" in
          let Hdef := fresh "Hdef" in
          eapply Forall2_ignore1, Forall_forall in H as (blk&Hinblks&Hdef); [|eapply Hin]
      | H:Forall (fun _ => exists _ _, Forall2 _ _ _ /\ _ /\ Permutation _ _) ?brs, Hin: In _ ?brs |- _ =>
          let Hvars := fresh "Hvars" in
          let Hlast := fresh "Hlast" in
          let Hperm := fresh "Hperm" in
          eapply Forall_forall in H as (?&Hvars&Hlast&Hperm); [|eapply Hin]
      end.

  Definition lasts_of_decls (decls : list decl) :=
    map_filter (fun '(x, (_, _, _, o)) => option_map (fun _ => x) o) decls.

  Inductive LastsDefinedScope {A} (P_vd : A -> list ident -> Prop) : scope A -> list ident -> Prop :=
  | LDscope : forall locs blks ys,
      P_vd blks (ys ++ lasts_of_decls locs) ->
      LastsDefinedScope P_vd (Scope locs blks) ys.

  Inductive LastsDefinedBranch {A} (P_vd : A -> Prop) : branch A -> Prop :=
  | LDbranch : forall caus blks,
      P_vd blks ->
      LastsDefinedBranch P_vd (Branch caus blks).

  Inductive LastsDefined : block -> list ident -> Prop :=
  | LDeq : forall eq, LastsDefined (Beq eq) []
  | LDlast : forall x e, LastsDefined (Blast x e) [x]
  | LDreset : forall blocks er xs,
      Forall2 LastsDefined blocks xs ->
      LastsDefined (Breset blocks er) (concat xs)
  | LDswitch : forall ec branches,
      branches <> [] ->
      Forall (fun blks => LastsDefinedBranch (Forall (fun blk => LastsDefined blk [])) (snd blks)) branches ->
      LastsDefined (Bswitch ec branches) []
  | LDauto : forall ini states type ck,
      states <> [] ->
      Forall (fun br =>
                LastsDefinedBranch
                  (fun s => LastsDefinedScope
                           (fun blks ys => exists xs, Forall2 LastsDefined (fst blks) xs
                                              /\ Permutation (concat xs) ys)
                           (snd s) []) (snd br)) states ->
      LastsDefined (Bauto type ck ini states) []
  | LDlocal : forall scope ys,
      LastsDefinedScope (fun blks ys => exists xs, Forall2 LastsDefined blks xs /\ Permutation (concat xs) ys) scope ys ->
      LastsDefined (Blocal scope) ys.

  (** ** Shadowing is prohibited *)

  Inductive NoDupScope {A} (P_nd : list ident -> A -> Prop) : list ident -> scope A -> Prop :=
  | NDscope : forall env locs blks,
      P_nd (env ++ map fst locs) blks ->
      NoDupMembers locs ->
      (forall x, InMembers x locs -> ~In x env) ->
      NoDupScope P_nd env (Scope locs blks).

  Inductive NoDupBranch {A} (P_nd : A -> Prop) : branch A -> Prop :=
  | NDbranch : forall caus blks,
      P_nd blks ->
      NoDupMembers caus ->
      NoDupBranch P_nd (Branch caus blks).

  Inductive NoDupLocals : list ident -> block -> Prop :=
  | NDLeq : forall env eq, NoDupLocals env (Beq eq)
  | NDLlast : forall env x e, NoDupLocals env (Blast x e)
  | NDLreset : forall env blocks er,
      Forall (NoDupLocals env) blocks ->
      NoDupLocals env (Breset blocks er)
  | NDLswitch : forall env ec branches,
      Forall (fun blks => NoDupBranch (Forall (NoDupLocals env)) (snd blks)) branches ->
      NoDupLocals env (Bswitch ec branches)
  | NDLauto : forall env type ini states ck,
      Forall (fun blks => NoDupBranch (fun blks => NoDupScope (fun env blks => Forall (NoDupLocals env) (fst blks)) env (snd blks)) (snd blks)) states ->
      NoDupLocals env (Bauto type ck ini states)
  | NDLlocal : forall env scope,
      NoDupScope (fun env => Forall (NoDupLocals env)) env scope ->
      NoDupLocals env (Blocal scope).

  Lemma NoDupScope_NoDupMembers : forall Γ locs,
      NoDupMembers Γ ->
      NoDupMembers locs ->
      (forall x, InMembers x locs -> ~In x (map fst Γ)) ->
      NoDupMembers (Γ ++ senv_of_decls locs).
  Proof.
    intros * Nd1 Nd2 Nd3.
    apply NoDupMembers_app; auto.
    - now apply NoDupMembers_senv_of_decls.
    - intros * In1 In2. rewrite fst_InMembers in In1. rewrite InMembers_senv_of_decls in In2.
      eapply Nd3; eauto.
  Qed.

  (** ** All the locals must be well-formed *)

  Inductive GoodLocalsScope {A} (P_good : A -> Prop) (prefs : PS.t) : scope A -> Prop :=
  | GoodScope : forall locs blks,
      Forall (AtomOrGensym prefs) (map fst locs) ->
      P_good blks ->
      GoodLocalsScope P_good prefs (Scope locs blks).

  Inductive GoodLocalsBranch {A} (P_good : A -> Prop) : branch A -> Prop :=
  | GoodBranch : forall caus blks,
      P_good blks ->
      GoodLocalsBranch P_good (Branch caus blks).

  Inductive GoodLocals (prefs : PS.t) : block -> Prop :=
  | GoodEq : forall eq,
      GoodLocals prefs (Beq eq)
  | GoodLast : forall x ty,
      GoodLocals prefs (Blast x ty)
  | GoodReset : forall blks er,
      Forall (GoodLocals prefs) blks ->
      GoodLocals prefs (Breset blks er)
  | GoodSwitch : forall ec branches,
      Forall (fun blks => GoodLocalsBranch (Forall (GoodLocals prefs)) (snd blks)) branches ->
      GoodLocals prefs (Bswitch ec branches)
  | GoodAuto : forall type ini states ck,
      Forall (fun blks => GoodLocalsBranch (fun blks => GoodLocalsScope (fun blks => Forall (GoodLocals prefs) (fst blks)) prefs (snd blks)) (snd blks)) states ->
      GoodLocals prefs (Bauto type ck ini states)
  | GoodLocal : forall scope,
      GoodLocalsScope (Forall (GoodLocals prefs)) prefs scope ->
      GoodLocals prefs (Blocal scope).

  (* Full node

    The `PSyn` and `prefs` parameters are used to caracterize changes in nodes
    during compilation
    - `PSyn` indicates a property of the syntax of block
      (see `noauto_block`, `noswitch_block`, `nolocal_top_block`)
    - `prefs` indicates the possible prefix for variable names in a node.
      for instance, after elaboration, names of the form "elab$x$42" can appear.
      after compilation of last expressions, names of the form "last$x$42" can also appear.
      See `AtomOrGensym` and `GoodLocals` for more details

    These are represented as type parameters of a node.
    The other solution would be to use subset types, but this would complicate the
    definition compilation functions over the global.
    With this representation, most of these functions are simply defined as mapping
    a node compilation function.

    Input and Output variables are declared with:
    - typing and clocking annotations (provided by the programmer)
    - a causality label (added by elaboration) that is used to build the dependency graph of the node
   *)
  Record node {PSyn : _ -> _ -> Prop} {prefs : PS.t} : Type :=
    mk_node {
        n_name     : ident;
        n_hasstate : bool;
        n_in       : list (ident * (type * clock * ident));
        n_out      : list decl;
        n_block    : block;

        n_ingt0    : 0 < length n_in;
        n_outgt0   : 0 < length n_out;
        n_defd     : exists xs, VarsDefined n_block xs /\ Permutation xs (senv_of_decls n_out);
        n_lastd    : exists xs, LastsDefined n_block xs /\ Permutation xs (lasts_of_decls n_out);
        n_nodup    : NoDup (map fst n_in ++ map fst n_out) /\
                     NoDupLocals (map fst n_in ++ map fst n_out) n_block;
        n_good     : Forall (AtomOrGensym prefs) (map fst n_in ++ map fst n_out)
                     /\ GoodLocals prefs n_block
                     /\ atom n_name;
        n_syn      : PSyn n_out n_block;
      }.

  Global Instance node_unit {PSyn prefs} : ProgramUnit (@node PSyn prefs) :=
    { name := n_name; }.

  (** ** Program *)

  Record global {PSyn prefs} :=
    Global {
        types   : list type;
        externs : list (ident * (list ctype * ctype));
        nodes   : list (@node PSyn prefs);
      }.
  Arguments Global {_ _}.

  Global Program Instance global_program {PSyn prefs} : Program (@node PSyn prefs) global :=
    { units := nodes;
      update := fun g => Global g.(types) g.(externs) }.

  Section find_node.
    Context {PSyn : list decl -> block -> Prop}.
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
      forall f n G types externs,
        n.(n_name) = f ->
        find_node f (Global types externs (n::G)) = Some n.
    Proof.
      intros * Heq; subst.
      unfold find_node, find_unit; simpl.
      destruct (ident_eq_dec _ _); simpl; congruence.
    Qed.

    Lemma find_node_other:
      forall f n G types externs,
        n.(n_name) <> f ->
        find_node f (Global types externs (n::G)) = find_node f (Global types externs G).
    Proof.
      intros * Hnf.
      unfold find_node. f_equal.
      eapply find_unit_other; eauto.
      now intros ?.
    Qed.

    Lemma find_node_cons f (a : @node PSyn prefs) types externs nds n :
      find_node f (Global types externs (a :: nds)) = Some n ->
      (f = n_name a /\ a = n) \/
      (f <> n_name a /\ find_node f (Global types externs nds) = Some n).
    Proof.
      unfold find_node. intros Hfind.
      apply option_map_inv in Hfind as ((?&?)&Hfind&?); subst.
      eapply CommonProgram.find_unit_cons in Hfind as [(?&?)|(?&?)]; try reflexivity.
      - inv H0. eauto.
      - simpl in *. right.
        rewrite H0; auto.
    Qed.

    Lemma find_node_change_types : forall nds enms enms' ext ext' f,
        find_node f (Global enms ext nds) = find_node f (Global enms' ext' nds).
    Proof.
      induction nds; intros *. reflexivity.
      destruct (ident_eq_dec f (n_name a)); subst.
      - rewrite 2 find_node_now; auto.
      - rewrite 2 find_node_other; auto.
    Qed.

    Lemma find_node_In :
      forall G n,
        NoDup (List.map name (units G)) ->
        In n (nodes G) ->
        find_node (n_name n) G = Some n.
    Proof.
      unfold find_node.
      intros * Nd Hin.
      eapply In_find_unit in Nd as (?&?); eauto.
      now setoid_rewrite H.
    Qed.

    Lemma name_find_node :
      forall f G,
        In f (map n_name (nodes G)) ->
        exists nd, find_node f G = Some nd.
    Proof.
      intros * Hin.
      destruct G as [tys exts nds].
      induction nds as [|nd]; simpl in *. contradiction.
      destruct (ident_eq_dec (n_name nd) f).
      - rewrite find_node_now; eauto.
      - rewrite find_node_other; firstorder; auto.
    Qed.

    Lemma find_node_name :
      forall f G n,
        find_node f G = Some n ->
        In f (map n_name (nodes G)).
    Proof.
      intros * Hf.
      pose proof (find_node_Exists f G) as Hi.
      rewrite Exists_exists in Hi.
      destruct Hi as [[? []] ?]; subst; try congruence.
      now apply in_map.
    Qed.

  End find_node.

  Lemma equiv_program_types {PSyn prefs} : forall (G G' : @global PSyn prefs),
      equiv_program G G' ->
      types G = types G'.
  Proof.
    intros * Heq.
    specialize (Heq []); inv Heq; auto.
  Qed.

  Corollary suffix_types {PSyn prefs} : forall (G G' : @global PSyn prefs),
      suffix G G' ->
      types G = types G'.
  Proof.
    intros * Suff. inv Suff.
    apply equiv_program_types; auto.
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

    Hypothesis EextcallCase:
      forall f es ann,
        Forall P es ->
        P (Eextcall f es ann).

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
      - apply EextcallCase; SolveForall; auto.
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

    Hypothesis BlastCase:
      forall x e,
        P (Blast x e).

    Hypothesis BresetCase:
      forall blocks er,
        Forall P blocks ->
        P (Breset blocks er).

    Hypothesis BswitchCase:
      forall ec branches,
        Forall (fun '(_, Branch _ blks) => Forall P blks) branches ->
        P (Bswitch ec branches).

    Hypothesis BautoCase:
      forall type ini states ck,
        Forall (fun '(_, Branch _ (_, Scope _ (blks, _))) => Forall P blks) states ->
        P (Bauto type ck ini states).

    Hypothesis BlocalCase:
      forall locs blocks,
        Forall P blocks ->
        P (Blocal (Scope locs blocks)).

    Fixpoint block_ind2 (d: block) : P d.
    Proof.
      destruct d.
      - apply BeqCase; auto.
      - apply BlastCase; auto.
      - apply BresetCase; induction l; auto.
      - apply BswitchCase; induction l as [|[?[? blks]]]; constructor; auto.
        induction blks; auto.
      - apply BautoCase; induction l as [|[?[?[?[?[blks ?]]]]]]; constructor; auto.
        induction blks; auto.
      - destruct s as [? blks]. apply BlocalCase; induction blks; auto.
    Qed.

  End block_ind2.

  (** annots *)

  Fact length_annot_numstreams : forall e,
      length (annot e) = numstreams e.
  Proof.
    destruct e; simpl; auto; destruct_conjs; auto using length_map.
  Qed.

  (** typesof *)

  Fact typeof_annot : forall e,
      typeof e = map fst (annot e).
  Proof.
    destruct e; simpl; try reflexivity;
      destruct_conjs; auto.
    all:now rewrite map_map, map_id.
  Qed.

  Corollary length_typeof_numstreams : forall e,
      length (typeof e) = numstreams e.
  Proof.
    intros.
    rewrite typeof_annot.
    rewrite length_map.
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
    apply length_map.
  Qed.

  Fact annots_numstreams : forall es,
      length (annots es) = list_sum (List.map numstreams es).
  Proof.
    induction es; simpl; auto.
    rewrite length_app; f_equal; auto.
    rewrite <- length_typeof_numstreams, typeof_annot.
    now rewrite length_map.
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
    destruct e; simpl; try reflexivity; destruct_conjs;
      repeat rewrite map_map; auto.
  Qed.

  Corollary length_clockof_numstreams : forall e,
      length (clockof e) = numstreams e.
  Proof.
    intros.
    rewrite clockof_annot.
    repeat rewrite length_map.
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
    apply length_map.
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
    destruct e; simpl; try reflexivity;
      destruct_conjs; repeat rewrite map_map; auto.
  Qed.

  Corollary length_nclockof_numstreams : forall e,
      length (nclockof e) = numstreams e.
  Proof.
    intros.
    erewrite <-length_map, nclockof_annot, length_map.
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
    erewrite <-length_map, nclocksof_annots, length_map. auto.
  Qed.

  Lemma clockof_nclockof:
    forall e,
      clockof e = map stripname (nclockof e).
  Proof.
    destruct e; simpl; destruct_conjs; try rewrite map_map; auto.
  Qed.

  Lemma nclockof_length :
    forall e, length (nclockof e) = length (clockof e).
  Proof.
    intros e. rewrite clockof_nclockof, length_map; auto.
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
    Context {PSyn1 PSyn2 : list decl -> block -> Prop}.
    Context {prefs1 prefs2 : PS.t}.

    (** Nodes are equivalent if their interface are equivalent,
        that is if they have the same identifier and the same
        input/output types *)
    Definition node_iface_eq (n : @node PSyn1 prefs1) (n' : @node PSyn2 prefs2) : Prop :=
      n.(n_name) = n'.(n_name) /\
      n.(n_hasstate) = n'.(n_hasstate) /\
      map (fun '(x, (ty, ck, _)) => (x, (ty, ck))) n.(n_in) = map (fun '(x, (ty, ck, _)) => (x, (ty, ck))) n'.(n_in) /\
      map (fun '(x, (ty, ck, _, _)) => (x, (ty, ck))) n.(n_out) = map (fun '(x, (ty, ck, _, _)) => (x, (ty, ck))) n'.(n_out).

    Definition global_iface_incl (G : @global PSyn1 prefs1) (G' : @global PSyn2 prefs2) : Prop :=
      incl (types G) (types G')
      /\ incl (externs G) (externs G')
      /\ forall f n, find_node f G = Some n ->
               exists n', find_node f G' = Some n' /\ node_iface_eq n n'.

    (** Globals are equivalent if they contain equivalent nodes *)
    Definition global_iface_eq (G : @global PSyn1 prefs1) (G' : @global PSyn2 prefs2) : Prop :=
      types G = types G'
      /\ externs G = externs G'
      /\ forall f, orel2 node_iface_eq (find_node f G) (find_node f G').

    Lemma iface_eq_iface_incl : forall (G : @global PSyn1 prefs1) (G' : @global PSyn2 prefs2),
        global_iface_eq G G' ->
        global_iface_incl G G'.
    Proof.
      intros * (Htyps&Hexts&Hg2).
      repeat split.
      - now rewrite Htyps.
      - now rewrite Hexts.
      - intros * Hfind. specialize (Hg2 f). rewrite Hfind in Hg2; inv Hg2. eauto.
    Qed.

    Lemma global_iface_eq_nil : forall types externs,
        global_iface_eq (Global types externs []) (Global types externs []).
    Proof.
      unfold global_iface_eq, find_node.
      repeat split; auto.
      intros *; simpl. constructor.
    Qed.

    Lemma global_iface_eq_cons : forall types externs nds nds' n n',
        global_iface_eq (Global types externs nds) (Global types externs nds') ->
        n.(n_name) = n'.(n_name) ->
        n.(n_hasstate) = n'.(n_hasstate) ->
        n.(n_in) = n'.(n_in) ->
        n.(n_out) = n'.(n_out) ->
        global_iface_eq (Global types externs (n::nds)) (Global types externs (n'::nds')).
    Proof.
      intros * (?&?&Heq) Hname Hstate Hin Hout.
      repeat split; auto. intros ?.
      destruct (Pos.eq_dec (n_name n) f); subst.
      - simpl. repeat rewrite find_node_now; auto.
        repeat constructor; f_equal; auto.
      - repeat rewrite find_node_other; auto.
        congruence.
    Qed.

    Lemma global_iface_eq_find : forall G G' f n,
        global_iface_eq G G' ->
        find_node f G = Some n ->
        exists n', (find_node f G' = Some n' /\
               node_iface_eq n n').
    Proof.
      intros G G' f n (_&_&Hglob) Hfind.
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

  Lemma global_iface_incl_refl {PSyn prefs} : Reflexive (@global_iface_incl PSyn _ prefs _).
  Proof.
    intros G. repeat split; intros; try reflexivity.
    do 2 esplit; eauto. apply node_iface_eq_refl.
  Qed.

  Fact global_iface_incl_trans {P1 P2 P3 p1 p2 p3} : forall (n1 : @global P1 p1) (n2 : @global P2 p2) (n3 : @global P3 p3),
      global_iface_incl n1 n2 ->
      global_iface_incl n2 n3 ->
      global_iface_incl n1 n3.
  Proof.
    intros n1 n2 n3 H12 H23.
    destruct H12 as (?&?&H12), H23 as (?&?&H23).
    repeat split. 1,2:etransitivity; eauto.
    - intros * Hfind. specialize (H12 _ _ Hfind) as (?&Hfind2&?).
      specialize (H23 _ _ Hfind2) as (?&Hfind3&?).
      do 2 esplit; eauto.
      eapply node_iface_eq_trans; eauto.
  Qed.

  Fact global_iface_eq_refl {PSyn prefs} : Reflexive (@global_iface_eq PSyn _ prefs _).
  Proof.
    intros G. repeat split; intros; try reflexivity.
    destruct (find_node f G); constructor.
    apply node_iface_eq_refl.
  Qed.

  Fact global_iface_eq_sym {P1 P2 p1 p2} : forall (G1 : @global P1 p1) (G2 : @global P2 p2),
      global_iface_eq G1 G2 ->
      global_iface_eq G2 G1.
  Proof.
    intros * (?&?&H12).
    repeat split; auto.
    intros f. specialize (H12 f).
    inv H12; constructor; auto.
    apply node_iface_eq_sym; auto.
  Qed.

  Fact global_iface_eq_trans {P1 P2 P3 p1 p2 p3} : forall (n1 : @global P1 p1) (n2 : @global P2 p2) (n3 : @global P3 p3),
      global_iface_eq n1 n2 ->
      global_iface_eq n2 n3 ->
      global_iface_eq n1 n3.
  Proof.
    intros n1 n2 n3 H12 H23.
    destruct H12 as (?&?&H12), H23 as (?&?&H23).
    repeat split; try congruence.
    intros f. specialize (H12 f). specialize (H23 f).
    inv H12; inv H23; try congruence; constructor.
    rewrite <-H4 in H6. inv H6.
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
  | wl_Eextapp : forall G f es ann,
      Forall (wl_exp G) es ->
      annots es <> [] ->
      wl_exp G (Eextcall f es ann)
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

  Inductive wl_scope {A} (P_wl : A -> Prop) {PSyn prefs} (G : @global PSyn prefs) : scope A -> Prop :=
  | wl_Scope : forall locs blks,
      P_wl blks ->
      wl_scope P_wl G (Scope locs blks).

  Inductive wl_branch {A} (P_wl : A -> Prop) : branch A -> Prop :=
  | wl_Branch : forall caus blks,
      P_wl blks ->
      wl_branch P_wl (Branch caus blks).

  Inductive wl_block {PSyn prefs} (G : @global PSyn prefs) : block -> Prop :=
  | wl_Beq : forall eq,
      wl_equation G eq ->
      wl_block G (Beq eq)
  | wl_Blast : forall x e,
      wl_exp G e ->
      numstreams e = 1 ->
      wl_block G (Blast x e)
  | wl_Breset : forall blocks er,
      Forall (wl_block G) blocks ->
      wl_exp G er ->
      numstreams er = 1 ->
      wl_block G (Breset blocks er)
  | wl_Bswitch : forall ec branches,
      wl_exp G ec ->
      numstreams ec = 1 ->
      branches <> [] ->
      Forall (fun blks => wl_branch (Forall (wl_block G)) (snd blks)) branches ->
      wl_block G (Bswitch ec branches)
  | wl_Bauto : forall type ini oth states ck,
      Forall (fun '(e, _) => wl_exp G e /\ numstreams e = 1) ini ->
      states <> [] ->
      Forall (fun blks =>
                wl_branch (fun blks =>
                             Forall (fun '(e, _) => wl_exp G e /\ numstreams e = 1) (fst blks)
                             /\ wl_scope (fun blks =>
                                           Forall (wl_block G) (fst blks)
                                           /\ Forall (fun '(e, _) => wl_exp G e /\ numstreams e = 1) (snd blks)) G (snd blks)
                  ) (snd blks)) states ->
      wl_block G (Bauto type ck (ini, oth) states)
  | wl_Blocal : forall scope,
      wl_scope (Forall (wl_block G)) G scope ->
      wl_block G (Blocal scope).

  Inductive wl_node {PSyn prefs} (G : @global PSyn prefs) : @node PSyn prefs -> Prop :=
  | wl_Node : forall n,
      wl_block G (n_block n) ->
      wl_node G n.

  Definition wl_global {PSyn prefs} : @global PSyn prefs -> Prop :=
    wt_program wl_node.

  (** ** Limiting the variables appearing in expression, equation or block to an environnement *)

  Inductive wx_clock (vars : static_env) : clock -> Prop :=
  | wx_Cbase : wx_clock vars Cbase
  | wx_Con : forall ck x tx,
      wx_clock vars ck ->
      IsVar vars x ->
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
  | wc_Eextcall : forall f es ann,
      Forall (wx_exp Γ) es ->
      wx_exp Γ (Eextcall f es ann)
  | wx_Efby : forall e0s es anns,
      Forall (wx_exp Γ) e0s ->
      Forall (wx_exp Γ) es ->
      wx_exp Γ (Efby e0s es anns)
  | wx_Earrow : forall e0s es anns,
      Forall (wx_exp Γ) e0s ->
      Forall (wx_exp Γ) es ->
      wx_exp Γ (Earrow e0s es anns)
  | wx_Ewhen : forall es x tx b tys nck,
      IsVar Γ x ->
      Forall (wx_exp Γ) es ->
      wx_exp Γ (Ewhen es (x, tx) b (tys, nck))
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

  Inductive wx_scope {A} (P_wx : static_env -> A -> Prop) : static_env -> scope A -> Prop :=
  | wx_Scope : forall Γ locs blks,
      let Γ' := Γ ++ senv_of_decls locs in
      P_wx Γ' blks ->
      wx_scope P_wx Γ (Scope locs blks).

  Inductive wx_branch {A} (P_wx : A -> Prop) : branch A -> Prop :=
  | wx_Branch : forall caus blks,
      P_wx blks ->
      wx_branch P_wx (Branch caus blks).

  Inductive wx_block : static_env -> block -> Prop :=
  | wx_Beq : forall Γ eq,
      wx_equation Γ eq ->
      wx_block Γ (Beq eq)
  | wx_Blast : forall Γ x e,
      IsLast Γ x ->
      wx_exp Γ e ->
      wx_block Γ (Blast x e)
  | wx_Breset : forall Γ blks er,
      Forall (wx_block Γ) blks ->
      wx_exp Γ er ->
      wx_block Γ (Breset blks er)
  | wc_Bswitch : forall Γ ec branches,
      wx_exp Γ ec ->
      Forall (fun blks => wx_branch ( Forall (wx_block Γ)) (snd blks)) branches ->
      wx_block Γ (Bswitch ec branches)
  | wx_Bauto : forall Γ type ini oth states ck,
      wx_clock Γ ck ->
      Forall (fun '(e, _) => wx_exp Γ e) ini ->
      states <> [] ->
      Forall (fun blks =>
                wx_branch
                  (fun blks =>
                     Forall (fun '(e, _) => wx_exp Γ e) (fst blks)
                     /\ wx_scope (fun Γ blks => Forall (wx_block Γ) (fst blks)
                                            /\ Forall (fun '(e, _) => wx_exp Γ e) (snd blks)) Γ (snd blks))
                  (snd blks)
        ) states ->
      wx_block Γ (Bauto type ck (ini, oth) states)
  | wx_Blocal : forall Γ scope,
      wx_scope (fun Γ => Forall (wx_block Γ)) Γ scope ->
      wx_block Γ (Blocal scope).

  Inductive wx_node {PSyn prefs} : @node PSyn prefs -> Prop :=
  | wx_Node : forall n,
      let Γ := senv_of_ins (n_in n) ++ senv_of_decls (n_out n) in
      wx_block Γ (n_block n) ->
      wx_node n.

  Definition wx_global {PSyn prefs} (G: @global PSyn prefs) : Prop :=
    Forall wx_node (nodes G).

  Section wx_incl.

    Hint Constructors wx_exp wx_block : core.

    Lemma wx_clock_incl : forall Γ Γ' ck,
        (forall x, IsVar Γ x -> IsVar Γ' x) ->
        wx_clock Γ ck ->
        wx_clock Γ' ck.
    Proof.
      induction ck; intros * Hv Hwx; inv Hwx; constructor; eauto.
    Qed.

    Lemma wx_exp_incl : forall Γ Γ' e,
        (forall x, IsVar Γ x -> IsVar Γ' x) ->
        (forall x, IsLast Γ x -> IsLast Γ' x) ->
        wx_exp Γ e ->
        wx_exp Γ' e.
    Proof.
      induction e using exp_ind2; intros * Hincl1 Hincl2 Hwx; inv Hwx; eauto with senv;
        constructor; simpl_Forall; eauto.
      - intros ??; subst; simpl in *.
        simpl_Forall; eauto.
        eapply Forall_forall in H7; eauto.
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

    Fact wx_scope_incl {A} (P_wx: _ -> A -> Prop) :  forall Γ Γ' locs blks,
        (forall x, IsVar Γ x -> IsVar Γ' x) ->
        (forall x, IsLast Γ x -> IsLast Γ' x) ->
        (forall Γ Γ', (forall x, IsVar Γ x -> IsVar Γ' x) ->
                 (forall x, IsLast Γ x -> IsLast Γ' x) ->
                 P_wx Γ blks ->
                 P_wx Γ' blks) ->
        wx_scope P_wx Γ (Scope locs blks) ->
        wx_scope P_wx Γ' (Scope locs blks).
    Proof.
      intros * Hin1 Hin2 Hp Hwx. inv Hwx.
      econstructor; subst Γ'0; eauto.
      - eapply Hp; [| |eauto]; intros ?.
        rewrite 2 IsVar_app. intros [|]; eauto.
        rewrite 2 IsLast_app. intros [|]; eauto.
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
      - (* last *)
        econstructor; eauto using wx_exp_incl.
      - (* reset *)
        constructor; simpl_Forall; eauto.
        eapply wx_exp_incl; eauto.
      - (* switch *)
        constructor.
        + eapply wx_exp_incl; eauto.
        + simpl_Forall; eauto. take (wx_branch _ _) and inv it. constructor.
          simpl_Forall; eauto.
      - (* automaton *)
        constructor; auto; simpl_Forall; eauto using wx_exp_incl, wx_clock_incl.
        take (wx_branch _ _) and inv it. constructor. destruct_conjs.
        destruct s. split; simpl_Forall; eauto using wx_exp_incl.
        eapply wx_scope_incl; eauto.
        intros * ?? (?&?); split; simpl_Forall; eauto using wx_exp_incl.
      - (* local *)
        constructor. eapply wx_scope_incl; eauto.
        intros; simpl_Forall; eauto.
    Qed.
  End wx_incl.

  (** ** Specifications of some subsets of the language *)

  (** *** Normalized expressions *)

  Inductive normalized_lexp : exp -> Prop :=
  | normalized_Econst : forall c, normalized_lexp (Econst c)
  | normalized_Eenum : forall k ty, normalized_lexp (Eenum k ty)
  | normalized_Evar : forall x ty ck, normalized_lexp (Evar x (ty, ck))
  | normalized_Elast : forall x ty ck, normalized_lexp (Elast x (ty, ck))
  | normalized_Eunop : forall op e1 ty cl,
      normalized_lexp e1 ->
      normalized_lexp (Eunop op e1 (ty, cl))
  | normalized_Ebinop : forall op e1 e2 ty cl,
      normalized_lexp e1 ->
      normalized_lexp e2 ->
      normalized_lexp (Ebinop op e1 e2 (ty, cl))
  | normalized_Ewhen : forall e x b ty cl,
      normalized_lexp e ->
      normalized_lexp (Ewhen [e] x b ([ty], cl)).

  Inductive normalized_cexp : exp -> Prop :=
  | normalized_Emerge : forall x es ty cl,
      Forall (fun es => exists e, (snd es) = [e] /\ normalized_cexp e) es ->
      normalized_cexp (Emerge x es ([ty], cl))
  | normalized_Ecase : forall e es d ty cl,
      normalized_lexp e ->
      Forall (fun es => exists e, (snd es) = [e] /\ normalized_cexp e) es ->
      (forall ds, d = Some ds -> exists d, ds = [d] /\ normalized_cexp d) ->
      normalized_cexp (Ecase e es d ([ty], cl))
  | normalized_lexp_cexp : forall e,
      normalized_lexp e ->
      normalized_cexp e.

  Global Hint Constructors normalized_lexp normalized_cexp : lsyntax norm.

  (** *** Normalized blocks and nodes *)

  Inductive normalized_constant : exp -> Prop :=
  | constant_Econst : forall c,
      normalized_constant (Econst c)
  | constant_Eenum : forall k ty,
      normalized_constant (Eenum k ty)
  | constant_Ewhen : forall e x b ty cl,
      normalized_constant e ->
      normalized_constant (Ewhen [e] x b ([ty], cl)).

  Inductive normalized_equation (outs: list ident) (lasts: list ident) : equation -> Prop :=
  | normalized_eq_Eapp : forall xs f es er lann,
      Forall normalized_lexp es ->
      Forall (fun e => exists x ann, e = Evar x ann) er ->
      Forall (fun x => ~In x lasts) xs ->
      normalized_equation outs lasts (xs, [Eapp f es er lann])
  | normalized_eq_Efby : forall x e0 e ann,
      normalized_constant e0 ->
      normalized_lexp e ->
      ~In x outs ->
      ~In x lasts ->
      normalized_equation outs lasts ([x], [Efby [e0] [e] [ann]])
  | normalized_eq_Eextcall : forall x f es ann,
      Forall normalized_lexp es ->
      ~In x lasts ->
      normalized_equation outs lasts ([x], [Eextcall f es ann])
  | normalized_eq_cexp : forall x e,
      normalized_cexp e ->
      normalized_equation outs lasts ([x], [e]).

  Inductive normalized_block (outs: list ident) (lasts: list ident) : block -> Prop :=
  | normalized_Beq : forall eq,
      normalized_equation outs lasts eq ->
      normalized_block outs lasts (Beq eq)
  | normalized_Blast : forall x e,
      normalized_constant e ->
      normalized_block outs lasts (Blast x e)
  | normalized_Breset : forall block x ann,
      normalized_block outs lasts block ->
      normalized_block outs lasts (Breset [block] (Evar x ann)).

  Inductive normalized : list decl -> block -> Prop :=
  | Normnode : forall out locs blks,
      Forall (fun '(_, (_, _, o)) => o = None) out ->
      Forall (normalized_block (List.map fst out) (lasts_of_decls locs)) blks ->
      (exists xs, VarsDefinedComp (Blocal (Scope locs blks)) xs /\ Permutation xs (map fst out)) ->
      normalized out (Blocal (Scope locs blks)).

  Global Hint Constructors normalized_constant normalized_equation normalized_block : lsyntax norm.

  (** *** Unnested equations *)

  Inductive unnested_equation (lasts: list ident) : equation -> Prop :=
  | unnested_eq_Eapp : forall xs f es er lann,
      Forall normalized_lexp es ->
      Forall (fun e => exists x ann, e = Evar x ann) er ->
      Forall (fun x => ~In x lasts) xs ->
      unnested_equation lasts (xs, [Eapp f es er lann])
  | unnested_eq_Efby : forall x e0 e ann,
      normalized_lexp e0 ->
      normalized_lexp e ->
      ~In x lasts ->
      unnested_equation lasts ([x], [Efby [e0] [e] [ann]])
  | unnested_eq_Earrow : forall x e0 e ann,
      normalized_lexp e0 ->
      normalized_lexp e ->
      unnested_equation lasts ([x], [Earrow [e0] [e] [ann]])
  | unnested_eq_Eextcall: forall x f es ann,
      Forall normalized_lexp es ->
      ~In x lasts ->
      unnested_equation lasts ([x], [Eextcall f es ann])
  | unnested_eq_cexp : forall x e,
      normalized_cexp e ->
      unnested_equation lasts ([x], [e]).

  (** *** After normalization of last *)

  Inductive normlast_block (lasts: list ident) : block -> Prop :=
  | normlast_Beq : forall eq,
      unnested_equation lasts eq ->
      normlast_block lasts (Beq eq)
  | normlast_Blast : forall x e,
      normalized_constant e ->
      normlast_block lasts (Blast x e)
  | normlast_Breset : forall block x ann,
      normlast_block lasts block ->
      normlast_block lasts (Breset [block] (Evar x ann)).

  Inductive normlast : list decl -> block -> Prop :=
  | NormLnode : forall out locs blks,
      Forall (fun '(_, (_, _, o)) => o = None) out ->
      Forall (normlast_block (lasts_of_decls locs)) blks ->
      (exists xs, VarsDefinedComp (Blocal (Scope locs blks)) xs /\ Permutation xs (map fst out)) ->
      normlast out (Blocal (Scope locs blks)).

  Global Hint Constructors normlast_block : lsyntax norm.

  (** *** Unnested blocks and nodes *)

  Inductive unnested_block : block -> Prop :=
  | unnested_Beq : forall eq,
      unnested_equation [] eq ->
      unnested_block (Beq eq)
  | unnested_Blast : forall x e,
      normalized_lexp e ->
      unnested_block (Blast x e)
  | unnested_Breset : forall block x ann,
      unnested_block block ->
      unnested_block (Breset [block] (Evar x ann)).

  Inductive unnested : list decl -> block -> Prop :=
  | UNnode : forall out locs blks,
      Forall unnested_block blks ->
      (exists xs, VarsDefinedComp (Blocal (Scope locs blks)) xs /\ Permutation xs (map fst out)) ->
      unnested out (Blocal (Scope locs blks)).

  Global Hint Constructors unnested_equation unnested_block : lsyntax norm.

  (** *** Without local blocks *)

  Inductive nolocal_block : block -> Prop :=
  | NLeq : forall eq, nolocal_block (Beq eq)
  | NLlast : forall x e, nolocal_block (Blast x e)
  | NLreset : forall blks er,
      Forall nolocal_block blks ->
      nolocal_block (Breset blks er).

  Inductive nolocal_top_block : block -> Prop :=
  | NLtop : forall locs blks,
      Forall nolocal_block blks ->
      nolocal_top_block (Blocal (Scope locs blks)).

  Inductive nolocal : list decl -> block -> Prop :=
  | NLnode : forall out blk,
      nolocal_top_block blk ->
      (exists xs, VarsDefinedComp blk xs /\ Permutation xs (map fst out)) ->
      nolocal out blk.

  (** *** Without switches *)

  Inductive noswitch_block : block -> Prop :=
  | NSeq : forall eq, noswitch_block (Beq eq)
  | NSlast : forall x e, noswitch_block (Blast x e)
  | NSreset : forall blks er,
      Forall noswitch_block blks ->
      noswitch_block (Breset blks er)
  | NSlocal : forall locs blks,
      Forall noswitch_block blks ->
      noswitch_block (Blocal (Scope locs blks)).

  Inductive noswitch : list decl -> block -> Prop :=
  | NSnode : forall out blk,
      noswitch_block blk ->
      (exists xs, VarsDefinedComp blk xs /\ Permutation xs (map fst out)) ->
      noswitch out blk.

  (** *** Without automaton *)

  Inductive noauto_scope {A} (P_noauto : A -> Prop) : scope A -> Prop :=
  | NAscope : forall locs blks,
      P_noauto blks ->
      noauto_scope P_noauto (Scope locs blks).

  Inductive noauto_branch {A} (P_noauto : A -> Prop) : branch A -> Prop :=
  | NAbranch : forall caus blks,
      P_noauto blks ->
      noauto_branch P_noauto (Branch caus blks).

  Inductive noauto_block : block -> Prop :=
  | NAeq : forall eq, noauto_block (Beq eq)
  | NAlast : forall x e, noauto_block (Blast x e)
  | NAreset : forall blks er,
      Forall noauto_block blks ->
      noauto_block (Breset blks er)
  | NAswitch : forall ec branches,
      Forall (fun blks => noauto_branch (Forall noauto_block) (snd blks)) branches ->
      noauto_block (Bswitch ec branches)
  | NAlocal : forall s,
      noauto_scope (Forall noauto_block) s ->
      noauto_block (Blocal s).

  Inductive noauto : list decl -> block -> Prop :=
  | NAnode : forall out blk,
      noauto_block blk ->
      (exists xs, VarsDefinedComp blk xs /\ Permutation xs (map fst out)) ->
      noauto out blk.

  (** *** After completion *)

  Inductive complete : list decl -> block -> Prop :=
  | Compnode : forall out blk xs,
      VarsDefinedComp blk xs ->
      Permutation xs (map fst out) ->
      complete out blk.

  (** ** Inclusion of these properties *)

  Fact noswitch_noauto : forall blk,
      noswitch_block blk ->
      noauto_block blk.
  Proof.
    induction blk using block_ind2; intros * Hns;
      inv Hns; constructor; simpl_Forall; eauto.
    constructor; auto. simpl_Forall; eauto.
  Qed.

  Fact nolocal_noswitch : forall blk,
      nolocal_block blk ->
      noswitch_block blk.
  Proof.
    induction blk using block_ind2; intros * Hns;
      inv Hns; constructor; simpl_Forall; eauto.
  Qed.

  Lemma unnested_nolocal : forall blk,
      unnested_block blk ->
      nolocal_block blk.
  Proof.
    induction 1; constructor; auto.
  Qed.

  Fact constant_normalized_lexp : forall e,
      normalized_constant e ->
      normalized_lexp e.
  Proof.
    induction 1; auto with norm.
  Qed.

  Fact unnested_eq_nil lasts : forall eq,
      unnested_equation lasts eq ->
      unnested_equation [] eq.
  Proof.
    induction 1; eauto using constant_normalized_lexp with norm.
    constructor; auto. simpl_Forall. intros [].
  Qed.

  Fact normalized_eq_unnested_eq outs lasts : forall eq,
      normalized_equation outs lasts eq ->
      unnested_equation lasts eq.
  Proof.
    induction 1; eauto using constant_normalized_lexp with norm.
  Qed.

  Lemma normlast_unnested lasts : forall blk,
      normlast_block lasts blk ->
      unnested_block blk.
  Proof.
    induction 1; constructor; eauto using unnested_eq_nil, constant_normalized_lexp.
  Qed.

  Lemma normalized_normlast outs lasts : forall blk,
      normalized_block outs lasts blk ->
      normlast_block lasts blk.
  Proof.
    induction 1; constructor; eauto using normalized_eq_unnested_eq.
  Qed.

  Section normal_args.
    (** ** Normalized arguments *)

    Fixpoint noops_exp (ck: clock) (e : exp) : Prop :=
      match ck with
      | Cbase => True
      | Con ck' _ _ =>
          match e with
          | Econst _ | Eenum _ _ | Evar _ _ => True
          | Ewhen [e'] _ _ _ => noops_exp ck' e'
          | _ => False
          end
      end.

    Context {PSyn : list decl -> block -> Prop} {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Inductive normal_args_eq : equation -> Prop :=
    | normal_args_eq_Eapp : forall xs f n es er lann,
        find_node f G = Some n ->
        Forall2 noops_exp (map (fun '(_, (_, ck, _)) => ck) n.(n_in)) es ->
        normal_args_eq (xs, [Eapp f es er lann])
    | normal_args_eq_Efby : forall x e0 e ann,
        normal_args_eq ([x], [Efby [e0] [e] [ann]])
    | normal_args_eq_Earrow : forall x e0 e ann,
        normal_args_eq ([x], [Earrow [e0] [e] [ann]])
    | normal_args_eq_Eextcall: forall x f es ann,
        normal_args_eq ([x], [Eextcall f es ann])
    | normal_args_eq_cexp : forall x e,
        normalized_cexp e ->
        normal_args_eq ([x], [e]).

    Inductive normal_args_blk : block -> Prop :=
    | normal_args_Beq : forall eq,
        normal_args_eq eq ->
        normal_args_blk (Beq eq)
    | normal_args_Blast : forall x e,
        normal_args_blk (Blast x e)
    | normal_args_Breset : forall blks e,
        Forall normal_args_blk blks ->
        normal_args_blk (Breset blks e)
    | normal_args_Blocal : forall locs blks,
        Forall normal_args_blk blks ->
        normal_args_blk (Blocal (Scope locs blks)).

    Definition normal_args_node (n: @node PSyn prefs) : Prop :=
      normal_args_blk n.(n_block).

  End normal_args.

  Definition normal_args {PSyn prefs} (G: @global PSyn prefs) :=
    Forall' (fun ns => normal_args_node (Global G.(types) G.(externs) ns)) G.(nodes).

  Lemma iface_eq_normal_args_eq {PSyn1 PSyn2 prefs1 prefs2} : forall (G: @global PSyn1 prefs1) (G': @global PSyn2 prefs2) eq,
      global_iface_eq G G' ->
      normal_args_eq G eq ->
      normal_args_eq G' eq.
  Proof.
    intros * Heq Hunt.
    inv Hunt; try constructor; eauto.
    destruct Heq as (_&_&Heq).
    specialize (Heq f).
    rewrite H in Heq. inv Heq. destruct H3 as (_&_&?&_).
    econstructor; eauto.
    erewrite map_ext, <-map_map, <-H1. simpl_Forall; eauto.
    instantiate (1:=fun '(_, (_, ck)) => ck); eauto. intros; destruct_conjs; eauto.
  Qed.

  Lemma iface_eq_normal_args_blk {PSyn1 PSyn2 prefs1 prefs2} : forall (G: @global PSyn1 prefs1) (G': @global PSyn2 prefs2) d,
      global_iface_eq G G' ->
      normal_args_blk G d ->
      normal_args_blk G' d.
  Proof.
    induction d using block_ind2; intros * Heq Hunt; inv Hunt; constructor.
    - eapply iface_eq_normal_args_eq; eauto.
    - simpl_Forall; eauto.
    - simpl_Forall; eauto.
  Qed.

  (** ** Inversion tactics *)

  Ltac inv_exp :=
    match goal with
    | H:wl_exp _ _ |- _ => inv H
    | H:wx_exp _ _ |- _ => inv H
    end.

  Ltac inv_scope :=
    match goal with
    | H:Is_defined_in_scope _ _ _ |- _ => inv H
    | H:VarsDefinedScope _ _ _ |- _ => inv H
    | H:VarsDefinedCompScope _ _ _ |- _ => inv H
    | H:LastsDefinedScope _ _ _ |- _ => inv H
    | H:NoDupScope _ _ _ |- _ => inv H
    | H:GoodLocalsScope _ _ _ |- _ => inv H
    | H:wl_scope _ _ _ |- _ => inv H
    | H:wx_scope _ _ _ |- _ => inv H
    | H:noauto_scope _ _ |- _ => inv H
    end;
    destruct_conjs; subst.

  Ltac inv_branch :=
    match goal with
    | H:Is_defined_in_branch _ _ |- _ => inv H
    | H:VarsDefinedBranch _ _ _ |- _ => inv H
    | H:VarsDefinedCompBranch _ _ _ |- _ => inv H
    | H:LastsDefinedBranch _ _ |- _ => inv H
    | H:NoDupBranch _ _ |- _ => inv H
    | H:GoodLocalsBranch _ _ |- _ => inv H
    | H:wl_branch _ _ |- _ => inv H
    | H:wx_branch _ _ |- _ => inv H
    | H:noauto_branch _ _ |- _ => inv H
    end;
    destruct_conjs; subst.

  Ltac inv_block :=
    match goal with
    | H:Is_defined_in _ _ |- _ => inv H
    | H:VarsDefined _ _ |- _ => inv H
    | H:VarsDefinedComp _ _ |- _ => inv H
    | H:NoDupLocals _ _ |- _ => inv H
    | H:GoodLocals _ _ |- _ => inv H
    | H:wl_block _ _ |- _ => inv H
    | H:wx_block _ _ |- _ => inv H
    | H:nolocal_block _ |- _ => inv H
    | H:nolocal_top_block _ |- _ => inv H
    | H:noswitch_block _ |- _ => inv H
    | H:noauto_block _ |- _ => inv H
    end.

  (** ** Additional properties *)

  Fact NoDupScope_incl {A} (P_nd: _ -> A -> Prop) : forall locs blks xs xs',
      (forall xs xs', incl xs xs' -> P_nd xs' blks -> P_nd xs blks) ->
      incl xs xs' ->
      NoDupScope P_nd xs' (Scope locs blks) ->
      NoDupScope P_nd xs (Scope locs blks).
  Proof.
    intros * Hp Hincl Hnd.
    inv Hnd; constructor; eauto using incl_appl'.
    intros * Hin1 Hin2. eapply H4; eauto.
  Qed.

  Lemma NoDupLocals_incl : forall blk xs xs',
      incl xs xs' ->
      NoDupLocals xs' blk ->
      NoDupLocals xs blk.
  Proof.
    induction blk using block_ind2; intros * Hincl Hnd; inv_block.
    - (* eq *) constructor.
    - (* last *) constructor.
    - (* reset *)
      constructor. simpl_Forall; eauto.
    - (* switch *)
      constructor. simpl_Forall; eauto.
      inv_branch. constructor; auto.
      simpl_Forall; eauto.
    - (* automaton *)
      constructor. simpl_Forall; eauto.
      inv_branch. constructor; auto.
      destruct_conjs. destruct s. eapply NoDupScope_incl; eauto.
      intros. simpl_Forall; eauto.
    - (* local *)
      constructor; auto.
      eapply NoDupScope_incl; eauto.
      intros. simpl_Forall; eauto.
  Qed.

  Corollary node_NoDupLocals {PSyn prefs} : forall (n : @node PSyn prefs),
      NoDupLocals (map fst (senv_of_ins (n_in n) ++ senv_of_decls (n_out n))) (n_block n).
  Proof.
    intros *.
    rewrite map_app, map_fst_senv_of_ins, map_fst_senv_of_decls.
    apply n_nodup.
  Qed.

  Add Parametric Morphism : NoDupLocals
      with signature @Permutation _ ==> eq ==> Basics.impl
        as NoDupLocals_Permutation.
  Proof.
    intros * Hperm ? Hnd.
    eapply NoDupLocals_incl; eauto.
    rewrite Hperm. reflexivity.
  Qed.

  Fact NoDupScope_incl' {A} (P_nd : list ident -> A -> Prop) P_good npref prefs : forall locs blks xs ys,
      ~PS.In npref prefs ->
      GoodLocalsScope P_good prefs (Scope locs blks) ->
      (forall x, In x ys -> In x xs \/ exists id hint, x = gensym npref hint id) ->
      NoDupScope P_nd xs (Scope locs blks) ->
      (forall xs ys,
          P_good blks ->
          (forall x, In x ys -> In x xs \/ exists id hint, x = gensym npref hint id) ->
          P_nd xs blks ->
          P_nd ys blks) ->
      NoDupScope P_nd ys (Scope locs blks).
  Proof.
    intros * Hnin Hgood Hin Hnd Hp; repeat inv_scope.
    constructor; auto.
    - eapply Hp in H1; eauto.
      intros. rewrite in_app_iff in *. destruct H; eauto.
      edestruct Hin; eauto.
    - intros ? Hinm. specialize (H4 _ Hinm) as Hx.
      contradict Hx. apply Hin in Hx as [?|(?&?&Hpref)]; auto; subst. exfalso.
      eapply Forall_forall in H2. 2:(rewrite <- fst_InMembers; eauto).
      inv H2.
      + apply gensym_not_atom in H; auto.
      + destruct H as (?&Hpsin&?&?&Heq).
        eapply gensym_injective in Heq as (?&?); subst. contradiction.
  Qed.

  Lemma NoDupLocals_incl' prefs npref : forall blk xs ys,
      ~PS.In npref prefs ->
      GoodLocals prefs blk ->
      (forall x, In x ys -> In x xs \/ exists id hint, x = gensym npref hint id) ->
      NoDupLocals xs blk ->
      NoDupLocals ys blk.
  Proof.
    induction blk using block_ind2;
      intros * Hnin Hgood Hin Hnd; repeat inv_block.
    - (* equation *) constructor.
    - (* last *) constructor.
    - (* reset *)
      constructor. simpl_Forall; eauto.
    - (* switch *)
      constructor. simpl_Forall; eauto.
      repeat inv_branch. constructor; auto.
      simpl_Forall; eauto.
    - (* automaton *)
      constructor. simpl_Forall; eauto.
      repeat inv_branch. constructor; auto.
      destruct s. eapply NoDupScope_incl'; eauto.
      intros; simpl_Forall; eauto.
    - (* local *)
      constructor; auto.
      eapply NoDupScope_incl'; eauto.
      intros; simpl_Forall; eauto.
  Qed.

  Lemma node_NoDupMembers {PSyn prefs} : forall (n : @node PSyn prefs),
      NoDupMembers (senv_of_ins (n_in n) ++ senv_of_decls (n_out n)).
  Proof.
    intros n.
    rewrite fst_NoDupMembers, map_app, map_fst_senv_of_ins, map_fst_senv_of_decls.
    apply n_nodup.
  Qed.

  Global Instance Permutation_idents_Proper:
    Proper (@Permutation (ident * (type * Cks.clock * ident))
              ==> @Permutation ident) idents.
  Proof.
    intros xs ys Hperm.
    induction Hperm; simpl; eauto using Permutation.
  Qed.

  Lemma node_NoDup_in {PSyn prefs} : forall (n : @node PSyn prefs),
      NoDup (idents (n_in n)).
  Proof.
    intros n.
    eapply NoDup_app_l.
    apply n_nodup.
  Qed.

  Lemma NoDupMembers_n_in {PSyn prefs} : forall (node: @node PSyn prefs),
      NoDupMembers node.(n_in).
  Proof.
    intros node.
    pose proof (node.(n_nodup)) as (Hnd & Hndl); clear Hndl.
    now apply NoDup_app_l, fst_NoDupMembers in Hnd.
  Qed.

  Lemma node_NoDup_out {PSyn prefs} : forall (n : @node PSyn prefs),
      NoDup (map fst (n_out n)).
  Proof.
    intros n.
    eapply NoDup_app_r.
    apply n_nodup.
  Qed.

  Lemma not_in_out {PSyn prefs} :
    forall (n : @node PSyn prefs) x,
      In x (List.map fst (n_in n)) ->
      In x (List.map fst (n_out n)) ->
      False.
  Proof.
    intros * Hin Hout.
    pose proof (n_nodup n) as [ND].
    eapply NoDup_app_In; eauto.
  Qed.

  Lemma AtomOrGensym_add : forall pref prefs x,
      AtomOrGensym prefs x ->
      AtomOrGensym (PS.add pref prefs) x.
  Proof.
    intros * [?|(pref'&?&?)]; [left|right]; subst; auto.
    exists pref'. auto using PSF.add_2.
  Qed.

  Lemma Forall_AtomOrGensym_add : forall pref prefs xs,
      Forall (AtomOrGensym prefs) xs ->
      Forall (AtomOrGensym (PS.add pref prefs)) xs.
  Proof.
    intros * Hat.
    simpl_Forall; eauto using AtomOrGensym_add.
  Qed.

  Lemma GoodLocals_add : forall p prefs blk,
      GoodLocals prefs blk ->
      GoodLocals (PS.add p prefs) blk.
  Proof.
    induction blk using block_ind2; intros * Hgood; inv_block.
    - (* equation *) constructor; eauto.
    - (* last *) constructor; auto.
    - (* reset *)
      constructor; eauto.
      simpl_Forall; eauto.
    - (* switch *)
      constructor; eauto.
      simpl_Forall; eauto.
      inv H1; econstructor; eauto using Forall_AtomOrGensym_add.
      simpl_Forall; eauto.
    - (* automaton *)
      constructor; eauto.
      simpl_Forall; eauto.
      inv_branch. inv_scope.
      repeat econstructor; eauto using Forall_AtomOrGensym_add.
      simpl_Forall; eauto.
    - (* locals *)
      constructor.
      inv_scope; econstructor; eauto using Forall_AtomOrGensym_add.
      simpl_Forall; eauto.
  Qed.

  (** Correspondance between VarsDefinedComp and Is_defined_in *)

  Lemma VarsDefinedCompScope_Is_defined {A} P_nd P_vd (P_def: _ -> Prop) : forall locs (blks: A) xs x,
      VarsDefinedCompScope P_vd (Scope locs blks) xs ->
      NoDupScope P_nd xs (Scope locs blks) ->
      In x xs ->
      (forall xs,
          P_vd blks xs ->
          P_nd xs blks ->
          In x xs ->
          P_def blks) ->
      Is_defined_in_scope P_def (Var x) (Scope locs blks).
  Proof.
    intros * Hnd Hvars Hin Hind; inv Hnd; inv Hvars.
    econstructor; eauto using in_or_app.
    intros * Hnin. eapply H5; eauto.
  Qed.

  Lemma VarsDefinedCompBranch_Is_defined {A} P_nd P_vd (P_def: _ -> Prop) : forall caus (blks: A) xs,
      VarsDefinedCompBranch P_vd (Branch caus blks) xs ->
      NoDupBranch P_nd (Branch caus blks) ->
      (P_vd blks xs ->
       P_nd blks ->
       P_def blks) ->
      Is_defined_in_branch P_def (Branch caus blks).
  Proof.
    intros * Hnd Hvars Hind; inv Hnd; inv Hvars.
    econstructor; eauto.
  Qed.

  Lemma VarsDefinedComp_Is_defined : forall blk xs x,
      VarsDefinedComp blk xs ->
      NoDupLocals xs blk ->
      In x xs ->
      Is_defined_in (Var x) blk.
  Proof.
    induction blk using block_ind2; intros * Hvars Hnd Hin; inv Hnd; inv Hvars.
    - (* equation *)
      destruct eq; simpl in *. constructor; auto.
    - (* last *) inv Hin.
    - (* reset *)
      constructor.
      eapply in_concat in Hin as (?&Hin1&Hin2). inv_VarsDefined.
      solve_Exists. simpl_Forall.
      eapply H; eauto.
      eapply NoDupLocals_incl; [|eauto]; auto using incl_concat.
    - (* switch *)
      constructor.
      inv H; try congruence. inv H2. inv H5. clear H1 H7 H8.
      left. destruct x0 as (?&[]).
      eapply VarsDefinedCompBranch_Is_defined; eauto.
      intros; simpl in *. destruct H as (?&Hvars&Hperm).
      rewrite <-Hperm in Hin. eapply in_concat in Hin as (?&Hin1&Hin2). inv_VarsDefined.
      solve_Exists. simpl_Forall.
      eapply H0; eauto.
      eapply NoDupLocals_incl; [|eauto]. rewrite <-Hperm; auto using incl_concat.
    - (* automaton *)
      constructor.
      inv H; try congruence. inv H2. destruct_conjs. inv H7. clear H1 H5 H8.
      left. destruct b. eapply VarsDefinedCompBranch_Is_defined; eauto.
      intros; destruct_conjs; destruct s. eapply VarsDefinedCompScope_Is_defined; eauto.
      intros; simpl in *. destruct H2 as (?&Hvars&Hperm).
      rewrite <-Hperm in H7. eapply in_concat in H7 as (?&Hin1&Hin2). inv_VarsDefined.
      solve_Exists. simpl_Forall.
      eapply H0; eauto.
      eapply NoDupLocals_incl; [|eauto]. rewrite <-Hperm; auto using incl_concat.
    - (* local *)
      constructor.
      eapply VarsDefinedCompScope_Is_defined; eauto.
      intros; simpl in *. destruct H0 as (?&Hvars&Hperm).
      rewrite <-Hperm in H4. eapply in_concat in H4 as (?&Hin1&Hin2). inv_VarsDefined.
      solve_Exists. simpl_Forall.
      eapply H; eauto.
      eapply NoDupLocals_incl; [|eauto]. rewrite <-Hperm; auto using incl_concat.
  Qed.

  Corollary Forall_VarsDefinedComp_Is_defined : forall blks xs x,
      Forall2 (VarsDefinedComp) blks xs ->
      Forall (NoDupLocals (concat xs)) blks ->
      In x (concat xs) ->
      Exists (Is_defined_in (Var x)) blks.
  Proof.
    intros * Hnd Hvars Hin.
    apply in_concat in Hin as (?&Hin1&Hin2). inv_VarsDefined.
    simpl_Forall. solve_Exists.
    eapply VarsDefinedComp_Is_defined in Hdef; eauto.
    eapply NoDupLocals_incl; [|eauto]. apply incl_concat; auto.
  Qed.

  (** Correspondance between VarsDefined and Is_defined_in *)

  Lemma VarsDefinedScope_Is_defined {A} P_nd P_vd (P_def: _ -> Prop) : forall locs (blks: A) xs x,
      VarsDefinedScope P_vd (Scope locs blks) xs ->
      NoDupScope P_nd (map fst xs) (Scope locs blks) ->
      InMembers x xs ->
      (forall xs,
          P_vd blks xs ->
          P_nd (map fst xs) blks ->
          InMembers x xs ->
          P_def blks) ->
      Is_defined_in_scope P_def (Var x) (Scope locs blks).
  Proof.
    intros * Hnd Hvars Hin Hind; inv Hnd; inv Hvars.
    econstructor; eauto.
    - take (P_vd _ _) and eapply Hind in it; eauto.
      + now rewrite map_app, map_fst_senv_of_decls.
      + apply InMembers_app; auto.
    - intros * Hnin. eapply H5; eauto. now apply fst_InMembers.
  Qed.

  Lemma VarsDefined_Is_defined : forall blk xs x,
      VarsDefined blk xs ->
      NoDupLocals (map fst xs) blk ->
      InMembers x xs ->
      Is_defined_in (Var x) blk.
  Proof.
    induction blk using block_ind2; intros * Hvars Nd Hin; inv Hvars; inv Nd.
    - (* equation *)
      destruct eq; simpl in *. constructor; subst.
      now apply fst_InMembers.
    - (* last *) inv Hin.
    - (* reset *)
      constructor.
      eapply InMembers_concat in Hin as (?&Hin1&Hin2). inv_VarsDefined.
      solve_Exists. simpl_Forall.
      eapply H; eauto using NoDupLocals_incl, incl_map, incl_concat.
    - (* switch *)
      simpl_In. simpl_Forall. auto.
    - (* automaton *)
      simpl_In. simpl_Forall. auto.
    - (* local *)
      constructor.
      eapply VarsDefinedScope_Is_defined; eauto.
      intros; simpl in *. destruct H0 as (?&Hvars&Hperm).
      rewrite <-Hperm in H4. eapply InMembers_concat in H4 as (?&Hin1&Hin2). inv_VarsDefined.
      solve_Exists. simpl_Forall.
      eapply H; eauto.
      eapply NoDupLocals_incl; [|eauto]. rewrite <-Hperm; auto using incl_map, incl_concat.
  Qed.

  Corollary Forall_VarsDefined_Is_defined : forall blks xs x,
      Forall2 (VarsDefined) blks xs ->
      Forall (NoDupLocals (map fst (concat xs))) blks ->
      InMembers x (concat xs) ->
      Exists (Is_defined_in (Var x)) blks.
  Proof.
    intros * Hnd Hvars Hin.
    apply InMembers_concat in Hin as (?&Hin1&Hin2). inv_VarsDefined.
    simpl_Forall. solve_Exists.
    eapply VarsDefined_Is_defined in Hdef; eauto.
    eapply NoDupLocals_incl; [|eauto]. eauto using incl_map, incl_concat.
  Qed.

  (** Weakening VarsDefinedComp to VarsDefined *)

  Fact VarsDefinedCompScope_VarsDefinedScope {A} P_nd P_blk1 (P_blk2 : _ -> _ -> Prop) : forall locs (blk: A) Γ,
      NoDupScope P_nd (map fst Γ) (Scope locs blk) ->
      VarsDefinedCompScope P_blk1 (Scope locs blk) (map fst Γ) ->
      (forall Γ, P_nd (map fst Γ) blk -> P_blk1 blk (map fst Γ) -> P_blk2 blk Γ) ->
      VarsDefinedScope P_blk2 (Scope locs blk) Γ.
  Proof.
    intros * Ind ND VD. repeat inv_scope.
    take (P_blk1 _ _) and rewrite <-map_fst_senv_of_decls, <-map_app in it.
    take (P_nd _ _) and rewrite <-map_fst_senv_of_decls, <-map_app in it.
    econstructor; eauto.
  Qed.

  Fact VarsDefinedCompBranch_VarsDefinedBranch {A} P_nd P_blk1 (P_blk2 : _ -> _ -> Prop) : forall locs (blk: A) Γ,
      NoDupBranch P_nd (Branch locs blk) ->
      VarsDefinedCompBranch P_blk1 (Branch locs blk) (map fst Γ) ->
      (P_nd blk -> P_blk1 blk (map fst Γ) -> P_blk2 blk Γ) ->
      VarsDefinedBranch P_blk2 (Branch locs blk) Γ.
  Proof.
    intros * ND VD Ind. repeat inv_branch.
    eapply LVDbranch with (ysl:=[]); eauto.
    - rewrite app_nil_r; eauto.
    - intros * V. inv V. simpl_In. now exfalso.
  Qed.

  Lemma VarsDefinedComp_VarsDefined : forall blk Γ,
      NoDupLocals (map fst Γ) blk ->
      VarsDefinedComp blk (map fst Γ) ->
      VarsDefined blk Γ.
  Proof.
    induction blk using block_ind2; intros * ND VD;
      assert (ND':=ND); inv ND';
      assert (VD':=VD); inv VD'; inv_VarsDefined.
    - (* equation *)
      now constructor.
    - (* last *)
      symmetry in H. apply map_eq_nil in H. subst. constructor.
    - (* reset *)
      apply map_eq_concat in H4 as (?&?&?); subst.
      constructor. simpl_Forall; eauto using NoDupLocals_incl, incl_map, incl_concat.
    - (* switch *)
      constructor; auto.
      + simpl_Forall. destruct b.
        eapply VarsDefinedCompBranch_VarsDefinedBranch; eauto.
        intros * ND1 (?&F&Perm).
        apply Permutation_map_inv in Perm as (?&Eq&Perm).
        apply map_eq_concat in Eq as (?&?&?); subst.
        do 2 esplit; [|symmetry; eauto]. simpl_Forall; eauto.
        eapply H; eauto. eapply NoDupLocals_incl; [|eauto]. rewrite Perm; eauto using incl_map, incl_concat.
      + simpl_Forall.
        eapply VarsDefinedComp_Is_defined; eauto. solve_In.
    - (* state machine *)
      constructor; auto.
      simpl_Forall. destruct b as [?(?&[?(?&?)])].
      + eapply VarsDefinedCompBranch_VarsDefinedBranch; eauto. intros; simpl in *.
        eapply VarsDefinedCompScope_VarsDefinedScope; eauto.
        intros * ND' (?&F&Perm).
        apply Permutation_map_inv in Perm as (?&Eq&Perm).
        apply map_eq_concat in Eq as (?&?&?); subst.
        do 2 esplit; [|symmetry; eauto]. simpl_Forall; eauto.
        eapply H; eauto. eapply NoDupLocals_incl; [|eauto]. rewrite Perm; eauto using incl_map, incl_concat.
      + simpl_Forall.
        eapply VarsDefinedComp_Is_defined; eauto. solve_In.
    - (* scope *)
      constructor. eapply VarsDefinedCompScope_VarsDefinedScope; eauto.
      intros * Nd' (?&F&Perm).
      apply Permutation_map_inv in Perm as (?&Eq&Perm).
      apply map_eq_concat in Eq as (?&?&?); subst.
      do 2 esplit; [|symmetry; eauto]. simpl_Forall; eauto.
      eapply H; eauto. eapply NoDupLocals_incl; [|eauto]. rewrite Perm; eauto using incl_map, incl_concat.
  Qed.

  Lemma noswitch_VarsDefinedComp_VarsDefined : forall blk xs,
      noswitch_block blk ->
      VarsDefinedComp blk (map fst xs) ->
      VarsDefined blk xs.
  Proof.
    induction blk using block_ind2; intros * NS VD; inv NS; inv VD.
    - (* equation *)
      constructor. auto.
    - (* last *)
      symmetry in H. apply map_eq_nil in H; subst. constructor.
    - (* reset *)
      apply map_eq_concat in H4 as (?&?&?); subst.
      constructor. simpl_Forall; eauto.
    - (* scope *)
      inv_scope. do 2 constructor.
      take (Permutation _ _) and rewrite <-map_fst_senv_of_decls, <-map_app in it.
      apply Permutation_map_inv in it as (?&Eq&Perm).
      apply map_eq_concat in Eq as (?&?&?); subst.
      do 2 esplit; [|symmetry; eauto].
      simpl_Forall. eauto.
  Qed.

  (** Correspondance between Is_defined and VarsDefined *)

  Lemma VarsDefinedScope_Is_defined' {A} P_nd P_vd (P_def: _ -> Prop) : forall locs (blks: A) xs x,
      VarsDefinedScope P_vd (Scope locs blks) xs ->
      NoDupScope P_nd (map fst xs) (Scope locs blks) ->
      Is_defined_in_scope P_def (Var x) (Scope locs blks) ->
      (forall xs,
          P_vd blks xs ->
          P_nd (map fst xs) blks ->
          P_def blks ->
          InMembers x xs) ->
      InMembers x xs.
  Proof.
    intros * Hnd Hvars Hdef Hind; inv Hnd; inv Hvars; inv Hdef.
    eapply Hind, InMembers_app in H2 as [Hin|Hin]. 3,4:eauto. 1,2:eauto.
    - apply InMembers_senv_of_decls in Hin. simpl in *. congruence.
    - now rewrite map_app, map_fst_senv_of_decls.
  Qed.

  Lemma VarsDefinedBranch_Is_defined' {A} P_nd P_vd (P_def: _ -> Prop) : forall locs (blks: A) xs x,
      VarsDefinedBranch P_vd (Branch locs blks) xs ->
      NoDupBranch P_nd (Branch locs blks) ->
      Is_defined_in_branch P_def (Branch locs blks) ->
      (forall xs',
          incl xs' xs ->
          P_vd blks xs' ->
          P_nd blks ->
          P_def blks ->
          InMembers x xs') ->
      InMembers x xs.
  Proof.
    intros * Hnd Hvars Hdef Hind; inv Hnd; inv Hvars; inv Hdef.
    eapply Hind in H0. 3-4:eauto.
    - take (Permutation _ _) and rewrite <-it, InMembers_app; auto.
    - take (Permutation _ _) and rewrite <-it. solve_incl_app.
  Qed.

  Lemma VarsDefined_Is_defined' : forall blk xs x,
      VarsDefined blk xs ->
      NoDupLocals (map fst xs) blk ->
      Is_defined_in (Var x) blk ->
      InMembers x xs.
  Proof.
    induction blk using block_ind2; intros * Hnd Hvars Hin; repeat inv_block.
    - (* equation *)
      now rewrite fst_InMembers, H0.
    - (* reset *)
      simpl_Exists. inv_VarsDefined. simpl_Forall.
      eapply InMembers_concat. repeat esplit; eauto.
      eapply H; eauto.
      eapply NoDupLocals_incl; [|eauto]; auto using incl_map, incl_concat.
    - (* switch *)
      rename H2 into Hdef. simpl_Exists. simpl_Forall.
      destruct b. eapply VarsDefinedBranch_Is_defined'; eauto.
      intros. simpl_Exists. inv_VarsDefined. simpl_Forall.
      take (Permutation _ _) and rewrite <-it. eapply InMembers_concat. repeat esplit; eauto.
      eapply H; eauto.
      eapply NoDupLocals_incl; [|eauto]. etransitivity; eauto using incl_map, incl_concat.
      take (Permutation _ _) and rewrite it; eauto using incl_map.
    - (* automaton *)
      rename H2 into Hdef. simpl_Exists. simpl_Forall.
      destruct b. eapply VarsDefinedBranch_Is_defined'; eauto. intros; destruct_conjs.
      destruct s. eapply VarsDefinedScope_Is_defined'; eauto.
      1:{ eapply NoDupScope_incl; eauto using incl_map.
          intros; simpl in *; simpl_Forall; eauto using NoDupLocals_incl. }
      intros; simpl in *. simpl_Exists. inv_VarsDefined. simpl_Forall.
      take (Permutation _ _) and rewrite <-it. eapply InMembers_concat. repeat esplit; eauto.
      eapply H; eauto.
      eapply NoDupLocals_incl; [|eauto].
      take (Permutation _ _) and rewrite <-it; eauto using incl_map, incl_concat.
    - (* local *)
      eapply VarsDefinedScope_Is_defined'; eauto.
      intros; simpl in *. simpl_Exists. inv_VarsDefined. simpl_Forall.
      take (Permutation _ _) and rewrite <-it. eapply InMembers_concat. repeat esplit; eauto.
      eapply H; eauto.
      eapply NoDupLocals_incl; [|eauto].
      take (Permutation _ _) and rewrite <-it; auto using incl_map, incl_concat.
  Qed.

  Corollary VarsDefinedComp_Is_defined' : forall blk xs x,
      VarsDefinedComp blk xs ->
      NoDupLocals xs blk ->
      Is_defined_in (Var x) blk ->
      In x xs.
  Proof.
    intros * VD ND Def.
    replace xs with (map fst (map (fun x => (x, Build_annotation OpAux.bool_velus_type Cbase xH None)) xs)) in *.
    2:{ now rewrite map_map, map_id. }
    eapply VarsDefinedComp_VarsDefined, VarsDefined_Is_defined', fst_InMembers in VD; eauto.
  Qed.

  Corollary VarsDefined_spec : forall blk xs,
      VarsDefined blk xs ->
      NoDupLocals (map fst xs) blk ->
      forall x, InMembers x xs <-> Is_defined_in (Var x) blk.
  Proof.
    intros.
    split; intros; eauto using VarsDefined_Is_defined, VarsDefined_Is_defined'.
  Qed.

  Corollary Exists_VarsDefined_spec : forall blks xs,
      Forall2 VarsDefined blks xs ->
      Forall (NoDupLocals (map fst (concat xs))) blks ->
      forall x, InMembers x (concat xs) <-> Exists (Is_defined_in (Var x)) blks.
  Proof.
    intros * VD ND ?.
    rewrite InMembers_concat, Exists_exists.
    split; intros; destruct_conjs; inv_VarsDefined; simpl_Forall;
      eauto 7 using VarsDefined_Is_defined, VarsDefined_Is_defined', NoDupLocals_incl, incl_map, incl_concat.
  Qed.

  (** Correspondance between LastsDefined and Is_defined_in *)

  Fact lasts_of_decls_incl : forall xs,
      incl (lasts_of_decls xs) (map fst xs).
  Proof.
    intros ?? In.
    unfold lasts_of_decls in *. solve_In.
  Qed.
  Global Hint Resolve lasts_of_decls : lsyntax.

  Lemma LastsDefinedScope_Is_defined {A} P_nd P_vd (P_def: _ -> Prop) : forall locs (blks: A) xs x,
      LastsDefinedScope P_vd (Scope locs blks) xs ->
      NoDupScope P_nd xs (Scope locs blks) ->
      In x xs ->
      (forall xs xs', incl xs xs' -> P_nd xs' blks -> P_nd xs blks) ->
      (forall xs,
          P_vd blks xs ->
          P_nd xs blks ->
          In x xs ->
          P_def blks) ->
      Is_defined_in_scope P_def (Last x) (Scope locs blks).
  Proof.
    intros * Hnd Hvars Hin Incl Hind; inv Hnd; inv Hvars.
    econstructor; eauto.
    - take (P_vd _ _) and eapply Hind in it; eauto using in_or_app.
      eapply Incl; eauto using incl_appr', lasts_of_decls_incl.
    - intros * Hnin. eapply H5; eauto.
  Qed.

  Lemma LastsDefined_Is_defined : forall blk xs x,
      LastsDefined blk xs ->
      NoDupLocals xs blk ->
      In x xs ->
      Is_defined_in (Last x) blk.
  Proof.
    induction blk using block_ind2; intros * Hvars Nd Hin; inv Hvars; inv Nd;
      try (now inv Hin).
    - (* last *)
      apply In_singleton in Hin; subst. econstructor.
    - (* reset *)
      constructor.
      eapply in_concat in Hin as (?&Hin1&Hin2). inv_VarsDefined.
      solve_Exists. simpl_Forall.
      eapply H; eauto using NoDupLocals_incl, incl_map, incl_concat.
    - (* local *)
      constructor.
      eapply LastsDefinedScope_Is_defined; eauto.
      + intros. simpl in *. simpl_Forall. eauto using NoDupLocals_incl.
      + intros; simpl in *. destruct H0 as (?&Hvars&Hperm).
        rewrite <-Hperm in H4. eapply in_concat in H4 as (?&Hin1&Hin2). inv_VarsDefined.
        solve_Exists. simpl_Forall.
        eapply H; eauto.
        eapply NoDupLocals_incl; [|eauto]. rewrite <-Hperm; auto using incl_map, incl_concat.
  Qed.

  Corollary Forall_LastsDefined_Is_defined : forall blks xs x,
      Forall2 (LastsDefined) blks xs ->
      Forall (NoDupLocals (concat xs)) blks ->
      In x (concat xs) ->
      Exists (Is_defined_in (Last x)) blks.
  Proof.
    intros * Hnd Hvars Hin.
    apply in_concat in Hin as (?&Hin1&Hin2). inv_VarsDefined.
    simpl_Forall. solve_Exists.
    eapply LastsDefined_Is_defined in Hdef; eauto.
    eapply NoDupLocals_incl; [|eauto]. eauto using incl_map, incl_concat.
  Qed.

  (** Correspondance between Is_defined_in and LastsDefined *)

  Lemma LastsDefinedScope_Is_defined' {A} P_nd P_vd (P_def: _ -> Prop) : forall locs (blks: A) xs x,
      LastsDefinedScope P_vd (Scope locs blks) xs ->
      NoDupScope P_nd xs (Scope locs blks) ->
      Is_defined_in_scope P_def (Last x) (Scope locs blks) ->
      (forall xs xs', incl xs xs' -> P_nd xs' blks -> P_nd xs blks) ->
      (forall xs,
          P_vd blks xs ->
          P_nd xs blks ->
          P_def blks ->
          In x xs) ->
      In x xs.
  Proof.
    intros * Hnd Hvars Hdef Incl Hind; inv Hnd; inv Hvars; inv Hdef.
    eapply Hind, in_app_iff in H2 as [Hin|Hin]. 3,4:eauto. 1,2:eauto.
    - apply lasts_of_decls_incl, fst_InMembers in Hin. simpl in *. congruence.
    - eapply Incl; eauto using incl_appr', lasts_of_decls_incl.
  Qed.

  Lemma LastsDefined_Is_defined' : forall blk xs x,
      LastsDefined blk xs ->
      NoDupLocals xs blk ->
      Is_defined_in (Last x) blk ->
      In x xs.
  Proof.
    induction blk using block_ind2; intros * Hvars Hnd Hin; inv Hvars; inv Hnd; inv Hin;
      auto with datatypes.
    - (* reset *)
      simpl_Exists. inv_VarsDefined. simpl_Forall.
      eapply in_concat. repeat esplit; eauto.
      eapply H; eauto.
      eapply NoDupLocals_incl; [|eauto]; auto using incl_map, incl_concat.
    - (* local *)
      eapply LastsDefinedScope_Is_defined'; eauto.
      + intros; simpl in *. simpl_Forall; eauto using NoDupLocals_incl.
      + intros; simpl in *. simpl_Exists. inv_VarsDefined. simpl_Forall.
        take (Permutation _ _) and rewrite <-it. eapply in_concat. repeat esplit; eauto.
        eapply H; eauto.
        eapply NoDupLocals_incl; [|eauto].
        take (Permutation _ _) and rewrite <-it; auto using incl_map, incl_concat.
  Qed.

  Corollary LastsDefined_spec : forall blk xs,
      LastsDefined blk xs ->
      NoDupLocals xs blk ->
      forall x, In x xs <-> Is_defined_in (Last x) blk.
  Proof.
    intros.
    split; intros; eauto using LastsDefined_Is_defined, LastsDefined_Is_defined'.
  Qed.

  Corollary Exists_LastsDefined_spec : forall blks xs,
      Forall2 LastsDefined blks xs ->
      Forall (NoDupLocals (concat xs)) blks ->
      forall x, In x (concat xs) <-> Exists (Is_defined_in (Last x)) blks.
  Proof.
    intros * VD ND ?.
    rewrite in_concat, Exists_exists.
    split; intros; destruct_conjs; inv_VarsDefined; simpl_Forall;
      eauto 7 using LastsDefined_Is_defined, LastsDefined_Is_defined', NoDupLocals_incl, incl_map, incl_concat.
  Qed.

  (** Additional properties of Is_defined_in *)

  Lemma Is_defined_in_wx_In : forall blk env x,
      wx_block env blk ->
      Is_defined_in x blk ->
      InMembers (var_last_ident x) env.
  Proof.
    induction blk using block_ind2; intros * Hwx Hdef; inv Hwx; inv Hdef.
    - (* equation *)
      destruct H1; auto. simpl_Forall. inv H0; auto.
    - (* last *)
      inv H2. eauto using In_InMembers.
    - (* reset *)
      simpl_Exists; simpl_Forall; eauto.
    - (* switch *)
      simpl_Exists; simpl_Forall; eauto.
      repeat inv_branch. simpl_Exists; simpl_Forall; eauto.
      eapply H in H0; eauto.
    - (* automaton *)
      simpl_Exists; simpl_Forall; eauto.
      repeat inv_branch. repeat inv_scope. simpl_Exists. simpl_Forall.
      eapply H, InMembers_app in H3 as [|]. 3:eauto. 1,2:eauto.
      exfalso. apply H4, InMembers_senv_of_decls; auto.
    - (* local *)
      repeat inv_scope. simpl_Exists; simpl_Forall.
      eapply H, InMembers_app in H5 as [|]. 3:eauto. 1,2:eauto.
      exfalso. apply H6, InMembers_senv_of_decls; auto.
  Qed.

  Corollary Exists_Is_defined_in_wx_In : forall blks env x,
      Forall (wx_block env) blks ->
      Exists (Is_defined_in x) blks ->
      InMembers (var_last_ident x) env.
  Proof.
    intros * Hf Hex.
    simpl_Exists; simpl_Forall; eauto using Is_defined_in_wx_In.
  Qed.

  Lemma VarsDefinedComp_det : forall blk xs1 xs2,
      VarsDefinedComp blk xs1 ->
      VarsDefinedComp blk xs2 ->
      Permutation xs1 xs2.
  Proof.
    induction blk using block_ind2; intros * Hvd1 Hvd2;
      inv Hvd1; inv Hvd2; inv_VarsDefined.
    - (* equation *)
      reflexivity.
    - (* last *)
      reflexivity.
    - (* reset *)
      apply Permutation_concat.
      apply Forall2_swap_args in H3. eapply Forall2_trans_ex in H4; eauto.
      simpl_Forall; eauto.
    - (* switch *)
      inv H4; inv H6; try congruence. clear H1 H8.
      destruct x. inv H0. inv H7. inv_VarsDefined; simpl in *. subst. inv H8.
      rewrite <-Hperm, <-Hperm0.
      apply Permutation_concat.
      apply Forall2_swap_args in Hvars0. eapply Forall2_trans_ex in Hvars; eauto.
      simpl_Forall; eauto.
    - (* automaton *)
      inv H6; inv H8; try congruence. clear H1 H6.
      destruct_conjs. inv H0. inv H4. inv H1. inv H6. inv_VarsDefined; simpl in *. destruct_conjs; subst. inv H1.
      eapply Permutation_app_inv_r. rewrite <-Hperm, <-Hperm0.
      apply Permutation_concat.
      apply Forall2_swap_args in Hvars0. eapply Forall2_trans_ex in Hvars; eauto.
      simpl_Forall; eauto.
    - (* local *)
      inv H1. inv H2. destruct_conjs.
      eapply Permutation_app_inv_r. rewrite <-H2, <-H3.
      apply Permutation_concat.
      apply Forall2_swap_args in H1. eapply Forall2_trans_ex in H0; eauto.
      simpl_Forall; eauto.
  Qed.

  Lemma LastsDefined_det : forall blk xs1 xs2,
      LastsDefined blk xs1 ->
      LastsDefined blk xs2 ->
      Permutation xs1 xs2.
  Proof.
    induction blk using block_ind2; intros * Hvd1 Hvd2;
      inv Hvd1; inv Hvd2; try reflexivity.
    - (* reset *)
      apply Permutation_concat.
      apply Forall2_swap_args in H3. eapply Forall2_trans_ex in H4; eauto.
      simpl_Forall; eauto.
    - (* local *)
      inv H1. inv H2. destruct_conjs.
      eapply Permutation_app_inv_r. rewrite <-H2, <-H3.
      apply Permutation_concat.
      apply Forall2_swap_args in H1. eapply Forall2_trans_ex in H0; eauto.
      simpl_Forall; eauto.
  Qed.

  Fact VarsDefinedBranch_Perm1 : forall xs ys s,
      Permutation xs ys ->
      VarsDefinedBranch
        (fun blks ys => exists xs0, Forall2 VarsDefined blks xs0 /\ Permutation (concat xs0) ys) s xs ->
      VarsDefinedBranch
        (fun blks ys => exists xs0, Forall2 VarsDefined blks xs0 /\ Permutation (concat xs0) ys) s ys.
  Proof.
    intros * Hperm Hvd; inv Hvd; inv_VarsDefined.
    econstructor; eauto. all:intros; try rewrite <-Hperm in *; eauto.
  Qed.

  Fact VarsDefinedScope_Perm1 : forall xs ys (s: scope (_ * list transition)),
      Permutation xs ys ->
      VarsDefinedScope
        (fun blks ys => exists xs0, Forall2 VarsDefined (fst blks) xs0 /\ Permutation (concat xs0) ys) s xs ->
      VarsDefinedScope
        (fun blks ys => exists xs0, Forall2 VarsDefined (fst blks) xs0 /\ Permutation (concat xs0) ys) s ys.
  Proof.
    intros * Hperm Hvd; inv Hvd; inv_VarsDefined.
    econstructor. do 2 esplit; eauto.
    now rewrite <-Hperm.
  Qed.

  Fact VarsDefinedBranch_Perm2 : forall xs ys b,
      Permutation xs ys ->
      VarsDefinedBranch
        (fun (blks : list transition * scope (list block * list transition)) ys =>
           VarsDefinedScope (fun blks0 ys0 => exists xs0, Forall2 VarsDefined (fst blks0) xs0 /\ Permutation (concat xs0) ys0) (snd blks) ys) b xs ->
      VarsDefinedBranch
        (fun (blks : list transition * scope (list block * list transition)) ys =>
           VarsDefinedScope (fun blks0 ys0 => exists xs0, Forall2 VarsDefined (fst blks0) xs0 /\ Permutation (concat xs0) ys0) (snd blks) ys) b ys.
  Proof.
    intros * Hperm Hvd; inv Hvd; inv_VarsDefined.
    econstructor; eauto.
    1,2:now rewrite <-Hperm.
  Qed.

  Lemma Is_defined_in_vars_defined : forall x blk,
      Is_defined_in (Var x) blk ->
      PS.In x (vars_defined blk).
  Proof.
    induction blk using block_ind2; intros * Hin; simpl in *.
    - (* equation *)
      inv Hin; auto.
      now rewrite ps_from_list_In.
    - (* last *) inv Hin.
    - (* reset *)
      inv Hin. simpl_Exists.
      eapply In_In_PSUnion; eauto. 2:eapply in_map_iff; eauto.
      simpl_Forall; eauto.
    - (* switch *)
      inv Hin. rename H2 into Hin. simpl_Exists. simpl_Forall.
      inv Hin. simpl_Exists; simpl_Forall.
      repeat (eapply In_In_PSUnion; [|eapply in_map_iff; eauto]; simpl).
      eauto.
    - (* automaton *)
      inv Hin. rename H2 into Hin. simpl_Exists. simpl_Forall.
      inv Hin. inv H0; destruct_conjs; subst. simpl_Exists; simpl_Forall.
      repeat (eapply In_In_PSUnion; [|eapply in_map_iff; eauto]; simpl).
      apply PSF.filter_3. intros ???; subst; auto.
      + eapply In_In_PSUnion; eauto. eapply in_map_iff; eauto.
      + eapply Bool.negb_true_iff.
        eapply Bool.not_true_iff_false. intro contra.
        apply H4.
        eapply mem_assoc_ident_true in contra as ((?&?)&?); eauto using In_InMembers.
    - (* local *)
      inv Hin. inv H2.
      eapply PSF.filter_3. intros ???; subst; auto.
      + simpl_Exists.
        eapply In_In_PSUnion; eauto. 2:eapply in_map_iff; eauto.
        simpl_Forall; eauto.
      + eapply Bool.negb_true_iff.
        eapply Bool.not_true_iff_false. intro contra.
        apply H5.
        eapply mem_assoc_ident_true in contra as ((?&?)&?); eauto using In_InMembers.
  Qed.

  Lemma vars_defined_Is_defined_in : forall x blk,
      PS.In x (vars_defined blk) ->
      Is_defined_in (Var x) blk.
  Proof.
    induction blk using block_ind2; intros * Hin; simpl in *.
    - (* equation *)
      destruct eq. rewrite ps_from_list_In in Hin.
      now constructor.
    - (* last *)
      apply not_In_empty in Hin as [].
    - (* reset *)
      apply PSUnion_In_In in Hin as (?&Hin1&Hin2). simpl_In.
      simpl_Forall.
      constructor. solve_Exists.
    - (* switch *)
      unfold vars_defined_scope in *.
      apply PSUnion_In_In in Hin as (?&Hin1&Hin2). simpl_In. destruct b; simpl in *.
      simpl_Forall.
      apply PSUnion_In_In in Hin2 as (?&Hin2&Hin3). simpl_In. simpl_Forall.
      constructor. solve_Exists. constructor. solve_Exists.
    - (* automaton *)
      unfold vars_defined_scope in *.
      apply PSUnion_In_In in Hin as (?&Hin1&Hin2). simpl_In.
      simpl_Forall. destruct b; destruct_conjs; destruct s; destruct_conjs.
      apply PS.filter_spec in Hin2 as (Hin2&Hassoc). 2:intros ?? Heq; inv Heq; auto.
      apply PSUnion_In_In in Hin2 as (?&Hin2&Hin3). simpl_In.
      simpl_Forall.
      constructor. solve_Exists. constructor. constructor. solve_Exists.
      intros contra. eapply InMembers_In in contra as (?&?).
      eapply Bool.negb_true_iff, mem_assoc_ident_false in Hassoc; eauto.
    - (* local *)
      eapply PS.filter_spec in Hin as (Hin&Hassoc). 2:intros ?? Heq; inv Heq; auto.
      apply PSUnion_In_In in Hin as (?&Hin1&Hin2). simpl_In.
      simpl_Forall.
      econstructor. constructor. solve_Exists.
      intros contra. eapply InMembers_In in contra as (?&?).
      eapply Bool.negb_true_iff, mem_assoc_ident_false in Hassoc; eauto.
  Qed.

  Corollary vars_defined_spec : forall x blk,
      PS.In x (vars_defined blk) <-> Is_defined_in (Var x) blk.
  Proof.
    split; intros; eauto using vars_defined_Is_defined_in, Is_defined_in_vars_defined.
  Qed.

  Corollary map_vars_defined_spec : forall x blks,
      PS.In x (PSUnion (map vars_defined blks)) <-> Exists (Is_defined_in (Var x)) blks.
  Proof.
    intros. split; intros In.
    - apply PSUnion_In_In in In as (?&?&?). simpl_In. solve_Exists.
      now apply vars_defined_spec.
    - simpl_Exists. eapply In_In_PSUnion; [|solve_In].
      now apply vars_defined_spec.
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
