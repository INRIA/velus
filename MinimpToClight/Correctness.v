Set Automatic Coercions Import.

Require Import Rustre.Common.
Require Import Rustre.MP2CL.Translation.
Require Import Rustre.Minimp.Semantics.
Require Import Rustre.Interface.

Module Import Sem := SemanticsFun Op Syn.

Require Import common.Events.
Require Import common.Globalenvs.
Require Import common.Memory.
Require Import lib.Integers.
Require Import common.Smallstep.
Require Import common.Errors.
Require Import lib.Coqlib.
Require common.AST.
Require cfrontend.Clight.

Require Import Arith.Wf_nat.

Open Scope list_scope.
Import List.ListNotations.

Record fundef := Fundef {name: ident; body: stmt}.
Definition vardef := cl_ident.

Definition genv := Genv.t fundef vardef.
Inductive state := State (H: heap) (S: stack) (s: stmt).

Definition make_gvar (init volatile: bool) (name: cl_ident) :=
  (name,
   @AST.Gvar fundef _ (AST.mkglobvar name (if init then [AST.Init_space Z0] else []) false volatile)).

Definition make_gfun (name: cl_ident) (body: stmt) :=
  (name,
   @AST.Gfun _ vardef (Fundef name body)).

Definition convert_class (defs: list (cl_ident * AST.globdef fundef vardef)) (c: class)
  : list (cl_ident * AST.globdef fundef vardef) :=
  match c with
    mk_class c_name c_input c_output c_mems c_objs c_step c_reset =>
    let name := translate_ident c_name in
    let cls := make_gvar false false name in
    let step := make_gfun (step_id name) c_step in
    let reset := make_gfun (reset_id name) c_reset in
    cls :: step :: reset :: defs
  end.

Definition convert_prog (p: program): AST.program fundef vardef :=
  let defs := List.fold_left convert_class p nil in
  AST.mkprogram defs [] main_id.
  
Inductive step: genv -> state -> trace -> state -> Prop :=
  DoStep: forall prog ge H S s H' S' t,
    stmt_eval prog H S s (H', S') ->
    step ge (State H S s) t (State H' S' Skip).

Definition globalenv (p: program) :=
  Genv.globalenv (convert_prog p).

Parameter convert_mem: mem -> heap * stack.
Inductive initial_state (p: program): state -> Prop :=
  IniState: forall b f m0 H0 S0,
    let ge := globalenv p in
    let p' := convert_prog p in
    Genv.init_mem p' = Some m0 ->
    Genv.find_symbol ge p'.(AST.prog_main) = Some b ->
    Genv.find_funct_ptr ge b = Some f ->
    convert_mem m0 = (H0, S0) ->
    initial_state p (State H0 S0 f.(body)).

Inductive final_state (s: state) (n: int): Prop := False.

Definition semantics (p: program) :=
  let ge := globalenv p in
  Semantics_gen step (initial_state p) final_state ge ge.

Section SPEC.

  Inductive tr_function: fundef -> Clight.function -> Prop :=
    tr_function_intro: forall f tf,
      (* tr_stmt f.(Csyntax.fn_body) tf.(fn_body) -> *)
      (* fn_return tf = Csyntax.fn_return f -> *)
      (* fn_callconv tf = Csyntax.fn_callconv f -> *)
      (* fn_params tf = Csyntax.fn_params f -> *)
      (* fn_vars tf = Csyntax.fn_vars f -> *)
      (* tr_function f tf *) tr_function f tf.

  Inductive tr_fundef: fundef -> Clight.fundef -> Prop :=
    tr_fundef_intro: forall f tf,
      tr_function f tf -> tr_fundef f (Clight.Internal tf).

  Inductive tr_vardef: vardef -> Ctypes.type -> Prop :=
    tr_vardef_intro: forall x t,
      tr_vardef x t.

  Theorem transl_program_spec:
    forall main_node p tp,
      translate p main_node = OK tp ->
      AST.match_program tr_fundef tr_vardef nil main_id (convert_prog p) tp.
  Admitted.

End SPEC.
Section PRESERVATION.
 
  Variable main_node : ident.

  Variable prog: program.
  Variable tprog: Clight.program.
  Hypothesis TRANSL: translate prog main_node = OK tprog.
  
  Let ge := globalenv prog.
  Let tge := Clight.globalenv tprog.

  Definition measure (st: state) : nat := 0%nat.
  
  Inductive match_states: state -> Clight.state -> Prop :=
    match_intro: forall S S', match_states S S'.

  Lemma public_preserved:
    forall (s: ident), Genv.public_symbol tge s = Genv.public_symbol ge s.
  Proof.
    intros. eapply Genv.public_symbol_match. eapply transl_program_spec; eauto.
    simpl. tauto.
  Qed.

  (* 
    S1 <------->    S1'
    |t           |t or |t 
    v            v+    v* |S2| < |S1|
    S2 <------->    S2'
 *)
  Theorem simulation:
    forall S1 t S2,
      step ge S1 t S2 ->
      forall S1' (MS: match_states S1 S1'),
      exists S2',
        (plus Clight.step1 tge S1' t S2' \/
         (star Clight.step1 tge S1' t S2' /\ measure S2 < measure S1)%nat)
        /\ match_states S2 S2'.
  Proof.
    intros S1 t S2 STEP. destruct STEP. destruct H0; admit.
  Qed.
  
  Lemma transl_initial_states:
    forall S,
      initial_state prog S ->
      exists S', Clight.initial_state tprog S' /\ match_states S S'.
  Proof.
    intros S IS. inv IS.
    admit.
  Qed.

  Lemma transl_final_states:
    forall S S' r,
      match_states S S' -> final_state S r -> Clight.final_state S' r.
  Proof.
    intros S S' r H FS.
    admit.
  Qed.

  Theorem transl_program_correct:
    forward_simulation (semantics prog) (Clight.semantics1 tprog).
  Proof.
    eapply forward_simulation_star_wf with (order := ltof _ measure).
    eexact public_preserved.
    eexact transl_initial_states.
    eexact transl_final_states.
    apply well_founded_ltof.
    exact simulation.
  Qed.

End PRESERVATION.