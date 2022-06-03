From compcert Require Import common.Events.
From compcert Require Import common.Values.
From compcert Require Import common.Globalenvs.
From compcert Require Import cfrontend.Clight.
From compcert Require Import lib.Integers.

From Velus Require Import Common.
From Velus Require Import Ident.
From Velus Require Import ObcToClight.Interface.

From Coq Require Import List.
Import List.ListNotations.

Import IStr.
Import OpAux.

Import Obc.Syn.

Section finite_traces.

  Variable p: Clight.program.

  Definition eventval_of_cvalue (v: cvalue): eventval :=
    match v with
    | Vint i => EVint i
    | Vlong i => EVlong i
    | Vfloat f => EVfloat f
    | Vsingle f => EVsingle f
    | Vptr _ _ => (* Not supported *) EVint Int.zero
    | Vundef => (* Not supported *) EVint Int.zero
    end.

  Definition eventval_of_value (v: value) : eventval :=
    match v with
    | Vscalar v => eventval_of_cvalue v
    | Venum n => EVint (enumtag_to_int n)
    end.

  Lemma eventval_of_cvalue_match:
    forall v t,
      wt_cvalue v t ->
      eventval_match (globalenv p)
                     (eventval_of_cvalue v)
                     (AST.type_of_chunk (type_chunk t)) v.
  Proof.
    destruct v; intros * Wt; inv Wt; simpl; try econstructor.
    destruct sz; try destruct sg; econstructor.
  Qed.

  Corollary eventval_of_value_match:
    forall v t,
      wt_value v t ->
      eventval_match (globalenv p)
                     (eventval_of_value v)
                     (AST.type_of_chunk (type_to_chunk t))
                     (value_to_cvalue v).
  Proof.
    inversion 1; subst; simpl.
    - now apply eventval_of_cvalue_match.
    - destruct (memory_chunk_of_enumtag_spec (length tn)) as [(Hn & E)|[(Hn & E)|(Hn & E)]];
        rewrite E; constructor.
  Qed.

  Definition load_event_of_value (v: value) (xt: ident * type): event :=
    Event_vload (type_to_chunk (snd xt))
                (prefix_glob (fst xt))
                Ptrofs.zero (eventval_of_value v).

  Definition store_event_of_value (v: value) (xt: ident * type): event :=
    Event_vstore (type_to_chunk (snd xt))
                 (prefix_glob (fst xt))
                 Ptrofs.zero (eventval_of_value v).

  Definition load_events  : list value -> list (ident * type) -> trace :=
    CommonList.map2 load_event_of_value.
  Definition store_events : list value -> list (ident * type) -> trace :=
    CommonList.map2 store_event_of_value.

  Fact load_events_nil : forall vs, load_events vs [] = [].
  Proof. apply map2_nil_r. Qed.

  Fact load_events_cons : forall v vs xt xts,
      load_events (v :: vs) (xt :: xts) = [load_event_of_value v xt] ++ load_events vs xts.
  Proof. auto. Qed.

  Fact store_events_nil : forall vs, store_events vs [] = [].
  Proof. apply map2_nil_r. Qed.

  Fact store_events_cons : forall v vs xt xts,
      store_events (v :: vs) (xt :: xts) = [store_event_of_value v xt] ++ store_events vs xts.
  Proof. auto. Qed.

End finite_traces.

Section infinite_traces.

  Variable ins  : stream (list value).
  Variable outs : stream (list value).

  Variable xs : list (ident * type).
  Variable ys : list (ident * type).

  Hypothesis xs_ys_spec: xs <> [] \/ ys <> [].

  Hypothesis Len_ins: forall n, length (ins n) = length xs.
  Hypothesis Len_outs: forall n, length (outs n) = length ys.

  Lemma load_store_events_not_E0:
    forall n,
      load_events (ins n) xs <> E0 \/ store_events (outs n) ys <> E0.
  Proof.
    intro n; specialize (Len_ins n); specialize (Len_outs n).
    destruct xs_ys_spec.
    - left; destruct xs, (ins n); auto; simpl in Len_ins; discriminate.
    - right; destruct ys, (outs n); auto; simpl in Len_outs; discriminate.
  Qed.

  Program CoFixpoint mk_trace' (n: nat): traceinf' :=
    Econsinf' (load_events (ins n) xs ** store_events (outs n) ys)
              (mk_trace' (S n)) _.
  Next Obligation.
    intro E; apply Eapp_E0_inv in E.
    pose proof (load_store_events_not_E0 n).
    intuition.
  Qed.

  Definition mk_trace (n: nat) : traceinf :=
    traceinf_of_traceinf' (mk_trace' n).

  Lemma unfold_mk_trace: forall n,
      mk_trace n =
      (load_events (ins n) xs ** E0 ** store_events (outs n) ys)
        *** E0
        *** mk_trace (S n).
  Proof.
    unfold mk_trace.
    intro.
    rewrite E0_left, E0_left_inf, (unroll_traceinf' (mk_trace' n)).
    simpl.
    now rewrite traceinf_traceinf'_app.
  Qed.

End infinite_traces.

(** The trace of an Obc method *)
Section Obc.
  Variable (m: method) (ins outs: stream (list value)).

  Hypothesis in_out_spec : m.(m_in) <> [] \/ m.(m_out) <> [].

  Hypothesis Len_ins : forall n, length (ins n) = length m.(m_in).
  Hypothesis Len_outs: forall n, length (outs n) = length m.(m_out).

  Program Definition trace_step (n: nat): traceinf :=
    mk_trace ins outs m.(m_in) m.(m_out) _ _ _ n.

End Obc.
