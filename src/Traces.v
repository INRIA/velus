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

Import Obc.Syn.
Import Str.
Import OpAux.

Section finite_traces.

  Variable p: Clight.program.

  Definition eventval_of_val (v: val): eventval :=
    match v with
    | Vint i => EVint i
    | Vlong i => EVlong i
    | Vfloat f => EVfloat f
    | Vsingle f => EVsingle f
    | Vptr _ _ => (* Not supported *) EVint Int.zero
    | Vundef => (* Not supported *) EVint Int.zero
    end.

  Lemma eventval_of_val_match:
    forall v t,
      wt_val v t ->
      eventval_match (globalenv p)
                     (eventval_of_val v)
                     (AST.type_of_chunk (type_chunk t)) v.
  Proof.
    destruct v; intros * Wt; inv Wt; simpl; try econstructor.
    destruct sz; try destruct sg; econstructor.
  Qed.

  Definition load_event_of_val (v: val) (xt: ident * type): event :=
    Event_vload (type_chunk (snd xt))
                (glob_id (fst xt))
                Ptrofs.zero (eventval_of_val v).

  Definition store_event_of_val (v: val) (xt: ident * type): event :=
    Event_vstore (type_chunk (snd xt))
                 (glob_id (fst xt))
                 Ptrofs.zero (eventval_of_val v).

  Definition mk_events (f: val -> ident * type -> event) (vs: list val) (args: list (ident * type)) : trace :=
    map (fun vxt => f (fst vxt) (snd vxt)) (combine vs args).

  Definition load_events  : list val -> list (ident * type) -> trace := mk_events load_event_of_val.
  Definition store_events : list val -> list (ident * type) -> trace := mk_events store_event_of_val.

  Lemma mk_events_nil: forall f vs, mk_events f vs [] = [].
  Proof. intros; destruct vs; simpl; auto. Qed.

  Lemma mk_events_cons:
    forall f v vs xt xts,
      mk_events f (v :: vs) (xt :: xts) = f v xt :: mk_events f vs xts.
  Proof. auto. Qed.

  Corollary load_events_nil : forall vs, load_events vs [] = [].
  Proof. apply mk_events_nil. Qed.

  Corollary load_events_cons : forall v vs xt xts,
      load_events (v :: vs) (xt :: xts) = [load_event_of_val v xt] ++ load_events vs xts.
  Proof. apply mk_events_cons. Qed.

  Corollary store_events_nil : forall vs, store_events vs [] = [].
  Proof. apply mk_events_nil. Qed.

  Corollary store_events_cons : forall v vs xt xts,
      store_events (v :: vs) (xt :: xts) = [store_event_of_val v xt] ++ store_events vs xts.
  Proof. apply mk_events_cons. Qed.

End finite_traces.

Section infinite_traces.

  Variable ins  : stream (list val).
  Variable outs : stream (list val).

  Variable xs : list (ident * type).
  Variable ys : list (ident * type).

  Hypothesis xs_spec: xs <> [].
  Hypothesis ys_spec: ys <> [].

  Hypothesis Hwt_ins : forall n, wt_vals (ins n) xs.
  Hypothesis Hwt_outs: forall n, wt_vals (outs n) ys.

  Lemma load_events_not_E0: forall n,
      load_events (ins n) xs <> E0.
  Proof.
    clear - Hwt_ins xs_spec.
    intros n; specialize Hwt_ins with n.
    destruct xs; auto.
    inv Hwt_ins; rewrite load_events_cons; discriminate.
  Qed.

  Lemma store_events_not_E0: forall n,
      store_events (outs n) ys <> E0.
  Proof.
    clear - Hwt_outs ys_spec.
    intros n; specialize Hwt_outs with n.
    destruct ys; auto.
    inv Hwt_outs; simpl; rewrite store_events_cons; discriminate.
  Qed.

  CoFixpoint mk_trace (n: nat): traceinf'.
  refine(
      (Econsinf' (load_events (ins n) xs)
                 (Econsinf' (store_events (outs n) ys)
                            (mk_trace (S n)) _) _));
    [ apply store_events_not_E0
    | apply load_events_not_E0 ].
  Defined.

  Lemma unfold_mk_trace: forall n,
      traceinf_of_traceinf' (mk_trace n) =
      (load_events (ins n) xs ** E0 ** store_events (outs n) ys)
        *** E0
        *** traceinf_of_traceinf' (mk_trace (S n)).
  Proof.
    intro.
    rewrite E0_left, E0_left_inf, (unroll_traceinf' (mk_trace n)).
    unfold mk_trace at 1.
    now rewrite 2!traceinf_traceinf'_app, Eappinf_assoc.
  Qed.

End infinite_traces.

Section Obc.
  Variable (m_step: method) (ins outs: stream (list val)).

  Hypothesis in_spec : m_step.(m_in) <> [].
  Hypothesis out_spec: m_step.(m_out) <> [].

  Hypothesis Hwt_ins : forall n, wt_vals (ins n) m_step.(m_in).
  Hypothesis Hwt_outs: forall n, wt_vals (outs n) m_step.(m_out).

  Definition trace_step (n: nat): traceinf' :=
    mk_trace ins outs m_step.(m_in) m_step.(m_out) in_spec out_spec Hwt_ins Hwt_outs n.

End Obc.
