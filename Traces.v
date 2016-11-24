Require Import common.Events.
Require Import common.Values.
Require Import common.Globalenvs.
Require Import cfrontend.Clight.
Require Import lib.Integers.

Require Import Velus.Common.
Require Import Velus.Ident.
Require Import Velus.ObcToClight.Interface.

Require Import List.
Import List.ListNotations.
Require Import Instantiator.
Import Obc.Typ.
Import Obc.Syn.
(* Import Obc.Sem. *)
Import NL.Str.
Import OpAux.
Import Trans.

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
    forall v t, wt_val v t -> 
           eventval_match (globalenv p) 
                          (eventval_of_val v) 
                          (AST.type_of_chunk (type_chunk t)) v.
  Proof.
    destruct v; intros ** Wt; inv Wt; simpl; try econstructor.
    destruct sz; try destruct sg; econstructor.
  Qed.
  
  Definition load_event_of_val (v: val)(xt: ident * type): event
    := Event_vload (type_chunk (snd xt))
                   (glob_id (fst xt)) 
                   Int.zero (eventval_of_val v).

  Definition store_event_of_val (v: val)(xt: ident * type): event
    := Event_vstore (type_chunk (snd xt))
                    (glob_id (fst xt)) 
                    Int.zero (eventval_of_val v).

  Definition mk_event (f: val -> ident * type -> event)
             (vs: list val)(args: list (ident * type))
    := map (fun vxt => f (fst vxt) (snd vxt)) (combine vs args). 

  Definition load_events := mk_event load_event_of_val.
  Definition store_events := mk_event store_event_of_val.

  Lemma mk_event_nil: forall f vs, mk_event f vs [] = [].
  Proof. intros; destruct vs; simpl; auto. Qed.

  Lemma mk_event_cons: 
    forall f v vs xt xts, 
      mk_event f (v :: vs) (xt :: xts) = f v xt :: mk_event f vs xts.
  Proof. auto. Qed.

  Corollary load_events_nil : forall vs, load_events vs [] = [].
  Proof. apply mk_event_nil. Qed.

  Corollary load_events_cons : forall v vs xt xts, 
      load_events (v :: vs) (xt :: xts) = [load_event_of_val v xt] ++ load_events vs xts.
  Proof. apply mk_event_cons. Qed.

  Corollary store_events_nil : forall vs, store_events vs [] = [].
  Proof. apply mk_event_nil. Qed.

  Corollary store_events_cons : forall v vs xt xts, 
      store_events (v :: vs) (xt :: xts) = [store_event_of_val v xt] ++ store_events vs xts.
  Proof. apply mk_event_cons. Qed.

End finite_traces.

Section infinite_traces.

  Variable ins : stream (list const).
  Variable outs : stream (list const).

  Variable xs : list (ident * type).
  Variable ys : list (ident * type).

  Hypothesis xs_spec: xs <> [].
  Hypothesis ys_spec: ys <> [].

  Hypothesis Hwt_ins: forall n, wt_vals (map sem_const (ins n)) xs.
  Hypothesis Hwt_outs: forall n, wt_vals (map sem_const (outs n)) ys.

  Lemma load_events_not_E0: forall n, 
      load_events (map sem_const (ins n)) xs <> E0.
  Proof.
    clear - Hwt_ins xs_spec.
    intros n; specialize Hwt_ins with n.
    destruct xs; auto.
    inv Hwt_ins; rewrite load_events_cons; discriminate.
  Qed.

  Lemma store_events_not_E0: forall n, 
      store_events (map sem_const (outs n)) ys <> E0.
  Proof.
    clear - Hwt_outs ys_spec.
    intros n; specialize Hwt_outs with n.
    destruct ys; auto.
    inv Hwt_outs; simpl; rewrite store_events_cons; discriminate.
  Qed.

  CoFixpoint mk_trace (n: nat): traceinf'.
  clear - mk_trace n ins outs xs ys. 
  refine(
      (Econsinf' (load_events (map sem_const (ins n)) xs)
                 (Econsinf' (store_events (map sem_const (outs n)) ys)
                            (mk_trace (S n)) _) _));
    [ apply store_events_not_E0
    | apply load_events_not_E0 ].
  Defined.

  Lemma unfold_mk_trace: forall n,
      traceinf_of_traceinf' (mk_trace n) = 
      (load_events (map sem_const (ins n)) xs
                   ++ E0
                   ++ store_events (map sem_const (outs n)) ys)
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
  Variable (m_step: method) (ins outs: stream (list const)).

  Hypothesis in_spec: m_step.(m_in) <> [].
  Hypothesis out_spec: m_step.(m_out) <> [].

  Hypothesis Hwt_ins: forall n, wt_vals (map sem_const (ins n)) m_step.(m_in).
  Hypothesis Hwt_outs: forall n, wt_vals (map sem_const (outs n)) m_step.(m_out).

  Definition trace_step (n: nat): traceinf' :=
    mk_trace ins outs m_step.(m_in) m_step.(m_out) in_spec out_spec Hwt_ins Hwt_outs n.

End Obc.
