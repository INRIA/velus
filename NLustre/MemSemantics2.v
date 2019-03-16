Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Arith.Compare_dec.

Require Import Coq.FSets.FMapPositive.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.RMemory.
Require Import Velus.NLustre.Stream.
Require Import Velus.NLustre.NLExprSyntax.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.IsVariable.
Require Import Velus.NLustre.IsDefined.
Require Import Velus.NLustre.NLExprSemantics.
Require Import Velus.NLustre.NLSemantics.
Require Import Velus.NLustre.NLInterpretor.
Require Import Velus.NLustre.Ordered.
Require Import Velus.NLustre.Memories.
Require Import Velus.NLustre.IsFree.
Require Import Velus.NLustre.NoDup.

Set Implicit Arguments.

(** * The NLustre+Memory semantics *)

(**

  We provide a "non-standard" dataflow semantics where the state
  introduced by an [fby] is kept in a separate [memory] of
  streams. The only difference is therefore in the treatment of the
  [fby].

 *)


(* XXX: Is this comment still relevant?

   NB: The history H is not really necessary here. We could just as well
       replay all the semantic definitions using a valueEnv N ('N' for now),
       since all the historical information is in ms. This approach would
       have two advantages:

       1. Conceptually cleanliness: N corresponds more or less to the
          temporary variables in the Obc implementation (except that it
          would also contain values for variables defined by EqFby).

       2. No index needed to access values in when reasoning about
          translation correctness.

       But this approach requires more uninteresting definitions and
       and associated proofs of properties, and a longer proof of equivalence
       with sem_node: too much work for too little gain.
 *)

Module Type MEMSEMANTICS
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import OpAux   : OPERATORS_AUX   Op)
       (Import Clks    : CLOCKS          Ids)
       (Import ExprSyn : NLEXPRSYNTAX        Op)
       (Import Syn     : NLSYNTAX        Ids Op       Clks ExprSyn)
       (Import Str     : STREAM              Op OpAux)
       (Import Ord     : ORDERED         Ids Op       Clks ExprSyn Syn)
       (Import ExprSem : NLEXPRSEMANTICS Ids Op OpAux Clks ExprSyn     Str)
       (Import Sem     : NLSEMANTICS     Ids Op OpAux Clks ExprSyn Syn Str Ord ExprSem)
       (Import Interp  : NLINTERPRETOR   Ids Op OpAux Clks ExprSyn     Str     ExprSem)
       (Import Mem     : MEMORIES        Ids Op       Clks ExprSyn Syn)
       (Import IsD     : ISDEFINED       Ids Op       Clks ExprSyn Syn                 Mem)
       (Import IsV     : ISVARIABLE      Ids Op       Clks ExprSyn Syn                 Mem IsD)
       (Import IsF     : ISFREE          Ids Op       Clks ExprSyn Syn)
       (Import NoD     : NODUP           Ids Op       Clks ExprSyn Syn                 Mem IsD IsV).

  Definition memories := stream (memory val).
  Definition history := stream env.

  Definition mfby (x: ident) (c0: val) (xs: stream value) (rs: stream bool) (M M': memories) (ys: stream value) : Prop :=
    find_val x (M 0) = Some c0
    /\ (forall n, find_val x (M (S n)) = find_val x (M' n))
    /\ forall n, match find_val x (M n) with
           | Some mv =>
             match xs n with
             | absent =>
               find_val x (M' n) = Some mv
               /\ ys n = absent
             | present v =>
               find_val x (M' n) = Some v
               /\ ys n = present (if rs n then c0 else mv)
             end
           | None => False
           end.

  Section NodeSemantics.

    Definition sub_inst_n (x: ident) (M M': memories) : Prop :=
      forall n, sub_inst x (M n) (M' n).

    Variable G: global.

    Definition memory_closed (M: memory val) (eqs: list equation) : Prop :=
      (forall i, find_inst i M <> None -> InMembers i (gather_insts eqs))
      /\ forall x, find_val x M <> None -> In x (gather_mems eqs).

    Definition memory_closed_n (M: memories) (eqs: list equation) : Prop :=
      forall n, memory_closed (M n) eqs.

    Inductive msem_equation: stream bool -> stream bool -> history -> memories -> memories -> equation -> Prop :=
    | SEqDef:
        forall bk rs H M M' x ck xs ce,
          (forall n, sem_var_instant (H n) x (xs n)) ->
          (forall n, sem_caexp_instant (bk n) (H n) ck ce (xs n)) ->
          msem_equation bk rs H M M' (EqDef x ck ce)
    | SEqApp:
        forall bk rs H M M' x xs ck f Mx Mx' arg ls xss,
          hd_error xs = Some x ->
          sub_inst_n x M Mx ->
          sub_inst_n x M' Mx' ->
          (forall n, sem_laexps_instant (bk n) (H n) ck arg (ls n)) ->
          (forall n, sem_vars_instant (H n) xs (xss  n))->
          msem_node f rs ls Mx Mx' xss ->
          msem_equation bk rs H M M' (EqApp xs ck f arg None)
    | SEqReset:
        forall bk rs' rs'' H M M' x xs ck f Mx Mx' arg y ys rs ls xss,
          hd_error xs = Some x ->
          sub_inst_n x M Mx ->
          sub_inst_n x M' Mx' ->
          (forall n, sem_laexps_instant (bk n) (H n) ck arg (ls n)) ->
          (forall n, sem_vars_instant (H n) xs (xss n)) ->
          (forall n, sem_var_instant (H n) y (ys n)) ->
          reset_of ys rs ->
          (forall n, rs'' n = rs n || rs' n) ->
          msem_node f rs'' ls Mx Mx' xss ->
          msem_equation bk rs' H M M' (EqApp xs ck f arg (Some y))
    | SEqFby:
        forall bk rs H M M' x ck ls xs c0 le,
          (forall n, sem_laexp_instant (bk n) (H n) ck le (ls n)) ->
          (forall n, sem_var_instant (H n) x (xs n)) ->
          mfby x (sem_const c0) ls rs M M' xs ->
          msem_equation bk rs H M M' (EqFby x ck c0 le)

    with msem_node:
           ident -> stream bool -> stream (list value) -> memories -> memories -> stream (list value) -> Prop :=
           SNode:
             forall bk rs H f xss M M' yss node,
               clock_of xss bk ->
               find_node f G = Some node ->
               (forall n, sem_vars_instant (H n) (map fst node.(n_in)) (xss n)) ->
               (forall n, sem_vars_instant (H n) (map fst node.(n_out)) (yss n)) ->
               same_clock xss ->
               same_clock yss ->
               (forall n, absent_list (xss n) <-> absent_list (yss n)) ->
               (forall n, sem_clocked_vars_instant (bk n) (H n) (idck node.(n_in))) ->
               Forall (msem_equation bk rs H M M') node.(n_eqs) ->
               memory_closed_n M node.(n_eqs) ->
               memory_closed_n M' node.(n_eqs) ->
               msem_node f rs xss M M' yss.

  End NodeSemantics.

  (** ** Induction principle for [msem_equation] and [msem_node] *)

  (** The automagically-generated induction principle is not strong
enough: it does not support the internal fixpoint introduced by
[Forall] *)

  Section msem_node_mult.

    Variable G: global.

    Variable P_equation: stream bool -> stream bool -> history -> memories -> memories -> equation -> Prop.
    Variable P_node: ident -> stream bool -> stream (list value) -> memories -> memories -> stream (list value) -> Prop.

    Hypothesis EqDefCase:
      forall bk rs H M M' x ck xs ce,
        (forall n, sem_var_instant (H n) x (xs n)) ->
        (forall n, sem_caexp_instant (bk n) (H n) ck ce (xs n)) ->
        P_equation bk rs H M M' (EqDef x ck ce).

    Hypothesis EqAppCase:
      forall bk rs H M M' x xs ck f Mx Mx' arg ls xss,
        hd_error xs = Some x ->
        sub_inst_n x M Mx ->
        sub_inst_n x M' Mx' ->
        (forall n, sem_laexps_instant (bk n) (H n) ck arg (ls n)) ->
        (forall n, sem_vars_instant (H n) xs (xss  n))->
        msem_node G f rs ls Mx Mx' xss ->
        P_node f rs ls Mx Mx' xss ->
        P_equation bk rs H M M' (EqApp xs ck f arg None).

    Hypothesis EqResetCase:
      forall bk rs' rs'' H M M' x xs ck f Mx Mx' arg y ys rs ls xss,
        hd_error xs = Some x ->
        sub_inst_n x M Mx ->
        sub_inst_n x M' Mx' ->
        (forall n, sem_laexps_instant (bk n) (H n) ck arg (ls n)) ->
        (forall n, sem_vars_instant (H n) xs (xss n)) ->
        (forall n, sem_var_instant (H n) y (ys n)) ->
        reset_of ys rs ->
        (forall n, rs'' n = rs n || rs' n) ->
        msem_node G f rs'' ls Mx Mx' xss ->
        P_node f rs'' ls Mx Mx' xss ->
        P_equation bk rs' H M M' (EqApp xs ck f arg (Some y)).

    Hypothesis EqFbyCase:
      forall bk rs H M M' x ck ls xs c0 le,
        (forall n, sem_laexp_instant (bk n) (H n) ck le (ls n)) ->
        (forall n, sem_var_instant (H n) x (xs n)) ->
        mfby x (sem_const c0) ls rs M M' xs ->
        P_equation bk rs H M M' (EqFby x ck c0 le).

    Hypothesis NodeCase:
      forall bk rs H f xss M M' yss node,
        clock_of xss bk ->
        find_node f G = Some node ->
        (forall n, sem_vars_instant (H n) (map fst node.(n_in)) (xss n)) ->
        (forall n, sem_vars_instant (H n) (map fst node.(n_out)) (yss n)) ->
        same_clock xss ->
        same_clock yss ->
        (forall n, absent_list (xss n) <-> absent_list (yss n)) ->
        (forall n, sem_clocked_vars_instant (bk n) (H n) (idck node.(n_in))) ->
        Forall (msem_equation G bk rs H M M') node.(n_eqs) ->
        memory_closed_n M node.(n_eqs) ->
        memory_closed_n M' node.(n_eqs) ->
        Forall (P_equation bk rs H M M') node.(n_eqs) ->
        P_node f rs xss M M' yss.

    Fixpoint msem_equation_mult
             (b rs: stream bool) (H: history) (M M': memories) (e: equation)
             (Sem: msem_equation G b rs H M M' e) {struct Sem}
      : P_equation b rs H M M' e
    with msem_node_mult
           (f: ident)
           (rs: stream bool)
           (xss: stream (list value))
           (M M': memories)
           (oss: stream (list value))
           (Sem: msem_node G f rs xss M M' oss) {struct Sem}
         : P_node f rs xss M M' oss.
    Proof.
      - destruct Sem; eauto.
      - destruct Sem; eauto.
        eapply NodeCase; eauto.
        match goal with
          H: memory_closed_n M _, H': memory_closed_n M' _, Heqs: Forall _ (n_eqs _)
          |- _ => clear H H'; induction Heqs; auto
        end.
    Qed.

    Combined Scheme msem_node_equation_reset_ind from
             msem_node_mult, msem_equation_mult.

  End msem_node_mult.

  Definition msem_nodes (G: global) : Prop :=
    Forall (fun no => exists rs xs M M' ys, msem_node G no.(n_name) rs xs M M' ys) G.


  (** ** Properties *)

  (** *** Environment cons-ing lemmas *)

  (* Instead of repeating all these cons lemmas (i.e., copying and pasting them),
   and dealing with similar obligations multiple times in translation_correct,
   maybe it would be better to bake Ordered_nodes into msem_node and to make
   it like Miniimp, i.e.,
      find_node f G = Some (nd, G') and msem_node G' nd xs ys ?
   TODO: try this when the other elements are stabilised. *)

  Lemma msem_node_cons:
    forall n G f rs xs M M' ys,
      Ordered_nodes (n :: G) ->
      msem_node (n :: G) f rs xs M M' ys ->
      n.(n_name) <> f ->
      msem_node G f rs xs M M' ys.
  Proof.
    Hint Constructors msem_node msem_equation.
    intros ** Hord Hsem Hnf.
    revert Hnf.
    induction Hsem as [| | | |?????????? Hf ????????? IH]
        using msem_node_mult
      with (P_equation := fun bk rs H M M' eq =>
                            ~Is_node_in_eq n.(n_name) eq ->
                            msem_equation G bk rs H M M' eq); eauto.
    - intro Hnin.
      econstructor; eauto.
      apply IHHsem. intro Hnf; apply Hnin; rewrite Hnf. constructor.
    - intro Hnin.
      econstructor; eauto.
      apply IHHsem. intro Hnf; apply Hnin; rewrite Hnf. constructor.
    - intro.
      pose proof Hf.
      rewrite find_node_tl with (1:=Hnf) in Hf.
      econstructor; eauto.
      apply find_node_later_not_Is_node_in with (2:=Hf) in Hord.
      apply Is_node_in_Forall in Hord.
      apply Forall_Forall with (1:=Hord) in IH.
      apply Forall_impl with (2:=IH).
      intuition.
  Qed.

  Lemma msem_node_cons2:
    forall n G f rs xs M M' ys,
      Ordered_nodes G ->
      msem_node G f rs xs M M' ys ->
      Forall (fun n' => n_name n <> n_name n') G ->
      msem_node (n :: G) f rs xs M M' ys.
  Proof.
    Hint Constructors msem_equation.
    intros ** Hord Hsem Hnin.
    assert (Hnin':=Hnin).
    revert Hnin'.
    induction Hsem as [| | | |???????? n' ? Hfind ?????? Heqs WF WF' IH]
        using msem_node_mult
      with (P_equation := fun bk rs H M M' eq =>
                            ~Is_node_in_eq n.(n_name) eq ->
                            msem_equation (n :: G) bk rs H M M' eq); eauto.
    intro HH; clear HH.
    assert (n.(n_name) <> f) as Hnf.
    { intro Hnf.
      rewrite Hnf in *.
      pose proof (find_node_name _ _ _ Hfind).
      apply find_node_split in Hfind.
      destruct Hfind as [bG [aG Hge]].
      rewrite Hge in Hnin.
      apply Forall_app in Hnin.
      destruct Hnin as [H' Hfg]; clear H'.
      inversion_clear Hfg.
      match goal with H:f<>_ |- False => now apply H end.
    }
    apply find_node_other with (2:=Hfind) in Hnf.
    econstructor; eauto.
    + assert (forall g, Is_node_in g n'.(n_eqs) -> Exists (fun nd=> g = nd.(n_name)) G)
        as Hniex by (intros g Hini;
                     apply find_node_find_again with (1:=Hord) (2:=Hfind) in Hini;
                     exact Hini).
      assert (Forall (fun eq => forall g,
                          Is_node_in_eq g eq -> Exists (fun nd=> g = nd.(n_name)) G)
                     n'.(n_eqs)) as HH.
      {
        clear Heqs IH WF WF'.
        induction n'.(n_eqs) as [|eq eqs]; [now constructor|].
        constructor.
        - intros g Hini.
          apply Hniex.
          constructor 1; apply Hini.
        - apply IHeqs.
          intros g Hini; apply Hniex.
          constructor 2; apply Hini.
      }
      apply Forall_Forall with (1:=HH) in IH.
      apply Forall_impl with (2:=IH).
      intros eq (Hsem & IH1).
      apply IH1.
      intro Hini.
      apply Hsem in Hini.
      apply Forall_Exists with (1:=Hnin) in Hini.
      apply Exists_exists in Hini.
      destruct Hini as [nd' [Hin [Hneq Heq]]].
      intuition.
  Qed.

  Lemma msem_equations_cons:
    forall G bk rs H M M' eqs n,
      Ordered_nodes (n :: G) ->
      ~Is_node_in n.(n_name) eqs ->
      (Forall (msem_equation G bk rs H M M') eqs <->
       Forall (msem_equation (n :: G) bk rs H M M') eqs).
  Proof.
    intros ** Hord Hnini.
    induction eqs as [|eq eqs IH]; [now constructor|].
    apply not_Is_node_in_cons in Hnini as [Hnini Hninis].
    split; intros Hsem; apply Forall_cons2 in Hsem as [Heq Heqs];
      apply IH in Heqs; auto; constructor; auto.
    - inv Hord.
      destruct Heq; eauto using msem_node_cons2.
    - inv Heq; eauto;
        assert (n.(n_name) <> f)
        by (intro HH; apply Hnini; rewrite HH; constructor);
        eauto using msem_node_cons.
  Qed.

  Lemma find_node_msem_node:
    forall G f,
      msem_nodes G ->
      find_node f G <> None ->
      exists rs xs M M' ys,
        msem_node G f rs xs M M' ys.
  Proof.
    intros G f Hnds Hfind.
    apply find_node_Exists in Hfind.
    apply Exists_exists in Hfind.
    destruct Hfind as [nd [Hin Hf]].
    unfold msem_nodes in Hnds.
    rewrite Forall_forall in Hnds.
    apply Hnds in Hin.
    destruct Hin as (rs & xs & M & M' & ys &?).
    exists rs, xs, M, M', ys.
    rewrite Hf in *; auto.
  Qed.

  (** *** Memory management *)

  Definition add_val_n (y: ident) (ms: stream val) (M: memories): memories :=
    fun n => add_val y (ms n) (M n).

  Lemma mfby_add_val_n:
    forall x v0 rs ls M M' xs y ms ms',
      x <> y ->
      mfby x v0 rs ls M M' xs ->
      mfby x v0 rs ls (add_val_n y ms M) (add_val_n y ms' M') xs.
  Proof.
    unfold add_val_n.
    intros ** Fby; destruct Fby as (?&?& Spec).
    split; [|split].
    - rewrite find_val_gso; auto.
    - intro; rewrite 2 find_val_gso; auto.
    - intro n; rewrite 2 find_val_gso; auto; apply Spec.
  Qed.

  Definition add_inst_n (y: ident) (M' M: memories): memories :=
    fun n => add_inst y (M' n) (M n).

  Lemma mfby_add_inst_n:
    forall x v0 rs ls M M' xs y My My',
      mfby x v0 rs ls M M' xs ->
      mfby x v0 rs ls (add_inst_n y My M) (add_inst_n y My' M') xs.
  Proof.
    inversion 1; econstructor; eauto.
  Qed.

  Hint Resolve mfby_add_val_n mfby_add_inst_n.

  Lemma msem_equation_madd_val:
    forall G bk rs H M M' x ms ms' eqs,
      ~Is_defined_in_eqs x eqs ->
      Forall (msem_equation G bk rs H M M') eqs ->
      Forall (msem_equation G bk rs H (add_val_n x ms M) (add_val_n x ms' M')) eqs.
  Proof.
    Hint Constructors msem_equation.
    intros ** Hnd Hsem.
    induction eqs as [|eq eqs IH]; [now constructor|].
    apply not_Is_defined_in_cons in Hnd.
    destruct Hnd as [Hnd Hnds].
    apply Forall_cons2 in Hsem.
    destruct Hsem as [Hsem Hsems].
    constructor; [|now apply IH with (1:=Hnds) (2:=Hsems)].
    destruct Hsem; eauto.
    apply not_Is_defined_in_eq_EqFby in Hnd.
    eapply SEqFby; eauto.
  Qed.

  Lemma msem_equation_madd_inst:
    forall G bk rs H M M' Mx Mx' x eqs,
      ~Is_defined_in_eqs x eqs ->
      Forall (msem_equation G bk rs H M M') eqs ->
      Forall (msem_equation G bk rs H (add_inst_n x Mx M) (add_inst_n x Mx' M')) eqs.
  Proof.
    Hint Constructors msem_equation.
    intros * Hnd Hsem.
    induction eqs as [|eq eqs IH]; [now constructor|].
    apply not_Is_defined_in_cons in Hnd.
    destruct Hnd as [Hnd Hnds].
    apply Forall_cons2 in Hsem.
    destruct Hsem as [Hsem Hsems].
    constructor; [|now apply IH with (1:=Hnds) (2:=Hsems)].
    destruct Hsem as [|????? x' ???????? Hsome
                         |?????? x' ??????????? Hsome|];
      eauto;
      assert (sub_inst_n x' (add_inst_n x Mx M) Mx0)
        by (apply not_Is_defined_in_eq_EqApp in Hnd;
            unfold sub_inst_n, sub_inst, add_inst_n in *; intro;
            rewrite find_inst_gso; auto; intro; subst x; destruct xs;
            inv Hsome; apply Hnd; now constructor);
      assert (sub_inst_n x' (add_inst_n x Mx' M') Mx'0)
        by (apply not_Is_defined_in_eq_EqApp in Hnd;
            unfold sub_inst_n, sub_inst, add_inst_n in *; intro;
            rewrite find_inst_gso; auto; intro; subst x; destruct xs;
            inv Hsome; apply Hnd; now constructor);
      eauto.
  Qed.


  (* XXX: I believe that this comment is outdated ([no_dup_defs] is long gone)

   - The no_dup_defs hypothesis is essential for the EqApp case.

     If the set of equations contains two EqApp's to the same variable:
        eq::eqs = [ EqApp x f lae; ...; EqApp x g lae' ]

     Then it is possible to have a coherent H, namely if
        f(lae) = g(lae')

     But nothing forces the 'memory streams' (internal memories) of
     f(lae) and g(lae') to be the same. This is problematic since they are
     both 'stored' at M x...

   - The no_dup_defs hypothesis is not essential for the EqFby case.

     If the set of equations contains two EqFby's to for the same variable:
        eq::eqs = [ EqFby x v0 lae; ...; EqFby x v0' lae'; ... ]

     then the 'memory streams' associated with each, ms and ms', must be
     identical since if (Forall (sem_equation G H) (eq::eqs)) exists then
     then the H forces the coherence between 'both' x's, and necessarily also
     between v0 and v0', and lae and lae'.

     That said, proving this result is harder than just assuming something
     that should be true anyway: that there are no duplicate definitions in
     eqs.

   Note that the no_dup_defs hypothesis requires a stronger definition of
   either Is_well_sch or Welldef_global.
   *)


  (** ** Fundamental theorem *)

  (**

We show that the standard semantics implies the existence of a
dataflow memory for which the non-standard semantics holds true.

   *)

  Lemma memory_closed_n_App:
    forall M eqs i Mx xs ck f es r,
      memory_closed_n M eqs ->
      hd_error xs = Some i ->
      memory_closed_n (add_inst_n i Mx M) (EqApp xs ck f es r :: eqs).
  Proof.
    intros ** WF Hd n; specialize (WF n); destruct WF as (Insts &?).
    split; auto.
    intro y; intros ** Hin.
    unfold sub_inst, add_inst_n in Hin; apply not_None_is_Some in Hin as (?& Find).
    destruct (ident_eq_dec y i).
    - subst.
      unfold gather_insts, concatMap; simpl.
      destruct xs; simpl in *; inv Hd; left; auto.
    - rewrite find_inst_gso in Find; auto.
      unfold gather_insts, concatMap; simpl.
      apply InMembers_app; right; auto.
      apply Insts; eauto.
      apply not_None_is_Some; eauto.
  Qed.

  Lemma memory_closed_n_Fby:
    forall M eqs x ck v0 e vs,
      memory_closed_n M eqs ->
      memory_closed_n (add_val_n x vs M) (EqFby x ck v0 e :: eqs).
  Proof.
    intros ** WF n; specialize (WF n); destruct WF as (?& Vals).
    split; auto.
    intro y; intros ** Hin.
    unfold add_val_n in Hin; apply not_None_is_Some in Hin as (?& Find).
    destruct (ident_eq_dec y x).
    - subst; simpl; auto.
    - rewrite find_val_gso in Find; auto.
      unfold gather_mems, concatMap; simpl.
      right; apply Vals; eauto.
      apply not_None_is_Some; eauto.
  Qed.


  Lemma sem_msem_eq:
    forall G bk H eqs M M' eq,
      (forall f xs ys,
          sem_node G f xs ys ->
          exists M M', msem_node G f (fun n => false) xs M M' ys) ->
      (forall f r xs ys,
          sem_reset G f r xs ys ->
          exists M M', msem_node G f r xs M M' ys) ->
      sem_equation G bk H eq ->
      NoDup_defs (eq :: eqs) ->
      Forall (msem_equation G bk (fun n => false) (restr_hist H) M M') eqs ->
      memory_closed_n M eqs ->
      memory_closed_n M' eqs ->
      exists M1 M1', Forall (msem_equation G bk (fun n => false) (restr_hist H) M1 M1') (eq :: eqs)
                /\ memory_closed_n M1 (eq :: eqs)
                /\ memory_closed_n M1' (eq :: eqs).
  Proof.
    intros ** IH IH' Heq NoDup Hmeqs WF WF'.
    inversion Heq as [|???????? Hls Hxs Hsem
                         |??????????? Hls Hxs Hy Hr Hsem
                         |???????? Hle Hvar Hfby];
      match goal with H:_=eq |- _ => rewrite <-H in * end.

    - exists M, M'.
      econstructor; eauto.

    - apply IH in Hsem as (Mx & Mx' & Hmsem).
      exists (add_inst_n (hd Ids.default x) Mx M), (add_inst_n (hd Ids.default x) Mx' M').

      assert (exists i, hd_error x = Some i) as [i Hsome].
      { assert (Hlen: 0 < length x).
        { assert (length x = length (xs 0))
            by (specialize (Hxs 0); simpl in Hxs; eapply Forall2_length; eauto).

          assert (exists n, length (map fst n.(n_out)) = length (xs 0)
                       /\ 0 < length n.(n_out)) as (n & ? & ?).
          { inv Hmsem.
            exists node0; split; auto.
            - eapply Forall2_length; eauto.
              specialize (H9 0); eauto.
            - exact node0.(n_outgt0).
          }
          assert (length (map fst n.(n_out)) = length n.(n_out))
            by apply map_length.
          intuition.
        }
        now apply length_hd_error.
      }
      erewrite hd_error_Some_hd; eauto; split.
      + constructor.
        * econstructor; eauto;
            unfold sub_inst, add_inst_n; intro; now apply find_inst_gss.
        * inv NoDup.
          apply hd_error_Some_In in Hsome.
          apply msem_equation_madd_inst; auto.
      + split; apply memory_closed_n_App; auto.

    - pose proof Hsem as Hsem'.
      apply IH' in Hsem as (Mx & Mx' & Hmsem).
      exists (add_inst_n (hd Ids.default x) Mx M), (add_inst_n (hd Ids.default x) Mx' M').

      assert (exists i, hd_error x = Some i) as [i Hsome].
      { assert (Hlen: 0 < length x).
        { assert (length x = length (xs 0))
            by (specialize (Hxs 0); simpl in Hxs; eapply Forall2_length; eauto).

          assert (exists n, length (map fst n.(n_out)) = length (xs 0)
                       /\ 0 < length n.(n_out)) as (n & ? & ?).
          { inv Hmsem.
            exists node0; split; auto.
            - eapply Forall2_length; eauto.
              specialize (H9 0); eauto.
            - exact node0.(n_outgt0).
          }
          assert (length (map fst n.(n_out)) = length n.(n_out))
            by apply map_length.
          intuition.
        }
        now apply length_hd_error.
      }
      erewrite hd_error_Some_hd; eauto; split.
      + constructor.
        * econstructor; eauto;
            try (unfold sub_inst, add_inst_n; intro; now apply find_inst_gss).
          now setoid_rewrite Bool.orb_false_r.
        * inv NoDup.
          apply hd_error_Some_In in Hsome.
          apply msem_equation_madd_inst; auto.
      + split; apply memory_closed_n_App; auto.

    - exists (add_val_n x (hold (sem_const c0) ls) M), (add_val_n x (fun n =>
                                                                  match ls n with
                                                                  | present v => v
                                                                  | absent => hold (sem_const c0) ls n
                                                                  end) M');
        split.
      + constructor.
        * unfold add_val_n.
          econstructor; eauto; split; [|split];
             intros; try rewrite Hfby; unfold fby;
               simpl; repeat rewrite find_val_gss; auto.
          destruct (ls n); auto.
        * inv NoDup.
          apply msem_equation_madd_val; eauto.
      + split; apply memory_closed_n_Fby; auto.
  Qed.

  Lemma memory_closed_empty':
    memory_closed_n (fun _ : nat => empty_memory val) [].
  Proof.
    constructor; simpl.
    - setoid_rewrite find_inst_gempty; congruence.
    - setoid_rewrite find_val_gempty; congruence.
  Qed.

  (* XXX: for this lemma, and the ones before/after it, factorize 'G',
'bk' and possibly other variables in a Section *)
  Corollary sem_msem_eqs:
    forall G bk H eqs,
      (forall f xs ys,
          sem_node G f xs ys ->
          exists M M', msem_node G f (fun n => false) xs M M' ys) ->
      (forall f r xs ys,
          sem_reset G f r xs ys ->
          exists M M', msem_node G f r xs M M' ys) ->
      NoDup_defs eqs ->
      Forall (sem_equation G bk H) eqs ->
      exists M1 M1', Forall (msem_equation G bk (fun n => false) (restr_hist H) M1 M1') eqs
                /\ memory_closed_n M1 eqs
                /\ memory_closed_n M1' eqs.
  Proof.
    intros ** IH NoDup Heqs.
    induction eqs as [|eq eqs IHeqs].
    - exists (fun n => empty_memory _), (fun n => empty_memory _); split; auto.
      split; apply memory_closed_empty'.
    - apply Forall_cons2 in Heqs as [Heq Heqs].
      eapply IHeqs in Heqs as (?&?&?&?&?).
      + eapply sem_msem_eq; eauto.
      + eapply NoDup_defs_cons; eauto.
  Qed.

  Require Import Coq.Logic.ClassicalChoice.
  Require Import Coq.Logic.ConstructiveEpsilon.
  Require Import Coq.Logic.Epsilon.
  Require Import Coq.Logic.IndefiniteDescription.

  (* Check functional_choice. *)

  (* Lemma functional_choice_sig: *)
  (*   forall A B (R: A -> B -> Prop), *)
  (*     (forall x, { y | R x y }) -> *)
  (*     exists f, forall x, R x (f x). *)
  (* Proof. *)
  (*   intros ** Ex. *)
  (*   exists (fun n => proj1_sig (Ex n)). *)
  (*   intro x; destruct (Ex x); auto. *)
  (* Qed. *)

  Require Import Setoid.
  Add Parametric Morphism G: (msem_equation G)
      with signature eq_str ==> eq ==> eq ==> eq ==> eq ==> eq ==> Basics.impl
        as msem_equation_eq_str.
  Proof.
    intros b b' E ** Sem.
    inversion_clear Sem; econstructor; eauto;
      intro; rewrite <-E; auto.
  Qed.

  Add Parametric Morphism G r H M M' eqs: (fun bk => Forall (msem_equation G bk r H M M') eqs)
      with signature eq_str ==> Basics.impl
        as msem_equations_eq_str.
  Proof.
    intros b b' E ** Sem.
    apply Forall_forall; intros ** Hin; eapply Forall_forall in Sem; eauto.
    rewrite <-E; auto.
  Qed.

  (* Ltac interp_sound n := *)
  (*   repeat match goal with *)
  (*          | H: forall n, sem_var_instant ?H' ?x ?vs |- _ => *)
  (*            specialize (H n); apply sem_var_instant_reset in H *)
  (*          | H: sem_vars ?H' ?xs ?vss |- _ => *)
  (*            specialize (H n); apply sem_vars_instant_reset in H *)
  (*          | H: sem_caexp ?bk ?H' ?c ?e ?vs |- _ => *)
  (*            specialize (H n); simpl in H; eapply sem_caexp_instant_reset in H; eauto *)
  (*          | H: sem_laexp ?bk ?H' ?c ?e ?vs |- _ => *)
  (*            specialize (H n); simpl in H; eapply sem_laexp_instant_reset in H; eauto *)
  (*          | H: sem_laexps ?bk ?H' ?c ?es ?vss |- _ => *)
  (*            specialize (H n); simpl in H; eapply sem_laexps_instant_reset in H; eauto *)
  (*          end; *)
  (*   unfold interp_var, interp_vars, interp_laexp, interp_laexps, interp_caexp, lift, lift'; *)
  (*   try erewrite <-interp_caexp_instant_sound; *)
  (*   try erewrite <-interp_laexp_instant_sound; *)
  (*   try erewrite <-interp_laexps_instant_sound; *)
  (*   try erewrite <-interp_var_instant_sound; *)
  (*   try erewrite <-interp_vars_instant_sound; *)
  (*   eauto. *)

  Lemma msem_node_slices:
    forall G f r xs ys F F',
      Ordered_nodes G ->
      (forall k,
          msem_node G f (fun nat => false)
                    (mask (all_absent (xs 0)) k r xs)
                    (F k) (F' k)
                    (mask (all_absent (ys 0)) k r ys)) ->
      msem_node G f r xs (fun n => F (count r n) n) (fun n => F' (count r n) n) ys.
  Proof.
    induction G as [|n]; intros ** Ord Sems;
      try (specialize (Sems 0); inversion_clear Sems as [?????????? Find]; now inv Find).
    assert (exists node, find_node f (n :: G) = Some node) as (node & Find)
        by (specialize (Sems 0); inv Sems; eauto).
    pose proof Find as Find'.
    simpl in Find'.
    destruct (ident_eqb (n_name n) f) eqn: E.
    - inv Find'.
      assert (forall k, exists Hk,
                   let bk := clock_of' (mask (all_absent (xs 0)) k r xs) in
                   (forall n, sem_vars_instant (Hk n) (map fst node.(n_in)) (mask (all_absent (xs 0)) k r xs n))
                   /\ (forall n, sem_vars_instant (Hk n) (map fst node.(n_out)) (mask (all_absent (ys 0)) k r ys n))
                   /\ same_clock (mask (all_absent (xs 0)) k r xs)
                   /\ same_clock (mask (all_absent (ys 0)) k r ys)
                   /\ (forall n, absent_list (mask (all_absent (xs 0)) k r xs n)
                           <-> absent_list (mask (all_absent (ys 0)) k r ys n))
                   /\ (forall n, sem_clocked_vars_instant (bk n) (Hk n) (idck node.(n_in)))
                   /\ Forall (msem_equation (node :: G) bk (fun n => false) Hk (F k) (F' k)) node.(n_eqs)
                   /\ memory_closed_n (F k) node.(n_eqs)
                   /\ memory_closed_n (F' k) node.(n_eqs)) as Node.
      { intro; specialize (Sems k);
          inversion_clear Sems as [????????? Clock Find'];
          rewrite Find' in Find; inv Find; do 2 eexists; intuition; eauto;
            apply clock_of_equiv' in Clock.
        - rewrite <-Clock; auto.
        - eapply msem_equations_eq_str; eauto.
      }
      apply functional_choice in Node as (FH & Node).
      eapply SNode with (H := fun n => FH (count r n) n); eauto;
        try eapply clock_of_equiv;
        try (intro n; specialize (Node (count r n));
           destruct Node as (Ins & Outs & Same & Same' & Abs & VarsCk & ? & Closed & Closed');
           specialize (Ins n); specialize (Outs n);
           specialize (Same n); specialize (Same' n);
           specialize (Abs n); specialize (VarsCk n);
           rewrite mask_transparent in Ins, Outs, Same, Same';
           rewrite 2 mask_transparent in Abs;
           unfold clock_of' in VarsCk; rewrite mask_transparent in VarsCk;
           auto).
      assert (forall k, let bk := clock_of' (mask (all_absent (xs 0)) k r xs) in
                   Forall (msem_equation (node :: G) bk (fun _ : nat => false) (FH k) (F k) (F' k)) (n_eqs node))
        as Heqs by (intro k; destruct (Node k); intuition).
      assert (forall k n, r n = true -> F k n ≋ F k 0) as RstSpec by admit.
      clear - Heqs RstSpec.
      induction (n_eqs node) as [|eq]; constructor; auto.
      + assert (forall k, let bk := clock_of' (mask (all_absent (xs 0)) k r xs) in
                     msem_equation (node :: G) bk (fun _ : nat => false) (FH k) (F k) (F' k) eq) as Heq
            by (intro k; specialize (Heqs k); inv Heqs; auto).
        clear Heqs.
        set (H := fun n : nat => FH (count r n) n).
        set (bk := fun n => clock_of' (mask (all_absent (xs 0)) (count r n) r xs) n).
        assert (forall n, clock_of' xs n = bk n) as Clock
            by (intro; subst bk; simpl; unfold clock_of'; rewrite mask_transparent; auto).
        destruct eq.
        * apply SEqDef with (xs := fun n => interp_caexp_instant (bk n) (H n) c c0);
            intro n; specialize (Heq (count r n)); inv Heq;
              erewrite <-interp_caexp_instant_sound; try rewrite Clock; eauto.
        *{ assert (exists x, hd_error i = Some x) as (x & Hx) by (specialize (Heq 0); inv Heq; eauto).
           assert (exists Fx, forall k, sub_inst_n x (F k) (Fx k)) as (Fx & HMx).
           { assert (forall k, exists Mxk, sub_inst_n x (F k) Mxk) as HMx
               by (intro k; specialize (Heq k);
                   inversion_clear Heq as [|?????????????? Hd|?????????????????? Hd|];
                   rewrite Hd in Hx; inv Hx; eauto).
             apply functional_choice in HMx; auto.
           }
           assert (exists Fx', forall k, sub_inst_n x (F' k) (Fx' k)) as (Fx' & HMx').
           { assert (forall k, exists Mxk, sub_inst_n x (F' k) Mxk) as HMx'
               by (intro k; specialize (Heq k);
                   inversion_clear Heq as [|?????????????? Hd|?????????????????? Hd|];
                   rewrite Hd in Hx; inv Hx; eauto).
             apply functional_choice in HMx'; auto.
           }
           destruct o.
           - eapply SEqReset with (Mx := fun n => Fx (count r n) n)
                                  (Mx' := fun n => Fx' (count r n) n)
                                  (ys := fun n => interp_var_instant (H n) i1)
                                  (xss := fun n => interp_vars_instant (H n) i)
                                  (ls := fun n => interp_laexps_instant (bk n) (H n) c l0)
                                  (rs := fun n => match interp_var_instant (H n) i1 with
                                               | absent => false
                                               | present v => match val_to_bool v with
                                                             | Some b => b
                                                             | None => false
                                                             end
                                               end); eauto;
               try (intro n; specialize (Heq (count r n)); inv Heq;
                    try erewrite <-interp_var_instant_sound;
                    try erewrite <-interp_vars_instant_sound;
                    try erewrite <-interp_laexps_instant_sound;
                    try rewrite Clock; eauto).
             + specialize (HMx (count r n)); auto.
             + specialize (HMx' (count r n)); auto.
             + specialize (H17 n).
               destruct (ys n); simpl; auto.
               simpl in *.
               destruct (val_to_bool c0); auto; discriminate.
             + unfold reset_of in *; eauto.  instantiate (1 := n). specialize (Heq 0); inv Heq; eauto.
             admit.
           - admit.
         }
        *{ apply SEqFby with (xs := fun n => interp_var_instant (H n) i)
                             (ls := fun n => interp_laexp_instant (bk n) (H n) c l0);
           try (intro n; specialize (Heq (count r n)); inv Heq;
                try erewrite <-interp_laexp_instant_sound;
                try erewrite <-interp_var_instant_sound; try rewrite Clock; eauto).
           split.
           - specialize (Heq (count r 0)); inversion_clear Heq as [| | |????????????? (?&?)]; auto.
           - pose proof Heq as Heq'.
             split; intro n; specialize (Heq (count r n));
               inversion_clear Heq as [| | |????????????? (Init & Loop & Spec)].
             + rewrite <-Loop; simpl.
               destruct (r (S n)) eqn: R; auto.
               rewrite RstSpec; auto; symmetry; rewrite RstSpec; auto.
               specialize (Heq' (S (count r n)));
                 inversion_clear Heq' as [| | |????????????? (Init' &?)].
               now rewrite Init, Init'.
             + erewrite <-interp_laexp_instant_sound, <-interp_var_instant_sound; eauto.
               specialize (Spec n).
               destruct (find_val i (F (count r n) n)) eqn: Find; auto.
               destruct (ls n); auto.
               destruct (r n) eqn: R; auto.
               rewrite RstSpec, Init in Find; auto.
               inv Find; auto.
         }
      + apply IHl.
        intro k; specialize (Heqs k); inv Heqs; auto.
    - inv Ord.
      apply msem_node_cons2; auto.
      apply IHG; auto.
      intro k; specialize (Sems k); apply msem_node_cons in Sems;
        auto using Ordered_nodes.
      apply ident_eqb_neq; auto.
  Qed.

  Theorem sem_msem_reset:
    forall G f r xs ys,
      Ordered_nodes G ->
      (forall f xs ys,
          sem_node G f xs ys ->
          exists M M', msem_node G f (fun n => false) xs M M' ys) ->
      sem_reset G f r xs ys ->
      exists M M', msem_node G f r xs M M' ys.
  Proof.
    intros ** IH Sem.
    inversion_clear Sem as [???? Sem'].

    assert (exists F F', forall k, msem_node G f (fun n => false)
                                   (mask (all_absent (xs 0)) k r xs)
                                   (F k) (F' k)
                                   (mask (all_absent (ys 0)) k r ys))
      as (F & F' & Msem).
    { assert (forall k, exists Mk Mk', msem_node G f (fun n => false)
                                       (mask (all_absent (xs 0)) k r xs)
                                       Mk Mk'
                                       (mask (all_absent (ys 0)) k r ys)) as Msem'
          by (intro; specialize (Sem' k); apply IH in Sem'; auto).
      (** Infinite Description  *)
      do 2 apply functional_choice in Msem' as (?&Msem'); eauto.

      (** Epsilon  *)
      (* assert (inhabited memories) as I *)
      (*     by (constructor; exact (fun n => @empty_memory val)). *)
      (* exists (fun n => epsilon *)
      (*            I (fun M => msem_node G f (mask (all_absent (xs 0)) n r xs) M *)
      (*                               (mask (all_absent (ys 0)) n r ys))). *)
      (* intro; now apply epsilon_spec.  *)

      (** Constructive Epsilon  *)
      (* pose proof (constructive_ground_epsilon memories) as F. *)

      (** Classical Choice  *)
      (* now apply choice in Msem'.   *)
    }
    exists (fun n => F (count r n) n), (fun n => F' (count r n) n).
    apply msem_node_slices; auto.
  Qed.


  Theorem sem_msem_node:
    forall G f xs ys,
      Ordered_nodes G ->
      sem_node G f xs ys ->
      exists M M', msem_node G f (fun n => false) xs M M' ys.
  Proof.
    induction G as [|node].
    inversion 2;
      match goal with Hf: find_node _ [] = _ |- _ => inversion Hf end.
    intros ** Hord Hsem.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [??????? Hfind ?????? Heqs].
    pose proof (find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    pose proof Hfind.
    simpl in Hfind.
    destruct (ident_eqb node.(n_name) f) eqn:Hnf.
    - assert (Hord':=Hord).
      inversion_clear Hord as [|? ? Hord'' Hnneqs Hnn].
      inv Hfind.
      eapply Forall_sem_equation_global_tl in Heqs; eauto.
      assert (forall f xs ys,
                 sem_node G f xs ys ->
                 exists M M', msem_node G f (fun n => false) xs M M' ys) as IHG'
          by auto.
      assert (forall f r xs ys,
                 sem_reset G f r xs ys ->
                 exists M M', msem_node G f r xs M M' ys) as IHG''
          by (intros; now apply sem_msem_reset).
      assert (exists M1 M1', Forall (msem_equation G bk (fun n => false) H M1 M1') n.(n_eqs)
                        /\ memory_closed_n M1 n.(n_eqs)
                        /\ memory_closed_n M1' n.(n_eqs))
        as (M1 & M1' & Hmsem & ?&?)
          by (eapply sem_msem_eqs; eauto; apply NoDup_defs_node).
      exists M1, M1'.
      econstructor; eauto.
      rewrite <-msem_equations_cons; eauto.
    - apply ident_eqb_neq in Hnf.
      apply sem_node_cons with (1:=Hord) (3:=Hnf) in Hsem.
      inv Hord.
      eapply IHG in Hsem as (M & M' &?); eauto.
      exists M, M'.
      now eapply msem_node_cons2; eauto.
  Qed.

  (* We use the mem-semantics to assert the absence of applications
  with no return arguments. This is a bit of a hack, if you ask me. So
  don't ask. *)
  Lemma non_trivial_EqApp:
    forall G bk H M M' eqs ,
      Forall (msem_equation G bk H M M') eqs ->
      forall ck f les y, ~ In (EqApp [] ck f les y) eqs.
  Proof.
    induction eqs; intros ** Hsem ? ? ? ? Hin.
    - match goal with
      | H: In _ [] |- _ => inv H
      end.
    - destruct Hin as [Hin_eq | Hin_eqs ]; subst.
      + inversion_clear Hsem as [ | ? ? Hsem_eq ];
      inv Hsem_eq; discriminate.
      + eapply IHeqs. inv Hsem; auto.
        repeat eexists. eauto.
  Qed.


  (** Initial memory *)

  Lemma memory_closed_empty:
    forall M, memory_closed M [] -> M ≋ empty_memory _.
  Proof.
    intros ** (Insts & Vals); unfold find_val, find_inst in *.
    constructor; simpl in *.
    - intro x.
      assert (Env.find x (values M) = None) as ->.
      { apply not_Some_is_None; intros ** E.
        eapply Vals, not_None_is_Some; eauto.
      }
      now rewrite Env.gempty.
    - split.
      + setoid_rewrite Env.Props.P.F.empty_in_iff; setoid_rewrite Env.In_find; split; try contradiction.
        intros (?&?); eapply Insts, not_None_is_Some; eauto.
      + setoid_rewrite Env.Props.P.F.empty_mapsto_iff; contradiction.
  Qed.

  Definition remove_inst_n (x: ident) (M: memories) : memories :=
    fun n => remove_inst x (M n).

  Definition remove_val_n (x: ident) (M: memories) : memories :=
    fun n => remove_val x (M n).

  Lemma msem_equation_remove_inst:
    forall G bk eqs H M M' x,
      ~Is_defined_in_eqs x eqs ->
      Forall (msem_equation G bk H M M') eqs ->
      Forall (msem_equation G bk H (remove_inst_n x M) (remove_inst_n x M')) eqs.
  Proof.
    Ltac foo H := unfold sub_inst_n, sub_inst in *; intro n;
                setoid_rewrite find_inst_gro; auto;
                intro E; subst; apply H;
                constructor;
                apply hd_error_Some_In; auto.
    induction eqs as [|[]]; intros ** Hnotin Sems;
      inversion_clear Sems as [|?? Sem]; auto; inversion_clear Sem;
        apply not_Is_defined_in_cons in Hnotin as (Hnotin &?);
        constructor; eauto using msem_equation;
          econstructor; eauto; foo Hnotin.
  Qed.

  Lemma msem_equation_remove_val:
    forall G bk eqs H M M' x,
      ~Is_defined_in_eqs x eqs ->
      Forall (msem_equation G bk H M M') eqs ->
      Forall (msem_equation G bk H (remove_val_n x M) (remove_val_n x M')) eqs.
  Proof.
    induction eqs as [|[]]; intros ** Hnotin Sems;
      inversion_clear Sems as [|?? Sem]; auto;
        inversion_clear Sem as [| | |???????????? Mfby];
        apply not_Is_defined_in_cons in Hnotin as (Hnotin &?);
        constructor; eauto using msem_equation.
    assert (x <> i) by (intro E; subst; apply Hnotin; constructor).
    destruct Mfby as (?&?& Spec).
    econstructor; eauto; unfold remove_val_n.
    split; [|split]; intros; repeat rewrite find_val_gro; auto.
    apply Spec.
  Qed.

  Lemma memory_closed_n_App':
    forall M eqs i xs ck f es r,
      memory_closed_n M (EqApp xs ck f es r :: eqs) ->
      hd_error xs = Some i ->
      memory_closed_n (remove_inst_n i M) eqs.
  Proof.
    intros ** WF Hd n; specialize (WF n); destruct WF as (Insts &?).
    split; auto.
    intro y; intros ** Hin.
    unfold sub_inst, remove_inst_n in Hin; apply not_None_is_Some in Hin as (?& Find).
    destruct (ident_eq_dec y i).
    - subst; rewrite find_inst_grs in Find; discriminate.
    - rewrite find_inst_gro in Find; auto.
      unfold gather_insts, concatMap in Insts; simpl in Insts.
      destruct xs; simpl in *; inv Hd.
      edestruct Insts.
      + apply not_None_is_Some; eauto.
      + congruence.
      + auto.
  Qed.

  Lemma memory_closed_n_Fby':
    forall M eqs x ck v0 e,
      memory_closed_n M (EqFby x ck v0 e :: eqs) ->
      memory_closed_n (remove_val_n x M) eqs.
  Proof.
    intros ** WF n; specialize (WF n); destruct WF as (?& Vals).
    split; auto.
    intro y; intros ** Hin.
    unfold remove_val_n in Hin; apply not_None_is_Some in Hin as (?& Find).
    destruct (ident_eq_dec y x).
    - subst; rewrite find_val_grs in Find; discriminate.
    - rewrite find_val_gro in Find; auto.
      unfold gather_mems, concatMap in Vals; simpl in Vals.
      edestruct Vals.
      + apply not_None_is_Some; eauto.
      + congruence.
      + auto.
  Qed.

  Lemma msem_eqs_same_initial_memory:
    forall M1 M1' G eqs bk1 H1 M2 M2' bk2 H2,
    (forall f xss1 M1 M1' yss1 xss2 M2 M2' yss2,
        msem_node G f xss1 M1 M1' yss1 ->
        msem_node G f xss2 M2 M2' yss2 ->
        M1 0 ≋ M2 0) ->
    NoDup_defs eqs ->
    memory_closed_n M1 eqs ->
    memory_closed_n M2 eqs ->
    Forall (msem_equation G bk1 H1 M1 M1') eqs ->
    Forall (msem_equation G bk2 H2 M2 M2') eqs ->
    M1 0 ≋ M2 0.
  Proof.
    intros ** IH Nodup Closed1 Closed2 Heqs1 Heqs2.
    revert dependent M1; revert dependent M2; revert M1' M2'.
    induction eqs as [|[] ? IHeqs]; intros;
      inversion_clear Heqs1 as [|?? Sem1 Sems1];
      inversion_clear Heqs2 as [|?? Sem2 Sems2];
      try inversion Sem1 as [|
                                   ????????????? Hd1 ???? Node|
                                   ???????????????? Hd1 ?? Args1 ??? Reset1|
                                   ?????????? Arg1 ? Mfby1];
      try inversion Sem2 as [|
                                   ????????????? Hd2|
                                   ???????????????? Hd2 ?? Args2 ??? Reset2|
                                   ?????????? Arg2 ? Mfby2];
      inv Nodup; subst; try discriminate; eauto.
    - assert (forall n, M1 n ≋ empty_memory _) as ->
          by (intro; apply memory_closed_empty; auto).
      assert (forall n, M2 n ≋ empty_memory _) as ->
          by (intro; apply memory_closed_empty; auto).
      reflexivity.

    - rewrite Hd2 in Hd1; inv Hd1.
      assert (~ Is_defined_in_eqs x eqs)
        by (apply hd_error_Some_In in Hd2; auto).
      apply msem_equation_remove_inst with (x := x) in Sems1;
        apply msem_equation_remove_inst with (x := x) in Sems2; auto.
      eapply IHeqs in Sems1; eauto; try eapply memory_closed_n_App'; eauto.
      erewrite add_remove_inst_same; eauto;
        symmetry; erewrite add_remove_inst_same; eauto.
      rewrite Sems1.
      eapply IH in Node; eauto.
      now rewrite Node.

    - rewrite Hd2 in Hd1; inv Hd1.
      assert (~ Is_defined_in_eqs x eqs)
        by (apply hd_error_Some_In in Hd2; auto).
      apply msem_equation_remove_inst with (x := x) in Sems1;
        apply msem_equation_remove_inst with (x := x) in Sems2; auto.
      eapply IHeqs in Sems1; eauto; try eapply memory_closed_n_App'; eauto.
      erewrite add_remove_inst_same; eauto;
        symmetry; erewrite add_remove_inst_same; eauto.
      rewrite Sems1.
      inversion_clear Reset1 as [?????? Nodes1];
        inversion_clear Reset2 as [?????? Nodes2].
      destruct (Nodes1 (count rs 0)) as (M01 &?& Node1 & MemMask1 &?),
                                        (Nodes2 (count rs0 0)) as (M02 &?&?& MemMask2 &?).
      eapply IH in Node1; eauto.
      now rewrite <-MemMask1, <-MemMask2, Node1; auto.

    - apply msem_equation_remove_val with (x := i) in Sems1;
        apply msem_equation_remove_val with (x := i) in Sems2; auto.
      eapply IHeqs in Sems1; eauto; try eapply memory_closed_n_Fby'; eauto.
      destruct Mfby1, Mfby2.
      erewrite add_remove_val_same; eauto;
        symmetry; erewrite add_remove_val_same; eauto.
      now rewrite Sems1.
  Qed.

  Theorem same_initial_memory:
    forall G f xss1 xss2 M1 M2 M1' M2' yss1 yss2,
      Ordered_nodes G ->
      msem_node G f xss1 M1 M1' yss1 ->
      msem_node G f xss2 M2 M2' yss2 ->
      M1 0 ≋ M2 0.
  Proof.
    induction G as [|node].
    inversion 2;
      match goal with Hf: find_node _ [] = _ |- _ => inversion Hf end.
    intros ** Hord Hsem1 Hsem2.
    assert (Hsem1' := Hsem1);  assert (Hsem2' := Hsem2).
    inversion_clear Hsem1' as [???????? Clock1 Hfind1 Ins1 ????? Heqs1];
      inversion_clear Hsem2' as [???????? Clock2 Hfind2 Ins2 ????? Heqs2].
    rewrite Hfind2 in Hfind1; inv Hfind1.
    pose proof Hord; inv Hord.
    pose proof Hfind2.
    simpl in Hfind2.
    destruct (ident_eqb node.(n_name) f) eqn:Hnf.
    - inv Hfind2.
      assert (~ Is_node_in (n_name n) (n_eqs n)) by (eapply find_node_not_Is_node_in; eauto).
      eapply msem_equations_cons in Heqs1; eauto.
      eapply msem_equations_cons in Heqs2; eauto.
      eapply msem_eqs_same_initial_memory; eauto.
      apply NoDup_defs_node.
    - assert (n_name node <> f) by now apply ident_eqb_neq.
      eapply msem_node_cons in Hsem1; eapply msem_node_cons in Hsem2; eauto.
  Qed.


  (** Absent Until *)

  Lemma mfby_absent_until:
    forall n0 x v0 ls M M' xs,
      mfby x v0 ls M M' xs ->
      (forall n, n < n0 -> ls n = absent) ->
      forall n, n <= n0 -> find_val x (M n) = Some v0.
  Proof.
    intros ** Mfby Abs n E; induction n;
      destruct Mfby as (Init & Spec & Spec'); auto.
    rewrite Spec.
    specialize (Spec' n).
    destruct (find_val x (M n)); try contradiction.
    rewrite Abs in Spec'; try omega.
    destruct Spec' as [->].
    apply IHn; omega.
  Qed.

  Lemma msem_eqs_absent_until:
    forall M M' G n0 eqs bk H n,
    (forall f xss M M' yss,
        msem_node G f xss M M' yss ->
        (forall n, n < n0 -> absent_list (xss n)) ->
        forall n, n <= n0 -> M n ≋ M 0) ->
    Ordered_nodes G ->
    n <= n0 ->
    (forall n, n < n0 -> bk n = false) ->
    NoDup_defs eqs ->
    memory_closed_n M eqs ->
    Forall (msem_equation G bk H M M') eqs ->
    M n ≋ M 0.
  Proof.
    intros ** IH Hord Spec Absbk Nodup Closed Heqs.
    revert dependent M; revert dependent M'.
    induction eqs as [|[] ? IHeqs]; intros;
      inversion_clear Heqs as [|?? Sem Sems];
      try inversion_clear Sem as [|
                                  ????????????? Hd ?? Args ? Node|
                                  ???????????????? Hd ?? Args ??? Reset|
                                  ?????????? Arg ? Mfby];
      inv Nodup; eauto.
    - assert (forall n, M n ≋ empty_memory _) as E
          by (intro; apply memory_closed_empty; auto).
     rewrite 2 E; reflexivity.

    - apply msem_equation_remove_inst with (x := x) in Sems.
      + apply IHeqs in Sems; auto.
        *{ apply IH with (n := n) in Node; auto.
           - erewrite add_remove_inst_same; eauto;
               symmetry; erewrite add_remove_inst_same; eauto.
             now rewrite Sems, Node.
           - intros k ** Spec'; specialize (Args k); simpl in Args.
             rewrite Absbk in Args; auto.
             inversion_clear Args as [?????? SClock|??? ->].
             + contradict SClock; apply not_subrate_clock.
             + apply all_absent_spec.
         }
        * eapply memory_closed_n_App'; eauto.
      + apply hd_error_Some_In in Hd; auto.

    - apply msem_equation_remove_inst with (x := x) in Sems.
      + apply IHeqs in Sems; auto.
        *{ inversion_clear Reset as [?????? Nodes].
           destruct (Nodes (count rs n)) as (Mn &?& Node_n & MemMask_n & MemMask_n'),
                                            (Nodes (count rs 0)) as (M0 &?&?& MemMask_0 &?).
           assert (Mn 0 ≋ M0 0) as E by (eapply same_initial_memory; eauto).
           apply IH with (n := n) in Node_n; auto.
           - erewrite add_remove_inst_same; eauto;
               symmetry; rewrite add_remove_inst_same; eauto.
             rewrite Sems, <-(MemMask_n n), <-(MemMask_0 0), Node_n, E; reflexivity.
           - intros k ** Spec'; specialize (Args k); simpl in Args.
             rewrite Absbk in Args; auto.
             inversion_clear Args as [?????? SClock|??? E'].
             + contradict SClock; apply not_subrate_clock.
             + apply absent_list_mask; try rewrite E'; apply all_absent_spec.
         }
        * eapply memory_closed_n_App'; eauto.
      + apply hd_error_Some_In in Hd; auto.

    - apply msem_equation_remove_val with (x := i) in Sems; auto.
      apply IHeqs in Sems; auto.
      + assert (find_val i (M n) = Some (sem_const c0)).
        { eapply mfby_absent_until; eauto.
          intros k ** Spec'; specialize (Arg k); simpl in Arg.
          rewrite Absbk in Arg; auto.
          inversion_clear Arg as [???? SClock|]; auto.
          contradict SClock; apply not_subrate_clock.
        }
        destruct Mfby as (Init & Loop & Spec').
        erewrite add_remove_val_same; eauto;
          symmetry; erewrite add_remove_val_same; eauto.
        now rewrite Sems.
      + eapply memory_closed_n_Fby'; eauto.
  Qed.

  Theorem msem_node_absent_until:
    forall n0 G f xss M M' yss,
      Ordered_nodes G ->
      msem_node G f xss M M' yss ->
      (forall n, n < n0 -> absent_list (xss n)) ->
      forall n, n <= n0 -> M n ≋ M 0.
  Proof.
    induction G as [|node].
    inversion 2;
      match goal with Hf: find_node _ [] = _ |- _ => inversion Hf end.
    intros ** Hord Hsem Abs n Spec.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [???????? Clock Hfind Ins ????? Heqs].
    assert (forall n, n < n0 -> bk n = false) as Absbk.
    { intros k Spec'; apply Abs in Spec'.
      rewrite <-Bool.not_true_iff_false.
      intro E; apply Clock in E.
      specialize (Ins k).
      apply Forall2_length in Ins.
      destruct (xss k).
      - rewrite map_length in Ins; simpl in Ins.
        pose proof (n_ingt0 n1); omega.
      - inv Spec'; inv E;  congruence.
    }
    pose proof (find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    pose proof Hord; inv Hord.
    pose proof Hfind.
    simpl in Hfind.
    destruct (ident_eqb node.(n_name) f) eqn:Hnf.
    - inv Hfind.
      eapply msem_equations_cons in Heqs; eauto.
      eapply msem_eqs_absent_until; eauto.
      apply NoDup_defs_node.
    - eapply msem_node_cons in Hsem; eauto.
      now apply ident_eqb_neq.
  Qed.

  Theorem msem_reset_spec:
    forall G f r xs M' M ys,
      Ordered_nodes G ->
      msem_reset G f r xs M M' ys ->
      forall n, r n = true -> M n ≋ M 0.
  Proof.
    inversion_clear 2 as [?????? Nodes].
    intros ** Hr.
    destruct (Nodes (count r n)) as (Mn & ? & Node_n & Mmask_n &?),
                                    (Nodes (count r 0)) as (M0 & ? & Node_0 & Mmask_0 &?).
    rewrite <-Mmask_n, <-Mmask_0; auto.
    assert (M0 0 ≋ Mn 0) as -> by (eapply same_initial_memory; eauto).
    eapply msem_node_absent_until; eauto.
    intros ** Spec.
    rewrite mask_opaque.
    - apply all_absent_spec.
    - eapply count_positive in Spec; eauto; omega.
  Qed.

  (** Absent  *)

  Lemma mfby_absent:
    forall n x v0 ls M M' xs,
      mfby x v0 ls M M' xs ->
      ls n = absent ->
      find_val x (M' n) = find_val x (M n).
  Proof.
    induction n; intros ** Mfby Abs;
      destruct Mfby as (Init & Spec & Spec').
    - specialize (Spec' 0); rewrite Init, Abs in Spec'.
      intuition; congruence.
    - (* rewrite Spec. *)
      specialize (Spec' (S n)).
      destruct (find_val x (M (S n))); try contradiction.
      rewrite Abs in Spec'.
      intuition.
  Qed.

  Lemma msem_eqs_absent:
    forall M M' G eqs bk H n,
    (forall f xss M M' yss n,
        msem_node G f xss M M' yss ->
        absent_list (xss n) ->
        M' n ≋ M n) ->
    Ordered_nodes G ->
    bk n = false ->
    NoDup_defs eqs ->
    memory_closed_n M eqs ->
    memory_closed_n M' eqs ->
    Forall (msem_equation G bk H M M') eqs ->
    M' n ≋ M n.
  Proof.
    intros ** IH Hord Absbk Nodup Closed Closed' Heqs.
    revert dependent M; revert dependent M'.
    induction eqs as [|[] ? IHeqs]; intros;
      inversion_clear Heqs as [|?? Sem Sems];
      try inversion_clear Sem as [|
                                  ????????????? Hd ?? Args ? Node|
                                  ???????????????? Hd ?? Args ??? Reset|
                                  ?????????? Arg ? Mfby];
      inv Nodup; eauto.
    - assert (forall n, M n ≋ empty_memory _) as E
          by (intro; apply memory_closed_empty; auto).
     assert (forall n, M' n ≋ empty_memory _) as E'
          by (intro; apply memory_closed_empty; auto).
     rewrite E, E'; reflexivity.

    - apply msem_equation_remove_inst with (x := x) in Sems.
      + apply IHeqs in Sems; try eapply memory_closed_n_App'; eauto.
        apply IH with (n := n) in Node; auto.
        * erewrite add_remove_inst_same; eauto;
            symmetry; erewrite add_remove_inst_same; eauto.
          now rewrite Sems, Node.
        * specialize (Args n); simpl in Args.
          rewrite Absbk in Args.
          inversion_clear Args as [?????? SClock|??? ->]; try apply all_absent_spec.
          contradict SClock; apply not_subrate_clock.
      + apply hd_error_Some_In in Hd; auto.

    - apply msem_equation_remove_inst with (x := x) in Sems.
      + apply IHeqs in Sems; try eapply memory_closed_n_App'; eauto.
        inversion_clear Reset as [?????? Nodes].
        destruct (Nodes (count rs n)) as (Mn &?& Node_n & MemMask_n & MemMask_n').
        apply IH with (n := n) in Node_n; auto.
        * erewrite add_remove_inst_same; eauto;
            symmetry; rewrite add_remove_inst_same; eauto.
          rewrite Sems, <-(MemMask_n n), <-(MemMask_n' n), Node_n; reflexivity.
        *{ specialize (Args n); simpl in Args.
           rewrite Absbk in Args.
           inversion_clear Args as [?????? SClock|??? E'].
           - contradict SClock; apply not_subrate_clock.
           - apply absent_list_mask; try rewrite E'; apply all_absent_spec.
         }
      + apply hd_error_Some_In in Hd; auto.

    - apply msem_equation_remove_val with (x := i) in Sems; auto.
      apply IHeqs in Sems; try eapply memory_closed_n_Fby'; eauto.
      assert (find_val i (M' n) = find_val i (M n)) as E.
      { eapply mfby_absent; eauto.
        specialize (Arg n); simpl in Arg.
        rewrite Absbk in Arg.
        inversion_clear Arg as [???? SClock|]; auto.
        contradict SClock; apply not_subrate_clock.
      }
      destruct Mfby as (Init & Loop & Spec').
      specialize (Spec' n).
      destruct (find_val i (M' n)) eqn: Eq', (find_val i (M n)) eqn: Eq;
        try contradiction; inv E.
      erewrite add_remove_val_same; eauto;
        symmetry; erewrite add_remove_val_same; eauto.
      now rewrite Sems.
  Qed.

  Theorem msem_node_absent:
    forall G f xss M M' yss n,
      Ordered_nodes G ->
      msem_node G f xss M M' yss ->
      absent_list (xss n) ->
      M' n ≋ M n.
  Proof.
    induction G as [|node].
    inversion 2;
      match goal with Hf: find_node _ [] = _ |- _ => inversion Hf end.
    intros ** Hord Hsem Abs.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [???????? Clock Hfind Ins ????? Heqs].
    assert (bk n = false) as Absbk.
    { rewrite <-Bool.not_true_iff_false.
      intro E; apply Clock in E.
      specialize (Ins n).
      apply Forall2_length in Ins.
      destruct (xss n).
      - rewrite map_length in Ins; simpl in Ins.
        pose proof (n_ingt0 n0); omega.
      - inv E; inv Abs; congruence.
    }
    pose proof (find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    pose proof Hord; inv Hord.
    pose proof Hfind.
    simpl in Hfind.
    destruct (ident_eqb node.(n_name) f) eqn:Hnf.
    - inv Hfind.
      eapply msem_equations_cons in Heqs; eauto.
      eapply msem_eqs_absent; eauto.
      apply NoDup_defs_node.
    - eapply msem_node_cons in Hsem; eauto.
      now apply ident_eqb_neq.
  Qed.

  (** The other way around  *)

  Lemma mfby_fby:
    forall x v0 es M M' xs,
      mfby x v0 es M M' xs ->
      xs ≈ fby v0 es.
  Proof.
    intros ** (Init & Loop & Spec) n.
    unfold fby.
    pose proof (Spec n) as Spec'.
    destruct (find_val x (M n)) eqn: Find_n; try contradiction.
    destruct (es n); destruct Spec' as (?& Hx); auto.
    rewrite Hx.
    clear - Init Loop Spec Find_n.
    revert dependent v.
    induction n; intros; simpl; try congruence.
    specialize (Spec n).
    destruct (find_val x (M n)); try contradiction.
    rewrite Loop in Find_n.
    destruct (es n); destruct Spec; try congruence.
    apply IHn; congruence.
  Qed.

  Theorem msem_sem_node_equation_reset:
    forall G,
      (forall f xss M M' yss,
          msem_node G f xss M M' yss ->
          sem_node G f xss yss)
      /\
      (forall bk H M M' eq,
          msem_equation G bk H M M' eq ->
          sem_equation G bk H eq)
      /\
      (forall f r xss M M' yss,
          msem_reset G f r xss M M' yss ->
          sem_reset G f r xss yss).
  Proof.
    intros; apply msem_node_equation_reset_ind;
      [intros|intros|intros|intros|intros ?????? IH|intros];
      eauto using sem_equation, mfby_fby, sem_node.
    constructor; intro; destruct (IH k) as (?&?&?); intuition.
  Qed.

  Corollary msem_sem_node:
    forall G f xss M M' yss,
      msem_node G f xss M M' yss ->
      sem_node G f xss yss.
  Proof.
    intros; eapply (proj1 (msem_sem_node_equation_reset G)); eauto.
  Qed.

  Corollary msem_sem_equation:
    forall G bk H M M' eq,
      msem_equation G bk H M M' eq ->
      sem_equation G bk H eq.
  Proof.
    intros; eapply (proj1 (proj2 (msem_sem_node_equation_reset G))); eauto.
  Qed.

  Corollary msem_sem_equations:
    forall G bk H M M' eqs,
      Forall (msem_equation G bk H M M') eqs ->
      Forall (sem_equation G bk H) eqs.
  Proof.
    induction 1; constructor; eauto using msem_sem_equation.
  Qed.

End MEMSEMANTICS.

Module MemSemanticsFun
       (Ids     : IDS)
       (Op      : OPERATORS)
       (OpAux   : OPERATORS_AUX   Op)
       (Clks    : CLOCKS          Ids)
       (ExprSyn : NLEXPRSYNTAX        Op)
       (Syn     : NLSYNTAX        Ids Op       Clks ExprSyn)
       (Str     : STREAM              Op OpAux)
       (Ord     : ORDERED         Ids Op       Clks ExprSyn Syn)
       (ExprSem : NLEXPRSEMANTICS Ids Op OpAux Clks ExprSyn     Str)
       (Sem     : NLSEMANTICS     Ids Op OpAux Clks ExprSyn Syn Str Ord ExprSem)
       (Mem     : MEMORIES        Ids Op       Clks ExprSyn Syn)
       (IsD     : ISDEFINED       Ids Op       Clks ExprSyn Syn                 Mem)
       (IsV     : ISVARIABLE      Ids Op       Clks ExprSyn Syn                 Mem IsD)
       (IsF     : ISFREE          Ids Op       Clks ExprSyn Syn)
       (NoD     : NODUP           Ids Op       Clks ExprSyn Syn                 Mem IsD IsV)
       <: MEMSEMANTICS Ids Op OpAux Clks ExprSyn Syn Str Ord ExprSem Sem Mem IsD IsV IsF NoD.
  Include MEMSEMANTICS Ids Op OpAux Clks ExprSyn Syn Str Ord ExprSem Sem Mem IsD IsV IsF NoD.
End MemSemanticsFun.
