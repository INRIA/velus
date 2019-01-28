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
       (Import Mem     : MEMORIES        Ids Op       Clks ExprSyn Syn)
       (Import IsD     : ISDEFINED       Ids Op       Clks ExprSyn Syn                 Mem)
       (Import IsV     : ISVARIABLE      Ids Op       Clks ExprSyn Syn                 Mem IsD)
       (Import IsF     : ISFREE          Ids Op       Clks ExprSyn Syn)
       (Import NoD     : NODUP           Ids Op       Clks ExprSyn Syn                 Mem IsD IsV).

  Definition memories := stream (memory val).

  Definition memory_masked (k: nat) (rs: cstream) (M M': memories) :=
    forall n, count rs n = k -> M' n = M n.

  Definition mfby (x: ident) (c0: val) (xs: stream value) (M M': memories) (ys: stream value) : Prop :=
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
               /\ ys n = present mv
             end
           | None => False
           end.

  Section NodeSemantics.

    Definition sub_inst_n (x: ident) (M M': memories) : Prop :=
      forall n, sub_inst x (M n) (M' n).

    Variable G: global.

    (* Inductive well_formed_memory: memory val -> ident -> Prop := *)
    (*   well_formed_memory_intro: *)
    (*     forall M f n, *)
    (*       find_node f G = Some n -> *)
    (*       (forall i M', sub_inst i M M' -> *)
    (*                exists f', In (i, f') (gather_insts n.(n_eqs)) *)
    (*                      /\ well_formed_memory M' f') -> *)
    (*       (forall i f', In (i, f') (gather_insts n.(n_eqs)) -> *)
    (*                exists M', sub_inst i M M' *)
    (*                      /\ well_formed_memory M' f') -> *)
    (*       (forall x, (exists v, find_val x M = Some v) <-> In x (gather_mem n.(n_eqs))) -> *)
    (*       well_formed_memory M f. *)

    (* Definition well_formed_memory_n (M: memories) (f: ident) : Prop := *)
    (*   forall n, well_formed_memory (M n) f. *)

    Definition memory_closed (M: memory val) (eqs: list equation) : Prop :=
      (forall i, find_inst i M <> None -> InMembers i (gather_insts eqs))
      /\ forall x, find_val x M <> None -> In x (gather_mem eqs).

    Definition memory_closed_n (M: memories) (eqs: list equation) : Prop :=
      forall n, memory_closed (M n) eqs.

    Inductive msem_equation: stream bool -> history -> memories -> memories -> equation -> Prop :=
    | SEqDef:
        forall bk H M M' x ck xs ce,
          sem_var H x xs ->
          sem_caexp bk H ck ce xs ->
          msem_equation bk H M M' (EqDef x ck ce)
    | SEqApp:
        forall bk H M M' x xs ck f Mx Mx' arg ls xss,
          hd_error xs = Some x ->
          sub_inst_n x M Mx ->
          sub_inst_n x M' Mx' ->
          sem_laexps bk H ck arg ls ->
          sem_vars H xs xss ->
          msem_node f ls Mx Mx' xss ->
          msem_equation bk H M M' (EqApp xs ck f arg None)
    | SEqReset:
        forall bk H M M' x xs ck f Mx Mx' arg r ck_r ys rs ls xss,
          hd_error xs = Some x ->
          sub_inst_n x M Mx ->
          sub_inst_n x M' Mx' ->
          sem_laexps bk H ck arg ls ->
          sem_vars H xs xss ->
          (* sem_avar bk H ck_r r ys -> *)
          sem_var H r ys ->
          reset_of ys rs ->
          msem_reset f rs ls Mx Mx' xss ->
          msem_equation bk H M M' (EqApp xs ck f arg (Some (r, ck_r)))
    | SEqFby:
        forall bk H M M' x ck ls xs c0 le,
          sem_laexp bk H ck le ls ->
          sem_var H x xs ->
          mfby x (sem_const c0) ls M M' xs ->
          msem_equation bk H M M' (EqFby x ck c0 le)

    with msem_reset:
           ident -> stream bool -> stream (list value) -> memories -> memories -> stream (list value) -> Prop :=
         | SReset:
             forall f r xss M M' yss,
               (forall k, exists Mk Mk',
                     msem_node f (mask (all_absent (xss 0)) k r xss)
                               Mk Mk'
                               (mask (all_absent (yss 0)) k r yss)
                     /\ memory_masked k r M Mk
                     /\ memory_masked k r M' Mk') ->
               msem_reset f r xss M M' yss

    with msem_node:
           ident -> stream (list value) -> memories -> memories -> stream (list value) -> Prop :=
         | SNode:
             forall bk H f xss M M' yss n,
               clock_of xss bk ->
               find_node f G = Some n ->
               sem_vars H (map fst n.(n_in)) xss ->
               sem_vars H (map fst n.(n_out)) yss ->
               same_clock xss ->
               same_clock yss ->
               (forall n, absent_list (xss n) <-> absent_list (yss n)) ->
               Forall (msem_equation bk H M M') n.(n_eqs) ->
               memory_closed_n M n.(n_eqs) ->
               msem_node f xss M M' yss.

    Definition msem_equations bk H M M' eqs := Forall (msem_equation bk H M M') eqs.

  End NodeSemantics.

  (** ** Induction principle for [msem_equation] and [msem_node] *)

  (** The automagically-generated induction principle is not strong
enough: it does not support the internal fixpoint introduced by
[Forall] *)

  Section msem_node_mult.

    Variable G: global.

    Variable P_equation: stream bool -> history -> memories -> memories -> equation -> Prop.
    Variable P_reset: ident -> stream bool -> stream (list value) -> memories -> memories -> stream (list value) -> Prop.
    Variable P_node: ident -> stream (list value) -> memories -> memories -> stream (list value) -> Prop.

    Hypothesis EqDefCase:
      forall bk H M M' x ck xs ce,
        sem_var H x xs ->
        sem_caexp bk H ck ce xs ->
        P_equation bk H M M' (EqDef x ck ce).

    Hypothesis EqAppCase:
      forall bk H M M' x xs ck f Mx Mx' arg ls xss,
        Some x = hd_error xs ->
        sub_inst_n x M Mx ->
        sub_inst_n x M' Mx' ->
        sem_laexps bk H ck arg ls ->
        sem_vars H xs xss ->
        msem_node G f ls Mx Mx' xss ->
        P_node f ls Mx Mx' xss ->
        P_equation bk H M M' (EqApp xs ck f arg None).

    Hypothesis EqResetCase:
      forall bk H M M' x xs ck f Mx Mx' arg r ck_r ys rs ls xss,
        Some x = hd_error xs ->
        sub_inst_n x M Mx ->
        sub_inst_n x M' Mx' ->
        sem_laexps bk H ck arg ls ->
        sem_vars H xs xss ->
        (* sem_avar bk H ck_r r ys -> *)
        sem_var H r ys ->
        reset_of ys rs ->
        msem_reset G f rs ls Mx Mx' xss ->
        P_reset f rs ls Mx Mx' xss ->
        P_equation bk H M M' (EqApp xs ck f arg (Some (r, ck_r))).

    Hypothesis EqFbyCase:
      forall bk H M M' x ck ls xs c0 le,
        sem_laexp bk H ck le ls ->
        sem_var H x xs ->
        mfby x (sem_const c0) ls M M' xs ->
        P_equation bk H M M' (EqFby x ck c0 le).

    Hypothesis ResetCase:
      forall f r xss M M' yss,
        (forall k, exists Mk Mk',
              msem_node G f (mask (all_absent (xss 0)) k r xss)
                        Mk Mk'
                        (mask (all_absent (yss 0)) k r yss)
              /\ memory_masked k r M Mk
              /\ memory_masked k r M' Mk'
              /\ P_node f (mask (all_absent (xss 0)) k r xss)
                       Mk Mk'
                       (mask (all_absent (yss 0)) k r yss)) ->
        P_reset f r xss M M' yss.

    Hypothesis NodeCase:
      forall bk H f xss M M' yss n,
        clock_of xss bk ->
        find_node f G = Some n ->
        sem_vars H (map fst n.(n_in)) xss ->
        sem_vars H (map fst n.(n_out)) yss ->
        same_clock xss ->
        same_clock yss ->
        (forall n, absent_list (xss n) <-> absent_list (yss n)) ->
        Forall (msem_equation G bk H M M') n.(n_eqs) ->
        memory_closed_n M n.(n_eqs) ->
        Forall (P_equation bk H M M') n.(n_eqs) ->
        P_node f xss M M' yss.

    Fixpoint msem_equation_mult
             (b: stream bool) (H: history) (M M': memories) (e: equation)
             (Sem: msem_equation G b H M M' e) {struct Sem}
      : P_equation b H M M' e
    with msem_reset_mult
           (f: ident) (r: stream bool)
           (xss: stream (list value))
           (M M': memories)
           (oss: stream (list value))
           (Sem: msem_reset G f r xss M M' oss) {struct Sem}
         : P_reset f r xss M M' oss
    with msem_node_mult
           (f: ident)
           (xss: stream (list value))
           (M M': memories)
           (oss: stream (list value))
           (Sem: msem_node G f xss M M' oss) {struct Sem}
         : P_node f xss M M' oss.
    Proof.
      - destruct Sem; eauto.
      - destruct Sem; eauto.
        apply ResetCase; auto.
        intro k; destruct (H k) as (?&?&?&?&?); eauto 7.
      - destruct Sem; eauto.
        eapply NodeCase; eauto.
        clear H8.
        induction H7; auto.
    Qed.

    Combined Scheme msem_equation_node_reset_ind from
             msem_equation_mult, msem_node_mult, msem_reset_mult.

  End msem_node_mult.

  Definition msem_nodes (G: global) : Prop :=
    Forall (fun no => exists xs M M' ys, msem_node G no.(n_name) xs M M' ys) G.


  (** ** Properties *)

  (** *** Environment cons-ing lemmas *)

  (* Instead of repeating all these cons lemmas (i.e., copying and pasting them),
   and dealing with similar obligations multiple times in translation_correct,
   maybe it would be better to bake Ordered_nodes into msem_node and to make
   it like Miniimp, i.e.,
      find_node f G = Some (nd, G') and msem_node G' nd xs ys ?
   TODO: try this when the other elements are stabilised. *)

  Lemma msem_node_cons:
    forall n G f xs M M' ys,
      Ordered_nodes (n :: G) ->
      msem_node (n :: G) f xs M M' ys ->
      n.(n_name) <> f ->
      msem_node G f xs M M' ys.
  Proof.
    Hint Constructors msem_node msem_equation msem_reset.
    intros ** Hord Hsem Hnf.
    revert Hnf.
    induction Hsem as [| | | |?????? IH |????????? Hf ??????? IH]
        using msem_node_mult
      with (P_equation := fun bk H M M' eq =>
                            ~Is_node_in_eq n.(n_name) eq ->
                            msem_equation G bk H M M' eq)
           (P_reset := fun f r xss M M' yss =>
                         n_name n <> f ->
                         msem_reset G f r xss M M' yss); eauto.
    - intro Hnin.
      econstructor; eauto.
      apply IHHsem. intro Hnf; apply Hnin; rewrite Hnf. constructor.
    - intro Hnin.
      econstructor; eauto.
      apply IHHsem. intro Hnf; apply Hnin; rewrite Hnf. constructor.
    - intro. econstructor. intro k; destruct (IH k) as (?&?&?&?&?&?); eauto 6.
    - intro.
      pose proof Hf.
      rewrite find_node_tl with (1:=Hnf) in Hf.
      econstructor; eauto.
      + apply find_node_later_not_Is_node_in with (2:=Hf) in Hord.
        apply Is_node_in_Forall in Hord.
        apply Forall_Forall with (1:=Hord) in IH.
        apply Forall_impl with (2:=IH).
        intuition.
  Qed.

  Corollary msem_reset_cons:
    forall n G f r xs M M' ys,
      Ordered_nodes (n :: G) ->
      msem_reset (n :: G) f r xs M M' ys ->
      n.(n_name) <> f ->
      msem_reset G f r xs M M' ys.
  Proof.
    intros ** Sem ?.
    inversion_clear Sem as [?????? SemN].
    constructor.
    intro k; destruct (SemN k) as (?&?&?&?); eauto using msem_node_cons.
  Qed.

  Lemma msem_node_cons2:
    forall n G f xs M M' ys,
      Ordered_nodes G ->
      msem_node G f xs M M' ys ->
      Forall (fun n' => n_name n <> n_name n') G ->
      msem_node (n :: G) f xs M M' ys.
  Proof.
    Hint Constructors msem_equation.
    intros ** Hord Hsem Hnin.
    assert (Hnin':=Hnin).
    revert Hnin'.
    induction Hsem as [| | | |?????? IH|??????? n' ? Hfind ????? Heqs WF IH]
        using msem_node_mult
      with (P_equation := fun bk H M M' eq =>
                            ~Is_node_in_eq n.(n_name) eq ->
                            msem_equation (n :: G) bk H M M' eq)
           (P_reset := fun f r xss M M' yss =>
                         Forall (fun n' : node => n_name n <> n_name n') G ->
                         msem_reset (n :: G) f r xss M M' yss); eauto.
    - intro. constructor; intro k; destruct (IH k) as (?&?&?&?&?&?); eauto 6.
    - intro HH; clear HH.
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
          clear Heqs IH WF.
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

  Lemma msem_reset_cons2:
    forall n G f r xs M M' ys,
      Ordered_nodes G ->
      msem_reset G f r xs M M' ys ->
      Forall (fun n' => n_name n <> n_name n') G ->
      msem_reset (n :: G) f r xs M M' ys.
  Proof.
    intros ** Sem ?.
    inversion_clear Sem as [?????? SemN].
    constructor.
    intro k; destruct (SemN k) as (?&?&?&?); eauto using msem_node_cons2.
  Qed.

  Lemma msem_equation_cons2:
    forall G bk H M M' eqs n,
      Ordered_nodes (n :: G) ->
      Forall (msem_equation G bk H M M') eqs ->
      ~Is_node_in n.(n_name) eqs ->
      Forall (msem_equation (n :: G) bk H M M') eqs.
  Proof.
    Hint Constructors msem_equation.
    intros ** Hord Hsem Hnini.
    induction eqs as [|eq eqs IH]; [now constructor|].
    apply Forall_cons2 in Hsem.
    destruct Hsem as [Heq Heqs].
    apply not_Is_node_in_cons in Hnini.
    destruct Hnini as [Hnini Hninis].
    apply IH with (2:=Hninis) in Heqs.
    constructor; [|now apply Heqs].
    inv Hord.
    destruct Heq; eauto.
    - eauto using msem_node_cons2.
    - eauto using msem_reset_cons2.
  Qed.

  Lemma find_node_msem_node:
    forall G f,
      msem_nodes G ->
      find_node f G <> None ->
      exists xs M M' ys,
        msem_node G f xs M M' ys.
  Proof.
    intros G f Hnds Hfind.
    apply find_node_Exists in Hfind.
    apply Exists_exists in Hfind.
    destruct Hfind as [nd [Hin Hf]].
    unfold msem_nodes in Hnds.
    rewrite Forall_forall in Hnds.
    apply Hnds in Hin.
    destruct Hin as [xs [M [M' [ys Hmsem]]]].
    exists xs, M, M', ys.
    rewrite Hf in *.
    exact Hmsem.
  Qed.

  (* TODO: Tidy this up... *)
  Lemma Forall_msem_equation_global_tl:
    forall n G bk H M M' eqs,
      Ordered_nodes (n :: G) ->
      ~ Is_node_in n.(n_name) eqs ->
      Forall (msem_equation (n :: G) bk H M M') eqs ->
      Forall (msem_equation G bk H M M') eqs.
  Proof.
    intros ??????? Hord.
    induction eqs as [|eq eqs IH]; trivial; [].
    intros Hnini Hmsem.
    apply Forall_cons2 in Hmsem; destruct Hmsem as [Hseq Hseqs].
    apply IH in Hseqs.
    - apply Forall_cons; trivial.
      apply not_Is_node_in_cons in Hnini.
      destruct Hnini.
      inv Hseq; eauto;
        assert (n.(n_name) <> f)
        by (intro HH; apply H0; rewrite HH; constructor).
      + eauto using msem_node_cons.
      + eauto using msem_reset_cons.
    - apply not_Is_node_in_cons in Hnini.
      now destruct Hnini.
  Qed.

  (** *** Memory management *)

  Definition add_val_n (y: ident) (ms: stream val) (M: memories): memories :=
    fun n => add_val y (ms n) (M n).

  Lemma mfby_add_val_n:
    forall x v0 ls M M' xs y ms ms',
      x <> y ->
      mfby x v0 ls M M' xs ->
      mfby x v0 ls (add_val_n y ms M) (add_val_n y ms' M') xs.
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
    forall x v0 ls M M' xs y My My',
      mfby x v0 ls M M' xs ->
      mfby x v0 ls (add_inst_n y My M) (add_inst_n y My' M') xs.
  Proof.
    inversion 1; econstructor; eauto.
  Qed.

  Hint Resolve mfby_add_val_n mfby_add_inst_n.

  Lemma msem_equation_madd_val:
    forall G bk H M M' x ms ms' eqs,
      ~Is_defined_in_eqs x eqs ->
      Forall (msem_equation G bk H M M') eqs ->
      Forall (msem_equation G bk H (add_val_n x ms M) (add_val_n x ms' M')) eqs.
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
    forall G bk H M M' Mx Mx' x eqs,
      ~Is_defined_in_eqs x eqs ->
      Forall (msem_equation G bk H M M') eqs ->
      Forall (msem_equation G bk H (add_inst_n x Mx M) (add_inst_n x Mx' M')) eqs.
  Proof.
    Hint Constructors msem_equation.
    intros * Hnd Hsem.
    induction eqs as [|eq eqs IH]; [now constructor|].
    apply not_Is_defined_in_cons in Hnd.
    destruct Hnd as [Hnd Hnds].
    apply Forall_cons2 in Hsem.
    destruct Hsem as [Hsem Hsems].
    constructor; [|now apply IH with (1:=Hnds) (2:=Hsems)].
    destruct Hsem as [|???? x' ???????? Hsome
                         |???? x' ???????????? Hsome|];
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
      unfold gather_mem, concatMap; simpl.
      right; apply Vals; eauto.
      apply not_None_is_Some; eauto.
  Qed.

  Lemma sem_msem_eq:
    forall G bk H eqs M M' eq,
      (forall f xs ys,
          sem_node G f xs ys ->
          exists M M', msem_node G f xs M M' ys) ->
      (forall f r xs ys,
          sem_reset G f r xs ys ->
          exists M M', msem_reset G f r xs M M' ys) ->
      sem_equation G bk H eq ->
      NoDup_defs (eq :: eqs) ->
      Forall (msem_equation G bk H M M') eqs ->
      memory_closed_n M eqs ->
      exists M1 M1', Forall (msem_equation G bk H M1 M1') (eq :: eqs)
                /\ memory_closed_n M1 (eq :: eqs).
  Proof.
    intros ** IH IH' Heq NoDup Hmeqs WF.
    inversion Heq as [|???????? Hls Hxs Hsem
                         |???????????? Hls Hxs Hy Hr Hsem
                         |???????? Hle Hvar];
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
            exists n; split; auto.
            - eapply Forall2_length; eauto.
              specialize (H9 0); eauto.
            - exact n.(n_outgt0).
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
      + apply memory_closed_n_App; auto.

    - pose proof Hsem as Hsem'.
      apply IH' in Hsem as (Mx & Mx' & Hmsem).
      exists (add_inst_n (hd Ids.default x) Mx M), (add_inst_n (hd Ids.default x) Mx' M').

      assert (exists i, hd_error x = Some i) as [i Hsome].
      { assert (Hlen: 0 < length x).
        { assert (length x = length (xs 0))
            by (specialize (Hxs 0); simpl in Hxs; eapply Forall2_length; eauto).

          assert (exists n, length (map fst n.(n_out)) = length (xs 0)
                       /\ 0 < length n.(n_out)) as (n & ? & ?).
          { inversion_clear Hmsem as [?????? Hmsem'].
            destruct (Hmsem' 0) as (?&?& Hmsem'' & ?);
              inversion_clear Hmsem'' as [??????????? Hout].
            exists n; split; auto.
            - unfold sem_vars, lift in Hout; specialize (Hout 0).
              apply Forall2_length in Hout; rewrite Hout.
              rewrite mask_length; auto.
              inversion_clear Hsem' as [???? Hsem].
              eapply wf_streams_mask.
              intro n'; specialize (Hsem n');
                apply sem_node_wf in Hsem as (? & ?); eauto.
            - exact n.(n_outgt0).
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
      + apply memory_closed_n_App; auto.

    - exists (add_val_n x (hold (sem_const c0) ls) M), (add_val_n x (fun n =>
                                                                  match ls n with
                                                                  | present v => v
                                                                  | absent => hold (sem_const c0) ls n
                                                                  end) M');
        split.
      + constructor.
        * unfold add_val_n.
          econstructor; eauto; split; [|split];
            subst; unfold fby; simpl;
              intros; repeat rewrite find_val_gss; auto.
          destruct (ls n); auto.
        * inv NoDup.
          apply msem_equation_madd_val; eauto.
      + now apply memory_closed_n_Fby.
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
          exists M M', msem_node G f xs M M' ys) ->
      (forall f r xs ys,
          sem_reset G f r xs ys ->
          exists M M', msem_reset G f r xs M M' ys) ->
      NoDup_defs eqs ->
      Forall (sem_equation G bk H) eqs ->
      exists M1 M1', Forall (msem_equation G bk H M1 M1') eqs
                /\ memory_closed_n M1 eqs.
  Proof.
    intros ** IH NoDup Heqs.
    induction eqs as [|eq eqs IHeqs].
    - exists (fun n => empty_memory _), (fun n => empty_memory _); split; auto.
      apply memory_closed_empty'.
    - apply Forall_cons2 in Heqs as [Heq Heqs].
      eapply IHeqs in Heqs as (?&?&?&?).
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

  Theorem sem_msem_reset:
    forall G f r xs ys,
      (forall f xs ys,
          sem_node G f xs ys ->
          exists M M', msem_node G f xs M M' ys) ->
      sem_reset G f r xs ys ->
      exists M M', msem_reset G f r xs M M' ys.
  Proof.
    intros ** IH Sem.
    inversion_clear Sem as [???? Sem'].
    assert (forall k, exists Mk Mk', msem_node G f (mask (all_absent (xs 0)) k r xs)
                                     Mk Mk'
                                     (mask (all_absent (ys 0)) k r ys)) as Msem'
        by (intro; specialize (Sem' k); apply IH in Sem'; auto).
    assert (exists F F', forall k, msem_node G f (mask (all_absent (xs 0)) k r xs)
                                   (F k) (F' k)
                                   (mask (all_absent (ys 0)) k r ys))
      as (F & F' & Msem).
    {
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
    clear Msem'.

    exists (fun n => F (count r n) n), (fun n => F' (count r n) n).
    constructor.
    intro k; specialize (Msem k).
    do 2 eexists; intuition eauto;
      intros n Count; auto.
  Qed.

  Theorem sem_msem_node:
    forall G f xs ys,
      Ordered_nodes G ->
      sem_node G f xs ys ->
      exists M M', msem_node G f xs M M' ys.
  Proof.
    induction G as [|node].
    inversion 2;
      match goal with Hf: find_node _ [] = _ |- _ => inversion Hf end.
    intros ** Hord Hsem.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [??????? Hfind ????? Heqs].
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
                 exists M M', msem_node G f xs M M' ys) as IHG'
          by auto.
      assert (forall f r xs ys,
                 sem_reset G f r xs ys ->
                 exists M M', msem_reset G f r xs M M' ys) as IHG''
          by (intros; now apply sem_msem_reset).
      assert (exists M1 M1', Forall (msem_equation G bk H M1 M1') n.(n_eqs)
                        /\ memory_closed_n M1 n.(n_eqs))
        as (M1 & M1' & Hmsem & ?)
          by (eapply sem_msem_eqs; eauto; apply NoDup_defs_node).
      exists M1, M1'.
      econstructor; eauto.
      eapply msem_equation_cons2; eauto.
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
      unfold gather_mem, concatMap in Vals; simpl in Vals.
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
                                   ????????????????? Hd1 ?? Args1 ??? Reset1|
                                   ?????????? Arg1 ? Mfby1];
      try inversion Sem2 as [|
                                   ????????????? Hd2|
                                   ????????????????? Hd2 ?? Args2 ??? Reset2|
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
    inversion_clear Hsem1' as [???????? Clock1 Hfind1 Ins1 ???? Heqs1];
      inversion_clear Hsem2' as [???????? Clock2 Hfind2 Ins2 ???? Heqs2].
    rewrite Hfind2 in Hfind1; inv Hfind1.
    pose proof Hord; inv Hord.
    pose proof Hfind2.
    simpl in Hfind2.
    destruct (ident_eqb node.(n_name) f) eqn:Hnf.
    - inv Hfind2.
      assert (~ Is_node_in (n_name n) (n_eqs n)) by (eapply find_node_not_Is_node_in; eauto).
      eapply Forall_msem_equation_global_tl in Heqs1; eauto.
      eapply Forall_msem_equation_global_tl in Heqs2; eauto.
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
    revert dependent M; revert M'.
    induction eqs as [|[] ? IHeqs]; intros;
      inversion_clear Heqs as [|?? Sem Sems];
      try inversion_clear Sem as [|
                                  ????????????? Hd ?? Args ? Node|
                                  ????????????????? Hd ?? Args ??? Reset|
                                  ?????????? Arg ? Mfby];
      inv Nodup; eauto.
    - assert (forall n, M n ≋ empty_memory _) as E
          by (intro; apply memory_closed_empty; auto).
      rewrite 2 E; reflexivity.

    - apply msem_equation_remove_inst with (x := x) in Sems.
      + apply IHeqs in Sems; auto.
        *{ erewrite add_remove_inst_same; eauto;
           symmetry; erewrite add_remove_inst_same; eauto.
           rewrite Sems.
           apply IH with (n := n) in Node; auto.
           - now rewrite Node.
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
        *{ erewrite add_remove_inst_same; eauto;
           symmetry; erewrite add_remove_inst_same; eauto.
           rewrite Sems.
           inversion_clear Reset as [?????? Nodes].
           destruct (Nodes (count rs n)) as (Mn &?& Node_n & MemMask_n &?),
                                            (Nodes (count rs 0)) as (M0 &?&?& MemMask_0 &?).
           assert (Mn 0 ≋ M0 0) as E by (eapply same_initial_memory; eauto).
           apply IH with (n := n) in Node_n; auto.
           - now rewrite <-(MemMask_n n), <-(MemMask_0 0), Node_n, E.
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
    inversion_clear Hsem' as [???????? Clock Hfind Ins ???? Heqs].
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
      eapply Forall_msem_equation_global_tl in Heqs; eauto.
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
