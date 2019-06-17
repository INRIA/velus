From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Omega.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Arith.Compare_dec.

From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import RMemory.
From Velus Require Import CoreExpr.Stream.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.IsVariable.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import CoreExpr.CESemantics.
From Velus Require Import NLustre.NLSemantics.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.Memories.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import NLustre.IsFree.
From Velus Require Import NLustre.NoDup.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import NLustre.NLClocking.
From Velus Require Import CoreExpr.CEClockingSemantics.
From Velus Require Import NLustre.NLClockingSemantics.

(* for Theorem sem_msem_reset *)
(* TODO: Are these really necessary? *)
From Coq Require Import Logic.ClassicalChoice.
From Coq Require Import Logic.ConstructiveEpsilon.
From Coq Require Import Logic.Epsilon.
From Coq Require Import Logic.IndefiniteDescription.

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
       (Import Ids      : IDS)
       (Import Op       : OPERATORS)
       (Import OpAux    : OPERATORS_AUX           Op)
       (Import CESyn    : CESYNTAX                Op)
       (Import Syn      : NLSYNTAX            Ids Op       CESyn)
       (Import Str      : STREAM                  Op OpAux)
       (Import Ord      : NLORDERED           Ids Op       CESyn Syn)
       (Import CESem    : CESEMANTICS         Ids Op OpAux CESyn     Str)
       (Import Sem      : NLSEMANTICS         Ids Op OpAux CESyn Syn Str Ord CESem)
       (Import Mem      : MEMORIES            Ids Op       CESyn Syn)
       (Import IsD      : ISDEFINED           Ids Op       CESyn Syn                 Mem)
       (Import IsV      : ISVARIABLE          Ids Op       CESyn Syn                 Mem IsD)
       (Import CEIsF    : CEISFREE            Ids Op       CESyn)
       (Import IsF      : ISFREE              Ids Op       CESyn Syn CEIsF)
       (Import NoD      : NODUP               Ids Op       CESyn Syn                 Mem IsD IsV)
       (Import CEClo    : CECLOCKING          Ids Op       CESyn)
       (Import Clo      : NLCLOCKING          Ids Op       CESyn Syn     Ord         Mem IsD CEIsF IsF CEClo)
       (Import CECloSem : CECLOCKINGSEMANTICS Ids Op OpAux CESyn     Str     CESem                     CEClo)
       (Import CloSem   : NLCLOCKINGSEMANTICS Ids Op OpAux CESyn Syn Str Ord CESem Sem Mem IsD CEIsF IsF CEClo Clo CECloSem).

  Definition memories := stream (memory val).

  Definition memory_masked (k: nat) (rs: cstream) (M Mk: memories) :=
    forall n,
      count rs n = (if rs n then S k else k) ->
      M n = Mk n.

  Definition memory_masked' (k: nat) (rs: cstream) (M Mk: memories) :=
    forall n, count rs n = k -> M n = Mk n.

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
      forall n, find_inst x (M n) = Some (M' n).

    Variable G: global.

    Definition memory_closed (M: memory val) (eqs: list equation) : Prop :=
      (forall i, find_inst i M <> None -> InMembers i (gather_insts eqs))
      /\ forall x, find_val x M <> None -> In x (gather_mems eqs).

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
          sem_exps bk H arg ls ->
          sem_vars H xs xss ->
	        sem_clock bk H ck (clock_of ls) ->
          msem_node f ls Mx Mx' xss ->
          msem_equation bk H M M' (EqApp xs ck f arg None)
    | SEqReset:
        forall bk H M M' x xs ck f Mx Mx' arg y ys rs ls xss,
          hd_error xs = Some x ->
          sub_inst_n x M Mx ->
          sub_inst_n x M' Mx' ->
          sem_exps bk H arg ls ->
          sem_vars H xs xss ->
          sem_clock bk H ck (clock_of ls) ->
          sem_var H y ys ->
          reset_of ys rs ->
          (forall k, exists Mk Mk',
                msem_node f (mask k rs ls) Mk Mk' (mask k rs xss)
                /\ memory_masked k rs Mx Mk
                /\ memory_masked' k rs Mx' Mk') ->
          msem_equation bk H M M' (EqApp xs ck f arg (Some y))
    | SEqFby:
        forall bk H M M' x ck ls xs c0 le,
          sem_aexp bk H ck le ls ->
          sem_var H x xs ->
          mfby x (sem_const c0) ls M M' xs ->
          msem_equation bk H M M' (EqFby x ck c0 le)

    with msem_node:
           ident -> stream (list value) -> memories -> memories -> stream (list value) -> Prop :=
           SNode:
             forall bk H f xss M M' yss n,
               bk = clock_of xss ->
               find_node f G = Some n ->
               sem_vars H (map fst n.(n_in)) xss ->
               sem_vars H (map fst n.(n_out)) yss ->
               sem_clocked_vars bk H (idck n.(n_in)) ->
               Forall (msem_equation bk H M M') n.(n_eqs) ->
               memory_closed_n M n.(n_eqs) ->
               memory_closed_n M' n.(n_eqs) ->
               msem_node f xss M M' yss.

  End NodeSemantics.

  (** ** Induction principle for [msem_equation] and [msem_node] *)

  (** The automagically-generated induction principle is not strong
enough: it does not support the internal fixpoint introduced by
[Forall] *)

  Section msem_node_mult.

    Variable G: global.

    Variable P_equation: stream bool -> history -> memories -> memories -> equation -> Prop.
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
        sem_exps bk H arg ls ->
        sem_vars H xs xss ->
        sem_clock bk H ck (clock_of ls) ->
        msem_node G f ls Mx Mx' xss ->
        P_node f ls Mx Mx' xss ->
        P_equation bk H M M' (EqApp xs ck f arg None).

    Hypothesis EqResetCase:
      forall bk H M M' x xs ck f Mx Mx' arg y ys rs ls xss,
        Some x = hd_error xs ->
        sub_inst_n x M Mx ->
        sub_inst_n x M' Mx' ->
        sem_exps bk H arg ls ->
        sem_vars H xs xss ->
        sem_clock bk H ck (clock_of ls) ->
        sem_var H y ys ->
        reset_of ys rs ->
        (forall k, exists Mk Mk',
              msem_node G f (mask k rs ls) Mk Mk' (mask k rs xss)
              /\ memory_masked k rs Mx Mk
              /\ memory_masked' k rs Mx' Mk'
              /\ P_node f (mask k rs ls) Mk Mk' (mask k rs xss)) ->
        P_equation bk H M M' (EqApp xs ck f arg (Some y)).

    Hypothesis EqFbyCase:
      forall bk H M M' x ck ls xs c0 le,
        sem_aexp bk H ck le ls ->
        sem_var H x xs ->
        mfby x (sem_const c0) ls M M' xs ->
        P_equation bk H M M' (EqFby x ck c0 le).

    Hypothesis NodeCase:
      forall bk H f xss M M' yss n,
        bk = clock_of xss ->
        find_node f G = Some n ->
        sem_vars H (map fst n.(n_in)) xss ->
        sem_vars H (map fst n.(n_out)) yss ->
        sem_clocked_vars bk H (idck n.(n_in)) ->
        Forall (msem_equation G bk H M M') n.(n_eqs) ->
        memory_closed_n M n.(n_eqs) ->
        memory_closed_n M' n.(n_eqs) ->
        Forall (P_equation bk H M M') n.(n_eqs) ->
        P_node f xss M M' yss.

    Fixpoint msem_equation_mult
             (b: stream bool) (H: history) (M M': memories) (e: equation)
             (Sem: msem_equation G b H M M' e) {struct Sem}
      : P_equation b H M M' e
    with msem_node_mult
           (f: ident)
           (xss: stream (list value))
           (M M': memories)
           (oss: stream (list value))
           (Sem: msem_node G f xss M M' oss) {struct Sem}
         : P_node f xss M M' oss.
    Proof.
      - destruct Sem; eauto.
        eapply EqResetCase; eauto.
        match goal with
          H: forall _, exists _ _, _ |- _ =>
          intro k; destruct (H k) as (?&?&?&?&?); eauto 7
        end.
      - destruct Sem; eauto.
        eapply NodeCase; eauto.
        match goal with
          H: memory_closed_n M _, H': memory_closed_n M' _, Heqs: Forall _ (n_eqs n)
          |- _ => clear H H'; induction Heqs; auto
        end.
    Qed.

    Combined Scheme msem_node_equation_reset_ind from
             msem_node_mult, msem_equation_mult.

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
    Hint Constructors msem_node msem_equation.
    intros * Hord Hsem Hnf.
    revert Hnf.
    induction Hsem as [| |???????????????????????? Hsems|
                       |????????? Hf ?????? IH]
        using msem_node_mult
      with (P_equation := fun bk H M M' eq =>
                            ~Is_node_in_eq n.(n_name) eq ->
                            msem_equation G bk H M M' eq);
      eauto.
    - intro Hnin.
      econstructor; eauto.
      apply IHHsem. intro Hnf; apply Hnin; rewrite Hnf. constructor.
    - intro Hnin.
      econstructor; eauto.
      intro k; destruct (Hsems k) as (?&?&?&?&?& IH).
      do 2 eexists; split; eauto.
      apply IH; intro Hnf; apply Hnin; rewrite Hnf. constructor.
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
    forall n G f xs M M' ys,
      Ordered_nodes G ->
      msem_node G f xs M M' ys ->
      Forall (fun n' => n_name n <> n_name n') G ->
      msem_node (n :: G) f xs M M' ys.
  Proof.
    Hint Constructors msem_equation.
    intros * Hord Hsem Hnin.
    assert (Hnin':=Hnin).
    revert Hnin'.
    induction Hsem as [| |???????????????????????? Hsems|
                       |??????? n' ? Hfind ??? Heqs WF WF' IH]
        using msem_node_mult
      with (P_equation := fun bk H M M' eq =>
                            ~Is_node_in_eq n.(n_name) eq ->
                            msem_equation (n :: G) bk H M M' eq);
      eauto.
    - intro; econstructor; eauto.
      intro k; destruct (Hsems k) as (?&?&?&?&?&?); eauto 6.
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
    forall G bk H M M' eqs n,
      Ordered_nodes (n :: G) ->
      ~Is_node_in n.(n_name) eqs ->
      (Forall (msem_equation G bk H M M') eqs <->
       Forall (msem_equation (n :: G) bk H M M') eqs).
  Proof.
    intros * Hord Hnini.
    induction eqs as [|eq eqs IH]; [now constructor|].
    apply not_Is_node_in_cons in Hnini as [Hnini Hninis].
    split; intros Hsem; apply Forall_cons2 in Hsem as [Heq Heqs];
      apply IH in Heqs; auto; constructor; auto.
    - inv Hord.
      destruct Heq as [| |???????????????????????? Hsems|]; eauto.
      + eauto using msem_node_cons2.
      + econstructor; eauto.
        intro k; destruct (Hsems k) as (?&?&?&?&?).
        do 2 eexists; split; eauto using msem_node_cons2.
    - inversion Heq as [| |???????????????????????? Hsems|]; subst; eauto;
        assert (n.(n_name) <> f)
        by (intro HH; apply Hnini; rewrite HH; constructor).
      + eauto using msem_node_cons.
      + econstructor; eauto.
        intro k; destruct (Hsems k) as (?&?&?&?&?).
        do 2 eexists; split; eauto using msem_node_cons.
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
    intros * Hxy Fby; destruct Fby as (?&?& Spec).
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
      ~Is_defined_in x eqs ->
      Forall (msem_equation G bk H M M') eqs ->
      Forall (msem_equation G bk H (add_val_n x ms M) (add_val_n x ms' M')) eqs.
  Proof.
    Hint Constructors msem_equation.
    intros * Hnd Hsem.
    induction eqs as [|eq eqs IH]; [now constructor|].
    apply not_Is_defined_in_cons in Hnd.
    destruct Hnd as [Hnd Hnds].
    apply Forall_cons2 in Hsem.
    destruct Hsem as [Hsem Hsems].
    constructor; [|now apply IH with (1:=Hnds) (2:=Hsems)].
    destruct Hsem as [| |???????????????????????? Hsem|]; eauto.
    apply not_Is_defined_in_eq_EqFby in Hnd.
    eapply SEqFby; eauto.
  Qed.

  Lemma msem_equation_madd_inst:
    forall G bk H M M' Mx Mx' x eqs,
      ~Is_defined_in x eqs ->
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
                         |???? x' ??????????? Hsome|];
      eauto;
      assert (sub_inst_n x' (add_inst_n x Mx M) Mx0)
        by (apply not_Is_defined_in_eq_EqApp in Hnd;
            unfold add_inst_n in *; intro;
            rewrite find_inst_gso; auto; intro; subst x; destruct xs;
            inv Hsome; apply Hnd; now constructor);
      assert (sub_inst_n x' (add_inst_n x Mx' M') Mx'0)
        by (apply not_Is_defined_in_eq_EqApp in Hnd;
            unfold add_inst_n in *; intro;
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
    intros * WF Hd n; specialize (WF n); destruct WF as (Insts &?).
    split; auto.
    intro y; intros * Hin.
    unfold add_inst_n in Hin; apply not_None_is_Some in Hin as (?& Find).
    destruct (ident_eq_dec y i).
    - subst.
      unfold gather_insts; simpl.
      destruct xs; simpl in *; inv Hd; left; auto.
    - rewrite find_inst_gso in Find; auto.
      unfold gather_insts; simpl.
      apply InMembers_app; right; auto.
      apply Insts; eauto.
      apply not_None_is_Some; eauto.
  Qed.

  Lemma memory_closed_n_Fby:
    forall M eqs x ck v0 e vs,
      memory_closed_n M eqs ->
      memory_closed_n (add_val_n x vs M) (EqFby x ck v0 e :: eqs).
  Proof.
    intros * WF n; specialize (WF n); destruct WF as (?& Vals).
    split; auto.
    intro y; intros * Hin.
    unfold add_val_n in Hin; apply not_None_is_Some in Hin as (?& Find).
    destruct (ident_eq_dec y x).
    - subst; simpl; auto.
    - rewrite find_val_gso in Find; auto.
      unfold gather_mems; simpl.
      right; apply Vals; eauto.
      apply not_None_is_Some; eauto.
  Qed.

  Theorem sem_msem_reset:
    forall G f r xs ys,
      (forall f xs ys,
          sem_node G f xs ys ->
          exists M M', msem_node G f xs M M' ys) ->
      (forall k, sem_node G f (mask k r xs) (mask k r ys)) ->
      exists M M',
      forall k, exists Mk Mk', msem_node G f (mask k r xs) Mk Mk' (mask k r ys)
                     /\ memory_masked k r M Mk
                     /\ memory_masked' k r M' Mk'.
  Proof.
    intros * IH Sem.
    assert (forall k, exists Mk Mk', msem_node G f (mask k r xs)
                                     Mk Mk'
                                     (mask k r ys)) as Msem
        by (intro; specialize (Sem k); apply IH in Sem; auto).
    assert (exists F F', forall k, msem_node G f (mask k r xs)
                                   (F k) (F' k)
                                   (mask k r ys))
      as (F & F' & Msem').
    {
      (** Infinite Description  *)
      do 2 apply functional_choice in Msem as (?& Msem); eauto.

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
    clear Msem Sem.

    exists (fun n => F (if r n then pred (count r n) else count r n) n), (fun n => F' (count r n) n).
    intro k; specialize (Msem' k).
    do 2 eexists; intuition eauto;
      intros n Count; auto.
    rewrite Count; cases.
  Qed.

  Lemma sem_msem_eq:
    forall G bk H eqs M M' eq,
      (forall f xs ys,
          sem_node G f xs ys ->
          exists M M', msem_node G f xs M M' ys) ->
      sem_equation G bk H eq ->
      NoDup_defs (eq :: eqs) ->
      Forall (msem_equation G bk H M M') eqs ->
      memory_closed_n M eqs ->
      memory_closed_n M' eqs ->
      exists M1 M1', Forall (msem_equation G bk H M1 M1') (eq :: eqs)
                /\ memory_closed_n M1 (eq :: eqs)
                /\ memory_closed_n M1' (eq :: eqs).
  Proof.
    intros * IH Heq NoDup Hmeqs WF WF'.
    inversion Heq as [|
                      ???????? Hls Hxs ? Hsem|
                      ??????????? Hls Hxs ? Hy Hr Hsem|
                      ???????? Hle Hvar Hfby];
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
          { inversion_clear Hmsem as [??????????? Out].
            exists n; split; auto.
            - eapply Forall2_length; eauto.
              specialize (Out 0); eauto.
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
            unfold add_inst_n; intro; now apply find_inst_gss.
        * inv NoDup.
          apply hd_error_Some_In in Hsome.
          apply msem_equation_madd_inst; auto.
      + split; apply memory_closed_n_App; auto.

    - pose proof Hsem as Hsem'.
      apply sem_msem_reset in Hsem as (Mx & Mx' & Hmsem); auto.
      exists (add_inst_n (hd Ids.default x) Mx M), (add_inst_n (hd Ids.default x) Mx' M').

      assert (exists i, hd_error x = Some i) as [i Hsome].
      { assert (Hlen: 0 < length x).
        { assert (length x = length (xs 0))
            by (specialize (Hxs 0); simpl in Hxs; eapply Forall2_length; eauto).

          assert (exists n, length (map fst n.(n_out)) = length (xs 0)
                       /\ 0 < length n.(n_out)) as (n & ? & ?).
          { destruct (Hmsem 0) as (?&?& Hmsem' & ?);
              inversion_clear Hmsem' as [??????????? Hout].
            exists n; split; auto.
            - unfold sem_vars, lift in Hout; specialize (Hout 0).
              apply Forall2_length in Hout; rewrite Hout.
              rewrite mask_length; auto.
              eapply wf_streams_mask.
              intro n'; specialize (Hsem' n');
                apply sem_node_wf in Hsem' as (? & ?); eauto.
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
            unfold add_inst_n; intro; now apply find_inst_gss.
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
          exists M M', msem_node G f xs M M' ys) ->
      NoDup_defs eqs ->
      Forall (sem_equation G bk H) eqs ->
      exists M1 M1', Forall (msem_equation G bk H M1 M1') eqs
                /\ memory_closed_n M1 eqs
                /\ memory_closed_n M1' eqs.
  Proof.
    intros G bk H eqs IH NoDup Heqs.
    induction eqs as [|eq eqs IHeqs].
    - exists (fun n => empty_memory _), (fun n => empty_memory _); split; auto.
      split; apply memory_closed_empty'.
    - apply Forall_cons2 in Heqs as [Heq Heqs].
      eapply IHeqs in Heqs as (?&?&?&?&?).
      + eapply sem_msem_eq; eauto.
      + eapply NoDup_defs_cons; eauto.
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
    intros * Hord Hsem.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [??????? Hfind ??? Heqs].
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
      assert (exists M1 M1', Forall (msem_equation G (clock_of xs) H M1 M1') n.(n_eqs)
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

  (** Initial memory *)

  Lemma memory_closed_empty:
    forall M, memory_closed M [] -> M ≋ empty_memory _.
  Proof.
    intros * (Insts & Vals); unfold find_val, find_inst in *.
    constructor; simpl in *.
    - intro x.
      assert (Env.find x (values M) = None) as ->.
      { apply not_Some_is_None; intros * E.
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
      ~Is_defined_in x eqs ->
      Forall (msem_equation G bk H M M') eqs ->
      Forall (msem_equation G bk H (remove_inst_n x M) (remove_inst_n x M')) eqs.
  Proof.
    Ltac foo H := unfold sub_inst_n in *; intro n;
                setoid_rewrite find_inst_gro; auto;
                intro E; subst; apply H;
                constructor;
                apply hd_error_Some_In; auto.
    induction eqs as [|[]]; intros * Hnotin Sems;
      inversion_clear Sems as [|?? Sem]; auto; inversion_clear Sem;
        apply not_Is_defined_in_cons in Hnotin as (Hnotin &?);
        constructor; eauto using msem_equation;
          econstructor; eauto; foo Hnotin.
  Qed.

  Lemma msem_equation_remove_val:
    forall G bk eqs H M M' x,
      ~Is_defined_in x eqs ->
      Forall (msem_equation G bk H M M') eqs ->
      Forall (msem_equation G bk H (remove_val_n x M) (remove_val_n x M')) eqs.
  Proof.
    induction eqs as [|[]]; intros * Hnotin Sems;
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
    intros * WF Hd n; specialize (WF n); destruct WF as (Insts &?).
    split; auto.
    intro y; intros * Hin.
    unfold remove_inst_n in Hin; apply not_None_is_Some in Hin as (?& Find).
    destruct (ident_eq_dec y i).
    - subst; rewrite find_inst_grs in Find; discriminate.
    - rewrite find_inst_gro in Find; auto.
      unfold gather_insts in Insts; simpl in Insts.
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
    intros * WF n; specialize (WF n); destruct WF as (?& Vals).
    split; auto.
    intro y; intros * Hin.
    unfold remove_val_n in Hin; apply not_None_is_Some in Hin as (?& Find).
    destruct (ident_eq_dec y x).
    - subst; rewrite find_val_grs in Find; discriminate.
    - rewrite find_val_gro in Find; auto.
      unfold gather_mems in Vals; simpl in Vals.
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
    intros * IH Nodup Closed1 Closed2 Heqs1 Heqs2.
    revert dependent M1; revert dependent M2; revert M1' M2'.
    induction eqs as [|[] ? IHeqs]; intros;
      inversion_clear Heqs1 as [|?? Sem1 Sems1];
      inversion_clear Heqs2 as [|?? Sem2 Sems2];
      try inversion Sem1 as [|????????????? Hd1 ????? Node|
                             ???????????????? Hd1 ?? Args1 ?? Var ? Reset1|
                             ?????????? Arg1 ? Mfby1];
      try inversion Sem2 as [|????????????? Hd2|
                             ???????????????? Hd2 ?? Args2 ???? Reset2|
                             ?????????? Arg2 ? Mfby2];
      inv Nodup; subst; try discriminate; eauto.
    - assert (forall n, M1 n ≋ empty_memory _) as ->
          by (intro; apply memory_closed_empty; auto).
      assert (forall n, M2 n ≋ empty_memory _) as ->
          by (intro; apply memory_closed_empty; auto).
      reflexivity.

    - rewrite Hd2 in Hd1; inv Hd1.
      assert (~ Is_defined_in x eqs)
        by (apply hd_error_Some_In in Hd2; auto).
      apply msem_equation_remove_inst with (x := x) in Sems1;
        apply msem_equation_remove_inst with (x := x) in Sems2; auto.
      eapply IHeqs in Sems1; eauto; try eapply memory_closed_n_App'; eauto.
      erewrite add_remove_inst_same; eauto;
        symmetry; erewrite add_remove_inst_same; eauto.
      rewrite Sems1.
      eapply IH in Node; eauto.
      now rewrite Node.

    - match goal with H: Some _ = Some _ |- _ => inv H end.
      rewrite Hd2 in Hd1; inv Hd1.
      assert (~ Is_defined_in x eqs)
        by (apply hd_error_Some_In in Hd2; auto).
      apply msem_equation_remove_inst with (x := x) in Sems1;
        apply msem_equation_remove_inst with (x := x) in Sems2; auto.
      eapply IHeqs in Sems1; eauto; try eapply memory_closed_n_App'; eauto.
      erewrite add_remove_inst_same; eauto;
        symmetry; erewrite add_remove_inst_same; eauto.
      rewrite Sems1.
      destruct (Reset1 (if rs 0 then pred (count rs 0) else count rs 0))
        as (M01 &?& Node1 & MemMask1 &?),
           (Reset2 (if rs0 0 then pred (count rs0 0) else count rs0 0))
          as (M02 &?&?& MemMask2 &?).
      eapply IH in Node1; eauto.
      rewrite MemMask1, MemMask2, Node1; try reflexivity; simpl; cases.

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
    intros * Hord Hsem1 Hsem2.
    assert (Hsem1' := Hsem1);  assert (Hsem2' := Hsem2).
    inversion_clear Hsem1' as [???????? Clock1 Hfind1 Ins1 ?? Heqs1];
      inversion_clear Hsem2' as [???????? Clock2 Hfind2 Ins2 ?? Heqs2].
    rewrite Hfind2 in Hfind1; inv Hfind1.
    pose proof Hord; inv Hord.
    pose proof Hfind2.
    simpl in Hfind2.
    destruct (ident_eqb node.(n_name) f) eqn:Hnf.
    - inv Hfind2.
      assert (~ Is_node_in n.(n_name) n.(n_eqs))
        by (eapply find_node_not_Is_node_in with (G:=n::G); eauto).
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
    intros * Mfby Abs n E; induction n;
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
    intros * IH Hord Spec Absbk Nodup Closed Heqs.
    revert dependent M; revert dependent M'.
    induction eqs as [|[] ? IHeqs]; intros;
      inversion_clear Heqs as [|?? Sem Sems];
      try inversion_clear Sem as [|????????????? Hd ???? Hck Node|
                                  ???????????????? Hd ???? Hck ?? Reset|
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
           - intros k * Spec'; specialize (Hck k).
             rewrite Absbk in Hck; auto.
             apply clock_of_instant_false.
             eapply not_subrate_clock_impl; eauto.
         }
        * eapply memory_closed_n_App'; eauto.
      + apply hd_error_Some_In in Hd; auto.

    - apply msem_equation_remove_inst with (x := x) in Sems.
      + apply IHeqs in Sems; auto.
        *{ destruct (Reset (if rs n then pred (count rs n) else count rs n))
             as (Mn &?& Node_n & MemMask_n & MemMask_n'),
                (Reset (if rs 0 then pred (count rs 0) else count rs 0))
               as (M0 &?&?& MemMask_0 &?).
           assert (Mn 0 ≋ M0 0) as E by (eapply same_initial_memory; eauto).
           apply IH with (n := n) in Node_n; auto.
           - erewrite add_remove_inst_same; eauto;
               symmetry; rewrite add_remove_inst_same; eauto.
             rewrite Sems, (MemMask_n n), (MemMask_0 0), Node_n, E; try reflexivity.
             + simpl; cases.
             + simpl; destruct (rs n) eqn: Hr; auto.
               apply count_true_ge_1 in Hr.
               erewrite <-Lt.S_pred; eauto.
           - intros k * Spec'; specialize (Hck k).
             rewrite Absbk in Hck; auto.
             apply absent_list_mask, clock_of_instant_false.
             eapply not_subrate_clock_impl; eauto.
         }
        * eapply memory_closed_n_App'; eauto.
      + apply hd_error_Some_In in Hd; auto.

    - apply msem_equation_remove_val with (x := i) in Sems; auto.
      apply IHeqs in Sems; auto.
      + assert (find_val i (M n) = Some (sem_const c0)).
        { eapply mfby_absent_until; eauto.
          intros k * Spec'; specialize (Arg k); simpl in Arg.
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
    intros * Hord Hsem Abs n Spec.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [???????? Clock Hfind Ins ?? Heqs].
    assert (forall n, n < n0 -> bk n = false) as Absbk.
    { intros k Spec'; apply Abs in Spec'.
      rewrite Clock.
      unfold nequiv_decb; apply existsb_Forall_neg, absent_list_spec_b; auto.
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

  (** Absent  *)

  Lemma mfby_absent:
    forall n x v0 ls M M' xs,
      mfby x v0 ls M M' xs ->
      ls n = absent ->
      find_val x (M' n) = find_val x (M n).
  Proof.
    induction n; intros * Mfby Abs;
      destruct Mfby as (Init & Spec & Spec').
    - specialize (Spec' 0); rewrite Init, Abs in Spec'.
      intuition; congruence.
    - specialize (Spec' (S n)).
      destruct (find_val x (M (S n))); try contradiction.
      rewrite Abs in Spec'.
      intuition.
  Qed.

  Lemma msem_eqs_absent:
    forall M M' G eqs bk H vars n,
    (forall f xss M M' yss n,
        msem_node G f xss M M' yss ->
        absent_list (xss n) ->
        M' n ≋ M n) ->
    Ordered_nodes G ->
    Forall (wc_equation G vars) eqs ->
    Forall (clock_match bk H) vars ->
    bk n = false ->
    NoDup_defs eqs ->
    memory_closed_n M eqs ->
    memory_closed_n M' eqs ->
    Forall (msem_equation G bk H M M') eqs ->
    M' n ≋ M n.
  Proof.
    intros * IH Hord WC ClkM Absbk Nodup Closed Closed' Heqs.
    revert dependent M; revert dependent M'.
    induction eqs as [|[] ? IHeqs]; intros;
      inversion_clear Heqs as [|?? Sem Sems];
      try inversion Sem as [|????????????? Hd ???? Hck Node|
                            ???????????????? Hd ?? Args ? Hck Var Rst Reset|
                            ?????????? Arg ? Mfby]; subst;
      inv Nodup; inversion_clear WC as [|?? WC_eq]; eauto.
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
        * specialize (Hck n); rewrite Absbk in Hck.
          eapply clock_of_instant_false, not_subrate_clock_impl; eauto.
      + apply hd_error_Some_In in Hd; auto.

    - apply msem_equation_remove_inst with (x := x) in Sems.
      + apply IHeqs in Sems; try eapply memory_closed_n_App'; eauto.
        destruct (Reset (count rs n))
          as (Mn & Mn' & Node_n & MemMask_n & MemMask_n').
        erewrite add_remove_inst_same; eauto;
          symmetry; rewrite add_remove_inst_same; eauto.
        rewrite Sems.
        specialize (MemMask_n' n); specialize (MemMask_n n).
        destruct (rs n) eqn: Hr.
        *{ inversion_clear WC_eq as [|???????? WC_reset|].
           assert (In (y, c) vars) as Hin by auto.
           eapply Forall_forall in ClkM; eauto.
           specialize (Rst n); rewrite Hr in Rst.
           specialize (ClkM n); destruct ClkM as [(Var' & Clock)|((?& Var') & Clock)].
           - specialize (Var n).
             eapply sem_var_instant_det in Var; eauto.
             rewrite <-Var in Rst; simpl in Rst; inv Rst.
           - contradict Clock.
             rewrite Absbk; apply not_subrate_clock.
         }
        *{ apply IH with (n := n) in Node_n; auto.
           - rewrite MemMask_n, MemMask_n', Node_n; auto; reflexivity.
           - specialize (Hck n); rewrite Absbk in Hck.
             apply absent_list_mask; try apply all_absent_spec.
             eapply clock_of_instant_false, not_subrate_clock_impl; eauto.
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

  (** The following proofs are sadly almost exactly the same than in NLClockingSemantics *)
  Lemma clock_match_msem_node_eqs_reset:
    forall G,
      Ordered_nodes G ->
      wc_global G ->
      (forall f xss M M' yss,
          msem_node G f xss M M' yss ->
          forall bk H n,
            find_node f G = Some n ->
            bk = clock_of xss ->
            sem_vars H (map fst n.(n_in)) xss ->
            sem_vars H (map fst n.(n_out)) yss ->
            Forall (clock_match bk H) (idck n.(n_in)) ->
            Forall (clock_match bk H) (idck n.(n_out)))
      /\
      (forall bk H M M' eq,
          msem_equation G bk H M M' eq ->
          forall iface x ck,
            NoDupMembers iface ->
            wc_equation G iface eq ->
            Is_defined_in_eq x eq ->
            In (x, ck) iface ->
            clock_match bk H (x, ck)).
  Proof.
    intros * Hord WCG; apply msem_node_equation_reset_ind;
      [intros ???????? Hvar Hexp|
       intros ???????????????? Hexps Hvars Hck Hsem|
       intros ??????????????????? Hexps Hvars Hck ?? Hsem|
       intros ?????????? Hexp Hvar Hfby|
       intros ???????? Hck Hf Hin Hout ???? IH].

    - (* EqDef *)
      intros iface y yck Hnd Hwc Hdef Hin n.
      inv Hdef. inv Hwc.
      match goal with H1:In (x, _) iface, H2:In (x, _) iface |- _ =>
        apply NoDupMembers_det with (1:=Hnd) (2:=H1) in H2; subst end.
      specialize (Hvar n). specialize (Hexp n).
      unfold clock_match_instant.
      inv Hexp; match goal with H:_ = xs n |- _ => rewrite <-H in * end; eauto.

    - (* EqApp *)
      intros IHHsem iface z zck Hndup Hwc Hdef Hiface.
      inversion_clear Hdef as [|? ? ? ? ? Hyys|].
      inversion_clear Hsem as [cks' H' ????? node Hco' Hfind Hvi Hvo].
      specialize (IHHsem _ _ _ Hfind Hco' Hvi Hvo).
      assert (Hvi' := Hvi).
      rewrite <-map_fst_idck in Hvi'.
      eapply sem_clocked_vars_clock_match in Hvi'; eauto.
      pose proof (IHHsem Hvi') as Hscv'. clear IHHsem.
      inversion_clear Hwc
        as [|????? node' Hfind' (isub & osub & Hfai & Hfao & Hfno)|].
      rewrite Hfind in Hfind'. inv Hfind'.

      assert (forall x y ys,
                 InMembers x (node'.(n_in) ++ node'.(n_out)) ->
                 orelse isub osub x = Some y ->
                 forall n,
                   sem_var_instant (restr_hist H' n) x ys ->
                   sem_var_instant (restr_hist H  n) y ys) as Htranso.
      { eapply sem_var_instant_transfer_out; eauto.
        - pose proof node'.(n_nodup) as Hnd.
          rewrite <-Permutation_app_assoc,
                  (Permutation.Permutation_app_comm node'.(n_in)),
                  Permutation_app_assoc in Hnd.
          now apply NoDupMembers_app_r in Hnd.
        - apply Forall2_impl_In with (2:=Hfai). intuition.
        - apply Forall2_impl_In with (2:=Hfao). intuition.
      }

      rewrite <-map_fst_idck in Hvo. unfold idck in Hvo. rewrite map_map in Hvo.
      intro n; specialize (Hvo n); specialize (Hvars n); simpl in *.
      unfold sem_vars_instant in Hvo.
      rewrite Forall2_map_1 in Hvo.
      apply Forall2_swap_args in Hfao.
      apply Forall2_trans_ex with (1:=Hfao) in Hvo.
      apply Forall2_swap_args in Hvars.
      apply Forall2_trans_ex with (1:=Hvo) in Hvars.
      apply Forall2_same in Hvars.
      eapply Forall_forall in Hvars
        as (s & Hin & ((x', (xty, xck)) & Hxin &
                       (Hoeq & yck' & Hiface' & Hinst) & Hsvx) & Hsvy); eauto.
      unfold dck in Hinst. simpl in *.
      apply NoDupMembers_det with (1:=Hndup) (2:=Hiface) in Hiface'.
      rewrite <-Hiface' in *.
      unfold idck in *. rewrite Forall_map in Hscv'.
      eapply Forall_forall in Hscv'; eauto; simpl in Hscv'.
      apply wc_find_node with (1:=WCG) in Hfind as (G'' & G' & HG' & Hfind).
      destruct Hfind as (WCi & WCo & WCv & WCeqs).
      assert (In (x', xck) (idck (node'.(n_in) ++ node'.(n_out)))) as Hxin'
        by (rewrite idck_app, in_app; right;
            apply In_idck_exists; eauto).
      apply wc_env_var with (1:=WCo) in Hxin'.
      destruct (Hscv' n) as [(Hv & Hc)|((c & Hv) & Hc)].
      + left; split.
        * apply sem_var_instant_det with (1:=Hsvx) in Hv. subst; auto.
        * eapply sem_clock_instant_transfer_out
            with (vars := idck (node'.(n_in) ++ node'.(n_out))); eauto.
          now setoid_rewrite InMembers_idck; eauto.
      + right; split.
        * exists c; apply sem_var_instant_det with (1:=Hsvx) in Hv. now subst.
        * eapply sem_clock_instant_transfer_out
            with (vars := idck (node'.(n_in) ++ node'.(n_out))); eauto.
          now setoid_rewrite InMembers_idck; eauto.

    - (* EqReset *)
      intros iface z zck Hndup Hwc Hdef Hiface n.
      inversion_clear Hdef as [|? ? ? ? ? Hyys|].
      specialize (Hsem (count rs n)); destruct Hsem as (?&?& Hsems &?&?& IHHsem).

      inversion_clear Hsems as [cks' H' ????? node Hco' Hfind Hvi Hvo].
      specialize (IHHsem _ _ _ Hfind Hco' Hvi Hvo).
      assert (Hvi' := Hvi).
      rewrite <-map_fst_idck in Hvi'.
      eapply sem_clocked_vars_clock_match in Hvi'; eauto.
      pose proof (IHHsem Hvi') as Hscv'. clear IHHsem.
      inversion_clear Hwc
        as [|????? node' Hfind' (isub & osub & Hfai & Hfao & Hfno)|].
      rewrite Hfind in Hfind'. inv Hfind'.

      assert (forall x y ys,
                 InMembers x (node'.(n_in) ++ node'.(n_out)) ->
                 orelse isub osub x = Some y ->
                 sem_var_instant (restr_hist H' n) x ys ->
                 sem_var_instant (restr_hist H  n) y ys) as Htranso.
      { eapply sem_var_instant_transfer_out'; eauto.
        - pose proof node'.(n_nodup) as Hnd.
          rewrite <-Permutation_app_assoc,
                  (Permutation.Permutation_app_comm node'.(n_in)),
                  Permutation_app_assoc in Hnd.
          now apply NoDupMembers_app_r in Hnd.
        - apply Forall2_impl_In with (2:=Hfai). intuition.
        - apply Forall2_impl_In with (2:=Hfao). intuition.
        - instantiate (1 := bk).
          rewrite mask_transparent; auto.
        - rewrite mask_transparent; auto.
      }

      rewrite <-map_fst_idck in Hvo. unfold idck in Hvo. rewrite map_map in Hvo.
      specialize (Hvo n); specialize (Hvars n); simpl in *.
      rewrite mask_transparent in Hvo; auto.
      unfold sem_vars_instant in Hvo.
      rewrite Forall2_map_1 in Hvo.
      apply Forall2_swap_args in Hfao.
      apply Forall2_trans_ex with (1:=Hfao) in Hvo.
      apply Forall2_swap_args in Hvars.
      apply Forall2_trans_ex with (1:=Hvo) in Hvars.
      apply Forall2_same in Hvars.
      eapply Forall_forall in Hvars
        as (s & Hin & ((x', (xty, xck)) & Hxin &
                       (Hoeq & yck' & Hiface' & Hinst) & Hsvx) & Hsvy); eauto.
      unfold dck in Hinst. simpl in *.
      apply NoDupMembers_det with (1:=Hndup) (2:=Hiface) in Hiface'.
      rewrite <-Hiface' in *.
      unfold idck in *. rewrite Forall_map in Hscv'.
      eapply Forall_forall in Hscv'; eauto; simpl in Hscv'.
      apply wc_find_node with (1:=WCG) in Hfind as (G'' & G' & HG' & Hfind).
      destruct Hfind as (WCi & WCo & WCv & WCeqs).
      assert (In (x', xck) (idck (node'.(n_in) ++ node'.(n_out)))) as Hxin'
        by (rewrite idck_app, in_app; right;
            apply In_idck_exists; eauto).
      apply wc_env_var with (1:=WCo) in Hxin'.
      destruct (Hscv' n) as [(Hv & Hc)|((c & Hv) & Hc)].
      + left; split.
        * apply sem_var_instant_det with (1:=Hsvx) in Hv. now subst.
        *{ eapply sem_clock_instant_transfer_out
             with (vars := idck (node'.(n_in) ++ node'.(n_out))); eauto.
           - unfold clock_of in Hc; rewrite mask_transparent in Hc; eauto.
           - now setoid_rewrite InMembers_idck; eauto.
         }
      + right; split.
        * exists c; apply sem_var_instant_det with (1:=Hsvx) in Hv. now subst.
        *{ eapply sem_clock_instant_transfer_out
             with (vars := idck (node'.(n_in) ++ node'.(n_out))); eauto.
           - unfold clock_of in Hc; rewrite mask_transparent in Hc; eauto.
           - now setoid_rewrite InMembers_idck; eauto.
       }

    - (* EqFby *)
      intros iface z zck Hnd Hwc Hdef Hin n.
      inv Hdef; inv Hwc.
      match goal with H1:In (?y, _) iface, H2:In (?y, _) iface |- _ =>
                      apply NoDupMembers_det with (1:=Hnd) (2:=H1) in H2; subst end.
      destruct Hfby as (Init & Loop & Spec).
      specialize (Hexp n); specialize (Hvar n); specialize (Spec n).
      destruct (find_val x (M n)) eqn: Find; try contradiction.
      unfold clock_match_instant.
      inv Hexp; match goal with H:_ = ls n |- _ => rewrite <-H in * end;
        destruct Spec as (?& Hxs); rewrite Hxs in *; eauto.

    - (* nodes *)
      intros bk' H' n' Hf' Hck' Hin' Hout' Hcm'.
      rewrite Hf in Hf'. inv Hf'.
      apply Forall_forall; unfold idck.
      intros (x, xck) Hxin.
      apply In_idck_exists in Hxin as (xty & Hxin). assert (Hxin' := Hxin).
      apply in_map with (f:=fst), node_output_defined_in_eqs in Hxin.
      apply Is_defined_in_In in Hxin as (eq & Heqin & Hxeq).
      eapply Forall_forall in IH; eauto.
      apply wc_find_node with (1:=WCG) in Hf
        as (G'' & G' & HG & (WCi & WCo & WCv & WCeqs)).
      eapply Forall_forall in WCeqs; eauto.
      assert (NoDupMembers (idck (n'.(n_in) ++ n'.(n_vars) ++ n'.(n_out))))
        as Hnd by apply NoDupMembers_idck, n_nodup.
      subst.
      apply IH with (x:=x) (ck:=xck) in Hnd;
        try (apply In_idck_exists; exists xty);
        eauto using wc_equation_global_app,
                    Ordered_nodes_append, wc_equation_global_cons
              with datatypes.
      intro n.
      specialize (Hin' n); specialize (Hout' n);
        specialize (Hin n); specialize (Hout n).
      simpl in *.
      unfold sem_vars_instant in Hin, Hout, Hin', Hout'.
      rewrite Forall2_map_1 in Hin', Hout'.
      apply Forall2_app with (2:=Hout') in Hin'.
      rewrite Forall2_map_1 in Hin, Hout.
      assert (Hout2:=Hout).
      apply Forall2_app with (1:=Hin) in Hout2.
      apply Forall2_Forall2 with (1:=Hout) in Hout'.
      apply Forall2_in_left with (2:=Hxin') in Hout' as (s & Hsin & Hvs & Hvs').
      destruct (Hnd n) as [(Hv & Hc)|((c & Hv) & Hc)].
      + left. simpl in *. split.
        * apply sem_var_instant_det with (1:=Hvs) in Hv. now subst.
        * eapply clock_vars_to_sem_clock_instant
          with (1:=Hout2) (2:=Hin') in WCo; eauto.
          eapply in_app; eauto.
      + right. simpl in *. split.
        * exists c; apply sem_var_instant_det with (1:=Hvs) in Hv. now subst.
        * eapply clock_vars_to_sem_clock_instant
          with (1:=Hout2) (2:=Hin') in WCo; eauto.
          eapply in_app; eauto.
  Qed.

  Corollary clock_match_msem_node:
    forall G f xss M M' yss bk H n,
      Ordered_nodes G ->
      wc_global G ->
      msem_node G f xss M M' yss ->
      find_node f G = Some n ->
      bk = clock_of xss ->
      sem_vars H (map fst n.(n_in)) xss ->
      sem_vars H (map fst n.(n_out)) yss ->
      Forall (clock_match bk H) (idck n.(n_in)) ->
      Forall (clock_match bk H) (idck n.(n_out)).
  Proof.
    intros ????????? Ord WCG; intros.
    eapply (proj1 (clock_match_msem_node_eqs_reset Ord WCG)); eauto.
  Qed.

  Corollary clock_match_msem_eq:
    forall G bk H M M' iface x ck eq,
      Ordered_nodes G ->
      wc_global G ->
      NoDupMembers iface ->
      msem_equation G bk H M M' eq ->
      wc_equation G iface eq ->
      Is_defined_in_eq x eq ->
      In (x, ck) iface ->
      clock_match bk H (x, ck).
  Proof.
    intros ????????? Ord WCG; intros.
    eapply (proj2 (clock_match_msem_node_eqs_reset Ord WCG)); eauto.
  Qed.

  Corollary clock_match_msem_eqs:
    forall G bk H M M' inputs vars eqs,
      Ordered_nodes G ->
      wc_global G ->
      NoDupMembers (inputs ++ vars) ->
      Forall (msem_equation G bk H M M') eqs ->
      Forall (wc_equation G (inputs ++ vars)) eqs ->
      Permutation.Permutation (vars_defined eqs) (map fst vars) ->
      forall x xck,
        In (x, xck) vars ->
        clock_match bk H (x, xck).
  Proof.
    intros G bk H M M' inputs vars eqs OG WCG Hndup Hsem Hwc Hdef x xck Hin.
    assert (In x (vars_defined eqs)) as Hxin
        by (now rewrite Hdef; apply in_map with (f:=fst) in Hin).
    apply Is_defined_in_vars_defined, Is_defined_in_In in Hxin
      as (eq & Hieq & Hdeq).
    eapply Forall_forall in Hsem; eauto.
    eapply Forall_forall in Hwc; eauto.
    eapply clock_match_msem_eq; eauto.
    rewrite in_app; auto.
  Qed.

  Theorem msem_node_absent:
    forall G f xss M M' yss n,
      Ordered_nodes G ->
      wc_global G ->
      msem_node G f xss M M' yss ->
      absent_list (xss n) ->
      M' n ≋ M n.
  Proof.
    induction G as [|node].
    inversion 3;
      match goal with Hf: find_node _ [] = _ |- _ => inversion Hf end.
    intros * Hord WC Hsem Abs.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [???????? Clock Hfind Ins ?? Heqs].
    assert (bk n = false) as Absbk
        by (rewrite Clock; unfold nequiv_decb;
            apply existsb_Forall_neg, absent_list_spec_b; auto).
    pose proof (find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    pose proof Hord; inv Hord.
    pose proof Hfind.
    inversion WC as [|??? (?&?&?& WCeqs)]; subst.
    simpl in Hfind.
    destruct (ident_eqb node.(n_name) f) eqn:Hnf.
    - inv Hfind.
      eapply msem_equations_cons in Heqs; eauto.
      eapply msem_eqs_absent; eauto.
      + rewrite idck_app, Forall_app; split.
        * eapply sem_clocked_vars_clock_match; eauto.
          rewrite map_fst_idck; eauto.
        *{ apply Forall_forall; intros (x, ck) ?.
           rewrite idck_app in WCeqs.
           eapply clock_match_msem_eqs with (eqs := n0.(n_eqs)) (G := G); eauto.
           - rewrite <-idck_app, NoDupMembers_idck.
             apply n_nodup.
           - rewrite map_fst_idck.
             apply n_defd.
         }
      + apply NoDup_defs_node.
    - eapply msem_node_cons in Hsem; eauto.
      now apply ident_eqb_neq.
  Qed.

  (** Relooper for free *)

  Lemma msem_eqs_relooper:
    forall M M' G eqs bk H,
      (forall f xss M M' yss,
          msem_node G f xss M M' yss ->
          forall n, M (S n) ≋ M' n) ->
      Ordered_nodes G ->
      NoDup_defs eqs ->
      memory_closed_n M eqs ->
      memory_closed_n M' eqs ->
      Forall (msem_equation G bk H M M') eqs ->
      forall n, M (S n) ≋ M' n.
  Proof.
    intros * IH Hord Nodup Closed Closed' Heqs n.
    revert dependent M; revert dependent M'.
    induction eqs as [|[] ? IHeqs]; intros;
      inversion_clear Heqs as [|?? Sem Sems];
      try inversion Sem as [|????????????? Hd ?? Args ?? Node|
                            ???????????????? Hd ?? Args ?? Var Rst Reset|
                            ?????????? Arg ? Mfby]; subst;
      inv Nodup; eauto.
    - assert (forall n, M n ≋ empty_memory _) as E
          by (intro; apply memory_closed_empty; auto).
     assert (forall n, M' n ≋ empty_memory _) as E'
          by (intro; apply memory_closed_empty; auto).
     rewrite E, E'; reflexivity.

    - apply msem_equation_remove_inst with (x := x) in Sems.
      + apply IHeqs in Sems; try eapply memory_closed_n_App'; eauto.
        apply IH with (n := n) in Node; auto.
        erewrite add_remove_inst_same; eauto;
          symmetry; erewrite add_remove_inst_same; eauto.
        now rewrite Sems, Node.
      + apply hd_error_Some_In in Hd; auto.

    - apply msem_equation_remove_inst with (x := x) in Sems.
      + apply IHeqs in Sems; try eapply memory_closed_n_App'; eauto.
        erewrite add_remove_inst_same; eauto;
          symmetry; rewrite add_remove_inst_same; eauto.
        destruct (Reset (count rs n))
          as (Mn & Mn' & Node_n & MemMask_n & MemMask_n').
        apply IH with (n := n) in Node_n.
        rewrite Sems, (MemMask_n' n), (MemMask_n (S n)), Node_n; auto; reflexivity.
      + apply hd_error_Some_In in Hd; auto.

    - apply msem_equation_remove_val with (x := i) in Sems; auto.
      apply IHeqs in Sems; try eapply memory_closed_n_Fby'; eauto.
      destruct Mfby as (Init & Loop & Spec').
      specialize (Spec' (S n)).
      destruct (find_val i (M (S n))) eqn: Eq; try contradiction.
      erewrite add_remove_val_same; eauto.
      rewrite Loop in Eq.
      symmetry; erewrite add_remove_val_same; eauto.
      now rewrite Sems.
  Qed.

  Theorem msem_node_relooper:
    forall G f xss M M' yss,
      Ordered_nodes G ->
      msem_node G f xss M M' yss ->
      forall n, M (S n) ≋ M' n.
  Proof.
    induction G as [|node].
    inversion 2;
      match goal with Hf: find_node _ [] = _ |- _ => inversion Hf end.
    intros * Hord Hsem n.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [???????? Clock Hfind Ins ?? Heqs].
    pose proof (find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    pose proof Hord; inv Hord.
    pose proof Hfind.
    simpl in Hfind.
    destruct (ident_eqb node.(n_name) f) eqn:Hnf.
    - inv Hfind.
      eapply msem_equations_cons in Heqs; eauto.
      eapply msem_eqs_relooper; eauto.
      apply NoDup_defs_node.
    - eapply msem_node_cons in Hsem; eauto.
      now apply ident_eqb_neq.
  Qed.

  (* (** The other way around  *) *)
  (* Lemma mfby_fby: *)
  (*   forall x v0 es M M' xs, *)
  (*     mfby x v0 es M M' xs -> *)
  (*     xs ≈ fby v0 es. *)
  (* Proof. *)
  (*   intros * (Init & Loop & Spec) n. *)
  (*   unfold fby. *)
  (*   pose proof (Spec n) as Spec'. *)
  (*   destruct (find_val x (M n)) eqn: Find_n; try contradiction. *)
  (*   destruct (es n); destruct Spec' as (?& Hx); auto. *)
  (*   rewrite Hx. *)
  (*   clear - Init Loop Spec Find_n. *)
  (*   revert dependent v. *)
  (*   induction n; intros; simpl; try congruence. *)
  (*   specialize (Spec n). *)
  (*   destruct (find_val x (M n)); try contradiction. *)
  (*   rewrite Loop in Find_n. *)
  (*   destruct (es n); destruct Spec; try congruence. *)
  (*   apply IHn; congruence. *)
  (* Qed. *)

  (* Theorem msem_sem_node_equation_reset: *)
  (*   forall G, *)
  (*     (forall f xss M M' yss, *)
  (*         msem_node G f xss M M' yss -> *)
  (*         sem_node G f xss yss) *)
  (*     /\ *)
  (*     (forall bk H M M' eq, *)
  (*         msem_equation G bk H M M' eq -> *)
  (*         sem_equation G bk H eq) *)
  (*     /\ *)
  (*     (forall f r xss M M' yss, *)
  (*         msem_reset G f r xss M M' yss -> *)
  (*         sem_reset G f r xss yss). *)
  (* Proof. *)
  (*   intros; apply msem_node_equation_reset_ind; *)
  (*     [intros|intros|intros|intros|intros ?????? IH|intros]; *)
  (*     eauto using sem_equation, mfby_fby, sem_node. *)
  (*   constructor; intro; destruct (IH k) as (?&?&?); intuition. *)
  (* Qed. *)

  (* Corollary msem_sem_node: *)
  (*   forall G f xss M M' yss, *)
  (*     msem_node G f xss M M' yss -> *)
  (*     sem_node G f xss yss. *)
  (* Proof. *)
  (*   intros; eapply (proj1 (msem_sem_node_equation_reset G)); eauto. *)
  (* Qed. *)

  (* Corollary msem_sem_equation: *)
  (*   forall G bk H M M' eq, *)
  (*     msem_equation G bk H M M' eq -> *)
  (*     sem_equation G bk H eq. *)
  (* Proof. *)
  (*   intros; eapply (proj1 (proj2 (msem_sem_node_equation_reset G))); eauto. *)
  (* Qed. *)

  (* Corollary msem_sem_equations: *)
  (*   forall G bk H M M' eqs, *)
  (*     Forall (msem_equation G bk H M M') eqs -> *)
  (*     Forall (sem_equation G bk H) eqs. *)
  (* Proof. *)
  (*   induction 1; constructor; eauto using msem_sem_equation. *)
  (* Qed. *)

End MEMSEMANTICS.

Module MemSemanticsFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX           Op)
       (CESyn : CESYNTAX                Op)
       (Syn   : NLSYNTAX            Ids Op       CESyn)
       (Str   : STREAM                  Op OpAux)
       (Ord   : NLORDERED           Ids Op       CESyn Syn)
       (CESem : CESEMANTICS         Ids Op OpAux CESyn     Str)
       (Sem   : NLSEMANTICS         Ids Op OpAux CESyn Syn Str Ord CESem)
       (Mem   : MEMORIES            Ids Op       CESyn Syn)
       (IsD   : ISDEFINED           Ids Op       CESyn Syn                 Mem)
       (IsV   : ISVARIABLE          Ids Op       CESyn Syn                 Mem IsD)
       (CEIsF : CEISFREE            Ids Op       CESyn)
       (IsF   : ISFREE              Ids Op       CESyn Syn CEIsF)
       (NoD   : NODUP               Ids Op       CESyn Syn                 Mem IsD IsV)
       (CEClo : CECLOCKING          Ids Op       CESyn)
       (Clo   : NLCLOCKING          Ids Op       CESyn Syn     Ord         Mem IsD CEIsF IsF CEClo)
       (CECloSem : CECLOCKINGSEMANTICS Ids Op OpAux CESyn     Str     CESem                     CEClo)
       (CloSem   : NLCLOCKINGSEMANTICS Ids Op OpAux CESyn Syn Str Ord CESem Sem Mem IsD CEIsF IsF CEClo Clo CECloSem)
<: MEMSEMANTICS Ids Op OpAux CESyn Syn Str Ord CESem Sem Mem IsD IsV CEIsF IsF NoD CEClo Clo CECloSem CloSem.
  Include MEMSEMANTICS Ids Op OpAux CESyn Syn Str Ord CESem Sem Mem IsD IsV CEIsF IsF NoD CEClo Clo CECloSem CloSem.
End MemSemanticsFun.
