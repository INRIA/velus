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
From Velus Require Import VelusMemory.
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

(** * The NLustre+VelusMemory semantics *)

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

  Definition mfby (x: ident) (c0: val) (xs: stream value) (M: memories) (ys: stream value) : Prop :=
    find_val x (M 0) = Some c0
    /\ forall n, match find_val x (M n) with
           | Some mv =>
             match xs n with
             | absent =>
               find_val x (M (S n)) = Some mv
               /\ ys n = absent
             | present v =>
               find_val x (M (S n)) = Some v
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

    Inductive msem_equation: stream bool -> history -> memories -> equation -> Prop :=
    | SEqDef:
        forall bk H M x ck xs ce,
          sem_var H x xs ->
          sem_caexp bk H ck ce xs ->
          msem_equation bk H M (EqDef x ck ce)
    | SEqApp:
        forall bk H M x xs ck f Mx arg ls xss,
          hd_error xs = Some x ->
          sub_inst_n x M Mx ->
          sem_exps bk H arg ls ->
          sem_vars H xs xss ->
	        sem_clock bk H ck (clock_of ls) ->
          msem_node f ls Mx xss ->
          msem_equation bk H M (EqApp xs ck f arg None)
    | SEqReset:
        forall bk H M x xs ck f Mx arg y cky ys rs ls xss,
          hd_error xs = Some x ->
          sub_inst_n x M Mx ->
          sem_exps bk H arg ls ->
          sem_vars H xs xss ->
          sem_clock bk H ck (clock_of ls) ->
          sem_var H y ys ->
          bools_of ys rs ->
          (forall k, exists Mk,
                msem_node f (mask k rs ls) Mk (mask k rs xss)
                /\ memory_masked k rs Mx Mk) ->
          msem_equation bk H M (EqApp xs ck f arg (Some (y, cky)))
    | SEqFby:
        forall bk H M x ck ls xs c0 le,
          sem_aexp bk H ck le ls ->
          sem_var H x xs ->
          mfby x (sem_const c0) ls M xs ->
          msem_equation bk H M (EqFby x ck c0 le)

    with msem_node:
           ident -> stream (list value) -> memories -> stream (list value) -> Prop :=
           SNode:
             forall bk H f xss M yss n,
               bk = clock_of xss ->
               find_node f G = Some n ->
               sem_vars H (map fst n.(n_in)) xss ->
               sem_vars H (map fst n.(n_out)) yss ->
               sem_clocked_vars bk H (idck n.(n_in)) ->
               Forall (msem_equation bk H M) n.(n_eqs) ->
               memory_closed_n M n.(n_eqs) ->
               msem_node f xss M yss.

  End NodeSemantics.

  (** ** Induction principle for [msem_equation] and [msem_node] *)

  (** The automagically-generated induction principle is not strong
enough: it does not support the internal fixpoint introduced by
[Forall] *)

  Section msem_node_mult.

    Variable G: global.

    Variable P_equation: stream bool -> history -> memories -> equation -> Prop.
    Variable P_node: ident -> stream (list value) -> memories -> stream (list value) -> Prop.

    Hypothesis EqDefCase:
      forall bk H M x ck xs ce,
        sem_var H x xs ->
        sem_caexp bk H ck ce xs ->
        P_equation bk H M (EqDef x ck ce).

    Hypothesis EqAppCase:
      forall bk H M x xs ck f Mx arg ls xss,
        Some x = hd_error xs ->
        sub_inst_n x M Mx ->
        sem_exps bk H arg ls ->
        sem_vars H xs xss ->
        sem_clock bk H ck (clock_of ls) ->
        msem_node G f ls Mx xss ->
        P_node f ls Mx xss ->
        P_equation bk H M (EqApp xs ck f arg None).

    Hypothesis EqResetCase:
      forall bk H M x xs ck f Mx arg y cky ys rs ls xss,
        Some x = hd_error xs ->
        sub_inst_n x M Mx ->
        sem_exps bk H arg ls ->
        sem_vars H xs xss ->
        sem_clock bk H ck (clock_of ls) ->
        sem_var H y ys ->
        bools_of ys rs ->
        (forall k, exists Mk,
              msem_node G f (mask k rs ls) Mk (mask k rs xss)
              /\ memory_masked k rs Mx Mk
              /\ P_node f (mask k rs ls) Mk (mask k rs xss)) ->
        P_equation bk H M (EqApp xs ck f arg (Some (y, cky))).

    Hypothesis EqFbyCase:
      forall bk H M x ck ls xs c0 le,
        sem_aexp bk H ck le ls ->
        sem_var H x xs ->
        mfby x (sem_const c0) ls M xs ->
        P_equation bk H M (EqFby x ck c0 le).

    Hypothesis NodeCase:
      forall bk H f xss M yss n,
        bk = clock_of xss ->
        find_node f G = Some n ->
        sem_vars H (map fst n.(n_in)) xss ->
        sem_vars H (map fst n.(n_out)) yss ->
        sem_clocked_vars bk H (idck n.(n_in)) ->
        Forall (msem_equation G bk H M) n.(n_eqs) ->
        memory_closed_n M n.(n_eqs) ->
        Forall (P_equation bk H M) n.(n_eqs) ->
        P_node f xss M yss.

    Fixpoint msem_equation_mult
             (b: stream bool) (H: history) (M: memories) (e: equation)
             (Sem: msem_equation G b H M e) {struct Sem}
      : P_equation b H M e
    with msem_node_mult
           (f: ident)
           (xss: stream (list value))
           (M: memories)
           (oss: stream (list value))
           (Sem: msem_node G f xss M oss) {struct Sem}
         : P_node f xss M oss.
    Proof.
      - destruct Sem; eauto.
        eapply EqResetCase; eauto.
        match goal with
          H: forall _, exists _, _ |- _ =>
          intro k; destruct (H k) as (?&?&?); eauto 7
        end.
      - destruct Sem; eauto.
        eapply NodeCase; eauto.
        match goal with
          H: memory_closed_n M _, Heqs: Forall _ (n_eqs n)
          |- _ => clear H; induction Heqs; auto
        end.
    Qed.

    Combined Scheme msem_node_equation_ind from
             msem_node_mult, msem_equation_mult.

  End msem_node_mult.

  Definition msem_nodes (G: global) : Prop :=
    Forall (fun no => exists xs M ys, msem_node G no.(n_name) xs M ys) G.


  (** ** Properties *)

  (** *** Environment cons-ing lemmas *)

  (* Instead of repeating all these cons lemmas (i.e., copying and pasting them),
   and dealing with similar obligations multiple times in translation_correct,
   maybe it would be better to bake Ordered_nodes into msem_node and to make
   it like Miniimp, i.e.,
      find_node f G = Some (nd, G') and msem_node G' nd xs ys ?
   TODO: try this when the other elements are stabilised. *)

  Lemma msem_node_cons:
    forall n G f xs M ys,
      Ordered_nodes (n :: G) ->
      msem_node (n :: G) f xs M ys ->
      n.(n_name) <> f ->
      msem_node G f xs M ys.
  Proof.
    Hint Constructors msem_node msem_equation.
    intros * Hord Hsem Hnf.
    revert Hnf.
    induction Hsem as [| |?????????????????????? Hsems|
                       |???????? Hf ????? IH]
        using msem_node_mult
      with (P_equation := fun bk H M eq =>
                            ~Is_node_in_eq n.(n_name) eq ->
                            msem_equation G bk H M eq);
      eauto.
    - intro Hnin.
      econstructor; eauto.
      apply IHHsem. intro; apply Hnin; subst. constructor.
    - intro Hnin.
      econstructor; eauto.
      intro k; destruct (Hsems k) as (?&?&?& IH).
      eexists; split; eauto.
      apply IH; intro; apply Hnin; subst. constructor.
    - intro.
      rewrite find_node_tl with (1:=Hnf) in Hf.
      econstructor; eauto.
      apply find_node_later_not_Is_node_in with (2:=Hf) in Hord.
      apply Is_node_in_Forall in Hord.
      apply Forall_Forall with (1:=Hord) in IH.
      apply Forall_impl with (2:=IH).
      intuition.
  Qed.

  Lemma find_node_other_name:
    forall G f n n',
      find_node f G = Some n' ->
      Forall (fun n' => n.(n_name) <> n'.(n_name)) G ->
      n.(n_name) <> f.
  Proof.
    intros G f n n' Hfind Hnin Hnf.
    rewrite Hnf in Hnin.
    pose proof (find_node_name _ _ _ Hfind).
    apply find_node_split in Hfind.
    destruct Hfind as [bG [aG Hge]].
    rewrite Hge in Hnin.
    apply Forall_app in Hnin.
    destruct Hnin as [H' Hfg]; clear H'.
    inversion_clear Hfg.
    now take (f<>_) and apply it.
  Qed.

  Lemma msem_cons2:
    forall n G,
      Ordered_nodes G ->
      Forall (fun n' => n.(n_name) <> n'.(n_name)) G ->
      (forall f xv M yv,
          msem_node G f xv M yv ->
          msem_node (n :: G) f xv M yv)
      /\
      (forall bk R M eq,
          msem_equation G bk R M eq ->
          ~Is_node_in_eq n.(n_name) eq ->
          msem_equation (n::G) bk R M eq).
  Proof.
    intros n G OG Fn.
    apply msem_node_equation_ind; try (now intros; econstructor; eauto).
    - intros. econstructor; eauto. intro k.
      take (forall k, exists Mr, _) and specialize (it k);
        destruct it as (Mk & ? & ? & ?).
      exists Mk. split; auto.
    - intros.
      take (find_node f G = Some _) and rename it into Ff.
      econstructor; eauto.
      + rewrite <-find_node_other in Ff; eauto.
        apply find_node_In in Ff as (? & Ff).
        rewrite Forall_forall in Fn. specialize (Fn _ Ff). now subst.
      + apply find_node_not_Is_node_in_eq with (g:=n.(n_name)) in Ff; auto.
        take (Forall _ n0.(n_eqs)) and rename it into Feqs.
        apply Forall_Forall with (1:=Ff) in Feqs.
        apply Forall_impl_In with (2:=Feqs).
        intros eq Ineq (? & ?); auto.
  Qed.

  Lemma msem_node_cons2:
    forall n G f xs M ys,
      Ordered_nodes G ->
      msem_node G f xs M ys ->
      Forall (fun n' => n_name n <> n_name n') G ->
      msem_node (n :: G) f xs M ys.
  Proof. intros; apply msem_cons2; auto. Qed.

  Lemma msem_equations_cons:
    forall G bk H M eqs n,
      Ordered_nodes (n :: G) ->
      ~Is_node_in n.(n_name) eqs ->
      (Forall (msem_equation G bk H M) eqs <->
       Forall (msem_equation (n :: G) bk H M) eqs).
  Proof.
    intros * Hord Hnini.
    induction eqs as [|eq eqs IH]; [now constructor|].
    apply not_Is_node_in_cons in Hnini as [Hnini Hninis].
    split; intros Hsem; apply Forall_cons2 in Hsem as [Heq Heqs];
      apply IH in Heqs; auto; constructor; auto.
    - inv Hord.
      destruct Heq as [| |?????????????????????? Hsems|]; eauto.
      + eauto using msem_node_cons2.
      + econstructor; eauto.
        intro k; destruct (Hsems k) as (?&?&?).
        eexists; split; eauto using msem_node_cons2.
    - inversion Heq as [| |?????????????????????? Hsems|]; subst; eauto;
        assert (n.(n_name) <> f)
        by (intro HH; apply Hnini; rewrite HH; constructor).
      + eauto using msem_node_cons.
      + econstructor; eauto.
        intro k; destruct (Hsems k) as (?&?&?).
        eexists; split; eauto using msem_node_cons.
  Qed.

  Lemma find_node_msem_node:
    forall G f,
      msem_nodes G ->
      find_node f G <> None ->
      exists xs M ys,
        msem_node G f xs M ys.
  Proof.
    intros G f Hnds Hfind.
    apply find_node_Exists in Hfind.
    apply Exists_exists in Hfind.
    destruct Hfind as [nd [Hin Hf]].
    unfold msem_nodes in Hnds.
    rewrite Forall_forall in Hnds.
    apply Hnds in Hin.
    destruct Hin as [xs [M [ys Hmsem]]].
    exists xs, M, ys.
    rewrite Hf in *.
    exact Hmsem.
  Qed.

  (** *** VelusMemory management *)

  Definition add_val_n (y: ident) (ms: stream val) (M: memories): memories :=
    fun n => add_val y (ms n) (M n).

  Lemma mfby_add_val_n:
    forall x v0 ls M xs y ms,
      x <> y ->
      mfby x v0 ls M xs ->
      mfby x v0 ls (add_val_n y ms M) xs.
  Proof.
    unfold add_val_n.
    intros * Hxy Fby; destruct Fby as (?& Spec).
    split.
    - rewrite find_val_gso; auto.
    - intro n; rewrite 2 find_val_gso; auto; apply Spec.
  Qed.

  Definition add_inst_n (y: ident) (M' M: memories): memories :=
    fun n => add_inst y (M' n) (M n).

  Lemma mfby_add_inst_n:
    forall x v0 ls M xs y My,
      mfby x v0 ls M xs ->
      mfby x v0 ls (add_inst_n y My M) xs.
  Proof.
    inversion 1; econstructor; eauto.
  Qed.

  Hint Resolve mfby_add_val_n mfby_add_inst_n.

  Lemma msem_equation_madd_val:
    forall G bk H M x ms eqs,
      ~Is_defined_in x eqs ->
      Forall (msem_equation G bk H M) eqs ->
      Forall (msem_equation G bk H (add_val_n x ms M)) eqs.
  Proof.
    Hint Constructors msem_equation.
    intros * Hnd Hsem.
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
    forall G bk H M Mx x eqs,
      ~Is_defined_in x eqs ->
      Forall (msem_equation G bk H M) eqs ->
      Forall (msem_equation G bk H (add_inst_n x Mx M)) eqs.
  Proof.
    Hint Constructors msem_equation.
    intros * Hnd Hsem.
    induction eqs as [|eq eqs IH]; [now constructor|].
    apply not_Is_defined_in_cons in Hnd.
    destruct Hnd as [Hnd Hnds].
    apply Forall_cons2 in Hsem.
    destruct Hsem as [Hsem Hsems].
    constructor; [|now apply IH with (1:=Hnds) (2:=Hsems)].
    destruct Hsem as [|??? x' ??????? Hsome
                         |??? x' ??????????? Hsome|];
      eauto;
      assert (sub_inst_n x' (add_inst_n x Mx M) Mx0)
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
          exists M, msem_node G f xs M ys) ->
      (forall k, sem_node G f (mask k r xs) (mask k r ys)) ->
      exists M,
      forall k, exists Mk, msem_node G f (mask k r xs) Mk (mask k r ys)
                     /\ memory_masked k r M Mk.
  Proof.
    intros * IH Sem.
    assert (forall k, exists Mk, msem_node G f (mask k r xs) Mk (mask k r ys)) as Msem
        by (intro; specialize (Sem k); apply IH in Sem; auto).
    assert (exists F, forall k, msem_node G f (mask k r xs) (F k) (mask k r ys))
      as (F & Msem').
    {
      (** Infinite Description  *)
      apply functional_choice in Msem as (?&?); eauto.

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

    exists (fun n => F (if r n then pred (count r n) else count r n) n).
    intro k; specialize (Msem' k).
    do 2 eexists; intuition eauto;
      intros n Count; auto.
    rewrite Count; cases.
  Qed.

  Lemma sem_msem_eq:
    forall G bk H eqs M eq,
      (forall f xs ys,
          sem_node G f xs ys ->
          exists M, msem_node G f xs M ys) ->
      sem_equation G bk H eq ->
      NoDup_defs (eq :: eqs) ->
      Forall (msem_equation G bk H M) eqs ->
      memory_closed_n M eqs ->
      exists M1, Forall (msem_equation G bk H M1) (eq :: eqs)
            /\ memory_closed_n M1 (eq :: eqs).
  Proof.
    intros * IH Heq NoDup Hmeqs WF.
    inversion Heq as [|
                      ???????? Hls Hxs ? Hsem|
                      ???????????? Hls Hxs ? Hy Hr Hsem|
                      ???????? Hle Hvar Hfby];
      match goal with H:_=eq |- _ => rewrite <-H in * end.

    - exists M.
      econstructor; eauto.

    - apply IH in Hsem as (Mx & Hmsem).
      exists (add_inst_n (hd Ids.default x) Mx M).

      assert (exists i, hd_error x = Some i) as [i Hsome].
      { assert (Hlen: 0 < length x).
        { assert (length x = length (xs 0))
            by (specialize (Hxs 0); simpl in Hxs; eapply Forall2_length; eauto).

          assert (exists n, length (map fst n.(n_out)) = length (xs 0)
                       /\ 0 < length n.(n_out)) as (n & ? & ?).
          { inversion_clear Hmsem as [?????????? Out].
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
      apply sem_msem_reset in Hsem as (Mx & Hmsem); auto.
      exists (add_inst_n (hd Ids.default x) Mx M).

      assert (exists i, hd_error x = Some i) as [i Hsome].
      { assert (Hlen: 0 < length x).
        { assert (length x = length (xs 0))
            by (specialize (Hxs 0); simpl in Hxs; eapply Forall2_length; eauto).

          assert (exists n, length (map fst n.(n_out)) = length (xs 0)
                       /\ 0 < length n.(n_out)) as (n & ? & ?).
          { destruct (Hmsem 0) as (?& Hmsem' & ?);
              inversion_clear Hmsem' as [?????????? Hout].
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

    - exists (add_val_n x (hold (sem_const c0) ls) M);
        split.
      + constructor.
        * unfold add_val_n.
          econstructor; eauto; split;
            intros; try rewrite Hfby; unfold fby;
              simpl; repeat rewrite find_val_gss; auto.
          destruct (ls n); auto.
        * inv NoDup.
          apply msem_equation_madd_val; eauto.
      + split; apply memory_closed_n_Fby; auto.
  Qed.

  Lemma memory_closed_empty:
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
          exists M, msem_node G f xs M ys) ->
      NoDup_defs eqs ->
      Forall (sem_equation G bk H) eqs ->
      exists M1, Forall (msem_equation G bk H M1) eqs
            /\ memory_closed_n M1 eqs.
  Proof.
    intros G bk H eqs IH NoDup Heqs.
    induction eqs as [|eq eqs IHeqs].
    - exists (fun n => empty_memory _); split; auto.
      apply memory_closed_empty.
    - apply Forall_cons2 in Heqs as [Heq Heqs].
      eapply IHeqs in Heqs as (?&?&?).
      + eapply sem_msem_eq; eauto.
      + eapply NoDup_defs_cons; eauto.
  Qed.

  Theorem sem_msem_node:
    forall G f xs ys,
      Ordered_nodes G ->
      sem_node G f xs ys ->
      exists M, msem_node G f xs M ys.
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
                 exists M, msem_node G f xs M ys) as IHG'
          by auto.
      assert (exists M1, Forall (msem_equation G (clock_of xs) H M1) n.(n_eqs)
                    /\ memory_closed_n M1 n.(n_eqs))
        as (M1 & Hmsem &?)
          by (eapply sem_msem_eqs; eauto; apply NoDup_defs_node).
      exists M1.
      econstructor; eauto.
      rewrite <-msem_equations_cons; eauto.
    - apply ident_eqb_neq in Hnf.
      apply sem_node_cons with (1:=Hord) (3:=Hnf) in Hsem.
      inv Hord.
      eapply IHG in Hsem as (M &?); eauto.
      exists M.
      now eapply msem_node_cons2; eauto.
  Qed.

  (** Initial memory *)

  Lemma msem_eqs_same_initial_memory:
    forall M1 G eqs bk1 H1 M2 bk2 H2,
      (forall f xss1 M1 yss1 xss2 M2 yss2,
          msem_node G f xss1 M1 yss1 ->
          msem_node G f xss2 M2 yss2 ->
          M1 0 ≋ M2 0) ->
      NoDup_defs eqs ->
      memory_closed_n M1 eqs ->
      memory_closed_n M2 eqs ->
      Forall (msem_equation G bk1 H1 M1) eqs ->
      Forall (msem_equation G bk2 H2 M2) eqs ->
      M1 0 ≋ M2 0.
  Proof.
    intros * IH Nodup Closed1 Closed2 Heqs1 Heqs2.
    specialize (Closed1 0); specialize (Closed2 0);
      destruct Closed1 as (Insts1 & Values1), Closed2 as (Insts2 & Values2);
      unfold find_val, find_inst in *.
    constructor.

    - clear Insts1 Insts2.
      intro x.
      specialize (Values1 x); specialize (Values2 x).
      destruct (Env.find x (values (M1 0))) eqn: Find1;
        destruct (Env.find x (values (M2 0))) eqn: Find2; auto.
      + assert (In x (gather_mems eqs)) as Hin by (apply Values1; congruence).
        clear Values1 Values2.
        induction eqs as [|[]]; simpl in Hin; try contradiction;
          inv Nodup;
          inversion_clear Heqs1 as [|?? Heq1];
          inversion_clear Heqs2 as [|?? Heq2]; auto.
        destruct Hin; auto; subst.
        inversion_clear Heq1 as [| | |??????????? (Find1'&?)];
          inversion_clear Heq2 as [| | |??????????? (Find2'&?)];
          unfold find_val in *; congruence.
      + assert (In x (gather_mems eqs)) as Hin by (apply Values1; congruence).
        clear Values1 Values2.
        induction eqs as [|[]]; simpl in Hin; try contradiction;
          inv Nodup;
          inversion_clear Heqs1 as [|?? Heq1];
          inversion_clear Heqs2 as [|?? Heq2]; auto.
        destruct Hin; auto; subst.
        inversion_clear Heq1 as [| | |??????????? (Find1'&?)];
          inversion_clear Heq2 as [| | |??????????? (Find2'&?)];
          unfold find_val in *; congruence.
      + assert (In x (gather_mems eqs)) as Hin by (apply Values2; congruence).
        clear Values1 Values2.
        induction eqs as [|[]]; simpl in Hin; try contradiction;
          inv Nodup;
          inversion_clear Heqs1 as [|?? Heq1];
          inversion_clear Heqs2 as [|?? Heq2]; auto.
        destruct Hin; auto; subst.
        inversion_clear Heq1 as [| | |??????????? (Find1'&?)];
          inversion_clear Heq2 as [| | |??????????? (Find2'&?)];
          unfold find_val in *; congruence.

    - clear Values1 Values2.
      constructor.
      + setoid_rewrite Env.Props.P.F.in_find_iff.
        intro i; split; intros Find.
        * apply Insts1 in Find.
          clear Insts1 Insts2.
          induction eqs as [|[]]; simpl in Find; try contradiction;
          inv Nodup;
          inversion_clear Heqs1 as [|?? Heq1];
          inversion_clear Heqs2 as [|?? Heq2]; auto.
          apply InMembers_app in Find; destruct Find as [Find|]; auto.
          cases; inv Find; try contradiction.
          inversion_clear Heq2 as [|??????????? Hd|??????????????? Hd|];
            inv Hd; unfold sub_inst_n, find_inst in *; congruence.
        * apply Insts2 in Find.
          clear Insts1 Insts2.
          induction eqs as [|[]]; simpl in Find; try contradiction;
          inv Nodup;
          inversion_clear Heqs1 as [|?? Heq1];
          inversion_clear Heqs2 as [|?? Heq2]; auto.
          apply InMembers_app in Find; destruct Find as [Find|]; auto.
          cases; inv Find; try contradiction.
          inversion_clear Heq1 as [|??????????? Hd|??????????????? Hd|];
            inv Hd; unfold sub_inst_n, find_inst in *; congruence.
      + setoid_rewrite Env.Props.P.F.find_mapsto_iff.
        intros i e e' Find1 Find2.
        assert (InMembers i (gather_insts eqs)) as Hin by (apply Insts1; congruence).
        clear Insts1 Insts2.
        induction eqs as [|[]]; simpl in Hin; try contradiction;
          inv Nodup;
          inversion_clear Heqs1 as [|?? Heq1];
          inversion_clear Heqs2 as [|?? Heq2]; auto.
        apply InMembers_app in Hin; destruct Hin as [Hin|]; auto.
        cases; inv Hin; try contradiction.
        inversion Heq1 as [|??????????? Hd1 Find1'|??????????????? Hd1 Find1' ????? Reset1|]; subst;
          inversion_clear Heq2 as [|??????????? Hd2 Find2'|??????????????? Hd2 Find2' ????? Reset2|];
          inv Hd1; inv Hd2; unfold sub_inst_n, find_inst in *;
            rewrite Find1' in Find1; inv Find1;
              rewrite Find2' in Find2; inv Find2; eauto.
        destruct (Reset1 (if rs 0 then pred (count rs 0) else count rs 0))
          as (M01 & Node1 & MemMask1),
             (Reset2 (if rs0 0 then pred (count rs0 0) else count rs0 0))
            as (M02 &?& MemMask2).
        rewrite MemMask1, MemMask2; eauto; simpl; cases.
  Qed.

  Theorem same_initial_memory:
    forall G f xss1 xss2 M1 M2 yss1 yss2,
      Ordered_nodes G ->
      msem_node G f xss1 M1 yss1 ->
      msem_node G f xss2 M2 yss2 ->
      M1 0 ≋ M2 0.
  Proof.
    induction G as [|node].
    inversion 2;
      match goal with Hf: find_node _ [] = _ |- _ => inversion Hf end.
    intros * Hord Hsem1 Hsem2.
    assert (Hsem1' := Hsem1);  assert (Hsem2' := Hsem2).
    inversion_clear Hsem1' as [??????? Clock1 Hfind1 Ins1 ?? Heqs1];
      inversion_clear Hsem2' as [??????? Clock2 Hfind2 Ins2 ?? Heqs2].
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
    forall n0 x v0 ls M xs,
      mfby x v0 ls M xs ->
      (forall n, n < n0 -> ls n = absent) ->
      forall n, n <= n0 -> find_val x (M n) = Some v0.
  Proof.
    intros * Mfby Abs n E; induction n;
      destruct Mfby as (Init & Spec); auto.
    specialize (Spec n).
    destruct (find_val x (M n)); try contradiction.
    rewrite Abs in Spec; try omega.
    destruct Spec as [->].
    apply IHn; omega.
  Qed.

  Lemma msem_eqs_absent_until:
    forall M G n0 eqs bk H n,
    (forall f xss M yss,
        msem_node G f xss M yss ->
        (forall n, n < n0 -> absent_list (xss n)) ->
        forall n, n <= n0 -> M n ≋ M 0) ->
    Ordered_nodes G ->
    n <= n0 ->
    (forall n, n < n0 -> bk n = false) ->
    NoDup_defs eqs ->
    memory_closed_n M eqs ->
    Forall (msem_equation G bk H M) eqs ->
    M n ≋ M 0.
  Proof.
    intros * IH Hord Spec Absbk Nodup Closed Heqs.
    pose proof (Closed 0) as Closed0; specialize (Closed n);
      destruct Closed0 as (Insts0 & Values0), Closed as (Insts & Values);
      unfold find_val, find_inst in *.
    constructor.

    - clear Insts Insts0.
      intro x.
      specialize (Values x); specialize (Values0 x).
      destruct (Env.find x (values (M n))) eqn: Find;
        destruct (Env.find x (values (M 0))) eqn: Find0; auto.
      + assert (In x (gather_mems eqs)) as Hin by (apply Values; congruence).
        clear Values Values0.
        induction eqs as [|[]]; simpl in Hin; try contradiction;
          inv Nodup;
          inversion_clear Heqs as [|?? Heq]; auto.
        destruct Hin; auto; subst.
        inversion_clear Heq as [| | |????????? Sem ? Mfby].
        pose proof Mfby as Mfby'; destruct Mfby'.
        eapply mfby_absent_until in Mfby; unfold find_val in *; eauto; try congruence.
        intros k ?; specialize (Sem k). inv Sem; auto.
        rewrite Absbk in *; auto.
        exfalso; eapply not_subrate_clock; eauto.
      + assert (In x (gather_mems eqs)) as Hin by (apply Values; congruence).
        clear Values Values0.
        induction eqs as [|[]]; simpl in Hin; try contradiction;
          inv Nodup;
          inversion_clear Heqs as [|?? Heq]; auto.
        destruct Hin; auto; subst.
        inversion_clear Heq as [| | |????????? Sem ? Mfby].
        pose proof Mfby as Mfby'; destruct Mfby'.
        eapply mfby_absent_until in Mfby; unfold find_val in *; eauto; try congruence.
      + assert (In x (gather_mems eqs)) as Hin by (apply Values0; congruence).
        clear Values Values0.
        induction eqs as [|[]]; simpl in Hin; try contradiction;
          inv Nodup;
          inversion_clear Heqs as [|?? Heq]; auto.
        destruct Hin; auto; subst.
        inversion_clear Heq as [| | |????????? Sem ? Mfby].
        pose proof Mfby as Mfby'; destruct Mfby'.
        eapply mfby_absent_until in Mfby; unfold find_val in *; eauto; try congruence.
        intros k ?; specialize (Sem k). inv Sem; auto.
        rewrite Absbk in *; auto.
        exfalso; eapply not_subrate_clock; eauto.

    - clear Values Values0.
      constructor.
      + setoid_rewrite Env.Props.P.F.in_find_iff.
        intro i; split; intros Find.
        * apply Insts in Find.
          clear Insts Insts0.
          induction eqs as [|[]]; simpl in Find; try contradiction;
          inv Nodup;
          inversion_clear Heqs as [|?? Heq]; auto.
          apply InMembers_app in Find; destruct Find as [Find|]; auto.
          cases; inv Find; try contradiction.
          inversion_clear Heq as [|??????????? Hd|??????????????? Hd|];
            inv Hd; unfold sub_inst_n, find_inst in *; congruence.
        * apply Insts0 in Find.
          clear Insts Insts0.
          induction eqs as [|[]]; simpl in Find; try contradiction;
          inv Nodup;
          inversion_clear Heqs as [|?? Heq]; auto.
          apply InMembers_app in Find; destruct Find as [Find|]; auto.
          cases; inv Find; try contradiction.
          inversion_clear Heq as [|??????????? Hd|??????????????? Hd|];
            inv Hd; unfold sub_inst_n, find_inst in *; congruence.
      + setoid_rewrite Env.Props.P.F.find_mapsto_iff.
        intros i e e' Find Find0.
        assert (InMembers i (gather_insts eqs)) as Hin by (apply Insts; congruence).
        clear Insts Insts0.
        induction eqs as [|[]]; simpl in Hin; try contradiction;
          inv Nodup;
          inversion_clear Heqs as [|?? Heq]; auto.
        apply InMembers_app in Hin; destruct Hin as [Hin|]; auto.
        cases; inv Hin; try contradiction.
        inversion_clear Heq as [|??????????? Hd Find' ?? Hck|??????????????? Hd Find' ?? Hck ?? Reset|];
          inv Hd; unfold sub_inst_n, find_inst in *;
            rewrite Find' in Find; inv Find; rewrite Find' in Find0; inv Find0; eauto.
        * eapply IH; eauto.
          intros k ?; specialize (Hck k).
          rewrite Absbk in Hck; auto.
          apply clock_of_instant_false.
          eapply not_subrate_clock_impl; eauto.
        * destruct (Reset (if rs n then pred (count rs n) else count rs n))
             as (Mn & Node_n & MemMask_n),
                (Reset (if rs 0 then pred (count rs 0) else count rs 0))
               as (M0 &?& MemMask_0).
          assert (Mn 0 ≋ M0 0) as E by (eapply same_initial_memory; eauto).
          rewrite MemMask_n, MemMask_0, <-E.
          -- eapply IH; eauto.
             intros k ?; specialize (Hck k).
             rewrite Absbk in Hck; auto.
             apply absent_list_mask, clock_of_instant_false.
             eapply not_subrate_clock_impl; eauto.
          -- simpl; cases.
          -- destruct (rs n) eqn: Hr; auto.
             apply count_true_ge_1 in Hr.
             erewrite <-Lt.S_pred; eauto.
  Qed.

  Theorem msem_node_absent_until:
    forall n0 G f xss M yss,
      Ordered_nodes G ->
      msem_node G f xss M yss ->
      (forall n, n < n0 -> absent_list (xss n)) ->
      forall n, n <= n0 -> M n ≋ M 0.
  Proof.
    induction G as [|node].
    inversion 2;
      match goal with Hf: find_node _ [] = _ |- _ => inversion Hf end.
    intros * Hord Hsem Abs n Spec.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [??????? Clock Hfind Ins ?? Heqs].
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


  (** The other way around  *)

  Lemma mfby_fby:
    forall x v0 es M xs,
      mfby x v0 es M xs ->
      xs ≈ fby v0 es.
  Proof.
    intros * (Init & Spec) n.
    unfold fby.
    pose proof (Spec n) as Spec'.
    destruct (find_val x (M n)) eqn: Find_n; try contradiction.
    destruct (es n); destruct Spec' as (?& Hx); auto.
    rewrite Hx.
    clear - Init Spec Find_n.
    revert dependent v.
    induction n; intros; simpl; try congruence.
    specialize (Spec n).
    destruct (find_val x (M n)); try contradiction.
    destruct (es n); destruct Spec; try congruence.
    apply IHn; congruence.
  Qed.

  Theorem msem_sem_node_equation:
    forall G,
      (forall f xss M yss,
          msem_node G f xss M yss ->
          sem_node G f xss yss)
      /\
      (forall bk H M eq,
          msem_equation G bk H M eq ->
          sem_equation G bk H eq).
  Proof.
    intros; apply msem_node_equation_ind;
      [intros|intros|intros ?????????????????????? Rst|intros|intros];
      eauto using sem_equation, mfby_fby, sem_node.
    - econstructor; eauto; intro k; destruct (Rst k) as (?&?&?); intuition.
    - econstructor; auto.
      + eauto.
      + rewrite <-mfby_fby; eauto.
  Qed.

  Corollary msem_sem_node:
    forall G f xss M yss,
      msem_node G f xss M yss ->
      sem_node G f xss yss.
  Proof.
    intros; eapply (proj1 (msem_sem_node_equation G)); eauto.
  Qed.

  Corollary msem_sem_equation:
    forall G bk H M eq,
      msem_equation G bk H M eq ->
      sem_equation G bk H eq.
  Proof.
    intros; eapply (proj2 (msem_sem_node_equation G)); eauto.
  Qed.

  Corollary msem_sem_equations:
    forall G bk H M eqs,
      Forall (msem_equation G bk H M) eqs ->
      Forall (sem_equation G bk H) eqs.
  Proof.
    induction 1; constructor; eauto using msem_sem_equation.
  Qed.

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
