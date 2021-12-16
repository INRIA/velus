From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Arith.Compare_dec.

From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import VelusMemory.
From Velus Require Import IndexedStreams.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.IsVariable.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import CoreExpr.CESemantics.
From Velus Require Import NLustre.NLIndexedSemantics.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.Memories.
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

Module Type NLMEMSEMANTICS
       (Import Ids      : IDS)
       (Import Op       : OPERATORS)
       (Import OpAux    : OPERATORS_AUX       Ids Op)
       (Import Cks      : CLOCKS              Ids Op OpAux)
       (Import CESyn    : CESYNTAX            Ids Op OpAux Cks)
       (Import Syn      : NLSYNTAX            Ids Op OpAux Cks CESyn)
       (Import Str      : INDEXEDSTREAMS      Ids Op OpAux Cks)
       (Import Ord      : NLORDERED           Ids Op OpAux Cks CESyn Syn)
       (Import CESem    : CESEMANTICS         Ids Op OpAux Cks CESyn     Str)
       (Import Sem      : NLINDEXEDSEMANTICS  Ids Op OpAux Cks CESyn Syn Str Ord CESem)
       (Import Mem      : MEMORIES            Ids Op OpAux Cks CESyn Syn)
       (Import IsD      : ISDEFINED           Ids Op OpAux Cks CESyn Syn                 Mem)
       (Import IsV      : ISVARIABLE          Ids Op OpAux Cks CESyn Syn                 Mem IsD)
       (Import NoD      : NODUP               Ids Op OpAux Cks CESyn Syn                 Mem IsD IsV)
       (Import CEClo    : CECLOCKING          Ids Op OpAux Cks CESyn)
       (Import Clo      : NLCLOCKING          Ids Op OpAux Cks CESyn Syn     Ord         Mem IsD CEClo)
       (Import CECloSem : CECLOCKINGSEMANTICS Ids Op OpAux Cks CESyn     Str     CESem                     CEClo)
       (Import CloSem   : NLCLOCKINGSEMANTICS Ids Op OpAux Cks CESyn Syn Str Ord CESem Sem Mem IsD CEClo Clo CECloSem).

  Definition memories := stream (memory value).

  Definition memory_masked (k: nat) (rs: cstream) (M Mk: memories) :=
    forall n,
      count rs n = (if rs n then S k else k) ->
      M n = Mk n.

  Definition mfbyreset (x: ident) (c0: value) (xs: stream svalue) (rs: stream bool) (M: memories) (ys: stream svalue) : Prop :=
    find_val x (M 0) = Some c0
    /\ forall n, match find_val x (M n) with
           | Some mv =>
             match rs n, xs n with
             | false, absent =>
               find_val x (M (S n)) = Some mv
               /\ ys n = absent
             | true, absent =>
               find_val x (M (S n)) = Some c0
               /\ ys n = absent
             | false, present v =>
               find_val x (M (S n)) = Some v
               /\ ys n = present mv
             | true, present v =>
               find_val x (M (S n)) = Some v
               /\ ys n = present c0
             end
           | None => False
           end.

  Section NodeSemantics.

    Definition sub_inst_n (x: ident) (M M': memories) : Prop :=
      forall n, find_inst x (M n) = Some (M' n).

    Variable G: global.

    Definition memory_closed (M: memory value) (eqs: list equation) : Prop :=
      (forall i, find_inst i M <> None -> InMembers i (gather_insts eqs))
      /\ forall x, find_val x M <> None -> In x (map fst (gather_mems eqs)).

    Definition memory_closed_n (M: memories) (eqs: list equation) : Prop :=
      forall n, memory_closed (M n) eqs.

    Inductive msem_equation: stream bool -> history -> memories -> equation -> Prop :=
    | SEqDef:
        forall bk H M x ck xs ce,
          sem_var H x xs ->
          sem_caexp bk H ck ce xs ->
          msem_equation bk H M (EqDef x ck ce)
    | SEqApp:
        forall bk H M x xs ck f Mx arg xrs ys rs ls xss,
          hd_error xs = Some x ->
          sub_inst_n x M Mx ->
          sem_exps bk H arg ls ->
          sem_vars H xs xss ->
          sem_clock bk H ck (clock_of ls) ->
          Forall2 (sem_var H) (map fst xrs) ys ->
          bools_ofs ys rs ->
          (forall k, exists Mk,
                msem_node f (mask k rs ls) Mk (mask k rs xss)
                /\ memory_masked k rs Mx Mk) ->
          msem_equation bk H M (EqApp xs ck f arg xrs)
    | SEqFby:
        forall bk H M x ck ls xs c0 le xrs ys rs,
          sem_aexp bk H ck le ls ->
          sem_var H x xs ->
          Forall2 (sem_var H) (map fst xrs) ys ->
          sem_clocked_vars bk H xrs ->
          bools_ofs ys rs ->
          mfbyreset x (sem_const c0) ls rs M xs ->
          msem_equation bk H M (EqFby x ck c0 le xrs)

    with msem_node:
           ident -> stream (list svalue) -> memories -> stream (list svalue) -> Prop :=
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

  Global Hint Constructors msem_node msem_equation : nlsem.

  (** ** Induction principle for [msem_equation] and [msem_node] *)

  (** The automagically-generated induction principle is not strong
      enough: it does not support the internal fixpoint introduced by
      [Forall] *)

  Section msem_node_mult.

    Variable G: global.

    Variable P_equation: stream bool -> history -> memories -> equation -> Prop.
    Variable P_node: ident -> stream (list svalue) -> memories -> stream (list svalue) -> Prop.

    Hypothesis EqDefCase:
      forall bk H M x ck xs ce,
        sem_var H x xs ->
        sem_caexp bk H ck ce xs ->
        P_equation bk H M (EqDef x ck ce).

    Hypothesis EqAppCase:
      forall bk H M x xs ck f Mx arg xrs ys rs ls xss,
        hd_error xs = Some x ->
        sub_inst_n x M Mx ->
        sem_exps bk H arg ls ->
        sem_vars H xs xss ->
        sem_clock bk H ck (clock_of ls) ->
        Forall2 (sem_var H) (map fst xrs) ys ->
        bools_ofs ys rs ->
        (forall k, exists Mk,
              msem_node G f (mask k rs ls) Mk (mask k rs xss)
              /\ memory_masked k rs Mx Mk
              /\ P_node f (mask k rs ls) Mk (mask k rs xss)) ->
        P_equation bk H M (EqApp xs ck f arg xrs).

    Hypothesis EqFbyCase:
      forall bk H M x ck ls xs c0 le xrs ys rs,
        sem_aexp bk H ck le ls ->
        sem_var H x xs ->
        Forall2 (sem_var H) (map fst xrs) ys ->
        sem_clocked_vars bk H xrs ->
        bools_ofs ys rs ->
        mfbyreset x (sem_const c0) ls rs M xs ->
        P_equation bk H M (EqFby x ck c0 le xrs).

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
           (xss: stream (list svalue))
           (M: memories)
           (oss: stream (list svalue))
           (Sem: msem_node G f xss M oss) {struct Sem}
         : P_node f xss M oss.
    Proof.
      - destruct Sem; eauto.
        eapply EqAppCase; eauto.
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

  (** ** Properties *)

  (** *** Environment cons-ing lemmas *)

  Lemma msem_node_cons:
    forall n G f xs M ys enums,
      Ordered_nodes (Global enums (n :: G)) ->
      msem_node (Global enums (n :: G)) f xs M ys ->
      n.(n_name) <> f ->
      msem_node (Global enums G) f xs M ys.
  Proof.
    intros ?????? enums Hord Hsem Hnf.
    revert Hnf.
    induction Hsem as [ |????????????????????? Hsems|
                       |???????? Hf ????? IH]
        using msem_node_mult
      with (P_equation := fun bk H M eq =>
                            ~Is_node_in_eq n.(n_name) eq ->
                            msem_equation (Global enums G) bk H M eq);
      eauto with nlsem.
    - intro Hnin.
      econstructor; eauto.
      intro k; destruct (Hsems k) as (?&?&?& IH).
      eexists; split; eauto.
      apply IH; intro; apply Hnin; subst. constructor.
    - intro.
      rewrite find_node_other with (1:=Hnf) in Hf.
      econstructor; eauto.
      apply find_node_other_not_Is_node_in with (2:=Hf) in Hord.
      apply Is_node_in_Forall in Hord.
      apply Forall_Forall with (1:=Hord) in IH.
      apply Forall_impl with (2:=IH).
      intuition.
  Qed.

  Lemma msem_cons2:
    forall n G enums,
      Ordered_nodes (Global enums G) ->
      Forall (fun n' => n.(n_name) <> n'.(n_name)) G ->
      (forall f xv M yv,
          msem_node (Global enums G) f xv M yv ->
          msem_node (Global enums (n :: G)) f xv M yv)
      /\
      (forall bk R M eq,
          msem_equation (Global enums G) bk R M eq ->
          ~Is_node_in_eq n.(n_name) eq ->
          msem_equation (Global enums (n::G)) bk R M eq).
  Proof.
    intros n G enums OG Fn.
    apply msem_node_equation_ind; try (now intros; econstructor; eauto).
    - intros. econstructor; eauto. intro k.
      take (forall k, exists Mr, _) and specialize (it k);
        destruct it as (Mk & ? & ? & ?).
      exists Mk. split; auto.
    - intros.
      take (find_node f _ = Some _) and rename it into Ff.
      econstructor; eauto.
      + erewrite <-find_node_other in Ff; eauto.
        apply find_node_In in Ff as (? & Ff).
        rewrite Forall_forall in Fn. specialize (Fn _ Ff). now subst.
      + apply find_node_not_Is_node_in_eq with (g:=n.(n_name)) in Ff; auto.
        take (Forall _ n0.(n_eqs)) and rename it into Feqs.
        apply Forall_Forall with (1:=Ff) in Feqs.
        apply Forall_impl_In with (2:=Feqs).
        intros eq Ineq (? & ?); auto.
  Qed.

  Lemma msem_node_cons2:
    forall n G f xs M ys enums,
      Ordered_nodes (Global enums G) ->
      msem_node (Global enums G) f xs M ys ->
      Forall (fun n' => n_name n <> n_name n') G ->
      msem_node (Global enums (n :: G)) f xs M ys.
  Proof. intros; apply msem_cons2; auto. Qed.

  Local Hint Resolve msem_node_cons msem_cons2 msem_node_cons2 : nlsem.

  Lemma msem_equations_cons:
    forall G bk H M eqs n enums,
      Ordered_nodes (Global enums (n :: G)) ->
      ~Is_node_in n.(n_name) eqs ->
      (Forall (msem_equation (Global enums G) bk H M) eqs <->
       Forall (msem_equation (Global enums (n :: G)) bk H M) eqs).
  Proof.
    intros * Hord Hnini.
    induction eqs as [|eq eqs IH]; [now constructor|].
    apply not_Is_node_in_cons in Hnini as [Hnini Hninis].
    split; intros Hsem; apply Forall_cons2 in Hsem as [Heq Heqs];
      apply IH in Heqs; auto; constructor; auto.
    - inversion_clear Hord as [|?? []].
      destruct Heq as [|????????????????????? Hsems|]; eauto with nlsem.
      econstructor; eauto.
      intro k; destruct (Hsems k) as (?&?&?).
      eexists; split; eauto with nlsem.
    - inversion Heq as [|????????????????????? Hsems|]; subst; eauto with nlsem;
        assert (n.(n_name) <> f)
        by (intro HH; apply Hnini; rewrite HH; constructor).
      econstructor; eauto.
      intro k; destruct (Hsems k) as (?&?&?).
      eexists; split; eauto with nlsem.
  Qed.

  (** *** VelusMemory management *)

  Definition add_val_n (y: ident) (ms: stream value) (M: memories): memories :=
    fun n => add_val y (ms n) (M n).

  (* Lemma mfby_add_val_n: *)
  (*   forall x v0 ls M xs y ms, *)
  (*     x <> y -> *)
  (*     mfby x v0 ls M xs -> *)
  (*     mfby x v0 ls (add_val_n y ms M) xs. *)
  (* Proof. *)
  (*   unfold add_val_n. *)
  (*   intros * Hxy Fby; destruct Fby as (?& Spec). *)
  (*   split. *)
  (*   - rewrite find_val_gso; auto. *)
  (*   - intro n; rewrite 2 find_val_gso; auto; apply Spec. *)
  (* Qed. *)

  Lemma mfbyreset_add_val_n:
    forall x v0 ls rs M xs y ms,
      x <> y ->
      mfbyreset x v0 ls rs M xs ->
      mfbyreset x v0 ls rs (add_val_n y ms M) xs.
  Proof.
    unfold add_val_n.
    intros * Hxy Fby; destruct Fby as (?& Spec).
    split.
    - rewrite find_val_gso; auto.
    - intro n; rewrite 2 find_val_gso; auto; apply Spec.
  Qed.

  Definition add_inst_n (y: ident) (M' M: memories): memories :=
    fun n => add_inst y (M' n) (M n).

  (* Lemma mfby_add_inst_n: *)
  (*   forall x v0 ls M xs y My, *)
  (*     mfby x v0 ls M xs -> *)
  (*     mfby x v0 ls (add_inst_n y My M) xs. *)
  (* Proof. *)
  (*   inversion 1; econstructor; eauto. *)
  (* Qed. *)

  Lemma mfbyreset_add_inst_n:
    forall x v0 ls rs M xs y My,
      mfbyreset x v0 ls rs M xs ->
      mfbyreset x v0 ls rs (add_inst_n y My M) xs.
  Proof.
    inversion 1; econstructor; eauto.
  Qed.

  Local Hint Resolve mfbyreset_add_val_n mfbyreset_add_inst_n : nlsem.

  Lemma msem_equation_madd_val:
    forall G bk H M x ms eqs,
      ~Is_defined_in x eqs ->
      Forall (msem_equation G bk H M) eqs ->
      Forall (msem_equation G bk H (add_val_n x ms M)) eqs.
  Proof.
    intros * Hnd Hsem.
    induction eqs as [|eq eqs IH]; [now constructor|].
    apply not_Is_defined_in_cons in Hnd.
    destruct Hnd as [Hnd Hnds].
    apply Forall_cons2 in Hsem.
    destruct Hsem as [Hsem Hsems].
    constructor; [|now apply IH with (1:=Hnds) (2:=Hsems)].
    destruct Hsem; eauto with nlsem.
    apply not_Is_defined_in_eq_EqFby in Hnd; eauto with nlsem.
  Qed.

  Lemma msem_equation_madd_inst:
    forall G bk H M Mx x eqs,
      ~Is_defined_in x eqs ->
      Forall (msem_equation G bk H M) eqs ->
      Forall (msem_equation G bk H (add_inst_n x Mx M)) eqs.
  Proof.
    intros * Hnd Hsem.
    induction eqs as [|eq eqs IH]; [now constructor|].
    apply not_Is_defined_in_cons in Hnd.
    destruct Hnd as [Hnd Hnds].
    apply Forall_cons2 in Hsem.
    destruct Hsem as [Hsem Hsems].
    constructor; [|now apply IH with (1:=Hnds) (2:=Hsems)].
    destruct Hsem as [|??? x' ?????????? Hsome|];
      eauto with nlsem;
      assert (sub_inst_n x' (add_inst_n x Mx M) Mx0)
        by (apply not_Is_defined_in_eq_EqApp in Hnd;
            unfold add_inst_n in *; intro;
            rewrite find_inst_gso; auto; intro; subst x; destruct xs;
            inv Hsome; apply Hnd; now constructor);
      eauto with nlsem.
  Qed.

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
    forall M eqs x ck v0 e r vs,
      memory_closed_n M eqs ->
      memory_closed_n (add_val_n x vs M) (EqFby x ck v0 e r :: eqs).
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

  Section sem_msem_eq.

    Variable (G : global).

    Hypothesis Hnode :
      forall f xs ys,
        sem_node G f xs ys ->
        exists M, msem_node G f xs M ys.

    Theorem sem_msem_reset:
      forall f r xs ys,
        (forall k, sem_node G f (mask k r xs) (mask k r ys)) ->
        exists M,
        forall k, exists Mk, msem_node G f (mask k r xs) Mk (mask k r ys)
                   /\ memory_masked k r M Mk.
    Proof.
      intros * Sem.
      assert (forall k, exists Mk, msem_node G f (mask k r xs) Mk (mask k r ys)) as Msem
          by (intro; specialize (Sem k); apply Hnode in Sem; auto).
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
      forall bk H eqs M eq,
        sem_equation G bk H eq ->
        NoDup_defs (eq :: eqs) ->
        Forall (msem_equation G bk H M) eqs ->
        memory_closed_n M eqs ->
        exists M1, Forall (msem_equation G bk H M1) (eq :: eqs)
              /\ memory_closed_n M1 (eq :: eqs).
    Proof.
      intros * Heq NoDup Hmeqs WF.
      inversion Heq as [|
                        ??????????? Hls Hxs ? Hy Hr Hsem|
                        ??????????? Hle Hvar Hr Hbools Hfby]; subst.
      - exists M; eauto with nlsem.

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
            rewrite H0, <-H2, map_length; auto.
          }
          now apply length_hd_error.
        }
        erewrite hd_error_Some_hd; eauto; split.
        + constructor.
          * econstructor; eauto;
              unfold add_inst_n; intro; now apply find_inst_gss.
          * inv NoDup.
            apply hd_error_Some_In in Hsome.
            apply msem_equation_madd_inst; auto with nldef.
        + split; apply memory_closed_n_App; auto.

      - rewrite reset_fby_fbyreset in Hvar.
        exists (add_val_n x (holdreset (sem_const c0) ls rs) M);
          split.
        + constructor.
          * unfold add_val_n.
            econstructor; eauto.
            split; intros; unfold fbyreset;
              simpl; repeat rewrite find_val_gss; auto.
            destruct (rs n) eqn:Hrs, (ls n) eqn:Hls; auto.
          * inv NoDup.
            apply msem_equation_madd_val; auto with nldef.
        + split; apply memory_closed_n_Fby; auto.
    Qed.

    Lemma memory_closed_empty:
      memory_closed_n (fun _ : nat => empty_memory _) [].
    Proof.
      constructor; simpl.
      - setoid_rewrite find_inst_gempty; congruence.
      - setoid_rewrite find_val_gempty; congruence.
    Qed.

    Corollary sem_msem_eqs:
      forall bk H eqs,
        NoDup_defs eqs ->
        Forall (sem_equation G bk H) eqs ->
        exists M1, Forall (msem_equation G bk H M1) eqs
              /\ memory_closed_n M1 eqs.
    Proof.
      intros bk H eqs NoDup Heqs.
      induction eqs as [|eq eqs IHeqs].
      - exists (fun n => empty_memory _); split; auto.
        apply memory_closed_empty.
      - apply Forall_cons2 in Heqs as [Heq Heqs].
        eapply IHeqs in Heqs as (?&?&?).
        + eapply sem_msem_eq; eauto.
        + eapply NoDup_defs_cons; eauto.
    Qed.
  End sem_msem_eq.

  Theorem sem_msem_node:
    forall G f xs ys,
      Ordered_nodes G ->
      sem_node G f xs ys ->
      exists M, msem_node G f xs M ys.
  Proof.
    intros (enums & G); induction G as [|node].
    inversion 2;
      match goal with Hf: find_node _ (Global _ []) = _ |- _ => inversion Hf end.
    intros * Hord Hsem.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [??????? Hfind ??? Heqs].
    pose proof (find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    pose proof Hfind.
    apply option_map_inv in Hfind as ((?&?)& Hfind &?); simpl in *; subst.
    eapply find_unit_cons in Hfind as [[E Hfind]|[E Hfind]]; simpl; eauto.
    - assert (Hord':=Hord).
      inversion Hord as [|? ? [Hnneqs Hnn]]; subst.
      inv Hfind.
      eapply Forall_sem_equation_global_tl in Heqs; eauto.
      eapply sem_msem_eqs in Heqs as (M & ?&?); eauto using NoDup_defs_node.
      exists M.
      econstructor; eauto.
      rewrite <-msem_equations_cons; eauto.
    - apply sem_node_cons with (1:=Hord) in Hsem; auto.
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
      + assert (In x (map fst (gather_mems eqs))) as Hin by (apply Values1; congruence).
        clear Values1 Values2.
        induction eqs as [|[]]; simpl in Hin; try contradiction;
          inv Nodup;
          inversion_clear Heqs1 as [|?? Heq1];
          inversion_clear Heqs2 as [|?? Heq2]; auto.
        destruct Hin; auto; subst.
        inversion_clear Heq1 as [| |????????????????? (Find1'&?)];
          inversion_clear Heq2 as [| |????????????????? (Find2'&?)];
          unfold find_val in *; congruence.
      + assert (In x (map fst (gather_mems eqs))) as Hin by (apply Values1; congruence).
        clear Values1 Values2.
        induction eqs as [|[]]; simpl in Hin; try contradiction;
          inv Nodup;
          inversion_clear Heqs1 as [|?? Heq1];
          inversion_clear Heqs2 as [|?? Heq2]; auto.
        destruct Hin; auto; subst.
        inversion_clear Heq1 as [| |????????????????? (Find1'&?)];
          inversion_clear Heq2 as [| |????????????????? (Find2'&?)];
          unfold find_val in *; congruence.
      + assert (In x (map fst (gather_mems eqs))) as Hin by (apply Values2; congruence).
        clear Values1 Values2.
        induction eqs as [|[]]; simpl in Hin; try contradiction;
          inv Nodup;
          inversion_clear Heqs1 as [|?? Heq1];
          inversion_clear Heqs2 as [|?? Heq2]; auto.
        destruct Hin; auto; subst.
        inversion_clear Heq1 as [| |????????????????? (Find1'&?)];
          inversion_clear Heq2 as [| |????????????????? (Find2'&?)];
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
          inversion_clear Heq2 as [|?????????????? Hd|];
            inv Hd; unfold sub_inst_n, find_inst in *; congruence.
        * apply Insts2 in Find.
          clear Insts1 Insts2.
          induction eqs as [|[]]; simpl in Find; try contradiction;
          inv Nodup;
          inversion_clear Heqs1 as [|?? Heq1];
          inversion_clear Heqs2 as [|?? Heq2]; auto.
          apply InMembers_app in Find; destruct Find as [Find|]; auto.
          cases; inv Find; try contradiction.
          inversion_clear Heq1 as [|?????????????? Hd|];
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
        inversion Heq1 as [|?????????????? Hd1 Find1' ????? Reset1|]; subst;
          inversion_clear Heq2 as [|?????????????? Hd2 Find2' ????? Reset2|];
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
    intros (enums & G); induction G as [|node].
    inversion 2;
      match goal with Hf: find_node _ (Global _ []) = _ |- _ => inversion Hf end.
    intros * Hord Hsem1 Hsem2.
    assert (Hsem1' := Hsem1);  assert (Hsem2' := Hsem2).
    inversion_clear Hsem1' as [??????? Clock1 Hfind1 Ins1 ?? Heqs1];
      inversion_clear Hsem2' as [??????? Clock2 Hfind2 Ins2 ?? Heqs2].
    rewrite Hfind2 in Hfind1; inv Hfind1.
    inversion Hord as [|?? []]; subst.
    pose proof Hfind2.
    apply option_map_inv in Hfind2 as ((?&?)& Hfind2 &?); simpl in *; subst.
    eapply find_unit_cons in Hfind2 as [[E Hfind2]|[E Hfind2]]; simpl; eauto.
    - inv Hfind2.
      assert (~ Is_node_in node.(n_name) node.(n_eqs))
        by (eapply find_node_not_Is_node_in with (G := Global enums (node::G)); eauto).
      eapply msem_equations_cons in Heqs1; eauto.
      eapply msem_equations_cons in Heqs2; eauto.
      eapply msem_eqs_same_initial_memory; eauto.
      apply NoDup_defs_node.
    - eapply msem_node_cons in Hsem1; eapply msem_node_cons in Hsem2; eauto.
  Qed.

  (** Absent Until *)

  (* Lemma mfby_absent_until: *)
  (*   forall n0 x v0 ls M xs, *)
  (*     mfby x v0 ls M xs -> *)
  (*     (forall n, n < n0 -> ls n = absent) -> *)
  (*     forall n, n <= n0 -> find_val x (M n) = Some v0. *)
  (* Proof. *)
  (*   intros * Mfby Abs n E; induction n; *)
  (*     destruct Mfby as (Init & Spec); auto. *)
  (*   specialize (Spec n). *)
  (*   destruct (find_val x (M n)); try contradiction. *)
  (*   rewrite Abs in Spec; try lia. *)
  (*   destruct Spec as [->]. *)
  (*   apply IHn; lia. *)
  (* Qed. *)

  Lemma mfbyreset_absent_until:
    forall n0 x v0 ls rs M xs,
      mfbyreset x v0 ls rs M xs ->
      (forall n, n < n0 -> ls n = absent) ->
      forall n, n <= n0 -> find_val x (M n) = Some v0.
  Proof.
    intros * Mfby Abs n E; induction n;
      destruct Mfby as (Init & Spec); auto.
    specialize (Spec n).
    destruct (find_val x (M n)); try contradiction.
    rewrite Abs in Spec; try lia.
    destruct (rs n); destruct Spec as [->]; auto.
    apply IHn; lia.
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
      + assert (In x (map fst (gather_mems eqs))) as Hin by (apply Values; congruence).
        clear Values Values0.
        induction eqs as [|[]]; simpl in Hin; try contradiction;
          inv Nodup;
          inversion_clear Heqs as [|?? Heq]; auto.
        destruct Hin; auto; subst.
        inversion_clear Heq as [| |???????????? Sem ???? Mfby].
        pose proof Mfby as Mfby'; destruct Mfby'.
        eapply mfbyreset_absent_until in Mfby; unfold find_val in *; eauto; try congruence.
        intros k ?; specialize (Sem k). inv Sem; auto.
        rewrite Absbk in *; auto.
        exfalso; eapply not_subrate_clock; eauto.
      + assert (In x (map fst (gather_mems eqs))) as Hin by (apply Values; congruence).
        clear Values Values0.
        induction eqs as [|[]]; simpl in Hin; try contradiction;
          inv Nodup;
          inversion_clear Heqs as [|?? Heq]; auto.
        destruct Hin; auto; subst.
        inversion_clear Heq as [| |???????????? Sem ???? Mfby].
        pose proof Mfby as Mfby'; destruct Mfby'.
        eapply mfbyreset_absent_until in Mfby; unfold find_val in *; eauto; try congruence.
      + assert (In x (map fst (gather_mems eqs))) as Hin by (apply Values0; congruence).
        clear Values Values0.
        induction eqs as [|[]]; simpl in Hin; try contradiction;
          inv Nodup;
          inversion_clear Heqs as [|?? Heq]; auto.
        destruct Hin; auto; subst.
        inversion_clear Heq as [| |???????????? Sem ???? Mfby].
        pose proof Mfby as Mfby'; destruct Mfby'.
        eapply mfbyreset_absent_until in Mfby; unfold find_val in *; eauto; try congruence.
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
          inversion_clear Heq as [|?????????????? Hd|];
            inv Hd; unfold sub_inst_n, find_inst in *; congruence.
        * apply Insts0 in Find.
          clear Insts Insts0.
          induction eqs as [|[]]; simpl in Find; try contradiction;
          inv Nodup;
          inversion_clear Heqs as [|?? Heq]; auto.
          apply InMembers_app in Find; destruct Find as [Find|]; auto.
          cases; inv Find; try contradiction.
          inversion_clear Heq as [|?????????????? Hd|];
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
        inversion_clear Heq as [|?????????????? Hd Find' ?? Hck ?? Reset|];
          inv Hd; unfold sub_inst_n, find_inst in *;
            rewrite Find' in Find; inv Find; rewrite Find' in Find0; inv Find0; eauto.
        destruct (Reset (if rs n then pred (count rs n) else count rs n))
          as (Mn & Node_n & MemMask_n),
             (Reset (if rs 0 then pred (count rs 0) else count rs 0))
            as (M0 &?& MemMask_0).
        assert (Mn 0 ≋ M0 0) as E by (eapply same_initial_memory; eauto).
        rewrite MemMask_n, MemMask_0, <-E.
        * eapply IH; eauto.
          intros k ?; specialize (Hck k).
          rewrite Absbk in Hck; auto.
          apply absent_list_mask, clock_of_instant_false.
          eapply not_subrate_clock_impl; eauto.
        * simpl; cases.
        * destruct (rs n) eqn: Hr; auto.
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
    intros ? (?& G); induction G as [|node].
    inversion 2;
      match goal with Hf: find_node _ (Global _ []) = _ |- _ => inversion Hf end.
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
    apply option_map_inv in Hfind as ((?&?)& Hfind &?); simpl in *; subst.
    eapply find_unit_cons in Hfind as [[E Hfind]|[E Hfind]]; simpl; eauto.
    - inv Hfind.
      eapply msem_equations_cons in Heqs; eauto.
      eapply msem_eqs_absent_until; eauto.
      apply NoDup_defs_node.
    - eapply msem_node_cons in Hsem; eauto.
  Qed.


  (** The other way around  *)

  (* Lemma mfby_fby: *)
  (*   forall x v0 es M xs, *)
  (*     mfby x v0 es M xs -> *)
  (*     xs ≈ fby v0 es. *)
  (* Proof. *)
  (*   intros * (Init & Spec) n. *)
  (*   unfold fby. *)
  (*   pose proof (Spec n) as Spec'. *)
  (*   destruct (find_val x (M n)) eqn: Find_n; try contradiction. *)
  (*   destruct (es n); destruct Spec' as (?& Hx); auto. *)
  (*   rewrite Hx. *)
  (*   clear - Init Spec Find_n. *)
  (*   revert dependent v. *)
  (*   induction n; intros; simpl; try congruence. *)
  (*   specialize (Spec n). *)
  (*   destruct (find_val x (M n)); try contradiction. *)
  (*   destruct (es n); destruct Spec; try congruence. *)
  (*   apply IHn; congruence. *)
  (* Qed. *)

  (* Lemma mfby_hold: *)
  (*   forall x v0 es M xs, *)
  (*     mfby x v0 es M xs -> *)
  (*     forall n, find_val x (M n) = Some (hold v0 es n). *)
  (* Proof. *)
  (*   intros * (Init & Spec) n. *)
  (*   induction n; simpl. *)
  (*   - congruence. *)
  (*   - specialize (Spec n). rewrite IHn in Spec. *)
  (*     destruct (es n); destruct Spec as (?& Hx); auto. *)
  (* Qed. *)

  Lemma mfbyreset_fbyreset:
    forall x v0 es rs M xs,
      mfbyreset x v0 es rs M xs ->
      xs ≈ fbyreset v0 es rs.
  Proof.
    intros * (Init & Spec) n.
    unfold fbyreset.
    pose proof (Spec n) as Spec'.
    destruct (find_val x (M n)) eqn: Find_n; try contradiction.
    destruct (rs n), (es n); destruct Spec' as (?& Hx); auto.
    rewrite Hx.
    clear - Init Spec Find_n.
    revert dependent v.
    induction n; intros; simpl. destruct (rs 0); congruence.
    specialize (Spec n).
    destruct (find_val x (M n)); try contradiction.
    destruct (rs n), (es n); try destruct Spec; try congruence.
    eapply IHn. congruence.
  Qed.

  Lemma mfbyreset_holdreset:
    forall x v0 es rs M xs,
      mfbyreset x v0 es rs M xs ->
      forall n, find_val x (M n) = Some (holdreset v0 es rs n).
  Proof.
    intros * (Init & Spec) n.
    induction n; simpl.
    - congruence.
    - specialize (Spec n). rewrite IHn in Spec.
      destruct (rs n), (es n); destruct Spec as (?&Hx); auto.
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
      [intros|intros ????????????????????? Rst|intros|intros];
      eauto using sem_equation, sem_node.
    - econstructor; eauto; intro k; destruct (Rst k) as (?&?&?); intuition.
    - econstructor; auto.
      1,3,4:eauto.
      rewrite reset_fby_fbyreset, <- mfbyreset_fbyreset; eauto.
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

End NLMEMSEMANTICS.

Module NLMemSemanticsFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX       Ids Op)
       (Cks   : CLOCKS              Ids Op OpAux)
       (CESyn : CESYNTAX            Ids Op OpAux Cks)
       (Syn   : NLSYNTAX            Ids Op OpAux Cks CESyn)
       (Str   : INDEXEDSTREAMS      Ids Op OpAux Cks)
       (Ord   : NLORDERED           Ids Op OpAux Cks CESyn Syn)
       (CESem : CESEMANTICS         Ids Op OpAux Cks CESyn     Str)
       (Sem   : NLINDEXEDSEMANTICS  Ids Op OpAux Cks CESyn Syn Str Ord CESem)
       (Mem   : MEMORIES            Ids Op OpAux Cks CESyn Syn)
       (IsD   : ISDEFINED           Ids Op OpAux Cks CESyn Syn                 Mem)
       (IsV   : ISVARIABLE          Ids Op OpAux Cks CESyn Syn                 Mem IsD)
       (NoD   : NODUP               Ids Op OpAux Cks CESyn Syn                 Mem IsD IsV)
       (CEClo : CECLOCKING          Ids Op OpAux Cks CESyn)
       (Clo   : NLCLOCKING          Ids Op OpAux Cks CESyn Syn     Ord         Mem IsD CEClo)
       (CECloSem : CECLOCKINGSEMANTICS Ids Op OpAux Cks CESyn     Str     CESem                     CEClo)
       (CloSem   : NLCLOCKINGSEMANTICS Ids Op OpAux Cks CESyn Syn Str Ord CESem Sem Mem IsD CEClo Clo CECloSem)
<: NLMEMSEMANTICS Ids Op OpAux Cks CESyn Syn Str Ord CESem Sem Mem IsD IsV NoD CEClo Clo CECloSem CloSem.
  Include NLMEMSEMANTICS Ids Op OpAux Cks CESyn Syn Str Ord CESem Sem Mem IsD IsV NoD CEClo Clo CECloSem CloSem.
End NLMemSemanticsFun.
