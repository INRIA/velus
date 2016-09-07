Require Import Coq.FSets.FMapPositive.
Require Import PArith.
Require Import Rustre.Common.
Require Import Rustre.Minimp.Syntax.
Require Import Rustre.Dataflow.Syntax.
Require Import Rustre.Dataflow.Memories.

Require Import List.
Require Import Coq.Lists.List.
Import List.ListNotations.
Require Import Coq.Sorting.Permutation.
Require Import Morphisms.

Open Scope positive.
Open Scope list.

(** * Translation *)

(** ** Identification of node instances *)

(** 

Each node application in CoreDF turns into a method call in the
imperative setting. This means that, upon initializing a node, one
must declare a new instance for each its application.

Remark: it is necessary to distinguish different instantiations of the
same node (i.e., different objects of the same class). This is done in
Auger's thesis in the language LSNI, where node applications are
assigned unique identifiers. His context is richer, in particular,
because the result of a node application may be assigned to a
pattern-tuple containing multiple identifiers.

Here, we take advantage of the fact that the result of a node
application is assigned to a single variable. We use the name of that
variable to identify the instance.  *)

Module Type TRANSLATION
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import SynDF : Rustre.Dataflow.Syntax.SYNTAX Ids Op)
       (Import SynMP : Rustre.Minimp.Syntax.SYNTAX Ids Op OpAux)
       (Import Mem   : MEMORIES Ids Op SynDF).

  (* definition is needed in signature *)
  Definition gather_eq
             (acc: list ident * list (ident * ident)) (eq: equation) :=
    match eq with
    | EqDef _ _ _     => acc
    | EqApp x _ f _ _ => (fst acc, (x, f) :: snd acc)
    | EqFby x _ _ _ => (x::fst acc, snd acc)
    end.

  (* definition is needed in signature *)
  Definition gather_eqs
             (eqs: list equation) : list ident * list (ident * ident) :=
    List.fold_left gather_eq eqs ([], []).

  (** ** Translation *)

  Section Translate.

    Variable memories : PS.t.

    (* =tovar= *)
    Definition tovar (xt: ident * typ) : exp :=
      let (x, ty) := xt in
      if PS.mem x memories then State x ty else Var x ty.
    (* =end= *)

    (* =control= *)
    (* definition is needed in signature *)
    Fixpoint Control (ck: clock) (s: stmt) : stmt :=
      match ck with
      | Cbase => s
      | Con ck x true  => Control ck (Ifte (tovar (x, bool_typ)) s Skip)
      | Con ck x false => Control ck (Ifte (tovar (x, bool_typ)) Skip s)
      end.
    (* =end= *)

    (* =translate_lexp= *)
    (* definition is needed in signature *)
    Fixpoint translate_lexp (e : lexp) : exp :=
      match e with
      | Econst c => Const c
      | Evar x ty => tovar (x, ty)
      | Ewhen e c x => translate_lexp e
      | Eunop op e ty => Unop op (translate_lexp e) ty
      | Ebinop op e1 e2 ty => Binop op (translate_lexp e1) (translate_lexp e2) ty
      end.
    (* =end= *)

    (* =translate_cexp= *)
    (* definition is needed in signature *)
    Fixpoint translate_cexp (x: ident) (e: cexp) : stmt :=
      match e with
      | Emerge y ty t f => Ifte (tovar (y, ty))
                                (translate_cexp x t)
                                (translate_cexp x f)
      | Eite b t f => Ifte (translate_lexp b)
                           (translate_cexp x t)
                           (translate_cexp x f)
      | Eexp l => Assign x (translate_lexp l)
      end.
    (* =end= *)

    (* =translate_eqn= *)
    (* definition is needed in signature *)
    Definition translate_eqn (eqn: equation) : stmt :=
      match eqn with
      | EqDef x ck ce => Control ck (translate_cexp x ce)
      | EqApp x ck f les ty =>
          Control ck (Call [(x, ty)] f x step (List.map translate_lexp les))
      | EqFby x ck v le => Control ck (AssignSt x (translate_lexp le))
      end.
    (* =end= *)

  (*   (** Remark: eqns ordered in reverse order of execution for coherence with *)
  (*      [Is_well_sch]. *) *)

    (* =translate_eqns= *)
    (* definition is needed in signature *)
    Definition translate_eqns (eqns: list equation) : stmt :=
      List.fold_left (fun i eq => Comp (translate_eqn eq) i) eqns Skip.
    (* =end= *)

  End Translate.

  (* =translate_reset_eqn= *)
  (* definition is needed in signature *)
  Definition translate_reset_eqn (s: stmt) (eqn: equation) : stmt :=
    match eqn with
    | EqDef _ _ _ => s
    | EqFby x _ c0 _  => Comp (AssignSt x (Const c0)) s
    | EqApp x _ f _ _ => Comp (Call [] f x reset []) s
    end.
  (* =end= *)

  (* =translate_reset_eqns= *)
  (* definition is needed in signature *)
  Definition translate_reset_eqns (eqns: list equation): stmt :=
    List.fold_left translate_reset_eqn eqns Skip.
  (* =end= *)

  (* definition is needed in signature *)
  Definition ps_from_list (l: list ident) : PS.t :=
    List.fold_left (fun s i=>PS.add i s) l PS.empty.

  Hint Constructors NoDupMembers VarsDeclared.
  
  Program Definition reset_method (eqns: list equation): method :=
    {| m_name := reset;
       m_in   := [];
       m_vars := [];
       m_out  := [];
       m_body := translate_reset_eqns eqns;
       m_nodupvars := _;
       m_varsdecl  := _;
       m_good      := _
    |}.
  Next Obligation.
    unfold translate_reset_eqns.
    cut(forall s,
           VarsDeclared [] s ->
           VarsDeclared [] (List.fold_left translate_reset_eqn eqns s)); auto.
    induction eqns as [|eq eqns]; auto.
    destruct eq; auto;
      simpl; intros; apply IHeqns.
    (* TODO: get auto to solve this goal completely *)
    - constructor; auto.
      constructor; auto.
      apply List.incl_refl.
    - constructor; auto.
      constructor; auto.
      constructor; auto.
  Qed.

  (** Properties of translation functions *)

  Instance eq_equiv : Equivalence PS.eq.
  Proof. firstorder. Qed.

  Instance List_fold_left_add_Proper (xs: list ident) :
    Proper (PS.eq ==> PS.eq)
           (List.fold_left (fun s i => PS.add i s) xs).
  Proof.
    induction xs as [|x xs IH]; intros S S' Heq; [exact Heq|].
    assert (PS.eq (PS.add x S) (PS.add x S')) as Heq'
        by (rewrite Heq; reflexivity).
    simpl; rewrite Heq'; reflexivity.
  Qed.

  Instance List_fold_left_memory_eq_Proper (eqs: list equation) :
    Proper (PS.eq ==> PS.eq)
           (List.fold_left memory_eq eqs).
  Proof.
    induction eqs as [|eq eqs IH]; intros S S' Heq; [exact Heq|].
    simpl.
    apply IH.
    destruct eq; [apply Heq|apply Heq|].
    simpl; rewrite Heq; reflexivity.
  Qed.

  Lemma add_ps_from_list_cons:
    forall xs x, PS.eq (PS.add x (ps_from_list xs))
                  (ps_from_list (x::xs)).
  Proof.
    intros; unfold ps_from_list; simpl.
    generalize PS.empty as S.
    induction xs as [|y xs IH]; [ reflexivity | ].
    intro S; simpl; rewrite IH; rewrite PSP.add_add; reflexivity.
  Qed.

  Lemma ps_from_list_gather_eqs_memories:
    forall eqs, PS.eq (ps_from_list (fst (gather_eqs eqs))) (memories eqs).
  Proof.
    induction eqs as [|eq eqs IH]; [reflexivity|].
    unfold memories, gather_eqs.
    assert (forall eqs F S,
               PS.eq (ps_from_list (fst (List.fold_left gather_eq eqs (F, S))))
                     (List.fold_left memory_eq eqs (ps_from_list F))) as HH.
    { clear eq eqs IH; induction eqs as [|eq eqs IH]; [reflexivity|].
      intros F S.
      destruct eq; [now apply IH|now apply IH|].
      simpl; rewrite IH; rewrite add_ps_from_list_cons; reflexivity. }
    rewrite HH; reflexivity.
  Qed.

  Instance tovar_Proper :
    Proper (PS.eq ==> eq ==> eq) tovar.
  Proof.
    intros M M' HMeq x x' Hxeq; rewrite <- Hxeq; clear Hxeq x'.
    unfold tovar; destruct x as [x ty].
    destruct (PS.mem x M) eqn:Hmem;
      rewrite <- HMeq, Hmem; reflexivity.
  Qed.

  Instance translate_lexp_Proper :
    Proper (PS.eq ==> eq ==> eq) translate_lexp.
  Proof.
    intros M M' HMeq e e' Heq; rewrite <- Heq; clear Heq e'.
    revert M M' HMeq.
    induction e (* using lexp_ind2 *); intros M M' HMeq; simpl; auto.
    + rewrite HMeq; auto.
    + f_equal; auto.
    + f_equal; auto.
  Qed.

  Instance translate_cexp_Proper :
    Proper (PS.eq ==> eq ==> eq ==> eq) translate_cexp.
  Proof.
    intros M M' HMeq y y' Hyeq c c' Hceq; rewrite <- Hyeq, <- Hceq;
    clear y' c' Hyeq Hceq.
    revert M M' HMeq.
    induction c; intros; simpl.
    - erewrite IHc1; try eassumption.
      erewrite IHc2; try eassumption. 
      rewrite HMeq; auto.
    - erewrite IHc1; try eassumption.
      erewrite IHc2; try eassumption. 
      rewrite HMeq; auto.
    - rewrite HMeq; auto.
  Qed.

  Instance Control_Proper :
    Proper (PS.eq ==> eq ==> eq ==> eq) Control.
  Proof.
    intros M M' HMeq ck ck' Hckeq e e' Heq; rewrite <-Hckeq, <-Heq;
    clear ck' e' Hckeq Heq.
    revert e; induction ck as [ |ck' IH s sv].
    - reflexivity.
    - intro e.
      destruct sv; simpl; rewrite IH, HMeq; reflexivity.
  Qed.

  Instance translate_eqn_Proper :
    Proper (PS.eq ==> eq ==> eq) translate_eqn.
  Proof.
    intros M M' HMeq eq eq' Heq; rewrite <- Heq; clear Heq eq'.
    destruct eq as [y ck []|y ck f []|y ck v0 []]; simpl; try now rewrite HMeq.
    - rewrite HMeq at 1 2. do 3 f_equal.
      apply List.map_ext. intro. now rewrite HMeq.
  Qed.

  Instance translate_eqns_Proper :
    Proper (PS.eq ==> eq ==> eq) translate_eqns.
  Proof.
    intros M M' Heq eqs eqs' Heqs.
    rewrite <- Heqs; clear Heqs.
    unfold translate_eqns.
    assert (forall S S',
               S = S' ->
               List.fold_left (fun i eq => Comp (translate_eqn M eq) i) eqs S
               = List.fold_left (fun i eq => Comp (translate_eqn M' eq) i) eqs S')
      as HH.
    { revert M M' Heq.
      induction eqs as [|eq eqs IH]; intros M M' Heq S S' HSeq; [apply HSeq|].
      simpl; apply IH with (1:=Heq); rewrite HSeq, Heq; reflexivity. }
    rewrite HH with (S':=Skip); reflexivity.
  Qed.

  Definition is_fby (eq: equation) : bool :=
    match eq with
    | EqFby _ _ _ _ => true
    | _ => false
    end.

  Definition is_app (eq: equation) : bool :=
    match eq with
    | EqApp _ _ _ _ _ => true
    | _ => false
    end.

  Definition is_def (eq: equation) : bool :=
    match eq with
    | EqDef _ _ _ => true
    | _ => false
    end.

  Lemma is_filtered_eqs:
    forall eqs,
      Permutation
        (filter is_def eqs ++ filter is_app eqs ++ filter is_fby eqs)
        eqs.
  Proof.
    induction eqs as [|eq eqs]; auto.
    destruct eq; simpl.
    - now apply Permutation_cons.
    - rewrite <-Permutation_cons_app.
      apply Permutation_cons; reflexivity.
      now symmetry.
    - symmetry.
      rewrite <-Permutation_app_assoc.
      apply Permutation_cons_app.
      rewrite Permutation_app_assoc.
      now symmetry.
  Qed.

  Lemma filter_app:
    forall {A} (p:A->bool) xs ys,
      filter p xs ++ filter p ys = filter p (xs ++ ys).
  Proof.
    induction xs as [|x xs]; intro ys; auto.
    simpl; destruct (p x); simpl; rewrite IHxs; auto.
  Qed.

  Lemma filter_mem_fst:
    forall p (xs: list (ident * typ)),
      map fst (filter (fun (x:ident*typ)=>PS.mem (fst x) p) xs)
      = filter (fun x=>PS.mem x p) (map fst xs).
  Proof.
    induction xs as [|x xs]; auto.
    simpl.
    destruct (PS.mem (fst x) p); simpl;
      now rewrite IHxs.
  Qed.

  Instance Permutation_filter_Proper {A} (p:A->bool):
    Proper (@Permutation A ==> @Permutation A) (filter p).
  Proof.
    Hint Constructors Permutation.
    intros xs ys Hperm.
    induction Hperm; simpl; auto.
    - destruct (p x); auto.
    - destruct (p x); destruct (p y); auto.
    - now rewrite IHHperm1, IHHperm2.
  Qed.

  Lemma in_memories_var_defined:
    forall x eqs,
      PS.In x (memories eqs) ->
      In x (map var_defined eqs).
  Proof.
    intros x eqs Hin.
    induction eqs as [|eq eqs].
    now apply PSF.empty_iff in Hin.
    unfold memories in *. simpl in *.
    apply In_fold_left_memory_eq in Hin.
    destruct Hin as [Hin|Hin].
    - specialize (IHeqs Hin). now right.
    - destruct eq; simpl in Hin;
        try (apply PSF.empty_iff in Hin; contradiction).
      apply PS.add_spec in Hin.
      destruct Hin as [Hin|Hin].
      now subst; simpl; left.
      now apply PSF.empty_iff in Hin.
  Qed.
      
  Lemma in_memories_is_fby:
    forall eqs eq,
      In eq eqs ->
      NoDup (map var_defined eqs) ->
      PS.mem (var_defined eq) (memories eqs) = is_fby eq.
  Proof.
    induction eqs as [|eq eqs].
    now intuition.
    intros eq' Hin Hndup.
    simpl in Hndup. apply NoDup_cons' in Hndup.
    destruct Hndup as [Hnin Hndup].
    unfold memories.
    destruct Hin as [|Hin].
    - subst eq'.
      destruct eq; simpl in *;
        try (apply mem_spec_false; intro HH; apply Hnin;
             apply in_memories_var_defined with (1:=HH)).
      apply PS.mem_spec.
      apply In_fold_left_memory_eq.
      right. apply PS.add_spec. now left.
    - specialize (IHeqs _ Hin Hndup).
      unfold memories in *.
      destruct eq; simpl; try apply IHeqs; auto.
      simpl in Hnin.
      destruct eq'; simpl;
        try (apply mem_spec_false; intro HH;
             apply In_fold_left_memory_eq in HH;
             destruct HH as [HH|HH];
             apply mem_spec_false in IHeqs;
             try contradiction;
             try (apply PS.add_spec in HH; destruct HH as [HH|HH];
                  subst)).
      + apply Hnin.
        clear Hnin IHeqs.
        induction eqs.
        simpl in *. contradiction.
        inversion_clear Hin as [|Hin']; subst.
        now left.
        simpl in *; apply NoDup_cons' in Hndup.
        destruct Hndup as [Hnin Hndup].
        specialize (IHeqs Hndup Hin').
        right; assumption.
      + now apply not_In_empty in HH.
      + apply Hnin.
        clear Hnin IHeqs.
        induction eqs.
        simpl in *. contradiction.
        inversion_clear Hin as [|Hin']; subst.
        now left.
        simpl in *; apply NoDup_cons' in Hndup.
        destruct Hndup as [Hnin Hndup].
        specialize (IHeqs Hndup Hin').
        right; assumption.
      + now apply not_In_empty in HH.
      + simpl in IHeqs.
        apply PS.mem_spec.
        apply In_fold_left_memory_eq.
        left. now rewrite PS.mem_spec in IHeqs.
  Qed.

  Lemma fst_partition_memories_var_defined:
    forall n,
      Permutation
        (map fst (fst (partition
                         (fun x=>PS.mem (fst x) (memories n.(n_eqs)))
                         n.(n_vars))))
        (map var_defined (filter is_fby n.(n_eqs))).
  Proof.
    intro n.
    match goal with |- Permutation (map fst (fst (partition ?p ?l))) _ =>
      assert (Permutation (map fst (fst (partition p l)))
                          (map fst (filter p n.(n_vars))))
        as Hperm by (apply Permutation_map_aux; apply partition_filter)
    end.
    rewrite Hperm; clear Hperm.
    match goal with |- context[filter ?p ?l] =>
      rewrite <-(app_nil_r (filter p l))
    end.
    assert (filter (fun x=>PS.mem (fst x) (memories n.(n_eqs))) [n.(n_out)]
            = []) as Hfout.
    { simpl.
      match goal with |- (if ?p then _ else _) = _ => destruct p eqn:Heq end;
        auto.
      rewrite PS.mem_spec in Heq.
      contradiction (n.(n_vout)). }
    rewrite <-Hfout; clear Hfout.
    rewrite filter_app, filter_mem_fst, <-n_defd.
    remember (memories n.(n_eqs)) as mems.
    set (P:=fun eqs eq=> In eq eqs ->
                         PS.mem (var_defined eq) mems = is_fby eq).
    assert (forall eq, P n.(n_eqs) eq) as Peq.
    { subst P mems.
      intro. intro Hin. apply in_memories_is_fby; auto.
      rewrite n_defd.
      apply fst_NoDupMembers.
      pose proof (n.(n_nodup)) as Hnodup.
      now apply NoDupMembers_app_r in Hnodup.
    }
    clear Heqmems.
    induction n.(n_eqs) as [|eq eqs]; auto.
    assert (forall eq, P eqs eq) as Peq'
        by (intros e Hin; apply Peq; constructor (assumption)).
    specialize (IHeqs Peq'). clear Peq'.
    destruct eq eqn:Heq; simpl;
      specialize (Peq eq); red in Peq; subst eq;
      simpl in Peq; (rewrite Peq; [|now intuition]);
      rewrite IHeqs; auto.
  Qed.

  Lemma fst_gather_eqs_var_defined:
    forall n,
      map fst (snd (gather_eqs n.(n_eqs)))
      = map var_defined (filter is_app n.(n_eqs)).
  Proof.
    
  Admitted.
  
  Lemma VarsDeclared_translate_eqns:
    forall n,
      VarsDeclared
        (snd (partition (fun x=> PS.mem (fst x) (memories n.(n_eqs))) n.(n_vars))
         ++ [n.(n_out)])
        (translate_eqns (memories n.(n_eqs)) n.(n_eqs)).
  Proof.
  Admitted.

  Lemma MemsDeclared_translate_eqns:
    forall n,
      MemsDeclared
        (fst (partition (fun x=> PS.mem (fst x) (memories n.(n_eqs)))
                        n.(n_vars)))
        (translate_eqns (memories n.(n_eqs)) n.(n_eqs)).
  Proof.
  Admitted.

  Lemma MemsDeclared_translate_reset_eqns:
    forall n,
      MemsDeclared
        (fst (partition (fun x=> PS.mem (fst x) (memories n.(n_eqs)))
                        n.(n_vars)))
        (translate_reset_eqns n.(n_eqs)).
  Proof.
  Admitted.

  Lemma InstanceDeclared_translate_eqns:
    forall n,
      InstanceDeclared (snd (gather_eqs n.(n_eqs)))
        (translate_eqns (ps_from_list (fst (gather_eqs n.(n_eqs)))) n.(n_eqs)).
  Proof.
  Admitted.

  Lemma InstanceDeclared_translate_reset_eqns:
    forall n,
      InstanceDeclared (snd (gather_eqs n.(n_eqs)))
                       (translate_reset_eqns n.(n_eqs)).
  Proof.
  Admitted.


  

  (* =translate_node= *)
  (* definition is needed in signature *)
  Program Definition translate_node (n: node) : class :=
    (* TODO: fst (gather_eqs) should be a PS.t
               (i.e., do ps_from_list directly) *)
    let gathered := gather_eqs n.(n_eqs) in
    let memids := fst gathered in
    let dobjs := snd gathered in
    let mems := ps_from_list memids in
    let partitioned := partition (fun x=>PS.mem (fst x) mems) n.(n_vars) in
    let dmems := fst partitioned in
    let dvars := snd partitioned in
    {| c_name    := n.(n_name);
       c_mems    := dmems;
       c_objs    := dobjs;
       c_methods := [ {| m_name := step;
                         m_in   := n.(n_in);
                         m_vars := dvars;
                         m_out  := [n.(n_out)];
                         m_body := translate_eqns mems n.(n_eqs);
                         m_nodupvars := _;
                         m_varsdecl  := _;
                         m_good      := _
                      |};
                      reset_method n.(n_eqs) ];
       c_nodups   := _;
       
       c_memsdecl := _;
       c_instdecl := _
    |}.
  (* =end= *)
  Next Obligation.
    rewrite (Permutation_app_comm n.(n_in)).
    rewrite Permutation_app_assoc.
    match goal with |- context [snd (partition ?p ?l)] =>
      apply (NoDupMembers_app_r (fst (partition p l))) end.
    match goal with |- NoDupMembers ?l =>
      cut (Permutation l (n_in n ++ n_vars n ++ [n_out n]))
    end.
    intro Hperm; rewrite Hperm. now apply n_nodup.
    assert (Permutation (n.(n_in) ++ n.(n_vars) ++ [n.(n_out)])
                        (n.(n_vars) ++ [n.(n_out)] ++ n.(n_in))) as Hr
        by (now rewrite Permutation_app_comm, Permutation_app_assoc).
    rewrite Hr.
    rewrite <- (Permutation_app_assoc _ _ ([n.(n_out)] ++ n.(n_in))).
    apply Permutation_app; auto.
    symmetry; apply permutation_partition.
  Qed.
  Next Obligation.
    simpl. rewrite ps_from_list_gather_eqs_memories.
    rewrite partition_switch
    with (g:=fun x=> PS.mem (fst x) (memories n.(n_eqs))).
    2:now intro; rewrite ps_from_list_gather_eqs_memories.
    now apply VarsDeclared_translate_eqns.
  Qed.
  Next Obligation.
    rewrite (Permutation_app_comm n.(n_in)).
    rewrite Permutation_app_assoc.
    match goal with |- context [snd (partition ?p ?l)] =>
      apply (Forall_app_weaken (fst (partition p l))) end.
    match goal with |- Forall _ ?l =>
      cut (Permutation l (n_in n ++ n_vars n ++ [n_out n]))
    end.
    intro Hperm; rewrite Hperm. now apply n_good.
    assert (Permutation (n.(n_in) ++ n.(n_vars) ++ [n.(n_out)])
                        (n.(n_vars) ++ [n.(n_out)] ++ n.(n_in))) as Hr
        by (now rewrite Permutation_app_comm, Permutation_app_assoc).
    rewrite Hr.
    rewrite <- (Permutation_app_assoc _ _ ([n.(n_out)] ++ n.(n_in))).
    apply Permutation_app; auto.
    symmetry; apply permutation_partition.
  Qed.
  Next Obligation.
    rewrite partition_switch
    with (g:=fun x=> PS.mem (fst x) (memories n.(n_eqs))).
    2:intro x; now rewrite ps_from_list_gather_eqs_memories.
    rewrite fst_gather_eqs_var_defined.
    (* Annoying, Coq should be able to rewrite these directly... *)
    match goal with |- NoDup (?l1 ++ ?l2) =>
      assert (Permutation (l1 ++ l2)
                          (map var_defined (filter is_fby n.(n_eqs)) ++ l2))
       as Hperm
       by (apply Permutation_app; auto;
            now rewrite fst_partition_memories_var_defined)
    end.
    rewrite Hperm; clear Hperm.
    eapply (NoDup_app_weaken _ (map var_defined (filter is_def n.(n_eqs)))).
    rewrite Permutation_app_comm.
    match goal with |- NoDup (?l1 ++ ?l2 ++ ?l3) =>
      assert (Permutation (l1 ++ l2 ++ l3) (l1 ++ l3 ++ l2)) as Hperm
        by (rewrite Permutation_app'; auto; now rewrite Permutation_app_comm)
    end.
    rewrite Hperm. clear Hperm.
    rewrite <- 2 map_app.
    match goal with |- NoDup (map ?f ?l) =>
      assert (Permutation (map f l) (map f n.(n_eqs))) as Hperm
        by (apply Permutation_map_aux; apply is_filtered_eqs)
    end.
    rewrite Hperm. clear Hperm.
    pose proof (n_nodup n) as Hndm.
    apply NoDupMembers_app_r in Hndm.
    apply fst_NoDupMembers in Hndm.
    now rewrite n_defd.
  Qed.
  Next Obligation.
    repeat constructor.
    - simpl. rewrite partition_switch
             with (g:=fun x=> PS.mem (fst x) (memories n.(n_eqs))).
      2:now intro; rewrite ps_from_list_gather_eqs_memories.
      rewrite ps_from_list_gather_eqs_memories.
      now apply MemsDeclared_translate_eqns.
    - simpl. rewrite partition_switch
             with (g:=fun x=> PS.mem (fst x) (memories n.(n_eqs))).
      2:now intro; rewrite ps_from_list_gather_eqs_memories.
      now apply MemsDeclared_translate_reset_eqns.
  Qed.       
  Next Obligation.
    repeat constructor.
    now apply InstanceDeclared_translate_eqns.
    now apply InstanceDeclared_translate_reset_eqns.
  Qed.

  (* =translate= *)
  (* definition is needed in signature *)
  Definition translate (G: global) : program :=
    List.map translate_node G.
  (* =end= *)

  Lemma exists_step_method:
    forall node,
    exists stepm,
      find_method step (translate_node node).(c_methods) = Some stepm.
  Proof.
    intro node.
    simpl. rewrite ident_eqb_refl. eauto.
  Qed.

  Lemma exists_reset_method:
    forall node,
      find_method reset (translate_node node).(c_methods)
      = Some (reset_method node.(n_eqs)).
  Proof.
    intro node.
    assert (ident_eqb step reset = false) as Hsr.
    apply ident_eqb_neq.
    apply PositiveOrder.neq_sym. apply reset_not_step.
    simpl. now rewrite Hsr, ident_eqb_refl.
  Qed.

  Lemma find_method_stepm:
    forall node stepm,
      find_method step (translate_node node).(c_methods) = Some stepm ->
      stepm.(m_out) = [node.(n_out)].
  Proof.
    intros node stepm.
    simpl. rewrite ident_eqb_refl.
    injection 1.
    intro HH; rewrite <-HH.
    reflexivity.
  Qed.

  Lemma find_class_translate:
    forall n G cls prog',
      find_class n (translate G) = Some (cls, prog')
      -> (exists node, find_node n G = Some node
                       /\ cls = translate_node node).
  Proof.
    induction G as [|node G]; [now inversion 1|].
    intros ** Hfind.
    simpl in Hfind.
    destruct (equiv_dec node.(n_name) n) as [Heq|Hneq].
    - rewrite Heq, ident_eqb_refl in Hfind.
      injection Hfind; intros; subst.
      exists node. split; auto.
      simpl. now rewrite Heq, ident_eqb_refl.
    - apply ident_eqb_neq in Hneq. rewrite Hneq in Hfind.
      apply IHG in Hfind. destruct Hfind as (node' & Hfind & Hcls).
      exists node'. simpl. rewrite Hneq. auto.
  Qed.
  
End TRANSLATION.

Module TranslationFun
       (Import Ids : IDS)
       (Import Op  : OPERATORS)
       (Import OpAux: OPERATORS_AUX Op)
       (Import SynDF : Rustre.Dataflow.Syntax.SYNTAX Ids Op)
       (Import SynMP : Rustre.Minimp.Syntax.SYNTAX Ids Op OpAux)
       (Import Mem : MEMORIES Ids Op SynDF)
       <: TRANSLATION Ids Op OpAux SynDF SynMP Mem.

  Include TRANSLATION Ids Op OpAux SynDF SynMP Mem.
  
End TranslationFun.

