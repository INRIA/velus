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
  
  Lemma permutation_partition:
    forall {A:Type} p (l: list A),
      Permutation l (fst (partition p l) ++ snd (partition p l)).
  Proof.
    induction l as [|x l].
    now constructor.
    simpl.
    destruct (p x).
    - rewrite (surjective_pairing (partition _ _)).
      now simpl; apply Permutation_cons.
    - rewrite (surjective_pairing (partition _ _)).
      now simpl; apply Permutation_cons_app.
  Qed.

  Lemma Permutation_app_assoc:
    forall {A: Type} (ws: list A) xs ys,
      Permutation ((ws ++ xs) ++ ys) (ws ++ xs ++ ys).
  Proof.
    intros.
    induction ws.
    reflexivity.
    now apply Permutation_cons.
  Qed.

  Instance InMembers_Permutation_Proper (A B:Type):
    Proper (eq ==> Permutation (A:=A * B) ==> iff) InMembers.
  Proof.
    intros x y Heq xs ys Hperm.
    rewrite Heq. clear Heq x.
    split; intro Hinm.
    - apply InMembers_In in Hinm.
      destruct Hinm as [b Hinm].
      apply Permutation_in with (2:=Hinm) in Hperm.
      apply In_InMembers with (1:=Hperm).
    - apply InMembers_In in Hinm.
      destruct Hinm as [b Hinm].
      symmetry in Hperm.
      apply Permutation_in with (2:=Hinm) in Hperm.
      apply In_InMembers with (1:=Hperm).
  Qed.

  Instance NoDupMembers_Permutation_Proper (A B:Type):
    Proper (Permutation (A:=A * B) ==> iff) NoDupMembers.
  Proof.
    intros xs ys Hperm.
    induction Hperm.
    - now intuition.
    - destruct x as [x y].
      rewrite 2 nodupmembers_cons, IHHperm, Hperm.
      reflexivity.
    - split; intro HH.
      + inversion HH as [|a b l' Hninm Hndup]. clear HH. subst.
        destruct x as [x y].
        inversion Hndup as [|c d l' Hinm' Hndup']. clear Hndup. subst.
        econstructor.
        * intro Hinm. apply Hinm'.
          inversion_clear Hinm; subst; auto.
          exfalso; apply Hninm. now constructor.
        * constructor; auto. intro Hinm.
          apply Hninm. constructor (assumption).
      + inversion HH as [|a b l' Hninm Hndup]. clear HH. subst.
        destruct y as [x y].
        inversion Hndup as [|c d l' Hinm' Hndup']. clear Hndup. subst.
        econstructor.
        * intro Hinm. apply Hinm'.
          inversion_clear Hinm; subst; auto.
          exfalso; apply Hninm. now constructor.
        * constructor; auto. intro Hinm.
          apply Hninm. constructor (assumption).
    - now rewrite IHHperm1.
  Qed.

  Lemma NoDup_cons:
    forall {A} (x:A) xs,
      NoDup (x::xs) <-> ~In x xs /\ NoDup xs.
  Proof.
    split; intro HH.
    - inversion_clear HH. intuition.
    - destruct HH. constructor; auto.
  Qed.

  Instance In_Permutation_Proper (A:Type):
    Proper (eq ==> Permutation (A:=A) ==> iff) (@In A).
  Proof.
    intros x y Hxy xs ys Hperm.
    subst y.
    split; intro HH; [|symmetry in Hperm];
      now apply Permutation_in with (1:=Hperm) in HH.
  Qed.
  
  Instance NoDup_Permutation_Proper (A:Type):
    Proper (Permutation (A:=A) ==> iff) (@NoDup A).
  Proof.
    intros xs ys Hperm.
    induction Hperm.
    - now intuition.
    - rewrite 2 NoDup_cons, IHHperm, Hperm.
      reflexivity.
    - split; inversion_clear 1 as [|? ? Hnin Hndup];
        inversion_clear Hndup as [|? ? Hnin' Hndup'];
        (constructor; [|constructor]); auto; intro Hnin3;
          apply Hnin.
      + inversion Hnin3; [|contradiction].
        subst. now constructor.
      + constructor (assumption).
      + inversion Hnin3; [|contradiction].
        subst. now constructor.
      + constructor (assumption).
    - now rewrite IHHperm1, IHHperm2.
  Qed.
  
  Lemma Permutation_Forall:
    forall {A} (l l': list A) P,
      Permutation l l' ->
      Forall P l ->
      Forall P l'.
  Proof.
    induction 1; inversion 1; auto.
    match goal with H:Forall _ (_ :: _) |- _ => inversion H end.
    repeat constructor; auto.
  Qed.

  Instance Forall_Permutation_Proper (A:Type):
    Proper (eq ==> Permutation (A:=A) ==> iff) Forall.
  Proof.
    intros P Q HPQ xs ys Hperm.
    subst P.
    split; intro HH; [|symmetry in Hperm];
      apply Permutation_Forall with (1:=Hperm) (2:=HH).
  Qed.

  Lemma Forall_app_weaken:
    forall {A} xs P (ys : list A),
      Forall P (xs ++ ys) ->
      Forall P ys.
  Proof.
    intros ** HH. apply Forall_app in HH. intuition.
  Qed.

  Lemma partition_switch:
    forall {A} f g,
      (forall x:A, f x = g x) ->
      forall xs, partition f xs = partition g xs.
  Proof.
    intros ** Hfg xs.
    induction xs as [|x xs]; auto. simpl.
    specialize (Hfg x). symmetry in Hfg. rewrite Hfg, IHxs.
    reflexivity.
  Qed.

  Lemma partition_filter:
    forall {A} P (xs: list A),
      Permutation (fst (partition P xs)) (filter P xs).
  Proof.
    induction xs as [|x xs]; auto.
    simpl; rewrite (surjective_pairing (partition P xs)).
    destruct (P x); auto.
    now apply Permutation_cons.
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

  Lemma NoDup_app_weaken:
    forall {A} (xs: list A) ys,
      NoDup (xs ++ ys) ->
      NoDup xs.
  Proof.
    Hint Constructors NoDup.
    intros ** Hndup.
    induction xs as [|x xs]; auto.
    inversion_clear Hndup as [|? ? Hnin Hndup'].
    apply IHxs in Hndup'.
    constructor; auto.
    intro Hin. apply Hnin.
    apply in_or_app; now left.
  Qed.
  
  Lemma fst_partition_memories_var_defined:
    forall n,
      map fst (fst (partition
                      (fun x=> PS.mem (fst x) (memories n.(n_eqs))) n.(n_vars)))
      = map var_defined (filter is_fby n.(n_eqs)).
  Proof.
  Admitted.

  Lemma fst_gather_eqs_var_defined:
    forall n,
      map fst (snd (gather_eqs n.(n_eqs)))
      = map var_defined (filter is_app n.(n_eqs)).
  Proof.
  Admitted.
  
  Lemma VarsDeclared_translate_eqns:
    forall n mems,
      VarsDeclared
        (snd (partition (fun x=> PS.mem (fst x) mems) n.(n_vars))
         ++ [n.(n_out)])
        (translate_eqns mems n.(n_eqs)).
  Proof.
  Admitted.

  Lemma MemsDeclared_translate_eqns:
    forall n mems,
      MemsDeclared
        (fst (partition (fun x=> PS.mem (fst x) mems) n.(n_vars)))
        (translate_eqns mems n.(n_eqs)).
  Proof.
  Admitted.

  Lemma MemsDeclared_translate_reset_eqns:
    forall n mems,
      MemsDeclared
        (fst (partition (fun x=> PS.mem (fst x) mems) n.(n_vars)))
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
    repeat progress match goal with
                    | H: (_ , _) = _ |- _ =>
                      rewrite surjective_pairing in H;
                        injection H; clear H
                    end.
    intros; subst.
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
    repeat progress match goal with
                    | H: (_ , _) = _ |- _ =>
                      rewrite surjective_pairing in H;
                        injection H; clear H
                    end.
    intros; subst.
    now apply VarsDeclared_translate_eqns.
  Qed.
  Next Obligation.
    repeat progress match goal with
                    | H: (_ , _) = _ |- _ =>
                      rewrite surjective_pairing in H;
                        injection H; clear H
                    end.
    intros; subst.
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
    repeat progress match goal with
                    | H: (_ , _) = _ |- _ =>
                      rewrite surjective_pairing in H;
                        injection H; clear H
                    end.
    intros; subst.
    rewrite partition_switch
    with (g:=fun x=> PS.mem (fst x) (memories n.(n_eqs))).
    2:intro x; now rewrite ps_from_list_gather_eqs_memories.
    rewrite fst_partition_memories_var_defined.
    rewrite fst_gather_eqs_var_defined.
    eapply (NoDup_app_weaken _ (map var_defined (filter is_def n.(n_eqs)))).
    rewrite Permutation_app_comm.
    (* Annoying, Coq should be able to rewrite these directly... *)
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
    rewrite n_defd.
    apply fst_NoDupMembers.
    apply NoDupMembers_app_r with (ws:=n.(n_in)).
    apply n_nodup.
  Qed.
  Next Obligation.
    repeat constructor;
      simpl;
      repeat progress match goal with
                      | H: (_ , _) = _ |- _ =>
                        rewrite surjective_pairing in H;
                          injection H; clear H
                      end;
      intros; subst.
      now apply MemsDeclared_translate_eqns.
      now apply MemsDeclared_translate_reset_eqns.
  Qed.       
  Next Obligation.
    repeat constructor;
      simpl;
      repeat progress match goal with
                      | H: (_ , _) = _ |- _ =>
                        rewrite surjective_pairing in H;
                          injection H; clear H
                      end;
      intros; subst.
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

