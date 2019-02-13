Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.

Require Import Velus.NLustre.NLExprSyntax.
Require Import Velus.SyBloc.SBSyntax.

Require Import Velus.Obc.ObcSyntax.

Require Import List.
Import List.ListNotations.
Require Import Morphisms.

Open Scope positive.
Open Scope list.

(** * Translation *)

Module Type TRANSLATION
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import OpAux   : OPERATORS_AUX Op)
       (Import Clks    : CLOCKS    Ids)
       (Import ExprSyn : NLEXPRSYNTAX  Op)
       (Import SynSB   : SBSYNTAX  Ids Op       Clks ExprSyn)
       (Import SynObc  : OBCSYNTAX Ids Op OpAux).

  Section Translate.

    Variable memories : PS.t.

    Definition tovar (xt: ident * type) : exp :=
      let (x, ty) := xt in
      if PS.mem x memories then State x ty else Var x ty.

    Definition bool_var (x: ident) : exp := tovar (x, bool_type).

    Fixpoint Control (ck: clock) (s: stmt) : stmt :=
      match ck with
      | Cbase          => s
      | Con ck x true  => Control ck (Ifte (bool_var x) s Skip)
      | Con ck x false => Control ck (Ifte (bool_var x) Skip s)
      end.

    Fixpoint translate_lexp (e: lexp) : exp :=
      match e with
      | Econst c           => Const c
      | Evar x ty          => tovar (x, ty)
      | Ewhen e c x        => translate_lexp e
      | Eunop op e ty      => Unop op (translate_lexp e) ty
      | Ebinop op e1 e2 ty => Binop op (translate_lexp e1) (translate_lexp e2) ty
      end.

    Fixpoint translate_cexp (x: ident) (e: cexp) : stmt :=
      match e with
      | Emerge y t f =>
        Ifte (bool_var y) (translate_cexp x t) (translate_cexp x f)
      | Eite b t f =>
        Ifte (translate_lexp b) (translate_cexp x t) (translate_cexp x f)
      | Eexp l =>
        Assign x (translate_lexp l)
      end.

    Definition translate_eqn (eqn: equation) : stmt :=
      match eqn with
      | EqDef x ck ce =>
        Control ck (translate_cexp x ce)
      | EqNext x ck le =>
        Control ck (AssignSt x (translate_lexp le))
      | EqCall s xs ck rst f es =>
        Control ck (Call xs f s step (map translate_lexp es))
      | EqReset s ck f =>
        Control ck (Call [] f s reset [])
      end.

  (*   (** Remark: eqns ordered in reverse order of execution for coherence with *)
  (*      [Is_well_sch]. *) *)

    Definition translate_eqns (eqns: list equation) : stmt :=
      fold_left (fun i eq => Comp (translate_eqn eq) i) eqns Skip.

  End Translate.

  Definition ps_from_list (l: idents) : PS.t :=
    fold_left (fun s i=>PS.add i s) l PS.empty.

  Hint Constructors NoDupMembers.

  (** Properties of translation functions *)

  Instance eq_equiv : Equivalence PS.eq.
  Proof. firstorder. Qed.

  Instance List_fold_left_add_Proper (xs: idents) :
    Proper (PS.eq ==> PS.eq)
           (fold_left (fun s i => PS.add i s) xs).
  Proof.
    induction xs as [|x xs IH]; intros S S' Heq; [exact Heq|].
    assert (PS.eq (PS.add x S) (PS.add x S')) as Heq'
        by (rewrite Heq; reflexivity).
    simpl; rewrite Heq'; reflexivity.
  Qed.

  (* Instance List_fold_left_memory_eq_Proper (eqs: list equation) : *)
  (*   Proper (PS.eq ==> PS.eq) *)
  (*          (fold_left memory_eq eqs). *)
  (* Proof. *)
  (*   induction eqs as [|eq eqs IH]; intros S S' Heq; [exact Heq|]. *)
  (*   simpl. *)
  (*   apply IH. *)
  (*   destruct eq; [apply Heq|apply Heq|]. *)
  (*   simpl; rewrite Heq; reflexivity. *)
  (* Qed. *)

  Lemma add_ps_from_list_cons:
    forall xs x, PS.eq (PS.add x (ps_from_list xs))
                  (ps_from_list (x::xs)).
  Proof.
    intros; unfold ps_from_list; simpl.
    generalize PS.empty as S.
    induction xs as [|y xs IH]; [ reflexivity | ].
    intro S; simpl; rewrite IH; rewrite PSP.add_add; reflexivity.
  Qed.

  (* Lemma ps_from_list_gather_eqs_memories: *)
  (*   forall eqs, PS.eq (ps_from_list (fst (gather_eqs eqs))) (memories eqs). *)
  (* Proof. *)
  (*   induction eqs as [|eq eqs IH]; [reflexivity|]. *)
  (*   unfold memories, gather_eqs. *)
  (*   assert (forall eqs F S, *)
  (*              PS.eq (ps_from_list (fst (fold_left gather_eq eqs (F, S)))) *)
  (*                    (fold_left memory_eq eqs (ps_from_list F))) as HH. *)
  (*   { *)
  (*     clear eq eqs IH; induction eqs as [|eq eqs IH]; [reflexivity|]. *)
  (*     intros F S. *)
  (*     destruct eq; *)
  (*       [ now apply IH *)
  (*       | now destruct i; apply IH *)
  (*       | ]. *)
  (*     simpl; rewrite IH; rewrite add_ps_from_list_cons; reflexivity. *)
  (*   } *)
  (*   rewrite HH; reflexivity. *)
  (* Qed. *)

  Instance tovar_Proper :
    Proper (PS.eq ==> eq ==> eq) tovar.
  Proof.
    intros M M' HMeq x x' Hxeq; rewrite <- Hxeq; clear Hxeq x'.
    unfold tovar; destruct x as [x ty].
    destruct (PS.mem x M) eqn:Hmem;
      rewrite <- HMeq, Hmem; reflexivity.
  Qed.

  Instance bool_var_Proper :
    Proper (PS.eq ==> eq ==> eq) bool_var.
  Proof.
    intros M M' HMeq x x' Hxeq; unfold bool_var; rewrite Hxeq, HMeq; auto.
  Qed.

  Instance translate_lexp_Proper :
    Proper (PS.eq ==> eq ==> eq) translate_lexp.
  Proof.
    intros M M' HMeq e e' Heq; rewrite <- Heq; clear Heq e'.
    revert M M' HMeq.
    induction e; intros M M' HMeq; simpl; auto.
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
    destruct eq; simpl; try now rewrite HMeq.
    setoid_rewrite HMeq at 1.
    do 2 f_equal.
    apply map_ext.
    now setoid_rewrite HMeq.
  Qed.

  Instance translate_eqns_Proper :
    Proper (PS.eq ==> eq ==> eq) translate_eqns.
  Proof.
    intros M M' Heq eqs eqs' Heqs.
    rewrite <- Heqs; clear eqs' Heqs.
    unfold translate_eqns.
    assert (forall S S',
               S = S' ->
               fold_left (fun i eq => Comp (translate_eqn M eq) i) eqs S
               = fold_left (fun i eq => Comp (translate_eqn M' eq) i) eqs S')
      as HH.
    { revert M M' Heq.
      induction eqs as [|eq eqs IH]; intros M M' Heq S S' HSeq; [apply HSeq|].
      simpl; apply IH with (1:=Heq); rewrite HSeq, Heq; reflexivity. }
    rewrite HH with (S':=Skip); reflexivity.
  Qed.

  Lemma filter_mem_fst:
    forall p (xs: list (ident * (type * clock))),
      map fst (filter (fun (x:ident*(type*clock))=>PS.mem (fst x) p) xs)
      = filter (fun x=>PS.mem x p) (map fst xs).
  Proof.
    induction xs as [|x xs]; auto.
    simpl.
    destruct (PS.mem (fst x) p); simpl;
      now rewrite IHxs.
  Qed.

  (* Lemma in_memories_var_defined: *)
  (*   forall x eqs, *)
  (*     PS.In x (memories eqs) -> *)
  (*     In x (vars_defined eqs). *)
  (* Proof. *)
  (*   intros x eqs Hin. *)
  (*   induction eqs as [|eq eqs]. *)
  (*   now apply PSF.empty_iff in Hin. *)
  (*   unfold memories in *. simpl in *. *)
  (*   apply In_fold_left_memory_eq in Hin. *)
  (*   destruct Hin as [Hin|Hin]. *)
  (*   - specialize (IHeqs Hin); apply in_app; now right. *)
  (*   - destruct eq; simpl in Hin; *)
  (*       try (apply PSF.empty_iff in Hin; contradiction). *)
  (*     apply PS.add_spec in Hin. *)
  (*     destruct Hin as [Hin|Hin]. *)
  (*     now subst; simpl; left. *)
  (*     now apply PSF.empty_iff in Hin. *)
  (* Qed. *)

  (* Lemma in_memories_is_fby: *)
  (*   forall eqs eq, *)
  (*     In eq eqs -> *)
  (*     NoDup (vars_defined eqs) -> *)
  (*     forall x, In x (var_defined eq) -> *)
  (*     PS.mem x (memories eqs) = is_fby eq. *)
  (* Proof. *)
  (*   induction eqs as [|eq eqs]. *)
  (*   - (* Case: eqs ~ [] *) *)
  (*     now intuition. *)
  (*   - (* Case: eqs ~ eq' :: eqs *) *)
  (*     intros eq' Hin Hndup. *)
  (*     simpl in Hndup. *)

  (*     assert (  NoDup (var_defined eq) *)
  (*               /\ NoDup (vars_defined eqs) *)
  (*               /\ Forall (fun x => ~In x (vars_defined eqs)) (var_defined eq)) *)
  (*       as (Hndup_eq & Hndup_eqs & Hndup_def) *)
  (*       by now apply NoDup_app'_iff. *)
  (*     clear Hndup. *)

  (*     unfold memories. *)
  (*     destruct Hin as [|Hin]; intros x ?. *)
  (*     + (* Case: eq' = eq *) *)
  (*       subst eq'. *)

  (*       assert (PS.mem x (fold_left memory_eq eqs PS.empty) = false). *)
  (*       { *)
  (*         apply mem_spec_false; intro. *)
  (*         eapply Forall_forall in Hndup_def; eauto. *)
  (*         eapply Hndup_def; eauto. *)
  (*         now apply in_memories_var_defined. *)
  (*       } *)

  (*       destruct eq; simpl in *; auto. *)
  (*       apply In_fold_left_memory_eq. *)
  (*       right. apply PS.add_spec. now intuition. *)
  (*     + (* Case: In eq' eqs *) *)
  (*       assert (IHrec: PS.mem x (memories eqs) = is_fby eq') *)
  (*         by now apply IHeqs. *)
  (*       rewrite <- IHrec; clear IHrec. *)

  (*       destruct eq; simpl; auto. *)

  (*       assert (x <> i). *)
  (*       { *)
  (*         intro; subst x. *)
  (*         eapply Forall_forall in Hndup_def; [|simpl; eauto]. *)
  (*         apply Hndup_def; simpl; eauto. *)
  (*         eapply in_concat'; eauto. *)
  (*         now apply in_map. *)
  (*       } *)

  (*       assert (mem_fold_left_memory_eq: *)
  (*                 PS.In x (fold_left memory_eq eqs (PS.add i PS.empty)) <-> *)
  (*                 PS.In x (fold_left memory_eq eqs PS.empty)). *)
  (*       { *)
  (*         assert (PS.In x (fold_left memory_eq eqs (PS.add i PS.empty)) <-> *)
  (*                 PS.In x (fold_left memory_eq eqs PS.empty) \/ PS.In x (PS.add i PS.empty)) *)
  (*           by apply In_fold_left_memory_eq. *)

  (*         assert (PS.In x (fold_left memory_eq eqs PS.empty) \/ PS.In x (PS.add i PS.empty) *)
  (*                 <-> PS.In x (fold_left memory_eq eqs PS.empty)). *)
  (*         { *)
  (*           split. 2: intuition. *)
  (*           intros [Hin_eqs | Hin_empty]; auto. *)
  (*           exfalso. *)
  (*           apply PS.add_spec in Hin_empty. *)
  (*           destruct Hin_empty as [|Hin_empty]; try contradiction. *)
  (*           apply not_In_empty in Hin_empty. contradiction. *)
  (*         } *)

  (*         intuition. *)
  (*       } *)

  (*       assert (In_mem: forall m n, (PS.In x m <-> PS.In x n) <-> PS.mem x m = PS.mem x n). *)
  (*       { *)
  (*         (* XXX: isn't that already defined in PS? *) *)
  (*         intros m n. *)
  (*         destruct (PS.mem x n) eqn:Heq. *)
  (*         - rewrite <- PS.mem_spec. intuition. *)
  (*         - rewrite -> mem_spec_false. *)
  (*           apply mem_spec_false in Heq. intuition. *)
  (*       } *)

  (*       now apply In_mem. *)
  (* Qed. *)


  (* Lemma in_memories_filter_is_fby: *)
  (*   forall x eqs, *)
  (*     PS.In x (memories eqs) <-> In x (vars_defined (filter is_fby eqs)). *)
  (* Proof. *)
  (*   unfold memories. *)
  (*   induction eqs as [|eq eqs]. *)
  (*   - split; intro HH; try apply not_In_empty in HH; intuition. *)
  (*   - destruct eq; simpl; (try now rewrite IHeqs). *)
  (*     split; intro HH. *)
  (*     + apply In_fold_left_memory_eq in HH. *)
  (*       destruct HH as [HH|HH]. *)
  (*       * right; now apply IHeqs. *)
  (*       * apply PS.add_spec in HH. *)
  (*         destruct HH as [HH|HH]; subst; auto. *)
  (*         contradiction (not_In_empty x). *)
  (*     + apply In_fold_left_memory_eq. *)
  (*       destruct HH as [HH|HH]. *)
  (*       * rewrite PS.add_spec; intuition. *)
  (*       * apply IHeqs in HH; now left. *)
  (* Qed. *)

  (* Lemma fby_In_filter_memories: *)
  (*   forall eqs vars x (ty: type) ck c0 e, *)
  (*     In (EqFby x ck c0 e) eqs -> *)
  (*     In (x, ty) vars -> *)
  (*     In (x, ty) (filter (fun x=> PS.mem (fst x) (memories eqs)) vars). *)
  (* Proof. *)
  (*   intros ** Heqs Hvars. *)
  (*   apply filter_In. split; auto. *)
  (*   apply PS.mem_spec. *)
  (*   assert (In (EqFby x ck c0 e) (filter is_fby eqs)) as Heqs' *)
  (*       by (apply filter_In; auto). *)
  (*   assert (In (fst (x, ty)) (vars_defined (filter is_fby eqs))). *)
  (*   { *)
  (*     eapply in_concat'. *)
  (*     2:now apply in_map; eauto. *)
  (*     simpl; eauto. *)
  (*   } *)
  (*   now apply in_memories_filter_is_fby. *)
  (* Qed. *)

  (* Lemma not_in_memories_filter_notb_is_fby: *)
  (*   forall x eqs, *)
  (*     NoDup (vars_defined eqs) -> *)
  (*     In x (vars_defined (filter (notb is_fby) eqs)) -> *)
  (*     ~PS.In x (memories eqs). *)
  (* Proof. *)
  (*   intros x eqs Hnodup HH. *)
  (*   rewrite in_memories_filter_is_fby. *)

  (*   induction eqs as [|eq eqs]; [intuition|]. *)

  (*     assert (concat_filter: *)
  (*               forall f, *)
  (*                 In x (vars_defined (filter f eqs)) -> *)
  (*                 In x (vars_defined eqs)). *)
  (*     { *)
  (*       intros f Hinx. *)
  (*       unfold vars_defined, concatMap in Hinx. *)
  (*       apply in_concat in Hinx as (l & Hinl & Hindef). *)
  (*       eapply in_concat'; eauto. *)
  (*       eapply in_map_iff in Hindef as (eq' & Heq & Hineq). *)
  (*       eapply filter_In in Hineq as [? _]. *)
  (*       now rewrite in_map_iff; eauto. *)
  (*     } *)

  (*   destruct eq; simpl in *; intro Hin. *)
  (*   - (* Case: eq ~ EqDef *) *)
  (*     inversion_clear Hnodup as [|? ? Hnin Hnodup']. *)
  (*     destruct HH as [HH|HH]; [|now apply IHeqs]. *)
  (*     clear IHeqs Hnodup'; subst i. *)

  (*     now apply Hnin, (concat_filter is_fby). *)

  (*   - (* Case: eq ~ EqApp *) *)
  (*     assert (    NoDup i *)
  (*               /\ NoDup (vars_defined eqs) *)
  (*               /\ Forall (fun x => ~In x (vars_defined eqs)) i) *)
  (*       as (_ & Hnodup_eqs & Hnodup_def) *)
  (*       by now apply NoDup_app'_iff. *)
  (*     clear Hnodup. *)

  (*     unfold vars_defined in HH; *)
  (*       rewrite concatMap_cons in HH; *)
  (*       apply in_app in HH as [HH | HH]; [| now apply IHeqs]. *)

  (*     eapply Forall_forall in Hnodup_def; eauto. *)

  (*   - (* Case: eq ~ EqFby *) *)
  (*     destruct Hin. *)
  (*     + (* Case: i = x *) *)
  (*       subst i. *)
  (*       unfold vars_defined in Hnodup; *)
  (*         rewrite concatMap_cons in Hnodup; *)
  (*         unfold var_defined in Hnodup. *)
  (*         apply NoDup_cons' in Hnodup as [Hnodup _]. *)
  (*       now apply Hnodup, (concat_filter (notb is_fby)). *)

  (*     + (* Case: In x (concat (map var_defined (filter is_fby eqs))) *) *)
  (*       eapply IHeqs; eauto. *)
  (*       now unfold vars_defined in Hnodup; *)
  (*         rewrite concatMap_cons in Hnodup; *)
  (*         unfold var_defined in Hnodup; *)
  (*         apply NoDup_cons' in Hnodup as [_ ?]. *)
  (* Qed. *)


  (* Lemma fst_partition_memories_var_defined: *)
  (*   forall n, *)
  (*     Permutation *)
  (*       (map fst (fst (partition *)
  (*                        (fun x=>PS.mem (fst x) (memories n.(n_eqs))) *)
  (*                        n.(n_vars)))) *)
  (*       (vars_defined (filter is_fby n.(n_eqs))). *)
  (* Proof. *)
  (*   intro n. *)
  (*   match goal with |- Permutation (map fst (fst (partition ?p ?l))) _ => *)
  (*     assert (Permutation (map fst (fst (partition p l))) *)
  (*                         (map fst (filter p n.(n_vars)))) *)
  (*       as Hperm by (apply Permutation_map_aux; apply fst_partition_filter) *)
  (*   end. *)
  (*   rewrite Hperm; clear Hperm. *)
  (*   match goal with |- context[filter ?p ?l] => *)
  (*     rewrite <-(app_nil_r (filter p l)) *)
  (*   end. *)

  (*   assert (NoDup (filter (fun x => PS.mem (fst x) (memories (n_eqs n))) (n_out n))). *)
  (*   { *)
  (*     apply NoDupMembers_NoDup, fst_NoDupMembers. *)
  (*     rewrite filter_mem_fst. *)
  (*     apply nodup_filter. *)
  (*     pose proof (n.(n_nodup)) as Hnodup. *)
  (*     do 2 apply NoDupMembers_app_r in Hnodup. *)
  (*     now apply fst_NoDupMembers. *)
  (*   } *)

  (*   assert (filter (fun x=>PS.mem (fst x) (memories n.(n_eqs))) n.(n_out) = []) *)
  (*     as Hfout. *)
  (*   { simpl. *)
  (*     apply Permutation_nil. *)
  (*     apply NoDup_Permutation; auto using NoDup. intros x. *)
  (*     split; try (now intuition); []. intro Hin. *)

  (*     apply filter_In in Hin as [Hin Hmem]. *)

  (*     assert (In (fst x) (map fst (n_out n))) *)
  (*       by now eapply in_map. *)

  (*     assert (In (fst x) (vars_defined (filter is_fby (n_eqs n)))) *)
  (*       by now apply in_memories_filter_is_fby. *)

  (*     eapply n.(n_vout); eauto. *)
  (*   } *)

  (*   rewrite <-Hfout; clear Hfout. *)
  (*   rewrite filter_app, filter_mem_fst, <-n_defd. *)
  (*   remember (memories n.(n_eqs)) as mems. *)
  (*   set (P:=fun eqs eq=> In eq eqs -> *)
  (*                     forall x, In x (var_defined eq) -> *)
  (*                          PS.mem x mems = is_fby eq). *)
  (*   assert (forall eq, P n.(n_eqs) eq) as Peq. *)
  (*   { subst P mems. *)
  (*     intro. intro Hin. *)
  (*     apply in_memories_is_fby; auto. *)
  (*     rewrite n_defd. *)
  (*     apply fst_NoDupMembers. *)
  (*     pose proof (n.(n_nodup)) as Hnodup. *)
  (*     now apply NoDupMembers_app_r in Hnodup. *)
  (*   } *)
  (*   clear Heqmems. *)
  (*   induction n.(n_eqs) as [|eq eqs]; auto. *)
  (*   assert (forall eq, P eqs eq) as Peq' *)
  (*       by (intros e Hin; apply Peq; constructor (assumption)). *)
  (*   specialize (IHeqs Peq'). clear Peq'. *)
  (*   destruct eq eqn:Heq; simpl; *)
  (*     specialize (Peq eq); red in Peq; subst eq; *)
  (*       simpl in Peq. *)

  (*   + (* Case: EqDef *) *)
  (*     rewrite Peq; eauto. *)
  (*   + (* Case: EqApp *) *)
  (*     assert (Pfilter: Permutation (filter (fun x => PS.mem x mems) i) []). *)
  (*     { *)
  (*       assert (Hmem_in: forall x, In x i -> PS.mem x mems = false) *)
  (*         by now apply Peq; eauto. *)

  (*       assert (Hfilter: filter (fun x => PS.mem x mems) i = []). *)
  (*       { *)
  (*         clear - Hmem_in. *)
  (*         induction i as [ | a i IHi] ; auto; simpl. *)
  (*         rewrite Hmem_in; try now constructor. *)
  (*         apply IHi. intros. *)
  (*         apply Hmem_in. constructor(assumption). *)
  (*       } *)

  (*       now rewrite Hfilter. *)
  (*     } *)

  (*     unfold vars_defined; *)
  (*       rewrite concatMap_cons; *)
  (*       unfold var_defined. *)
  (*     now rewrite <- filter_app, IHeqs, Pfilter. *)

  (*   + (* Case: EqFby *) *)
  (*     unfold vars_defined; *)
  (*       rewrite concatMap_cons; *)
  (*       unfold var_defined; simpl. *)
  (*     rewrite Peq; eauto. *)
  (* Qed. *)


  (* Lemma gather_eqs_fst_spec: *)
  (*   forall eqs, Permutation (fst (gather_eqs eqs)) (gather_mem eqs). *)
  (* Proof. *)
  (* intro eqs. *)
  (* assert (Hgen: forall F S, *)
  (*            Permutation (fst (fold_left gather_eq eqs (F, S))) *)
  (*                        (F ++ gather_mem eqs)). *)
  (* { *)
  (*   induction eqs as [ | eq eqs IHeqs ]; intros F S; simpl. *)
  (*   - now rewrite app_nil_r. *)
  (*   - destruct eq as [ | i | i ck v0 le ]; simpl; *)
  (*       match goal with *)
  (*       | |- context[ EqApp _ _ _ _ _ ] => destruct i *)
  (*       | _ => idtac *)
  (*       end; rewrite IHeqs; auto. *)
  (*     assert (Hmem: gather_mem (EqFby i ck v0 le :: eqs) *)
  (*                   = i :: gather_mem eqs) *)
  (*       by now unfold gather_mem; rewrite concatMap_cons. *)

  (*     now rewrite Hmem, <- Permutation_middle, app_comm_cons. *)
  (* } *)

  (* now apply Hgen. *)
  (* Qed. *)

  (* Lemma gather_eqs_snd_spec: *)
  (*   forall eqs, Permutation (snd (gather_eqs eqs)) (gather_insts eqs). *)
  (* Proof. *)
  (* intro eqs. *)
  (* assert (Hgen: forall F S, *)
  (*            Permutation (snd (fold_left gather_eq eqs (F, S))) *)
  (*                        (S ++ gather_insts eqs)). *)
  (* { *)
  (*   induction eqs as [ | eq eqs IHeqs ]; intros F S; simpl. *)
  (*   - now rewrite app_nil_r. *)
  (*   - destruct eq as [ | is ck f les | ]; simpl; *)
  (*       match goal with *)
  (*       | |- context[ EqApp _ _ _ _ _ ] => destruct is *)
  (*       | _ => idtac *)
  (*       end; rewrite IHeqs; auto. *)

  (*     assert (Hmem_cons: gather_insts (EqApp (i :: is) ck f les o :: eqs) *)
  (*                   = (i, f) :: gather_insts eqs) *)
  (*       by now unfold gather_insts; rewrite concatMap_cons. *)

  (*     now rewrite Hmem_cons, <- Permutation_middle, app_comm_cons. *)
  (* } *)

  (* now apply Hgen. *)
  (* Qed. *)

  (* Lemma fst_gather_eqs_var_defined: *)
  (*   forall eqs, *)
  (*     Permutation ((map fst (snd (gather_eqs eqs))) ++ (gather_app_vars eqs)) *)
  (*                 (vars_defined (filter is_app eqs)). *)
  (* Proof. *)
  (* intro eqs. *)
  (* assert (Hperm: Permutation (map fst (gather_insts eqs) ++ gather_app_vars eqs) *)
  (*                     (vars_defined (filter is_app eqs))). *)
  (* { *)
  (*   induction eqs as [|eq eqs]; auto. *)
  (*   destruct eq; try (now simpl; auto). *)
  (*   destruct i as [ | x xs ]; auto. *)


  (*   assert (Happ: gather_app_vars (EqApp (x :: xs) c i0 l o :: eqs) *)
  (*           = xs ++ gather_app_vars eqs) *)
  (*     by now unfold gather_app_vars; rewrite concatMap_cons. *)

  (*   assert (Hinst: map fst (gather_insts (EqApp (x :: xs) c i0 l o :: eqs)) *)
  (*           = x :: map fst (gather_insts eqs)) *)
  (*     by now unfold gather_insts; rewrite concatMap_cons. *)

  (*   rewrite Happ, Hinst. *)
  (*   simpl; *)
  (*     unfold vars_defined; *)
  (*     rewrite concatMap_cons, <- IHeqs. *)
  (*   unfold var_defined; simpl. *)
  (*   apply Permutation_cons. *)
  (*   do 2rewrite <- Permutation_app_assoc. *)
  (*   now apply Permutation_app_tail, Permutation_app_comm. *)
  (* } *)

  (* rewrite <- Hperm. *)
  (* apply Permutation_app_tail. *)
  (* now rewrite gather_eqs_snd_spec. *)
  (* Qed. *)

  Program Definition step_method (b: block) : method :=
    let memids := map fst b.(b_lasts) in
    let mems := ps_from_list memids in
    {| m_name := step;
       m_in   := b.(b_in);
       m_vars := b.(b_vars);
       m_out  := b.(b_out);
       m_body := translate_eqns mems b.(b_eqs)
    |}.
  Next Obligation.
    apply b_nodup.
  Qed.
  Next Obligation.
    apply b_good.
  Qed.

  Definition translate_reset_eqns (b: block) : stmt :=
    let mems := fold_left (fun s xc => Comp s (AssignSt (fst xc) (Const (snd xc)))) b.(b_lasts) Skip in
    fold_left (fun s xf => Comp s (Call [] (snd xf) (fst xf) reset [])) b.(b_blocks) mems.

  Program Definition reset_method (b: block) : method :=
    {| m_name := reset;
       m_in   := [];
       m_vars := [];
       m_out  := [];
       m_body := translate_reset_eqns b
    |}.

  Program Definition translate_block (b: block) : class :=
    {| c_name    := b.(b_name);
       c_mems    := map (fun xc => (fst xc, type_const (snd xc))) b.(b_lasts);
       c_objs    := b.(b_blocks);
       c_methods := [ step_method b; reset_method b ]
    |}.
  Next Obligation.
    rewrite map_map; simpl; apply b_nodup_lasts_blocks.
  Qed.
  Next Obligation.
    constructor; auto using NoDup.
    inversion_clear 1; auto.
    now apply reset_not_step.
  Qed.
  Next Obligation.
    pose proof b.(b_good) as (?&?& Blocks &?).
    split; auto.
    clear - Blocks.
    induction Blocks as [|?? Valid]; constructor; auto.
    apply Valid.
  Qed.

  Definition translate (P: SynSB.program) : program :=
    map translate_block P.

  Lemma map_c_name_translate:
    forall p,
      map c_name (translate p) = map b_name p.
  Proof.
    induction p; auto.
    simpl; rewrite IHp; reflexivity.
  Qed.

  Lemma exists_step_method:
    forall block,
      find_method step (translate_block block).(c_methods) = Some (step_method block).
  Proof.
    intro; simpl; rewrite ident_eqb_refl; eauto.
  Qed.

  Lemma exists_reset_method:
    forall block,
      find_method reset (translate_block block).(c_methods)
      = Some (reset_method block).
  Proof.
    assert (ident_eqb step reset = false) as Hsr.
    { apply ident_eqb_neq.
      apply PositiveOrder.neq_sym; apply reset_not_step.
    }
    simpl; now rewrite Hsr, ident_eqb_refl.
  Qed.

  Lemma find_method_stepm_out:
    forall block stepm,
      find_method step (translate_block block).(c_methods) = Some stepm ->
      stepm.(m_out) = block.(b_out).
  Proof.
    intros ??; simpl.
    rewrite ident_eqb_refl.
    inversion 1; auto.
  Qed.

  Lemma find_method_stepm_in:
    forall block stepm,
      find_method step (translate_block block).(c_methods) = Some stepm ->
      stepm.(m_in) = block.(b_in).
  Proof.
    intros ??; simpl.
    rewrite ident_eqb_refl.
    inversion 1; auto.
  Qed.

  Lemma find_class_translate:
    forall b P cls P',
      find_class b (translate P) = Some (cls, P') ->
      exists block P',
        find_block b P = Some (block, P')
        /\ cls = translate_block block.
  Proof.
    induction P as [|block P]; [now inversion 1|].
    intros ** Hfind; simpl in Hfind.
    destruct (equiv_dec block.(b_name) b) as [Heq|Hneq].
    - rewrite Heq, ident_eqb_refl in Hfind.
      inv Hfind.
      exists block, P. split; auto.
      simpl. now rewrite Heq, ident_eqb_refl.
    - apply ident_eqb_neq in Hneq. rewrite Hneq in Hfind.
      apply IHP in Hfind as (block' & P'' & Hfind & Hcls).
      exists block', P''. simpl. rewrite Hneq. auto.
  Qed.

  Lemma find_block_translate:
    forall b P block P',
      find_block b P = Some (block, P') ->
      exists cls prog',
        find_class b (translate P) = Some (cls, prog')
        /\ cls = translate_block block
        /\ prog' = translate P'.
  Proof.
    induction P as [|block P]; [now inversion 1|].
    intros ** Hfind; simpl in Hfind.
    destruct (equiv_dec block.(b_name) b) as [Heq|Hneq].
    - rewrite Heq, ident_eqb_refl in Hfind.
      injection Hfind; intros; subst block0 P'.
      exists (translate_block block), (translate P).
      split; [|split]; auto.
      simpl. now rewrite Heq, ident_eqb_refl.
    - apply ident_eqb_neq in Hneq. rewrite Hneq in Hfind.
      apply IHP in Hfind as (cls & prog' & Hfind & Hcls).
      exists cls, prog'. split; auto. simpl. now rewrite Hneq.
  Qed.

End TRANSLATION.

Module TranslationFun
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import OpAux   : OPERATORS_AUX Op)
       (Import Clks    : CLOCKS    Ids)
       (Import ExprSyn : NLEXPRSYNTAX  Op)
       (Import SynSB   : SBSYNTAX  Ids Op       Clks ExprSyn)
       (Import SynObc  : OBCSYNTAX Ids Op OpAux)
       <: TRANSLATION Ids Op OpAux Clks ExprSyn SynSB SynObc.
  Include TRANSLATION Ids Op OpAux Clks ExprSyn SynSB SynObc.
End TranslationFun.