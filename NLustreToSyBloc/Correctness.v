Require Import Coq.FSets.FMapPositive.
Require Import PArith.
Require Import Logic.FunctionalExtensionality.

Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.NLustre.NLExprSyntax.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.Memories.
Require Import Velus.SyBloc.SBSyntax.
Require Import Velus.NLustre.Ordered.
Require Import Velus.NLustre.Stream.
Require Import Velus.NLustre.NLExprSemantics.
Require Import Velus.NLustre.NLSemantics.
Require Import Velus.NLustre.MemSemantics.
Require Import Velus.SyBloc.SBSemantics.
Require Import Velus.NLustreToSyBloc.Translation.
Require Import Velus.RMemory.
(* Require Import Velus.NLustre.NLInterpretor. *)
(* Require Import Velus.NLustre.WellFormed. *)
Require Import Velus.NLustre.IsFree.
Require Import Velus.NLustre.IsVariable.
Require Import Velus.NLustre.IsDefined.
Require Import Velus.NLustre.NoDup.
Require Import Velus.NLustre.NLClocking.

Require Import List.
Import List.ListNotations.

Open Scope list.
Open Scope nat.

Module Type CORRECTNESS
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import OpAux   : OPERATORS_AUX     Op)
       (Import Clks    : CLOCKS          Ids)
       (Import ExprSyn : NLEXPRSYNTAX        Op)
       (Import SynNL   : NLSYNTAX        Ids Op       Clks ExprSyn)
       (Import SynSB          : SBSYNTAX        Ids Op       Clks ExprSyn)
       (Import Str     : STREAM              Op OpAux)
       (Import Ord     : ORDERED         Ids Op       Clks ExprSyn SynNL)
       (Import ExprSem : NLEXPRSEMANTICS Ids Op OpAux Clks ExprSyn             Str)
       (Import SemNL   : NLSEMANTICS     Ids Op OpAux Clks ExprSyn SynNL       Str Ord                     ExprSem)
       (Import SemSB          : SBSEMANTICS     Ids Op OpAux Clks ExprSyn       SynSB Str                         ExprSem)
       (Import Mem     : MEMORIES        Ids Op       Clks ExprSyn SynNL)
       (Import Trans   : TRANSLATION     Ids Op       Clks ExprSyn SynNL SynSB         Mem)
       (* (Import Interp  : NLINTERPRETOR   Ids Op OpAux Clks ExprSyn             Str                         ExprSem) *)
       (Import IsD     : ISDEFINED       Ids Op       Clks ExprSyn SynNL               Mem)
       (Import IsV     : ISVARIABLE      Ids Op       Clks ExprSyn SynNL               Mem IsD)
       (Import IsF     : ISFREE          Ids Op       Clks ExprSyn SynNL)
       (Import NoD     : NODUP           Ids Op       Clks ExprSyn SynNL               Mem IsD IsV)
       (* (Import WeF     : WELLFORMED      Ids Op       Clks ExprSyn SynNL           Ord Mem IsD IsV IsF NoD) *)
       (Import MemSem  : MEMSEMANTICS    Ids Op OpAux Clks ExprSyn SynNL       Str Ord                     ExprSem SemNL Mem IsD IsV IsF NoD)
       (Import NLClk   : NLCLOCKING      Ids Op       Clks ExprSyn SynNL                                                 Mem IsD     IsF).

  (* Inductive inst_in_eq: ident -> SynSB.equation -> Prop := *)
  (* | InstInEqReset: *)
  (*     forall x ck m r, *)
  (*       inst_in_eq x (SynSB.EqReset ck m x r) *)
  (* | InstInEqCall: *)
  (*     forall x xs ck m es, *)
  (*       inst_in_eq x (SynSB.EqCall xs ck m x es). *)

  (* Definition inst_in_eqs (x: ident) (eqs: list SynSB.equation) : Prop := *)
  (*   List.Exists (inst_in_eq x) eqs. *)

  Inductive well_formed_app_eq: SynNL.equation -> Prop :=
  | wfa_EqDef:
      forall x ck e,
        well_formed_app_eq (SynNL.EqDef x ck e)
  | wfa_EqFby:
      forall x ck v0 e,
        well_formed_app_eq (EqFby x ck v0 e)
  | wfa_EqApp:
      forall xs ck f es r,
        0 < length xs ->
        well_formed_app_eq (EqApp xs ck f es r).

  Definition well_formed_app := Forall well_formed_app_eq.

  (* Lemma sem_equations_well_formed_app: *)
  (*   forall P bk H M eqs, *)
  (*     Forall (SemSB.sem_equation P bk H M) (translate_eqns eqs) -> *)
  (*     well_formed_app eqs. *)
  (* Proof. *)
  (*   unfold translate_eqns, concatMap. *)
  (*   induction eqs as [|eq]; simpl; intros ** Sem; constructor. *)
  (*   - destruct eq; try destruct o as [()|]; constructor; *)
  (*       simpl in Sem; inversion_clear Sem as [|?? Sem' Sem'']. *)
  (*     + inversion_clear Sem'' as [|?? Sem]. *)
  (*       eapply SemSB.sem_EqCall_gt0; eauto. *)
  (*     + eapply SemSB.sem_EqCall_gt0; eauto. *)
  (*   - apply Forall_app in Sem as (); apply IHeqs; auto. *)
  (* Qed. *)

  Lemma nl_sem_equations_well_formed_app:
    forall G bk H eqs,
      Forall (SemNL.sem_equation G bk H) eqs ->
      well_formed_app eqs.
  Proof.
    induction eqs as [|eq]; simpl; inversion_clear 1; constructor; auto.
    - destruct eq; try destruct o as [()|]; constructor;
        eapply sem_EqApp_gt0; eauto.
    - apply IHeqs; auto.
  Qed.

  (* Lemma inst_in_Is_defined_in_eqs: *)
  (*   forall xs eqs, *)
  (*     well_formed_app eqs -> *)
  (*     inst_in_eqs (hd default xs) (translate_eqns eqs) -> *)
  (*     Is_defined_in_eqs (hd default xs) eqs. *)
  (* Proof. *)
  (*   intros ** Wfa In. *)
  (*   unfold translate_eqns, concatMap in In. *)
  (*   induction eqs as [|eq]; simpl in *; *)
  (*     inversion_clear Wfa as [|?? Wfa_eq]. *)
  (*   - inv In. *)
  (*   - apply Exists_app' in In as [E|E]. *)
  (*     + left. *)
  (*       destruct eq; try destruct o as [()|]; simpl in *; inv Wfa_eq; *)
  (*         inversion_clear E as [?? Def|?? Nil]; *)
  (*         try inversion_clear Nil as [?? Def|?? Nil']; *)
  (*         try inv Def; try inv Nil'; match goal with H: hd _ _ = hd _ _ |- _ => rewrite H end; *)
  (*           eapply Is_defined_in_EqApp; eauto. *)
  (*     + right; apply IHeqs; auto. *)
  (* Qed. *)

  (* Lemma not_inst_in_eqs_cons: *)
  (*   forall x eq eqs, *)
  (*     ~ inst_in_eqs x (eq :: eqs) *)
  (*     <-> ~ inst_in_eq x eq /\ ~ inst_in_eqs x eqs. *)
  (* Proof. *)
  (*   split. *)
  (*   - intro Hndef; split; intro; *)
  (*       eapply Hndef; constructor (assumption). *)
  (*   - intros [? ?] Hdef_all. *)
  (*     inv Hdef_all; eauto. *)
  (* Qed. *)

  (* Lemma not_inst_in_eqs_app: *)
  (*   forall eqs eqs' x, *)
  (*     ~ inst_in_eqs x (eqs ++ eqs') -> *)
  (*     ~ inst_in_eqs x eqs /\ ~ inst_in_eqs x eqs'. *)
  (* Proof. *)
  (*   unfold inst_in_eqs. *)
  (*   intros * Nd. *)
  (*   split; intro; apply Nd. *)
  (*   - now apply Exists_app_l. *)
  (*   - now apply Exists_app. *)
  (* Qed. *)

  (* Lemma mfby_add_inst: *)
  (*   forall i v0 ls M xs x M', *)
  (*     SemSB.mfby i v0 ls M xs -> *)
  (*     SemSB.mfby i v0 ls (add_inst x M' M) xs. *)
  (* Proof. *)
  (*   inversion_clear 1. *)
  (*   econstructor; eauto. *)
  (* Qed. *)
  (* Hint Resolve mfby_add_inst. *)

  (* Lemma mfby_add_val: *)
  (*   forall i v0 ls M xs x mv, *)
  (*     i <> x -> *)
  (*     SemSB.mfby i v0 ls M xs -> *)
  (*     SemSB.mfby i v0 ls (add_val x mv M) xs. *)
  (* Proof. *)
  (*   inversion_clear 2. *)
  (*   econstructor; eauto. *)
  (*   rewrite find_val_gso; auto. *)
  (* Qed. *)

  (* Inductive defined_in_eq: ident -> SynSB.equation -> Prop := *)
  (* | DefEqDef: *)
  (*     forall x ck e, *)
  (*       defined_in_eq x (SynSB.EqDef x ck e) *)
  (* | DefEqFby: *)
  (*     forall x ck v e, *)
  (*       defined_in_eq x (SynSB.EqFby x ck v e) *)
  (* | DefEqCall: *)
  (*     forall x xs ck b o es, *)
  (*       In x xs -> *)
  (*       defined_in_eq x (SynSB.EqCall xs ck b o es). *)

  (* Definition defined_in_eqs (x: ident) (eqs: list SynSB.equation) : Prop := *)
  (*   List.Exists (defined_in_eq x) eqs. *)

  (* Lemma defined_in_Is_defined_in_eqs: *)
  (*   forall x eqs, *)
  (*     defined_in_eqs x (translate_eqns eqs) -> *)
  (*     Is_defined_in_eqs x eqs. *)
  (* Proof. *)
  (*   intros ** Def. *)
  (*   induction eqs as [|eq]. *)
  (*   - inv Def. *)
  (*   - unfold translate_eqns, concatMap in Def; simpl in Def. *)
  (*     apply Exists_app' in Def; destruct Def as [E|E]. *)
  (*     + left. *)
  (*       destruct eq; try destruct o as [()|]; simpl in E; *)
  (*         inversion_clear E as [?? Def|?? Nil]; *)
  (*         try inversion_clear Nil as [?? Def|?? Nil']; *)
  (*         try inv Def; try inv Nil'; constructor; auto. *)
  (*     + right; apply IHeqs; auto. *)
  (* Qed. *)

  (* Lemma not_defined_in_eqs_cons: *)
  (*   forall x eq eqs, *)
  (*     ~ defined_in_eqs x (eq :: eqs) *)
  (*     <-> ~ defined_in_eq x eq /\ ~ defined_in_eqs x eqs. *)
  (* Proof. *)
  (*   split. *)
  (*   - intro Hndef; split; intro; *)
  (*       eapply Hndef; constructor(assumption). *)
  (*   - intros [? ?] Hdef_all; inv Hdef_all; eauto. *)
  (* Qed. *)

  (* Lemma not_defined_in_eqs_app: *)
  (*   forall eqs eqs' x, *)
  (*     ~ defined_in_eqs x (eqs ++ eqs') -> *)
  (*     ~ defined_in_eqs x eqs /\ ~ defined_in_eqs x eqs'. *)
  (* Proof. *)
  (*   unfold defined_in_eqs. *)
  (*   intros * Nd. *)
  (*   split; intro; apply Nd. *)
  (*   - now apply Exists_app_l. *)
  (*   - now apply Exists_app. *)
  (* Qed. *)

  (* Inductive compat_eq: equation -> list SynSB.equation -> Prop := *)
  (* | CompatEqDef: *)
  (*     forall x ck e eqs, *)
  (*       compat_eq (EqDef x ck e) eqs *)
  (* | CompatEqFby: *)
  (*     forall x ck c0 e eqs, *)
  (*       ~ defined_in_eqs x eqs -> *)
  (*       compat_eq (EqFby x ck c0 e) eqs *)
  (* | CompatEqApp: *)
  (*     forall xs ck f es r eqs, *)
  (*       ~ inst_in_eqs (hd default xs) eqs -> *)
  (*       compat_eq (EqApp xs ck f es r) eqs. *)

  (* Inductive compat_eqs: list equation -> Prop := *)
  (* | CompatNil: *)
  (*     compat_eqs [] *)
  (* | CompatCons: *)
  (*     forall eq eqs, *)
  (*       compat_eqs eqs -> *)
  (*       compat_eq eq (translate_eqns eqs) -> *)
  (*       compat_eqs (eq :: eqs). *)

  (* Lemma Is_well_sch_compat: *)
  (*   forall n mems, *)
  (*     well_formed_app (n_eqs n) -> *)
  (*     Is_well_sch mems (map fst (n_in n)) (n_eqs n) -> *)
  (*     compat_eqs (n_eqs n). *)
  (* Proof. *)
  (*   intros ** Wfa WSCH. *)
  (*   induction (n_eqs n) as [|eq]; *)
  (*     inversion_clear Wfa as [|?? Wfa_eq]; inversion_clear WSCH as [|???? NotDef]; *)
  (*       constructor; auto. *)
  (*   destruct eq; inv Wfa_eq; constructor. *)
  (*   - intro E; apply (NotDef (hd default i)). *)
  (*     + eapply Is_defined_in_EqApp; eauto. *)
  (*     + eapply inst_in_Is_defined_in_eqs; eauto. *)
  (*   - intro E; eapply NotDef; try constructor. *)
  (*     now apply defined_in_Is_defined_in_eqs. *)
  (* Qed. *)

  (* Inductive is_block_in_eq: ident -> SynSB.equation -> Prop := *)
  (*   IBI: *)
  (*     forall xs ck b i es, *)
  (*       is_block_in_eq b (SynSB.EqCall xs ck b i es). *)

  (* Definition is_block_in (b: ident) (eqs: list SynSB.equation) : Prop := *)
  (*   Exists (is_block_in_eq b) eqs. *)

  (* Lemma not_is_block_in_cons: *)
  (*   forall b eq eqs, *)
  (*     ~ is_block_in b (eq :: eqs) <-> ~ is_block_in_eq b eq /\ ~ is_block_in b eqs. *)
  (* Proof. *)
  (*   intros. *)
  (*   split; intro HH. *)
  (*   - split; intro; apply HH; unfold is_block_in; intuition. *)
  (*   - destruct HH; inversion_clear 1; intuition. *)
  (* Qed. *)

  (* Lemma is_block_in_Forall: *)
  (*   forall b eqs, *)
  (*     ~ is_block_in b eqs <-> Forall (fun eq => ~ is_block_in_eq b eq) eqs. *)
  (* Proof. *)
  (*   induction eqs as [|eq eqs IH]; *)
  (*     [split; [now constructor|now inversion 2]|]. *)
  (*   split; intro HH. *)
  (*   - apply not_is_block_in_cons in HH. *)
  (*     destruct HH as [Heq Heqs]. *)
  (*     constructor; [exact Heq|apply IH with (1:=Heqs)]. *)
  (*   - apply not_is_block_in_cons. *)
  (*     inversion_clear HH as [|? ? Heq Heqs]. *)
  (*     apply IH in Heqs. *)
  (*     intuition. *)
  (* Qed. *)

  (* Lemma is_block_is_node: *)
  (*   forall f eqs, *)
  (*     Is_node_in f eqs <-> is_block_in f (translate_eqns eqs). *)
  (* Proof. *)
  (*   induction eqs; split; inversion 1 as [?? InEq E|??? E]. *)
  (*   - inv InEq. *)
  (*     unfold translate_eqns, concatMap; simpl. *)
  (*     destruct r as [()|]. *)
  (*     + right; left; econstructor. *)
  (*     + left; constructor. *)
  (*   - unfold translate_eqns, concatMap; simpl. *)
  (*     apply Exists_app; rewrite <-IHeqs; auto. *)
  (*   - inv InEq. *)
  (*     unfold translate_eqns, concatMap in E; simpl in E. *)
  (*     destruct a; try destruct o as [()|]; simpl in E; inv E. *)
  (*     left; constructor. *)
  (*   - unfold translate_eqns, concatMap in H; simpl in H. *)
  (*     apply Exists_app' in H as [E'|E']. *)
  (*     + left. *)
  (*       destruct a; try destruct o as [()|]; simpl in E'; *)
  (*         inversion_clear E' as [?? Def|?? Nil]; *)
  (*         try inversion_clear Nil as [?? Def|?? Nil']; *)
  (*         try inv Def; try inv Nil'; constructor. *)
  (*     + right; rewrite IHeqs; auto. *)
  (* Qed. *)

  Definition coherent_msem_state_instant (R: env) (M: memory val) : Prop :=
    forall x v v',
      find_val x M = Some v ->
      Env.find x R = Some (present v') ->
      v' = v.

  (* Definition compat_state_instant (R: env) (M: memory val) (R': SemSB.env) (S: SemSB.state) : Prop := *)
  (*   forall x v, *)
  (*     PM.find x R = Some v -> *)
  (*     match find_val x M with *)
  (*       | Some v => find_val x S = Some v *)
  (*       | None => PM.find x R' = Some v *)
  (*     end. *)

  (* Definition coherent_msem_state (R: history) (M: memories) : Prop := *)
  (*   forall n, coherent_msem_state_instant (restr_hist R n) (M n). *)

  (* Definition compat_state (H: history) (M: memories) (H': stream SemSB.env) (E: stream SemSB.state) : Prop := *)
  (*   forall n, compat_state_instant (restr_hist H n) (M n) (H' n) (E n). *)

  (* Definition lasts_spec_instant (lasts: Env.t const) (M: memory val) : Prop := *)
  (*   forall x, *)
  (*     if Env.mem x lasts then find_val x M <> None else find_val x M = None. *)

  (* Definition lasts_spec (lasts: Env.t const) (M: memories) : Prop := *)
  (*   forall n, lasts_spec_instant lasts (M n). *)

  (* Lemma compat_hist_spec: *)
  (*   forall H lasts H' E, *)
  (*     compat_hist H lasts H' E -> *)
  (*     forall n, compat_env (restr_hist H n) lasts (SemSB.restr_hist H' n) (SemSB.restr_evol E n). *)
  (* Proof. *)
  (*   unfold compat_hist; intros ** CompatEnv n x v Find. *)
  (*   unfold restr_hist, PM.map in Find; rewrite PM.gmapi in Find. *)
  (*   destruct (PM.find x H) eqn: Find'; inv Find. *)
  (*   apply CompatEnv in Find'. *)
  (*   (* destruct (Env.mem x lasts). *) *)
  (*   (* - unfold SemSB.restr_evol; rewrite find_val_mmap, Find'; auto. *) *)
  (*   - unfold SemSB.restr_hist, PM.map; simpl; rewrite PM.gmapi, Find'; auto. *)
  (* Qed. *)

  Lemma In_fst_fold_left_gather_eq:
    forall eqs xc mems insts,
      In xc (fst (fold_left gather_eq eqs (mems, insts))) <->
      In xc mems \/ In xc (fst (fold_left gather_eq eqs ([], insts))).
  Proof.
    induction eqs as [|[]]; simpl; intros; auto.
    - split; auto; intros [|]; auto; contradiction.
    - destruct i; simpl in *; auto.
    - rewrite IHeqs; symmetry; rewrite IHeqs.
      split; intros [Hin|Hin']; auto.
      + now left; right.
      + destruct Hin' as [[|]|]; auto; try contradiction.
        now left; left.
      + destruct Hin; auto.
        now right; left; left.
  Qed.

  Lemma In_snd_fold_left_gather_eq:
    forall eqs xf mems insts,
      In xf (snd (fold_left gather_eq eqs (mems, insts))) <->
      In xf insts \/ In xf (snd (fold_left gather_eq eqs (mems, []))).
  Proof.
    induction eqs as [|[]]; simpl; intros; auto.
    - split; auto; intros [|]; auto; contradiction.
    - destruct i; simpl in *; auto.
      rewrite IHeqs; symmetry; rewrite IHeqs.
      split; intros [Hin|Hin']; auto.
      + now left; right.
      + destruct Hin' as [[|]|]; auto; try contradiction.
        now left; left.
      + destruct Hin; auto.
        now right; left; left.
  Qed.

  Lemma In_snd_gather_eqs_Is_node_in:
    forall eqs i f,
      In (i, f) (snd (gather_eqs eqs)) ->
      Is_node_in f eqs.
  Proof.
    unfold gather_eqs.
    intro.
    generalize (@nil (ident * const)).
    induction eqs as [|[]]; simpl; try contradiction; intros ** Hin; auto.
    - right; eapply IHeqs; eauto.
    - destruct i.
      + right; eapply IHeqs; eauto.
      + apply In_snd_fold_left_gather_eq in Hin as [Hin|Hin].
        * destruct Hin as [E|]; try contradiction; inv E.
          left; constructor.
        * right; eapply IHeqs; eauto.
    - right; eapply IHeqs; eauto.
  Qed.

  Lemma Ordered_nodes_blocks:
    forall G,
      Ordered_nodes G ->
      Ordered_blocks (translate G).
  Proof.
    induction 1 as [|??? IH NodeIn Nodup]; simpl; constructor; auto.
    - destruct nd; simpl in *; clear - NodeIn.
      apply Forall_forall; intros ** Hin.
      destruct x; apply In_snd_gather_eqs_Is_node_in in Hin.
      apply NodeIn in Hin as [? E]; split; auto.
      clear NodeIn.
      induction nds as [|n].
      + inv E.
      + simpl; destruct (ident_eqb (n_name n) i0) eqn: Eq.
        * inv E; eauto.
        * inv E; eauto.
          rewrite ident_eqb_refl in Eq; discriminate.
    - clear - Nodup.
      induction Nodup; simpl; auto.
  Qed.

  Lemma msem_eqs_reset_lasts:
    forall G bk H M M' n,
      memory_closed_n M (n_eqs n) ->
      Forall (msem_equation G bk H M M') (n_eqs n) ->
      reset_lasts (translate_node n) (M 0).
  Proof.
    intros ** Closed Heqs.
    split.
    - intros ** Hin.
      destruct n; simpl in *.
      unfold gather_eqs in *.
      clear - Heqs Hin.
      revert Hin; generalize (@nil (ident * ident)).
      induction n_eqs0 as [|[] ? IH]; simpl in *; intros; try contradiction;
        inversion_clear Heqs as [|?? Heq]; inv Heq; eauto.
      + destruct i; try discriminate; eauto.
      + destruct i; try discriminate; eauto.
      + apply In_fst_fold_left_gather_eq in Hin as [Hin|]; eauto.
        destruct Hin as [E|]; try contradiction; inv E.
        match goal with H: mfby _ _ _ _ _ _ |- _ => destruct H as (?&?) end; auto.
    - specialize (Closed 0); destruct Closed as [? Vals].
      intros ** Find.
      assert (In x (SynNL.gather_mem (n_eqs n))) as Hin
          by (apply Vals, not_None_is_Some; eauto).
      destruct n; simpl in *.
      unfold gather_eqs in *.
      clear - Hin Find Heqs.
      revert Hin; generalize (@nil (ident * ident)).
      induction n_eqs0 as [|[] ? IH]; simpl in *; intros; try contradiction;
        inversion_clear Heqs as [|?? Heq]; inv Heq; eauto.
      + destruct i; try discriminate; eauto.
      + destruct i; try discriminate; eauto.
      + destruct Hin.
        * subst.
          match goal with H: mfby _ _ _ _ _ _ |- _ => destruct H as (Find'&?) end.
          rewrite Find in Find'; inv Find'.
          exists c0; split; auto.
          apply In_fst_fold_left_gather_eq; left; left; auto.
        * edestruct IH as (c1 &?& Hin); eauto.
          exists c1; split; auto.
          apply In_fst_fold_left_gather_eq; right; eauto.
  Qed.

  Lemma msem_eqs_In_snd_gather_eqs_spec:
    forall eqs G bk H M M' x f,
      Forall (msem_equation G bk H M M') eqs ->
      In (x, f) (snd (gather_eqs eqs)) ->
      exists xss Mx Mx' yss,
        (msem_node G f xss Mx Mx' yss
         \/ exists r, msem_reset G f r xss Mx Mx' yss)
        /\ sub_inst_n x M Mx.
  Proof.
    unfold gather_eqs.
    intro; generalize (@nil (ident * const)).
    induction eqs as [|[]]; simpl; intros ** Heqs Hin;
      inversion_clear Heqs as [|?? Heq];
      try inversion_clear Heq as [|????????????? Hd|????????????????? Hd|];
        try contradiction; eauto.
    - destruct i; try discriminate.
      apply In_snd_fold_left_gather_eq in Hin as [Hin|]; eauto.
      destruct Hin as [E|]; try contradiction; inv E; inv Hd.
      do 4 eexists; split; eauto.
    - destruct i; try discriminate.
      apply In_snd_fold_left_gather_eq in Hin as [Hin|]; eauto.
      destruct Hin as [E|]; try contradiction; inv E; inv Hd.
      do 4 eexists; split; eauto.
  Qed.

  Lemma msem_node_initial_state:
    forall G f xss M M' yss,
      Ordered_nodes G ->
      msem_node G f xss M M' yss ->
      initial_state (translate G) f (M 0).
  Proof.
    induction G as [|node ? IH].
    inversion 2;
      match goal with Hf: find_node _ [] = _ |- _ => inversion Hf end.
    intros ** Hord Hsem.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [???????? Clock Hfind Ins ???? Heqs].
    pose proof (find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    pose proof Hord; inversion_clear Hord as [|??? NodeIn].
    pose proof Hfind as Hfind'.
    simpl in Hfind.
    assert (Ordered_blocks (translate_node node :: translate G))
           by (change (translate_node node :: translate G) with (translate (node :: G));
               apply Ordered_nodes_blocks; auto).
    destruct (ident_eqb node.(n_name) f) eqn:Hnf.
    - inversion Hfind; subst n.
      apply find_node_translate in Hfind' as (?&?&?&?); subst.
      eapply Forall_msem_equation_global_tl in Heqs; eauto.
      econstructor; eauto.
      + eapply msem_eqs_reset_lasts; eauto.
      + intros ** Hin.
        assert (b' <> n_name node).
        { destruct node; simpl in *.
          apply In_snd_gather_eqs_Is_node_in in Hin.
          apply NodeIn; auto.
        }
        destruct node; simpl in *.
        edestruct msem_eqs_In_snd_gather_eqs_spec
          as (?& Mx &?&?& [Node|(rs & Reset)] & Sub); eauto.
        * apply IH in Node; auto.
          eexists; split; eauto.
          apply initial_state_tail; simpl; auto.
        * inversion_clear Reset as [?????? Nodes].
          destruct (Nodes (count rs 0)) as (M0 &?& Node & Mmask &?).
          apply IH in Node; auto.
          specialize (Mmask 0); specialize (Sub 0).
          rewrite <-Mmask in Sub; auto.
          eexists; split; eauto.
          apply initial_state_tail; simpl; auto.
    - assert (n_name node <> f) by now apply ident_eqb_neq.
      eapply msem_node_cons in Hsem; eauto.
      simpl; rewrite <-initial_state_tail; eauto.
  Qed.

  Section Global.

    (* Variable G: global. *)
    (* Let P := translate G. *)

    (*   Inductive lasts_eq_spec (lasts: Env.t const) : equation -> Prop := *)
    (* | LSdef: *)
    (*     forall x ck e, *)
    (*       Env.mem x lasts = false -> *)
    (*       lasts_eq_spec lasts (EqDef x ck e) *)
    (* | LSapp: *)
    (*     forall xs ck f es r, *)
    (*       Forall (fun x => Env.mem x lasts = false) xs -> *)
    (*       lasts_eq_spec lasts (EqApp xs ck f es r) *)
    (* | LSfby: *)
    (*     forall x ck c0 e, *)
    (*       Env.find x lasts = Some c0 -> *)
    (*       lasts_eq_spec lasts (EqFby x ck c0 e). *)


    Definition sem_equations_n
               (P: program) (bk: stream bool) (H: history)
               (E: stream state) (T: stream transient_states) (E': stream state)
               (eqs: list equation) :=
      forall n, Forall (sem_equation P (bk n) (restr_hist H n) (E n) (T n) (E' n)) eqs.

    Definition sem_block_n
               (P: program) (f: ident)
               (E: stream state) (xss yss: stream (list value)) (E': stream state) :=
      forall n, sem_block P f (E n) (xss n) (yss n) (E' n).

    Definition add_n (x: ident) (Mx: stream state) (I: stream transient_states) :=
      fun n => Env.add x (Mx n) (I n).

    Lemma sem_equations_n_add_n:
      forall P eqs bk H S S' Is x Sx,
        sem_equations_n P bk H S Is S' eqs ->
        sem_equations_n P bk H S (add_n x Sx Is) S' eqs.
    Proof.
      induction eqs as [|eq eqs]; intros ** Sem n; constructor.
      - specialize (Sem n); inversion_clear Sem as [|?? Sem'].
        inv Sem'; eauto using SemSB.sem_equation.
        + econstructor; eauto.
          unfold add_n; rewrite Env.gso; auto.
          admit.
        + econstructor; eauto.
          unfold add_n; rewrite Env.gso; auto.
          admit.
      - apply IHeqs.
        intro n'; specialize (Sem n'); inv Sem; auto.
    Qed.

    Lemma equation_correctness:
      forall G eq eqs bk H M M' Is,
        (forall f xss M M' yss,
            msem_node G f xss M M' yss ->
            sem_block_n (translate G) f M xss yss M') ->
        Ordered_nodes G ->
        msem_equation G bk H M M' eq ->
        sem_equations_n (translate G) bk H M Is M' eqs ->
        exists Is', sem_equations_n (translate G) bk H M Is' M' (translate_eqn eq ++ eqs).
    Proof.
      intros ** IHnode Hord Heq Heqs.
      destruct Heq as [| |?????????????????????? Var Hr Reset|?????????? Arg Var Mfby];
        simpl.

      - do 3 (econstructor; eauto).

      - erewrite hd_error_Some_hd; eauto.
        exists (add_n x Mx Is); intro.
        constructor; auto.
        + econstructor; eauto.
          * split; eauto; reflexivity.
          * apply Env.gss.
          * now apply IHnode.
        + now apply sem_equations_n_add_n.

      - erewrite hd_error_Some_hd; eauto.
        exists (fun n => Env.add x (if rs n then Mx 0 else Mx n) (Is n)); intro.
        pose proof (msem_reset_spec Hord Reset) as Spec.
        inversion_clear Reset as [?????? Nodes].
        destruct (Nodes (count rs n)) as (Mn & Mn' & Node_n & Mmask_n & Mmask'_n);
          destruct (Nodes (count rs 0)) as (M0 & M0' & Node_0 & Mmask_0 & Mmask'_0).
        apply IHnode in Node_n.
        specialize (Node_n n); specialize (Mmask_n n); specialize (Mmask'_n n).
        rewrite 2 mask_transparent, Mmask_n, Mmask'_n in Node_n; auto.
        specialize (Var n); specialize (Hr n).
        assert (forall Mx, sem_equations_n (translate G) bk H M (add_n x Mx Is) M' eqs) as Heqs'
            by now intro; apply sem_equations_n_add_n.
        destruct (rs n) eqn: E.
        + specialize (Heqs' (fun n => Mx 0) n).
          assert (Env.find x (Env.add x (Mx 0) (Is n)) = Some (Mx 0))
            by apply Env.gss.
          constructor; auto; [|constructor; auto].
          *{ destruct (ys n); try discriminate.
             econstructor; eauto.
             - eapply Son; eauto.
               admit.
             - instantiate (1 := empty_memory _); simpl.
               rewrite <-Mmask_0; auto.
               eapply msem_node_initial_state; eauto.
           }
          *{ eapply SemSB.SEqCall with (Is := Mx 0); eauto.
             - instantiate (1 := empty_memory _); congruence.
             - eapply sem_block_equal_memory; eauto; reflexivity.   (* TODO: fix rewriting here? *)
           }
        + specialize (Heqs' Mx n).
          assert (Env.find x (Env.add x (Mx n) (Is n)) = Some (Mx n))
            by apply Env.gss.
          destruct (ys n) eqn: E'.
          *{ do 2 (econstructor; eauto using SemSB.sem_equation).
             - apply Son_abs1; auto.
               admit.
             - simpl; split; eauto; reflexivity.
             - econstructor; eauto.
               instantiate (1 := empty_memory _); discriminate.
           }
          *{ do 2 (econstructor; eauto using SemSB.sem_equation).
             - change true with (negb false).
               eapply Son_abs2; eauto.
               admit.
             - simpl; split; eauto; reflexivity.
             - econstructor; eauto.
               instantiate (1 := empty_memory _); discriminate.
           }

      - do 2 (econstructor; auto).
        destruct Mfby as (?&?& Spec).
        specialize (Spec n); destruct (find_val x (M n)) eqn: E; try contradiction.
        specialize (Var n); specialize (Arg n).
        pose proof Arg as Arg'.
        destruct (ls n); destruct Spec as (?& Hxs); rewrite Hxs in Var; inv Arg'; eauto using sem_equation.
    Qed.

    Corollary equations_correctness:
      forall G bk H M M' eqs,
        (forall f xss M M' yss,
            msem_node G f xss M M' yss ->
            sem_block_n (translate G) f M xss yss M') ->
        Ordered_nodes G ->
        Forall (msem_equation G bk H M M') eqs ->
        exists Is, sem_equations_n (translate G) bk H M Is M' (translate_eqns eqs).
    Proof.
      intros ** Hord IH Heqs.
      unfold translate_eqns, concatMap.
      induction eqs as [|eq eqs IHeqs]; simpl.
      - exists (fun n => Env.empty state); constructor.
      - apply Forall_cons2 in Heqs as [Heq Heqs].
        eapply IHeqs in Heqs as (?&?).
        eapply equation_correctness; eauto.
    Qed.

    Lemma clock_of_correctness:
      forall xss bk,
        ExprSem.clock_of xss bk ->
        forall n, clock_of (xss n) (bk n).
    Proof. auto. Qed.

    Lemma same_clock_correctness:
      forall xss,
        ExprSem.same_clock xss ->
        forall n, same_clock (xss n).
    Proof. auto. Qed.
    Hint Resolve clock_of_correctness same_clock_correctness.

    Lemma not_Is_node_in_not_Is_block_in:
      forall eqs f,
        ~ Is_node_in f eqs ->
        ~ Is_block_in f (translate_eqns eqs).
    Proof.
      unfold translate_eqns, concatMap.
      induction eqs as [|eq]; simpl; intros ** Hnin Hin.
      - inv Hin.
      - apply not_Is_node_in_cons in Hnin as (Hnineq & Hnin).
        apply IHeqs in Hnin.
        destruct eq; simpl in *.
        + inversion_clear Hin as [?? E|?? Hins]; try inv E; auto.
        + destruct o as [[]|]; inversion_clear Hin as [?? E|?? Hins]; auto.
          * inv E; apply Hnineq; constructor.
          * inversion_clear Hins as [?? E|?? Hins']; auto.
            inv E; apply Hnineq; constructor.
          * inv E; apply Hnineq; constructor.
        + inversion_clear Hin as [?? E|?? Hins]; try inv E; auto.
    Qed.

    Theorem correctness:
      forall G f xss M M' yss,
        Ordered_nodes G ->
        msem_node G f xss M M' yss ->
        sem_block_n (translate G) f M xss yss M'.
    Proof.
      induction G as [|node ? IH].
      inversion 2;
        match goal with Hf: find_node _ [] = _ |- _ => inversion Hf end.
      intros ** Hord Hsem n.
      assert (Hsem' := Hsem).
      inversion_clear Hsem' as [???????? Clock Hfind Ins Outs ??? Heqs].
      pose proof (find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
      pose proof Hord; inversion_clear Hord as [|??? NodeIn].
      pose proof Hfind as Hfind'.
      simpl in Hfind.
      assert (Ordered_blocks (translate_node node :: translate G))
        by (change (translate_node node :: translate G) with (translate (node :: G));
            apply Ordered_nodes_blocks; auto).
      destruct (ident_eqb node.(n_name) f) eqn:Hnf.
      - inversion Hfind; subst n0.
        apply find_node_translate in Hfind' as (?&?&?&?); subst.
        eapply Forall_msem_equation_global_tl in Heqs; eauto.
        apply equations_correctness in Heqs as (?&Heqs); auto.
        econstructor; eauto.
        + specialize (Ins n); destruct node; simpl in *.
          rewrite map_fst_idty; eauto.
        + specialize (Outs n); destruct node; simpl in *.
          rewrite map_fst_idty; eauto.
        + apply sem_equations_cons2; eauto.
          apply not_Is_node_in_not_Is_block_in; auto.
      - assert (n_name node <> f) by now apply ident_eqb_neq.
        eapply msem_node_cons, IH in Hsem; eauto.
        apply sem_block_cons2; auto using Ordered_blocks.
    Qed.
