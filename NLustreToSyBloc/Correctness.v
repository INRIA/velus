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
Require Import Velus.NLustre.NLInterpretor.
Require Import Velus.NLustre.WellFormed.
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
       (SynSB          : SBSYNTAX        Ids Op       Clks ExprSyn)
       (Import Str     : STREAM              Op OpAux)
       (Import Ord     : ORDERED         Ids Op       Clks ExprSyn SynNL)
       (Import ExprSem : NLEXPRSEMANTICS Ids Op OpAux Clks ExprSyn             Str)
       (Import SemNL   : NLSEMANTICS     Ids Op OpAux Clks ExprSyn SynNL       Str Ord                     ExprSem)
       (SemSB          : SBSEMANTICS     Ids Op OpAux Clks ExprSyn       SynSB Str                         ExprSem)
       (Import Mem     : MEMORIES        Ids Op       Clks ExprSyn SynNL)
       (Import Trans   : TRANSLATION     Ids Op       Clks ExprSyn SynNL SynSB         Mem)
       (Import Interp  : NLINTERPRETOR   Ids Op OpAux Clks ExprSyn             Str                         ExprSem)
       (Import IsD     : ISDEFINED       Ids Op       Clks ExprSyn SynNL               Mem)
       (Import IsV     : ISVARIABLE      Ids Op       Clks ExprSyn SynNL               Mem IsD)
       (Import IsF     : ISFREE          Ids Op       Clks ExprSyn SynNL)
       (Import NoD     : NODUP           Ids Op       Clks ExprSyn SynNL               Mem IsD IsV)
       (Import WeF     : WELLFORMED      Ids Op       Clks ExprSyn SynNL           Ord Mem IsD IsV IsF NoD)
       (Import MemSem  : MEMSEMANTICS    Ids Op OpAux Clks ExprSyn SynNL       Str Ord                     ExprSem SemNL Mem IsD IsV IsF NoD WeF)
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

  Inductive well_formed_app_eq: equation -> Prop :=
  | wfa_EqDef:
      forall x ck e,
        well_formed_app_eq (EqDef x ck e)
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
      Forall (sem_equation G bk H) eqs ->
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
      PM.find x R = Some (present v') ->
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

  Section Global.

    Variable G: SynNL.global.
    Let P := translate G.

    (* Section InstantSemantics. *)
    (*   Variable base: bool. *)
    (*   Variable R: env. *)
    (*   Variable M: memory val. *)
    (*   Variable R': SemSB.env. *)
    (*   Variable S: SemSB.state. *)

    (*   Hypothesis CoherentMsem: coherent_msem_state_instant R M. *)
    (*   Hypothesis CompatEnv: compat_state_instant R M R' S. *)

    (*   Variable lasts: Env.t const. *)

    (*   Hypothesis LastsSpec: lasts_spec_instant lasts M. *)

    (*   Definition correct_clock_instant (ck: clock) (v: value) : Prop := *)
    (*     sem_clock_instant base R ck (v <>b absent). *)

    (*   Lemma var_var_correctness_instant: *)
    (*     forall x v, *)
    (*       find_val x M = None -> *)
    (*       sem_var_instant R x v -> *)
    (*       SemSB.sem_var_var R' x v. *)
    (*   Proof. *)
    (*     intros ** Last Sem; inversion_clear Sem as [?? Find]; apply CompatEnv in Find. *)
    (*     rewrite Last in Find; constructor; auto. *)
    (*   Qed. *)
    (*   Hint Resolve var_var_correctness_instant. *)

    (*   Lemma clock_correctness_instant: *)
    (*     forall ck b, *)
    (*       sem_clock_instant base R ck b -> *)
    (*       SemSB.sem_clock base R' S (translate_clock lasts ck) b. *)
    (*   Proof. *)
    (*     induction 1 as [|?????? Var|????? Var|?????? Var]; simpl; eauto using SemSB.sem_clock. *)
    (*     - econstructor; eauto. *)
    (*       inversion_clear Var as [?? Find]. *)
    (*       pose proof Find as Find'. *)
    (*       apply CompatEnv in Find. *)
    (*       unfold tovar; specialize (LastsSpec x). *)
    (*       destruct (Environment.mem x lasts); constructor. *)
    (*       + apply not_None_is_Some in LastsSpec as (v & Spec). *)
    (*         rewrite Spec in Find. *)
    (*         constructor; auto. *)
    (*         assert (c = v) as -> by (eapply CoherentMsem; eauto); auto. *)
    (*       + rewrite LastsSpec in Find. *)
    (*         constructor; auto. *)
    (*     - econstructor; eauto. *)
    (*       inversion_clear Var as [?? Find]. *)
    (*       apply CompatEnv in Find. *)
    (*       unfold tovar; specialize (LastsSpec x). *)
    (*       destruct (Environment.mem x lasts); constructor. *)
    (*       + apply not_None_is_Some in LastsSpec as (v & Spec). *)
    (*         rewrite Spec in Find. *)
    (*         constructor; auto. *)
    (*         congruence. *)
    (*       + rewrite LastsSpec in Find. *)
    (*         econstructor; eauto. *)
    (*     - eapply SemSB.Son_abs2; eauto. *)
    (*       inversion_clear Var as [?? Find]. *)
    (*       pose proof Find as Find'. *)
    (*       apply CompatEnv in Find. *)
    (*       unfold tovar; specialize (LastsSpec x). *)
    (*       destruct (Environment.mem x lasts); constructor. *)
    (*       + apply not_None_is_Some in LastsSpec as (v & Spec). *)
    (*         rewrite Spec in Find. *)
    (*         constructor; auto. *)
    (*         assert (c = v) as -> by (eapply CoherentMsem; eauto); auto. *)
    (*       + rewrite LastsSpec in Find. *)
    (*         constructor; auto. *)
    (*   Qed. *)
    (*   Hint Resolve clock_correctness_instant. *)

    (*   Lemma state_var_correctness_instant: *)
    (*     forall x v ck, *)
    (*       find_val x M <> None -> *)
    (*       sem_var_instant R x v -> *)
    (*       correct_clock_instant ck v -> *)
    (*       SemSB.sem_state_var base R' S (translate_clock lasts ck) x v. *)
    (*   Proof. *)
    (*     intros ** Last Sem Clock; inversion_clear Sem as [?? Find]. *)
    (*     pose proof Find as Find'; apply CompatEnv in Find. *)
    (*     apply not_None_is_Some in Last as (v' & Spec). *)
    (*     rewrite Spec in Find. *)
    (*     destruct v. *)
    (*     - constructor; try congruence; auto. *)
    (*     - constructor; auto. *)
    (*       assert (c = v') as -> by (eapply CoherentMsem; eauto); auto. *)
    (*   Qed. *)
    (*   Hint Resolve state_var_correctness_instant. *)

    (*   Lemma var_correctness_instant: *)
    (*     forall x v ck, *)
    (*       sem_var_instant R x v -> *)
    (*       correct_clock_instant ck v -> *)
    (*       SemSB.sem_var base R' S (translate_clock lasts ck) (tovar lasts x) v. *)
    (*   Proof. *)
    (*     intros; specialize (LastsSpec x); unfold tovar. *)
    (*     destruct (Env.mem x lasts); auto using SemSB.sem_var. *)
    (*   Qed. *)
    (*   Hint Resolve var_correctness_instant. *)

    (*   Lemma typeof_correctness: *)
    (*     forall e, *)
    (*       SynSB.typeof (translate_lexp lasts e) = typeof e. *)
    (*   Proof. *)
    (*     induction e; intros; simpl; auto. *)
    (*   Qed. *)

    (*   Fact present_not_absent: *)
    (*     forall v, present v <>b absent = true. *)
    (*   Proof. *)
    (*     reflexivity. *)
    (*   Qed. *)

    (*   Lemma lexp_correctness_instant: *)
    (*     forall e v ck vars, *)
    (*       sem_lexp_instant base R e v -> *)
    (*       wc_lexp vars e ck -> *)
    (*       correct_clock_instant ck v -> *)
    (*       SemSB.sem_lexp base R' S (translate_clock lasts ck) (translate_lexp lasts e) v. *)
    (*   Proof. *)
    (*     induction e; do 2 inversion_clear 1; simpl; eauto using SemSB.sem_lexp. *)
    (*     - inversion 1; eauto using SemSB.sem_lexp. *)
    (*     - inversion 1; eauto using SemSB.sem_lexp. *)
    (*       assert (present xc = absent) by (eapply sem_var_instant_det; eauto); *)
    (*         discriminate. *)
    (*     - inversion 1; eauto using SemSB.sem_lexp. *)
    (*       assert (present c = absent) by (eapply sem_var_instant_det; eauto); *)
    (*         discriminate. *)
    (*     - econstructor; eauto. *)
    (*       now rewrite typeof_correctness. *)
    (*     - econstructor; eauto. *)
    (*       now rewrite 2 typeof_correctness. *)
    (*   Qed. *)
    (*   Hint Resolve lexp_correctness_instant. *)

    (*   Lemma cexp_correctness_instant: *)
    (*     forall e v ck vars, *)
    (*       sem_cexp_instant base R e v -> *)
    (*       wc_cexp vars e ck -> *)
    (*       correct_clock_instant ck v -> *)
    (*       SemSB.sem_cexp base R' S (translate_clock lasts ck) (translate_cexp lasts e) v. *)
    (*   Proof. *)
    (*     induction e; do 2 inversion 1; subst; simpl; eauto using SemSB.sem_cexp. *)
    (*     - constructor; auto. *)
    (*       + eapply (IHe1 _ (Con ck i true)); eauto. *)
    (*         econstructor; eauto. *)
    (*         apply val_to_bool_true. *)
    (*       + eapply (IHe2 _ (Con ck i false)); eauto. *)
    (*         change false with (negb true). *)
    (*         eapply Son_abs2; eauto. *)
    (*         apply val_to_bool_true. *)
    (*     - intros; apply SemSB.Smerge_false; auto. *)
    (*       + eapply (IHe1 _ (Con ck i true)); eauto. *)
    (*         change true with (negb false). *)
    (*         eapply Son_abs2; eauto. *)
    (*         apply val_to_bool_false. *)
    (*       + eapply (IHe2 _ (Con ck i false)); eauto. *)
    (*         econstructor; eauto. *)
    (*         apply val_to_bool_false. *)
    (*     - constructor; auto. *)
    (*       + eapply (IHe1 _ (Con ck i true)); eauto. *)
    (*         constructor; auto. *)
    (*       + eapply (IHe2 _ (Con ck i false)); eauto. *)
    (*         econstructor; eauto. *)
    (*     - econstructor; eauto; destruct b; eauto. *)
    (*   Qed. *)
    (*   Hint Resolve cexp_correctness_instant. *)

    (*   Lemma laexp_correctness_instant: *)
    (*     forall e ck v vars, *)
    (*       sem_laexp_instant base R ck e v -> *)
    (*       wc_lexp vars e ck -> *)
    (*       SemSB.sem_laexp base R' S (translate_clock lasts ck) (translate_lexp lasts e) v. *)
    (*   Proof. *)
    (*     induction 1; constructor; eauto. *)
    (*   Qed. *)

    (*   Lemma caexp_correctness_instant: *)
    (*     forall e ck v vars, *)
    (*       sem_caexp_instant base R ck e v -> *)
    (*       wc_cexp vars e ck -> *)
    (*       SemSB.sem_caexp base R' S (translate_clock lasts ck) (translate_cexp lasts e) v. *)
    (*   Proof. *)
    (*     induction 1; constructor; eauto. *)
    (*   Qed. *)

    (* End InstantSemantics. *)
    (* Hint Resolve *)
    (*      state_var_correctness_instant *)
    (*      var_var_correctness_instant *)
    (*      var_correctness_instant *)
    (*      lexp_correctness_instant *)
    (*      cexp_correctness_instant *)
    (*      clock_correctness_instant *)
    (*      laexp_correctness_instant *)
    (*      caexp_correctness_instant. *)

    Inductive lasts_eq_spec (lasts: Env.t const) : equation -> Prop :=
    | LSdef:
        forall x ck e,
          Env.mem x lasts = false ->
          lasts_eq_spec lasts (EqDef x ck e)
    | LSapp:
        forall xs ck f es r,
          Forall (fun x => Env.mem x lasts = false) xs ->
          lasts_eq_spec lasts (EqApp xs ck f es r)
    | LSfby:
        forall x ck c0 e,
          Env.find x lasts = Some c0 ->
          lasts_eq_spec lasts (EqFby x ck c0 e).

    Fact hd_error_Some_hd:
      forall {A} d (xs: list A) x,
        hd_error xs = Some x ->
        hd d xs = x.
    Proof.
      destruct xs; simpl; intros; try discriminate.
      now inv H.
    Qed.

    Definition sem_equations_n
               (P: SynSB.program) (bk: stream bool) (H: history)
               (E: stream SemSB.state) (T: stream SemSB.transient_states) (E': stream SemSB.state)
               (eqs: list SynSB.equation) :=
      forall n, Forall (SemSB.sem_equation P (bk n) (restr_hist H n) (E n) (T n) (E' n)) eqs.

    Definition sem_block_n
               (P: SynSB.program) (f: ident)
               (E: stream SemSB.state) (xss yss: stream (list value)) (E': stream SemSB.state) :=
      forall n, SemSB.sem_block P f (E n) (xss n) (yss n) (E' n).

    Definition sem_reset_n
               (P: SynSB.program) (f: ident) (r: stream bool) (E E0: stream SemSB.state) :=
      forall n, SemSB.sem_reset P f (r n) (E n) (E0 n).

    Definition entry_states (M M': memories) : stream SemSB.state :=
      fun n => match n with
            | 0 => M 0
            | S n => M' n
            end.

    Definition instances_n (M: memories) : stream SemSB.transient_states :=
      fun n => instances (M n).

    Lemma entry_states_sub_inst_n:
      forall M M' x Mx Mx',
        sub_inst_n x M Mx ->
        sub_inst_n x M' Mx' ->
        sub_inst_n x (entry_states M M') (entry_states Mx Mx').
    Proof.
      intros ** S S' n.
      destruct n; simpl; auto.
    Qed.

    Lemma equation_correctness:
      forall eq eqs bk H M M',
        (forall f xss M M' yss,
            msem_node G f xss M M' yss ->
            sem_block_n P f (* (entry_states M *) M xss yss M') ->
        (forall f r xss M M' yss,
            msem_reset G f r xss M M' yss ->
            sem_block_n P f (entry_states M M') xss yss M'
        (* /\ sem_reset_n P f r (entry_states M M')  *)
        ) ->
        msem_equation G bk H M M' eq ->
        (* compat_state H M H' E -> *)
        (* coherent_msem_state H M -> *)
        (* lasts_eq_spec lasts eq -> *)
        (* lasts_spec lasts M -> *)
        (* wc_equation vars eq -> *)
        sem_equations_n P bk H (entry_states M M') (instances_n M) M' eqs ->
        sem_equations_n P bk H (entry_states M M') (instances_n M) M' (translate_eqn eq ++ eqs).
    Proof.
      intros ** IHnode IHrst Heq (* Compat CoherentMSem LastsEqSpec LastsSpec WC *) Heqs n.
      destruct Heq as [| | |??????????? Var Mfby];
        (* inversion_clear LastsEqSpec as [??? Last| |???? Last]; *)
        (* inv WC; *)
        simpl.

      - do 2 (econstructor; eauto).

      - erewrite hd_error_Some_hd; eauto.
        (* assert (Env.find x (instances_n M n) = Some (entry_states Mx Mx' n)) by admit.  *)
        constructor; auto; [|constructor; auto]; econstructor; eauto.
        + eapply entry_states_sub_inst_n; eauto.
        + admit.
        + unfold instances_n, sub_inst_n, sub_inst, find_inst in *; auto.
        + now apply IHnode.

      - erewrite hd_error_Some_hd; eauto.
        constructor; auto; [|constructor; auto].
        + econstructor; eauto.
          * apply entry_states_sub_inst_n; eauto.
          * admit.
        + constructor; auto.
          econstructor; eauto;
            unfold instances_n, sub_inst_n, sub_inst, find_inst in *; auto.
          apply IHnode; auto.

          admit.

      - econstructor; eauto.
        inversion_clear Mfby as [??????? Spec].
        specialize (Spec n); destruct (find_val x (M n)); try contradiction.
        destruct (ls n) eqn: Els; destruct Spec as (?&?&?);
          econstructor; eauto.
        + congruence.
        + congruence.
    Qed.


    Lemma equation_correctness:
      forall lasts eq bk H M eqs H' E T E' vars,
        (* (forall f xss oss, *)
        (*     sem_node G f xss oss -> *)
        (*     exists M, SemSB.sem_block P f M xss oss) -> *)
        (* (forall f r xss oss, *)
        (*     sem_reset G f r xss oss -> *)
        (*     exists M, SemSB.sem_block P f M xss oss *)
        (*          /\ SemSB.reset_regs r M) -> *)
        msem_equation G bk H M eq ->
        lasts_eq_spec lasts eq ->
        (* compat_eq eq eqs -> *)
        lasts_spec lasts M ->
        compat_state H M H' E ->
        coherent_msem_state H M ->
        relooper lasts E E' ->
        coherent_state E T E' ->
        wc_equation vars eq ->
        Forall (SemSB.sem_equation P bk H' E T E') eqs ->
        (* correspondence H lasts H' E T E' -> *)
        (* SemSB.well_structured_memories eqs M -> *)
        (* exists H' E T E', *)
        Forall (SemSB.sem_equation P bk H' E T E') (translate_eqn lasts eq ++ eqs).
    (* /\ SemSB.well_structured_memories (translate_eqn eq ++ eqs) M'. *)
    Proof.
      intros ** Heq LastsEqSpec LastsSpec Compat Coherent Reloop Coherent' WC Heqs(* Corres *);
        destruct Heq as [| | |?????????? Var];
        inversion_clear LastsEqSpec as [??? Last| |];
        inv WC;
        (* inversion_clear Corres as [?????? Compat Coherent Reloop]; *)
        simpl.
      - constructor; eauto.
        econstructor; eauto.
        eapply var_var_correctness; eauto.
        intro; specialize (LastsSpec n x); rewrite Last in LastsSpec; auto.
      - erewrite hd_error_Some_hd; eauto.
        constructor.
        + admit.
        + constructor; auto.
          admit.
      - erewrite hd_error_Some_hd; eauto.
        constructor.
        + admit.
        + constructor; auto.
          admit.
      - constructor; auto.
        econstructor; eauto.
        instantiate (1 := ls).
        pose proof Var as Var'.
        assert (forall n : nat, find_val x (M n) <> None) by admit.
        assert (correct_clock bk H ck xs) by admit.
        eapply (state_var_correctness bk H M H' E _ _ lasts _ _ _ ck(*H M H' E*)) in Var'; eauto.
        inversion_clear Reloop as [??? Loop].
        intro.
        specialize (Var n); inversion_clear Var as [?? Find].
        unfold restr_hist, PM.map in Find; rewrite PM.gmapi in Find.
        destruct (PM.find x H) eqn: Find'; inversion Find as [Eq]; clear Find.
        destruct (ls n) eqn: Els.
        + constructor.
          * unfold SemSB.restr_evol.
            rewrite find_val_mmap.
            assert (find_val x E = Some v).
            assert (exists z, find_val x E' = Some z) as (? & ->); simpl; try congruence.
            inversion_clear Coherent' as [??? SpecE']; eapply SpecE'.
            unfold compat_state, compat_state_instant in Compat.
            instantiate (1 := v).

            apply Compat in Find'; rewrite Mem in Find'.
        pose proof Find' as Find''.
        inversion_clear Coherent as [??? Spec].
        apply Spec in Find'' as (? & Find'').
        rewrite Find''; unfold SemSB.sample; simpl.
        eapply Loop in Find'; eauto.
        rewrite Find' in Fby.
        admit.

        inv Fby.
instantiate (1 := ls).

        inv Find.
        unfold fby in *.


    Theorem correctness:
      forall f xss M yss,
        msem_node G f xss M yss ->
        exists E E',
        forall n, SemSB.sem_block P f (E n) (xss n) (yss n) (E' n).
    Proof.
      intros.


    Section Sem.

      Variable bk: stream bool.
      Variable H: history.
      Variable M: memories.
      Variable H': SemSB.history.
      Variable E: SemSB.evolution.

      Hypothesis CoherentMsem: coherent_msem_state H M.
      Hypothesis CompatEnv: compat_state H M H' E.

      Variable lasts: Env.t const.

      Hypothesis LastsSpec: lasts_spec lasts M.

      (* Fact CompatEnv: *)
      (*   forall n, *)
      (*     compat_env (restr_hist H n) lasts (SemSB.restr_hist H' n) (SemSB.restr_evol E n). *)
      (* Proof. *)
      (*   now apply compat_hist_spec. *)
      (* Qed. *)
      (* Hint Resolve CompatEnv. *)

      Definition correct_clock (ck: clock) (vs: stream value) : Prop :=
        sem_clock bk H ck (fun n => vs n <>b absent).

      Ltac spe_tac k :=
        intros until k;
        let Sem := fresh in
        let n := fresh in
        intros Sem ** n; specialize (Sem n); eauto.

      Tactic Notation "spe" integer(k) :=
        spe_tac k.

      Lemma var_var_correctness:
        forall x vs,
          (forall n, find_val x (M n) = None) ->
          sem_var H x vs ->
          SemSB.sem_var_var H' x vs.
      Proof. spe 1. Qed.
      Hint Resolve var_var_correctness.

      Lemma clock_correctness:
        forall ck bs,
          sem_clock bk H ck bs ->
          SemSB.sem_clock bk H' E (translate_clock lasts ck) bs.
      Proof. spe 0. Qed.
      Hint Resolve clock_correctness.

      Lemma state_var_correctness:
        forall x vs ck,
          (forall n, find_val x (M n) <> None) ->
          sem_var H x vs ->
          correct_clock ck vs ->
          SemSB.sem_state_var bk H' E (translate_clock lasts ck) x vs.
      Proof. spe 2. Qed.
      Hint Resolve state_var_correctness.

      Lemma var_correctness:
        forall x vs ck,
          sem_var H x vs ->
          correct_clock ck vs ->
          SemSB.sem_var bk H' E (translate_clock lasts ck) (tovar lasts x) vs.
      Proof. spe 1. Qed.
      Hint Resolve var_correctness.

      Lemma lexp_correctness:
        forall e vs ck vars,
          sem_lexp bk H e vs ->
          wc_lexp vars e ck ->
          correct_clock ck vs ->
          SemSB.sem_lexp bk H' E (translate_clock lasts ck) (translate_lexp lasts e) vs.
      Proof. spe 2. Qed.
      Hint Resolve lexp_correctness.

      Lemma cexp_correctness:
        forall e vs ck vars,
          sem_cexp bk H e vs ->
          wc_cexp vars e ck ->
          correct_clock ck vs ->
          SemSB.sem_cexp bk H' E (translate_clock lasts ck) (translate_cexp lasts e) vs.
      Proof. spe 2. Qed.
      Hint Resolve cexp_correctness.

      Lemma laexp_correctness:
        forall e ck vs vars,
          sem_laexp bk H ck e vs ->
          wc_lexp vars e ck ->
          SemSB.sem_laexp bk H' E (translate_clock lasts ck) (translate_lexp lasts e) vs.
      Proof. spe 0. Qed.

      Lemma caexp_correctness:
        forall e ck vs vars,
          sem_caexp bk H ck e vs ->
          wc_cexp vars e ck ->
          SemSB.sem_caexp bk H' E (translate_clock lasts ck) (translate_cexp lasts e) vs.
      Proof. spe 0. Qed.


    End Sem.
    Hint Resolve
         var_var_correctness
         laexp_correctness
         caexp_correctness.

    Inductive relooper: Env.t const -> SemSB.evolution -> SemSB.evolution -> Prop :=
      relooper_intro:
        forall E E' lasts,
        (forall x vs vs' c,
            find_val x E = Some vs ->
            find_val x E' = Some vs' ->
            (forall n, vs (S n) = vs' n)
            /\ vs 0 = sem_const c) ->
        relooper lasts E E'.

    Inductive coherent_state: SemSB.evolution -> SemSB.transient_evolutions -> SemSB.evolution -> Prop :=
      coherent_state_intro:
        forall E T E',
          (forall x vs,
              find_val x E = Some vs ->
              exists vs', find_val x E' = Some vs') ->
          coherent_state E T E'.

    (* Inductive correspondence: *)
    (*   history -> Env.t const -> SemSB.history -> SemSB.evolution -> SemSB.transient_evolutions -> SemSB.evolution -> Prop := *)
    (*   correspondence_intro: *)
    (*     forall H lasts H' E T E', *)
    (*       compat_hist H lasts H' E -> *)
    (*       coherent_state E T E' -> *)
    (*       relooper lasts E E' -> *)
    (*       correspondence H lasts H' E T E'. *)

    (* Fact find_mem: *)
    (*   forall {A} x e (v: A), *)
    (*     Env.find x e = Some v -> *)
    (*     Env.mem x e = true. *)
    (* Proof. *)
    (*   unfold Env.mem; intros ** ->; auto. *)
    (* Qed. *)
    (* Hint Resolve find_mem. *)

    Lemma hold_det:
      forall v0 xs xs',
        same_clock (fun n => [xs n; xs' n]) ->
        hold v0 xs ≈ hold v0 xs' ->
        xs ≈ xs'.
    Proof.
      intros ** Same Eq n.
      specialize (Eq (S n)); simpl in *.
      specialize (Same n); destruct Same as [Same|Same].
      + inversion_clear Same as [|??? Same']; inv Same'; congruence.
      + inversion_clear Same as [|??? Same']; inv Same'; destruct (xs n), (xs' n); congruence.
    Qed.

    Lemma hold_det':
      forall n v0 xs xs',
        instant_same_clock [xs n; xs' n] ->
        hold v0 xs (S n) = hold v0 xs' (S n) ->
        xs n = xs' n.
    Proof.
      intros ** Same Eq.
      simpl in *.
      destruct Same as [Same|Same].
      + inversion_clear Same as [|??? Same']; inv Same'; congruence.
      + inversion_clear Same as [|??? Same']; inv Same'; destruct (xs n), (xs' n); congruence.
    Qed.

    Inductive lasts_eq_spec (lasts: Env.t const) : equation -> Prop :=
      | LSdef:
          forall x ck e,
            Env.mem x lasts = false ->
            lasts_eq_spec lasts (EqDef x ck e)
      | LSapp:
          forall xs ck f es r,
            Forall (fun x => Env.mem x lasts = false) xs ->
            lasts_eq_spec lasts (EqApp xs ck f es r)
      | LSfby:
          forall x ck c0 e,
            Env.find x lasts = Some c0 ->
            lasts_eq_spec lasts (EqFby x ck c0 e).

    Fact hd_error_Some_hd:
      forall {A} d (xs: list A) x,
        hd_error xs = Some x ->
        hd d xs = x.
    Proof.
      destruct xs; simpl; intros; try discriminate.
      now inv H.
    Qed.

    Lemma equation_correctness:
      forall lasts eq bk H M eqs H' E T E' vars,
        (* (forall f xss oss, *)
        (*     sem_node G f xss oss -> *)
        (*     exists M, SemSB.sem_block P f M xss oss) -> *)
        (* (forall f r xss oss, *)
        (*     sem_reset G f r xss oss -> *)
        (*     exists M, SemSB.sem_block P f M xss oss *)
        (*          /\ SemSB.reset_regs r M) -> *)
        msem_equation G bk H M eq ->
        lasts_eq_spec lasts eq ->
        (* compat_eq eq eqs -> *)
        lasts_spec lasts M ->
        compat_state H M H' E ->
        coherent_msem_state H M ->
        relooper lasts E E' ->
        coherent_state E T E' ->
        wc_equation vars eq ->
        Forall (SemSB.sem_equation P bk H' E T E') eqs ->
        (* correspondence H lasts H' E T E' -> *)
        (* SemSB.well_structured_memories eqs M -> *)
        (* exists H' E T E', *)
        Forall (SemSB.sem_equation P bk H' E T E') (translate_eqn lasts eq ++ eqs).
    (* /\ SemSB.well_structured_memories (translate_eqn eq ++ eqs) M'. *)
    Proof.
      intros ** Heq LastsEqSpec LastsSpec Compat Coherent Reloop Coherent' WC Heqs(* Corres *);
        destruct Heq as [| | |?????????? Var];
        inversion_clear LastsEqSpec as [??? Last| |];
        inv WC;
        (* inversion_clear Corres as [?????? Compat Coherent Reloop]; *)
        simpl.
      - constructor; eauto.
        econstructor; eauto.
        eapply var_var_correctness; eauto.
        intro; specialize (LastsSpec n x); rewrite Last in LastsSpec; auto.
      - erewrite hd_error_Some_hd; eauto.
        constructor.
        + admit.
        + constructor; auto.
          admit.
      - erewrite hd_error_Some_hd; eauto.
        constructor.
        + admit.
        + constructor; auto.
          admit.
      - constructor; auto.
        econstructor; eauto.
        instantiate (1 := ls).
        pose proof Var as Var'.
        assert (forall n : nat, find_val x (M n) <> None) by admit.
        assert (correct_clock bk H ck xs) by admit.
        eapply (state_var_correctness bk H M H' E _ _ lasts _ _ _ ck(*H M H' E*)) in Var'; eauto.
        inversion_clear Reloop as [??? Loop].
        intro.
        specialize (Var n); inversion_clear Var as [?? Find].
        unfold restr_hist, PM.map in Find; rewrite PM.gmapi in Find.
        destruct (PM.find x H) eqn: Find'; inversion Find as [Eq]; clear Find.
        destruct (ls n) eqn: Els.
        + constructor.
          * unfold SemSB.restr_evol.
            rewrite find_val_mmap.
            assert (find_val x E = Some v).
            assert (exists z, find_val x E' = Some z) as (? & ->); simpl; try congruence.
            inversion_clear Coherent' as [??? SpecE']; eapply SpecE'.
            unfold compat_state, compat_state_instant in Compat.
            instantiate (1 := v).

            apply Compat in Find'; rewrite Mem in Find'.
        pose proof Find' as Find''.
        inversion_clear Coherent as [??? Spec].
        apply Spec in Find'' as (? & Find'').
        rewrite Find''; unfold SemSB.sample; simpl.
        eapply Loop in Find'; eauto.
        rewrite Find' in Fby.
        admit.

        inv Fby.
instantiate (1 := ls).

        inv Find.
        unfold fby in *.


      Lemma sem_equation_add_inst:
        forall M M' x eqs,
          ~ inst_in_eqs x eqs ->
          Forall (SemSB.sem_equation P bk H M) eqs ->
          Forall (SemSB.sem_equation P bk H (add_inst x M' M)) eqs.
      Proof.
        intros * Hnd Hsem.
        induction eqs as [|eq eqs IH]; [now constructor|].
        apply not_inst_in_eqs_cons in Hnd as [Hnd].
        apply Forall_cons2 in Hsem as [Hsem Hsems].
        constructor; auto.
        induction eq; inv Hsem; eauto using SemSB.sem_equation.
        - econstructor; eauto.
          unfold sub_inst.
          unfold sub_inst; rewrite find_inst_gso; auto.
          intro; apply Hnd; subst; constructor.
        - econstructor; eauto.
          unfold sub_inst; rewrite find_inst_gso; auto.
          intro; apply Hnd; subst; constructor.
      Qed.

      Lemma sem_equation_add_val:
        forall M mv x eqs,
          ~ defined_in_eqs x eqs ->
          Forall (SemSB.sem_equation P bk H M) eqs ->
          Forall (SemSB.sem_equation P bk H (add_val x mv M)) eqs.
      Proof.
        intros * Hnd Hsem.
        induction eqs as [|eq eqs IH]; [now constructor|].
        apply not_defined_in_eqs_cons in Hnd as [Hnd].
        apply Forall_cons2 in Hsem as [Hsem Hsems].
        constructor; auto.
        induction eq; inv Hsem; eauto using SemSB.sem_equation.
        econstructor; eauto.
        apply mfby_add_val; auto.
        intro; subst; apply Hnd; constructor.
      Qed.

    End Sem.

    Lemma equation_correctness:
      forall bk H eqs M eq,
        (forall f xss oss,
            sem_node G f xss oss ->
            exists M, SemSB.sem_block P f M xss oss) ->
        (forall f r xss oss,
            sem_reset G f r xss oss ->
            exists M, SemSB.sem_block P f M xss oss
                 /\ SemSB.reset_regs r M) ->
        sem_equation G bk H eq ->
        compat_eq eq eqs ->
        Forall (SemSB.sem_equation P bk H M) eqs ->
        SemSB.well_structured_memories eqs M ->
        exists M', Forall (SemSB.sem_equation P bk H M') (translate_eqn eq ++ eqs)
              /\ SemSB.well_structured_memories (translate_eqn eq ++ eqs) M'.
    Proof.
      intros ** IHnode IHreset Heq WF Heqs WS.
      inv Heq; simpl; inv WF.
      - repeat (econstructor; eauto).
      - edestruct IHnode as (M' & Block); eauto.
        exists (add_inst (hd default x) M' M); split.
        + constructor.
          * econstructor; eauto.
            apply find_inst_gss.
          * apply sem_equation_add_inst; auto.
        + apply SemSB.well_structured_add_inst_call; auto.
      - edestruct IHreset as (M' & Block & Reset); eauto.
        exists (add_inst (hd default x) M' M); split.
        + constructor.
          * econstructor; eauto.
            apply find_inst_gss.
          *{ constructor.
             - econstructor; eauto.
               apply find_inst_gss.
             - apply sem_equation_add_inst; auto.
           }
        + apply SemSB.well_structured_add_inst_reset_call; auto.
      - exists (add_val x {| SemSB.content := hold (sem_const c0) ls; SemSB.reset := fun _ => false |} M); split.
        + constructor.
          *{ econstructor; eauto.
             econstructor.
             - apply find_val_gss.
             - reflexivity.
             - intro; unfold fby; simpl.
               destruct (ls n); auto.
           }
          * apply sem_equation_add_val; auto.
        + apply SemSB.well_structured_add_val_fby; auto.
    Qed.

    Lemma well_structured_empty:
      SemSB.well_structured_memories [] (empty_memory SemSB.mvalues).
    Proof.
      constructor; unfold find_val, find_inst, SemSB.fbys, SemSB.insts;
        simpl; intros; split; intro H; contradict H; auto; apply not_In_empty.
    Qed.

    Corollary equations_correctness:
      forall bk H eqs,
        (forall f xss oss,
            sem_node G f xss oss ->
            exists M, SemSB.sem_block P f M xss oss) ->
        (forall f r xss oss,
            sem_reset G f r xss oss ->
            exists M, SemSB.sem_block P f M xss oss
                 /\ SemSB.reset_regs r M) ->
        compat_eqs eqs ->
        Forall (sem_equation G bk H) eqs ->
        exists M', Forall (SemSB.sem_equation P bk H M') (translate_eqns eqs)
              /\ SemSB.well_structured_memories (translate_eqns eqs) M'.
    Proof.
      intros ** IHnode IHreset WF Heqs.
      induction eqs as [|eq eqs IHeqs].
      - exists (@empty_memory SemSB.mvalues).
        split; try now constructor.
        apply well_structured_empty.
      - apply Forall_cons2 in Heqs as [Heq Heqs].
        inv WF.
        eapply IHeqs in Heqs as [? ()]; eauto.
        unfold translate_eqns; rewrite concatMap_cons.
        eapply equation_correctness; eauto.
    Qed.

    Lemma find_block_later_not_is_block_in:
      forall b n bl P',
        Ordered_nodes (n :: G) ->
        SynSB.find_block b P = Some (bl, P') ->
        ~ is_block_in n.(n_name) bl.(SynSB.b_eqs).
    Proof.
      intros ** Hord Hfind Hini.
      pose proof (SynSB.find_block_name _ _ _ _ Hfind) as Hb.
      apply find_block_translate in Hfind as (n' & Hfind' & E).
      rewrite E in Hini; simpl in Hini.
      apply is_block_is_node in Hini.
      eapply find_node_later_not_Is_node_in; eauto.
    Qed.

    Lemma find_block_not_is_block_in:
      forall b bl P',
        Ordered_nodes G ->
        SynSB.find_block b P = Some (bl, P') ->
        ~ is_block_in bl.(SynSB.b_name) bl.(SynSB.b_eqs).
    Proof.
      intros ** Hord Hfind Hini.
      pose proof (SynSB.find_block_name _ _ _ _ Hfind) as Hb.
      apply find_block_translate in Hfind as (n' & Hfind' & E).
      apply find_node_split in Hfind' as [G' [aG Hge]].
      rewrite Hge in Hord.
      apply Ordered_nodes_append in Hord.
      inversion_clear Hord as [|? ? Hord' Heqs Hnin].
      destruct (Heqs (SynSB.b_name bl)) as (Eq).
      - subst bl; simpl in *.
        clear - Hini.
        induction (n_eqs n') as [|eq]; simpl in *.
        + inv Hini.
        + unfold translate_eqns, concatMap, is_block_in in Hini; simpl in Hini.
          unfold is_block_in in Hini; rewrite Exists_app' in Hini.
          destruct Hini as [Hini|Hini].
          * left.
            destruct eq; try destruct o as [()|]; simpl in Hini;
              inversion_clear Hini as [?? In|?? Nil];
              try inversion_clear Nil as [?? In|?? Nil']; try inv In; try inv Nil';
                constructor.
          * right. apply IHl; auto.
      - apply Eq; subst bl; reflexivity.
    Qed.

    Lemma sem_block_cons:
      forall n f xs M ys,
        Ordered_nodes (n :: G) ->
        n.(n_name) <> f ->
        SemSB.sem_block (translate (n :: G)) f xs M ys ->
        SemSB.sem_block P f xs M ys.
    Proof.
      intros ** Hord Hnf Hsem.
      revert Hnf.
      induction Hsem
        as [| | | |????????? Hfind ????? Heqs WS IHeqs]
             using SemSB.sem_block_mult
        with (P_equation := fun bk H M eq =>
                              ~ is_block_in_eq n.(n_name) eq ->
                              SemSB.sem_equation (translate G) bk H M eq);
        eauto using SemSB.sem_equation.
      - intros Hnin.
        econstructor; eauto.
        apply IHHsem.
        intro Hnb; apply Hnin.
        rewrite Hnb; constructor.
      - intro; simpl in Hfind; apply ident_eqb_neq in Hnf; rewrite Hnf in Hfind; eauto.
        econstructor; eauto.
        assert (Forall (fun eq => ~ is_block_in_eq (n_name n) eq) (SynSB.b_eqs bl)) as NotIns
            by (eapply is_block_in_Forall, find_block_later_not_is_block_in; eauto).
        clear Heqs WS.
        induction (SynSB.b_eqs bl); inv NotIns; inv IHeqs; constructor; auto.
    Qed.

    Lemma sem_block_cons2:
      forall n f xs M ys,
        Forall (fun n' => n_name n <> n_name n') G ->
        SemSB.sem_block P f xs M ys ->
        SemSB.sem_block (translate (n :: G)) f xs M ys.
    Proof.
      intros ** Hnin Hsem.
      induction Hsem
        as [| | | |????????? Hfind]
             using SemSB.sem_block_mult
        with (P_equation := fun bk H M eq =>
                              SemSB.sem_equation (translate (n :: G)) bk H M eq);
        eauto using SemSB.sem_equation.
      econstructor; eauto.
      simpl.
      assert (n.(n_name) <> b) as Hnf.
      { intro Hnf.
        rewrite Hnf in *.
        pose proof (SynSB.find_block_name _ _ _ _ Hfind) as Hb.
        apply find_block_translate in Hfind as (n' & Hfind' & ?).
        apply find_node_split in Hfind' as [G' [aG Hge]].
        rewrite Hge in Hnin.
        apply Forall_app in Hnin.
        destruct Hnin as [H' Hfg]; clear H'.
        inversion_clear Hfg.
        match goal with H:b<>_ |- False => apply H end.
        rewrite <-Hb; subst bl; auto.
      }
      apply ident_eqb_neq in Hnf; rewrite Hnf.
      eauto.
    Qed.

    Lemma sem_equation_cons:
      forall bk H M eqs n,
        Ordered_nodes (n :: G) ->
        ~Is_node_in n.(n_name) eqs ->
        Forall (SemSB.sem_equation P bk H M) (translate_eqns eqs) ->
        Forall (SemSB.sem_equation (translate (n :: G)) bk H M) (translate_eqns eqs).
    Proof.
      intros ** Hord Hnini Hsem.
      induction eqs as [|eq eqs IH]; [now constructor|].
      unfold translate_eqns in *; rewrite concatMap_cons in Hsem.
      apply Forall_app in Hsem as [Heq Heqs].
      apply not_Is_node_in_cons in Hnini.
      destruct Hnini as [Hnini Hninis].
      apply IH with (1:=Hninis) in Heqs.
      rewrite concatMap_cons.
      apply Forall_app; split; auto.
      inv Hord.
      induction eq; simpl in *.
      - constructor; auto.
        inversion_clear Heq as [|?? Hsem].
        inv Hsem; eauto using SemSB.sem_equation.
      - destruct o as [(r, ckr)|]; inversion_clear Heq as [|?? Hsem Heq'];
          constructor; inv Hsem; econstructor; eauto.
        + inversion_clear Heq' as [|?? Hsem'].
          inv Hsem'; econstructor; eauto.
          apply sem_block_cons2; auto.
        + apply sem_block_cons2; auto.
      - constructor; auto.
        inversion_clear Heq as [|?? Hsem].
        inv Hsem; eauto using SemSB.sem_equation.
    Qed.

  End Global.


  Fixpoint path_inst (p: list ident) (M: SemSB.memories) : option SemSB.memories :=
    match p with
    | [] => Some M
    | x :: p =>
      match find_inst x M with
      | Some M => path_inst p M
      | None => None
      end
    end.

  Lemma path_inst_last:
    forall p M M' x M'',
      path_inst p M = Some M' ->
      sub_inst x M' M'' ->
      path_inst (p ++ [x]) M = Some M''.
  Proof.
    induction p as [|y]; simpl; intros ** Path Sub.
    - inv Path; rewrite Sub; auto.
    - destruct (find_inst y M); inv Path; eauto.
  Qed.

  Section Choices.

    Variable Fm: nat -> SemSB.memories.
    Variable Fh: nat -> history.
    Variable Fmvs: nat -> SemSB.mvalues.
    Variable r: stream bool.

    Definition reset_content (x: ident) (p: list ident) : stream val :=
      fun n => match path_inst p (Fm (count r n)) with
            | Some M =>
              match find_val x M with
              | Some mv => mv.(SemSB.content) n
              | None => false_val
              end
            | None => false_val
            end.

    Definition reset_reset (x: ident) (p: list ident) : stream bool :=
      fun n => match path_inst p (Fm (count r n)) with
            | Some M =>
              match find_val x M with
              | Some mv => r n || mv.(SemSB.reset) n
              | None => r n
              end
            | None => r n
            end.

    Lemma reset_reset_spec:
      forall n x p,
        r n = true ->
        reset_reset x p n = true.
    Proof.
      unfold reset_reset; intros ** ->.
      destruct (path_inst p (Fm (count r n))); auto.
      destruct (find_val x m); auto.
    Qed.

    Definition reset_memories_path (p: list ident) (M0: SemSB.memories) : SemSB.memories :=
      mmapi (fun p x mv =>
               {| SemSB.content := reset_content x p;
                  SemSB.reset := reset_reset x p |})
            p M0.

    Definition reset_memories := reset_memories_path [].

    Lemma sub_inst_reset_memories_path:
      forall x p M M',
        sub_inst x M M' ->
        sub_inst x (reset_memories_path p M) (reset_memories_path (p ++ [x]) M').
    Proof.
      intros ** Find; unfold sub_inst, reset_memories_path.
      rewrite find_inst_mmapi, Find; auto.
    Qed.

    Lemma sub_inst_reset_memories_path':
      forall x p M M',
        sub_inst x (reset_memories_path p M) M' ->
        exists M'', M' = reset_memories_path (p ++ [x]) M''
               /\ sub_inst x M M''.
    Proof.
      unfold sub_inst, reset_memories_path; intros ** Find.
      rewrite find_inst_mmapi in Find.
      destruct (find_inst x M) eqn: E; inv Find; eauto.
    Qed.

    Lemma reset_memories_path_spec:
      forall k p r',
        (forall n,
            r' n = true ->
            r n = true) ->
        SemSB.reset_regs r' (reset_memories_path p (Fm k)).
    Proof.
      intros ** Spec; unfold reset_memories_path.
      revert p.
      induction (Fm k) as [?? IH] using memory_ind'.
      constructor.
      - intros x mvs.
        unfold find_val.
        simpl; rewrite Env.find_mapi.
        intro Find.
        destruct (Env.find x xvs); inv Find; auto.
        intros; simpl; apply reset_reset_spec; auto.
      - induction xms as [|[y]].
        + intros; discriminate.
        + simpl in IH; inv IH.
          intros x M'.
          unfold sub_inst, find_inst.
          simpl.
          destruct (Env.POTB.compare x y); simpl;
            intro Find; inv Find; eauto.
    Qed.

    Corollary reset_memories_path_sub_spec:
      forall k p r' x M,
        sub_inst x (Fm k) M ->
        (forall n, r' n = true -> r n = true) ->
        SemSB.reset_regs r' (reset_memories_path (p ++ [x]) M).
    Proof.
      intros ** Sub Spec; eapply reset_memories_path_spec with (k := k) in Spec.
      inversion_clear Spec as [??? Inst]; eapply Inst, sub_inst_reset_memories_path; eauto.
    Qed.

    Corollary reset_memories_spec:
      forall k r',
        (forall n, r' n = true -> r n = true) ->
        SemSB.reset_regs r (reset_memories (Fm k)).
    Proof.
      intros; now apply reset_memories_path_spec.
    Qed.

    Definition reset_history (H0: history) : history :=
      PM.mapi (fun x _ => fun n => match PM.find x (Fh (count r n)) with
                             | Some xs => xs n
                             | None => absent
                             end) H0.

    Definition reset_mvalues: SemSB.mvalues :=
    {| SemSB.content := fun n => (Fmvs (count r n)).(SemSB.content) n;
       SemSB.reset := fun n => r n || (Fmvs (count r n)).(SemSB.reset) n |}.

    Lemma reset_mvalues_spec:
      forall x e c0 ck xss,
        (forall n, 0 < length (xss n)) ->
        (forall k,
            exists bk xs ls,
              sem_var (Fh k) x xs
              /\ sem_laexp bk (Fh k) ck e ls
              /\ find_val x (Fm k) = Some (Fmvs k)
              /\ SemSB.content (Fmvs k) 0 = sem_const c0
              /\ (forall n : nat,
                    match ls n with
                    | absent =>
                      SemSB.content (Fmvs k) (S n) =
                      (if SemSB.reset (Fmvs k) (S n)
                       then sem_const c0
                       else SemSB.content (Fmvs k) n)
                      /\ xs n = absent
                    | present v' =>
                      SemSB.content (Fmvs k) (S n) =
                      (if SemSB.reset (Fmvs k) (S n)
                       then sem_const c0
                       else v')
                      /\ xs n = present (SemSB.content (Fmvs k) n)
                    end)
              /\ clock_of (mask (all_absent (xss 0)) k r xss) bk) ->
        forall n, r n = true ->
             SemSB.content reset_mvalues n = sem_const c0.
    Proof.
      intros ** Length Spec n E.
      unfold reset_mvalues; simpl.
      induction n; simpl; rewrite E.
      - destruct (Spec 1) as (?&?&?&?); intuition.
      - specialize (Spec (S (count r n))); destruct Spec as (bk &?&?&?& Hexp &?& Init & Heq & Clock).
        assert (forall n',
                   n' <= n ->
                   interp_laexp_instant (bk n') (restr_hist (Fh (S (count r n))) n') ck e = absent)
          as Absent.
        { assert (forall n',
                     n' <= n ->
                     bk n' = false) as Hbk.
          { clear - Clock Length.
            intros ** Lte.
            specialize (Clock n').
            rewrite mask_opaque in Clock; auto.
            - apply Bool.not_true_is_false; intro Ebk.
              apply Clock in Ebk.
              specialize (Length 0).
              clear - Ebk Length; induction (xss 0); simpl in *; inv Ebk; auto; omega.
            - apply Lt.le_lt_or_eq in Lte as [Lt|]; subst; auto.
              apply (count_le' r) in Lt; omega.
          }
          intros.
          specialize (Hexp n'); simpl in Hexp.
          pose proof Hexp as Hexp'; apply interp_laexp_instant_sound in Hexp'; rewrite Hexp' in Hexp.
          destruct (interp_laexp_instant (bk n') (restr_hist (Fh (S (count r n))) n') ck e); auto.
          inversion_clear Hexp as [???? HClock|].
          rewrite Hbk in HClock; auto; contradict HClock.
          apply not_subrate_clock.
        }
        assert (forall n', n' <= n -> SemSB.content (Fmvs (S (count r n))) n' = sem_const c0) as Spec.
        { intros ** Lte.
          induction n'; auto.
          specialize (Hexp n'); simpl in Hexp; apply interp_laexp_instant_sound in Hexp.
          specialize (Heq n').
          rewrite Hexp, Absent in Heq; try omega; destruct Heq as (->).
          destruct (SemSB.reset (Fmvs (S (count r n))) (S n')); auto.
          apply IHn'; omega.
        }
        specialize (Hexp n); simpl in Hexp; apply interp_laexp_instant_sound in Hexp.
        specialize (Heq n);
          rewrite Hexp, Absent in Heq; auto; destruct Heq as (->).
        destruct (SemSB.reset (Fmvs (S (count r n))) (S n)); auto.
    Qed.

    Lemma find_val_reset_memories:
      forall x,
        (forall k, find_val x (Fm k) = Some (Fmvs k)) ->
        find_val x (reset_memories (Fm 0)) = Some reset_mvalues.
    Proof.
      intros ** Spec.
      unfold reset_mvalues, reset_memories, reset_memories_path.
      rewrite find_val_mmapi.
      destruct (find_val x (Fm 0)) eqn: E; simpl.
      - do 3 f_equal.
        + unfold reset_content; simpl.
          extensionality n.
          rewrite Spec; auto.
        + unfold reset_reset.
          extensionality n.
          simpl; rewrite Spec; auto.
      - rewrite Spec in E; discriminate.
    Qed.

    Section InterpReset.

      Variable n: nat.

      Definition spec_var (x: ident) : Prop :=
        forall k, PM.find x (Fh k) <> None.

      Definition spec_vars := Forall spec_var.

      Inductive spec_clock: clock -> Prop :=
      | spec_clock_base:
          spec_clock Cbase
      | spec_clock_con:
          forall ck x b,
            spec_var x ->
            spec_clock ck ->
            spec_clock (Con ck x b).

      Inductive spec_lexp: lexp -> Prop :=
      | spec_lexp_const:
          forall c,
            spec_lexp (Econst c)
      | spec_lexp_var:
          forall x t,
            spec_var x ->
            spec_lexp (Evar x t)
      | spec_lexp_when:
          forall e x b,
            spec_var x ->
            spec_lexp e ->
            spec_lexp (Ewhen e x b)
      | spec_lexp_unop:
          forall op e t,
            spec_lexp e ->
            spec_lexp (Eunop op e t)
      | spec_lexp_binop:
          forall op e1 e2 t,
            spec_lexp e1 ->
            spec_lexp e2 ->
            spec_lexp (Ebinop op e1 e2 t).

      Definition spec_lexps := Forall spec_lexp.

      Inductive spec_cexp: cexp -> Prop :=
      | spec_cexp_merge:
          forall x e1 e2,
            spec_var x ->
            spec_cexp e1 ->
            spec_cexp e2 ->
            spec_cexp (Emerge x e1 e2)
      | spec_cexp_ite:
          forall le e1 e2,
            spec_lexp le ->
            spec_cexp e1 ->
            spec_cexp e2 ->
            spec_cexp (Eite le e1 e2)
      | spec_cexp_exp:
          forall e,
            spec_lexp e ->
            spec_cexp (Eexp e).

      Inductive spec_eq: SynSB.equation -> Prop :=
      | spec_eq_def:
          forall x ck e,
            spec_var x ->
            spec_clock ck ->
            spec_cexp e ->
            spec_eq (SynSB.EqDef x ck e)
      | spec_eq_fby:
          forall x ck c0 e,
            spec_var x ->
            spec_clock ck ->
            spec_lexp e ->
            spec_eq (SynSB.EqFby x ck c0 e)
      | spec_eq_reset:
          forall ck b i r,
            spec_var r ->
            spec_eq (SynSB.EqReset ck b i r)
      | spec_eq_call:
          forall xs ck b i es,
            spec_vars xs ->
            spec_clock ck ->
            spec_lexps es ->
            spec_eq (SynSB.EqCall xs ck b i es).

      Lemma sem_var_instant_reset:
        forall x v,
          spec_var x ->
          sem_var_instant (restr_hist (Fh (count r n)) n) x v ->
          sem_var_instant (restr_hist (reset_history (Fh 0)) n) x v.
      Proof.
        intros ** Spec Sem.
        induction Sem; constructor.
        unfold reset_history, restr_hist, PM.map in *.
        repeat rewrite PM.gmapi in *; rewrite option_map_map.
        destruct (PM.find x (Fh (count r n))) eqn: E.
        - destruct (PM.find x (Fh 0)) eqn: E'; auto.
          exfalso; eapply Spec; eauto.
        - exfalso; eapply Spec; eauto.
      Qed.
      Hint Resolve sem_var_instant_reset.

      Lemma sem_vars_instant_reset:
        forall xs vs,
          spec_vars xs ->
          sem_vars_instant (restr_hist (Fh (count r n)) n) xs vs ->
          sem_vars_instant (restr_hist (reset_history (Fh 0)) n) xs vs.
      Proof.
        intros ** Spec Sem.
        induction Sem; inv Spec; constructor; auto.
        apply IHSem; auto.
      Qed.

      Variable bk: stream bool.
      Variable xss: stream (list value).
      Hypothesis Clk: clock_of (mask (all_absent (xss 0)) (count r n) r xss) bk.
      Let bk' := clock_of' xss.

      Lemma sem_clock_instant_reset:
        forall ck b,
          spec_clock ck ->
          sem_clock_instant (bk n) (restr_hist (Fh (count r n)) n) ck b ->
          sem_clock_instant (bk' n) (restr_hist (reset_history (Fh 0)) n) ck b.
      Proof.
        intros ** Spec Sem; induction Sem; inv Spec; eauto using sem_clock_instant.
        apply clock_of_equiv' in Clk; rewrite Clk.
        subst bk'.
        unfold clock_of'.
        rewrite mask_transparent; constructor.
      Qed.
      Hint Resolve sem_clock_instant_reset.

      Lemma sem_lexp_instant_reset:
        forall e v,
          spec_lexp e ->
          sem_lexp_instant (bk n) (restr_hist (Fh (count r n)) n) e v ->
          sem_lexp_instant (bk' n) (restr_hist (reset_history (Fh 0)) n) e v.
      Proof.
        intros ** Spec Sem; induction Sem; inv Spec; eauto using sem_lexp_instant.
        constructor; subst.
        apply clock_of_equiv' in Clk; rewrite Clk.
        unfold clock_of'.
        rewrite mask_transparent; auto.
      Qed.
      Hint Resolve sem_lexp_instant_reset.

      Lemma sem_lexps_instant_reset:
        forall es vs,
          spec_lexps es ->
          sem_lexps_instant (bk n) (restr_hist (Fh (count r n)) n) es vs ->
          sem_lexps_instant (bk' n) (restr_hist (reset_history (Fh 0)) n) es vs.
      Proof.
        unfold sem_lexps_instant; intros ** Spec Sem;
          induction Sem; inv Spec; constructor; eauto.
      Qed.
      Hint Resolve sem_lexps_instant_reset.

      Lemma sem_laexp_instant_reset:
        forall ck e v,
          spec_clock ck ->
          spec_lexp e ->
          sem_laexp_instant (bk n) (restr_hist (Fh (count r n)) n) ck e v ->
          sem_laexp_instant (bk' n) (restr_hist (reset_history (Fh 0)) n) ck e v.
      Proof.
        induction 3; constructor; auto.
      Qed.

      Lemma sem_laexps_instant_reset:
        forall ck es vs,
          spec_clock ck ->
          spec_lexps es ->
          sem_laexps_instant (bk n) (restr_hist (Fh (count r n)) n) ck es vs ->
          sem_laexps_instant (bk' n) (restr_hist (reset_history (Fh 0)) n) ck es vs.
      Proof.
        induction 3.
        - eapply SLticks; eauto.
        - apply SLabss; auto.
      Qed.

      Lemma sem_cexp_instant_reset:
        forall e v,
          spec_cexp e ->
          sem_cexp_instant (bk n) (restr_hist (Fh (count r n)) n) e v ->
          sem_cexp_instant (bk' n) (restr_hist (reset_history (Fh 0)) n) e v.
      Proof.
        intros ** Spec Sem; induction Sem; inv Spec; eauto using sem_cexp_instant.
      Qed.
      Hint Resolve sem_cexp_instant_reset.

      Lemma sem_caexp_instant_reset:
        forall ck e v,
          spec_clock ck ->
          spec_cexp e ->
          sem_caexp_instant (bk n) (restr_hist (Fh (count r n)) n) ck e v ->
          sem_caexp_instant (bk' n) (restr_hist (reset_history (Fh 0)) n) ck e v.
      Proof.
        induction 3; constructor; auto.
      Qed.

    End InterpReset.

    Lemma sem_spec_var_instant:
      forall x,
        (forall k n, exists v, sem_var_instant (restr_hist (Fh k) n) x v) ->
        spec_var x.
    Proof.
      intros ** Sem k E; destruct (Sem k 0) as (?& Sem');
        inversion_clear Sem' as [?? Find].
      unfold restr_hist, PM.map in Find.
      rewrite PM.gmapi, E in Find.
      discriminate.
    Qed.

    Corollary sem_spec_var:
      forall x,
        (forall k, exists xs, sem_var (Fh k) x xs) ->
        spec_var x.
    Proof.
      intros x Sem; apply sem_spec_var_instant.
      intros; destruct (Sem k) as (?& Sem');
        specialize (Sem' n); eauto.
    Qed.

    Lemma sem_spec_vars_instant:
      forall xs,
        (forall k n, exists xss, sem_vars_instant (restr_hist (Fh k) n) xs xss) ->
        spec_vars xs.
    Proof.
      intros ** Sem; induction xs; constructor.
      - apply sem_spec_var_instant; intros; destruct (Sem k n) as (?& Sem'); inv Sem'; eauto.
      - apply IHxs; intros; destruct (Sem k n) as (?& Sem'); inv Sem'; eauto.
    Qed.

    Corollary sem_spec_vars:
      forall xs,
        (forall k, exists xss, sem_vars (Fh k) xs xss) ->
        spec_vars xs.
    Proof.
      intros ** Sem; apply sem_spec_vars_instant.
      intros; destruct (Sem k) as (?& Sem'); specialize (Sem' n); eauto.
    Qed.

    Lemma sem_spec_clock_instant:
      forall ck,
        (forall k n, exists base b, sem_clock_instant base (restr_hist (Fh k) n) ck b) ->
        spec_clock ck.
    Proof.
      intros ** Sem; induction ck; constructor.
      - apply sem_spec_var_instant; intros.
        destruct (Sem k n) as (?&?& Clock); inv Clock; eauto.
      - apply IHck.
        intros; destruct (Sem k n) as (?&?& Clock); inv Clock; eauto.
    Qed.

    Corollary sem_spec_clock_caexp:
      forall ck e,
        (forall k, exists bk vs, sem_caexp bk (Fh k) ck e vs) ->
        spec_clock ck.
    Proof.
      intros ** Sem; apply sem_spec_clock_instant.
      intros; destruct (Sem k) as (?&?& Sem'); specialize (Sem' n); simpl in Sem'.
      inv Sem'; eauto.
    Qed.

    Corollary sem_spec_clock_laexp:
      forall ck e,
        (forall k, exists bk vs, sem_laexp bk (Fh k) ck e vs) ->
        spec_clock ck.
    Proof.
      intros ** Sem; apply sem_spec_clock_instant.
      intros; destruct (Sem k) as (?&?& Sem'); specialize (Sem' n); simpl in Sem'.
      inv Sem'; eauto.
    Qed.

    Lemma sem_spec_clock_laexps:
      forall ck es,
        (forall k, exists bk vss, sem_laexps bk (Fh k) ck es vss) ->
        spec_clock ck.
    Proof.
      intros ** Sem; apply sem_spec_clock_instant.
      intros; destruct (Sem k) as (?&?& Sem'); specialize (Sem' n); simpl in Sem'.
      inv Sem'; eauto.
    Qed.

    Lemma sem_spec_lexp_instant:
      forall e,
        (forall k n, exists base v, sem_lexp_instant base (restr_hist (Fh k) n) e v) ->
        spec_lexp e.
    Proof.
      intros ** Sem; induction e; auto using spec_lexp.
      - constructor; apply sem_spec_var_instant;
          intros; destruct (Sem k n) as (?&?& Sem'); inv Sem'; eauto.
      - constructor.
        + apply sem_spec_var_instant; intros; destruct (Sem k n) as (?&?& Sem'); inv Sem'; eauto.
        + apply IHe; intros; destruct (Sem k n) as (?&?& Sem'); inv Sem'; eauto.
      - constructor; apply IHe; intros; destruct (Sem k n) as (?&?& Sem'); inv Sem'; eauto.
      - constructor.
        + apply IHe1; intros; destruct (Sem k n) as (?&?& Sem'); inv Sem'; eauto.
        + apply IHe2; intros; destruct (Sem k n) as (?&?& Sem'); inv Sem'; eauto.
    Qed.

    Corollary sem_spec_laexp:
      forall e ck,
        (forall k, exists bk vs, sem_laexp bk (Fh k) ck e vs) ->
        spec_lexp e.
    Proof.
      intros ** Sem.
      apply sem_spec_lexp_instant; intros.
      destruct (Sem k) as (?&?& Sem'); specialize (Sem' n); inv Sem'; eauto.
    Qed.

    Lemma sem_spec_cexp_instant:
      forall e,
        (forall k n, exists base v, sem_cexp_instant base (restr_hist (Fh k) n) e v) ->
        spec_cexp e.
    Proof.
      intros ** Sem; induction e.
      - constructor.
        + apply sem_spec_var_instant; intros; destruct (Sem k n) as (?&?& Sem'); inv Sem'; eauto.
        + apply IHe1; intros; destruct (Sem k n) as (?&?& Sem'); inv Sem'; eauto.
        + apply IHe2; intros; destruct (Sem k n) as (?&?& Sem'); inv Sem'; eauto.
      - constructor.
        + apply sem_spec_lexp_instant; intros; destruct (Sem k n) as (?&?& Sem'); inv Sem'; eauto.
        + apply IHe1; intros; destruct (Sem k n) as (?&?& Sem'); inv Sem'; eauto.
        + apply IHe2; intros; destruct (Sem k n) as (?&?& Sem'); inv Sem'; eauto.
      - constructor; apply sem_spec_lexp_instant; intros; destruct (Sem k n) as (?&?& Sem'); inv Sem'; eauto.
    Qed.

    Corollary sem_spec_caexp:
      forall e ck,
        (forall k, exists bk vs, sem_caexp bk (Fh k) ck e vs) ->
        spec_cexp e.
    Proof.
      intros ** Sem.
      apply sem_spec_cexp_instant; intros.
      destruct (Sem k) as (?&?& Sem'); specialize (Sem' n); inv Sem'; eauto.
    Qed.

    Lemma sem_spec_lexps_instant:
      forall es,
        (forall k n, exists base vs, sem_lexps_instant base (restr_hist (Fh k) n) es vs) ->
        spec_lexps es.
    Proof.
      intros ** Sem; induction es; constructor.
      - apply sem_spec_lexp_instant; intros; destruct (Sem k n) as (?&?& Sem'); inv Sem'; eauto.
      - apply IHes; intros; destruct (Sem k n) as (?&?& Sem'); inv Sem'; eauto.
    Qed.

    Corollary sem_spec_laexps:
      forall es ck,
        (forall k, exists bk vss, sem_laexps bk (Fh k) ck es vss) ->
        spec_lexps es.
    Proof.
      intros ** Sem.
      apply sem_spec_lexps_instant; intros; destruct (Sem k) as (?&?& Sem'); specialize (Sem' n); inv Sem'; eauto.
    Qed.

    Ltac sem_spec H :=
      let k := fresh in
      let H' := fresh in
      match goal with
      | |- spec_var _ => apply sem_spec_var
      | |- spec_vars _ => apply sem_spec_vars
      | _: cexp |- spec_clock _ => eapply sem_spec_clock_caexp
      | _: lexp |- spec_clock _ => eapply sem_spec_clock_laexp
      | _: list lexp |- spec_clock _ => eapply sem_spec_clock_laexps
      | |- spec_cexp _ => eapply sem_spec_caexp
      | |- spec_lexp _ => eapply sem_spec_laexp
      | |- spec_lexps _ => eapply sem_spec_laexps
      end;
      try (intro k; destruct (H k) as (?&?& H'); inv H'; eauto).

    Lemma sem_spec_eq:
      forall P eq,
        (forall k, exists bk M, SemSB.sem_equation P bk (Fh k) M eq) ->
        spec_eq eq.
    Proof.
      intros ** Sem; destruct eq;  constructor (sem_spec Sem).
    Qed.

  End Choices.
  Hint Resolve reset_memories_spec sub_inst_reset_memories_path.

  Inductive reset_regs_instant (n: nat): bool -> SemSB.memories -> Prop :=
    reset_regs_instant_intro:
      forall M b,
        (forall x mvs,
            find_val x M = Some mvs ->
            b = true -> mvs.(SemSB.reset) n = true) ->
        (forall x M',
            sub_inst x M M' ->
            reset_regs_instant n b M') ->
        reset_regs_instant n b M.

  Lemma sub_inst_reset_regs_instant:
    forall bs M x M',
      (forall n, reset_regs_instant n (bs n) M) ->
      sub_inst x M M' ->
      forall n, reset_regs_instant n (bs n) M'.
  Proof.
    intros ** Rst Sub n.
    revert dependent M'; revert x.
    specialize (Rst n); induction Rst as [??? Inst IH].
    constructor.
    - intros; apply Inst in Sub.
      inv Sub; eauto.
    - intros; eapply IH; eauto.
  Qed.

  Lemma reset_regs_instant_spec:
    forall bs M,
      SemSB.reset_regs bs M <->
      forall n, reset_regs_instant n (bs n) M.
  Proof.
    split.
    - induction 1 as [?? Val ? IH]; intro; constructor.
      + intros; eapply Val; eauto.
      + intros; eapply IH; eauto.
    - induction M as [?? IH] using memory_ind'; intros Rst; constructor.
      + intros; specialize (Rst n); inv Rst; eauto.
      + intros ** Sub; pose proof Sub as Sub'.
        unfold sub_inst, find_inst in Sub.
        eapply Env.find_in, in_map with (f := snd) in Sub; simpl in Sub.
        eapply In_Forall in IH; eauto.
        apply IH.
        eapply sub_inst_reset_regs_instant; eauto.
  Qed.

  Corollary reset_regs_instant_spec':
    forall bs M n,
      SemSB.reset_regs bs M ->
      reset_regs_instant n (bs n) M.
  Proof.
    intros ** Rst.
    rewrite reset_regs_instant_spec in Rst; auto.
  Qed.

  Inductive same_skeleton: SemSB.memories -> SemSB.memories -> Prop :=
    same_skeleton_intro:
      forall M M',
        (forall x, find_val x M <> None -> find_val x M' <> None) ->
        (forall x M1,
            find_inst x M = Some M1 ->
            exists M2, find_inst x M' = Some M2
                  /\ same_skeleton M1 M2) ->
        same_skeleton M M'.

  Lemma same_skeleton_sub_inst:
    forall M M' x Mx Mx',
      same_skeleton M M' ->
      sub_inst x M Mx ->
      sub_inst x M' Mx' ->
      same_skeleton Mx Mx'.
  Proof.
    inversion_clear 1 as [??? Inst]; intros ** Sub Sub'.
    apply Inst in Sub as (? & Sub'' & ?).
    rewrite Sub' in Sub''; inv Sub''; auto.
  Qed.

  Lemma reset_memories_path_spec_instant':
    forall r Fm p r' M0 n M',
      same_skeleton M0 M' ->
      path_inst p (Fm (count r n)) = Some M' ->
      reset_regs_instant n r' M' ->
      reset_regs_instant n r' (reset_memories_path Fm r p M0).
  Proof.
    intros ** Same Sub RstSpec.
    inversion_clear Same as [?? FindVal FindInst].

    revert dependent p.
    revert dependent M'.
    induction M0 as [?? IH] using memory_ind'; intros.
    inversion_clear RstSpec as [?? Val Inst].
    constructor.
    - unfold reset_memories_path; intros y mvs Find' Rst; subst.
      rewrite find_val_mmapi in Find'.
      destruct (find_val y (Mnode xvs xms)) eqn: E; inv Find'.
      unfold reset_reset; simpl.
      rewrite Sub.
      destruct (find_val y M') eqn: E'.
      + erewrite Val; eauto 1.
        apply Bool.orb_true_r.
      + contradict E'; eapply FindVal; eauto;
          rewrite E; intro; discriminate.
    - intros ** Find.
      apply sub_inst_reset_memories_path' in Find as (M0' &?& Find); subst.
      unfold sub_inst in Find.
      pose proof Find as Find'.
      unfold sub_inst, find_inst in Find.
      apply Env.find_in, in_map with (f := snd) in Find; simpl in Find.
      eapply In_Forall in IH; eauto.
      assert (exists M'', find_inst x M' = Some M''
                     /\ same_skeleton M0' M'') as (M'' &?& Same)
          by (apply FindInst in Find' as (?&?&?); eauto).
      inv Same.
      eapply IH; eauto.
      eapply path_inst_last; eauto.
  Qed.

  Corollary reset_memories_path_sub_spec_instant':
    forall r Fm x r' M0 n M',
      same_skeleton M0 M' ->
      sub_inst x (Fm (count r n)) M' ->
      reset_regs_instant n r' M' ->
      reset_regs_instant n r' (reset_memories_path Fm r [x] M0).
  Proof.
    intros ** Same Sub RstSpec.
    eapply reset_memories_path_spec_instant'; eauto.
    simpl; rewrite Sub; auto.
  Qed.

  Lemma sem_var_instant_bl_vars:
    forall xs xs' xss Fh r n,
      (forall x k n,
          In x xs' ->
          exists v, PM.find x (restr_hist (Fh k) n) = Some v) ->
      incl xs xs' ->
      sem_vars (Fh (count r n)) xs (mask (all_absent (xss 0)) (count r n) r xss) ->
      Forall2 (sem_var_instant (restr_hist (reset_history Fh r (Fh 0)) n)) xs (xss n).
  Proof.
    intros ** SameDomFh Incl Sem.
    unfold mask in Sem; specialize (Sem n); simpl in *.
    rewrite <-EqNat.beq_nat_refl in Sem.
    induction Sem as [|x ??? Sem]; constructor; auto.
    - clear IHSem.
      inversion_clear Sem as [?? Find]; constructor.
      assert (exists v, PM.find x (restr_hist (Fh 0) n) = Some v)
        as (? & Find') by (apply SameDomFh, Incl; constructor; auto).
      unfold restr_hist, reset_history, PM.map in *.
      repeat rewrite PM.gmapi in *; rewrite option_map_map.
      destruct (PM.find x (Fh (count r n))); try discriminate.
      destruct (PM.find x (Fh 0)); try discriminate; auto.
    - apply IHSem; intros x' **.
      apply Incl; right; auto.
  Qed.

  Lemma sem_laexps_interp_mask:
    forall xss r Fh ck es k bk' ess,
      let H := reset_history Fh r (Fh 0) in
      let bk := clock_of' xss in
      spec_clock Fh ck ->
      spec_lexps Fh es ->
      (forall n, 0 < length (xss n)) ->
      clock_of (mask (all_absent (xss 0)) k r xss) bk' ->
      sem_laexps bk' (Fh k) ck es ess ->
      ess ≈ mask (all_absent (interp_laexps bk H ck es 0)) k r (interp_laexps bk H ck es).
  Proof.
    intros ** Length Clock Exps n.
    specialize (Exps n); simpl in Exps.
    destruct (EqNat.beq_nat k (count r n)) eqn: E.
    - apply EqNat.beq_nat_true in E; subst k.
      rewrite mask_transparent; auto.
      eapply interp_laexps_instant_sound, sem_laexps_instant_reset; eauto.
    - apply EqNat.beq_nat_false in E.
      specialize (Clock n).
      rewrite mask_opaque; rewrite mask_opaque in Clock; auto.
      inversion_clear Exps as [?????? SemCk|??? Eq].
      + assert (bk' n = false) as Hbk'.
        { apply Bool.not_true_is_false; intro Eq.
          apply Clock in Eq.
          specialize (Length 0); induction (xss 0); simpl in *; inv Eq; auto; omega.
        }
        rewrite Hbk' in *.
        contradict SemCk; apply not_subrate_clock.
      + rewrite Eq.
        unfold interp_laexps, lift, interp_laexps_instant.
        destruct (forallb (fun v : value => v ==b absent) (interp_lexps_instant (bk 0) (restr_hist H 0) es)
                          && negb (interp_clock_instant (bk 0) (restr_hist H 0) ck)
                  || forallb (fun v : value => v <>b absent) (interp_lexps_instant (bk 0) (restr_hist H 0) es)
                            && interp_clock_instant (bk 0) (restr_hist H 0) ck);
          unfold interp_lexps_instant; rewrite all_absent_map; auto.
        unfold all_absent at 3; rewrite all_absent_map; auto.
  Qed.

  Lemma sem_vars_interp_mask:
    forall r Fh xs k ess oss oss0,
      let H := reset_history Fh r (Fh 0) in
      sem_vars (Fh k) xs oss ->
      sem_vars (Fh 0) xs oss0 ->
      (forall n, absent_list (ess n) <-> absent_list (oss n)) ->
      (forall n, k <> count r n -> absent_list (oss n)) ->
      oss ≈ mask (all_absent (interp_vars H xs 0)) k r (interp_vars H xs).
  Proof.
    intros ** Vars Vars0 Same Abs n.
    specialize (Vars n); specialize (Vars0 n);
      specialize (Same n); (* specialize (Eess n) *) simpl in *.
    unfold mask in *.
    destruct (EqNat.beq_nat k (count r n)) eqn: E; simpl.
    - clear Same.
      revert Vars0; generalize (oss0 n).
      induction Vars as [|???? Var]; intros; inversion_clear Vars0 as [|???? Var0]; simpl; auto.
      f_equal; eauto.
      inversion_clear Var0 as [?? Find0]; inversion_clear Var as [?? Find].
      unfold interp_var_instant.
      subst H; unfold reset_history; unfold restr_hist, PM.map in *.
      rewrite 2 PM.gmapi; simpl.
      rewrite PM.gmapi in Find0.
      destruct (PM.find x (Fh 0)); inv Find0; simpl.
      rewrite PM.gmapi in Find.
      apply EqNat.beq_nat_true in E; subst k.
      destruct (PM.find x (Fh (count r n))); inv Find; auto.
    - specialize (Abs n).
      assert (absent_list (oss n)) as Abs'
          by (apply Abs, EqNat.beq_nat_false; auto).
      apply interp_vars_instant_sound in Vars as ->.
      clear - Abs'; induction xs; simpl; auto.
      inv Abs'; f_equal; auto.
  Qed.

  Lemma sub_inst_reset_memories:
    forall F F' r x,
      (forall k, sub_inst x (F k) (F' k)) ->
      sub_inst x (reset_memories F r (F 0)) (reset_memories F' r (F' 0)).
  Proof.
    intros ** Sub.
    pose proof (Sub 0) as Sub0.
    eapply (sub_inst_reset_memories_path F r _ []) in Sub0.
    unfold sub_inst, reset_memories.
    rewrite Sub0; f_equal; simpl.
    clear Sub0.
    generalize (@nil ident).
    induction (F' 0) as [?? IH] using memory_ind'; intros.
    unfold reset_memories_path.
    simpl. f_equal.
    - f_equal.
      extensionality y; extensionality mvs.
      f_equal.
      + extensionality n; unfold reset_content; simpl.
        now rewrite Sub.
      + extensionality n; unfold reset_reset; simpl.
        now rewrite Sub.
    - induction xms as [|(i & M')]; simpl; auto.
      inversion_clear IH as [|?? Eq]; f_equal; auto.
      f_equal.
      unfold reset_memories_path in Eq; auto.
  Qed.

  (* Lemma foo: *)
  (*   forall eqs M M', *)
  (*     SemSB.well_structured_memories eqs M -> *)
  (*     SemSB.well_structured_memories eqs M' -> *)
  (*     (* SemSB.sem_equation P bk H M e -> *) *)
  (*     (* SemSB.sem_equation P bk H M' e -> *) *)
  (*     same_skeleton M M'. *)
  (* Proof. *)
  (*   intros ** WS WS'. *)
  (*   revert dependent M'. *)
  (*   induction M using memory_ind'; intros. *)
  (*   constructor. *)
  (*   - intros x Find. *)
  (*     now apply WS, WS' in Find. *)
  (*   - intros ** Find'. *)
  (*     assert (find_inst x (Mnode xvs xms) <> None) as Find by (rewrite not_None_is_Some; eauto). *)
  (*     apply WS, WS' in Find. *)
  (*     apply not_None_is_Some in Find as (). *)
  (*     eexists; split; eauto. *)
  (*     unfold find_inst in Find'; *)
  (*       apply Env.find_in, in_map with (f := snd) in Find'; simpl in Find'. *)
  (*     eapply In_Forall in H; eauto. *)
  (*     apply H. *)
  (*     SearchAbout Forall In. *)
  (*     eauto. *)
  Definition gather_eq (acc: Env.t ident) (eq: SynSB.equation): Env.t ident :=
    match eq with
    | SynSB.EqDef _ _ _
    | SynSB.EqReset _ _ _ _
    | SynSB.EqFby _ _ _ _ => acc
    | SynSB.EqCall _ _ f i _ => Env.add i f acc
    end.

  Definition gather (eqs: list SynSB.equation) : Env.t ident :=
    fold_left gather_eq eqs [].

  Arguments Env.add: simpl never.

  Lemma fold_left_gather_eq_find:
    forall eqs e e' x,
      Env.find x e = Env.find x e' ->
      Env.find x (fold_left gather_eq eqs e) = Env.find x (fold_left gather_eq eqs e').
  Proof.
    Arguments Env.add: simpl never.
    unfold gather; induction eqs as [|eq]; simpl; auto; intros ** E.
    destruct eq; simpl; auto.
    apply IHeqs.
    destruct (ident_eqb x i1) eqn: Eq;
      [apply ident_eqb_eq in Eq; subst|apply ident_eqb_neq in Eq].
    - rewrite 2 Env.gss; auto.
    - rewrite 2 Env.gso; auto.
  Qed.

  Corollary gather_find:
    forall eqs e x,
      Env.find x e = None ->
      Env.find x (fold_left gather_eq eqs e) = Env.find x (gather eqs).
  Proof.
    intros ** E; apply fold_left_gather_eq_find.
    rewrite E; reflexivity.
  Qed.

  Lemma fold_left_gather_eq_find_not_none:
     forall eqs e x,
      Env.find x (fold_left gather_eq eqs e) <> None <->
      Env.find x (gather eqs) <> None \/ Env.find x e <> None.
  Proof.
    unfold gather; induction eqs as [|eq]; simpl.
    - split; intros E; auto.
      destruct E; auto; discriminate.
    - split; [intro E|intros [E|]]; rewrite IHeqs; try apply IHeqs in E as [|E]; auto.
      + destruct eq; simpl gather_eq in *; auto.
        destruct (ident_eqb x i1) eqn: Eq;
          [apply ident_eqb_eq in Eq; subst|apply ident_eqb_neq in Eq].
        * rewrite Env.gss in *; auto.
        * rewrite Env.gso in E; auto.
      + destruct eq; simpl gather_eq in *; try now contradict E.
        destruct (ident_eqb x i1) eqn: Eq;
          [apply ident_eqb_eq in Eq; subst|apply ident_eqb_neq in Eq].
        * rewrite Env.gss in *; auto.
        * rewrite Env.gso in E; auto; discriminate.
      + destruct eq; simpl gather_eq in *; auto.
        destruct (ident_eqb x i1) eqn: Eq;
          [apply ident_eqb_eq in Eq; subst|apply ident_eqb_neq in Eq].
        * rewrite Env.gss; right; discriminate.
        * rewrite Env.gso; auto.
  Qed.

  Lemma fold_left_gather_eq_find_some:
     forall eqs e x y,
      Env.find x (fold_left gather_eq eqs e) = Some y <->
      Env.find x (gather eqs) = Some y \/ (Env.find x e = Some y /\ Env.find x (gather eqs) = None).
  Proof.
    unfold gather; induction eqs as [|eq]; simpl.
    - split; intros E; auto.
      destruct E as [|()]; auto; discriminate.
    - split; [intro E|intros ** [E|(?&E)]]; rewrite IHeqs; try apply IHeqs in E as [|(E & E')]; auto.
      + destruct eq; simpl gather_eq in *; auto.
        destruct (ident_eqb x i1) eqn: Eq;
          [apply ident_eqb_eq in Eq; subst|apply ident_eqb_neq in Eq].
        * rewrite Env.gss in *; auto.
        * rewrite Env.gso in E; auto.
          right; split; auto.
          rewrite fold_left_gather_eq_find with (e' := []); auto.
          apply Env.gso; auto.
      + destruct eq; simpl gather_eq in *; try now contradict E.
        destruct (ident_eqb x i1) eqn: Eq;
          [apply ident_eqb_eq in Eq; subst|apply ident_eqb_neq in Eq].
        * rewrite Env.gss in *; auto.
        * rewrite Env.gso in E; auto; discriminate.
      + destruct eq; simpl gather_eq in *; auto.
        destruct (ident_eqb x i1) eqn: Eq;
          [apply ident_eqb_eq in Eq; subst|apply ident_eqb_neq in Eq].
        * contradict E.
          rewrite fold_left_gather_eq_find_not_none.
          right.
          rewrite Env.gss; discriminate.
        * rewrite Env.gso; auto.
          right; split; auto.
          erewrite fold_left_gather_eq_find; eauto.
          rewrite Env.gso; auto.
  Qed.

  Lemma fold_left_gather_eq_find_none:
     forall eqs e x,
      Env.find x (fold_left gather_eq eqs e) = None <->
      Env.find x (gather eqs) = None /\ Env.find x e = None.
  Proof.
    unfold gather; induction eqs as [|eq]; simpl.
    - split; intros E; auto.
      destruct E; auto.
    - split; [intro E|intros ** (E&?)];
        apply IHeqs in E as (E&E'); rewrite IHeqs;
          destruct eq; simpl gather_eq in *; auto.
      + split; [split|]; auto.
        *{ destruct (ident_eqb x i1) eqn: Eq;
            [apply ident_eqb_eq in Eq; subst|apply ident_eqb_neq in Eq].
           - rewrite Env.gss in *; auto.
           - rewrite Env.gso; auto.
         }
        *{ destruct (ident_eqb x i1) eqn: Eq;
            [apply ident_eqb_eq in Eq; subst|apply ident_eqb_neq in Eq].
           - rewrite Env.gss in *; discriminate.
           - rewrite Env.gso in E'; auto.
         }
      + split; auto.
        destruct (ident_eqb x i1) eqn: Eq;
          [apply ident_eqb_eq in Eq; subst|apply ident_eqb_neq in Eq].
        * rewrite Env.gss in *; discriminate.
        * rewrite Env.gso in *; auto.
  Qed.

  Lemma gather_find':
    forall eqs e x,
      Env.find x (gather eqs) = None ->
      Env.find x (fold_left gather_eq eqs e) = Env.find x e.
  Proof.
    intros ** E.
    destruct (Env.find x e) eqn: E'.
    - rewrite fold_left_gather_eq_find_some; auto.
    - rewrite fold_left_gather_eq_find_none; auto.
  Qed.

  Lemma not_inst_in_gather_none:
    forall eqs x,
      ~ inst_in_eqs x eqs ->
      Env.find x (gather eqs) = None.
  Proof.
    unfold gather; induction eqs as [|eq]; simpl; intros ** E; auto.
    destruct eq; simpl gather_eq; try (now apply IHeqs; intro; apply E; right).
      destruct (ident_eqb x i1) eqn: Eq;
        [apply ident_eqb_eq in Eq; subst|apply ident_eqb_neq in Eq].
    - exfalso; apply E.
      left; constructor.
    - rewrite fold_left_gather_eq_find_none; split.
      + apply IHeqs; intro.
        apply E; right; auto.
      + rewrite Env.gso; auto.
  Qed.

  Lemma Welldef_gloabl_Is_well_sch:
    forall G f n,
      Welldef_global G ->
      find_node f G = Some n ->
      Is_well_sch (memories n.(n_eqs)) (map fst (n_in n)) n.(n_eqs).
  Proof.
    induction G as [|node]; intros ** WD Find.
    - inv Find.
    - inv WD.
      simpl in Find.
      destruct (ident_eqb node.(n_name) f); eauto.
      inversion Find; subst n; auto .
  Qed.

  Lemma sub_inst_translate_sem_block:
    forall G f bl P' M xss oss x M',
      Welldef_global G ->
      SemSB.sem_block (translate G) f M xss oss ->
      SynSB.find_block f (translate G) = Some (bl, P') ->
      sub_inst x M M' ->
      exists g xss' oss',
        SemSB.sem_block (translate G) g M' xss' oss'
        /\ Env.find x (gather bl.(SynSB.b_eqs)) = Some g.
  Proof.
    intros ** WD Sem Find' Sub.
    inversion_clear Sem as [????????? Find ????? Eqs WS].
    rewrite Find in Find'; inv Find'.
    apply find_block_translate in Find as (n & Find &?); subst; simpl in *.
    assert (find_inst x M <> None) as E by (rewrite not_None_is_Some; eauto).
    apply WS in E.
    unfold SemSB.insts in E.
    unfold translate_eqns, concatMap in *.
    assert (compat_eqs n.(n_eqs)) as Compat.
    { eapply Welldef_gloabl_Is_well_sch in WD; eauto.
      eapply Is_well_sch_compat in WD; eauto.
      eapply sem_equations_well_formed_app; eauto.
    }
    clear WD WS.
    induction (n_eqs n) as [|eq].
    - contradict E; apply not_In_empty.
    - inversion_clear Compat as [|??? Compat_eq].
      destruct eq; try destruct o as [()|]; unfold gather; simpl in *;
        inversion_clear Eqs as [|?? Heq Heqs];
        inv Compat_eq; auto.
      + set (y := hd default i) in *.
        inversion_clear Heqs as [|?? Heq''].
        inversion_clear Heq'' as [| | |???????????? Sub'].
        destruct (ident_eqb x y) eqn: Eq;
          [apply ident_eqb_eq in Eq; subst|apply ident_eqb_neq in Eq].
        *{ unfold sub_inst in Sub'; rewrite Sub in Sub'; inv Sub'.
           do 3 eexists; split; eauto.
           rewrite gather_find'.
           - apply Env.gss.
           - apply not_inst_in_gather_none; auto.
         }
        *{ rewrite gather_find.
           - apply IHl; auto.
             apply SemSB.In_fold_left_inst_eq in E as [|E]; auto.
             rewrite 2 PSE.MP.Dec.F.add_neq_iff in E; auto.
             contradict E; apply not_In_empty.
           - rewrite Env.gso; auto.
         }
      + set (y := hd default i) in *.
        inversion_clear Heq as [| | |???????????? Sub'].
        destruct (ident_eqb x y) eqn: Eq;
          [apply ident_eqb_eq in Eq; subst|apply ident_eqb_neq in Eq].
        *{ unfold sub_inst in Sub'; rewrite Sub in Sub'; inv Sub'.
           do 3 eexists; split; eauto.
           rewrite gather_find'.
           - apply Env.gss.
           - apply not_inst_in_gather_none; auto.
         }
        *{ rewrite gather_find.
           - apply IHl; auto.
             apply SemSB.In_fold_left_inst_eq in E as [|E]; auto.
             rewrite PSE.MP.Dec.F.add_neq_iff in E; auto.
             contradict E; apply not_In_empty.
           - rewrite Env.gso; auto.
         }
  Qed.

  Lemma sem_block_same_skeleton:
    forall G M M' f xss oss xss' oss',
      (* Ordered_nodes G -> *)
      Welldef_global G ->
      SemSB.sem_block (translate G) f M xss oss ->
      SemSB.sem_block (translate G) f M' xss' oss' ->
      same_skeleton M M'.
  Proof.
    induction M as [?? IH] using memory_ind'.
    intros ** Sem Sem'; pose proof Sem as Sem1; pose proof Sem' as Sem2;
      inversion_clear Sem as [????????? Find ????? Eqs WS];
      inversion_clear Sem' as [????????? Find' ????? Eqs' WS'].
    rewrite Find' in Find; inv Find.
    constructor.
    - intros x E.
      apply WS'.
      apply WS in E; auto.
    - intros ** E.
      pose proof E as E1.
      assert (find_inst x (Mnode xvs xms) <> None) as E' by (rewrite not_None_is_Some; eauto).
      apply WS, WS' in E'.
      apply not_None_is_Some in E' as ().
      eexists; split; eauto.
      unfold find_inst in E.
      apply Env.find_in, in_map with (f := snd) in E; simpl in E.
      eapply In_Forall in IH; eauto.
      eapply sub_inst_translate_sem_block in Sem1 as (?&?&?&?& Find1); eauto.
      eapply sub_inst_translate_sem_block in Sem2 as (?&?&?&?& Find2); eauto.
      rewrite Find1 in Find2; inv Find2.
      eauto.
  Qed.

  Lemma well_structured_reset_memories:
    forall Fm r M0 eqs,
    SemSB.well_structured_memories eqs M0 ->
    SemSB.well_structured_memories eqs (reset_memories Fm r M0).
  Proof.
    inversion_clear 1 as [Vals Insts].
    constructor; intro; unfold reset_memories, reset_memories_path.
    - rewrite find_val_mmapi, <-Vals.
      destruct (find_val x M0); simpl; split; auto; intros ** ?; discriminate.
    - rewrite find_inst_mmapi, <-Insts.
      destruct (find_inst x M0); simpl; split; auto; intros ** ?; discriminate.
  Qed.

  Ltac interp_sound n :=
    repeat match goal with
           | H: sem_var ?H' ?x ?vs |- _ =>
             specialize (H n); apply sem_var_instant_reset in H
           | H: sem_vars ?H' ?xs ?vss |- _ =>
             specialize (H n); apply sem_vars_instant_reset in H
           | H: sem_caexp ?bk ?H' ?c ?e ?vs |- _ =>
             specialize (H n); simpl in H; eapply sem_caexp_instant_reset in H; eauto
           | H: sem_laexp ?bk ?H' ?c ?e ?vs |- _ =>
             specialize (H n); simpl in H; eapply sem_laexp_instant_reset in H; eauto
           | H: sem_laexps ?bk ?H' ?c ?es ?vss |- _ =>
             specialize (H n); simpl in H; eapply sem_laexps_instant_reset in H; eauto
           end;
    unfold interp_var, interp_vars, interp_laexp, interp_laexps, interp_caexp, lift, lift';
    try erewrite <-interp_caexp_instant_sound;
    try erewrite <-interp_laexp_instant_sound;
    try erewrite <-interp_laexps_instant_sound;
    try erewrite <-interp_var_instant_sound;
    try erewrite <-interp_vars_instant_sound;
    eauto.

  (* Require Import Coq.Logic.ClassicalChoice. *)
  (* Require Import Coq.Logic.ConstructiveEpsilon. *)
  (* Require Import Coq.Logic.Epsilon. *)
  Require Import Coq.Logic.IndefiniteDescription.

  Theorem slices_sem_block:
    forall G f r xss oss Fm,
      Welldef_global G ->
      (forall k,
          SemSB.sem_block (translate G) f (Fm k)
                          (mask (all_absent (xss 0)) k r xss)
                          (mask (all_absent (oss 0)) k r oss)) ->
      SemSB.sem_block (translate G) f (reset_memories Fm r (Fm 0)) xss oss.
  Proof.
    intros ** WD Sem.
    revert dependent f; revert xss oss r Fm.
    induction G as [|node]; intros.
    specialize (Sem 0); inv Sem;
      match goal with Hf: SynSB.find_block _ _ = _ |- _ => inversion Hf end.

    pose proof (Welldef_global_Ordered_nodes _ WD) as Ord.
    pose proof (Welldef_global_cons _ _ WD) as WD'.

    pose proof Ord as Ord'.
    inversion_clear Ord as [|?? Ord'' Hnneqs Hnn].

    assert (exists bl P', SynSB.find_block f (translate (node :: G)) = Some (bl, P'))
      as (bl & P' & Find)
        by (specialize (Sem 0); inv Sem; eauto).

    assert (forall k k', same_skeleton (Fm k) (Fm k')) as SameSkeleton
        by (intros; pose proof (Sem k) as Sk; specialize (Sem k');
            eapply sem_block_same_skeleton with (1 := WD); eauto).

    assert (exists F, forall k, exists bk,
                   sem_vars (F k) (map fst (SynSB.b_in bl)) (mask (all_absent (xss 0)) k r xss)
                   /\ sem_vars (F k) (map fst (SynSB.b_out bl)) (mask (all_absent (oss 0)) k r oss)
                   /\ Forall (SemSB.sem_equation (translate (node :: G)) bk (F k) (Fm k)) (SynSB.b_eqs bl)
                   /\ clock_of (mask (all_absent (xss 0)) k r xss) bk
                   /\ SemSB.well_structured_memories (SynSB.b_eqs bl) (Fm k))
      as (Fh & Spec).
    { assert (forall k, exists H bk,
                   sem_vars H (map fst (SynSB.b_in bl)) (mask (all_absent (xss 0)) k r xss)
                   /\ sem_vars H (map fst (SynSB.b_out bl)) (mask (all_absent (oss 0)) k r oss)
                   /\ Forall (SemSB.sem_equation (translate (node :: G)) bk H (Fm k)) (SynSB.b_eqs bl)
                   /\ clock_of (mask (all_absent (xss 0)) k r xss) bk
                   /\ SemSB.well_structured_memories (SynSB.b_eqs bl) (Fm k))
        as Spec.
      { intro; specialize (Sem k); inv Sem.
        match goal with
          H: SynSB.find_block _ _ = _ |- _ => rewrite Find in H; inv H end.
        eauto 7.
      }
      now apply functional_choice in Spec.
    }

    assert (forall x k n,
               In x (map fst (SynSB.b_in bl) ++ map fst (SynSB.b_out bl)) ->
               exists v, PM.find x (restr_hist (Fh k) n) = Some v)
      as SameDomFh.
    { clear - Spec.
      intros ** Hin.
      apply in_app in Hin as [Hin|Hin].
      - destruct (Spec k) as (?& In & ?).
        specialize (In n); simpl in *.
        eapply Forall2_In_l in In as (?& Sem); eauto.
        inv Sem; eauto.
      - destruct (Spec k) as (?&?& Out &?).
        specialize (Out n); simpl in *.
        eapply Forall2_In_l in Out as (?& Sem); eauto.
        inv Sem; eauto.
    }

    eapply SemSB.SBlock with (H := reset_history Fh r (Fh 0)); eauto.
    - apply clock_of_equiv.
    - intro; destruct (Spec (count r n)) as (?& In & ?).
      eapply sem_var_instant_bl_vars; eauto.
      intros ? ?; rewrite in_app; auto.
    - intro; destruct (Spec (count r n)) as (?&?& Out &?).
      eapply sem_var_instant_bl_vars; eauto.
      intros ? ?; rewrite in_app; auto.
    - intro; specialize (Sem (count r n)); inversion_clear Sem as [???????????? Same].
      specialize (Same n); rewrite mask_transparent in Same; auto.
    - intro; specialize (Sem (count r n)); inversion_clear Sem as [????????????? Same].
      specialize (Same n); rewrite mask_transparent in Same; auto.
    - intro; specialize (Sem (count r n)); inversion_clear Sem as [?????????????? AbsAbs].
      specialize (AbsAbs n); rewrite 2 mask_transparent in AbsAbs; auto.
    - assert (forall n, 0 < length (xss n)) as Length.
      { clear - Sem.
        pose proof Sem as Sem'.
        intro; specialize (Sem 0); inversion_clear Sem as [?????????? Vars];
          specialize (Vars n); simpl in Vars.
        apply Forall2_length in Vars.
        rewrite mask_length in Vars.
        - rewrite <-Vars, map_length; apply SynSB.b_ingt0.
        - eapply wf_streams_mask.
          intro k'; specialize (Sem' k');
            apply SemSB.sem_block_wf in Sem' as (); eauto.
      }

      assert (~ is_block_in (n_name node) (SynSB.b_eqs bl)) as NotIn.
      { pose proof Find as Find'. simpl in Find.
        destruct (ident_eqb (n_name node) f) eqn: E.
        - assert (n_name node = SynSB.b_name bl) as -> by (inv Find; auto).
          eapply find_block_not_is_block_in with (1 := Ord'); eauto.
        - eapply find_block_later_not_is_block_in; eauto.
      }

      assert (forall k, exists bk,
                   sem_vars (Fh k) (map fst (SynSB.b_in bl)) (mask (all_absent (xss 0)) k r xss)
                   /\ sem_vars (Fh k) (map fst (SynSB.b_out bl)) (mask (all_absent (oss 0)) k r oss)
                   /\ Forall (SemSB.sem_equation (translate (node :: G)) bk (Fh k) (Fm k)) (SynSB.b_eqs bl)
                   /\ clock_of (mask (all_absent (xss 0)) k r xss) bk) as Spec'
          by (intro; destruct (Spec k) as (?&?&?&?&?&?); eauto).
      clear Spec; rename Spec' into Spec.

      induction (SynSB.b_eqs bl) as [|eq ? IHeqs]; constructor; auto.
      + clear IHeqs.
        assert (forall k, exists bk, SemSB.sem_equation (translate (node :: G)) bk (Fh k) (Fm k) eq
                           /\ clock_of (mask (all_absent (xss 0)) k r xss) bk)
          as Spec'
            by (intros; destruct (Spec k) as (?&?&?& Heq &?); inv Heq; eauto).
        clear Spec.
        set (bk := clock_of' xss).
        set (H := reset_history Fh r (Fh 0)).

        assert (spec_eq Fh eq) as SpecEq
            by (eapply sem_spec_eq; intros; destruct (Spec' k) as (?&?&?); eauto).

        destruct eq; inv SpecEq.

        * apply SemSB.SEqDef with (xs := interp_caexp bk H c c0);
            intro; destruct (Spec' (count r n)) as (?& Heq &?); inv Heq;
              interp_sound n.

        *{ apply SemSB.SEqFby with (xs := interp_var H i) (ls := interp_laexp bk H c l0);
             try (intro; destruct (Spec' (count r n)) as (?& Heq &?); inv Heq; interp_sound n).
           assert (exists F, forall k, exists bk xs ls,
                          sem_var (Fh k) i xs
                          /\ sem_laexp bk (Fh k) c l0 ls
                          /\ find_val i (Fm k) = Some (F k)
                          /\ (F k).(SemSB.content) 0 = sem_const c0
                          /\ (forall n,
                                match ls n with
                                | absent =>
                                  (F k).(SemSB.content) (S n) =
                                  (if (F k).(SemSB.reset) (S n) then sem_const c0 else (F k).(SemSB.content) n)
                                  /\ xs n = absent
                                | present v' =>
                                  (F k).(SemSB.content) (S n) =
                                  (if (F k).(SemSB.reset) (S n) then sem_const c0 else v')
                                  /\ xs n = present ((F k).(SemSB.content) n)
                                end)
                          /\ clock_of (mask (all_absent (xss 0)) k r xss) bk)
             as (Fmvs & Spec).
           { assert (forall k, exists mvs bk xs ls,
                          sem_var (Fh k) i xs
                          /\ sem_laexp bk (Fh k) c l0 ls
                          /\ find_val i (Fm k) = Some mvs
                          /\ mvs.(SemSB.content) 0 = sem_const c0
                          /\ (forall n,
                                match ls n with
                                | absent =>
                                  mvs.(SemSB.content) (S n) =
                                  (if mvs.(SemSB.reset) (S n) then sem_const c0 else mvs.(SemSB.content) n)
                                  /\ xs n = absent
                                | present v' =>
                                  mvs.(SemSB.content) (S n) =
                                  (if mvs.(SemSB.reset) (S n) then sem_const c0 else v')
                                  /\ xs n = present (mvs.(SemSB.content) n)
                                end)
                          /\ clock_of (mask (all_absent (xss 0)) k r xss) bk) as Spec.
             { intro; destruct (Spec' k) as (?& Heq &?); inversion_clear Heq as [|??????????? Fby| |]; inv Fby.
               eauto 10.
             }
             now apply functional_choice in Spec.
           }

           apply SemSB.mfby_intro with (mvs := reset_mvalues Fmvs r).
           - apply find_val_reset_memories.
             intro; destruct (Spec k) as (?&?&?&?); intuition.
           - simpl; destruct (r 0).
             + destruct (Spec 1) as (?&?&?&?); intuition.
             + destruct (Spec 0) as (?&?&?&?); intuition.
           - intro; destruct (Spec (count r n)) as (?&?&?&?&?&?&?& Heq &?).
             pose proof (reset_mvalues_spec _ _ _ _ _ _ _ _ _ Length Spec (S n)) as SpecMv.
             clear Spec.
             interp_sound n.
             specialize (Heq n).
             destruct (r (S n)) eqn: E;
               [rewrite SpecMv; auto|];
               simpl; rewrite E; simpl; auto.
             destruct (x1 n); intuition.
         }

        *{ assert (exists M0, sub_inst i0 (Fm 0) M0) as (M0 & Find0)
               by (destruct (Spec' 0) as (?& Heq & ?); inv Heq; eauto).
           apply SemSB.SEqReset with (rs := interp_var H i1) (M' := reset_memories_path Fm r [i0] M0).
           - intro; destruct (Spec' (count r n)) as (?& Heq &?); inv Heq; interp_sound n.
           - now apply sub_inst_reset_memories_path.
           - rewrite reset_regs_instant_spec.
             intro; destruct (Spec' (count r n)) as (?& Heq &?); inversion_clear Heq as [| |????????? Var|].
             eapply reset_memories_path_sub_spec_instant'; eauto.
             + eapply same_skeleton_sub_inst; eauto.
             + replace (reset_of (interp_var H i1) n) with (reset_of_value (interp_var H i1 n)); auto.
               interp_sound n.
               replace (reset_of_value (rs n)) with (reset_of rs n); auto.
               apply reset_regs_instant_spec'; auto.
         }

        *{ assert (exists F, (forall k,
                            SemSB.sem_block (translate G) i0
                                            (F k)
                                            (mask (all_absent (interp_laexps bk H c l0 0)) k r (interp_laexps bk H c l0))
                                            (mask (all_absent (interp_vars H i 0)) k r (interp_vars H i)))
                        /\ forall k, sub_inst i1 (Fm k) (F k)) as (F & Spec & Sub).
           { assert (forall k, exists M bk ess oss,
                          sem_laexps bk (Fh k) c l0 ess
                          /\ sub_inst i1 (Fm k) M
                          /\ SemSB.sem_block (translate (node :: G)) i0 M ess oss
                          /\ sem_vars (Fh k) i oss
                          /\ clock_of (mask (all_absent (xss 0)) k r xss) bk) as Spec.
             { intro; destruct (Spec' k) as (?& Heq & Clock);
                 inversion_clear Heq as [| | |???? M' ?????? Exps ? Block Vars]; eauto 9.
             }
             apply functional_choice in Spec as (F & Spec).
             exists F; split; intro; destruct (Spec k) as (?&?&?& Exps & ? & Block & Vars & ?); auto.
             erewrite sem_laexps_interp_mask in Block; eauto.
             pose proof Block as Block'; inversion_clear Block' as [?????????????? Same].
             destruct (Spec' 0) as (?& Heq &?); inv Heq.
             erewrite sem_vars_interp_mask with (1 := Vars) (r := r) in Block; eauto.
             - eapply sem_block_cons; eauto.
               intro E; apply NotIn; rewrite E; do 2 constructor.
             - intros ** E; apply Same.
               rewrite mask_opaque; auto.
               apply all_absent_spec.
           }
           eapply SemSB.SEqCall with (M' := reset_memories F r (F 0))
                                     (ess := interp_laexps bk H c l0)
                                     (oss := interp_vars H i).
           - intro; destruct (Spec' (count r n)) as (?& Heq &?); inv Heq; interp_sound n.
           - now apply sub_inst_reset_memories.
           - apply sem_block_cons2; auto.
           - intro; destruct (Spec' (count r n)) as (?& Heq &?); inv Heq; interp_sound n.
         }

      + apply IHeqs.
        * intro E; apply NotIn; right; auto.
        * intro; destruct (Spec k) as (?&?&?& Heqs &?); inv Heqs; eauto.

    - destruct (Spec 0) as (?&?&?&?&?&?).
      apply well_structured_reset_memories; auto.
  Qed.

  Theorem reset_correctness:
    forall G f r xss oss,
      Welldef_global G ->
      (forall f xss oss,
          sem_node G f xss oss ->
          exists M, SemSB.sem_block (translate G) f M xss oss) ->
      sem_reset G f r xss oss ->
      exists M, SemSB.sem_block (translate G) f M xss oss
           /\ SemSB.reset_regs r M.
  Proof.
    intros ** Ord IHNode Sem.
    inversion_clear Sem as [???? Sem'].

    assert (exists F, forall k, SemSB.sem_block (translate G) f (F k)
                                      (mask (all_absent (xss 0)) k r xss)
                                      (mask (all_absent (oss 0)) k r oss))
      as (Fm & Sem).
    { assert (forall k, exists M', SemSB.sem_block (translate G) f M'
                                         (mask (all_absent (xss 0)) k r xss)
                                         (mask (all_absent (oss 0)) k r oss)) as SBsem
          by (intro; specialize (Sem' k); apply IHNode in Sem'; auto).

      (** Infinite Description  *)
      now apply functional_choice in SBsem.

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
    apply slices_sem_block in Sem; eauto.
  Qed.

  Theorem correctness:
    forall G f xss oss,
      Welldef_global G ->
      sem_node G f xss oss ->
      exists M, SemSB.sem_block (translate G) f M xss oss.
  Proof.
    induction G as [|node].
    inversion 2;
      match goal with Hf: find_node _ [] = _ |- _ => inversion Hf end.
    intros ** WD Hsem.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [??????? Hfind ????? Heqs].
    pose proof (Welldef_global_Ordered_nodes _ WD) as Hord.
    pose proof (Welldef_global_cons _ _ WD) as WD'.
    pose proof (find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    simpl in Hfind.
    destruct (ident_eqb node.(n_name) f) eqn:Hnf.
    - assert (Hord':=Hord).
      inversion_clear Hord as [|? ? Hord'' Hnneqs Hnn].
      inv Hfind.
      eapply Forall_sem_equation_global_tl in Heqs; eauto.

      assert (forall f xss oss,
                 sem_node G f xss oss ->
                 exists M, SemSB.sem_block (translate G) f M xss oss)
        as IHG' by auto.

      assert (forall f r xss oss,
                 sem_reset G f r xss oss ->
                 exists M, SemSB.sem_block (translate G) f M xss oss
                      /\ SemSB.reset_regs r M)
        by (intros; apply reset_correctness; auto).

      assert (exists M', Forall (SemSB.sem_equation (translate G) bk H M') (translate_eqns n.(n_eqs))
                    /\ SemSB.well_structured_memories (translate_eqns n.(n_eqs)) M')
        as (M & Hmsem & WS).
      { eapply equations_correctness; eauto.
        inv WD; eapply Is_well_sch_compat; eauto.
        eapply nl_sem_equations_well_formed_app; eauto.
      }

      exists M.
      econstructor; eauto.
      + simpl; now rewrite Hnf.
      + simpl; rewrite map_fst_idty; eauto.
      + simpl; rewrite map_fst_idty; eauto.
      + eapply sem_equation_cons; eauto.
      + auto.
    - apply ident_eqb_neq in Hnf.
      eapply sem_node_cons in Hsem; eauto.
      inv Hord.
      eapply IHG in Hsem as [M]; eauto.
      exists M.
      now eapply sem_block_cons2; eauto.
  Qed.
