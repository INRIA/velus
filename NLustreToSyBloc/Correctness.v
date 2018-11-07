Require Import Coq.FSets.FMapPositive.
Require Import PArith.
Require Import Logic.FunctionalExtensionality.

Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.Memories.
Require Import Velus.SyBloc.SBSyntax.
Require Import Velus.NLustre.Ordered.
Require Import Velus.NLustre.Stream.
Require Import Velus.NLustre.NLSemantics.
Require Import Velus.SyBloc.SBSemantics.
Require Import Velus.NLustreToSyBloc.Translation.
Require Import Velus.RMemory.
Require Import Velus.SyBloc.SBInterpretor.

Require Import List.
Import List.ListNotations.
Require Import Coq.Sorting.Permutation.
Require Import Morphisms.

Open Scope list.
Open Scope nat.

Module Type CORRECTNESS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Clks  : CLOCKS      Ids)
       (Import SynNL : NLSYNTAX    Ids Op       Clks)
       (SynSB        : SBSYNTAX    Ids Op       Clks)
       (Import Str   : STREAM          Op OpAux)
       (Import Ord   : ORDERED     Ids Op       Clks SynNL)
       (Import SemNL : NLSEMANTICS Ids Op OpAux Clks SynNL       Str Ord)
       (SemSB        : SBSEMANTICS Ids Op OpAux Clks       SynSB Str)
       (Import Mem   : MEMORIES    Ids Op       Clks SynNL)
       (Import Trans : TRANSLATION Ids Op       Clks SynNL SynSB Mem)

       (Import Interp: SBINTERPRETOR Ids Op OpAux Clks SynSB Str SemSB).

  (* Fixpoint memvar_lexp (x: ident) (e: SynSB.lexp) := *)
  (*   match e with *)
  (*   | SynSB.Ereg y _ => x = y *)
  (*   | SynSB.Ewhen e _ _ => memvar_lexp x e *)
  (*   | SynSB.Eunop _ e _ => memvar_lexp x e *)
  (*   | SynSB.Ebinop _ e1 e2 _ => memvar_lexp x e1 \/ memvar_lexp x e2 *)
  (*   | _ => False *)
  (*   end. *)

  (* Fixpoint memvar_cexp (x: ident) (ce: SynSB.cexp) := *)
  (*   match ce with *)
  (*   | SynSB.Emerge _ e1 e2 => memvar_cexp x e1 \/ memvar_cexp x e2 *)
  (*   | SynSB.Eite e t f => memvar_lexp x e \/ memvar_cexp x t \/ memvar_cexp x f *)
  (*   | SynSB.Eexp e => memvar_lexp x e *)
  (*   end. *)

  (* Definition memory_spec (m: SemSB.memory) (memids: PS.t) (R: env) := *)
  (*   forall x v, *)
  (*     PM.find x R = Some v -> *)
  (*     PS.mem x memids = true -> *)
  (*     SemSB.get_reg x m = Some v. *)

  (* Definition memories_spec (M: SemSB.memories) (memids: PS.t) (H: history) := *)
  (*   forall n, memory_spec (SemSB.restr_mem M n) memids (SemSB.restr_hist H n). *)
  Section Global.

    Variable G: SynNL.global.
    Let P := translate G.

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

    Corollary sem_block_same_skeleton:
      forall f M M' xss oss xss' oss',
        SemSB.sem_block (translate G) f M xss oss ->
        SemSB.sem_block (translate G) f M' xss' oss' ->
        same_skeleton M M'.
    Proof.
    Admitted.

    Section SemInstant.

      Variable base: bool.
      Variable R: env.

      Lemma var_instant_correctness:
        forall x v,
          sem_var_instant R x v ->
          SemSB.sem_var_instant R x v.
      Proof.
        induction 1; constructor; auto.
      Qed.
      Hint Resolve var_instant_correctness.

      Lemma clock_instant_correctness:
        forall ck b,
          sem_clock_instant base R ck b ->
          SemSB.sem_clock_instant base R ck b.
      Proof.
        induction 1; eauto using SemSB.sem_clock_instant.
      Qed.

      Lemma typeof_correctness:
        forall e,
          SynSB.typeof (translate_lexp e) = typeof e.
      Proof.
        induction e; intros; simpl; auto.
      Qed.
      (* Hint Resolve typeof_correctness. *)


      Lemma lexp_instant_correctness:
        forall e v,
          sem_lexp_instant base R e v ->
          SemSB.sem_lexp_instant base R (translate_lexp e) v.
      Proof.
        induction 1; simpl; eauto using SemSB.sem_lexp_instant.
        - econstructor; eauto.
          now rewrite typeof_correctness.
        - econstructor; eauto.
          now rewrite 2 typeof_correctness.
      Qed.
      Hint Resolve lexp_instant_correctness.

      Lemma lexps_instant_correctness:
        forall es vs,
          sem_lexps_instant base R es vs ->
          SemSB.sem_lexps_instant base R (map translate_lexp es) vs.
      Proof.
        induction 1; constructor; auto.
      Qed.

      Lemma cexp_instant_correctness:
        forall ce v,
          sem_cexp_instant base R ce v ->
          SemSB.sem_cexp_instant base R (translate_cexp ce) v.
      Proof.
        induction 1; simpl; eauto using SemSB.sem_cexp_instant.
      Qed.


    End SemInstant.
    Hint Resolve var_instant_correctness clock_instant_correctness
         lexp_instant_correctness lexps_instant_correctness
         cexp_instant_correctness.

    Section Sem.

      Variable bk: stream bool.
      Variable H: history.

      Lemma var_correctness:
        forall x xs,
          sem_var bk H x xs ->
          SemSB.sem_var H x xs.
      Proof.
        intros ** Sem n; specialize (Sem n); auto.
      Qed.
      Hint Resolve var_correctness.

      Lemma vars_correctness:
        forall xs xss,
          sem_vars bk H xs xss ->
          SemSB.sem_vars H xs xss.
      Proof.
        intros ** Sem n; specialize (Sem n);
          induction Sem; constructor; auto.
      Qed.

      Lemma laexp_correctness:
        forall ck e xs,
          sem_laexp bk H ck e xs ->
          SemSB.sem_laexp bk H ck (translate_lexp e) xs.
      Proof.
        intros ** Sem n; specialize (Sem n); simpl in Sem.
        induction Sem; constructor; auto.
      Qed.

      Lemma caexp_correctness:
        forall ck ce xs,
          sem_caexp bk H ck ce xs ->
          SemSB.sem_caexp bk H ck (translate_cexp ce) xs.
      Proof.
        intros ** Sem n; specialize (Sem n); simpl in Sem.
        induction Sem; constructor; auto.
      Qed.

      Lemma laexps_correctness:
        forall ck es vs,
          sem_laexps bk H ck es vs ->
          SemSB.sem_laexps bk H ck (map translate_lexp es) vs.
      Proof.
        intros ** Sem n; specialize (Sem n); inv Sem.
        - econstructor 1; eauto.
        - constructor; auto.
          now rewrite all_absent_map.
      Qed.

      Inductive inst_in_eq: ident -> SynSB.equation -> Prop :=
      | InstInEqReset:
          forall x ck m r,
            inst_in_eq x (SynSB.EqReset ck m x r)
      | InstInEqCall:
          forall x xs ck m es,
            inst_in_eq x (SynSB.EqCall xs ck m x es).

      Definition inst_in_eqs (x: ident) (eqs: list SynSB.equation) : Prop :=
        List.Exists (inst_in_eq x) eqs.

      Lemma not_inst_in_eqs_cons:
        forall x eq eqs,
          ~ inst_in_eqs x (eq :: eqs)
          <-> ~ inst_in_eq x eq /\ ~ inst_in_eqs x eqs.
      Proof.
        split.
        - intro Hndef; split; intro;
            eapply Hndef; constructor (assumption).
        - intros [? ?] Hdef_all.
          inv Hdef_all; eauto.
      Qed.

      Lemma mfby_add_inst:
        forall i v0 ls M xs x M',
          SemSB.mfby i v0 ls M xs ->
          SemSB.mfby i v0 ls (add_inst x M' M) xs.
      Proof.
        inversion_clear 1.
        econstructor; eauto.
      Qed.
      Hint Resolve mfby_add_inst.

      Lemma mfby_add_val:
        forall i v0 ls M xs x mv,
          i <> x ->
          SemSB.mfby i v0 ls M xs ->
          SemSB.mfby i v0 ls (add_val x mv M) xs.
      Proof.
        inversion_clear 2.
        econstructor; eauto.
        rewrite find_val_gso; auto.
      Qed.

      Inductive defined_in_eq: ident -> SynSB.equation -> Prop :=
      | DefEqDef:
          forall x ck e,
            defined_in_eq x (SynSB.EqDef x ck e)
      | DefEqFby:
          forall x ck v e,
            defined_in_eq x (SynSB.EqFby x ck v e)
      | DefEqCall:
          forall x xs ck b o es,
            In x xs ->
            defined_in_eq x (SynSB.EqCall xs ck b o es).

      Definition defined_in_eqs (x: ident) (eqs: list SynSB.equation) : Prop :=
        List.Exists (defined_in_eq x) eqs.

      Lemma not_defined_in_eqs_cons:
        forall x eq eqs,
          ~ defined_in_eqs x (eq :: eqs)
          <-> ~ defined_in_eq x eq /\ ~ defined_in_eqs x eqs.
      Proof.
        split.
        - intro Hndef; split; intro;
            eapply Hndef; constructor(assumption).
        - intros [? ?] Hdef_all; inv Hdef_all; eauto.
      Qed.

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
    Hint Resolve var_correctness vars_correctness
         laexp_correctness caexp_correctness laexps_correctness.

    Fixpoint well_formed_eqs (eqs: list SynSB.equation) : Prop :=
        match eqs with
        | [] => True
        | SynSB.EqReset _ _ x _ :: eqs =>
          ~ inst_in_eqs x eqs /\ well_formed_eqs eqs
        | SynSB.EqCall xs _ _ x _ :: eqs =>
          ~ inst_in_eqs x eqs /\ Forall (fun x => ~ defined_in_eqs x eqs) xs /\ well_formed_eqs eqs
        | SynSB.EqDef x _ _ :: eqs =>
          ~ defined_in_eqs x eqs /\well_formed_eqs eqs
        | SynSB.EqFby x _ _ _ :: eqs =>
          ~ defined_in_eqs x eqs /\well_formed_eqs eqs
        end.

    Lemma Exists_app_l:
      forall (A : Type) (P : A -> Prop) (ll rr : list A),
        Exists P ll ->
        Exists P (ll ++ rr).
    Proof.
      induction 1.
      - now constructor.
      - now constructor 2.
    Qed.

    Lemma not_defined_in_eqs_app:
      forall eqs eqs' x,
        ~ defined_in_eqs x (eqs ++ eqs') ->
        ~ defined_in_eqs x eqs /\ ~ defined_in_eqs x eqs'.
    Proof.
      unfold defined_in_eqs.
      intros * Nd.
      split; intro; apply Nd.
      - now apply Exists_app_l.
      - now apply Exists_app.
    Qed.

    Lemma not_inst_in_eqs_app:
      forall eqs eqs' x,
        ~ inst_in_eqs x (eqs ++ eqs') ->
        ~ inst_in_eqs x eqs /\ ~ inst_in_eqs x eqs'.
    Proof.
      unfold inst_in_eqs.
      intros * Nd.
      split; intro; apply Nd.
      - now apply Exists_app_l.
      - now apply Exists_app.
    Qed.

    Lemma well_formed_eqs_app:
      forall eqs eqs',
        well_formed_eqs (eqs ++ eqs') ->
        well_formed_eqs eqs /\ well_formed_eqs eqs'.
    Proof.
      induction eqs as [|e]; simpl; auto.
      destruct e; intros ** [? H]; edestruct IHeqs; eauto;
        repeat match goal with
               | H: ~ defined_in_eqs _ (_ ++ _) |- _ => apply not_defined_in_eqs_app in H as (?&?)
               | H: ~ inst_in_eqs _ (_ ++ _) |- _ => apply not_inst_in_eqs_app in H as (?&?)
               end; auto.
      - destruct H; eauto.
      - destruct H; auto.
        repeat split; auto.
        eapply Forall_impl with (1:=not_defined_in_eqs_app eqs eqs') in H.
        now rewrite <-Forall_Forall' in H.
    Qed.


    (* Lemma memories_spec_add_inst: *)
    (*   forall M memids H x M', *)
    (*     memories_spec M memids H -> *)
    (*     memories_spec (add_inst x M' M) memids H. *)
    (* Proof. *)
    (*   intros ** Spec n x' v Find Mem. *)
    (*   specialize (Spec n x' v Find Mem). *)
    (*   unfold SemSB.get_reg in *. *)
    (*   now rewrite restr_mem_add_inst, mfind_mem_add_inst. *)
    (* Qed. *)
    (* Hint Resolve memories_spec_add_inst. *)

  End Global.
  Hint Resolve var_correctness vars_correctness
       laexp_correctness caexp_correctness laexps_correctness.

  Inductive compat_eq: equation -> list SynSB.equation -> Prop :=
  | CompatEqDef:
      forall x ck e eqs,
        (* ~ defined_in_eqs x eqs -> *)
        compat_eq (EqDef x ck e) eqs
  | CompatEqFby:
      forall x ck c0 e eqs,
        ~ defined_in_eqs x eqs ->
        compat_eq (EqFby x ck c0 e) eqs
  | CompatEqApp:
      forall xs ck f es r eqs,
        ~ inst_in_eqs (hd default xs) eqs ->
        compat_eq (EqApp xs ck f es r) eqs.

  Inductive compat_eqs: list equation -> Prop :=
  | CompatNil:
      compat_eqs []
  | CompatCons:
      forall eq eqs,
        compat_eqs eqs ->
        compat_eq eq (translate_eqns eqs) ->
        compat_eqs (eq :: eqs).

  Lemma equation_correctness:
    forall G bk H eqs M eq,
      (forall f xss oss,
          sem_node G f xss oss ->
          exists M, SemSB.sem_block (translate G) f M xss oss) ->
      (forall f r xss oss,
          sem_reset G f r xss oss ->
          exists M, SemSB.sem_block (translate G) f M xss oss
               /\ SemSB.reset_regs r M) ->
      sem_equation G bk H eq ->
      compat_eq eq eqs ->
      Forall (SemSB.sem_equation (translate G) bk H M) eqs ->
      exists M', Forall (SemSB.sem_equation (translate G) bk H M') (translate_eqn eq ++ eqs).
  Proof.
    intros ** IHnode IHreset Heq WF Heqs.
    inv Heq; simpl; inv WF.
    - repeat (econstructor; eauto).
    - edestruct IHnode as (M' & Block); eauto.
      exists (add_inst (hd default x) M' M).
      constructor.
      + econstructor; eauto.
        apply find_inst_gss.
      + apply sem_equation_add_inst; auto.
    - edestruct IHreset as (M' & Block & Reset); eauto.
      exists (add_inst (hd default x) M' M).
      constructor.
      + econstructor; eauto.
        apply find_inst_gss.
      + constructor.
        * econstructor; eauto.
          apply find_inst_gss.
        * apply sem_equation_add_inst; auto.
    - exists (add_val x {| SemSB.content := hold (sem_const c0) ls; SemSB.reset := fun _ => false |} M).
      constructor.
      + econstructor; eauto.
        econstructor.
        * apply find_val_gss.
        * reflexivity.
        * intro; unfold fby; simpl.
          destruct (ls n); auto.
      + apply sem_equation_add_val; auto.
  Qed.

  Corollary equations_correctness:
    forall G bk H eqs,
      (forall f xss oss,
          sem_node G f xss oss ->
          exists M, SemSB.sem_block (translate G) f M xss oss) ->
      (forall f r xss oss,
          sem_reset G f r xss oss ->
          exists M, SemSB.sem_block (translate G) f M xss oss
               /\ SemSB.reset_regs r M) ->
      compat_eqs eqs ->
      Forall (sem_equation G bk H) eqs ->
      exists M', Forall (SemSB.sem_equation (translate G) bk H M') (translate_eqns eqs).
  Proof.
    intros ** IHnode IHreset WF Heqs.
    induction eqs as [|eq eqs IHeqs]; [exists (@empty_memory SemSB.mvalues); now constructor|].
    apply Forall_cons2 in Heqs as [Heq Heqs].
    inv WF.
    eapply IHeqs in Heqs as [M Heqs]; eauto.
    unfold translate_eqns; rewrite concatMap_cons.
    eapply equation_correctness; eauto.
  Qed.

  Inductive is_block_in_eq: ident -> SynSB.equation -> Prop :=
    IBI:
      forall xs ck b i es,
        is_block_in_eq b (SynSB.EqCall xs ck b i es).

  Definition is_block_in (b: ident) (eqs: list SynSB.equation) : Prop :=
    Exists (is_block_in_eq b) eqs.

  Lemma not_is_block_in_cons:
    forall b eq eqs,
      ~ is_block_in b (eq :: eqs) <-> ~ is_block_in_eq b eq /\ ~ is_block_in b eqs.
  Proof.
    intros.
    split; intro HH.
    - split; intro; apply HH; unfold is_block_in; intuition.
    - destruct HH; inversion_clear 1; intuition.
  Qed.

  Lemma is_block_in_Forall:
    forall b eqs,
      ~ is_block_in b eqs <-> Forall (fun eq => ~ is_block_in_eq b eq) eqs.
  Proof.
    induction eqs as [|eq eqs IH];
      [split; [now constructor|now inversion 2]|].
    split; intro HH.
    - apply not_is_block_in_cons in HH.
      destruct HH as [Heq Heqs].
      constructor; [exact Heq|apply IH with (1:=Heqs)].
    - apply not_is_block_in_cons.
      inversion_clear HH as [|? ? Heq Heqs].
      apply IH in Heqs.
      intuition.
  Qed.

  Lemma Exists_app':
    forall A P (l l': list A),
      Exists P (l ++ l') <-> Exists P l \/ Exists P l'.
  Proof.
    split.
    - induction l; simpl; auto.
      inversion_clear 1 as [|?? E]; intuition.
    - intros [E|E].
      + induction l; simpl; inv E; auto.
      + induction l; simpl; auto.
  Qed.

  Lemma is_block_is_node:
    forall f eqs,
      Is_node_in f eqs <-> is_block_in f (translate_eqns eqs).
  Proof.
    induction eqs; split; inversion 1 as [?? InEq E|??? E].
    - inv InEq.
      unfold translate_eqns, concatMap; simpl.
      destruct r as [()|].
      + right; left; econstructor.
      + left; constructor.
    - unfold translate_eqns, concatMap; simpl.
      apply Exists_app; rewrite <-IHeqs; auto.
    - inv InEq.
      unfold translate_eqns, concatMap in E; simpl in E.
      destruct a; try destruct o as [()|]; simpl in E; inv E.
      left; constructor.
    - unfold translate_eqns, concatMap in H; simpl in H.
      apply Exists_app' in H as [E'|E'].
      + left.
        destruct a;try destruct o as [()|]; simpl in E';
          inversion E' as [?? InEq|?? InNil]; try inv InNil; try inv InEq.
        * inv H3; constructor.
        * inv H3.
        * constructor.
      + right; rewrite IHeqs; auto.
  Qed.

  Lemma find_block_later_not_is_block_in:
    forall b n G bl P,
      Ordered_nodes (n :: G) ->
      SynSB.find_block b (translate G) = Some (bl, P) ->
      ~ is_block_in n.(n_name) bl.(SynSB.b_eqs).
  Proof.
    intros ** Hord Hfind Hini.
    pose proof (SynSB.find_block_name _ _ _ _ Hfind) as Hb.
    apply find_block_translate in Hfind as (n' & Hfind' & E).
    rewrite E in Hini; simpl in Hini.
    apply is_block_is_node in Hini.
    eapply find_node_later_not_Is_node_in; eauto.
  Qed.

  Lemma sem_block_cons:
    forall n G f xs M ys,
      Ordered_nodes (n :: G) ->
      n.(n_name) <> f ->
      SemSB.sem_block (translate (n :: G)) f xs M ys ->
      SemSB.sem_block (translate G) f xs M ys.
  Proof.
    intros ** Hord Hnf Hsem.
    revert Hnf.
    induction Hsem
      as [| | | |????????? Hfind ????? Heqs IHeqs]
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
      clear Heqs.
      induction (SynSB.b_eqs bl); inv NotIns; inv IHeqs; constructor; auto.
  Qed.

  Lemma sem_block_cons2:
    forall n G f xs M ys,
      Forall (fun n' => n_name n <> n_name n') G ->
      SemSB.sem_block (translate G) f xs M ys ->
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
    forall G bk H M eqs n,
      Ordered_nodes (n :: G) ->
      ~Is_node_in n.(n_name) eqs ->
      Forall (SemSB.sem_equation (translate G) bk H M) (translate_eqns eqs) ->
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

    (* Lemma reset_reset_spec': *)
    (*   forall n x p M mv, *)
    (*     path_inst p (Fm (count r n)) = Some M -> *)
    (*     find_val x M = Some mv -> *)
    (*     mv.(SemSB.reset) n = true -> *)
    (*     reset_reset x p n = true. *)
    (* Proof. *)
    (*   unfold reset_reset; intros ** ->; intros ->; intros ->. *)
    (*   apply Bool.orb_true_r. *)
    (* Qed. *)

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
        (forall k,
            exists bk xs ls,
           SemSB.sem_var (Fh k) x xs /\
           SemSB.sem_laexp bk (Fh k) ck e ls /\
           find_val x (Fm k) = Some (Fmvs k) /\
           SemSB.content (Fmvs k) 0 = sem_const c0 /\
           (forall n : nat,
            match ls n with
            | absent =>
                SemSB.content (Fmvs k) (S n) = (if SemSB.reset (Fmvs k) (S n) then sem_const c0 else SemSB.content (Fmvs k) n) /\
                xs n = absent
            | present v' =>
                SemSB.content (Fmvs k) (S n) = (if SemSB.reset (Fmvs k) (S n) then sem_const c0 else v') /\
                xs n = present (SemSB.content (Fmvs k) n)
            end) /\ SemSB.clock_of (mask (all_absent (xss 0)) k r xss) bk) ->
        forall n, r n = true ->
             SemSB.content reset_mvalues n = sem_const c0.
    Proof.
      intros ** Spec n E.
      unfold reset_mvalues; simpl.
      induction n; simpl; rewrite E.
      - destruct (Spec 1) as (?&?&?&?); intuition.
      - specialize (Spec (S (count r n))); destruct Spec as (bk &?&?&?& Hexp &?& Init & Heq & Clock).
        assert (forall n',
                   n' <= n ->
                   interp_laexp_instant (bk n') (SemSB.restr_hist (Fh (S (count r n))) n') ck e = absent)
          as Absent.
        { assert (forall n',
                     n' <= n ->
                     bk n' = false) as Hbk.
          { clear - Clock.
            intros ** Lte.
            specialize (Clock n').
            rewrite mask_opaque in Clock; auto.
            - apply Bool.not_true_is_false; intro Ebk.
              apply Clock in Ebk.
              clear - Ebk; induction Ebk; auto.
              admit.
            - apply Lt.le_lt_or_eq in Lte as [Lt|]; subst; auto.
              apply (count_le' r) in Lt; omega.
          }
          intros.
          specialize (Hexp n'); simpl in Hexp.
          pose proof Hexp as Hexp'; apply interp_laexp_instant_sound in Hexp'; rewrite Hexp' in Hexp.
          destruct (interp_laexp_instant (bk n') (SemSB.restr_hist (Fh (S (count r n))) n') ck e); auto.
          inversion_clear Hexp as [???? HClock|].
          rewrite Hbk in HClock; auto; contradict HClock.
          apply SemSB.not_subrate_clock.
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

      Lemma interp_var_instant_reset:
        forall x,
          (forall k, PM.find x (Fh k) <> None) ->
          interp_var_instant (SemSB.restr_hist (Fh (count r n)) n) x =
          interp_var_instant (SemSB.restr_hist (reset_history (Fh 0)) n) x.
      Proof.
        intros ** Spec.
        unfold interp_var_instant, reset_history, SemSB.restr_hist, PM.map.
        repeat rewrite PM.gmapi; rewrite option_map_map.
        destruct (PM.find x (Fh (count r n))) eqn: E.
        - destruct (PM.find x (Fh 0)) eqn: E'; auto.
          exfalso; eapply Spec; eauto.
        - exfalso; eapply Spec; eauto.
      Qed.

      Lemma sem_var_instant_reset:
        forall x v,
          (forall k, PM.find x (Fh k) <> None) ->
          SemSB.sem_var_instant (SemSB.restr_hist (Fh (count r n)) n) x v ->
          SemSB.sem_var_instant (SemSB.restr_hist (reset_history (Fh 0)) n) x v.
      Proof.
        intros ** Spec Sem.
        induction Sem; constructor.
        unfold reset_history, SemSB.restr_hist, PM.map in *.
        repeat rewrite PM.gmapi in *; rewrite option_map_map.
        destruct (PM.find x (Fh (count r n))) eqn: E.
        - destruct (PM.find x (Fh 0)) eqn: E'; auto.
          exfalso; eapply Spec; eauto.
        - exfalso; eapply Spec; eauto.
      Qed.

      Lemma interp_vars_instant_reset:
        forall xs,
          Forall (fun x => forall k, PM.find x (Fh k) <> None) xs ->
          interp_vars_instant (SemSB.restr_hist (Fh (count r n)) n) xs =
          interp_vars_instant (SemSB.restr_hist (reset_history (Fh 0)) n) xs.
      Proof.
        intros ** Spec.
        unfold interp_vars_instant; induction xs; inv Spec; simpl; auto.
        rewrite interp_var_instant_reset; auto; f_equal; auto.
      Qed.

      Lemma sem_vars_instant_reset:
        forall xs vs,
          Forall (fun x => forall k, PM.find x (Fh k) <> None) xs ->
          SemSB.sem_vars_instant (SemSB.restr_hist (Fh (count r n)) n) xs vs ->
          SemSB.sem_vars_instant (SemSB.restr_hist (reset_history (Fh 0)) n) xs vs.
      Proof.
        intros ** Spec Sem.
        induction Sem; inv Spec; constructor.
        - apply sem_var_instant_reset; auto.
        - apply IHSem; auto.
      Qed.

      Variable bk: stream bool.
      Variable xss: stream (list value).
      Hypothesis Clk: SemSB.clock_of (mask (all_absent (xss 0)) (count r n) r xss) bk.
      Let bk' := SemSB.clock_of' xss.

      Lemma interp_clock_instant_reset:
        forall ck,
          interp_clock_instant (bk n) (SemSB.restr_hist (Fh (count r n)) n) ck =
          interp_clock_instant (bk' n) (SemSB.restr_hist (reset_history (Fh 0)) n) ck.
      Proof.
        induction ck; intros; simpl.
        - apply SemSB.clock_of_equiv' in Clk; rewrite Clk.
          unfold SemSB.clock_of'.
          rewrite mask_transparent; auto.
        - rewrite interp_var_instant_reset; [|admit].
          rewrite IHck; auto.
      Qed.

      Lemma sem_clock_instant_reset:
        forall ck b,
          SemSB.sem_clock_instant (bk n) (SemSB.restr_hist (Fh (count r n)) n) ck b ->
          SemSB.sem_clock_instant (bk' n) (SemSB.restr_hist (reset_history (Fh 0)) n) ck b.
      Proof.
        induction 1.
        - apply SemSB.clock_of_equiv' in Clk; rewrite Clk.
          subst bk'.
          unfold SemSB.clock_of'.
          rewrite mask_transparent; constructor.
        - econstructor; eauto.
          apply sem_var_instant_reset; eauto.
          admit.
        - constructor; auto.
          apply sem_var_instant_reset; eauto.
          admit.
        - eapply SemSB.Son_abs2; eauto.
          apply sem_var_instant_reset; eauto.
          admit.
      Qed.
      Hint Resolve sem_clock_instant_reset.

      Lemma interp_lexp_instant_reset:
        forall e,
          interp_lexp_instant (bk n) (SemSB.restr_hist (Fh (count r n)) n) e =
          interp_lexp_instant (bk' n) (SemSB.restr_hist (reset_history (Fh 0)) n) e.
      Proof.
        induction e; intros; simpl.
        - apply SemSB.clock_of_equiv' in Clk; rewrite Clk.
          unfold SemSB.clock_of'.
          rewrite mask_transparent; auto.
        - apply interp_var_instant_reset.
          admit.
        - rewrite interp_var_instant_reset, IHe; auto.
          admit.
        - rewrite IHe; auto.
        - rewrite IHe1, IHe2; auto.
      Qed.

      Lemma sem_lexp_instant_reset:
        forall e v,
          SemSB.sem_lexp_instant (bk n) (SemSB.restr_hist (Fh (count r n)) n) e v ->
          SemSB.sem_lexp_instant (bk' n) (SemSB.restr_hist (reset_history (Fh 0)) n) e v.
      Proof.
        induction 1; eauto using SemSB.sem_lexp_instant.
        - constructor; subst.
          apply SemSB.clock_of_equiv' in Clk; rewrite Clk.
          unfold SemSB.clock_of'.
          rewrite mask_transparent; auto.
        - constructor.
          apply sem_var_instant_reset; auto.
          admit.
        - econstructor; eauto.
          apply sem_var_instant_reset; auto.
          admit.
        - eapply SemSB.Swhen_abs1; eauto.
          apply sem_var_instant_reset; auto.
          admit.
        - constructor; auto.
          apply sem_var_instant_reset; auto.
          admit.
      Qed.
      Hint Resolve sem_lexp_instant_reset.

      Lemma interp_lexps_instant_reset:
        forall es,
          interp_lexps_instant (bk n) (SemSB.restr_hist (Fh (count r n)) n) es =
          interp_lexps_instant (bk' n) (SemSB.restr_hist (reset_history (Fh 0)) n) es.
      Proof.
        unfold interp_lexps_instant; induction es; simpl; auto.
        rewrite interp_lexp_instant_reset; f_equal; auto.
      Qed.

      Lemma sem_lexps_instant_reset:
        forall es vs,
          SemSB.sem_lexps_instant (bk n) (SemSB.restr_hist (Fh (count r n)) n) es vs ->
          SemSB.sem_lexps_instant (bk' n) (SemSB.restr_hist (reset_history (Fh 0)) n) es vs.
      Proof.
        unfold SemSB.sem_lexps_instant; induction 1; constructor; auto.
      Qed.

      Lemma interp_laexp_instant_reset:
        forall ck e,
          interp_laexp_instant (bk n) (SemSB.restr_hist (Fh (count r n)) n) ck e =
          interp_laexp_instant (bk' n) (SemSB.restr_hist (reset_history (Fh 0)) n) ck e.
      Proof.
        intros.
        unfold interp_laexp_instant, interp_annotated_instant.
        erewrite interp_clock_instant_reset, interp_lexp_instant_reset; eauto.
      Qed.

      Lemma sem_laexp_instant_reset:
        forall ck e v,
          SemSB.sem_laexp_instant (bk n) (SemSB.restr_hist (Fh (count r n)) n) ck e v ->
          SemSB.sem_laexp_instant (bk' n) (SemSB.restr_hist (reset_history (Fh 0)) n) ck e v.
      Proof.
        induction 1; constructor; auto.
      Qed.

      Lemma interp_laexps_instant_reset:
        forall ck es,
          interp_laexps_instant (bk n) (SemSB.restr_hist (Fh (count r n)) n) ck es =
          interp_laexps_instant (bk' n) (SemSB.restr_hist (reset_history (Fh 0)) n) ck es.
      Proof.
        intros; unfold interp_laexps_instant.
        rewrite interp_lexps_instant_reset, interp_clock_instant_reset; auto.
      Qed.

      Lemma sem_laexps_instant_reset:
        forall ck es vs,
          SemSB.sem_laexps_instant (bk n) (SemSB.restr_hist (Fh (count r n)) n) ck es vs ->
          SemSB.sem_laexps_instant (bk' n) (SemSB.restr_hist (reset_history (Fh 0)) n) ck es vs.
      Proof.
        induction 1.
        - eapply SemSB.SLticks; eauto.
          apply sem_lexps_instant_reset; auto.
        - apply SemSB.SLabss; auto.
          apply sem_lexps_instant_reset; auto.
        - apply SemSB.SNil.
      Qed.

      Lemma interp_cexp_instant_reset:
        forall e,
          interp_cexp_instant (bk n) (SemSB.restr_hist (Fh (count r n)) n) e =
          interp_cexp_instant (bk' n) (SemSB.restr_hist (reset_history (Fh 0)) n) e.
      Proof.
        induction e; simpl.
        - rewrite interp_var_instant_reset, IHe1, IHe2; auto.
          admit.
        - rewrite interp_lexp_instant_reset, IHe1, IHe2; auto.
        - apply interp_lexp_instant_reset.
      Qed.

      Lemma sem_cexp_instant_reset:
        forall e v,
          SemSB.sem_cexp_instant (bk n) (SemSB.restr_hist (Fh (count r n)) n) e v ->
          SemSB.sem_cexp_instant (bk' n) (SemSB.restr_hist (reset_history (Fh 0)) n) e v.
      Proof.
        induction 1; eauto using SemSB.sem_cexp_instant.
        - econstructor; eauto.
          apply sem_var_instant_reset; auto.
          admit.
        - eapply SemSB.Smerge_false; eauto.
          apply sem_var_instant_reset; auto.
          admit.
        - econstructor; eauto.
          apply sem_var_instant_reset; auto.
          admit.
      Qed.
      Hint Resolve sem_cexp_instant_reset.

      Lemma interp_caexp_instant_reset:
        forall ck e,
          interp_caexp_instant (bk n) (SemSB.restr_hist (Fh (count r n)) n) ck e =
          interp_caexp_instant (bk' n) (SemSB.restr_hist (reset_history (Fh 0)) n) ck e.
      Proof.
        intros.
        unfold interp_caexp_instant, interp_annotated_instant.
        erewrite interp_clock_instant_reset, interp_cexp_instant_reset; eauto.
      Qed.

      Lemma sem_caexp_instant_reset:
        forall ck e v,
          SemSB.sem_caexp_instant (bk n) (SemSB.restr_hist (Fh (count r n)) n) ck e v ->
          SemSB.sem_caexp_instant (bk' n) (SemSB.restr_hist (reset_history (Fh 0)) n) ck e v.
      Proof.
        induction 1; constructor; auto.
      Qed.

    End InterpReset.

  End Choices.
  Hint Resolve reset_memories_spec sub_inst_reset_memories_path.

  Lemma Forall2_In_l:
    forall {A B: Type} (l: list A) (l': list B) P x,
      Forall2 P l l' ->
      In x l ->
      exists x', P x x'.
  Proof.
    intros ** F2 Hin.
    induction F2.
    - contradiction.
    - inv Hin; eauto.
  Qed.

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

  (* Section InstantEq. *)

  (*   Variable P: SynSB.program. *)

  (*   Variable n: nat. *)

  (*   Inductive mfby_instant: ident -> val -> value -> SemSB.memories -> value -> Prop := *)
  (*     mfby_instant_intro: *)
  (*       forall x mvs v0 v M v', *)
  (*         find_val x M = Some mvs -> *)
  (*         mvs.(SemSB.content) 0 = v0 -> *)
  (*         match v' with *)
  (*         | absent => *)
  (*           mvs.(SemSB.content) (S n) = (if mvs.(SemSB.reset) (S n) then v0 else mvs.(SemSB.content) n) *)
  (*           /\ v = absent *)
  (*         | present v' => *)
  (*           mvs.(SemSB.content) (S n) = (if mvs.(SemSB.reset) (S n) then v0 else v') *)
  (*           /\ v = present (mvs.(SemSB.content) n) *)
  (*         end -> *)
  (*         mfby_instant x v0 v' M v. *)

  (*   Inductive sem_equation_instant: bool -> env -> SemSB.memories -> SynSB.equation -> Prop := *)
  (*   | SEqIDef: *)
  (*       forall base R M x v ck ce, *)
  (*         (* v = interp_caexp_instant base R ck ce -> *) *)
  (*         SemSB.sem_var_instant R x v -> *)
  (*         SemSB.sem_caexp_instant base R ck ce v -> *)
  (*         sem_equation_instant base R M (SynSB.EqDef x ck ce) *)
  (*   | SEqIFby: *)
  (*       forall base R M x ck c0 e v v', *)
  (*         SemSB.sem_var_instant R x v -> *)
  (*         SemSB.sem_laexp_instant base R ck e v' -> *)
  (*         mfby_instant x (sem_const c0) v' M v -> *)
  (*         sem_equation_instant base R M (SynSB.EqFby x ck c0 e) *)
  (*   | SEqIReset: *)
  (*       forall base R M ck b i r v M', *)
  (*         SemSB.sem_var_instant R r v -> *)
  (*         sub_inst i M M' -> *)
  (*         reset_regs_instant n (SemSB.reset_of_value v) M' -> *)
  (*         sem_equation_instant base R M (SynSB.EqReset ck b i r) *)
  (*   | SEqICall: *)
  (*       forall base R M ys M' ck b i es ves vys, *)
  (*         SemSB.sem_laexps_instant base R ck es ves -> *)
  (*         sub_inst i M M' -> *)
  (*         sem_block_instant b M' ves vys -> *)
  (*         SemSB.sem_vars_instant R ys vys -> *)
  (*         sem_equation_instant base R M (SynSB.EqCall ys ck b i es) *)

  (*   with sem_block_instant: ident -> SemSB.memories -> list value -> list value -> Prop := *)
  (*          SIBlock: *)
  (*            forall b bl P' M R vxs vys base, *)
  (*              (present_list vxs <-> base = true) -> *)
  (*              SynSB.find_block b P = Some (bl, P') -> *)
  (*              SemSB.sem_vars_instant R (map fst bl.(SynSB.b_in)) vxs -> *)
  (*              SemSB.sem_vars_instant R (map fst bl.(SynSB.b_out)) vys -> *)
  (*              SemSB.instant_same_clock vxs -> *)
  (*              SemSB.instant_same_clock vys -> *)
  (*              (absent_list vxs <-> absent_list vys) -> *)
  (*              Forall (sem_equation_instant base R M) bl.(SynSB.b_eqs) -> *)
  (*              sem_block_instant b M vxs vys. *)
  (* End InstantEq. *)

  (* Ltac interp_sound H := *)
  (*   match type of H with *)
  (*   | SemSB.sem_var_instant ?R ?x ?v => *)
  (*     assert (v = interp_var_instant R x) by (apply interp_var_instant_sound; auto) *)
  (*   | SemSB.sem_laexp_instant ?b ?R ?c ?e ?v => *)
  (*     assert (v = interp_laexp_instant b R c e) by (apply interp_laexp_instant_sound; auto) *)
  (*   | SemSB.sem_caexp_instant ?b ?R ?c ?e ?v => *)
  (*     assert (v = interp_caexp_instant b R c e) by (apply interp_caexp_instant_sound; auto) *)
  (*   | SemSB.sem_laexps_instant ?b ?R ?c ?es ?vs => *)
  (*     assert (vs = interp_laexps_instant b R c es) by (apply interp_laexps_instant_sound; auto) *)
  (*   | SemSB.sem_vars_instant ?R ?xs ?vs => *)
  (*     assert (vs = interp_vars_instant R xs) by (apply interp_vars_instant_sound; auto) *)
  (*   end; subst; auto. *)

  (* Lemma spec_sem_equation: *)
  (*   forall e P bk H M, *)
  (*     (forall b M xss yss, (forall n, sem_block_instant P n b M (xss n) (yss n)) <-> SemSB.sem_block P b M xss yss) -> *)
  (*     ((forall n, sem_equation_instant P n (bk n) (SemSB.restr_hist H n) M e) <-> SemSB.sem_equation P bk H M e). *)
  (* Proof. *)
  (*   intros ** Block; split; intros Sem. *)
  (*   - induction e. *)
  (*     + apply SemSB.SEqDef with (xs := interp_caexp bk H c c0); *)
  (*         intro; specialize (Sem n); inversion_clear Sem as [???????? Exp| | |]; interp_sound Exp. *)
  (*     + apply SemSB.SEqFby with (xs := interp_var H i) (ls := interp_laexp bk H c l). *)
  (*       * intro; specialize (Sem n); inversion_clear Sem as [|????????? Var| |]; interp_sound Var. *)
  (*       * intro; specialize (Sem n); inversion_clear Sem as [|?????????? Exp| |]; interp_sound Exp. *)
  (*       * pose proof (Sem 0) as Sem0; inversion_clear Sem0 as [|??????????? Fby| |]; *)
  (*           inversion_clear Fby as [?????? Find]. *)
  (*         econstructor; eauto. *)
  (*         clear - Sem Find. *)
  (*         intro; specialize (Sem n); inversion_clear Sem as [|????????? Var Exp Fby| |]; *)
  (*           inversion_clear Fby as [?????? Find']; rewrite Find' in Find; inv Find; *)
  (*             interp_sound Var; interp_sound Exp. *)
  (*     + pose proof (Sem 0) as Sem0; inversion_clear Sem0 as [| |?????????? Sub|]. *)
  (*       eapply SemSB.SEqReset with (rs := interp_var H i1); eauto. *)
  (*       * intro; specialize (Sem n); inversion_clear Sem as [| |????????? Var|]; interp_sound Var. *)
  (*       * clear - Sem Sub. *)
  (*         apply reset_regs_instant_spec. *)
  (*         intro; specialize (Sem n); inversion_clear Sem as [| |????????? Var Sub'|]; *)
  (*           unfold sub_inst in *; rewrite Sub' in Sub; inv Sub; interp_sound Var. *)
  (*     + pose proof (Sem 0) as Sem0; inversion_clear Sem0 as [| | |???????????? Sub]. *)
  (*       eapply SemSB.SEqCall with (ess := interp_laexps bk H c l) (oss := interp_vars H i); eauto. *)
  (*       * intro; specialize (Sem n); inversion_clear Sem as [| | |??????????? Exps]; interp_sound Exps. *)
  (*       * clear - Block Sem Sub. *)
  (*         apply Block; intro; specialize (Sem n); inversion_clear Sem as [| | |??????????? Exps Sub' ? Vars]; *)
  (*           unfold sub_inst in *; rewrite Sub' in Sub; inv Sub; *)
  (*             interp_sound Exps; interp_sound Vars. *)
  (*       * intro; specialize (Sem n); inversion_clear Sem as [| | |?????????????? Vars]; interp_sound Vars. *)
  (*   - destruct Sem as [|??????????? Fby| |????????????? SemBlock]; intro; eauto using sem_equation_instant. *)
  (*     + econstructor; eauto. *)
  (*       inversion_clear Fby as [???????? Spec]; specialize (Spec n). *)
  (*       econstructor; eauto. *)
  (*     + econstructor; eauto. *)
  (*       change (SemSB.reset_of_value (rs n)) with (SemSB.reset_of rs n). *)
  (*       apply reset_regs_instant_spec'; auto. *)
  (*     + econstructor; eauto. *)
  (*       apply Block; auto. *)
  (* Qed. *)

  (* Lemma spec_sem_block: *)
  (*   forall P b M xss yss, (forall n, sem_block_instant P n b M (xss n) (yss n)) <-> SemSB.sem_block P b M xss yss. *)
  (* Proof. *)
  (*   induction P; intros. *)
  (*   - split; intros Sem. *)
  (*     + specialize (Sem 0); inv Sem; simpl in *; discriminate. *)
  (*     + inv Sem; simpl in *; discriminate. *)
  (*   - split; intros Sem. *)
  (*     + pose proof (Sem 0) as Sem0; inversion_clear Sem0 as [????????? Find]. *)
  (*       admit. *)
  (*     + inversion Sem. *)
  (*       econstructor; eauto. *)
  (*       * apply SemSB.clock_of_equiv. *)
  (*       * intro; specialize (Sem n); inversion_clear Sem as [????????? Find' Vars]; *)
  (*           rewrite Find' in Find; inv Find. *)
  (*         interp_sound Vars. *)

(*   Lemma spec_EqDef: *)
(*     forall P bk H M x ck e, *)
(*       (forall n, *)
(*           let v := interp_caexp_instant (bk n) (SemSB.restr_hist H n) ck e in *)
(*           SemSB.sem_var_instant (SemSB.restr_hist H n) x v *)
(*           /\ SemSB.sem_caexp_instant (bk n) (SemSB.restr_hist H n) ck e v) <-> *)
(*       SemSB.sem_equation P bk H M (SynSB.EqDef x ck e). *)
(*   Proof. *)
(*     split. *)
(*     - intros ** Spec. *)
(*       apply SemSB.SEqDef with (xs := interp_caexp bk H ck e); *)
(*         intro; destruct (Spec n); auto. *)
(*     - inversion_clear 1 as [???????  Hvar Hexp| | |]; *)
(*         intro; specialize (Hvar n); specialize (Hexp n); simpl in *. *)
(*       erewrite <-interp_caexp_instant_sound; eauto. *)
(*   Qed. *)

(*   Lemma spec_EqFby: *)
(*     forall P bk H M x ck c0 e, *)
(*       (exists mvs, *)
(*           find_val x M = Some mvs *)
(*           /\ mvs.(SemSB.content) 0 = sem_const c0 *)
(*           /\ (forall n, *)
(*                 let v := interp_var_instant (SemSB.restr_hist H n) x in *)
(*                 let v' := interp_laexp_instant (bk n) (SemSB.restr_hist H n) ck e in *)
(*                 SemSB.sem_var_instant (SemSB.restr_hist H n) x v *)
(*                 /\ SemSB.sem_laexp_instant (bk n) (SemSB.restr_hist H n) ck e v' *)
(*                 /\ match v' with *)
(*                   | absent => *)
(*                     mvs.(SemSB.content) (S n) = *)
(*                     (if mvs.(SemSB.reset) (S n) then sem_const c0 else mvs.(SemSB.content) n) *)
(*                     /\ v = absent *)
(*                   | present v' => *)
(*                     mvs.(SemSB.content) (S n) = *)
(*                     (if mvs.(SemSB.reset) (S n) then sem_const c0 else v') *)
(*                     /\ v = present (mvs.(SemSB.content) n) *)
(*                   end)) <-> *)
(*       SemSB.sem_equation P bk H M (SynSB.EqFby x ck c0 e). *)
(*   Proof. *)
(*     split. *)
(*     - intros ** (? & ? & ? & Spec). *)
(*       apply SemSB.SEqFby with (xs := interp_var H x) (ls := interp_laexp bk H ck e). *)
(*       + intro; destruct (Spec n); auto. *)
(*       + intro; destruct (Spec n) as (?&?&?); auto. *)
(*       + econstructor; eauto. *)
(*         intro; destruct (Spec n) as (?&?&?); auto. *)
(*     - inversion_clear 1 as [|????????? Hvar Hexp Fby| |]; *)
(*         inversion_clear Fby as [???????? Spec]. *)
(*       econstructor; intuition; eauto. *)
(*       specialize (Hvar n); specialize (Hexp n); simpl in *. *)
(*       erewrite <-interp_laexp_instant_sound, <-interp_var_instant_sound; eauto; intuition. *)
(*       specialize (Spec n); auto. *)
(*   Qed. *)

(*   Lemma spec_EqReset: *)
(*     forall P bk H M ck b i r, *)
(*       (exists M', *)
(*           sub_inst i M M' *)
(*           /\ *)
(*           forall n, *)
(*             let v := interp_var_instant (SemSB.restr_hist H n) r in *)
(*             SemSB.sem_var_instant (SemSB.restr_hist H n) r v *)
(*             /\ reset_regs_instant n (SemSB.reset_of_value v) M') <-> *)
(*       SemSB.sem_equation P bk H M (SynSB.EqReset ck b i r). *)
(*   Proof. *)
(*     split. *)
(*     - intros ** (M' & Sub & Spec). *)
(*       apply SemSB.SEqReset with (M' := M') (rs := interp_var H r); auto. *)
(*       + intro; destruct (Spec n); auto. *)
(*       + clear Sub. *)
(*         induction M' as [?? IH] using memory_ind'. *)
(*         constructor. *)
(*         * intros; destruct (Spec n) as (? & RstRegs); inv RstRegs; eauto. *)
(*         * (* intros ** Find. *) *)
(*           intros ** Find; pose proof Find as Find'; unfold sub_inst, find_inst in Find. *)
(*           apply Env.find_in, in_map with (f := snd) in Find; simpl in Find. *)
(*           eapply In_Forall in IH; eauto. *)
(*           apply IH. *)
(*           intro; destruct (Spec n) as (? & IHSpec); split; auto. *)
(*           inv IHSpec; eauto. *)
(*     - inversion_clear 1 as [| |????????? Hvar Sub Rst|]. *)
(*       econstructor; split; eauto. *)
(*       intro; specialize (Hvar n); simpl in *. *)
(*       erewrite <-interp_var_instant_sound; eauto; split; auto. *)
(*       assert (forall n, SemSB.reset_of rs n = SemSB.reset_of_value (rs n)); auto. *)
(*       clear Sub. *)
(*       induction Rst as [?? Rst' Rst'']. *)
(*       constructor; eauto. *)
(*   Qed. *)

(*                (* clock_of xss bk -> *) *)
(*                (* find_block b P = Some (bl, P') -> *) *)
(*                (* sem_vars H (map fst bl.(b_in)) xss -> *) *)
(*                (* sem_vars H (map fst bl.(b_out)) yss -> *) *)
(*                (* same_clock xss -> *) *)
(*                (* same_clock yss -> *) *)
(*                (* (forall n, absent_list (xss n) <-> absent_list (yss n)) -> *) *)
(*                (* Forall (sem_equation bk H M) bl.(b_eqs) -> *) *)

(*   Lemma spec_EqCall: *)
(*     forall P bk H M ys ck b i es, *)
(*       (exists M' bl P' H', *)
(*           sub_inst i M M' *)
(*           /\ SynSB.find_block b P = Some (bl, P') *)
(* (* Forall (SemSB.sem_equation P (clock_of' (fun n : nat => interp_laexps_instant (bk n) (SemSB.restr_hist H n) ck es)) H' M') *) *)
(* (*      (SynSB.b_eqs bl) *) *)

(*           (* /\ SemSB.sem_block P b M' (interp_laexps bk H ck es) (interp_vars H ys)) *) *)
(*           /\ *)
(*           forall n, *)
(*             let ves := interp_laexps_instant (bk n) (SemSB.restr_hist H n) ck es in *)
(*             let vys := interp_vars_instant (SemSB.restr_hist H n) ys in *)
(*             let base := forallb (fun v => negb (v ==b absent)) ves in *)
(*             SemSB.sem_vars_instant (SemSB.restr_hist H n) ys vys *)
(*             /\ SemSB.sem_laexps_instant (bk n) (SemSB.restr_hist H n) ck es ves *)
(*             /\ (present_list ves <-> base = true) *)
(*             /\ SemSB.sem_vars_instant (SemSB.restr_hist H' n) (map fst (SynSB.b_in bl)) ves *)
(*             /\ SemSB.sem_vars_instant (SemSB.restr_hist H' n) (map fst (SynSB.b_out bl)) vys *)
(*             /\ SemSB.instant_same_clock ves *)
(*             /\ SemSB.instant_same_clock vys *)
(*             /\ (absent_list ves <-> absent_list vys) *)
(*       ) <-> *)
(*       SemSB.sem_equation P bk H M (SynSB.EqCall ys ck b i es). *)
(*   Proof. *)
(*     split. *)
(*     - intros ** (M' & bl & P' & H' & Find & Sub & Spec). *)
(*       apply SemSB.SEqCall with (M' := M') (ess := interp_laexps bk H ck es) (oss := interp_vars H ys); auto; *)
(*         try (intro; destruct (Spec n) as (?&?&?); eauto). *)
(*       unfold interp_laexps, interp_vars, lift, lift'. *)
(*       econstructor; eauto. *)
(*       + apply clock_of_equiv. *)
(*       + intro; destruct (Spec n) as (?&?&?&?&?); eauto. *)
(*       + intro; destruct (Spec n) as (?&?&?&?&?&?); eauto. *)
(*       + intro; destruct (Spec n) as (?&?&?&?&?&?&?); eauto. *)
(*       + intro; destruct (Spec n) as (?&?&?&?&?&?&?&?); eauto. *)
(*       + intro; destruct (Spec n) as (?&?&?&?&?&?&?&?); eauto. *)
(*       + admit. *)
(*         - admit. *)
(*     (* - inversion_clear 1 as [| | |??????????? Exps Sub Block Vars]. *) *)
(*     (*   split. *) *)
(*     (*   + econstructor; split; eauto. *) *)
(*     (*     rewrite <-interp_vars_sound, <-interp_laexps_sound; eauto. *) *)
(*     (*   + intro; specialize (Exps n); specialize (Vars n); simpl in *. *) *)
(*     (*     erewrite <-interp_vars_instant_sound, <-interp_laexps_instant_sound; eauto. *) *)
(*   Qed. *)

  (* Lemma reset_regs_instant_path: *)
  (*   forall n b M, *)
  (*     reset_regs_instant n b M -> *)
  (*     (forall x mvs, *)
  (*         find_val x M = Some mvs -> *)
  (*         b = true -> mvs.(SemSB.reset) n = true) *)
  (*     /\ (forall p M', *)
  (*           path_inst p M = Some M' -> *)
  (*           reset_regs_instant n b M'). *)
  (* Proof. *)
  (*   induction 1 as [?? Val Inst IH]; split; auto; intros ** Path. *)
  (*   induction p as [|x]; simpl in Path. *)
  (*   - inv Path; auto using reset_regs_instant. *)
  (*   - destruct (find_inst x M) eqn: E; try discriminate. *)
  (*     apply IH in E; destruct E; eauto. *)
  (* Qed. *)


  (* Lemma reset_memories_path_spec_instant: *)
  (*   forall k p r' Fm r n, *)
  (*     (r' = true -> r n = true) -> *)
  (*     reset_regs_instant n r' (reset_memories_path Fm r p (Fm k)). *)
  (* Proof. *)
  (*   intros ** Spec; unfold reset_memories_path. *)
  (*   revert dependent p. *)
  (*   induction (Fm k) as [?? IH] using memory_ind'; intros. *)
  (*   constructor. *)
  (*   - intros x mvs. *)
  (*     unfold reset_memories_path, find_val; simpl; rewrite Env.find_mapi. *)
  (*     intro Find. *)
  (*     destruct (Env.find x xvs); inv Find; auto. *)
  (*     simpl; intro; apply reset_reset_spec; auto. *)
  (*   - induction xms as [|[y]]. *)
  (*     + intros; discriminate. *)
  (*     + simpl in IH; inv IH. *)
  (*       intros x M'. *)
  (*       unfold sub_inst, find_inst. *)
  (*       simpl. *)
  (*       destruct (Env.POTB.compare x y); simpl; *)
  (*         intro Find; inv Find; eauto. *)
  (* Qed. *)

  (* Corollary reset_memories_path_sub_spec_instant: *)
  (*   forall p r' x M Fm r k n, *)
  (*     sub_inst x (Fm k) M -> *)
  (*     (r' = true -> r n = true) -> *)
  (*     reset_regs_instant n r' (reset_memories_path Fm r (p ++ [x]) M). *)
  (* Proof. *)
  (*   intros ** Sub Spec; eapply reset_memories_path_spec_instant with (k := k) in Spec. *)
  (*   inversion_clear Spec as [??? Inst]; eapply Inst, sub_inst_reset_memories_path; eauto. *)
  (* Qed. *)

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
          exists v, PM.find x (SemSB.restr_hist (Fh k) n) = Some v) ->
      incl xs xs' ->
      SemSB.sem_vars (Fh (count r n)) xs (mask (all_absent (xss 0)) (count r n) r xss) ->
      Forall2 (SemSB.sem_var_instant (SemSB.restr_hist (reset_history Fh r (Fh 0)) n)) xs (xss n).
  Proof.
    intros ** SameDomFh Incl Sem.
    unfold mask in Sem; specialize (Sem n); simpl in *.
    rewrite <-EqNat.beq_nat_refl in Sem.
    induction Sem as [|x ??? Sem]; constructor; auto.
    - clear IHSem.
      inversion_clear Sem as [?? Find]; constructor.
      assert (exists v, PM.find x (SemSB.restr_hist (Fh 0) n) = Some v)
        as (? & Find') by (apply SameDomFh, Incl; constructor; auto).
      unfold SemSB.restr_hist, reset_history, PM.map in *.
      repeat rewrite PM.gmapi in *; rewrite option_map_map.
      destruct (PM.find x (Fh (count r n))); try discriminate.
      destruct (PM.find x (Fh 0)); try discriminate; auto.
    - apply IHSem; intros x' **.
      apply Incl; right; auto.
  Qed.

  Lemma sem_laexps_interp_mask:
    forall xss r Fh ck es k bk' ess,
      let H := reset_history Fh r (Fh 0) in
      let bk := SemSB.clock_of' xss in
      SemSB.clock_of (mask (all_absent (xss 0)) k r xss) bk' ->
      SemSB.sem_laexps bk' (Fh k) ck es ess ->
      ess ≈ mask (all_absent (interp_laexps bk H ck es 0)) k r (interp_laexps bk H ck es).
  Proof.
    intros ** Clock Exps n.
    specialize (Exps n); simpl in Exps.
    destruct (EqNat.beq_nat k (count r n)) eqn: E.
    - apply EqNat.beq_nat_true in E; subst k.
      rewrite mask_transparent; auto.
      eapply interp_laexps_instant_sound, sem_laexps_instant_reset; eauto.
    - apply EqNat.beq_nat_false in E.
      specialize (Clock n).
      rewrite mask_opaque; rewrite mask_opaque in Clock; auto.
      inversion_clear Exps as [?????? SemCk|??? Eq|].
      + assert (bk' n = false) as Hbk'.
        { apply Bool.not_true_is_false; intro Eq.
          apply Clock in Eq.
          admit.
        }
        rewrite Hbk' in *.
        contradict SemCk; apply SemSB.not_subrate_clock.
      + rewrite Eq.
        unfold interp_laexps, lift, interp_laexps_instant.
        destruct (forallb (fun v : value => v ==b absent) (interp_lexps_instant (bk 0) (SemSB.restr_hist H 0) es)
                          && negb (interp_clock_instant (bk 0) (SemSB.restr_hist H 0) ck)
                  || forallb (fun v : value => v <>b absent) (interp_lexps_instant (bk 0) (SemSB.restr_hist H 0) es)
                            && interp_clock_instant (bk 0) (SemSB.restr_hist H 0) ck);
          unfold interp_lexps_instant; rewrite all_absent_map; auto.
        unfold all_absent at 3; rewrite all_absent_map; auto.
      + unfold interp_laexps, lift, interp_laexps_instant; simpl.
        destruct (negb (interp_clock_instant (bk 0) (SemSB.restr_hist H 0) ck)
                  || interp_clock_instant (bk 0) (SemSB.restr_hist H 0) ck); auto.
  Qed.

  Lemma sem_vars_interp_mask:
    forall r Fh xs k ess oss oss0,
      let H := reset_history Fh r (Fh 0) in
      SemSB.sem_vars (Fh k) xs oss ->
      SemSB.sem_vars (Fh 0) xs oss0 ->
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
      subst H; unfold reset_history; unfold SemSB.restr_hist, PM.map in *.
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

  Ltac interp_sound n :=
    repeat match goal with
           | H: SemSB.sem_var ?H' ?x ?vs |- _ =>
             specialize (H n); apply sem_var_instant_reset in H
           | H: SemSB.sem_vars ?H' ?xs ?vss |- _ =>
             specialize (H n); apply sem_vars_instant_reset in H
           | H: SemSB.sem_caexp ?bk ?H' ?c ?e ?vs |- _ =>
             specialize (H n); simpl in H; eapply sem_caexp_instant_reset in H; eauto
           | H: SemSB.sem_laexp ?bk ?H' ?c ?e ?vs |- _ =>
             specialize (H n); simpl in H; eapply sem_laexp_instant_reset in H; eauto
           | H: SemSB.sem_laexps ?bk ?H' ?c ?es ?vss |- _ =>
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
    forall G f r xss oss Fm P,
      Ordered_nodes G ->
      (forall k,
          SemSB.sem_block (translate G) f (Fm k)
                          (mask (all_absent (xss 0)) k r xss)
                          (mask (all_absent (oss 0)) k r oss)
          /\ P k (Fm k)) ->
      SemSB.sem_block (translate G) f (reset_memories Fm r (Fm 0)) xss oss
      /\ forall k, P k (Fm k).
  Proof.
    intros ** Ord Sem.
    revert dependent f; revert xss oss r P Fm.
    induction G as [|node]; intros.
    destruct (Sem 0) as (Sem'); inv Sem';
      match goal with Hf: SynSB.find_block _ _ = _ |- _ => inversion Hf end.

    pose proof Ord as Ord'.
    inversion_clear Ord as [|?? Ord'' Hnneqs Hnn].

    assert (forall k, P k (Fm k)) as HP by (intro; destruct (Sem k); auto).

    split; auto.

    assert (exists bl P', SynSB.find_block f (translate (node :: G)) = Some (bl, P'))
      as (bl & P' & Find)
        by (destruct (Sem 0) as (Sem'); inv Sem'; eauto).

    assert (forall k k', same_skeleton (Fm k) (Fm k')) as SameSkeleton
        by (intros; pose proof (Sem k) as Sk; specialize (Sem k');
            destruct Sk, Sem; eapply sem_block_same_skeleton; eauto).

    assert (exists F, forall k, exists bk,
                   SemSB.sem_vars (F k) (map fst (SynSB.b_in bl)) (mask (all_absent (xss 0)) k r xss)
                   /\ SemSB.sem_vars (F k) (map fst (SynSB.b_out bl)) (mask (all_absent (oss 0)) k r oss)
                   /\ Forall (SemSB.sem_equation (translate (node :: G)) bk (F k) (Fm k)) (SynSB.b_eqs bl)
                   /\ SemSB.clock_of (mask (all_absent (xss 0)) k r xss) bk)
      as (Fh & Spec).
    { assert (forall k, exists H bk,
                   SemSB.sem_vars H (map fst (SynSB.b_in bl)) (mask (all_absent (xss 0)) k r xss)
                   /\ SemSB.sem_vars H (map fst (SynSB.b_out bl)) (mask (all_absent (oss 0)) k r oss)
                   /\ Forall (SemSB.sem_equation (translate (node :: G)) bk H (Fm k)) (SynSB.b_eqs bl)
                   /\ SemSB.clock_of (mask (all_absent (xss 0)) k r xss) bk)
        as Spec.
      { intro; destruct (Sem k) as (Sem'); inv Sem'.
        match goal with
          H: SynSB.find_block _ _ = _ |- _ => rewrite Find in H; inv H end.
        eauto 6.
      }
      now apply functional_choice in Spec.
    }

    assert (forall x k n,
               In x (map fst (SynSB.bl_vars bl)) ->
               exists v, PM.find x (SemSB.restr_hist (Fh k) n) = Some v)
      as SameDomFh.
    { clear - Spec.
      intros ** Hin; unfold SynSB.bl_vars in Hin; do 2 rewrite map_app in Hin.
      apply in_app in Hin as [Hin|Hin]; [|apply in_app in Hin as [Hin|Hin]].
      - destruct (Spec k) as (?& In & ?).
        specialize (In n); simpl in *.
        eapply Forall2_In_l in In as (?& Sem); eauto.
        inv Sem; eauto.
      - destruct (Spec k) as (?&?& Out &?).
        specialize (Out n); simpl in *.
        eapply Forall2_In_l in Out as (?& Sem); eauto.
        inv Sem; eauto.
      - admit.
    }

    eapply SemSB.SBlock with (H := reset_history Fh r (Fh 0)); eauto.
    - apply SemSB.clock_of_equiv.
    - intro; destruct (Spec (count r n)) as (?& In & ?).
      eapply sem_var_instant_bl_vars; eauto.
      intros ? Hin.
      unfold SynSB.bl_vars; rewrite map_app, in_app; auto.
    - intro; destruct (Spec (count r n)) as (?&?& Out &?).
      eapply sem_var_instant_bl_vars; eauto.
      intros ? Hin.
      unfold SynSB.bl_vars; rewrite 2 map_app, 2 in_app; auto.
    - intro; destruct (Sem (count r n)) as (Sem'); inversion_clear Sem' as [???????????? Same].
      specialize (Same n); rewrite mask_transparent in Same; auto.
    - intro; destruct (Sem (count r n)) as (Sem'); inversion_clear Sem' as [????????????? Same].
      specialize (Same n); rewrite mask_transparent in Same; auto.
    - intro; destruct (Sem (count r n)) as (Sem'); inversion_clear Sem' as [?????????????? AbsAbs].
      specialize (AbsAbs n); rewrite 2 mask_transparent in AbsAbs; auto.
    - induction (SynSB.b_eqs bl) as [|eq ? IHeqs]; constructor; auto.
      + clear IHeqs.
        assert (forall k, exists bk, SemSB.sem_equation (translate (node :: G)) bk (Fh k) (Fm k) eq
                           /\ SemSB.clock_of (mask (all_absent (xss 0)) k r xss) bk)
          as Spec'
            by (intros; destruct (Spec k) as (?&?&?& Heq &?); inv Heq; eauto).
        clear Spec.
        set (bk := SemSB.clock_of' xss).
        set (H := reset_history Fh r (Fh 0)).

        destruct eq.

        * assert (forall k, PM.find i (Fh k) <> None) by admit.
          apply SemSB.SEqDef with (xs := interp_caexp bk H c c0);
            intro; destruct (Spec' (count r n)) as (?& Heq &?); inv Heq;
              interp_sound n.

        *{ assert (forall k, PM.find i (Fh k) <> None) as Hfind by admit.
           apply SemSB.SEqFby with (xs := interp_var H i) (ls := interp_laexp bk H c l0);
             try (intro; destruct (Spec' (count r n)) as (?& Heq &?); inv Heq; interp_sound n).
           assert (exists F, forall k, exists bk xs ls,
                          SemSB.sem_var (Fh k) i xs
                          /\ SemSB.sem_laexp bk (Fh k) c l0 ls
                          /\find_val i (Fm k) = Some (F k)
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
                          /\ SemSB.clock_of (mask (all_absent (xss 0)) k r xss) bk)
             as (Fmvs & Spec).
           { assert (forall k, exists mvs bk xs ls,
                          SemSB.sem_var (Fh k) i xs
                          /\ SemSB.sem_laexp bk (Fh k) c l0 ls
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
                          /\ SemSB.clock_of (mask (all_absent (xss 0)) k r xss) bk) as Spec.
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
           - clear - Spec Hfind.
             intro; destruct (Spec (count r n)) as (?&?&?&?&?&?&?& Heq &?).
             pose proof (reset_mvalues_spec _ _ _ _ _ _ _ _ _ Spec (S n)) as Spec'.
             clear Spec.
             interp_sound n.
             specialize (Heq n).
             destruct (r (S n)) eqn: E; [rewrite Spec'; auto|];
               simpl; rewrite E; simpl; auto.
             destruct (x1 n); intuition.
         }

        *{ assert (forall k, PM.find i1 (Fh k) <> None) by admit.
           assert (exists M0, sub_inst i0 (Fm 0) M0) as (M0 & Find0)
               by (destruct (Spec' 0) as (?& Heq & ?); inv Heq; eauto).
           apply SemSB.SEqReset with (rs := interp_var H i1) (M' := reset_memories_path Fm r [i0] M0).
           - intro; destruct (Spec' (count r n)) as (?& Heq &?); inv Heq; interp_sound n.
           - now apply sub_inst_reset_memories_path.
           - rewrite reset_regs_instant_spec.
             intro; destruct (Spec' (count r n)) as (?& Heq &?); inversion_clear Heq as [| |????????? Var|].
             eapply reset_memories_path_sub_spec_instant'; eauto.
             + eapply same_skeleton_sub_inst; eauto.
             + replace (SemSB.reset_of (interp_var H i1) n) with (SemSB.reset_of_value (interp_var H i1 n)); auto.
               interp_sound n.
               replace (SemSB.reset_of_value (rs n)) with (SemSB.reset_of rs n); auto.
               apply reset_regs_instant_spec'; auto.
         }

        *{ assert (Forall (fun x => forall k, PM.find x (Fh k) <> None) i) by admit.
           assert (exists F, forall k,
                        SemSB.sem_block (translate G) i0
                                        (F k)
                                        (mask (all_absent (interp_laexps bk H c l0 0)) k r (interp_laexps bk H c l0))
                                        (mask (all_absent (interp_vars H i 0)) k r (interp_vars H i))
                        /\ sub_inst i1 (Fm k) (F k)) as (F & Spec).
           { assert (forall k, exists M bk ess oss,
                          SemSB.sem_laexps bk (Fh k) c l0 ess
                          /\ sub_inst i1 (Fm k) M
                          /\ SemSB.sem_block (translate (node :: G)) i0 M ess oss
                          /\ SemSB.sem_vars (Fh k) i oss
                          /\ SemSB.clock_of (mask (all_absent (xss 0)) k r xss) bk) as Spec.
             { intro; destruct (Spec' k) as (?& Heq & Clock);
                 inversion_clear Heq as [| | |???? M' ?????? Exps ? Block Vars]; eauto 9.
             }
             apply functional_choice in Spec as (F & Spec).
             exists F; intro; destruct (Spec k) as (?&?&?& Exps & ? & Block & Vars & ?).

             erewrite sem_laexps_interp_mask in Block; eauto.
             pose proof Block as Block'; inversion_clear Block' as [?????????????? Same].
             destruct (Spec' 0) as (?& Heq &?); inv Heq.
             erewrite sem_vars_interp_mask with (1 := Vars) (r := r) in Block; eauto.
             - split; auto.
               eapply sem_block_cons; eauto.
               admit.
             - intros ** E; apply Same.
               rewrite mask_opaque; auto.
               apply all_absent_spec.
           }
           edestruct (IHG Ord'' (interp_laexps bk H c l0) (interp_vars H i) r (fun k M => sub_inst i1 (Fm k) M))
             as (?& Sub); eauto.
           eapply SemSB.SEqCall with (M' := reset_memories F r (F 0))
                                     (ess := interp_laexps bk H c l0)
                                     (oss := interp_vars H i).
           - intro; destruct (Spec' (count r n)) as (?& Heq &?); inv Heq; interp_sound n.
           - now apply sub_inst_reset_memories.
           - apply sem_block_cons2; auto.
           - intro; destruct (Spec' (count r n)) as (?& Heq &?); inv Heq; interp_sound n.
         }

      + apply IHeqs.
        intro; destruct (Spec k) as (?&?&?& Heqs &?); inv Heqs; eauto.
  Qed.

  Theorem reset_correctness:
    forall G f r xss oss,
      Ordered_nodes G ->
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
    edestruct (slices_sem_block G f r xss oss Fm (fun _ _ => True)); eauto.
  Qed.

  Theorem correctness:
    forall G f xss oss,
      (* Welldef_global G -> *)
      Ordered_nodes G ->
      sem_node G f xss oss ->
      exists M, SemSB.sem_block (translate G) f M xss oss.
  Proof.
    induction G as [|node].
    inversion 2;
      match goal with Hf: find_node _ [] = _ |- _ => inversion Hf end.
    intros ** Hord Hsem.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [??????? Hfind ????? Heqs].
    (* pose proof (Welldef_global_Ordered_nodes _ Hwdef) as Hord. *)
    (* pose proof (Welldef_global_cons _ _ Hwdef) as HwdefG. *)
    pose proof (find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    simpl in Hfind.
    destruct (ident_eqb node.(n_name) f) eqn:Hnf.
    - assert (Hord':=Hord).
      inversion_clear Hord as [|? ? Hord'' Hnneqs Hnn].
      injection Hfind; intro HR; rewrite HR in *; clear HR; simpl in *.
      eapply Forall_sem_equation_global_tl in Heqs; eauto.
      assert (forall f xss oss,
                 sem_node G f xss oss ->
                 exists M, SemSB.sem_block (translate G) f M xss oss)
        as IHG' by auto.

      assert (forall f r xss oss,
                 sem_reset G f r xss oss ->
                 exists M, SemSB.sem_block (translate G) f M xss oss
                      /\ SemSB.reset_regs r M).
      { clear - IHG' Hord''.
        intros; apply reset_correctness; auto.
      }

      assert (exists M', Forall (SemSB.sem_equation (translate G) bk H M') (translate_eqns n.(n_eqs)))
        as (M & Hmsem).
      { eapply equations_correctness; eauto.
        admit.
      }
      exists M.
      econstructor; eauto.
      + simpl; now rewrite Hnf.
      + simpl; rewrite map_fst_idty; eauto.
      + simpl; rewrite map_fst_idty; eauto.
      + eapply sem_equation_cons; eauto.
    - apply ident_eqb_neq in Hnf.
      apply sem_node_cons with (1:=Hord) (3:=Hnf) in Hsem.
      inv Hord.
      eapply IHG in Hsem as [M]; eauto.
      exists M.
      now eapply sem_block_cons2; eauto.
  Qed.
