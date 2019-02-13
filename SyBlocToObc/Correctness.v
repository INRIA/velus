Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.RMemory.

Require Import Velus.NLustre.NLExprSyntax.
Require Import Velus.NLustre.Stream.
Require Import Velus.NLustre.NLExprSemantics.
Require Import Velus.SyBloc.SBSyntax.
Require Import Velus.SyBloc.SBSemantics.

Require Import Velus.Obc.ObcSyntax.
Require Import Velus.Obc.ObcSemantics.

Require Import Velus.NLustre.NLSyntax.
Require Export Velus.NLustre.IsFree.

Require Import Velus.SyBlocToObc.Translation.

Require Import List.
Import List.ListNotations.
Require Import Setoid.

(* Open Scope positive. *)
Open Scope nat.
Open Scope list.

Module Type CORRECTNESS
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import OpAux   : OPERATORS_AUX       Op)
       (Import Clks    : CLOCKS          Ids)
       (Import ExprSyn : NLEXPRSYNTAX        Op)
       (SynNL          : NLSYNTAX        Ids Op       Clks ExprSyn)
       (Import SynSB   : SBSYNTAX        Ids Op       Clks ExprSyn)
       (Import Str     : STREAM              Op OpAux)
       (Import ExprSem : NLEXPRSEMANTICS Ids Op OpAux Clks ExprSyn              Str)
       (Import SemSB   : SBSEMANTICS     Ids Op OpAux Clks ExprSyn SynSB        Str ExprSem)
       (Import SynObc  : OBCSYNTAX       Ids Op OpAux)
       (Import SemObc  : OBCSEMANTICS    Ids Op OpAux                    SynObc)
       (Import Trans   : TRANSLATION     Ids Op OpAux Clks ExprSyn SynSB SynObc)
       (Import IsF     : ISFREE          Ids Op       Clks ExprSyn SynNL).

  Section MemoryCorres.

    Variable P: SynSB.program.

    Inductive Memory_Corres: ident -> state -> menv -> Prop :=
      MemC:
        forall b S me bl P',
          find_block b P = Some (bl, P') ->
          Forall (Memory_Corres_eq S me) bl.(b_eqs) ->
          Memory_Corres b S me

    with Memory_Corres_eq: state -> menv -> equation -> Prop :=
         | MemC_EqDef:
             forall S me x ck e,
               Memory_Corres_eq S me (EqDef x ck e)
         | MemC_EqNext:
             forall S me x ck e,
               (forall v, find_val x S = Some v ->
                     find_val x me = Some v) ->
               Memory_Corres_eq S me (EqNext x ck e)
         | MemC_EqReset:
             forall S me s ck b,
               (forall Ss, sub_inst s S Ss ->
                    exists me', sub_inst s me me') ->
               Memory_Corres_eq S me (EqReset s ck b)
         | MemC_EqCall:
           forall S me s xs ck rst b es,
             (forall Ss, sub_inst s S Ss ->
                    exists me', sub_inst s me me'
                           /\ Memory_Corres b Ss me') ->
             Memory_Corres_eq S me (EqCall s xs ck rst b es).

    Definition Memory_Corres_eqs (S: state) (me: menv) (eqs: list equation) :=
      Forall (Memory_Corres_eq S me) eqs.

    Section MemoryCorresMult.

      Variable P_block: ident -> state -> menv -> Prop.
      Variable P_equation: state -> menv -> equation -> Prop.

      Hypothesis EqDef_case:
        forall S me x ck e,
          P_equation S me (EqDef x ck e).

      Hypothesis EqNext_case:
        forall S me x ck e,
          (forall v, find_val x S = Some v ->
                find_val x me = Some v) ->
          P_equation S me (EqNext x ck e).

      Hypothesis EqReset_case:
        forall S me s ck b,
          (forall Ss, sub_inst s S Ss ->
                 exists me', sub_inst s me me') ->
          P_equation S me (EqReset s ck b).

      Hypothesis EqCall_case:
        forall S me s xs ck rst b es,
          (forall Ss, sub_inst s S Ss ->
                 exists me', sub_inst s me me'
                        /\ Memory_Corres b Ss me'
                        /\ P_block b Ss me') ->
          P_equation S me (EqCall s xs ck rst b es).

      Hypothesis MemC_case:
        forall b S me bl P',
          find_block b P = Some (bl, P') ->
          Forall (Memory_Corres_eq S me) bl.(b_eqs) ->
          Forall (P_equation S me) bl.(b_eqs) ->
          P_block b S me.

      Fixpoint Memory_Corres_mult
               (b: ident) (S: state) (me: menv)
               (Hmc: Memory_Corres b S me):
        P_block b S me
      with Memory_Corres_eq_mult
             (S: state) (me: menv) (eq: equation)
             (Hmceq: Memory_Corres_eq S me eq):
             P_equation S me eq.
      Proof.
        - destruct Hmc. eauto.
          eapply MemC_case; eauto.
          match goal with H: Forall _ _ |- _ => induction H; auto end.
        - destruct Hmceq as [| | |???????? Spec]; eauto.
          apply EqCall_case.
          intros ** Sub; apply Spec in Sub as (?&?&?); eauto.
      Qed.

    End MemoryCorresMult.

  End MemoryCorres.

  Lemma Memory_Corres_eqs_add_val:
    forall P S me x v eqs,
      find_val x S = Some v ->
      Memory_Corres_eqs P S me eqs ->
      Memory_Corres_eqs P S (add_val x v me) eqs.
  Proof.
    unfold Memory_Corres_eqs.
    induction eqs as [|eq]; auto.
    intros Find; inversion_clear 1 as [|?? Corres].
    constructor; auto.
    destruct eq; constructor; inv Corres; eauto.
    intros ** Find'.
    destruct (ident_eq_dec i x).
    - subst; rewrite find_val_gss; congruence.
    - rewrite find_val_gso; auto.
  Qed.

  Definition equiv_env (in_domain: ident -> Prop) (R: env) (mems: PS.t) (me: menv) (ve: venv) : Prop :=
    forall x c,
      in_domain x ->
      sem_var_instant R x (present c) ->
      if PS.mem x mems
      then find_val x me = Some c
      else Env.find x ve = Some c.

  Lemma equiv_env_map:
    forall (in_dom1 in_dom2: ident -> Prop) R mems me ve,
      (forall x, in_dom2 x -> in_dom1 x) ->
      equiv_env in_dom1 R mems me ve ->
      equiv_env in_dom2 R mems me ve.
  Proof.
    unfold equiv_env; intros ** Eq ????; apply Eq; auto.
  Qed.

  Ltac weaken_equiv_env_with tac :=
    match goal with
      H: equiv_env ?in_dom1 ?R ?mems ?me ?ve
      |- equiv_env ?in_dom2 ?R ?mems ?me ?ve =>
      eapply equiv_env_map; [|exact H]; tac
    end.

  Tactic Notation "weaken_equiv_env" "with" tactic(tac) :=
    weaken_equiv_env_with tac.

  Tactic Notation "weaken_equiv_env" :=
    weaken_equiv_env with constructor (now auto).

  Hint Extern 4 (equiv_env _ _ _ _ _) => weaken_equiv_env.

  Inductive Is_defined_in_eq: ident -> equation -> Prop :=
  | DefEqDef:
      forall x ck e,
        Is_defined_in_eq x (EqDef x ck e)
  | DefEqNext:
      forall x ck e,
        Is_defined_in_eq x (EqNext x ck e)
  | DefEqCall:
      forall x s xs ck rst b es,
        In x xs ->
        Is_defined_in_eq x (EqCall s xs ck rst b es).

  Definition Is_defined_in_eqs (x: ident) (eqs: list equation) : Prop :=
    Exists (Is_defined_in_eq x) eqs.

  Inductive Is_variable_in_eq: ident -> equation -> Prop :=
  | VarEqDef:
      forall x ck e,
        Is_variable_in_eq x (EqDef x ck e)
  | VarEqCall:
      forall x s xs ck rst b es,
        In x xs ->
        Is_variable_in_eq x (EqCall s xs ck rst b es).

  Definition Is_variable_in_eqs (x: ident) (eqs: list equation) : Prop :=
    Exists (Is_variable_in_eq x) eqs.

  Inductive Is_state_in_eq: ident -> equation -> nat -> Prop :=
  | StateEqReset:
      forall s ck b,
        Is_state_in_eq s (EqReset s ck b) 0
  | StateEqCall:
      forall s xs ck rst b es,
        Is_state_in_eq s (EqCall s xs ck rst b es) 1.

  Inductive Is_free_in_eq: ident -> equation -> Prop :=
  | FreeEqDef:
      forall x ck e y,
        Is_free_in_caexp y ck e ->
        Is_free_in_eq y (EqDef x ck e)
  | FreeEqNext:
      forall x ck e y,
        Is_free_in_laexp y ck e ->
        Is_free_in_eq y (EqNext x ck e)
  | FreeEqReset:
      forall s ck b x,
        Is_free_in_clock x ck ->
        Is_free_in_eq x (EqReset s ck b)
  | FreeEqCall:
      forall s x ck rst b es y,
        Is_free_in_laexps y ck es ->
        Is_free_in_eq y (EqCall s x ck rst b es).

  Inductive Is_well_sch (inputs: list ident) (mems: PS.t): list equation -> Prop :=
  | WSchNil:
      Is_well_sch inputs mems []
  | WSchEq:
      forall eq eqs,
        Is_well_sch inputs mems eqs ->
        (forall x,
            Is_free_in_eq x eq ->
            if PS.mem x mems
            then ~ Is_defined_in_eqs x eqs
            else Is_variable_in_eqs x eqs \/ In x inputs) ->
        (forall x, Is_defined_in_eq x eq -> ~ Is_defined_in_eqs x eqs) ->
        (forall s k,
            Is_state_in_eq s eq k ->
            Forall (fun eq => forall k', Is_state_in_eq s eq k' -> k' < k) eqs) ->
        Is_well_sch inputs mems (eq :: eqs).

  (* Section BuildMemWith. *)

  (*   Context {A B V: Type}. *)
  (*   Variable f: A -> V. *)
  (*   Variable g: ident * B -> memory V. *)

  (*   Definition build_mem_with (xs: list (ident * A)) (ys: list (ident * B)) (m: memory V): memory V := *)
  (*     fold_left (fun m x => add_inst (fst x) (g x) m) ys *)
  (*               (fold_left (fun m y => add_val (fst y) (f (snd y)) m) xs m). *)

  (*   Definition build_mem_with_spec (xs: list (ident * A)) (ys: list (ident * B)) (m: memory V): memory V := *)
  (*     let (xs, vs) := split xs in *)
  (*     let (ys', ws) := split ys in *)
  (*     Mem (Env.adds xs (map f vs) (values m)) (Env.adds ys' (map g ys) (instances m)). *)

  (*   Lemma build_mem_with_spec_values: *)
  (*     forall xs ys m, *)
  (*       values (build_mem_with_spec xs ys m) = *)
  (*       let (xs, vs) := split xs in *)
  (*       Env.adds xs (map f vs) (values m). *)
  (*   Proof. *)
  (*     intros; unfold build_mem_with_spec; destruct (split xs), (split ys); auto. *)
  (*   Qed. *)

  (*   Lemma build_mem_with_spec_instances: *)
  (*     forall xs ys m, *)
  (*       instances (build_mem_with_spec xs ys m) = *)
  (*       let (ys', ws) := split ys in *)
  (*       Env.adds ys' (map g ys) (instances m). *)
  (*   Proof. *)
  (*     intros; unfold build_mem_with_spec; destruct (split xs), (split ys); auto. *)
  (*   Qed. *)

  (*   Lemma build_mem_with_equal: *)
  (*     forall ys xs m, *)
  (*       NoDupMembers ys -> *)
  (*       NoDupMembers xs -> *)
  (*       build_mem_with xs ys m ≋ build_mem_with_spec xs ys m. *)
  (*   Proof. *)
  (*     unfold build_mem_with, build_mem_with_spec. *)
  (*     induction ys as [|(y, b)]; intros ** NoDup_ys NoDup_xs; simpl. *)
  (*     - rewrite Env.adds_nil_nil. *)
  (*       revert m. *)
  (*       induction xs as [|(x, a)]; intro; simpl. *)
  (*       + now rewrite Env.adds_nil_nil. *)
  (*       + inversion_clear NoDup_xs as [|??? Notin]. *)
  (*         rewrite IHxs; auto. *)
  (*         destruct (split xs) eqn: E; simpl. *)
  (*         rewrite Env.adds_cons_cons; try reflexivity. *)
  (*         replace l with (fst (split xs)); [|now rewrite E]. *)
  (*         intro Hin; apply Notin. *)
  (*         apply in_split_l' in Hin as (?&?). *)
  (*         eapply In_InMembers; eauto. *)
  (*     - destruct (split xs) eqn: Exs, (split ys) as (l') eqn: Eys; simpl in *. *)
  (*       inversion_clear NoDup_ys as [|??? Notin]. *)
  (*       rewrite Env.adds_cons_cons. *)
  (*       + set (m' := add_inst y (g (y, b)) m). *)
  (*         change (Env.add y (g (y, b)) (instances m)) with (instances m'); *)
  (*           change (values m) with (values m'). *)
  (*         apply (IHys _ m') in NoDup_xs; auto. *)
  (*         rewrite Exs in NoDup_xs. *)
  (*         rewrite <-NoDup_xs. *)
  (*         subst m'; clear; revert m. *)
  (*         induction xs as [|(x', a')]; intros; simpl; try reflexivity. *)
  (*         rewrite IHxs. *)
  (*         now rewrite add_inst_val_comm. *)
  (*       + replace l' with (fst (split ys)); [|now rewrite Eys]. *)
  (*         intro Hin; apply Notin. *)
  (*         apply in_split_l' in Hin as (?&?). *)
  (*         eapply In_InMembers; eauto. *)
  (*   Qed. *)

  (* End BuildMemWith. *)

  (* Add Parametric Morphism A B V f xs ys m: (fun g => @build_mem_with_spec A B V f g xs ys m) *)
  (*     with signature (fun g g' => forall x, g x ≋ g' x) ==> equal_memory *)
  (*       as build_mem_with_spec_rec_equal_memory. *)
  (* Proof. *)
  (*   intros g g' E. *)
  (*   unfold build_mem_with_spec. *)
  (*   induction ys as [|(y, b)]; simpl; try reflexivity. *)
  (*   destruct (split ys); simpl. *)
  (*   unfold Env.adds. simpl. *)
  (*   destruct (split xs); simpl. *)
  (*   constructor; try reflexivity. *)
  (*   simpl. *)
  (*   inversion_clear IHys as [??? Insts]. *)
  (*   unfold Env.adds in Insts; simpl in Insts. *)
  (*   now rewrite E, Insts. *)
  (* Qed. *)

  (* Fixpoint reset_state_spec (P: SynSB.program) (me: menv) (b: ident) : menv := *)
  (*   let reset_state_spec_aux (P: SynSB.program) (me: menv) (xb: ident * ident) := *)
  (*       reset_state_spec P match find_inst (fst xb) me with *)
  (*                          | Some me' => me' *)
  (*                          | None => mempty *)
  (*                          end (snd xb) *)
  (*   in *)
  (*   match P with *)
  (*   | [] => me *)
  (*   | bl :: P => *)
  (*     if ident_eqb (b_name bl) b *)
  (*     then build_mem_with_spec sem_const (reset_state_spec_aux P me) (b_lasts bl) (b_blocks bl) me *)
  (*     else reset_state_spec P me b *)
  (*   end. *)

  (* Definition reset_state_spec_aux (P: SynSB.program) (me: menv) (xb: ident * ident) : menv := *)
  (*   reset_state_spec P match find_inst (fst xb) me with *)
  (*                      | Some me' => me' *)
  (*                      | None => mempty *)
  (*                      end (snd xb). *)

  (* Fixpoint reset_state (P: SynSB.program) (me: menv) (b: ident) : menv := *)
  (*   let reset_state_aux (P: SynSB.program) (me: menv) (xb: ident * ident) := *)
  (*       reset_state P match find_inst (fst xb) me with *)
  (*                          | Some me' => me' *)
  (*                          | None => mempty *)
  (*                          end (snd xb) *)
  (*   in *)
  (*   match P with *)
  (*   | [] => me *)
  (*   | bl :: P => *)
  (*     if ident_eqb (b_name bl) b *)
  (*     then build_mem_with sem_const (reset_state_aux P me) (b_lasts bl) (b_blocks bl) me *)
  (*     else reset_state P me b *)
  (*   end. *)

  (* Definition reset_state_aux (P: SynSB.program) (me: menv) (xb: ident * ident) : menv := *)
  (*   reset_state P match find_inst (fst xb) me with *)
  (*                 | Some me' => me' *)
  (*                 | None => mempty *)
  (*                 end (snd xb). *)

  (* Lemma reset_state_equal: *)
  (*   forall P me b, *)
  (*     reset_state P me b ≋ reset_state_spec P me b. *)
  (* Proof. *)
  (*   induction P as [|bl]; intros; simpl; try reflexivity. *)
  (*   destruct (ident_eqb (b_name bl) b); auto. *)
  (*   rewrite (build_mem_with_spec_rec_equal_memory _ _ _ _ _ _ _ _ (reset_state_aux P me)). *)
  (*   - apply build_mem_with_equal. *)
  (*     + apply b_nodup_blocks. *)
  (*     + apply b_nodup_lasts. *)
  (*   - now setoid_rewrite IHP. *)
  (* Qed. *)

  (* Lemma reset_state_spec_find_Some: *)
  (*   forall P me b P' bl, *)
  (*     find_block b P = Some (bl, P') -> *)
  (*     reset_state_spec P me b = build_mem_with_spec sem_const *)
  (*                                                   (reset_state_spec_aux P' me) *)
  (*                                                   (b_lasts bl) (b_blocks bl) *)
  (*                                                   me. *)
  (* Proof. *)
  (*   intros ** Find. *)
  (*   induction P as [|bl']. *)
  (*   - inv Find. *)
  (*   - simpl in *. *)
  (*     destruct (ident_eqb (b_name bl') b); auto. *)
  (*     inv Find; auto. *)
  (* Qed. *)

  (* Lemma reset_state_spec_find_None: *)
  (*   forall P me b, *)
  (*     find_block b P = None -> *)
  (*     reset_state_spec P me b = me. *)
  (* Proof. *)
  (*   intros ** Find. *)
  (*   induction P as [|bl']; simpl in *; auto. *)
  (*   destruct (ident_eqb (b_name bl') b); try discriminate; auto. *)
  (* Qed. *)

  (* Lemma reset_state_find_Some: *)
  (*   forall P me b P' bl, *)
  (*     find_block b P = Some (bl, P') -> *)
  (*     reset_state P me b = build_mem_with sem_const *)
  (*                                         (reset_state_aux P' me) *)
  (*                                         (b_lasts bl) (b_blocks bl) *)
  (*                                         me. *)
  (* Proof. *)
  (*   intros ** Find. *)
  (*   induction P as [|bl']. *)
  (*   - inv Find. *)
  (*   - simpl in *. *)
  (*     destruct (ident_eqb (b_name bl') b); auto. *)
  (*     inv Find; auto. *)
  (* Qed. *)

  (* Lemma reset_state_find_None: *)
  (*   forall P me b, *)
  (*     find_block b P = None -> *)
  (*     reset_state P me b = me. *)
  (* Proof. *)
  (*   intros ** Find. *)
  (*   induction P as [|bl']; simpl in *; auto. *)
  (*   destruct (ident_eqb (b_name bl') b); try discriminate; auto. *)
  (* Qed. *)

  (* Lemma find_val_reset_state_spec: *)
  (*   forall P me b bl P', *)
  (*     find_block b P = Some (bl, P') -> *)
  (*     (forall x, find_val x me <> None -> InMembers x (b_lasts bl)) -> *)
  (*     (forall x c, *)
  (*         In (x, c) (b_lasts bl) -> *)
  (*         find_val x (reset_state_spec P me b) = Some (sem_const c)) *)
  (*     /\ *)
  (*     forall x v, *)
  (*       find_val x (reset_state_spec P me b) = Some v -> *)
  (*       exists c, v = sem_const c /\ In (x, c) (b_lasts bl). *)
  (* Proof. *)
  (*   intros ** Spec_me. *)
  (*   unfold find_val in *. *)
  (*   erewrite reset_state_spec_find_Some; eauto. *)
  (*   rewrite build_mem_with_spec_values. *)
  (*   pose proof (b_nodup_lasts_blocks bl) as NoDup. *)
  (*   apply NoDup_app_weaken in NoDup. *)
  (*   split; intros ** Hx. *)
  (*   - destruct (split (b_lasts bl)) eqn: E. *)
  (*     rewrite <-split_fst_map, E in NoDup; auto. *)
  (*     apply Env.In_find_adds; auto. *)
  (*     rewrite combine_map_snd. *)
  (*     pose proof (split_combine (b_lasts bl)) as Eq. *)
  (*     rewrite E in Eq. *)
  (*     apply in_map_iff. *)
  (*     setoid_rewrite Eq. *)
  (*     exists (x, c); auto. *)
  (*   - destruct (Env.find x (values me)) eqn: Find. *)
  (*     + assert (InMembers x (b_lasts bl)) as Hin *)
  (*           by (apply Spec_me; rewrite Find; discriminate). *)
  (*       clear Spec_me. *)
  (*       induction (b_lasts bl) as [|(x', c')]; simpl in *. *)
  (*       * inv Hin. *)
  (*       *{ destruct (split l) eqn: El. *)
  (*          destruct Hin; simpl in *. *)
  (*          - subst; rewrite Env.find_gsss in Hx. *)
  (*            inv Hx; eauto. *)
  (*          - inversion_clear NoDup as [|?? Notin]. *)
  (*            rewrite Env.find_gsso in Hx. *)
  (*            + apply IHl in Hx as (c &?&?); eauto. *)
  (*            + intro; subst; apply Notin, fst_InMembers; auto. *)
  (*        } *)
  (*     + destruct (split (b_lasts bl)) eqn: E. *)
  (*       rewrite <-split_fst_map, E in NoDup; auto. *)
  (*       apply Env.find_adds_In in Hx; auto. *)
  (*       rewrite combine_map_snd in Hx. *)
  (*       pose proof (split_combine (b_lasts bl)) as Eq. *)
  (*       rewrite E in Eq. *)
  (*       apply in_map_iff in Hx as ((?&?)& E' & Hin). *)
  (*       inv E'; setoid_rewrite Eq in Hin. *)
  (*       exists c; auto. *)
  (* Qed. *)

  (* Lemma reset_state_spec_other: *)
  (*   forall P P' b me bl, *)
  (*     find_block b P = None -> *)
  (*     b <> b_name bl -> *)
  (*     reset_state_spec (P ++ bl :: P') me b = reset_state_spec P' me b. *)
  (* Proof. *)
  (*   intros. *)
  (*   destruct (find_block b P') as [[]|] eqn: Find. *)
  (*   - symmetry; erewrite reset_state_spec_find_Some; eauto. *)
  (*     erewrite <-find_block_other_app in Find; eauto. *)
  (*     erewrite reset_state_spec_find_Some; eauto. *)
  (*   - symmetry; rewrite reset_state_spec_find_None; auto. *)
  (*     rewrite <-find_block_other_app with (P := P) (bl := bl) in Find; eauto. *)
  (*     rewrite reset_state_spec_find_None; auto. *)
  (* Qed. *)

  (* Lemma initial_reset_state_spec: *)
  (*   forall P me b P' bl, *)
  (*     Ordered_blocks P -> *)
  (*     find_block b P = Some (bl, P') -> *)
  (*     (forall x, find_val x me <> None -> InMembers x (b_lasts bl)) -> *)
  (*     initial_state P b (reset_state_spec P me b). *)
  (* Proof. *)
  (*   induction P; try now inversion 1. *)
  (*   intros ** Ord Find Spec_me. *)
  (*   econstructor; eauto. *)
  (*   - split; eapply find_val_reset_state_spec; eauto. *)
  (*   - intros. *)
  (*     unfold sub_inst, find_inst. *)
  (*     erewrite reset_state_spec_find_Some; eauto. *)
  (*     rewrite build_mem_with_spec_instances. *)
  (*     pose proof (b_nodup_lasts_blocks bl) as NoDup. *)
  (*     apply NoDup_comm, NoDup_app_weaken in NoDup. *)
  (*     destruct (split (b_blocks bl)) as (l, l') eqn: Eq. *)
  (*     simpl. *)
  (*     exists (reset_state_spec P' b'); split. *)
  (*     + apply Environment.Env.In_find_adds. *)
  (*       * assert (l = map fst (b_blocks bl)) as -> by (now rewrite <-split_fst_map, Eq); auto. *)
  (*       * rewrite combine_map_snd. *)
  (*         apply in_map_iff. *)
  (*         exists (x, b'); split; auto. *)
  (*         pose proof (split_combine (b_blocks bl)) as Eq'. *)
  (*         rewrite Eq in Eq';  setoid_rewrite Eq'; auto. *)
  (*     + simpl in Find. *)
  (*       destruct (ident_eqb (b_name a) b) eqn: E. *)
  (*       * inv Find. *)
  (*         pose proof Ord as Ord'. *)
  (*         inversion_clear Ord as [|??? Blocks]. *)
  (*         eapply Forall_forall in Blocks as (?&?&?&Find'); eauto. *)
  (*         apply IHP in Find'; auto. *)
  (*         rewrite <-initial_state_tail; auto. *)
  (*       * pose proof Ord as Ord'. *)
  (*         inversion_clear Ord as [|?? Ord'' Blocks]; clear Blocks. *)
  (*         apply find_block_app in Find as (P1 & HP &?). *)
  (*         rewrite HP in *. *)
  (*         apply Ordered_blocks_split in Ord''. *)
  (*         eapply Forall_forall in Ord'' as (?&?&?&?& Find'); eauto. *)
  (*         simpl in *. *)
  (*         rewrite <-find_block_other_app with (P := P1) (bl := bl) in Find'; auto. *)
  (*         pose proof Ord'. *)
  (*         inversion_clear Ord'. *)
  (*         pose proof Find' as Find. *)
  (*         apply IHP in Find'; auto. *)
  (*         rewrite reset_state_spec_other in Find'; auto. *)
  (*         rewrite <-initial_state_tail; auto. *)
  (*         pose proof Find as Find_name; apply find_block_name in Find_name. *)
  (*         rewrite <-Find_name. *)
  (*         apply find_block_In in Find. *)
  (*         eapply Forall_forall in Find; eauto. *)
  (*         apply Find. *)
  (* Qed. *)

  (* Corollary initial_reset_state: *)
  (*   forall P b P' bl, *)
  (*     Ordered_blocks P -> *)
  (*     find_block b P = Some (bl, P') -> *)
  (*     initial_state P b (reset_state P b). *)
  (* Proof. *)
  (*   intros. *)
  (*   rewrite reset_state_equal. *)
  (*   eapply initial_reset_state_spec; eauto. *)
  (* Qed. *)

  Lemma stmt_call_eval_cons:
    forall prog c' c me f vs me' rvs,
      c_name c <> c' ->
      (stmt_call_eval (c :: prog) me c' f vs me' rvs
       <-> stmt_call_eval prog me c' f vs me' rvs).
  Proof.
    intros ** Neq; rewrite <-ident_eqb_neq in Neq; split; intros Sem.
    - inversion_clear Sem as [??????????? Find].
      simpl in Find; rewrite Neq in Find; eauto using stmt_call_eval.
    - inv Sem; econstructor; eauto.
      simpl; rewrite Neq; auto.
  Qed.

  (* Lemma fuu: *)
  (*   forall P b P' bl me, *)
  (*     Ordered_blocks P -> *)
  (*     find_block b P = Some (bl, P') -> *)
  (*     stmt_call_eval (translate P) me b reset [] (reset_state P me b) []. *)
  (* Proof. *)
  (*   induction P as [|bl']; try now inversion 2. *)
  (*   intros ** Ord Find. *)
  (*   pose proof Find as Find'. *)
  (*   simpl in Find. *)
  (*   destruct (ident_eqb (b_name bl') b) eqn: E. *)
  (*   - inv Find. *)
  (*     (* pose proof Ord as Ord'. *) *)
  (*     (* inversion_clear Ord' as [|??? Blocks]; clear Blocks. *) *)
  (*     (* pose proof Find as Find'. *) *)
  (*     (* apply find_block_app in Find' as (P1 & Hp &?); rewrite Hp in *. *) *)
  (*     (* apply Ordered_blocks_split in Ord. *) *)
  (*     erewrite reset_state_find_Some; eauto. *)
  (*     pose proof Find' as Find_c; apply find_block_translate in Find_c as (?&?&?&?&?); subst. *)
  (*     econstructor; eauto. *)
  (*     + apply exists_reset_method. *)
  (*     + instantiate (1 := vempty). *)
  (*       simpl; rewrite Env.adds_nil_nil. *)
  (*       unfold translate_reset_eqns, build_mem_with. *)
  (*       inversion_clear Ord as [|??? Blocks]. *)
  (*       revert me. *)
  (*       induction (b_blocks bl) as [|(inst, b')]; simpl. *)
  (*       * induction (b_lasts bl) as [|(x, c)]; simpl; intro; eauto using stmt_eval. *)
  (*         rewrite stmt_eval_fold_left_lift. *)
  (*         do 2 eexists; split; eauto using stmt_eval, exp_eval. *)
  (*       *{ induction (b_lasts bl) as [|(x, c)]; simpl in *; intro; eauto using stmt_eval. *)
  (*          - rewrite stmt_eval_fold_left_lift. *)
  (*            inversion Blocks as [|?? (?&?&?&?) Blocks']; subst; simpl in *; *)
  (*              eauto. *)
  (*            do 2 eexists; split; eauto using stmt_eval. *)
  (*            unfold reset_state_aux at 2; simpl. *)
  (*            set (me' := add_inst inst (reset_state P' match find_inst inst me with *)
  (*                                   | Some om => om *)
  (*                                   | None => mempty *)
  (*                                   end b') me). *)
  (*            apply IHl.  *)
  (*            rewrite Env.adds_nil_nil. *)
  (*            apply IHl with (me := add_inst inst (reset_state_aux P' me (inst, b')) me) in Blocks'. *)
  (*            unfold reset_state_aux in *; simpl in *. *)
  (*            apply Blocks'.  *)

  (*              apply IHl.  *)
  (*              eapply IHP; eauto.  *)

  (*              rewrite find_inst_gempty. *)
  (*            inversion Blocks as [|?? (?&?&?& Find)]; subst; simpl in *. *)
  (*            pose proof Find as Find_c.  *)
  (*            rewrite stmt_call_eval_cons; auto.  *)
  (*            (* rewrite <-find_block_other_app with (P:=P1) (bl:=bl) in Find'; auto. *) *)
  (*            (* pose proof Find' as Find_c. *) *)
  (*            apply find_block_translate in Find_c as (?&?&?&?&?); subst. *)
  (*            econstructor; eauto. *)
  (*            + apply exists_reset_method. *)
  (*            + simpl; rewrite Env.adds_nil_nil. *)

  (*            SearchAbout find_class find_block. apply find_block_translate. *)
  (*         SearchAbout empty_memory. *)
  (*     econstructor; eauto using exp_eval. *)

  (* Lemma fuu: *)
  (*   forall P b P' bl, *)
  (*     Ordered_blocks P -> *)
  (*     find_block b P = Some (bl, P') -> *)
  (*     stmt_eval (translate P) mempty vempty (translate_reset_eqns bl) (reset_state P b, vempty). *)
  (* Proof. *)
  (*   induction P as [|bl']; try now inversion 2. *)
  (*   intros ** Ord Find. *)
  (*   pose proof Find as Find'. *)
  (*   simpl in Find. *)
  (*   destruct (ident_eqb (b_name bl') b) eqn: E. *)
  (*   - inv Find. *)
  (*     (* pose proof Ord as Ord'. *) *)
  (*     (* inversion_clear Ord' as [|??? Blocks]; clear Blocks. *) *)
  (*     (* pose proof Find as Find'. *) *)
  (*     (* apply find_block_app in Find' as (P1 & Hp &?); rewrite Hp in *. *) *)
  (*     (* apply Ordered_blocks_split in Ord. *) *)
  (*     erewrite reset_state_find_Some; eauto. *)
  (*     unfold translate_reset_eqns, build_mem_with. *)
  (*     inversion_clear Ord as [|??? Blocks]. *)
  (*     induction (b_blocks bl) as [|(inst, b')]; simpl. *)
  (*     + generalize mempty. *)
  (*       induction (b_lasts bl) as [|(x, c)]; simpl; eauto using stmt_eval. *)
  (*       intro. *)
  (*       rewrite stmt_eval_fold_left_lift. *)
  (*       do 2 eexists; split; eauto using stmt_eval, exp_eval. *)
  (*     + induction (b_lasts bl) as [|(x, c)]; simpl in *; eauto using stmt_eval. *)
  (*       *{ rewrite stmt_eval_fold_left_lift. *)
  (*          do 2 eexists; split. *)
  (*          - econstructor; eauto using stmt_eval. *)
  (*            econstructor; eauto. *)
  (*            rewrite find_inst_gempty. *)
  (*            inversion Blocks as [|?? (?&?&?& Find)]; subst; simpl in *. *)
  (*            pose proof Find as Find_c.  *)
  (*            rewrite stmt_call_eval_cons; auto.  *)
  (*            (* rewrite <-find_block_other_app with (P:=P1) (bl:=bl) in Find'; auto. *) *)
  (*            (* pose proof Find' as Find_c. *) *)
  (*            apply find_block_translate in Find_c as (?&?&?&?&?); subst. *)
  (*            econstructor; eauto. *)
  (*            + apply exists_reset_method. *)
  (*            + simpl; rewrite Env.adds_nil_nil. *)

  (*            SearchAbout find_class find_block. apply find_block_translate. *)
  (*         SearchAbout empty_memory. *)
  (*     econstructor; eauto using exp_eval. *)


  (*     destruct l; simpl. *)
  (*     + econstructor. *)
  (*   - *)


  (*   reset_state. reset_method; simpl. *)



  (* Lemma call_reset: *)
  (*   forall P b me bl P', *)
  (*     find_block b P = Some (bl, P') -> *)
  (*     exists me', *)
  (*       stmt_call_eval (translate P) me b reset [] me' [] *)
  (*       /\ initial_state P b me'. *)
  (* Proof. *)
  (*   intros ** Find. *)
  (*   apply find_block_translate in Find as (?&?&?&?). *)
  (*   eexists; split. *)
  (*   - econstructor; eauto. *)
  (*     + subst; apply exists_reset_method. *)
  (*     + rewrite Env.adds_nil_nil. SearchAbout Env.adds nil. SearchAbout find_method reset. *)
  (* Admitted. *)

  Ltac cases :=
    repeat match goal with
           | H: context [ match negb ?x with _ => _ end ] |- _ => destruct x; simpl; try solve [inv H; auto]
           | H: context [ match ?x with _ => _ end ] |- _ => destruct x; try solve [inv H; auto]
           | |- context [ match negb ?x with _ => _ end ] => destruct x; simpl
           | |- context [ match ?x with _ => _ end ] => destruct x
           end; auto.

  Section Expr.

    Variable (mems: PS.t).

    Lemma typeof_correct:
      forall e,
        typeof (translate_lexp mems e) = ExprSyn.typeof e.
    Proof.
      induction e; intros; simpl; auto; cases.
    Qed.

    Variable (R: env).
    Variable (me: menv) (ve: venv).

    Lemma lexp_correct:
      forall e c,
        sem_lexp_instant true R e (present c) ->
        equiv_env (fun x => Is_free_in_lexp x e) R mems me ve ->
        exp_eval me ve (translate_lexp mems e) c.
    Proof.
      induction e;
        inversion_clear 1 as [|??? Hvar| | | | | | |];
        simpl; intros ** Equiv; auto.
      - constructor; congruence.
      - apply Equiv in Hvar; auto using Is_free_in_lexp.
        cases; eauto using exp_eval.
      - econstructor; eauto.
        now rewrite typeof_correct.
      - econstructor; eauto.
        now rewrite 2 typeof_correct.
    Qed.
    Hint Resolve lexp_correct.

    Corollary lexps_correct:
      forall es cs,
        sem_lexps_instant true R es (map present cs) ->
        equiv_env (fun x => Exists (Is_free_in_lexp x) es) R mems me ve ->
        Forall2 (exp_eval me ve) (map (translate_lexp mems) es) cs.
    Proof.
      setoid_rewrite Forall2_map_1; setoid_rewrite Forall2_map_2;
        intros; eapply Forall2_impl_In; eauto.
      intros; apply lexp_correct; auto.
      weaken_equiv_env with (setoid_rewrite Exists_exists; eauto).
    Qed.
    Hint Resolve lexps_correct.

    Lemma cexp_correct:
      forall e c prog x,
        sem_cexp_instant true R e (present c) ->
        equiv_env (fun x => Is_free_in_cexp x e) R mems me ve ->
        stmt_eval prog me ve (translate_cexp mems x e) (me, Env.add x c ve).
    Proof.
      induction e;
        inversion 1 as [???? Hvar|???? Hvar| | | |];
        subst; simpl; intros ** Equiv; eauto using stmt_eval.
      - apply Equiv in Hvar; auto using Is_free_in_cexp.
        econstructor; eauto.
        + unfold bool_var, tovar.
          cases; eauto using exp_eval.
        + apply val_to_bool_true.
        + simpl; auto.
      - apply Equiv in Hvar; auto using Is_free_in_cexp.
        econstructor; eauto.
        + unfold bool_var, tovar.
          cases; eauto using exp_eval.
        + apply val_to_bool_false.
        + simpl; auto.
      - econstructor; eauto.
        cases.
    Qed.
    Hint Resolve cexp_correct.

    Section Clock.

      Variable ck: clock.
      Hypothesis Equiv: equiv_env (fun x => Is_free_in_clock x ck) R mems me ve.

      Lemma stmt_eval_Control:
        forall prog s,
          (sem_clock_instant true R ck false ->
           stmt_eval prog me ve (Control mems ck s) (me, ve))
          /\
          (forall me' ve',
              sem_clock_instant true R ck true ->
              stmt_eval prog me ve s (me', ve') ->
              stmt_eval prog me ve (Control mems ck s) (me', ve')).
      Proof.
        induction ck; split;
          inversion_clear 1 as [ |????? Hvar| |????? Hvar];
          simpl; intros; auto.
        - cases; edestruct IHc; eauto.
        - apply Equiv in Hvar; auto using Is_free_in_clock.
          unfold bool_var, tovar.
          cases; eapply IHc; eauto using stmt_eval, exp_eval.
        - apply Equiv in Hvar; auto using Is_free_in_clock.
          unfold bool_var, tovar.
          cases; eapply IHc; eauto using stmt_eval, exp_eval.
      Qed.

      Corollary stmt_eval_Control_absent:
        forall prog s,
          sem_clock_instant true R ck false ->
          stmt_eval prog me ve (Control mems ck s) (me, ve).
      Proof. apply stmt_eval_Control. Qed.

      Corollary stmt_eval_Control_present:
        forall prog s me' ve',
          sem_clock_instant true R ck true ->
          stmt_eval prog me ve s (me', ve') ->
          stmt_eval prog me ve (Control mems ck s) (me', ve').
      Proof. apply stmt_eval_Control. Qed.

    End Clock.

  End Expr.

  (* Lemma fuu: *)
  (*   forall eqs R x c prog me ve me' ve' mems, *)
  (*     sem_var_instant R x (present c) -> *)
  (*     Is_variable_in_eqs x eqs -> *)
  (*     stmt_eval prog me ve (translate_eqns mems eqs) (me', ve') -> *)
  (*     Env.find x ve' = Some c. *)
  (* Proof. *)
  (*   unfold translate_eqns. *)
  (*   induction eqs as [|[]]; *)
  (*     inversion_clear 2 as [?? Hlol|]; try inv Hlol; simpl; intros ** StEval. *)
  (*   - apply stmt_eval_fold_left_shift in StEval as (?&?&?& StEval). *)
  (*     inversion_clear StEval as [| | |????????? StEval' EvalSkip| |]; inv EvalSkip. *)

  (*     inv StEval'. *)
  (*   inv H0. *)

  Lemma equation_cons_correct:
    forall eq eqs P R S I S' me ve inputs mems,
      sem_equation P true R S I S' eq ->
      Is_well_sch inputs mems (eq :: eqs) ->
      Memory_Corres_eqs P S' me eqs ->
      Memory_Corres_eq P S me eq ->
      equiv_env (fun x => Is_free_in_eq x eq) R mems me ve ->
      exists me' ve',
        stmt_eval (translate P) me ve (translate_eqn mems eq) (me', ve')
        /\ Memory_Corres_eqs P S' me' (eq :: eqs).
  Proof.
    inversion_clear 1 as [????????? Hexp|
                          ???????????? Hexp|
                          ???????????? Init|
                          ??????????????? Hexps];
      inversion_clear 1;
      inversion_clear 2;
      intros; simpl.

    - inv Hexp; exists me; eexists; split;
        try solve [eapply stmt_eval_Control_absent; eauto; auto];
        try constructor; auto using Memory_Corres_eq; eauto; auto.
      eapply stmt_eval_Control_present; eauto; auto.
      eapply cexp_correct; eauto.

    - inv Hexp; eexists; exists ve; split;
        try solve [eapply stmt_eval_Control_absent; eauto; auto].
      + eapply stmt_eval_Control_present; eauto using stmt_eval, lexp_correct; auto.
      + constructor; auto.
        * constructor.
          setoid_rewrite find_val_gss; congruence.
        * apply Memory_Corres_eqs_add_val; auto.
      + do 2 (constructor; auto); intros.
        match goal with
        | H: find_val ?x ?S' = _, H': find_val ?x ?S' = _ |- _ =>
          rewrite H in H'; inv H'; auto
        end.

    - destruct r.
      + inversion_clear Init as [???? Find Rst].
        apply find_block_translate in Find as (?&?&?&?&?); subst.
        admit.
      + exists me, ve; split; try eapply stmt_eval_Control_absent; eauto; auto.
        constructor; auto.
        constructor.
        admit.

    - inv Hexps.
      + admit.
      + exists me, ve; split; try eapply stmt_eval_Control_absent; eauto; auto.
        constructor; auto.
        constructor.
        intros.
        match goal with
        | H: sub_inst ?s ?S' _, H': sub_inst ?s ?S' _ |- _ =>
          unfold sub_inst in H, H'; rewrite H in H'; inv H'; auto
        end.
        admit.

  Qed.

  Lemma foo:
    forall P S me ve me' ve' eqs eq mems,
      Memory_Corres_eq P S me eq ->
      stmt_eval (translate P) me ve (translate_eqns mems eqs) (me', ve') ->
      Memory_Corres_eq P S me' eq.
  Proof.
    induction 1.
    intros.

    destruct eq.

  Admitted.


  Lemma equations_cons_correct:
    forall eq eqs P R S I S' me ve me' ve' inputs mems,
      sem_equation P true R S I S' eq ->
      Is_well_sch inputs mems (eq :: eqs) ->
      Memory_Corres_eqs P S' me' eqs ->
      Memory_Corres_eq P S me eq ->
      equiv_env (fun x => Is_free_in_eq x eq) R mems me' ve' ->
      stmt_eval (translate P) me ve (translate_eqns mems eqs) (me', ve') ->
      exists me'' ve'',
        stmt_eval (translate P) me ve (translate_eqns mems (eq :: eqs)) (me'', ve'')
        /\ Memory_Corres_eqs P S' me'' (eq :: eqs).
  Proof.
    intros.
    edestruct equation_cons_correct as (me'' & ve'' &?&?); eauto.
    exists me'', ve''; split; auto.
    unfold translate_eqns; simpl; rewrite stmt_eval_fold_left_shift.
    exists me', ve'; split; eauto using stmt_eval.
  Qed.

  Lemma equations_correct:
    forall eqs P R S I S' me ve inputs mems,
      Forall (sem_equation P true R S I S') eqs ->
      Is_well_sch inputs mems eqs ->
      Memory_Corres_eqs P S me eqs ->
      exists me' ve',
        stmt_eval (translate P) me ve (translate_eqns mems eqs) (me', ve')
        /\ Memory_Corres_eqs P S' me' eqs.
  Proof.
    induction eqs; simpl;
      intros ** Heqs Wsch Corres; inv Heqs; inv Wsch; inv Corres.
    - do 4 econstructor.
    - edestruct IHeqs as (me' & ve' &?&?); eauto.
      eapply equations_cons_correct; eauto using Is_well_sch.
      admit.
  Qed.

  Theorem correctness:
    forall P b S xs ys S' me,
      sem_block P b S (map present xs) (map present ys) S' ->
      Memory_Corres P b S me ->
      exists me',
        stmt_call_eval (translate P) me b step xs me' ys
        /\ Memory_Corres P b S' me'.
  Proof.
    intros ** Sem Corres.
    inversion_clear Sem as [?????????? Clock Find ????? Heqs IHeqs].
    inversion_clear Corres as [????? Find']; rewrite Find' in Find; inv Find.
    assert (Is_well_sch (map fst (b_in bl)) (ps_from_list (map fst (b_lasts bl))) (b_eqs bl)) by admit.
    assert (base = true) by (apply Clock; rewrite present_list_spec; eauto); subst.
    edestruct equations_correct with (ve := Env.adds (map fst (m_in (step_method bl))) xs vempty)
      as (me' & ve' &?&?); eauto.
    exists me'; split; eauto using Memory_Corres.
    apply find_block_translate in Find' as (?&?&?&?&?); subst.
    econstructor; eauto.
    - apply exists_step_method.
    - instantiate (1 := ve').
      admit.
    - admit.
  Qed.


End CORRECTNESS.
