Require Import Rustre.Common.
Require Import Rustre.Operators.
Require Import Rustre.Dataflow.Syntax.
Require Import Rustre.Dataflow.IsFree.
Require Import Rustre.Dataflow.IsFree.Decide.
Require Import Rustre.Dataflow.IsVariable.
Require Import Rustre.Dataflow.IsDefined.
Require Import Rustre.Dataflow.WellFormed.

Require Import Rustre.Dataflow.Ordered.
Require Import Rustre.Dataflow.Memories.
Require Import Rustre.Dataflow.NoDup.

Require Import List.

(** * Well formed CoreDF programs: decision procedure *)

(** 

Decision procedure for the [Is_well_sch] predicate. We show that it is
equivalent to its specification.

Remark: This development is not formally part of the correctness proof.

 *)

Module Type DECIDE
       (Ids: IDS)
       (Op : OPERATORS)
       (Import Syn : SYNTAX Ids Op)
       (IsF : ISFREE Ids Op Syn)
       (Import IsFDec : IsFree.Decide.DECIDE Ids Op Syn IsF)
       (Import Ord : ORDERED Ids Op Syn)
       (Import Mem : MEMORIES Ids Op Syn)
       (Import IsD : ISDEFINED Ids Op Syn Mem)
       (Import IsV : ISVARIABLE Ids Op Syn Mem IsD)
       (Import NoD : NODUP Ids Op Syn Mem IsD IsV)
       (Import Wef : WELLFORMED Ids Op Syn IsF Ord Mem IsD IsV NoD).
  
  Section Decide.

  End Decide.

End DECIDE.

Module DecideFun
       (Ids: IDS)
       (Op : OPERATORS)
       (Import Syn : SYNTAX Ids Op)
       (IsF : ISFREE Ids Op Syn)
       (Import IsFDec : IsFree.Decide.DECIDE Ids Op Syn IsF)
       (Import Ord : ORDERED Ids Op Syn)
       (Import Mem : MEMORIES Ids Op Syn)
       (Import IsD : ISDEFINED Ids Op Syn Mem)
       (Import IsV : ISVARIABLE Ids Op Syn Mem IsD)
       (Import NoD : NODUP Ids Op Syn Mem IsD IsV)
       (Import Wef : WELLFORMED Ids Op Syn IsF Ord Mem IsD IsV NoD)
       <: DECIDE Ids Op Syn IsF IsFDec Ord Mem IsD IsV NoD Wef.
  
  Section Decide.

    Variable mems : PS.t.

    (* TODO: rewrite using a strong specification?  *)

    Open Scope bool_scope.

    Definition check_var (defined: PS.t) (variables: PS.t) (x: ident) : bool :=
      if PS.mem x mems
      then negb (PS.mem x defined)
      else PS.mem x variables.

    Lemma check_var_spec:
      forall defined variables x,
        check_var defined variables x = true
        <->
        (PS.In x mems -> ~PS.In x defined)
        /\ (~PS.In x mems -> PS.In x variables).
    Proof.
      (*  TODO: how to automate all of this? *)
      intros defined variables x.
      unfold check_var.
      split.
      - intro Hif.
        split; intro Hin.
        + apply PS.mem_spec in Hin.
          rewrite Hin, Bool.negb_true_iff in Hif.
          apply mem_spec_false in Hif. exact Hif.
        + apply mem_spec_false in Hin.
          rewrite Hin, PS.mem_spec in Hif. exact Hif.
      - destruct 1 as [Hin Hnin].
        destruct Common.In_dec with x mems as [H|H].
        + assert (PS.mem x mems = true) as H' by auto.
          rewrite H', Bool.negb_true_iff, mem_spec_false.
          now apply Hin with (1:=H).
        + assert (PS.mem x mems = false) as H' by now apply mem_spec_false.
          rewrite H', PS.mem_spec.
          now apply Hnin with (1:=H).
    Qed.

    Definition check_eq (eq: equation) (acc: bool*PS.t*PS.t): bool*PS.t*PS.t :=
      match acc with
      | (true, defined, variables) =>
        match eq with
        | EqDef x ck e =>
          ((PS.for_all (check_var defined variables)
                       (free_in_caexp ck e PS.empty))
             && (negb (PS.mem x defined)),
           PS.add x defined, PS.add x variables)
        | EqApp x ck f les _ =>
          ((PS.for_all (check_var defined variables)
                       (free_in_laexps ck les PS.empty))
             && (negb (PS.mem x defined)),
           PS.add x defined, PS.add x variables)
        | EqFby x ck v e =>
          ((PS.mem x mems && PS.for_all (check_var defined variables)
                   (free_in_laexp ck e PS.empty))
             && (negb (PS.mem x defined)),
           PS.add x defined, variables)
        end
      | (false, _, _) => (false, PS.empty, PS.empty)
      end.

    Definition well_sch (argIns: list ident)(eqs: list equation) : bool :=
      fst
        (fst
           (List.fold_right
              check_eq
              (true, PS.empty, fold_left (fun a b => PS.add b a) argIns PS.empty)
              eqs)).

    (* Lemma not_for_all_spec: *)
(*       forall (s : PS.t) (f : BinNums.positive -> bool), *)
(*         SetoidList.compat_bool PS.E.eq f -> *)
(*         (PS.for_all f s = false <-> ~(PS.For_all (fun x : PS.elt => f x = true) s)). *)
(*     Proof. *)
(*       intros s f HSL. *)
(*       split. *)
(*       - intros Hfa HFa. *)
(*         apply (PS.for_all_spec _ HSL) in HFa. *)
(*         rewrite Hfa in HFa. *)
(*         discriminate. *)
(*       - intro HFa. *)
(*         apply Bool.not_true_iff_false. *)
(*         intro Hfa; apply HFa. *)
(*         apply (PS.for_all_spec _ HSL). *)
(*         assumption. *)
(*     Qed. *)

(*     Lemma check_var_compat: *)
(*       forall defined variables, *)
(*         SetoidList.compat_bool PS.E.eq (check_var defined variables). *)
(*     Proof. *)
(*       intros defined variables x y Heq. *)
(*       unfold PS.E.eq in Heq. *)
(*       rewrite Heq. *)
(*       reflexivity. *)
(*     Qed. *)

(*     Lemma well_sch_pre_spec: *)
(*       forall argIns eqs good defined variables, *)
(*         (good, defined, variables) *)
(*         = List.fold_right check_eq (true, PS.empty, fold_left (fun a b => PS.add b a) argIns PS.empty) eqs *)
(*         -> *)
(*         (good = true *)
(*          -> (Is_well_sch mems argIns eqs *)
(*             /\ (forall x, PS.In x defined <-> Is_defined_in_eqs x eqs) *)
(*             /\ (forall x, PS.In x variables <-> Is_variable_in_eqs x eqs \/ In x argIns))) *)
(*         /\ (good = false -> ~Is_well_sch mems argIns eqs). *)
(*     Admitted. (* XXX: Stating that a decision procedure behaves as expected. Not used *) *)
(*     (* *)
(*   induction eqs as [|eq]. *)
(*   - simpl; injection 1; intros HRv HRm; subst. *)
(*     intuition; *)
(*       repeat match goal with *)
(*                | H: PS.In _ (PS.add _ _) |- _ => rewrite PS.add_spec in H; destruct H *)
(*                | H: PS.In _ PS.empty |- _ => apply PS.empty_spec in H; *)
(*                                              contradiction *)
(*                | H: Is_defined_in _ nil |- _ => now inversion H *)
(*                | H: Is_variable_in _ nil |- _ => now inversion H *)
(*                | H1:good=true, H2:good=false |- _ => rewrite H1 in H2; discriminate *)
(*                | |- _ => tauto *)
(*              end. *)
(*   - intros good defined variables HH. *)
(*     simpl in HH. *)
(*     destruct (List.fold_right check_eq (true, PS.empty, PS.add argIn PS.empty) eqs) *)
(*       as [[good' defined'] variables'] eqn:Heq. *)
(*     specialize IHeqs with good' defined' variables'. *)
(*     pose proof (IHeqs (eq_refl (good', defined', variables'))) as IH; *)
(*       clear IHeqs. *)
(*     destruct IH as [IHt IHf]. *)
(*     split; intro Hg; rewrite Hg in *; clear Hg. *)
(*     + destruct eq; (* the horror... *) (* XXX: . was ; *) *)
(*       (simpl in HH; *)
(*        assert (good' = true) as IH *)
(*            by (apply Bool.not_false_iff_true; *)
(*                intro Hgf; rewrite Hgf in HH; *)
(*                discriminate); *)
(*        rewrite IH in HH; *)
(*        apply IHt in IH; clear IHt IHf; *)
(*        destruct IH as [Hwsch [Hidi Hivi]]; *)
(*        symmetry in HH; *)
(*        injection HH; *)
(*        intros HRv HRd; rewrite <-HRv,<-HRd in *; clear HRv HRd HH; *)
(*        intro Hcv; apply Bool.andb_true_iff in Hcv; *)
(*          destruct Hcv as [Hcv Hnin]; *)
(*          try (apply Bool.andb_true_iff in Hcv; *)
(*                destruct Hcv as [Him Hcv]); *)
(*          rewrite Bool.negb_true_iff, *)
(*          <-PSF.not_mem_iff in Hnin; *)
(*        rewrite PS.for_all_spec in Hcv; *)
(*          [ |now apply check_var_compat]; *)
(*        try rewrite PS.mem_spec in Him; *)
(*        split; *)
(*        [constructor; *)
(*          try (exact Hwsch *)
(*               || assumption *)
(*               || (intro HH; apply Hidi in HH; contradiction)); *)
(*         intros y Hy; *)
(*           apply free_in_caexp_spec' in Hy *)
(*           || apply free_in_laexp_spec' in Hy; *)
(*           apply Hcv in Hy; *)
(*           apply check_var_spec in Hy; *)
(*           repeat progress match goal with *)
(*           | H:_ /\ _ |- _ => destruct H *)
(*           | |- _ /\ _ => split; intros *)
(*           | H1:PS.In ?y ?mems -> _, H2:PS.In ?y ?mems |- _ => apply H1 in H2 *)
(*           | |- ~Is_defined_in ?x _ => intro *)
(*           | H1:~PS.In ?x defined', *)
(*             H2:Is_defined_in ?x eqs |- _ => apply Hidi in H2; contradiction *)
(*           | |- Is_variable_in ?x eqs => auto; apply Hivi *)
(*           | _ => now intuition *)
(*                           end |]; *)
(*       (now rewrite <- Hivi; auto) || *)
(*       split; intro x; split; intro HH; *)
(*          (apply PS.add_spec in HH; *)
(*            destruct HH as [HH|HH]; try (now subst; repeat constructor); []; *)
(*            solve [ now apply Hidi in HH; constructor 2 *)
(*                  | apply Hivi in HH; destruct HH as [HH | HH]; tauto || constructor; constructor 2; *)
(*                    []; inversion_clear HH; (now constructor) || (now constructor 2) ]) *)
(*          || (rewrite PS.add_spec, ?Hivi, ?Hidi; *)
(*               apply Is_defined_in_cons in HH *)
(*               || (destruct HH as [HH | HH]; try tauto; []; apply Is_variable_in_cons in HH); *)
(*               destruct HH as [HH|HH]; inversion_clear HH; tauto) *)
(*          || (apply Hivi in HH; try (destruct HH as [HH | HH]; tauto || left); constructor 2; apply HH) *)
(*          || (rewrite Hivi; try (destruct HH as [HH | HH]; try tauto; []); *)
(*              apply Is_variable_in_cons in HH; destruct HH as [HH|HH]; inversion HH; tauto)). *)
(*     + destruct good'; [clear IHf| inversion 1; apply IHf; auto ]. *)
(*       pose proof (IHt (eq_refl true)) as IH; clear IHt. *)
(*       destruct IH as [Hwsch [Hidi Hivi]]. *)
(*       destruct eq; *)
(*         (simpl in HH; *)
(*           injection HH; *)
(*           intros HRd HRv Hcv; *)
(*           rewrite HRd,HRv in *; *)
(*           clear HRd HRv HH; *)
(*           symmetry in Hcv; *)
(*           repeat progress match goal with *)
(*           | Hcv:PS.mem _ _ && _ = false |- _ => *)
(*             apply Bool.andb_false_iff in Hcv; *)
(*               destruct Hcv as [Hcv|Hcv]; *)
(*               [ inversion 1; *)
(*                 apply mem_spec_false in Hcv; *)
(*                 contradiction *)
(*               | rewrite not_for_all_spec in Hcv; *)
(*                 [ |now apply check_var_compat] ] *)
(*           | H:_ && negb _ = false |- _ => *)
(*             apply Bool.andb_false_iff in Hcv; *)
(*               destruct Hcv as [Hcv|Hcv]; *)
(*               [rewrite not_for_all_spec in Hcv; *)
(*                 [ |now apply check_var_compat] *)
(*               | rewrite Bool.negb_false_iff in Hcv; *)
(*                 rewrite PS.mem_spec in Hcv; *)
(*                 apply Hidi in Hcv; *)
(*                 inversion 1; *)
(*                 contradiction ] *)
(*           | Hcv:PS.mem _ _ && _ && _ = false |- _ => *)
(*             apply Bool.andb_false_iff in Hcv; *)
(*               destruct Hcv as [Hcv|Hcv]; *)
(*               [|rewrite Bool.negb_false_iff in Hcv; *)
(*                  rewrite PS.mem_spec in Hcv; *)
(*                  apply Hidi in Hcv; *)
(*                  inversion 1; *)
(*                  contradiction] *)
(*           | H:PS.for_all _ _ = false |- _ => *)
(*             apply not_for_all_spec in Hcv; [|apply check_var_compat] *)
(*           | _ => idtac *)
(*           end; *)
(*           intro Hwsch'; *)
(*           apply Hcv; *)
(*           inversion_clear Hwsch' as [|? ? ? Hwsch0 HH *)
(*                                         |? ? ? ? Hwsch0 HH *)
(*                                         |? ? ? ? Hwsch0 Hi HH]; *)
(*           intros x Hx; *)
(*           apply free_in_caexp_spec in Hx || apply free_in_laexp_spec in Hx; *)
(*           destruct Hx as [Hx|Hx]; [ | apply not_In_empty in Hx; contradiction ]; *)
(*           intros; *)
(*           repeat progress *)
(*                  match goal with *)
(*                  | |- _ /\ _ => split; intros *)
(*                  | H: _ /\ _ |- _ => destruct H *)
(*                  | H: Is_free_in_caexp _ _ |- _ => apply HH in H *)
(*                  | H: Is_free_in_laexp _ _ |- _ => apply HH in H *)
(*                  | |- check_var defined' variables' x = true *)
(*                    => apply check_var_spec *)
(*                  | H1:~PS.In ?x ?mems -> Is_variable_in ?x ?eqs, *)
(*                    H2:~PS.In ?x ?mems |- PS.In ?x variables' *)
(*                    => apply H1 in H2; apply Hivi in H2; assumption *)
(*                  | H1:PS.In ?x ?mems -> ~Is_defined_in ?x ?eqs, *)
(*                       H2:PS.In ?x ?mems |- _ => apply H1 in H2 *)
(*                  | H:~Is_defined_in ?x ?eqs |- ~PS.In ?x defined' *)
(*                    => intro HN; apply Hidi in HN; contradiction *)
(*                  end); *)
(*           rewrite Hivi; auto. *)
(* Qed. *)
(*      *) *)
(*     Lemma well_sch_spec: *)
(*       forall argIns eqns, *)
(*         if well_sch argIns eqns *)
(*         then Is_well_sch mems argIns eqns *)
(*         else ~Is_well_sch mems argIns eqns. *)
(*     Proof. *)
(*       intros argIn eqns. *)
(*       pose proof (well_sch_pre_spec argIn eqns). *)
(*       unfold well_sch. *)
(*       destruct (List.fold_right check_eq (true, PS.empty, fold_left (fun a b => PS.add b a) argIn PS.empty) eqns) *)
(*         as [[good defined] variables]. *)
(*       simpl. *)
(*       specialize H with good defined variables. *)
(*       pose proof (H (eq_refl _)) as H'; clear H. *)
(*       destruct H' as [Ht Hf]. *)
(*       destruct good; *)
(*         intuition. *)
(*     Qed. *)

  End Decide.

End DecideFun.