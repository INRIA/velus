From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import CommonTyping.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Fresh.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax.

(** * Remove Local Blocks *)

Module Type NORMLAST
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv).

  (** ** Normalization of last variables
      This is structured into three phases

      1) initialize non-constant lasts
      ```
      last x = e0;
      ```
      becomes
      ```
      lx = e0 fby x;
      ```
      and replace `last x` by `lx` everywhere

      2) remove lasts on outputs
      ```
      last o = ...
      ```
      becomes
      ```
      last lo = ...
      o = lo
      ```
      and replace `o` by `lo` everywhere

      3) remove lasts defined by a non-cexp equation

      ```
      x = e
      ```
      becomes
      ```
      x1 = e
      x = x1
      ```
   *)

  (** ** Generating fresh identifiers *)

  Module Fresh := Fresh.Fresh(Ids).
  Import Fresh Notations Facts Tactics.
  Local Open Scope fresh_monad_scope.

  Definition FreshAnn A := Fresh last A (type * clock).

  (** ** Phase 1 *)
  Section initialize.

    (** Analysis *)

    Fixpoint is_constant (e : exp) : bool :=
      match e with
      | Econst _ | Eenum _ _ => true
      | Ewhen [e] _ _ ([ty], _) => is_constant e
      | _ => false
      end.

    Fixpoint non_constant_lasts (blk : block) : PS.t :=
      match blk with
      | Beq _ => PS.empty
      | Blast x e => if is_constant e then PS.empty else PS.singleton x
      | Breset [blk] e => non_constant_lasts blk
      | _ => PS.empty (* Should not happen *)
      end.

    (** Transformation of sub-blocks *)
    Section block.
      Variable (sub : Env.t ident). (* Transforms last x into lx *)

      Fixpoint init_exp (e : exp) :=
        match e with
        | Econst _ | Eenum _ _ | Evar _ _ => e
        | Elast x ann =>
            match Env.find x sub with
            | Some lx => Evar lx ann
            | None => Elast x ann
            end
        | Eunop op e1 ann => Eunop op (init_exp e1) ann
        | Ebinop op e1 e2 ann => Ebinop op (init_exp e1) (init_exp e2) ann
        | Eextcall f es ann => Eextcall f (map init_exp es) ann
        | Efby e0s e1s anns => Efby (map init_exp e0s) (map init_exp e1s) anns
        | Earrow e0s e1s anns => Earrow (map init_exp e0s) (map init_exp e1s) anns
        | Ewhen es x t ann => Ewhen (map init_exp es) x t ann
        | Emerge (x, ty) es ann => Emerge (x, ty) (map (fun '(i, es) => (i, map init_exp es)) es) ann
        | Ecase e es d ann =>
            Ecase (init_exp e) (map (fun '(i, es) => (i, map init_exp es)) es) (option_map (map init_exp) d) ann
        | Eapp f es er ann => Eapp f (map init_exp es) (map init_exp er) ann
        end.

      Definition init_equation '(xs, es) : equation :=
        (xs, map init_exp es).

      Definition hd_ann := hd (OpAux.bool_velus_type, Cbase).

      Fixpoint init_block (blk : block) : block :=
        match blk with
        | Beq eq => Beq (init_equation eq)
        | Blast x e =>
            let ann := hd_ann (annot e) in
            let e' := init_exp e in
            match Env.find x sub with
            | Some lx => Beq ([lx], [Efby [e'] [Evar x ann] [ann]])
            | None => Blast x e'
            end
        | Breset [blk] er =>
            Breset [init_block blk] (init_exp er)
        | _ => blk (* Should not happen :) *)
        end.

    End block.

    (** Top block *)

    Definition init_top_block (outs : list decl) blk : FreshAnn (list decl * block) :=
      match blk with
      | Blocal (Scope vars blks) =>
          let olasts := map_filter (fun '(x, (ty, ck, _, o)) => option_map (fun _ => (x, (ty, ck))) o) outs in
          let vlasts := map_filter (fun '(x, (ty, ck, _, o)) => option_map (fun _ => (x, (ty, ck))) o) vars in
          (* Lasts that are not initialized by constants *)
          let ncl := PSUnion (map non_constant_lasts blks) in
          do linits <- fresh_idents (filter (fun '(x, _) => PS.mem x ncl) (olasts++vlasts));
          let sub := Env.from_list (map fst linits) in
          (* Some output may become last-less *)
          let outs' := map (fun '(x, (ty, ck, cx, clx)) =>
                              if Env.mem x sub then (x, (ty, ck, cx, None))
                              else (x, (ty, ck, cx, clx))) outs in
          (* Compile sub-blocks *)
          let blks' := map (init_block sub) blks in
          ret (outs',
              Blocal (Scope (map (fun '(x, (ty, ck, cx, o)) => (x, (ty, ck, cx, if PS.mem x ncl then None else o))) vars
                               ++map (fun '(_, lx, (ty, ck)) => (lx, (ty, ck, xH, None))) linits)
                        blks'))
      | _ => ret (outs, blk) (* Should not happen *)
      end.

  End initialize.

  Definition rename_var sub (x : ident) :=
    or_default x (Env.find x sub).

  (** ** Phase 2 *)
  Section outputs.

    Section block.
      Variable sub : Env.t ident.

      Fixpoint rename_exp (e : exp) :=
        match e with
        | Econst _ | Eenum _ _ | Evar _ _ => e
        | Elast x ann => Elast (rename_var sub x) ann
        | Eunop op e1 ann => Eunop op (rename_exp e1) ann
        | Ebinop op e1 e2 ann => Ebinop op (rename_exp e1) (rename_exp e2) ann
        | Eextcall f es ann => Eextcall f (map rename_exp es) ann
        | Efby e0s e1s anns => Efby (map rename_exp e0s) (map rename_exp e1s) anns
        | Earrow e0s e1s anns => Earrow (map rename_exp e0s) (map rename_exp e1s) anns
        | Ewhen es x t ann => Ewhen (map rename_exp es) x t ann
        | Emerge (x, ty) es ann => Emerge (x, ty) (map (fun '(i, es) => (i, map rename_exp es)) es) ann
        | Ecase e es d ann =>
            Ecase (rename_exp e) (map (fun '(i, es) => (i, map rename_exp es)) es) (option_map (map rename_exp) d) ann
        | Eapp f es er ann => Eapp f (map rename_exp es) (map rename_exp er) ann
        end.

      (* Copy from old identifiers to new *)
      Fixpoint copy_eqs_on sub xs anns : list equation :=
        match xs with
        | [] => []
        | x::xs =>
            let tl := copy_eqs_on sub xs (tl anns) in
            match Env.find x sub with
            | Some y => ([x], [Evar y (hd_ann anns)])::tl
            | None => tl
            end
        end.

      (* Copy from new identifiers to old *)
      Fixpoint copy_eqs_no sub xs anns : list equation :=
        match xs with
        | [] => []
        | x::xs =>
            let tl := copy_eqs_no sub xs (tl anns) in
            match Env.find x sub with
            | Some y => ([y], [Evar x (hd_ann anns)])::tl
            | None => tl
            end
        end.

      Definition rename_equation '(xs, es) : list equation :=
        match es with
        | [Eapp _ _ _ anns] => (xs, map rename_exp es)::copy_eqs_no sub xs anns
        | _ => (map (rename_var sub) xs, map rename_exp es)::copy_eqs_on sub xs (annots es)
        end.

      Fixpoint rename_block (blk : block) : list block :=
        match blk with
        | Beq eq => map Beq (rename_equation eq)
        | Blast x e => [Blast (rename_var sub x) (rename_exp e)]
        | Breset [blk] er =>
            map (fun blk => Breset [blk] (rename_exp er)) (rename_block blk)
        | _ => [blk] (* Should not happen :) *)
        end.
    End block.

    Definition output_top_block (outs : list decl) blk : FreshAnn block :=
      match blk with
      | Blocal (Scope vars blks) =>
          let olasts := map_filter (fun '(x, (ty, ck, _, o)) => option_map (fun _ => (x, (ty, ck))) o) outs in
          (* Lasts on outputs *)
          do louts <- fresh_idents olasts;
          let sub := Env.from_list (map fst louts) in
          (* Compile sub-blocks *)
          let blks' := flat_map (rename_block sub) blks in
          ret (Blocal (Scope (vars++map (fun '(_, lx, (ty, ck)) => (lx, (ty, ck, xH, Some xH))) louts)
                         blks'))
      | _ => ret blk (* Should not happen *)
      end.

  End outputs.

  (** ** Phase 3 *)
  Section cexps.

    (** Analysis *)

    Fixpoint non_cexp_defs (blk : block) : PS.t :=
      match blk with
      | Beq (xs, [Eapp _ _ _ _]) => PSP.of_list xs
      | Beq ([x], [Efby _ _ _])
      | Beq ([x], [Earrow _ _ _])
      | Beq ([x], [Eextcall _ _ _]) => PS.singleton x
      | Beq ([x], [_]) => PS.empty
      | Blast x e => PS.empty
      | Breset [blk] e => non_cexp_defs blk
      | _ => PS.empty (* Should not happen *)
      end.

    Section block.
      Variable sub : Env.t ident.

      Fixpoint unnest_block (blk : block) : block :=
        match blk with
        | Beq (xs, es) => Beq (xs, map (rename_exp sub) es)
        | Blast x e => Blast (rename_var sub x) (rename_exp sub e)
        | Breset [blk] er =>
            Breset [unnest_block blk] (rename_exp sub er)
        | _ => blk (* Should not happen :) *)
        end.

    End block.

    Definition unnest_top_block blk : FreshAnn block :=
      match blk with
      | Blocal (Scope vars blks) =>
          let vlasts := map_filter (fun '(x, (ty, ck, _, o)) => option_map (fun _ => (x, (ty, ck))) o) vars in
          (* Lasts that are defined by a stateful construct *)
          let stl := PSUnion (map non_cexp_defs blks) in
          do lexts <- fresh_idents (filter (fun '(x, _) => PS.mem x stl) vlasts);
          let sub := Env.from_list (map fst lexts) in
          let exteqs := List.map (fun '(x, lx, ann) => Beq ([lx], [Evar x ann])) lexts in
          (* Compile sub-blocks *)
          let blks' := map (unnest_block sub) blks in
          ret (Blocal (Scope (map (fun '(x, (ty, ck, cx, o)) => (x, (ty, ck, cx, if PS.mem x stl then None else o))) vars
                                ++map (fun '(_, lx, (ty, ck)) => (lx, (ty, ck, xH, Some xH))) lexts)
                         (exteqs++blks')))
      | _ => ret blk (* Should not happen *)
      end.

  End cexps.

  (** ** Some properties *)

  Lemma last_not_in_norm1_prefs :
    ~PS.In last norm1_prefs.
  Proof.
    unfold norm1_prefs, local_prefs, switch_prefs, auto_prefs, elab_prefs.
    rewrite ? PS.add_spec, PSF.singleton_iff.
    pose proof gensym_prefs_NoDup as Hnd. unfold gensym_prefs in Hnd.
    rewrite ? NoDup_cons_iff in Hnd. destruct_conjs.
    intros Eq. repeat take (_ \/ _) and destruct it as [Eq|Eq]; eauto 7 with datatypes.
  Qed.

  Import Permutation.

  Fact fresh_idents_NoDup : forall lasts lasts' st st',
      @fresh_idents last (type * clock) lasts st = (lasts', st') ->
      NoDupMembers (map (fun '(_, lx, (ty, ck)) => (lx, (ty, ck, xH, @None ident))) lasts').
  Proof.
    unfold fresh_idents.
    induction lasts; intros * Hfresh;
      destruct_conjs; repeat inv_bind; constructor; eauto.
    - intros Hinm. rewrite fst_InMembers in Hinm; simpl_In.
      eapply fresh_idents_nIn_ids in H0.
      simpl_Forall.
      eapply H0, fresh_ident_Inids; eauto.
  Qed.

  (** ** Phase 1: Wellformedness properties *)

  Fact non_constant_lasts_Def : forall x blk xs,
      PS.In x (non_constant_lasts blk) ->
      LastsDefined blk xs ->
      In x xs.
  Proof.
    induction blk using block_ind2; intros * In VD; inv VD; simpl in *; cases;
      try apply not_In_empty in In as [];
      try apply PSF.singleton_1 in In; subst; try now repeat constructor.
    - (* reset *)
      simpl_Forall. rewrite app_nil_r. auto.
  Qed.

  Corollary map_non_constant_lasts_Def : forall x blks xs,
      PS.In x (PSUnion (map non_constant_lasts blks)) ->
      Forall2 LastsDefined blks xs ->
      In x (concat xs).
  Proof.
    intros * In1 LD.
    eapply PSUnion_In_In in In1 as (?&In1&In2).
    simpl_In. inv_VarsDefined.
    eapply in_concat; do 2 esplit; eauto using non_constant_lasts_Def.
  Qed.

  (** *** VarsDefinedComp *)

  Lemma init_block_vars : forall subinits blk xs ls,
      unnested_block blk ->
      VarsDefinedComp blk xs ->
      LastsDefined blk ls ->
      exists ys, VarsDefinedComp (init_block subinits blk) ys
            /\ Permutation ys
                (xs++map_filter (fun x => Env.find x subinits) ls).
  Proof.
    induction blk using block_ind2; intros * Un Vars Lasts; inv Un.
    - (* equation *)
      destruct eq. inv Vars. inv Lasts. simpl. setoid_rewrite app_nil_r.
      do 2 esplit; eauto. constructor.
    - (* last *)
      inv Vars. inv Lasts. simpl.
      cases.
      1,2:do 2 esplit; eauto; constructor.
    - (* reset *)
      inv Vars. inv Lasts. simpl_Forall.
      eapply H3 in H1 as (?&Vars&Perm); eauto.
      do 2 esplit. repeat constructor; eauto.
      simpl. now rewrite ? app_nil_r.
  Qed.

  Corollary map_init_block_vars : forall subinits blks xs ls,
      Forall unnested_block blks ->
      Forall2 VarsDefinedComp blks xs ->
      Forall2 LastsDefined blks ls ->
      exists ys, Forall2 VarsDefinedComp (map (init_block subinits) blks) ys
            /\ Permutation (concat ys)
                (concat xs++map_filter (fun x => Env.find x subinits) (concat ls)).
  Proof.
    induction blks; intros * Un Vars Lasts; inv Un; inv Vars; inv Lasts; simpl.
    - do 2 esplit; eauto.
    - eapply init_block_vars in H3 as (?&V1&P1); eauto.
      eapply IHblks in H5 as (?&V2&P2); eauto.
      do 2 esplit. constructor; eauto.
      simpl. rewrite P1, P2. solve_Permutation_app.
  Qed.

  Lemma init_top_block_vars : forall outs blk outs' blk' st st',
      unnested outs blk ->
      NoDupMembers outs ->
      NoDupLocals (map fst outs) blk ->
      (exists ls, LastsDefined blk ls /\ Permutation ls (lasts_of_decls outs)) ->
      init_top_block outs blk st = (outs', blk', st') ->
      VarsDefinedComp blk' (map fst outs).
  Proof.
    intros * Un ND1 ND2 (ls&Lasts&PermL) NL.
    inversion Un as [??? Syn1 (?&Vars&Perm)]; subst; clear Un.
    inv ND2. inv Vars. inv Lasts. repeat inv_scope. repeat inv_bind.
    do 2 constructor.
    eapply map_init_block_vars in H as (?&Vars'&Perm'); eauto.
    do 2 esplit.
    - repeat apply Forall2_app; eauto.
    - rewrite ? concat_app, Perm', H0, H3, Perm, PermL, ? map_app, <-app_assoc.
      apply Permutation_app_head.
      erewrite map_map, map_ext with (l:=locs). apply Permutation_app_head.
      2:intros; unfold decl in *; destruct_conjs; auto.
      symmetry. erewrite ? map_map, map_ext with (l:=x2), fresh_idents_Perm with (sub:=Env.empty _); eauto.
      3:{ intros; destruct_conjs; auto. }
      2:{ apply NoDupMembers_filter, NoDupMembers_app.
          1,2:(apply NoDupMembers_map_filter; auto;
               intros; destruct_conjs; take (option ident) and destruct it; simpl; auto).
          intros * In1 In2. simpl_In.
          eapply H9; solve_In.
      }
      assert (Forall (fun x =>
                        PS.mem x (PSUnion (map non_constant_lasts blks)) = true
                        <-> Env.In x (Env.from_list (map fst x2)))
                (lasts_of_decls locs ++ lasts_of_decls outs)) as Equiv.
      { simpl_Forall. apply in_app_iff in H as In.
        erewrite Env.In_from_list, <-fresh_idents_InMembers; eauto.
        rewrite <-filter_app, InMembers_app.
        clear - In. split; intros In1.
        - unfold lasts_of_decls in *. destruct In as [|]; [right|left]; solve_In; auto.
        - destruct In1; simpl_In; auto. }
      apply Forall_app in Equiv as (Equiv1&Equiv2).
      rewrite <- ? filter_app, ? map_app, ? map_map, map_filter_app.
      apply Permutation_app.
      + clear - Equiv2. induction outs as [|(?&(((?&?)&?)&[]))]; simpl; auto.
        inv Equiv2.
        destruct (PS.mem i _) eqn:Eq; simpl.
        * destruct H1 as ((?&Find)&_); simpl; auto.
          setoid_rewrite Find. auto.
        * assert (Env.find i (Env.from_list (map fst x2)) = None) as Find.
          { apply Env.Props.P.F.not_find_in_iff. rewrite <-H1. congruence. }
          setoid_rewrite Find. auto.
      + clear - Equiv1. induction locs as [|(?&(((?&?)&?)&[]))]; simpl; auto.
        inv Equiv1.
        destruct (PS.mem i _) eqn:Eq; simpl.
        * destruct H1 as ((?&Find)&_); simpl; auto.
          setoid_rewrite Find. auto.
        * assert (Env.find i (Env.from_list (map fst x2)) = None) as Find.
          { apply Env.Props.P.F.not_find_in_iff. rewrite <-H1. congruence. }
          setoid_rewrite Find. auto.
  Qed.

  (** *** LastsDefined *)

  Lemma init_block_lasts : forall sub blk ls,
      unnested_block blk ->
      LastsDefined blk ls ->
      LastsDefined (init_block sub blk) (filter (fun x => negb (Env.mem x sub)) ls).
  Proof.
    induction blk using block_ind2; intros * Un Lasts; inv Un; inv Lasts; simpl.
    - (* equation *) constructor.
    - (* last *)
      rewrite Env.mem_find.
      destruct (Env.find _ _); simpl; constructor.
    - (* reset *)
      rewrite <-concat_filter_map. constructor.
      simpl_Forall.
  Qed.

  Lemma init_top_block_lasts : forall outs blk outs' blk' st st',
      unnested outs blk ->
      (exists ls, LastsDefined blk ls /\ Permutation ls (lasts_of_decls outs)) ->
      NoDupLocals (map fst outs) blk ->
      init_top_block outs blk st = (outs', blk', st') ->
      LastsDefined blk' (lasts_of_decls outs').
  Proof.
    unfold init_top_block.
    intros * Un (?&LD&PermL) ND DL. inv Un. inv ND. inv LD. repeat inv_scope. repeat inv_bind.
    do 2 constructor.
    exists (map (filter (fun x => negb (Env.mem x (Env.from_list (map fst x2))))) x0). split.
    - simpl_Forall; eauto using init_block_lasts.
    - rewrite concat_filter_map, H2, PermL, <-filter_app.
      unfold lasts_of_decls. rewrite map_filter_app, map_filter_nil with (xs:=map _ x2), app_nil_r.
      2:simpl_Forall; auto.
      apply Permutation_app.
      + clear - outs. induction outs as [|(?&(((?&?)&?)&?))]; simpl; auto.
        destruct o; simpl; auto.
        1,2:destruct (Env.mem i _) eqn:Mem; simpl; auto.
      + assert (Forall (fun '(x, (_, _, _, o)) =>
                          Env.In x (Env.from_list (map fst x2))
                          <-> PS.mem x (PSUnion (map non_constant_lasts blks)) = true) locs) as NL.
        { simpl_Forall.
          erewrite Env.In_from_list, <-fresh_idents_InMembers; eauto.
          split; intros In; [|rewrite <-filter_app, InMembers_app; right].
          + simpl_In; auto.
          + eapply map_non_constant_lasts_Def in In as In1; eauto.
            rewrite H2, PermL, in_app_iff in In1. unfold lasts_of_decls in *; destruct In1; simpl_In.
            * exfalso. eapply H10; solve_In.
            * eapply NoDupMembers_det in H5; eauto. inv H5.
              solve_In. auto.
        }
        clear - NL. induction NL as [|(?&(((?&?)&?)&?))]; simpl; auto.
        destruct o; simpl; auto.
        * destruct (Env.mem k _) eqn:Mem1; simpl; auto.
          -- apply Env.mem_2, H in Mem1. rewrite Mem1; auto.
          -- destruct (PS.mem _ _) eqn:Mem2; simpl; auto.
             rewrite <-Env.Props.P.F.not_mem_in_iff, H in Mem1. congruence.
        * destruct (PS.mem _ _) eqn:Mem1; auto.
  Qed.

  (** *** GoodLocals *)

  Lemma init_block_GoodLocals subinits : forall blk,
      GoodLocals last_prefs blk ->
      GoodLocals last_prefs (init_block subinits blk).
  Proof.
    induction blk using block_ind2; intros * Hnd; simpl; auto.
    - (* equation *)
      constructor.
    - (* last *)
      cases; constructor.
    - (* reset *)
      cases; auto.
      inv Hnd. simpl_Forall.
      repeat constructor. eauto.
  Qed.

  Lemma init_top_block_GoodLocals : forall outs blk outs' blk' st st',
      GoodLocals last_prefs blk ->
      init_top_block outs blk st = (outs', blk', st') ->
      GoodLocals last_prefs blk'.
  Proof.
    intros * Good NL.
    unfold init_top_block in *.
    cases; repeat inv_bind; auto.
    inv Good. repeat inv_scope.
    repeat constructor.
    - repeat (take (fresh_idents _ _ = _) and apply fresh_idents_prefixed in it).
      rewrite ? map_app, ? Forall_app. repeat split; simpl_Forall; auto.
      + subst; right; do 2 esplit; eauto using PSF.add_1.
    - rewrite ? Forall_app. repeat split; simpl_Forall; try constructor.
      apply init_block_GoodLocals; auto.
  Qed.

  (** *** NoDupLocals *)

  Lemma init_block_NoDupLocals subinits : forall blk xs,
      unnested_block blk ->
      NoDupLocals xs (init_block subinits blk).
  Proof.
    induction blk using block_ind2; intros * Un; inv Un; simpl; cases; constructor; simpl_Forall; auto.
  Qed.

  Lemma init_top_block_NoDupLocals xs : forall outs locs blks outs' blks' locs' st st',
      Forall (AtomOrGensym norm1_prefs) xs ->
      Forall (fun x => AtomOrGensym norm1_prefs x \/ In x (st_ids st)) (map fst locs) ->
      Forall unnested_block blks ->
      NoDupLocals xs (Blocal (Scope locs blks)) ->
      init_top_block outs (Blocal (Scope locs blks)) st = (outs', Blocal (Scope locs' blks'), st') ->
      NoDupLocals xs (Blocal (Scope locs' blks')).
  Proof.
    intros * At1 At2 Un ND (* Good *) NL.
    unfold init_top_block in *.
    cases; repeat inv_bind; auto.
    inv ND. (* inv Good. *) repeat inv_scope.
    repeat constructor.
    - simpl_Forall. eapply init_block_NoDupLocals; eauto.
    - repeat apply NoDupMembers_app; eauto using fresh_idents_NoDup.
      + apply NoDupMembers_map; auto. intros; destruct_conjs; auto.
      + intros * In1 In2.
        simpl_In. simpl_Forall.
        destruct At2 as [|].
        * take (fresh_idents _ _ = _) and apply fresh_idents_prefixed in it. simpl_Forall; subst.
          eapply contradict_AtomOrGensym; eauto using last_not_in_norm1_prefs.
        * take (fresh_idents _ _ = _) and apply fresh_idents_nIn_ids in it. simpl_Forall; subst.
          contradiction.
    - intros * In1 In2.
      rewrite ? InMembers_app in In1. destruct In1 as [|]; simpl_In; simpl_Forall.
      + eapply H6; eauto; simpl; solve_In.
      + take (fresh_idents _ _ = _) and apply fresh_idents_prefixed in it. simpl_Forall; subst.
        eapply contradict_AtomOrGensym; eauto using last_not_in_norm1_prefs.
  Qed.

  (** *** The blocks stay unnested *)

  Lemma init_exp_normalized_constant sub : forall e,
      normalized_constant e ->
      normalized_constant (init_exp sub e).
  Proof.
    induction e using exp_ind2; intros * Norm; inv Norm; simpl_Forall;
      try constructor; auto.
  Qed.

  Lemma init_exp_normalized_lexp sub : forall e,
      normalized_lexp e ->
      normalized_lexp (init_exp sub e).
  Proof.
    induction e using exp_ind2; intros * Norm; inv Norm; simpl_Forall;
      try constructor; auto.
    simpl. cases; constructor.
  Qed.

  Lemma init_exp_normalized_cexp sub : forall e,
      normalized_cexp e ->
      normalized_cexp (init_exp sub e).
  Proof.
    induction e using exp_ind2; intros * Norm; inv Norm;
      try now (constructor; eauto using init_exp_normalized_lexp).
    1,2:(destruct_conjs; simpl; constructor; simpl_Forall; subst;
         eauto using init_exp_normalized_lexp).
    1,2:do 2 esplit; simpl; eauto; simpl_Forall; eauto.
    intros. inv_equalities. simpl in *.
    specialize (H7 _ eq_refl). destruct_conjs. subst.
    do 2 esplit; simpl; eauto. simpl_Forall. eauto.
  Qed.

  Lemma init_block_unnested sub : forall blk,
      unnested_block blk ->
      unnested_block (init_block sub blk).
  Proof.
    induction blk using block_ind2; intros * Un; inv Un; simpl.
    - (* equation *)
      constructor.
      inv H0; constructor; simpl_Forall; eauto using init_exp_normalized_lexp, init_exp_normalized_cexp.
      subst. eauto.
    - (* last *)
      cases; repeat constructor; eauto using init_exp_normalized_lexp.
      destruct (hd_ann _). constructor.
    - (* reset *)
      simpl_Forall. constructor; auto.
  Qed.

  Lemma init_top_block_unnested : forall outs blk outs' blk' st st',
      unnested outs blk ->
      NoDupMembers outs ->
      NoDupLocals (map fst outs) blk ->
      (exists ls, LastsDefined blk ls /\ Permutation ls (lasts_of_decls outs)) ->
      init_top_block outs blk st = (outs', blk', st') ->
      unnested outs' blk'.
  Proof.
    intros * Un ND1 ND2 Lasts NL.
    eapply init_top_block_vars in Un as VD; eauto.
    inv Un. simpl in *.
    repeat inv_bind; subst.
    constructor; eauto.
    - simpl_Forall; eauto using init_block_unnested.
    - destruct_conjs. do 2 esplit; eauto.
      symmetry. erewrite map_map, map_ext; eauto. intros; destruct_conjs; cases; auto.
  Qed.

  (** *** The last are initialized *)

  Inductive initialized_block : block -> Prop :=
  | IBeq : forall eq, initialized_block (Beq eq)
  | IBlast : forall x e, normalized_constant e -> initialized_block (Blast x e)
  | IBreset : forall e blk, initialized_block blk -> initialized_block (Breset [blk] e).

  Fact is_constant_normalized_constant : forall e,
      is_constant e = true ->
      normalized_constant e.
  Proof with eauto.
    intros * Hconst.
    induction e using exp_ind2; simpl in Hconst; try congruence.
    + constructor.
    + constructor.
    + cases. simpl_Forall. constructor; auto.
  Qed.

  Lemma init_block_initialized sub : forall blk,
      unnested_block blk ->
      (forall x, PS.In x (non_constant_lasts blk) -> Env.In x sub) ->
      initialized_block (init_block sub blk).
  Proof.
    induction blk using block_ind2; intros * Un Inits; inv Un; repeat inv_bind.
    - (* equation *)
      constructor.
    - (* last *)
      simpl. cases_eqn Eq.
      + constructor.
      + constructor. apply init_exp_normalized_constant.
        destruct (is_constant e) eqn:Const; auto using is_constant_normalized_constant.
        exfalso.
        eapply Env.Props.P.F.not_find_in_iff; eauto.
        apply Inits. simpl. rewrite Const. auto using PSF.singleton_2.
    - (* reset *)
      simpl_Forall. constructor. auto.
  Qed.

  Lemma init_top_block_initialized outs : forall locs blks outs' locs' blks' st st',
      (exists xs, LastsDefined (Blocal (Scope locs blks)) xs /\ Permutation xs (lasts_of_decls outs)) ->
      Forall unnested_block blks ->
      init_top_block outs (Blocal (Scope locs blks)) st = (outs', Blocal (Scope locs' blks'), st') ->
      Forall initialized_block blks'.
  Proof.
    intros * (?&LD&PermL) Un NL. simpl in *.
    inv LD. repeat Syn.inv_scope.
    repeat inv_bind; subst.
    simpl_Forall. eapply init_block_initialized; eauto.
    - intros * In1.
      inv_VarsDefined.
      eapply non_constant_lasts_Def in In1 as In2; eauto.
      eapply in_concat' in In2; eauto. rewrite H0, PermL in In2.
      unfold lasts_of_decls in *. apply in_app_iff in In2 as [|]; simpl_In; simpl_Forall; subst.
      1,2:eapply Env.In_from_list; erewrite <-fresh_idents_InMembers; eauto.
      1,2:eapply filter_InMembers; do 2 esplit.
      2,4:eapply PSF.mem_1, In_In_PSUnion; eauto; solve_In.
      1,2:apply in_app_iff. left. 2:right. 1,2:solve_In; simpl; eauto.
  Qed.

  (** ** Phase 2: Wellformedness properties *)

  Fact not_in_rename : forall x xs,
      ~InMembers x xs ->
      rename_var (Env.from_list xs) x = x.
  Proof.
    unfold rename_var, Env.from_list.
    intros * Hnin.
    destruct (Env.find x _) eqn:Hfind.
    - eapply Env.find_adds'_In in Hfind as [Hfind|Hfind].
      + exfalso. eapply Hnin; eauto using In_InMembers.
      + rewrite Env.gempty in Hfind. congruence.
    - apply Env.find_adds'_nIn in Hfind as (Hfind1&Hfind2); auto.
  Qed.

  (** *** VarsDefinedComp *)

  Lemma rename_block_vars : forall sub blk xs,
      unnested_block blk ->
      VarsDefinedComp blk xs ->
      exists ys, Forall2 VarsDefinedComp (rename_block sub blk) ys
            /\ Permutation (concat ys) (xs++map_filter (fun x => Env.find x sub) xs).
  Proof.
    induction blk using block_ind2; intros * Un Vars; inv Un; inv Vars; simpl.
    - (* equation *)
      inv H0; simpl.
      5:take (normalized_cexp _) and inv it; simpl; try take (normalized_lexp _) and inv it.
      all:try (unfold rename_var; destruct (Env.find x sub); do 2 esplit; repeat constructor; simpl).
      do 2 esplit. repeat constructor.
      + instantiate (1:=map_filter (fun x => match Env.find x sub with Some y => Some [y] | None => None end) xs).
        clear - xs. revert lann0. induction xs; intros; repeat constructor; auto.
        simpl. cases; repeat constructor; auto.
      + simpl. erewrite map_filter_ext, <-map_map_filter, concat_map_singl1; eauto.
    - (* last *)
      do 2 esplit. repeat constructor. reflexivity.
    - (* reset *)
      simpl_Forall. edestruct H3 as (?&VD&Perm); eauto.
      exists (map (fun x => concat [x]) x0). split. simpl_Forall.
      apply LVDCreset with (xs:=[b]). constructor; auto.
      simpl. setoid_rewrite app_nil_r. now rewrite map_id.
  Qed.

  Corollary map_rename_block_vars : forall sub blks xs,
      Forall unnested_block blks ->
      Forall2 VarsDefinedComp blks xs ->
      exists ys, Forall2 VarsDefinedComp (flat_map (rename_block sub) blks) ys
            /\ Permutation (concat ys) (concat xs++map_filter (fun x => Env.find x sub) (concat xs)).
  Proof.
    induction blks; intros * Un Vars; inv Un; inv Vars; simpl; eauto.
    edestruct rename_block_vars as (?&VD1&P1); eauto.
    edestruct IHblks as (?&VD2&P2); eauto.
    do 2 esplit.
    - apply Forall2_app; eauto.
    - rewrite ? concat_app, ? map_app, P1, P2.
      solve_Permutation_app.
  Qed.

  Lemma output_top_block_vars : forall outs blk blk' st st',
      unnested outs blk ->
      NoDupMembers outs ->
      NoDupLocals (map fst outs) blk ->
      output_top_block outs blk st = (blk', st') ->
      VarsDefinedComp blk' (map fst outs).
  Proof.
    intros * Un ND1 ND2 NL.
    inversion Un as [??? Syn1 (?&Vars&Perm)]; subst; clear Un.
    inv Vars. inv ND2. repeat inv_scope. repeat inv_bind.
    do 2 constructor.
    eapply map_rename_block_vars in H as (?&VD'&Perm'); eauto.
    do 2 esplit; eauto.
    - rewrite Perm', H0, Perm, ? map_filter_app, ? map_app, Permutation_app_comm with (l:=map fst locs), <- ? app_assoc.
      apply Permutation_app_head.
      rewrite Permutation_app_comm with (l':=map fst locs). apply Permutation_app_head.
      erewrite map_filter_nil with (xs:=map fst locs), app_nil_r.
      2:{ simpl_Forall. erewrite <-Env.Props.P.F.not_find_in_iff, Env.In_from_list, <-fresh_idents_InMembers; eauto.
          intros contra. eapply H7; eauto using In_InMembers. solve_In. }
      symmetry. erewrite ? map_map, map_ext with (l:=x1), fresh_idents_Perm with (sub:=Env.empty _); eauto.
      3:{ intros; destruct_conjs; auto. }
      2:{ apply NoDupMembers_map_filter; auto.
          intros; destruct_conjs; auto. take (option ident) and destruct it; simpl; auto. }
      assert (Forall (fun '(x, (_, _, _, o)) => Env.In x (Env.from_list (map fst x1)) <-> o <> None) outs) as NL.
      { simpl_Forall.
        erewrite Env.In_from_list, <-fresh_idents_InMembers; eauto; split; intros.
        - simpl_In. eapply NoDupMembers_det in H; eauto. inv H. congruence.
        - destruct o; try congruence. solve_In. auto.
      }
      unfold Env.from_list, or_default.
      clear - NL. induction NL; destruct_conjs; auto.
      destruct o; simpl.
      + cases_eqn Eq. exfalso.
        eapply Env.Props.P.F.not_find_in_iff, H; eauto. congruence.
      + cases_eqn Eq. exfalso.
        eapply H; auto. econstructor; eauto.
  Qed.

  (** *** LastsDefined *)

  Lemma rename_block_lasts : forall sub blk ls,
      unnested_block blk ->
      LastsDefined blk ls ->
      exists ys, Forall2 LastsDefined (rename_block sub blk) ys
            /\ Permutation (concat ys) (map (rename_var sub) ls).
  Proof.
    induction blk using block_ind2; intros * Un Lasts; inv Un; inv Lasts.
    - (* equation *)
      inv H0; simpl.
      5:take (normalized_cexp _) and inv it; simpl; try take (normalized_lexp _) and inv it.
      all:try (unfold rename_var; destruct (Env.find x sub); do 2 esplit; repeat constructor; simpl).
      do 2 esplit. repeat constructor.
      + instantiate (1:=map_filter (fun x => match Env.find x sub with Some y => Some [] | None => None end) xs).
        clear - xs. revert lann0. induction xs; intros; repeat constructor; auto.
        simpl. cases; repeat constructor; auto.
      + simpl. erewrite map_filter_ext, <-map_map_filter with (f:=fun x => match Env.find x sub with Some _ => Some x | None => None end), concat_map_nil; eauto.
        intros; simpl; cases; auto.
    - (* last *)
      do 2 esplit. repeat constructor. reflexivity.
    - (* reset *)
      simpl_Forall. edestruct H3 as (?&VD&Perm); eauto.
      exists (map (fun x => concat [x]) x0). split. simpl_Forall.
      apply LDreset with (xs:=[b]). constructor; auto.
      simpl. setoid_rewrite app_nil_r. now rewrite map_id.
  Qed.

  Corollary map_rename_block_lasts : forall sub blks xs,
      Forall unnested_block blks ->
      Forall2 LastsDefined blks xs ->
      exists ys, Forall2 LastsDefined (flat_map (rename_block sub) blks) ys
            /\ Permutation (concat ys) (map (rename_var sub) (concat xs)).
  Proof.
    induction blks; intros * Un Vars; inv Un; inv Vars; simpl; eauto.
    edestruct rename_block_lasts as (?&VD1&P1); eauto.
    edestruct IHblks as (?&VD2&P2); eauto.
    do 2 esplit.
    - apply Forall2_app; eauto.
    - rewrite ? concat_app, ? map_app, P1, P2.
      solve_Permutation_app.
  Qed.

  Lemma output_top_block_lasts : forall outs blk blk' st st',
      unnested outs blk ->
      LastsDefined blk (lasts_of_decls outs) ->
      NoDupMembers outs ->
      NoDupLocals (map fst outs) blk ->
      output_top_block outs blk st = (blk', st') ->
      LastsDefined blk' [].
  Proof.
    unfold output_top_block.
    intros * Un LD Nd1 Nd2 DL. inv Un. inv Nd2. repeat inv_bind.
    inv LD. repeat inv_scope. repeat constructor. simpl.
    eapply map_rename_block_lasts in H2 as (?&LD&Perm); eauto.
    do 2 esplit; eauto.
    - unfold lasts_of_decls in *. erewrite Perm, H4, map_app, map_filter_app.
      rewrite Permutation_app_comm. apply Permutation_app.
      + erewrite map_ext_in, map_id; auto.
        intros * In.
        apply not_in_rename. erewrite <-fresh_idents_InMembers; eauto.
        intros In2. simpl_In.
        eapply H11; solve_In.
      + eapply fresh_idents_Perm in H1 as P.
        2:{ apply NoDupMembers_map_filter; auto. intros; destruct_conjs; auto. destruct o; simpl; auto. }
        rewrite map_map, map_map_filter in P.
        erewrite map_map_filter, map_filter_ext, <-P.
        2:intros; destruct_conjs; auto; destruct o; simpl; eauto; reflexivity.
        clear - x. induction x as [|((?&?)&(?&?))]; simpl; auto.
  Qed.

  (** *** GoodLocals *)

  Lemma rename_block_GoodLocals sub : forall blk,
      GoodLocals last_prefs blk ->
      Forall (GoodLocals last_prefs) (rename_block sub blk).
  Proof.
    induction blk using block_ind2; intros * Hnd; simpl; auto.
    - (* equation *)
      simpl_Forall. constructor.
    - (* last *)
      simpl_Forall. constructor.
    - (* reset *)
      cases; auto.
      inv Hnd. simpl_Forall.
      repeat constructor. specialize (H2 H3). simpl_Forall. eauto.
  Qed.

  Lemma output_top_block_GoodLocals : forall outs blk blk' st st',
      GoodLocals last_prefs blk ->
      output_top_block outs blk st = (blk', st') ->
      GoodLocals last_prefs blk'.
  Proof.
    intros * Good NL.
    unfold output_top_block in *.
    cases; repeat inv_bind; auto.
    inv Good. repeat inv_scope.
    repeat constructor.
    - repeat (take (fresh_idents _ _ = _) and apply fresh_idents_prefixed in it).
      rewrite ? map_app, ? Forall_app. repeat split; simpl_Forall; auto.
      subst; right; do 2 esplit; eauto using PSF.add_1.
    - apply Forall_flat_map. simpl_Forall.
      eapply rename_block_GoodLocals, Forall_forall in H4; eauto.
  Qed.

  (** *** NoDupLocals *)

  Lemma rename_block_NoDupLocals sub : forall blk xs,
      unnested_block blk ->
      Forall (NoDupLocals xs) (rename_block sub blk).
  Proof.
    induction blk using block_ind2; intros * Un; inv Un; auto; simpl.
    - (* equation *)
      simpl_Forall. constructor.
    - (* last *)
      simpl_Forall. cases; constructor.
    - (* reset *)
      simpl_Forall. repeat constructor.
      specialize (H3 xs H1). simpl_Forall; auto.
  Qed.

  Lemma output_top_block_NoDupLocals : forall outs locs blks xs blks' locs' st st',
      Forall (AtomOrGensym norm1_prefs) xs ->
      Forall (fun x => AtomOrGensym norm1_prefs x \/ In x (st_ids st)) (map fst locs) ->
      Forall unnested_block blks ->
      NoDupLocals xs (Blocal (Scope locs blks)) ->
      output_top_block outs (Blocal (Scope locs blks)) st = (Blocal (Scope locs' blks'), st') ->
      NoDupLocals xs (Blocal (Scope locs' blks')).
  Proof.
    intros * At1 At2 Un ND NL.
    unfold output_top_block in *.
    cases; repeat inv_bind; auto.
    inv ND. (* inv Good. *) repeat inv_scope.
    repeat constructor.
    - apply Forall_flat_map. simpl_Forall.
      eapply rename_block_NoDupLocals, Forall_forall in Un; eauto.
    - repeat apply NoDupMembers_app; auto.
      + eapply fresh_idents_NoDup in H.
        erewrite fst_NoDupMembers, map_map, map_ext, <-map_map, <-fst_NoDupMembers; eauto. intros; destruct_conjs; auto.
      + intros * In1 In2.
        simpl_In. simpl_Forall.
        destruct At2 as [|].
        * take (fresh_idents _ _ = _) and apply fresh_idents_prefixed in it. simpl_Forall; subst.
          eapply contradict_AtomOrGensym; eauto using last_not_in_norm1_prefs.
        * take (fresh_idents _ _ = _) and apply fresh_idents_nIn_ids in it. simpl_Forall; subst.
          contradiction.
    - intros * In1 In2.
      rewrite ? InMembers_app in In1. destruct In1 as [|]; simpl_In; simpl_Forall.
      + eapply H6; eauto. solve_In.
      + take (fresh_idents _ _ = _) and apply fresh_idents_prefixed in it. simpl_Forall; subst.
        eapply contradict_AtomOrGensym; eauto using last_not_in_norm1_prefs.
  Qed.

  (** *** The blocks stay unnested *)

  Lemma rename_exp_normalized_constant sub : forall e,
      normalized_constant e ->
      normalized_constant (rename_exp sub e).
  Proof.
    induction e using exp_ind2; intros * Norm; inv Norm; simpl_Forall;
      try constructor; auto.
  Qed.

  Lemma rename_exp_normalized_lexp sub : forall e,
      normalized_lexp e ->
      normalized_lexp (rename_exp sub e).
  Proof.
    induction e using exp_ind2; intros * Norm; inv Norm; simpl_Forall;
      try constructor; auto.
  Qed.

  Lemma rename_exp_normalized_cexp sub : forall e,
      normalized_cexp e ->
      normalized_cexp (rename_exp sub e).
  Proof.
    induction e using exp_ind2; intros * Norm; inv Norm;
      try now (constructor; eauto using rename_exp_normalized_lexp).
    1,2:(destruct_conjs; simpl; constructor; simpl_Forall; subst;
         eauto using rename_exp_normalized_lexp).
    1,2:do 2 esplit; simpl; eauto; simpl_Forall; eauto.
    intros. inv_equalities. simpl in *.
    specialize (H7 _ eq_refl). destruct_conjs. subst.
    do 2 esplit; simpl; eauto. simpl_Forall. eauto.
  Qed.

  Lemma rename_block_unnested sub : forall blk,
      unnested_block blk ->
      Forall unnested_block (rename_block sub blk).
  Proof.
    induction blk using block_ind2; intros * Un; inv Un; simpl.
    - (* equation *)
      inv H0; simpl.
      + (* app *)
        repeat constructor.
        1-3:simpl_Forall; subst; simpl; eauto using rename_exp_normalized_lexp.
        clear - xs. revert lann0.
        induction xs; intros *; simpl; cases; repeat constructor; auto.
        destruct (hd_ann _); constructor.
      + (* fby *)
        cases; destruct_conjs; repeat constructor; eauto using rename_exp_normalized_lexp.
      + (* arrow *)
        cases; destruct_conjs; repeat constructor; eauto using rename_exp_normalized_lexp.
      + (* extcall *)
        cases; destruct_conjs; repeat constructor; simpl_Forall; eauto using rename_exp_normalized_lexp.
      + (* cexp *)
        eapply rename_exp_normalized_cexp in H as N1.
        take (normalized_cexp e) and inv it; try take (normalized_lexp _) and inv it.
        all:simpl; cases; repeat (constructor; eauto).
    - (* last *)
      cases; repeat constructor; eauto using rename_exp_normalized_lexp.
    - (* reset *)
      simpl_Forall. specialize (H3 H1). simpl_Forall. constructor; auto.
  Qed.

  Definition remove_lasts (outs: list decl) : list decl :=
    map (fun xtc => (fst xtc, (fst (fst (fst (snd xtc))), snd (fst (fst (snd xtc))), xH, None))) outs.

  Fact remove_lasts_fst : forall outs,
      map fst (remove_lasts outs) = map fst outs.
  Proof.
    intros *. unfold remove_lasts.
    rewrite map_map; auto.
  Qed.

  Lemma output_top_block_unnested : forall outs blk blk' st st',
      unnested outs blk ->
      NoDupMembers outs ->
      NoDupLocals (map fst outs) blk ->
      output_top_block outs blk st = (blk', st') ->
      unnested (remove_lasts outs) blk'.
  Proof.
    intros * Un ND1 ND2 NL.
    eapply output_top_block_vars in Un as VD; eauto.
    inv Un. simpl in *.
    repeat inv_bind; subst.
    constructor; eauto.
    apply Forall_flat_map. simpl_Forall.
    eapply rename_block_unnested, Forall_forall in H; eauto.
    rewrite remove_lasts_fst; eauto.
  Qed.

  (** *** The blocks stay initialized. *)

  Lemma rename_block_initialized sub : forall blk,
      initialized_block blk ->
      Forall initialized_block (rename_block sub blk).
  Proof.
    induction blk using block_ind2; intros * Un; inv Un; simpl.
    - (* equation *)
      simpl_Forall. constructor.
    - (* last *)
      simpl_Forall. constructor; auto using rename_exp_normalized_constant.
    - (* reset *)
      simpl_Forall. specialize (H3 H1). simpl_Forall. constructor; auto.
  Qed.

  Lemma output_top_block_initialized outs : forall locs blks locs' blks' st st',
      Forall initialized_block blks ->
      output_top_block outs (Blocal (Scope locs blks)) st = (Blocal (Scope locs' blks'), st') ->
      Forall initialized_block blks'.
  Proof.
    intros * In Un.
    repeat inv_bind; subst.
    apply Forall_flat_map. simpl_Forall.
    eapply rename_block_initialized, Forall_forall in In; eauto.
  Qed.

  (** ** Phase 3: Wellformedness properties *)

  (** *** VarsDefinedComp *)

  Lemma unnest_block_vars : forall sub blk xs,
      unnested_block blk ->
      VarsDefinedComp blk xs ->
      VarsDefinedComp (unnest_block sub blk) xs.
  Proof.
    induction blk using block_ind2; intros * Un Vars; inv Un.
    - (* equation *)
      destruct eq. inv Vars. simpl. constructor.
    - (* last *)
      inv Vars. simpl. constructor.
    - (* reset *)
      inv Vars. simpl_Forall.
      replace (y++[]) with (concat [y]) by auto.
      repeat constructor; eauto.
  Qed.

  Corollary map_unnest_block_vars : forall sub blks xs,
      Forall unnested_block blks ->
      Forall2 VarsDefinedComp blks xs ->
      Forall2 VarsDefinedComp (map (unnest_block sub) blks) xs.
  Proof.
    induction blks; intros * Un Vars; inv Un; inv Vars; simpl; constructor; eauto using unnest_block_vars.
  Qed.

  Lemma unnest_top_block_vars : forall outs blk blk' st st',
      unnested outs blk ->
      unnest_top_block blk st = (blk', st') ->
      VarsDefinedComp blk' (map fst outs).
  Proof.
    intros * Un (* ND1 ND2 *) NL.
    inversion Un as [??? Syn1 (?&Vars&Perm)]; subst; clear Un.
    inv Vars. repeat inv_scope. repeat inv_bind.
    do 2 constructor.
    eapply map_unnest_block_vars in H; eauto.
    do 2 esplit.
    - repeat apply Forall2_app; eauto.
      erewrite Forall2_map_1, Forall2_map_2 with (f:=fun '(_, x, _) => [x]).
      apply Forall2_same. simpl_Forall. constructor.
    - rewrite ? concat_app, H0, Perm.
      rewrite Permutation_app_comm, <-app_assoc, map_app, ? map_map. apply Permutation_app_head.
      erewrite map_ext with (l:=x1), <-map_map with (l:=x1), concat_map_singl1.
      apply Permutation_app_tail. 2:intros; destruct_conjs; auto.
      erewrite map_ext; eauto. intros; destruct_conjs; auto.
  Qed.

  (** *** LastsDefined *)

  Lemma unnest_block_lasts : forall blk sub ls,
      unnested_block blk ->
      LastsDefined blk ls ->
      LastsDefined (unnest_block sub blk) (map (rename_var sub) ls).
  Proof.
    induction blk using block_ind2; intros * Un Lasts; inv Un; inv Lasts; simpl.
    - (* equation *)
      cases. constructor.
    - (* last *)
      constructor.
    - (* reset *)
      rewrite concat_map. constructor. simpl_Forall.
  Qed.

  Lemma unnest_top_block_lasts : forall outs blk blk' st st',
      unnested outs blk ->
      LastsDefined blk [] ->
      NoDupLocals (map fst outs) blk ->
      unnest_top_block blk st = (blk', st') ->
      LastsDefined blk' [].
  Proof.
    intros * Un LD ND DL.
    unfold unnest_top_block in *.
    inv Un; repeat inv_bind; auto.
    inv LD. inv ND. repeat inv_scope.
    repeat constructor. do 2 esplit.
    - eapply Forall2_app with (l1':=map (fun x => []) x) (l2':=map _ x0); simpl_Forall.
      + constructor.
      + eapply unnest_block_lasts; eauto.
    - simpl. erewrite concat_app, concat_map_nil, <-concat_map, H3; simpl.
      symmetry. unfold lasts_of_decls.
      erewrite map_filter_app.
      assert (map_filter (fun '(x2, (_, _, _, o)) => option_map (fun _ : ident => x2) o)
                (map (fun '(_, lx, (ty, ck)) => (lx, (ty, ck, xH, Some xH))) x)
             = map (fun '(_, lx, _) => lx) x) as Eq; [|setoid_rewrite Eq; clear Eq].
      1:{ clear - x. induction x as [|((?&?)&(?&?))]; simpl; auto. }
      erewrite fresh_idents_Perm with (sub:=Env.empty _); eauto.
      2:{ apply NoDupMembers_filter, NoDupMembers_map_filter; auto.
          intros; destruct_conjs. destruct o; simpl; auto. }
      assert (Forall (fun '(x1, (_, _, _, o)) =>
                          Env.In x1 (Env.from_list (map fst x))
                          <-> o <> None /\ PS.mem x1 (PSUnion (map non_cexp_defs blks)) = true) locs) as NL.
      { simpl_Forall.
        erewrite Env.In_from_list, <-fresh_idents_InMembers; eauto.
        split; intros In.
        + simpl_In; split; auto.
          eapply NoDupMembers_det in H5; eauto. inv H5. congruence.
        + destruct_conjs. destruct o; try congruence.
          solve_In. auto.
      }
      clear - NL. induction NL as [|(?&(((?&?)&?)&?))]; simpl; auto.
      destruct o, (PS.mem _ _) eqn:Mem; simpl; auto.
      + rewrite Mem; simpl. rewrite <-Permutation_middle. constructor; auto.
      + rewrite Mem. unfold rename_var, or_default.
        destruct (Env.find _ _) eqn:Find; [|constructor; eauto].
        exfalso.
        apply Env.find_In, H in Find as (?&?). congruence.
  Qed.

  (** *** GoodLocals *)

  Lemma unnest_block_GoodLocals sub : forall blk,
      GoodLocals last_prefs blk ->
      GoodLocals last_prefs (unnest_block sub blk).
  Proof.
    induction blk using block_ind2; intros * Hnd; simpl; auto.
    - (* equation *)
      cases. constructor.
    - (* last *)
      constructor.
    - (* reset *)
      cases; auto.
      inv Hnd. simpl_Forall.
      constructor. auto.
  Qed.

  Lemma unnest_top_block_GoodLocals : forall blk blk' st st',
      GoodLocals last_prefs blk ->
      unnest_top_block blk st = (blk', st') ->
      GoodLocals last_prefs blk'.
  Proof.
    intros * Good NL.
    unfold unnest_top_block in *.
    cases; repeat inv_bind; auto.
    inv Good. repeat inv_scope.
    repeat constructor.
    - repeat (take (fresh_idents _ _ = _) and apply fresh_idents_prefixed in it).
      rewrite ? map_app, ? Forall_app. repeat split; simpl_Forall; auto.
      subst; right; do 2 esplit; eauto using PSF.add_1.
    - rewrite ? Forall_app. repeat split; simpl_Forall; try constructor.
      apply unnest_block_GoodLocals; auto.
  Qed.

  (** *** NoDupLocals *)

  Lemma unnest_block_NoDupLocals sub : forall blk xs,
      unnested_block blk ->
      NoDupLocals xs (unnest_block sub blk).
  Proof.
    induction blk using block_ind2; intros * Un; inv Un; simpl; cases; constructor; simpl_Forall; auto.
  Qed.

  Lemma unnest_top_block_NoDupLocals xs : forall locs blks blks' locs' st st',
      Forall (AtomOrGensym norm1_prefs) xs ->
      Forall (fun x => AtomOrGensym norm1_prefs x \/ In x (st_ids st)) (map fst locs) ->
      Forall unnested_block blks ->
      NoDupLocals xs (Blocal (Scope locs blks)) ->
      unnest_top_block (Blocal (Scope locs blks)) st = (Blocal (Scope locs' blks'), st') ->
      NoDupLocals xs (Blocal (Scope locs' blks')).
  Proof.
    intros * At1 At2 Un ND (* Good *) NL.
    unfold init_top_block in *.
    cases; repeat inv_bind; auto.
    inv ND. (* inv Good. *) repeat inv_scope.
    repeat constructor.
    - apply Forall_app; split; simpl_Forall.
      + constructor.
      + eapply unnest_block_NoDupLocals; eauto.
    - apply NoDupMembers_app.
      + apply NoDupMembers_map; auto.
        intros; destruct_conjs; auto.
      + eapply fresh_idents_NoDup in H.
        erewrite fst_NoDupMembers, map_map, map_ext, <-map_map, <-fst_NoDupMembers; eauto. intros; destruct_conjs; auto.
      + intros * In1 In2.
        simpl_In. simpl_Forall.
        destruct At2 as [|].
        * take (fresh_idents _ _ = _) and apply fresh_idents_prefixed in it. simpl_Forall; subst.
          eapply contradict_AtomOrGensym; eauto using last_not_in_norm1_prefs.
        * take (fresh_idents _ _ = _) and apply fresh_idents_nIn_ids in it. simpl_Forall; subst.
          contradiction.
    - intros * In1 In2.
      rewrite ? InMembers_app in In1. destruct In1 as [|]; simpl_In; simpl_Forall.
      + eapply H6; eauto. solve_In.
      + take (fresh_idents _ _ = _) and apply fresh_idents_prefixed in it. simpl_Forall; subst.
        eapply contradict_AtomOrGensym; eauto using last_not_in_norm1_prefs.
  Qed.

  (** *** The blocks stay unnested. *)

  Lemma unnest_block_unnested sub : forall blk,
      unnested_block blk ->
      unnested_block (unnest_block sub blk).
  Proof.
    induction blk using block_ind2; intros * Un; inv Un; simpl.
- (* equation *)
      inv H0; simpl.
      + (* app *)
        repeat constructor.
        1-3:simpl_Forall; subst; simpl; eauto using rename_exp_normalized_lexp.
      + (* fby *)
        cases; destruct_conjs; repeat constructor; eauto using rename_exp_normalized_lexp.
      + (* arrow *)
        cases; destruct_conjs; repeat constructor; eauto using rename_exp_normalized_lexp.
      + (* extcall *)
        cases; destruct_conjs; repeat constructor; simpl_Forall; eauto using rename_exp_normalized_lexp.
      + (* cexp *)
        eapply rename_exp_normalized_cexp in H as N1.
        take (normalized_cexp e) and inv it; try take (normalized_lexp _) and inv it.
        all:simpl; cases; repeat (constructor; eauto).
    - (* last *)
      cases; repeat constructor; eauto using rename_exp_normalized_lexp.
    - (* reset *)
      simpl_Forall. specialize (H3 H1). simpl_Forall. constructor; auto.
  Qed.

  Lemma unnest_top_block_unnested : forall outs blk blk' st st',
      unnested outs blk ->
      NoDupMembers outs ->
      NoDupLocals (map fst outs) blk ->
      unnest_top_block blk st = (blk', st') ->
      unnested outs blk'.
  Proof.
    intros * Un ND1 ND2 NL.
    eapply unnest_top_block_vars in Un as VD; eauto.
    inv Un. simpl in *.
    repeat inv_bind; subst.
    constructor; eauto.
    apply Forall_app; split; simpl_Forall; eauto using unnest_block_unnested.
    repeat constructor.
  Qed.

  (** *** The blocks stay initialized. *)

  Lemma unnest_block_initialized sub : forall blk,
      initialized_block blk ->
      initialized_block (unnest_block sub blk).
  Proof.
    induction blk using block_ind2; intros * Un; inv Un; simpl.
    - (* equation *)
      cases. constructor.
    - (* last *)
      constructor; auto using rename_exp_normalized_constant.
    - (* reset *)
      simpl_Forall. constructor; auto.
  Qed.

  Lemma unnest_top_block_initialized : forall locs blks locs' blks' st st',
      Forall initialized_block blks ->
      unnest_top_block (Blocal (Scope locs blks)) st = (Blocal (Scope locs' blks'), st') ->
      Forall initialized_block blks'.
  Proof.
    intros * In Un.
    repeat inv_bind; subst. apply Forall_app; split; simpl_Forall; eauto using unnest_block_initialized.
    constructor.
  Qed.

  (** *** Lasts are only defined by cexps *)

  Inductive last_cexp_eq (lasts : list ident) : equation -> Prop :=
  | LCEapp : forall xs f es er lann,
      Forall (fun x => ~In x lasts) xs -> last_cexp_eq lasts (xs, [Eapp f es er lann])
  | LCEfby : forall x e0 e ann,
      ~In x lasts -> last_cexp_eq lasts ([x], [Efby [e0] [e] [ann]])
  | LCEarrow : forall x e0 e ann,
      last_cexp_eq lasts ([x], [Earrow [e0] [e] [ann]])
  | LCEextcall : forall x f es ann,
      ~In x lasts -> last_cexp_eq lasts ([x], [Eextcall f es ann])
  | LCEcexp : forall x e,
      normalized_cexp e -> last_cexp_eq lasts ([x], [e]).

  Inductive last_cexp_block (lasts : list ident) : block -> Prop :=
  | LCEq : forall eq, last_cexp_eq lasts eq -> last_cexp_block lasts (Beq eq)
  | LCLast : forall x e, last_cexp_block lasts (Blast x e)
  | LCReset : forall e blk, last_cexp_block lasts blk -> last_cexp_block lasts (Breset [blk] e).

  Lemma unnest_block_cexp lasts sub : forall blk,
      unnested_block blk ->
      (forall x, PS.In x (non_cexp_defs blk) -> ~In x lasts) ->
      last_cexp_block lasts (unnest_block sub blk).
  Proof.
    induction blk using block_ind2; intros * Un Sub; inv Un; simpl.
    - (* equation *)
      cases. constructor. unfold rename_var.
      inv H0; simpl in *; constructor; eauto using rename_exp_normalized_cexp.
      + simpl_Forall. eapply Sub. cases; apply In_of_list; eauto.
      + apply Sub. apply PSF.singleton_2; auto.
      + apply Sub. apply PSF.singleton_2; auto.
    - (* last *)
      constructor; auto.
    - (* reset *)
      simpl_Forall. constructor; auto.
  Qed.

  Fact non_cexp_defs_Def : forall x blk xs,
      PS.In x (non_cexp_defs blk) ->
      VarsDefinedComp blk xs ->
      In x xs.
  Proof.
    induction blk using block_ind2; intros * In VD; inv VD; simpl in *; cases;
      try apply not_In_empty in In as [];
      try apply PSF.singleton_1 in In; subst; try now repeat constructor.
    - (* app *)
      apply In_of_list in In; auto.
    - (* reset *)
      simpl_Forall. rewrite app_nil_r. eauto.
  Qed.

  Corollary map_non_cexp_defs_Def : forall x blks xs,
      PS.In x (PSUnion (map non_cexp_defs blks)) ->
      Forall2 VarsDefinedComp blks xs ->
      In x (concat xs).
  Proof.
    intros * In1 LD.
    eapply PSUnion_In_In in In1 as (?&In1&In2).
    simpl_In. inv_VarsDefined.
    eapply in_concat; do 2 esplit; eauto using non_cexp_defs_Def.
  Qed.

  Lemma unnest_top_block_cexp : forall outs locs blks locs' blks' st st',
      unnested outs (Blocal (Scope locs blks)) ->
      NoDupMembers locs ->
      Forall (AtomOrGensym norm1_prefs) (map fst outs) ->
      Forall (fun x => AtomOrGensym norm1_prefs x \/ In x (st_ids st)) (map fst locs) ->
      unnest_top_block (Blocal (Scope locs blks)) st = (Blocal (Scope locs' blks'), st') ->
      Forall (last_cexp_block (lasts_of_decls locs')) blks'.
  Proof.
    intros * Un ND At1 At2 In. inv Un.
    repeat inv_bind; subst. apply Forall_app; split; simpl_Forall; eauto using unnest_block_initialized.
    - repeat constructor.
    - eapply unnest_block_cexp; eauto.
      intros * Hin.
      eapply fresh_idents_NoDupMembers in H as ND'.
      2:{ apply NoDupMembers_filter, NoDupMembers_map_filter; auto.
          intros; destruct_conjs; destruct o; simpl; auto. }
      eapply fresh_idents_prefixed in H as Pref.
      eapply fresh_idents_nIn_ids in H as Nin.
      unfold lasts_of_decls in *. rewrite map_filter_app, not_In_app; split.
      + intros * In1. simpl_In.
        rewrite PSF.mem_1 in H9; [congruence|].
        eapply In_In_PSUnion; eauto. solve_In.
      + destruct (in_dec ident_eq_dec x2 (lasts_of_decls locs)); unfold lasts_of_decls in *.
        * intros * In2. simpl_In. simpl_Forall. subst.
          destruct At2; eauto.
          eapply contradict_AtomOrGensym; eauto using last_not_in_norm1_prefs.
        * intros * In2. simpl_In.
          inv H0. inv_scope.
          eapply map_non_cexp_defs_Def in H0 as Def; [|eapply In_In_PSUnion; eauto; solve_In].
          rewrite H4, H1, in_app_iff in Def. destruct Def as [|]; simpl_In; simpl_Forall; subst.
          2:destruct At2; eauto. 1,2:eapply contradict_AtomOrGensym; eauto using last_not_in_norm1_prefs.
  Qed.

  (** *** Composition of the three functions *)

  Global Hint Resolve unnest_top_block_unnested : normlast.
  Global Hint Resolve init_top_block_GoodLocals output_top_block_GoodLocals unnest_top_block_GoodLocals : normlast.
  Global Hint Resolve init_top_block_initialized output_top_block_initialized unnest_top_block_initialized : normlast.

  Definition normlast_top_block outs blk :=
    do (outs, blk) <- init_top_block outs blk;
    do blk <- output_top_block outs blk;
    unnest_top_block blk.

  Lemma unnested_normlast_block lasts : forall blk,
      unnested_block blk ->
      initialized_block blk ->
      last_cexp_block lasts blk ->
      normlast_block lasts blk.
  Proof.
    induction blk using block_ind2; intros * Un In L; inv Un; inv In; inv L.
    - (* equation *)
      constructor. inv H0; inv H1; constructor; auto.
      all:take (normalized_cexp _) and inv it; take (normalized_lexp _) and inv it.
    - (* last *)
      constructor; auto.
    - (* reset *)
      simpl_Forall. constructor; auto.
  Qed.

  Lemma normlast_top_block_props : forall ins outs blk blk' st st',
      unnested outs blk ->
      (exists ls : list ident, LastsDefined blk ls /\ Permutation ls (lasts_of_decls outs)) ->
      NoDupMembers outs ->
      NoDupLocals (ins ++ map fst outs) blk ->
      Forall (AtomOrGensym norm1_prefs) (ins ++ map fst outs) ->
      GoodLocals norm1_prefs blk ->
      normlast_top_block outs blk st = (blk', st') ->
      normlast (remove_lasts outs) blk'
      /\ LastsDefined blk' []
      /\ NoDupLocals (ins ++ map fst outs) blk'
      /\ GoodLocals last_prefs blk'.
  Proof.
    intros * Un Lasts NDo ND At Good NL.
    unfold normlast_top_block in *. repeat inv_bind.
    eapply init_top_block_unnested in H as Un1; eauto.
    inversion Un. inversion Un1. subst.
    assert (Forall (fun x : ident => AtomOrGensym norm1_prefs x \/ In x (st_ids st)) (map fst locs)) as AtL0.
    { inv Good. repeat inv_scope. simpl_Forall. auto. }
    2:{ eapply NoDupLocals_incl; [|eauto]. solve_incl_app. }
    eapply init_top_block_NoDupLocals with (xs:=ins ++ map fst outs) in H as ND1; eauto.
    assert (map fst x = map fst outs) as Fst.
    { clear - H. repeat inv_bind. erewrite map_map, map_ext; [reflexivity|].
      intros; destruct_conjs; cases; auto.
    }
    assert (NoDupMembers x) as NDo1.
    { now rewrite fst_NoDupMembers, Fst, <-fst_NoDupMembers. }
    assert (NoDupLocals (map fst x) (Blocal (Scope locs0 blks0))) as ND'1.
    { rewrite Fst. eapply NoDupLocals_incl; [|eauto]. apply incl_appr, incl_refl. }
    eapply output_top_block_unnested in H0 as Un2; eauto.
    inversion Un2; subst.
    assert (Forall (fun x => AtomOrGensym norm1_prefs x \/ In x (st_ids x1)) (map fst locs0)) as AtL1.
    { clear - H AtL0. repeat inv_bind. rewrite map_app, Forall_app. split.
      + simpl_Forall. destruct AtL0; auto.
        right. eapply incl_map; eauto. apply st_follows_incl; eauto using fresh_idents_st_follows.
      + eapply fresh_idents_In_ids in H. simpl_Forall. auto.
    }
    assert (Forall (fun x => AtomOrGensym norm1_prefs x \/ In x (st_ids x3)) (map fst locs1)) as AtL2.
    { clear - H0 AtL1. repeat inv_bind. rewrite map_app, Forall_app. split.
      + simpl_Forall. destruct AtL1; auto.
        right. eapply incl_map; eauto. apply st_follows_incl; eauto using fresh_idents_st_follows.
      + eapply fresh_idents_In_ids in H. simpl_Forall. auto.
    }
    eapply output_top_block_NoDupLocals with (outs:=x) in H0 as ND2; eauto.
    eapply unnest_top_block_unnested in H1 as Un3; eauto.
    2:{ rewrite fst_NoDupMembers, remove_lasts_fst, <-fst_NoDupMembers; eauto. }
    2:{ eapply NoDupLocals_incl; [|eauto]. apply incl_appr. rewrite remove_lasts_fst.
        clear - H. repeat inv_bind. erewrite map_map, map_ext; [reflexivity|].
        intros; destruct_conjs; cases; auto.
    }
    inversion Un3; subst.
    eapply unnest_top_block_NoDupLocals with (xs:=ins++map fst outs) in H1 as ND3; eauto.

    eapply unnest_top_block_initialized in H1 as Init; eauto with normlast.
    eapply unnest_top_block_cexp in H1 as Cexp; eauto.
    2:{ inv ND2. inv_scope. auto. }
    2:{ apply Forall_app in At as (?&?). rewrite remove_lasts_fst, Fst; auto. }

    split; [|split; [|split]]; eauto using GoodLocals_add with normlast.
    - constructor; auto.
      + unfold remove_lasts. simpl_Forall. auto.
      + simpl_Forall.
        eapply unnested_normlast_block; eauto.
      + rewrite remove_lasts_fst, <-Fst, <-remove_lasts_fst; auto.
    - eapply unnest_top_block_lasts in H1; eauto.
      2:{ eapply NoDupLocals_incl; eauto. rewrite remove_lasts_fst, Fst; solve_incl_app. }
      eapply output_top_block_lasts in H0; eauto.
      eapply init_top_block_lasts in H; eauto.
      eapply NoDupLocals_incl; [|eauto]. solve_incl_app.
  Qed.

  Corollary normlast_node_props : forall (n: @node unnested norm1_prefs) blk' st st',
      normlast_top_block (n_out n) (n_block n) st = (blk', st') ->
      normlast (remove_lasts (n_out n)) blk'
      /\ LastsDefined blk' []
      /\ NoDupLocals (map fst (n_in n)++map fst (n_out n)) blk' (* Non, xs *)
      /\ GoodLocals last_prefs blk'.
  Proof.
    intros * NL.
    pose proof n.(n_nodup) as (ND1&ND2).
    pose proof n.(n_good) as (Good1&Good2&_).
    eapply normlast_top_block_props; eauto.
    - apply n.(n_syn).
    - apply n.(n_lastd).
    - apply fst_NoDupMembers; eauto using NoDup_app_r.
  Qed.

  (** ** Transformation of node and program *)

  Program Definition normlast_node (n: @node unnested norm1_prefs) : @node normlast last_prefs :=
    let res := normlast_top_block (n_out n) (n_block n) init_st in
    {|
      n_name := (n_name n);
      n_hasstate := (n_hasstate n);
      n_in := (n_in n);
      n_out := remove_lasts (n_out n);
      n_block := fst res;
      n_ingt0 := (n_ingt0 n);
      n_outgt0 := (n_outgt0 n);
    |}.
  Next Obligation.
    unfold remove_lasts. now rewrite length_map.
  Qed.
  Next Obligation.
    destruct (normlast_top_block _ _) as (?&?) eqn:Hdl.
    eapply normlast_node_props in Hdl as (Norm&_&ND&_).
    inversion Norm; subst. destruct H1 as (?&VD&Perm).
    apply Permutation_map_inv in Perm as (outs'&?&Perm1); subst.
    exists (senv_of_decls (remove_lasts outs')). split.
    - eapply VarsDefinedComp_VarsDefined; simpl; eauto.
      2:rewrite map_fst_senv_of_decls, remove_lasts_fst; eauto.
      rewrite map_fst_senv_of_decls, remove_lasts_fst, <-Perm1, remove_lasts_fst.
      eapply NoDupLocals_incl; [|eauto]. solve_incl_app.
    - unfold remove_lasts, senv_of_decls in *. rewrite <-Perm1, ? map_map; simpl.
      reflexivity.
  Qed.
  Next Obligation.
    destruct (normlast_top_block _ _) as (?&?) eqn:Hdl.
    eapply normlast_node_props in Hdl as (_&Lasts&_).
    do 2 esplit; eauto.
    unfold lasts_of_decls, remove_lasts. rewrite map_filter_nil; auto.
    simpl_Forall. auto.
  Qed.
  Next Obligation.
    pose proof (n_nodup n) as (Hnd1&_).
    destruct (normlast_top_block _ _) as (?&?) eqn:Hdl.
    eapply normlast_node_props in Hdl as (_&_&Hnd2&_).
    unfold remove_lasts. rewrite map_map. auto.
  Qed.
  Next Obligation.
    pose proof (n_good n) as (Hgood1&_&Hatom).
    destruct (normlast_top_block _ _) as (?&?) eqn:Hdl.
    eapply normlast_node_props in Hdl as (_&_&_&Hgood2).
    repeat split; auto.
    - rewrite Forall_app in *. destruct_conjs.
      unfold remove_lasts. split; simpl_Forall; now apply AtomOrGensym_add.
  Qed.
  Next Obligation.
    destruct (normlast_top_block _ _) as (?&?) eqn:Hdl.
    eapply normlast_node_props in Hdl as (Hsyn&_&_&_).
    auto.
  Qed.

  Global Program Instance normlast_node_transform_unit: TransformUnit (@node unnested norm1_prefs) node :=
    { transform_unit := normlast_node }.

  Global Program Instance normlast_global_without_units : TransformProgramWithoutUnits (@global unnested norm1_prefs) (@global normlast last_prefs) :=
    { transform_program_without_units := fun g => Global g.(types) g.(externs) [] }.

  Definition normlast_global : @global unnested norm1_prefs -> @global normlast last_prefs :=
    transform_units.

  (** *** Equality of interfaces *)

  Lemma normlast_global_iface_eq : forall G,
      global_iface_eq G (normlast_global G).
  Proof.
    repeat split; auto.
    intros f. unfold find_node.
    destruct (find_unit f G) as [(?&?)|] eqn:Hfind; simpl.
    - setoid_rewrite find_unit_transform_units_forward; eauto.
      simpl. repeat constructor.
      simpl. unfold remove_lasts. erewrite map_map. apply map_ext. intros; destruct_conjs; auto.
    - destruct (find_unit f (normlast_global G)) as [(?&?)|] eqn:Hfind'; simpl; try constructor.
      eapply find_unit_transform_units_backward in Hfind' as (?&?&?&?); congruence.
  Qed.

  (** *** Typeof *)

  Section init_typeof.
    Variable sub : Env.t ident.

    Lemma init_exp_typeof : forall e,
        typeof (init_exp sub e) = typeof e.
    Proof.
      induction e using exp_ind2; destruct_conjs; simpl; auto.
      cases; auto.
    Qed.

    Corollary init_exp_typesof : forall es,
        typesof (map (init_exp sub) es) = typesof es.
    Proof.
      unfold typesof. intros.
      rewrite ? flat_map_concat_map, map_map. f_equal.
      apply map_ext; eauto using init_exp_typeof.
    Qed.
  End init_typeof.

  Section rename_typeof.
    Variable sub : Env.t ident.

    Lemma rename_exp_typeof : forall e,
        typeof (rename_exp sub e) = typeof e.
    Proof.
      induction e using exp_ind2; destruct_conjs; simpl; auto.
    Qed.

    Corollary rename_exp_typesof : forall es,
        typesof (map (rename_exp sub) es) = typesof es.
    Proof.
      unfold typesof. intros.
      rewrite ? flat_map_concat_map, map_map. f_equal.
      apply map_ext; eauto using rename_exp_typeof.
    Qed.
  End rename_typeof.

  (** ** Preservation of normal_args *)

  Global Hint Constructors normal_args_blk : lsyn.

  Section normal_args.
    Context {PSyn : list decl -> block -> Prop} {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Lemma init_exp_noops sub : forall e ck,
        noops_exp ck e ->
        noops_exp ck (init_exp sub e).
    Proof.
      induction e using exp_ind2; intros * No; destruct ck; simpl in *; auto.
      - (* last *)
        take False and inv it.
      - (* when *)
        destruct es as [|? [|]]; try take False and inv it.
        simpl. simpl_Forall. auto.
      - (* merge *)
        take False and inv it.
    Qed.

    Lemma init_block_normal_args sub : forall blk,
        normal_args_blk G blk ->
        normal_args_blk G (init_block sub blk).
    Proof.
      induction blk using block_ind2; intros * N; inv N; simpl; eauto with lsyn.
      - (* equation *)
        constructor. take (normal_args_eq _ _) and inv it; simpl;
          econstructor; eauto using init_exp_normalized_cexp.
        simpl_Forall; eauto using init_exp_noops.
      - (* last *)
        cases; repeat constructor.
      - (* reset *)
        cases; auto with lsyn. simpl_Forall.
        repeat constructor; auto.
    Qed.

    Lemma init_top_block_normal_args : forall outs blk outs' blk' st st',
        normal_args_blk G blk ->
        init_top_block outs blk st = (outs', blk', st') ->
        normal_args_blk G blk'.
    Proof.
      intros * N NL. unfold init_top_block in *.
      cases; repeat inv_bind; auto.
      inv N. econstructor. simpl_Forall; eauto using init_block_normal_args.
    Qed.

    Lemma rename_exp_noops sub : forall e ck,
        noops_exp ck e ->
        noops_exp ck (rename_exp sub e).
    Proof.
      induction e using exp_ind2; intros * No; destruct ck; simpl in *; auto.
      - (* when *)
        destruct es as [|? [|]]; try take False and inv it.
        simpl. simpl_Forall. auto.
      - (* merge *)
        take False and inv it.
    Qed.

    Lemma rename_block_normal_args sub : forall blk,
        normal_args_blk G blk ->
        Forall (normal_args_blk G) (rename_block sub blk).
    Proof.
      induction blk using block_ind2; intros * N; inv N; simpl; eauto with lsyn.
      - (* equation *)
        take (normal_args_eq _ _) and inv it; simpl.
        5:take (normalized_cexp _) and inversion it; subst; try take (normalized_lexp _) and inversion it; subst.
        all:try take (normalized_lexp _) and eapply rename_exp_normalized_lexp with (sub:=sub) in it.
        all:try take (normalized_cexp _) and eapply rename_exp_normalized_cexp with (sub:=sub) in it.
        all:repeat (constructor; eauto).
        all:cases; destruct_conjs; repeat constructor.
        + econstructor; eauto. simpl_Forall; eauto using rename_exp_noops.
        + revert lann0. clear H0.
          induction xs; intros; simpl; cases; constructor; auto.
          destruct (hd_ann _). repeat constructor.
      - (* reset *)
        cases; auto with lsyn. simpl_Forall.
        repeat constructor; auto. eapply Forall_forall in H; eauto.
    Qed.

    Lemma output_top_block_normal_args : forall outs blk blk' st st',
        normal_args_blk G blk ->
        output_top_block outs blk st = (blk', st') ->
        normal_args_blk G blk'.
    Proof.
      intros * N NL. unfold output_top_block in *.
      cases; repeat inv_bind; auto.
      inv N. econstructor.
      apply Forall_flat_map. simpl_Forall.
      eapply rename_block_normal_args, Forall_forall in H1; eauto.
    Qed.

    Lemma unnest_block_normal_args sub : forall blk,
        normal_args_blk G blk ->
        normal_args_blk G (unnest_block sub blk).
    Proof.
      induction blk using block_ind2; intros * N; inv N; simpl; eauto with lsyn.
      - (* equation *)
        cases. inv H0; simpl; repeat (constructor; eauto using rename_exp_normalized_cexp).
        econstructor; eauto.
        simpl_Forall; eauto using rename_exp_noops.
      - (* reset *)
        cases; auto with lsyn. simpl_Forall.
        repeat constructor; auto.
    Qed.

    Lemma unnest_top_block_normal_args : forall blk blk' st st',
        normal_args_blk G blk ->
        unnest_top_block blk st = (blk', st') ->
        normal_args_blk G blk'.
    Proof.
      intros * N NL. unfold unnest_top_block in *.
      cases; repeat inv_bind; auto.
      inv N. econstructor.
      apply Forall_app; split; simpl_Forall; eauto using unnest_block_normal_args.
      repeat constructor.
    Qed.

  End normal_args.

  Lemma normlast_node_normal_args G1 G2 : forall n,
      global_iface_eq G1 G2 ->
      normal_args_node G1 n ->
      normal_args_node G2 (normlast_node n).
  Proof.
    intros * Incl N. unfold normal_args_node in *. simpl.
    destruct (normlast_top_block _ _ _) eqn:NL.
    unfold normlast_top_block in *. repeat inv_bind.
    eapply unnest_top_block_normal_args; eauto.
    eapply output_top_block_normal_args; eauto.
    eapply init_top_block_normal_args; eauto.
    eapply iface_eq_normal_args_blk; eauto.
  Qed.

  Lemma normlast_global_normal_args : forall G,
      normal_args G ->
      normal_args (normlast_global G).
  Proof.
    intros []. induction nodes0; inversion 1; subst; constructor; eauto.
    - eapply normlast_node_normal_args; eauto.
      apply normlast_global_iface_eq.
    - eapply IHnodes0; eauto.
  Qed.

End NORMLAST.

Module NormLastFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       <: NORMLAST Ids Op OpAux Cks Senv Syn.
  Include NORMLAST Ids Op OpAux Cks Senv Syn.
End NormLastFun.
