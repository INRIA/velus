Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Velus.Common.
Require Import Velus.Operators.
Open Scope positive.

Require Import Velus.RMemory.
Require Import Velus.NLustre.
Require Import Velus.Obc.
Require Import Velus.NLustreToObc.Translation.
Require Import Velus.Obc.FuseIfte.

Require Import Velus.NLustre.Typing.

(** ** Well-typing preservation *)

Module Type TYPING
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import DF    : NLUSTRE Ids Op OpAux)
       (Import Obc   : OBC Ids Op OpAux)
       (Import Mem   : MEMORIES Ids Op DF.Syn)

       (Import Trans : TRANSLATION Ids Op OpAux DF.Syn Obc.Syn Mem)

       (Import Fus   : FUSEIFTE Ids Op OpAux DF.Syn Obc.Syn Obc.Sem Obc.Equ).


  (** Preservation of well-typing. *)

  (** For the ifte fusion optimization *)

  Lemma zip_wt:
    forall p insts mems vars s1 s2,
      wt_stmt p insts mems vars s1 ->
      wt_stmt p insts mems vars s2 ->
      wt_stmt p insts mems vars (zip s1 s2).
  Proof.
    induction s1, s2; simpl;
      try match goal with |- context [if ?e1 ==b ?e2 then _ else _] =>
            destruct (equiv_decb e1 e2) end;
      auto with obctyping;
      inversion_clear 1;
      try inversion_clear 2;
      auto with obctyping.
    inversion_clear 1.
    auto with obctyping.
  Qed.

  Lemma fuse_wt:
    forall p insts mems vars s,
      wt_stmt p insts mems vars s ->
      wt_stmt p insts mems vars (fuse s).
  Proof.
    intros ** WTs.
    destruct s; auto; simpl; inv WTs.
    match goal with H1:wt_stmt _ _ _ _ s1, H2:wt_stmt _ _ _ _ s2 |- _ =>
                    revert s2 s1 H1 H2 end.
    induction s2; simpl; auto using zip_wt.
    intros s2 WTs1 WTcomp.
    inv WTcomp.
    apply IHs2_2; auto.
    apply zip_wt; auto.
  Qed.

  Section Expressions.

    (* DF variables and their types: n_in ++ n_out ++ n_vars *)
    Variable nvars  : list (ident * type).

    (* Obc memories: c_mems (=n_vars and is_fby) *)
    Variable mems   : list (ident * type).

    (* Obc variables: m_in (=n_in) ++ m_out (=n_out)
                        ++ m_vars (=n_vars and not is_fby) *)
    Variable vars   : list (ident * type).

    (* Set from mems *)
    Variable memset : PS.t.

    Hypothesis nvars_to_mems:
      forall x ty,
        In (x, ty) nvars ->
        PS.In x memset ->
        In (x, ty) mems.

    Hypothesis nvars_to_vars:
      forall x ty,
        In (x, ty) nvars ->
        ~PS.In x memset ->
        In (x, ty) vars.

    Hint Resolve nvars_to_mems nvars_to_vars : transty.

    Ltac FromMemset :=
      match goal with
      | |- context [ PS.mem ?i memset ] =>
        destruct (PS.mem i memset) eqn:Hpsm;
        match goal with
        | H:PS.mem _ _ = true  |- _ => rewrite PS.mem_spec in H
        | H:PS.mem _ _ = false |- _ => rewrite mem_spec_false in H
        | _ => idtac
        end
      end.

    Lemma typeof_translate_lexp:
      forall e,
        Obc.Syn.typeof (translate_lexp memset e) = DF.Syn.typeof e.
    Proof.
      induction e; auto.
      simpl; now FromMemset.
    Qed.

    Lemma translate_lexp_wt:
      forall e,
        wt_lexp nvars e ->
        wt_exp mems vars (translate_lexp memset e).
    Proof.
      induction e; simpl; intro WTle; inv WTle; auto with obctyping.
      - FromMemset; eauto with obctyping.
      - constructor; auto. now rewrite typeof_translate_lexp.
      - constructor; auto. now rewrite 2 typeof_translate_lexp.
    Qed.

    Hint Resolve translate_lexp_wt : transty.

    Lemma translate_cexp_wt:
      forall p insts x e,
        wt_cexp nvars e ->
        In (x, typeofc e) vars ->
        wt_stmt p insts mems vars (translate_cexp memset x e).
    Proof.
      induction e; simpl; intros WTe Hv; inv WTe.
      - match goal with H:typeofc e1 = typeofc e2 |- _ => rewrite <-H in * end.
        FromMemset; eauto 6 with obctyping.
      - assert (Hv' := Hv).
        match goal with H:typeofc e1 = typeofc e2 |- _ => rewrite H in Hv' end.
        constructor; eauto with transty obctyping.
        now rewrite typeof_translate_lexp.
      - constructor; eauto with transty obctyping.
        now rewrite typeof_translate_lexp.
    Qed.

    Hint Resolve translate_cexp_wt : transty.

    Lemma Control_wt:
      forall p insts ck s,
        wt_clock nvars ck ->
        wt_stmt p insts mems vars s ->
        wt_stmt p insts mems vars (Control memset ck s).
    Proof.
      induction ck; intros s WTc WTs; inv WTc; auto.
      destruct b; simpl; FromMemset; eauto with obctyping.
    Qed.

    Hint Resolve Control_wt : transty.

  End Expressions.

  Definition wt_eqs_vars insts mems vars memset eqs :=
    Forall
      (fun eq=> match eq with
             | EqDef x ck e => In (x, typeofc e) vars
             | EqApp xs ck f es =>
                 match xs with
                 | [] => True
                 | x :: _ => In (x, f) insts
                 end
               /\ Forall (fun x => ~PS.In x memset) xs
             | EqFby x ck c0 e => In (x, type_const c0) mems
             end)
      eqs.

  Lemma wt_step_translate_eqns:
    forall g n insts mems vars memset,
      wt_node g n ->
      wt_eqs_vars insts mems vars memset n.(n_eqs) ->
      (forall x ty, In (x, ty) (n.(n_in) ++ n.(n_vars) ++ n.(n_out)) ->
                    PS.In x memset -> In (x, ty) mems) ->
      (forall x ty, In (x, ty) (n.(n_in) ++ n.(n_vars) ++ n.(n_out)) ->
                    ~PS.In x memset -> In (x, ty) vars) ->
      wt_stmt (translate g) insts mems vars
              (translate_eqns memset n.(n_eqs)).
  Proof.
    intros ** WTn Heqs Hmems Hvars.
    unfold translate_eqns.
    match goal with |- wt_stmt ?p ?i ?m ?v (fold_left ?f ?eqs Skip) =>
                    cut (forall s, wt_stmt p i m v s -> wt_stmt p i m v (fold_left f eqs s));
                      auto with obctyping
    end.
    unfold wt_node in WTn.
    induction n.(n_eqs) as [|eq eqs]; auto.
    apply Forall_cons2 in WTn.
    destruct WTn as [WTeq WTeqs].
    apply Forall_cons2 in Heqs.
    destruct Heqs as (Heq & Heqs).
    specialize (IHeqs WTeqs Heqs).
    intros s WTs.
    simpl. apply IHeqs; auto; clear IHeqs.
    constructor; auto.
    inv WTeq; simpl;
      apply Control_wt with (nvars:=n.(n_in) ++ n.(n_vars) ++ n.(n_out));
      auto.
    - eapply translate_cexp_wt; eauto.
    - destruct Heq as (Heq1 & Heq2).

      assert (Forall2 (fun y xt => In (y, snd xt) vars) xs (n_out n0)).
      {
        assert (length xs = length (n_out n0))
          by (eapply Forall2_length; eauto).

        apply Forall2_forall2; split; auto;
          intros def_x [def_y def_yty] dn x [y yty] Hlen Hxn Hytn.

        assert (In x xs)
          by (rewrite <-Hxn; apply nth_In; auto).

        assert (~ PS.In x memset)
          by (eapply In_Forall in Heq2; eauto).

        assert (In (x, snd (y, yty)) (n_in n ++ n_vars n ++ n_out n)).
        {
          match goal with
          | H: Forall2 _ xs (n_out n0) |- _ =>
            apply Forall2_forall2 in H as [_ Hin_vars]
          end.
          eapply Hin_vars; eauto.
        }

        apply Hvars; auto.
      }

      match goal with H:find_node _ _ = Some _ |- _ =>
                      apply find_node_translate in H;
                        destruct H as (cls & prog' & Hfind & Hcls) end.
      match goal with H:cls=translate_node ?n |- _ =>
                      destruct (exists_step_method n) as (stepm & Hstep) end.
      eapply wt_Call; subst cls; eauto.
      + assert (Hlen: (0 < length xs)%nat).
        {
          assert (length xs = length (n_out n0)) as ->
            by now eapply Forall2_length; eauto.

          now destruct n0.
        }
        destruct xs; try now inv Hlen.
      + erewrite find_method_stepm_out; eauto.
      + rewrite (find_method_stepm_in _ _ Hstep).
        apply Forall2_map_1.
        match goal with H:Forall2 _ _ _ |- _ =>
                        apply Forall2_impl_In with (2:=H) end.
        intros; now rewrite typeof_translate_lexp.
      + apply Forall_map.
        match goal with H:Forall _ _ |- _ =>
                        apply Forall_impl with (2:=H) end.
        intros; eauto using translate_lexp_wt.
    - constructor; eauto using translate_lexp_wt.
      match goal with H:DF.Syn.typeof e = _ |- _ =>
                      rewrite typeof_translate_lexp, H; auto end.
  Qed.

  Lemma wt_reset_method_translate:
    forall g n insts mems,
      wt_node g n ->
      Forall (fun eq=> match eq with
                       | EqDef x ck e => True
                       | EqApp xs ck f es =>
                         match xs with
                         | [] => True
                         | x :: _ => In (x, f) insts
                         end
                       | EqFby x ck c0 e => In (x, type_const c0) mems
                       end) n.(n_eqs) ->
      wt_method (translate g) insts mems (reset_method n.(n_eqs)).
  Proof.
    intros ** WTn Heqs.
    unfold wt_method; simpl.
    unfold translate_reset_eqns.
    match goal with |- wt_stmt ?p ?i ?m ?v (fold_left ?f ?eqs Skip) =>
                    cut (forall s, wt_stmt p i m v s -> wt_stmt p i m v (fold_left f eqs s));
                      auto with obctyping
    end.
    unfold wt_node in WTn.
    induction n.(n_eqs) as [|eq eqs]; auto.
    apply Forall_cons2 in WTn as [WTeq WTeqs].
    specialize (IHeqs WTeqs).
    apply Forall_cons2 in Heqs as [Heq Heqs].
    intros s WTs.
    simpl. apply IHeqs; auto.
    destruct eq; simpl; auto; constructor; inv WTeq; auto with obctyping.
    match goal with H:find_node _ _ = Some _ |- _ =>
                    apply find_node_translate in H;
                      destruct H as (cls & prog' & Hfind & Hcls) end.

    assert (In (hd Ids.default i, i0) insts).
    {
      assert (Hlen: (0 < length i)%nat).
      {
        assert (length i = length (n_out n0)) as ->
            by now eapply Forall2_length; eauto.

        now destruct n0.
      }

      destruct i; try now inv Hlen.
    }

    eapply wt_Call with (fm:=reset_method _); simpl;
      eauto using NoDup; subst cls.
    apply exists_reset_method.
  Qed.


  Lemma translate_wt_vals_ins:
    forall node stepm ins,
      find_method step (translate_node node).(c_methods) = Some stepm ->
      wt_vals ins node.(n_in) ->
      wt_vals ins stepm.(m_in).
  Proof. intros; erewrite find_method_stepm_in; eauto. Qed.

  Lemma translate_wt_vals_outs:
    forall node stepm outs,
      find_method step (translate_node node).(c_methods) = Some stepm ->
      wt_vals outs node.(n_out) ->
      wt_vals outs stepm.(m_out).
  Proof. intros; erewrite find_method_stepm_out; eauto. Qed.


  Lemma EqFby_type_in_node:
    forall g n x ck c0 e,
      wt_node g n ->
      In (EqFby x ck c0 e) n.(n_eqs) ->
      In (x, type_const c0) n.(n_vars).
  Proof.
    intros ** WTn Hin.
    apply In_Forall with (2:=Hin) in WTn.
    inversion_clear WTn as [| |? ? ? ? Hvars Htye WTc WTl].
    repeat (apply in_app in Hvars; destruct Hvars as [Hv|Hvars]); auto.
    -  (* Case: In (x, type_const c0) (n_in n) *)
      apply In_EqFby_Is_defined_in_eqs in Hin.
      apply Is_defined_in_var_defined in Hin.
      rewrite n.(n_defd) in Hin.
      apply fst_InMembers in Hin.
      apply In_InMembers in Hv.
      apply (NoDupMembers_app_InMembers _ _ _ n.(n_nodup)) in Hv.
      contradiction.
    - (* Case: In (x, type_const c0) (n_out n) *)
      pose proof (n.(n_vout)) as Hnin.

      assert (In x (vars_defined (filter is_fby (n_eqs n)))).
      {
        assert (In (EqFby x ck c0 e) (filter is_fby n.(n_eqs))) as Heqs'
            by (apply filter_In; auto).

        assert (In x (var_defined (EqFby x ck c0 e)))
          by (simpl; auto).

        assert (In (var_defined (EqFby x ck c0 e))
                   (map var_defined (filter is_fby (n_eqs n))))
          by (eapply in_map in Heqs'; eauto).

        eapply in_concat; eauto.
      }

      assert (In x (map fst (n_out n))).
      {
        apply in_map_iff. eexists; esplit; eauto.
        simpl; auto.
      }

      edestruct Hnin; eauto.
  Qed.

  Lemma EqApp_type_in_node:
    forall g n xs ck f les,
      wt_node g n ->
      In (EqApp xs ck f les) (n_eqs n) ->
      NoDup xs.
  Proof.
  intros ** WTn Hin.
  eapply In_Forall in WTn; eauto.
  now inversion_clear WTn.
  Qed.

  Lemma EqDef_type_in_node:
    forall g n x ck e,
      wt_node g n ->
      In (EqDef x ck e) (n_eqs n) ->
      In (x, typeofc e)
         (n.(n_in)
              ++ filter (fun x=> negb (PS.mem (fst x) (memories n.(n_eqs))))
              n.(n_vars)
                  ++ n.(n_out)).
  Proof.
    intros ** WTn Hin.
    apply In_Forall with (2:=Hin) in WTn.
    inversion_clear WTn as [? ? ? Hv WTc WTe| |].
    apply In_EqDef_Is_variable_in_eqs in Hin.
    pose proof (Is_variable_in_eqs_Is_defined_in_eqs _ _ Hin) as Hdin.
    apply Is_defined_in_var_defined in Hdin.
    rewrite n.(n_defd) in Hdin.
    apply fst_InMembers in Hdin.
    repeat (apply in_app in Hv; destruct Hv as [Hin'|Hv]); intuition.
    apply in_app; right; apply in_app; left.
    apply Is_variable_in_var_defined in Hin.
    apply not_in_memories_filter_notb_is_fby in Hin.
    2:now apply NoDup_var_defined_n_eqs.
    apply filter_In; split; auto.
    now apply Bool.negb_true_iff, mem_spec_false.
  Qed.

  Lemma translate_node_wt:
    forall g n,
      wt_program (translate g) ->
      wt_node g n ->
      wt_class (translate g) (translate_node n).
  Proof.
    intros g n WTp WTn.
    constructor; simpl; [|repeat constructor].
    - (* find_class for all applications *)
      unfold wt_node in WTn.
      rewrite gather_eqs_snd_spec.
      induction n.(n_eqs) as [|eq eqs]; simpl.
      + unfold gather_insts; rewrite concatMap_nil; constructor.
      + inversion_clear WTn as [|? ? WTeq WTeqs].
        destruct eq; simpl; auto.
        destruct i; simpl; try now apply IHeqs.
        constructor; auto.
        inv WTeq. simpl.
        match goal with H:find_node _ _ = Some _ |- _ =>
                        apply find_node_translate in H;
                          destruct H as (cls & prog' & Hfind & Hcls) end.
        intro HH; rewrite HH in Hfind; discriminate.
    - (* wt_method step *)
      unfold wt_method, meth_vars; simpl.
      rewrite fst_partition_filter, snd_partition_filter.
      setoid_rewrite ps_from_list_gather_eqs_memories at 1.
      setoid_rewrite ps_from_list_gather_eqs_memories at 2.
      Typeclasses eauto := 4. (* Why is this necessary? *)
      setoid_rewrite ps_from_list_gather_eqs_memories.
      Typeclasses eauto := 100.

      set (insts := snd (gather_eqs (n_eqs n))).
      set (mems := filter (fun x => PS.mem (fst x) (memories (n_eqs n))) (n_vars n)).
      set (vars := (n_in n ++
                    filter (fun x => negb (PS.mem (fst x) (memories (n_eqs n)))) (n_vars n) ++
                    n_out n)).
      set (memset := (memories (n_eqs n))).

      assert (wt_eqs_vars insts mems vars memset n.(n_eqs)).
      {
        apply all_In_Forall. intros eq' Hin.
        destruct eq'; auto.
        - (* Case: EqDef *)
          apply EqDef_type_in_node with (1:=WTn) (2:=Hin).
        - (* Case: EqApp *)
          repeat split.
(*
          + (* Prove: NoDup i *)
            now eapply EqApp_type_in_node; eauto.
*)
          + (* Prove: In (hd Ids.default i, i0) insts *)
            destruct i; auto.
            unfold insts.
            rewrite gather_eqs_snd_spec.
            unfold gather_insts.
            apply in_concat' with (l0 := [(i, i0)]); try now constructor.
            eapply in_map_iff.
            exists (EqApp (i :: i1) c i0 l). eauto.
          + (* Prove: Forall (fun x : positive => ~ PS.In x memset) i *)
            unfold memset.
            apply Forall_forall; intros x Hx.
            eapply In_EqApp_Is_variable_in_eqs in Hin; eauto.
            apply Is_variable_in_var_defined in Hin.
            apply not_in_memories_filter_notb_is_fby in Hin; eauto.
            apply NoDup_var_defined_n_eqs.
        - apply fby_In_filter_memories with (1:=Hin).
          eapply EqFby_type_in_node with (1:=WTn) (2:=Hin).
      }

      assert (forall x ty, In (x, ty) (n.(n_in) ++ n.(n_vars) ++ n.(n_out)) ->
                    PS.In x memset -> In (x, ty) mems).
      {
        intros x ty Hin Hmem.
        pose proof (in_memories_var_defined _ _ Hmem) as Hdef.
        rewrite n.(n_defd) in Hdef.
        apply fst_InMembers in Hdef.
        apply NoDupMembers_app_InMembers with (ws:=n.(n_in)) in Hdef.
        2:now rewrite Permutation.Permutation_app_comm; apply n.(n_nodup).
        unfold mems.
        repeat (apply in_app in Hin; destruct Hin as [Hin|Hin]); intuition.
        - (* Case: In x (n_in n) *)
          contradiction Hdef. apply In_InMembers with (1:=Hin).
        - (* Case: In x (n_vars n) *)
          apply filter_In; split; auto.
        - (* Case: In x (n_out n) *)
          apply in_memories_filter_is_fby in Hmem.
          edestruct n_vout; eauto.
          replace x with (fst (x, ty)); auto.
          eapply in_map; auto.
      }

      assert (forall x ty, In (x, ty) (n.(n_in) ++ n.(n_vars) ++ n.(n_out)) ->
                    ~PS.In x memset -> In (x, ty) vars). {
        intros x ty Hin Hnmem.  unfold vars.
        repeat (apply in_app in Hin; destruct Hin as [Hin|Hin]); intuition.
        apply in_app; right; apply in_app; left.
        apply filter_In; split; auto.
        now apply Bool.negb_true_iff, mem_spec_false.
      }

      apply wt_step_translate_eqns; auto.
    - (* wt_method reset *)
      unfold wt_method; simpl.
      rewrite fst_partition_filter.
      setoid_rewrite ps_from_list_gather_eqs_memories.
      apply wt_reset_method_translate; auto.
      apply all_In_Forall.
      intros eq Hin.
      destruct eq; auto.
      + (* Case: EqApp *)
        simpl.
        destruct i; auto.
        rewrite gather_eqs_snd_spec.
        apply in_concat' with (l0 := [(i, i0)]); try now constructor.
        eapply in_map_iff.
        exists (EqApp (i :: i1) c i0 l).
        eauto.
      + (* Case: EqFby *)
        apply fby_In_filter_memories with (1:=Hin).
        eapply EqFby_type_in_node with (1:=WTn) (2:=Hin).
  Qed.

  Hint Resolve translate_node_wt : transty.

  Lemma translate_wt:
    forall g,
      wt_global g ->
      wt_program (translate g).
  Proof.
    intros g WTg.
    pose proof (wt_global_NoDup _ WTg) as Hnodup.
    induction g as [|n g]; auto with obctyping.
    inversion_clear WTg as [|? ? WTg' WTn Hnr]; rename WTg' into WTg.
    inv Hnodup.
    simpl; constructor; eauto with transty.
    simpl; rewrite map_c_name_translate.
    auto using NoDup_cons.
  Qed.


End TYPING.

Module TypingFun
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import DF    : NLUSTRE Ids Op OpAux)
       (Import Obc   : OBC Ids Op OpAux)
       (Import Mem   : MEMORIES Ids Op DF.Syn)

       (Import Trans : TRANSLATION Ids Op OpAux DF.Syn Obc.Syn Mem)

       (Import Fus   : FUSEIFTE Ids Op OpAux DF.Syn Obc.Syn Obc.Sem Obc.Equ)
       <: TYPING Ids Op OpAux DF Obc Mem Trans Fus.

       Include TYPING Ids Op OpAux DF Obc Mem Trans Fus.
End TypingFun.    
