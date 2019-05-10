From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Environment.

From Coq Require Import Arith.Arith.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Setoid.
From Coq Require Import Omega.

Section Dfs.

  Variable graph : Env.t (list ident).

  Record dfs_state : Type :=
    mk_dfs_state {
        in_progress : PS.t;
        progress_in_graph : forall x, PS.In x in_progress -> Env.In x graph
      }.

  Extraction Inline in_progress.

  Definition empty_dfs_state :=
    {| in_progress := PS.empty;
       progress_in_graph := fun x Hin =>
                              False_ind (Env.In x graph) (not_In_empty x Hin) |}.
  Extraction Inline empty_dfs_state.

  Lemma cardinals_in_progress_le_graph:
    forall a,
      PS.cardinal a.(in_progress) <= Env.cardinal graph.
  Proof.
    intro a.
    rewrite Env.cardinal_1, PS.cardinal_spec.
    rewrite <-(map_length fst).
    pose proof a.(progress_in_graph) as Hag.
    assert (NoDup (PS.elements (in_progress a))) as Hnds
        by (rewrite NoDup_NoDupA; apply PS.elements_spec2w).
    assert (NoDupMembers (Env.elements graph)) as Hndg
        by (apply Env.NoDupMembers_elements).
    apply fst_NoDupMembers in Hndg.
    setoid_rewrite PSF.elements_iff in Hag.
    setoid_rewrite Env.In_Members in Hag.
    setoid_rewrite fst_InMembers in Hag.
    revert Hag Hnds Hndg.
    generalize (map fst (Env.elements graph)) as g.
    generalize (PS.elements a.(in_progress)) as n.
    induction n as [|x n IH]; auto using le_0_n.
    intros g Hin NDn NDg. simpl.
    inversion_clear NDn as [|?? Hnx NDn'].
    assert (In x g) as Hxg by auto.
    apply in_split in Hxg as (g1 & g2 & Hg); subst.
    rewrite <-Permutation.Permutation_middle.
    simpl; apply le_n_S.
    rewrite <-Permutation.Permutation_middle in NDg; inv NDg.
    apply IH; auto.
    intros y Hyi.
    apply (In_weaken_cons x).
    now rewrite Permutation.Permutation_middle; auto.
    intro; subst. apply Hnx.
    apply SetoidList.InA_alt in Hyi as (y & Heq & Hyin).
    subst; auto.
  Qed.

  Definition max_depth_remaining (s : dfs_state) : nat :=
    Env.cardinal graph - PS.cardinal s.(in_progress).

  Definition deeper : dfs_state -> dfs_state -> Prop :=
    ltof _ max_depth_remaining.

  Lemma wf_deeper: well_founded deeper.
  Proof.
    apply well_founded_ltof.
  Defined.
    
  Lemma add_deeper:
    forall x s P,
      ~ PS.In x (in_progress s) ->
      deeper {| in_progress := PS.add x (in_progress s);
                progress_in_graph := P |} s.
  Proof.
    unfold deeper, ltof, max_depth_remaining.
    intros x s Hprog Hnin.
    pose proof (cardinals_in_progress_le_graph s) as Hag.
    pose proof (cardinals_in_progress_le_graph
                  {| in_progress := PS.add x (in_progress s);
                     progress_in_graph := Hprog |}) as Hbg.
    simpl in *.
    rewrite PSP.add_cardinal_2 with (1:=Hnin) in *.
    omega.
  Qed.

  Inductive WellOrdered : list positive -> Prop :=
  | well_ordered_empty: WellOrdered []
  | well_ordered_cons: forall x xs ys,
      Env.find x graph = Some ys ->
      incl ys xs ->
      WellOrdered xs ->
      WellOrdered (x::xs).

  Definition visited (p : PS.t) (v : PS.t) : Prop :=
    (forall x, PS.In x p -> ~PS.In x v)
    /\ (forall y, PS.In y v ->
                  exists zs, Env.find y graph = Some zs
                             /\ (forall z, In z zs -> PS.In z v))
    /\ (exists xs, Permutation (PS.elements v) xs /\ WellOrdered xs).

  Definition none_visited : { v | visited PS.empty v }.
  Proof.
    exists PS.empty.
    repeat split; auto using not_In_empty.
    - intros * Hin. now apply not_In_empty in Hin.
    - exists nil. split; eauto using WellOrdered.
  Defined.
  Extraction Inline none_visited.

  Lemma sig2_of_sig:
    forall {A : Type} {P Q : A -> Prop} (s : { s : A | P s }),
      Q (proj1_sig s) ->
      { s | P s & Q s }.
  Proof.
    intros ? ? ? (s, Ps) Qs.
    exact (exist2 _ _ s Ps Qs).
  Defined.
  Extraction Inline sig2_of_sig.

  Lemma sig2_weaken2:
    forall {A : Type} {P Q Q' : A -> Prop},
      (forall s, Q s -> Q' s) ->
      { s : A | P s & Q s } ->
      { s | P s & Q' s }.
  Proof.
    intros * HQQ s.
    destruct s as (s, Ps, Qs).
    apply HQQ in Qs.
    exact (exist2 _ _ s Ps Qs).
  Defined.
  Extraction Inline sig2_weaken2.
  
  Definition In_ps (xs : list positive) (v : PS.t) :=
    Forall (fun x => PS.In x v) xs.

  Lemma In_ps_nil:
    forall v, In_ps [] v.
  Proof.
    intro v. apply Forall_nil.
  Qed.

  Lemma In_ps_singleton:
    forall x v,
      PS.In x v <-> In_ps [x] v.
  Proof.
    split; intro HH; [|now inv HH].
    now apply Forall_cons; auto.
  Qed.

  Definition dfs'_loop
             (inp : PS.t)
             (dfs' : forall x (v : { v | visited inp v }),
                 option { v' | visited inp v' & (In_ps [x] v'
                                                 /\ PS.Subset (proj1_sig v) v') })
             (zs : list positive)
             (v : {v | visited inp v })
    : option { v' | visited inp v' & (In_ps zs v' /\ PS.Subset (proj1_sig v) v') }.
  Proof.
    revert zs v.
    fix dfs'_loop 1.
    intros zs v.
    destruct zs as [|w ws].
    - refine (Some (sig2_of_sig v _)).
      split. now apply In_ps_nil. reflexivity.
    - destruct (dfs' w v) as [(v', Pv', (Hinv', Hsubv'))|]; [|exact None].
      destruct (dfs'_loop ws (exist _ v' Pv')) as [v''|]; [|exact None].
      refine (Some (sig2_weaken2 _ v'')).
      intros S (Hin, Hsub). split.
      + apply Forall_cons; auto.
        rewrite <-Hsub. now inv Hinv'.
      + rewrite <-Hsub. simpl. rewrite <-Hsubv'. reflexivity.
  Defined.
  Extraction Inline dfs'_loop.

  Definition pre_visited_add:
    forall {inp} x
      (v : { v | visited inp v }),
      ~PS.In x (proj1_sig v) ->
      { v' | visited (PS.add x inp) v' & v' = (proj1_sig v) }.
  Proof.
    intros inp x (v, (Pv1 & Pv2 & Pv3)) Hnxp.
    simpl in *. exists v; split; auto.
    intros y Hyp. apply PS.add_spec in Hyp as [HH|HH]; subst; auto.
  Defined.
  Extraction Inline pre_visited_add.
  
  Definition dfs'
     (s : dfs_state)
     (dfs'' : forall s', deeper s' s ->
                forall x (v : { v | visited s'.(in_progress) v }),
                  option { v' | visited s'.(in_progress) v'
                                & In_ps [x] v' /\ PS.Subset (proj1_sig v) v' })
     (x : positive)
     (v : { v | visited s.(in_progress) v })
    : option { v' | visited s.(in_progress) v'
                    & In_ps [x] v' /\ PS.Subset (proj1_sig v) v' }.
  Proof.
    destruct (PS.mem x s.(in_progress)) eqn:Mxs; [exact None|].
    destruct (PS.mem x (proj1_sig v)) eqn:Mxv.
    (* This node has already been visited. Show postcondition. *)
    now refine (Some (sig2_of_sig v _)); split;
      [apply In_ps_singleton; apply (PSF.mem_2 Mxv)|reflexivity].
    (* Not yet visited ... *)
    destruct (Env.find x graph) as [zs|] eqn:Mxg; [|exact None].
    assert (forall z, PS.In z (PS.add x s.(in_progress)) -> Env.In z graph) as Hprog.
    { intros z Hzin.
      apply PS.add_spec in Hzin as [|Hzin]; subst.
      - now apply Env.find_In in Mxg.
      - now apply s.(progress_in_graph). }
    pose (s' := mk_dfs_state (PS.add x s.(in_progress)) Hprog).
    apply PSE.mem_4 in Mxs. apply PSE.mem_4 in Mxv.
    assert (deeper s' s) as Hdeeper by now apply add_deeper.
    pose proof (pre_visited_add x v Mxv) as (v', V', Qv'). subst.
    destruct (dfs'_loop s'.(in_progress) (dfs'' s' Hdeeper) zs (exist _ _ V'))
      as [(v'', (P1 & P2 & P3), (Hzs & Hsub))|]; [|exact None]. simpl in *.
    refine (Some _).
    exists (PS.add x v'').
    (* Show postconditions *)
    - repeat split.
      + intros y Hyin.
        setoid_rewrite PS.add_spec.
        apply not_or'. split; [now intro; subst; auto|].
        apply P1. now apply PSF.add_2.
      + intros y Hyin.
        apply PS.add_spec in Hyin as [HH|HH].
        * subst. exists zs; split; auto.
          intros z HH. apply PSF.add_2.
          now apply Forall_forall with (1:=Hzs) in HH.
        * destruct (P2 _ HH) as (? & ? & ?).
          eauto using PSF.add_2.
      + destruct P3 as (ys & Pys & WOys).
        exists (x::ys). split.
        * apply Permutation_elements_add; auto.
          apply P1. apply PS.add_spec; auto.
        * econstructor; eauto.
          intros z HH.
          rewrite <-Pys, In_PS_elements.
          now apply Forall_forall with (1:=Hzs) in HH.
    - split. now apply In_ps_singleton, PS.add_spec; left.
      rewrite <-Hsub. apply PSP.subset_add_2. reflexivity.
  Defined.

  Definition dfs
    : forall x (v : { v | visited PS.empty v }),
      option { v' | visited PS.empty v' & (In_ps [x] v'
                                           /\ PS.Subset (proj1_sig v) v') }
    := Fix wf_deeper _ dfs' empty_dfs_state.
  
End Dfs.

(* Recursive Extraction dfs. *)

(* With option_map, the extracted program is less pleasing.
   In principle, the correctness proof should follow directly from the
   final type: option (visited PS.empty (fun x -> In x (PM.elements graph))).
   But how to get this past the type checker? *)
Definition check_graph (graph : Env.t (list positive)) : bool :=
  match Env.fold (fun x _ vo =>
                    match vo with
                    | None => None
                    | Some v => match dfs graph x v with
                                | None => None
                                | Some v => Some (sig_of_sig2 v)
                                end
                    end)
                 graph (Some (none_visited graph)) with
  | None => false
  | Some _ => true
  end.

Theorem check_graph_spec:
  forall graph,
    check_graph graph = true ->
    exists xs,
      Permutation (map fst (Env.elements graph)) xs
      /\ WellOrdered graph xs.
Proof.
  unfold check_graph.
  intros graph Hcheck.
  match goal with [ H:context[ match Env.fold ?f ?graph ?acc with _ => _ end] |- _ ]
    => destruct (Env.fold f graph acc) eqn:Hfold; try discriminate end.
  clear Hcheck.
  rename s into v'.
  rewrite Env.fold_1 in Hfold.
  assert (PS.Equal (proj1_sig v')
                   (ps_adds (map fst (Env.elements graph))
                            (proj1_sig (none_visited graph)))) as Hveq;
    [apply PSP.double_inclusion; split|].
  - destruct v' as (v' & Pv'1 & Pv'2 & Pv'3 & Pv'4).
    simpl. intros x Hx.
    apply Pv'2 in Hx as (zs & Hx & Hsuc).
    apply Env.elements_correct in Hx.
    apply ps_adds_spec; left.
    apply in_map_iff. exists (x, zs); auto.
  - revert Hfold.
    change (fun vo (p : Env.key * list positive) =>
              match vo with None => None
              | Some v => match dfs graph (fst p) v with None => None
                          | Some v' => Some (sig_of_sig2 v')
                          end end) with
        (fun vo (p : _ * list positive) =>
           (fun x => match vo with None => None
                     | Some v => match dfs graph x v with None => None
                                 | Some v' => Some (sig_of_sig2 v')
                                 end end) (fst p)).
    rewrite fold_left_map_fst.
    revert v'.
    generalize (none_visited graph) as acc.
    generalize (map fst (Env.elements graph)) as xs.
    induction xs as [|x xs IH]; [inversion 1; reflexivity|].
    simpl. intros acc v' (* Hacc *) Hfold.
    match goal with [ H:context[fold_left ?f xs ?acc = Some v'] |- _ ]
      => assert (forall xs, fold_left f xs None = None)
        as Hnone by (clear; induction xs; simpl; auto) end.
    destruct (dfs graph x acc) as [acc'|] eqn:Hacc';
      [clear Hnone|now rewrite Hnone in Hfold].
    apply IH in Hfold.
    rewrite <-Hfold.
    apply Subset_ps_adds.
    destruct acc' as (acc', Vacc', (H1acc' & H2acc')); simpl in *.
    apply PSP.subset_add_3; auto. now apply In_ps_singleton.
  - clear Hfold. destruct v' as (v & Pv1 & Pv2 & (xs & Pxs & WOxs)).
    simpl in Hveq.
    exists xs. split; auto.
    setoid_rewrite Hveq in Pxs.
    rewrite <-Pxs, ps_adds_of_list, Permutation_PS_elements_of_list; auto.
    apply fst_NoDupMembers, Env.NoDupMembers_elements.
Qed.

(** Simple tests *)

Definition to_graph (nss : list (positive * list positive)) : Env.t (list positive)
  := List.fold_left (fun g ns => Env.add (fst ns) (snd ns) g) nss (Env.empty _).

(*
         1          9
        / \        / \
       2   6      /  11
      / \ / \     |  /
     3   7   8    | /
    / \     /     10
   4   \   /
        \ /
         5                 *)
Definition good_graph1 : Env.t (list positive) :=
  to_graph [( 1, [2; 6]);
            ( 2, [3; 7]);
            ( 3, [4; 5]);
            ( 4, []);
            ( 5, []);
            ( 6, [7; 8]);
            ( 7, []);
            ( 8, [5]);
            ( 9, [10; 11]);
            (10, []);
            (11, [10])]%positive.

Lemma test1: check_graph good_graph1 = true.
Proof eq_refl.

Lemma test1b: exists xs,
    Permutation (map fst (Env.elements good_graph1)) xs
    /\ WellOrdered good_graph1 xs.
Proof check_graph_spec good_graph1 eq_refl.
    
(* As above, but link 4 back to 2 *)
Definition bad_graph1 : Env.t (list positive) :=
  (Env.add 4 [2] good_graph1)%positive.

Lemma test2: check_graph bad_graph1 = false.
Proof eq_refl.

Definition good_graph2 : Env.t (list positive) :=
  to_graph [(1, [2; 3; 4; 5; 6; 7; 8; 9; 10]);
            (2, []);
            (3, []);
            (4, []);
            (5, [10;8;7]);
            (6, []);
            (7, []);
            (8, []);
            (9, [2;3;4;5;6;7]);
            (10, [])]%positive.

Lemma test3: check_graph good_graph2 = true.
Proof eq_refl.

Lemma test3b: exists xs,
    Permutation (map fst (Env.elements good_graph2)) xs
    /\ WellOrdered good_graph2 xs.
Proof check_graph_spec good_graph2 eq_refl.

Definition bad_graph2 : Env.t (list positive) :=
  (Env.add 4 [9] (Env.add 3 [4] (Env.add 6 [3] good_graph2)))%positive.

Lemma test4: check_graph bad_graph2 = false.
Proof eq_refl.

