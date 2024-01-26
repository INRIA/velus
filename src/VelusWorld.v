From compcert Require Import common.Errors.
From compcert Require Import common.Events.
From compcert Require Import common.Behaviors.
From compcert Require Import common.Determinism.
From compcert Require Import common.Smallstep.

From Velus Require Import Common.
From Velus Require Import Ident.
From Velus Require Import CoindStreams.
From Velus Require Import Traces.
From Velus Require Import ObcToClight.Interface.
Import Op.

From Velus Require Import Velus.
From Velus Require Import Instantiator.
Import L.
Import CIStr.

From Coq Require Import Permutation.
From Coq Require Import String.

From Coq Require Import List.
Import List.ListNotations.

Open Scope stream_scope.

(** * An execution environment (“World”) *)

(** ** Abstract Definition of World *)

Definition state := list (ident * Stream value).

Definition update_assoc_ident [A] (x : ident) (vs : A) '(y, ys) : (ident * A) :=
  if ident_eqb x y then (y, vs) else (y, ys).

Definition get (s : state) (x : ident) : option (eventval * state) :=
  match assoc_ident x s with
  | None => None
  | Some (Cons v vs) => Some (eventval_of_value v, map (update_assoc_ident x vs) s)
  end.

CoFixpoint stream_world (s : state) : world :=
  World (fun evname evargs => None)
        (fun chunk id ofs =>
           option_map (fun z => (fst z, stream_world (snd z))) (get s id))
        (fun chunk id ofs v => Some (stream_world s)).

Lemma stream_world_deterministic:
  forall P si, sem_deterministic (world_sem (Asm.semantics P) (stream_world si)).
Proof.
  intros.
  apply world_sem_deterministic.
  apply Asm.semantics_determinate.
Qed.

Lemma stream_world_behaves_deterministic:
  forall P si, forall beh1 beh2 : program_behavior,
    program_behaves (world_sem (Asm.semantics P) (stream_world si)) beh1 ->
    program_behaves (world_sem (Asm.semantics P) (stream_world si)) beh2 ->
    same_behaviors beh1 beh2.
Proof.
  intros.
  eapply program_behaves_deterministic; eauto.
  apply stream_world_deterministic.
Qed.

(** *** Properties of [update_assoc_ident] *)

Section UpdateAssocIdent.

  Context {A : Type}.

  Lemma update_assoc_ident_inv:
    forall x sx (s : list (ident * A)),
      map fst (map (update_assoc_ident x sx) s) = map fst s.
  Proof.
    induction s as [|(y, ?) s]; [reflexivity|].
    simpl; rewrite IHs.
    destruct (ident_eqb x y); reflexivity.
  Qed.

  Lemma map_update_assoc_ident:
    forall z zs (s : list (ident * A)),
      ~InMembers z s ->
      map (update_assoc_ident z zs) s = s.
  Proof.
    induction s as [|(y, ys) s]; intro Hni. reflexivity.
    rewrite map_cons.
    apply NotInMembers_cons in Hni as (Hni1 & Hni2).
    setoid_rewrite (IHs Hni1). simpl.
    rewrite (proj2 (ident_eqb_neq z y)); auto.
  Qed.

  Lemma update_assoc_ident_not_In:
    forall x xs (ins : list A) s,
      ~ In x xs ->
      map (update_assoc_ident x s) (combine xs ins) = combine xs ins.
  Proof.
    induction xs as [|y xs]; [reflexivity|].
    intros ins s Hni.
    apply not_in_cons in Hni as [Hne Hni].
    destruct ins as [|i ins]; [reflexivity|].
    apply (IHxs ins s) in Hni.
    simpl. rewrite Hni. now apply ident_eqb_neq in Hne as ->.
  Qed.

  Lemma update_assoc_ident_not_eq:
    forall x y vs (s : list (ident * A)),
      x <> y ->
      assoc_ident (prefix_glob x) (map (update_assoc_ident (prefix_glob y) vs) s)
      = assoc_ident (prefix_glob x) s.
  Proof.
    induction s as [|(z, ?) s]; [reflexivity|].
    intro Hxy.
    simpl.
    destruct (ident_eqb (prefix_glob y) z) eqn:Hyz.
    - apply ident_eqb_eq in Hyz.
      assert (prefix_glob x <> z) as Hxz
          by (intro Hxz; rewrite <-Hxz in Hyz; apply prefix_glob_injective in Hyz; auto).
      rewrite assoc_ident_cons2, IHs, assoc_ident_cons2; auto.
    - apply ident_eqb_neq in Hyz.
      destruct (ident_eqb (prefix_glob x) z) eqn:Hxz.
      + apply ident_eqb_eq in Hxz.
        now rewrite Hxz, assoc_ident_cons1, assoc_ident_cons1.
      + apply ident_eqb_neq in Hxz.
        rewrite assoc_ident_cons2, assoc_ident_cons2, IHs; auto.
  Qed.

End UpdateAssocIdent.

(** ** Instantiate the World for a particular program *)

(** *** Preliminary Definitions: [consume] and [adv_stream_state] *)

Definition consume (s : state) (x : ident) : state :=
  match assoc_ident (prefix_glob x) s with
  | None => s
  | Some (Cons _ vs) => map (update_assoc_ident (prefix_glob x) vs) s
  end.

Lemma consume_nil:
  forall x, consume [] x = [].
Proof.
  intro x; unfold consume.
  now rewrite assoc_ident_nil.
Qed.

Lemma consume_cons:
  forall s x z zs,
    NoDupMembers ((z, zs) :: s) ->
    consume ((z, zs) :: s) x =
      (if ident_eqb (prefix_glob x) z then (z, Streams.tl zs) else (z, zs)) :: consume s x.
Proof.
  induction s as [|(y, ys) s]; intros x z zs Hnd.
  - rewrite consume_nil.
    unfold consume.
    destruct (ident_eqb (prefix_glob x) z) eqn:Hxz; simpl.
    + apply ident_eqb_eq in Hxz; subst.
      rewrite assoc_ident_cons1, ident_eqb_refl.
      now destruct zs.
    + apply ident_eqb_neq in Hxz; subst.
      now rewrite assoc_ident_cons2 with (1:=Hxz), assoc_ident_nil.
  - setoid_rewrite IHs; clear IHs. 2:now inv Hnd.
    unfold consume.
    destruct (ident_eqb (prefix_glob x) z) eqn:Hxz;
      destruct (ident_eqb (prefix_glob x) y) eqn:Hyz;
      simpl;
      repeat (match goal with
              | H:ident_eqb _ _ = true |- _ => apply ident_eqb_eq in H; subst;
                                             try rewrite assoc_ident_cons1, ident_eqb_refl
              | H:ident_eqb _ _ = false |- _ => rewrite H;
                                              apply ident_eqb_neq in H;
                                              try rewrite assoc_ident_cons2 with (1:=H)
              end);
      take (NoDupMembers _) and inv it;
      take (NoDupMembers _) and inv it;
      take (~InMembers _ (_ :: _)) and apply NotInMembers_cons in it as (? & ?).
    + contradiction.
    + destruct zs; simpl.
      rewrite map_update_assoc_ident; auto.
      now take (~InMembers (prefix_glob x) s) and apply assoc_ident_false in it as ->.
    + rewrite ident_eqb_refl, assoc_ident_cons1; auto.
      destruct ys; simpl.
      rewrite map_update_assoc_ident; auto.
      now take (~InMembers (prefix_glob x) s) and apply assoc_ident_false in it as ->.
    + repeat rewrite assoc_ident_cons2; auto.
      destruct (assoc_ident (prefix_glob x) s); auto.
      now destruct s0.
Qed.

Lemma get_consume:
  forall st x,
    get st (prefix_glob x) = option_map
                               (fun s => (eventval_of_value (Streams.hd s), consume st x))
                               (assoc_ident (prefix_glob x) st).
Proof.
  intros st x.
  unfold consume, get.
  destruct (assoc_ident (prefix_glob x) st); [|reflexivity].
  now destruct s.
Qed.

Lemma InMembers_consume:
  forall x s c,
    NoDupMembers s ->
    InMembers x s <-> InMembers x (consume s c).
Proof.
  induction s as [|(y, sy) s]. now split; inversion 1.
  split; intro IM.
  - rewrite consume_cons; auto.
    take (NoDupMembers (_ :: s)) and inv it. inv IM.
    now destruct (ident_eqb (prefix_glob c) x); simpl; eauto.
    destruct (ident_eqb (prefix_glob c) y); simpl; rewrite <-IHs; auto.
  - rewrite consume_cons in IM; auto.
    destruct (ident_eqb (prefix_glob c) y); destruct IM.
    + now subst; constructor.
    + take (InMembers x (consume s c)) and apply IHs in it.
      now constructor 2.
      now take (NoDupMembers _) and inv it.
    + now subst; constructor.
    + take (InMembers x (consume s c)) and apply IHs in it.
      now constructor 2.
      now take (NoDupMembers _) and inv it.
Qed.

Lemma NoDupMembers_consume:
  forall s x,
    NoDupMembers s <-> NoDupMembers (consume s x).
Proof.
  unfold consume. split; intros Hnd;
    destruct (assoc_ident (prefix_glob x) s) as [(v & vs)|]; auto;
    rewrite fst_NoDupMembers in *;
    now rewrite update_assoc_ident_inv in *.
Qed.

Lemma consume_commute:
  forall s x y,
    NoDupMembers s ->
    x <> y ->
    consume (consume s x) y = consume (consume s y) x.
Proof.
  induction s as [|(z, zs) s].
  now setoid_rewrite consume_nil.
  intros x y Hnd Hne.
  setoid_rewrite consume_cons; auto.
  assert (NoDupMembers (consume s x))
    by (now apply NoDupMembers_consume; inv Hnd).
  destruct (ident_eqb (prefix_glob x) z) eqn:Hxz;
    destruct (ident_eqb (prefix_glob y) z) eqn:Hyz;
    setoid_rewrite consume_cons;
    repeat (match goal with
            | H:ident_eqb _ _ = true |- _ => apply ident_eqb_eq in H; subst
            | H:ident_eqb _ _ = false |- _ => rewrite H; apply ident_eqb_neq in H
            | H:_ = _ |- _ => rewrite H; clear H
            | H:NoDupMembers (consume _ _) |- _ => apply NoDupMembers_consume in H
            | |- NoDupMembers (_ :: _) => constructor
            | |- NoDupMembers (consume _ _) => apply NoDupMembers_consume
            | H:NoDupMembers (_ :: _) |- _ => inv H
            | |- ~InMembers _ _ => rewrite <-InMembers_consume
            end; auto);
    try rewrite ident_eqb_refl;
    try rewrite IHs; auto.
Qed.

Lemma assoc_ident_not_consumed:
  forall x xs,
    ~ In x xs ->
    forall s, assoc_ident (prefix_glob x) (fold_left consume xs s)
         = assoc_ident (prefix_glob x) s.
Proof.
  induction xs as [|y xs]; [reflexivity|]; intros Hni s.
  apply not_in_cons in Hni as (? & ?).
  simpl; rewrite IHxs; auto.
  unfold consume. destruct (assoc_ident (prefix_glob y) s) as [(v, vs)|];
    [|reflexivity].
  rewrite update_assoc_ident_not_eq; auto.
Qed.

Lemma fold_left_consume_cons:
  forall e cs s,
    ~In (fst e) (map prefix_glob cs) ->
    NoDupMembers (e :: s) ->
    fold_left consume cs (e :: s) = e :: fold_left consume cs s.
Proof.
  induction cs as [|c cs]; auto.
  destruct e as (x, sx).
  simpl. intros s Hni Hnd.
  rewrite consume_cons; auto.
  apply Decidable.not_or in Hni as (Hni1 & Hni2).
  inv Hnd.
  take (NoDupMembers s) and rename it into Hnd.
  take (~InMembers x s) and rename it into Hni.
  rewrite (InMembers_consume _ _ c Hnd) in Hni.
  apply (NoDupMembers_consume _ c) in Hnd.
  setoid_rewrite <-IHcs; auto. 2:now constructor.
  now apply ident_eqb_neq in Hni1 as ->.
Qed.

Function adv_stream_state (n : nat) (cs : list ident) (s : state) : state :=
  match n with
  | 0 => List.fold_left consume cs s
  | S n => adv_stream_state n cs
            (List.map (fun xs => (fst xs, Streams.tl (snd xs))) s)
  end.

Lemma adv_stream_state_drop:
  forall cs n s,
    adv_stream_state n cs s
    = fold_left consume cs (map (fun xs => (fst xs, Str_nth_tl n (snd xs))) s).
Proof.
  induction n; intro s; simpl.
  - assert (map (fun xs => (fst xs, snd xs)) s = s) as ->
      by (induction s as [|(x1, x2) s]; simpl; auto).
    reflexivity.
  - now rewrite IHn, map_map; simpl.
Qed.

Lemma adv_stream_state_map:
  forall s cs,
    NoDupMembers s ->
    NoDup cs ->
    forall n, adv_stream_state n cs s
         = map (fun xs => (fst xs, Str_nth_tl
                    (if mem_ident (fst xs) (map prefix_glob cs) then S n else n)
                    (snd xs))) s.
Proof.
  setoid_rewrite adv_stream_state_drop.
  (* induction on s *)
  induction s as [|(x, sx) s]; intros cs Hnds Hndcs n.
  now simpl; clear Hndcs; induction cs; auto.
  simpl. rewrite <-IHs; auto. 2:now inv Hnds. clear IHs.
  (* induction on cs *)
  remember (map (fun xs => (fst xs, Str_nth_tl n (snd xs))) s) as S eqn:HS.
  assert (~InMembers x S) as Hnm
      by (inv Hnds; rewrite fst_InMembers, map_map; simpl;
          now rewrite <-fst_InMembers).
  assert (NoDupMembers S) as Hnds'
      by (subst; inv Hnds; apply NoDupMembers_map; auto).
  revert Hnds' Hndcs Hnm; clear; revert S.
  induction cs as [|c cs]; auto.
  intros S Hnds Hndcs Hnm; simpl.
  rewrite consume_cons. 2:now constructor.
  assert (~In (prefix_glob c) (map prefix_glob cs)) as Hin.
  { intro Hi. inv Hndcs. take(~In c cs) and apply it; clear it.
    now apply (in_inj_app_map _ prefix_glob_injective) in Hi. }
  assert (NoDupMembers (consume S c)) by (now apply NoDupMembers_consume).
  destruct (ident_eq_dec (prefix_glob c) x) as [Hcx|Hcx].
  - subst; rewrite ident_eqb_refl; simpl.
    rewrite tl_nth_tl, fold_left_consume_cons; auto.
    constructor; auto.
    intro Hc; apply InMembers_consume in Hc; auto.
  - apply ident_eqb_neq in Hcx as ->; simpl.
    inv Hndcs; rewrite IHcs; clear IHcs; auto.
    rewrite <-InMembers_consume; auto.
Qed.

Lemma consume_next:
  forall x xs n si,
    ~InMembers x xs ->
    NoDupMembers xs ->
    NoDupMembers si ->
    consume (adv_stream_state n (idents xs) si) x
    = adv_stream_state n (x :: idents xs) si.
Proof.
  intros x xs n; revert xs; induction n.
  - simpl.
    induction xs as [|y xs]; [reflexivity|].
    intros s Hni Hndxs Hnds. inv Hndxs.
    apply NotInMembers_cons in Hni as (Hni & Hnd).
    simpl. rewrite consume_commute; auto.
    rewrite <-IHxs; auto.
    now apply NoDupMembers_consume.
  - simpl.
    intros xs si Hni Hndxs Hnds.
    rewrite IHn; auto.
    apply NoDupMembers_map; auto.
Qed.

(** *** Instantiate the world for Lustre programs *)

Section VelusWorld.

  Context {PSyn : list decl -> block -> Prop} {prefs : PS.t}.
  Variable (G : @global PSyn prefs).

  Function init_stream_state (f : ident) (ins : list (Stream value)) : state :=
    match find_node f G with
    | Some node =>
        combine (map (Basics.compose prefix_glob fst) (@n_in PSyn prefs node)) ins
    | None => []
    end.

  Definition velus_world (f : ident) (ins : list (Stream value)) : world
    := stream_world (init_stream_state f ins).

  Definition nth_stream_state (f : ident) (ins : list (Stream value))
                              (n : nat) (cs : list ident) : state :=
    adv_stream_state n cs (init_stream_state f ins).

  Lemma NoDupMembers_init_stream_state:
    forall f ins, NoDupMembers (init_stream_state f ins).
  Proof.
    intros.
    unfold init_stream_state.
    destruct (find_node f G); auto using NoDupMembers_nil.
    apply NoDup_NoDupMembers_combine.
    pose proof (NoDupMembers_n_in n) as Hnd.
    induction n.(n_in) as [|(x, ?) xs]; [now constructor|].
    unfold Basics.compose at 1; simpl.
    inv Hnd. constructor; [|now apply IHxs].
    take (NoDupMembers xs) and clear it IHxs.
    take (~InMembers x xs) and revert x xs it.
    clear; induction xs as [|(y, ?) xs]; [now inversion 2|].
    intros Hni Hi; apply Hni.
    apply NotInMembers_cons in Hni as [Hni Hne].
    constructor 2.
    destruct Hi as [Hi|Hi].
    now apply prefix_glob_injective in Hi; exfalso; apply Hne.
    specialize (IHxs Hni). now exfalso; apply IHxs.
  Qed.

  Lemma nth_stream_state_permutation:
    forall f n ins xs,
      NoDup xs ->
      forall xs',
        Permutation xs xs' ->
        nth_stream_state f ins n xs = nth_stream_state f ins n xs'.
  Proof.
    unfold nth_stream_state.
    intros * Hnd * Hperm.
    setoid_rewrite adv_stream_state_drop.
    match goal with |- context [ fold_left _ _ ?s = _ ] =>
                      assert (NoDupMembers s) as Hnd'
                        by (apply NoDupMembers_map; auto;
                            apply (NoDupMembers_init_stream_state f ins));
                      revert Hnd'; generalize s
    end.
    induction Hperm; simpl; intros ll Hnd'.
    - reflexivity.
    - apply NoDup_cons_iff in Hnd as (Hni & Hnd).
      setoid_rewrite (IHHperm Hnd); auto; now apply NoDupMembers_consume.
    - apply NoDup_cons_iff in Hnd as (Hny & Hnd).
      apply NoDup_cons_iff in Hnd as (Hnx & Hnd).
      apply not_in_cons in Hny as (Nne & Hny).
      rewrite consume_commute; auto.
    - specialize (IHHperm1 Hnd).
      rewrite Hperm1 in Hnd; specialize (IHHperm2 Hnd).
      rewrite IHHperm1; auto.
  Qed.

  Lemma assoc_ident_nth_stream_state:
    forall f ins n,
    forall (node: @node PSyn prefs), find_node f G = Some node ->
    forall xs x, InMembers x node.(n_in) ->
            ~In x xs ->
            assoc_ident (prefix_glob x) (nth_stream_state f ins n xs)
            = assoc_ident x (combine (map fst node.(n_in)) (List.map (Str_nth_tl n) ins)).
  Proof.
    intros * Hfind * Hin; rename node0 into node.
    unfold nth_stream_state.
    rewrite adv_stream_state_drop; simpl.
    unfold init_stream_state. rewrite Hfind; clear Hfind.
    pose proof (NoDupMembers_n_in node) as Hnd.
    intro Hni; rewrite assoc_ident_not_consumed; auto.
    clear xs Hni.
    revert ins; induction node.(n_in) as [|(y, sy) ys]. reflexivity.
    destruct ins as [|i ins]. reflexivity.
    destruct Hin as [Hin|Hin].
    - subst. clear IHys.
      simpl. now setoid_rewrite assoc_ident_cons1.
    - apply NoDupMembers_cons_inv in Hnd as [Hnin Hnd].
      specialize (IHys Hin Hnd ins).
      assert (x <> y) by (now intro; apply Hnin; subst).
      simpl; setoid_rewrite assoc_ident_cons2; auto.
      unfold Basics.compose; simpl.
      intro Hpg; apply prefix_glob_injective in Hpg; auto.
  Qed.

  Corollary consume_next_nth_stream_state:
    forall f ins n x xs,
      ~InMembers x xs ->
      NoDupMembers xs ->
      consume (nth_stream_state f ins n (idents xs)) x
      = nth_stream_state f ins n (x :: idents xs).
  Proof.
    intros * Hni Hnd.
    apply consume_next; auto.
    apply NoDupMembers_init_stream_state.
  Qed.

  Lemma nth_stream_state_next:
    forall (node: @node PSyn prefs) f ins,
      find_node f G = Some node ->
      forall Len_ins: Datatypes.length ins = Datatypes.length node.(n_in),
      forall n, nth_stream_state f ins n (idents node.(n_in))
           = nth_stream_state f ins (S n) [].
  Proof.
    intros node f ins FN Hlen.
    unfold nth_stream_state.
    assert (NoDup (idents node.(n_in))) as Hnd
        by (pose proof (NoDupMembers_n_in node) as Hnd;
            now apply fst_NoDupMembers in Hnd).
    pose proof (NoDupMembers_init_stream_state f ins) as Hndm.
    setoid_rewrite adv_stream_state_map; auto using NoDup.
    intro n. simpl.
    assert (map prefix_glob (idents node.(n_in)) = map fst (init_stream_state f ins)) as ->.
    { unfold init_stream_state, idents, Basics.compose; rewrite FN.
      rewrite combine_map_fst', map_map; auto. now rewrite map_length. }
    revert Hndm; generalize (init_stream_state f ins); clear.
    induction s as [|(x, sx) s]; simpl; auto. intro Hndm; inv Hndm.
    rewrite ident_eqb_refl, <-IHs; simpl; clear IHs; auto.
    match goal with |- (_ :: ?left) = (_ :: ?right) => cut (left = right) end.
    now intro HH; rewrite HH.
    apply map_ext_in. intros (y, sy) Hi; simpl.
    assert (x <> y) as Hxy
        by (intro Hxy; take (~InMembers x s) and apply it; subst;
            apply In_InMembers with (1:=Hi)).
    now apply ident_eqb_neq in Hxy as ->.
  Qed.

  (* TODO: possible to separate out the generic and specific parts.
     I.e., possible_traceinf wi t -> ... *)
  Lemma velus_world_forever_reactive:
    forall P, single_events P ->
    forall f ins outs (node: @node PSyn prefs),
    find_node f G = Some node ->
    forall Len_ins: Datatypes.length ins = Datatypes.length node.(n_in),
    forall Len_outs: Datatypes.length outs = Datatypes.length node.(n_out),
    forall s n,
      Forever_reactive P s
        (trace_node node ins outs Len_ins Len_outs n) ->
      Forever_reactive (world_sem P (velus_world f ins))
        (s, stream_world (nth_stream_state f ins n []))
        (trace_node node ins outs Len_ins Len_outs n).
  Proof.
    intros P SE f ins outs node FN Len_ins Len_outs.
    cofix CI.
    intros * FR.
    rewrite trace_node_step in FR.
    apply CompCertLib.inv_forever_reactive with (1:=SE) in FR as (s' & Hstar & FR).
    rewrite trace_node_step.
    apply forever_reactive_intro
      with (s2 := (s', stream_world (nth_stream_state f ins (S n) []))).
    - (* star s s' -> star (s, n) (s', n + 1) *)
      clear CI FR.
      apply CompCertLib.single_events_star_split with (1:=SE) in Hstar
          as (sl & Hload & Hstore).
      eapply star_trans with (s2:=(sl, stream_world (nth_stream_state f ins (S n) [])));
        [| |reflexivity].
      + (* star load_events *)
        (* TODO: tidy up. State as a separate lemma? *)
        rewrite <-nth_stream_state_next with (1:=FN) (2:=Len_ins).
        assert (Datatypes.length ins
                = Datatypes.length (idfst (idfst (n_in node)))) as Hlen
            by (rewrite Len_ins; now repeat rewrite length_idfst).
        clear Hstore Len_outs outs Len_ins s'.
        pose proof (assoc_ident_nth_stream_state _ ins n _ FN) as Hinv.
        pose proof (eq_refl node.(n_in)) as Hn.
        revert Hn Hinv Hload Hlen.
        generalize node.(n_in) at 2 3 4 5 7 as xs.
        generalize ins at 2 3 4 10 as xins.
        intros xins xs Hn.
        pose proof Hn as Hn'. rewrite <- (app_nil_l xs) in Hn.
        assert ([] = idents []) as Hids by reflexivity.
        revert Hids Hn.
        generalize ([] : list (ident * (type * Cks.clock * ident))) at 1 2 as xs'.
        intros xs' Hids Hn.
        repeat rewrite length_idfst.
        setoid_rewrite Hn' at 1; clear Hn'. rewrite Hn.
        setoid_rewrite Hids; clear Hids.
        pose proof (NoDupMembers_n_in node) as Hnd; rewrite Hn in Hnd.
        clear Hn. revert SE xs' xins s sl Hnd. clear. intro SE.
        induction xs as [|[x [[xty xck] xid]] xs].
        * intros xs' xins. unfold load_events.
          intros s s' Hin Hinv Hstar Hlen.
          eapply CompCertLib.star_world_sem with (1:=Hstar).
          simpl; rewrite app_nil_r, map2_nil_r; now constructor.
        * intros xs' xins s s' Hnd Hinv Hstar Hlen.
          destruct xins as [|xi xins]; inv Hlen.
          simpl in Hstar.
          change (Star P s ([load_event_of_value (tr_Stream xi n) (x, xty)]
                              ** load_events (tr_Streams xins n) (idfst (idfst xs))) s')
            in Hstar.
          apply CompCertLib.single_events_star_split with (1:=SE) in Hstar
              as (s'' & Hstar1 & Hstar2).
          rewrite <-Permutation_middle, app_comm_cons in Hnd.
          eapply IHxs in Hstar2; eauto; clear IHxs.
          2:{ (* invariant preservation *)
            clear Hstar1 Hstar2.
            intros ys y Hyin Hyni; simpl.
            assert (y <> x) as Hyx.
            { intro; subst.
              simpl in Hnd; rewrite Permutation_middle in Hnd.
              apply NoDupMembers_app_r in Hnd. now inv Hnd. }
            rewrite Hinv; simpl; auto.
            rewrite assoc_ident_cons2; auto.
          }
          assert (Permutation (idents (xs' ++ (x, (xty, xck, xid)) :: xs))
                    (idents ((x, (xty, xck, xid)) :: xs' ++ xs))) as Hperm
              by (now rewrite Permutation_middle).
          assert (NoDup (idents (xs' ++ (x, (xty, xck, xid)) :: xs))) as Hnd'
              by (rewrite Hperm; unfold idents; now apply fst_NoDupMembers).
          rewrite (nth_stream_state_permutation _ _ _ _ Hnd' _ Hperm).
          match goal with
          | |- star _ _ _ (load_events ?ii ?xx) _ =>
              change (load_events ?ii ?xx)
              with ([load_event_of_value (tr_Stream xi n) (x, xty)]
                      ++ load_events (tr_Streams xins n) (idfst (idfst xs)))
          end.
          rewrite app_comm_cons.
          eapply star_trans
            with (2:=Hstar2) (t1:=[load_event_of_value (tr_Stream xi n) (x, xty)]); auto.
          apply CompCertLib.star_world_sem with (1:=Hstar1); clear Hstar1 Hstar2.
          simpl.
          apply possible_trace_cons
            with (w2:=stream_world (nth_stream_state f ins n (x :: idents xs'))).
          2:now constructor.
          constructor; simpl.
          rewrite get_consume.
          assert (~In x (idents xs')).
          { unfold idents in Hnd'; apply fst_NoDupMembers in Hnd'.
            rewrite <-Permutation_middle in Hnd'.
            apply NoDupMembers_cons_inv in Hnd' as (Hnd' & _).
            apply NotInMembers_app in Hnd' as (_ & Hnd').
            now rewrite fst_InMembers in Hnd'. }
          rewrite Hinv; simpl; auto.
          rewrite assoc_ident_cons1.
          destruct (Str_nth_tl n xi) as [v vs] eqn:Hxi.
          unfold tr_Stream, Str_nth; rewrite Hxi; simpl.
          apply NoDupMembers_app_l in Hnd; inv Hnd.
          rewrite consume_next_nth_stream_state; auto.
      + (* star store_events *)
        generalize (nth_stream_state f ins (S n) []) as w; intros w.
        assert (Datatypes.length outs
                = Datatypes.length (idfst (idfst (idfst (n_out node))))) as Hlen
            by (rewrite Len_outs; now repeat rewrite length_idfst).
        revert Hstore Hlen. generalize (idfst (idfst (idfst (n_out node)))) as xs.
        clear Hload Len_ins FN s Len_outs.
        intro xs; revert xs outs sl s'.
        induction xs as [|x xs]; intros outs s s' Hstar Hout.
        * unfold store_events in *. rewrite map2_nil_r in *.
          eauto using CompCertLib.star_world_sem, possible_trace.
        * destruct outs as [|o outs]; inv Hout.
          change (Star P s ([store_event_of_value (tr_Stream o n) x]
                              ** store_events (tr_Streams outs n) xs) s') in Hstar.
          apply CompCertLib.single_events_star_split with (1:=SE) in Hstar
              as (s'' & Hstar1 & Hstar2).
          apply IHxs in Hstar2; auto.
          apply star_trans
            with (2:=Hstar2) (t1:=[store_event_of_value (tr_Stream o n) x]); auto.
          apply CompCertLib.star_world_sem with (1:=Hstar1).
          apply possible_trace_cons with (w2:=stream_world w);
            eauto using possible_trace, possible_event.
    - (* load_events _ _ ** store_events _ _ <> E0 *)
      clear CI Hstar FR s s'.
      unfold tr_Streams at 1.
      pose proof node.(n_ingt0) as Hgt0.
      destruct node.(n_in); [inv Hgt0|clear Hgt0].
      destruct ins; [inv Len_ins|].
      inversion 1.
    - (* forever_reactive s' -> forever_reactive (s', n + 1) *)
      now apply (CI _ _ FR).
  Qed.

  Lemma velus_world_behaves:
    forall P main,
      single_events P ->
      forall ins outs node,
        find_node main G = Some node ->
      forall Len_ins: Datatypes.length ins = Datatypes.length node.(n_in),
      forall Len_outs: Datatypes.length outs = Datatypes.length node.(n_out),
        program_behaves P
          (Reacts (trace_node node ins outs Len_ins Len_outs 0)) ->
        program_behaves (world_sem P (velus_world main ins))
          (Reacts (trace_node node ins outs Len_ins Len_outs 0)).
  Proof.
    intros * SE * FN * PB.
    inv PB.
    eapply program_runs with (s:=(s, velus_world main ins)).
    now constructor; auto.
    take (state_behaves P s (Reacts _)) and inv it.
    take (Forever_reactive P s _)
      and apply velus_world_forever_reactive with (1:=SE) (2:=FN) in it.
    now constructor.
  Qed.

  Lemma asm_and_velus_world_deterministic:
    forall P main ins beh1 beh2,
      program_behaves (world_sem (Asm.semantics P) (velus_world main ins)) beh1 ->
      program_behaves (world_sem (Asm.semantics P) (velus_world main ins)) beh2 ->
      same_behaviors beh1 beh2.
  Proof.
    intros * PB1 PB2.
    apply stream_world_behaves_deterministic with (1:=PB1) (2:=PB2).
  Qed.

  Corollary react_in_asm_and_velus_world_never_goes_wrong:
    forall P main ins t,
      program_behaves (world_sem (Asm.semantics P) (velus_world main ins)) (Reacts t) ->
      ~exists t', program_behaves (world_sem (Asm.semantics P) (velus_world main ins)) (Goes_wrong t').
  Proof.
    intros * PB1.
    apply Classical_Pred_Type.all_not_not_ex.
    intros t' PB2.
    apply asm_and_velus_world_deterministic with (1:=PB1) in PB2.
    now inv PB2.
  Qed.

End VelusWorld.

