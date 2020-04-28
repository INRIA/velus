From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Streams.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Setoid.
From Coq Require Import Morphisms.

From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import CommonList.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax Lustre.LClocking Lustre.LOrdered Lustre.LSemantics.
From Velus Require Import CoindStreams.

Local Set Warnings "-masking-absolute-name".
Module Type LCLOCKSEMANTICS
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Syn : LSYNTAX Ids Op)
       (Import Clo : LCLOCKING Ids Op Syn)
       (Import Lord : LORDERED Ids Op Syn)
       (Import Str : COINDSTREAMS Op OpAux)
       (Import Sem : LSEMANTICS Ids Op OpAux Syn Lord Str).

  Definition history_tl (H: history) : history := Env.map (@tl value) H.

  Fact history_tl_find : forall (H: history) id vs,
      Env.find id H = Some vs ->
      Env.find id (history_tl H) = Some (tl vs).
  Proof.
    intros H id vs Hfind.
    unfold history_tl.
    rewrite Env.Props.P.F.map_o.
    rewrite Hfind. reflexivity.
  Qed.

  Fact history_tl_find_None : forall (H: history) id,
      Env.find id H = None ->
      Env.find id (history_tl H) = None.
  Proof.
    intros H id Hfind.
    unfold history_tl.
    rewrite Env.Props.P.F.map_o.
    rewrite Hfind. reflexivity.
  Qed.

  CoInductive sem_clock: history -> Stream bool -> clock -> Stream bool -> Prop :=
  | Sbase:
      forall H b b',
        b ≡ b' ->
        sem_clock H b Cbase b'
  | Son:
      forall H b bk bs ck x k xs c,
        sem_clock H b ck (true ⋅ bk) ->
        sem_var H x (present c ⋅ xs) ->
        val_to_bool c = Some k ->
        sem_clock (history_tl H) (tl b) (Con ck x k) bs ->
        sem_clock H b (Con ck x k) (true ⋅ bs)
  | Son_abs1:
      forall H b bk bs ck x k xs,
        sem_clock H b ck (false ⋅ bk) ->
        sem_var H x (absent ⋅ xs) ->
        sem_clock (history_tl H) (tl b) (Con ck x k) bs ->
        sem_clock H b (Con ck x k) (false ⋅ bs)
  | Son_abs2:
      forall H b bk bs ck x k c xs,
        sem_clock H b ck (true ⋅ bk) ->
        sem_var H x (present c ⋅ xs) ->
        val_to_bool c = Some k ->
        sem_clock (history_tl H) (tl b) (Con ck x (negb k)) bs ->
        sem_clock H b (Con ck x (negb k)) (false ⋅ bs).

  CoInductive synchronized: Stream value -> Stream bool -> Prop :=
  | synchro_present:
      forall v vs bs,
        synchronized vs bs ->
        synchronized (present v ⋅ vs) (true ⋅ bs)
  | synchro_absent:
      forall vs bs,
        synchronized vs bs ->
        synchronized (absent ⋅ vs) (false ⋅ bs).

  Fixpoint interp_clock H b cl : Stream bool :=
    match cl with
    | Cbase => b
    | Con cl id b' =>
      let b := interp_clock H b cl in
      match Env.find id H with
      | Some v =>
        map2 (fun b v => match v with
                      | OpAux.present v =>
                        match OpAux.val_to_bool v with
                        | Some true => andb b b'
                        | Some false => andb b (negb b')
                        | _ => false
                        end
                      | _ => false
                      end) b v
      | None => b
      end
    end.


  Fact interp_clock_hd : forall cl H b bs,
      hd (interp_clock H (b ⋅ bs) cl) =
         match cl with
         | Cbase => b
         | Con cl id b' =>
           let b := hd (interp_clock H (b ⋅ bs) cl) in
           match Env.find id H with
           | Some v => match (hd v) with
                      | present v => match (OpAux.val_to_bool v) with
                                    | Some true => andb b b'
                                    | Some false => andb b (negb b')
                                    | _ => false
                                    end
                      | absent => false
                      end
           | None => b
           end
         end.
  Proof.
    induction cl; intros H b0 bs.
    - reflexivity.
    - destruct (Env.find i H) eqn:Hfind; simpl.
      + rewrite Hfind.
        rewrite <- map2_hd. reflexivity.
      + simpl. rewrite Hfind. reflexivity.
  Qed.

  Fact interp_clock_tl : forall cl H bs,
      tl (interp_clock H bs cl) ≡ interp_clock (history_tl H) (tl bs) cl.
  Proof.
    induction cl; intros H bs; simpl in *.
    - reflexivity.
    - destruct (Env.find i H) eqn:Hfind.
      + apply history_tl_find in Hfind. rewrite Hfind.
        rewrite <- map2_tl. rewrite IHcl. reflexivity.
      + apply history_tl_find_None in Hfind. rewrite Hfind. auto.
  Qed.

  Lemma interp_clock_Cons : forall cl H b bs,
      interp_clock H (b ⋅ bs) cl ≡ hd (interp_clock H (b ⋅ bs) cl) ⋅ (interp_clock (history_tl H) bs cl).
  Proof.
    intros cl H b bs.
    constructor; simpl; auto.
    symmetry. replace bs with (tl (b ⋅ bs)) at 1; auto.
    rewrite interp_clock_tl. reflexivity.
  Qed.

  Fact interp_clock_sound_instant : forall cl H bs bs',
      sem_clock H bs cl bs' ->
      hd (interp_clock H bs cl) = hd bs'.
  Proof with eauto.
    induction cl; intros H [b0 bs] bs' Hsem; inv Hsem.
    - inv H1...
    - eapply IHcl in H4.
      rewrite interp_clock_hd; simpl.
      inv H7. eapply Env.find_1 in H1. rewrite H1.
      rewrite <- H2; simpl. rewrite H9; simpl. rewrite H4; simpl.
      destruct b...
    - rewrite interp_clock_hd; simpl.
      inv H8. eapply Env.find_1 in H1. rewrite H1.
      rewrite <- H2. reflexivity.
    - eapply IHcl in H4.
      rewrite interp_clock_hd; simpl.
      inv H7. eapply Env.find_1 in H1. rewrite H1.
      rewrite <- H2; simpl. rewrite H9; simpl. rewrite H4; simpl.
      destruct k...
  Qed.

  Lemma interp_clock_sound : forall cl H bs bs',
      sem_clock H bs cl bs' ->
      interp_clock H bs cl ≡ bs'.
  Proof with eauto.
    cofix interp_clock_sound.
    intros cl H [b bs] [b' bs'] Hsem.
    constructor; simpl.
    - apply interp_clock_sound_instant in Hsem...
    - inv Hsem.
      + inv H1...
      + rewrite interp_clock_tl...
      + rewrite interp_clock_tl...
      + rewrite interp_clock_tl...
  Admitted.

  (* Lemma sem_exp_synchronized : forall G H b e vs, *)
  (*     sem_exp G H b e vs -> *)
  (*     Forall2 synchronized vs (List.map (interp_clock H b) (clockof e)). *)
  (* Proof. *)
  (*   induction e; intros vs Hsem; inv Hsem. *)
  (*   - (* const *) *)
  (*     repeat constructor. *)
  (*     rewrite H4. *)
  (* Qed. *)
End LCLOCKSEMANTICS.


Module LClockSemanticsFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Syn : LSYNTAX Ids Op)
       (Clo : LCLOCKING Ids Op Syn)
       (Lord : LORDERED Ids Op Syn)
       (Str : COINDSTREAMS Op OpAux)
       (Sem : LSEMANTICS Ids Op OpAux Syn Lord Str) <: LCLOCKSEMANTICS Ids Op OpAux Syn Clo Lord Str Sem.
  Include LCLOCKSEMANTICS Ids Op OpAux Syn Clo Lord Str Sem.
End LClockSemanticsFun.
