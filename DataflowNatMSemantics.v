Require Import Coq.FSets.FMapPositive.
Require Import Rustre.Common.
Require Import Rustre.DataflowSyntax.
Require Import SynchronousNat.
Require Import DataflowNatSemantics.

(*
   NB: The history H is not really necessary here. We could just as well
       replay all the semantic definitions using a valueEnv N ('N' for now),
       since all the historical information is in ms. This approach would
       have two advantages:

       1. Conceptually cleanliness: N corresponds more or less to the
          temporary variables in the Minimp implementation (except that it
          would also contain values for variables defined by EqFby).

       2. No index needed to access values in when reasoning about
          translation correctness.

       But this approach requires more uninteresting definitions and
       and associated proofs of properties, and a longer proof of equivalence
       with sem_node: too much work for too little gain.
 *)

Inductive memory : Set := mk_memory {
  mm_values : PM.t (nat -> const);
  mm_instances : PM.t memory
}.

Definition mfind_mem x menv := PM.find x menv.(mm_values).
Definition mfind_inst f menv := PM.find f menv.(mm_instances).

Inductive msem_equation (G: global) : history -> memory -> equation -> Prop :=
| SEqDef:
    forall H M x cae,
      (forall n,
          exists v, sem_var H x n v
                    /\ sem_caexp H cae n v) ->
      msem_equation G H M (EqDef x cae)
| SEqApp:
    forall H M x f M' arg ls xs,
      mfind_inst x M = Some M' ->
      (forall n, sem_laexp H arg n (ls n)) ->
      (forall n, sem_var H x n (xs n)) ->
      msem_node G f ls M' xs ->
      msem_equation G H M (EqApp x f arg)
| SEqFby:
    forall H M ms x ls v0 lae,
      mfind_mem x M = Some ms ->
      ms 0 = v0 ->
      (forall n, sem_laexp H lae n (ls n)) ->
      (forall n, match ls n with
                 | absent    => ms (S n) = ms n              (* held *)
                                /\ sem_var H x n absent
                 | present v => ms (S n) = v
                                /\ sem_var H x n (present (ms n))
                 end) ->
      msem_equation G H M (EqFby x v0 lae)

with msem_node (G: global) : ident -> stream -> memory -> stream -> Prop :=
| SNode:
    forall f xs M ys i o eqs,
      find_node f G = Some (mk_node f i o eqs) ->
      (exists (H: history),
        (forall n, sem_var H i.(v_name) n (xs n))
        /\ (forall n, sem_var H o.(v_name) n (ys n))
        /\ List.Forall (msem_equation G H M) eqs) ->
        msem_node G f xs M ys.

(* TODO: Warning: Ignoring recursive call
         We must write these induction principles manually. *)
(*
Scheme msem_equation_mult := Induction for msem_equation Sort Prop
with msem_node_mult := Induction for msem_node Sort Prop.

(* TODO: move to DataflowNatSemantics.v *)
Scheme sem_equation_mult := Induction for sem_equation Sort Prop
with sem_node_mult := Induction for sem_node Sort Prop.
*)

Definition msem_nodes (G: global) : Prop :=
  List.Forall (fun no => exists xs M ys, msem_node G no.(n_name) xs M ys) G.

Lemma msem_node_cons:
  forall node G f xs M ys,
    Ordered_nodes (node::G)
    -> msem_node (node :: G) f xs M ys
    -> node.(n_name) <> f
    -> msem_node G f xs M ys.
Proof.
Admitted.   (* TODO: Show this! *)

(* TODO:
    show that:
       sem_node G f xs ys
       <->
       (exists ms, msem_node G f xs ms ys)

    this requires constructing an ms: what can we reuse from the
    sem_held_equations development?

    then it is trivial that:
       sem_nodes G <-> msem_nodes G
 *)


Lemma sem_msem_node:
  forall G f xs ys,
    sem_node G f xs ys <-> (exists ms, msem_node G f xs ms ys).
Proof.
  intros G f xs ys.
  split; [ intro Hsem | intro Hmsem ].
  - admit.
  - admit.
Qed.

(* TODO:
    - rework is_step_correct.
    - base it on msem_node G f xs ms ys
    - induction on G, with well-defined predicate
    - memories correspond to values of ms (and recursively for called nodes)
    - local history corresponds to env
    - inputs and outputs link correctly with xs and ys

    - show that reset gives the first memory
 *)

(* TODO:
    - prove correctness in terms of sem_node G f xs ys,
      hiding the internal memory details.
      (provided the initial memory is created by reset)
 *)

Lemma find_node_msem_node:
  forall G f,
    msem_nodes G
    -> find_node f G <> None
    -> (exists xs M ys, msem_node G f xs M ys).
Proof.
  intros G f Hnds Hfind.
  apply find_node_Exists in Hfind.
  apply List.Exists_exists in Hfind.
  destruct Hfind as [nd [Hin Hf]].
  unfold msem_nodes in Hnds.
  rewrite List.Forall_forall in Hnds.
  apply Hnds in Hin.
  destruct Hin as [xs [M [ys Hmsem]]].
  exists xs; exists M; exists ys.
  rewrite Hf in *.
  exact Hmsem.
Qed.

(* TODO: Replace with the new development in DataflowNatMSemantics:

Inductive sem_held_equation (H: history) (H': history) : equation -> Prop :=
| SHEqDef:
    forall x cae,
      (forall n c, sem_var H x n (present c) -> sem_var H' x n (present c))
      -> sem_held_equation H H' (EqDef x cae)
| SHEqApp:
    forall x f lae,
      (forall n c, sem_var H x n (present c) -> sem_var H' x n (present c))
      -> sem_held_equation H H' (EqApp x f lae)
| SHEqFby:
    forall x v0 lae ys,
      (forall n, sem_laexp H lae n (ys n))
      -> (forall n c, sem_var H' x n (present c) <-> holdR v0 ys n c)
      -> sem_held_equation H H' (EqFby x v0 lae).

Definition sem_held_equations
           (H: history) (H': history) (eqs: list equation) : Prop :=
  List.Forall (sem_held_equation H H') eqs.

Lemma sem_held_equations_tl:
  forall H H' eq eqs,
    sem_held_equations H H' (eq::eqs) -> sem_held_equations H H' eqs.
Proof.
  intros H H' eq eqs Hsem.
  apply Forall_cons2 in Hsem.
  intuition.
Qed.

Lemma sem_held_equations_corres:
  forall G H H' eqs,
    sem_equations G H eqs
    -> sem_held_equations H H' eqs
    -> (forall x n c,
           Is_defined_in x eqs
           -> sem_var H x n (present c)
           -> sem_var H' x n (present c)).
Proof.
  induction eqs as [|eq]; [inversion 3|].
  intros Hs Hsh x n c Hdef Hsv.
  apply Forall_cons2 in Hs; destruct Hs as [Hseq Hseqs];
  apply Forall_cons2 in Hsh; destruct Hsh as [Hsheq Hsheqs];
  apply Is_defined_in_cons in Hdef; destruct Hdef as [Hdef|Hdef];
  [ | destruct Hdef as [Hndef Hdef];
      apply (IHeqs Hseqs Hsheqs _ _ _ Hdef Hsv) ].
  destruct eq as [| |y v0 lae]; inversion Hdef; subst;
  inversion_clear Hsheq as [? ? HH|? ? ? HH|? ? ? ys Hys HH];
  apply HH; try apply Hsv.

  inversion_clear Hseq as [| |? xs ? ? Hxs Hfby].
  rewrite sem_laexp_repr in Hxs.
  assert (forall n, xs n = ys n) as Hxsys by
        (intro n0;
         specialize Hys with n0;
         specialize Hxs with n0 (xs n0);
         apply sem_laexp_det with H n0 lae;
         (apply Hxs; reflexivity) || apply Hys).
  apply Hfby in Hsv.
  rewrite <- (holdR_ext _ _ Hxsys).
  apply fbyR_holdR with (1:=Hsv).
Qed.

Section StreamGenerators.

  Variable H: history.
  Variable arbitrary : stream.

  Definition const_eqb (c1: const) (c2: const) : bool :=
    match (c1, c2) with
    | (Cint z1, Cint z2) => BinInt.Z.eqb z1 z2
    | (Cbool b1, Cbool b2) => Bool.eqb b1 b2
    | _ => false
    end.

  Definition value_eqb (v1: value) (v2: value) : bool :=
    match (v1, v2) with
    | (present c1, present c2) => const_eqb c1 c2
    | (absent, absent) => true
    | _ => false
    end.

  Fixpoint str_clock (ck: clock) (n: nat) : bool :=
    match ck with
    | Cbase => true
    | Con ck' x c => match PM.find x H with
                     | None => false
                     | Some xs => andb (str_clock ck' n)
                                       (value_eqb (xs n) (present (Cbool c)))
                     end
    end.

  Fixpoint str_lexp (e: lexp) (n: nat) : value :=
    match e with
    | Econst c => present c
    | Evar x => match PM.find x H with
                | Some xs => xs n
                | None => absent
                end
    | Ewhen e' x c => match PM.find x H with
                      | Some xs => match xs n with
                                   | present (Cbool b) =>
                                     if Bool.eqb b c
                                     then str_laexp e' n
                                     else absent
                                   | _ => absent
                                   end
                      | None => absent
                      end
    end
  with str_laexp (e: laexp) (n: nat) : value :=
    match e with
    | LAexp ck e => if str_clock ck n then str_lexp e n else absent
    end.

  Lemma str_clock_spec:
    forall ck n c,
      sem_clock H ck n c
      -> str_clock ck n = c.
  Proof.
    induction ck.
    inversion 1; intuition.
    intros n c.
    inversion_clear 1;
      repeat progress (simpl;
         match goal with
         | H:sem_var _ _ _ _ |- _ => inversion_clear H
         | H: PM.find _ _ = _ |- _ => rewrite H
         | H: _ = present (Cbool ?b) |- _ => (rewrite H; destruct b)
         | H: sem_clock _ _ _ _ |- _ => (apply IHck in H; rewrite H)
         | H: b <> _ |- _ => (apply Bool.not_true_is_false in H
                              || apply Bool.not_false_is_true in H;
                              rewrite H)
         | _ => (cbv; reflexivity)
         end).
    destruct (PM.find i H); cbv; reflexivity.
  Qed.

  Lemma str_lexp_spec:
    forall e n v,
      sem_lexp H e n v
      -> str_lexp e n = v.
  Proof.
    induction e using lexp_mult
    with (P:=fun e => forall n v, sem_laexp H e n v -> str_laexp e n = v);
    inversion 1;
    repeat progress (simpl;
           match goal with
           | H:sem_lexp _ _ _ _ |- _ => (apply IHe in H; rewrite H)
           | H:sem_laexp _ _ _ _ |- _ => (apply IHe in H; rewrite H)
           | H:sem_clock _ _ _ _ |- _ => (apply str_clock_spec in H; rewrite H)
           | H:sem_var _ _ _ _ |- _ => (inversion_clear H as [xs Hfind Hxsn];
                                        rewrite Hfind; rewrite Hxsn)
           | |- (if Bool.eqb ?b1 ?b2 then _ else _) = _ =>
             try destruct b1; try destruct b2; simpl; intuition
           | _ => intuition
           end).
  Qed.

  Lemma str_laexp_spec:
    forall e n v,
      sem_laexp H e n v
      -> str_laexp e n = v.
  Proof.
    inversion_clear 1; simpl;
    repeat progress
           match goal with
           | H:sem_clock _ _ _ _ |- _ => (apply str_clock_spec in H; rewrite H)
           | H:sem_lexp _ _ _ _ |- _ => (apply str_lexp_spec in H; rewrite H)
           | _ => intuition
           end.
  Qed.

End StreamGenerators.

Definition hold_history (H: history) : history -> list equation -> history :=
  List.fold_right
    (fun eq H' =>
       match eq with
       | EqFby x v0 e => PM.add x (fun n=>present (hold v0 (str_laexp H e) n)) H'
       | EqApp x _ _ => H'
       | EqDef x _ => H'
       end).

(* An alternative lemma would be:
   sem_held_equations H H' (filter_dup_defs eqs) -> sem_held_equations H H' eqs
   which should hold since the H in sem_equations/sem_held_equations requires
   that multiple definitions of the same variable be coherent. But proving
   this stronger result is much harder than just assuming something that
   should anyway be true: there are no duplicate definitions in eqs.

   Note, however, that this requires a stronger definition of Is_well_sch. *)
Lemma not_in_add_to_sem_held_equations:
  forall x xs eqs H H',
    ~Is_defined_in x eqs
    -> sem_held_equations H H' eqs
    -> sem_held_equations H (PM.add x xs H') eqs.
Proof.
  induction eqs as [|eq].
  intuition (apply List.Forall_nil).
  intros H H' Hndef Hsem.
  apply not_Is_defined_in_cons in Hndef; destruct Hndef as [Hndef0 Hndef1].
  unfold sem_held_equations in Hsem.
  apply Forall_cons2 in Hsem; destruct Hsem as [Hsem0 Hsem1].
  apply (IHeqs _ _ Hndef1) in Hsem1.
  destruct eq; [ apply not_Is_defined_in_eq_EqDef in Hndef0
               | apply not_Is_defined_in_eq_EqApp in Hndef0
               | apply not_Is_defined_in_eq_EqFby in Hndef0 ];
  apply List.Forall_cons; try apply Hsem1;
  inversion_clear Hsem0 as [? ? Hsv|? ? ? Hsv|? ? ? ys Hlae Hsv];
  try constructor;
  intros;
  try (apply sem_var_gso with (1:=Hndef0); apply Hsv; assumption).
  apply SHEqFby with (1:=Hlae).
  intros; rewrite <- Hsv; split; intro HH.
  apply sem_var_gso with (1:=Hndef0) in HH; assumption.
  apply sem_var_gso with (1:=Hndef0); assumption.
Qed.


(*
   eqs = [ EqDef x y; EqFby y (Cint 0) (Econst (Cint 1)) ]
   eqs' = eqFby x (Cint 0) (Econst (Cint 1)) :: eqs

   Both eqs and eqs' have a coherent semantics (sem_equations G H _),
   but their respective hold semantics differ (for eqs', x is always present).
*)
Lemma sem_held_equations_existence:
  forall G H eqs,
    sem_equations G H eqs
    -> no_dup_defs eqs
    -> sem_held_equations H (hold_history H H eqs) eqs
       /\ (forall y n c,
              sem_var H y n (present c)
              -> sem_var (hold_history H H eqs) y n (present c)).
Proof.
  intros G H eqs Hsem Hndups.
  induction eqs as [|eq].
  - intuition constructor.
  - apply Forall_cons2 in Hsem; destruct Hsem as [Hsem Hsems].
    apply IHeqs in Hsems; [clear IHeqs
                          | inversion_clear Hndups; assumption ].
    destruct Hsems as [Hsems Hvars].
    destruct eq.

    split; [apply Forall_cons2|intuition];
    split; [constructor; apply Hvars|intuition].

    split; [apply Forall_cons2|intuition];
    split; [constructor; apply Hvars|intuition].

    split.

    (* show: sem_var -> sem_var *)
    Focus 2.
    intros y n c0 Hvar.
    pose proof (Hvars _ _ _ Hvar) as Hvar'.
    destruct (ident_eq_dec i y) as [Hiy|Hniy]; [rewrite Hiy|].
    2:(inversion_clear Hvar'; apply Sv with xs; simpl; try rewrite PM.gso; auto).
    simpl.
    eapply Sv.
    rewrite PM.gss.
    rewrite <-Some_injection.
    reflexivity.
    simpl.
    apply present_injection.
    inversion_clear Hsem.
    rewrite Hiy in *.
    apply H1 in Hvar.
    rewrite hold_injection with _ xs _ _.
    apply hold_rel.
    apply fbyR_holdR.
    exact Hvar.
    intro n0.
    rewrite sem_laexp_repr in H0.
    specialize H0 with n0 (xs n0).
    assert (sem_laexp H l n0 (xs n0)) as Hsl by (apply H0; reflexivity).
    apply str_laexp_spec in Hsl.
    exact Hsl.

    (* show sem_held_equations *)

    simpl.
    apply Forall_cons2.
    split.
    inversion_clear Hsem.
    apply SHEqFby with xs.
    apply H0.
    intros n c0.
    split.
    inversion_clear 1.
    rewrite PM.gss in H3.
    injection H3.
    intro.
    rewrite <-H2 in H4.
    injection H4.
    intro.
    apply hold_rel.
    rewrite <-H5.
    apply hold_injection.
    intro n0.
    specialize H0 with n0.
    apply str_laexp_spec in H0.
    rewrite H0.
    reflexivity.
    intro Hhold.
    apply hold_rel in Hhold.
    eapply Sv.
    rewrite PM.gss.
    rewrite <-Some_injection.
    reflexivity.
    simpl.
    apply present_injection.
    rewrite hold_injection with _ xs _ _.
    apply Hhold.
    intro n0.
    specialize H0 with n0.
    apply str_laexp_spec in H0.
    exact H0.

    apply not_in_add_to_sem_held_equations.
    inversion_clear Hndups as [|? ? Hndups'].
    apply Hndups'.
    constructor.
    apply Hsems.
Qed.

Lemma sem_held_equations_exist:
  forall G H eqs,
    sem_equations G H eqs
    -> no_dup_defs eqs
    -> exists H', sem_held_equations H H' eqs.
Proof.
  intros H H' eqs Hsems Hndups.
  apply sem_held_equations_existence in Hsems.
  destruct Hsems as [Hsems].
  now (eexists; apply Hsems).
  assumption.
Qed.


Lemma sem_held_equations_app2:
  forall H H' oeqs eqs,
    sem_held_equations H H' (oeqs ++ eqs)
    -> sem_held_equations H H' eqs.
Proof.
  intros H H' oeqs eqs H0.
  apply Forall_app in H0; intuition.
Qed.

Lemma sem_held_equations_cons:
  forall H H' eq eqs,
    sem_held_equations H H' (eq :: eqs)
    <-> sem_held_equation H H' eq /\ sem_held_equations H H' eqs.
Proof.
  split; intro Hs.
  apply Forall_cons2 in Hs; auto.
  apply Forall_cons2; auto.
Qed.
*)

