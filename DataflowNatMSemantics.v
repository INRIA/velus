Require Import List.
Import List.ListNotations.
Open Scope list_scope.

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
Definition mfind_inst x menv := PM.find x menv.(mm_instances).

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
        /\ (forall n y, xs n = absent ->
                        Is_defined_in y eqs ->
                        sem_var H y n absent)
        /\ List.Forall (msem_equation G H M) eqs) ->
      msem_node G f xs M ys.

Section msem_node_mult.
  Variable G: global.

  Variable Pn: forall (f : ident) (xs : stream) (M : memory) (ys : stream),
                 msem_node G f xs M ys -> Prop.
  Variable P: forall (H : history) (M : memory) (eq : equation),
                 msem_equation G H M eq -> Prop.

  Hypothesis EqDef_case:
    forall (H    : history)
           (M    : memory)
           (x    : ident)
           (cae  : caexp)
           (Hvar : forall n, exists v, sem_var H x n v /\ sem_caexp H cae n v),
      P H M (EqDef x cae) (SEqDef G H M x cae Hvar).

  Hypothesis EqApp_case:
    forall (H      : history)
           (M      : memory)
           (y      : ident)
           (f      : ident)
           (M'     : memory)
           (lae    : laexp)
           (ls     : stream)
           (ys     : stream)
           (Hmfind : mfind_inst y M = Some M')
           (Hls    : forall n, sem_laexp H lae n (ls n))
           (Hys    : forall n, sem_var H y n (ys n))
           (Hmsem  : msem_node G f ls M' ys),
      Pn f ls M' ys Hmsem
      -> P H M (EqApp y f lae)
               (SEqApp G H M y f M' lae ls ys Hmfind Hls Hys Hmsem).

  Hypothesis EqFby_case:
    forall (H : history)
           (M : memory)
           (ms : nat -> const)
           (y : ident)
           (ls : stream)
           (v0 : const)
           (lae : laexp)
           (Hmfind : mfind_mem y M = Some ms)
           (Hms0 : ms 0 = v0)
           (Hls : forall n, sem_laexp H lae n (ls n))
           (Hy : forall n,
               match ls n with
               | absent => ms (S n) = ms n /\ sem_var H y n absent
               | present v =>
                 ms (S n) = v /\ sem_var H y n (present (ms n))
               end),
      P H M (EqFby y v0 lae) (SEqFby G H M ms y ls v0 lae Hmfind Hms0 Hls Hy).

  Hypothesis SNode_case:
    forall (f : ident)
           (xs : stream)
           (M : memory)
           (ys : stream)
           (i  : var_dec)
           (o : var_dec)
           (eqs : list equation)
           (Hfind : find_node f G = Some (mk_node f i o eqs))
           (Hnode : exists H : history,
                 (forall n, sem_var H (v_name i) n (xs n))
              /\ (forall n, sem_var H (v_name o) n (ys n))
              /\ (forall n y,
                     xs n = absent
                     -> Is_defined_in y eqs
                     -> sem_var H y n absent)
              /\ Forall (msem_equation G H M) eqs),
      (exists H : history,
             (forall n, sem_var H (v_name i) n (xs n))
          /\ (forall n, sem_var H (v_name o) n (ys n))
          /\ (forall n y,
                 xs n = absent
                 -> Is_defined_in y eqs
                 -> sem_var H y n absent)
          /\ Forall (fun eq=>exists Hsem, P H M eq Hsem) eqs)
      -> Pn f xs M ys (SNode G f xs M ys i o eqs Hfind Hnode).

  Fixpoint msem_node_mult (f : ident)
                          (xs : stream)
                          (M : memory)
                          (ys : stream)
                          (Hn : msem_node G f xs M ys) {struct Hn}
                                                          : Pn f xs M ys Hn :=
    match Hn in (msem_node _ f xs M ys) return (Pn f xs M ys Hn) with
    | SNode f xs M ys i o eqs Hf Hnode =>
        SNode_case f xs M ys i o eqs Hf Hnode
        (* Turn: exists H : history,
                      (forall n, sem_var H (v_name i) n (xs n))
                   /\ (forall n, sem_var H (v_name o) n (ys n))
                   /\ (forall n y, xs n = absent
                                   -> Is_defined_in y eqs
                                   -> sem_var H y n absent)
                   /\ Forall (msem_equation G H M) eqs
           Into: exists H : history,
                      (forall n, sem_var H (v_name i) n (xs n))
                   /\ (forall n, sem_var H (v_name o) n (ys n))
                   /\ (forall n y, xs n = absent
                                   -> Is_defined_in y eqs
                                   -> sem_var H y n absent)
                   /\ Forall (fun eq=>exists Hsem, P H M eq Hsem) eqs *)
           (match Hnode with
            | ex_intro H (conj Hxs (conj Hys (conj Hclk Heqs))) =>
                ex_intro _ H (conj Hxs (conj Hys (conj Hclk
                  (((fix map (eqs : list equation)
                             (Heqs: Forall (msem_equation G H M) eqs) :=
                       match Heqs in Forall _ fs
                             return (Forall (fun eq=> exists Hsem,
                                                        P H M eq Hsem) fs)
                       with
                       | Forall_nil => Forall_nil _
                       | Forall_cons eq eqs Heq Heqs' =>
                         Forall_cons eq (@ex_intro _ _ Heq
                                           (msem_equation_mult H M eq Heq))
                                     (map eqs Heqs')
                       end) eqs Heqs)))))
            end)
    end

  with msem_equation_mult (H : history)
                          (M : memory)
                          (eq : equation)
                          (Heq : msem_equation G H M eq) {struct Heq}
                                                            : P H M eq Heq :=
         match Heq in (msem_equation _ H M eq) return (P H M eq Heq)
         with
         | SEqDef H M y cae Hvar => EqDef_case H M y cae Hvar
         | SEqApp H M y f M' lae ls ys Hmfind Hls Hys Hmsem =>
             EqApp_case H M y f M' lae ls ys Hmfind Hls Hys Hmsem
                        (msem_node_mult f ls M' ys Hmsem)
         | SEqFby H M ms x ls v0 lae Hmfind Hms0 Hls Hy =>
  	     EqFby_case H M ms x ls v0 lae Hmfind Hms0 Hls Hy
         end.

End msem_node_mult.


(* The clock constraint in msem_node,
     (forall n y, xs n = absent -> Is_defined_in y eqs -> sem_var H y n absent)

   is only necessary for the correctness proof of imperative code generation.
   A translated node is only executed when the clock of its input expression
   is true. For this 'optimization' to be correct, whenever the input is
   absent, the output must be absent and the internal memories must not change.
   These facts are consequences of the clock constraint above (see the
   absent_invariant lemma below).

   Such an 'assumption' introduces an obligation on clock checking. A node
   will not have an m-semantics if it violates the constraint.
 *)

Inductive Mem_unchanged (n: nat) : memory -> Prop :=
| MUn:
    forall menv,
      (forall x xs, mfind_mem x menv = Some xs
                    -> xs (S n) = xs n) ->
      (forall x omenv,
          mfind_inst x menv = Some omenv
          -> Mem_unchanged n omenv) ->
      Mem_unchanged n menv.

(*
Inductive Memory_unchanged (G: global) (n: nat) : ident -> memory -> Prop :=
| MemC:
    forall f M i o eqs,
      find_node f G = Some(mk_node f i o eqs)
      -> List.Forall (Memory_Unchanged_eq G n M) eqs
      -> Memory_unchanged G n f M menv

with Memory_Corres_eq (G: global) (n: nat) :
       memory -> memoryEnv -> equation -> Prop :=
| MemC_EqDef:
    forall M menv x cae,
      Memory_Corres_eq G n M menv (EqDef x cae)
| MemC_EqApp:
    forall M menv x f lae,
      (forall Mo omenv, mfind_inst x M = Some Mo
                        -> find_obj x menv = Some omenv
                        -> Memory_Corres G n f Mo omenv)
      -> Memory_Corres_eq G n M menv (EqApp x f lae)
| MemC_EqFby:
    forall M menv x v0 lae,
      (forall ms, mfind_mem x M = Some ms
                  -> find_mem x menv = Some (ms n))
      -> Memory_Corres_eq G n M menv (EqFby x v0 lae).
*)


Lemma absent_invariant:
  forall G f xs M ys n,
    msem_node G f xs M ys
    -> xs n = absent
    -> Mem_unchanged n M.
Proof.
  (*
  inversion_clear 1.


  intros G f xs M ys n Hmsem.
  induction Hmsem
  using msem_node_mult
  with (P := fun H M eq Heq => True).
  Show 4.
*)
Admitted.

Definition msem_nodes (G: global) : Prop :=
  List.Forall (fun no => exists xs M ys, msem_node G no.(n_name) xs M ys) G.

Lemma msem_node_cons:
  forall node G f xs M ys,
    Ordered_nodes (node::G)
    -> msem_node (node :: G) f xs M ys
    -> node.(n_name) <> f
    -> msem_node G f xs M ys.
Proof.
  intros node G f xs M ys Hord Hsem Hnf.
  revert Hnf.
  induction Hsem as [|H M y f M' lae ls ys Hmfind Hls Hys Hmsem IH| |
                      f xs M ys i o eqs Hf Heqs IH]
  using msem_node_mult
  with (P := fun H M eq Hsem => ~Is_node_in_eq node.(n_name) eq
                                -> msem_equation G H M eq).
  - constructor; intuition.
  - intro Hnin.
    eapply SEqApp with (1:=Hmfind) (2:=Hls) (3:=Hys).
    apply IH. intro Hnf. apply Hnin. rewrite Hnf. constructor.
  - intro; eapply SEqFby with (1:=Hmfind) (2:=Hms0) (3:=Hls) (4:=Hy).
  - intro.
    rewrite find_node_tl with (1:=Hnf) in Hf.
    apply SNode with (1:=Hf).
    clear Heqs.
    destruct IH as [H [Hxs [Hys [Habs Heqs]]]].
    exists H.
    split; [exact Hxs|].
    split; [exact Hys|].
    split; [exact Habs|].
    apply find_node_later_not_Is_node_in with (2:=Hf) in Hord.
    apply Is_node_in_Forall in Hord.
    apply Forall_Forall with (1:=Hord) in Heqs.
    apply Forall_impl with (2:=Heqs).
    destruct 1 as [Hnini [Hsem HH]].
    intuition.
Qed.

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

(* TODO: Tidy this up... *)
Lemma Forall_msem_equation_global_tl:
  forall nd G H M eqs,
    Ordered_nodes (nd::G)
    -> (forall f, Is_node_in f eqs -> find_node f G <> None)
    -> ~ Is_node_in nd.(n_name) eqs
    -> List.Forall (msem_equation (nd::G) H M) eqs
    -> List.Forall (msem_equation G H M) eqs.
Proof.
  intros nd G H M eqs Hord.
  induction eqs as [|eq eqs IH]; [trivial|].
  intros Hfind Hnini Hmsem.
  apply Forall_cons2 in Hmsem; destruct Hmsem as [Hseq Hseqs].
  apply IH in Hseqs.
  Focus 2.
  { intros f Hini.
    apply List.Exists_cons_tl with (x:=eq) in Hini.
    now apply Hfind with (1:=Hini). }
  Unfocus.
  Focus 2.
  { apply not_Is_node_in_cons in Hnini.
    destruct Hnini; assumption. }
  Unfocus.

  apply List.Forall_cons with (2:=Hseqs).
  inversion Hseq as [|? ? ? ? ? ? Hmfind Hmsem|]; subst.
  - constructor; auto.
  - apply not_Is_node_in_cons in Hnini.
    destruct Hnini.
    assert (nd.(n_name) <> f).
    intro HH.
    apply H0.
    rewrite HH.
    constructor.
    inversion_clear Hseq.
    econstructor.
    eexact H8.
    eexact H9.
    eexact H10.
    apply msem_node_cons with (1:=Hord); assumption.
  - econstructor.
    eassumption.
    reflexivity.
    eassumption.
    assumption.
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

 *)

Section StreamExecution.

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

End StreamExecution.

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
    sem_node G f xs ys -> (exists ms, msem_node G f xs ms ys).
Admitted.
(*
Proof.
  intros G f xs ys Hsem.
  induction G as [|node G IH];
    [ inversion Hsem as [? ? ? ? ? ? Hfind]; now inversion Hfind |].
  inversion_clear Hsem as [? ? ? ? ? ? Hfind HH].
  destruct HH as [H [Hxs [Hys Heqs]]].
  eexists.
  econstructor.
  eapply Hfind.
  exists H.
  split; [exact Hxs|].
  split; [exact Hys|].
  split; [admit|]. (* TODO: need to incorporate assumption on clocks *)
  SearchAbout msem_equation.
  induction eqs.


  eexists.
  econstructor.
  SearchAbout find_node.
  admit.
Qed.
*)

(*
Lemma Forall_msem_equation_global_tl:
  forall nd G H M eqs,
    Ordered_nodes (nd::G)
    -> (forall f, Is_node_in f eqs -> find_node f G <> None)
    -> ~ Is_node_in nd.(n_name) eqs
    -> List.Forall (msem_equation (nd::G) H M) eqs
    -> List.Forall (msem_equation G H M) eqs.
*)


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
(*
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
 *)

