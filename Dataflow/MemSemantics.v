Require Import Rustre.Nelist.
Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Coq.FSets.FMapPositive.
Require Import Rustre.Common.
Require Import Rustre.Heap.
Require Import Rustre.Dataflow.Stream.
Require Import Rustre.Dataflow.Syntax.
Require Import Rustre.Dataflow.IsVariable.
Require Import Rustre.Dataflow.IsDefined.
Require Import Rustre.Dataflow.Semantics.
Require Import Rustre.Dataflow.Ordered.
Require Import Rustre.Dataflow.WellFormed.

Set Implicit Arguments.

(**

  We provide a "non-standard" dataflow semantics where the state
  introduced by an [fby] is kept in a separate [heap] of streams.

 *)


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

Definition memory := memory (stream const).

Implicit Type M : memory.

Inductive msem_equation G: history -> memory -> equation -> Prop :=
| SEqDef:
    forall H M x ck xs ce,
      sem_var H x xs ->
      sem_caexp H ck ce xs ->
      msem_equation G H M (EqDef x ck ce)
| SEqApp:
    forall H M x ck f M' arg ls xs,
      mfind_inst x M = Some M' ->
      sem_laexps H ck arg ls ->
      sem_var H x xs ->
      msem_node G f ls M' xs ->
      msem_equation G H M (EqApp x ck f arg)
(* =msem_equation:fby= *)
| SEqFby: forall H M ms x ck ls xs v0 le,
    mfind_mem x M = Some ms ->
    ms 0 = v0 ->
    sem_laexp H ck le ls ->
    sem_var H x xs ->
    (forall n, match ls n with
          | absent    => ms (S n) = ms n /\ xs n = absent
          | present v => ms (S n) = v    /\ xs n = present (ms n)
          end) ->
    msem_equation G H M (EqFby x ck v0 le)
(* =end= *)

with msem_node G: ident -> stream (nelist value) -> memory -> stream value -> Prop :=
| SNode:
    forall f xss M ys i o eqs,
      find_node f G = Some (mk_node f i o eqs) ->
      (exists H,
         sem_vars H i xss
        /\ sem_var H o ys
        /\ (forall n, absent_list xss n ->
                      Forall (rhs_absent_instant (restr H n)) eqs)
        /\ (forall n, absent_list xss n <-> ys n = absent)
        /\ Forall (msem_equation G H M) eqs) ->
      msem_node G f xss M ys.

Definition msem_equations G H M eqs := List.Forall (msem_equation G H M) eqs.

Section msem_node_mult.
  Variable G: global.

  Variable Pn: forall (f : ident) xss (M : memory) (ys : stream value),
                 msem_node G f xss M ys -> Prop.
  Variable P: forall (H : history) (M : memory) (eq : equation),
                 msem_equation G H M eq -> Prop.

  Hypothesis EqDef_case:
    forall (H    : history)
           (M    : memory)
           (x    : ident)
           (ck   : clock)
           (xs   : stream value)
           (ce   : cexp)
           (Hvar : sem_var H x xs)
           (Hexp : sem_caexp H ck ce xs),
      P (SEqDef G M Hvar Hexp).

  Hypothesis EqApp_case:
    forall (H      : history)
           (M      : memory)
           (y      : ident)
           (ck   : clock)
           (f      : ident)
           (M'     : memory)
           (les    : nelist lexp)
           (ls     : stream (nelist value))
           (ys     : stream value)
           (Hmfind : mfind_inst y M = Some M')
           (Hls    : sem_laexps H ck les ls)
           (Hys    : sem_var H y ys)
           (Hmsem  : msem_node G f ls M' ys),
      Pn Hmsem
      -> P (SEqApp M Hmfind Hls Hys Hmsem).

  Hypothesis EqFby_case:
    forall (H      : history)
           (M      : memory)
           (ms     : stream const)
           (y      : ident)
           (ck     : clock)
           (ls     : stream value)
           (yS     : stream value)
           (v0     : const)
           (le     : lexp)
           (Hmfind : mfind_mem y M = Some ms)
           (Hms0 : ms 0 = v0)
           (Hls : sem_laexp H ck le ls)
           (HyS : sem_var H y yS)
           (Hy : forall n,
               match ls n with
               | absent => ms (S n) = ms n /\ yS n = absent
               | present v =>
                 ms (S n) = v /\ yS n = (present (ms n))
               end),
      P (SEqFby G M Hmfind Hms0 Hls HyS Hy).

  Hypothesis SNode_case:
    forall (f : ident)
           (xss : stream (nelist value))
           (M : memory)
           (ys : stream value)
           (i  : nelist ident)
           (o : ident)
           (eqs : list equation)
           (Hfind : find_node f G = Some (mk_node f i o eqs))
           (Hnode : exists H : history,
                 sem_vars H i xss
              /\ sem_var H o ys
              /\ (forall n, absent_list xss n ->
                            Forall (rhs_absent_instant (restr H n)) eqs)
              /\ (forall n, absent_list xss n <-> ys n = absent)
              /\ Forall (msem_equation G H M) eqs),
      (exists H : history,
             sem_vars H i xss
          /\ sem_var H o ys
          /\ (forall n, absent_list xss n ->
                        Forall (rhs_absent_instant (restr H n)) eqs)
          /\ (forall n, absent_list xss n <-> ys n = absent)
          /\ Forall (fun eq=>exists Hsem, P (eq := eq)(M := M)(H := H) Hsem) eqs)
      -> Pn  (SNode Hfind Hnode).

  Fixpoint msem_node_mult (f : ident)
                          (xss : stream (nelist value))
                          (M : memory)
                          (ys : stream value)
                          (Hn : msem_node G f xss M ys) {struct Hn}
                                                          : Pn Hn :=
    match Hn in (msem_node _ f xs M ys) return (Pn Hn) with
    | SNode f xs M ys i o eqs Hf Hnode =>
        SNode_case Hf Hnode
        (* Turn: exists H : history,
                      (forall n, sem_var H (v_name i) n (xs n))
                   /\ (forall n, sem_var H (v_name o) n (ys n))
                   /\ (forall n, xs n = absent
                                 -> Forall (rhs_absent H n) eqs)
                   /\ (forall n, xs n = absent <-> ys n = absent)
                   /\ Forall (msem_equation G H M) eqs
           Into: exists H : history,
                      (forall n, sem_var H (v_name i) n (xs n))
                   /\ (forall n, sem_var H (v_name o) n (ys n))
                   /\ (forall n, xs n = absent
                                 -> Forall (rhs_absent H n) eqs)
                   /\ (forall n, xs n = absent <-> ys n = absent)
                   /\ Forall (fun eq=>exists Hsem, P H M eq Hsem) eqs *)
           (match Hnode with
            | ex_intro H (conj Hxs (conj Hys (conj Hclk (conj Hout Heqs)))) =>
                ex_intro _ H (conj Hxs (conj Hys (conj Hclk (conj Hout
                  (((fix map (eqs : list equation)
                             (Heqs: Forall (msem_equation G H M) eqs) :=
                       match Heqs in Forall _ fs
                             return (Forall (fun eq=> exists Hsem,
                                                        P Hsem) fs)
                       with
                       | Forall_nil => Forall_nil _
                       | Forall_cons eq eqs Heq Heqs' =>
                         Forall_cons eq (@ex_intro _ _ Heq
                                           (msem_equation_mult Heq))
                                     (map eqs Heqs')
                       end) eqs Heqs))))))
            end)
    end

  with msem_equation_mult (H : history)
                          (M : memory)
                          (eq : equation)
                          (Heq : msem_equation G H M eq) {struct Heq}
                                                            : P Heq :=
         match Heq in (msem_equation _ H M eq) return (P Heq)
         with
         | SEqDef H M y ck xs cae Hvar Hexp => EqDef_case M Hvar Hexp
         | SEqApp H M y ck f M' lae ls ys Hmfind Hls Hys Hmsem =>
             EqApp_case M Hmfind Hls Hys                         (msem_node_mult Hmsem)
         | SEqFby H M ms x ck ls yS v0 lae Hmfind Hms0 Hls hyS Hy =>
  	     EqFby_case M Hmfind Hms0 Hls hyS Hy
         end.

End msem_node_mult.

Definition msem_nodes (G: global) : Prop :=
  Forall (fun no => exists xs M ys, msem_node G no.(n_name) xs M ys) G.

(* Lionel: As these two lemmas are not used, I simply commented them out.
Lemma rhs_absent_lhs_node:
  forall G f xss M ys n,
       Welldef_global G
    -> msem_node G f xss M ys
    -> absent_list xss n
    -> ys n = absent.
Proof.
  intros G f xs M ys n Hwdef Hsem.
  induction Hsem as [| H M y ck f M' le ls ys Hmfind Hls Hys Hmsem IH |
                     | f xs M ys i o eqs Hf Heqs IH]
  using msem_node_mult
  with (P := fun H M eq Hsem =>
               forall x, rhs_absent_instant (restr H n) eq
                         -> msem_equation G H M eq
                         -> Is_defined_in_eq x eq
                         -> sem_var_instant (restr H n) x absent).
  - intros y Habs Hmsem Hidi.
    inversion_clear Hidi.
    inversion_clear Habs as [? ? Hcae| |].
    specialize (Hvar n); specialize (Hexp n); simpl in *.
    assert (Habs: xs n = absent) by sem_det.
    rewrite Habs in *.
    assumption.
  - intros x Habs Hseq Hidi.
    inversion_clear Hidi.
    inversion_clear Habs as [|? ? ? ? ? Hle Hvs|].
    assert (Nelist.map (fun f => f n) ls = vs).
    { assert (Hlen : Nelist.length ls = Nelist.length vs).
      { transitivity (Nelist.length le); [symmetry |]; eapply Nelist.Forall2_length; eassumption. }
      induction vs as [v | v vs]; destruct ls as [l1 | l1 ls]; simpl.
      + 
      
    Print absent_list. 
    specialize (Hls n); specialize (Hys n); simpl in *.
    assert (Hle_abs: ls n = vs) by sem_det.
    rewrite Hle_abs in *.
    assert (absent_list ls n) by (unfold absent_list; congruence).
    rewrite IH in *; eauto.
  - intros x Habs Hsem Hidi.
    inversion_clear Hidi.
    inversion_clear Habs as [| |? ? ? Hlae].
    specialize (Hls n); simpl in *.
    assert (Hls_abs: ls n = absent) by sem_det.
    specialize Hy with n.
    rewrite Hls_abs in *.
    destruct Hy as [Hy0 Hy1].
    specialize (HyS n); simpl in HyS. rewrite Hy1 in HyS. 
    auto.
  - apply Welldef_global_output_Is_variable_in with (2:=Hf) in Hwdef.
    simpl in Hwdef.
    apply Is_variable_in_Is_defined_in in Hwdef.
    intro Habsx.
    clear Heqs.
    destruct IH as [H [Hxs [Hys [Habs [Hout Heqs]]]]].
    specialize (Hxs n).
    specialize (Hys n).
    apply Habs in Habsx.
    clear Hf Habs.
    induction eqs as [|eq eqs IHeqs]; [now inversion Hwdef|].
    apply Is_defined_in_cons in Hwdef.
    apply Forall_cons2 in Heqs.
    destruct Heqs as [Heqs0 Heqs1].
    apply Forall_cons2 in Habsx.
    destruct Habsx as [Habsx0 Habsx1].
    destruct Hwdef as [Hin|[Hnin0 Hnin1]];
      [clear IHeqs Heqs1|now apply IHeqs with (1:=Hnin1) (2:=Heqs1) (3:=Habsx1)].
    destruct Heqs0 as [Hmsem Heqs].
    apply Heqs with (1:=Habsx0) (2:=Hmsem) in Hin.
    simpl in *.
    sem_det.
Qed.


Lemma rhs_absent_lhs:
  forall G H M n x neqs,
    Welldef_global G
    -> Forall (rhs_absent_instant (restr H n)) neqs
    -> Forall (msem_equation G H M) neqs
    -> Is_defined_in x neqs
    -> sem_var_instant (restr H n) x absent.
Proof.
  intros G H M n x neqs Hwdef.
  induction neqs as [|eq eqs IH]; [now inversion 2|].
  intros Hrhs Hsem Hidi.
  apply Is_defined_in_cons in Hidi.
  apply Forall_cons2 in Hsem.
  destruct Hsem as [Hsem0 Hsem1].
  apply Forall_cons2 in Hrhs.
  destruct Hrhs as [Hrhs0 Hrhs1].
  destruct Hidi as [Hidi|Hidi].
  - destruct eq;
    inversion_clear Hrhs0 as [? ? Habs|? ? ? ? Habs|? ? ? ? Habs];
    inversion_clear Hsem0 as [? ? ? ? ? Hvar Hcae
                             |? ? ? ? ? ? ? ? Hmfind Hlae Hvar Hsem
                             |? ? ? ? ? ? ? ? Hmfind Hms0 Hlae Hvar];
    inversion_clear Hidi.
    + specialize (Hcae n); specialize (Hvar n); simpl in *.
      assert (Hxs_abs: xs n = absent) by sem_det.
      congruence.
    + specialize (Hlae n); specialize (Hvar n); simpl in *.
      assert (Hv_abs: ls n = vs) by sem_det.
      assert (absent_list ls n) by (unfold absent_list; congruence).
      assert (Hxs_abs: xs n = absent) by (eapply rhs_absent_lhs_node; eauto).
      congruence.
    + specialize (Hlae n); specialize (Hvar n); simpl in *.
      assert (Hls_abs: ls n = absent) by sem_det.
      specialize H2 with n.
      rewrite Hls_abs in H2; simpl in Hvar.
      destruct H2. rewrite H2 in Hvar.
      auto.
  - destruct Hidi as [Hnidi Hidi].
    now apply IH with (1:=Hrhs1) (2:=Hsem1) (3:=Hidi).
Qed.
*)

(* Instead of repeating all these cons lemmas (i.e., copying and pasting them),
   and dealing with similar obligations multiple times in translation_correct,
   maybe it would be better to bake Ordered_nodes into msem_node and to make
   it like Miniimp, i.e.,
      find_node f G = Some (nd, G') and msem_node G' nd xs ys ?
   TODO: try this when the other elements are stabilised. *)

Lemma msem_node_cons:
  forall node G f xs M ys,
    Ordered_nodes (node::G)
    -> msem_node (node :: G) f xs M ys
    -> node.(n_name) <> f
    -> msem_node G f xs M ys.
Proof.
  intros node G f xs M ys Hord Hsem Hnf.
  revert Hnf.
  induction Hsem as [|H M y ck f M' les ls ys Hmfind Hls Hys Hmsem IH| |
                      f xs M ys i o eqs Hf Heqs IH]
  using msem_node_mult
  with (P := fun H M eq Hsem => ~Is_node_in_eq node.(n_name) eq
                                -> msem_equation G H M eq).
  - econstructor; eauto.
  - intro Hnin.
    eapply SEqApp with (1:=Hmfind) (2:=Hls) (3:=Hys).
    apply IH. intro Hnf. apply Hnin. rewrite Hnf. constructor.
  - intro; eapply SEqFby; eassumption.
  - intro.
    rewrite find_node_tl with (1:=Hnf) in Hf.
    apply SNode with (1:=Hf).
    clear Heqs.
    destruct IH as [H [Hxs [Hys [Habs [Hout Heqs]]]]].
    exists H.
    split; [exact Hxs|].
    split; [exact Hys|].
    split; [exact Habs|].
    split; [exact Hout|].
    apply find_node_later_not_Is_node_in with (2:=Hf) in Hord.
    apply Is_node_in_Forall in Hord.
    apply Forall_Forall with (1:=Hord) in Heqs.
    apply Forall_impl with (2:=Heqs).
    destruct 1 as [Hnini [Hsem HH]].
    intuition.
Qed.

Lemma msem_node_cons2:
  forall nd G f xs M ys,
    Ordered_nodes G
    -> msem_node G f xs M ys
    -> Forall (fun nd' : node => n_name nd <> n_name nd') G
    -> msem_node (nd::G) f xs M ys.
Proof.
  Hint Constructors msem_equation.
  intros nd G f xs M ys Hord Hsem Hnin.
  assert (Hnin':=Hnin).
  revert Hnin'.
  induction Hsem as [|H M y f M' lae ls ys Hmfind Hls Hys Hmsem IH| |
                      f xs M ys i o eqs Hfind Heqs IH]
  using msem_node_mult
  with (P := fun H M eq Hsem => ~Is_node_in_eq nd.(n_name) eq
                                -> msem_equation (nd::G) H M eq);
    try eauto; intro HH.
  clear HH.
  assert (nd.(n_name) <> f) as Hnf.
  { intro Hnf.
    rewrite Hnf in *.
    apply find_node_split in Hfind.
    destruct Hfind as [bG [aG Hge]].
    rewrite Hge in Hnin.
    apply Forall_app in Hnin.
    destruct Hnin as [H0 Hfg]; clear H0.
    inversion_clear Hfg.
    match goal with H:f<>_ |- False => apply H end.
    reflexivity. }
  apply find_node_other with (2:=Hfind) in Hnf.
  econstructor; [exact Hnf|clear Hnf].
  clear Heqs.
  destruct IH as [H [Hxs [Hys [Habs [Hout Heqs]]]]].
  exists H.
  intuition; clear Hxs Hys.
  assert (forall g, Is_node_in g eqs
                    -> Exists (fun nd=> g = nd.(n_name)) G)
    as Hniex
    by (intros g Hini;
        apply find_node_find_again with (1:=Hord) (2:=Hfind) in Hini;
        exact Hini).
  assert (Forall
            (fun eq=> forall g,
                 Is_node_in_eq g eq
                 -> Exists (fun nd=> g = nd.(n_name)) G) eqs) as HH.
  {
    clear Hfind Heqs Habs.
    induction eqs as [|eq eqs IH]; [now constructor|].
    constructor.
    - intros g Hini.
      apply Hniex.
      constructor 1; apply Hini.
    - apply IH.
      intros g Hini; apply Hniex.
      constructor 2; apply Hini.
  }
  apply Forall_Forall with (1:=HH) in Heqs.
  apply Forall_impl with (2:=Heqs).
  intros eq IH.
  destruct IH as [Hsem [IH0 IH1]].
  apply IH1.
  intro Hini.
  apply Hsem in Hini.
  apply Forall_Exists with (1:=Hnin) in Hini.
  apply Exists_exists in Hini.
  destruct Hini as [nd' [Hin [Hneq Heq]]].
  intuition.
Qed.

Lemma msem_equation_cons2:
  forall G H M eqs nd,
    Ordered_nodes (nd::G)
    -> Forall (msem_equation G H M) eqs
    -> ~Is_node_in nd.(n_name) eqs
    -> Forall (msem_equation (nd::G) H M) eqs.
Proof.
  Hint Constructors msem_equation.
  intros G H M eqs nd Hord Hsem Hnini.
  induction eqs as [|eq eqs IH]; [now constructor|].
  apply Forall_cons2 in Hsem.
  destruct Hsem as [Heq Heqs].
  apply not_Is_node_in_cons in Hnini.
  destruct Hnini as [Hnini Hninis].
  apply IH with (2:=Hninis) in Heqs.
  constructor; [|now apply Heqs].
  destruct Heq as [|? ? ? ? ? ? ? ? ? Hmfind Hls Hxs Hmsem|]; try now eauto.
  econstructor.
  - exact Hmfind.
  - exact Hls.
  - exact Hxs.
  - inversion_clear Hord as [|? ? Hord' Hnn Hnns].
    apply msem_node_cons2 with (1:=Hord') (3:=Hnns).
    apply Hmsem.
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
  rewrite Forall_forall in Hnds.
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
    -> Forall (msem_equation (nd::G) H M) eqs
    -> Forall (msem_equation G H M) eqs.
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

  apply Forall_cons with (2:=Hseqs).
  inversion Hseq as [|? ? ? ? ? ? Hmfind Hmsem|]; subst.
  - econstructor; eauto.
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
  - econstructor; eassumption || reflexivity.
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
  Forall (sem_held_equation H H') eqs.

 *)

Lemma msem_equation_madd_mem:
  forall G H M x ms eqs,
    ~Is_defined_in x eqs
    -> Forall (msem_equation G H M) eqs
    -> Forall (msem_equation G H (madd_mem x ms M)) eqs.
Proof.
  Hint Constructors msem_equation.
  intros G H M x ms eqs Hnd Hsem.
  induction eqs as [|eq eqs IH]; [now constructor|].
  apply not_Is_defined_in_cons in Hnd.
  destruct Hnd as [Hnd Hnds].
  apply Forall_cons2 in Hsem.
  destruct Hsem as [Hsem Hsems].
  constructor; [|now apply IH with (1:=Hnds) (2:=Hsems)].
  destruct Hsem as [| |? ? ? ? ? ? ? ? ? Hmfind Hms0 Hlae Hvar]; try now eauto.
  apply not_Is_defined_in_eq_EqFby in Hnd.
  eapply SEqFby; try eassumption.
  apply not_eq_sym in Hnd.
  rewrite mfind_mem_gso with (1:=Hnd).
  exact Hmfind.
Qed.

Lemma msem_equation_madd_obj:
  forall G H M M' x eqs,
    ~Is_defined_in x eqs
    -> Forall (msem_equation G H M) eqs
    -> Forall (msem_equation G H (madd_obj x M' M)) eqs.
Proof.
  Hint Constructors msem_equation.
  intros G H M M' x eqs Hnd Hsem.
  induction eqs as [|eq eqs IH]; [now constructor|].
  apply not_Is_defined_in_cons in Hnd.
  destruct Hnd as [Hnd Hnds].
  apply Forall_cons2 in Hsem.
  destruct Hsem as [Hsem Hsems].
  constructor; [|now apply IH with (1:=Hnds) (2:=Hsems)].
  destruct Hsem as [|? ? ? ? ? ? ? ? ? Hmfind Hls Hxs Hmsem|]; try now eauto.
  apply not_Is_defined_in_eq_EqApp in Hnd.
  econstructor.
  - apply not_eq_sym in Hnd.
    erewrite mfind_inst_gso with (1:=Hnd).
    exact Hmfind.
  - exact Hls.
  - exact Hxs.
  - exact Hmsem.
Qed.

(*
   - The no_dup_defs hypothesis is essential for the EqApp case.

     If the set of equations contains two EqApp's to the same variable:
        eq::eqs = [ EqApp x f lae; ...; EqApp x g lae' ]

     Then it is possible to have a coherent H, namely if
        f(lae) = g(lae')

     But nothing forces the 'memory streams' (internal memories) of
     f(lae) and g(lae') to be the same. This is problematic since they are
     both 'stored' at M x...

   - The no_dup_defs hypothesis is not essential for the EqFby case.

     If the set of equations contains two EqFby's to for the same variable:
        eq::eqs = [ EqFby x v0 lae; ...; EqFby x v0' lae'; ... ]

     then the 'memory streams' associated with each, ms and ms', must be
     identical since if (Forall (sem_equation G H) (eq::eqs)) exists then
     then the H forces the coherence between 'both' x's, and necessarily also
     between v0 and v0', and lae and lae'.

     That said, proving this result is harder than just assuming something
     that should be true anyway: that there are no duplicate definitions in
     eqs.

   Note that the no_dup_defs hypothesis requires a stronger definition of
   either Is_well_sch or Welldef_global.
*)
Lemma sem_msem_eq:
  forall G H eqs M eq mems argIn,
    (forall f xs ys, sem_node G f xs ys
                     -> exists M : memory, msem_node G f xs M ys)
    -> sem_equation G H eq
    -> Is_well_sch mems argIn (eq::eqs)
    -> Forall (msem_equation G H M) eqs
    -> exists M', Forall (msem_equation G H M') (eq::eqs).
Proof.
  intros G H eqs M eq mems argIn IH Heq Hwsch Hmeqs.
  inversion Heq as [? ? ? ? ? Hsem
                   |? ? ? ? ? ? ? Hls Hxs Hsem
                   |? ? ? ? ? ? ? Hle Hvar];
    match goal with H:_=eq |- _ => rewrite <-H in * end.
  - exists M.
    constructor ((econstructor; eassumption) || assumption).
  - apply IH in Hsem.
    destruct Hsem as [M' Hmsem].
    exists (madd_obj x M' M).
    constructor.
    econstructor.
    + now apply mfind_inst_gss.
    + exact Hls.
    + exact Hxs.
    + exact Hmsem.
    + inversion_clear Hwsch as [| |? ? ? ? ? ? ? Hnii|].
      eauto using msem_equation_madd_obj. 
  - exists (madd_mem x (hold v0 ls) M).
    constructor.
    econstructor.
    + now apply mfind_mem_gss.
    + reflexivity.
    + exact Hle.
    + intros n.
      specialize (Hvar n); simpl in Hvar.
      eassumption.
    + intro n.
      destruct (ls n) eqn:Hls.
      * split; [simpl; rewrite Hls; reflexivity|].
        rewrite H1. unfold fby. rewrite Hls; auto.
      * split; [simpl; rewrite Hls; reflexivity|].
        rewrite H1. unfold fby. rewrite Hls; auto.
    + inversion_clear Hwsch as [| | |? ? ? ? ? ? ? ? Hnmi].
      apply msem_equation_madd_mem.
      apply Hnmi.
      now apply Hmeqs.
Qed.


Lemma sem_msem_eqs:
  forall G H eqs mems argIn,
    (forall f xs ys, sem_node G f xs ys
                     -> exists M : memory, msem_node G f xs M ys)
    -> Is_well_sch mems argIn eqs
    -> Forall (sem_equation G H) eqs
    -> exists M', Forall (msem_equation G H M') eqs.
Proof.
  intros G H eqs mems argIn IH Hwsch Heqs.
  induction eqs as [|eq eqs IHeqs]; [exists (empty_memory _); now constructor|].
  apply Forall_cons2 in Heqs.
  destruct Heqs as [Heq Heqs].
  apply IHeqs with (1:=Is_well_sch_cons _ _ _ _ Hwsch) in Heqs.
  destruct Heqs as [M Heqs].
  now apply sem_msem_eq with (1:=IH) (2:=Heq) (3:=Hwsch) (4:=Heqs).
Qed.

Lemma sem_msem_node:
  forall G f xs ys,
    Welldef_global G
    -> sem_node G f xs ys
    -> (exists M, msem_node G f xs M ys).
Proof.
  induction G as [|node].
  inversion 2;
    match goal with Hf: find_node _ [] = _ |- _ => inversion Hf end.
  intros f xs ys Hwdef Hsem.
  assert (Hsem' := Hsem).
  inversion_clear Hsem' as [? ? ? ? ? ? Hfind HH].
  destruct HH as [H [Hxs [Hys [Habs [Hout Heqs]]]]].
  pose proof (Welldef_global_Ordered_nodes _ Hwdef) as Hord.
  pose proof (Welldef_global_cons _ _ Hwdef) as HwdefG.
  pose proof (find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
  simpl in Hnini.
  simpl in Hfind.
  destruct (ident_eqb node.(n_name) f) eqn:Hnf.
  - assert (Hord':=Hord).
    inversion_clear Hord as [|? ? Hord'' Hnneqs Hnn].
    injection Hfind; intro HR; rewrite HR in *; clear HR; simpl in *.
    apply Forall_sem_equation_global_tl with (1:=Hord') (2:=Hnini) in Heqs.
    assert (forall f xs ys,
               sem_node G f xs ys
               -> exists M, msem_node G f xs M ys) as IHG'
        by auto.
    inversion_clear Hwdef as [|? ? ? Hw0 neqs ? ? Hwsch Hw2 Hw3 Hw4 Hw5 Hw6].
    simpl in neqs; unfold neqs in *.
    pose proof (sem_msem_eqs IHG' Hwsch Heqs) as HH.
    destruct HH as [M Hmsem].
    exists M.
    econstructor;
      [simpl; rewrite ident_eqb_refl; reflexivity|].
    exists H.
    split; [exact Hxs|].
    split; [exact Hys|].
    split; [exact Habs|].
    split; [exact Hout|].
    apply msem_equation_cons2 with (1:=Hord') (2:=Hmsem) (3:=Hnini).
  - apply ident_eqb_neq in Hnf.
    apply sem_node_cons with (1:=Hord) (3:=Hnf) in Hsem.
    inversion_clear Hord as [|? ? Hord' H0 Hnig].
    apply IHG with (1:=HwdefG) in Hsem.
    destruct Hsem as [M Hsem].
    exists M.
    apply msem_node_cons2 with (1:=Hord') (3:=Hnig).
    exact Hsem.
Qed.
