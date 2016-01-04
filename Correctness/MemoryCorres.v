Require Import List.

Require Import Rustre.Common.
Require Import Rustre.Heap.
Require Import Rustre.Dataflow.
Require Import Rustre.Minimp.Syntax.
Require Import Rustre.Minimp.Semantics.
Require Import Rustre.Translation.

(**

  [Memory_Corres] relates a dataflow [memory] with an object [heap] at
  an instant [n]. Morally, we are saying that taking a snapshot of the
  memory at time [n] gives [heap].

 *)

Inductive Memory_Corres (G: global) (n: nat) :
       ident -> memory -> heap -> Prop :=
| MemC:
    forall f M menv i o eqs,
      find_node f G = Some(mk_node f i o eqs)
      -> List.Forall (Memory_Corres_eq G n M menv) eqs
      -> Memory_Corres G n f M menv

with Memory_Corres_eq (G: global) (n: nat) :
       memory -> heap -> equation -> Prop :=
| MemC_EqDef:
    forall M menv x cae,
      Memory_Corres_eq G n M menv (EqDef x cae)
| MemC_EqApp:
    forall M menv x f lae,
      (forall Mo, mfind_inst x M = Some Mo
                  -> (exists omenv,
                         mfind_inst x menv = Some omenv
                         /\ Memory_Corres G n f Mo omenv))
      -> Memory_Corres_eq G n M menv (EqApp x f lae)
| MemC_EqFby:
    forall M menv x v0 lae,
      (forall ms, mfind_mem x M = Some ms
                  -> mfind_mem x menv = Some (ms n))
      -> Memory_Corres_eq G n M menv (EqFby x v0 lae).

Section Memory_Corres_mult.
  Variables (G: global) (n: nat).

  Variable P : ident -> memory -> heap -> Prop.
  Variable Peq : memory -> heap -> equation -> Prop.

  Hypothesis EqDef_case: forall M menv x cae,
      Peq M menv (EqDef x cae).

  Hypothesis EqApp_case: forall M menv x f lae,
      (forall Mo (Hmfind: mfind_inst x M = Some Mo),
          (exists omenv, mfind_inst x menv = Some omenv /\ P f Mo omenv))
      -> Peq M menv (EqApp x f lae).

  Hypothesis EqFby_case: forall M menv x v0 lae,
      (forall ms, mfind_mem x M = Some ms
                  -> mfind_mem x menv = Some (ms n))
      -> Peq M menv (EqFby x v0 lae).

  Hypothesis MemC_case:
    forall f M menv i o eqs
           (Hfind : find_node f G = Some (mk_node f i o eqs)),
      Forall (Peq M menv) eqs
      -> P f M menv.

  Fixpoint Memory_Corres_mult (f    : ident)
                              (M    : memory)
                              (menv : heap)
                              (Hmc  : Memory_Corres G n f M menv)
                              {struct Hmc} : P f M menv :=
    match Hmc in (Memory_Corres _ _ f M menv) return (P f M menv) with
    | MemC f M menv i o eqs Hfind Heqs =>
        MemC_case f M menv i o eqs Hfind
          (* Turn: Forall (Memory_Corres_eq G n M menv) eqs
             into: Forall (Peq M menv) eqs *)
          ((fix map (eqs : list equation)
                    (Heqs: Forall (Memory_Corres_eq G n M menv) eqs) :=
              match Heqs in Forall _ fs return (Forall (Peq M menv) fs)
              with
              | Forall_nil => Forall_nil _
              | Forall_cons eq eqs Heq Heqs' =>
                Forall_cons eq (Memory_Corres_eq_mult M menv eq Heq)
                            (map eqs Heqs')
              end) eqs Heqs)
    end

  with Memory_Corres_eq_mult (M     : memory)
                             (menv  : heap)
                             (eq    : equation)
                             (Hmceq : Memory_Corres_eq G n M menv eq)
                             {struct Hmceq} : Peq M menv eq.
  refine(
    match Hmceq in (Memory_Corres_eq _ _ M menv eq) return (Peq M menv eq)
    with
    | MemC_EqDef M menv x cae => EqDef_case M menv x cae
    | MemC_EqApp M menv x f lae Hmc =>
        EqApp_case M menv x f lae
                   (fun (Mo     : memory)
                        (Hmfind : mfind_inst x M = Some Mo) => _)
    | MemC_EqFby M menv x v0 lae Hfind => EqFby_case M menv x v0 lae Hfind
    end).
  specialize (Hmc Mo Hmfind).
  destruct Hmc as [omenv [Hfindo Hmc]].
  exists omenv.
  apply Memory_Corres_mult in Hmc.
  split; [exact Hfindo|exact Hmc].
  Defined.

End Memory_Corres_mult.

Lemma Memory_Corres_eq_node_tl:
  forall node G eq n M menv,
    Ordered_nodes (node::G)
    -> ~Is_node_in_eq node.(n_name) eq
    -> (Memory_Corres_eq (node::G) n M menv eq
        <-> Memory_Corres_eq G n M menv eq).
Proof.
  intros node G eqs n M menv Hord Hini.
  split; intro Hmc; revert M menv eqs Hmc Hini.
  - induction 1 as [|? ? ? ? ? Hfind| |? ? ? ? ? ? Hfindn IH]
      using Memory_Corres_eq_mult
      with (P:=fun f M menv=>
                 node.(n_name) <> f ->
                 Memory_Corres G n f M menv);
    intro HH; try constructor.
    + intros Mo Hmfind.
      specialize (Hfind _ Hmfind).
      destruct Hfind as [omenv [Hfindo IH]].
      exists omenv.
      split; [exact Hfindo|].
      apply IH.
      intro Hneq; rewrite <-Hneq in HH.
      apply HH; repeat constructor.
    + trivial.
    + simpl in Hfindn.
      apply ident_eqb_neq in HH.
      rewrite HH in Hfindn.
      econstructor; [exact Hfindn|].
      apply find_node_later_not_Is_node_in with (2:=Hfindn) in Hord.
      simpl in Hord; clear Hfindn.
      apply Is_node_in_Forall in Hord.
      apply Forall_Forall with (1:=Hord) in IH.
      apply Forall_impl with (2:=IH).
      intuition.
  - induction 1 as [|? ? ? ? ? Hfind| |? ? ? ? ? ? Hfindn IH]
      using Memory_Corres_eq_mult
      with (P:=fun f M menv=>
                 node.(n_name) <> f ->
                 Memory_Corres (node::G) n f M menv);
    intro HH; try constructor.
    + intros Mo Hmfind.
      specialize (Hfind _ Hmfind).
      destruct Hfind as [omenv [Hfindo IH]].
      exists omenv.
      split; [exact Hfindo|].
      apply IH.
      intro Hneq; rewrite <-Hneq in HH.
      apply HH; repeat constructor.
    + intuition.
    + apply find_node_later_not_Is_node_in with (2:=Hfindn) in Hord.
      rewrite <-find_node_tl with (1:=HH) in Hfindn.
      econstructor; [exact Hfindn|].
      apply Is_node_in_Forall in Hord.
      apply Forall_Forall with (1:=Hord) in IH.
      apply Forall_impl with (2:=IH).
      intuition.
Qed.

Lemma Memory_Corres_eqs_node_tl:
  forall node G eqs n M menv,
    Ordered_nodes (node::G)
    -> ~Is_node_in node.(n_name) eqs
    -> (Forall (Memory_Corres_eq (node::G) n M menv) eqs
        <-> Forall (Memory_Corres_eq G n M menv) eqs).
Proof.
  induction eqs as [|eq eqs IH]; [now intuition|].
  intros n M menv Hord Hnini.
  apply not_Is_node_in_cons in Hnini.
  destruct Hnini as [Hnini Hninis].
  split;
    intro HH; apply Forall_cons2 in HH; destruct HH as [HH HHs];
    apply Forall_cons;
    (apply Memory_Corres_eq_node_tl with (1:=Hord) (2:=Hnini) (3:=HH)
     || apply IH with (1:=Hord) (2:=Hninis) (3:=HHs)).
Qed.

Lemma Memory_Corres_node_tl:
  forall f node G n M menv,
    Ordered_nodes (node :: G)
    -> node.(n_name) <> f
    -> (Memory_Corres (node :: G) n f M menv <-> Memory_Corres G n f M menv).
Proof.
  intros f node G n M menv Hord Hnf.
  split;
    inversion_clear 1;
    econstructor;
    repeat progress
         match goal with
         | Hf: find_node ?f (_ :: ?G) = Some _ |- _ =>
           rewrite find_node_tl with (1:=Hnf) in Hf
         | |- find_node ?f (_ :: ?G) = Some _ =>
           rewrite find_node_tl with (1:=Hnf)
         | Hf: find_node ?f ?G = Some _ |- find_node ?f ?G = Some _ => exact Hf
         | H:Forall (Memory_Corres_eq _ _ _ _) _
           |- Forall (Memory_Corres_eq _ _ _ _) _ =>
           apply Memory_Corres_eqs_node_tl with (1:=Hord) (3:=H)
         | Hf: find_node ?f ?G = Some _ |- ~Is_node_in _ _ =>
           apply find_node_later_not_Is_node_in with (1:=Hord) (2:=Hf)
         end.
Qed.

Lemma Is_memory_in_Memory_Corres_eqs:
  forall G n M menv x eqs,
    Is_defined_in x eqs
    -> ~Is_variable_in x eqs
    -> Forall (Memory_Corres_eq G n M menv) eqs
    -> (forall ms, mfind_mem x M = Some ms
                   -> mfind_mem x menv = Some (ms n)).
Proof.
  induction eqs as [|eq eqs IH]; [now inversion 1|].
  intros Hidi Hnvi Hmc ms.
  apply Is_defined_in_cons in Hidi.
  apply not_Is_variable_in_cons in Hnvi.
  destruct Hnvi as [Hnvi Hnvis].
  inversion_clear Hmc as [|? ? Hmceq Hmceqs].
  destruct Hidi as [Himeqs|[Himeq Himeqs]];
    [|now apply IH with (1:=Himeqs) (2:=Hnvis) (3:=Hmceqs)].
  destruct eq;
  inversion Himeqs; subst;
  try (exfalso; apply Hnvi; now constructor).
  inversion_clear Hmceq; auto.
Qed.

Lemma Memory_Corres_eqs_add_mem:
  forall G M menv n y ms eqs,
    mfind_mem y M = Some ms
    -> Forall (Memory_Corres_eq G n M menv) eqs
    -> Forall (Memory_Corres_eq G n M (madd_mem y (ms n) menv)) eqs.
Proof.
  induction eqs as [|eq eqs IH]; [now auto|].
  intros Hmfind Hmc.
  apply Forall_cons2 in Hmc.
  destruct Hmc as [Hmc0 Hmc1].
  apply Forall_cons; [|apply IH with (1:=Hmfind) (2:=Hmc1)].
  destruct eq; repeat constructor.
  - intros Mo Hifind.
    inversion_clear Hmc0 as [|? ? ? ? ? Hmc|].
    specialize (Hmc _ Hifind).
    destruct Hmc as [omenv HH].
    exists omenv.
    exact HH.
  - intros ms' Hmfind'.
    destruct (ident_eq_dec i y) as [He|Hne].
    + rewrite He in *.
      rewrite Hmfind in Hmfind'.
      injection Hmfind'; intro H; rewrite <- H; clear H.
      rewrite mfind_mem_gss; reflexivity.
    + rewrite mfind_mem_gso with (1:=Hne).
      inversion_clear Hmc0 as [| |? ? ? ? ? Hmc].
      now apply Hmc with (1:=Hmfind').
Qed.

(* Unfortunately, a similar lemma to Memory_Corres_eqs_add_mem but for add_obj
   does not seem to hold without extra conditions:

     Lemma Memory_Corres_eqs_add_obj:
       forall G n M menv y Mo g omenv eqs,
         mfind_inst y M = Some Mo
         -> Memory_Corres G n g Mo omenv
         -> Memory_Corres_eqs G n M menv eqs
         -> Memory_Corres_eqs G n M (add_obj y omenv menv) eqs.

   Consider the equations:
      [ x = f y; x = g y; ... ]
   It is possible for this system to have an m-semantics if both f and g have
   the same input/output behaviour, but also possible for the memory structures
   of f and g to differ from one another. In this case, we end up having as
   hypothesis
        Memory_Corres G n g Mo omenv
   and the goal
        Memory_Corres G n f Mo omenv *)

Lemma Memory_Corres_eqs_add_obj:
  forall G n M menv eqs y omenv,
    Forall (Memory_Corres_eq G n M menv) eqs
    -> ~Is_defined_in y eqs
    -> Forall (Memory_Corres_eq G n M (madd_obj y omenv menv)) eqs.
Proof.
  induction eqs as [|eq eqs IH]; [now constructor|].
  intros y omenv Hmce Hniii.
  apply Forall_cons2 in Hmce.
  destruct Hmce as [Hmce0 Hmce1].
  apply not_Is_defined_in_cons in Hniii.
  destruct Hniii as [Hniii0 Hniii1].
  apply Forall_cons; [|now apply IH with (1:=Hmce1) (2:=Hniii1)].
  destruct eq; constructor; try constructor.
  - intros Mo Hmfind.
    destruct (ident_eq_dec i y) as [Hiy|Hniy].
    + rewrite Hiy in Hniii0; exfalso; apply Hniii0; constructor.
    + inversion_clear Hmce0 as [|? ? ? ? ? Hfindo|].
      specialize (Hfindo _ Hmfind).
      destruct Hfindo as [omenv' [Hfindo Hmc]].
      exists omenv'.
      split; [|exact Hmc].
      rewrite mfind_inst_gso; [|exact Hniy].
      exact Hfindo.
  - intros ms Hmfind.
    inversion_clear Hmce0 as [| |? ? ? ? ? HH].
    rewrite mfind_mem_add_inst.
    apply HH with (1:=Hmfind).
Qed.

Lemma Memory_Corres_unchanged:
  forall G f n ls M ys menv,
    Welldef_global G
    -> msem_node G f ls M ys
    -> absent_list ls n
    -> Memory_Corres G n f M menv
    -> Memory_Corres G (S n) f M menv.
Proof.
  intros G f n ls M ys menv Hwdef Hmsem Habs.
  revert menv.
  induction Hmsem as [|H M y f M' lae ls ys Hmfind Hls Hys Hmsem IH
                      |H M ms y ls yS v0 lae Hmfind Hms0 Hls HyS Hy
                      |f xs M ys i o eqs Hf Heqs IH]
  using msem_node_mult
  with (P := fun H M eq Hsem =>
               forall menv,
                 rhs_absent_instant (restr H n) eq
                 -> Memory_Corres_eq G n M menv eq
                 -> Memory_Corres_eq G (S n) M menv eq).
  - inversion_clear 2; constructor; assumption.
  - intros Hrhsa Hmceq.
    constructor.
    intros Mo Hmfind'.
    rewrite Hmfind in Hmfind'.
    injection Hmfind'; intro Heq; rewrite <-Heq; clear Heq Hmfind'.
    inversion_clear Hmceq as [|? ? ? ? ? Hmc'|].
    specialize (Hmc' _ Hmfind).
    destruct Hmc' as [omenv [Hfindo Hmc]].
    exists omenv.
    split; [exact Hfindo|].
    apply IH with (2:=Hmc).
    inversion_clear Hrhsa as [|? ? ? ? Hlaea|].
    specialize (Hls n); simpl in Hls.
    assert (ls n = vs) by sem_det.
    unfold absent_list; congruence.
  - rename Habs into menv.
    intros Hdefabs Hmceq.
    constructor.
    intros ms0 Hmfind0.
    rewrite Hmfind in Hmfind0.
    injection Hmfind0; intro Heq; rewrite <-Heq; clear Heq Hmfind0 ms0.
    inversion_clear Hmceq as [| |? ? ? ? ? Hmenv].
    apply Hmenv in Hmfind.
    rewrite Hmfind.
    inversion_clear Hdefabs as [| |? ? ? Hlaea].
    specialize (Hls n); simpl in Hls.
    specialize Hy with n.
    assert (Hls_abs: ls n = absent) by sem_det.
    rewrite Hls_abs in Hy.
    destruct Hy as [Hmseq H0].
    rewrite Hmseq.
    reflexivity.
  - intros menv Hmc.
    inversion_clear Hmc as [? ? ? i' o' eqs' Hf' Hmceqs].
    rewrite Hf in Hf'.
    injection Hf';
      intros HR1 HR2 HR3;
      rewrite <-HR1, <-HR2, <-HR3 in *;
      clear i' o' eqs' Hf' HR1 HR2 HR3.
    clear Heqs.
    destruct IH as [H [Hxs [Hys [Habs' [Hout HH]]]]].
    apply Habs' in Habs.
    apply Forall_Forall with (1:=Habs) in HH.
    apply Forall_Forall with (1:=Hmceqs) in HH.
    clear Habs Hmceqs.
    econstructor; [exact Hf|].
    apply Forall_impl with (2:=HH); clear HH.
    intros eq HH.
    destruct HH as [Hmceq [Habseq [Hmsem HH]]].
    now apply HH with (1:=Habseq) (2:=Hmceq).
Qed.