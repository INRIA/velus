From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import Transcription.Tr.

From Velus Require Import Lustre.LOrdered.
From Velus Require Import NLustre.NLOrdered.

From Velus Require Import CoindStreams IndexedStreams.

From Coq Require Import String.

From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import Permutation.
From Coq Require Import Omega.
From Coq Require Import Setoid.
From Coq Require Import Morphisms.

Open Scope list.

From compcert Require Import common.Errors.
Open Scope error_monad_scope.

Module Type TRORDERED
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import OpAux: OPERATORS_AUX        Op)
       (L           : LSYNTAX          Ids Op)
       (Lord        : LORDERED         Ids Op       L)
       (Import CE   : CESYNTAX             Op)
       (NL          : NLSYNTAX         Ids Op              CE)
       (Ord         : NLORDERED        Ids Op              CE NL)
       (Import TR   : TR               Ids Op OpAux L      CE NL).

  Lemma inin_l_nl :
    forall f n n' Hpref,
      to_node n Hpref = OK n' ->
      Ord.Is_node_in f (NL.n_eqs n') ->
      Lord.Is_node_in f (L.n_eqs n).
  Proof.
    intros * Htr Hord.
    destruct n'. simpl in Hord.
    tonodeInv Htr.
    clear - Hord Hmmap. revert dependent n_eqs.
    induction (L.n_eqs n); intros. inv Hmmap. inv Hord.
    apply mmap_cons in Hmmap.
    destruct Hmmap as (eq' & l' & Hneqs & Hteq & Hmmap); subst.
    inversion_clear Hord as [ ? ? Hord' |].
    - econstructor.
      destruct eq' as [| i ck x le |]; inv Hord'.
      destruct a as [ xs [|]]. inv Hteq. cases.
      destruct l0; [ idtac | inv Hteq; cases ].
      destruct e; inv Hteq; cases; monadInv H0;
        econstructor; apply Lord.INEapp2.
    - apply Exists_cons_tl. eapply IHl; eauto.
  Qed.

  Lemma ninin_l_nl :
    forall f n n' Hpref,
      to_node n Hpref = OK n' ->
      ~ Lord.Is_node_in f (L.n_eqs n) ->
      ~ Ord.Is_node_in f (NL.n_eqs n').
  Proof.
    intros. intro. destruct H0. eapply inin_l_nl; eauto.
  Qed.

  Fact to_global_names : forall name G G' Hprefs,
      Exists (fun n => (name = L.n_name n)%type) G ->
      to_global G Hprefs = OK G' ->
      Exists (fun n => (name = NL.n_name n)%type) G'.
  Proof.
    induction G; intros * Hnames Htog; inv Hnames; monadInv Htog; eauto.
    left. eapply to_node_name; eauto.
  Qed.

  Lemma ord_l_nl :
    forall G P Hprefs,
      to_global G Hprefs = OK P ->
      Lord.Ordered_nodes G ->
      Ord.Ordered_nodes P.
  Proof.
    intros * Htr Hord.
    revert dependent P.
    induction Hord; intros; monadInv Htr; constructor; eauto.
    - intros f Hin.
      assert (Lord.Is_node_in f (L.n_eqs nd)) as Hfin.
      eapply inin_l_nl; eauto.
      apply H in Hfin. destruct Hfin as [ Hf Hnds ].
      split.
      + apply to_node_name in EQ. now rewrite <- EQ.
      + eapply to_global_names; eauto.
    - apply to_node_name in EQ. rewrite <- EQ.
      eapply TR.to_global_names; eauto.
  Qed.

End TRORDERED.

Module TrOrderedFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (LSyn : LSYNTAX Ids Op)
       (LOrd : LORDERED Ids Op LSyn)
       (CE : CESYNTAX Op)
       (NL : NLSYNTAX Ids Op CE)
       (Ord : NLORDERED Ids Op CE NL)
       (TR : TR Ids Op OpAux LSyn CE NL)
       <: TRORDERED Ids Op OpAux LSyn LOrd CE NL Ord TR.
  Include TRORDERED Ids Op OpAux LSyn LOrd CE NL Ord TR.
End TrOrderedFun.
