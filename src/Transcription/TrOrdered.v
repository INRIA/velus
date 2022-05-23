From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import Transcription.Tr.

From Velus Require Import Lustre.LOrdered.
From Velus Require Import NLustre.NLOrdered.

From Coq Require Import String.

From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import Permutation.
From Coq Require Import Setoid.
From Coq Require Import Morphisms.

Open Scope list.

From compcert Require Import common.Errors.
Open Scope error_monad_scope.

Module Type TRORDERED
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import OpAux: OPERATORS_AUX    Ids Op)
       (Import Cks  : CLOCKS           Ids Op OpAux)
       (Senv        : STATICENV        Ids Op OpAux Cks)
       (L           : LSYNTAX          Ids Op OpAux Cks Senv)
       (Lord        : LORDERED         Ids Op OpAux Cks Senv L)
       (Import CE   : CESYNTAX         Ids Op OpAux Cks)
       (NL          : NLSYNTAX         Ids Op OpAux Cks         CE)
       (Ord         : NLORDERED        Ids Op OpAux Cks         CE NL)
       (Import TR   : TR               Ids Op OpAux Cks Senv L  CE NL).

  Lemma inin_l_nl :
    forall f n n',
      to_node n = OK n' ->
      Ord.Is_node_in f (NL.n_eqs n') ->
      Lord.Is_node_in_block f (L.n_block n).
  Proof.
    intros * Htr Hord.
    destruct n'. simpl in Hord.
    tonodeInv Htr. cases. do 2 constructor. right.
    clear - Hord Hmmap. monadInv Hmmap. rename EQ into Hmmap. revert dependent n_eqs.
    induction l2; intros. inv Hmmap. inv Hord.
    apply mmap_cons in Hmmap.
    destruct Hmmap as (eq' & l' & Hneqs & Hteq & Hmmap); subst.
    inversion_clear Hord as [ ? ? Hord' |].
    - constructor. clear IHl2 Hmmap.
      revert dependent eq'. generalize (@nil (ident * clock)) as xr.
      induction a using L.block_ind2; intros; simpl in *;
        try solve [monadInv Hteq].
      + destruct eq' as [| i ck x le |]; inv Hord'.
        destruct eq as [ xs [|]]. inv Hteq.
        destruct l1; [ idtac | inv Hteq; cases ].
        destruct e; inv Hteq; cases; monadInv H0.
        do 2 econstructor; apply Lord.INEapp2.
      + cases. apply Forall_singl in H.
        eapply H in Hteq; eauto.
        constructor. eauto.
    - apply Exists_cons_tl. eapply IHl2; eauto.
  Qed.

  Lemma ninin_l_nl :
    forall f n n',
      to_node n = OK n' ->
      ~ Lord.Is_node_in_block f (L.n_block n) ->
      ~ Ord.Is_node_in f (NL.n_eqs n').
  Proof.
    intros. intro. destruct H0. eapply inin_l_nl; eauto.
  Qed.

  Fact to_global_names' : forall name G G',
      Forall (fun n => (name <> L.n_name n)%type) G.(L.nodes) ->
      to_global G = OK G' ->
      Forall (fun n => (name <> NL.n_name n)%type) G'.(NL.nodes).
  Proof.
    intros ? (enms&nds) ? Hnames Htog. monadInv Htog.
    revert dependent x.
    induction nds; intros; simpl in *; monadInv EQ; simpl; inv Hnames; constructor.
    - erewrite <-to_node_name; eauto.
    - eapply IHnds in EQ; eauto.
  Qed.

  Lemma ord_l_nl :
    forall G P,
      to_global G = OK P ->
      Lord.Ordered_nodes G ->
      Ord.Ordered_nodes P.
  Proof.
    intros (?&nds) ? Htr Hord. monadInv Htr.
    revert dependent x.
    unfold Lord.Ordered_nodes, CommonProgram.Ordered_program in Hord; simpl in Hord.
    induction Hord as [|?? (?&?)]; intros; simpl in *; monadInv EQ; constructor; eauto.
    constructor.
    - intros f Hin.
      assert (Lord.Is_node_in_block f (L.n_block x)) as Hfin.
      { eapply inin_l_nl; eauto. }
      apply H in Hfin as (?&(?&?&?)). split; auto.
      + erewrite <-to_node_name; eauto.
      + assert (L.find_node f {| L.enums := enums; L.nodes := l |} = Some x0) as Hfind'.
        { unfold L.find_node. rewrite H2; auto. }
        eapply find_node_global in Hfind' as (?&?&?). 2:(unfold to_global; simpl; rewrite EQ; simpl; eauto).
        unfold NL.find_node in H3. apply option_map_inv in H3 as ((?&?)&?&?); subst.
        erewrite CommonProgram.find_unit_later; eauto. 1-2:simpl; auto.
        apply CommonProgram.equiv_program_refl.
    - replace l with {| L.enums := enums; L.nodes := l |}.(L.nodes) in H0 by eauto.
      eapply to_global_names' in H0. 2:(unfold to_global; simpl; rewrite EQ; simpl; eauto).
      simpl in H0. erewrite to_node_name in H0; eauto.
    - eapply IHHord in EQ; eauto.
  Qed.

End TRORDERED.

Module TrOrderedFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (LSyn : LSYNTAX Ids Op OpAux Cks Senv)
       (LOrd : LORDERED Ids Op OpAux Cks Senv LSyn)
       (CE : CESYNTAX Ids Op OpAux Cks)
       (NL : NLSYNTAX Ids Op OpAux Cks CE)
       (Ord : NLORDERED Ids Op OpAux Cks CE NL)
       (TR : TR Ids Op OpAux Cks Senv LSyn CE NL)
       <: TRORDERED Ids Op OpAux Cks Senv LSyn LOrd CE NL Ord TR.
  Include TRORDERED Ids Op OpAux Cks Senv LSyn LOrd CE NL Ord TR.
End TrOrderedFun.
