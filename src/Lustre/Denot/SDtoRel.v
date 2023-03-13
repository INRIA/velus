From Coq Require Import BinPos List Permutation Morphisms.

From Velus Require Import Common Ident Environment Operators Clocks CoindStreams.
From Velus Require Import Lustre.StaticEnv Lustre.LSyntax Lustre.LOrdered Lustre.LSemantics Lustre.LTyping Lustre.LClocking Lustre.LCausality.

From Velus Require Import FunctionalEnvironment.
From Velus Require Import Lustre.Denot.Cpo.

Close Scope equiv_scope. (* conflicting notation "==" *)

Require Import Cpo_ext CommonDS SDfuns Denot Infty InftyProof Safe CommonList2.

Import List ListNotations.

Module Type SDTOREL
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Senv  : STATICENV     Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
       (Import Typ   : LTYPING       Ids Op OpAux Cks Senv Syn)
       (Import Cl    : LCLOCKING     Ids Op OpAux Cks Senv Syn)
       (Import Caus  : LCAUSALITY    Ids Op OpAux Cks Senv Syn)
       (Import Lord  : LORDERED      Ids Op OpAux Cks Senv Syn)
       (Import Str   : COINDSTREAMS  Ids Op OpAux Cks)
       (Import Sem   : LSEMANTICS Ids Op OpAux Cks Senv Syn Lord Str)
       (Import Den   : LDENOT     Ids Op OpAux Cks Senv Syn Lord)
       (Import Inf   : LDENOTINF  Ids Op OpAux Cks Senv Syn Typ Caus Lord Den)
       (Import Safe  : LDENOTSAFE Ids Op OpAux Cks Senv Syn Typ Cl Lord Den).

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX  *)

(* TODO: inutile finalement ? *)
Section Forallt.

  (* forall sur les lignes d'une matrice donnée en colonnes *)
  Context {A : Type}.
  Variable (d : A). (* paramètre par défaut *)
  Variable (P : list A -> Prop).

  Inductive Forallt : list (list A) -> Prop :=
  | ftnil : forall l,
      Forall (eq []) l ->
      Forallt l
  | ftcons : forall (l : list (list A)),
      P (List.map (hd d) l) ->
      Forallt (List.map (@tl A) l) ->
      Forallt l.

End Forallt.


  Lemma tl_length :
    forall A (l : list A),
      length (tl l) = Nat.pred (length l).
  Proof.
    now destruct l.
  Qed.

  Lemma nth_nil :
    forall A n (d : A),
      nth n [] d = d.
  Proof.
    destruct n; auto.
  Qed.

  Lemma hd_nth :
    forall A (l : list A) (d : A),
      nth O l d = hd d l.
  Proof.
    destruct l; auto.
  Qed.

  Lemma tl_nth :
    forall A (l : list A) (d : A) n,
      nth (S n) l d = nth n (tl l) d.
  Proof.
    destruct l, n; auto.
  Qed.

  Lemma map_hd_nth :
    forall A (l : list (list A)) d,
      map (hd d) l = map (fun l0 => nth 0 l0 d) l.
  Proof.
    induction l; simpl; f_equal; auto using hd_nth.
  Qed.

  Lemma map_tl_nth :
    forall A (l : list (list A)) n d,
      map (fun l0 => nth (S n) l0 d) l = map (fun l0 => nth n (tl l0) d) l.
  Proof.
    induction l; simpl; f_equal; auto using tl_nth.
  Qed.

  Lemma list_eq_ext :
    forall A (l1 l2 : list A) d,
      length l1 = length l2 ->
      (forall n, n < length l1 -> nth n l1 d = nth n l2 d) ->
      l1 = l2.
  Proof.
    clear.
    induction l1; simpl; intros * Hl Hn.
    - destruct l2; simpl in *; congruence.
    - destruct l2; try (simpl in *; congruence).
      f_equal.
      + apply (Hn O); auto with arith.
      + eapply IHl1 with d; intros; auto.
        rewrite (Hn (S n)); auto with arith.
  Qed.

  Lemma list_eq_ext2 :
    forall A (l1 l2 : list A),
      (forall n, nth_error l1 n = nth_error l2 n) ->
      l1 = l2.
  Proof.
    clear.
    induction l1; intros * Hn.
    - destruct l2; simpl in *; auto.
      specialize (Hn O); inv Hn.
    - destruct l2.
      specialize (Hn O); inv Hn.
      f_equal.
      + now injection (Hn O).
      + eapply IHl1; intros; auto.
        apply (Hn (S n)).
  Qed.

  Lemma Forall3_same_2_3:
    forall A B P (xs: list A) (ys : list B),
      Forall3 P xs ys ys <-> Forall2 (fun x y => P x y y) xs ys.
  Proof.
    induction xs as [|x xs IH]; split; intros * H; inv H; constructor; auto.
    rewrite <- IH; auto.
    rewrite IH; auto.
  Qed.


(** ** Forall2 sur les lignes d'une matrice *)
Section Forall2t.

  Context {A B : Type}.
  Variable (d : A). (* paramètre par défaut *)

  Variable (P : list A -> B -> Prop).

  (* On considère une matrice de A et une colonne supplémentaire
     de B. Le prédicat P doit être vrai sur chaque ligne. *)
  Inductive Forall2t : list (list A) -> list B -> Prop :=
  | f2tnil : forall l,
      Forall (eq []) l ->
      Forall2t l []
  | f2tcons : forall (l : list (list A)) (h : B) (t : list B),
      P (List.map (hd d) l) h ->
      Forall2t (List.map (@tl A) l) t ->
      Forall2t l (h :: t).

  Lemma Forall2t_forall2 :
    forall ll l (b : B),
      Forall (fun xl => length xl = length l) ll ->
      Forall2t ll l
      <-> forall n,
          n < length l ->
          P (map (fun l => nth n l d) ll) (nth n l b).
  Proof.
    intros * Hl; split.
    - intros Ht.
      induction Ht; intros * Le.
      { now inv Le. }
      destruct n; simpl.
      + rewrite <- map_hd_nth; auto.
      + setoid_rewrite map_map in IHHt.
        rewrite map_tl_nth.
        apply IHHt; auto with arith.
        eapply Forall_map, Forall_impl; eauto.
        intros [] **; simpl in *; lia.
    - intro Nth.
      revert dependent ll.
      induction l as [| x l]; intros.
      { constructor; simpl_Forall; now apply symmetry, length_zero_iff_nil. }
      constructor.
      + rewrite map_hd_nth.
        apply (Nth O); simpl; auto with arith.
      + eapply IHl.
        { eapply Forall_map, Forall_impl; eauto.
          intros [] **; simpl in *; lia. }
        intros.
        rewrite map_map, <- map_tl_nth.
        apply (Nth (S n)); simpl; auto with arith.
  Qed.

  (** Calcul de la transposée d'une matrice. On donne sa spécification
      dans son type car raisonner sur la fonction direcement est rendu
      très pénible par la preuve de terminaison. *)
  Program Fixpoint transp (l : list (list A)) (k : { k | Forall (fun l => length l = k) l })
    {measure (length (concat l))}
    : { l' : list (list A)
      | (l <> [] -> length l' = k /\ Forall (fun ll => length ll = length l) l')
        /\ forall n m, nth n (nth m l' []) d = nth m (nth n l []) d } :=
    match l with
    | [] => []
    | [] :: _ => []
    | rows => List.map (hd d) rows :: transp (List.map (@tl _) rows) (exist _ (Nat.pred k) _)
    end.

  Next Obligation.
    simpl; split; intros; cases; congruence.
  Qed.

  Next Obligation.
    inv H.
    simpl; split; intros; auto.
    setoid_rewrite length_zero_iff_nil in H3.
    rewrite Forall_nth in H3.
    cases; simpl in *.
    - destruct (Nat.lt_ge_cases n (length wildcard')).
      + rewrite H3; auto.
      + do 2 (rewrite nth_overflow; auto).
    - destruct (Nat.lt_ge_cases n (length wildcard')).
      + rewrite H3; auto.
      + do 2 (rewrite nth_overflow; simpl; auto with arith).
  Qed.

  Next Obligation.
    rewrite Forall_map.
    setoid_rewrite tl_length.
    simpl_Forall; auto.
  Qed.

  Next Obligation.
    destruct l as [|[] l].
    1,2: contradict H; eauto.
    simpl.
    rewrite 2 app_length.
    assert (le (length (concat (map (tl (A:=A)) l))) (length (concat l))); auto with arith.
    clear.
    induction l; simpl; auto.
    rewrite 2 app_length.
    destruct a; simpl; auto with arith.
  Qed.

  Next Obligation.
    rename n into Hl'.
    destruct transp as [? [Heq Ht]]; simpl.
    destruct Heq as [Heq Hf]; auto using map_eq_nnil.
    split; intros.
    { rewrite Heq; simpl.
      split.
      - destruct k; auto.
        destruct l as [|[]]; simpl in *; try congruence.
        inv H; simpl in *; congruence.
      - constructor; auto using map_length.
        eapply Forall_impl in Hf; eauto.
        simpl; intros * HH.
        now rewrite map_length in HH.
    }
    destruct (Nat.lt_ge_cases n (length l)) as [Lt|Le].
    2:{ rewrite (nth_overflow _ _ Le), nth_nil.
        cases. rewrite nth_overflow; auto; now rewrite map_length.
        rewrite Ht, nth_overflow; auto.
        rewrite nth_overflow; simpl; auto with arith.
        now rewrite map_length.
    }
    cases; simpl.
    erewrite map_nth', hd_nth; eauto.
    erewrite Ht, map_nth', tl_nth; eauto.
  Qed.

  Next Obligation.
    split; intros; congruence.
  Qed.

  (* Forall2t est bien l'analogue de Forall2 sur la matrice
     tansposée. *)
  Lemma Forall2t_Forall2 :
    forall ll l (Hl : Forall (fun l' => length l' = length l) ll),
      ll <> [] ->
      Forall2t ll l ->
      Forall2 P (proj1_sig (transp ll (exist _ _ Hl))) l.
  Proof.
    intros * Nnil Hft.
    apply Forall2_forall2.
    destruct transp as [ll' [Hlt Ht]]; simpl in *.
    destruct Hlt as [Hlt Hf]; auto.
    split; auto.
    intros * Hn ??; subst.
    rewrite (nth_indep _ _ [] Hn).
    rewrite (Forall2t_forall2 _ _ b) in Hft; auto.
    assert ((nth n ll' []) =  (map (fun l => nth n l d) ll)) as ->.
    2: apply Hft; congruence.
    eapply list_eq_ext with d.
    - eapply Forall_nth in Hf as ->; auto using map_length.
    - intros m Hm.
      (* TODO: il y a sans doute plus propre à faire... *)
      erewrite Ht, map_nth'; auto.
      eapply Forall_nth in Hf; eauto.
      now rewrite Hf in Hm.
  Qed.

End Forall2t.



(** Dans cette section on donne une définition alternative à la sémantique
    du merge (LSemantics.Smerge), qui ne manipule pas de Forall2Brs.
    Il est probable que ça passe mieux avec les définitions de Denot.v. *)
Section Smerge_alt.

  Lemma Forall2Brs_transp :
    forall (G : global) H b,
    forall ess vss d Hk,
      vss <> [] ->
      Forall2
        (fun '(t, es) (vs : list (enumtag * Stream svalue)) =>
           exists xss : list (list (Stream svalue)),
             Forall2 (sem_exp G H b) es xss /\ vs = map (pair t) (concat xss)) ess vss ->
      Forall2Brs (sem_exp G H b) ess (proj1_sig (transp d vss Hk)).
  Proof.
    intros * Nnil Hf.
    destruct (transp d vss Hk) as (vsst & HH & Hnm).
    destruct HH as [Hlt Hllt]; auto; simpl in *; clear HH.
    destruct Hk as (k & Hk); simpl in *; subst.
    clear Nnil.
    revert dependent vsst.
    induction Hf; intros.
    - constructor.
      simpl_Forall. destruct x; simpl in *; congruence.
    - destruct x as (t, es).
      destruct H0 as (xss & Hsem & ?); subst.
      inv Hk.
      econstructor; eauto.
      + eapply (IHHf (map (@tl _) vsst)).
        * simpl_Forall. now rewrite map_length.
        * intros; destruct (Nat.le_gt_cases (length vsst) m).
          2: erewrite map_nth', <- tl_nth, Hnm; auto.
          setoid_rewrite nth_overflow at 2.
          2: rewrite map_length; auto.
          rewrite nth_nil, nth_overflow; auto.
          destruct (nth_in_or_default n l' []) as [| ->]; simpl in *; try lia.
          simpl_Forall; lia.
        * simpl_Forall. rewrite tl_length; lia.
      + rewrite Forall3_map_2, Forall3_same_2_3.
        clear IHHf.
        rewrite map_length in *.
        apply Forall2_forall2; split; intros; subst; auto.
        rewrite nth_indep with (d' := []); try lia.
        assert (In (nth n vsst []) vsst) as Hin.
        { apply nth_In; congruence. }
        simpl_Forall.
        destruct (nth n vsst []) eqn:GG; simpl in *; try lia.
        f_equal.
        specialize (Hnm O n).
        rewrite GG in Hnm; simpl in Hnm; subst.
        erewrite map_nth'; eauto.
  Qed.

  (** Cette définition semble plus naturelle : vss correspond exactement
      à la matrice de concaténation de [sem_exp] sur ess, l'opérateur
      merge relationnel est appliqué sur les lignes de la matrice
      grâce à Forall2t. *)
  Lemma Smerge_alt :
    forall (G : global) H b x tx ess lann os,
    forall d (xs : Stream svalue) (vss : list (list (enumtag * Stream svalue))),
      sem_var (fst H) x xs ->
      vss <> [] ->
      Forall (fun l => length l = length os) vss ->
      Forall2 (fun '(t,es) vs =>
                 exists xss, Forall2 (sem_exp G H b) es xss
                        /\ vs = map (pair t) (concat xss)) ess vss  ->
      Forall2t d (merge xs) vss os ->
      sem_exp G H b (Emerge (x, tx) ess lann) os.
  Proof.
    intros * Hx Nnil Hl Hf Ht.
    unshelve eapply Forall2t_Forall2 in Ht; auto.
    unshelve eapply Forall2Brs_transp in Hf; eauto.
    revert Ht Hf.
    destruct (transp d vss _) as (vsst & HH); intros; simpl in *.
    destruct HH as ([Hlt Hllt] & Hnm); auto.
    apply Smerge with xs vsst; auto.
  Qed.

End Smerge_alt.


(* TODO: à terme, mettre cette section dans LSemantics *)
Section Sem_absent.

(* TODO: move *)
Section FromLClockedSemantics.
Lemma clocks_of_false :
  forall ss,
    clocks_of (List.map (fun _ : Stream svalue => Streams.const absent) ss) ≡ Streams.const false.
Proof.
  intros *.
  eapply ntheq_eqst. intros n.
  rewrite clocks_of_nth, const_nth.
  induction ss; simpl; auto.
  rewrite const_nth; simpl; auto.
Qed.
Lemma clocks_of_false2 :
  forall n,
    clocks_of (repeat (Streams.const absent) n) ≡ Streams.const false.
Proof.
  intros.
  eapply ntheq_eqst. intro k.
  rewrite clocks_of_nth, const_nth.
  induction n; simpl; auto.
  rewrite const_nth; simpl; auto.
Qed.
Lemma fby_absent {A}:
  @fby A (Streams.const absent) (Streams.const absent) (Streams.const absent).
Proof.
  cofix CoFix.
  rewrite CommonStreams.const_Cons. constructor; auto.
Qed.
(* à adapter de ClockedSem.sem_node_ck_cons' *)
Corollary sem_node_cons' :
    forall (nd : node) nds types externs f xs ys,
      Ordered_nodes (Global types externs (nd::nds))
      -> sem_node (Global types externs nds) f xs ys
      -> nd.(n_name) <> f
      -> sem_node (Global types externs (nd::nds)) f xs ys.
Proof.
Admitted.

(* à adapter de ClockedSem.sem_block_ck_cons' *)
Lemma sem_block_cons' :
  forall (nd : node) nds types externs bck Hi bk,
    Ordered_nodes (Global types externs (nd::nds))
    -> sem_block (Global types externs nds) Hi bk bck
    -> ~Is_node_in_block nd.(n_name) bck
    -> sem_block (Global types externs (nd::nds)) Hi bk bck.
Proof.
Admitted.

End FromLClockedSemantics.


(* Hypothèse d'induction sur les nœuds du programme *)
Definition sem_global_abs (G : global) :=
  forall f n,
    find_node f G = Some n ->
    let ss := repeat (Streams.const absent) (length (n_in n)) in
    let os := repeat (Streams.const absent) (length (n_out n)) in
    sem_node G f ss os.

Lemma sem_exp_absent :
  forall (G : global) Γ,
    sem_global_abs G ->
    forall e,
    restr_exp e ->
    wt_exp G Γ e ->
    let H := (fun _ => Some (Streams.const absent), FEnv.empty (Stream svalue)) in
    sem_exp G H (Streams.const false) e (repeat (Streams.const absent) (numstreams e)).
Proof.
  intros * HG.
  induction e using exp_ind2; intros Hr Hwt ?; inv Hr; inv Hwt.
  - (* Econst *)
    constructor.
    apply ntheq_eqst; intro.
    now rewrite const_nth', 2 const_nth.
  - (* Evar *)
    constructor; econstructor; now eauto.
  - (* Eunop *)
    take (typeof e = _) and rewrite <- length_typeof_numstreams, it in IHe.
    simpl in *; econstructor; eauto using Is_node_in_exp.
    eapply lift1_spec; intros.
    left. split; apply const_nth.
  - (* Ebinop *)
    take (typeof e1 = _) and rewrite <- length_typeof_numstreams, it in IHe1.
    take (typeof e2 = _) and rewrite <- length_typeof_numstreams, it in IHe2.
    simpl in *; econstructor; eauto using Is_node_in_exp.
    eapply lift2_spec; intros.
    left. repeat split; apply const_nth.
  - (* Efby *)
    apply Sfby with
      (s0ss := List.map (fun e => repeat (Streams.const absent) (numstreams e)) e0s)
      (sss := List.map (fun e => repeat (Streams.const absent) (numstreams e)) es); simpl.
    + clear H9 H10 H11.
      induction e0s; simpl in *; constructor; inv H; inv H4; inv H7; eauto.
    + clear H9 H10 H11.
      induction es; simpl in *; inv H0; inv H6; inv H8; constructor; auto.
    + rewrite <- 2 flat_map_concat_map, 2 flat_map_repeat.
      rewrite <- 2 annots_numstreams, <- 2 length_typesof_annots.
      take (typesof es = _) and rewrite it.
      take (typesof e0s = _) and rewrite it.
      rewrite map_length.
      apply Forall3_repeat, fby_absent.
  - (* Ewhen *)
    apply Swhen with
      (s := Streams.const absent)
      (ss := List.map (fun e => repeat (Streams.const absent) (numstreams e)) es); simpl.
    + rewrite Forall2_map_2. apply Forall2_same.
      apply Forall_impl_inside with (P := restr_exp) in H; auto.
      apply Forall_impl_inside with (P := wt_exp _ _) in H; auto.
    + econstructor; now eauto.
    + rewrite <- flat_map_concat_map, flat_map_repeat.
      rewrite <- annots_numstreams, <- length_typesof_annots.
      apply Forall2_repeat.
      apply when_spec. intros n.
      left. repeat split; apply const_nth.
  - (* Emerge *)
    simpl.
    pose (vss := map (fun '(t,es) => repeat (t, @Streams.const svalue absent)
                                    (list_sum (map numstreams es))) es).
    assert (Hl : Forall (fun l => length l = length tys) vss).
    { subst vss.
      simpl_Forall; subst.
      now rewrite repeat_length, length_typesof_annots, annots_numstreams. }
    eapply Smerge_alt with (d := (46, Streams.const absent)) (vss := vss);
      subst vss; rewrite ?repeat_length; auto using map_eq_nnil.
    + econstructor; now eauto.
    + subst H0.
      simpl_Forall.
      exists (map (fun e => repeat (Streams.const absent) (numstreams e)) l).
      split; simpl_Forall; eauto.
      rewrite concat_map, map_map, <- flat_map_repeat, flat_map_concat_map.
      f_equal; auto using map_ext, map_repeat.
    + eapply Forall2t_forall2 with (b := Streams.const absent);
        rewrite ?repeat_length; intros; auto.
      rewrite nth_repeat, map_map; simpl.
      apply merge_spec; intros.
      left; repeat split; auto using const_nth.
      simpl_Forall; subst.
      rewrite nth_repeat_in; simpl; auto using const_nth.
      now rewrite <- annots_numstreams, <- length_typesof_annots.
  - (* Eapp *)
    eapply Sapp with
      (ss := List.map (fun e => repeat (Streams.const absent) (numstreams e)) es);
      simpl; eauto using bools_ofs_empty.
    + rewrite Forall2_map_2. apply Forall2_same.
      apply Forall_impl_inside with (P := restr_exp) in H; auto.
      apply Forall_impl_inside with (P := wt_exp _ _) in H; auto.
    + intro k.
      rewrite <- flat_map_concat_map, flat_map_repeat, 2 map_repeat.
      rewrite <- annots_numstreams, <- length_typesof_annots.
      eapply sem_node_morph in HG; eauto.
      (* in *)
      take (Forall2 _ _ (n_in n)) and apply Forall2_length in it as ->.
      destruct k;
        [now setoid_rewrite mask_false_0 | now setoid_rewrite mask_false_S].
      (* out *)
      take (Forall2 _ _ (n_out n)) and apply Forall2_length in it.
      setoid_rewrite it.
      destruct k;
        [now setoid_rewrite mask_false_0 | now setoid_rewrite mask_false_S].
Qed.

(* TODO: comprendre pourquoi on a besoin de ces deux cons-là *)
Global Instance Forall2_Proper A B :
  Proper ((eq ==> eq ==> Basics.impl) ==> eq ==> eq ==> Basics.impl)
    (Forall2(A:=A) (B:=B)).
Proof.
  repeat intro; subst.
  induction H2; constructor; auto.
  eapply H; eauto.
Qed.
Global Instance sem_exp_Proper (G : global) H :
  Proper (@EqSt bool ==> (@eq exp  ==> eq ==> Basics.impl))
    (sem_exp G H).
Proof.
  intros ?? Heq  ??? ??? Hsem; subst.
  now rewrite <- Heq.
Qed.

(***************************************
 avec Ordered_nodes ça semble impossible car on ne peut pas avoir
 wt_node à chaque fois
Voir avec Basile :
 pourquoi wt_global -> Ordered_nodes ?
On voudrait un wt_global plus faible mais plus
 facile à manipuler (pas de Forall' !!)
on réserve le Ordered_nodes pour les raisonnements inductifs
 *)
Lemma sem_global_absent :
  forall (G : global),
    restr_global G ->
    wt_global G ->
    sem_global_abs G.
Proof.
  intros [tys exts nds] Hr Hwt.
  induction nds as [| n' nds]; intros f n Hfind ??. inv Hfind.
  apply wt_global_wl_global in Hwt as Hord.
  apply wl_global_Ordered_nodes in Hord.
  destruct (ident_eq_dec f (n_name n')); subst.
  rewrite find_node_now in Hfind; auto; inv Hfind.
  { (* TODO: en extraire un lemme, mais comment ? *)
  subst ss os.
  eapply Snode with (H := fun _ => Some (Streams.const absent));
    eauto using find_node_now.
  + (* ins *)
    apply Forall2_forall2; unfold idents.
    rewrite map_length, repeat_length.
    split; intros; subst; auto.
    econstructor; eauto.
    rewrite nth_repeat_in; now auto.
  + (* outs *)
    apply Forall2_forall2; unfold idents.
    rewrite map_length, repeat_length.
    split; intros; subst; auto.
    econstructor; eauto.
    rewrite nth_repeat_in; now auto.
  + (* équation *)
    apply sem_block_cons'; eauto using find_node_not_Is_node_in, find_node_now.
    inv Hr. take (restr_node _) and inv it.
    apply wt_global_cons in Hwt as Hwt'.
    apply wt_global_uncons in Hwt as (?&?&?& Hwt).
    rewrite <- H in Hwt. inv Hwt.
    take (wt_equation _ _ _) and inv it.
    constructor.
    apply Seq with
      (ss := List.map (fun e => repeat (Streams.const absent) (numstreams e)) es); simpl.
    (* expressions *)
    rewrite clocks_of_false2.
    match goal with H:Forall (wt_exp _ ?Γ) _ |- _=> revert H; generalize Γ end.
    intros; clear dependent n.
    induction es; simpl_Forall; constructor; eauto.
    eapply sem_exp_absent; now eauto.
    (* variables *)
    assert (length xs = list_sum (List.map numstreams es)) as Hl.
    { rewrite <- annots_numstreams, <- length_typesof_annots.
      eauto using Forall2_length. }
    clear - Hl. revert dependent xs.
    induction es; simpl; intros.
    * destruct xs; simpl in *; auto; congruence.
    * apply length_app_decomp in Hl as (xs1 & xs2 & ? & Hl1 & Hl2); subst.
      apply Forall2_app; auto.
      rewrite <- Hl1; clear.
      induction xs1; simpl; constructor; auto.
      now econstructor.
  }
  rewrite find_node_other in Hfind; auto.
  inv Hr; apply wt_global_cons in Hwt.
  unfold sem_global_abs in IHnds.
  apply sem_node_cons'; eauto.
Qed.

End Sem_absent.


(** ** Translation of [DS (sampl value)] to [Stream svalue]  *)

Definition sval_of_sampl : sampl value -> svalue :=
  fun v => match v with
        | pres v => present v
        | abs => absent
        | err e => absent
        end.

Definition S_of_DSv := S_of_DS sval_of_sampl.

Lemma S_of_DSv_eq :
  forall (s : DS (sampl value)) Hs t (Heq : s == t),
  exists Ht,
    S_of_DSv s Hs ≡ S_of_DSv t Ht.
Proof.
  esplit.
  apply (__S_of_DS_eq _ _ Hs _ Heq).
Qed.

(** lift S_of_DSv on lists of streams  *)
Definition Ss_of_nprod {n} (np : @nprod (DS (sampl value)) n)
  (Hinf : forall_nprod (@infinite _) np) : list (Stream svalue).
  induction n as [|[]].
  - exact [].
  - exact [S_of_DSv np Hinf].
  - exact (S_of_DSv (fst np) (proj1 Hinf) :: IHn (snd np) (proj2 Hinf)).
Defined.

Lemma Ss_of_nprod_length :
  forall n (np : nprod n) infn,
    length (Ss_of_nprod np infn) = n.
Proof.
  clear.
  induction n as [|[]]; simpl; eauto.
Qed.

Lemma _Ss_of_nprod_eq :
  forall n (np np' : nprod n) Hinf Hinf',
    np == np' ->
    EqSts (Ss_of_nprod np Hinf) (Ss_of_nprod np' Hinf').
Proof.
  induction n as [|[]]; intros * Heq.
  - constructor.
  - constructor; auto.
    now apply _S_of_DS_eq.
  - apply Dprod_eq_elim_fst in Heq as ?.
    apply Dprod_eq_elim_snd in Heq as ?.
    constructor; simpl; eauto.
    apply _S_of_DS_eq. auto.
    apply IHn. auto.
Qed.

(* utilisation : edestruct (Ss_of_nprod_eq _ Hinf) as [Inf' ->] *)
Corollary Ss_of_nprod_eq :
  forall {n} (np : nprod n) Hinf np',
    np == np' ->
    exists Hinf',
      EqSts (Ss_of_nprod np Hinf) (Ss_of_nprod np' Hinf').
Proof.
  intros * Heq.
  assert (forall_nprod (@infinite _) np') as H by now rewrite <- Heq.
  exists H. now apply _Ss_of_nprod_eq.
Qed.

(* utilisation : edestruct Ss_of_nprod_nth as [Inf' ->] *)
Lemma Ss_of_nprod_nth :
  forall n (np : nprod n) Inf k d s,
    k < n ->
    exists Inf2,
      nth k (Ss_of_nprod np Inf) s ≡ S_of_DSv (get_nth k d np) Inf2.
Proof.
  intros * Hk.
  exists (forall_nprod_k _ _ Inf k d Hk).
  revert_all.
  induction n as [|[]]; intros.
  - inv Hk.
  - assert (k = O) by lia; subst; simpl.
    now apply _S_of_DS_eq.
  - destruct k.
    + now apply _S_of_DS_eq.
    + unshelve rewrite (IHn (snd np) (proj2 Inf) k d s); auto with arith.
      now apply _S_of_DS_eq.
Qed.

Lemma _Ss_app :
  forall n m (np : nprod n) (mp : nprod m) Hnm Hn Hm,
    EqSts (Ss_of_nprod (nprod_app np mp) Hnm)
      ((Ss_of_nprod np Hn) ++ (Ss_of_nprod mp Hm)).
Proof.
  intros.
  induction n as [|[]]; intros; auto.
  - apply _Ss_of_nprod_eq; auto.
  - destruct m.
    + simpl. constructor; auto. now apply _S_of_DS_eq.
    + constructor.
      * now apply _S_of_DS_eq.
      * unshelve eapply IHn. split.
  - constructor. now apply _S_of_DS_eq.
    apply IHn.
Qed.

Corollary Ss_app :
  forall {n m} (np : nprod n) (mp : nprod m) Hnm,
  exists Hn Hm,
    EqSts (Ss_of_nprod (nprod_app np mp) Hnm)
      ((Ss_of_nprod np Hn) ++ (Ss_of_nprod mp Hm)).
Proof.
  intros.
  destruct (app_forall_nprod _ _ _ Hnm) as [Hn Hm].
  exists Hn,Hm.
  apply _Ss_app.
Qed.


(** ** Correspondence of semantic predicate for streams functions *)

(** In the lext lemmas we use the method of coinduction loading from
    "Circular coinduction in Coq using bisimulation-up-to techniques" by
    Endrullis, Hendriks and Bodin.
    Their idea is to push computation/rewriting in the arguments of the
    coinductive predicate instead of performing it at top-level, which
    would breaks Coq guardedness condition. Thus, instead of proving
      forall xs ys, P xs ys
    we prove
      forall xs ys, forall xs' ys', xs ≡ xs' -> ys ≡ ys' -> P xs' ys'
 *)

Lemma ok_const :
  forall c bs Hinf,
    S_of_DSv (sconst (Vscalar (sem_cconst c)) (DS_of_S bs)) Hinf ≡ const bs c.
Proof.
  intros.
  remember_st (S_of_DSv _ Hinf) as xs.
  remember_st (const bs c) as ys.
  revert_all.
  cofix Cof; intros * Eqx ? Eqy.
  destruct xs as [vx xs], ys as [vy ys], bs as [b bs].
  apply S_of_DS_Cons in Eqx as (x & tx & Hxs & Hxvx & itx & Eqx).
  setoid_rewrite unfold_Stream in Eqy.
  setoid_rewrite DS_inv in Hxs at 2; simpl in *.
  unfold sconst in *.
  rewrite MAP_map, Cpo_streams_type.map_eq_cons in Hxs.
  apply Con_eq_simpl in Hxs as [? Heq]; subst; simpl.
  inv Eqy; simpl in *; subst.
  constructor; simpl; cases.
  rewrite (ex_proj2 (S_of_DS_eq _ _ _ _ (symmetry Heq))) in Eqx; eauto.
Qed.

Lemma ok_unop :
  forall op ty (xs : DS (sampl value)),
    let rs := sunop (fun v => sem_unop op v ty) xs in
    forall (xsi : infinite xs)
      (rsi : infinite rs),
      safe_DS rs ->
      lift1 op ty (S_of_DSv xs xsi) (S_of_DSv rs rsi).
Proof.
  intros.
  remember_st (S_of_DSv xs xsi) as xs'.
  remember_st (S_of_DSv rs rsi) as rs'.
  revert_all.
  cofix Cof; intros * Sr ? Eqx ? Eqr.
  destruct xs' as [vx xs'], rs' as [vr rs'].
  apply S_of_DS_Cons in Eqx as (x & tx & Hxs & Hxvx & itx & Eqx).
  apply S_of_DS_Cons in Eqr as (r & tr & Hrs & Hrvr & itr & Eqr).
  subst rs.
  rewrite Hxs, sunop_eq in Hrs, Sr.
  cases_eqn HH; simpl; try now inv Sr.
  all: apply Con_eq_simpl in Hrs as [? Heq]; subst; simpl.
  all: constructor; eauto.
  all: apply DSForall_tl in Sr.
  all: rewrite (ex_proj2 (S_of_DS_eq _ _ _ _ (symmetry Heq))) in Eqr; eauto.
Qed.

Lemma ok_binop :
  forall op ty1 ty2 (xs ys : DS (sampl value)),
    let rs := sbinop (fun v1 v2 => sem_binop op v1 ty1 v2 ty2) xs ys in
    forall (xsi : infinite xs)
      (ysi : infinite ys)
      (rsi : infinite rs),
      safe_DS rs ->
      lift2 op ty1 ty2 (S_of_DSv xs xsi) (S_of_DSv ys ysi) (S_of_DSv rs rsi).
Proof.
  intros.
  remember_st (S_of_DSv xs xsi) as xs'.
  remember_st (S_of_DSv ys ysi) as ys'.
  remember_st (S_of_DSv rs rsi) as rs'.
  revert_all.
  cofix Cof; intros * Sr ? Eqx ? Eqy ? Eqr.
  destruct xs' as [vx xs'], ys' as [vy ys'], rs' as [vr rs'].
  apply S_of_DS_Cons in Eqx as (x & tx & Hxs & Hxvx & itx & Eqx).
  apply S_of_DS_Cons in Eqy as (y & ty & Hys & Hyvy & ity & Eqy).
  apply S_of_DS_Cons in Eqr as (r & tr & Hrs & Hrvr & itr & Eqr).
  subst rs.
  rewrite Hxs, Hys, sbinop_eq in Hrs, Sr.
  cases_eqn HH; simpl; try now inv Sr.
  all: apply Con_eq_simpl in Hrs as [? Heq]; subst; simpl.
  all: constructor; eauto.
  all: apply DSForall_tl in Sr.
  all: rewrite (ex_proj2 (S_of_DS_eq _ _ _ _ (symmetry Heq))) in Eqr; eauto.
Qed.

Lemma ok_fby1 :
  forall v (xs ys : DS (sampl value)),
    let rs := SDfuns.fby1 (Some v) xs ys in
    forall (xsi : infinite xs)
      (ysi : infinite ys)
      (rsi : infinite rs),
      safe_DS rs ->
      fby1 v (S_of_DSv xs xsi) (S_of_DSv ys ysi) (S_of_DSv rs rsi).
Proof.
  intros.
  remember_st (S_of_DSv xs xsi) as xs'.
  remember_st (S_of_DSv ys ysi) as ys'.
  remember_st (S_of_DSv rs rsi) as rs'.
  revert_all.
  cofix Cof; intros * Sr ? Eqx ? Eqy ? Eqr.
  destruct xs' as [vx xs'], ys' as [vy ys'], rs' as [vr rs'].
  apply S_of_DS_Cons in Eqx as (x & tx & Hxs & Hxvx & itx & Eqx).
  apply S_of_DS_Cons in Eqy as (y & ty & Hys & Hyvy & ity & Eqy).
  apply S_of_DS_Cons in Eqr as (r & tr & Hrs & Hrvr & itr & Eqr).
  subst rs.
  rewrite Hxs, Hys, fby1_eq in Hrs.
  destruct x, y; simpl in *; subst.
  all: try apply Con_eq_simpl in Hrs as [? Heq]; subst; simpl.
  (* error cases *)
  all: rewrite Hxs, Hys in *.
  all: rewrite fby1_eq, ?fby1AP_eq in Sr, rsi.
  all: repeat apply DSForall_tl in Sr.
  all: try (rewrite DS_const_eq in Sr; inv Sr; now exfalso).
  all: constructor; rewrite fby1AP_eq in Heq.
  all: rewrite (ex_proj2 (S_of_DS_eq _ _ _ _ (symmetry Heq))) in Eqr; eauto.
Qed.

Lemma ok_fby :
  forall (xs ys : DS (sampl value)),
    let rs := SDfuns.fby xs ys in
    forall (xsi : infinite xs)
      (ysi : infinite ys)
      (rsi : infinite rs),
      safe_DS rs ->
      fby (S_of_DSv xs xsi) (S_of_DSv ys ysi) (S_of_DSv rs rsi).
Proof.
  intros.
  remember_st (S_of_DSv xs xsi) as xs'.
  remember_st (S_of_DSv ys ysi) as ys'.
  remember_st (S_of_DSv rs rsi) as rs'.
  revert_all.
  cofix Cof; intros * Sr ? Eqx ? Eqy ? Eqr.
  destruct xs' as [vx xs'], ys' as [vy ys'], rs' as [vr rs'].
  apply S_of_DS_Cons in Eqx as (x & tx & Hxs & Hxvx & itx & Eqx).
  apply S_of_DS_Cons in Eqy as (y & ty & Hys & Hyvy & ity & Eqy).
  apply S_of_DS_Cons in Eqr as (r & tr & Hrs & Hrvr & itr & Eqr).
  subst rs.
  rewrite Hxs, Hys, fby_eq in Hrs.
  destruct x, y; simpl in *; subst.
  all: try apply Con_eq_simpl in Hrs as [? Heq]; subst; simpl.
  (* error cases *)
  all: rewrite Hxs, Hys in *.
  all: rewrite fby_eq, ?fbyA_eq, ?fby1AP_eq in Sr, rsi.
  all: repeat apply DSForall_tl in Sr.
  all: try (rewrite DS_const_eq in Sr; inv Sr; now exfalso).
  all: constructor; rewrite ?fbyA_eq, ?fby1AP_eq in Heq.
  all: rewrite (ex_proj2 (S_of_DS_eq _ _ _ _ (symmetry Heq))) in Eqr; eauto.
  rewrite <- Eqr, <- Eqx, <- Eqy.
  apply ok_fby1; auto.
Qed.

Lemma ok_when :
  forall k (xs cs : DS (sampl value)),
    let rs := swhenv k xs cs in
    forall (xsi : infinite xs)
      (csi : infinite cs)
      (rsi : infinite rs),
      safe_DS rs ->
      when k (S_of_DSv xs xsi) (S_of_DSv cs csi) (S_of_DSv rs rsi).
Proof.
  intros.
  remember_st (S_of_DSv xs xsi) as xs'.
  remember_st (S_of_DSv cs csi) as cs'.
  remember_st (S_of_DSv rs rsi) as rs'.
  revert_all.
  cofix Cof; intros * Sr ? Eqx ? Eqc ? Eqr.
  destruct xs' as [vx xs'], cs' as [vc cs'], rs' as [vr rs'].
  apply S_of_DS_Cons in Eqx as (x & tx & Hxs & Hxvx & itx & Eqx).
  apply S_of_DS_Cons in Eqc as (c & tc & Hcs & Hcvc & itc & Eqc).
  apply S_of_DS_Cons in Eqr as (r & tr & Hrs & Hrvr & itr & Eqr).
  subst rs.
  unfold swhenv in *; rewrite Hxs, Hcs, swhen_eq in Hrs.
  cases_eqn HH; simpl in *; subst; try take (Some _ = Some _) and inv it.
  all: try apply Con_eq_simpl in Hrs as [? Heq]; subst; simpl.
  (* error cases *)
  all: rewrite Hxs, Hcs in *.
  all: rewrite swhen_eq in Sr, rsi.
  all: repeat apply DSForall_tl in Sr.
  all: try (rewrite DS_const_eq in Sr; inv Sr; now exfalso).
  2: assert (k = e) by (now apply Nat.eqb_eq); subst.
  all: econstructor; auto using (proj1 (Nat.eqb_neq _ _)).
  all: rewrite (ex_proj2 (S_of_DS_eq _ _ _ _ (symmetry Heq))) in Eqr; eauto.
  all: cases; try easy; inv Sr; eauto.
Qed.


(** ** Fonctions pour passer d'un [DS_prod SI] à un Str.history *)

Definition hist_of_envs
  (ins : list ident)
  (envI : DS_prod SI) (InfI : all_infinite envI)
  (env : DS_prod SI) (Inf : all_infinite env) : Str.history :=
  fun x => Some (if mem_ident x ins
              then S_of_DSv (envI x) (InfI x)
              else S_of_DSv (env x) (Inf x)).

Lemma sem_hist_of_envs : forall ins envI InfI env Inf x Infx,
    sem_var (hist_of_envs ins envI InfI env Inf) x
      (S_of_DSv (denot_var ins envI env x) Infx).
Proof.
  intros.
  unfold hist_of_envs.
  econstructor; eauto.
  cases_eqn HH; apply _S_of_DS_eq.
  all: unfold denot_var; cases; congruence.
Qed.

Lemma _hist_of_envs_eq :
  forall ins envI HinfI env Hinf env' Hinf',
    env == env' ->
    FEnv.Equiv (EqSt (A:=svalue)) (hist_of_envs ins envI HinfI env Hinf) (hist_of_envs ins envI HinfI env' Hinf').
Proof.
  intros * Heq.
  unfold hist_of_envs.
  constructor.
  cases; apply _S_of_DS_eq; auto.
Qed.

(* utilisation : edestruct (hist_of_envs_eq env Hinf) as [Hinf' ->] *)
Corollary hist_of_envs_eq :
  forall ins envI HinfI env Hinf env',
    env == env' ->
    exists Hinf',
    FEnv.Equiv (EqSt (A:=svalue)) (hist_of_envs ins envI HinfI env Hinf) (hist_of_envs ins envI HinfI env' Hinf').
Proof.
  intros * Heq.
  esplit.
  unshelve (rewrite _hist_of_envs_eq; eauto; reflexivity).
  eapply all_infinite_Oeq_compat; eauto.
Qed.

Lemma sem_var_ins : forall ins envI InfI env Inf x s,
    In x ins ->
    s ≡ S_of_DSv (envI x) (InfI x) ->
    sem_var (hist_of_envs ins envI InfI env Inf) x s.
Proof.
  intros * Hin Heq.
  econstructor; try reflexivity.
  cases_eqn Hmem; auto.
  now apply mem_ident_false in Hmem.
Qed.

Lemma sem_var_nins : forall ins envI InfI env Inf x s,
    ~ In x ins ->
    s ≡ S_of_DSv (env x) (Inf x) ->
    sem_var (hist_of_envs ins envI InfI env Inf) x s.
Proof.
  intros * Hin Heq.
  econstructor; try reflexivity.
  cases_eqn Hmem; auto.
  now apply mem_ident_spec in Hmem.
Qed.


(** Hypothèse sur les entrées d'un nœud : elles doivent être bien typées
    et respecter leurs annotations d'horloge. *)
Definition correct_ins (n : node) envI bs :=
  let ins := List.map fst n.(n_in) in
  let Γ := senv_of_inout (n.(n_in) ++ n.(n_out)) in
  env_correct Γ ins envI bs 0.


Section Ok_node.

Variables
  (G : global)
  (envG : Dprodi FI).

(** Toutes les hypothèses de section sur G et envG seront obtenues par
    récurrence dans ok_global. *)

Hypothesis (Wtg : wt_global G).
Hypothesis (Wcg : wc_global G).
Hypothesis (Hrg : restr_global G).

Hypothesis InfG :
  forall envI f, all_infinite envI -> all_infinite (envG f envI).

Hypothesis CorrectG :
    forall f n envI,
      find_node f G = Some n ->
      let ins := List.map fst n.(n_in) in
      let Γ := senv_of_inout (n.(n_in) ++ n.(n_out)) in
      forall bs, bss ins envI <= bs ->
      env_correct Γ ins envI bs 0 ->
      env_correct Γ ins envI bs (envG f envI).

Hypothesis Hnode :
  forall f n (ss : nprod (length (n_in n))),
    find_node f G = Some n ->
    let ins := idents (n_in n) in
    let envI := env_of_np ins ss in
    let os := np_of_env (idents (n_out n)) (envG f envI) in
    correct_ins n envI (bss ins envI) ->
    forall infI infO,
      sem_node G f (Ss_of_nprod ss infI) (Ss_of_nprod os infO).


Lemma wc_env_in :
  forall f (n : node),
    find_node f G = Some n ->
    wc_env (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)).
Proof.
  intros * Hfind.
  now destruct (wc_find_node _ _ _ Wcg Hfind) as (?&?&?&?).
Qed.

Lemma Ss_exps :
  forall G ins envG envI bs env es Hinf Infe,
    EqSts (Ss_of_nprod (denot_exps G ins es envG envI bs env) Hinf)
      (flat_map (fun e => Ss_of_nprod (denot_exp G ins e envG envI bs env) (Infe e)) es).
Proof.
  induction es; intros; simpl.
  constructor.
  edestruct (Ss_of_nprod_eq _ Hinf) as [Inf' ->].
  { rewrite denot_exps_eq; reflexivity. }
  setoid_rewrite (ex_proj2 (ex_proj2 (Ss_app _ _ _))).
  apply app_EqSts; auto.
  now apply _Ss_of_nprod_eq.
Qed.

(** Deux tactiques bien pratiques pour la suite *)

(* C'est souvent une bonne idée de généraliser les termes [infinite_exp]
   car ça élimine une dépendance sur [denot_exp]. *)
Ltac gen_infinite_exp :=
  repeat (
  simpl; (* important, même si l'action n'est pas visible *)
  let f := fresh "Inf" in
  match goal with
  | |- context [ infinite_exp ?H1 ?H2 ?H3 ?H4 ?H5 ?H6 ?H7 ?H8 ?H9 ?H10 ?H11 ] =>
      generalize (infinite_exp H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11) as f
  | |- context [ infinite_exps ?H1 ?H2 ?H3 ?H4 ?H5 ?H6 ?H7 ?H8 ?H9 ?H10 ?H11 ] =>
      generalize (infinite_exps H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11) as f
  end).

(* Isole un terme [denot_exp ...] dans une égalisé [Hse] afin de pouvoir
   réécrire [denot_exp_eq] dedans, sans complications liées à S_of_DSv. *)
Ltac save_denot_exp se Hse :=
  gen_infinite_exp;
  simpl; (* important, même si l'action n'est pas visible *)
  match goal with
  | |- context [ ?f1 (?f2 (?f3 (?f4 (denot_exp ?e1 ?e2 ?e3) ?e4) ?e5) ?e6) ?e7 ] =>
      remember (f1 (f2 (f3 (f4 (denot_exp e1 e2 e3) e4) e5) e6) e7)
      as se eqn:Hse
  end.

(* Une fois [denot_exp_eq] appliqué, on voit souvent apparaître [denot_exps]
   sur les sous-expressions. Si l'hypothèse de récurrence est déjà dégrossie,
   il peut être utile d'abstraire les sous-flots avec ça : *)
Ltac gen_sub_exps :=
  gen_infinite_exp;
  simpl; (* important, même si l'action n'est pas visible *)
  repeat match goal with
  | |- context [ ?f1 (?f2 (?f3 (?f4 (denot_exps ?e1 ?e2 ?e3) ?e4) ?e5) ?e6) ?e7 ] =>
      generalize (f1 (f2 (f3 (f4 (denot_exps e1 e2 e3) e4) e5) e6) e7)
  | |- context [ ?f1 (?f2 (?f3 (?f4 (denot_exp ?e1 ?e2 ?e3) ?e4) ?e5) ?e6) ?e7 ] =>
      generalize (f1 (f2 (f3 (f4 (denot_exp e1 e2 e3) e4) e5) e6) e7)
  end.


(** On traite à part le cas des appels de nœuds car il apparaît à la fois
    dans une expression Eapp et dans une équation de type xs=[Eapp].
    Dand les deux cas seules les hypothèses du lemme suivant sont
    nécessaires. En particulier, rien à dire sur la dépendance entre les
    horloges de l'équation et de l'application. *)
Lemma ok_sem_Eapp :
  forall Γ ins env Inf envI InfI bs bsi,
    env_correct Γ ins envI bs env ->
    let H := (hist_of_envs ins envI InfI env Inf, FEnv.empty _) in
    forall f n es anns bck sub,
      Forall2 (fun (et : type) '(_, (t, _, _)) => et = t) (typesof es) (n_in n) ->
      Forall2 (WellInstantiated bck sub) (List.map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) (nclocksof es) ->
      wc_env (map (fun '(x, (_, ck, _)) => (x, ck)) n.(n_in)) ->
      find_node f G = Some n ->
      length (anns) = length (n_out n) ->
      Forall restr_exp es ->
      Forall (wt_exp G Γ) es ->
      Forall (wc_exp G Γ) es ->
      Forall (op_correct_exp G ins envG envI bs env) es ->
      let ss := denot_exps G ins es envG envI bs env in
      let os := denot_exp G ins (Eapp f es [] anns) envG envI bs env in
      let sss := map (fun e => Ss_of_nprod
                              (denot_exp G ins e envG envI bs env)
                              (infinite_exp G ins envI envG bs env InfG bsi InfI Inf e)) es in
      forall infO,
        Forall2 (sem_exp G H (S_of_DS id bs bsi)) es sss ->
        sem_exp G H (S_of_DS id bs bsi) (Eapp f es [] anns) (Ss_of_nprod os infO).
Proof.
  intros ?? env * Hc * WTi WIi WCi Hfind Hlo Hr Hwt Hwc Hoc ???? Hsem.
  apply Forall2_length in WTi as Hli.
  rewrite length_typesof_annots in Hli.
  econstructor; eauto using bools_ofs_empty.
  clear Hsem. intros [].
  - (* k = 0, c'est intéressant *)
    setoid_rewrite masks_false_0.
    rewrite annots_numstreams in Hli.
    (* hypothèse principale pour Hnode : *)
    assert (Hins : correct_ins n (env_of_np (idents (n_in n)) ss)
                     (bss (idents (n_in n)) (env_of_np (idents (n_in n)) ss))).
    { unfold correct_ins.
      pose proof (nclocksof_sem G envG ins envI bs env es) as Ncs.
      edestruct safe_exps_ with (es := es) as (sTy & sCl & sEf); eauto.
      rewrite clocksof_nclocksof in sCl.
      eapply safe_inst_in with (ss := ss) in Hli as Hec; eauto.
      eapply env_correct_morph in Hec; eauto 1.
      (* équivalence des horloges *)
      apply env_correct_decompose in Hec as (?& Hcl &?).
      apply bss_le_bs in Hcl as Hbs; auto.
      apply infinite_le_eq in Hbs as ->; auto.
      now apply bss_inf, env_of_np_inf, infinite_exps.
    }
    subst sss.
    unshelve rewrite <- flat_map_concat_map, <- Ss_exps;
      auto using DS_of_S_inf, infinite_exps.
    (* il faut aussi que ss soit de type nprod (length n_in n) *)
    subst ss.
    revert infO Hins. revert os.
    save_denot_exp se Hse.
    setoid_rewrite denot_exp_eq in Hse; revert Hse; simpl.
    gen_sub_exps.
    rewrite Hfind, Hli.
    rewrite <- (map_length fst) in Hlo.
    unfold idents, eq_rect.
    cases; intros; subst; try congruence; eauto.
  - (* k <> 0, on utilise sem_global_absent *)
    setoid_rewrite masks_false_S.
    subst sss; simpl.
    rewrite 2 map_ignore, concat_length_sum, map_map.
    setoid_rewrite Ss_of_nprod_length.
    rewrite <- annots_numstreams, Hli, Hlo.
    apply sem_global_absent; auto.
Qed.

(* ce morphisme est ad hoc, pas sûr qu'il faille l'ajouter à CoindStreams *)
Global Add Parametric Morphism k t : (fun s => when k s t)
       with signature (@EqSt _) ==> (@EqSt _) ==> Basics.impl
         as  when_morph2.
Proof.
  intros ?? HH ?? -> ?.
  now rewrite <- HH.
Qed.

Lemma ok_sem_exp :
  forall Γ ins env Inf envI InfI bs bsi,
    env_correct Γ ins envI bs env ->
    let H := (hist_of_envs ins envI InfI env Inf, FEnv.empty _) in
    forall (e : exp) (Hwt : wt_exp G Γ e) (Hwc : wc_exp G Γ e) (Hr : restr_exp e),
      op_correct_exp G ins envG envI bs env e ->
      let ss := denot_exp G ins e envG envI bs env in
      let Infe := infinite_exp _ _ _ _ _ _ InfG bsi InfI Inf _ in
      sem_exp G H (S_of_DS id bs bsi) e (Ss_of_nprod ss Infe).
Proof.
  intros ?? env * Hc H.
  induction e using exp_ind2; intros * ??? Hoc ss Infe.
  all: inv Hr; subst ss; simpl.
  - (* Econst *)
    constructor.
    edestruct (S_of_DSv_eq _ Infe) as [Infe' ->].
    { rewrite denot_exp_eq. reflexivity. }
    unshelve rewrite <- ok_const; auto using sconst_inf, DS_of_S_inf.
    apply _S_of_DS_eq.
    now rewrite DS_of_S_of_DS.
  - (* Evar *)
    constructor; simpl.
    edestruct (S_of_DSv_eq _ Infe) as [Infe' ->].
    { rewrite denot_exp_eq. reflexivity. }
    apply sem_hist_of_envs.
  - (* Eunop *)
    eapply safe_exp in Hoc as Hs; eauto using restr_exp.
    apply wt_exp_wl_exp in Hwt as Hwl.
    inv Hwt. inv Hwc. inv Hoc. inv Hwl.
    edestruct (Ss_of_nprod_eq _ Infe) as [Hinf0 HH].
    { setoid_rewrite denot_exp_eq. reflexivity. }
    rewrite HH; clear HH.
    rewrite denot_exp_eq in Hs.
    revert Hinf0 IHe Hs; simpl.
    gen_sub_exps.
    take (numstreams e = 1) and rewrite it.
    take (typeof e = _) and rewrite it.
    econstructor; eauto using ok_unop.
  - (* Ebinop *)
    eapply safe_exp in Hoc as Hs; eauto using restr_exp.
    apply wt_exp_wl_exp in Hwt as Hwl.
    inv Hwt. inv Hwc. inv Hoc. inv Hwl.
    edestruct (Ss_of_nprod_eq _ Infe) as [Hinf0 HH].
    { setoid_rewrite denot_exp_eq. reflexivity. }
    rewrite HH; clear HH.
    rewrite denot_exp_eq in Hs.
    revert Hinf0 IHe1 IHe2 Hs; simpl.
    gen_sub_exps.
    take (numstreams e1 = 1) and rewrite it.
    take (numstreams e2 = 1) and rewrite it.
    take (typeof e1 = _) and rewrite it.
    take (typeof e2 = _) and rewrite it.
    econstructor; eauto using ok_binop.
  - (* Efby *)
    eapply safe_exp in Hoc as Hs; eauto using restr_exp.
    apply wt_exp_wl_exp in Hwt as Hwl.
    inv Hwt. inv Hwc. inv Hoc. inv Hwl.
    apply Forall_impl_inside with (P := wt_exp _ _) in H0, H1; auto.
    apply Forall_impl_inside with (P := wc_exp _ _) in H0, H1; auto.
    apply Forall_impl_inside with (P := restr_exp) in H0, H1; auto.
    apply Forall_impl_inside with (P := op_correct_exp _ _ _ _ _ _) in H0, H1; auto.
    econstructor; simpl in *.
    + erewrite Forall2_map_2, <- Forall2_same. apply H0.
    + erewrite Forall2_map_2, <- Forall2_same. apply H1.
    + rewrite <- 2 flat_map_concat_map.
      unshelve rewrite <- 2 Ss_exps; auto using DS_of_S_inf, infinite_exps.
      revert Infe Hs.
      save_denot_exp se Hse.
      setoid_rewrite denot_exp_eq in Hse; revert Hse; simpl.
      gen_sub_exps.
      rewrite annots_numstreams in *.
      unfold eq_rect.
      cases; intros; subst; try congruence.
      clear - Hs.
      induction (list_sum (map numstreams es)) as [|[]];
        eauto using Forall3_nil, Forall3_cons, ok_fby.
      inv Hs.
      constructor; [ simpl; now apply ok_fby | now apply IHn ].
  - (* Ewhen *)
    destruct x as [x ty].
    eapply safe_exp in Hoc as Hs; eauto using restr_exp.
    apply wt_exp_wl_exp in Hwt as Hwl.
    inv Hwt. inv Hwc. inv Hoc. inv Hwl.
    apply Forall_impl_inside with (P := wt_exp _ _) in H0; auto.
    apply Forall_impl_inside with (P := wc_exp _ _) in H0; auto.
    apply Forall_impl_inside with (P := restr_exp) in H0; auto.
    apply Forall_impl_inside with (P := op_correct_exp _ _ _ _ _ _) in H0; auto.
    econstructor; simpl.
    + erewrite Forall2_map_2, <- Forall2_same. apply H0.
    + unshelve apply sem_hist_of_envs; auto using denot_var_inf.
    + rewrite <- flat_map_concat_map.
      unshelve rewrite <- Ss_exps; auto using DS_of_S_inf, infinite_exps.
      revert Infe Hs.
      save_denot_exp se Hse.
      setoid_rewrite denot_exp_eq in Hse; revert Hse; simpl.
      gen_sub_exps.
      rewrite annots_numstreams in *.
      unfold eq_rect.
      cases; intros; subst; try congruence.
      clear - Hs.
      induction (list_sum (map numstreams es)) as [|[]]; eauto using Forall2, ok_when.
      inv Hs.
      constructor; [ now apply ok_when | now apply IHn ].
  - (* Eapp *)
    eapply safe_exp in Hoc as Hs; eauto using restr_exp.
    apply wt_exp_wl_exp in Hwt as Hwl.
    inv Hwt. inv Hwc. inv Hoc. inv Hwl.
    repeat take (find_node _ _ = _) and rewrite it in *.
    repeat take (Some _ = Some _) and inv it.
    apply Forall_impl_inside with (P := wt_exp _ _) in H0; auto.
    apply Forall_impl_inside with (P := wc_exp _ _) in H0; auto.
    apply Forall_impl_inside with (P := restr_exp) in H0; auto.
    apply Forall_impl_inside with (P := op_correct_exp _ _ _ _ _ _) in H0; auto.
    eapply ok_sem_Eapp; eauto using wc_env_in.
    rewrite Forall2_map_2, <- Forall2_same. apply H0.
Qed.

Corollary ok_sem_exps :
  forall Γ ins env Inf envI InfI bs bsi,
    env_correct Γ ins envI bs env ->
    let H := (hist_of_envs ins envI InfI env Inf, FEnv.empty _) in
    forall es,
      Forall restr_exp es ->
      Forall (wt_exp G Γ) es ->
      Forall (wc_exp G Γ) es ->
      Forall (op_correct_exp G ins envG envI bs env) es ->
      Forall2 (sem_exp G H (S_of_DS id bs bsi)) es
        (map (fun e => Ss_of_nprod (denot_exp G ins e envG envI bs env)
                      (infinite_exp G ins envI envG bs env InfG bsi InfI Inf e)) es).
Proof.
  intros.
  apply Forall2_forall2; split.
  { now rewrite map_length. }
  intros d1 d2 k ?? Hk ??; subst.
  unshelve erewrite map_nth'; auto.
  eapply ok_sem_exp; eauto.
  all: apply (proj1 (Forall_nth _ _)); eauto.
Qed.

Lemma ok_sem_equation :
  forall Γ xs es ins envI bs bsi,
    Forall restr_exp es ->
    wc_equation G Γ (xs,es) ->
    wt_equation G Γ (xs,es) ->
    NoDup (ins ++ xs) ->
    let env := FIXP _ (denot_equation G ins (xs,es) envG envI bs) in
    env_correct Γ ins envI bs env ->
    Forall (op_correct_exp G ins envG envI bs env) es ->
    forall InfI Inf,
    let H := (hist_of_envs ins envI InfI env Inf, FEnv.empty _) in
    sem_equation G H (S_of_DS id bs bsi) (xs,es).
Proof.
  intros * Hr Wc Wt Nd env Hc Oc ???.
  unshelve eapply Seq with
    (ss := map (fun e => Ss_of_nprod (denot_exp G ins e envG envI bs env) _) es).
  { eapply infinite_exp; eauto using DS_of_S_inf. }
  - (* sem_exp *)
    inv Wt. inv Wc; eauto using ok_sem_exps.
    (* reste le cas d'un appel dépendant, à la mano *)
    constructor; auto.
    repeat take (Forall _ [_]) and inv it.
    take (wt_exp _ _ _) and inv it.
    take (op_correct_exp _ _ _ _ _ _ _) and inv it.
    take (restr_exp _) and inv it.
    take (find_node _ _ = _) and rewrite it in *.
    take (Some _ = Some _) and inv it.
    eapply ok_sem_Eapp; eauto using wc_env_in, ok_sem_exps, Forall2_length.
  - (* sem_var *)
    subst H; simpl.
    unshelve rewrite <- flat_map_concat_map, <- Ss_exps; eauto using infinite_exps.
    edestruct (hist_of_envs_eq ) as [Inf2 ->].
    { unfold env. rewrite FIXP_eq. fold env. apply denot_equation_Oeq. }
    assert (length xs = list_sum (map numstreams es)) as Hl.
    { rewrite <- annots_numstreams, <- length_typesof_annots.
      inv Wt. eauto using Forall2_length. }
    apply Forall2_forall2; rewrite Ss_of_nprod_length; split; intros; subst; auto.
    rewrite Permutation_app_comm in Nd.
    apply sem_var_nins; eauto using NoDup_app_In, nth_In.
    edestruct Ss_of_nprod_nth as [Inf3 ->]; try lia.
    apply _S_of_DS_eq.
    erewrite denot_var_nins, env_of_np_nth; eauto using NoDup_app_In, nth_In.
    apply mem_nth_nth; eauto using NoDup_app_l.
Qed.


(** Correspondance clocks_of/bss *)

Lemma ac_AC :
  forall s Inf,
    abstract_clock (S_of_DSv s Inf) ≡ S_of_DS id (AC s) (map_inf _ _ _ _ Inf).
Proof.
  clear.
  intros.
  match goal with
  | |- ?tt ≡ ?uu => remember_st tt as t; remember_st uu as u
  end.
  revert_all.
  cofix Cof; intros s Inf t Ht u Hu.
  destruct t, u.
  apply infinite_decomp in Inf as HH.
  destruct HH as (x & s' & Hs & Inf2).
  destruct (S_of_DSv_eq _ Inf _ Hs) as [Inf3 HH].
  rewrite HH in Ht; clear HH.
  setoid_rewrite S_of_DS_cons in Ht.
  edestruct (S_of_DS_eq id (AC s)) as [Inf4 HH]. { now rewrite Hs, AC_cons. }
  rewrite HH in Hu; clear HH.
  cases; rewrite S_of_DS_cons in Hu; inv Hu; inv Ht; simpl in *; subst.
  all: constructor; simpl; auto.
  all: eapply Cof; eauto; rewrite <- H0; eauto using _S_of_DS_eq.
Qed.

Lemma zip_zipWith :
  forall A B C (f : A -> B -> C),
    forall x y Infx Infy Infr,
      zipWith f (S_of_DS id x Infx) (S_of_DS id y Infy) ≡ S_of_DS id (ZIP f x y) Infr.
Proof.
  clear.
  intros.
  remember_st (S_of_DS id x Infx) as xs.
  remember_st (S_of_DS id y Infy) as ys.
  remember_st (S_of_DS id _ Infr) as rs.
  revert_all; cofix Cof; intros.
  destruct xs as [vx xs], ys as [vy ys], rs as [vr rs].
  apply S_of_DS_Cons in Hxs as (vx' & xs' & Hx & Hvx & Infx' & Hxs).
  apply S_of_DS_Cons in Hys as (vy' & ys' & Hy & Hvy & Infy' & Hys).
  apply S_of_DS_Cons in Hrs as (vr' & rs' & Hr & Hvr & Infr' & Hrs).
  rewrite Hx, Hy, zip_cons in Hr.
  apply Con_eq_simpl in Hr as [].
  constructor; simpl.
  - subst; auto.
  - unshelve eapply Cof; eauto.
    { eapply infinite_morph; eauto. }
    rewrite <- Hrs.
    now apply _S_of_DS_eq.
Qed.

Lemma _clocks_of_bss :
  forall l (np : nprod (length l)) Inf Infb,
    NoDup l ->
    clocks_of (Ss_of_nprod np Inf) ≡
      S_of_DS id (bss l (env_of_np l np)) Infb.
Proof.
  clear.
  induction l as [| x [| y l]]; intros * ND.
  - rewrite clocks_of_nil.
    unshelve rewrite (const_DS_const id false); auto.
    apply _S_of_DS_eq; auto.
  - simpl.
    rewrite clocks_of_ac, ac_AC.
    apply _S_of_DS_eq, map_eq_compat.
    setoid_rewrite env_of_np_eq; simpl.
    cases_eqn HH; congruence.
  - inv ND.
    setoid_rewrite clocks_of_cons.
    unshelve setoid_rewrite (IHl (snd np)); auto.
    { inv Inf. now apply bss_inf, env_of_np_inf. }
    unshelve rewrite ac_AC, zip_zipWith.
    { inv Inf. apply zip_inf. apply map_inf; auto.
      now apply bss_inf, env_of_np_inf. }
    apply _S_of_DS_eq.
    setoid_rewrite bss_cons at 2.
    rewrite env_of_np_eq; simpl (mem_nth _ _).
    destruct (ident_eq_dec _ _); try congruence.
    setoid_rewrite bss_switch_env at 2; auto.
    intros; apply env_of_np_tl; intro; congruence.
Qed.

Corollary clocks_of_bss :
  forall l (np : nprod (length l)) Inf,
    NoDup l ->
    exists Infb,
    clocks_of (Ss_of_nprod np Inf) ≡
      S_of_DS id (bss l (env_of_np l np)) Infb.
Proof.
  intros.
  exists (bss_inf l _ (env_of_np_inf _ _ _ Inf)).
  apply _clocks_of_bss; auto.
Qed.


(** Node semantics  *)

Lemma nodup_equation :
  forall (n : node),
    match n_block n with
    | Beq (xs, _) => NoDup (List.map fst n.(n_in) ++ xs)
    | _ => True (* TODO *)
    end.
Proof.
  destruct n; simpl in *.
  destruct n_defd0 as (xs & Vd & Hxs).
  destruct n_nodup0 as [ND].
  cases; simpl in *.
  inversion Vd; subst.
  now rewrite Hxs, <- map_app, <- fst_NoDupMembers.
Qed.

(** Pour pouvoir utiliser InfG, CorrectG, Hnode, on considère
 * l'ajout d'un nœud en tête de G.(nodes). *)
Lemma ok_sem_node :
  forall (n : node),
    let '(Global tys exts nds) := G in
    Ordered_nodes (Global tys exts (n :: nds)) ->
    restr_node n ->
    wc_node G n ->
    wt_node G n ->
    let f := n_name n in
    let Γ := senv_of_inout (n_in n ++ n_out n) in
    let ins := idents (n_in n) in
    forall (ss : nprod (length (n_in n))),
    let envI := env_of_np ins ss in
    let bs := bss ins envI in
    let envn := FIXP _ (denot_node G n envG envI) in
    let os := np_of_env (idents (n_out n)) envn in
    env_correct Γ ins envI bs envn ->
    op_correct G ins envG envI bs envn n ->
    all_infinite envn ->
    forall infI infO,
      sem_node (Global tys exts (n :: nds)) f (Ss_of_nprod ss infI) (Ss_of_nprod os infO).
Proof.
  (* on pose ok_sem_equation car une fois G détruit, impossible *)
  pose proof (ok_sem_equation) as Hequ.
  destruct G as [tys exts nds].
  intros n Hord Hr Wc Wt ???????? Hco Hoc Infn ??.
  pose (InfI := env_of_np_inf ins _ _ infI).
  epose (H := hist_of_envs ins envI InfI _ Infn).
  eapply Snode with (H := H); eauto using find_node_now.
  - (* sem_var in *)
    subst H envI.
    apply Forall2_forall2.
    split. { rewrite Ss_of_nprod_length. now setoid_rewrite map_length. }
    intros; subst.
    assert (Hlen := H).
    setoid_rewrite map_length in Hlen.
    apply sem_var_ins; auto using nth_In.
    edestruct Ss_of_nprod_nth as [Inf2 ->]; auto using errTy.
    apply _S_of_DS_eq.
    erewrite env_of_np_nth; eauto.
    apply mem_nth_nth; auto using node_NoDup_in.
  - (* sem_var out *)
    subst H os.
    apply Forall2_forall2.
    split. { rewrite Ss_of_nprod_length. now setoid_rewrite map_length. }
    intros; subst.
    assert (Hlen := H).
    setoid_rewrite map_length in Hlen.
    apply sem_var_nins.
    { intro. eapply (not_in_out n); eauto using nth_In. }
    unshelve edestruct Ss_of_nprod_nth as [Inf2 ->]; auto using errTy.
    apply _S_of_DS_eq.
    erewrite nth_np_of_env; auto.
  - (* sem_block *)
    apply sem_block_cons'; eauto using find_node_not_Is_node_in, find_node_now.
    inv Wc. inv Wt. inv Hr.
    pose proof (nodup_equation n) as NDi.
    unfold op_correct in Hoc.
    take (_ = n_block _) and rewrite <- it in *.
    destruct_conjs.
    take (wt_block _ _ _) and inv it.
    take (wc_block _ _ _) and inv it.
    (* simplification de envn *)
    (* FIXME: revert dependent envn ne conserve pas la définition
     * https://github.com/coq/coq/issues/15817 *)
    revert infO Hco Hoc H. revert os Infn. revert envn.
    rewrite denot_node_eq. unfold denot_block, op_correct.
    take (_ = n_block _) and rewrite <- it.
    (* on veut que ss soit du type (nprod (length idents (n_in n))) *)
    assert (length (idents (n_in n)) = length (n_in n)) as Hl
        by now setoid_rewrite map_length.
    revert dependent ss; rewrite <- Hl; intros.
    edestruct clocks_of_bss as [Inf ->]; eauto using bss_inf, NoDup_app_l.
    constructor; eauto.
Qed.

End Ok_node.


Theorem _ok_global :
  forall (HasCausInj : forall (Γ : static_env) (x cx : ident), HasCaus Γ x cx -> x = cx),
  forall G,
    restr_global G ->
    wt_global G ->
    wc_global G ->
    op_correct_global G ->
    Forall node_causal (nodes G) ->
    forall f n (ss : nprod (length (n_in n))),
      find_node f G = Some n ->
      let ins := idents (n_in n) in
      let envI := env_of_np ins ss in
      let os := np_of_env (idents (n_out n)) (denot_global G f envI) in
      let bs := bss ins envI in
      correct_ins n envI bs ->
      forall InfSs InfO,
        sem_node G f (Ss_of_nprod ss InfSs) (Ss_of_nprod os InfO).
Proof.
  intros ?? Rg Wtg Wcg Ocg Causg ??? Hfind ???? Hins ??.
  unfold op_correct_global in Ocg.
  assert (Ordered_nodes G) as Hord.
  { now apply wl_global_Ordered_nodes, wt_global_wl_global. }
  pose proof (SafeG := safe_prog G Rg Wtg Wcg Ocg).
  remember (denot_global G) as envG eqn:HG.
  assert (InfG : forall f envI,
             all_infinite envI ->
             all_infinite (envG f envI)).
  { subst envG. eauto using denot_inf. }
  assert (HenvG : forall f nd envI,
             find_node f G = Some nd ->
             envG f envI == FIXP _ (denot_node G nd envG envI)).
  { intros * Hf; subst.
    unfold denot_global.
    now rewrite <- PROJ_simpl, FIXP_eq, PROJ_simpl, denot_global_eq, Hf at 1. }
  (* HenvG est tout ce qu'il faut savoir sur la définition de envG *)
  clear HG.
  revert dependent n. revert f.
  destruct G as [tys exts nds].
  induction nds as [|a nds]; intros. { inv Hfind. }
  destruct (ident_eq_dec (n_name a) f); subst.
  - (* cas du nœud courant *)
    rewrite find_node_now in Hfind; auto; inv Hfind.
    edestruct (Ss_of_nprod_eq _ InfO) as [Inf3 ->].
    { subst os.
      rewrite HenvG, <- denot_node_cons;
        eauto using find_node_not_Is_node_in, find_node_now.
    }
    apply wt_global_uncons in Wtg as Wtn.
    apply wt_global_cons in Wtg as Wtg'.
    apply wc_global_uncons in Wcg as Wcn.
    inversion Rg; subst.
    inversion Wcg; subst.
    inversion Wtg; subst.
    eapply ok_sem_node in Wtg' as Hsem; eauto using find_node_uncons.
    { eapply Hsem; eauto.
      all: rewrite (denot_node_cons _ n);
        eauto using find_node_not_Is_node_in, find_node_now.
      all: rewrite <- HenvG; auto using find_node_now, env_of_np_inf.
      inv Ocg. apply (op_correct_cons _ n);
        eauto using find_node_not_Is_node_in, find_node_now.
    }
    (* plus qu'à utiliser IHnds *)
    inv Causg. inversion Hord; subst.
    intros; apply IHnds; auto.
    + clear - Ocg Hord. inv Ocg.
      eapply Forall_impl_In; eauto.
      intros * Hin HH ???.
      eapply op_correct_cons in HH; eauto using Ordered_nodes_nin.
    + eauto using find_node_uncons.
    + intros f' ndf' envI' Hfind'.
      eapply find_node_uncons with (nd := n) in Hfind' as ?; auto.
      rewrite HenvG, <- denot_node_cons; eauto using find_node_later_not_Is_node_in.
  - (* cas de récurrence *)
    rewrite find_node_other in Hfind; auto.
    apply sem_node_cons'; auto.
    apply IHnds; auto.
    + now inv Rg.
    + eauto using wt_global_cons.
    + eauto using wc_global_cons.
    + clear - Ocg Hord. inv Ocg.
      eapply Forall_impl_In; eauto.
      intros * Hin HH ???.
      eapply op_correct_cons in HH; eauto using Ordered_nodes_nin.
    + now inv Causg.
    + eauto using Ordered_nodes_cons.
    + intros f' ndf' envI' Hfind'.
      eapply find_node_uncons with (nd := a) in Hfind' as ?; eauto.
    + intros f' ndf' envI' Hfind'.
      eapply find_node_uncons with (nd := a) in Hfind' as ?; auto.
      rewrite HenvG, <- denot_node_cons; eauto using find_node_later_not_Is_node_in.
Qed.

Definition correct_inputs (n : node) (ss : nprod (length (n_in n))) :=
  let ins := idents (n_in n) in
  let envI := env_of_np ins ss in
  let bs := bss ins envI in
  let Γ := senv_of_inout (n.(n_in) ++ n.(n_out)) in
  env_correct Γ ins envI bs 0.

(** Witness of the relational semantics *)
Theorem ok_global :
  forall (HasCausInj : forall (Γ : static_env) (x cx : ident), HasCaus Γ x cx -> x = cx),
  forall G,
    restr_global G ->
    wt_global G ->
    wc_global G ->
    op_correct_global G ->
    Forall node_causal (nodes G) ->
    forall f n, find_node f G = Some n ->
    forall (xs : nprod (length (n_in n))) InfXs,
      correct_inputs n xs ->
      exists (os : nprod ((length (n_out n)))) InfO,
        sem_node G f (Ss_of_nprod xs InfXs) (Ss_of_nprod os InfO).
Proof.
  intros ?? Hr Hwt Hwc Hoc Hcaus Hfind ???? Hins.
  unshelve eapply _ok_global with (InfSs := InfXs) in Hins; eauto.
  { apply forall_np_of_env, denot_inf; auto using env_of_np_inf. }
  rewrite <- (map_length fst (n_out n)); eauto.
Qed.

End SDTOREL.

Module SdtorelFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS        Ids Op OpAux)
       (Senv  : STATICENV     Ids Op OpAux Cks)
       (Syn   : LSYNTAX Ids Op OpAux Cks Senv)
       (Typ   : LTYPING Ids Op OpAux Cks Senv Syn)
       (Cl    : LCLOCKING     Ids Op OpAux Cks Senv Syn)
       (Caus  : LCAUSALITY    Ids Op OpAux Cks Senv Syn)
       (Lord  : LORDERED      Ids Op OpAux Cks Senv Syn)
       (Str   : COINDSTREAMS  Ids Op OpAux Cks)
       (Sem   : LSEMANTICS Ids Op OpAux Cks Senv Syn Lord Str)
       (Den   : LDENOT     Ids Op OpAux Cks Senv Syn Lord)
       (Inf   : LDENOTINF  Ids Op OpAux Cks Senv Syn Typ Caus Lord Den)
       (Safe  : LDENOTSAFE Ids Op OpAux Cks Senv Syn Typ Cl Lord Den)
<: SDTOREL Ids Op OpAux Cks Senv Syn Typ Cl Caus Lord Str Sem Den Inf Safe.
  Include SDTOREL Ids Op OpAux Cks Senv Syn Typ Cl Caus Lord Str Sem Den Inf Safe.
End SdtorelFun.
