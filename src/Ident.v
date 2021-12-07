From Velus Require Import Common.
From Coq Require Import String.
From Coq Require Import Ascii.
From Coq Require Import List.
Import List.ListNotations.

Open Scope bool_scope.

(** *** ident <-> string conversion *)
Axiom pos_to_str: ident -> string. (* uses extern_atom *)
Axiom str_to_pos: string -> ident. (* uses intern_string *)

Axiom str_to_pos_injective:
  forall x x',
    str_to_pos x = str_to_pos x' ->
    x = x'.
Axiom pos_to_str_equiv:
  forall x, pos_to_str (str_to_pos x) = x.

Fixpoint In_str (x: ascii) (s: string): Prop :=
  match s with
  | EmptyString => False
  | String x' s => x' = x \/ In_str x s
  end.

Scheme Equality for ascii.
Fixpoint mem_str (x: ascii) (s: string): bool :=
  match s with
  | EmptyString => false
  | String x' s => (ascii_beq x' x || mem_str x s)%bool
  end.

Lemma mem_In_str:
  forall x s,
    In_str x s <-> mem_str x s = true.
Proof.
  induction s; simpl.
  - split; auto.
    intro; discriminate.
  - split; intro H.
    + rewrite Bool.orb_true_iff; destruct H.
      * left; now apply internal_ascii_dec_lb.
      * right; now apply IHs.
    + rewrite Bool.orb_true_iff in H; destruct H.
      * left; now apply internal_ascii_dec_bl.
      * right; now apply IHs.
Qed.

Lemma not_mem_In_str:
  forall x s,
    ~In_str x s <-> mem_str x s = false.
Proof.
  induction s; simpl.
  - split; auto.
  - split; intro H.
    + rewrite Bool.orb_false_iff; apply Decidable.not_or in H; destruct H; split.
      * apply Bool.not_true_is_false; intro E.
        apply internal_ascii_dec_bl in E.
        contradiction.
      * now apply IHs.
    + rewrite Bool.orb_false_iff in H; destruct H; intros [E|E].
      * apply Bool.not_true_iff_false in H; apply H.
        now apply internal_ascii_dec_lb.
      * now apply IHs.
Qed.

Definition sep: ascii := "$"%char.

Module Export Ids <: IDS.
  Definition bool_id := str_to_pos "bool".
  Definition true_id := str_to_pos "True".
  Definition false_id := str_to_pos "False".

  Definition self := str_to_pos "self".
  Definition out := str_to_pos "out".
  Definition temp := str_to_pos "temp".
  Definition fun_id: ident  := str_to_pos "fun".
  Definition sync_id: ident := str_to_pos "sync".
  Definition main_id: ident := str_to_pos "main".
  Definition main_proved_id: ident := str_to_pos "main_proved".
  Definition main_sync_id: ident := str_to_pos "main_sync".
  Definition step := str_to_pos "step".
  Definition reset := str_to_pos "reset".
  Definition glob := str_to_pos "glob".
  Definition elab := str_to_pos "elab".
  Definition switch := str_to_pos "swi".
  Definition local := str_to_pos "local".
  Definition norm1 := str_to_pos "norm1".
  Definition norm2 := str_to_pos "norm2".
  Definition obc2c := str_to_pos "obc2c".

  Definition default := 1%positive.

  Ltac prove_str_to_pos_neq :=
    match goal with
    | |- ?x1 <> ?x2 =>
      intros Heq; apply str_to_pos_injective in Heq; inv Heq
    end.

  Definition elab_prefs := PS.singleton elab.
  Definition switch_prefs := PS.add switch elab_prefs.
  Definition local_prefs := PS.add local switch_prefs.
  Definition norm1_prefs := PS.add norm1 local_prefs.
  Definition norm2_prefs := PS.add norm2 norm1_prefs.

  Definition gensym_prefs := [elab; switch; local; norm1; norm2].

  Lemma gensym_prefs_NoDup : NoDup gensym_prefs.
  Proof.
    unfold gensym_prefs.
    repeat constructor; auto.
    1-4:repeat rewrite not_in_cons; repeat split; auto.
    1-10:prove_str_to_pos_neq.
  Qed.

  Lemma self_not_out: self <> out.
  Proof. prove_str_to_pos_neq. Qed.
  Global Hint Resolve self_not_out : ident.

  Lemma reset_not_step:
    reset <> step.
  Proof. prove_str_to_pos_neq. Qed.
  Global Hint Resolve reset_not_step : ident.

  Lemma fun_not_out: fun_id <> out.
  Proof. prove_str_to_pos_neq. Qed.
  Global Hint Resolve fun_not_out : ident.

  Lemma fun_not_glob: fun_id <> glob.
  Proof. prove_str_to_pos_neq. Qed.
  Global Hint Resolve fun_not_glob : ident.

  Fact obc2c_not_in_gensym_prefs :
    ~In obc2c gensym_prefs.
  Proof.
    unfold gensym_prefs.
    repeat rewrite not_in_cons.
    repeat split; auto; prove_str_to_pos_neq.
  Qed.
  Global Hint Resolve obc2c_not_in_gensym_prefs : ident.

  Fact self_not_in_gensym_prefs :
    ~In self gensym_prefs.
  Proof.
    unfold gensym_prefs.
    repeat rewrite not_in_cons.
    repeat split; auto; prove_str_to_pos_neq.
  Qed.
  Global Hint Resolve self_not_in_gensym_prefs : ident.

  Fact temp_not_in_gensym_prefs :
    ~In temp gensym_prefs.
  Proof.
    unfold gensym_prefs.
    repeat rewrite not_in_cons.
    repeat split; auto; prove_str_to_pos_neq.
  Qed.
  Global Hint Resolve temp_not_in_gensym_prefs : ident.

  Definition atom x := ~In_str sep (pos_to_str x).
  Definition is_atom x := negb (mem_str sep (pos_to_str x)).

  Lemma is_atom_spec : forall x,
      is_atom x = true <->
      atom x.
  Proof.
    intros x. unfold is_atom, atom.
    rewrite Bool.negb_true_iff.
    rewrite not_mem_In_str. reflexivity.
  Qed.

  Local Ltac prove_atom :=
    match goal with
    | |- atom ?x =>
      unfold atom, x; rewrite pos_to_str_equiv;
      rewrite not_mem_In_str; reflexivity
    end.

  Lemma self_atom: atom self.
  Proof. prove_atom. Qed.
  Lemma out_atom: atom out.
  Proof. prove_atom. Qed.
  Lemma temp_atom: atom temp.
  Proof. prove_atom. Qed.

  Lemma fun_id_atom: atom fun_id.
  Proof. prove_atom. Qed.
  Lemma sync_id_atom: atom sync_id.
  Proof. prove_atom. Qed.
  Lemma main_id_atom: atom main_id.
  Proof. prove_atom. Qed.
  Lemma main_proved_id_atom: atom main_proved_id.
  Proof. prove_atom. Qed.
  Lemma main_sync_id_atom: atom main_sync_id.
  Proof. prove_atom. Qed.

  Lemma step_atom: atom step.
  Proof. prove_atom. Qed.
  Lemma reset_atom: atom reset.
  Proof. prove_atom. Qed.

  Lemma glob_atom: atom glob.
  Proof. prove_atom. Qed.

  Lemma elab_atom: atom elab.
  Proof. prove_atom. Qed.
  Lemma switch_atom: atom switch.
  Proof. prove_atom. Qed.
  Lemma local_atom: atom local.
  Proof. prove_atom. Qed.
  Lemma norm1_atom: atom norm1.
  Proof. prove_atom. Qed.
  Lemma norm2_atom: atom norm2.
  Proof. prove_atom. Qed.
  Lemma obc2c_atom: atom obc2c.
  Proof. prove_atom. Qed.

  Global Hint Resolve step_atom reset_atom fun_id_atom sync_id_atom
         out_atom main_id_atom main_proved_id_atom main_sync_id_atom
         self_atom glob_atom elab_atom norm1_atom norm2_atom obc2c_atom : ident.

  Axiom prefix : ident -> ident -> ident.

  Axiom prefix_not_atom:
    forall pref id,
      ~atom (prefix pref id).
  Global Hint Resolve prefix_not_atom : ident.

  Axiom prefix_injective':
    forall pref id pref' id',
      pref <> pref' \/ id <> id' ->
      prefix pref id <> prefix pref' id'.

  Corollary prefix_injective:
    forall pref id pref' id',
      prefix pref id = prefix pref' id' ->
      pref = pref' /\ id = id'.
  Proof.
    intros * Heq.
    destruct (ident_eq_dec pref pref'), (ident_eq_dec id id'); auto.
    1-3:exfalso; eapply prefix_injective' in Heq; eauto.
  Qed.

  Definition prefix_fun (f c: ident): ident :=
    prefix fun_id (prefix f c).
  Definition prefix_out (f o: ident): ident :=
    prefix out (prefix f o).
  Definition prefix_temp (f c: ident): ident :=
    prefix temp (prefix f c).

  Lemma prefix_fun_injective:
    forall c c' f f',
      prefix_fun c f = prefix_fun c' f' ->
      c = c' /\ f = f'.
  Proof.
    unfold prefix_fun.
    intros * Heq.
    eapply prefix_injective, prefix_injective; eauto.
  Qed.

  Lemma prefix_out_injective:
    forall c c' f f',
      prefix_out c f = prefix_out c' f' ->
      c = c' /\ f = f'.
  Proof.
    unfold prefix_out.
    intros * Hneq.
    eapply prefix_injective, prefix_injective; eauto.
  Qed.

  Lemma prefix_fun_not_out:
    forall c f c' f', prefix_fun c f <> prefix_out c' f'.
  Proof.
    intros *.
    eapply prefix_injective'. left.
    prove_str_to_pos_neq.
  Qed.

  Definition prefix_glob (id: ident): ident :=
    prefix glob id.

  Lemma main_not_glob:
    forall x, prefix_glob x <> main_id.
  Proof.
    unfold prefix_glob.
    intros * H.
    eapply prefix_not_atom.
    rewrite H; eauto with ident.
  Qed.

  Lemma main_proved_not_glob:
    forall x, prefix_glob x <> main_proved_id.
  Proof.
    unfold prefix_glob.
    intros * H.
    eapply prefix_not_atom.
    rewrite H; eauto with ident.
  Qed.

  Lemma sync_not_glob:
    forall x, prefix_glob x <> sync_id.
  Proof.
    unfold prefix_glob.
    intros * H.
    eapply prefix_not_atom.
    rewrite H; eauto with ident.
  Qed.

  Lemma main_sync_not_glob:
    forall x, prefix_glob x <> main_sync_id.
  Proof.
    unfold prefix_glob.
    intros * H.
    eapply prefix_not_atom.
    rewrite H; eauto with ident.
  Qed.

  Lemma self_not_glob:
    forall x, prefix_glob x <> self.
  Proof.
    unfold prefix_glob.
    intros * H.
    eapply prefix_not_atom.
    rewrite H; eauto with ident.
  Qed.

  Lemma prefix_glob_injective:
    forall x x',
      prefix_glob x = prefix_glob x' ->
      x = x'.
  Proof.
    intros * Hneq.
    eapply prefix_injective; eauto with ident.
  Qed.

  Lemma glob_not_in_prefixed:
    forall {A} (xs: list (ident * A)) ps,
      Forall (fun x => exists m c, x = prefix_fun m c) ps ->
      Forall (fun z => ~ In z ps) (map (fun xt => prefix_glob (fst xt)) xs).
  Proof.
    induction xs as [|(x, t)]; simpl; intros * Pref; auto.
    constructor; auto.
    intro Hin.
    eapply Forall_forall in Hin; eauto; simpl in Hin.
    destruct Hin as (?&?&Hpre).
    eapply prefix_injective in Hpre as (Heq&?); subst.
    contradict Heq. prove_str_to_pos_neq.
  Qed.

  Lemma NoDupMembers_glob:
    forall {A} (ys xs: list (ident * A)),
      NoDupMembers (xs ++ ys) ->
      Forall (fun z => ~ In z (map (fun xt => prefix_glob (fst xt)) xs))
             (map (fun xt => prefix_glob (fst xt)) ys).
  Proof.
    induction ys as [|(y, t)]; simpl; intros * Nodup; auto.
    rewrite NoDupMembers_app_cons in Nodup; destruct Nodup as [Notin Nodup].
    constructor; auto.
    rewrite in_map_iff; intros ((x, t') & E & Hin).
    eapply prefix_injective in E as (?&?); subst.
    eapply Notin, In_InMembers, in_app; eauto.
  Qed.

  (** *** Name generation with fresh identifiers *)

  Axiom gensym : ident -> option ident -> ident -> ident.

  Axiom gensym_not_atom:
    forall pref hint x,
      ~atom (gensym pref hint x).

  Axiom gensym_injective':
    forall pref hint id pref' hint' id',
      pref <> pref' \/ id <> id' ->
      gensym pref hint id <> gensym pref' hint' id'.

  Corollary gensym_injective:
    forall pref hint id pref' hint' id',
      gensym pref hint id = gensym pref' hint' id' ->
      pref = pref' /\ id = id'.
  Proof.
    intros * Heq.
    destruct (ident_eq_dec pref pref'), (ident_eq_dec id id'); auto.
    1-3:exfalso; eapply gensym_injective' in Heq; eauto.
  Qed.

  Definition AtomOrGensym (prefs : PS.t) (id : ident) :=
    atom id \/ PS.Exists (fun pre => exists n hint, id = gensym pre hint n) prefs.

  Axiom prefix_gensym_injective':
    forall pref id pref' hint' id',
      pref <> pref' ->
      prefix pref id <> gensym pref' hint' id'.

  Corollary prefix_gensym_injective:
    forall pref id pref' hint' id',
      prefix pref id = gensym pref' hint' id' ->
      pref = pref'.
  Proof.
    intros * Heq.
    destruct (ident_eq_dec pref pref'); auto.
    exfalso. eapply prefix_gensym_injective' in n; eauto.
  Qed.
End Ids.
