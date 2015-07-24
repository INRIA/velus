Require Import Coq.FSets.FMapPositive.
Require Import List.
Require Import Rustre.Common.
Require Import Rustre.DataflowSyntax.


Definition alls {A B} (v : B) (l : list A) := List.map (fun _ => v) l.

Fixpoint map2 {A B C} (f : A -> B -> C) l1 l2 :=
  match l1, l2 with
    | nil, _ => nil
    | _, nil => nil
    | x1 :: l1, x2 :: l2 => f x1 x2 :: map2 f l1 l2
  end.

Lemma map2_nil {A B C} : forall (f : A -> B -> C) l1 l2, map2 f l1 l2 = nil <-> l1 = nil \/ l2 = nil.
Proof. intros f [| x1 l1] [| x2 l2]; simpl; try tauto. intuition discriminate. Qed.

Lemma map2_cons {A B C} : forall (f : A -> B -> C) l1 l2 y l, map2 f l1 l2 = y :: l <->
  exists x1 l1' x2 l2', l1 = x1 :: l1' /\ l2 = x2 :: l2' /\ y = f x1 x2 /\ map2 f l1' l2' = l.
Proof.
intros f [| x1 l1] [| x2 l2] y l; simpl; split; intro Heq; decompose [and ex] Heq; try now discriminate.
- inversion Heq. subst. repeat eexists; repeat split; eassumption.
- subst. inversion_clear H; inversion_clear H0 (* FIXME: generated names *). reflexivity.
Qed.

Lemma last_app {A} : forall (l l' : list A) d, l' <> nil -> last (l ++ l') d = last l' d.
Proof.
intros l l' d Hl'. induction l as [| e l]; simpl.
- reflexivity.
- rewrite <- IHl. destruct (l ++ l') eqn:Heq; trivial.
  apply app_eq_nil in Heq. intuition.
Qed.

Lemma rev_is_nil {A} : forall l : list A, rev l = nil <-> l = nil.
Proof.
intros [| ? ?]; simpl.
+ reflexivity.
+ split; intro H.
  - apply app_eq_nil in H. intuition discriminate.
  - discriminate.
Qed.

(** *  Dataflow semantics with lists  **)

(* Idea?: clocks, expressions -> instantaneous semantics
          equations -> list semantics *)
Inductive value :=
  | abs
  | here (v : const).
Coercion here : const >-> value.

Definition venv := PositiveMap.t value.
Definition history := list venv.


Definition instant_sem_var env x c := PositiveMap.find x env = Some (here c).

Definition sem_var (H : history) (x : ident) (cl : list value) : Prop :=
  List.map (PositiveMap.find x) H = List.map (@Some _) cl.

(** **  Semantics for one instant  **)

(** ***  Clock semantics  **)

Inductive instant_sem_clock (env : venv) : clock -> bool -> Prop :=
  | base: instant_sem_clock env Cbase true
  | on_tick: forall ck x b,
      instant_sem_clock env ck true ->
      PositiveMap.find x env = Some (here (Cbool b)) -> 
      instant_sem_clock env (Con ck x b) true
  | on_abs1 : forall ck x b,
      instant_sem_clock env ck false ->
      instant_sem_clock env (Con ck x b) false
  | on_abs2 : forall ck x c c',
      instant_sem_clock env ck true ->
      PositiveMap.find x env = Some (here c') -> 
      Cbool c <> c' ->
      instant_sem_clock env (Con ck x c) false.

(** ***  Expression semantics  **)

Inductive instant_sem_laexp (env : venv) : laexp -> value -> Prop :=
  | Stick : forall ck ce c,
      instant_sem_lexp env ce c ->
      instant_sem_clock env ck true ->
      instant_sem_laexp env (LAexp ck ce) c
  | Sabs : forall ck ce,
      instant_sem_lexp env ce abs ->
      instant_sem_clock env ck false ->
      instant_sem_laexp env (LAexp ck ce) abs

with instant_sem_lexp (env : venv) : lexp -> value -> Prop :=
  | Sconst : forall c, instant_sem_lexp env (Econst c) c
  | Svar : forall x c,
      instant_sem_var env x c ->
      instant_sem_lexp env (Evar x) c
  | Swhen_eq : forall s x b c,
      instant_sem_var env x  (Cbool b) ->
      instant_sem_laexp env s c ->
      instant_sem_lexp env (Ewhen s x b) c
  | Swhen_abs : forall s x b b',
      instant_sem_var env x (Cbool b') -> b <> b' ->
      instant_sem_lexp env (Ewhen s x b) abs.

Inductive instant_sem_caexp (env : venv) : caexp -> value -> Prop :=
  | SCtick : forall ck ce c,
      instant_sem_cexp env ce c ->
      instant_sem_clock env ck true ->
      instant_sem_caexp env (CAexp ck ce) c
  | SCabs : forall ck ce,
      instant_sem_cexp env ce abs ->
      instant_sem_clock env ck false ->
      instant_sem_caexp env (CAexp ck ce) abs

with instant_sem_cexp (env : venv) : cexp -> value -> Prop :=
  | Smerge_true : forall x t f c,
      instant_sem_var env x (Cbool true) ->
      instant_sem_caexp env t c ->
      instant_sem_cexp env (Emerge x t f) c
  | Smerge_false : forall x t f c,
      instant_sem_var env x (Cbool false) ->
      instant_sem_caexp env f c ->
      instant_sem_cexp env (Emerge x t f) c
  | Sexp : forall e c,
      instant_sem_lexp env e c ->
      instant_sem_cexp env (Eexp e) c.

(** **  Lifting to lists  **)

Inductive sem_clock : history -> clock -> list bool -> Prop :=
  | Snil_ck : forall ck, sem_clock nil ck nil
  | Scons_ck : forall env H ck b bl, 
      instant_sem_clock env ck b -> sem_clock H ck bl -> sem_clock (env :: H) ck (b :: bl).

Inductive sem_laexp : history -> laexp -> list value -> Prop :=
  | Snil_laexp : forall cae, sem_laexp nil cae nil
  | Scons_laexp : forall env H cae c cl,
      instant_sem_laexp env cae c -> sem_laexp H cae cl -> sem_laexp (env :: H) cae (c :: cl).

Inductive sem_lexp : history -> lexp -> list value -> Prop :=
  | Snil_lexp : forall ce, sem_lexp nil ce nil
  | Scons_lexp : forall env H ce c cl,
      instant_sem_lexp env ce c -> sem_lexp H ce cl -> sem_lexp (env :: H) ce (c :: cl).

Inductive sem_caexp : history -> caexp -> list value -> Prop :=
  | Snil_caexp : forall cae, sem_caexp nil cae nil
  | Scons_caexp : forall env H cae c cl,
      instant_sem_caexp env cae c -> sem_caexp H cae cl -> sem_caexp (env :: H) cae (c :: cl).

Inductive sem_cexp : history -> cexp -> list value -> Prop :=
  | Snil_cexp : forall cae, sem_cexp nil cae nil
  | Scons_cexp : forall env H ce c cl,
      instant_sem_cexp env ce c -> sem_cexp H ce cl -> sem_cexp (env :: H) ce (c :: cl).


(** Alternative definition by a forall on lists *)
Fixpoint for_all2 {A B} (P : A -> B -> Prop) l1 l2 :=
  match l1, l2 with
    | nil, nil => True
    | x1 :: l1, x2 :: l2 => P x1 x2 /\ for_all2 P l1 l2
    | _ :: _, nil => False
    | nil, _ :: _ => False
  end.

Lemma for_all2_length {A B} : forall (P : A -> B -> Prop) l1 l2, for_all2 P l1 l2 -> length l1 = length l2.
Proof.
intros P l1. induction l1 as [| x1 l1]; intros l2 Hall.
- destruct l2; trivial. now elim Hall.
- destruct l2; try now elim Hall. simpl in *. f_equal. now apply IHl1.
Qed.

Definition sem_clock' : history -> clock -> list bool -> Prop :=
  fun H ck bl => for_all2 (fun env => instant_sem_clock env ck) H bl.

Definition sem_laexp' : history -> laexp -> list value -> Prop :=
  fun H cae cl => for_all2 (fun env => instant_sem_laexp env cae) H cl.

Definition sem_lexp' : history -> lexp -> list value -> Prop :=
  fun H ce cl => for_all2 (fun env => instant_sem_lexp env ce) H cl.

Definition sem_caexp' : history -> caexp -> list value -> Prop :=
  fun H cae cl => for_all2 (fun env => instant_sem_caexp env cae) H cl.

Definition sem_cexp' : history -> cexp -> list value -> Prop :=
  fun H ce cl => for_all2 (fun env => instant_sem_cexp env ce) H cl.

(** Equivalence of both definitions *)

Ltac solve_equiv :=
  intro H; induction H as [| env H IHH]; intros cae bl;
  [ split; intro Hsem;
    [ inversion_clear Hsem; exact I
    | apply for_all2_length in Hsem; destruct bl; constructor || discriminate ]
  | split; intro Hsem;
    [ inversion_clear Hsem; rewrite IHH in *; now split
    | assert (Hnil : bl <> nil) by (intro; subst; apply for_all2_length in Hsem; discriminate);
      destruct bl as [| b bl]; try (now elim Hnil); [];
      destruct Hsem; constructor; trivial; now rewrite IHH ] ].

Lemma sem_clock_equiv : forall H ck bl, sem_clock H ck bl <-> sem_clock' H ck bl.
Proof. solve_equiv. Qed.

Lemma sem_laexp_equiv : forall H cae cl, sem_laexp H cae cl <-> sem_laexp' H cae cl.
Proof. solve_equiv. Qed.

Lemma sem_lexp_equiv : forall H cae cl, sem_lexp H cae cl <-> sem_lexp' H cae cl.
Proof. solve_equiv. Qed.

Lemma sem_caexp_equiv : forall H cae cl, sem_caexp H cae cl <-> sem_caexp' H cae cl.
Proof. solve_equiv. Qed.

Lemma sem_cexp_equiv : forall H cae cl, sem_cexp H cae cl <-> sem_cexp' H cae cl.
Proof. solve_equiv. Qed.


(** **  Semantics of equations  **)

(** Now we need to take into account the fby operator.
    Version of the paper: head of the list = first instant. *)
Fixpoint fby (v : const) (s : list value) : list value :=
  match s with
  | here v' :: s => here v :: fby v' s
  | abs :: s => abs :: fby v s
  | nil => nil
  end.

(* Original "(exists ...) -> ..." tranformed into "forall (... -> ...)" *)
Inductive sem_equation (G : global) : history -> equation -> Prop :=
  | SEqDef : forall H x cae v,
      sem_lexp H (Evar x) v ->
      sem_caexp H cae v ->
      sem_equation G H (EqDef x cae)
  | SEqApp : forall H x f arg input output eqs H' vi vo,
      PositiveMap.find f G = Some (mk_node f input output eqs) ->
      sem_laexp H arg vi -> (* arg evaluate to vi *)
      sem_lexp H (Evar x) vo -> (* x evaluates to vo *)
      sem_lexp H' (Evar input.(v_name)) vi -> (* in the local context, input evaluates to vi *)
      sem_lexp H' (Evar output.(v_name)) vo -> (* in the local context, output evaluates to vo *)
      List.Forall (sem_equation G H') eqs -> (* in the local context, the equations have correct semantics *)
      sem_equation G H (EqApp x f arg)
  | SEqFby : forall H x v y cl,
      sem_var H y.(v_name) cl ->
      sem_lexp H (Evar x) (fby v cl) ->
      sem_equation G H (EqFby x v y).

(** ***  Reverse orientation for lists: last instant is first  **)

Fixpoint fby_aux (v0 : const) (s : list value) : list value * const  :=
  match s with
  | here v :: s => let '(s', v') := fby_aux v0 s in (here v' :: s', v)
  | abs :: s => let '(s', v') := fby_aux v0 s in (abs :: s', v')
  | nil => (nil, v0)
  end.
Definition fby_rev v s := fst (fby_aux v s).

Lemma fby_rev_nil : forall v, fby_rev v nil = nil.
Proof. reflexivity. Qed.

Lemma fby_aux_abs : forall v0 s, fby_aux v0 (abs :: s) = (abs :: fst (fby_aux v0 s), snd (fby_aux v0 s)).
Proof.
induction s as [| [| v] s]; simpl in *.
+ reflexivity.
+ destruct (fby_aux v0 s); rewrite IHs; reflexivity.
+ destruct (fby_aux v0 s); simpl. reflexivity.
Qed.

Corollary fby_rev_cons_abs : forall v0 s, fby_rev v0 (abs :: s) = abs :: fby_rev v0 s.
Proof. unfold fby_rev. intros. now rewrite fby_aux_abs. Qed.

Lemma fby_rev_next : forall d v0 v s n,
  List.nth (S n) (fby_rev v0 (v :: s)) (here d) = List.nth n (fby_rev v0 s) (here d).
Proof. unfold fby_rev. intros d c [| c'] s n; simpl; destruct (fby_aux c s); reflexivity. Qed.

Lemma fby_rev_abs : forall d v s n, List.nth n s (here d) = abs -> List.nth n (fby_rev v s) (here d) = abs.
Proof.
intros d v s. induction s as [| v' s]; intros n Hn.
+ assumption.
+ destruct n; simpl.
  - destruct v'; simpl in *; discriminate || now rewrite fby_rev_cons_abs.
  - rewrite fby_rev_next. now apply IHs.
Qed.

Lemma fby_aux_app : forall s1 s2 v s1' s2' v' v'' , fby_aux v s2 = (s2', v') -> fby_aux v' s1 = (s1', v'') ->
  fby_aux v (s1 ++ s2) = (s1' ++ s2', v'').
Proof.
intros s1. induction s1 as [| [| c] s1]; intros s2 v s1' s2' v' v'' Hs2 Hs1.
* inversion Hs1. subst. simpl. assumption.
* simpl app. rewrite fby_aux_abs in Hs1 |- *. destruct s1' as [| ? s1']; inversion Hs1.
  simpl. apply (IHs1 _ _ s1' _ _ v'') in Hs2.
  + rewrite Hs2. f_equal.
    - now rewrite H1.
    - simpl. auto.
  + subst. apply surjective_pairing.
* simpl in *. destruct (fby_aux v' s1) eqn:Hs1'.
  rewrite (IHs1 _ _ _ _ _ _ Hs2 Hs1'). inversion_clear Hs1. simpl. reflexivity.
Qed.

Corollary fby_rev_last_abs : forall v s, fby_rev v (s ++ abs :: nil) = fby_rev v s ++ abs :: nil.
Proof. intros. unfold fby_rev. erewrite fby_aux_app; simpl; try reflexivity. apply surjective_pairing. Qed.

(** Equivalence theorem between fby and fby_rev *)
Theorem fby_fby_rev : forall s v, fby_rev v (rev s) = List.rev (fby v s).
Proof.
induction s as [| [| c] s]; intro v; simpl.
- reflexivity.
- rewrite fby_rev_last_abs, IHs. reflexivity. 
- unfold fby_rev. erewrite fby_aux_app; simpl; try reflexivity.
  rewrite surjective_pairing at 1. rewrite <- IHs. reflexivity.
Qed.

(* Same semantics as Tim, but is it the right one? Maybe it should be called last? *)
Fixpoint hold_aux v0 s := 
  match s with
  | here v :: s => let '(s', v') := hold_aux v0 s in (here v' :: s', v)
  | abs :: s => let '(s', v') := hold_aux v0 s in (here v' :: s', v')
  | nil => (nil, v0)
  end.
Definition hold v s := fst (hold_aux v s).

Lemma hold_never_abs : forall d s v n, List.nth n (hold v s) (here d) <> abs.
Proof.
unfold hold. intros d s. induction s as [| [| v'] s]; intros v n.
+ destruct n; simpl; discriminate.
+ destruct n as [| n]; simpl.
  - specialize (IHs v 0). destruct (hold_aux v s) as [l c]. simpl. discriminate.
  - specialize (IHs v n). destruct (hold_aux v s) as [l c]. simpl in *. assumption.
+ destruct n as [| n]; simpl.
  - specialize (IHs v 0). destruct (hold_aux v s) as [l c]. simpl. discriminate.
  - specialize (IHs v n). destruct (hold_aux v s) as [l c]. simpl in *. assumption.
Qed.

Lemma hold_next : forall d c v s n, List.nth (S n) (hold c (v :: s)) (here d) = List.nth n (hold c s) (here d).
Proof. unfold hold. intros d c [| c'] s n; simpl; destruct (hold_aux c s); reflexivity. Qed.

Lemma fby_hold_aux_eq_snd : forall v s, snd (fby_aux v s) = snd (hold_aux v s).
Proof.
intros v s. induction s as [| [| v'] s]; simpl.
- reflexivity.
- destruct (fby_aux v s), (hold_aux v s); simpl in *. assumption.
- destruct (fby_aux v s), (hold_aux v s); simpl in *. reflexivity.
Qed.

Lemma fby_hold_aux_equiv_fst : forall d v s n, List.nth n s (here d) <> abs ->
  List.nth n (fby_rev v s) (here d) = List.nth n (hold v s) (here d).
Proof.
intros d v s. induction s as [| [| v'] s]; intros n Hhere.
+ destruct n; simpl; reflexivity.
+ destruct n as [| n]; simpl.
  - now elim Hhere.
  - specialize (IHs n Hhere). rewrite fby_rev_cons_abs. simpl. now rewrite IHs, hold_next.
+ destruct n as [| n]; simpl.
  - unfold fby_rev, hold. simpl. destruct (fby_aux v s) eqn:Hfby, (hold_aux v s) eqn:Hhold; simpl.
    f_equal. change (snd (l, c) = snd (l0, c0)). rewrite <- Hfby, <- Hhold. apply fby_hold_aux_eq_snd.
  - specialize (IHs n Hhere). now rewrite fby_rev_next, hold_next, IHs.
Qed.

Inductive sem_equation_rev (G : global) : history -> equation -> Prop :=
  | SEqDef_rev : forall H x cae v,
      sem_lexp H (Evar x) v -> sem_caexp H cae v -> sem_equation_rev G H (EqDef x cae)
  | SEqApp_rev : forall H x f arg input output eqs H' vi vo,
      PositiveMap.find f G = Some (mk_node f input output eqs) ->
      sem_laexp H arg vi -> (* arg evaluate to vi *)
      sem_lexp H (Evar x) vo -> (* x evaluates to vo *)
      sem_lexp H' (Evar input.(v_name)) vi -> (* in the local context, input evaluates to vi *)
      sem_lexp H' (Evar output.(v_name)) vo -> (* in the local context, output evaluates to vo *)
      List.Forall (sem_equation_rev G H') eqs -> (* in the local context, the equations have correct semantics *)
      sem_equation_rev G H (EqApp x f arg)
  | SEqFby_rev : forall H x v y cl,
      sem_var H y.(v_name) cl ->
      sem_lexp H (Evar x) (fby_rev v cl) ->
      sem_equation_rev G H (EqFby x v y).


(** ***  Equivalence between semantics using forward or backward lists  **)

(** First, the equivalence on lesser semantics **)

Lemma for_all2_app {A B} : forall (P : A -> B -> Prop) l1 l2 l1' l2',
  for_all2 P l1 l1' -> for_all2 P l2 l2' -> for_all2 P (l1 ++ l2) (l1' ++ l2').
Proof.
intros P l1 l2. induction l1; intros l1' l2' HP1 HP2.
+ apply for_all2_length in HP1.
  destruct l1'; simpl in *; assumption || discriminate.
+ destruct l1'.
  - apply for_all2_length in HP1. simpl in HP1. discriminate.
  - destruct HP1. split; auto.
Qed.

Lemma for_all2_rev_aux {A B} : forall (P : A -> B -> Prop) l1 l2, for_all2 P l1 l2 -> for_all2 P (rev l1) (rev l2).
Proof.
intros P l1. induction l1; intros l2 Hall.
+ apply for_all2_length in Hall.
  destruct l2; simpl in *; exact I || discriminate.
+ destruct l2.
  - apply for_all2_length in Hall. simpl in Hall. discriminate.
  - destruct Hall. simpl. apply for_all2_app; simpl; auto.
Qed.

Lemma for_all2_rev {A B} : forall (P : A -> B -> Prop) l1 l2, for_all2 P (rev l1) (rev l2) <-> for_all2 P l1 l2.
Proof.
intros. split.
- setoid_rewrite <- rev_involutive at 5 6. apply for_all2_rev_aux.
- apply for_all2_rev_aux.
Qed.

Lemma sem_var_rev : forall H x cl, sem_var (rev H) x (rev cl) <-> sem_var H x cl.
Proof.
intros. unfold sem_var. do 2 rewrite map_rev.
split; intro Heq.
- now rewrite <- rev_involutive, <- Heq, rev_involutive.
- unfold venv. now rewrite Heq.
Qed.

Lemma sem_clock_rev : forall H ce bl, sem_clock (rev H) ce (rev bl) <-> sem_clock H ce bl.
Proof. intros. setoid_rewrite sem_clock_equiv. apply for_all2_rev. Qed.

Lemma sem_laexp_rev : forall H ce v, sem_laexp (rev H) ce (rev v) <-> sem_laexp H ce v.
Proof. intros. setoid_rewrite sem_laexp_equiv. apply for_all2_rev. Qed.

Lemma sem_lexp_rev : forall H ce v, sem_lexp (rev H) ce (rev v) <-> sem_lexp H ce v.
Proof. intros. setoid_rewrite sem_lexp_equiv. apply for_all2_rev. Qed.

Lemma sem_caexp_rev : forall H ce v, sem_caexp (rev H) ce (rev v) <-> sem_caexp H ce v.
Proof. intros. setoid_rewrite sem_caexp_equiv. apply for_all2_rev. Qed.

Lemma sem_cexp_rev : forall H ce v, sem_cexp (rev H) ce (rev v) <-> sem_cexp H ce v.
Proof. intros. setoid_rewrite sem_cexp_equiv. apply for_all2_rev. Qed.

Print sem_equation_rev.

Theorem sem_equation_rev_1 : forall G H eq, sem_equation G H eq -> sem_equation_rev G (rev H) eq.
Proof.
intros G H eq Heq. induction Heq.
+ econstructor; rewrite sem_lexp_rev || rewrite sem_caexp_rev; eassumption.
+ apply (SEqApp_rev G (rev H) _ _ _ input output eqs (rev H') (rev vi) (rev vo));
  rewrite ?sem_lexp_rev, ?sem_laexp_rev; trivial.
  admit. (* TODO: induction scheme is not strong enough *)
+ econstructor.
  - rewrite sem_var_rev. eassumption. 
  - now rewrite fby_fby_rev, sem_lexp_rev.
Qed.

Theorem sem_equation_rev_2 : forall G H eq, sem_equation_rev G (rev H) eq -> sem_equation G H eq.
Proof.
intros G H eq. generalize (eq_refl (rev H)). generalize (rev H) at -1.
intros H' HeqH' Heq. induction Heq.
+ subst. econstructor; rewrite <- sem_lexp_rev || rewrite <- sem_caexp_rev; rewrite rev_involutive; eassumption.
+ apply (SEqApp G H _ _ _ input output eqs (rev H') (rev vi) (rev vo)); trivial; subst;
  try now rewrite <- sem_lexp_rev || rewrite <- sem_laexp_rev; rewrite rev_involutive.
  now rewrite sem_lexp_rev || rewrite sem_laexp_rev.
  now rewrite sem_lexp_rev || rewrite sem_laexp_rev.
  admit. (* TODO: induction scheme is not strong enough *)
+ subst. econstructor.
  - rewrite <- sem_var_rev, rev_involutive. eassumption. 
  - setoid_rewrite <- rev_involutive at 1 2. now rewrite <- fby_fby_rev, sem_lexp_rev, rev_involutive.
Qed.
