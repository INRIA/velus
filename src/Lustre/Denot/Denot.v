From Coq Require Import BinPos List.
From Cpo Require Import Cpo_def Cpo_streams_type Systems.

From Velus Require Import Common Ident Operators Clocks CoindStreams.
From Velus Require Import Lustre.StaticEnv Lustre.LSyntax Lustre.LOrdered Lustre.LSemantics Lustre.LTyping.

Close Scope equiv_scope. (* conflicting notation "==" *)

Require Import Cpo_ext.
Require Import SDfuns.

Module Type LDENOT
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Senv  : STATICENV     Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
       (Import Typ   : LTYPING       Ids Op OpAux Cks Senv Syn)
       (Import Lord  : LORDERED      Ids Op OpAux Cks Senv Syn)
       (Import Str   : COINDSTREAMS  Ids Op OpAux Cks).


  (* TODO: pour l'instant on se restreint aux cas suivants *)
  Inductive restr_exp : exp -> Prop :=
  | restr_Econst :
    forall c,
      restr_exp (Econst c)
  | restr_Evar :
    forall x ann,
      restr_exp (Evar x ann)
  | restr_Eunop :
    forall op e ann,
      restr_exp e ->
      restr_exp (Eunop op e ann)
  | restr_Efby :
    forall e0s es anns,
      Forall restr_exp e0s ->
      Forall restr_exp es ->
      restr_exp (Efby e0s es anns)
  (* | restr_Eapp : *)
  (*   forall f es ers anns, *)
  (*     Forall restr_exp es -> *)
  (*     Forall restr_exp ers -> *)
  (*     restr_exp (Eapp f es ers anns) *)
  .

 Section EXP.

    (* Context {PSyn : block -> Prop}. *)
    (* Context {prefs : PS.t}. *)
    (* Parameter G : @global PSyn prefs. *)

    Fixpoint nprod (n : nat) : cpo :=
      match n with
      | O => DS unit
      | 1 => DS (sampl value)
      | S n => Dprod (DS (sampl value)) (nprod n)
      end.

    (* TODO: helper lemma ? *)
    Definition nprod_app : forall n p, nprod n -C-> nprod p -C-> nprod (n + p).
      induction n as [|[]]; intro p.
      - exact (CURRY _ _ _ (SND _ _ )).
      - destruct p.
        + exact (CTE _ _).
        + exact (PAIR _ _).
      - apply curry.
        exact ((PAIR _ _ @2_ (FST _ _ @_ FST _ _))
                 ((IHn p @2_ (SND _ _ @_ FST _ _)) (SND _ _))).
    Defined.

    Fixpoint lift (F : forall D, DS (sampl D) -C-> DS (sampl D)) n {struct n} : nprod n -C-> nprod n :=
      match n with
      | O => ID _
      | S n =>
          match n return nprod n -C-> nprod n -> nprod (S n) -C-> nprod (S n) with
          | O => fun _ => F _
          | S _ => fun fn => PROD_map (F _) fn
          end (lift F n)
      end.

    Definition lift2
      (F : forall A : Type, DS (sampl A) -C-> DS (sampl A) -C-> DS (sampl A)) n :
      nprod n -C-> nprod n -C-> nprod n.
      induction n as [|[]].
      - exact 0. (* ? *)
      - exact (F _).
      - apply curry.
        apply (fcont_comp2 (PAIR _ _)).
        exact ((F _ @2_ (FST _ _ @_ FST _ _ )) (FST _ _ @_ SND _ _ )).
        exact ((IHn @2_ (SND _ _ @_ FST _ _ )) (SND _ _ @_ SND _ _ )).
    Defined.

    Lemma lift2_simpl :
      forall F n u U v V,
        lift2 F (S (S n)) (u, U) (v, V) = (F _ u v, lift2 F (S n) U V).
    Proof.
      trivial.
    Qed.

    Fixpoint nprod_const (c : sampl value) n {struct n} : nprod n :=
      match n with
      | O => DS_const tt
      | S n =>
          match n return nprod n -> nprod (S n) with
          | O => fun _ => DS_const c
          | S m => fun np => (DS_const c, np)
          end (nprod_const c n)
      end.

    Variable vars : list (ident * (type * clock)).

    (* TODO: raffiner *)
    Definition type_vars (x : ident) : Type :=
      if existsb (ident_eqb x) (List.map fst vars)
      then sampl value
      else unit.

    Definition denot_exp (e : exp) : DS_prod type_vars -C-> DS bool -C-> nprod (numstreams e).
      apply curry.
      revert e.
      fix denot_exp 1.
      intro e.
      destruct e eqn:He; simpl (nprod _).
      - (* Econst *)
        exact (sconst (Vscalar (sem_cconst c)) @_ SND _ _).
      - (* Eenum *)
        exact (CTE _ _ 0).
      - (* Evar *)
        destruct (existsb (ident_eqb i) (List.map fst vars)) eqn:Heq.
        + eapply fcont_comp. 2: apply FST.
          eapply fcont_comp. 2: apply (PROJ _ i).
          unfold type_vars, DS_fam. rewrite Heq.
          exact (ID _).
        + exact (CTE _ _ (DS_const (err error_Ty))).
      - (* Elast *)
        exact (CTE _ _ 0).
      - (* Eunop *)
        specialize (denot_exp e0) as fe.
        destruct (numstreams e0) as [|[]].
        (* pas le bon nombre de flots: *)
        1,3: exact (CTE _ _ (DS_const (err error_Ty))).
        destruct (typeof e0) as [|ty []].
        (* pas le bon nombre de flots: *)
        1,3: exact (CTE _ _ (DS_const (err error_Ty))).
        exact (sunop (fun v => sem_unop u v ty) @_ fe).
      - (* Ebinop *)
        exact (CTE _ _ 0).
      - (* Efby *)
        rename l into e0s.
        rename l0 into es.
        rename l1 into anns.
        clear He.
        (* vérifier le typage *)
        destruct (Nat.eq_dec
                    (list_sum (List.map numstreams e0s))
                    (list_sum (List.map numstreams es))) as [Heq|].
        destruct (Nat.eq_dec
                    (length anns)
                    (list_sum (List.map numstreams es))
                 ) as [->|].
        (* si les tailles ne correspondent pas : *)
        2,3: exact (CTE _ _ (nprod_const (err error_Ty) _)).
        (* calculer les flots de e0s *)
        assert (Dprod (DS_prod type_vars) (DS bool) -C-> nprod (list_sum (List.map numstreams e0s))) as s0s.
        { clear Heq. induction e0s as [|a]; simpl (list_sum _).
          + exact (CTE _ _ (DS_const tt)).
          + exact ((nprod_app _ _ @2_ (denot_exp a)) IHe0s). }
        (* calculer les flots de es *)
        assert (Dprod (DS_prod type_vars) (DS bool) -C-> nprod (list_sum (List.map numstreams es))) as ss.
        { clear Heq. induction es as [|a]; simpl (list_sum _).
          + exact (CTE _ _ (DS_const tt)).
          + exact ((nprod_app _ _ @2_ (denot_exp a)) IHes). }
        rewrite Heq in s0s.
        exact ((lift2 (@SDfuns.fby) _ @2_ s0s) ss).
      - (* Earrow *)
        exact (CTE _ _ 0).
      - (* Ewhen *)
        exact (CTE _ _ 0).
      - (* Emerge *)
        exact (CTE _ _ 0).
      - (* Ecase *)
        exact (CTE _ _ 0).
      - (* Eapp *)
        exact (CTE _ _ 0).
    Defined.

    Ltac forward_apply A :=
      match type of A with
      | ?B -> ?C =>
          assert C; [ apply A |]
      end.

    (* deuxième idée, ne fonctionne pas non plus *)
    Definition denot_equation (e : equation) :
      DS_prod type_vars -C-> DS bool -C-> DS_prod type_vars.
      destruct e as (xs,es).
      (* vérification des tailles *)
      destruct (Nat.eq_dec
                  (length xs)
                  (list_sum (List.map numstreams es))
               ) as [Heq|].
      (* 2: exact (CTE _ _ 0). (* TODO : error_Ty *) *)
      2:{ (* TODO: plus joli *)
        apply curry, Dprodi_DISTR.
        intro. apply CTE. unfold type_vars. simpl.
        cases. exact (DS_const (err error_Ty)). exact (DS_const tt). }
      (* calcul des expressions *)
      apply curry.
      assert (Dprod (DS_prod type_vars) (DS bool) -C-> nprod (list_sum (List.map numstreams es))) as ss.
      { clear Heq. induction es as [|a]; simpl (list_sum _).
        + exact (CTE _ _ (DS_const tt)).
        + exact ((nprod_app _ _ @2_ (uncurry (denot_exp a))) IHes). }
      (* on incrémente ensuite le produit *)
      remember (list_sum (List.map numstreams es)) as n eqn:Hn. clear Hn.
      revert dependent n.
      induction xs as [| y xs]; intros.
      - exact (FST _ _).
      - subst.
        forward_apply (IHxs (length xs) eq_refl).
        { eapply fcont_comp. 2: apply ss.
          simpl (nprod _). cases. exact (CTE _ _ (DS_const tt)).
          exact (SND _ _). }
        eapply (fcont_comp X).
        eapply (fcont_comp2 (PAIR _ _)). 2: apply SND.
        eapply Dprodi_DISTR. intro x.
        destruct (ident_eqb x y).
        + unfold DS_fam, type_vars at 2.
          cases. { eapply (fcont_comp). 2: apply ss.
                   simpl. cases. exact (ID _). exact (FST _ _). }
          exact (CTE _ _ (DS_const tt)). (* TODO: plutôt error_Ty ? *)
        + exact (PROJ _ x @_ FST _ _).
    Defined.


    (* 1ère idée, n'a pas l'air de fonctionner *)
    Definition denot_equation' (e : equation) :
      DS_prod type_vars -C-> DS bool -C-> DS_prod type_vars.
      destruct e as (xs,es).
      (* vérification des tailles *)
      destruct (Nat.eq_dec
                  (length xs)
                  (list_sum (List.map numstreams es))
               ) as [Heq|].
      (* 2: exact (CTE _ _ 0). (* TODO : error_Ty *) *)
      2:{ (* TODO: plus joli *)
        apply curry, Dprodi_DISTR.
        intro. apply CTE. unfold type_vars. simpl.
        cases. exact (DS_const (err error_Ty)). exact (DS_const tt). }
      (* calcul des expressions *)
      apply curry.
      assert (Dprod (DS_prod type_vars) (DS bool) -C-> nprod (list_sum (List.map numstreams es))) as ss.
      { clear Heq. induction es as [|a]; simpl (list_sum _).
        + exact (CTE _ _ (DS_const tt)).
        + exact ((nprod_app _ _ @2_ (uncurry (denot_exp a))) IHes). }
      (* on construit le produit variable par variable *)
      apply Dprodi_DISTR.
      intro x.
      destruct (existsb (ident_eqb x) (List.map fst vars)) eqn:Hx.
      2:{ unfold DS_fam, type_vars at 2.
          rewrite Hx.
          exact (CTE _ _ (DS_const tt)). (* TODO: plutôt error_Ty ? *)
      }
      (* si la variable apparaît dans xs on prend la valeur calculée,
         sinon celle de l'environment *)
      remember (list_sum (List.map numstreams es)) as n eqn:Hn. clear Hn.
      revert dependent n.
      induction xs as [| y xs]; intros.
      - exact (PROJ _ x @_ FST _ _).
      - destruct n. inversion Heq.
        destruct (ident_eqb x y).
        + (* on prend l'expression *)
          unfold DS_fam, type_vars at 2. rewrite Hx.
          eapply fcont_comp. 2: apply ss.
          destruct n.
          * exact (ID _).
          * exact (FST _ _).
        + (* on passe à la suite *)
          inversion Heq; subst.
          eapply IHxs; eauto.
          eapply fcont_comp. 2: apply ss.
          destruct (length xs).
          * exact (CTE _ _ (DS_const tt)).
          * exact (SND _ _).
    Defined.

    End EXP.

End LDENOT.

Module LDenotFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS        Ids Op OpAux)
       (Senv  : STATICENV     Ids Op OpAux Cks)
       (Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
       (Typ   : LTYPING       Ids Op OpAux Cks Senv Syn)
       (Lord  : LORDERED      Ids Op OpAux Cks Senv Syn)
       (Str   : COINDSTREAMS  Ids Op OpAux Cks)
<: LDENOT Ids Op OpAux Cks Senv Syn Typ Lord Str.
  Include LDENOT Ids Op OpAux Cks Senv Syn Typ Lord Str.
End LDenotFun.
