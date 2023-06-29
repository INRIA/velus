From Coq Require Import FSets.FMapPositive.
From Coq Require Import Setoid.
From Coq Require Import List.
From Coq Require Import String.
Import List.ListNotations.
Open Scope list_scope.

From compcert Require Import common.Errors.

From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import VelusMemory.
From Velus Require Import Obc.ObcSyntax.
From Velus Require Import Obc.ObcSemantics.

(** * Obc interpreter *)

Module Type OBCINTERPRETER
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Syn   : OBCSYNTAX Ids Op OpAux)
       (Import Sem   : OBCSEMANTICS Ids Op OpAux Syn).

  Open Scope error_monad_scope.

  Section eval_stmt.

    Variable eval_method : menv -> ident -> ident -> list (option value) -> res (menv * list (option value)).

    Fixpoint eval_exp (me: menv) (ve: venv) (e: exp) : res (option value) :=
      match e with
      | Var x _ => OK (Env.find x ve)
      | State x _ _ =>
          match find_val x me with
          | Some v => OK (Some v)
          | None => Error (msg "state variable absent")
          end
      | Const c => OK (Some (Vscalar (sem_cconst c)))
      | Enum e _ => OK (Some (Venum e))
      | Unop op e _ =>
          do v1 <- eval_exp me ve e;
          match v1 with
          | Some v =>
              match sem_unop op v (typeof e) with
              | Some v => OK (Some v)
              | None => Error (msg "unary operator failure")
              end
          | _ => Error (msg "unary operator input cannot be absent")
          end
      | Binop op e1 e2 _ =>
          do v1 <- eval_exp me ve e1;
          do v2 <- eval_exp me ve e2;
          match v1, v2 with
          | Some v1, Some v2 =>
              match sem_binop op v1 (typeof e1) v2 (typeof e2) with
              | Some v => OK (Some v)
              | None => Error (msg "binary operator failure")
              end
          | _, _ => Error (msg "binary operator input cannot be absent")
          end
      | Valid x _ =>
          match Env.find x ve with
          | Some v => OK (Some v)
          | None => Error (msg "valid variable absent")
          end
      end.

    Section eval_stmt_branch.
      Variable eval_stmt : menv -> venv -> stmt -> res (menv * venv).
      Variable (me : menv) (ve : venv).
      Variable default : stmt.

      Fixpoint eval_stmt_branch
        (branches : list (option stmt)) (c : nat) : res (menv * venv) :=
        match branches, c with
        | Some stmt::_, 0 => eval_stmt me ve stmt
        | None::_, 0 => eval_stmt me ve default
        | _::branches, S n => eval_stmt_branch branches n
        | [], _ => Error (msg "not enough branches in switch")
        end.
    End eval_stmt_branch.

    Fixpoint eval_stmt (me : menv) (ve : venv) (s : stmt) {struct s} : res (menv * venv) :=
      match s with
      | Assign x e =>
          do v <- eval_exp me ve e;
          match v with
          | None => Error (msg "value in assign is absent")
          | Some v => OK (me, Env.add x v ve)
          end
      | AssignSt x e _ =>
          do v <- eval_exp me ve e;
          match v with
          | None => Error (msg "value in stassign is absent")
          | Some v => OK (add_val x v me, ve)
          end
      | Call ys clsid o f es =>
          do vos <- Errors.mmap (eval_exp me ve) es;
          do (ome', rvos) <- eval_method (instance_match o me) clsid f vos;
          OK (add_inst o ome' me, Env.adds_opt ys rvos ve)
      | ExternCall _ _ _ _ => Error (msg "extern calls not supported in interpreter")
      | Comp stmt1 stmt2 =>
          do (me1, ve1) <- eval_stmt me ve stmt1;
          eval_stmt me1 ve1 stmt2
      | Switch cond branches default =>
          do v <- eval_exp me ve cond;
          match v with
          | Some (Venum c) =>
              eval_stmt_branch eval_stmt me ve default branches c
          | _ => Error (msg "condition of switch didnt produce an enumerated value")
          end
      | Skip => OK (me, ve)
      end.

  End eval_stmt.

  Definition eval_method (p : program) : menv -> ident -> ident -> list (option value) -> res (menv * list (option value)) :=
    (fix aux (cls : list class) me clsid f vos :=
       match cls with
       | [] => Error (MSG "Class " :: CTX clsid :: msg " not found")
       | cl::cls => if cl.(c_name) ==b clsid
                  then match find_method f cl.(c_methods) with
                       | Some fm =>
                           if negb (List.length vos ==b List.length fm.(m_in))
                           then Error (msg ("Not the correct number of argument"))
                           else
                             do (me', ve') <- eval_stmt (aux cls) me (Env.adds_opt (map fst fm.(m_in)) vos vempty) fm.(m_body);
                             OK (me', map (fun x => Env.find x ve') (map fst fm.(m_out)))
                       | None => Error (MSG "Method " :: CTX f :: msg " not found")
                       end
                  else aux cls me clsid f vos
       end) p.(classes).

  (** ** Correctness *)

  Lemma eval_exp_correct : forall me ve e v,
      eval_exp me ve e = OK v ->
      exp_eval me ve e v.
  Proof.
    induction e; intros * Heval; simpl in *; try monadInv Heval; try constructor.
    - (* State *)
      cases_eqn Heq. monadInv Heval. now constructor.
    - (* Unop *)
      cases_eqn EQ; monadInv EQ0.
      econstructor; eauto.
    - (* Binop *)
      cases_eqn EQ; monadInv EQ2.
      econstructor; eauto.
    - (* Valid *)
      cases_eqn EQ; monadInv Heval.
      now constructor.
  Qed.

  Fact eval_stmt_branch_inv eval_method : forall me ve default k branches me' ve',
    eval_stmt_branch (eval_stmt eval_method) me ve default branches k = OK (me', ve') ->
    exists s,
      nth_error branches k = Some s
      /\ eval_stmt eval_method me ve (or_default default s) = OK (me', ve').
  Proof.
    induction k; intros * Heval; destruct branches; simpl in *; try monadInv Heval.
    1,2:cases; eauto.
  Qed.

  Lemma eval_stmt_correct eval_method p : forall st me ve me' ve',
      (forall me clsid f vos me' rvos,
          eval_method me clsid f vos = OK (me', rvos) ->
          stmt_call_eval p me clsid f vos me' rvos) ->
      eval_stmt eval_method me ve st = OK (me', ve') ->
      stmt_eval p me ve st (me', ve').
  Proof.
    induction st using stmt_ind2';
      intros * Hmethod Heval; simpl in *; try monadInv Heval; try constructor.
    - (* Assign *)
      cases_eqn EQ. monadInv EQ0.
      constructor; auto using eval_exp_correct.
    - (* StAssign *)
      cases_eqn EQ. monadInv EQ0.
      constructor; auto using eval_exp_correct.
    - (* Switch *)
      cases_eqn EQ; subst.
      apply eval_stmt_branch_inv in EQ0 as (?&Hnth&Heval).
      econstructor; eauto using eval_exp_correct.
      apply nth_error_In in Hnth. simpl_Forall.
      destruct x; simpl in *; eauto.
    - (* Comp *)
      econstructor; eauto.
    - (* Call *)
      eapply Icall with (vos:=x); eauto.
      + clear - EQ. apply mmap_inversion in EQ.
        induction EQ; constructor; auto using eval_exp_correct.
  Qed.

  Theorem eval_method_correct : forall p me clsid f vos me' rvos,
    eval_method p me clsid f vos = OK (me', rvos) ->
    stmt_call_eval p me clsid f vos me' rvos.
  Proof.
    unfold eval_method, find_class. intros [].
    induction classes0; intros * Heval; simpl in *. monadInv Heval.
    destruct (c_name _ ==b clsid) eqn:Heq.
    - rewrite equiv_decb_equiv in Heq. inv Heq.
      destruct (find_method _ _) eqn:Hfind'; [|monadInv Heval].
      destruct (_ ==b _) eqn:Hlen; simpl in *; monadInv Heval.
      rewrite equiv_decb_equiv in Hlen.
      econstructor; eauto.
      + setoid_rewrite find_unit_now; reflexivity.
      + eapply eval_stmt_correct in EQ; eauto.
      + now simpl_Forall.
    - rewrite not_equiv_decb_equiv in Heq.
      eapply IHclasses0 in Heval. inv Heval.
      econstructor; eauto.
      setoid_rewrite find_unit_other; eauto.
      intros ?; reflexivity.
  Qed.

  (** ** Completeness *)

  Lemma eval_exp_complete : forall me ve e v,
      exp_eval me ve e v ->
      eval_exp me ve e = OK v.
  Proof.
    induction e; intros * Hsem; inv Hsem; simpl; auto.
    - (* State *)
      take (find_val _ _ = _) and now rewrite it.
    - (* Unop *)
      erewrite IHe; eauto. simpl.
      take (sem_unop _ _ _ = _) and now rewrite it.
    - (* Binop *)
      erewrite IHe1, IHe2; eauto. simpl.
      take (sem_binop _ _ _ _ _ = _) and now rewrite it.
    - (* Valid *)
      take (Env.find _ _ = _) and now rewrite it.
  Qed.

End OBCINTERPRETER.

Module ObcInterpreterFun
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Syn   : OBCSYNTAX Ids Op OpAux)
       (Import Sem   : OBCSEMANTICS Ids Op OpAux Syn) <: OBCINTERPRETER Ids Op OpAux Syn Sem.
  Include OBCINTERPRETER Ids Op OpAux Syn Sem.
End ObcInterpreterFun.
