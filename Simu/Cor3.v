Require Import CommonCor.
Require Import Sem2.
Require cfrontend.ClightBigstep.

(* SIMULATION *)

Section SIMU.

  Variable main_node : ident.
  Variable prog: program.
  Variable tprog: Clight.program.
  Variable c_main: class.
  Variable cls_main: list class.
  
  (* Let ge := globalenv prog. *)
  Let tge := Clight.globalenv tprog.
  
  Hypothesis TRANSL: translate prog main_node = Errors.OK tprog.
  (* Hypothesis WF: well_formed prog. *)
  Hypothesis MAINNODE: find_class main_node prog = Some (c_main, cls_main).

  Definition c_state := (Clight.env * Clight.temp_env * Memory.Mem.mem)%type.
   
  Inductive match_states: state -> c_state -> Prop :=
  | intro_state: forall me ve e le m,
      compat_venv c_main ve e m ->
      compat_menv main_node tprog c_main me e m ->
      mem_sep main_node c_main e m ->
      self_sep main_node e m ->
      fields_sep tprog m ->
      nodup_env e ->
      nodup_vars c_main ->
      nodup_mems c_main ->
      match_states
        (me, ve)
        (e, le, m).

  Hint Constructors Clight.eval_lvalue Clight.eval_expr well_formed_stmt.
  Hint Resolve expr_eval_simu Clight.assign_loc_value sem_cast_same.
  Hint Constructors compat_stmt well_formed_stmt.
  Hint Constructors match_states.

  Definition big_step (st: c_state) s t (st': c_state) : Prop :=
    let '(e, le, m) := st in
    let '(e', le', m') := st' in
    ClightBigstep.exec_stmt tge e le m s t le' m' ClightBigstep.Out_normal.   
  
  Theorem simu:
    forall me1 ve1 s S2,
      well_formed_stmt c_main s ->
      stmt_eval (me1, ve1) s S2 ->
      forall e1 le1 m1,
        match_states (me1, ve1) (e1, le1, m1) ->
        compat_stmt main_node tprog me1 ve1 e1 m1 s ->
        exists S2' t,
          big_step (e1, le1, m1) (translate_stmt main_node s) t S2'
          /\ match_states S2 S2'.
  Proof.
    intros until S2; intro Hwf.
    induction 1;
    inversion_clear 1 as [? ? ? ? ? Hvenv Hmenv];
    inv Hwf; inversion_clear 1.  
    
    (* Assign x e : "x = e" *)
    - edestruct compat_assign_pres as [m']; eauto; destruct_conjs. admit.
      exists (e1, le1, m'), Events.E0; split.
      + eapply ClightBigstep.exec_Sassign; eauto. 
        * eapply expr_eval_simu; eauto. 
        * rewrite type_pres; auto. admit.
      + constructor; auto. 

    (* AssignSt x e : "self->x = e"*)
    - app_exp_eval_det.
      edestruct compat_stassign_pres as [m']; eauto; destruct_conjs. 
      do 2 econstructor; split.
      + eapply Smallstep.plus_one, Clight.step_assign; eauto.
        *{ eapply Clight.eval_Efield_struct
           with (id:=main_node) (att:=Ctypes.noattr); eauto.
           eapply Clight.eval_Elvalue; eauto. 
           - apply Clight.eval_Ederef. 
             eapply Clight.eval_Elvalue; eauto.
             apply Clight.deref_loc_value with (chunk:=AST.Mint32); eauto.
           - apply Clight.deref_loc_copy; auto.
         }
        * eapply expr_eval_simu; eauto.
        * rewrite type_pres; auto. 
      + constructor; auto. 

    (* Ifte e s1 s2 : "if e then s1 else s2" *)
    - do 2 econstructor; split.      
      + eapply Smallstep.plus_one, Clight.step_ifthenelse.
        * eapply expr_eval_simu; eauto.
        * erewrite type_pres, bool_val_ptr; eauto. 
      + destruct b; econstructor; auto.         

    (* Comp s1 s2 : "s1; s2" *)
    - do 2 econstructor; split.
      + eapply Smallstep.plus_one, Clight.step_seq.
      + constructor; auto. 
     
    (* Skip : "skip" *)
    - inv Hcont.
      do 2 econstructor; split.
      + eapply Smallstep.plus_one, Clight.step_skip_seq.
      + constructor; auto. admit.
  Qed.