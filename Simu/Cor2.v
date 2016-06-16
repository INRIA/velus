Require Import CommonCor.
Require Import Sem2.

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

  Inductive compat_cont: (* menv -> venv -> Clight.env -> Memory.Mem.mem -> *) cont -> Clight.cont -> Prop :=
  | compat_kstop: (* forall me ve e m, *)
      compat_cont (* me ve e m*) Kstop Clight.Kstop
  | compat_kseq: forall (* me ve e m *) s k k',
      well_formed_stmt c_main s ->
      (* compat_stmt me ve e m s -> *)
      compat_cont k k' ->
      compat_cont (* me ve e m *) (Kseq s k) (Clight.Kseq (translate_stmt main_node s) k').  

   
  Inductive match_states: state * stmt * cont -> Clight.state -> Prop :=
  | intro_state: forall me ve s k k' e le m,
      compat_venv c_main ve e m ->
      compat_menv main_node tprog c_main me e m ->
      well_formed_stmt c_main s ->
      compat_stmt main_node tprog me ve e m s ->
      compat_cont k k' ->
      mem_sep main_node c_main e m ->
      self_sep main_node e m ->
      fields_sep tprog m ->
      nodup_env e ->
      nodup_vars c_main ->
      nodup_mems c_main ->
      match_states
        ((me, ve), s, k)
        (Clight.State (main_fun main_node c_main) (translate_stmt main_node s) k' e le m).

  Hint Constructors Clight.eval_lvalue Clight.eval_expr well_formed_stmt.
  Hint Resolve expr_eval_simu Clight.assign_loc_value sem_cast_same.
  Hint Constructors compat_stmt well_formed_stmt.
  Hint Constructors match_states compat_cont.

  Lemma bool_val_compat:
  forall me ve m e v b l o,
    exp_eval me ve e v ->
    v <> Values.Vptr l o ->
    valid_val v (typeof e) ->
    bool_val v = Some b ->
    Cop.bool_val v (typeof e) m = Some b.
  Proof.
    intros ** Heval Hptr (Haccess & Hnotundef & Htype) Hbool_val.
    unfold Cop.bool_val.
    unfold chunk_of_typ in Haccess.
    admit.
  Qed.

  Theorem simu:
    forall S1 S2,
      stmt_eval_cont S1 S2 ->
      forall S1',
        match_states S1 S1' ->
        exists S2' t,
          Smallstep.plus Clight.step1 tge S1' t S2'
          /\ match_states S2 S2'.
  Proof.
    induction 1;
    inversion_clear 1 as [? ? ? ? ? ? ? ? Hvenv Hmenv Hwf Hstmt Hcont];
    inv Hwf; inversion_clear Hstmt; destruct_conjs.
    
    (* Assign x e : "x = e" *)
    - app_exp_eval_det.
      edestruct compat_assign_pres as [m']; eauto; destruct_conjs. 
      do 2 econstructor; split.
      + eapply Smallstep.plus_one, Clight.step_assign; eauto.
        * eapply expr_eval_simu; eauto. 
        * rewrite type_pres; auto. 
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