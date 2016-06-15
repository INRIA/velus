Require Import CommonCor.
Require Import Sem.

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


  (* Inductive match_states: state * stmt * cont -> Clight.state -> Prop := *)
  (* | intro_state: forall me ve s k k' e le m, *)
  (*     compat_venv c_main ve e m -> *)
  (*     compat_menv main_node tprog c_main me e m -> *)
  (*     well_formed_stmt c_main s -> *)
  (*     compat_stmt main_node tprog me ve e m s -> *)
  (*     compat_cont k k' -> *)
  (*     mem_sep main_node c_main e m -> *)
  (*     self_sep main_node e m -> *)
  (*     fields_sep tprog m -> *)
  (*     nodup_env e -> *)
  (*     nodup_vars c_main -> *)
  (*     nodup_mems c_main -> *)
  (*     match_states *)
  (*       ((me, ve), s, k) *)
  (*       (Clight.State (main_fun main_node c_main) (translate_stmt main_node s) k' e le m). *)
     
  Inductive match_states: state -> Clight.state -> Prop :=
    intro_state: forall me ve s k e le m,
      compat_venv c_main ve e m ->
      compat_menv main_node tprog c_main me e m ->
      well_formed_stmt c_main s ->
      compat_stmt main_node tprog me ve e m s ->
      state_context (me, ve, s) k e le m ->
      mem_sep main_node c_main e m ->
      self_sep main_node e m ->
      fields_sep tprog m ->
      nodup_env e ->
      nodup_vars c_main ->
      nodup_mems c_main ->
      match_states
        (me, ve, s)
        (Clight.State (main_fun main_node c_main) (translate_stmt main_node s) k e le m)

  with state_context: state -> Clight.cont -> Clight.env -> Clight.temp_env -> Memory.Mem.mem -> Prop :=
       | ctxt_assign: forall me ve x e k env le m,
           state_context (me, ve, Assign x e) k env le m
       | ctxt_stassign: forall me ve x e k env le m,
           state_context (me, ve, AssignSt x e) k env le m
       | ctxt_comp: forall me1 ve1 s1 me2 ve2 s2 me3 ve3 k e le m m' m'',
           match_states
             (me1, ve1, s1)
             (Clight.State (main_fun main_node c_main)
                           (translate_stmt main_node s1)
                           (Clight.Kseq (translate_stmt main_node s2) k) e le m) ->
           stmt_eval (me1, ve1, s1) (me2, ve2, Skip) ->
           match_states
             (me2, ve2, Skip)
             (Clight.State (main_fun main_node c_main)
                           (translate_stmt main_node Skip)
                           (Clight.Kseq (translate_stmt main_node s2) k) e le m') ->
           match_states
             (me2, ve2, s2)
             (Clight.State (main_fun main_node c_main) (translate_stmt main_node s2) k e le m') ->
           stmt_eval (me2, ve2, s2) (me3, ve3, Skip) ->
           match_states
             (me3, ve3, Skip)
             (Clight.State (main_fun main_node c_main) (translate_stmt main_node Skip) k e le m'') ->
           state_context (me1, ve1, Comp s1 s2) k e le m
       | ctxt_skip_comp: forall me ve s me' ve' k e le m m',
          match_states
             (me, ve, s)
             (Clight.State (main_fun main_node c_main) (translate_stmt main_node s) k e le m) ->
          stmt_eval (me, ve, s) (me', ve', Skip) ->
          match_states
             (me', ve', Skip)
             (Clight.State (main_fun main_node c_main) (translate_stmt main_node Skip) k e le m') ->
          state_context (me, ve, Comp Skip s) k e le m
       | ctxt_skip: forall me ve k e le m,
           state_context (me, ve, Skip) k e le m.
  
  Hint Resolve expr_eval_simu Clight.assign_loc_value sem_cast_same.
  Hint Constructors compat_stmt state_context.

  Ltac discriminate' :=
    match goal with
    | H: ?x <> ?x |- _ => contradict H; reflexivity
    end.
  
  Theorem simu:
    forall S1 S2,
      stmt_eval S1 S2 ->
      forall S1',
        match_states S1 S1' ->
        exists S2' t,
          Smallstep.plus Clight.step1 tge S1' t S2'
          /\ match_states S2 S2'.
  Proof.
    induction 1;
    inversion_clear 1 as [? ? ? ? ? ? ? Hvenv Hmenv Hwf Hstmt Hctxt]; 
    inv Hwf; inversion_clear Hstmt; inversion Hctxt;
    (((subst s1 || subst s2); inv_stmt_eval) || destruct_conjs).
    
    (* Assign x e : "x = e" *)
    - app_exp_eval_det.
      edestruct compat_assign_pres as [m']; eauto; destruct_conjs. 
      exists (Clight.State (main_fun main_node c_main) Clight.Sskip k e0 le m'), Events.E0; split.
      + eapply Smallstep.plus_one, Clight.step_assign; eauto.
        * eapply expr_eval_simu; eauto.
        * rewrite type_pres; auto. 
      + constructor; (tauto || auto). 
        
    (* AssignSt x e : "self->x = e"*)
    - app_exp_eval_det.
      edestruct compat_stassign_pres as [m']; eauto; destruct_conjs. 
      exists (Clight.State (main_fun main_node c_main) Clight.Sskip k e0 le m'), Events.E0; split.
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
      + constructor; (tauto || auto). 

    (* Comp s1 s2 : "s1; s2" *)
    - repeat app_stmt_eval_det.
      edestruct IHstmt_eval1 as [S2' [t1 [Step1 ?]]]; eauto.
      edestruct IHstmt_eval2 as [S3' [t2 [Step2 ?]]]; eauto.
      assert (S2' = Clight.State (main_fun main_node c_main)
               (translate_stmt main_node Skip)
               (Clight.Kseq (translate_stmt main_node s2) k) e le m'). admit. subst S2'.
      assert (S3' = Clight.State (main_fun main_node c_main) (translate_stmt main_node Skip) k e le m''). admit. subst S3'.
      exists (Clight.State (main_fun main_node c_main) (translate_stmt main_node Skip) k e le m''), Events.E0; split; auto.
      eapply Smallstep.plus_left' with
      (s2:=Clight.State (main_fun main_node c_main) (translate_stmt main_node s1)
                        (Clight.Kseq (translate_stmt main_node s2) k) e le m)
        (t1:=Events.E0) (t2:=Events.E0); auto.
      + eapply Clight.step_seq.
      + eapply Smallstep.plus_trans; eauto.
        *{ eapply Smallstep.plus_left' with
          (s2:=Clight.State (main_fun main_node c_main) (translate_stmt main_node s2) k e le m')
            (t1:=Events.E0) (t2:=Events.E0); auto.
           - apply Clight.step_skip_seq.
           - assert (t2 = Events.E0). admit. subst t2; auto.
         }
        * assert (t1 = Events.E0). admit. subst t1; auto.

    (* Comp Skip s : "skip; s" *)
    - repeat app_stmt_eval_det.
      edestruct IHstmt_eval as [S2' [t1 [Step1 Match2]]]; eauto.
      assert (S2' = Clight.State (main_fun main_node c_main) (translate_stmt main_node Skip) k e le m'). admit. subst S2'.
      exists (Clight.State (main_fun main_node c_main) (translate_stmt main_node Skip) k e le m'), Events.E0; split; auto.
      eapply Smallstep.plus_left' with
      (s2:=Clight.State (main_fun main_node c_main) (translate_stmt main_node Skip)
                        (Clight.Kseq (translate_stmt main_node s) k) e le m)
        (t1:=Events.E0) (t2:=Events.E0); auto.
      + eapply Clight.step_seq.
      + eapply Smallstep.plus_left' with
        (s2:=Clight.State (main_fun main_node c_main) (translate_stmt main_node s) k e le m)
          (t1:=Events.E0) (t2:=Events.E0); auto.
        * apply Clight.step_skip_seq.
        * assert (t1 = Events.E0). admit. subst t1; auto.
  Qed.