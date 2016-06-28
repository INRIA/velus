Require Import cfrontend.Clight.
Require Import cfrontend.ClightBigstep.
Require Import cfrontend.Cop.
Require Import cfrontend.Ctypes.
Require Import common.Events.
Require Import common.Memory.
Require Import common.Values.
Require Import common.Globalenvs.
Require Import lib.Maps.
Require Import lib.Coqlib.

Section BIGSTEP.

  Variable ge: genv.
  Inductive exec_stmt_2: env -> temp_env -> mem -> statement -> trace -> temp_env -> mem -> outcome -> Prop :=
  | exec_Sskip: forall e le m,
      exec_stmt_2 e le m Sskip
                E0 le m Out_normal
  | exec_Sassign: forall e le m a1 a2 loc ofs v2 v m',
      eval_lvalue ge e le m a1 loc ofs ->
      eval_expr ge e le m a2 v2 ->
      sem_cast v2 (typeof a2) (typeof a1) = Some v ->
      assign_loc ge (typeof a1) m loc ofs v m' ->
      exec_stmt_2 e le m (Sassign a1 a2)
                E0 le m' Out_normal
  | exec_Sset: forall e le m id a v,
      eval_expr ge e le m a v ->
      exec_stmt_2 e le m (Sset id a)
                E0 (PTree.set id v le) m Out_normal
  | exec_Scall: forall e le m optid a al tyargs tyres cconv vf vargs f t m' vres,
      classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
      eval_expr ge e le m a vf ->
      eval_exprlist ge e le m al tyargs vargs ->
      Genv.find_funct ge vf = Some f ->
      type_of_fundef f = Tfunction tyargs tyres cconv ->
      eval_funcall_2 m f vargs t m' vres ->
      exec_stmt_2 e le m (Scall optid a al)
                t (set_opttemp optid vres le) m' Out_normal
  | exec_Sbuiltin: forall e le m optid ef al tyargs vargs t m' vres,
      eval_exprlist ge e le m al tyargs vargs ->
      external_call ef ge vargs m t vres m' ->
      exec_stmt_2 e le m (Sbuiltin optid ef tyargs al)
                t (set_opttemp optid vres le) m' Out_normal
  | exec_Sseq_1: forall e le m s1 s2 t1 le1 m1 t2 le2 m2 out,
      exec_stmt_2 e le m s1 t1 le1 m1 Out_normal ->
      exec_stmt_2 e le1 m1 s2 t2 le2 m2 out ->
      exec_stmt_2 e le m (Ssequence s1 s2)
                (t1 ** t2) le2 m2 out
  | exec_Sseq_2: forall e le m s1 s2 t1 le1 m1 out,
      exec_stmt_2 e le m s1 t1 le1 m1 out ->
      out <> Out_normal ->
      exec_stmt_2 e le m (Ssequence s1 s2)
                t1 le1 m1 out
  | exec_Sifthenelse: forall e le m a s1 s2 v1 b t le' m' out,
      eval_expr ge e le m a v1 ->
      bool_val v1 (typeof a) m = Some b ->
      exec_stmt_2 e le m (if b then s1 else s2) t le' m' out ->
      exec_stmt_2 e le m (Sifthenelse a s1 s2)
                t le' m' out
  | exec_Sreturn_none: forall e le m,
      exec_stmt_2 e le m (Sreturn None)
                E0 le m (Out_return None)
  | exec_Sreturn_some: forall e le m a v,
      eval_expr ge e le m a v ->
      exec_stmt_2 e le m (Sreturn (Some a))
                E0 le m (Out_return (Some (v, typeof a)))
  | exec_Sbreak: forall e le m,
      exec_stmt_2 e le m Sbreak
                E0 le m Out_break
  | exec_Scontinue: forall e le m,
      exec_stmt_2 e le m Scontinue
                E0 le m Out_continue
  | exec_Sloop_stop1: forall e le m s1 s2 t le' m' out' out,
      exec_stmt_2 e le m s1 t le' m' out' ->
      out_break_or_return out' out ->
      exec_stmt_2 e le m (Sloop s1 s2)
                t le' m' out
  | exec_Sloop_stop2: forall e le m s1 s2 t1 le1 m1 out1 t2 le2 m2 out2 out,
      exec_stmt_2 e le m s1 t1 le1 m1 out1 ->
      out_normal_or_continue out1 ->
      exec_stmt_2 e le1 m1 s2 t2 le2 m2 out2 ->
      out_break_or_return out2 out ->
      exec_stmt_2 e le m (Sloop s1 s2)
                (t1**t2) le2 m2 out
  | exec_Sloop_loop: forall e le m s1 s2 t1 le1 m1 out1 t2 le2 m2 t3 le3 m3 out,
      exec_stmt_2 e le m s1 t1 le1 m1 out1 ->
      out_normal_or_continue out1 ->
      exec_stmt_2 e le1 m1 s2 t2 le2 m2 Out_normal ->
      exec_stmt_2 e le2 m2 (Sloop s1 s2) t3 le3 m3 out ->
      exec_stmt_2 e le m (Sloop s1 s2)
                (t1**t2**t3) le3 m3 out
  | exec_Sswitch: forall e le m a t v n sl le1 m1 out,
      eval_expr ge e le m a v ->
      sem_switch_arg v (typeof a) = Some n ->
      exec_stmt_2 e le m (seq_of_labeled_statement (select_switch n sl)) t le1 m1 out ->
      exec_stmt_2 e le m (Sswitch a sl)
                t le1 m1 (outcome_switch out)

  with eval_funcall_2: mem -> fundef -> list val -> trace -> mem -> val -> Prop :=
       | eval_funcall_internal: forall le m f vargs t e m1 le' m2 m3 out vres,
           list_norepet (var_names f.(fn_vars)) ->
           list_norepet (var_names f.(fn_params)) ->
           list_disjoint (var_names f.(fn_params)) (var_names f.(fn_temps)) ->
           alloc_variables ge empty_env m f.(fn_vars) e m1 ->
           bind_parameter_temps f.(fn_params) vargs (create_undef_temps f.(fn_temps)) = Some le ->
           exec_stmt_2 e le m1 f.(fn_body) t le' m2 out ->
           outcome_result_value out f.(fn_return) vres ->
           Mem.free_list m2 (blocks_of_env ge e) = Some m3 ->
           eval_funcall_2 m (Internal f) vargs t m3 vres
       | eval_funcall_external: forall m ef targs tres cconv vargs t vres m',
           external_call ef ge vargs m t vres m' ->
           eval_funcall_2 m (External ef targs tres cconv) vargs t m' vres.

End BIGSTEP.