Require Import List.
Import List.ListNotations.
Open Scope list_scope.

(* Require Import Coq.Sorting.Permutation. *)
(* Require Import Setoid. *)
(* Require Import Morphisms. *)
(* Require Import Coq.Arith.EqNat. *)

(* Require Import Coq.FSets.FMapPositive. *)
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.RMemory.
Require Import Velus.SyMac.SMSyntax.
(* Require Import Velus.NLustre.Ordered. *)
Require Import Velus.NLustre.Stream.


Module Type SMSEMANTICS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Clks  : CLOCKS    Ids)
       (Import Syn   : SMSYNTAX  Ids Op Clks)
       (Import Str   : STREAM        Op OpAux).

  Definition env := PM.t value.
  Definition history := PM.t (stream value).

  Definition memory := RMemory.memory (list value).
  Definition memories := RMemory.memory (list (stream value)).

  Fixpoint find_init (x: ident) (mems: list (ident * const)): option value :=
    match mems with
    | [] => None
    | m :: mems =>
      if ident_eqb (fst m) x
      then Some (present (sem_const (snd m))) else find_init x mems
    end.

  Definition get_mem (k: nat) (init: bool) (x: ident) (m: memory) (mems: list (ident * const)):=
    if init then find_init x mems
    else match mfind_mem x m with
         | Some lv =>
           match k with
           | 0 => nth_error lv 0
           | S k' =>
             match nth_error lv k' with
             | Some absent => nth_error lv k
             | None => None
             | v => v
             end
           end
         | None => None
         end.

  (** ** Instantaneous semantics *)

  Section InstantSemantics.

    Variable init: bool.
    Variable base: bool.
    Variable R: env.
    Variable m: memory.
    Variable k: nat.
    Variable mems: list (ident * const).

    Inductive sem_var_instant: ident -> value -> Prop :=
      Sv:
        forall x v,
          PM.find x R = Some v ->
          sem_var_instant x v.

    Inductive sem_mem_var_instant: ident -> value -> Prop :=
      Smv:
        forall x v,
          get_mem k init x m mems = Some v ->
          sem_mem_var_instant x v.

    Inductive sem_clock_instant: clock -> bool -> Prop :=
    | Sbase:
        sem_clock_instant Cbase base
    | Son:
        forall ck x c b,
          sem_clock_instant ck true ->
          sem_var_instant x (present c) ->
          val_to_bool c = Some b ->
          sem_clock_instant (Con ck x b) true
    | Son_abs1:
        forall ck x c,
          sem_clock_instant ck false ->
          sem_var_instant x absent ->
          sem_clock_instant (Con ck x c) false
    | Son_abs2:
        forall ck x c b,
          sem_clock_instant ck true ->
          sem_var_instant x (present c) ->
          val_to_bool c = Some b ->
          sem_clock_instant (Con ck x (negb b)) false.

    Inductive sem_lexp_instant: lexp -> value -> Prop:=
    | Sconst:
        forall c v,
          v = (if base then present (sem_const c) else absent) ->
          sem_lexp_instant (Econst c) v
    | Svar:
        forall x v ty,
          sem_var_instant x v ->
          sem_lexp_instant (Evar x ty) v
    | Slast:
        forall x ck b v ty,
          sem_clock_instant ck b ->
          sem_mem_var_instant x v ->
          sem_lexp_instant (Emem x ck ty) v
    | Swhen_eq:
        forall s x sc xc b,
          sem_var_instant x (present xc) ->
          sem_lexp_instant s (present sc) ->
          val_to_bool xc = Some b ->
          sem_lexp_instant (Ewhen s x b) (present sc)
    | Swhen_abs1:
        forall s x sc xc b,
          sem_var_instant x (present xc) ->
          val_to_bool xc = Some b ->
          sem_lexp_instant s (present sc) ->
          sem_lexp_instant (Ewhen s x (negb b)) absent
    | Swhen_abs:
        forall s x b,
          sem_var_instant x absent ->
          sem_lexp_instant s absent ->
          sem_lexp_instant (Ewhen s x b) absent
    | Sunop_eq:
        forall le op c c' ty,
          sem_lexp_instant le (present c) ->
          sem_unop op c (typeof le) = Some c' ->
          sem_lexp_instant (Eunop op le ty) (present c')
    | Sunop_abs:
        forall le op ty,
          sem_lexp_instant le absent ->
          sem_lexp_instant (Eunop op le ty) absent
    | Sbinop_eq:
        forall le1 le2 op c1 c2 c' ty,
          sem_lexp_instant le1 (present c1) ->
          sem_lexp_instant le2 (present c2) ->
          sem_binop op c1 (typeof le1) c2 (typeof le2) = Some c' ->
          sem_lexp_instant (Ebinop op le1 le2 ty) (present c')
    | Sbinop_abs:
        forall le1 le2 op ty,
          sem_lexp_instant le1 absent ->
          sem_lexp_instant le2 absent ->
          sem_lexp_instant (Ebinop op le1 le2 ty) absent.

    Definition sem_lexps_instant (les: list lexp) (vs: list value) :=
      Forall2 sem_lexp_instant les vs.

    Inductive sem_cexp_instant: cexp -> value -> Prop :=
    | Smerge_true:
        forall x t f c,
          sem_var_instant x (present true_val) ->
          sem_cexp_instant t (present c) ->
          sem_cexp_instant f absent ->
          sem_cexp_instant (Emerge x t f) (present c)
    | Smerge_false:
        forall x t f c,
          sem_var_instant x (present false_val) ->
          sem_cexp_instant t absent ->
          sem_cexp_instant f (present c) ->
          sem_cexp_instant (Emerge x t f) (present c)
    | Smerge_abs:
        forall x t f,
          sem_var_instant x absent ->
          sem_cexp_instant t absent ->
          sem_cexp_instant f absent ->
          sem_cexp_instant (Emerge x t f) absent
    | Site_eq:
        forall x t f c b ct cf,
          sem_lexp_instant x (present c) ->
          sem_cexp_instant t (present ct) ->
          sem_cexp_instant f (present cf) ->
          val_to_bool c = Some b ->
          sem_cexp_instant (Eite x t f) (if b then present ct else present cf)
    | Site_abs:
        forall b t f,
          sem_lexp_instant b absent ->
          sem_cexp_instant t absent ->
          sem_cexp_instant f absent ->
          sem_cexp_instant (Eite b t f) absent
    | Sexp:
        forall e v,
          sem_lexp_instant e v ->
          sem_cexp_instant (Eexp e) v.

    (* Inductive rhs_absent_instant: equation -> Prop := *)
    (* | AEqDef: *)
    (*     forall x ck cae, *)
    (*       sem_caexp_instant ck cae absent -> *)
    (*       rhs_absent_instant (EqDef x ck cae) *)
    (* | AEqApp: *)
    (*     forall x f ck laes vs, *)
    (*       sem_laexps_instant ck laes vs -> *)
    (*       absent_list vs -> *)
    (*       rhs_absent_instant (EqApp x ck f laes None) *)
    (* | AEqReset: *)
    (*     forall x f ck laes vs r ck_r, *)
    (*       sem_laexps_instant ck laes vs -> *)
    (*       absent_list vs -> *)
    (*       (* sem_avar_instant ck_r r absent -> *) *)
    (*       rhs_absent_instant (EqApp x ck f laes (Some (r, ck_r))) *)
    (* | AEqFby: *)
    (*     forall x ck v0 lae, *)
    (*       sem_laexp_instant ck lae absent -> *)
    (*       rhs_absent_instant (EqFby x ck v0 lae). *)

  End InstantSemantics.

  Section InstantAnnotatedSemantics.
    Variable init : bool.
    Variable base : bool.
    Variable R: env.
    Variable m: memory.
    Variable k: nat.
    Variable mems: list (ident * const).

    Inductive sem_annotated_instant {A}
              (sem_instant: bool -> bool -> env -> memory -> nat -> list (ident * const) -> A -> value -> Prop)
      : clock -> A -> value -> Prop :=
    | Stick:
        forall ck a c,
          sem_instant init base R m k mems a (present c) ->
          sem_clock_instant base R ck true ->
          sem_annotated_instant sem_instant ck a (present c)
    | Sabs:
        forall ck a,
          sem_instant init base R m k mems a absent ->
          sem_clock_instant base R ck false ->
          sem_annotated_instant sem_instant ck a absent.

    Definition sem_laexp_instant := sem_annotated_instant sem_lexp_instant.
    Definition sem_caexp_instant := sem_annotated_instant sem_cexp_instant.

    Inductive sem_laexps_instant: clock -> list lexp -> list value -> Prop:=
    | SLticks:
        forall ck ces cs vs,
          vs = map present cs ->
          sem_lexps_instant init base R m k mems ces vs ->
          sem_clock_instant base R ck true ->
          sem_laexps_instant ck ces vs
    | SLabss:
        forall ck ces vs,
          vs = all_absent ces ->
          sem_lexps_instant init base R m k mems ces vs ->
          sem_clock_instant base R ck false ->
          sem_laexps_instant ck ces vs.

  End InstantAnnotatedSemantics.

  (** ** Liftings of instantaneous semantics *)

  Section LiftSemantics.

    Variable bk : stream bool.
    Variable H : history.
    Variable M: memories.
    Variable k: nat.
    Variable mems: list (ident * const).

    Definition restr_hist (n: nat): env :=
      PM.map (fun xs => xs n) H.
    Hint Unfold restr_hist.

    Definition restr_mem (n: nat): memory :=
      mmap (fun lv => map (fun xs => xs n) lv) M.
    Hint Unfold restr_mem.

    Definition lift {A B} (sem: bool -> bool -> env -> memory -> nat -> list (ident * const) -> A -> B -> Prop)
               x (ys: stream B): Prop :=
      forall n, sem (n ==b 0) (bk n) (restr_hist n) (restr_mem n) k mems x (ys n).
    Hint Unfold lift.

    Definition lift' {A B} (sem: bool -> env -> A -> B -> Prop) x (ys: stream B): Prop :=
      forall n, sem (bk n) (restr_hist n) x (ys n).
    Hint Unfold lift'.

    Definition lift'' {A B} (sem: env -> A -> B -> Prop) x (ys: stream B): Prop :=
      forall n, sem (restr_hist n) x (ys n).
    Hint Unfold lift''.

    Definition sem_clock (ck: clock) (xs: stream bool): Prop :=
      lift' sem_clock_instant ck xs.

    Definition sem_var (x: ident) (xs: stream value): Prop :=
      lift'' sem_var_instant x xs.

    Definition sem_vars (x: idents) (xs: stream (list value)): Prop :=
      lift'' (fun R => Forall2 (sem_var_instant R)) x xs.

    Definition sem_laexp ck (e: lexp) (xs: stream value): Prop :=
      lift (fun init base R m k mems => sem_laexp_instant init base R m k mems ck) e xs.

    Definition sem_laexps (ck: clock) (e: list lexp) (xs: stream (list value)): Prop :=
      lift (fun init base R m k mems => sem_laexps_instant init base R m k mems ck) e xs.

    Definition sem_lexp (e: lexp) (xs: stream value): Prop :=
      lift sem_lexp_instant e xs.

    Definition sem_lexps (e: list lexp) (xs: stream (list value)): Prop :=
      lift sem_lexps_instant e xs.

    Definition sem_caexp ck (c: cexp) (xs: stream value): Prop :=
      lift (fun init base R m k mems => sem_caexp_instant init base R m k mems ck) c xs.

    Definition sem_cexp (c: cexp) (xs: stream value): Prop :=
      lift sem_cexp_instant c xs.

  End LiftSemantics.

  (** ** Time-dependent semantics *)

  Definition instant_same_clock (l : list value) : Prop :=
    absent_list l \/ present_list l.

  Definition same_clock (l_s : stream (list value)) : Prop :=
    forall n, instant_same_clock (l_s n).

  Definition clock_of (xss: stream (list value))(bs: stream bool): Prop :=
    forall n,
      present_list (xss n) <-> bs n = true.

  (* Definition clock_of' (xss: stream (list value)) : stream bool := *)
  (*   fun n => forallb (fun v => negb (v ==b absent)) (xss n). *)

  (* Lemma clock_of_equiv: *)
  (*   forall xss, clock_of xss (clock_of' xss). *)
  (* Proof. *)
  (*   split; intros H. *)
  (*   - unfold clock_of'. *)
  (*     rewrite forallb_forall. *)
  (*     intros; rewrite Bool.negb_true_iff. *)
  (*     rewrite not_equiv_decb_equiv. *)
  (*     eapply In_Forall in H; eauto. *)
  (*   - unfold clock_of' in H. *)
  (*     rewrite forallb_forall in H. *)
  (*     apply all_In_Forall; intros ** Hin E. *)
  (*     specialize (H _ Hin). *)
  (*     rewrite Bool.negb_true_iff, not_equiv_decb_equiv in H. *)
  (*     apply H; eauto. *)
  (* Qed. *)

  Inductive post_mem: nat -> ident -> stream value -> memories -> Prop :=
    next_mem_intro:
      forall k x xs M lvs lv,
        mfind_mem x M = Some lvs ->
        nth_error lvs k = Some lv ->
        (forall n, lv (S n) = xs n) ->
        post_mem k x xs M.

  Section ModeSemantics.

    Variable P: program.

    Inductive sem_equation: nat -> stream bool -> history -> memories -> list (ident * const) -> equation -> Prop :=
    | SEqDef:
        forall k bk H M mems x xs ck ce,
          sem_var H x xs ->
          sem_caexp bk H M k mems ck ce xs ->
          sem_equation k bk H M mems (EqDef x ck ce)
    | SEqPost:
        forall k bk H M mems x ck ce xs,
          sem_caexp bk H M k mems ck ce xs ->
          post_mem k x xs M ->
          sem_equation k bk H M mems (EqPost x ck ce)
    | SEqCall:
        forall k bk H M mems ys x Mx ck ma_n P' ma i m k' es ess oss,
          find_machine ma_n P = Some (ma, P') ->
          sem_laexps bk H M k mems ck es ess ->
          hd_error ys = Some x ->
          sub_inst x M Mx ->
          sem_mode k' ma m Mx ess oss ->
          sem_vars H ys oss ->
          sem_equation k bk H M mems (EqCall ys ck ma_n i m k' es)

    with sem_mode: nat -> machine -> ident -> memories -> stream (list value) -> stream (list value) -> Prop :=
           SMode:
             forall k ma mo mo_n M H xss yss bk,
               clock_of xss bk ->
               find_mode mo_n ma.(ma_modes) = Some mo ->
               sem_vars H (map fst mo.(m_in)) xss ->
               sem_vars H (map fst mo.(m_out)) yss ->
               (* XXX: This should be obtained through well-clocking: *)
               (*  * tuples are synchronised: *)
               same_clock xss ->
               same_clock yss ->
               (*  * output clock matches input clock *)
               (forall n, absent_list (xss n) <-> absent_list (yss n)) ->
               (* XXX: END *)
               Forall (sem_equation k bk H M ma.(ma_mems)) mo.(m_eqs) ->
               sem_mode k ma mo_n M xss yss.

  End ModeSemantics.

End SMSEMANTICS.
