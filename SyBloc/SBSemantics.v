Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Setoid.
Require Import Morphisms.

Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.RMemory.
Require Import Velus.SyBloc.SBSyntax.
Require Import Velus.NLustre.Stream.

Module Type SBSEMANTICS
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import OpAux   : OPERATORS_AUX       Op)
       (Import Syn     : SBSYNTAX        Ids Op)
       (Import Str     : STREAM              Op OpAux).

  (** ** Environment and history *)

  (**

An history maps variables to streams of values (the variables'
histories). Taking a snapshot of the history at a given time yields an
environment.

   *)

  Definition state := memory val.
  (* Definition evolution := memory (stream val). *)

  Definition transient_states := PM.t state.
  (* Definition transient_evolutions := PM.t evolution. *)


  Definition env := PM.t value.
  (* Definition history := PM.t (stream value). *)

  (** ** Instantaneous semantics *)

  Section ExprSemantics.

    Variable base: bool.
    Variable R: env.
    Variable S: state.
    (* Variable Ts: transient_states. *)

    Inductive sem_var_var: ident -> value -> Prop :=
      Svv:
        forall x v,
          PM.find x R = Some v ->
          sem_var_var x v.

    Inductive sem_clock: clock -> bool -> Prop :=
    | Sbase:
        sem_clock Cbase base
    | Son:
        forall ck x c b,
          sem_clock ck true ->
          sem_var ck x (present c) ->
          val_to_bool c = Some b ->
          sem_clock (Con ck x b) true
    | Son_abs1:
        forall ck x c,
          sem_clock ck false ->
          sem_var ck x absent ->
          sem_clock (Con ck x c) false
    | Son_abs2:
        forall ck x c b,
          sem_clock ck true ->
          sem_var ck x (present c) ->
          val_to_bool c = Some b ->
          sem_clock (Con ck x (negb b)) false

    with sem_state_var: clock -> ident -> value -> Prop :=
         | SsvPresent:
             forall x v ck,
               find_val x S = Some v ->
               sem_clock ck true ->
               sem_state_var ck x (present v)
         | SsvAbsent:
             forall x ck,
               find_val x S <> None ->
               sem_clock ck false ->
               sem_state_var ck x absent

    with sem_var: clock -> var -> value -> Prop :=
         | Sv:
             forall x v ck,
               sem_var_var x v ->
               sem_var ck (Var x) v
         | Sl:
             forall x v ck,
               sem_state_var ck x v ->
               sem_var ck (Last x) v.

    Scheme sem_clock_mut := Induction for sem_clock Sort Prop
             with sem_state_var_mut := Induction for sem_state_var Sort Prop
             with sem_var_mut := Induction for sem_var Sort Prop.

    Combined Scheme sem_clock_state_var_var_mut from
             sem_clock_mut, sem_state_var_mut, sem_var_mut.

    Definition sem_vars (xs: idents) (vs: list value) : Prop :=
      Forall2 sem_var_var xs vs.

    Inductive sem_lexp: clock -> lexp -> value -> Prop:=
    | Sconst:
        forall c v ck,
          v = (if base then present (sem_const c) else absent) ->
          sem_lexp ck (Econst c) v
    | Svar:
        forall x v ty ck,
          sem_var ck x v ->
          sem_lexp ck (Evar x ty) v
    | Swhen_eq:
        forall s x sc xc b ck,
          sem_var ck x (present xc) ->
          sem_lexp ck s (present sc) ->
          val_to_bool xc = Some b ->
          sem_lexp (Con ck x b) (Ewhen s x b) (present sc)
    | Swhen_abs1:
        forall s x sc xc b ck,
          sem_var ck x (present xc) ->
          val_to_bool xc = Some b ->
          sem_lexp ck s (present sc) ->
          sem_lexp (Con ck x (negb b)) (Ewhen s x (negb b)) absent
    | Swhen_abs:
        forall s x b ck,
          sem_var ck x absent ->
          sem_lexp ck s absent ->
          sem_lexp (Con ck x b) (Ewhen s x b) absent
    | Sunop_eq:
        forall le op c c' ty ck,
          sem_lexp ck le (present c) ->
          sem_unop op c (typeof le) = Some c' ->
          sem_lexp ck (Eunop op le ty) (present c')
    | Sunop_abs:
        forall le op ty ck,
          sem_lexp ck le absent ->
          sem_lexp ck (Eunop op le ty) absent
    | Sbinop_eq:
        forall le1 le2 op c1 c2 c' ty ck,
          sem_lexp ck le1 (present c1) ->
          sem_lexp ck le2 (present c2) ->
          sem_binop op c1 (typeof le1) c2 (typeof le2) = Some c' ->
          sem_lexp ck (Ebinop op le1 le2 ty) (present c')
    | Sbinop_abs:
        forall le1 le2 op ty ck,
          sem_lexp ck le1 absent ->
          sem_lexp ck le2 absent ->
          sem_lexp ck (Ebinop op le1 le2 ty) absent.

    Definition sem_lexps (ck: clock) (les: list lexp) (vs: list value) :=
      Forall2 (sem_lexp ck) les vs.

    Inductive sem_cexp: clock -> cexp -> value -> Prop :=
    | Smerge_true:
        forall x t f c ck,
          sem_var ck x (present true_val) ->
          sem_cexp (Con ck x true) t (present c) ->
          sem_cexp (Con ck x false) f absent ->
          sem_cexp ck (Emerge x t f) (present c)
    | Smerge_false:
        forall x t f c ck,
          sem_var ck x (present false_val) ->
          sem_cexp (Con ck x true) t absent ->
          sem_cexp (Con ck x false) f (present c) ->
          sem_cexp ck (Emerge x t f) (present c)
    | Smerge_abs:
        forall x t f ck,
          sem_var ck x absent ->
          sem_cexp (Con ck x true) t absent ->
          sem_cexp (Con ck x false) f absent ->
          sem_cexp ck (Emerge x t f) absent
    | Site_eq:
        forall x t f c b ct cf ck,
          sem_lexp ck x (present c) ->
          sem_cexp ck t (present ct) ->
          sem_cexp ck f (present cf) ->
          val_to_bool c = Some b ->
          sem_cexp ck (Eite x t f) (if b then present ct else present cf)
    | Site_abs:
        forall b t f ck,
          sem_lexp ck b absent ->
          sem_cexp ck t absent ->
          sem_cexp ck f absent ->
          sem_cexp ck (Eite b t f) absent
    | Sexp:
        forall e v ck,
          sem_lexp ck e v ->
          sem_cexp ck (Eexp e) v.

    Inductive sem_annotated {A}
              (sem: clock -> A -> value -> Prop)
      : clock -> A -> value -> Prop :=
    | Stick:
        forall ck a c,
          sem ck a (present c) ->
          sem_clock ck true ->
          sem_annotated sem ck a (present c)
    | Sabs:
        forall ck a,
          sem ck a absent ->
          sem_clock ck false ->
          sem_annotated sem ck a absent.

    Definition sem_laexp := sem_annotated sem_lexp.
    Definition sem_caexp := sem_annotated sem_cexp.

    Inductive sem_laexps: clock -> list lexp -> list value -> Prop:=
    | SLticks:
        forall ck ces cs vs,
          vs = map present cs ->
          sem_lexps ck ces vs ->
          sem_clock ck true ->
          sem_laexps ck ces vs
    | SLabss:
        forall ck ces vs,
          vs = all_absent ces ->
          sem_lexps ck ces vs ->
          sem_clock ck false ->
          sem_laexps ck ces vs.

  End ExprSemantics.

  Definition reset_of (v: value) : bool :=
    match v with
    | present x => x ==b true_val
    | absent => false
    end.

  (* Definition reset_of (xs: stream value) : stream bool := *)
  (*   fun n => reset_of_value (xs n). *)

  Definition reset_last (bl: block) (r: bool) (x: ident) (v: val) : val :=
    if r then
      match find_init x bl with
      | Some c => sem_const c
      | None => false_val
      end
    else v.

  Definition reset_lasts (bl: block) (r: bool) (S S0: state) : Prop :=
    values S0 = Env.mapi (reset_last bl r) (values S).

  Definition same_clock (vs: list value) : Prop :=
    absent_list vs \/ present_list vs.

  Definition clock_of (vs: list value) (b: bool): Prop :=
    present_list vs <-> b = true.

  Section Semantics.

    Variable P: program.

    Inductive sem_reset: ident -> bool -> state -> state -> Prop :=
      SReset:
        forall b (r: bool) S S0 bl P',
          find_block b P = Some (bl, P') ->
          reset_lasts bl r S S0 ->
          (forall b' S',
              sub_inst b' S S' ->
              exists S0',
                sub_inst b' S0 S0'
                /\ sem_reset b' r S' S0') ->
          sem_reset b r S S0.

    Inductive sem_equation: bool -> env -> state -> transient_states -> state -> equation -> Prop :=
    | SEqDef:
        forall base R S T S' x v ck ce,
          sem_var_var R x v ->
          sem_caexp base R S ck ce v ->
          sem_equation base R S T S' (EqDef x ck ce)
    | SEqNext:
        forall base R S T S' x ck e v,
          sem_state_var base R S' ck x v ->
          sem_laexp base R S ck e v ->
          sem_equation base R S T S' (EqNext x ck e)
    | SEqTransient:
        forall base R S T S' s ck Ss,
          sub_inst s S Ss ->
          PM.find s T = Some Ss ->
          sem_equation base R S T S' (EqTransient s ck)
    | SEqReset:
        forall base R S T S' ck b s r vr Ss S0,
          sem_var base R S ck r vr ->
          sub_inst s S Ss ->
          sem_reset b (reset_of vr) Ss S0 ->
          PM.find s T = Some S0 ->
          sem_equation base R S T S' (EqReset s ck b r)
    | SEqCall:
        forall base R S T S' ys ck b s es xs Ss os Ss',
          sem_laexps base R S ck es xs ->
          PM.find s T = Some Ss ->
          sem_block b Ss xs os Ss' ->
          sem_vars R ys os ->
          sub_inst s S' Ss' ->
          sem_equation base R S T S' (EqCall s ys ck b es)

    with sem_block: ident -> state -> list value -> list value -> state -> Prop :=
           SBlock:
             forall b bl P' S T S' R xs ys base,
               clock_of xs base ->
               find_block b P = Some (bl, P') ->
               sem_vars R (map fst bl.(b_in)) xs ->
               sem_vars R (map fst bl.(b_out)) ys ->
               same_clock xs ->
               same_clock ys ->
               (absent_list xs <-> absent_list ys) ->
               Forall (sem_equation base R S T S') bl.(b_eqs) ->
               (* well_structured_memories bl.(b_eqs) M -> *)
               sem_block b S xs ys S'.


  End Semantics.

  Section sem_block_mult.
    Variable P: program.

    Variable P_equation: bool -> env -> state -> transient_states -> state -> equation -> Prop.
    Variable P_block: ident -> state -> list value -> list value -> state -> Prop.

    Hypothesis EqDefCase:
      forall base R S T S' x v ck ce,
        sem_var_var R x v ->
        sem_caexp base R S ck ce v ->
        P_equation base R S T S' (EqDef x ck ce).

    Hypothesis EqNextCase:
      forall base R S T S' x ck e v,
        sem_state_var base R S' ck x v ->
        sem_laexp base R S ck e v ->
        P_equation base R S T S' (EqNext x ck e).

    Hypothesis EqTransientCase:
      forall base R S T S' s ck Ss,
        sub_inst s S Ss ->
        PM.find s T = Some Ss ->
        P_equation base R S T S' (EqTransient s ck).

    Hypothesis EqResetCase:
      forall base R S T S' ck b s r vr Ss S0,
        sem_var base R S ck r vr ->
        sub_inst s S Ss ->
        sem_reset P b (reset_of vr) Ss S0 ->
        PM.find s T = Some S0 ->
        P_equation base R S T S' (EqReset s ck b r).

    Hypothesis EqCallCase:
      forall base R S T S' s ys ck b es xs Ss os Ss',
        sem_laexps base R S ck es xs ->
        PM.find s T = Some Ss ->
        sem_block P b Ss xs os Ss' ->
        sem_vars R ys os ->
        sub_inst s S' Ss' ->
        P_block b Ss xs os Ss' ->
        P_equation base R S T S' (EqCall s ys ck b es).

    Hypothesis BlockCase:
      forall b bl P' R S T S' xs ys base,
        clock_of xs base ->
        find_block b P = Some (bl, P') ->
        sem_vars R (map fst bl.(b_in)) xs ->
        sem_vars R (map fst bl.(b_out)) ys ->
        same_clock xs ->
        same_clock ys ->
        (absent_list xs <-> absent_list ys) ->
        Forall (sem_equation P base R S T S') bl.(b_eqs) ->
        Forall (P_equation base R S T S') bl.(b_eqs) ->
        P_block b S xs ys S'.

    Fixpoint sem_equation_mult
             (base: bool) (R: env) (S: state) (T: transient_states) (S': state) (e: equation)
             (Sem: sem_equation P base R S T S' e) {struct Sem}
      : P_equation base R S T S' e
    with sem_block_mult
           (f: ident) (S: state) (xs ys: list value) (S': state)
           (Sem: sem_block P f S xs ys S') {struct Sem}
         : P_block f S xs ys S'.
    Proof.
      - destruct Sem; eauto.
      - destruct Sem.
        eapply BlockCase; eauto.
        match goal with H: Forall _ _ |- _ => induction H; auto end.
    Qed.

    Combined Scheme sem_equation_block_ind from
             sem_equation_mult, sem_block_mult.

  End sem_block_mult.

 (*  (** ** Liftings of instantaneous semantics *) *)

(*   Section LiftSemantics. *)

(*     Variable base : stream bool. *)
(*     Variable H : history. *)
(*     Variable E : evolution. *)

(*     Definition sample {A} (n: nat) (xs: stream A) := xs n. *)
(*     Hint Unfold sample. *)

(*     Definition restr_evol (n: nat): state := *)
(*       mmap (sample n) E. *)

(*     Definition restr_hist (n: nat): env := *)
(*       PM.map (sample n) H. *)
(*     Hint Unfold restr_hist. *)

(*     Definition lift {A B} (sem: bool -> env -> state -> clock -> A -> B -> Prop) *)
(*                ck x (ys: stream B): Prop := *)
(*       forall n, sem (bk n) (restr_hist n) (restr_evol n) ck x (ys n). *)
(*     Hint Unfold lift. *)

(*     Definition lift' {A B} (sem: env -> state -> clock -> A -> B -> Prop) ck x (ys: stream B): Prop := *)
(*       forall n, sem (restr_hist n) (restr_evol n) ck x (ys n). *)
(*     Hint Unfold lift'. *)

(*     Definition lift'' {A B} (sem: env -> clock -> A -> B -> Prop) ck x (ys: stream B): Prop := *)
(*       forall n, sem (restr_hist n) ck x (ys n). *)
(*     Hint Unfold lift''. *)

(*     Definition lift''' {A B} (sem: state -> clock -> A -> B -> Prop) ck x (ys: stream B): Prop := *)
(*       forall n, sem (restr_evol n) ck x (ys n). *)
(*     Hint Unfold lift'''. *)

(*     Definition lift'''' {A B} (sem: bool -> env -> state -> A -> B -> Prop) *)
(*                x (ys: stream B): Prop := *)
(*       forall n, sem (bk n) (restr_hist n) (restr_evol n) x (ys n). *)
(*     Hint Unfold lift''''. *)

(*     Definition lift''''' {A B} (sem: env -> A -> B -> Prop) *)
(*                x (ys: stream B): Prop := *)
(*       forall n, sem (restr_hist n) x (ys n). *)
(*     Hint Unfold lift'''''. *)
(*     (* Definition lift''' {A B} (sem: bool -> env -> A -> B -> Prop) x (ys: stream B): Prop := *) *)
(*     (*   forall n, sem (bk n) (restr_hist n) x (ys n). *) *)
(*     (* Hint Unfold lift'''. *) *)

(*     Definition sem_clock (ck: clock) (xs: stream bool): Prop := *)
(*       lift'''' sem_clock ck xs. *)

(*     Definition sem_var ck (x: var) (xs: stream value): Prop := *)
(*       lift sem_var ck x xs. *)

(*     (* Definition sem_last (x: ident) (xs: stream value): Prop := *) *)
(*     (*   lift'' sem_last x xs. *) *)

(*     Definition sem_var_var (x: ident) (xs: stream value): Prop := *)
(*       lift''''' sem_var_var x xs. *)

(*     Definition sem_state_var ck (x: ident) (xs: stream value): Prop := *)
(*       lift sem_state_var ck x xs. *)

(*     Definition sem_vars (x: idents) (xs: stream (list value)): Prop := *)
(*       lift''''' sem_vars x xs. *)

(*     Definition sem_laexp ck (e: lexp) (xs: stream value): Prop := *)
(*       lift'''' (fun base R S => sem_laexp base R S ck) e xs. *)

(*     Definition sem_laexps (ck: clock) (e: list lexp) (xs: stream (list value)): Prop := *)
(*       lift'''' (fun base R S => sem_laexps base R S ck) e xs. *)

(*     Definition sem_lexp ck (e: lexp) (xs: stream value): Prop := *)
(*       lift sem_lexp ck e xs. *)

(*     Definition sem_lexps ck (e: list lexp) (xs: stream (list value)): Prop := *)
(*       lift sem_lexps ck e xs. *)

(*     Definition sem_caexp ck (c: cexp) (xs: stream value): Prop := *)
(*       lift'''' (fun base R S => sem_caexp base R S ck) c xs. *)

(*     Definition sem_cexp ck (c: cexp) (xs: stream value): Prop := *)
(*       lift sem_cexp ck c xs. *)

(*   End LiftSemantics. *)

(*   (** ** Time-dependent semantics *) *)

(*   Definition instant_same_clock (l : list value) : Prop := *)
(*     absent_list l \/ present_list l. *)

(*   Definition same_clock (l_s : stream (list value)) : Prop := *)
(*     forall n, instant_same_clock (l_s n). *)

(*   Definition clock_of (xss: stream (list value))(bs: stream bool): Prop := *)
(*     forall n, *)
(*       present_list (xss n) <-> bs n = true. *)

(*   Definition clock_of' (xss: stream (list value)) : stream bool := *)
(*     fun n => forallb (fun v => negb (v ==b absent)) (xss n). *)

(*   Lemma clock_of_equiv: *)
(*     forall xss, clock_of xss (clock_of' xss). *)
(*   Proof. *)
(*     split; intros H. *)
(*     - unfold clock_of'. *)
(*       rewrite forallb_forall. *)
(*       intros; rewrite Bool.negb_true_iff. *)
(*       rewrite not_equiv_decb_equiv. *)
(*       eapply In_Forall in H; eauto. *)
(*     - unfold clock_of' in H. *)
(*       rewrite forallb_forall in H. *)
(*       apply all_In_Forall; intros ** Hin E. *)
(*       specialize (H _ Hin). *)
(*       rewrite Bool.negb_true_iff, not_equiv_decb_equiv in H. *)
(*       apply H; eauto. *)
(*   Qed. *)

(*   Lemma clock_of_equiv': *)
(*     forall xss bk, *)
(*       clock_of xss bk -> *)
(*       bk ≈ clock_of' xss. *)
(*   Proof. *)
(*     intros ** H n; specialize (H n). *)
(*     unfold clock_of'. *)
(*     induction (xss n) as [|v]; simpl. *)
(*     - apply H; constructor. *)
(*     - destruct v. *)
(*       + simpl. *)
(*         rewrite <-Bool.not_true_iff_false, <-H. *)
(*         inversion 1; auto. *)
(*       + simpl. *)
(*         apply IHl; rewrite <-H. *)
(*         split; intro P. *)
(*         * constructor; auto. *)
(*           intro; discriminate. *)
(*         * inv P; auto. *)
(*   Qed. *)

(*   (* Record mvalues := *) *)
(*   (*   Mvalues { content: stream val; *) *)
(*   (*             reset: stream bool *) *)
(*   (*           }. *) *)

(*   (* (* Definition memory := RMemory.memory mvalue. *) *) *)
(*   (* Definition memories := RMemory.memory mvalues. *) *)

(*   (* Inductive reset_regs: stream bool -> memories -> Prop := *) *)
(*   (*   reset_regs_intro: *) *)
(*   (*     forall M rs, *) *)
(*   (*       (forall x mvs, *) *)
(*   (*           find_val x M = Some mvs -> *) *)
(*   (*           forall n, rs n = true -> mvs.(reset) n = true) -> *) *)
(*   (*       (forall x M', *) *)
(*   (*           sub_inst x M M' -> *) *)
(*   (*           reset_regs rs M') -> *) *)
(*   (*       reset_regs rs M. *) *)

(*   (* (* Definition next (n: nat) (mvs: mvalues) (v0 v: val) : Prop := *) *) *)
(*   (* (*   mvs.(content) (S n) = (if mvs.(reset) (S n) then v0 else v). *) *) *)

(*   (* (* Inductive fby_spec: nat -> val -> value -> mvalues -> value -> Prop := *) *) *)
(*   (* (* | fby_spec_present: *) *) *)
(*   (* (*     forall n v0 v mvs, *) *) *)
(*   (* (*       next n mvs v0 v -> *) *) *)
(*   (* (*       fby_spec n v0 (present v) mv (mv.(content) n) *) *) *)
(*   (* (* | fby_spec_absent: *) *) *)
(*   (* (*     forall n v0 v mvs, *) *) *)
(*   (* (*       next n mvs v0 (mvs.(content) n) -> *) *) *)
(*   (* (*       fby_spec n v0 absent mvs absent. *) *) *)

(*   (* Inductive mfby: ident -> val -> stream value -> memories -> stream value -> Prop := *) *)
(*   (*   mfby_intro: *) *)
(*   (*     forall x mvs v0 ls M xs, *) *)
(*   (*       find_val x M = Some mvs -> *) *)
(*   (*       mvs.(content) 0 = v0 -> *) *)
(*   (*       (forall n, match ls n with *) *)
(*   (*             | absent => *) *)
(*   (*               mvs.(content) (S n) = (if mvs.(reset) (S n) then v0 else mvs.(content) n) *) *)
(*   (*               /\ xs n = absent *) *)
(*   (*             | present v => *) *)
(*   (*               mvs.(content) (S n) = (if mvs.(reset) (S n) then v0 else v) *) *)
(*   (*               /\ xs n = present (mvs.(content) n) *) *)
(*   (*             end) -> *) *)
(*   (*       mfby x v0 ls M xs. *) *)

(*   (* Definition fby_eq (mems: PS.t) (eq: equation) : PS.t := *) *)
(*   (*   match eq with *) *)
(*   (*   | EqFby x _ _ _ => PS.add x mems *) *)
(*   (*   | _ => mems *) *)
(*   (*   end. *) *)

(*   (* Definition fbys (eqs: list equation) : PS.t := *) *)
(*   (*   fold_left fby_eq eqs PS.empty. *) *)

(*   (* Definition inst_eq (insts: PS.t) (eq: equation) : PS.t := *) *)
(*   (*   match eq with *) *)
(*   (*   | EqReset _ _ i _ => PS.add i insts *) *)
(*   (*   | EqCall _ _ _ i _ => PS.add i insts *) *)
(*   (*   | _ => insts *) *)
(*   (*   end. *) *)

(*   (* Definition insts (eqs: list equation) : PS.t := *) *)
(*   (*   fold_left inst_eq eqs PS.empty. *) *)

(*   (* Definition well_structured_memories (eqs: list equation) (M: memories) := *) *)
(*   (*   (forall x, *) *)
(*   (*       find_val x M <> None <-> PS.In x (fbys eqs)) *) *)
(*   (*   /\ forall x, *) *)
(*   (*     find_inst x M <> None <-> PS.In x (insts eqs). *) *)

(*   Definition reset_of_value (v: value) : bool := *)
(*     match v with *)
(*     | present x => x ==b true_val *)
(*     | absent => false *)
(*     end. *)

(*   Definition reset_of (xs: stream value) : stream bool := *)
(*     fun n => reset_of_value (xs n). *)

(*   Definition reset_last (bl: block) (r: stream bool) (x: ident) (xs: stream val) := *)
(*     fun n => *)
(*       if r n then *)
(*         match find_init x bl with *)
(*         | Some c => sem_const c *)
(*         | None => false_val *)
(*         end *)
(*       else xs n. *)

(*   Definition reset_lasts (bl: block) (r: stream bool) (E E0: evolution) := *)
(*     values E0 = Env.mapi (reset_last bl r) (values E). *)

(*   Section BlockSemantics. *)

(*     Variable P: program. *)

(*     Inductive sem_reset: ident -> stream bool -> evolution -> evolution -> Prop := *)
(*       SReset: *)
(*         forall b (r: stream bool) E E0 bl P', *)
(*           find_block b P = Some (bl, P') -> *)
(*           reset_lasts bl r E E0 -> *)
(*           (forall b' E', *)
(*               sub_inst b' E E' -> *)
(*               exists E0', *)
(*                 sub_inst b' E0 E0' *)
(*                 /\ sem_reset b' r E' E0') -> *)
(*           sem_reset b r E E0. *)

(*     Inductive sem_equation: stream bool -> history -> evolution -> transient_evolutions -> evolution -> equation -> Prop := *)
(*     | SEqDef: *)
(*         forall bk H E T E' x xs ck ce, *)
(*           sem_var_var H x xs -> *)
(*           sem_caexp bk H E ck ce xs -> *)
(*           sem_equation bk H E T E' (EqDef x ck ce) *)
(*     | SEqNext: *)
(*         forall bk H E T E' x ck e xs ls, *)
(*           sem_state_var bk H E' ck x xs -> *)
(*           sem_laexp bk H E ck e ls -> *)
(*           sem_equation bk H E T E' (EqNext x ck e) *)
(*     | SEqTransient: *)
(*         forall bk H E T E' s ck Es, *)
(*           sub_inst s E Es -> *)
(*           PM.find s T = Some Es -> *)
(*           sem_equation bk H E T E' (EqTransient s ck) *)
(*     | SEqReset: *)
(*         forall bk H E T E' ck b s r rs Es E0, *)
(*           sem_var bk H E ck r rs -> *)
(*           sub_inst s E Es -> *)
(*           sem_reset b (reset_of rs) Es E0 -> *)
(*           PM.find s T = Some E0 -> *)
(*           sem_equation bk H E T E' (EqReset s ck b r) *)
(*     | SEqCall: *)
(*         forall bk H E T E' ys ck b s es ess Es oss Es', *)
(*           sem_laexps bk H E ck es ess -> *)
(*           PM.find s T = Some Es -> *)
(*           sem_block b Es ess oss Es' -> *)
(*           sem_vars H ys oss -> *)
(*           sub_inst s E' Es' -> *)
(*           sem_equation bk H E T E' (EqCall s ys ck b es) *)

(*     with sem_block: ident -> evolution -> stream (list value) -> stream (list value) -> evolution -> Prop := *)
(*            SBlock: *)
(*              forall b bl P' E T E' H xss yss bk, *)
(*                clock_of xss bk -> *)
(*                find_block b P = Some (bl, P') -> *)
(*                sem_vars H (map fst bl.(b_in)) xss -> *)
(*                sem_vars H (map fst bl.(b_out)) yss -> *)
(*                same_clock xss -> *)
(*                same_clock yss -> *)
(*                (forall n, absent_list (xss n) <-> absent_list (yss n)) -> *)
(*                Forall (sem_equation bk H E T E') bl.(b_eqs) -> *)
(*                (* well_structured_memories bl.(b_eqs) M -> *) *)
(*                sem_block b E xss yss E'. *)

(*   End BlockSemantics. *)

(*   Section sem_block_mult. *)
(*     Variable P: program. *)

(*     Variable P_equation: stream bool -> history -> evolution -> transient_evolutions -> evolution -> equation -> Prop. *)
(*     Variable P_block: ident -> evolution -> stream (list value) -> stream (list value) -> evolution -> Prop. *)

(*     Hypothesis EqDefCase: *)
(*       forall bk H E T E' x xs ck ce, *)
(*         sem_var_var H x xs -> *)
(*         sem_caexp bk H E ck ce xs -> *)
(*         P_equation bk H E T E' (EqDef x ck ce). *)

(*     Hypothesis EqNextCase: *)
(*       forall bk H E T E' x ck e xs ls, *)
(*         sem_state_var bk H E' ck x xs -> *)
(*         sem_laexp bk H E ck e ls -> *)
(*         P_equation bk H E T E' (EqNext x ck e). *)

(*     Hypothesis EqTransientCase: *)
(*       forall bk H E T E' s ck Es, *)
(*         sub_inst s E Es -> *)
(*         PM.find s T = Some Es -> *)
(*         P_equation bk H E T E' (EqTransient s ck). *)

(*     Hypothesis EqResetCase: *)
(*       forall bk H E T E' ck b s r rs Es E0, *)
(*         sem_var bk H E ck r rs -> *)
(*         sub_inst s E Es -> *)
(*         sem_reset P b (reset_of rs) Es E0 -> *)
(*         PM.find s T = Some E0 -> *)
(*         P_equation bk H E T E' (EqReset s ck b r). *)

(*     Hypothesis EqCallCase: *)
(*       forall bk H E T E' s ys ck b es ess Es oss Es', *)
(*         sem_laexps bk H E ck es ess -> *)
(*         PM.find s T = Some Es -> *)
(*         sem_block P b Es ess oss Es' -> *)
(*         sem_vars H ys oss -> *)
(*         sub_inst s E' Es' -> *)
(*         P_block b Es ess oss Es' -> *)
(*         P_equation bk H E T E' (EqCall s ys ck b es). *)

(*     Hypothesis BlockCase: *)
(*       forall b bl P' H E T E' xss yss bk, *)
(*         clock_of xss bk -> *)
(*         find_block b P = Some (bl, P') -> *)
(*         sem_vars H (map fst bl.(b_in)) xss -> *)
(*         sem_vars H (map fst bl.(b_out)) yss -> *)
(*         same_clock xss -> *)
(*         same_clock yss -> *)
(*         (forall n, absent_list (xss n) <-> absent_list (yss n)) -> *)
(*         Forall (sem_equation P bk H E T E') bl.(b_eqs) -> *)
(*         Forall (P_equation bk H E T E') bl.(b_eqs) -> *)
(*         P_block b E xss yss E'. *)

(*     Fixpoint sem_equation_mult *)
(*             (b: stream bool) (H: history) (E: evolution) (T: transient_evolutions) (E': evolution) (e: equation) *)
(*             (Sem: sem_equation P b H E T E' e) {struct Sem} *)
(*       : P_equation b H E T E' e *)
(*     with sem_block_mult *)
(*            (f: ident) (E: evolution) (xss oss: stream (list value)) (E': evolution) *)
(*            (Sem: sem_block P f E xss oss E') {struct Sem} *)
(*          : P_block f E xss oss E'. *)
(*     Proof. *)
(*       - destruct Sem; eauto. *)
(*       - destruct Sem. *)
(*         eapply BlockCase; eauto. *)
(*         match goal with H: Forall _ _ |- _ => induction H; auto end. *)
(*     Qed. *)

(*     Combined Scheme sem_equation_block_ind from *)
(*              sem_equation_mult, sem_block_mult. *)

(*   End sem_block_mult. *)

(*   (** Morphisms properties *) *)

(*   (* Add Parametric Morphism b A B sem H E : (@lift b H E A B sem) *) *)
(*   (*     with signature eq ==> @eq_str B ==> Basics.impl *) *)
(*   (*       as lift_eq_str. *) *)
(*   (* Proof. *) *)
(*   (*   intros x xs xs' Eq Lift n. *) *)
(*   (*   rewrite <-Eq; auto. *) *)
(*   (* Qed. *) *)

(*   (* Add Parametric Morphism A B sem H E : (@lift' H E A B sem) *) *)
(*   (*     with signature eq ==> @eq_str B ==> Basics.impl *) *)
(*   (*       as lift'_eq_str. *) *)
(*   (* Proof. *) *)
(*   (*   intros x xs xs' Eq Lift n. *) *)
(*   (*   rewrite <-Eq; auto. *) *)
(*   (* Qed. *) *)

(*   (* Add Parametric Morphism A B sem E : (@lift'' E A B sem) *) *)
(*   (*     with signature eq ==> @eq_str B ==> Basics.impl *) *)
(*   (*       as lift''_eq_str. *) *)
(*   (* Proof. *) *)
(*   (*   intros x xs xs' Eq Lift n. *) *)
(*   (*   rewrite <-Eq; auto. *) *)
(*   (* Qed. *) *)

(*   (* Add Parametric Morphism A B sem H : (@lift''' H A B sem) *) *)
(*   (*     with signature eq ==> @eq_str B ==> Basics.impl *) *)
(*   (*       as lift'''_eq_str. *) *)
(*   (* Proof. *) *)
(*   (*   intros x xs xs' Eq Lift n. *) *)
(*   (*   rewrite <-Eq; auto. *) *)
(*   (* Qed. *) *)

(*   (* Add Parametric Morphism : clock_of *) *)
(*   (*     with signature eq_str ==> eq ==> Basics.impl *) *)
(*   (*       as clock_of_eq_str. *) *)
(*   (* Proof. *) *)
(*   (*   unfold clock_of. intros ** E b Pres n. *) *)
(*   (*   split; intros H. *) *)
(*   (*   - apply Pres. *) *)
(*   (*     specialize (E n). *) *)
(*   (*     induction H; rewrite E; constructor; auto. *) *)
(*   (*   - apply Pres in H. *) *)
(*   (*     specialize (E n). *) *)
(*   (*     induction H; rewrite <-E; constructor; auto. *) *)
(*   (* Qed. *) *)

(*   (* Add Parametric Morphism : reset_of *) *)
(*   (*     with signature eq_str ==> eq_str *) *)
(*   (*       as reset_of_eq_str. *) *)
(*   (* Proof. *) *)
(*   (*   unfold reset_of. intros ** E n. *) *)
(*   (*   now rewrite E. *) *)
(*   (* Qed. *) *)

(*   (* Add Parametric Morphism : reset_regs *) *)
(*   (*     with signature eq_str ==> eq ==> Basics.impl *) *)
(*   (*       as reset_regs_eq_str. *) *)
(*   (* Proof. *) *)
(*   (*   intros ** E M Rst. *) *)
(*   (*   induction Rst; constructor; eauto. *) *)
(*   (* Qed. *) *)

(*   Add Parametric Morphism : same_clock *)
(*       with signature eq_str ==> Basics.impl *)
(*         as same_clock_eq_str. *)
(*   Proof. *)
(*     unfold same_clock; intros ** E ? ?; rewrite <-E; auto. *)
(*   Qed. *)

(*   (** ** Clocking property *) *)

(*   Lemma not_subrate_clock: *)
(*     forall R S ck, *)
(*       ~ sem_clock_instant false R S ck true. *)
(*   Proof. *)
(*     intros ** Sem; induction ck; inv Sem. *)
(*     now apply IHck. *)
(*   Qed. *)

(*   Lemma present_not_absent_list: *)
(*     forall xs (vs: list val), *)
(*       instant_same_clock xs -> *)
(*       ~ absent_list xs -> *)
(*       present_list xs. *)
(*   Proof. *)
(*     intros ** Hsamexs Hnabs. *)
(*     now destruct Hsamexs. *)
(*   Qed. *)

(*   Lemma sem_vars_gt0: *)
(*     forall H (xs: list (ident * type)) ls, *)
(*       0 < length xs -> *)
(*       sem_vars H (map fst xs) ls -> *)
(*       forall n, 0 < length (ls n). *)
(*   Proof. *)
(*     intros ** Hgt0 Hsem n. *)
(*     specialize (Hsem n). *)
(*     apply Forall2_length in Hsem. *)
(*     rewrite map_length in Hsem. *)
(*     now rewrite Hsem in Hgt0. *)
(*   Qed. *)

(*   Ltac assert_const_length xss := *)
(*     match goal with *)
(*       H: sem_vars _ _ xss |- _ => *)
(*       let H' := fresh in *)
(*       let k := fresh in *)
(*       let k' := fresh in *)
(*       assert (wf_streams xss) *)
(*         by (intros k k'; pose proof H as H'; *)
(*             unfold sem_vars, lift in *; *)
(*             specialize (H k); specialize (H' k'); *)
(*             apply Forall2_length in H; apply Forall2_length in H'; *)
(*             now rewrite H in H') *)
(*     end. *)

(*   (** ** Determinism of the semantics *) *)

(*   (** *** Instantaneous semantics *) *)

(*   Section InstantDeterminism. *)

(*     Variable base: bool. *)
(*     Variable R: env. *)
(*     Variable S: state. *)

(*     Lemma sem_var_var_instant_det: *)
(*       forall x v1 v2, *)
(*         sem_var_var_instant R x v1 *)
(*         -> sem_var_var_instant R x v2 *)
(*         -> v1 = v2. *)
(*     Proof. *)
(*       intros x v1 v2 H1 H2. *)
(*       inversion_clear H1 as [Hf1]; *)
(*         inversion_clear H2 as [Hf2]; *)
(*         congruence. *)
(*     Qed. *)
(*     Hint Resolve sem_var_var_instant_det. *)

(*     Lemma sem_clock_state_var_var_instant_det: *)
(*       (forall ck v1, *)
(*           sem_clock_instant base R S ck v1 -> *)
(*           forall v2, *)
(*             sem_clock_instant base R S ck v2 -> *)
(*             v1 = v2) *)
(*       /\ *)
(*       (forall ck x v1, *)
(*           sem_state_var_instant base R S ck x v1 -> *)
(*           forall v2, *)
(*             sem_state_var_instant base R S ck x v2 -> *)
(*             v1 = v2) *)
(*       /\ *)
(*       (forall ck x v1, *)
(*           sem_var_instant base R S ck x v1 -> *)
(*           forall v2, *)
(*             sem_var_instant base R S ck x v2 -> *)
(*             v1 = v2). *)
(*     Proof. *)
(*       apply sem_clock_state_var_var_mut. *)
(*       - intro; now inversion 1. *)
(*       - intros ** VarDet ?? Sem. *)
(*         inversion Sem as [ | | |??? b' ? SVar]; subst; auto. *)
(*         apply VarDet in SVar; inv SVar. *)
(*         destruct b'; simpl in *; congruence. *)
(*       - intros ** Sem; inv Sem; auto. *)
(*       - intros ** VarDet ?? Sem. *)
(*         inversion Sem as [ |????? SVar| |]; subst; auto. *)
(*         apply VarDet in SVar; inv SVar. *)
(*         destruct b; simpl in *; congruence. *)
(*       - intros ** ClockDet ? Sem. *)
(*         inversion_clear Sem as [|??? SClock]; try congruence. *)
(*         apply ClockDet in SClock; discriminate. *)
(*       - intros ** ClockDet ? Sem. *)
(*         inversion_clear Sem as [???? SClock|]; auto. *)
(*         apply ClockDet in SClock; discriminate. *)
(*       - intros ** Sem; inv Sem; eauto. *)
(*       - intros ** Sem; inv Sem; auto. *)
(*     Qed. *)

(*     Corollary sem_clock_instant_det: *)
(*       forall ck v1 v2, *)
(*         sem_clock_instant base R S ck v1 *)
(*         -> sem_clock_instant base R S ck v2 *)
(*         -> v1 = v2. *)
(*     Proof. *)
(*       intros; eapply sem_clock_state_var_var_instant_det; eauto. *)
(*     Qed. *)
(*     Hint Resolve sem_clock_instant_det. *)

(*     Corollary sem_state_var_instant_det: *)
(*       forall x ck v1 v2, *)
(*         sem_state_var_instant base R S ck x v1 *)
(*         -> sem_state_var_instant base R S ck x v2 *)
(*         -> v1 = v2. *)
(*     Proof. *)
(*       intros; eapply (proj1 (proj2 sem_clock_state_var_var_instant_det)); eauto. *)
(*     Qed. *)
(*     Hint Resolve sem_state_var_instant_det. *)

(*     Corollary sem_var_instant_det: *)
(*       forall x ck v1 v2, *)
(*         sem_var_instant base R S ck x v1 *)
(*         -> sem_var_instant base R S ck x v2 *)
(*         -> v1 = v2. *)
(*     Proof. *)
(*       intros; eapply sem_clock_state_var_var_instant_det; eauto. *)
(*     Qed. *)
(*     Hint Resolve sem_var_instant_det. *)

(*     Lemma sem_lexp_instant_det: *)
(*       forall e ck v1 v2, *)
(*         sem_lexp_instant base R S ck e v1 *)
(*         -> sem_lexp_instant base R S ck e v2 *)
(*         -> v1 = v2. *)
(*     Proof. *)
(*       induction e (* using lexp_ind2 *). *)
(*       - (* Econst *) *)
(*         do 2 inversion_clear 1; destruct base; congruence. *)
(*       - (* Evar *) *)
(*         intros ** S1 S2; inv S1; inv S2; eauto. *)
(*       - (* Ewhen *) *)
(*         intros ** S1 S2; inv S1; inv S2; eauto; *)
(*           repeat progress match goal with *)
(*                           | H1:sem_lexp_instant ?b ?R ?S ?ck ?e ?v1, *)
(*                                H2:sem_lexp_instant ?b ?R ?S ?ck ?e ?v2 |- _ => *)
(*                             apply IHe with (1:=H1) in H2 *)
(*                           | H1:sem_var_instant ?b ?R ?S ?ck ?i ?v1, *)
(*                                H2:sem_var_instant ?b ?R ?S ?ck ?i ?v2 |- _ => *)
(*                             apply sem_var_instant_det with (1:=H1) in H2 *)
(*                           | Hp:present _ = present _ |- _ => *)
(*                             injection Hp; intro; subst *)
(*                           | H1:val_to_bool _ = Some _, *)
(*                                H2:val_to_bool _ = Some (negb _) |- _ => *)
(*                             rewrite H2 in H1; exfalso; injection H1; *)
(*                               now apply Bool.no_fixpoint_negb *)
(*                           end; subst; auto. *)
(*       - (* Eunop *) *)
(*         intros ** S1 S2; inv S1; inv S2; *)
(*           repeat progress match goal with *)
(*                           | H1:sem_lexp_instant _ _ _ _ e _, H2:sem_lexp_instant _ _ _ _ e _ |- _ => *)
(*                             apply IHe with (1:=H1) in H2; inversion H2; subst *)
(*                           | H1:sem_unop _ _ _ = _, H2:sem_unop _ _ _ = _ |- _ => *)
(*                             rewrite H1 in H2; injection H2; intro; subst *)
(*                           | H1:sem_lexp_instant _ _ _ _ _ (present _), *)
(*                                H2:sem_lexp_instant _ _ _ _ _ absent |- _ => *)
(*                             apply IHe with (1:=H1) in H2 *)
(*                           end; try auto. *)
(*       - (* Ebinop *) *)
(*         intros ** S1 S2; inv S1; inv S2; *)
(*           repeat progress match goal with *)
(*                           | H1:sem_lexp_instant _ _ _ _ e1 _, H2:sem_lexp_instant _ _ _ _ e1 _ |- _ => *)
(*                             apply IHe1 with (1:=H1) in H2 *)
(*                           | H1:sem_lexp_instant _ _ _ _ e2 _, H2:sem_lexp_instant _ _ _ _ e2 _ |- _ => *)
(*                             apply IHe2 with (1:=H1) in H2 *)
(*                           | H1:sem_binop _ _ _ _ _ = Some ?v1, *)
(*                                H2:sem_binop _ _ _ _ _ = Some ?v2 |- _ => *)
(*                             rewrite H1 in H2; injection H2; intro; subst *)
(*                           | H:present _ = present _ |- _ => injection H; intro; subst *)
(*                           end; subst; auto; discriminate. *)
(*     Qed. *)
(*     Hint Resolve sem_lexp_instant_det. *)

(*     Lemma sem_laexp_instant_det: *)
(*       forall ck e v1 v2, *)
(*         sem_laexp_instant base R S ck e v1 *)
(*         -> sem_laexp_instant base R S ck e v2 *)
(*         -> v1 = v2. *)
(*     Proof. *)
(*       do 2 inversion_clear 1; eauto. *)
(*     Qed. *)

(*     Lemma sem_lexps_instant_det: *)
(*       forall les ck cs1 cs2, *)
(*         sem_lexps_instant base R S ck les cs1 -> *)
(*         sem_lexps_instant base R S ck les cs2 -> *)
(*         cs1 = cs2. *)
(*     Proof. *)
(*       intros ???; eapply Forall2_det; eauto. *)
(*     Qed. *)
(*     Hint Resolve sem_lexps_instant_det. *)

(*     Lemma sem_laexps_instant_det: *)
(*       forall ck e v1 v2, *)
(*         sem_laexps_instant base R S ck e v1 *)
(*         -> sem_laexps_instant base R S ck e v2 *)
(*         -> v1 = v2. *)
(*     Proof. *)
(*       do 2 inversion_clear 1; eauto. *)
(*     Qed. *)

(*     Lemma sem_cexp_instant_det: *)
(*       forall e ck v1 v2, *)
(*         sem_cexp_instant base R S ck e v1 *)
(*         -> sem_cexp_instant base R S ck e v2 *)
(*         -> v1 = v2. *)
(*     Proof. *)
(*       induction e; *)
(*         do 2 inversion_clear 1; *)
(*         try repeat progress match goal with *)
(*                             | H1: sem_cexp_instant ?bk ?R ?S ?ck ?e ?l, *)
(*                                   H2: sem_cexp_instant ?bk ?R ?S ?ck ?e ?r |- _ => *)
(*                               apply IHe1 with (1:=H1) in H2 *)
(*                                                          || apply IHe2 with (1:=H1) in H2; *)
(*                                 injection H2; intro; subst *)
(*                             | H1: sem_var_instant ?b ?R ?S ?ck ?i (present true_val), *)
(*                                   H2: sem_var_instant ?b ?R ?S ?ck ?i (present false_val) |- _ => *)
(*                               apply sem_var_instant_det with (1:=H1) in H2; *)
(*                                 exfalso; injection H2; now apply true_not_false_val *)
(*                             | H1: sem_lexp_instant ?bk ?R ?S ?ck ?l ?v1, *)
(*                                   H2: sem_lexp_instant ?bk ?R ?S ?ck ?l ?v2 |- _ => *)
(*                               apply sem_lexp_instant_det with (1:=H1) in H2; *)
(*                                 discriminate || injection H2; intro; subst *)
(*                             | H1: sem_var_instant ?bk ?R ?S ?ck ?i (present _), *)
(*                                   H2: sem_var_instant ?bk ?R ?S ?ck ?i absent |- _ => *)
(*                               apply sem_var_instant_det with (1:=H1) in H2; discriminate *)
(*                             | H1: val_to_bool _ = Some _, *)
(*                                   H2:val_to_bool _ = Some _ |- _ => *)
(*                               rewrite H1 in H2; injection H2; intro; subst *)
(*                             end; eauto. *)
(*     Qed. *)
(*     Hint Resolve sem_cexp_instant_det. *)

(*     Lemma sem_caexp_instant_det: *)
(*       forall ck e v1 v2, *)
(*         sem_caexp_instant base R S ck e v1 *)
(*         -> sem_caexp_instant base R S ck e v2 *)
(*         -> v1 = v2. *)
(*     Proof. *)
(*       intros until v2. *)
(*       do 2 inversion_clear 1; eauto. *)
(*     Qed. *)

(*   End InstantDeterminism. *)

(*   (** *** Lifted semantics *) *)

(*   (* Section LiftDeterminism. *) *)

(* (*     Variable bk : stream bool. *) *)
(* (*     Variable H : history. *) *)

(* (*     Require Import Logic.FunctionalExtensionality. *) *)

(* (*     Lemma lift_det: *) *)
(* (*       forall {A B} (P: bool -> env -> A -> B -> Prop) (bk: stream bool) *) *)
(* (*         x (xs1 xs2 : stream B), *) *)
(* (*         (forall b R v1 v2, P b R x v1 -> P b R x v2 -> v1 = v2) -> *) *)
(* (*         lift bk H P x xs1 -> lift bk H P x xs2 -> xs1 = xs2. *) *)
(* (*     Proof. *) *)
(* (*       intros ** Hpoint H1 H2. *) *)
(* (*       extensionality n. specialize (H1 n). specialize (H2 n). *) *)
(* (*       eapply Hpoint; eassumption. *) *)
(* (*     Qed. *) *)

(* (*     Lemma lift'_det: *) *)
(* (*       forall {A B} (P: env -> A -> B -> Prop) *) *)
(* (*         x (xs1 xs2 : stream B), *) *)
(* (*         (forall R v1 v2, P R x v1 -> P R x v2 -> v1 = v2) -> *) *)
(* (*         lift' H P x xs1 -> lift' H P x xs2 -> xs1 = xs2. *) *)
(* (*     Proof. *) *)
(* (*       intros ** Hpoint H1 H2. *) *)
(* (*       extensionality n. specialize (H1 n). specialize (H2 n). *) *)
(* (*       eapply Hpoint; eassumption. *) *)
(* (*     Qed. *) *)

(* (*     Ltac apply_lift sem_det := *) *)
(* (*       intros; eapply lift_det; try eassumption; *) *)
(* (*       compute; intros; eapply sem_det; eauto. *) *)

(* (*     Ltac apply_lift' sem_det := *) *)
(* (*       intros; eapply lift'_det; try eassumption; *) *)
(* (*       compute; intros; eapply sem_det; eauto. *) *)

(* (*     Lemma sem_var_det: *) *)
(* (*       forall x xs1 xs2, *) *)
(* (*         sem_var H x xs1 -> sem_var H x xs2 -> xs1 = xs2. *) *)
(* (*     Proof. *) *)
(* (*       apply_lift' sem_var_instant_det. *) *)
(* (*     Qed. *) *)

(* (*     Lemma sem_clock_det: *) *)
(* (*       forall ck bs1 bs2, *) *)
(* (*         sem_clock bk H ck bs1 -> sem_clock bk H ck bs2 -> bs1 = bs2. *) *)
(* (*     Proof. *) *)
(* (*       apply_lift sem_clock_instant_det. *) *)
(* (*     Qed. *) *)

(* (*     Lemma sem_lexp_det: *) *)
(* (*       forall e xs1 xs2, *) *)
(* (*         sem_lexp bk H e xs1 -> sem_lexp bk H e xs2 -> xs1 = xs2. *) *)
(* (*     Proof. *) *)
(* (*       apply_lift sem_lexp_instant_det. *) *)
(* (*     Qed. *) *)

(* (*     Lemma sem_lexps_det: *) *)
(* (*       forall les cs1 cs2, *) *)
(* (*         sem_lexps bk H les cs1 -> *) *)
(* (*         sem_lexps bk H les cs2 -> *) *)
(* (*         cs1 = cs2. *) *)
(* (*     Proof. *) *)
(* (*       apply_lift sem_lexps_instant_det. *) *)
(* (*     Qed. *) *)

(* (*     Lemma sem_laexp_det: *) *)
(* (*       forall ck e xs1 xs2, *) *)
(* (*         sem_laexp bk H ck e xs1 -> sem_laexp bk H ck e xs2 -> xs1 = xs2. *) *)
(* (*     Proof. *) *)
(* (*       apply_lift sem_laexp_instant_det. *) *)
(* (*     Qed. *) *)

(* (*     Lemma sem_laexps_det: *) *)
(* (*       forall ck e xs1 xs2, *) *)
(* (*         sem_laexps bk H ck e xs1 -> sem_laexps bk H ck e xs2 -> xs1 = xs2. *) *)
(* (*     Proof. *) *)
(* (*       apply_lift sem_laexps_instant_det. *) *)
(* (*     Qed. *) *)

(* (*     Lemma sem_cexp_det: *) *)
(* (*       forall c xs1 xs2, *) *)
(* (*         sem_cexp bk H c xs1 -> sem_cexp bk H c xs2 -> xs1 = xs2. *) *)
(* (*     Proof. *) *)
(* (*       apply_lift sem_cexp_instant_det. *) *)
(* (*     Qed. *) *)

(* (*     Lemma sem_caexp_det: *) *)
(* (*       forall ck c xs1 xs2, *) *)
(* (*         sem_caexp bk H ck c xs1 -> sem_caexp bk H ck c xs2 -> xs1 = xs2. *) *)
(* (*     Proof. *) *)
(* (*       apply_lift sem_caexp_instant_det. *) *)
(* (*     Qed. *) *)

(* (*   (* XXX: every semantics definition, including [sem_var] which doesn't *) *)
(* (* need it, takes a base clock value or base clock stream, except *) *)
(* (* [sem_var_instant]. For uniformity, we may want to pass a (useless) *) *)
(* (* clock to [sem_var_instant] too. *) *) *)

(* (*   End LiftDeterminism. *) *)

(*   (* Ltac sem_det := *) *)
(*   (*   match goal with *) *)
(*   (*   | H1: sem_clock_instant ?bk ?H ?C ?X, *) *)
(*   (*         H2: sem_clock_instant ?bk ?H ?C ?Y |- ?X = ?Y => *) *)
(*   (*     eapply sem_clock_instant_det; eexact H1 || eexact H2 *) *)
(*   (*   | H1: sem_clock ?bk ?H ?C ?X, *) *)
(*   (*         H2: sem_clock ?bk ?H ?C ?Y |- ?X = ?Y => *) *)
(*   (*     eapply sem_clock_det; eexact H1 || eexact H2 *) *)
(*   (*   | H1: sem_cexp_instant ?bk ?H ?C ?X, *) *)
(*   (*         H2: sem_cexp_instant ?bk ?H ?C ?Y |- ?X = ?Y => *) *)
(*   (*     eapply sem_cexp_instant_det; eexact H1 || eexact H2 *) *)
(*   (*   | H1: sem_cexp ?bk ?H ?C ?X, *) *)
(*   (*         H2: sem_cexp ?bk ?H ?C ?Y |- ?X = ?Y => *) *)
(*   (*     eapply sem_cexp_det; eexact H1 || eexact H2 *) *)
(*   (*   | H1: sem_lexps_instant ?bk ?H ?C ?X, *) *)
(*   (*         H2: sem_lexps_instant ?bk ?H ?C ?Y |- ?X = ?Y => *) *)
(*   (*     eapply sem_lexps_instant_det; eexact H1 || eexact H2 *) *)
(*   (*   | H1: sem_lexps ?bk ?H ?C ?X, *) *)
(*   (*         H2: sem_lexps ?bk ?H ?C ?Y |- ?X = ?Y => *) *)
(*   (*     eapply sem_lexps_det; eexact H1 || eexact H2 *) *)
(*   (*   | H1: sem_laexps_instant ?bk ?H ?ck ?C ?X, *) *)
(*   (*         H2: sem_laexps_instant ?bk ?H ?ck ?C ?Y |- ?X = ?Y => *) *)
(*   (*     eapply sem_laexps_instant_det; eexact H1 || eexact H2 *) *)
(*   (*   | H1: sem_laexps ?bk ?H ?ck ?C ?X, *) *)
(*   (*         H2: sem_laexps ?bk ?H ?ck ?C ?Y |- ?X = ?Y => *) *)
(*   (*     eapply sem_laexps_det; eexact H1 || eexact H2 *) *)
(*   (*   | H1: sem_lexp_instant ?bk ?H ?C ?X, *) *)
(*   (*         H2: sem_lexp_instant ?bk ?H ?C ?Y |- ?X = ?Y => *) *)
(*   (*     eapply sem_lexp_instant_det; eexact H1 || eexact H2 *) *)
(*   (*   | H1: sem_lexp ?bk ?H ?C ?X, *) *)
(*   (*         H2: sem_lexp ?bk ?H ?C ?Y |- ?X = ?Y => *) *)
(*   (*     eapply sem_lexp_det; eexact H1 || eexact H2 *) *)
(*   (*   | H1: sem_laexp_instant ?bk ?H ?CK ?C ?X, *) *)
(*   (*         H2: sem_laexp_instant ?bk ?H ?CK ?C ?Y |- ?X = ?Y => *) *)
(*   (*     eapply sem_laexp_instant_det; eexact H1 || eexact H2 *) *)
(*   (*   | H1: sem_laexp ?bk ?H ?CK ?C ?X, *) *)
(*   (*         H2: sem_laexp ?bk ?H ?CK ?C ?Y |- ?X = ?Y => *) *)
(*   (*     eapply sem_laexp_det; eexact H1 || eexact H2 *) *)
(*   (*   | H1: sem_var_instant ?H ?C ?X, *) *)
(*   (*         H2: sem_var_instant ?H ?C ?Y |- ?X = ?Y => *) *)
(*   (*     eapply sem_var_instant_det; eexact H1 || eexact H2 *) *)
(*   (*   | H1: sem_var ?H ?C ?X, *) *)
(*   (*         H2: sem_var ?H ?C ?Y |- ?X = ?Y => *) *)
(*   (*     eapply sem_var_det; eexact H1 || eexact H2 *) *)
(*   (*   end. *) *)
(*   (* Record mvalue := *) *)
(*   (*   Mvalue { content_i: val; *) *)
(*   (*            reset_i: bool *) *)
(*   (*          }. *) *)


(*   (** Morphisms properties *) *)

(*   Add Parametric Morphism P b E E': (fun xss yss => sem_block P b E xss yss E') *)
(*       with signature eq_str ==> eq_str ==> Basics.impl *)
(*         as sem_node_eq_str. *)
(*   Proof. *)
(*     intros ** E1 ? ? E2 Block. *)
(*     inv Block. *)
(*     econstructor; eauto; intro; try rewrite <-E1; try rewrite <-E2; auto. *)
(*   Qed. *)

(*   Lemma sem_block_wf: *)
(*     forall P f E E' xss yss, *)
(*       sem_block P f E xss yss E' -> *)
(*       wf_streams xss /\ wf_streams yss. *)
(*   Proof. *)
(*     intros ** Sem; split; inv Sem; *)
(*       assert_const_length xss; assert_const_length yss; auto. *)
(*   Qed. *)

(*   (* Lemma sem_EqCall_gt0: *) *)
(*   (*   forall P bk H M xs ck b i es, *) *)
(*   (*     sem_equation P bk H M (EqCall xs ck b i es) -> *) *)
(*   (*     0 < length xs. *) *)
(*   (* Proof. *) *)
(*   (*   inversion_clear 1 as [| | |????????????? Block' Vars]. *) *)
(*   (*   inversion_clear Block' as [??????????? Out]. *) *)
(*   (*   specialize (Out 0); specialize (Vars 0); simpl in *; *) *)
(*   (*     apply Forall2_length in Out; apply Forall2_length in Vars. *) *)
(*   (*   rewrite <-Out in Vars; rewrite Vars, map_length; apply b_outgt0. *) *)
(*   (* Qed. *) *)

(*   (* Lemma In_fold_left_fby_eq: *) *)
(*   (*   forall x eqs m, *) *)
(*   (*     PS.In x (fold_left fby_eq eqs m) *) *)
(*   (*     <-> PS.In x (fbys eqs) \/ PS.In x m. *) *)
(*   (* Proof. *) *)
(*   (*   unfold fbys. *) *)
(*   (*   induction eqs as [|eq]. *) *)
(*   (*   - split; auto. *) *)
(*   (*     destruct 1 as [H|]. *) *)
(*   (*     apply not_In_empty in H; contradiction. *) *)
(*   (*     auto. *) *)
(*   (*   - split. *) *)
(*   (*     + intro H. *) *)
(*   (*       simpl; rewrite IHeqs. *) *)
(*   (*       simpl in H; apply IHeqs in H; destruct H; auto. *) *)
(*   (*       destruct eq; auto. *) *)
(*   (*       apply PS.add_spec in H. *) *)
(*   (*       destruct H. *) *)
(*   (*       rewrite H; left; right; apply PS.add_spec; intuition. *) *)
(*   (*       intuition. *) *)
(*   (*     + destruct 1 as [H|H]. *) *)
(*   (*       * simpl in H; rewrite IHeqs in H; apply IHeqs; destruct H; auto. *) *)
(*   (*         right. *) *)
(*   (*         destruct eq; try (apply not_In_empty in H; contradiction). *) *)
(*   (*         simpl; apply PS.add_spec. *) *)
(*   (*         apply PS.add_spec in H; destruct H; *) *)
(*   (*           try apply not_In_empty in H; intuition. *) *)
(*   (*       * apply IHeqs; right; destruct eq; auto. *) *)
(*   (*         apply PS.add_spec; auto. *) *)
(*   (* Qed. *) *)

(*   (* Lemma In_fold_left_inst_eq: *) *)
(*   (*   forall x eqs m, *) *)
(*   (*     PS.In x (fold_left inst_eq eqs m) *) *)
(*   (*     <-> PS.In x (insts eqs) \/ PS.In x m. *) *)
(*   (* Proof. *) *)
(*   (*   unfold insts. *) *)
(*   (*   induction eqs as [|eq]. *) *)
(*   (*   - split; auto. *) *)
(*   (*     destruct 1 as [H|]. *) *)
(*   (*     apply not_In_empty in H; contradiction. *) *)
(*   (*     auto. *) *)
(*   (*   - split. *) *)
(*   (*     + intro H. *) *)
(*   (*       simpl; rewrite IHeqs. *) *)
(*   (*       simpl in H; apply IHeqs in H; destruct H; auto. *) *)
(*   (*       destruct eq; auto; apply PS.add_spec in H; destruct H; auto; *) *)
(*   (*         rewrite H; left; right; apply PS.add_spec; auto. *) *)
(*   (*     + destruct 1 as [H|H]. *) *)
(*   (*       * simpl in H; rewrite IHeqs in H; apply IHeqs; destruct H; auto. *) *)
(*   (*         right. *) *)
(*   (*         destruct eq; try (apply not_In_empty in H; contradiction); *) *)
(*   (*           simpl; apply PS.add_spec; *) *)
(*   (*             apply PS.add_spec in H; destruct H; auto; *) *)
(*   (*               apply not_In_empty in H; contradiction. *) *)
(*   (*       * apply IHeqs; right; destruct eq; auto; *) *)
(*   (*           apply PS.add_spec; auto. *) *)
(*   (* Qed. *) *)

(*   (* Lemma well_structured_def: *) *)
(*   (*   forall M x ck e eqs, *) *)
(*   (*     well_structured_memories (EqDef x ck e :: eqs) M <-> *) *)
(*   (*     well_structured_memories eqs M. *) *)
(*   (* Proof. *) *)
(*   (*   split; eauto. *) *)
(*   (* Qed. *) *)

(*   (* Lemma well_structured_add_inst_call: *) *)
(*   (*   forall M M' xs ck f i es eqs, *) *)
(*   (*     well_structured_memories eqs M -> *) *)
(*   (*     well_structured_memories (EqCall xs ck f i es :: eqs) (add_inst i M' M). *) *)
(*   (* Proof. *) *)
(*   (*   intros ** WS. *) *)
(*   (*   constructor; unfold fbys, insts; simpl; split; intro H. *) *)
(*   (*   - rewrite find_val_add_inst in H; apply WS in H; auto. *) *)
(*   (*   - rewrite find_val_add_inst; apply WS in H; auto. *) *)
(*   (*   - rewrite In_fold_left_inst_eq. *) *)
(*   (*     destruct (ident_eqb x i) eqn: E; *) *)
(*   (*       [apply ident_eqb_eq in E; subst|apply ident_eqb_neq in E]. *) *)
(*   (*     + right; apply PSE.MP.Dec.F.add_1; auto. *) *)
(*   (*     + rewrite find_inst_gso in H; auto. *) *)
(*   (*       apply WS in H; auto. *) *)
(*   (*   - destruct (ident_eqb x i) eqn: E; *) *)
(*   (*       [apply ident_eqb_eq in E; subst|apply ident_eqb_neq in E]. *) *)
(*   (*     + rewrite find_inst_gss; intro; discriminate. *) *)
(*   (*     + rewrite find_inst_gso; auto. *) *)
(*   (*       apply WS. *) *)
(*   (*       apply In_fold_left_inst_eq in H as [|H]; auto. *) *)
(*   (*       apply PSE.MP.Dec.F.add_3 in H; auto. *) *)
(*   (*       contradict H; apply not_In_empty. *) *)
(*   (* Qed. *) *)

(*   (* Lemma well_structured_reset_call: *) *)
(*   (*   forall M xs ck f i es ck_r r eqs, *) *)
(*   (*     well_structured_memories (EqCall xs ck f i es :: eqs) M -> *) *)
(*   (*     well_structured_memories (EqReset ck_r f i r :: EqCall xs ck f i es :: eqs) M. *) *)
(*   (* Proof. *) *)
(*   (*   inversion_clear 1 as [Vals Insts]. *) *)
(*   (*   constructor; unfold fbys, insts in *; simpl in *. *) *)
(*   (*   - intro; rewrite Vals; reflexivity. *) *)
(*   (*   - intro; rewrite Insts. *) *)
(*   (*     rewrite 2 In_fold_left_inst_eq. *) *)
(*   (*     split; intros [H|H']; auto. *) *)
(*   (*     + rewrite PSE.MP.Dec.F.add_iff; auto. *) *)
(*   (*     + apply PSE.MP.Dec.F.add_iff in H' as []; auto. *) *)
(*   (*       rewrite PSE.MP.Dec.F.add_iff; auto. *) *)
(*   (* Qed. *) *)

(*   (* Corollary well_structured_add_inst_reset_call: *) *)
(*   (*   forall M M' xs ck f i es ck_r r eqs, *) *)
(*   (*     well_structured_memories eqs M -> *) *)
(*   (*     well_structured_memories (EqReset ck_r f i r :: EqCall xs ck f i es :: eqs) (add_inst i M' M). *) *)
(*   (* Proof. *) *)
(*   (*   intros; apply well_structured_reset_call, well_structured_add_inst_call; auto. *) *)
(*   (* Qed. *) *)

(*   (* Lemma well_structured_add_val_fby: *) *)
(*   (*   forall M mvs x ck v0 e eqs, *) *)
(*   (*     well_structured_memories eqs M -> *) *)
(*   (*     well_structured_memories (EqFby x ck v0 e :: eqs) (add_val x mvs M). *) *)
(*   (* Proof. *) *)
(*   (*   intros ** WS. *) *)
(*   (*   constructor; unfold fbys, insts; simpl; split; intro H. *) *)
(*   (*   - rewrite In_fold_left_fby_eq. *) *)
(*   (*     destruct (ident_eqb x x0) eqn: E; *) *)
(*   (*       [apply ident_eqb_eq in E; subst|apply ident_eqb_neq in E]. *) *)
(*   (*     + right; apply PSE.MP.Dec.F.add_1; auto. *) *)
(*   (*     + rewrite find_val_gso in H; auto. *) *)
(*   (*       apply WS in H; auto. *) *)
(*   (*   - destruct (ident_eqb x x0) eqn: E; *) *)
(*   (*       [apply ident_eqb_eq in E; subst|apply ident_eqb_neq in E]. *) *)
(*   (*     + rewrite find_val_gss; intro; discriminate. *) *)
(*   (*     + rewrite find_val_gso; auto. *) *)
(*   (*       apply WS. *) *)
(*   (*       apply In_fold_left_fby_eq in H as [|H]; auto. *) *)
(*   (*       apply PSE.MP.Dec.F.add_3 in H; auto. *) *)
(*   (*       contradict H; apply not_In_empty. *) *)
(*   (*   - rewrite find_inst_add_val in H; apply WS in H; auto. *) *)
(*   (*   - rewrite find_inst_add_val; apply WS in H; auto. *) *)
(*   (* Qed. *) *)

End SBSEMANTICS.