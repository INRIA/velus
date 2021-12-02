From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import Operators.

Open Scope bool_scope.
From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

(** * Obc syntax *)

(**
  Obc is a minimal object-oriented programming language.
 *)

Module Type OBCSYNTAX
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op).

  Inductive exp : Type :=
  | Var   : ident -> type -> exp                (* variable  *)
  | State : ident -> type -> exp                (* state variable  *)
  | Enum  : enumtag -> type -> exp
  | Const : cconst -> exp                         (* constant *)
  | Unop  : unop -> exp -> type -> exp          (* unary operator *)
  | Binop : binop -> exp -> exp -> type -> exp  (* binary operator *)
  | Valid : ident -> type -> exp.                         (* valid value assertion *)

  Definition typeof (e: exp): type :=
    match e with
    | Const c => Tprimitive (ctype_cconst c)
    | Var _ ty
    | State _ ty
    | Enum _ ty
    | Unop _ _ ty
    | Binop _ _ _ ty
    | Valid _ ty => ty
    end.

  Inductive stmt : Type :=
  | Assign   : ident -> exp -> stmt                    (* x = e *)
  | AssignSt : ident -> exp -> stmt                  (* self.x = e *)
  | Switch   : exp -> list (option stmt) -> stmt -> stmt
  | Comp     : stmt -> stmt -> stmt                      (* s1; s2 *)
  | Call     : list ident -> ident -> ident -> ident -> list exp -> stmt
  (* y1, ..., yn := class instance method (e1, ..., em) *)
  (* The method name must be an atom, in order to guarantee injectivity of the prefixed C call *)
  | Skip.

  Section stmt_ind2.

    Variable P : stmt -> Prop.

    Hypothesis AssignCase:
      forall x e,
        P (Assign x e).

    Hypothesis AssignStCase:
      forall x e,
        P (AssignSt x e).

    Hypothesis SwitchCase:
      forall e ss d,
        Forall (fun s => P (or_default d s)) ss ->
        P (Switch e ss d).

    Hypothesis CompCase:
      forall s1 s2,
        P s1 ->
        P s2 ->
        P (Comp s1 s2).

    Hypothesis CallCase:
      forall ys c i f es,
        P (Call ys c i f es).

    Hypothesis SkipCase:
      P Skip.

    Fixpoint stmt_ind2 (s : stmt) : P s.
    Proof.
      destruct s.
      - apply AssignCase.
      - apply AssignStCase.
      - apply SwitchCase; auto.
        induction l as [|[]]; auto.
      - apply CompCase; auto.
      - apply CallCase.
      - apply SkipCase.
    Defined.

  End stmt_ind2.

  Section stmt_ind2'.

    Variable P : stmt -> Prop.

    Hypothesis AssignCase:
      forall x e,
        P (Assign x e).

    Hypothesis AssignStCase:
      forall x e,
        P (AssignSt x e).

    Hypothesis SwitchCase:
      forall e ss d,
        P d ->
        Forall (or_default_with True P) ss ->
        P (Switch e ss d).

    Hypothesis CompCase:
      forall s1 s2,
        P s1 ->
        P s2 ->
        P (Comp s1 s2).

    Hypothesis CallCase:
      forall ys c i f es,
        P (Call ys c i f es).

    Hypothesis SkipCase:
      P Skip.

    Fixpoint stmt_ind2' (s : stmt) : P s.
    Proof.
      destruct s.
      - apply AssignCase.
      - apply AssignStCase.
      - apply SwitchCase; auto.
        induction l as [|[]]; constructor; simpl; auto.
      - apply CompCase; auto.
      - apply CallCase.
      - apply SkipCase.
    Defined.

  End stmt_ind2'.

  Record method : Type :=
    mk_method {
        m_name : ident;
        m_in   : list (ident * type);
        m_vars : list (ident * type);
        m_out  : list (ident * type);
        m_body : stmt;

        m_nodupvars : NoDupMembers (m_in ++ m_vars ++ m_out);
        m_good      : Forall (AtomOrGensym (PSP.of_list gensym_prefs)) (map fst (m_in ++ m_vars ++ m_out)) /\
                      atom m_name
      }.

  Definition meth_vars m := m.(m_in) ++ m.(m_vars) ++ m.(m_out).
  Hint Resolve m_nodupvars.

  Lemma m_nodupout:
    forall f, NoDupMembers (m_out f).
  Proof.
    intro; pose proof (m_nodupvars f) as Nodup;
    now repeat apply NoDupMembers_app_r in Nodup.
  Qed.

  Lemma m_nodupin:
    forall f, NoDupMembers (m_in f).
  Proof.
    intro; pose proof (m_nodupvars f) as Nodup;
    now apply NoDupMembers_app_l in Nodup.
  Qed.

  Lemma m_nodupvars':
    forall f, NoDupMembers (m_vars f).
  Proof.
    intro; pose proof (m_nodupvars f) as Nodup;
    now apply NoDupMembers_app_r, NoDupMembers_app_l in Nodup.
  Qed.

  Remark In_meth_vars_out:
    forall f x ty,
      InMembers x f.(m_out) ->
      In (x, ty) (meth_vars f) ->
      In (x, ty) f.(m_out).
  Proof.
    intros * E ?.
    pose proof (m_nodupvars f) as Nodup.
    apply InMembers_In in E as (ty' &?).
    assert (In (x, ty') (meth_vars f))
      by (now apply in_or_app; right; apply in_or_app; right).
    now app_NoDupMembers_det.
  Qed.

  Lemma m_good_out:
    forall m x,
      In x m.(m_out) ->
      AtomOrGensym (PSP.of_list gensym_prefs) (fst x).
  Proof.
    intros.
    pose proof (m_good m) as (G&_).
    eapply Forall_forall; eauto.
    apply in_map, in_app; right; apply in_app; now right.
  Qed.

  Lemma m_good_in:
    forall m x,
      In x m.(m_in) ->
      AtomOrGensym (PSP.of_list gensym_prefs) (fst x).
  Proof.
    intros.
    pose proof (m_good m) as (G&_).
    eapply Forall_forall; eauto.
    apply in_map, in_app; now left.
  Qed.

  Lemma m_good_vars:
    forall m x,
      In x m.(m_vars) ->
      AtomOrGensym (PSP.of_list gensym_prefs) (fst x).
  Proof.
    intros.
    pose proof (m_good m) as (G&_).
    eapply Forall_forall; eauto.
    apply in_map, in_app; right; apply in_app; now left.
  Qed.

  Lemma m_AtomOrGensym :
    forall x m,
      InMembers x (meth_vars m) ->
      AtomOrGensym (PSP.of_list gensym_prefs) x.
  Proof.
    intros * Hinm.
    pose proof m.(m_good) as (Good&_).
    eapply fst_InMembers in Hinm.
    eapply Forall_forall in Good; eauto.
  Qed.

  Record class : Type :=
    mk_class {
        c_name    : ident;
        c_mems    : list (ident * type);
        c_objs    : list (ident * ident);   (* (instance, class) *)
        c_methods : list method;

        c_nodup   : NoDup (map fst c_mems ++ map fst c_objs);
        c_nodupm  : NoDup (map m_name c_methods);
        c_good    : Forall (AtomOrGensym (PSP.of_list gensym_prefs)) (map fst c_objs) /\ atom c_name
      }.

  Global Instance system_unit: ProgramUnit class :=
    { name := c_name; }.

  Global Instance system_state_unit: ProgramStateUnit class type :=
    { state_variables := c_mems;
      instance_variables := c_objs }.

  Lemma c_nodupmems:
    forall c, NoDupMembers (c_mems c).
  Proof.
    intro.
    pose proof (c_nodup c) as Nodup.
    apply NoDup_app_weaken in Nodup.
    now rewrite fst_NoDupMembers.
  Qed.

  Lemma c_nodupobjs:
    forall c, NoDupMembers (c_objs c).
  Proof.
    intro.
    pose proof (c_nodup c) as Nodup.
    rewrite Permutation.Permutation_app_comm in Nodup.
    apply NoDup_app_weaken in Nodup.
    now rewrite fst_NoDupMembers.
  Qed.

  Record program : Type :=
    Program {
        enums : list (ident * nat);
        classes : list class;
      }.

  Global Program Instance program_program: CommonProgram.Program class program :=
    { units := classes;
      update := fun p => Program p.(enums) }.

  Global Program Instance program_program_without_units : TransformProgramWithoutUnits program program :=
    { transform_program_without_units := fun p => Program p.(enums) [] }.

  Fixpoint find_method (f: ident) (ms: list method) : option method :=
    match ms with
    | [] => None
    | m :: ms' => if ident_eqb m.(m_name) f
                 then Some m else find_method f ms'
    end.

  Definition find_class : ident -> program -> option (class * program) :=
    find_unit.

  Definition Forall_methods P p :=
    Forall (fun c => Forall P c.(c_methods)) p.(classes).

  (** Properties of method lookups *)

  Remark find_method_In:
    forall fid ms f,
      find_method fid ms = Some f ->
      In f ms.
  Proof.
    intros * Hfind.
    induction ms; inversion Hfind as [H].
    destruct (ident_eqb (m_name a) fid) eqn: E.
    - inversion H; subst.
      apply in_eq.
    - auto using in_cons.
  Qed.

  Remark find_method_name:
    forall fid fs f,
      find_method fid fs = Some f ->
      f.(m_name) = fid.
  Proof.
    intros * Hfind.
    induction fs; inversion Hfind as [H].
    destruct (ident_eqb (m_name a) fid) eqn: E.
    - inversion H; subst.
      now apply ident_eqb_eq.
    - now apply IHfs.
  Qed.

  Lemma find_method_map:
    forall f,
      (forall m, (f m).(m_name) = m.(m_name)) ->
      forall n ms,
        find_method n (map f ms) = option_map f (find_method n ms).
  Proof.
    intros f Hfname.
    induction ms as [|m ms IH]; auto. simpl.
    destruct (ident_eqb (f m).(m_name) n) eqn:Heq;
      rewrite Hfname in Heq; rewrite Heq; auto.
  Qed.

  (** Properties of class lookups *)

  (* Lemma find_class_enums: *)
  (*   forall p c cl p', *)
  (*     find_class c p = Some (cl, p') -> *)
  (*     p'.(enums) = p.(enums). *)
  (* Proof. *)
  (*   intros [? p]; induction p; try now inversion 1. *)
  (*   unfold find_class; simpl; intros * Find. *)
  (*   destruct (ident_eqb (c_name a) c); eauto. *)
  (*   inv Find; auto. *)
  (* Qed. *)
 
  (* Lemma find_class_none: *)
  (*   forall clsnm cls prog enums, *)
  (*     find_class clsnm (Program enums (cls::prog)) = None *)
  (*     <-> (cls.(c_name) <> clsnm /\ find_class clsnm (Program enums prog) = None). *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold find_class; simpl; destruct (ident_eqb (c_name cls) clsnm) eqn: E. *)
  (*   - split; intro HH; try discriminate. *)
  (*     destruct HH. *)
  (*     apply ident_eqb_eq in E; contradiction. *)
  (*   - apply ident_eqb_neq in E; split; intro HH; tauto. *)
  (* Qed. *)

  (* Remark find_class_app: *)
  (*   forall id p c p', *)
  (*     find_class id p = Some (c, p') -> *)
  (*     exists cls'', *)
  (*       p.(classes) = cls'' ++ c :: p'.(classes) *)
  (*       /\ find_class id (Program p.(enums) cls'') = None. *)
  (* Proof. *)
  (*   intros ? [? cls] ?? Hfind. *)
  (*   induction cls; try now inversion Hfind. *)
  (*   unfold find_class in Hfind; simpl in Hfind. *)
  (*   destruct (ident_eqb (c_name a) id) eqn: E. *)
  (*   - inv Hfind. *)
  (*     exists nil; auto. *)
  (*   - specialize (IHcls Hfind). *)
  (*     destruct IHcls as (cls'' & Hcls'' & Hnone); simpl in *. *)
  (*     rewrite Hcls''. *)
  (*     exists (a :: cls''); split; auto. *)
  (*     unfold find_class; simpl; rewrite E; auto. *)
  (* Qed. *)

  Remark find_class_name:
    forall id p c p',
      find_class id p = Some (c, p') ->
      c.(c_name) = id.
  Proof.
    intros * Find; apply find_unit_In in Find as []; auto.
  Qed.

  (* Remark find_class_In: *)
  (*   forall id p c p', *)
  (*     find_class id p = Some (c, p') -> *)
  (*     In c p.(classes). *)
  (* Proof. *)
  (*   intros ? [? cls] ?? Hfind. *)
  (*   induction cls; try now inversion Hfind. *)
  (*   unfold find_class in Hfind; simpl in Hfind. *)
  (*   destruct (ident_eqb (c_name a) id) eqn: E. *)
  (*   - inv Hfind. *)
  (*     apply in_eq. *)
  (*   - apply in_cons; auto. *)
  (* Qed. *)

  (* Remark In_find_class: *)
  (*   forall p c, *)
  (*     NoDup (map c_name p.(classes)) -> *)
  (*     In c p.(classes) -> *)
  (*     exists p', find_class c.(c_name) p = Some (c, p'). *)
  (* Proof. *)
  (*   intros [? cls] ? Nodup Hin; simpl in *. *)
  (*   induction cls; try contradiction. *)
  (*   simpl in Nodup; inversion_clear Nodup as [|?? Hnin]. *)
  (*   unfold find_class; simpl. *)
  (*   destruct (ident_eqb (c_name a) (c_name c)) eqn: E. *)
  (*   - inv Hin; eauto. *)
  (*     exfalso; apply Hnin. *)
  (*     apply ident_eqb_eq in E; rewrite E. *)
  (*     now apply in_map. *)
  (*   - inv Hin. *)
  (*     + rewrite ident_eqb_refl in E; discriminate. *)
  (*     + edestruct IHcls; auto. *)
  (* Qed. *)

  (* Lemma find_class_app': *)
  (*   forall n xs ys enums, *)
  (*     find_class n (Program enums (xs ++ ys)) = *)
  (*     match find_class n (Program enums xs) with *)
  (*     | None => find_class n (Program enums ys) *)
  (*     | Some (c, prog) => Some (c, Program enums (prog.(classes) ++ ys)) *)
  (*     end. *)
  (* Proof. *)
  (*   induction xs as [|c xs IH]; simpl; auto. *)
  (*   intro ys. *)
  (*   unfold find_class; simpl. *)
  (*   destruct (ident_eqb c.(c_name) n); auto. *)
  (*   apply IH. *)
  (* Qed. *)

  (* Lemma not_In_find_class: *)
  (*   forall n cls enums, *)
  (*     ~In n (map c_name cls) -> *)
  (*     find_class n (Program enums cls) = None. *)
  (* Proof. *)
  (*   induction cls as [|c cls IH]; auto. *)
  (*   simpl; intros * Hnin. *)
  (*   apply Decidable.not_or in Hnin. *)
  (*   destruct Hnin as (Hnin1 & Hnin2). *)
  (*   unfold find_class; simpl. *)
  (*   apply ident_eqb_neq in Hnin1. *)
  (*   rewrite Hnin1. *)
  (*   apply IH; auto. *)
  (* Qed. *)

  (* Lemma find_class_ltsuffix: *)
  (*   forall n prog c prog', *)
  (*     find_class n prog = Some (c, prog') -> *)
  (*     ltsuffix prog'.(classes) prog.(classes). *)
  (* Proof. *)
  (*   intros ? [? prog]. *)
  (*   induction prog as [|c prog IH]. now inversion 1. *)
  (*   red; simpl. intros c' prog' Hfind. *)
  (*   unfold find_class in Hfind; simpl in Hfind. *)
  (*   destruct (ident_eqb c.(c_name) n). *)
  (*   - inv Hfind. *)
  (*     exists [c']. simpl; split; auto; discriminate. *)
  (*   - destruct (IH _ _ Hfind) as (xs & Hprog & Hxs); simpl in Hprog; subst. *)
  (*     exists (c::xs); simpl; split; auto; discriminate. *)
  (* Qed. *)

  (* Lemma find_class_ltsuffix2: *)
  (*   forall n prog1 prog2 c1 c2 prog1' prog2', *)
  (*     find_class n prog1 = Some (c1, prog1') -> *)
  (*     find_class n prog2 = Some (c2, prog2') -> *)
  (*     ltsuffix2 (prog1'.(classes), prog2'.(classes)) (prog1.(classes), prog2.(classes)). *)
  (* Proof. *)
  (*   split; simpl; eauto using find_class_ltsuffix. *)
  (* Qed. *)

  Lemma Forall_methods_find:
    forall prog P cid c prog' fid f,
      Forall_methods P prog ->
      find_class cid prog = Some (c, prog') ->
      find_method fid c.(c_methods) = Some f ->
      P f.
  Proof.
    unfold Forall_methods; intros * Spec Findc Findf.
    apply find_unit_In in Findc as [].
    apply find_method_In in Findf.
    do 2 eapply Forall_forall in Spec; eauto.
  Qed.

  (** Syntactic predicates *)

  Inductive Is_free_in_exp : ident -> exp -> Prop :=
  | FreeVar: forall i ty,
      Is_free_in_exp i (Var i ty)
  | FreeState: forall i ty,
      Is_free_in_exp i (State i ty)
  | FreeUnop: forall i op e ty,
      Is_free_in_exp i e ->
      Is_free_in_exp i (Unop op e ty)
  | FreeBinop: forall i op e1 e2 ty,
      Is_free_in_exp i e1 \/ Is_free_in_exp i e2 ->
      Is_free_in_exp i (Binop op e1 e2 ty)
  | FreeValid: forall i t,
      Is_free_in_exp i (Valid i t).

  Lemma not_free_aux1 : forall i op e ty,
      ~Is_free_in_exp i (Unop op e ty) ->
      ~Is_free_in_exp i e.
  Proof.
    auto using Is_free_in_exp.
  Qed.

  Lemma not_free_aux2 : forall i op e1 e2 ty,
      ~Is_free_in_exp i (Binop op e1 e2 ty) ->
      ~Is_free_in_exp i e1 /\ ~Is_free_in_exp i e2.
  Proof.
    intros i op e1 e2 ty Hfree; split; intro H; apply Hfree;
      constructor; [now left | now right].
  Qed.

  Ltac not_free :=
    lazymatch goal with
    | H : ~Is_free_in_exp ?x (Var ?i ?ty) |- _ =>
        let HH := fresh in
        assert (HH : i <> x) by (intro; subst; apply H; constructor);
        clear H; rename HH into H
    | H : ~Is_free_in_exp ?x (State ?i ?ty) |- _ =>
        let HH := fresh in
        assert (HH : i <> x) by (intro; subst; apply H; constructor);
        clear H; rename HH into H
    | H : ~Is_free_in_exp ?x (Valid ?i ?ty) |- _ =>
        let HH := fresh in
        assert (HH : i <> x) by (intro; subst; apply H; constructor);
        clear H; rename HH into H
    | H : ~Is_free_in_exp ?x (Unop ?op ?e ?ty) |- _ =>
        apply not_free_aux1 in H
    | H : ~Is_free_in_exp ?x (Binop ?op ?e1 ?e2 ?ty) |- _ =>
        destruct (not_free_aux2 x op e1 e2 ty H)
    end.

  (** Misc. properties *)

  Lemma exp_dec : forall e1 e2 : exp, {e1 = e2} + {e1 <> e2}.
  Proof.
    repeat decide equality;
      try apply equiv_dec.
  Qed.

  Global Instance: EqDec exp eq := { equiv_dec := exp_dec }.

  Definition rev_prog (p: program) : program :=
    Program p.(enums) (rev_tr p.(classes)).
(*
  (** Simple Static Analysis of Obc statements *)

  Definition naked_var (e: exp) : option ident :=
    match e with
    | Var x _ => Some x
    | _ => None
    end.

  Inductive Is_naked_arg_in (x: ident) : stmt -> Prop :=
  | NACall: forall xs c i m es,
        Exists (fun e=> naked_var e = Some x) es ->
        Is_naked_arg_in x (Call xs c i m es)
  | NAIfte1: forall e s1 s2,
        Is_naked_arg_in x s1 ->
        Is_naked_arg_in x (Ifte e s1 s2)
  | NAIfte2: forall e s1 s2,
        Is_naked_arg_in x s2 ->
        Is_naked_arg_in x (Ifte e s1 s2)
  | NAComp1: forall s1 s2,
        Is_naked_arg_in x s1 ->
        Is_naked_arg_in x (Comp s1 s2)
  | NAComp2: forall s1 s2,
        Is_naked_arg_in x s2 ->
        Is_naked_arg_in x (Comp s1 s2).

  Inductive Must_write_in (x: ident) : stmt -> Prop :=
  | MWIAssign: forall e,
      Must_write_in x (Assign x e)
  | MWIAssignSg: forall e,
      Must_write_in x (AssignSt x e)
  | MWIIfte: forall e s1 s2,
      Must_write_in x s1 ->
      Must_write_in x s2 ->
      Must_write_in x (Ifte e s1 s2)
  | MWIComp1: forall s1 s2,
      Must_write_in x s1 ->
      Must_write_in x (Comp s1 s2)
  | MWIComp2: forall s1 s2,
      Must_write_in x s2 ->
      Must_write_in x (Comp s1 s2)
  | MWICall: forall xs cl o m es,
      In x xs ->
      Must_write_in x (Call xs cl o m es).

  Function analyze_obc' (na : PS.t) (mw: PS.t) (s: stmt) : PS.t * PS.t :=
    match s with
    | Assign x e => (na, PS.add x mw)
    | AssignSt x e => (na, PS.add x mw)
    | Ifte e s1 s2 =>
      let (na1, mw1) := analyze_obc' na mw s1 in
      let (na2, mw2) := analyze_obc' na1 mw s2 in
      (na2, PS.inter mw1 mw2)
    | Comp s1 s2 =>
      let (na1, mw1) := analyze_obc' na mw s1 in
      analyze_obc' na1 mw1 s2
    | Call xs cl i m es =>
      (ps_from_fo_list' naked_var es na, ps_from_list' xs mw)
    | Skip => (na, mw)
    end.

  Definition analyze_obc : stmt -> PS.t * PS.t :=
    analyze_obc' PS.empty PS.empty.

  Lemma analyze_obc'_spec_na:
    forall s na mw na' mw' x,
      analyze_obc' na mw s = (na', mw') ->
      PS.In x na' ->
      PS.In x na \/ Is_naked_arg_in x s.
  Proof.
    induction s; simpl; intros na mw na' mw' x Hao Hin.
    - inv Hao; auto.
    - inv Hao; auto.
    - destruct (analyze_obc' na mw s1) as (na1, mw1) eqn:Hao1.
      destruct (analyze_obc' na1 mw s2) as (na2, mw2) eqn:Hao2.
      inversion Hao; subst; clear Hao.
      eapply IHs2 in Hao2; eauto.
      destruct Hao2; auto using Is_naked_arg_in.
      eapply IHs1 in Hao1; eauto.
      destruct Hao1; auto using Is_naked_arg_in.
    - destruct (analyze_obc' na mw s1) as (na1, mw1) eqn:Hao1.
      eapply IHs2 in Hao; eauto.
      destruct Hao; auto using Is_naked_arg_in.
      eapply IHs1 in Hao1; eauto.
      destruct Hao1; auto using Is_naked_arg_in.
    - inv Hao. apply In_ps_from_fo_list' in Hin.
      destruct Hin as [|Hin]; auto. right.
      constructor. apply Exists_exists.
      induction l as [|e es IH]. now inversion Hin.
      inversion Hin as [Hna|Hin']; eauto with datatypes.
      apply IH in Hin' as (e' & Ha & Hb); eauto with datatypes.
    - inv Hao; auto.
  Qed.

  Lemma analyze_obc'_spec_mw:
    forall s na mw na' mw' x,
      analyze_obc' na mw s = (na', mw') ->
      PS.In x mw' ->
      PS.In x mw \/ Must_write_in x s.
  Proof.
    induction s; simpl; intros na mw na' mw' x Hao Hin.
    - inv Hao. apply PS.add_spec in Hin as [Hin|Hin]; subst;
                 auto using Must_write_in.
    - inv Hao. apply PS.add_spec in Hin as [Hin|Hin]; subst;
                 auto using Must_write_in.
    - destruct (analyze_obc' na mw s1) as (na1, mw1) eqn:Hao1.
      destruct (analyze_obc' na1 mw s2) as (na2, mw2) eqn:Hao2.
      inversion Hao; subst; clear Hao.
      apply PS.inter_spec in Hin as (Hin1 & Hin2).
      eapply IHs2 in Hao2; eauto.
      destruct Hao2; auto using Must_write_in.
      eapply IHs1 in Hao1; eauto.
      destruct Hao1; auto using Must_write_in.
    - destruct (analyze_obc' na mw s1) as (na1, mw1) eqn:Hao1.
      eapply IHs2 in Hao; eauto.
      destruct Hao; auto using Must_write_in.
      eapply IHs1 in Hao1; eauto.
      destruct Hao1; auto using Must_write_in.
    - inv Hao. apply In_ps_from_list' in Hin.
      destruct Hin; auto using Must_write_in.
    - inv Hao; auto.
  Qed.

  Lemma analyze_obc_spec_na:
    forall s na mw,
      analyze_obc s = (na, mw) ->
      forall x, PS.In x na -> Is_naked_arg_in x s.
  Proof.
    intros * Ha x Hin.
    eapply analyze_obc'_spec_na in Ha; eauto.
    destruct Ha as [Ha|]; auto.
    now apply not_In_empty in Ha.
  Qed.

  Lemma analyze_obc_spec_mw:
    forall s na mw,
      analyze_obc s = (na, mw) ->
      forall x, PS.In x mw -> Must_write_in x s.
  Proof.
    intros * Ha x Hin.
    eapply analyze_obc'_spec_mw in Ha; eauto.
    destruct Ha as [Ha|]; auto.
    now apply not_In_empty in Ha.
  Qed.
*)
End OBCSYNTAX.

Module ObcSyntaxFun
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op) <: OBCSYNTAX Ids Op OpAux.
  Include OBCSYNTAX Ids Op OpAux.
End ObcSyntaxFun.
