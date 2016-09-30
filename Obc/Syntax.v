Require Import Rustre.Common.
Require Import Rustre.Operators.

Open Scope bool_scope.
Require Import List.
Import List.ListNotations.
Open Scope list_scope.

(** * Obc syntax *)

(**
  Obc is a minimal object-oriented programming language.
 *)

Module Type SYNTAX
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op).

  Inductive exp : Type :=
  | Var   : ident -> type -> exp                (* variable  *)
  | State : ident -> type -> exp                (* state variable  *)
  | Const : const-> exp                         (* constant *)
  | Unop  : unop -> exp -> type -> exp          (* unary operator *)
  | Binop : binop -> exp -> exp -> type -> exp. (* binary operator *)

  Definition typeof (e: exp): type :=
    match e with
    | Const c => type_const c
    | Var _ ty
    | State _ ty
    | Unop _ _ ty
    | Binop _ _ _ ty => ty
    end.

  Inductive stmt : Type :=
  | Assign : ident -> exp -> stmt                    (* x = e *)
  | AssignSt : ident -> exp -> stmt                  (* self.x = e *)
  | Ifte : exp -> stmt -> stmt -> stmt               (* if e then s1 else s2 *)
  | Comp : stmt -> stmt -> stmt                      (* s1; s2 *)
  | Call : list ident -> ident -> ident -> ident -> list exp -> stmt
  (* y1, ..., yn := class instance method (e1, ..., em) *)
  | Skip.

  Record method : Type :=
    mk_method {
        m_name : ident;
        m_in   : list (ident * type);
        m_vars : list (ident * type);
        m_out  : list (ident * type);
        m_body : stmt;
        
        m_nodupvars : NoDupMembers (m_in ++ m_vars ++ m_out);
        m_good      : Forall NotReserved (m_in ++ m_vars ++ m_out)
      }.

  Lemma m_notreserved:
    forall x m,
      In x reserved ->
      ~InMembers x (m.(m_in) ++ m.(m_vars) ++ m.(m_out)).
  Proof.
    intros ** Hin Hinm.
    pose proof m.(m_good) as Good.
    induction (m.(m_in) ++ m.(m_vars) ++ m.(m_out)) as [|(x', t)];
      inv Hinm; inv Good.
    - contradiction.
    - now apply IHl.
  Qed.
  
  Record class : Type :=
    mk_class {
        c_name    : ident;
        c_mems    : list (ident * type);
        c_objs    : list (ident * ident);   (* (instance, class) *)
        c_methods : list method;

        c_nodup   : NoDup (map fst c_mems ++ map fst c_objs)
      }.

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
    apply NoDup_app, NoDup_app_weaken in Nodup.
    now rewrite fst_NoDupMembers.
  Qed.

  Definition program : Type := list class.
  
  Definition find_method (f: ident): list method -> option method :=
    fix find ms := match ms with
                   | [] => None
                   | m :: ms' => if ident_eqb m.(m_name) f
                                then Some m else find ms'
                   end.

  Remark find_method_In:
    forall fid ms f,
      find_method fid ms = Some f ->
      In f ms.
  Proof.
    intros ** Hfind.
    induction ms; inversion Hfind as [H].
    destruct (ident_eqb (m_name a) fid) eqn: E.
    - inversion H; subst. 
      apply in_eq. 
    - apply in_cons; auto.
  Qed.

  Remark find_method_name:
    forall fid fs f,
      find_method fid fs = Some f ->
      f.(m_name) = fid.
  Proof.
    intros ** Hfind.
    induction fs; inversion Hfind as [H].
    destruct (ident_eqb (m_name a) fid) eqn: E.
    - inversion H; subst. 
      now apply ident_eqb_eq.
    - now apply IHfs.
  Qed.

  Definition find_class (n: ident) : program -> option (class * list class) :=
    fix find p := match p with
                  | [] => None
                  | c :: p' => if ident_eqb c.(c_name) n
                              then Some (c, p') else find p'
                  end.

  Lemma find_class_none:
    forall clsnm cls prog,
      find_class clsnm (cls::prog) = None
      <-> (cls.(c_name) <> clsnm /\ find_class clsnm prog = None).
  Proof.
    intros clsnm cls prog.
    simpl; destruct (ident_eqb (c_name cls) clsnm) eqn: E.
    - split; intro HH; try discriminate.
      destruct HH.
      apply ident_eqb_eq in E; contradiction.
    - apply ident_eqb_neq in E; split; intro HH; tauto.
  Qed.

  Remark find_class_app:
    forall id cls c cls',
      find_class id cls = Some (c, cls') ->
      exists cls'',
        cls = cls'' ++ c :: cls'
        /\ find_class id cls'' = None.
  Proof.
    intros ** Hfind.
    induction cls; inversion Hfind as [H].
    destruct (ident_eqb (c_name a) id) eqn: E.
    - inversion H; subst. 
      exists nil; auto.
    - specialize (IHcls H).
      destruct IHcls as (cls'' & Hcls'' & Hnone).
      rewrite Hcls''.
      exists (a :: cls''); split; auto.
      simpl; rewrite E; auto.
  Qed.

  Remark find_class_name:
    forall id cls c cls',
      find_class id cls = Some (c, cls') ->
      c.(c_name) = id.
  Proof.
    intros ** Hfind.
    induction cls; inversion Hfind as [H].
    destruct (ident_eqb (c_name a) id) eqn: E.
    - inversion H; subst. 
      now apply ident_eqb_eq.
    - now apply IHcls.
  Qed.

  Remark find_class_In:
    forall id cls c cls',
      find_class id cls = Some (c, cls') ->
      In c cls.
  Proof.
    intros ** Hfind.
    induction cls; inversion Hfind as [H].
    destruct (ident_eqb (c_name a) id) eqn: E.
    - inversion H; subst. 
      apply in_eq. 
    - apply in_cons; auto.
  Qed.

  Inductive WelldefClasses: list class -> Prop :=
  | wdc_nil:
      WelldefClasses []
  | wdc_cons:
      forall c cls',
        WelldefClasses cls' ->
        (forall o c', In (o, c') c.(c_objs) ->
                 find_class c' cls' <> None) ->
        Forall (fun c' => c.(c_name) <> c'.(c_name)) cls' ->
        WelldefClasses (c :: cls').

  Lemma WelldefClasses_cons:
    forall c cls,
      WelldefClasses (c :: cls) ->
      WelldefClasses cls.
  Proof.
    induction cls; inversion 1; auto.
  Qed.

  Lemma WelldefClasses_app:
    forall cls cls',
      WelldefClasses (cls ++ cls') ->
      WelldefClasses cls'.
  Proof.
    induction cls; inversion 1; auto.
  Qed.

  Remark welldef_not_class_in:
    forall pre_prog post_prog o c c',
      WelldefClasses (pre_prog ++ c :: post_prog) ->
      In (o, c'.(c_name)) c.(c_objs) ->
      find_class c'.(c_name) pre_prog = None.
  Proof.
    induction pre_prog as [|k]; intros post_prog o c c' WD Hin; auto.
    rewrite <-app_comm_cons in WD.
    pose proof WD as WD'.
    apply WelldefClasses_cons in WD'.
    pose proof WD' as WD''.
    apply WelldefClasses_app in WD'.
    inversion_clear WD' as [|? ? Hwd Hclassin Hdiff]; subst.
    clear Hwd Hdiff.
    specialize (Hclassin _ _ Hin).
    apply not_None_is_Some in Hclassin;
      destruct Hclassin as ((k', prog') & Hclassin).
    pose proof (find_class_name _ _ _ _ Hclassin) as Eq.
    apply find_class_In in Hclassin.
    inversion_clear WD as [|? ? Hwd Hobjs Hdiff]; subst.
    clear Hwd Hobjs.
    apply Forall_app in Hdiff; destruct Hdiff as [Hdiff' Hdiff].
    clear Hdiff'.
    inversion_clear Hdiff as [|? ? Hkc Hdiff'].
    clear Hkc.
    simpl.
    destruct (ident_eqb (c_name k) (c_name c')) eqn: Heq.
    - eapply In_Forall in Hdiff'; eauto.
      apply ident_eqb_eq in Heq.
      rewrite <-Eq in Heq; contradiction.
    - eapply IHpre_prog; eauto.
  Qed.

  Remark welldef_not_same_name:
    forall pre_prog post_prog o c c',
      WelldefClasses (pre_prog ++ c :: post_prog) ->
      In (o, c'.(c_name)) c.(c_objs) ->
      c'.(c_name) <> c.(c_name).
  Proof.
    induction pre_prog as [|k]; intros post_prog o c c' WD Hin.
    - simpl in WD; inversion WD as [|? ? WD' Find Forall]; subst.
      specialize (Find _ _ Hin).
      apply not_None_is_Some in Find.
      destruct Find as ((c'', prog') & Find).
      pose proof Find as Findname.
      apply find_class_name in Findname.
      apply find_class_In in Find.
      apply In_Forall with (x:=c'') in Forall; eauto.
      rewrite <-Findname; auto.
    - eapply IHpre_prog; eauto.
      rewrite <-app_comm_cons in WD.
      apply WelldefClasses_cons in WD; eauto.
  Qed.

  Inductive sub_prog: program -> program -> Prop := 
    sub_prog_intro: forall p p', 
      sub_prog p (p' ++ p). 

  Remark find_class_sub_same: 
    forall prog1 prog2 clsid cls prog', 
      find_class clsid prog2 = Some (cls, prog') -> 
      WelldefClasses prog1 -> 
      sub_prog prog2 prog1 -> 
      find_class clsid prog1 = Some (cls, prog'). 
  Proof. 
    intros ** Hfind WD Sub. 
    inversion Sub; clear Sub; subst.  
    pose proof (find_class_app _ _ _ _ Hfind) as H.
    destruct H as (prog2' & Hprog2 & Hnone).
    induction p'; simpl; auto. 
    rewrite <-List.app_comm_cons in WD. 
    assert (List.In cls (p' ++ prog2)) as Hin_cls. 
    - pose proof (find_class_In _ _ _ _ Hfind) as Hin.
      apply List.in_or_app; right; auto.  
    - inversion WD as [|? ? ? ? Hforall]; subst a.
      apply find_class_name in Hfind; subst clsid.
      apply In_Forall with (2:=Hin_cls) in Hforall.
      apply ident_eqb_neq in Hforall. 
      rewrite Hforall. 
      apply IHp'. eapply WelldefClasses_cons; eauto. 
  Qed.

  Lemma find_class_sub: 
    forall prog clsid cls prog', 
      find_class clsid prog = Some (cls, prog') -> 
      sub_prog prog' prog. 
  Proof. 
    intros ** Find. 
    apply find_class_app in Find.
    destruct Find as (? & ? & ?); subst. 
    rewrite List_shift_first. 
    constructor. 
  Qed. 

  Hint Constructors sub_prog.
  
  Lemma exp_dec : forall e1 e2 : exp, {e1 = e2} + {e1 <> e2}.
  Proof.
    decide equality;
    try apply equiv_dec.
  Qed.
  
  Instance: EqDec exp eq := { equiv_dec := exp_dec }.

  Lemma reset_not_step:
    reset <> step.
  Proof.
    pose proof (Ids.methods_nodup) as Hndup.
    unfold methods in Hndup.
    inversion_clear Hndup.
    intro Hrs. rewrite Hrs in *.
    intuition.
  Qed.

End SYNTAX.

Module SyntaxFun
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op) <: SYNTAX Ids Op OpAux.

                                             Include SYNTAX Ids Op OpAux.

End SyntaxFun.

