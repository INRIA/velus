From Coq Require Import String.
From Coq Require Import Sorting.Mergesort.

From Velus Require Import Common.CompCertLib.
From Velus Require Instantiator.

From Velus Require Import Lustre.Parser.LustreAst.
From Velus Require Import Common.
From Velus Require Import Ident.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.

Module Import Syn := Instantiator.L.Syn.

Import Interface.
Import Interface.Op.
Import Interface.OpAux.
Import Interface.Cks.
Import Instantiator.L.Typ.
Import Instantiator.L.Clo.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From compcert Require cfrontend.Cop.
From compcert Require cparser.Cabs.

From Coq Require Import Permutation.

From compcert Require Import common.Errors.

(* Elaborate an AST into a well-typed and well-clocked Lustre program. *)

(** *)
(*   Lexing and parsing gives a list of LustreAst declarations. Elaboration *)
(*   transforms them into Lustre declarations, and checks that the resulting *)
(*   program is well-typed and well-clocked. Several other well-formedness *)
(*   requirements (node invariants) are also checked. *)

(*   The type and clock checking is done during elaboration for two reasons: *)

(*   - Source file location information is needed for error messages but is *)
(*     not present in the Lustre AST. *)

(*   - The Lustre AST requires type and clock annotations. *)

(*   Types and clocks are inferred simultaneously, and checked separately *)
(*   Simultaneous inferrence is more efficient, and separate checking simplifies *)
(*   the proofs *)

(*   Variable declarations within nodes are elaborated to produce a map from *)
(*   each identifier to its declared type and clock. A PositiveMap is used for *)
(*   efficiency during checking, but the declarations are maintained in lists *)
(*   as their order is significant. The related proofs use permutations and *)
(*   rewriting to switch between the two representations. The declaration map *)
(*   is then used as an environment for checking and annotating equations and *)
(*   expressions. *)

(*   The elaboration of variable declarations is performed by [elab_var_decls]. *)
(*   Multiple passes may be required for a list of declarations because clocks *)
(*   may be dependent on other declared variables. For example, *)
(* << *)
(*     a : bool; *)
(*     b : bool when c; *)
(*     c : bool when a; *)
(* >> *)
(*   The function must detect and reject cyclic definitions. For example, *)
(* << *)
(*     a : bool; *)
(*     b : bool when c; *)
(*     c : bool when b; *)
(* >> *)
(*   We pass the original list of declarations as a `fuel' argument to *)
(*   convince Coq that the function terminates. It would be possible to detect *)
(*   cyclic definitions sooner (the pass completes without treating any *)
(*   definitions), but we do not bother since this is an abnormal case. *)

(*   While the worst-case complexity of this function is not great (O(n^2)), *)
(*   you have to work pretty hard to hit (`concertina'-ed inter-dependent *)
(*   declarations), and the typical case (declarations in order of their *)
(*   dependencies) is linear. *)

(*   The [elab_var_decls] function builds the map in three cumulative steps: *)
(*   first inputs, then outputs, then locals. This is done to ensure that input *)
(*   clocks are only dependent on other inputs and that output clocks are only *)
(*   dependent on inputs or other outputs. *)

Parameter elab_const_int : Cabs.loc -> string -> constant.
Parameter elab_const_float : Cabs.floatInfo -> constant.
Parameter elab_const_char : Cabs.loc -> bool -> list char_code -> constant.

(* CompCert: lib/Camlcoq.ml: camlstring_of_coqstring and coqstring_of_camlstring *)
(*    using Require ExtrOCamlString in the extraction file to extract Coq *)
(*    strings as an OCaml "char list". Then use the Ident.pos_of_string *)
(*    function. *)
(*    TODO: In the long run, we should try to use OCaml strings everywhere. *)
Parameter string_of_astloc : astloc -> String.string.
Parameter cabsloc_of_astloc : astloc -> Cabs.loc.
Parameter cabs_floatinfo : floatInfo -> Cabs.floatInfo.

Local Ltac NamedDestructCases :=
  repeat progress
         match goal with
         | H:match ?e with _ => _ end = OK _ |- _ =>
           let Heq := fresh "Heq" in
           destruct e eqn:Heq; try discriminate
         | H:OK _ = OK _ |- _ => injection H; clear H; intro; subst
         end.

Definition msg_of_types (ty ty': type) : errmsg :=
  MSG "expected '" :: MSG (string_of_type ty)
      :: MSG "' but got '" :: MSG (string_of_type ty') :: msg "'".

Definition msg_of_enum_type (ty: type) : errmsg :=
  MSG "enumerated type expected but got '" :: MSG (string_of_type ty) :: msg "'".

Definition msg_of_primitive_type (ty: type) : errmsg :=
  MSG "primitive type expected but got '" :: MSG (string_of_type ty) :: msg "'".

(* Used for unification *)
Inductive sident :=
| Vnm : ident -> sident
| Vidx : ident -> sident.

Inductive sclock :=
| Sbase : sclock
| Svar : ident -> sclock
| Son : sclock -> sident -> (type * enumtag) -> sclock.

Definition sident_eq (id1 id2 : sident) : bool :=
  match id1, id2 with
  | Vnm id1, Vnm id2
  | Vidx id1, Vidx id2 => ident_eqb id1 id2
  | _, _ => false
  end.

Lemma sident_eq_spec:
  forall id1 id2,
    sident_eq id1 id2 = true <-> id1 = id2.
Proof.
  intros *; split; intro HH; auto;
    destruct id1, id2; simpl in *;
      try now inversion HH.
  1,2,3,4:rewrite ident_eqb_eq in *; congruence.
Qed.

Instance sident_EqDec : EqDec sident eq.
Proof.
  intros id1 id2. compute.
  pose proof (sident_eq_spec id1 id2) as Heq.
  destruct (sident_eq id1 id2); [left|right].
  now apply Heq.
  intro HH. apply Heq in HH.
  discriminate.
Qed.

Lemma sident_eqb_eq :
  forall (x y: sident), x ==b y = true <-> x = y.
Proof.
  setoid_rewrite equiv_decb_equiv; reflexivity.
Qed.

Fixpoint sclock_eq (ck1 ck2: sclock) : bool :=
  match ck1, ck2 with
  | Sbase, Sbase => true
  | Svar id1, Svar id2 => ident_eqb id1 id2
  | Son ck1' x1 b1, Son ck2' x2 b2 =>
    ((x1 ==b x2) && (b1 ==b b2)) && sclock_eq ck1' ck2'
  | _, _ => false
  end.

Lemma sclock_eq_spec:
  forall ck1 ck2,
    sclock_eq ck1 ck2 = true <-> ck1 = ck2.
Proof.
  induction ck1, ck2; split; intro HH; auto;
    try now inversion HH; simpl in *.
  - inversion HH.
    rewrite ident_eqb_eq in H0. congruence.
  - inv HH. simpl.
    apply ident_eqb_refl.
  - inversion HH as [Heq].
    apply andb_prop in Heq.
    destruct Heq as (Heq & Hc).
    apply andb_prop in Heq.
    destruct Heq as (Hi & Hb).
    apply sident_eqb_eq in Hi.
    rewrite equiv_decb_equiv in Hb.
    apply IHck1 in Hc.
    subst. rewrite Hb. reflexivity.
  - inversion HH as [Heq].
    subst. simpl.
    rewrite Bool.andb_true_iff.
    split. 2:now apply IHck1.
    rewrite Bool.andb_true_iff.
    split. now apply sident_eqb_eq.
    now apply equiv_decb_equiv.
Qed.

Instance sclock_EqDec : EqDec sclock eq.
Proof.
  intros ck1 ck2. compute.
  pose proof (sclock_eq_spec ck1 ck2) as Heq.
  destruct (sclock_eq ck1 ck2); [left|right].
  now apply Heq.
  intro HH. apply Heq in HH.
  discriminate.
Qed.

Lemma sclock_eqb_eq :
  forall (x y: sclock), x ==b y = true <-> x = y.
Proof.
  setoid_rewrite equiv_decb_equiv; reflexivity.
Qed.

Fixpoint sclk (ck : clock) : sclock :=
  match ck with
  | Cbase => Sbase
  | Con ck' x b => Son (sclk ck') (Vnm x) b
  end.

Fixpoint sclk' (ck : sclock) : clock :=
  match ck with
  | Sbase | Svar _ => Cbase
  | Son ck' (Vnm x) b
  | Son ck' (Vidx x) b => Con (sclk' ck') x b
  end.

Definition nsclock := (sclock * option sident)%type.
Definition stripname (nck : nsclock) := (fst nck).

Definition ann : Type := (type * nsclock)%type.
Definition lann : Type := (list type * nsclock)%type.

(** elaboration exp : annotations use sclock *)
Inductive eexp : Type :=
(* constant have a sclock in order to later add whens *)
| Econst : cconst -> sclock -> eexp
| Eenum : enumtag -> type -> sclock -> eexp
| Evar   : ident -> ann -> eexp
| Eunop  : unop -> eexp -> ann -> eexp
| Ebinop : binop -> eexp -> eexp -> ann -> eexp

| Efby   : list eexp -> list eexp -> list eexp -> list ann -> eexp
| Earrow : list eexp -> list eexp -> list eexp -> list ann -> eexp

| Ewhen  : list eexp -> ident -> enumtag -> lann -> eexp
| Emerge : (ident * type) -> list (list eexp) -> lann -> eexp
| Ecase  : eexp -> list (option (list eexp)) -> list eexp -> lann -> eexp

| Eapp   : ident -> list eexp -> list eexp -> list ann -> eexp.

Section eexp_ind2.

  Variable P : eexp -> Prop.

  Hypothesis EconstCase:
    forall c ck,
      P (Econst c ck).

  Hypothesis EenumCase:
    forall k ty ck,
      P (Eenum k ty ck).

  Hypothesis EvarCase:
    forall x a,
      P (Evar x a).

  Hypothesis EunopCase:
    forall op e a,
      P e ->
      P (Eunop op e a).

  Hypothesis EbinopCase:
    forall op e1 e2 a,
      P e1 ->
      P e2 ->
      P (Ebinop op e1 e2 a).

  Hypothesis EfbyCase:
    forall e0s es er a,
      Forall P e0s ->
      Forall P es ->
      Forall P er ->
      P (Efby e0s es er a).

  Hypothesis EarrowCase:
    forall e0s es er a,
      Forall P e0s ->
      Forall P es ->
      Forall P er ->
      P (Earrow e0s es er a).

  Hypothesis EwhenCase:
    forall es x b a,
      Forall P es ->
      P (Ewhen es x b a).

  Hypothesis EmergeCase:
    forall x es a,
      Forall (Forall P) es ->
      P (Emerge x es a).

  Hypothesis EcaseCase:
    forall e es d a,
      P e ->
      Forall (LiftO True (Forall P)) es ->
      Forall P d ->
      P (Ecase e es d a).

  Hypothesis EappCase:
    forall f es er a,
      Forall P es ->
      Forall P er ->
      P (Eapp f es er a).

  Local Ltac SolveForall :=
    match goal with
    | |- Forall ?P ?l => induction l; auto
    | _ => idtac
    end.

  Fixpoint eexp_ind2 (e: eexp) : P e.
  Proof.
    destruct e.
    - apply EconstCase; auto.
    - apply EenumCase; auto.
    - apply EvarCase; auto.
    - apply EunopCase; auto.
    - apply EbinopCase; auto.
    - apply EfbyCase; SolveForall; auto.
    - apply EarrowCase; SolveForall; auto.
    - apply EwhenCase; SolveForall.
    - apply EmergeCase; SolveForall.
      constructor; auto. SolveForall.
    - apply EcaseCase; SolveForall; auto.
      constructor; auto. destruct a; simpl; auto.
      SolveForall.
    - apply EappCase; SolveForall; auto.
  Qed.

End eexp_ind2.

Inductive const_annot :=
| ConstA: cconst -> const_annot
| EnumA: enumtag -> (ident * nat) -> const_annot.

Definition msg_of_sident (id : sident) : errmsg :=
  match id with
  | Vnm x => CTX x :: nil
  | Vidx x => MSG "?c" :: POS x :: nil
  end.

Fixpoint msg_ident_list (xs: list ident) :=
  match xs with
  | [] => []
  | [x] => [CTX x]
  | x::xs => CTX x :: MSG ", " :: msg_ident_list xs
  end.

Definition init_type (ty : type) (ck : sclock) :=
  match ty with
  | Tprimitive cty => Econst (Op.init_ctype cty) ck
  | Tenum _ => Eenum 0 ty ck
  end.

(** A completely ad-hoc monad, used only for elaboration :) *)
Section ElabMonad.
  Context {A : Type}.

  Definition elab_state : Type := (ident * Env.t sclock * Env.t sident).
  Definition Elab A := elab_state -> res (A * elab_state).

  Definition init_state : elab_state := (xH, Env.empty _, Env.empty _).

  Definition ret (x : A) : Elab A := fun st => OK (x, st).

  Definition bind {B : Type} (x : Elab A) (f : A -> Elab B) : Elab B :=
    fun st => match (x st) with
           | OK (a, st') => f a st'
           | Error err => Error err
           end.

  Definition bind2 {A1 A2 B : Type} (x : Elab (A1 * A2)) (f : A1 -> A2 -> Elab B) : Elab B :=
    fun st => match (x st) with
           | OK ((a1, a2), st') => f a1 a2 st'
           | Error err => Error err
           end.

  Definition error (msg : errmsg) : Elab A :=
    fun st => Error msg.

  Definition err_loc' (loc: astloc) (m: errmsg) :=
    MSG (string_of_astloc loc) :: MSG ":" :: m.

  Definition err_loc (loc: astloc) (m: errmsg) : Elab A :=
    error (err_loc' loc m).

  Definition fresh_ident : Elab ident :=
    fun '(n, sub1, sub2) =>
      let id := Ids.gensym Ids.elab n in
      OK (id, (Pos.succ n, sub1, sub2)).

  (** Substitution functions *)

  (** Occur check *)
  Fixpoint occurs id sck :=
    match sck with
    | Sbase => false
    | Svar x => x ==b id
    | Son sck _ _ => occurs id sck
    end.

  Definition subst_in_sident (id : ident) (sid1 sid2 : sident) :=
    match sid2 with
    | Vnm _ => sid2
    | Vidx x => if x ==b id then sid1 else sid2
    end.

  (** Substitute `ck` to `id` in `sck` *)
  Fixpoint subst_in_sclock (id : ident) (ck sck : sclock) :=
    match sck with
    | Sbase => Sbase
    | Svar x => if x ==b id then ck else sck
    | Son sck ckid b => Son (subst_in_sclock id ck sck) ckid b
    end.

  (** Substitute `sid` to `id` in `sck` *)
  Fixpoint subst_ident_in_sclock id sid sck :=
    match sck with
    | Sbase | Svar _ => sck
    | Son sck x b =>
      Son (subst_ident_in_sclock id sid sck) (subst_in_sident id sid x) b
    end.

  Definition subst_clock (id : ident) : Elab (option sclock) :=
    fun st => let '(_, sub1, _) := st in OK (Env.find id sub1, st).

  Definition subst_ident (id : ident) : Elab (option sident) :=
    fun st => let '(_, _, sub2) := st in OK (Env.find id sub2, st).

  Lemma bind_inv {B} : forall (x : Elab A) (f : A -> Elab B) res st,
      (bind x f) st = OK res ->
      exists y st'',
        x st = OK (y, st'') /\ f y st'' = OK res.
  Proof.
    intros * Hbind.
    unfold bind in Hbind.
    destruct (x st) as [[y st'']|]; eauto. inv Hbind.
  Qed.

  Lemma bind2_inv {A1 A2 B} : forall (x : Elab (A1 * A2)) (f : A1 -> A2 -> Elab B) res st,
      (bind2 x f) st = OK res ->
      exists y1 y2 st'',
        x st = OK ((y1, y2), st'') /\ f y1 y2 st'' = OK res.
  Proof.
    intros * Hbind.
    unfold bind2 in Hbind.
    destruct (x st) as [[[y1 y2] st'']|]; eauto. inv Hbind.
  Qed.
End ElabMonad.

Module ElabNotations.

  Notation "'do' X <- A ; B" :=
    (bind A (fun X => B))
      (at level 200, X ident, A at level 100, B at level 200).

  Notation "'do' ( X , Y ) <- A ; B" :=
    (bind2 A (fun X Y => B))
      (at level 200, X ident, Y ident, A at level 100, B at level 200).

End ElabNotations.

Import ElabNotations.

Section mmap.
  Context {A B : Type}.
  Variable (f : A -> Elab B).

  Fixpoint mmap (l: list A) {struct l} : Elab (list B) :=
    match l with
    | nil => ret nil
    | hd :: tl => do hd' <- f hd; do tl' <- mmap tl; ret (hd' :: tl')
    end.
End mmap.

Section mmap2.
  Context {A B1 B2 : Type}.
  Variable (f : A -> Elab (B1 * B2)).

  Fixpoint mmap2 (l: list A) {struct l} : Elab (list B1 * list B2) :=
    match l with
    | nil => ret (nil, nil)
    | hd :: tl => do (hd1, hd2) <- f hd;
                 do (tl1, tl2) <- mmap2 tl;
                 ret ((hd1::tl1), (hd2::tl2))
    end.
End mmap2.

Section ElabSclock.

  Variable tenv : Env.t (list ident).

  Definition msg_of_enumtag (t: ident) (c: enumtag) : errcode :=
    match Env.find t tenv with
    | Some cs =>
      match nth_error cs c with
      | Some c => CTX c
      | None => MSG ""
      end
    | None => MSG ""
    end.

  Fixpoint msg_of_sclock (ck: sclock) : errmsg :=
    match ck with
    | Sbase          => msg "."
    | Svar x         => CTX x :: nil
    | Son ck id (Tenum (t, _), c) =>
      msg_of_sclock ck ++ MSG " on " :: msg_of_enumtag t c
                    :: MSG "(" :: msg_of_sident id ++ MSG ")" :: nil
    | _ => msg ""
    end.

  (** Add a new association to the substitution *)
  Definition add_to_clock_subst (id : ident) (sck : sclock) : Elab unit :=
    fun '(nid, sub1, sub2) =>
      let sub1' := Env.map (subst_in_sclock id sck) sub1 in
      match Env.find id sub1' with
      | Some sck' => if sck' ==b sck then OK (tt, (nid, sub1', sub2))
                    else Error (MSG "Imcompatibility in subst : " :: msg_of_sclock sck ++ MSG " and "
                                    :: msg_of_sclock sck' ++ nil)
      | None => OK (tt, (nid, Env.add id sck sub1', sub2))
      end.

  Definition add_to_ident_subst (id : ident) (id' : sident) : Elab unit :=
    fun '(nid, sub1, sub2) =>
      let sub1 := Env.map (subst_ident_in_sclock id id') sub1 in
      let sub2' := Env.map (subst_in_sident id id') sub2 in
      match Env.find id sub2' with
      | Some id'' => if id'' ==b id' then OK (tt, (nid, sub1, sub2'))
                    else Error (MSG "Imcompatibility in subst : " :: msg_of_sident id'
                                    ++ MSG " and " :: msg_of_sident id'')
      | None => OK (tt, (nid, sub1, Env.add id id' sub2'))
      end.

  (** Apply the current substitution to an ident *)
  Definition update_sident (sid : sident) : Elab sident :=
    match sid with
    | Vnm _ => ret sid
    | Vidx x =>
      do x' <- subst_ident x;
      match x' with
      | None => ret sid
      | Some x' => ret x'
      end
    end.

  (** Apply the current substitution in a clock *)
  Fixpoint update_sclock (sck : sclock) : Elab sclock :=
    match sck with
    | Sbase => ret Sbase
    | Svar x =>
      do x' <- subst_clock x;
      match x' with
      | Some sck' => ret sck'
      | None => ret (Svar x)
      end
    | Son sck' x b =>
      do sck' <- update_sclock sck';
      do x <- update_sident x;
      ret (Son sck' x b)
    end.

  Definition update_ann (a : (type * nsclock)) : Elab (type * nsclock) :=
    let '(ty, (ck, id)) := a in
    do ck' <- update_sclock ck;
    match id with
    | None => ret (ty, (ck', None))
    | Some id =>
      do id' <- update_sident id;
      ret (ty, (ck', Some id'))
    end.

  (** Unify two sident *)
  Definition unify_sident loc (sid1 sid2 : sident) : Elab unit :=
    do sid1 <- update_sident sid1;
    do sid2 <- update_sident sid2;
    match sid1, sid2 with
    | Vnm id1, Vnm id2 =>
      if id1 ==b id2 then ret tt
      else err_loc loc (MSG "Ident unification error : " :: CTX id1 :: MSG ", " :: CTX id2 :: nil)
    | Vidx id, sid
    | sid, Vidx id => add_to_ident_subst id sid
    end.

  (** Unify two clocks *)
  Definition unify_sclock (loc : astloc) (ck1 ck2 : sclock) : Elab unit :=
    do ck1 <- update_sclock ck1;
    do ck2 <- update_sclock ck2;
    (fix aux ck1 ck2 :=
       match ck1, ck2 with
       | Sbase, Sbase => ret tt
       | Svar x, ck
       | ck, Svar x =>
         do ck <- update_sclock ck;
         add_to_clock_subst x ck
       | Son ck1 id1 (ty1, k1), Son ck2 id2 (ty2, k2) =>
         if (k1 =? k2) && (ty1 ==b ty2) then
           do _ <- aux ck1 ck2;
           unify_sident loc id1 id2
         else err_loc loc (MSG "Clock unification error : " :: msg_of_sclock ck1 ++ MSG ", " ::
                               msg_of_sclock ck2)
       | _, _ => err_loc loc (MSG "Clock unification error : " :: msg_of_sclock ck1 ++ MSG ", " ::
                                 msg_of_sclock ck2)
       end) ck1 ck2.

  Definition unify_nclock (loc : astloc) (id1 : ident)  (ck1 : sclock) (nck2 : nsclock) : Elab unit :=
    let '(ck2, id2) := nck2 in
    do _ <- unify_sclock loc ck1 ck2;
    match id2 with
    | None => ret tt
    | Some id2 =>
      unify_sident loc (Vnm id1) id2
    end.

End ElabSclock.

Module BranchesOrder <: Orders.TotalLeBool'.

  Definition t : Type := (nat * (list (eexp * astloc)))%type.

  (* The arguments are inversed to put the list in the reverse order
       expected. *)
  Definition leb (s1 s2 : t) : bool := ((fst s2) <=? (fst s1)).

  Lemma leb_total:
    forall s1 s2,
      leb s1 s2 = true \/ leb s2 s1 = true.
  Proof.
    destruct s1 as (n1 & a1), s2 as (n2 & a2).
    unfold leb; simpl.
    setoid_rewrite OrdersEx.Nat_as_OT.leb_compare.
    destruct (n1 ?= n2) eqn:Hn; auto.
    apply Nat.compare_gt_iff in Hn.
    apply Nat.compare_lt_iff in Hn.
    rewrite Hn; auto.
  Qed.

End BranchesOrder.
Module BranchesSort := Sort BranchesOrder.

Section ElabExpressions.

  (* Map variable names to their types and clocks. *)
  Variable env : Env.t (type * clock).

  (* Map type names to their constructors *)
  Variable tenv: Env.t (list ident).

  (* Map node names to input and output types and clocks. *)
  Variable nenv : Env.t (list (ident * (type * clock))
                        * list (ident * (type * clock))).

  Open Scope nat.

  Definition find_var (loc: astloc) (x: ident) : Elab (type * sclock) :=
    match Env.find x env with
    | None => err_loc loc (CTX x :: msg " is not declared.")
    | Some (ty, ck) => ret (ty, sclk ck)
    end.

  Definition assert_id_type (loc: astloc) (x: ident) (xty ty: type) : Elab unit :=
    if xty ==b ty then ret tt
    else err_loc loc (CTX x :: MSG ": " :: msg_of_types xty ty).

  Definition assert_type (loc: astloc) (x: ident) (xty ty: type) : Elab unit :=
    if xty ==b ty then ret tt
    else err_loc loc (CTX x :: MSG ": " :: msg_of_types xty ty).

  Definition assert_type' (loc: astloc) (xty ty: type) : Elab unit :=
    if xty ==b ty then ret tt
    else err_loc loc (msg_of_types xty ty).

  Definition assert_enum_type (loc: astloc) (x: ident) (xty: type) : Elab (ident * nat) :=
    match xty with
    | Tenum tn => ret tn
    | _ => err_loc loc (CTX x :: MSG ": " :: msg_of_enum_type xty)
    end.

  Definition assert_enum_type' (loc: astloc) (ty: type) : Elab (ident * nat) :=
    match ty with
    | Tenum tn => ret tn
    | _ => err_loc loc (msg_of_enum_type ty)
    end.

  Definition assert_primitive_type' (loc: astloc) (ty: type) : Elab unit :=
    match ty with
    | Tprimitive _ => ret tt
    | Tenum tn => err_loc loc (msg_of_primitive_type ty)
    end.

  Definition find_node_interface (loc: astloc) (f: ident)
    : Elab (list (ident * (type * clock)) * list (ident * (type * clock))) :=
    match Env.find f nenv with
    | None => err_loc loc (MSG "node " :: CTX f :: msg " not found.")
    | Some tcs => ret tcs
    end.

  Definition enum_to_enumtag (loc: astloc) (ty: ident) (c: ident) (cs: list ident) : option (enumtag * nat) :=
    let (t, n) := fold_left
                    (fun (acc: option enumtag * nat) c' =>
                       let (t, n) := acc in
                       let t := match t with
                                | None => if c' ==b c then Some n else None
                                | Some t => Some t
                                end
                       in (t, n + 1)) cs (None, 0)
    in match t with
       | Some t => Some (t, n)
       | None => None
       end.

  Definition elab_enum (loc: astloc) (c: ident) : Elab (enumtag * (ident * nat)) :=
    let r := Env.fold (fun ty cs r => match r with
                                   | None =>
                                     match enum_to_enumtag loc ty c cs with
                                     | None => None
                                     | Some (t, n) => Some (t, (ty, n))
                                     end
                                   | Some x => Some x
                                   end) tenv None
    in match r with
       | Some r => ret r
       | None => err_loc loc (MSG "constructor " :: CTX c :: msg " not declared.")
       end.

  Definition elab_constant (loc: astloc) (c: LustreAst.constant) : Elab const_annot :=
    match c with
    | CONST_ENUM c =>
      do (c, tn) <- elab_enum loc c;
      ret (EnumA c tn)
    | CONST_INT s       => ret (ConstA (elab_const_int (cabsloc_of_astloc loc) s))
    | CONST_FLOAT fi    => ret (ConstA (elab_const_float (cabs_floatinfo fi)))
    | CONST_CHAR wide l => ret (ConstA (elab_const_char (cabsloc_of_astloc loc) wide l))
    end.

  Definition elab_unop (op: unary_operator) : unop :=
    match op with
    | MINUS => UnaryOp Cop.Oneg
    | NOT   => UnaryOp Cop.Onotint
    | BNOT  => UnaryOp Cop.Onotbool
    end.

  Definition elab_binop (op: binary_operator) : binop :=
    match op with
    | ADD  => Cop.Oadd
    | SUB  => Cop.Osub
    | MUL  => Cop.Omul
    | DIV  => Cop.Odiv
    | MOD  => Cop.Omod
    | BAND => Cop.Oand
    | BOR  => Cop.Oor
    | LAND => Cop.Oand
    | LOR  => Cop.Oor
    | XOR  => Cop.Oxor
    | LSL  => Cop.Oshl
    | LSR  => Cop.Oshr
    | EQ   => Cop.Oeq
    | NE   => Cop.One
    | LT   => Cop.Olt
    | GT   => Cop.Ogt
    | LE   => Cop.Ole
    | GE   => Cop.Oge
    end.

  Definition find_type_unop (loc: astloc) (op: unop) (ty: type) : Elab type :=
    match type_unop op ty with
    | None => err_loc loc (msg "wrong operator argument type")
    | Some ty' => ret ty'
    end.

  Definition find_type_binop (loc: astloc) (op: binop)
             (ty1 ty2: type) : Elab type :=
    match type_binop op ty1 ty2 with
    | None => err_loc loc (msg "wrong operator argument type")
    | Some ty' => ret ty'
    end.

  Definition enum_bound (loc: astloc) (ty: ident) : Elab nat :=
    match Env.find ty tenv with
    | None => err_loc loc (MSG "enumerated type " :: CTX ty :: msg " not declared.")
    | Some cs => let n := length cs in
                if 0 <? n then ret n
                else err_loc loc (MSG "empty enumerated type " :: CTX ty :: msg " .")
    end.

  Definition elab_type (loc: astloc) (ty: LustreAst.type_name) : Elab type :=
    match ty with
    | Tint8    => ret (Tprimitive (Tint Ctypes.I8  Ctypes.Signed))
    | Tuint8   => ret (Tprimitive (Tint Ctypes.I8  Ctypes.Unsigned))
    | Tint16   => ret (Tprimitive (Tint Ctypes.I16 Ctypes.Signed))
    | Tuint16  => ret (Tprimitive (Tint Ctypes.I16 Ctypes.Unsigned))
    | Tint32   => ret (Tprimitive (Tint Ctypes.I32 Ctypes.Signed))
    | Tuint32  => ret (Tprimitive (Tint Ctypes.I32 Ctypes.Unsigned))
    | Tint64   => ret (Tprimitive (Tlong Ctypes.Signed))
    | Tuint64  => ret (Tprimitive (Tlong Ctypes.Unsigned))
    | Tfloat32 => ret (Tprimitive (Tfloat Ctypes.F32))
    | Tfloat64 => ret (Tprimitive (Tfloat Ctypes.F64))
    | Tenum_name t =>
      do n <- enum_bound loc t;
      ret (Tenum (t, n))
    end.

  Definition elab_primitive_type (loc: astloc)  (ty: LustreAst.type_name) : Elab ctype :=
    do ty <- elab_type loc ty;
    match ty with
    | Tprimitive t => ret t
    | Tenum _ => err_loc loc (msg "primitive type expected")
    end.

  Definition err_not_singleton {A} (loc: astloc) : Elab A :=
    err_loc loc (msg "singleton argument expected").

  Definition single_annot (loc: astloc) (e: eexp) : Elab (type * sclock) :=
    match e with
    | Econst c ck => ret (Tprimitive (ctype_cconst c), ck)
    | Eenum _ ty ck => ret (ty, ck)
    | Eapp _ _ _ [(ty, nck)]
    | Evar _ (ty, nck)
    | Eunop _ _ (ty, nck)
    | Ebinop _ _ _ (ty, nck)
    | Ewhen _ _ _ ([ty], nck)
    | Efby _ _ _ [(ty, nck)]
    | Earrow _ _ _ [(ty, nck)]
    | Emerge _ _ ([ty], nck)
    | Ecase _ _ _ ([ty], nck) => ret (ty, stripname nck)
    | _ => err_not_singleton loc
    end.

  Fixpoint lannot (el : eexp * astloc) : list ((type * sclock) * astloc) :=
    let (e, loc) := el in
    match e with
    | Econst c ck => [((Tprimitive (ctype_cconst c), ck), loc)]
    | Eenum _ ty ck => [((ty, ck), loc)]
    | Evar _ (ty, nck)
    | Eunop _ _ (ty, nck)
    | Ebinop _ _ _ (ty, nck) => [((ty, stripname nck), loc)]
    | Ewhen _ _ _ (tys, nck)
    | Emerge _ _ (tys, nck)
    | Ecase _ _ _ (tys, nck) =>
      let ck := stripname nck in
      map (fun ty=> ((ty, ck), loc)) tys
    | Efby _ _ _ anns
    | Earrow _ _ _ anns
    | Eapp _ _ _ anns =>
      map (fun tc => ((fst tc, stripname (snd tc)), loc)) anns
    end.

  Definition lannots (els : list (eexp * astloc))
    : list ((type * sclock) * astloc) := flat_map lannot els.

  Definition lnannot (el : eexp * astloc) : list ((type * nsclock) * astloc) :=
    let (e, loc) := el in
    match e with
    | Econst c ck => [((Tprimitive (ctype_cconst c), (ck, None)), loc)]
    | Eenum _ ty ck => [((ty, (ck, None)), loc)]
    | Evar _ (ty, nck)
    | Eunop _ _ (ty, nck)
    | Ebinop _ _ _ (ty, nck) => [((ty, nck), loc)]
    | Ewhen _ _ _ (tys, nck)
    | Emerge _ _ (tys, nck)
    | Ecase _ _ _ (tys, nck) =>
      map (fun ty=> ((ty, nck), loc)) tys
    | Efby _ _ _ anns
    | Earrow _ _ _ anns
    | Eapp _ _ _ anns => map (fun tc => (tc, loc)) anns
    end.

  Definition lannots_ty {A B} (tcl : list ((type * A) * B)) : list type :=
    map (fun x=> fst (fst x)) tcl.

  Definition lannots_ck {A B} (tcl : list ((A * sclock) * B)) : list sclock :=
    map (fun x => snd (fst x)) tcl.

  Definition lnannots (els : list (eexp * astloc))
    : list ((type * nsclock) * astloc) := flat_map lnannot els.

  Definition hd_sclock (loc: astloc) (ls: list ((type * sclock) * astloc))
                                                                 : Elab sclock :=
    match ls with
    | nil => err_loc loc (msg "empty expression list")
    | l::_ => ret (snd (fst l))
    end.

  Fixpoint unify_same_clock (lck: sclock)
           (ans : list ((type * sclock) * astloc)) : Elab unit :=
    match ans with
    | [] => ret tt
    | an::ans' =>
      let '((ty, ck), loc) := an in
      do _ <- unify_sclock tenv loc ck lck;
      unify_same_clock lck ans'
    end.

  Fixpoint unify_paired_types (gloc: astloc)
           (ants anfs: list ((type * sclock) * astloc)) : Elab unit :=
    match ants, anfs with
    | [], [] => ret tt
    | ant::ants', anf::anfs' =>
      let '((tty, tck), tloc) := ant in
      let '((fty, fck), floc) := anf in
      if tty ==b fty then unify_paired_types gloc ants' anfs'
      else err_loc gloc (MSG "expression at "
                             :: MSG (string_of_astloc tloc)
                             :: MSG " has type '" :: MSG (string_of_type tty)
                             :: MSG "' but expression at "
                             :: MSG (string_of_astloc floc)
                             :: MSG " has type '" :: MSG (string_of_type fty)
                             :: msg "'")
    | _, _ => err_loc gloc (msg "arguments are of different lengths")
    end.

  Fixpoint unify_paired_clock_types (gloc: astloc)
           (ants anfs: list ((type * nsclock) * astloc)) : Elab unit :=
    match ants, anfs with
    | [], [] => ret tt
    | ant::ants', anf::anfs' =>
      let '((tty, (tck, _)), tloc) := ant in
      let '((fty, (fck, _)), floc) := anf in
      do _ <- unify_sclock tenv tloc tck fck;
      if tty ==b fty then unify_paired_clock_types gloc ants' anfs'
      else err_loc gloc (MSG "expression at "
                             :: MSG (string_of_astloc tloc)
                             :: MSG " has type '" :: MSG (string_of_type tty)
                             :: MSG "' but expression at "
                             :: MSG (string_of_astloc floc)
                             :: MSG " has type '" :: MSG (string_of_type fty)
                             :: msg "'")
    | _, _ => err_loc gloc (msg "arguments are of different lengths")
    end.

  Definition instantiating_subst (xtc : list (ident * (type * clock))) : Elab (Env.t ident) :=
    do xs <- mmap (fun '(x, _) => do x' <- fresh_ident; ret (x, x')) xtc;
    ret (Env.from_list xs).

  Fixpoint inst_clock (loc: astloc) (base: sclock) (sub : Env.t ident) (ck: clock) : Elab sclock :=
    match ck with
    | Cbase => ret base
    | Con ck' x b =>
      do sck' <- inst_clock loc base sub ck';
      match Env.find x sub with
      | None => err_loc loc
                  (MSG "The " :: CTX x
                     :: msg " argument must be instantiated with a variable.")
      | Some ni => ret (Son sck' (Vidx ni) b)
      end
    end.

  Definition inst_annot (loc: astloc) (base: sclock) (sub : Env.t ident)
             (anon_cons : ident -> sident)
             (xtc: ident * (type * clock)) : Elab ann :=
    let '(x, (ty, ck)) := xtc in
    do sck <- inst_clock loc base sub ck;
    match Env.find x sub with
    | None => ret (ty, (sck, None))
    | Some x => ret (ty, (sck, Some (anon_cons x)))
    end.

  Definition unify_nclock' (loc : astloc) (nck1 : nsclock) (nck2 : nsclock) : Elab unit :=
    let '(ck1, id1) := nck1 in let '(ck2, id2) := nck2 in
    do _ <- unify_sclock tenv loc ck1 ck2;
    match id1, id2 with
    | Some id1, Some id2 =>
      unify_sident loc id1 id2
    | _, _ => ret tt
    end.

  Fixpoint unify_inputs (gloc: astloc)
                        (iface: list (type * nsclock))
                        (args: list ((type * nsclock) * astloc)) : Elab unit :=
    match iface, args with
    | nil, nil => ret tt
    | nil, _ => err_loc gloc (msg "too many arguments")
    | _, nil => err_loc gloc (msg "not enough arguments")

    | (ty, nck)::iface', ((ty', nck'), loc)::args' =>
      do _ <- assert_type' loc ty' ty;
      do _ <- unify_nclock' loc nck' nck;
      unify_inputs gloc iface' args'
    end.

  Definition discardname (ann : (type * nsclock * astloc)) : (type * nsclock) :=
    let '(ty, (ck, id), _) := ann in (ty, (ck, None)).

  Definition assert_reset_type '(er, loc) :=
    do (erty, _) <- single_annot loc er;
    assert_type' loc erty bool_type.

  (* Elaborate an expression. *)

  Definition check_duplicates (loc: astloc) (cs: list enumtag) : Elab unit :=
    if length (nodup Nat.eq_dec cs) ==b length cs
    then ret tt
    else err_loc loc (msg "duplicate branch").

  Definition check_exhaustivity (loc: astloc) (n: nat) (cs: list enumtag) : Elab unit :=
    if length cs ==b n
    then ret tt
    else err_loc loc (msg "non-exhaustive pattern matching").

  Definition hd_branch {A : Type} loc (xs : list A) : Elab A :=
      match xs with
      | hd::_ => ret hd
      | [] => err_loc loc (msg "no branch")
      end.

  Fixpoint complete_branches k (brs : list (nat * list (eexp * astloc))) : list (option (list eexp)) :=
    match k with
    | 0 => map (fun '(_, e) => Some (map fst e)) brs
    | (S k) =>
      match brs with
      | [] => None::(complete_branches k brs)
      | (tag, es)::tl => if (tag =? k) then (Some (map fst es))::(complete_branches k tl)
                       else None::(complete_branches k brs)
      end
    end.

  Definition elab_branches {A} (loc: astloc) (tn: ident * nat) (exhaustive : bool)
             (elab_exp: LustreAst.expression -> Elab (eexp * astloc))
             (f_ck: enumtag -> sclock)
             (f_brs: list (nat * list (eexp * astloc)) -> list A)
             (aes: list (ident * list LustreAst.expression)) :
    Elab (list A * list (type * sclock * astloc)) :=
    do aes <- mmap (fun '(c, ae) =>
                     do (c, tn') <- elab_enum loc c;
                     do _ <- assert_type' loc (Tenum tn) (Tenum tn');
                     do e <- mmap elab_exp ae;
                     do _ <- unify_same_clock (f_ck c) (lannots e);
                     ret (c, e)) aes;
    let es := fst (split aes) in
    do _ <- check_duplicates loc es;
    do _ <- if exhaustive then check_exhaustivity loc (snd tn) es else ret tt;
    do e0 <- hd_branch loc aes;
    let anns0 := lannots (snd e0) in
    do _ <- mmap (fun '(_, ae) =>
                   unify_paired_types loc anns0 (lannots ae)
                ) aes;
    let aes := List.rev (f_brs (BranchesSort.sort aes)) in
    ret (aes, anns0).

  Fixpoint elab_exp (is_top : bool) (ae: expression) {struct ae} : Elab (eexp * astloc) :=
    let elab_exp := elab_exp false in
    match ae with
    | CONSTANT ac loc =>
      do x <- fresh_ident;
      do c <- elab_constant loc ac;
      match c with
      | ConstA c => ret (Econst c (Svar x), loc)
      | EnumA tag ty => ret (Eenum tag (Tenum ty) (Svar x), loc)
      end

    | VARIABLE x loc =>
      do (ty, ck) <- find_var loc x;
      ret (Evar x (ty, (ck, if is_top then None else Some (Vnm x))), loc)

    | UNARY aop [ae'] loc =>
      let op := elab_unop aop in
      do (e, loc') <- elab_exp ae';
      do (ty, sck) <- single_annot loc' e;
      do ty' <- find_type_unop loc op ty;
      ret (Eunop op e (ty', (sck, None)), loc)
    | UNARY _ _ loc => err_not_singleton loc

    | CAST aty' [ae'] loc =>
      do ty' <- elab_primitive_type loc aty';
      do (e, loc') <- elab_exp ae';
      do (ty, sck) <- single_annot loc' e;
      do _ <- assert_primitive_type' loc' ty;
      ret (Eunop (CastOp ty') e (Tprimitive ty', (sck, None)), loc)
    | CAST _ _ loc => err_not_singleton loc

    | BINARY aop [ae1] [ae2] loc =>
      let op := elab_binop aop in
      do (e1, loc1) <- elab_exp ae1;
      do (ty1, sck1) <- single_annot loc1 e1;
      do (e2, loc2) <- elab_exp ae2;
      do (ty2, sck2) <- single_annot loc2 e2;
      do ty' <- find_type_binop loc op ty1 ty2;
      do _ <- unify_sclock tenv loc sck1 sck2;
      ret (Ebinop op e1 e2 (ty', (sck1, None)), loc)
    | BINARY _ _ _ loc => err_not_singleton loc

    | FBY ae0s aes aer loc =>
      do e0s <- mmap elab_exp ae0s;
      do es <- mmap elab_exp aes;
      let ans0 := lnannots e0s in
      do _ <- unify_paired_clock_types loc ans0 (lnannots es);
      do ans0 <- mmap update_ann (map discardname ans0);
      do er <- mmap elab_exp aer;
      do _ <- mmap assert_reset_type er;
      ret (Efby (map fst e0s) (map fst es) (map fst er) ans0, loc)

    | ARROW ae0s aes aer loc =>
      do e0s <- mmap elab_exp ae0s;
      do es <- mmap elab_exp aes;
      let ans0 := lnannots e0s in
      do _ <- unify_paired_clock_types loc ans0 (lnannots es);
      do ans0 <- mmap update_ann (map discardname ans0);
      do er <- mmap elab_exp aer;
      do _ <- mmap assert_reset_type er;
      ret (Earrow (map fst e0s) (map fst es) (map fst er) ans0, loc)

    | WHEN aes' x c loc =>
      do (xty, xck) <- find_var loc x;
      do (c, tn') <- elab_enum loc c;
      do eas' <- mmap elab_exp aes';
      let ans' := lannots eas' in
      do _ <- unify_same_clock xck ans';
      ret (Ewhen (map fst eas') x c
                 (lannots_ty ans', (Son xck (Vnm x) (Tenum tn', c), None)), loc)

    | MERGE x aes loc =>
      do (xty, sck) <- find_var loc x;
      do tn <- assert_enum_type loc x xty;
      do (eas, tys) <- elab_branches loc tn true elab_exp (fun c => Son sck (Vnm x) (xty, c))
                                    (List.map (fun '(_, e) => List.map fst e))
                                    aes;
      ret (Emerge (x, Tenum tn) eas (lannots_ty tys, (sck, None)), loc)

    | CASE [ae] aes [] loc =>
      do (e, eloc) <- elab_exp ae;
      do (ety, eck) <- single_annot eloc e;
      do tn <- assert_enum_type' loc ety;
      do (eas, anns) <- elab_branches loc tn true elab_exp (fun _ => eck)
                                    (List.map (fun '(_, e) => Some (List.map fst e)))
                                    aes;
      let tys := lannots_ty anns in
      ret (Ecase e eas (map (fun ty => init_type ty eck) tys) (tys, (eck, None)), loc)
    | CASE [ae] aes des loc =>
      do (e, eloc) <- elab_exp ae;
      do (ety, eck) <- single_annot eloc e;
      do tn <- assert_enum_type' loc ety;
      do (eas, anns) <- elab_branches loc tn false elab_exp (fun _ => eck)
                                    (complete_branches (snd tn))
                                    aes;
      do deas <- mmap elab_exp des;
      do _ <- unify_paired_types loc anns (lannots deas);
      let tys := lannots_ty anns in
      ret (Ecase e eas (map fst deas) (tys, (eck, None)), loc)
    | CASE _ _ _ loc => err_not_singleton loc

    | APP f aes aer loc =>
      (* node interface *)
      do (tyck_in, tyck_out) <- find_node_interface loc f;
      (* elaborate arguments *)
      do eas <- mmap elab_exp aes;
      (* elaborate reset and check it has boolean type *)
      do er <- mmap elab_exp aer;
      do _ <- mmap assert_reset_type er;
      (* instantiate annotations *)
      let anns := lnannots eas in
      do sub <- instantiating_subst (tyck_in++tyck_out);
      do xbase <- fresh_ident;
      do ianns <- mmap (inst_annot loc (Svar xbase) sub Vidx) tyck_in;
      do oanns <- mmap (inst_annot loc (Svar xbase) sub (if is_top then Vidx else Vnm)) tyck_out;
      do _ <- unify_inputs loc ianns anns;
      ret (Eapp f (map fst eas) (map fst er) oanns, loc)
    end.

  Definition freeze_ident (sid : sident) : Elab ident :=
    do sid <- update_sident sid;
    match sid with
    | Vnm x | Vidx x => ret x
    end.

  Definition freeze_clock (sck : sclock) : Elab clock :=
    do sck <- update_sclock sck;
    ret (sclk' sck).

  Definition freeze_nclock (nck : nsclock) : Elab nclock :=
    let (sck, x) := nck in
    do ck <- freeze_clock sck;
    match x with
    | None => ret (ck, None)
    | Some x =>
      do x <- freeze_ident x;
      ret (ck, Some x)
    end.

  Definition freeze_ann (tc : ann) : Elab Syn.ann :=
    let '(ty, nck) := tc in
    do nck <- freeze_nclock nck;
    ret (ty, nck).

  (* Add [when]s around [e], assumed to be on the base clock, so that it *)
  (* has the given clock [ck]. *)
  Fixpoint add_whens (e: Syn.exp) (tys: list type) (ck: clock) : Elab Syn.exp :=
    match ck with
    | Cbase => ret e
    | Con ck' x (_, k) =>
      do e' <- add_whens e tys ck';
      if Env.mem x env then ret (Syn.Ewhen [e'] x k (tys, (ck, None)))
      else error (MSG "Clock variable " :: CTX x :: MSG " escapes its scope" :: nil)
    end.

  Fixpoint freeze_exp (e : eexp) : Elab Syn.exp :=
    let freeze_exps := mmap freeze_exp in
    match e with
    | Econst c ck =>
      let ty := ctype_cconst c in
      do ck' <- freeze_clock ck;
      add_whens (Syn.Econst c) [Tprimitive ty] ck'

    | Eenum k ty ck =>
      do ck' <- freeze_clock ck;
      add_whens (Syn.Eenum k ty) [ty] ck'

    | Evar x ann =>
      do ann' <- freeze_ann ann;
      ret (Syn.Evar x ann')

    | Eunop unop e ann =>
      do e' <- freeze_exp e;
      do ann' <- freeze_ann ann;
      ret (Syn.Eunop unop e' ann')

    | Ebinop binop e1 e2 ann =>
      do e1' <- freeze_exp e1;
      do e2' <- freeze_exp e2;
      do ann' <- freeze_ann ann;
      ret (Syn.Ebinop binop e1' e2' ann')

    | Efby e0s es er anns =>
      do e0s <- freeze_exps e0s;
      do es <- freeze_exps es;
      do er <- freeze_exps er;
      do anns <- mmap freeze_ann anns;
      ret (Syn.Efby e0s es er anns)

    | Earrow e0s es er anns =>
      do e0s <- freeze_exps e0s;
      do es <- freeze_exps es;
      do er <- freeze_exps er;
      do anns <- mmap freeze_ann anns;
      ret (Syn.Earrow e0s es er anns)

    | Ewhen es ckid b (tys, nck) =>
      do es <- freeze_exps es;
      do nck <- freeze_nclock nck;
      ret (Syn.Ewhen es ckid b (tys, nck))

    | Emerge ckid es (tys, nck) =>
      do es <- mmap freeze_exps es;
      do nck <- freeze_nclock nck;
      ret (Syn.Emerge ckid es (tys, nck))

    | Ecase e es d (tys, nck) =>
      do e <- freeze_exp e;
      do es <- mmap (or_default_with (ret None) (fun es => do es <- freeze_exps es; ret (Some es))) es;
      do d <- freeze_exps d;
      do nck <- freeze_nclock nck;
      ret (Syn.Ecase e es d (tys, nck))

    | Eapp f es er anns =>
      do es <- freeze_exps es;
      do er <- freeze_exps er;
      do anns <- mmap freeze_ann anns;
      ret (Syn.Eapp f es er anns)
    end.

  Fixpoint unify_pat (gloc: astloc)
                     (xs: list ident)
                     (anns: list ((type * nsclock) * astloc)) : Elab unit :=
    match xs, anns with
    | nil, nil => ret tt
    | x::xs', ((ty, ck), loc)::anns' =>
      do (xty, xck) <- find_var loc x;
      do _ <- assert_id_type loc x xty ty;
      do _ <- unify_nclock tenv loc x xck ck;
      unify_pat gloc xs' anns'
    | nil, _ => err_loc gloc (msg "too few variables on lhs of equation.")
    | _, nil => err_loc gloc (msg "too many variables on lhs of equation.")
    end.

  Definition elab_equation (aeq : LustreAst.equation) : Elab Syn.equation :=
    let '((xs, es), loc) := aeq in
    do es' <- mmap (elab_exp true) es;
    do _ <- unify_pat loc xs (lnannots es');
    do es' <- mmap freeze_exp (List.map fst es');
    ret (xs, es').

End ElabExpressions.

Section ElabDeclaration.

  (* Map type names to their constructors *)
  Variable tenv: Env.t (list ident).

  (* Map node names to input and output types and clocks. *)
  Variable nenv : Env.t (list (ident * (type * clock))
                        * list (ident * (type * clock))).

  Definition err_incoherent_clock (loc: astloc) (x: ident) : Elab unit :=
    err_loc loc (MSG "The declared clock of " :: CTX x
                     :: msg " is incoherent with the other declarations").

  Fixpoint assert_preclock (loc: astloc) (x: ident)
           (pck: LustreAst.clock) (ck: clock) : Elab unit :=
    match pck, ck with
    | BASE, Cbase => ret tt
    | ON pck' py pc, Con ck' y (_, c) =>
      if py ==b y then
        do (c', tn) <- elab_enum tenv loc pc;
        if c' ==b c
        then assert_preclock loc x pck' ck'
        else err_incoherent_clock loc x
      else err_incoherent_clock loc x
    | _, _ => err_incoherent_clock loc x
    end.

  Fixpoint elab_var_decls_pass
           (acc: Env.t (type * clock)
                 * list (ident * (type_name * preclock * astloc)))
           (vds: list (ident * (type_name * preclock * astloc)))
    : Elab (Env.t (type * clock)
           * list (ident * (type_name * preclock * astloc))) :=
    match vds with
    | [] => ret acc
    | (x, (sty, pck, loc)) as vd :: vds =>
      let (env, notdone) := acc in
        match pck with
        | FULLCK BASE =>
          if Env.mem x env
          then err_loc loc (CTX x :: msg " is declared more than once")
          else
            do ty <- elab_type tenv loc sty;
            elab_var_decls_pass (Env.add x (ty, Cbase) env, notdone) vds

        | FULLCK (ON cy' y c) =>
          match Env.find y env with
          | None => elab_var_decls_pass (env, vd :: notdone) vds
          | Some (yt, cy) =>
            if Env.mem x env
            then err_loc loc (CTX x :: msg " is declared more than once")
            else do _ <- assert_enum_type loc y yt;
                 do _ <- assert_preclock loc x cy' cy;
                 do (c', tn') <- elab_enum tenv loc c;
                 do _ <- assert_id_type loc y yt (Tenum tn');
                 do ty <- elab_type tenv loc sty;
                 elab_var_decls_pass (Env.add x (ty, Con cy y (yt, c')) env, notdone) vds
          end

        | WHENCK y c =>
          match Env.find y env with
          | None => elab_var_decls_pass (env, vd :: notdone) vds
          | Some (yt, cy) =>
            if Env.mem x env
            then err_loc loc (CTX x :: msg " is declared more than once")
            else do _ <- assert_enum_type loc y yt;
                 do (c', tn') <- elab_enum tenv loc c;
                 do _ <- assert_id_type loc y yt (Tenum tn');
                 do ty <- elab_type tenv loc sty;
                 elab_var_decls_pass
                   (Env.add x (ty, Con cy y (yt, c')) env, notdone) vds
          end
        end
    end.

  Fixpoint elab_var_decls' {A: Type}
           (loc : astloc)
           (fuel: list A)
           (env : Env.t (type * clock))
           (vds : list (ident * (type_name * preclock * astloc)))
    : Elab (Env.t (type * clock)) :=
      match vds with
      | [] => ret env
      | _ =>
        match fuel with
        | [] => err_loc loc (MSG "incoherent or cyclic clocks: "
                                :: msg_ident_list (map fst vds))
        | _ :: fuel' =>
          do (env', notdone) <- elab_var_decls_pass (env, []) vds;
          elab_var_decls' loc fuel' env' notdone
        end
      end.

  Definition elab_var_decls
             (loc: astloc)
             (env: Env.t (type * clock))
             (vds: list (ident * (type_name * preclock * astloc)))
    : Elab (Env.t (type * clock)) :=
    elab_var_decls' loc vds env vds.

  Definition annotate {A: Type} (env: Env.t A)
             (vd: ident * (type_name * preclock * astloc)) : Elab (ident * A) :=
    let '(x, (sty, pck, loc)) := vd in
    match Env.find x env with
    | None => error (msg "internal error (annotate)")
    | Some a => ret (x, a)
    end.

  Definition nameset {A: Type} s (xs: list (ident * A)) : PS.t :=
    List.fold_left (fun acc x => PS.add (fst x) acc) xs s.

  Lemma nameset_spec:
    forall {A: Type} x (xs: list (ident * A)) s,
      PS.In x (nameset s xs) <-> PS.In x s \/ In x (map fst xs).
  Proof.
    induction xs as [|yv xs IH].
    now intuition.
    destruct yv as (y & v); simpl.
    split; intro HH.
    - apply IH in HH.
      destruct HH as [HH|]; auto.
      rewrite PSP.FM.add_iff in HH.
      intuition.
    - apply IH.
      rewrite PSP.FM.add_iff.
      intuition.
  Qed.

  Definition check_defined (loc: astloc) (defd: PS.t) (eqs: list equation) : Elab unit :=
    let defd' := vars_defined eqs in
    if check_nodup defd' then
      let defd' := ps_from_list defd' in
      if PS.equal defd defd' then ret tt
      else err_loc loc (msg "Missing or too many variables defined")
    else err_loc loc (msg "Duplicate in vars defined").

  Lemma check_defined_spec:
    forall eqs loc defd st st',
      check_defined loc defd eqs st = OK (tt, st') ->
      (forall x, In x (vars_defined eqs) <-> PS.In x defd)
      /\ NoDup (vars_defined eqs).
  Proof.
    intros * Hcheck.
    unfold check_defined in Hcheck.
    destruct (check_nodup _) eqn:Hndup. 2:inv Hcheck.
    apply check_nodup_correct in Hndup.
    split; auto.
    destruct (PS.equal _ _) eqn:Hpseq. 2:inv Hcheck.
    apply PSF.equal_2 in Hpseq.
    intros x. rewrite (Hpseq x).
    rewrite ps_from_list_In. reflexivity.
  Qed.

  Definition check_nodupanon loc (xin xvar xout : list (ident * (type * clock))) (eqs : list equation) :=
    if check_nodup (Syn.idents (xin++xvar++xout++anon_in_eqs eqs))
    then ret tt
    else err_loc loc (msg "Duplicate in input, vars and outputs of node").

  Lemma check_nodupanon_spec : forall loc xin xvar xout eqs st st',
      check_nodupanon loc xin xvar xout eqs st = OK (tt, st') ->
      NoDupMembers (xin ++ xvar ++ xout ++ anon_in_eqs eqs).
  Proof.
    intros * Hcheck.
    unfold check_nodupanon in Hcheck.
    destruct (check_nodup _) eqn:Hndup. 2:inv Hcheck.
    apply check_nodup_correct in Hndup.
    rewrite fst_NoDupMembers; auto.
  Qed.

  Definition check_atom loc name :=
    if is_atom name
    then ret tt
    else err_loc loc (CTX name :: MSG " should be an atom" :: nil).

  Lemma check_atom_spec : forall loc name st res,
      check_atom loc name st = OK res ->
      atom name.
  Proof.
    intros * Hcheck.
    unfold check_atom in *.
    destruct is_atom eqn:Hat; inv Hcheck.
    apply is_atom_spec; auto.
  Qed.

  Ltac monadInv :=
    simpl in *;
    unfold err_not_singleton, err_loc, error in *;
    match goal with
    | H: OK _ = OK _ |- _ =>
      inversion H; clear H; try subst
    | H: Error _ = OK _ |- _ =>
      discriminate
    | H: ret _ _ = _ |- _ =>
      unfold ret in H
    | H: bind ?x ?f ?st = OK (?res, ?st') |- _ =>
      let H1 := fresh "Hbind" in
      let H2 := fresh "Hbind" in
      eapply bind_inv in H as [? [? [H1 H2]]]
    | H: bind2 ?x ?f ?st = OK (?res, ?st') |- _ =>
      let H1 := fresh "Hbind" in
      let H2 := fresh "Hbind" in
      eapply bind2_inv in H as [? [? [? [H1 H2]]]]
    end; simpl in *.

  Local Ltac destruct_to_singl l :=
    destruct l; [|destruct l]; auto.

  (** *** freeze_* functions dont modify the state *)

  Fact update_sclock_st_id : forall sck1 sck2 st1 st2,
      update_sclock sck1 st1 = OK (sck2, st2) ->
      st2 = st1.
  Proof.
    induction sck1; intros * Hfreeze; repeat monadInv.
    - reflexivity.
    - unfold subst_clock in Hbind; repeat monadInv.
      destruct x; repeat monadInv.
      1,2:destruct st1 as ((?&?)&?); repeat monadInv; auto.
    - eapply IHsck1 in Hbind; subst.
      unfold update_sident in Hbind1.
      destruct s; repeat monadInv; auto.
      unfold subst_ident in Hbind.
      destruct x0; repeat monadInv.
      1,2:destruct st1 as ((?&?)&?); repeat monadInv; auto.
  Qed.

  Fact freeze_clock_st_id : forall ck1 ck2 st1 st2,
      freeze_clock ck1 st1 = OK (ck2, st2) ->
      st2 = st1.
  Proof.
    unfold freeze_clock.
    intros * Hfreeze. repeat monadInv.
    eapply update_sclock_st_id; eauto.
  Qed.

  Fact freeze_nclock_st_id : forall nck1 nck2 st1 st2,
      freeze_nclock nck1 st1 = OK (nck2, st2) ->
      st2 = st1.
  Proof.
    unfold freeze_nclock, freeze_ident, update_sident, subst_ident.
    intros (?&[|]) * Hfreeze; repeat monadInv.
    - eapply freeze_clock_st_id in Hbind; subst.
      destruct s0; repeat monadInv; auto.
      destruct st1 as ((?&?)&?), x2, (Env.find _ _); repeat monadInv; auto.
    - eapply freeze_clock_st_id; eauto.
  Qed.

  Corollary freeze_ann_st_id : forall ann1 ann2 st1 st2,
      freeze_ann ann1 st1 = OK (ann2, st2) ->
      st2 = st1.
  Proof.
    unfold freeze_ann.
    intros (?&?) * Hfreeze; repeat monadInv.
    eapply freeze_nclock_st_id; eauto.
  Qed.

  Fact mmap_st_id {A B} : forall (f : A -> Elab B) xs ys st1 st2,
      Forall (fun x => forall y st1 st2, f x st1 = OK (y, st2) -> st2 = st1) xs ->
      mmap f xs st1 = OK (ys, st2) -> st2 = st1.
  Proof.
    induction xs; intros * Hf Hmap; repeat monadInv; auto.
    inv Hf.
    apply IHxs in Hbind1; auto.
    apply H1 in Hbind; auto. congruence.
  Qed.

  Lemma add_whens_st_id : forall env tys ck e e' st1 st2,
      add_whens env e tys ck st1 = OK (e', st2) ->
      st2 = st1.
  Proof.
    induction ck as [|??? (?&?)]; intros * Hadds; repeat monadInv; auto.
    eapply IHck in Hbind; subst.
    destruct (Env.mem _ _); repeat monadInv; auto.
  Qed.

  Lemma freeze_exp_st_id : forall env e e' st1 st2,
      freeze_exp env e st1 = OK (e', st2) ->
      st2 = st1.
  Proof.
    induction e using eexp_ind2; intros * Hfree; simpl in *; repeat monadInv.
    - (* const *)
      eapply freeze_clock_st_id in Hbind; subst.
      eapply add_whens_st_id; eauto.
    - (* enum *)
      eapply freeze_clock_st_id in Hbind; subst.
      eapply add_whens_st_id; eauto.
    - (* var *)
      eapply freeze_ann_st_id; eauto.
    - (* unop *)
      eapply IHe in Hbind; subst.
      eapply freeze_ann_st_id; eauto.
    - (* binop *)
      eapply IHe1 in Hbind; eapply IHe2 in Hbind1; subst.
      eapply freeze_ann_st_id; eauto.
    - (* fby *)
      eapply mmap_st_id in Hbind2; subst. 2:eapply Forall_forall; eauto using freeze_ann_st_id.
      eapply mmap_st_id in Hbind; eauto.
      eapply mmap_st_id in Hbind1; eauto.
      eapply mmap_st_id in Hbind0; eauto. subst; auto.
    - (* arrow *)
      eapply mmap_st_id in Hbind2; subst. 2:eapply Forall_forall; eauto using freeze_ann_st_id.
      eapply mmap_st_id in Hbind; eauto.
      eapply mmap_st_id in Hbind1; eauto.
      eapply mmap_st_id in Hbind0; eauto. subst; auto.
    - (* when *)
      destruct a; repeat monadInv.
      eapply mmap_st_id in Hbind; eauto.
      eapply freeze_nclock_st_id in Hbind1. subst; auto.
    - (* merge *)
      destruct a; repeat monadInv.
      eapply mmap_st_id in Hbind; eauto.
      2:{ eapply Forall_impl; [|eauto]. intros * ? * Hmap.
          eapply mmap_st_id in Hmap; eauto. }
      apply freeze_nclock_st_id in Hbind1. subst; auto.
    - (* case *)
      destruct a; repeat monadInv.
      apply IHe in Hbind.
      eapply mmap_st_id in Hbind1; eauto.
      2:{ eapply Forall_impl; [|eauto]. intros * ? * Hmap.
          destruct a; repeat monadInv; auto.
          eapply mmap_st_id in Hbind3; eauto. }
      eapply mmap_st_id in Hbind0; eauto.
      apply freeze_nclock_st_id in Hbind2. subst; auto.
    - (* app *)
      eapply mmap_st_id in Hbind0; subst. 2:eapply Forall_forall; eauto using freeze_ann_st_id.
      eapply mmap_st_id in Hbind; eauto.
      eapply mmap_st_id in Hbind1; eauto. subst; auto.
  Qed.

  (** *** The anons are prefixed by `elab` *)

  Fact instantiating_subst_AtomOrGensym' : forall {typ} (xs : list (ident * typ)) sub st1 st2,
    mmap (fun '(x, ty) => do x' <- fresh_ident; ret (x, x')) xs st1 = OK (sub, st2) ->
    forall x x', In (x, x') sub -> AtomOrGensym elab_prefs x'.
  Proof.
    induction xs as [|(?&?) ?]; intros * Hmmap * Hin; repeat monadInv; inv Hin.
    - inv H. unfold fresh_ident in Hbind0.
      destruct st1 as ((?&?)&?); monadInv.
      right. exists elab. split; eauto.
      eapply PSF.singleton_2; auto.
    - eapply IHxs; eauto.
  Qed.

  Lemma instantiating_subst_AtomOrGensym : forall xs sub st1 st2,
      instantiating_subst xs st1 = OK (sub, st2) ->
      forall x x', Env.MapsTo x x' sub -> AtomOrGensym elab_prefs x'.
  Proof.
    unfold instantiating_subst.
    intros * Hinst * Hmap; repeat monadInv.
    apply Env.from_list_find_In in Hmap.
    eapply instantiating_subst_AtomOrGensym'; eauto.
  Qed.

  Lemma anon_streams_AtomOrGensym : forall xs base loc sub anns anns' anns'' st0 st0' st1 st2 st3 st4,
      instantiating_subst xs st0 = OK (sub, st0') ->
      mmap (inst_annot loc (Svar base) sub Vnm) anns st1 = OK (anns', st2) ->
      mmap freeze_ann anns' st3 = OK (anns'', st4) ->
      Forall (AtomOrGensym elab_prefs) (map fst (Syn.anon_streams anns'')).
  Proof.
    induction anns; intros * Hsub Hinst Hfreeze; repeat monadInv; auto.
    destruct x2 as (?&?&[?|]); eauto.
    constructor; eauto. clear Hbind1 Hbind3.
    destruct a as (?&?&?); repeat monadInv.
    destruct (Env.find _ _) eqn:Hfind; repeat monadInv.
    unfold freeze_ident in Hbind; repeat monadInv.
    eapply instantiating_subst_AtomOrGensym in Hsub; eauto.
  Qed.

  Fact fresh_ins_AtomOrGensym' : forall env tenv nenv env' es es' es'' st1 st2 st3 st4,
      Forall
        (fun e => forall e' loc e'' st1 st2 st3 st4,
             elab_exp env tenv nenv false e st1 = OK (e', loc, st2) ->
             freeze_exp env' e' st3 = OK (e'', st4) -> Forall (AtomOrGensym elab_prefs) (map fst (fresh_in e''))) es ->
      mmap (elab_exp env tenv nenv false) es st1 = OK (es', st2) ->
      mmap (freeze_exp env') (map fst es') st3 = OK (es'', st4) ->
      Forall (AtomOrGensym elab_prefs) (map fst (fresh_ins es'')).
  Proof.
    induction es; intros * Hf Helab Hfreeze;
      inv Hf; repeat monadInv; unfold fresh_ins; simpl; auto.
    rewrite map_app. apply Forall_app; split; eauto.
    destruct x. eapply H1; eauto.
  Qed.

  Fact mmap_Permutation {A B} : forall (f: A -> Elab B) xs xs' ys st1 st2,
      (forall x y st1 st2, f x st1 = OK (y, st2) -> st2 = st1) ->
      Permutation xs xs' ->
      mmap f xs st1 = OK (ys, st2) ->
      exists ys' st2' ,
        Permutation ys ys' /\
        mmap f xs' st1 = OK (ys', st2').
  Proof.
    intros * Hf Hperm. revert ys st1 st2.
    induction Hperm; intros * Hmap; simpl in Hmap; repeat monadInv.
    - exists [], st2; auto.
    - eapply IHHperm in Hbind1 as (?&?&Hperm'&Hmap').
      exists (x0::x3), x4. split; auto.
      unfold bind.
      erewrite Hbind, Hmap'; auto.
    - do 2 eexists. split. eapply perm_swap.
      unfold bind. (* erewrite Hbind, Hbind0. *)
      assert (x1 = st1) by (eapply Hf in Hbind; eauto); subst.
      assert (x4 = st1) by (eapply Hf in Hbind0; eauto); subst.
      rewrite Hbind0, Hbind, Hbind1; simpl.
      unfold ret; eauto.
    - eapply IHHperm1 in Hmap as (?&?&Hperm'&Hmap').
      eapply IHHperm2 in Hmap' as (?&?&Hperm''&Hmap'').
      do 2 eexists. split; [|eauto].
      etransitivity; eauto.
  Qed.

  Fact fresh_ins_brs_AtomOrGensym1 :
    forall env tenv nenv env' loc id exhaustive f_ck es es' tys es'' st1 st2 st3 st4,
      Forall
        (fun e =>
           Forall
             (fun e0 =>
                forall e' loc e'' st1 st2 st3 st4,
                  elab_exp env tenv nenv false e0 st1 = OK (e', loc, st2) ->
                  freeze_exp env' e' st3 = OK (e'', st4) -> Forall (AtomOrGensym elab_prefs) (map fst (fresh_in e'')))
             (snd e)) es ->
      elab_branches tenv loc id exhaustive (elab_exp env tenv nenv false) f_ck (map (fun '(_, e) => map fst e)) es st1 = OK (es', tys, st2) ->
      mmap (mmap (freeze_exp env')) es' st3 = OK (es'', st4) ->
      Forall (AtomOrGensym elab_prefs) (map fst (flat_map (flat_map fresh_in) es'')).
  Proof.
    unfold elab_branches.
    intros * Hf Helab Hfreeze.
    assert (exists es'' st2',
              (mmap
                 (fun '(c, ae) =>
                    do (c0, tn')<- elab_enum tenv0 loc c;
                    do _ <- assert_type' loc (Tenum id) (Tenum tn');
                    do e <- mmap (elab_exp env tenv0 nenv0 false) ae;
                    do _ <- unify_same_clock tenv0 (f_ck c0) (lannots e); ret (c0, e)) es st1
               = OK (es'', st2')
              /\ Permutation (map (fun '(_, es) => map fst es) es'') es')) as (es'''&st2'&Helab'&Hperm).
    { clear - Helab. repeat monadInv.
      unfold bind in *.
      setoid_rewrite Hbind. do 2 eexists; unfold ret; split; eauto.
      rewrite <-Permutation_rev.
      apply Permutation_map, BranchesSort.Permuted_sort. }
    eapply mmap_Permutation in Hfreeze as (?&st4'&Hperm'&Hfreeze').
    3:symmetry in Hperm; eauto.
    2:{ intros * Hmap. eapply mmap_st_id in Hmap; eauto.
        eapply Forall_forall; intros. eapply freeze_exp_st_id; eauto. }
    rewrite Hperm'.
    clear Helab st2 st4 tys es'' es' Hperm Hperm'.
    revert st1 st2' st3 st4' x es''' Hf Helab' Hfreeze'.
    induction es as [|(?&?)]; intros * Hf Helab Hfreeze;
      inv Hf; repeat monadInv; unfold fresh_ins; simpl in *; auto.
    rewrite map_app. apply Forall_app; split; eauto.
    eapply fresh_ins_AtomOrGensym'; eauto.
  Qed.

  Fact fresh_ins_brs_AtomOrGensym2 :
    forall env tenv nenv env' loc id exhaustive f_ck f_brs es es' tys es'' st1 st2 st3 st4,
      Forall
        (fun e =>
           Forall
             (fun e0 =>
                forall e' loc e'' st1 st2 st3 st4,
                  elab_exp env tenv nenv false e0 st1 = OK (e', loc, st2) ->
                  freeze_exp env' e' st3 = OK (e'', st4) -> Forall (AtomOrGensym elab_prefs) (map fst (fresh_in e'')))
             (snd e)) es ->
      (forall xs, Permutation (map_filter (fun x => x) (f_brs xs))
                         (map_filter (fun x => x) (map (fun '(_, e) => Some (map fst e)) xs))) ->
      elab_branches tenv loc id exhaustive (elab_exp env tenv nenv false) f_ck f_brs es st1 = OK (es', tys, st2) ->
      mmap
        (or_default_with (ret None) (fun es : list eexp => do es0 <- mmap (freeze_exp env') es; ret (Some es0)))
        es' st3 = OK (es'', st4) ->
      Forall (AtomOrGensym elab_prefs) (map fst (flat_map (or_default_with [] (flat_map fresh_in)) es'')).
  Proof.
    unfold elab_branches.
    intros * Hf Hfbrs Helab Hfreeze.
    assert (exists es'' st2',
              (mmap
                 (fun '(c, ae) =>
                    do (c0, tn')<- elab_enum tenv0 loc c;
                    do _ <- assert_type' loc (Tenum id) (Tenum tn');
                    do e <- mmap (elab_exp env tenv0 nenv0 false) ae;
                    do _ <- unify_same_clock tenv0 (f_ck c0) (lannots e); ret (c0, e)) es st1
               = OK (es'', st2')
               /\ Permutation (map_filter (fun x => x) (map (fun '(_, e) => Some (map fst e)) es''))
                             (map_filter (fun x => x) es')))
      as (es'''&st2'&Helab'&Hperm).
    { clear - Hfbrs Helab. repeat monadInv.
      unfold bind in *.
      setoid_rewrite Hbind. do 2 eexists; unfold ret; split; eauto.
      rewrite <-Permutation_rev, Hfbrs.
      apply Permutation_map_filter_Proper; auto.
      apply Permutation_map, BranchesSort.Permuted_sort. }
    assert (mmap (mmap (freeze_exp env')) (map_filter (fun x => x) es') st3 = OK (map_filter (fun x => x) es'', st4))
      as Hfreeze'.
    { clear - Hfreeze. revert es'' st3 st4 Hfreeze.
      induction es' as [|[|]]; intros; repeat monadInv; auto.
      unfold bind; simpl. erewrite Hbind0, IHes'; eauto.
      auto. } clear Hfreeze.
    eapply mmap_Permutation in Hfreeze' as (?&st4'&Hperm'&Hfreeze').
    3:(symmetry in Hperm; eauto).
    2:{ intros * Hmap.
        eapply mmap_st_id in Hmap; eauto.
        eapply Forall_forall; intros. eapply freeze_exp_st_id; eauto. }
    replace (flat_map (or_default_with [] (flat_map fresh_in)) es'')
      with (flat_map fresh_ins (map_filter (fun x => x) es'')).
    2:{ clear - es''.
        induction es'' as [|[|]]; simpl; f_equal; auto. }
    rewrite Hperm'.
    clear Helab st2 st4 tys es'' es' Hperm Hperm'.
    revert st1 st2' st3 st4' x es''' Hf Helab' Hfreeze'.
    induction es as [|(?&?)]; intros * Hf Helab Hfreeze;
      inv Hf; repeat monadInv; unfold fresh_ins; simpl in *; auto.
    rewrite map_app. apply Forall_app; split; eauto.
    eapply fresh_ins_AtomOrGensym'; eauto.
  Qed.

  Lemma complete_branches_Perm : forall k xs,
      Permutation (map_filter (fun x => x) (complete_branches k xs))
                  (map_filter (fun x => x) (map (fun '(_, e1) => Some (map fst e1)) xs)).
  Proof.
    induction k; intros; simpl in *; auto.
    destruct xs as [|(?&?)]; simpl.
    - clear - k.
      induction k; simpl; auto.
    - destruct (n =? k); simpl; auto.
      rewrite IHk; auto.
  Qed.

  Fact freeze_init_type_AtomOrGensym : forall env' tys ck es' st1 st2,
      mmap (freeze_exp env') (map (fun ty : type => init_type ty ck) tys) st1 = OK (es', st2) ->
      Forall (AtomOrGensym elab_prefs) (map fst (fresh_ins es')).
  Proof.
    induction tys; intros * Hmap; repeat monadInv; auto.
    rewrite map_app, Forall_app. split; eauto.
    destruct a; simpl in Hbind; repeat monadInv.
    1-2:clear - Hbind2; revert x x0 x3 Hbind2.
    1,2:induction x2 as [|??? (?&?)]; intros; repeat monadInv; eauto.
    1,2:destruct Env.mem; repeat monadInv; rewrite app_nil_r; eauto.
  Qed.

  Lemma fresh_in_AtomOrGensym : forall env tenv nenv env' e e' loc e'' st1 st2 st3 st4,
      elab_exp env tenv nenv false e st1 = OK ((e', loc), st2) ->
      freeze_exp env' e' st3 = OK (e'', st4) ->
      Forall (AtomOrGensym elab_prefs) (map fst (fresh_in e'')).
  Proof.
    induction e using expression_ind2; intros * Helab Hfreeze; simpl in *.
    - (* unop *)
      destruct_to_singl es; repeat monadInv.
      apply Forall_singl in H; eauto.
    - (* binop *)
      destruct_to_singl es1; repeat monadInv.
      destruct_to_singl es2; repeat monadInv.
      apply Forall_singl in H. apply Forall_singl in H0.
      rewrite map_app, Forall_app. eauto.
    - (* case *)
      cases; repeat monadInv;
        repeat rewrite map_app, Forall_app; repeat split.
      + inv H. eapply H4 in Hbind; eauto.
      + eapply fresh_ins_brs_AtomOrGensym2; eauto.
      + eapply freeze_init_type_AtomOrGensym in Hbind4; eauto.
      + inv H. eapply H4 in Hbind; eauto.
      + eapply fresh_ins_brs_AtomOrGensym2 in Hbind2; eauto.
        eapply complete_branches_Perm.
      + inv H1. destruct x13. eapply H4 in Hbind5; eauto.
      + inv H1. eapply fresh_ins_AtomOrGensym' in Hbind3; eauto.
    - (* cast *)
      destruct_to_singl es; repeat monadInv.
      apply Forall_singl in H. eauto.
    - (* app *)
      repeat monadInv.
      repeat rewrite map_app, Forall_app; repeat split; eauto.
      + eapply fresh_ins_AtomOrGensym' in H; eauto.
      + eapply fresh_ins_AtomOrGensym' in H0; eauto.
      + eapply anon_streams_AtomOrGensym; eauto.
    - (* constant *)
      repeat monadInv. destruct x1; simpl in *; repeat monadInv.
      + clear - Hbind2. revert e'' x2 st4 Hbind2.
        induction x1 as [|??? (?&?)]; intros; simpl in *; repeat monadInv; auto.
        destruct (Env.mem _ _); repeat monadInv.
        eapply IHx1 in Hbind. rewrite app_nil_r; auto.
      + clear - Hbind2. revert e'' x2 st4 Hbind2.
        induction x1 as [|??? (?&?)]; intros; simpl in *; repeat monadInv; auto.
        destruct (Env.mem _ _); repeat monadInv.
        eapply IHx1 in Hbind. rewrite app_nil_r; auto.
    - (* var *)
      repeat monadInv; auto.
    - (* fby *)
      repeat monadInv.
      repeat rewrite map_app, Forall_app; repeat split; simpl; auto.
      + eapply fresh_ins_AtomOrGensym' in H; eauto.
      + eapply fresh_ins_AtomOrGensym' in H0; eauto.
      + eapply fresh_ins_AtomOrGensym' in H1; eauto.
    - (* arrow *)
      repeat monadInv.
      repeat rewrite map_app, Forall_app; repeat split; simpl; auto.
      + eapply fresh_ins_AtomOrGensym' in H; eauto.
      + eapply fresh_ins_AtomOrGensym' in H0; eauto.
      + eapply fresh_ins_AtomOrGensym' in H1; eauto.
    - (* when *)
      repeat monadInv.
      eapply fresh_ins_AtomOrGensym'; eauto.
    - (* merge *)
      repeat monadInv.
      eapply fresh_ins_brs_AtomOrGensym1; eauto.
  Qed.

  Corollary fresh_ins_AtomOrGensym : forall env tenv nenv env' es es' es'' st1 st2 st3 st4,
      mmap (elab_exp env tenv nenv false) es st1 = OK (es', st2) ->
      mmap (freeze_exp env') (map fst es') st3 = OK (es'', st4) ->
      Forall (AtomOrGensym elab_prefs) (map fst (fresh_ins es'')).
  Proof.
    intros * Helab Hfreeze.
    eapply fresh_ins_AtomOrGensym'; [|eauto|eauto].
    eapply Forall_forall. intros * _ * ??.
    eapply fresh_in_AtomOrGensym; eauto.
  Qed.
  Hint Resolve fresh_in_AtomOrGensym fresh_ins_AtomOrGensym.

  Lemma anon_in_AtomOrGensym : forall env tenv nenv env' e e' loc e'' st1 st2 st3 st4,
      elab_exp env tenv nenv true e st1 = OK ((e', loc), st2) ->
      freeze_exp env' e' st3 = OK (e'', st4) ->
      Forall (AtomOrGensym elab_prefs) (map fst (anon_in e'')).
  Proof.
    destruct e; intros * Helab Hfreeze.
    - (* unop *)
      destruct_to_singl l; repeat monadInv; eauto.
    - (* binop *)
      destruct_to_singl l; repeat monadInv.
      destruct_to_singl l0; repeat monadInv.
      rewrite map_app, Forall_app. eauto.
    - (* case *)
      simpl in Helab.
      cases; repeat monadInv;
        repeat rewrite map_app, Forall_app; repeat split.
      + eapply fresh_in_AtomOrGensym in Hbind; eauto.
      + eapply fresh_ins_brs_AtomOrGensym2 in Hbind2; eauto.
        do 2 (eapply Forall_forall; intros). eapply fresh_in_AtomOrGensym; eauto.
      + eapply freeze_init_type_AtomOrGensym in Hbind4; eauto.
      + eapply fresh_in_AtomOrGensym in Hbind; eauto.
      + eapply fresh_ins_brs_AtomOrGensym2 in Hbind2; eauto.
        do 2 (eapply Forall_forall; intros). eapply fresh_in_AtomOrGensym; eauto.
        eapply complete_branches_Perm.
      + destruct x13. eapply fresh_in_AtomOrGensym; eauto.
      + eapply fresh_ins_AtomOrGensym' in Hbind3; eauto.
        eapply Forall_forall; intros. eapply fresh_in_AtomOrGensym; eauto.
    - (* cast *)
      destruct_to_singl l; repeat monadInv; eauto.
    - (* app *)
      repeat monadInv; eauto.
      rewrite map_app, Forall_app; repeat split; eauto.
    - (* constant *)
      eapply Forall_incl; [|eapply incl_map, anon_in_fresh_in].
      repeat monadInv. destruct x1; simpl in *; repeat monadInv.
      + clear - Hbind2. revert e'' x2 st4 Hbind2.
        induction x1 as [|??? (?&?)]; intros; simpl in *; repeat monadInv; auto.
        destruct (Env.mem _ _); repeat monadInv.
        eapply IHx1 in Hbind. rewrite app_nil_r; auto.
      + clear - Hbind2. revert e'' x2 st4 Hbind2.
        induction x1 as [|??? (?&?)]; intros; simpl in *; repeat monadInv; auto.
        destruct (Env.mem _ _); repeat monadInv.
        eapply IHx1 in Hbind. rewrite app_nil_r; auto.
    - (* var *)
      repeat monadInv; auto.
    - (* fby *)
      repeat monadInv.
      repeat rewrite map_app, Forall_app; repeat split; simpl; eauto.
    - (* arrow *)
      repeat monadInv.
      repeat rewrite map_app, Forall_app; repeat split; simpl; eauto.
    - (* when *)
      repeat monadInv.
      eapply fresh_ins_AtomOrGensym; eauto.
    - (* merge *)
      repeat monadInv.
      eapply fresh_ins_brs_AtomOrGensym1 in Hbind0; eauto.
      do 2 (eapply Forall_forall; intros).
      eapply fresh_in_AtomOrGensym; eauto.
  Qed.

  Corollary anon_ins_AtomOrGensym : forall env tenv nenv env' es es' es'' st1 st2 st3 st4,
      mmap (elab_exp env tenv nenv true) es st1 = OK (es', st2) ->
      mmap (freeze_exp env') (map fst es') st3 = OK (es'', st4) ->
      Forall (AtomOrGensym elab_prefs) (map fst (anon_ins es'')).
  Proof.
    induction es; intros * Helab Hfreeze; repeat monadInv; auto.
    unfold anon_ins; simpl.
    rewrite map_app, Forall_app; split.
    - destruct x. eapply anon_in_AtomOrGensym; eauto.
    - eapply IHes; eauto.
  Qed.

  Lemma anon_in_eq_AtomOrGensym : forall env tenv nenv eq st eq' st' ,
    elab_equation env tenv nenv eq st = OK (eq', st') ->
    Forall (AtomOrGensym elab_prefs) (map fst (anon_in_eq eq')).
  Proof.
    intros ??? ((xs&es)&loc) * Helab; unfold anon_in_eq; simpl in *.
    repeat monadInv; simpl.
    eapply anon_ins_AtomOrGensym; eauto.
  Qed.

  Corollary anon_in_eqs_AtomOrGensym : forall env tenv nenv eqs st eqs' st' ,
      mmap (elab_equation env tenv nenv) eqs st = OK (eqs', st') ->
      Forall (AtomOrGensym elab_prefs) (map fst (anon_in_eqs eqs')).
  Proof.
    induction eqs; intros * Hmmap;
      simpl in *; repeat monadInv; unfold anon_in_eqs; simpl; auto.
    rewrite map_app, Forall_app; split; auto.
    - eapply anon_in_eq_AtomOrGensym; eauto.
    - eapply IHeqs; eauto.
  Qed.

  Local Obligation Tactic :=
    Tactics.program_simpl;
      match goal with
      | H:_ = bind _ _ _ |- _ => symmetry in H
      end;
      repeat monadInv;
      repeat (progress
                match goal with
                | x:unit |- _ => destruct x
                | H:(if ?b then _ else _) _ = _ |- _ =>
                  let Hb := fresh "Hb" in
                  (destruct b eqn:Hb; try discriminate)
                | H:ret _ _ = OK _ |- _ => unfold ret in H; inv H
              end).

  Program Definition elab_declaration_node
          (name: ident) (has_state: bool) (inputs outputs locals: var_decls)
          (equations: list LustreAst.equation) (loc: astloc) : res (@node elab_prefs) :=
    match (do env_in  <- elab_var_decls loc (Env.empty _) inputs;
           do env_out <- elab_var_decls loc env_in outputs;
           do env     <- elab_var_decls loc env_out locals;
           do xin     <- mmap (annotate env_in) inputs;
           do xout    <- mmap (annotate env_out) outputs;
           do xvar    <- mmap (annotate env) locals;
           do eqs     <- mmap (elab_equation env tenv nenv) equations;
           (* TODO better error messages *)
           do _       <- check_nodupanon loc xin xvar xout eqs;
           do _       <- check_defined loc (nameset (nameset PS.empty xvar) xout) eqs;
           do _       <- check_atom loc name;
           do _       <- mmap (check_atom loc) (map fst (xin ++ xvar ++ xout));
           if (length xin ==b O) || (length xout ==b O)
           then err_loc loc (msg "not enough inputs or outputs")
           else ret (xin, xout, xvar, eqs)) init_state with
    | Error e => Error e
    | OK ((xin, xout, xvar, eqs), ((nfui, _), _)) =>
      OK {| n_name     := name;
            n_hasstate := has_state;
            n_in       := xin;
            n_out      := xout;
            n_vars     := xvar;
            n_eqs      := eqs |}
    end.
  Next Obligation.
    (* 0 < length xin *)
    rewrite Bool.orb_false_iff in Hb; destruct Hb as (Hin & Hout).
    apply not_equiv_decb_equiv in Hin.
    now apply Nat.neq_0_lt_0 in Hin.
  Qed.
  Next Obligation.
    (* 0 < length xout *)
    rewrite Bool.orb_false_iff in Hb; destruct Hb as (Hin & Hout).
    apply not_equiv_decb_equiv in Hout.
    now apply Nat.neq_0_lt_0 in Hout.
  Qed.
  Next Obligation.
    (* Permutation (map var_defined eqs) (map fst (xvar ++ xout)) *)
    apply check_nodupanon_spec in Hbind6.
    apply check_defined_spec in Hbind7 as [Hdefd Hnodup].
    apply NoDup_Permutation; auto.
    - rewrite <- fst_NoDupMembers.
      apply NoDupMembers_app_r in Hbind6.
      rewrite app_assoc in Hbind6.
      apply NoDupMembers_app_l in Hbind6; auto.
    - intros ?. rewrite Hdefd.
      repeat rewrite nameset_spec.
      rewrite map_app, in_app_iff.
      split; [intros [[?|?]|?] | intros [?|?]]; auto.
      apply not_In_empty in H. inv H.
  Qed.
  Next Obligation.
    (* NoDupMembers (xin ++ xlocal ++ xout ++ anon_in_eqs eqs) *)
    apply check_nodupanon_spec in Hbind6; auto.
  Qed.
  Next Obligation.
    (* Forall AtomNotReserved (xin ++ xvar ++ xout) /\ atom name *)
    replace (map fst (xin ++ xvar ++ xout ++ anon_in_eqs eqs)) with ((map fst (xin ++ xvar ++ xout) ++ map fst (anon_in_eqs eqs))).
    2:{ repeat rewrite map_app; repeat rewrite <- app_assoc; auto. }
    rewrite Forall_app. repeat split.
    - clear - Hbind5 Hbind9.
      revert nfui wildcard' wildcard'0 x18 x19 Hbind9.
      induction (xin ++ xvar ++ xout); intros; simpl in *; auto.
      repeat monadInv. destruct a as (?&?). constructor; eauto.
      eapply check_atom_spec in Hbind; left; auto.
    - eapply anon_in_eqs_AtomOrGensym; eauto.
    - eapply check_atom_spec; eauto.
  Qed.

  Program Definition elab_declaration_type
          (name: ident) (constructors: list ident) (loc: astloc) : res (ident * nat) :=
    OK (name, length constructors).

End ElabDeclaration.

Section ElabDeclarations.
  Open Scope error_monad_scope.

  Fixpoint elab_declarations'
           (G: global)
           (tenv: Env.t (list ident))
           (nenv: Env.t (list (ident * (type * clock)) * list (ident * (type * clock))))
           (decls: list declaration) : res global :=
  match decls with
  | [] => OK G
  | NODE name has_state inputs outputs locals equations loc :: ds =>
    do n <- elab_declaration_node tenv nenv name has_state inputs outputs locals equations loc;
    if Env.mem (n_name n) nenv
    then Error (err_loc' loc (MSG "deplicate definition for " :: CTX name :: nil))
    else elab_declarations' (Global G.(enums) (n :: G.(nodes)))
                          tenv (Env.add n.(n_name) (n.(n_in), n.(n_out)) nenv) ds
  | TYPE name constructors loc :: ds =>
    do t <- elab_declaration_type name constructors loc;
    if Env.mem name tenv
    then Error (err_loc' loc (MSG "duplicate definition for " :: CTX name :: nil))
    else elab_declarations' (Global (t :: G.(enums)) G.(nodes))
                          (Env.add name constructors tenv) nenv ds
  end.

  Import Instantiator.L.

  Definition bool_enums :=
    [(bool_id, 2)].

  Definition bool_tenv :=
    Env.add bool_id
            [false_id; true_id] (* order is important *)
            (Env.empty _).


  Program Definition elab_declarations (decls: list declaration) :
    res {G | wt_global G /\ wc_global G } :=
    match elab_declarations' (Global bool_enums []) bool_tenv (Env.empty _) decls with
    | OK G =>
      match Typ.check_global G, Clo.check_global G with
      | true, true => OK (exist _ G _)
      | false, _ => Error (msg "Post-elab check failed (typing)")
      | _, false => Error (msg "Post-elab check failed (clocking)")
      end
    | Error err => Error err
    end.
  Next Obligation.
    rename Heq_anonymous into Hwt. rename Heq_anonymous0 into Hwc. rename Heq_anonymous1 into Helab.
    symmetry in Hwt, Hwc, Helab.
    apply Typ.check_global_correct in Hwt.
    apply Clo.check_global_correct in Hwc.
    split; auto.
  Qed.
End ElabDeclarations.
