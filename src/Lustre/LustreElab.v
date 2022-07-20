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

Fixpoint msg_of_list_types (tys : list type) : errmsg :=
  match tys with
  | [] => msg ""
  | [ty] => msg (string_of_type ty)
  | ty::tys => MSG (string_of_type ty) :: MSG ", " :: msg_of_list_types tys
  end.

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

Local Instance sident_EqDec : EqDec sident eq.
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

Local Instance sclock_EqDec : EqDec sclock eq.
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

Definition ann : Type := (type * sclock)%type.
Definition lann : Type := (list type * sclock)%type.

(** elaboration exp : annotations use sclock *)
Inductive eexp : Type :=
(* constant have a sclock in order to later add whens *)
| Econst : cconst -> sclock -> eexp
| Eenum : enumtag -> type -> sclock -> eexp
| Evar   : ident -> ann -> eexp
| Elast  : ident -> ann -> eexp
| Eunop  : unop -> eexp -> ann -> eexp
| Ebinop : binop -> eexp -> eexp -> ann -> eexp
| Eextcall : ident -> list eexp -> (ctype * sclock) -> eexp

| Efby   : list eexp -> list eexp -> list ann -> eexp
| Earrow : list eexp -> list eexp -> list ann -> eexp

| Ewhen  : list eexp -> (ident * type) -> enumtag -> lann -> eexp
| Emerge : (ident * type) -> list (enumtag * list eexp) -> lann -> eexp
| Ecase  : eexp -> list (enumtag * list eexp) -> option (list eexp) -> lann -> eexp

| Eapp   : ident -> list eexp -> list eexp -> list ann -> eexp.

Inductive const_annot :=
| ConstA: cconst -> const_annot
| EnumA: enumtag -> (ident * list ident) -> const_annot.

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
      let id := Ids.gensym Ids.elab None n in
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
      (at level 200, X name, A at level 100, B at level 200).

  Notation "'do' ( X , Y ) <- A ; B" :=
    (bind2 A (fun X Y => B))
      (at level 200, X name, Y name, A at level 100, B at level 200).

End ElabNotations.

Import ElabNotations.

Local Ltac monadInv :=
  simpl in *;
  match goal with
  | H: OK _ = OK _ |- _ =>
    inversion H; clear H; try subst
  | H: Error _ = OK _ |- _ =>
    discriminate
  | H: ret _ _ = _ |- _ =>
    unfold ret in H
  | H: bind ?x ?f ?st = OK ?res |- _ =>
    let H1 := fresh "Hbind" in
    let H2 := fresh "Hbind" in
    eapply bind_inv in H as (?&?&H1&H2)
  | H: bind2 ?x ?f ?st = OK ?res |- _ =>
    let H1 := fresh "Hbind" in
    let H2 := fresh "Hbind" in
    eapply bind2_inv in H as (?&?&?&H1&H2)
  end; simpl in *.

Section mmap.
  Context {A B : Type}.
  Variable (f : A -> Elab B).

  Fixpoint mmap (l: list A) {struct l} : Elab (list B) :=
    match l with
    | nil => ret nil
    | hd :: tl => do hd' <- f hd; do tl' <- mmap tl; ret (hd' :: tl')
    end.


  Fact mmap_values : forall a st a1s st',
      mmap a st = OK (a1s, st') ->
      Forall2 (fun a a1 => exists st'', exists st''', f a st'' = OK (a1, st''')) a a1s.
  Proof.
    induction a; intros st a1s st' Hfold; repeat monadInv.
    - constructor.
    - specialize (IHa _ _ _ Hbind1).
      constructor; eauto.
  Qed.
End mmap.

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

  Fixpoint msg_of_clock (ck: clock) : errmsg :=
    match ck with
    | Cbase          => msg "."
    | Con ck id (Tenum t _, c) =>
      msg_of_clock ck ++ MSG " on " :: msg_of_enumtag t c
                    :: MSG "(" :: CTX id :: MSG ")" :: nil
    | _ => msg ""
    end.

  Fixpoint msg_of_sclock (ck: sclock) : errmsg :=
    match ck with
    | Sbase          => msg "."
    | Svar x         => CTX x :: nil
    | Son ck id (Tenum t _, c) =>
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

  Definition update_ann (a : (type * sclock)) : Elab (type * sclock) :=
    let '(ty, ck) := a in
    do ck' <- update_sclock ck;
    ret (ty, ck').

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

Section ElabExpressions.

  (* Map variable names to their types and clocks, and if the variable is usable as last. *)
  Variable env : Env.t (type * clock * bool).

  (* Map type names to their constructors *)
  Variable tenv: Env.t (list ident).

  (* External functions *)
  Variable eenv: Env.t (list ctype * ctype).

  (* Map node names to input and output types and clocks. *)
  Variable nenv : Env.t (list (ident * (type * clock))
                        * list (ident * (type * clock))).

  Open Scope nat.

  Definition find_var (loc: astloc) (x: ident) : Elab (type * sclock) :=
    match Env.find x env with
    | None => err_loc loc (CTX x :: msg " is not declared.")
    | Some (ty, ck, _) => ret (ty, sclk ck)
    end.

  Definition find_last (loc: astloc) (x: ident) : Elab (type * sclock) :=
    match Env.find x env with
    | None => err_loc loc (CTX x :: msg " is not declared.")
    | Some (ty, ck, true) => ret (ty, sclk ck)
    | Some _ => err_loc loc (CTX x :: msg " is not declared with last.")
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

  Definition assert_types (loc: astloc) (xty ty: list type) : Elab unit :=
    if xty ==b ty then ret tt
    else err_loc loc (MSG "Incompatible types: expected (" :: msg_of_list_types xty ++ MSG "), got (" :: msg_of_list_types ty ++ msg ")").

  Definition assert_enum_type (loc: astloc) (x: ident) (xty: type) : Elab (ident * list ident) :=
    match xty with
    | Tenum tx tn => ret (tx, tn)
    | _ => err_loc loc (CTX x :: MSG ": " :: msg_of_enum_type xty)
    end.

  Definition assert_enum_type' (loc: astloc) (ty: type) : Elab (ident * list ident) :=
    match ty with
    | Tenum tx tn => ret (tx, tn)
    | _ => err_loc loc (msg_of_enum_type ty)
    end.

  Definition assert_primitive_type' (loc: astloc) (ty: type) : Elab unit :=
    match ty with
    | Tprimitive _ => ret tt
    | Tenum _ _ => err_loc loc (msg_of_primitive_type ty)
    end.

  Inductive node_interface :=
  | Internal : list (ident * (type * clock)) -> list (ident * (type * clock)) -> node_interface
  | External : list ctype -> ctype -> node_interface.

  Definition find_node_interface (loc: astloc) (f: ident) : Elab node_interface :=
    match Env.find f nenv with
    | Some (ins, outs) => ret (Internal ins outs)
    | None =>
        match Env.find f eenv with
        | Some (ins, outs) => ret (External ins outs)
        | None => err_loc loc (MSG "node " :: CTX f :: msg " not found.")
        end
    end.

  Definition enum_to_enumtag (loc: astloc) (ty: ident) (c: ident) (cs: list ident) : option (enumtag * list ident) :=
    let (t, n) := fold_left
                    (fun (acc: option enumtag * nat) c' =>
                       let (t, n) := acc in
                       let t := match t with
                                | None => if c' ==b c then Some n else None
                                | Some t => Some t
                                end
                       in (t, n + 1)) cs (None, 0)
    in match t with
       | Some t => Some (t, cs)
       | None => None
       end.

  Definition elab_enum (loc: astloc) (c: ident) : Elab (enumtag * (ident * list ident)) :=
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

  Definition enum_bound (loc: astloc) (ty: ident) :=
    match Env.find ty tenv with
    | None => err_loc loc (MSG "enumerated type " :: CTX ty :: msg " not declared.")
    | Some cs => let n := length cs in
                if 0 <? n then ret cs
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
      do tn <- enum_bound loc t;
      ret (Tenum t tn)
    end.

  Definition elab_primitive_type (loc: astloc)  (ty: LustreAst.type_name) : Elab ctype :=
    do ty <- elab_type loc ty;
    match ty with
    | Tprimitive t => ret t
    | Tenum _ _ => err_loc loc (msg "primitive type expected")
    end.

  Definition err_not_singleton {A} (loc: astloc) : Elab A :=
    err_loc loc (msg "singleton argument expected").

  Definition single_annot (loc: astloc) (e: eexp) : Elab (type * sclock) :=
    match e with
    | Econst c ck => ret (Tprimitive (ctype_cconst c), ck)
    | Eenum _ ty ck => ret (ty, ck)
    | Eapp _ _ _ [(ty, ck)]
    | Evar _ (ty, ck)
    | Elast _ (ty, ck)
    | Eunop _ _ (ty, ck)
    | Ebinop _ _ _ (ty, ck)
    | Ewhen _ _ _ ([ty], ck)
    | Efby _ _ [(ty, ck)]
    | Earrow _ _ [(ty, ck)]
    | Emerge _ _ ([ty], ck)
    | Ecase _ _ _ ([ty], ck) => ret (ty, ck)
    | Eextcall _ _ (cty, ck) => ret (Tprimitive cty, ck)
    | _ => err_not_singleton loc
    end.

  Definition lannot (el : eexp * astloc) : list ((type * sclock) * astloc) :=
    let (e, loc) := el in
    match e with
    | Econst c ck => [((Tprimitive (ctype_cconst c), ck), loc)]
    | Eenum _ ty ck => [((ty, ck), loc)]
    | Evar _ (ty, ck)
    | Elast _ (ty, ck)
    | Eunop _ _ (ty, ck)
    | Ebinop _ _ _ (ty, ck) => [((ty, ck), loc)]
    | Eextcall _ _ (cty, ck) => [((Tprimitive cty, ck), loc)]
    | Ewhen _ _ _ (tys, ck)
    | Emerge _ _ (tys, ck)
    | Ecase _ _ _ (tys, ck) =>
      map (fun ty=> ((ty, ck), loc)) tys
    | Efby _ _ anns
    | Earrow _ _ anns
    | Eapp _ _ _ anns =>
      map (fun tc => (tc, loc)) anns
    end.

  Definition lannots (els : list (eexp * astloc))
    : list ((type * sclock) * astloc) := flat_map lannot els.

  Definition lnannot (el : eexp * astloc) : list ((type * nsclock) * astloc) :=
    let (e, loc) := el in
    match e with
    | Econst c ck => [((Tprimitive (ctype_cconst c), (ck, None)), loc)]
    | Eenum _ ty ck => [((ty, (ck, None)), loc)]
    | Evar x (ty, ck) => [((ty, (ck, Some (Vnm x))), loc)]
    | Elast _ (ty, ck) => [((ty, (ck, None)), loc)]
    | Eunop _ _ (ty, ck)
    | Ebinop _ _ _ (ty, ck) => [((ty, (ck, None)), loc)]
    | Eextcall _ _ (cty, ck) => [((Tprimitive cty, (ck, None)), loc)]
    | Ewhen _ _ _ (tys, ck)
    | Emerge _ _ (tys, ck)
    | Ecase _ _ _ (tys, ck) =>
      map (fun ty=> ((ty, (ck, None)), loc)) tys
    | Efby _ _ anns
    | Earrow _ _ anns
    | Eapp _ _ _ anns => map (fun tc => ((fst tc, (snd tc, None)), loc)) anns
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
           (ants anfs: list ((type * sclock) * astloc)) : Elab unit :=
    match ants, anfs with
    | [], [] => ret tt
    | ant::ants', anf::anfs' =>
      let '((tty, tck), tloc) := ant in
      let '((fty, fck), floc) := anf in
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
                       (MSG "Clock depends on output " :: CTX x ::
                            msg ". Dependencies between clock outputs are only permitted when node instantiation is the root of the expression.")
      | Some ni => ret (Son sck' (Vidx ni) b)
      end
    end.

  Definition inst_annot (loc: astloc) (base: sclock) (sub : Env.t ident)
             (xtc: ident * (type * clock)) : Elab ann :=
    let '(x, (ty, ck)) := xtc in
    do sck <- inst_clock loc base sub ck;
    ret (ty, sck).

  Definition inst_nannot (loc: astloc) (base: sclock) (sub : Env.t ident)
             (xtc: ident * (type * clock)) : Elab (type * nsclock) :=
    let '(x, (ty, ck)) := xtc in
    do sck <- inst_clock loc base sub ck;
    match (Env.find x sub) with
    | None => ret (ty, (sck, None))
    | Some x => ret (ty, (sck, Some (Vidx x)))
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

  Definition discardloc (ann : (type * sclock * astloc)) : (type * sclock) :=
    let '(ty, ck, _) := ann in (ty, ck).

  Definition discardname (ann : (type * nsclock)) : (type * sclock) :=
    let '(ty, (ck, _)) := ann in (ty, ck).

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

  Definition check_noreset {A} (loc: astloc) (er: list A) : Elab unit :=
    if is_nil er then ret tt
    else err_loc loc (msg "External call cannot be reset").

  Definition hd_branch {A : Type} loc (xs : list A) : Elab A :=
      match xs with
      | hd::_ => ret hd
      | [] => err_loc loc (msg "no branch")
      end.

  Definition elab_branches (loc: astloc) (tn: ident * list ident) (exhaustive : bool)
             (elab_exp: LustreAst.expression -> Elab (eexp * astloc))
             (f_ck: enumtag -> sclock)
             (aes: list (ident * list LustreAst.expression)) :
    Elab (list (enumtag * list eexp) * list (type * sclock * astloc)) :=
    do aes <- mmap (fun '(c, ae) =>
                     do (c, tn') <- elab_enum loc c;
                     do _ <- assert_type' loc (Tenum (fst tn) (snd tn)) (Tenum (fst tn') (snd tn'));
                     do e <- mmap elab_exp ae;
                     do _ <- unify_same_clock (f_ck c) (lannots e);
                     ret (c, e)) aes;
    let cs := fst (split aes) in
    do _ <- check_duplicates loc cs;
    do _ <- if exhaustive then check_exhaustivity loc (length (snd tn)) cs else ret tt;
    do e0 <- hd_branch loc aes;
    let anns0 := lannots (snd e0) in
    do _ <- mmap (fun '(_, ae) =>
                   unify_paired_types loc anns0 (lannots ae)
                ) aes;
    ret (map (fun '(c, es) => (c, map fst es)) aes, anns0).

  Fixpoint elab_exp (ae: expression) {struct ae} : Elab (eexp * astloc) :=
    match ae with
    | CONSTANT ac loc =>
      do x <- fresh_ident;
      do c <- elab_constant loc ac;
      match c with
      | ConstA c => ret (Econst c (Svar x), loc)
      | EnumA tag ty => ret (Eenum tag (Tenum (fst ty) (snd ty)) (Svar x), loc)
      end

    | VARIABLE x loc =>
      do (ty, ck) <- find_var loc x;
      ret (Evar x (ty, ck), loc)

    | LAST x loc =>
      do (ty, ck) <- find_last loc x;
      ret (Elast x (ty, ck), loc)

    | UNARY aop [ae'] loc =>
      let op := elab_unop aop in
      do (e, loc') <- elab_exp ae';
      do (ty, sck) <- single_annot loc' e;
      do ty' <- find_type_unop loc op ty;
      ret (Eunop op e (ty', sck), loc)
    | UNARY _ _ loc => err_not_singleton loc

    | CAST aty' [ae'] loc =>
      do ty' <- elab_primitive_type loc aty';
      do (e, loc') <- elab_exp ae';
      do (ty, sck) <- single_annot loc' e;
      do _ <- assert_primitive_type' loc' ty;
      ret (Eunop (CastOp ty') e (Tprimitive ty', sck), loc)
    | CAST _ _ loc => err_not_singleton loc

    | BINARY aop [ae1] [ae2] loc =>
      let op := elab_binop aop in
      do (e1, loc1) <- elab_exp ae1;
      do (ty1, sck1) <- single_annot loc1 e1;
      do (e2, loc2) <- elab_exp ae2;
      do (ty2, sck2) <- single_annot loc2 e2;
      do ty' <- find_type_binop loc op ty1 ty2;
      do _ <- unify_sclock tenv loc sck1 sck2;
      ret (Ebinop op e1 e2 (ty', sck1), loc)
    | BINARY _ _ _ loc => err_not_singleton loc

    | FBY ae0s aes loc =>
      do e0s <- mmap elab_exp ae0s;
      do es <- mmap elab_exp aes;
      let ans0 := lannots e0s in
      do _ <- unify_paired_clock_types loc ans0 (lannots es);
      do ans0 <- mmap update_ann (map discardloc ans0);
      ret (Efby (map fst e0s) (map fst es) ans0, loc)

    | ARROW ae0s aes loc =>
      do e0s <- mmap elab_exp ae0s;
      do es <- mmap elab_exp aes;
      let ans0 := lannots e0s in
      do _ <- unify_paired_clock_types loc ans0 (lannots es);
      do ans0 <- mmap update_ann (map discardloc ans0);
      ret (Earrow (map fst e0s) (map fst es) ans0, loc)

    | WHEN aes' x c loc =>
      do (xty, xck) <- find_var loc x;
      do (c, tn') <- elab_enum loc c;
      do eas' <- mmap elab_exp aes';
      let ans' := lannots eas' in
      do _ <- unify_same_clock xck ans';
      ret (Ewhen (map fst eas') (x, xty) c
                 (lannots_ty ans', Son xck (Vnm x) (Tenum (fst tn') (snd tn'), c)), loc)

    | MERGE x aes loc =>
      do (xty, sck) <- find_var loc x;
      do tn <- assert_enum_type loc x xty;
      do (eas, tys) <- elab_branches loc tn true elab_exp (fun c => Son sck (Vnm x) (xty, c))
                                    aes;
      ret (Emerge (x, Tenum (fst tn) (snd tn)) eas (lannots_ty tys, sck), loc)

    | CASE [ae] aes [] loc =>
      do (e, eloc) <- elab_exp ae;
      do (ety, eck) <- single_annot eloc e;
      do tn <- assert_enum_type' loc ety;
      do (eas, anns) <- elab_branches loc tn true elab_exp (fun _ => eck) aes;
      let tys := lannots_ty anns in
      ret (Ecase e eas None (tys, eck), loc)
    | CASE [ae] aes des loc =>
      do (e, eloc) <- elab_exp ae;
      do (ety, eck) <- single_annot eloc e;
      do tn <- assert_enum_type' loc ety;
      do (eas, anns) <- elab_branches loc tn false elab_exp (fun _ => eck) aes;
      do deas <- mmap elab_exp des;
      do _ <- unify_paired_types loc anns (lannots deas);
      let tys := lannots_ty anns in
      ret (Ecase e eas (Some (map fst deas)) (tys, eck), loc)
    | CASE _ _ _ loc => err_not_singleton loc

    | APP f aes aer loc =>
      (* elaborate arguments *)
      do eas <- mmap elab_exp aes;
      (* node interface *)
      do interface <- find_node_interface loc f;
      match interface with
      | Internal tyck_in tyck_out =>
          (* elaborate reset and check it has boolean type *)
          do er <- mmap elab_exp aer;
          do _ <- mmap assert_reset_type er;
          (* instantiate annotations *)
          do sub <- instantiating_subst (tyck_in(* ++tyck_out *));
          do xbase <- fresh_ident;
          do ianns <- mmap (inst_nannot loc (Svar xbase) sub) tyck_in;
          do oanns <- mmap (inst_annot loc (Svar xbase) sub) tyck_out;
          let nanns := lnannots eas in
          do _ <- unify_inputs loc ianns nanns;
          ret (Eapp f (map fst eas) (map fst er) oanns, loc)
      | External tyins tyout =>
          do _ <- check_noreset loc aer;
          let anns := lannots eas in
          do xck <- hd_sclock loc anns;
          do _ <- assert_types loc (map Tprimitive tyins) (map (fun '(ty, _, _) => ty) anns);
          do _ <- unify_same_clock xck anns;
          ret (Eextcall f (map fst eas) (tyout, xck), loc)
      end
    end.

  Definition freeze_ident (sid : sident) : Elab ident :=
    do sid <- update_sident sid;
    match sid with
    | Vnm x => ret x
    | Vidx x => error (MSG "Variable " :: CTX x :: MSG " escapes its scope" :: nil)
    end.

  Definition freeze_clock (sck : sclock) : Elab clock :=
    do sck <- update_sclock sck;
    ret (sclk' sck).

  Definition freeze_ann (tc : ann) : Elab Syn.ann :=
    let '(ty, nck) := tc in
    do nck <- freeze_clock nck;
    ret (ty, nck).

  (* Add [when]s around [e], assumed to be on the base clock, so that it *)
  (* has the given clock [ck]. *)
  Fixpoint add_whens (e: Syn.exp) (tys: list type) (ck: clock) : Elab Syn.exp :=
    match ck with
    | Cbase => ret e
    | Con ck' x (tx, k) =>
      do e' <- add_whens e tys ck';
      if Env.mem x env then ret (Syn.Ewhen [e'] (x, tx) k (tys, ck))
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

    | Elast x ann =>
      do ann' <- freeze_ann ann;
      ret (Syn.Elast x ann')

    | Eunop unop e ann =>
      do e' <- freeze_exp e;
      do ann' <- freeze_ann ann;
      ret (Syn.Eunop unop e' ann')

    | Ebinop binop e1 e2 ann =>
      do e1' <- freeze_exp e1;
      do e2' <- freeze_exp e2;
      do ann' <- freeze_ann ann;
      ret (Syn.Ebinop binop e1' e2' ann')

    | Eextcall f es (cty, ck) =>
      do es' <- freeze_exps es;
      do ck' <- freeze_clock ck;
      ret (Syn.Eextcall f es' (cty, ck'))

    | Efby e0s es anns =>
      do e0s <- freeze_exps e0s;
      do es <- freeze_exps es;
      do anns <- mmap freeze_ann anns;
      ret (Syn.Efby e0s es anns)

    | Earrow e0s es anns =>
      do e0s <- freeze_exps e0s;
      do es <- freeze_exps es;
      do anns <- mmap freeze_ann anns;
      ret (Syn.Earrow e0s es anns)

    | Ewhen es (ckid, tx) b (tys, nck) =>
      do es <- freeze_exps es;
      do nck <- freeze_clock nck;
      ret (Syn.Ewhen es (ckid, tx) b (tys, nck))

    | Emerge ckid es (tys, nck) =>
      do es <- mmap (fun '(i, es) => do es' <- freeze_exps es; ret (i, es')) es;
      do nck <- freeze_clock nck;
      ret (Syn.Emerge ckid es (tys, nck))

    | Ecase e es d (tys, nck) =>
      do e <- freeze_exp e;
      do es <- mmap (fun '(i, es) => do es' <- freeze_exps es; ret (i, es')) es;
      do d <- or_default_with (ret None) (fun d => do d' <- freeze_exps d; ret (Some d')) d;
      do nck <- freeze_clock nck;
      ret (Syn.Ecase e es d (tys, nck))

    | Eapp f es er anns =>
      do es <- freeze_exps es;
      do er <- freeze_exps er;
      do anns <- mmap freeze_ann anns;
      ret (Syn.Eapp f es er anns)
    end.

  Fixpoint unify_pat (gloc: astloc)
                     (xs: list ident)
                     (anns: list ((type * sclock) * astloc)) : Elab unit :=
    match xs, anns with
    | nil, nil => ret tt
    | x::xs', ((ty, ck), loc)::anns' =>
      do (xty, xck) <- find_var loc x;
      do _ <- assert_id_type loc x xty ty;
      do _ <- unify_sclock tenv loc xck ck;
      unify_pat gloc xs' anns'
    | nil, _ => err_loc gloc (msg "too few variables on lhs of equation.")
    | _, nil => err_loc gloc (msg "too many variables on lhs of equation.")
    end.

  Fixpoint unify_npat (gloc: astloc)
                     (xs: list ident)
                     (anns: list ((type * nsclock))) : Elab unit :=
    match xs, anns with
    | nil, nil => ret tt
    | x::xs', ((ty, ck))::anns' =>
      do (xty, xck) <- find_var gloc x;
      do _ <- assert_id_type gloc x xty ty;
      do _ <- unify_nclock tenv gloc x xck ck;
      unify_npat gloc xs' anns'
    | nil, _ => err_loc gloc (msg "too few variables on lhs of equation.")
    | _, nil => err_loc gloc (msg "too many variables on lhs of equation.")
    end.

  Definition elab_equation (aeq : LustreAst.equation) : Elab Syn.equation :=
    let '((xs, es), loc) := aeq in
    match es with
    | [APP f aes aer loc] (* special app case, possibly with dependency in outputs *) =>
      (* node interface *)
      do interface <- find_node_interface loc f;
      match interface with
      | Internal tyck_in tyck_out =>
          (* elaborate arguments *)
          do eas <- mmap elab_exp aes;
          (* elaborate reset and check it has boolean type *)
          do er <- mmap elab_exp aer;
          do _ <- mmap assert_reset_type er;
          (* instantiate annotations *)
          let anns := lnannots eas in
          do sub <- instantiating_subst (tyck_in++tyck_out);
          do xbase <- fresh_ident;
          do ianns <- mmap (inst_nannot loc (Svar xbase) sub) tyck_in;
          do oanns <- mmap (inst_nannot loc (Svar xbase) sub) tyck_out;
          do _ <- unify_inputs loc ianns anns;
          do _ <- unify_npat loc xs oanns;
          (* freeze everything *)

          do e' <- freeze_exp (Eapp f (map fst eas) (map fst er) (map discardname oanns));
          ret (xs, [e'])
      | _ =>
          do es' <- mmap elab_exp es;
          do _ <- unify_pat loc xs (lannots es');
          do es' <- mmap freeze_exp (map fst es');
          ret (xs, es')
      end
    | _ (* general case *) =>
        do es' <- mmap elab_exp es;
        do _ <- unify_pat loc xs (lannots es');
        do es' <- mmap freeze_exp (map fst es');
        ret (xs, es')
    end.

End ElabExpressions.

Section ElabVarDecls.

  Definition err_incoherent_clock (loc: astloc) (x: ident) : Elab unit :=
    err_loc loc (MSG "The declared clock of " :: CTX x
                     :: msg " is incoherent with the other declarations").

  Variable tenv : Env.t (list ident).
  Variable extenv : Env.t (list ctype * ctype).

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
           (acc: Env.t (type * clock * bool)
                 * list (ident * (type_name * preclock * list expression * astloc)))
           (vds: list (ident * (type_name * preclock * list expression * astloc)))
    : Elab (Env.t (type * clock * bool)
           * list (ident * (type_name * preclock * list expression * astloc))) :=
    match vds with
    | [] => ret acc
    | (x, (sty, pck, e, loc)) as vd :: vds =>
      let (env, notdone) := acc in
        match pck with
        | FULLCK BASE =>
          if Env.mem x env
          then err_loc loc (CTX x :: msg " is declared more than once")
          else
            do ty <- elab_type tenv loc sty;
            elab_var_decls_pass (Env.add x (ty, Cbase, negb (is_nil e)) env, notdone) vds

        | FULLCK (ON cy' y c) =>
          match Env.find y env with
          | None => elab_var_decls_pass (env, vd :: notdone) vds
          | Some (yt, cy, _) =>
            if Env.mem x env
            then err_loc loc (CTX x :: msg " is declared more than once")
            else do _ <- assert_enum_type loc y yt;
                 do _ <- assert_preclock loc x cy' cy;
                 do (c', tn') <- elab_enum tenv loc c;
                 do _ <- assert_id_type loc y yt (Tenum (fst tn') (snd tn'));
                 do ty <- elab_type tenv loc sty;
                 elab_var_decls_pass (Env.add x (ty, Con cy y (yt, c'), negb (is_nil e)) env, notdone) vds
          end

        | WHENCK y c =>
          match Env.find y env with
          | None => elab_var_decls_pass (env, vd :: notdone) vds
          | Some (yt, cy, _) =>
            if Env.mem x env
            then err_loc loc (CTX x :: msg " is declared more than once")
            else do _ <- assert_enum_type loc y yt;
                 do (c', tn') <- elab_enum tenv loc c;
                 do _ <- assert_id_type loc y yt (Tenum (fst tn') (snd tn'));
                 do ty <- elab_type tenv loc sty;
                 elab_var_decls_pass
                   (Env.add x (ty, Con cy y (yt, c'), negb (is_nil e)) env, notdone) vds
          end
        end
    end.

  Fixpoint elab_var_decls' {A: Type}
           (loc : astloc)
           (fuel: list A)
           (env : Env.t (type * clock * bool))
           (vds : list (ident * (type_name * preclock * list expression * astloc)))
    : Elab (Env.t (type * clock * bool)) :=
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
             (env: Env.t (type * clock * bool))
             (vds: list (ident * (type_name * preclock * list expression * astloc)))
    : Elab (Env.t (type * clock * bool)) :=
    elab_var_decls' loc vds env vds.

  Definition annotate nenv (env: Env.t (type * clock * bool))
             (vd: ident * (type_name * preclock * list expression * astloc)) :
    Elab (ident * (type * clock * ident * option (exp * ident))) :=
    let '(x, (sty, pck, es, loc)) := vd in
    do cx <- fresh_ident;
    match Env.find x env with
    | None => error (msg "internal error (annotate)")
    | Some (ty, ck, _) =>
        match es with
        | [] => ret (x, (ty, ck, cx, None))
        | [ae] =>
            do (e, eloc) <- elab_exp env tenv extenv nenv ae;
            do (ety, eck) <- single_annot eloc e;
            do _ <- assert_id_type loc x ty ety;
            do _ <- unify_sclock tenv loc (sclk ck) eck;
            do e <- freeze_exp env e;
            do xcl <- fresh_ident;
            ret (x, (ty, ck, cx, Some (e, xcl)))
        | _ => err_not_singleton loc
        end
    end.

End ElabVarDecls.

Section AtomOrGensym.

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

  Corollary mmap_check_atom_AtomOrGensym : forall loc xs st res,
      mmap (check_atom loc) xs st = OK res ->
      Forall (AtomOrGensym elab_prefs) xs.
  Proof.
    induction xs; intros * Hmap; repeat monadInv; constructor; eauto.
    left. eapply check_atom_spec; eauto.
  Qed.

End AtomOrGensym.

Section ElabBlock.

  Variable tenv : Env.t (list ident).
  Variable extenv : Env.t (list ctype * ctype).
  Variable nenv : Env.t (list (ident * (type * clock)) * list (ident * (type * clock))).

  Fixpoint vars_defined (d : LustreAst.block) :=
    match d with
    | BEQ (xs, _, _) => ps_from_list xs
    | BRESET blocks _ _ => PSUnion (map vars_defined blocks)
    | BSWITCH _ branches _ =>
        PSUnion (map (fun '(_, blks) => PSUnion (map vars_defined blks)) branches)
    | BAUTO _ states _ =>
        PSUnion (map (fun '(_, (locs, blks, _, _)) =>
                        let locs := ps_from_list (map fst locs) in
                        PS.filter (fun x => negb (PS.mem x locs)) (PSUnion (map vars_defined blks))) states)
    | BLOCAL locs blks _ =>
        let locs := ps_from_list (map fst locs) in
        PS.filter (fun x => negb (PS.mem x locs)) (PSUnion (map vars_defined blks))
    end.

  Definition find_a_clock (tenv : Env.t (type * clock * bool)) (xs : PS.t) :=
    match (PS.choose xs) with
    | None => Cbase
    | Some x => or_default_with Cbase (fun '(_, ck, _) => ck) (Env.find x tenv)
    end.

  Definition find_a_clock_of_defined tenv (ab : LustreAst.block) :=
    find_a_clock tenv (vars_defined ab).

  Definition elab_transition_cond env nenv (es : list expression) loc :=
    match es with
    | [e] => do (e, _) <- elab_exp env tenv extenv nenv e;
            do (ety, eck) <- single_annot loc e;
            do ety <- assert_type' loc ety bool_type;
            do _ <- unify_sclock tenv loc eck Sbase;
            do e <- freeze_exp env e;
            ret e
    | _ => err_not_singleton loc
    end.

  Fixpoint elab_block env (ab : LustreAst.block) : Elab Syn.block :=
    match ab with
    | BEQ aeq =>
        do eq <- elab_equation env tenv extenv nenv aeq;
        ret (Beq eq)
    | BRESET ablks [aer] _ =>
        do blks <- mmap (elab_block env) ablks;
        do (er, loc) <- elab_exp env tenv extenv nenv aer;
        do _ <- assert_reset_type (er, loc);
        do er <- freeze_exp env er;
        ret (Breset blks er)
    | BRESET _ _ loc => err_not_singleton loc
    | BSWITCH [aec] abrs loc =>
        do (ec, eloc) <- elab_exp env tenv extenv nenv aec;
        do (ety, eck) <- single_annot eloc ec;
        do ec <- freeze_exp env ec;
        do tn <- assert_enum_type' loc ety;
        let ck := List.hd Cbase (clockof ec) in
        let env := Env.map (fun '(ty, _, b) => (ty, Cbase, b)) (Env.Props.P.filter (fun _ '(_, ck', _) => ck ==b ck') env) in
        let xs := vars_defined ab in
        do brs <- mmap (fun '(c, ablks) =>
                         do (c, tn') <- elab_enum tenv loc c;
                         do _ <- assert_type' loc (Tenum (fst tn) (snd tn)) (Tenum (fst tn') (snd tn'));
                         do blks <- mmap (elab_block env) ablks;
                         do caus <- mmap (fun x => do cx <- fresh_ident; ret (x, cx)) (PSP.to_list xs);
                         ret (c, Scope [] caus blks)) abrs;
        let cs := fst (split brs) in
        do _ <- check_duplicates loc cs;
        do _ <- check_exhaustivity loc (length (snd tn)) cs;
        ret (Bswitch ec brs)
    | BAUTO (ini, oth) states loc =>
        let ck := find_a_clock_of_defined env (BAUTO (ini, oth) states loc) in
        let env := Env.map (fun '(ty, _, b) => (ty, Cbase, b)) (Env.Props.P.filter (fun _ '(_, ck', _) => ck ==b ck') env) in
        let tenv' := Env.add xH (List.map fst states) (@Env.empty _) in
        let xs := vars_defined ab in
        do (oth, _) <- elab_enum tenv' loc oth;
        do ini <- mmap (fun '(e, t, loc) =>
                         do (t, _) <- elab_enum tenv' loc t;
                         do e <- elab_transition_cond env nenv e loc;
                         ret (e, t)) ini;
        do states <- mmap (fun '(constr, (locs, ablks, unt, unl)) =>
                            do (t, _) <- elab_enum tenv' loc constr;
                            do env <- elab_var_decls tenv loc env locs;
                            do locs <- mmap (annotate tenv extenv nenv env) locs;
                            do _ <- mmap (check_atom loc) (map fst locs);
                            do blks <- mmap (elab_block env) ablks;
                            do unt <- mmap (fun '(e, (t, b), loc) =>
                                             do (t, _) <- elab_enum tenv' loc t;
                                             do e <- elab_transition_cond env nenv e loc;
                                             ret (e, (t, b))) unt;
                            do unl <- mmap (fun '(e, (t, b), loc) =>
                                             do (t, _) <- elab_enum tenv' loc t;
                                             do e <- elab_transition_cond env nenv e loc;
                                             ret (e, (t, b))) unl;
                            do caus <- mmap (fun x => do cx <- fresh_ident; ret (x, cx)) (PSP.to_list xs);
                            ret ((t, constr), (unl, (Scope locs caus (blks, unt))))
                      ) states;
        do type <-
             if forallb (fun '(_, (unl, _)) => is_nil unl) states then ret Weak
             else if is_nil ini && forallb (fun '(_, (_, Scope _ _ (_, unt))) => is_nil unt) states then ret Strong
                  else err_loc loc (msg "Strong and Weak transitions cannot be mixed in the same state-machine");
        ret (Bauto type ck (ini, oth) states)
    | BSWITCH _ _ loc => err_not_singleton loc
    | BLOCAL locs ablks loc =>
        do env <- elab_var_decls tenv loc env locs;
        do locs <- mmap (annotate tenv extenv nenv env) locs;
        do _ <- mmap (check_atom loc) (map fst locs);
        do blks <- mmap (elab_block env) ablks;
        ret (Blocal (Scope locs [] blks))
    end.

End ElabBlock.

Section ElabDeclaration.

  (* Map type names to their constructors *)
  Variable tenv: Env.t (list ident).

  (* External functions *)
  Variable extenv: Env.t (list ctype * ctype).

  (* Map node names to input and output types and clocks. *)
  Variable nenv : Env.t (list (ident * (type * clock))
                        * list (ident * (type * clock))).

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

  Fixpoint find_dup (xs : list ident) :=
    match xs with
    | [] => xH
    | x::xs => if mem_ident x xs then x
             else find_dup xs
    end.

  Definition check_nodup loc (xs : list ident) :=
    if check_nodup xs
    then ret tt
    else err_loc loc (MSG "Duplicate declaration of " :: CTX (find_dup xs) :: msg "").

  Lemma check_nodup_spec : forall loc xs st st',
      check_nodup loc xs st = OK (tt, st') ->
      NoDup xs.
  Proof.
    intros * Hcheck.
    unfold check_nodup in Hcheck.
    destruct (Common.check_nodup _) eqn:Hndup. 2:inv Hcheck.
    apply check_nodup_correct in Hndup; auto.
  Qed.

  Definition check_nointersect loc (xs1 xs2 : PS.t) :=
    if PS.for_all (fun x => negb (PS.mem x xs2)) xs1 then ret tt
    else err_loc loc (msg "Duplicate local var").

  Lemma check_nointersect_spec : forall loc xs1 xs2 st st',
      check_nointersect loc xs1 xs2 st = OK (tt, st') ->
      forall x, PS.In x xs1 -> ~PS.In x xs2.
  Proof.
    intros * Hcheck. unfold check_nointersect in Hcheck.
    cases_eqn Hf.
    eapply PS.for_all_spec in Hf. 2:intros ?? Heq; now rewrite Heq.
    intros ? Hin.
    eapply Hf, Bool.negb_true_iff, PSE.mem_4 in Hin; eauto.
  Qed.

  Definition check_nodupscope {A} (f_nd: _ -> _ -> Elab (list unit)) loc (env : PS.t) (s : scope A) :=
    let 'Scope locs caus blk := s in
    do _ <- check_nodup loc (map fst locs);
    do _ <- check_nodup loc (map fst caus);
    let locsanon := nameset PS.empty locs in
    do _ <- check_nointersect loc env locsanon;
    do _ <- f_nd (PS.union env locsanon) blk;
    ret tt.

  Fixpoint check_noduplocals loc (env : PS.t) (blk : block) :=
    match blk with
    | Beq _ => ret tt
    | Breset blks _ =>
      do _ <- mmap (check_noduplocals loc env) blks;
      ret tt
    | Bswitch _ branches =>
        do _ <- mmap (fun '(_, s) =>
                       check_nodupscope (fun env => mmap (check_noduplocals loc env)) loc env s)
                    branches;
        ret tt
    | Bauto _ _ _ states =>
        do _ <- mmap (fun '(_, (_, s)) =>
                       check_nodupscope (fun env '(blks, _) => mmap (check_noduplocals loc env) blks)
                                        loc env s) states;
      ret tt
    | Blocal s => check_nodupscope (fun env => mmap (check_noduplocals loc env)) loc env s
    end.

  Fact check_nodupscope_spec {A} f_nd (P_nd: _ -> _ -> Prop) : forall env xs loc locs caus (blk: A) st res,
      (forall x, In x xs -> PS.In x env) ->
      check_nodupscope f_nd loc env (Scope locs caus blk) st = OK res ->
      (forall xs env st res,
          (forall x, In x xs -> PS.In x env) ->
          f_nd env blk st = OK res ->
          P_nd xs blk) ->
      NoDupScope P_nd xs (Scope locs caus blk).
  Proof.
    intros * Henv Hc; repeat monadInv.
    constructor.
    + eapply H in Hbind2; eauto.
      intros * Hin. rewrite PS.union_spec, nameset_spec.
      repeat rewrite in_app_iff in Hin. destruct Hin as [?|?]; eauto.
    + destruct x. apply check_nodup_spec in Hbind; auto.
      now apply fst_NoDupMembers.
    + intros ? Hin1 Hin2.
      destruct x3. eapply check_nointersect_spec in Hbind0. 2:eapply Henv; eauto.
      eapply Hbind0. repeat rewrite nameset_spec.
      repeat rewrite fst_InMembers in Hin1; auto.
    + destruct x1. apply check_nodup_spec in Hbind1; auto.
      now apply fst_NoDupMembers.
  Qed.

  Lemma check_noduplocals_spec loc : forall blk xs env st res,
      (forall x, In x xs -> PS.In x env) ->
      check_noduplocals loc env blk st = OK res ->
      NoDupLocals xs blk.
  Proof.
    Opaque check_nodupscope.
    induction blk using block_ind2; intros * Henv Hc; simpl in *; repeat monadInv.
    - (* equation *)
      constructor.
    - (* reset *)
      constructor.
      apply mmap_values, Forall2_ignore2 in Hbind. simpl_Forall; eauto.
    - (* switch *)
      constructor.
      apply mmap_values, Forall2_ignore2 in Hbind. simpl_Forall; eauto.
      destruct s. eapply check_nodupscope_spec; eauto. intros; simpl in *.
      destruct res. apply mmap_values, Forall2_ignore2 in H4. simpl_Forall; eauto.
    - (* automaton *)
      constructor.
      apply mmap_values, Forall2_ignore2 in Hbind. simpl_Forall; eauto.
      destruct s; destruct_conjs. eapply check_nodupscope_spec; eauto. intros; simpl in *.
      destruct res. apply mmap_values, Forall2_ignore2 in H4. simpl_Forall; eauto.
    - (* local *)
      constructor.
      eapply check_nodupscope_spec; eauto. intros; simpl in *.
      destruct res0. apply mmap_values, Forall2_ignore2 in H1. simpl_Forall; eauto.
  Qed.

  Definition msg_of_missing_variables (exp def : PS.t) :=
    match (PS.elements (PS.diff exp def)) with
    | x::_ => (CTX x :: msg " is not defined")
    | _ => match (PS.elements (PS.diff def exp)) with
          | x::_ => (CTX x :: msg " shouldn't be defined")
          | _ => msg "Missing or too many variables defined"
          end
    end.

  Definition check_defined_vars (loc: astloc) (exp def : list ident) : Elab unit :=
    if Common.check_nodup def then
      let exp := ps_from_list exp in
      let def := ps_from_list def in
      if PS.equal exp def then ret tt
      else err_loc loc (msg_of_missing_variables exp def)
    else err_loc loc (MSG "Duplicate definition of " :: CTX (find_dup def) :: msg "").

  Lemma check_defined_vars_spec loc : forall exp def st res,
      NoDup exp ->
      check_defined_vars loc exp def st = OK res ->
      Permutation exp def.
  Proof.
    unfold check_defined_vars.
    intros * Hnd Hc. cases_eqn Heq; repeat monadInv.
    apply check_nodup_correct in Heq.
    apply PSF.equal_2, PS_elements_Equal in Heq0.
    unfold ps_from_list in Heq0. rewrite 2 Permutation_PS_elements_ps_adds in Heq0; auto.
    2,3:rewrite Forall_forall; intros; eapply not_In_empty.
    rewrite PSP.elements_empty, 2 app_nil_r in Heq0; auto.
  Qed.

  Definition check_defined_local (loc: astloc) (locals : list ident) (xs : list ident) : Elab (list ident) :=
    let (locals', ys) := partition (fun x => existsb (ident_eqb x) locals) xs in
    do _ <- check_defined_vars loc locals locals';
    ret ys.

  Lemma check_defined_local_spec loc : forall locals xs ys st st',
      NoDup locals ->
      check_defined_local loc locals xs st = OK (ys, st') ->
      Permutation (locals ++ ys) xs.
  Proof.
    intros * Hnd2 Hc. unfold check_defined_local in Hc.
    cases_eqn Hf; repeat monadInv.
    eapply partition_Partition, Partition_Permutation in Hf.
    eapply check_defined_vars_spec in Hbind; eauto.
    now rewrite Hf, Hbind.
  Qed.

  Definition check_incl loc xs ys : Elab unit :=
    let ys := ps_from_list ys in
    if forallb (fun x => PS.mem x ys) xs then ret tt
    else err_loc loc (msg_of_missing_variables ys (ps_from_list xs)).

  Lemma check_incl_spec loc : forall xs ys st st',
      check_incl loc xs ys st = OK (tt, st') ->
      incl xs ys.
  Proof.
    unfold check_incl.
    intros * Hc; simpl in *. cases_eqn Eq.
    apply forallb_Forall in Eq. intros ??; simpl_Forall.
    apply PSF.mem_2, ps_from_list_In in Eq; auto.
  Qed.

  Definition check_defined_scope {A} f_nd loc (s : scope A) : Elab (list ident) :=
    let 'Scope locs caus blk := s in
    do xs <- f_nd blk;
    do xs <- check_defined_local loc (map fst locs) (concat xs);
    do _ <- check_incl loc (map fst caus) xs;
    ret xs.

  Fixpoint check_defined_block (loc: astloc) (blk: block) : Elab (list ident) :=
    match blk with
    | Beq (xs, _) => ret xs
    | Breset blks _ =>
      do xs <- mmap (check_defined_block loc) blks;
      ret (concat xs)
    | Bswitch _ [] => err_loc loc (msg "switches should have at least one branch")
    | Bswitch _ (hd::tl) =>
      do xs <- check_defined_scope (mmap (check_defined_block loc)) loc (snd hd);
      do _ <- check_nodup loc xs;
      do _ <- mmap (fun blks => do xs' <- check_defined_scope (mmap (check_defined_block loc)) loc (snd blks);
                            check_defined_vars loc xs xs') tl;
      ret xs
    | Bauto _ _ _ [] => err_loc loc (msg "state machines should have at least one branch")
    | Bauto _ _ _ ((_, (_, hd))::tl) =>
      do xs <- check_defined_scope (fun '(blks, _) => mmap (check_defined_block loc) blks) loc hd;
      do _ <- check_nodup loc xs;
      do _ <- mmap (fun '(_, (_, blks)) => do xs' <- check_defined_scope (fun '(blks, _) => mmap (check_defined_block loc) blks) loc blks;
                            check_defined_vars loc xs xs') tl;
      ret xs
    | Blocal s => check_defined_scope (mmap (check_defined_block loc)) loc s
    end.


  Fact check_defined_scope_spec {A} f_nd P_nd (P_vd: _ -> _ -> Prop) : forall env xs loc locs caus (blk: A) st st',
      NoDupScope P_nd env (Scope locs caus blk) ->
      check_defined_scope f_nd loc (Scope locs caus blk) st = OK (xs, st') ->
      (forall xs ys, Permutation xs ys -> P_vd blk xs -> P_vd blk ys) ->
      (forall env xs st st',
          P_nd env blk ->
          f_nd blk st = OK (xs, st') ->
          P_vd blk (concat xs)) ->
      VarsDefinedScope P_vd (Scope locs caus blk) xs.
  Proof.
    intros * Hnd Hc Hperm Hind; inv Hnd; repeat monadInv.
    apply check_defined_local_spec in Hbind1; [|now apply fst_NoDupMembers].
    destruct x3. apply check_incl_spec in Hbind0.
    constructor; auto.
    eapply Hind in Hbind; eauto.
    eapply Hperm; [|eauto].
    rewrite <-Hbind1. apply Permutation_app_comm.
  Qed.

  Lemma check_defined_blocks_spec loc : forall blks env xs st st',
      Forall (fun blk => forall env xs st st',
                  NoDupLocals env blk ->
                  check_defined_block loc blk st = OK (xs, st') ->
                  VarsDefined blk xs) blks ->
      Forall (NoDupLocals env) blks ->
      mmap (check_defined_block loc) blks st = OK (xs, st') ->
      Forall2 VarsDefined blks xs.
  Proof.
    induction blks; intros * Hf Hnd Hmmap; inv Hf; inv Hnd;
      repeat monadInv; constructor; eauto.
  Qed.

  Lemma check_defined_block_spec loc : forall blk env xs st st',
      NoDupLocals env blk ->
      check_defined_block loc blk st = OK (xs, st') ->
      VarsDefined blk xs.
  Proof.
    Opaque check_defined_scope.
    induction blk as [(?&?)| | | |] using block_ind2;
      intros * Hnd Hc; inv Hnd; repeat monadInv.
    - (* equation *)
      econstructor.
    - (* reset *)
      econstructor.
      apply mmap_values in Hbind. simpl_Forall; eauto.
    - (* switch *)
      simpl in *. cases. repeat monadInv. inv H. inv H2.
      repeat constructor.
      + congruence.
      + destruct p as [?[]]. eapply check_defined_scope_spec; eauto.
        * intros; inv_VarsDefined. do 2 esplit; [eauto|]. now rewrite Hperm.
        * intros. do 2 esplit; [|reflexivity].
          eapply check_defined_blocks_spec in H; eauto.
      + take unit and destruct it. take (check_nodup _ _ _ = _) and apply check_nodup_spec in it as Hnd.
        clear - Hnd Hbind0 H4 H5. revert x2 x3 st' Hbind0.
        induction H4; intros * Hbind; inv H5; repeat monadInv; constructor; eauto.
        eapply check_defined_vars_spec in Hbind2; eauto.
        destruct x as [?[]]. eapply check_defined_scope_spec in Hbind1; eauto.
        * eapply VarsDefinedScope_Perm1; [|eauto]. now symmetry.
        * intros; simpl in *; inv_VarsDefined.
          do 2 esplit; eauto. now rewrite Hperm.
        * intros; simpl in *. do 2 esplit; [|reflexivity].
          eapply check_defined_blocks_spec; eauto.
    - (* automaton *)
      simpl in *. cases. repeat monadInv. inv H. inv H2.
      repeat constructor.
      + congruence.
      + destruct s; destruct_conjs. eapply check_defined_scope_spec; eauto.
        * intros; inv_VarsDefined. do 2 esplit; [eauto|]. now rewrite Hperm.
        * intros; simpl in *. do 2 esplit; [|reflexivity].
          eapply check_defined_blocks_spec in H0; eauto.
      + take unit and destruct it. take (check_nodup _ _ _ = _) and apply check_nodup_spec in it as Hnd.
        clear - Hnd Hbind0 H4 H5. revert x2 x3 st' Hbind0.
        induction H4; intros * Hbind; inv H5; repeat monadInv; constructor; eauto.
        destruct x as [(?&?)[]]; repeat monadInv. eapply check_defined_vars_spec in Hbind2; eauto.
        destruct s. eapply check_defined_scope_spec in Hbind1; eauto.
        * eapply VarsDefinedScope_Perm2; [|eauto]. now symmetry.
        * intros; simpl in *; inv_VarsDefined.
          do 2 esplit; eauto. now rewrite Hperm.
        * intros; simpl in *. destruct p. do 2 esplit; [|reflexivity].
          eapply check_defined_blocks_spec; eauto.
    - (* local *)
      constructor; simpl in *; repeat monadInv.
      eapply check_defined_scope_spec; eauto.
      + intros; inv_VarsDefined. do 2 esplit; [eauto|].
        now rewrite Hperm.
      + intros; simpl in *. do 2 esplit; [|reflexivity].
        eapply check_defined_blocks_spec in H; eauto.
  Qed.

  Local Ltac destruct_to_singl l :=
    destruct l; [|destruct l]; auto.

  Lemma elab_block_GoodLocals : forall ablk env blk st st',
      elab_block tenv extenv nenv env ablk st = OK (blk, st') ->
      GoodLocals elab_prefs blk.
  Proof.
    induction ablk using LustreAst.block_ind2;
      intros * Helab; simpl in *; repeat monadInv.
    - (* equation *)
      constructor.
    - (* reset *)
      cases. repeat monadInv.
      constructor.
      apply mmap_values, Forall2_ignore1 in Hbind. simpl_Forall; eauto.
    - (* switch *)
      cases. repeat monadInv.
      constructor.
      apply mmap_values, Forall2_ignore1 in Hbind3. simpl_Forall; repeat monadInv.
      repeat constructor. apply mmap_values, Forall2_ignore1 in Hbind6. simpl_Forall; eauto.
    - (* automaton *)
      cases. repeat monadInv.
      constructor.
      apply mmap_values, Forall2_ignore1 in Hbind0. simpl_Forall; repeat monadInv.
      repeat constructor.
      + eapply mmap_check_atom_AtomOrGensym; eauto.
      + apply mmap_values, Forall2_ignore1 in Hbind6. simpl_Forall; eauto.
    - (* local *)
      repeat constructor.
      + eapply mmap_check_atom_AtomOrGensym; eauto.
      + apply mmap_values, Forall2_ignore1 in Hbind2. simpl_Forall; eauto.
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

  Definition add_no_last (xs : var_decls) : local_decls :=
    List.map (fun '(x, (ty, ck, loc)) => (x, (ty, ck, [], loc))) xs.

  Program Definition elab_declaration_node
          (name: ident) (has_state: bool) (inputs outputs : var_decls)
          (blk: LustreAst.block) (loc: astloc) : res (@node (fun _ => True) elab_prefs) :=
    let inputs := add_no_last inputs in
    let outputs := add_no_last outputs in
    match (do env_in  <- elab_var_decls tenv loc (Env.empty _) inputs;
           do env <- elab_var_decls tenv loc env_in outputs;
           do xin     <- mmap (annotate tenv extenv nenv env) inputs;
           do xout    <- mmap (annotate tenv extenv nenv env) outputs;
           do blk     <- elab_block tenv extenv nenv env blk;
           (* TODO better error messages *)
           do _       <- check_nodup loc (map fst (xin++xout));
           do _       <- check_noduplocals loc (nameset (nameset PS.empty xin) xout) blk;
           do defs    <- check_defined_block loc blk;
           do _       <- check_nodup loc defs;
           do _       <- check_defined_vars loc defs (map fst xout);
           do _       <- check_atom loc name;
           do _       <- mmap (check_atom loc) (map fst (xin ++ xout));
           if (length xin ==b O) || (length xout ==b O)
           then err_loc loc (msg "not enough inputs or outputs")
           else ret (xin, xout, blk)) init_state with
    | Error e => Error e
    | OK ((xin, xout, blk), ((nfui, _), _)) =>
      OK {| n_name     := name;
            n_hasstate := has_state;
            n_in       := idty xin;
            n_out      := idty xout;
            n_block    := blk |}
    end.
  Next Obligation.
    (* 0 < length xin *)
    rewrite Bool.orb_false_iff in Hb; destruct Hb as (Hin & Hout).
    apply not_equiv_decb_equiv in Hin.
    setoid_rewrite map_length.
    now apply Nat.neq_0_lt_0 in Hin.
  Qed.
  Next Obligation.
    (* 0 < length xout *)
    rewrite Bool.orb_false_iff in Hb; destruct Hb as (Hin & Hout).
    apply not_equiv_decb_equiv in Hout.
    setoid_rewrite map_length.
    now apply Nat.neq_0_lt_0 in Hout.
  Qed.
  Next Obligation.
    eapply check_defined_block_spec in Hbind6.
    2:{ eapply check_noduplocals_spec in Hbind5; eauto.
        instantiate (1:=[]). intros ? Hin. inv Hin. }
    eapply check_defined_vars_spec in Hbind8; eauto using check_nodup_spec.
    rewrite map_fst_idty; eauto.
  Qed.
  Next Obligation.
    split.
    - apply check_nodup_spec in Hbind4; auto.
      rewrite <-idty_app, NoDupMembers_idty, fst_NoDupMembers; auto.
    - eapply check_noduplocals_spec in Hbind5; eauto.
      intros ??. rewrite map_app, in_app_iff in H.
      repeat rewrite nameset_spec.
      destruct H as [Hin|Hin]; rewrite map_fst_idty in Hin; auto.
  Qed.
  Next Obligation.
    rewrite <-idty_app, map_fst_idty.
    repeat split.
    - eapply mmap_check_atom_AtomOrGensym; eauto.
    - eapply elab_block_GoodLocals; eauto.
    - eapply check_atom_spec; eauto.
  Qed.

  Program Definition elab_declaration_type
          (name: ident) (constr : list ident) (loc: astloc) : res type :=
    if Common.check_nodup constr
    then OK (Tenum name constr)
    else Error (err_loc' loc (MSG "duplicate constructor for type " :: CTX name :: nil)).

End ElabDeclaration.

Section ElabDeclarations.
  Open Scope error_monad_scope.

  Definition elab_ctype (loc: astloc) (ty: LustreAst.type_name) : res ctype :=
    match ty with
    | Tint8    => OK (Tint Ctypes.I8  Ctypes.Signed)
    | Tuint8   => OK (Tint Ctypes.I8  Ctypes.Unsigned)
    | Tint16   => OK (Tint Ctypes.I16 Ctypes.Signed)
    | Tuint16  => OK (Tint Ctypes.I16 Ctypes.Unsigned)
    | Tint32   => OK (Tint Ctypes.I32 Ctypes.Signed)
    | Tuint32  => OK (Tint Ctypes.I32 Ctypes.Unsigned)
    | Tint64   => OK (Tlong Ctypes.Signed)
    | Tuint64  => OK (Tlong Ctypes.Unsigned)
    | Tfloat32 => OK (Tfloat Ctypes.F32)
    | Tfloat64 => OK (Tfloat Ctypes.F64)
    | Tenum_name t =>
        Error (err_loc' loc (msg "Only primitive types are allowed in external declarations"))
    end.

  Fixpoint elab_declarations'
           (G: global)
           (tenv: Env.t (list ident))
           (eenv: Env.t (list ctype * ctype))
           (nenv: Env.t (list (ident * (type * clock)) * list (ident * (type * clock))))
           (decls: list declaration) : res global :=
  match decls with
  | [] => OK G
  | NODE name has_state inputs outputs block loc :: ds =>
    do n <- elab_declaration_node tenv eenv nenv name has_state inputs outputs block loc;
    if Env.mem (n_name n) nenv
    then Error (err_loc' loc (MSG "deplicate definition for " :: CTX name :: nil))
    else elab_declarations' (Global G.(types) G.(externs) (n :: G.(nodes)))
                          tenv eenv (Env.add n.(n_name) (idty n.(n_in), idty n.(n_out)) nenv) ds
  | TYPE name constructors loc :: ds =>
    do t <- elab_declaration_type name constructors loc;
    if Env.mem name tenv
    then Error (err_loc' loc (MSG "duplicate definition for " :: CTX name :: nil))
    else elab_declarations' (Global (t :: G.(types)) G.(externs) G.(nodes))
                          (Env.add name constructors tenv) eenv nenv ds
  | EXTERNAL name tyins tyout loc :: ds =>
    do tyins <- Errors.mmap (elab_ctype loc) tyins;
    do tyout <- elab_ctype loc tyout;
    if Env.mem name eenv
    then Error (err_loc' loc (MSG "duplicate definition for " :: CTX name :: nil))
    else elab_declarations' (Global G.(types) ((name, (tyins, tyout))::G.(externs)) G.(nodes))
                          tenv (Env.add name (tyins, tyout) eenv) nenv ds
  end.

  Import Instantiator.L.

  Definition bool_tenv :=
    Env.add bool_id
            [false_id; true_id] (* order is important *)
            (Env.empty _).

  Program Definition elab_declarations (decls: list declaration) :
    res {G | wt_global G /\ wc_global G } :=
    match elab_declarations' (Global [bool_velus_type] [] []) bool_tenv (Env.empty _) (Env.empty _) decls with
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
