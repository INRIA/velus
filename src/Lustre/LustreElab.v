From Coq Require Import String.
From Coq Require Import Omega.

From Velus Require Import Common.CompCertLib.
From Velus Require Instantiator.

From Velus Require Import Lustre.Parser.LustreAst.
From Velus Require Import Common.
From Velus Require Import Ident.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.

Module Import Syn := Instantiator.L.Syn.
(* Module Import Defs := Instantiator.NL.IsD. *)

Import Interface.Op.
Import Interface.OpAux.
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

Definition elab_constant (loc: astloc) (c: LustreAst.constant) : constant :=
  match c with
  | CONST_BOOL false  => Cint Integers.Int.zero Ctypes.IBool Ctypes.Signed
  | CONST_BOOL true   => Cint Integers.Int.one Ctypes.IBool Ctypes.Signed
  | CONST_INT s       => elab_const_int (cabsloc_of_astloc loc) s
  | CONST_FLOAT fi    => elab_const_float (cabs_floatinfo fi)
  | CONST_CHAR wide l => elab_const_char (cabsloc_of_astloc loc) wide l
  end.

Definition Is_interface_map (G: global)
           (nenv: Env.t (list (ident * (type * clock))
                        * list (ident * (type * clock)))) : Prop :=
  (forall f tcin tcout,
      Env.find f nenv = Some (tcin, tcout) ->
      (exists n, find_node f G = Some n
                 /\ Forall2 eq n.(n_in) tcin
                 /\ Forall2 eq n.(n_out) tcout))
  /\ (forall f, Env.find f nenv = None -> Forall (fun n=> f <> n.(n_name)) G).

Lemma Is_interface_map_empty:
  Is_interface_map [] (Env.empty _).
Proof.
  split; setoid_rewrite Env.gempty; intros; try discriminate; auto.
Qed.

Definition msg_of_types (ty ty': type) : errmsg :=
  MSG "expected '" :: MSG (string_of_type ty)
      :: MSG "' but got '" :: MSG (string_of_type ty') :: msg "'".

(* Used for unification *)
Inductive sident :=
| Vnm : ident -> sident
| Vidx : ident -> sident.

Inductive sclock :=
| Sbase : sclock
| Svar : ident -> sclock
| Son : sclock -> sident -> bool -> sclock.

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

Definition nsclock := (sclock * option sident).
Definition stripname (nck : nsclock) := (fst nck).

Definition ann : Type := (type * nsclock)%type.
Definition lann : Type := (list type * nsclock)%type.

(** elaboration exp : annotations use sclock *)
Inductive eexp : Type :=
(* constant have a sclock in order to later add whens *)
| Econst : const -> sclock -> eexp
| Evar   : ident -> ann -> eexp
| Eunop  : unop -> eexp -> ann -> eexp
| Ebinop : binop -> eexp -> eexp -> ann -> eexp

| Efby   : list eexp -> list eexp -> list ann -> eexp
| Earrow : list eexp -> list eexp -> list ann -> eexp

| Ewhen  : list eexp -> ident -> bool -> lann -> eexp
| Emerge : ident -> list eexp -> list eexp -> lann -> eexp
| Eite   : eexp -> list eexp -> list eexp -> lann -> eexp

| Eapp   : ident -> list eexp -> option eexp -> list ann -> eexp.

Fixpoint msg_of_clock (ck: clock) : errmsg :=
  match ck with
  | Cbase          => msg "."
  | Con ck x true  => msg_of_clock ck ++ MSG " on " :: CTX x :: nil
  | Con ck x false => msg_of_clock ck ++ MSG " onot " :: CTX x :: nil
  end.

Definition msg_of_sident (id : sident) : errmsg :=
  match id with
  | Vnm x => CTX x :: nil
  | Vidx x => MSG "?c" :: POS x :: nil
  end.

Fixpoint msg_of_sclock (ck: sclock) : errmsg :=
  match ck with
  | Sbase          => msg "."
  | Svar x         => CTX x :: nil
  | Son ck id true  => msg_of_sclock ck ++ MSG " on " :: msg_of_sident id
  | Son ck id false => msg_of_sclock ck ++ MSG " onot " :: msg_of_sident id
  end.

Fixpoint msg_ident_list (xs: list ident) :=
  match xs with
  | [] => []
  | [x] => [CTX x]
  | x::xs => CTX x :: MSG ", " :: msg_ident_list xs
  end.

Definition msg_of_clocks (ck ck': clock) : errmsg :=
  MSG "expected '" :: msg_of_clock ck
      ++ MSG "' but got '" :: msg_of_clock ck' ++ msg "'".

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

  Definition err_loc (loc: astloc) (m: errmsg) : Elab A :=
    error (MSG (string_of_astloc loc) :: MSG ":" :: m).

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
       | Son ck1 id1 true, Son ck2 id2 true
       | Son ck1 id1 false, Son ck2 id2 false =>
         do _ <- aux ck1 ck2;
         unify_sident loc id1 id2
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

  (* Map variable names to their types and clocks. *)
  Variable env : Env.t (type * clock).

  (* Preceding dataflow program. *)
  Variable G : global.

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

  Definition assert_type (loc: astloc) (xty ty: type) : Elab unit :=
    if xty ==b ty then ret tt else err_loc loc (msg_of_types xty ty).

  Definition find_node_interface (loc: astloc) (f: ident)
    : Elab (list (ident * (type * clock)) * list (ident * (type * clock))) :=
    match Env.find f nenv with
    | None => err_loc loc (MSG "node " :: CTX f :: msg " not found.")
    | Some tcs => ret tcs
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
    match type_unop' op ty with
    | None => err_loc loc (msg "wrong operator argument type")
    | Some ty' => ret ty'
    end.

  Definition find_type_binop (loc: astloc) (op: binop)
             (ty1 ty2: type) : Elab type :=
    match type_binop' op ty1 ty2 with
    | None => err_loc loc (msg "wrong operator argument type")
    | Some ty' => ret ty'
    end.

  Definition elab_type (ty: type_name) : type' :=
    match ty with
    | Tint8    => Tint Ctypes.I8  Ctypes.Signed
    | Tuint8   => Tint Ctypes.I8  Ctypes.Unsigned
    | Tint16   => Tint Ctypes.I16 Ctypes.Signed
    | Tuint16  => Tint Ctypes.I16 Ctypes.Unsigned
    | Tint32   => Tint Ctypes.I32 Ctypes.Signed
    | Tuint32  => Tint Ctypes.I32 Ctypes.Unsigned
    | Tint64   => Tlong Ctypes.Signed
    | Tuint64  => Tlong Ctypes.Unsigned
    | Tfloat32 => Tfloat Ctypes.F32
    | Tfloat64 => Tfloat Ctypes.F64
    | Tbool    => Tint Ctypes.IBool Ctypes.Signed
    end.

  Definition err_not_singleton {A} (loc: astloc) : Elab A :=
    err_loc loc (msg "singleton argument expected").

  Definition single_annot (loc: astloc) (e: eexp) : Elab (type * sclock) :=
    match e with
    | Econst c clock => ret (type_const c, clock)
    | Eapp _ _ _ [(ty, nck)]
    | Evar _ (ty, nck)
    | Eunop _ _ (ty, nck)
    | Ebinop _ _ _ (ty, nck)
    | Ewhen _ _ _ ([ty], nck)
    | Efby _ _ [(ty, nck)]
    | Emerge _ _ _ ([ty], nck)
    | Eite _ _ _ ([ty], nck) => ret (ty, stripname nck)
    | _ => err_not_singleton loc
    end.

  Fixpoint lannot (el : eexp * astloc) : list ((type * sclock) * astloc) :=
    let (e, loc) := el in
    match e with
    | Econst c clock => [((type_const c, clock), loc)]
    | Evar _ (ty, nck)
    | Eunop _ _ (ty, nck)
    | Ebinop _ _ _ (ty, nck) => [((ty, stripname nck), loc)]
    | Ewhen _ _ _ (tys, nck)
    | Emerge _ _ _ (tys, nck)
    | Eite _ _ _ (tys, nck) =>
      let ck := stripname nck in
      map (fun ty=> ((ty, ck), loc)) tys
    | Efby _ _ anns
    | Earrow _ _ anns
    | Eapp _ _ _ anns =>
      map (fun tc => ((fst tc, stripname (snd tc)), loc)) anns
    end.

  Definition lannots (els : list (eexp * astloc))
    : list ((type * sclock) * astloc) := flat_map lannot els.

  Definition lnannot (el : eexp * astloc) : list ((type * nsclock) * astloc) :=
    let (e, loc) := el in
    match e with
    | Econst c clock => [((type_const c, (clock, None)), loc)]
    | Evar _ (ty, nck)
    | Eunop _ _ (ty, nck)
    | Ebinop _ _ _ (ty, nck) => [((ty, nck), loc)]
    | Ewhen _ _ _ (tys, nck)
    | Emerge _ _ _ (tys, nck)
    | Eite _ _ _ (tys, nck) =>
      map (fun ty=> ((ty, nck), loc)) tys
    | Efby _ _ anns
    | Earrow _ _ anns
    | Eapp _ _ _ anns => map (fun tc => (tc, loc)) anns
    end.

  Definition lannots_ty {A B} (tcl : list ((type * A) * B)) : list type :=
    map (fun x=>fst (fst x)) tcl.

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
      do _ <- unify_sclock loc ck lck;
      unify_same_clock lck ans'
    end.

  Fixpoint unify_paired_types (gloc: astloc) (ck1 ck2: sclock)
           (ants anfs: list ((type * sclock) * astloc)) : Elab unit :=
    match ants, anfs with
    | [], [] => ret tt
    | ant::ants', anf::anfs' =>
      let '((tty, tck), tloc) := ant in
      let '((fty, fck), floc) := anf in
      do _ <- unify_sclock tloc tck ck1;
      do _ <- unify_sclock floc fck ck2;
      if tty ==b fty then unify_paired_types gloc ck1 ck2 ants' anfs'
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
      do _ <- unify_sclock tloc tck fck;
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
    do _ <- unify_sclock loc ck1 ck2;
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
      do _ <- assert_type loc ty' ty;
      do _ <- unify_nclock' loc nck' nck;
      unify_inputs gloc iface' args'
    end.

  Definition discardname (ann : (type * nsclock * astloc)) : (type * nsclock) :=
    let '(ty, (ck, id), _) := ann in (ty, (ck, None)).

  (* Elaborate an expression. *)

  Fixpoint elab_exp (is_top : bool) (ae: expression) {struct ae} : Elab (eexp * astloc) :=
    let elab_exp := elab_exp false in
    match ae with
    | CONSTANT ac loc =>
      do x <- fresh_ident;
      let c := elab_constant loc ac in
      let ty := type_const c in
      ret (Econst c (Svar x), loc)

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
      let ty' := elab_type aty' in
      do (e, loc') <- elab_exp ae';
      do (_, sck) <- single_annot loc' e;
      ret (Eunop (CastOp ty') e (ty', (sck, None)), loc)
    | CAST _ _ loc => err_not_singleton loc

    | BINARY aop [ae1] [ae2] loc =>
      let op := elab_binop aop in
      do (e1, loc1) <- elab_exp ae1;
      do (ty1, sck1) <- single_annot loc1 e1;
      do (e2, loc2) <- elab_exp ae2;
      do (ty2, sck2) <- single_annot loc2 e2;
      do ty' <- find_type_binop loc op ty1 ty2;
      do _ <- unify_sclock loc sck1 sck2;
      ret (Ebinop op e1 e2 (ty', (sck1, None)), loc)
    | BINARY _ _ _ loc => err_not_singleton loc

    | FBY ae0s aes loc =>
      do e0s <- mmap elab_exp ae0s;
      do es <- mmap elab_exp aes;
      let ans0 := lnannots e0s in
      do _ <- unify_paired_clock_types loc ans0 (lnannots es);
      do ans0 <- mmap update_ann (map discardname ans0);
      ret (Efby (map fst e0s) (map fst es) ans0, loc)

    | ARROW ae0s aes loc =>
      do e0s <- mmap elab_exp ae0s;
      do es <- mmap elab_exp aes;
      let ans0 := lnannots e0s in
      do _ <- unify_paired_clock_types loc ans0 (lnannots es);
      do ans0 <- mmap update_ann (map discardname ans0);
      ret (Earrow (map fst e0s) (map fst es) ans0, loc)

    | WHEN aes' x b loc =>
      do (xty, xck) <- find_var loc x;
      do _ <- assert_id_type loc x xty bool_type;
      do eas' <- mmap elab_exp aes';
      let ans' := lannots eas' in
      do _ <- unify_same_clock xck ans';
      ret (Ewhen (map fst eas') x b
                 (lannots_ty ans', (Son xck (Vnm x) b, None)), loc)

    | MERGE x aets aefs loc =>
      do (xty, sck) <- find_var loc x;
      let tck := Son sck (Vnm x) true in
      let fck := Son sck (Vnm x) false in
      do _ <- assert_id_type loc x xty bool_type;
      do eats <- mmap elab_exp aets;
      let ants := lannots eats in
      do eafs <- mmap elab_exp aefs;
      do _ <- unify_paired_types loc tck fck ants (lannots eafs);
      ret (Emerge x (map fst eats) (map fst eafs)
                  (lannots_ty ants, (sck, None)), loc)

    | IFTE [ae] aets aefs loc =>
      do (e, eloc) <- elab_exp ae;
      do (ety, eck) <- single_annot eloc e;
      do _ <- assert_type eloc ety bool_type;
      do eats <- mmap elab_exp aets;
      let ants := lannots eats in
      do eafs <- mmap elab_exp aefs;
      do _ <- unify_paired_types loc eck eck ants (lannots eafs);
      ret (Eite e (map fst eats) (map fst eafs)
                (lannots_ty ants, (eck, None)), loc)
    | IFTE _ _ _ loc => err_not_singleton loc

    | APP f aes [] loc =>
      (* node interface *)
      do (tyck_in, tyck_out) <- find_node_interface loc f;
      (* elaborate arguments *)
      do eas <- mmap elab_exp aes;
      (* instantiate annotations *)
      let anns := lnannots eas in
      do sub <- instantiating_subst (tyck_in++tyck_out);
      do xbase <- fresh_ident;
      do ianns <- mmap (inst_annot loc (Svar xbase) sub Vidx) tyck_in;
      do oanns <- mmap (inst_annot loc (Svar xbase) sub (if is_top then Vidx else Vnm)) tyck_out;
      do _ <- unify_inputs loc ianns anns;
      ret (Eapp f (map fst eas) None oanns, loc)

    | APP f aes [aer] loc =>
      (* node interface *)
      do (tyck_in, tyck_out) <- find_node_interface loc f;
      (* elaborate arguments *)
      do eas <- mmap elab_exp aes;
      (* elaborate reset and check it has boolean type *)
      do (er, erloc) <- elab_exp aer;
      do (erty, _) <- single_annot erloc er;
      do _ <- assert_type erloc erty bool_type;
      (* instantiate annotations *)
      let anns := lnannots eas in
      do sub <- instantiating_subst (tyck_in++tyck_out);
      do xbase <- fresh_ident;
      do ianns <- mmap (inst_annot loc (Svar xbase) sub Vidx) tyck_in;
      do oanns <- mmap (inst_annot loc (Svar xbase) sub (if is_top then Vidx else Vnm)) tyck_out;
      do _ <- unify_inputs loc ianns anns;
      ret (Eapp f (map fst eas) (Some er) oanns, loc)
    | APP _ _ _ loc => err_not_singleton loc
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
    | Con ck' x b =>
      do e' <- add_whens e tys ck';
      if Env.mem x env then ret (Syn.Ewhen [e'] x b (tys, (ck, None)))
      else error (MSG "Clock variable " :: CTX x :: MSG " escapes its scope" :: nil)
    end.

  Fixpoint freeze_exp (e : eexp) : Elab Syn.exp :=
    let freeze_exps := mmap freeze_exp in
    match e with
    | Econst c ck =>
      let ty := type_const c in
      do ck' <- freeze_clock ck;
      add_whens (Syn.Econst c) [ty] ck'

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

    | Ewhen es ckid b (tys, nck) =>
      do es <- freeze_exps es;
      do nck <- freeze_nclock nck;
      ret (Syn.Ewhen es ckid b (tys, nck))

    | Emerge ckid ets efs (tys, nck) =>
      do ets <- freeze_exps ets;
      do efs <- freeze_exps efs;
      do nck <- freeze_nclock nck;
      ret (Syn.Emerge ckid ets efs (tys, nck))

    | Eite e ets efs (tys, nck) =>
      do e <- freeze_exp e;
      do ets <- freeze_exps ets;
      do efs <- freeze_exps efs;
      do nck <- freeze_nclock nck;
      ret (Syn.Eite e ets efs (tys, nck))

    | Eapp f es None anns =>
      do es <- freeze_exps es;
      do anns <- mmap freeze_ann anns;
      ret (Syn.Eapp f es None anns)

    | Eapp f es (Some er) anns =>
      do es <- freeze_exps es;
      do er <- freeze_exp er;
      do anns <- mmap freeze_ann anns;
      ret (Syn.Eapp f es (Some er) anns)
    end.

  Fixpoint unify_pat (gloc: astloc)
                     (xs: list ident)
                     (anns: list ((type * nsclock) * astloc)) : Elab unit :=
    match xs, anns with
    | nil, nil => ret tt
    | x::xs', ((ty, ck), loc)::anns' =>
      do (xty, xck) <- find_var loc x;
      do _ <- assert_id_type loc x xty ty;
      do _ <- unify_nclock loc x xck ck;
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
    | ON pck' py pb, Con ck' y b =>
      if py ==b y
      then if pb ==b b
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
          else elab_var_decls_pass
                 (Env.add x (elab_type sty, Cbase) env, notdone) vds

        | FULLCK (ON cy' y b) =>
          match Env.find y env with
          | None => elab_var_decls_pass (env, vd :: notdone) vds
          | Some (yt, cy) =>
            if Env.mem x env
            then err_loc loc (CTX x :: msg " is declared more than once")
            else do _ <- assert_id_type loc y yt bool_type;
                 do _ <- assert_preclock loc x cy' cy;
                 elab_var_decls_pass
                   (Env.add x (elab_type sty, Con cy y b) env, notdone) vds
          end

        | WHENCK y b =>
          match Env.find y env with
          | None => elab_var_decls_pass (env, vd :: notdone) vds
          | Some (yt, cy) =>
            if Env.mem x env
            then err_loc loc (CTX x :: msg " is declared more than once")
            else do _ <- assert_id_type loc y yt bool_type;
                 elab_var_decls_pass
                   (Env.add x (elab_type sty, Con cy y b) env, notdone) vds
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

  (** *** The anons are prefixed by `elab` *)

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

  Definition elab_prefs := PS.singleton elab.

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

  Fact fresh_ins_AtomOrGensym' : forall G vars vars' es es' es'' st1 st2 st3 st4,
      Forall
        (fun e => forall e' loc e'' st1 st2 st3 st4,
             elab_exp G vars false e st1 = OK (e', loc, st2) ->
             freeze_exp vars' e' st3 = OK (e'', st4) -> Forall (AtomOrGensym elab_prefs) (map fst (fresh_in e''))) es ->
      mmap (elab_exp G vars false) es st1 = OK (es', st2) ->
      mmap (freeze_exp vars') (map fst es') st3 = OK (es'', st4) ->
      Forall (AtomOrGensym elab_prefs) (map fst (fresh_ins es'')).
  Proof.
    induction es; intros * Hf Helab Hfreeze;
      inv Hf; repeat monadInv; unfold fresh_ins; simpl; auto.
    rewrite map_app. apply Forall_app; split; eauto.
    - destruct x. eapply H1; eauto.
    - eapply IHes; eauto.
  Qed.

  Lemma fresh_in_AtomOrGensym : forall G vars vars' e e' loc e'' st1 st2 st3 st4,
      elab_exp G vars false e st1 = OK ((e', loc), st2) ->
      freeze_exp vars' e' st3 = OK (e'', st4) ->
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
    - (* ite *)
      destruct_to_singl es; repeat monadInv.
      apply Forall_singl in H.
      repeat rewrite map_app, Forall_app. repeat split; eauto.
      + eapply fresh_ins_AtomOrGensym' in H0; eauto.
      + eapply fresh_ins_AtomOrGensym' in H1; eauto.
    - (* cast *)
      destruct_to_singl es; repeat monadInv.
      apply Forall_singl in H. eauto.
    - (* app *)
      destruct_to_singl r; repeat monadInv.
      + rewrite map_app, Forall_app; split. eapply fresh_ins_AtomOrGensym' in H; eauto.
        eapply anon_streams_AtomOrGensym; eauto.
      + apply Forall_singl in H0.
        repeat rewrite map_app, Forall_app; repeat split; eauto.
        eapply fresh_ins_AtomOrGensym'; eauto.
        eapply anon_streams_AtomOrGensym; eauto.
    - (* constant *)
      repeat monadInv.
      clear - Hbind1. revert loc e'' x1 st4 Hbind1.
      induction x0; intros; simpl in *; repeat monadInv; auto.
      destruct (Env.mem _ _); repeat monadInv.
      eapply IHx0 in Hbind. rewrite app_nil_r; auto.
    - (* var *)
      repeat monadInv; auto.
    - (* fby *)
      repeat monadInv.
      rewrite map_app, Forall_app; split.
      + eapply fresh_ins_AtomOrGensym' in H; eauto.
      + eapply fresh_ins_AtomOrGensym' in H0; eauto.
    - (* arrow *)
      repeat monadInv.
      rewrite map_app, Forall_app; split.
      + eapply fresh_ins_AtomOrGensym' in H; eauto.
      + eapply fresh_ins_AtomOrGensym' in H0; eauto.
    - (* when *)
      repeat monadInv.
      eapply fresh_ins_AtomOrGensym'; eauto.
    - (* merge *)
      repeat monadInv.
      rewrite map_app, Forall_app; split.
      + eapply fresh_ins_AtomOrGensym' in H; eauto.
      + eapply fresh_ins_AtomOrGensym' in H0; eauto.
  Qed.

  Corollary fresh_ins_AtomOrGensym : forall G vars vars' es es' es'' st1 st2 st3 st4,
      mmap (elab_exp G vars false) es st1 = OK (es', st2) ->
      mmap (freeze_exp vars') (map fst es') st3 = OK (es'', st4) ->
      Forall (AtomOrGensym elab_prefs) (map fst (fresh_ins es'')).
  Proof.
    intros * Helab Hfreeze.
    eapply fresh_ins_AtomOrGensym'; [|eauto|eauto].
    eapply Forall_forall. intros * _ * ??.
    eapply fresh_in_AtomOrGensym; eauto.
  Qed.
  Hint Resolve fresh_in_AtomOrGensym fresh_ins_AtomOrGensym.

  Lemma anon_in_AtomOrGensym : forall G vars vars' e e' loc e'' st1 st2 st3 st4,
      elab_exp G vars true e st1 = OK ((e', loc), st2) ->
      freeze_exp vars' e' st3 = OK (e'', st4) ->
      Forall (AtomOrGensym elab_prefs) (map fst (anon_in e'')).
  Proof.
    destruct e; intros * Helab Hfreeze; simpl in *.
    - (* unop *)
      destruct_to_singl l; repeat monadInv; eauto.
    - (* binop *)
      destruct_to_singl l; repeat monadInv.
      destruct_to_singl l0; repeat monadInv.
      rewrite map_app, Forall_app. eauto.
    - (* ite *)
      destruct_to_singl l; repeat monadInv.
      repeat rewrite map_app, Forall_app. repeat split; eauto.
      + eapply fresh_ins_AtomOrGensym in Hbind7; eauto.
      + eapply fresh_ins_AtomOrGensym in Hbind6; eauto.
    - (* cast *)
      destruct_to_singl l; repeat monadInv; eauto.
    - (* app *)
      destruct_to_singl l0; repeat monadInv; eauto.
      rewrite map_app, Forall_app; repeat split; eauto.
    - (* constant *)
      eapply Forall_incl; [|eapply incl_map, anon_in_fresh_in].
      repeat monadInv.
      clear - Hbind1. revert loc e'' x1 st4 Hbind1.
      induction x0; intros; simpl in *; repeat monadInv; auto.
      destruct (Env.mem _ _); repeat monadInv.
      eapply IHx0 in Hbind. rewrite app_nil_r; auto.
    - (* var *)
      repeat monadInv; auto.
    - (* fby *)
      repeat monadInv.
      rewrite map_app, Forall_app; split.
      + eapply fresh_ins_AtomOrGensym in Hbind3; eauto.
      + eapply fresh_ins_AtomOrGensym in Hbind5; eauto.
    - (* arrow *)
      repeat monadInv.
      rewrite map_app, Forall_app; split.
      + eapply fresh_ins_AtomOrGensym in Hbind3; eauto.
      + eapply fresh_ins_AtomOrGensym in Hbind5; eauto.
    - (* when *)
      repeat monadInv.
      eapply fresh_ins_AtomOrGensym; eauto.
    - (* merge *)
      repeat monadInv.
      rewrite map_app, Forall_app; split.
      + eapply fresh_ins_AtomOrGensym in Hbind4; eauto.
      + eapply fresh_ins_AtomOrGensym in Hbind6; eauto.
  Qed.

  Corollary anon_ins_AtomOrGensym : forall G vars vars' es es' es'' st1 st2 st3 st4,
      mmap (elab_exp G vars true) es st1 = OK (es', st2) ->
      mmap (freeze_exp vars') (map fst es') st3 = OK (es'', st4) ->
      Forall (AtomOrGensym elab_prefs) (map fst (anon_ins es'')).
  Proof.
    induction es; intros * Helab Hfreeze; repeat monadInv; auto.
    unfold anon_ins; simpl.
    rewrite map_app, Forall_app; split.
    - destruct x. eapply anon_in_AtomOrGensym; eauto.
    - eapply IHes; eauto.
  Qed.

  Lemma anon_in_eq_AtomOrGensym : forall G vars eq st eq' st',
    elab_equation G vars eq st = OK (eq', st') ->
    Forall (AtomOrGensym elab_prefs) (map fst (anon_in_eq eq')).
  Proof.
    intros ?? ((xs&es)&loc) * Helab; unfold anon_in_eq; simpl in *.
    repeat monadInv; simpl.
    eapply anon_ins_AtomOrGensym; eauto.
  Qed.

  Corollary anon_in_eqs_AtomOrGensym : forall G vars eqs st eqs' st',
    mmap (elab_equation G vars) eqs st = OK (eqs', st') ->
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
      repeat progress
             match goal with
             | x:unit |- _ => destruct x
             | H:(if ?b then _ else _) _ = _ |- _ =>
               let Hb := fresh "Hb" in
               destruct b eqn:Hb; try discriminate
             | H:ret _ _ = OK _ |- _ => unfold ret in H; inv H
             end.

  Program Definition elab_declaration (decl: declaration) : res {n | n_prefixes n = elab_prefs} :=
    match decl with
      NODE name hasstate inputs outputs locals equations loc =>
      match (do env_in  <- elab_var_decls loc (Env.empty _) inputs;
             do env_out <- elab_var_decls loc env_in outputs;
             do env     <- elab_var_decls loc env_out locals;
             do xin     <- mmap (annotate env_in) inputs;
             do xout    <- mmap (annotate env_out) outputs;
             do xvar    <- mmap (annotate env) locals;
             do eqs     <- mmap (elab_equation env nenv) equations;
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
        OK (exist _ {| n_name     := name;
                       n_hasstate := hasstate;
                       n_in       := xin;
                       n_out      := xout;
                       n_vars     := xvar;
                       n_eqs      := eqs;
                       n_prefixes := elab_prefs |} _)
      end
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

End ElabDeclaration.

Section ElabDeclarations.
  Open Scope error_monad_scope.

  Fixpoint elab_declarations'
        (G: global) (nenv: Env.t (list (ident * (type * clock))
                                  * list (ident * (type * clock))))
        (decls: list declaration) : res global :=
  match decls with
  | [] => OK G
  | d :: ds =>
    do n <- elab_declaration nenv d;
    let n := proj1_sig n in
    elab_declarations' (n :: G) (Env.add n.(n_name) (n.(n_in), n.(n_out)) nenv) ds
  end.

  Fact elab_declarations'_prefixes : forall decls accG accE G,
      Forall (fun n => n_prefixes n = elab_prefs) accG ->
      elab_declarations' accG accE decls = OK G ->
      Forall (fun n => n_prefixes n = elab_prefs) G.
  Proof.
    induction decls; intros * Hacc Helab; simpl in *; monadInv Helab; auto.
    eapply IHdecls in EQ0; eauto.
    constructor; auto.
    destruct x as (n&Hprefs); simpl; auto.
  Qed.

  Import Instantiator.L.

  Program Definition elab_declarations (decls: list declaration) :
    res {G | wt_global G /\ wc_global G /\ Forall (fun n => n_prefixes n = elab_prefs) G} :=
    match elab_declarations' [] (Env.empty _) decls with
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
    repeat split; auto.
    eapply elab_declarations'_prefixes; eauto.
  Qed.
End ElabDeclarations.
