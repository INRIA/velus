Require Import Rustre.Common.


Import List.ListNotations.
Open Scope list_scope.

(** 

  Minimp is a minimal object-oriented programming language exposing
  two methods: [step] and [reset].

 *)

(** * Imperative language *)

(** ** Syntax *)

Inductive exp : Set :=
| Var : ident -> exp
| State : ident -> exp
| Const : const -> exp.

Implicit Type e: exp.

Inductive stmt : Set :=
  | Assign : ident -> exp -> stmt
  | AssignSt : ident -> exp -> stmt
  | Ifte : exp -> stmt -> stmt -> stmt
  | Step_ap : ident -> ident -> ident -> list exp -> stmt
           (* y = Step_ap class object arg *)
  | Reset_ap : ident -> ident -> stmt
           (* Reset_ap class object *)
  | Comp : stmt -> stmt -> stmt
  | Repeat : nat -> stmt -> stmt
  | Skip.

Implicit Type s: stmt.


Record obj_dec : Set := mk_obj_dec {
  obj_inst  : ident;
  obj_class : ident
}.

(* TODO: lots of fields are not strictly necessary *)
Record class : Set := mk_class {
  c_name   : ident;

  c_input  : list ident;
  c_output : ident;

  c_mems   : list ident;       (* TODO: should track type of each *)
  c_objs   : list obj_dec;

  c_step   : stmt;
  c_reset  : stmt
}.

Implicit Type c: class.

Definition program : Type := list class.

Implicit Type p: program.

Definition find_class (n: ident) : program -> option (class * list class) :=
  fix find p :=
    match p with
    | [] => None
    | c :: p' => if ident_eqb c.(c_name) n then Some (c, p') else find p'
    end.

