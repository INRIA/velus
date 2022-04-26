(** * System.v: Formalisation of Kahn networks *)
Set Implicit Arguments.

Require Export Cpo_streams_type.

(** ** Definition of nodes *)
(** Definition of a multiple node :
    - index for inputs with associated types
    - index for outputs with associated types
    - continuous function on corresponding streams 
*)

Definition DS_fam (I:Type)(SI:I -> Type) (i:I) := DS (SI i).

Definition DS_prod (I:Type)(SI:I -> Type) := Dprodi (DS_fam SI).

(** - A node is a continuous function from inputs to outputs *)

Definition node_fun (I O : Type) (SI : I -> Type) (SO : O -> Type) :cpo 
              := DS_prod SI -C-> DS_prod SO.

(** - node with a single output *)

Definition snode_fun (I : Type) (SI : I -> Type) (SO : Type) : cpo := DS_prod SI -C-> DS SO.

(** ** Definition of a system *)

(** - Each link is either an input link or is associated to the output of a simple node, 
       each input of that node is associated to a link with the apropriate type *)

Definition inlSL  (LI LO:Type) (SL:(LI+LO)->Type) (i:LI) := SL (inl LO i).
Definition inrSL  (LI LO:Type) (SL:(LI+LO)->Type) (o:LO) := SL (inr LI o).

(** A system associates a continuous functions to a set of typed output links *)

Definition system (LI LO:Type) (SL:LI+LO->Type) 
    := Dprodi (fun (o:LO) => DS_prod SL -C-> DS (inrSL SL o)).

(** ** Semantics of a system *)
(** Each system defines a new node with inputs for the inputs of the system *)

(** *** Definition of the equations *)
(** Equations are a continuous functional on links *)

Definition eqn_of_system :  forall (LI LO:Type) (SL:LI+LO->Type),
     system SL -> DS_prod (inlSL SL) ->  DS_prod SL -m> DS_prod SL.
intros LI LO SL s init.
exists (fun X : DS_prod SL => fun l : LI+LO => 
                       match l return (DS (SL l))  with 
                            inl i => init i
                          | inr o => s o X 
                      end).
red;intros X Y Hle; intro l.
case l; auto.
Defined.

Lemma eqn_of_system_simpl : forall (LI LO:Type) (SL:LI+LO->Type)(s:system SL)
               (init : DS_prod (inlSL SL)) (X:DS_prod SL),
               eqn_of_system s init X = 
                 fun l : LI+LO => 
                 match l return (DS (SL l)) with 
                     inl i => init i
                   | inr o => s o X
                end.
trivial.
Qed.

Lemma eqn_of_system_cont : forall (LI LO:Type) (SL:LI+LO->Type)(s:system SL)
               (init : DS_prod (inlSL SL)), continuous (eqn_of_system s init).
intros; apply Dprodi_continuous with (Di:= fun i => DS (SL i)); intro.
red; intros.
rewrite fmon_comp_simpl.
setoid_rewrite (Proj_simpl (O:=DS_fam SL)).
rewrite (eqn_of_system_simpl (SL:=SL)).
case i; intros; auto.
apply (le_lub (c:=DS (SL (inl LO l)))) with 
    (f:=(Proj (DS_fam SL) (inl LO l) @ eqn_of_system s init) @ h)
    (n:=O).
rewrite (fcont_continuous (s l)).
apply lub_le_compat; intro n; simpl.
apply DSle_refl.
Qed.
Global Hint Resolve eqn_of_system_cont : core.

Definition EQN_of_system : forall (LI LO:Type) (SL:LI+LO->Type),
               system SL -> DS_prod (inlSL SL) -> DS_prod SL -c> DS_prod SL.
intros LI LO SL s init; exists (eqn_of_system s init); auto.
Defined.

Lemma EQN_of_system_simpl :  forall (LI LO:Type) (SL:LI+LO->Type)(s:system SL)
               (init : DS_prod (inlSL SL)) (X:DS_prod SL), 
               EQN_of_system s init X = eqn_of_system s init X.
trivial.
Qed.

(** *** Properties of the equations *)
(** The equations are monotonic with respect to the inputs and the system *)

Lemma EQN_of_system_mon : forall (LI LO:Type) (SL:LI+LO->Type)
            (s1 s2 : system SL) (init1 init2 : DS_prod (inlSL SL)),
            s1 <= s2 -> init1 <= init2 -> EQN_of_system s1 init1 <= EQN_of_system s2 init2.
intros; apply fcont_le_intro; intro X.
repeat (rewrite (EQN_of_system_simpl)); repeat (rewrite (eqn_of_system_simpl)).
intro l; case l; auto.
intros; apply (H l0 X).
Qed.

Definition Eqn_of_system : forall (LI LO:Type) (SL:LI+LO->Type),
               (system SL) -m> DS_prod (inlSL SL) -M-> DS_prod SL -C-> DS_prod SL.
intros; exact (le_compat2_mon (EQN_of_system_mon (SL:=SL))).
Defined.

Lemma Eqn_of_system_simpl : forall (LI LO:Type) (SL:LI+LO->Type)(s:system SL)
               (init:DS_prod (inlSL SL)), Eqn_of_system SL s init = EQN_of_system s init.
trivial.
Qed.

(** The equations are continuous with respect to the inputs *)

Lemma Eqn_of_system_cont : forall (LI LO:Type) (SL:LI+LO->Type), 
            continuous2 (Eqn_of_system SL).
red; intros.
rewrite (Eqn_of_system_simpl (SL:=SL)).
apply (fcont_le_intro (D1:=DS_prod SL) (D2:=DS_prod SL)); intro X.
rewrite EQN_of_system_simpl; setoid_rewrite eqn_of_system_simpl; intro l.
case_eq l; intros.
rewrite fcont_lub_simpl.
unfold DS_prod; repeat (rewrite Dprodi_lub_simpl).
apply lub_le_compat; intro n; auto.
(* Case l is inr l0 *)
unfold system; rewrite Dprodi_lub_simpl.
repeat rewrite fcont_lub_simpl.
unfold DS_prod; rewrite Dprodi_lub_simpl.
apply lub_le_compat.
intro n; simpl; auto.
Qed.
Global Hint Resolve Eqn_of_system_cont : core.

Lemma Eqn_of_system_cont2 : forall (LI LO:Type) (SL:LI+LO->Type)(s:system SL),
            continuous (Eqn_of_system SL s).
red; intros; apply continuous2_right; auto.
Qed.

Lemma Eqn_of_system_cont1 : forall (LI LO:Type) (SL:LI+LO->Type),
            continuous (Eqn_of_system SL).
auto.
Qed.

Definition  EQN_of_SYSTEM  (LI LO:Type) (SL:LI+LO->Type)
       :  system SL -c> DS_prod (inlSL SL) -C-> DS_prod SL -C-> DS_prod SL
       :=   continuous2_cont (Eqn_of_system_cont (SL:=SL)).

(** *** Solution of the equations *)
(** The solution is defined as the smallest fixpoint of the equations
           it is a monotonic function of the  inputs *)

Definition sol_of_system  (LI LO:Type) (SL:LI+LO->Type) 
    : system SL -c> DS_prod (inlSL SL) -C-> DS_prod SL := FIXP (DS_prod SL) @@_ EQN_of_SYSTEM SL.

Lemma sol_of_system_simpl : 
    forall (LI LO:Type) (SL:LI+LO->Type) (s:system SL) (init:DS_prod (inlSL SL)),
    sol_of_system SL s init = FIXP (DS_prod SL) (EQN_of_system s init).
trivial.
Qed.

Lemma sol_of_system_eq : forall (LI LO:Type) (SL:LI+LO->Type) (s:system SL) (init:DS_prod (inlSL SL)),
    sol_of_system SL s init == eqn_of_system s init (sol_of_system SL s init).
intros; rewrite sol_of_system_simpl.
apply (fixp_eq (D:=DS_prod SL) (f:=eqn_of_system s init)); auto.
Qed.

(** *** New node from the system *)
(** We can choose an arbitrary set of outputs *)
Definition node_of_system (O:Type)(LI LO:Type) (SL:LI+LO->Type)(indO : O -> LO) :
          system SL -C-> node_fun (fun i : LI => SL (inl LO i)) (fun o : O => SL (inr LI (indO o)))
:= DLIFTi (DS_fam SL) (fun o => inr LI (indO o)) @@_ (sol_of_system SL).


