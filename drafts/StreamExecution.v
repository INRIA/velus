Section StreamExecution.

  Variable H: history.
  Variable arbitrary : stream.

  Definition const_eqb (c1: const) (c2: const) : bool :=
    match (c1, c2) with
    | (Cint z1, Cint z2) => BinInt.Z.eqb z1 z2
    | (Cbool b1, Cbool b2) => Bool.eqb b1 b2
    | _ => false
    end.

  Definition value_eqb (v1: value) (v2: value) : bool :=
    match (v1, v2) with
    | (present c1, present c2) => const_eqb c1 c2
    | (absent, absent) => true
    | _ => false
    end.

  Fixpoint str_clock (ck: clock) (n: nat) : bool :=
    match ck with
    | Cbase => true
    | Con ck' x c => match PM.find x H with
                     | None => false
                     | Some xs => andb (str_clock ck' n)
                                       (value_eqb (xs n) (present (Cbool c)))
                     end
    end.

  Fixpoint str_lexp (e: lexp) (n: nat) : value :=
    match e with
    | Econst c => present c
    | Evar x => match PM.find x H with
                | Some xs => xs n
                | None => absent
                end
    | Ewhen e' x c => match PM.find x H with
                      | Some xs => match xs n with
                                   | present (Cbool b) =>
                                     if Bool.eqb b c
                                     then str_laexp e' n
                                     else absent
                                   | _ => absent
                                   end
                      | None => absent
                      end
    end
  with str_laexp (e: laexp) (n: nat) : value :=
    match e with
    | LAexp ck e => if str_clock ck n then str_lexp e n else absent
    end.

  Lemma str_clock_spec:
    forall ck n c,
      sem_clock H ck n c
      -> str_clock ck n = c.
  Proof.
    induction ck.
    inversion 1; intuition.
    intros n c.
    inversion_clear 1;
      repeat progress (simpl;
         match goal with
         | H:sem_var _ _ _ _ |- _ => inversion_clear H
         | H: PM.find _ _ = _ |- _ => rewrite H
         | H: _ = present (Cbool ?b) |- _ => (rewrite H; destruct b)
         | H: sem_clock _ _ _ _ |- _ => (apply IHck in H; rewrite H)
         | H: b <> _ |- _ => (apply Bool.not_true_is_false in H
                              || apply Bool.not_false_is_true in H;
                              rewrite H)
         | _ => (cbv; reflexivity)
         end).
    destruct (PM.find i H); cbv; reflexivity.
  Qed.

  Lemma str_lexp_spec:
    forall e n v,
      sem_lexp H e n v
      -> str_lexp e n = v.
  Proof.
    induction e using lexp_mult
    with (P:=fun e => forall n v, sem_laexp H e n v -> str_laexp e n = v);
    inversion 1;
    repeat progress (simpl;
           match goal with
           | H:sem_lexp _ _ _ _ |- _ => (apply IHe in H; rewrite H)
           | H:sem_laexp _ _ _ _ |- _ => (apply IHe in H; rewrite H)
           | H:sem_clock _ _ _ _ |- _ => (apply str_clock_spec in H; rewrite H)
           | H:sem_var _ _ _ _ |- _ => (inversion_clear H as [xs Hfind Hxsn];
                                        rewrite Hfind; rewrite Hxsn)
           | |- (if Bool.eqb ?b1 ?b2 then _ else _) = _ =>
             try destruct b1; try destruct b2; simpl; intuition
           | _ => intuition
           end).
  Qed.

  Lemma str_laexp_spec:
    forall e n v,
      sem_laexp H e n v
      -> str_laexp e n = v.
  Proof.
    inversion_clear 1; simpl;
    repeat progress
           match goal with
           | H:sem_clock _ _ _ _ |- _ => (apply str_clock_spec in H; rewrite H)
           | H:sem_lexp _ _ _ _ |- _ => (apply str_lexp_spec in H; rewrite H)
           | _ => intuition
           end.
  Qed.

End StreamExecution.

