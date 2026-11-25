Require Import List Nat.
Require FinFun. (* only for lemmas on non-redundant lists *)

From RFXP Require Import Utils.

Section CNFDefs.

    Variant polarity := pos | neg.

    Variable V : Type.

    Definition literal := prod V polarity.

    Definition clause := { l : list literal | NoDup l }.

    Definition cardinality_constraint := prod { l : list literal | NoDup l } nat.

    Definition cnf_with_cc := list (sum clause cardinality_constraint).

    Definition cnf := list clause.

End CNFDefs.


Section CNFSatisfiabilityDefs.

    Context {V : Type}.

    Definition assignment := V -> bool.

    Variable I : assignment.

    Definition eval_literal (x : literal V) : bool :=
        match x with
        | pair v pos => I v
        | pair v neg => negb (I v)
        end.

    Definition eval_clause (c : clause V) : bool :=
        match c with
        | exist _ l _ => existsb eval_literal l 
        end.

    Definition eval_cardinality_constraint (c : cardinality_constraint V) : bool :=
        match c with
        | pair (exist _ l _) k => (length (filter eval_literal l)) <=? k
        end.

    Definition eval_constraint (c : clause V + cardinality_constraint V) : bool :=
        match c with
        | inl c => eval_clause c
        | inr c => eval_cardinality_constraint c
        end.

    Definition eval_cnf_with_cc (c : cnf_with_cc V) : bool :=
        forallb eval_constraint c.

    Definition eval_cnf (c : cnf V) : bool :=
        forallb eval_clause c.

End CNFSatisfiabilityDefs.

Arguments assignment V : clear implicits.


Section CNFExt.

    Context {V : Type} (I J : assignment V).

    Hypothesis i_eq_j : forall x, I x = J x.

    Theorem eval_literal_ext : forall (x : literal V),
        eval_literal I x = eval_literal J x.
    Proof. intros (x & []); simpl; now rewrite i_eq_j. Qed.

    Theorem eval_clause_ext : forall (c : clause V),
        eval_clause I c = eval_clause J c.
    Proof. intros (c & H); apply existsb_ext, eval_literal_ext. Qed.

    Theorem eval_cardinality_constraint_ext : forall (c : cardinality_constraint V),
        eval_cardinality_constraint I c = eval_cardinality_constraint J c.
    Proof.
        intros ((c & H) & n); simpl;
        rewrite List.filter_ext with (g := eval_literal J); try reflexivity;
        apply eval_literal_ext.
    Qed.

    Theorem eval_constraint_ext : forall (c : clause V + cardinality_constraint V),
        eval_constraint I c = eval_constraint J c.
    Proof. intros [|]; [apply eval_clause_ext | apply eval_cardinality_constraint_ext]. Qed.

    Theorem eval_cnf_with_cc_ext : forall (c : cnf_with_cc V),
        eval_cnf_with_cc I c = eval_cnf_with_cc J c.
    Proof. intros; apply forallb_ext, eval_constraint_ext. Qed.

    Theorem eval_cnf_ext : forall (c : cnf V),
        eval_cnf I c = eval_cnf J c.
    Proof. intros; apply forallb_ext, eval_clause_ext. Qed.

End CNFExt.


Section CNFMap.

    Context {U V : Type} (f : U -> V).

    Hypothesis f_inj : FinFun.Injective f.

    Definition map_literal (x : literal U) : literal V :=
        match x with
        | pair v p => pair (f v) p
        end.

    Lemma map_literal_inj : FinFun.Injective map_literal.
    Proof.
        intros (v1, p1) (v2, p2) H; inversion H;
        apply f_inj in H1; now rewrite H1.
    Qed.

    Definition map_clause (c : clause U) : clause V :=
        match c with
        | exist _ l p =>
            exist _ (map map_literal l) (FinFun.Injective_map_NoDup map_literal_inj p)
        end.

    Definition map_cardinality_constraint (c : cardinality_constraint U) : cardinality_constraint V :=
        match c with
        | pair (exist _ l p) k =>
            pair (exist _ (map map_literal l) (FinFun.Injective_map_NoDup map_literal_inj p)) k
        end.

    Definition map_constraint (c : clause U + cardinality_constraint U) : clause V + cardinality_constraint V :=
        match c with
        | inl c => inl (map_clause c)
        | inr c => inr (map_cardinality_constraint c)
        end.

    Definition map_cnf_with_cc : cnf_with_cc U -> cnf_with_cc V :=
        map map_constraint.

    Definition map_cnf : cnf U -> cnf V :=
        map map_clause.

    Definition map_assignment : assignment V -> assignment U :=
        fun I x => I (f x).

End CNFMap.

Section CNFMapSatisfiabilityFacts.

    Context {U V : Type} (f : U -> V) (I : assignment V).

    Hypothesis f_inj : FinFun.Injective f.

    Theorem map_literal_eval : forall (x : literal U),
        eval_literal I (map_literal f x) = eval_literal (map_assignment f I) x.
    Proof. intros (v, [|]); reflexivity. Qed.

    Theorem map_clause_eval : forall (c : clause U),
        eval_clause I (map_clause f f_inj c) = eval_clause (map_assignment f I) c.
    Proof.
        intros (l, p); simpl;
        destruct (existsb (eval_literal (map_assignment f I)) l) eqn:Heq.
        -   rewrite existsb_exists in Heq;
            destruct Heq as (x & H1 & H2);
            rewrite <- map_literal_eval in H2;
            rewrite existsb_exists;
            exists (map_literal f x); split;
            [ apply in_map, H1 | apply H2 ].
        -   rewrite existsb_nexists; intros y H;
            rewrite existsb_nexists in Heq;
            apply in_map_iff in H as (x & H1 & H2);
            rewrite <- H1, map_literal_eval;
            apply Heq, H2.
    Qed.

    Theorem map_cardinality_constraint_eval : forall (c : cardinality_constraint U),
        eval_cardinality_constraint I (map_cardinality_constraint f f_inj c) =
            eval_cardinality_constraint (map_assignment f I) c.
    Proof.
        intros ((l, p), k); simpl;
        replace (filter (eval_literal I) (map (map_literal f) l))
            with (map (map_literal f) (filter (eval_literal (map_assignment f I)) l));
            try (now rewrite length_map);
        rewrite filter_map_swap;
        replace (filter (eval_literal (map_assignment f I)) l)
            with (filter (fun x => eval_literal I (map_literal f x)) l);
            try reflexivity;
        apply filter_ext_in;
        intros x _; apply map_literal_eval.
    Qed.

    Theorem map_constraint_eval : forall (c : clause U + cardinality_constraint U),
        eval_constraint I (map_constraint f f_inj c) =
            eval_constraint (map_assignment f I) c.
    Proof. intros [|]; [apply map_clause_eval | apply map_cardinality_constraint_eval]. Qed.

    Theorem map_cnf_with_cc_eval : forall (c : cnf_with_cc U),
        eval_cnf_with_cc I (map_cnf_with_cc f f_inj c) = eval_cnf_with_cc (map_assignment f I) c.
    Proof.
        intros c; unfold eval_cnf_with_cc, map_cnf_with_cc;
        rewrite forallb_map; apply forallb_ext;
        intros; now rewrite map_constraint_eval.
    Qed.

    Theorem map_cnf_eval : forall (c : cnf U),
        eval_cnf I (map_cnf f f_inj c) = eval_cnf (map_assignment f I) c.
    Proof.
        intros c; unfold eval_cnf, map_cnf;
        rewrite forallb_map; apply forallb_ext;
        intros; now rewrite map_clause_eval.
    Qed.

End CNFMapSatisfiabilityFacts.