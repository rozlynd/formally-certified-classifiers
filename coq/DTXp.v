From RFXP Require Import FloatUtils Utils Features DT Xp Explainers.

Require Import Floats Equality Eqdep Setoid.


Module Type DTExplanationProblem <: ExplanationProblem :=
    FeatureSig <+ Output <+ DTOn <+ ClassifierInstance.

Module Type DTInputProblem <: InputProblem.
    Include DTExplanationProblem.
    Declare Module S : FinSet with Definition n := n.
End DTInputProblem.


Section FeatureSpaceConstraint.

    (* Representations for feature constraints *)

    Variant boolConstraint : Type :=
    | BEmpty
    | BTrue
    | BFalse
    | BAny.

    Variant floatConstraint : Type :=
    | FEmpty
    | FSingleton (a : float_std)
    | FBounded (a b : float_std) (p : FloatOTF.compare a b = Lt) (* [ a; b [ where a < b *)
    | FUnbounded (a : float_std). (* [ a; +inf ] *)

    Variant senumConstraint (s : StringSet.t) : Type :=
    | SEnum (p : StringSet.t) (q : StringSet.Subset p s).


    (* Check if a constraint is unsatisfiable *)

    Definition boolConstraintEmpty (c : boolConstraint) : bool :=
        match c with
        | BEmpty => true
        | _ => false
        end.

    Definition floatConstraintEmpty (c : floatConstraint) : bool :=
        match c with
        | FEmpty => true
        | _ => false
        end.

    Definition senumConstraintEmpty {s : StringSet.t} (c : senumConstraint s) : bool :=
        match c with
        | SEnum _ p _ => StringSet.is_empty p
        end.


    (* Constraint as predicate *)

    Definition boolConstraintSat (c : boolConstraint) (b : bool) : Prop :=
        match c with
        | BEmpty => False
        | BTrue => b = true
        | BFalse => b = false
        | BAny => True
        end.

    Definition floatConstraintSat (c : floatConstraint) (x : float_std) : Prop :=
        match c with
        | FEmpty => False
        | FSingleton a =>  a = x (* Complication: FloatOTF.eq +0 -0 = true, so we use Logic.eq instead *)
        | FBounded a b _ => FloatOTF.le a x /\ FloatOTF.lt x b
        | FUnbounded a => FloatOTF.le a x
        end.

    Definition senumConstraintSat {s : StringSet.t} (c : senumConstraint s) (x : string_enum s) : Prop :=
        match c with
        | SEnum _ p _ => StringSet.In (proj1_sig x) p
        end.


    (* Get a witness satisfying some constraint if one exists *)

    Definition boolConstraintWitness (c : boolConstraint) : option bool :=
        match c with
        | BEmpty => None
        | BTrue | BAny => Some true
        | BFalse => Some false
        end.

    Definition floatConstraintWitness (c : floatConstraint) : option float_std :=
        match c with
        | FEmpty => None
        | FSingleton a
        | FBounded a _ _
        | FUnbounded a => Some a
        end.

    Program Definition senumConstraintWitness {s : StringSet.t} (c : senumConstraint s) : option (string_enum s) :=
        match c with
        | SEnum _ p q =>
            match StringSet.choose p with
            | None => None
            | Some x => Some (exist _ x _)
            end
        end.
    Next Obligation. now apply q, choose_1. Qed.

    Lemma senumConstraintWitness_Some :
        forall {s : StringSet.t} (p : StringSet.t) (q : StringSet.Subset p s) (e : string_enum s),
            senumConstraintWitness (SEnum s p q) = Some e -> StringSet.choose p = Some (proj1_sig e).
    Proof.
        intros s p q e; simpl;
        set (h := senumConstraintWitness_obligation_1 s p q); clearbody h;
        destruct (StringSet.choose p) as [f |] eqn:E; intros H; now inversion H.
    Qed.

    Lemma senumConstraintWitness_None :
        forall {s : StringSet.t} (p : StringSet.t) (q : StringSet.Subset p s),
            senumConstraintWitness (SEnum s p q) = None -> StringSet.choose p = None.
    Proof.
        intros s p q; simpl;
        set (h := senumConstraintWitness_obligation_1 s p q); clearbody h;
        destruct (StringSet.choose p) as [f |] eqn:E; intros H; now inversion H.
    Qed.


    (* Split constraints on the left or right *)

    Definition boolConstraintLeftSplit (t : boolean_test) (c : boolConstraint) : boolConstraint :=
        match c with
        | BEmpty | BFalse => BEmpty
        | BTrue | BAny => BTrue
        end.

    Definition boolConstraintRightSplit (t : boolean_test) (c : boolConstraint) : boolConstraint :=
        match c with
        | BEmpty | BTrue => BEmpty
        | BFalse | BAny => BFalse
        end.

    Definition float_lt_dec (x y : float_std) : { FloatOTF.compare x y = Lt } + { FloatOTF.compare x y <> Lt }.
        destruct (FloatOTF.compare x y); try (left; reflexivity); now right.
    Defined.

    Program Definition floatConstraintLeftSplit (t : float_test) (c : floatConstraint) : floatConstraint :=
        let '(float_lt x) := t in
        match c with
        | FEmpty => FEmpty
        | FSingleton a =>
            match float_lt_dec a x with
            | left _ => FSingleton a
            | right _ => FEmpty
            end
        | FBounded a b p =>
            match float_lt_dec a x with
            | left _ =>
                match float_lt_dec x b with
                | left _ => FBounded a x _
                | right _ => FBounded a b p
                end
            | right _ => FEmpty
            end
        | FUnbounded a =>
            match float_lt_dec a x with
            | left _ => FBounded a x _
            | right _ => FEmpty
            end
        end.

    Program Definition floatConstraintRightSplit (t : float_test) (c : floatConstraint) : floatConstraint :=
        let '(float_lt x) := t in
        match c with
        | FEmpty => FEmpty
        | FSingleton a =>
            match float_lt_dec a x with
            | left _ => FEmpty
            | right _ => FSingleton a
            end
        | FBounded a b p =>
            match float_lt_dec a x with
            | left _ =>
                match float_lt_dec x b with
                | left _ => FBounded x b _
                | right _ => FEmpty
                end
            | right _ => FBounded a b p
            end
        | FUnbounded a =>
            match float_lt_dec a x with
            | left _ => FUnbounded x
            | right _ => FUnbounded a
            end
        end.

    Program Definition senumConstraintLeftSplit {s : StringSet.t} (t : string_enum_test s) (c : senumConstraint s) : senumConstraint s :=
        let '(subset_mem _ filt) := t in
        match c with
        | SEnum _ p q => SEnum s (StringSet.filter filt p) _
        end.
    Next Obligation.
        intros x H; apply filter_1 in H; try auto.
        intros y z E; now rewrite E.
    Qed.

    Program Definition senumConstraintRightSplit {s : StringSet.t} (t : string_enum_test s) (c : senumConstraint s) : senumConstraint s :=
        let '(subset_mem _ filt) := t in
        match c with
        | SEnum _ p q => SEnum s (StringSet.filter (fun x => negb (filt x)) p) _
        end.
    Next Obligation.
        intros x H; apply filter_1 in H; try auto.
        intros y z E; now rewrite E.
    Qed.


    (* Initialize a constraint as either the full domain or a singleton value *)

    Definition boolConstraintInitFull := BAny.
    Program Definition floatConstraintInitFull := FUnbounded FloatOTF.neg_inf.
    Definition senumConstraintInitFull (s : StringSet.t) := SEnum s s (@Subset_refl _).

    Definition boolConstraintInitSingleton (b : bool) :=
        if b then BTrue
        else BFalse.

    Definition floatConstraintInitSingleton (x : float_std) := FSingleton x.

    Program Definition senumConstraintInitSingleton {s : StringSet.t} (x : string_enum s) :=
        SEnum s (StringSet.singleton (proj1_sig x)) _.
    Next Obligation.
        intros y H; destruct x;
        apply singleton_1 in H; now rewrite <- H.
    Qed.


    (* Facts about individual constraints *)

    Theorem boolConstraintSatNotEmpty :
        forall (c : boolConstraint) (x : bool),
            boolConstraintSat c x -> boolConstraintEmpty c = false.
    Proof. intros c x H; destruct c; destruct x; now inversion H. Qed.

    Theorem boolConstraintWitnessSomeSat :
        forall (c : boolConstraint) (x : bool),
            boolConstraintWitness c = Some x -> boolConstraintSat c x.
    Proof. intros c x H; destruct c; destruct x; now inversion H. Qed.

    Theorem boolConstraintWitnessNoneEmpty :
        forall (c : boolConstraint),
            boolConstraintWitness c = None -> boolConstraintEmpty c = true.
    Proof. intros c H; destruct c; now inversion H. Qed.

    Theorem boolConstraintSatSplitLeft :
        forall (c : boolConstraint) (t : boolean_test) (x : bool),
            boolConstraintSat (boolConstraintLeftSplit t c) x <->
                boolConstraintSat c x /\ tests boolean_feature t x = true.
    Proof.
        intros c t x; split;
        [ intros H; destruct c; destruct t; destruct x; now inversion H
        | intros (H1 & H2); destruct c; destruct t; destruct x; now inversion H1 ].
    Qed.

    Theorem boolConstraintSatSplitRight :
        forall (c : boolConstraint) (t : boolean_test) (x : bool),
            boolConstraintSat (boolConstraintRightSplit t c) x <->
                boolConstraintSat c x /\ tests boolean_feature t x = false.
    Proof.
        intros c t x; split;
        [ intros H; destruct c; destruct t; destruct x; now inversion H
        | intros (H1 & H2); destruct c; destruct t; destruct x; now inversion H1 ].
    Qed.

    Theorem boolConstraintInitFullSat :
        forall (x : bool),
            boolConstraintSat boolConstraintInitFull x.
    Proof. constructor. Qed.

    Theorem boolConstraintWitnessSingleton :
        forall (x : bool),
            boolConstraintWitness (boolConstraintInitSingleton x) = Some x.
    Proof. intros x; destruct x; reflexivity. Qed.

    Theorem boolConstraintSatSingletonUnique :
        forall (x y : bool),
            boolConstraintSat (boolConstraintInitSingleton x) y -> x = y.
    Proof. intros x y H; destruct x; destruct y; now inversion H. Qed.


    Theorem floatConstraintSatNotEmpty :
        forall (c : floatConstraint) (x : float_std),
            floatConstraintSat c x -> floatConstraintEmpty c = false.
    Proof. intros c x H; destruct c; now inversion H. Qed.

    Theorem floatConstraintWitnessSomeSat :
        forall (c : floatConstraint) (x : float_std),
            floatConstraintWitness c = Some x -> floatConstraintSat c x.
    Proof.
        intros c x; destruct c; simpl; intros H; try (now inversion H);
        split; inversion H; subst x; now try now apply FloatOTFFacts.compare_lt_iff.
    Qed.

    Theorem floatConstraintWitnessNoneEmpty :
        forall (c : floatConstraint),
            floatConstraintWitness c = None -> floatConstraintEmpty c = true.
    Proof. intros c H; destruct c; now inversion H. Qed.

    Lemma float_test_true :
        forall (x y : float_std), tests float_feature (float_lt y) x = true <-> FloatOTF.compare x y = Lt.
    Proof.
        intros x y; rewrite FloatOTFFacts.compare_lt_iff, FloatOTFFacts.lt_not_ge_iff;
        split; simpl; intros H; destruct x; destruct y; simpl.
        -   intros abs; now rewrite Bool.negb_true_iff, abs in H.
        -   now apply Bool.eq_true_not_negb_iff.
    Qed.

    Lemma float_test_false :
        forall (x y : float_std), tests float_feature (float_lt y) x = false <-> FloatOTF.compare x y <> Lt.
    Proof.
        intros x y.
        setoid_replace (tests float_feature (float_lt y) x = false)
            with (tests float_feature (float_lt y) x <> true) using relation iff.
        -   rewrite float_test_true; now split.
        -   destruct (tests float_feature (float_lt y) x);
            split; intros; auto; now exfalso.
    Qed.

    Theorem floatConstraintSatSplitLeft :
        forall (c : floatConstraint) (t : float_test) (x : float_std),
            floatConstraintSat (floatConstraintLeftSplit t c) x <->
                floatConstraintSat c x /\ tests float_feature t x = true.
    Proof.
        intros c [y] x; rewrite float_test_true; simpl;
        destruct c as [| a | a b p | a ];
        [
        | destruct (float_lt_dec a y) as [e1|e1]
        | destruct (float_lt_dec a y) as [e1|e1]; destruct (float_lt_dec y b) as [e2|e2]
        | destruct (float_lt_dec a y) as [e1|e1]
        ]; split; simpl;
            try (assert (H1 : FloatOTF.lt a y) by (now rewrite FloatOTFFacts.compare_lt_iff in e1));
            try (assert (H1 : ~ FloatOTF.lt a y) by (now rewrite FloatOTFFacts.compare_nlt_iff in e1));
            try (assert (H2 : FloatOTF.lt y b) by (now rewrite FloatOTFFacts.compare_lt_iff in e2));
            try (assert (H2 : ~ FloatOTF.lt y b) by (now rewrite FloatOTFFacts.compare_nlt_iff in e2));
            try (now intros).
        -   intros; now subst.
        -   intros []; now subst.
        -   intros []; split; try split; auto;
                try (now transitivity y);
            now apply FloatOTFFacts.compare_lt_iff.
        -   intros [[]]; split; auto;
            now apply FloatOTFFacts.compare_lt_iff.
        -   intros []; split; try split; auto;
            assert (FloatOTF.lt x y) by
            (
                apply FloatOTFFacts.OrderTac.lt_le_trans with (y := b); auto;
                now rewrite FloatOTFFacts.compare_ge_iff in e2
            );
            now apply FloatOTFFacts.compare_lt_iff.
        -   intros [[]]; cut (FloatOTF.lt a y); try (now intros abs);
            apply FloatOTFFacts.OrderTac.le_lt_trans with (y := x); auto;
            now apply FloatOTFFacts.compare_lt_iff.
        -   intros [[]]; cut (FloatOTF.lt a y); try (now intros abs);
            apply FloatOTFFacts.OrderTac.le_lt_trans with (y := x); auto;
            now apply FloatOTFFacts.compare_lt_iff.
        -   intros []; split; auto;
            now apply FloatOTFFacts.compare_lt_iff.
        -   intros []; split; auto;
            now apply FloatOTFFacts.compare_lt_iff.
        -   intros []; cut (FloatOTF.lt a y); try (now intros abs);
            apply FloatOTFFacts.OrderTac.le_lt_trans with (y := x); auto;
            now apply FloatOTFFacts.compare_lt_iff.
    Qed.

    Theorem floatConstraintSatSplitRight :
        forall (c : floatConstraint) (t : float_test) (x : float_std),
            floatConstraintSat (floatConstraintRightSplit t c) x <->
                floatConstraintSat c x /\ tests float_feature t x = false.
    Proof.
        intros c [y] x; rewrite float_test_false; simpl;
        destruct c as [| a | a b p | a ];
        [
        | destruct (float_lt_dec a y) as [e1|e1]
        | destruct (float_lt_dec a y) as [e1|e1]; destruct (float_lt_dec y b) as [e2|e2]
        | destruct (float_lt_dec a y) as [e1|e1]
        ]; split; simpl;
            try (assert (H1 : FloatOTF.lt a y) by (now rewrite FloatOTFFacts.compare_lt_iff in e1));
            try (assert (H1 : ~ FloatOTF.lt a y) by (now rewrite FloatOTFFacts.compare_nlt_iff in e1));
            try (assert (H2 : FloatOTF.lt y b) by (now rewrite FloatOTFFacts.compare_lt_iff in e2));
            try (assert (H2 : ~ FloatOTF.lt y b) by (now rewrite FloatOTFFacts.compare_nlt_iff in e2));
            try (now intros).
        -   intros []; now subst.
        -   intros; now subst.
        -   intros []; split; try split; auto;
                try (transitivity y; try assumption; apply H1);
            now apply FloatOTFFacts.compare_nlt_iff.
        -   intros [[]]; split; auto;
            apply FloatOTFFacts.compare_le_iff; intros abs; apply H3; unfold FloatOTF.compare;
            now rewrite FloatOTFFacts.compare_antisym, abs.
        -   intros [[]]; apply FloatOTFFacts.le_not_gt_iff in H2;
            now apply H3, FloatOTFFacts.compare_lt_iff, FloatOTFFacts.OrderTac.lt_le_trans with (y := b).
        -   intros []; split; try split; auto;
            intros abs; apply H1, FloatOTFFacts.OrderTac.le_lt_trans with (y := x); try assumption;
            now apply FloatOTFFacts.compare_lt_iff in abs.
        -   intros []; split; try split; auto;
            intros abs; apply H1, FloatOTFFacts.OrderTac.le_lt_trans with (y := x); try assumption;
            now apply FloatOTFFacts.compare_lt_iff in abs.
        -   intros; split;
                try (apply FloatOTFFacts.OrderTac.lt_le_trans with (y := y); assumption);
            intros abs; now apply FloatOTFFacts.compare_lt_iff in abs.
        -   intros []; apply FloatOTFFacts.compare_le_iff; intros abs; apply H0; unfold FloatOTF.compare;
            now rewrite FloatOTFFacts.compare_antisym, abs.
        -   intros; split; auto;
            intros abs; apply H1, FloatOTFFacts.OrderTac.le_lt_trans with (y := x); try assumption;
            now apply FloatOTFFacts.compare_lt_iff.
    Qed.

    Theorem floatConstraintInitFullSat :
        forall (x : float_std),
            floatConstraintSat floatConstraintInitFull x.
    Proof. intros x; apply FloatOTFFacts.le_neg_inf. Qed.

    Theorem floatConstraintWitnessSingleton :
        forall (x : float_std),
            floatConstraintWitness (floatConstraintInitSingleton x) = Some x.
    Proof. now intros. Qed.

    Theorem floatConstraintSatSingletonUnique :
        forall (x y : float_std),
            floatConstraintSat (floatConstraintInitSingleton x) y -> x = y.
    Proof. now intros. Qed.


    Theorem senumConstraintSatNotEmpty :
        forall {s : StringSet.t} (c : senumConstraint s) (x : string_enum s),
            senumConstraintSat c x -> senumConstraintEmpty c = false.
    Proof.
        intros s [p q] x; simpl; intros H;
        destruct (StringSet.is_empty p) eqn:abs; try reflexivity; exfalso;
        apply is_empty_2 in abs; eapply abs, H.
    Qed.

    Theorem senumConstraintWitnessSomeSat :
        forall {s : StringSet.t} (c : senumConstraint s) (x : string_enum s),
            senumConstraintWitness c = Some x -> senumConstraintSat c x.
    Proof. intros s [p q] x H; now apply senumConstraintWitness_Some, choose_1 in H. Qed.

    Theorem senumConstraintWitnessNoneEmpty :
        forall {s : StringSet.t} (c : senumConstraint s),
            senumConstraintWitness c = None -> senumConstraintEmpty c = true.
    Proof. intros s [p q] H; now apply senumConstraintWitness_None, choose_2, is_empty_1 in H. Qed.

    Theorem senumConstraintSatSplitLeft :
        forall {s : StringSet.t} (c : senumConstraint s) (t : string_enum_test s) (x : string_enum s),
            senumConstraintSat (senumConstraintLeftSplit t c) x <->
                senumConstraintSat c x /\ tests (string_enum_feature s) t x = true.
    Proof.
        intros s [p q] [f] x; simpl;
        assert (h : Morphisms.Proper (Morphisms.respectful eq eq) f). {
            intros u v E; now rewrite E.
        }
        split.
        -   intros H; split; [eapply filter_1 | eapply filter_2]; eassumption.
        -   intros (H1 & H2); now apply filter_3.
    Qed.

    Theorem senumConstraintSatSplitRight :
        forall {s : StringSet.t} (c : senumConstraint s) (t : string_enum_test s) (x : string_enum s),
            senumConstraintSat (senumConstraintRightSplit t c) x <->
                senumConstraintSat c x /\ tests (string_enum_feature s) t x = false.
    Proof.
        intros s [p q] [f] x; simpl;
        assert (h : Morphisms.Proper (Morphisms.respectful eq eq) (fun x => negb (f x))). {
            intros u v E; now rewrite E.
        }
        split.
        -   intros H; split; [apply filter_1 with (f := fun x => negb (f x)) |]; try assumption;
            apply Bool.negb_true_iff; now apply filter_2 in H.
        -   intros (H1 & H2); apply filter_3; try assumption; now apply Bool.negb_true_iff.
    Qed.

    Theorem senumConstraintInitFullSat :
        forall {s : StringSet.t} (x : string_enum s),
            senumConstraintSat (senumConstraintInitFull s) x.
    Proof. now intros s [x q]. Qed.

    Theorem senumConstraintWitnessSingleton :
        forall {s : StringSet.t} (x : string_enum s),
            senumConstraintWitness (senumConstraintInitSingleton x) = Some x.
    Proof.
        intros s x;
        destruct (senumConstraintInitSingleton) as (p & q) eqn:Ec; inversion Ec as (H);
        destruct (senumConstraintWitness (SEnum s p q)) as [e |] eqn:E.
        -   apply senumConstraintWitness_Some in E;
            rewrite <- H in E; apply StringSet.choose_spec1, singleton_1 in E; f_equal;
            destruct e; destruct x; apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat;
            now inversion E.
        -   apply senumConstraintWitness_None in E;
            rewrite <- H in E; apply StringSet.choose_spec2 in E;
            exfalso; eapply E, singleton_2; reflexivity.
    Qed.

    Theorem senumConstraintSatSingletonUnique :
        forall {s : StringSet.t} (x y : string_enum s),
            senumConstraintSat (senumConstraintInitSingleton x) y -> x = y.
    Proof.
        intros s [x q] [y r] H; apply singleton_1 in H;
        now apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
    Qed.


    (* Definitions of witness, left/right split and init on the sum-type of constraints *)

    Variant fConstraint : featureKind -> Type :=
    | CBool : boolConstraint -> fConstraint isBooleanFeature
    | CFloat : floatConstraint -> fConstraint isContinuousFeature
    | CSEnum {s : StringSet.t} : senumConstraint s -> fConstraint (isStringEnumFeature s).

    Definition constraintEmpty {f : featureKind} (c : fConstraint f) : bool :=
        match c with
        | CBool c => boolConstraintEmpty c
        | CFloat c => floatConstraintEmpty c
        | CSEnum c => senumConstraintEmpty c
        end.

    Definition constraintSat {f : featureKind} (c : fConstraint f) : dom (getf f) -> Prop :=
        match c with
        | CBool c => fun x => boolConstraintSat c x
        | CFloat c => fun x => floatConstraintSat c x
        | CSEnum c => fun x => senumConstraintSat c x
        end.

    Definition constraintWitness {f : featureKind} (c : fConstraint f) : option (dom (getf f)) :=
        match c with
        | CBool c => boolConstraintWitness c
        | CFloat c => floatConstraintWitness c
        | CSEnum c => senumConstraintWitness c
        end.

    Definition constraintLeftSplit {f : featureKind} (t : testIndex (getf f)) (c : fConstraint f) : fConstraint f :=
        match c in fConstraint f return testIndex (getf f) -> fConstraint f with
        | CBool c => fun t => CBool (boolConstraintLeftSplit t c)
        | CFloat c => fun t => CFloat (floatConstraintLeftSplit t c)
        | CSEnum c => fun t => CSEnum (senumConstraintLeftSplit t c)
        end t.

    Definition constraintRightSplit {f : featureKind} (t : testIndex (getf f)) (c : fConstraint f) : fConstraint f :=
        match c in fConstraint f return testIndex (getf f) -> fConstraint f with
        | CBool c => fun t => CBool (boolConstraintRightSplit t c)
        | CFloat c => fun t => CFloat (floatConstraintRightSplit t c)
        | CSEnum c => fun t => CSEnum (senumConstraintRightSplit t c)
        end t.

    Definition constraintInitFull {f : featureKind} : fConstraint f :=
        match f with
        | isBooleanFeature => CBool boolConstraintInitFull
        | isContinuousFeature => CFloat floatConstraintInitFull
        | isStringEnumFeature s => CSEnum (senumConstraintInitFull s)
        end.

    Definition constraintInitSingleton {f : featureKind} : dom (getf f) -> fConstraint f :=
        match f with
        | isBooleanFeature => fun x => CBool (boolConstraintInitSingleton x)
        | isContinuousFeature => fun x => CFloat (floatConstraintInitSingleton x)
        | isStringEnumFeature s => fun x => CSEnum (senumConstraintInitSingleton x)
        end.


    Section fConstraintFacts.

        Context {f : featureKind}.

        Theorem constraintSatNotEmpty :
            forall (c : fConstraint f) (x : dom (getf f)),
                constraintSat c x -> constraintEmpty c = false.
        Proof.
            destruct c; simpl;
            [ eapply boolConstraintSatNotEmpty | eapply floatConstraintSatNotEmpty | eapply senumConstraintSatNotEmpty ].
        Qed.

        Theorem constraintWitnessSomeSat :
            forall (c : fConstraint f) (x : dom (getf f)),
                constraintWitness c = Some x -> constraintSat c x.
        Proof.
            destruct c; simpl;
            [ eapply boolConstraintWitnessSomeSat | eapply floatConstraintWitnessSomeSat | eapply senumConstraintWitnessSomeSat ].
        Qed.

        Theorem constraintWitnessNoneEmpty :
            forall (c : fConstraint f),
                constraintWitness c = None -> constraintEmpty c = true.
        Proof.
            destruct c; simpl;
            [ eapply boolConstraintWitnessNoneEmpty | eapply floatConstraintWitnessNoneEmpty | eapply senumConstraintWitnessNoneEmpty ].
        Qed.

        Theorem constraintSatSplitLeft :
            forall (c : fConstraint f) (t : testIndex (getf f)) (x : dom (getf f)),
                constraintSat (constraintLeftSplit t c) x <->
                    constraintSat c x /\ tests (getf f) t x = true.
        Proof.
            destruct c; simpl;
            [ eapply boolConstraintSatSplitLeft | eapply floatConstraintSatSplitLeft | eapply senumConstraintSatSplitLeft ].
        Qed.

        Theorem constraintSatSplitRight :
            forall (c : fConstraint f) (t : testIndex (getf f)) (x : dom (getf f)),
                constraintSat (constraintRightSplit t c) x <->
                    constraintSat c x /\ tests (getf f) t x = false.
        Proof.
            destruct c; simpl;
            [ eapply boolConstraintSatSplitRight | eapply floatConstraintSatSplitRight | eapply senumConstraintSatSplitRight ].
        Qed.

        Theorem constraintInitFullSat :
            forall (x : dom (getf f)),
                constraintSat (@constraintInitFull f) x.
        Proof.
            destruct f; simpl;
            [ eapply floatConstraintInitFullSat | eapply boolConstraintInitFullSat | eapply senumConstraintInitFullSat ].
        Qed.

        Theorem constraintWitnessSingleton :
            forall (x : dom (getf f)),
                constraintWitness (@constraintInitSingleton f x) = Some x.
        Proof.
            destruct f; simpl;
            [ eapply floatConstraintWitnessSingleton | eapply boolConstraintWitnessSingleton | eapply senumConstraintWitnessSingleton ].
        Qed.

        Theorem constraintSatSingletonUnique :
            forall (x y : dom (getf f)),
                constraintSat (@constraintInitSingleton f x) y -> x = y.
        Proof.
            destruct f; simpl;
            [ eapply floatConstraintSatSingletonUnique | eapply boolConstraintSatSingletonUnique | eapply senumConstraintSatSingletonUnique ].
        Qed.

    End fConstraintFacts.


    (* Vectors of constraints *)

    Inductive featureSpaceConstraint : forall {n : nat}, featureSig n -> Type :=
    | featureSpaceConstraintNil : featureSpaceConstraint featureSigNil
    | featureSpaceConstraintCons
        {f : featureKind} (c : fConstraint f)
        {n : nat} {fs : featureSig n} (cs : featureSpaceConstraint fs) :
            featureSpaceConstraint (featureSigCons f fs).

    Lemma featureSpaceConstraintConsInversion :
        forall {n : nat} {fs : featureSig n} {f : featureKind}
               (c1 c2 : fConstraint f) (cs1 cs2 : featureSpaceConstraint fs),
            featureSpaceConstraintCons c1 cs1 = featureSpaceConstraintCons c2 cs2 -> c1 = c2 /\ cs1 = cs2.
    Proof.
        intros n fs f c1 c2 cs1 cs2 E; inversion E;
        apply eq_sigT_eq_dep in H0;
        apply eq_dep_eq in H0;
        apply eq_sigT_eq_dep in H1;
        apply eq_dep_eq in H1;
        apply eq_sigT_eq_dep in H1;
        apply eq_dep_eq in H1;
        now split.
    Qed.

    (* HERE BE DRAGONS *)
    Local Fixpoint update {n : nat} {fs : featureSig n}
                          (cs : featureSpaceConstraint fs) {struct cs} :
                            forall (i : fin n),
                                (fConstraint (getFeatureKind fs i) -> fConstraint (getFeatureKind fs i)) ->
                                featureSpaceConstraint fs :=
        match cs with
        | featureSpaceConstraintNil =>
            fun _ _ => featureSpaceConstraintNil
        | @featureSpaceConstraintCons f c _ fs cs =>
            fun i =>
                match i in fin (S p)
                      return forall (fs : featureSig p) (cs : featureSpaceConstraint fs),
                        (forall (j : fin p),
                            (fConstraint (getFeatureKind fs j) -> fConstraint (getFeatureKind fs j)) ->
                            featureSpaceConstraint fs) ->
                        (fConstraint (getFeatureKind (featureSigCons f fs) i) ->
                            fConstraint (getFeatureKind (featureSigCons f fs) i)) ->
                        featureSpaceConstraint (featureSigCons f fs) with
                | F1 => fun fs cs _ ap => featureSpaceConstraintCons (ap c) cs
                | FS i => fun fs cs k ap => featureSpaceConstraintCons c (k i ap)
                end fs cs (update cs)
        end.

    Inductive sat : forall {n : nat} {fs : featureSig n}, featureSpaceConstraint fs -> featureVec fs -> Prop :=
    | featureSpaceSatNil : sat featureSpaceConstraintNil featureVecNil
    | featureSpaceSatCons {f : featureKind} (c : fConstraint f) (x : dom (getf f))
                          {n : nat} {fs : featureSig n} (cs : featureSpaceConstraint fs) (vs : featureVec fs) :
        constraintSat c x -> sat cs vs -> sat (featureSpaceConstraintCons c cs) (featureVecCons f x vs).

    Fixpoint empty {n : nat} {fs : featureSig n} (cs : featureSpaceConstraint fs) : bool :=
        match cs with
        | featureSpaceConstraintNil => false
        | featureSpaceConstraintCons c cs =>
            constraintEmpty c || empty cs
        end.

    Fixpoint witness {n : nat} {fs : featureSig n} (cs : featureSpaceConstraint fs) : option (featureVec fs) :=
        match cs with
        | featureSpaceConstraintNil => Some (featureVecNil)
        | @featureSpaceConstraintCons _ c _ _ cs =>
            match constraintWitness c with
            | None => None
            | Some x =>
                match witness cs with
                | None => None
                | Some vs => Some (featureVecCons _ x vs)
                end
            end
        end.

    Definition splitLeft {n : nat} {fs : featureSig n} (i : fin n) (t : testIndex (getFeature fs i)) :
            featureSpaceConstraint fs -> featureSpaceConstraint fs :=
        fun cs => update cs i (constraintLeftSplit t).

    Definition splitRight {n : nat} {fs : featureSig n} (i : fin n) (t : testIndex (getFeature fs i)) :
            featureSpaceConstraint fs -> featureSpaceConstraint fs :=
        fun cs => update cs i (constraintRightSplit t).

    Fixpoint init {n : nat} (X : fin n -> bool) {fs : featureSig n} (vs : featureVec fs) : featureSpaceConstraint fs :=
        match vs in @featureVec n fs return (fin n -> bool) -> featureSpaceConstraint fs with
        | featureVecNil => fun _ => featureSpaceConstraintNil
        | featureVecCons _ x vs => fun X =>
            let c :=
                if X F1 then constraintInitFull
                else constraintInitSingleton x
            in
            featureSpaceConstraintCons c (init (fun k => X (FS k)) vs)
        end X.


    Section fConstraintSpaceFacts.

        Context {n : nat} {fs : featureSig n}.

        Theorem constraintSpaceSatNotEmpty :
            forall (c : featureSpaceConstraint fs) (x : featureVec fs),
                sat c x -> empty c = false.
        Proof. intros c x H; induction H; simpl; erewrite ? constraintSatNotEmpty; now try eassumption. Qed.

        Corollary constraintSpaceEmptyUnsat :
            forall (c : featureSpaceConstraint fs) (x : featureVec fs),
                empty c = true -> ~ sat c x.
        Proof. intros c x H abs; now rewrite constraintSpaceSatNotEmpty with (x := x) in H. Qed.

        Theorem constraintSpaceWitnessSomeSat :
            forall (c : featureSpaceConstraint fs) (x : featureVec fs),
                witness c = Some x -> sat c x.
        Proof.
            intros c x H; induction c; try (now inversion H; constructor); simpl in H;
            destruct (constraintWitness c) eqn:Hwc; destruct (witness c0) eqn:Hwc0; inversion H;
            constructor; now try apply IHc; try apply constraintWitnessSomeSat.
        Qed.

        Corollary constraintSpaceEmptyWitnessNone :
            forall (c : featureSpaceConstraint fs),
                empty c = true -> witness c = None.
        Proof.
            intros c H; destruct (witness c) as [x |] eqn:Hw; try reflexivity;
            exfalso; now apply constraintSpaceEmptyUnsat with c x, constraintSpaceWitnessSomeSat.
        Qed.

        Corollary constraintSpaceWitnessSomeNonEmpty :
            forall (c : featureSpaceConstraint fs) (x : featureVec fs),
                witness c = Some x -> empty c = false.
        Proof.
            intros c x H; now apply constraintSpaceSatNotEmpty with (x := x), constraintSpaceWitnessSomeSat.
        Qed.

        Theorem constraintSpaceWitnessNoneEmpty :
            forall (c : featureSpaceConstraint fs),
                witness c = None -> empty c = true.
        Proof.
            intros c H; induction c; try (now inversion H); simpl in *;
            destruct (constraintWitness c) eqn:Hwc; [destruct (witness c0) eqn:Hwc0|]; try discriminate H;
            try (now rewrite IHc, Bool.orb_true_r); now rewrite constraintWitnessNoneEmpty.
        Qed.

        Corollary constraintSpaceNonEmptyWitnessSome :
            forall (c : featureSpaceConstraint fs),
                empty c = false -> exists (x : featureVec fs), witness c = Some x.
        Proof.
            intros c H; destruct (witness c) as [x |] eqn:Hw; try (now exists x);
            now rewrite constraintSpaceWitnessNoneEmpty in H.
        Qed.

        Corollary constraintSpaceNonEmptySat :
            forall (c : featureSpaceConstraint fs),
                empty c = false -> exists (x : featureVec fs), sat c x.
        Proof.
            intros c H; destruct constraintSpaceNonEmptyWitnessSome with c as (x & H'); try assumption;
            exists x; now apply constraintSpaceWitnessSomeSat.
        Qed.

        Theorem constraintSpaceSatSplitLeft :
            forall (c : featureSpaceConstraint fs) (i : fin n) (t : testIndex (getFeature fs i)) (x : featureVec fs),
                sat (splitLeft i t c) x <->
                    sat c x /\ tests (getFeature fs i) t (getValue' x i) = true.
        Proof.
            intros c i t x; unfold splitLeft; induction c; simpl; try (now inversion i);
            dependent destruction i.
            -   dependent destruction x; rewrite getValueF1'; split; intros H.
                +   dependent destruction H; apply constraintSatSplitLeft in H as (Hsat & Htest); split;
                    [ now constructor | auto ].
                +   destruct H as (Hsat & Htest); dependent destruction Hsat;
                    now constructor; try apply constraintSatSplitLeft.
            -   dependent rewrite (@getFeatureFS n f fs i) in t; dependent destruction x;
                specialize IHc with i t x1; rewrite getValueFS'; split; intros H.
                +   dependent destruction H; apply IHc in H0 as (Hsat & Htest); split;
                    [ now constructor | auto ].
                +   destruct H as (Hsat & Htest); dependent destruction Hsat;
                    constructor; now try apply IHc.
        Qed.

        Corollary constraintSpaceWitnessSplitLeft :
            forall (c : featureSpaceConstraint fs) (i : fin n) (t : testIndex (getFeature fs i)) (x : featureVec fs),
                witness (splitLeft i t c) = Some x ->
                    tests (getFeature fs i) t (getValue' x i) = true.
        Proof.
            intros c i t x H; now apply constraintSpaceWitnessSomeSat, constraintSpaceSatSplitLeft in H.
        Qed.

        Theorem constraintSpaceSatSplitRight :
            forall (c : featureSpaceConstraint fs) (i : fin n) (t : testIndex (getFeature fs i)) (x : featureVec fs),
                sat (splitRight i t c) x <->
                    sat c x /\ tests (getFeature fs i) t (getValue' x i) = false.
        Proof.
            intros c i t x; unfold splitLeft; induction c; simpl; try (now inversion i);
            dependent destruction i.
            -   dependent destruction x; rewrite getValueF1'; split; intros H.
                +   dependent destruction H; apply constraintSatSplitRight in H as (Hsat & Htest); split;
                    [ now constructor | auto ].
                +   destruct H as (Hsat & Htest); dependent destruction Hsat;
                    now constructor; try apply constraintSatSplitRight.
            -   dependent rewrite (@getFeatureFS n f fs i) in t; dependent destruction x;
                specialize IHc with i t x1; rewrite getValueFS'; split; intros H.
                +   dependent destruction H; apply IHc in H0 as (Hsat & Htest); split;
                    [ now constructor | auto ].
                +   destruct H as (Hsat & Htest); dependent destruction Hsat;
                    constructor; now try apply IHc.
        Qed.

        Corollary constraintSpaceWitnessSplitRight :
            forall (c : featureSpaceConstraint fs) (i : fin n) (t : testIndex (getFeature fs i)) (x : featureVec fs),
                witness (splitRight i t c) = Some x ->
                    tests (getFeature fs i) t (getValue' x i) = false.
        Proof.
            intros c i t x H; now apply constraintSpaceWitnessSomeSat, constraintSpaceSatSplitRight in H.
        Qed.

        Corollary constraintSpaceSplitSat :
            forall (c : featureSpaceConstraint fs) (i : fin n) (t : testIndex (getFeature fs i)) (x : featureVec fs),
                sat c x <->
                    sat (splitLeft i t c) x \/
                    sat (splitRight i t c) x.
        Proof.
            intros c i t x; rewrite constraintSpaceSatSplitLeft, constraintSpaceSatSplitRight;
            split; intros H;
            [ now destruct (tests (getFeature fs i) t (getValue' x i)) eqn:Ht; [left | right]
            | now destruct H ].
        Qed.

        Corollary constraintSpaceEmptySplit :
            forall (c : featureSpaceConstraint fs) (i : fin n) (t : testIndex (getFeature fs i)),
                empty c =
                    (empty (splitLeft i t c)
                    && empty (splitRight i t c))%bool.
        Proof.
            intros c i t;
            destruct (empty c) eqn:H;
            destruct (empty (splitLeft i t c)) eqn:Hl;
            destruct (empty (splitRight i t c)) eqn:Hr;
                try reflexivity; exfalso;
                try (
                    apply constraintSpaceNonEmptySat in Hr as (x & Hr);
                    apply constraintSpaceSatSplitRight in Hr as (Hr & _);
                    apply constraintSpaceSatNotEmpty in Hr; now rewrite Hr in H);
                try (
                    apply constraintSpaceNonEmptySat in Hl as (x & Hl);
                    apply constraintSpaceSatSplitLeft in Hl as (Hl & _);
                    apply constraintSpaceSatNotEmpty in Hl; now rewrite Hl in H);
            apply constraintSpaceNonEmptySat in H as (x & H);
            destruct (tests (getFeature fs i) t (getValue' x i)) eqn:Ht;
            eapply constraintSpaceEmptyUnsat; [apply Hl | idtac | apply Hr | idtac];
                try (now apply constraintSpaceSatSplitLeft with (x := x));
                try (now apply constraintSpaceSatSplitRight with (x := x)).
        Qed.

        Theorem constraintSpaceInitSat :
            forall (X : fin n -> bool) (vs vs' : featureVec fs),
                (forall (i : fin n), X i = false -> getValue' vs' i = getValue' vs i) ->
                sat (init X vs) vs'.
        Proof.
            intros X vs vs' H; induction vs; simpl;
            dependent destruction vs'; constructor.
            -   specialize H with F1; destruct (X F1);
                [ apply constraintInitFullSat
                | rewrite 2 getValueF1' in H; rewrite H; try reflexivity;
                  apply constraintWitnessSomeSat, constraintWitnessSingleton ].
            -   apply IHvs; intros i HX;
                specialize H with (FS i);
                rewrite 2 getValueFS' in H; now rewrite H.
        Qed.

        Theorem constraintSpaceInitSatValuesUnique :
            forall (X : fin n -> bool) (vs vs' : featureVec fs) (i : fin n),
                sat (init X vs) vs' -> X i = false -> getValue' vs' i = getValue' vs i.
        Proof.
            intros X vs vs' i Hsat HX;
            remember (init X vs) as cs eqn:E;
            induction Hsat; try (now inversion i);
            dependent destruction vs;
            apply featureSpaceConstraintConsInversion in E as (E1 & E2);
            dependent destruction i.
            -   rewrite 2 getValueF1'; rewrite HX in E1;
                rewrite E1 in H; now apply constraintSatSingletonUnique in H.
            -   rewrite 2 getValueFS'; eapply IHHsat; eassumption.
        Qed.

    End fConstraintSpaceFacts.

End FeatureSpaceConstraint.


Module DtWCXpCheckerImpl (C : DT) (S : FinSet with Definition n := C.n).
    Module Import FD := FeatureSigDefs C S.

    Fixpoint refute_aux
            (c0 : C.K.t)
            (C : featureSpaceConstraint C.fs)
            (dt : C.t)
            : option (featureVec C.fs) :=
        match dt with
        | Leaf c =>
            if C.K.eq_dec c c0 then
                None
            else
                witness C
        | Node i test dt1 dt2 =>
            let Cleft := splitLeft i test C in
            let CRight := splitRight i test C in
            if empty Cleft then
                if empty CRight then
                    None
                else
                    refute_aux c0 CRight dt2
            else
                match refute_aux c0 Cleft dt1 with
                | Some r => Some r
                | None =>
                    if empty CRight then
                        None
                    else
                        refute_aux c0 CRight dt2
                end
        end.

    Lemma refute_aux_Some_sat :
        forall (c0 : C.K.t) (C : featureSpaceConstraint C.fs) (dt : C.t) (v : featureVec C.fs),
            refute_aux c0 C dt = Some v -> sat C v.
    Proof.
        intros c0 C dt v; generalize dependent C;
        induction dt as [ c | i t dt1 IH1 dt2 IH2 ]; simpl; intros C H.
        -   destruct (C.K.eq_dec c c0); try discriminate H;
            now apply constraintSpaceWitnessSomeSat.
        -   destruct (empty (splitLeft i t C)).
            +   destruct (empty (splitRight i t C)); try discriminate H;
                cut (sat (splitRight i t C) v);
                [ intros; eapply constraintSpaceSatSplitRight; eassumption
                | now apply IH2 ].
            +   destruct (refute_aux c0 (splitLeft i t C) dt1) as [f|] eqn:Hdt1.
                *   inversion H; subst f;
                    cut (sat (splitLeft i t C) v);
                    [ intros; eapply constraintSpaceSatSplitLeft; eassumption
                    | now apply IH1 ].
                *   destruct (empty (splitRight i t C)); try discriminate H;
                    cut (sat (splitRight i t C) v);
                    [ intros; eapply constraintSpaceSatSplitRight; eassumption
                    | now apply IH2 ].
    Qed.

    Lemma refute_aux_Some_contradicts :
        forall (c0 : C.K.t) (C : featureSpaceConstraint C.fs) (dt : C.t) (v : featureVec C.fs),
            refute_aux c0 C dt = Some v -> ~ C.K.eq (C.eval dt v) c0.
    Proof.
        intros c0 C dt v H;
        remember (C.eval dt v) as c1 eqn:Hc; symmetry in Hc; apply C.evalCorrect in Hc;
        assert (Hsat : sat C v); try (eapply refute_aux_Some_sat; eassumption);
        generalize dependent C;
        induction dt as [ c | i t dt1 IH1 dt2 IH2 ]; simpl; intros C H Hsat.
        -   inversion Hc; now destruct (C.K.eq_dec c c0).
        -   destruct (empty (splitLeft i t C)) eqn:Hel.
            +   destruct (empty (splitRight i t C)) eqn:Her; try discriminate H;
                assert (Hsat2 : sat (splitRight i t C) v); try (eapply refute_aux_Some_sat; eassumption);
                apply IH2 with (C := splitRight i t C); try assumption;
                inversion Hc; apply inj_pair2 in H1; try auto;
                exfalso; subst;
                rewrite constraintSpaceSatNotEmpty with (x := v) in Hel; try discriminate Hel;
                now apply constraintSpaceSatSplitLeft.
            +   destruct (refute_aux c0 (splitLeft i t C) dt1) as [v' |] eqn:H'.
                *   inversion H; subst v';
                    assert (Hsat1 : sat (splitLeft i t C) v); try (eapply refute_aux_Some_sat; eassumption);
                    apply IH1 with (C := splitLeft i t C); try assumption;
                    inversion Hc; apply inj_pair2 in H1; try auto;
                    exfalso; subst;
                    apply constraintSpaceSatSplitLeft in Hsat1 as (_ & Hsat1);
                    unfold featureTest' in H2; now rewrite Hsat1 in H2.
                *   destruct (empty (splitRight i t C)) eqn:Her; try discriminate H;
                    assert (Hsat2 : sat (splitRight i t C) v); try (eapply refute_aux_Some_sat; eassumption);
                    apply IH2 with (C := splitRight i t C); try assumption;
                    inversion Hc; apply inj_pair2 in H1; try auto;
                    exfalso; subst;
                    apply constraintSpaceSatSplitRight in Hsat2 as (_ & Hsat2);
                    unfold featureTest' in H2; now rewrite Hsat2 in H2.
    Qed.

    Lemma refute_aux_None_unsat :
        forall (c0 : C.K.t) (C : featureSpaceConstraint C.fs) (dt : C.t) (v : featureVec C.fs),
            refute_aux c0 C dt = None -> sat C v -> C.eval dt v = c0.
    Proof.
        intros c0 C dt v; rewrite <- C.evalCorrect; generalize dependent C;
        induction dt as [ c | i t dt1 IH1 dt2 IH2 ]; simpl; intros C H Hsat.
        -   destruct (C.K.eq_dec c c0); try (subst c; constructor);
            destruct (constraintSpaceNonEmptyWitnessSome C) as (x & Hx);
                try (eapply constraintSpaceSatNotEmpty; eassumption);
            now rewrite Hx in H.
        -   destruct (empty (splitLeft i t C)) eqn:Hel.
            +   destruct (empty (splitRight i t C)) eqn:Her.
                *   exfalso; cut (empty C = true);
                    [ intros abs; now rewrite constraintSpaceSatNotEmpty with (x := v) in abs
                    | now erewrite constraintSpaceEmptySplit, Hel, Her ].
                *   destruct (featureTest' v i t) eqn:Htest;
                        try (rewrite constraintSpaceSatNotEmpty with (x := v) in Hel; try discriminate Hel;
                            now apply constraintSpaceSatSplitLeft);
                    constructor 3; try apply IH2 with (C := splitRight i t C); try assumption;
                    now apply constraintSpaceSatSplitRight.
            +   destruct (refute_aux c0 (splitLeft i t C) dt1) eqn:H'; try discriminate H;
                destruct (featureTest' v i t) eqn:Htest.
                *   constructor 2; try apply IH1 with (C := splitLeft i t C); try assumption;
                    now apply constraintSpaceSatSplitLeft.
                *   assert (Hsat2 : sat (splitRight i t C) v); try (now apply constraintSpaceSatSplitRight);
                    rewrite constraintSpaceSatNotEmpty with (x := v) in H; try assumption;
                    constructor 3; try apply IH2 with (C := splitRight i t C); assumption.
    Qed.


    Definition init : S.t -> featureVec C.fs -> featureSpaceConstraint C.fs :=
        fun X => init (fun i => S.mem i X).

    Lemma init_constraintEquivSat :
        forall (X : S.t) (v v' : featureVec C.fs),
            FD.equiv (S.compl X) v v' -> sat (init X v) v'.
    Proof.
        intros X v v' H; apply constraintSpaceInitSat;
        intros i Hi; symmetry; apply H, S.In_compl;
        intros abs; apply S.mem_spec in abs; now rewrite abs in Hi.
    Qed.

    Lemma init_constraintSatAgrees :
        forall (X : S.t) (v v' : featureVec C.fs),
            sat (init X v) v' -> FD.equiv (S.compl X) v v'.
    Proof.
        intros X v v' H i Hi; symmetry;
        eapply constraintSpaceInitSatValuesUnique;
        [ eassumption
        | apply Bool.not_true_is_false; intros abs;
          apply S.In_compl in Hi; now apply Hi, S.mem_spec ].
    Qed.


    Definition refute (dt : C.t) (v : featureVec C.fs) (X : S.t) : option (featureVec C.fs) :=
        refute_aux (C.eval dt v) (init X v) dt.

    Theorem refute_success_agrees :
        forall (dt : C.t) (v v' : featureVec C.fs) (X : S.t),
            refute dt v X = Some v' -> FD.equiv (S.compl X) v v'.
    Proof. intros; eapply init_constraintSatAgrees, refute_aux_Some_sat; eassumption. Qed.

    Theorem refute_success_contradicts :
        forall (dt : C.t) (v v' : featureVec C.fs) (X : S.t),
            refute dt v X = Some v' -> ~ C.K.eq (C.eval dt v) (C.eval dt v').
    Proof. intros; symmetry; eapply refute_aux_Some_contradicts; eassumption. Qed.

    Theorem refute_fail :
        forall (dt : C.t) (v v' : featureVec C.fs) (X : S.t),
            refute dt v X = None -> FD.equiv (S.compl X) v v' -> C.K.eq (C.eval dt v) (C.eval dt v').
    Proof.
        intros dt v v' X H1 H2; apply refute_aux_None_unsat with (v := v') in H1; try (now symmetry);
        now apply init_constraintEquivSat.
    Qed.

End DtWCXpCheckerImpl.


Module DtWCXpChecker (Import E_ : DTInputProblem) : WCXpChecker with Module E := E_.
    Module E := E_.
    Module Import Xp := ExplainersDefs E.
    Module Impl := DtWCXpCheckerImpl E E.S.

    Definition checkWCXp (X : S.t) :=
        match Impl.refute E.k E.v X with
        | None => false
        | Some _ => true
        end.

    Theorem checkWCXpSound :
        forall X, Bool.reflect (Xp.WCXp X) (checkWCXp X).
    Proof.
        intros X; unfold checkWCXp;
        destruct (Impl.refute E.k E.v X) as [v |] eqn:Heq;
        constructor.
        -   exists v; split.
            +   eapply Impl.refute_success_agrees; eassumption.
            +   eapply Impl.refute_success_contradicts; eassumption.
        -   intros (v & Heqv & Hcont);
            eapply Hcont, Impl.refute_fail; eassumption.
    Defined.

End DtWCXpChecker.


Module DtAXpFinder (E_ : DTInputProblem) : AXpFinder with Module E := E_.
    Module Chk := DtWCXpChecker E_.
    Module E := E_.
    Module Impl := AXpIterativeFinderOn E_ Chk.
    Include Impl.
End DtAXpFinder.

Module DtCXpFinder (E_ : DTInputProblem) : CXpFinder with Module E := E_.
    Module Chk := DtWCXpChecker E_.
    Module E := E_.
    Module Impl := CXpIterativeFinderOn E_ Chk.
    Include Impl.
End DtCXpFinder.
