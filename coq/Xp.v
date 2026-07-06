Require Import Equalities Morphisms.

From RFXP Require Import Utils Features.


Module Type FeatureSigOn (N : FinSig).
    Parameter fs : featureSig N.n.
End FeatureSigOn.

Module Type FeatureSig := FinSig <+ FeatureSigOn.


Module FeatureSigDefs (F : FeatureSig) (S : FinSetOn F).

    Definition equiv (X : S.t) (v1 v2 : featureVec F.fs) : Prop :=
        forall (i : fin F.n), S.In i X -> getValue' v1 i = getValue' v2 i.

    Global Instance equiv_compat : Proper (S.Equal ==> Logic.eq ==> Logic.eq ==> iff) equiv.
    Proof.
        intros s1 s2 HEs v1 v1' HE1 v2 v2' HE2; subst v1' v2';
        split; intros H i Hi; apply H, HEs, Hi.
    Qed.

End FeatureSigDefs.


Module Type Output.
    Declare Module K : UsualDecidableType.
End Output.

Module Type ClassifierOn (F : FeatureSig) (O : Output).
    Parameter t : Type.
    Parameter eval : t -> featureVec F.fs -> O.K.t.
End ClassifierOn.

Module Type Classifier := FeatureSig <+ Output <+ ClassifierOn.


Module Type ClassifierInstance (F : FeatureSig) (O : Output) (C : ClassifierOn F O).
    Parameter k : C.t.
    Parameter v : featureVec F.fs.
End ClassifierInstance.

Module Type ExplanationProblem := FeatureSig <+ Output <+ ClassifierOn <+ ClassifierInstance.

Module Type InputProblem <: ExplanationProblem.
    Include ExplanationProblem.
    Declare Module S : FinSet with Definition n := n.
End InputProblem.


Module ExplanationsDefs (Import E : InputProblem).

    Include FeatureSigDefs E S.

    Definition WCXp (X : S.t) : Prop :=
        exists (v' : featureVec fs), equiv (S.compl X) v v' /\ eval k v <> eval k v'.

    Definition WAXp (X : S.t) : Prop :=
        forall (v' : featureVec fs), equiv X v v' -> eval k v = eval k v'.

    Definition CXp (X : S.t) : Prop :=
        WCXp X /\ forall X', S.Subset X' X -> WCXp X' -> S.Equal X' X.

    Definition AXp (X : S.t) : Prop :=
        WAXp X /\ forall X', S.Subset X' X -> WAXp X' -> S.Equal X' X.

End ExplanationsDefs.


Module ExplanationsFacts (Import E : InputProblem).

    Module Import Xp := ExplanationsDefs E.
    Module P := FinSetProperties E.S.

    Instance compl_compat : Proper (S.Equal ==> S.Equal) S.compl := S.compl_compat.

    Global Instance WCXp_compat : Proper (S.Equal ==> iff) WCXp.
    Proof.
        intros s1 s2 HEs; split; intros (v' & H1 & H2);
        exists v'; split; try (now rewrite <- ?HEs); now rewrite -> ?HEs.
    Qed.

    Global Instance WAXp_compat : Proper (S.Equal ==> iff) WAXp.
    Proof.
        intros s1 s2 HEs; split; intros H v' HE; apply H;
        try (now rewrite HEs); now rewrite <- HEs.
    Qed.

    Global Instance CXp_compat : Proper (S.Equal ==> iff) CXp.
    Proof.
        intros s1 s2 HEs; unfold CXp; split; intros (H1 & H2); split;
        try (now rewrite HEs); try (now rewrite <- HEs); intros X;
        try (rewrite HEs; now apply H2);
        try (rewrite <- HEs; now apply H2).
    Qed.

    Global Instance AXp_compat : Proper (S.Equal ==> iff) AXp.
    Proof.
        intros s1 s2 HEs; unfold CXp; split; intros (H1 & H2); split;
        try (now rewrite HEs); try (now rewrite <- HEs); intros X;
        try (rewrite HEs; now apply H2);
        try (rewrite <- HEs; now apply H2).
    Qed.


    (* Monotonicity *)

    Theorem WCXp_monotonic :
        forall (X1 X2 : S.t), S.Subset X1 X2 -> WCXp X1 -> WCXp X2.
    Proof.
        intros X1 X2 HSubs (v' & HEq & HDiff);
        exists v'; split; try (now apply HDiff);
        intros i Hi; apply P.Subset_compl in HSubs;
        now apply HEq, HSubs.
    Qed.

    Theorem WAXp_monotonic :
        forall (X1 X2 : S.t), S.Subset X1 X2 -> WAXp X1 -> WAXp X2.
    Proof.
        intros X1 X2 HSubs H v' HEq;
        apply H; intros x Hx; now apply HEq, HSubs.
    Qed.


    (* Sufficient conditions for minimality *)

    (* Same proof used twice; could be made more abstractly *)
    Theorem CXp_mono :
        forall (X : S.t),
            ( WCXp X /\ forall i, S.In i X -> ~ WCXp (S.remove i X) )
                -> CXp X.
    Proof.
        intros X (isWCXp & removeOneNotWCXp); split; try assumption;
        intros X' HSubs isWCXp'; apply P.P.P.subset_antisym; try assumption;
        intros i Hi; destruct (P.P.P.In_dec i X') as [| HN ]; try assumption;
        exfalso; apply removeOneNotWCXp with (i := i); try assumption;
        apply WCXp_monotonic with (X1 := X'); try assumption;
        intros j Hj; apply S.remove_spec; split; try (now apply HSubs);
        intro abs; now rewrite abs in Hj.
    Qed.

    Theorem AXp_mono :
        forall (X : S.t),
            ( WAXp X /\ forall i, S.In i X -> ~ WAXp (S.remove i X) )
                -> AXp X.
    Proof.
        intros X (isWAXp & removeOneNotWAXp); split; try assumption;
        intros X' HSubs isWAXp'; apply P.P.P.subset_antisym; try assumption;
        intros i Hi; destruct (P.P.P.In_dec i X') as [| HN ]; try assumption;
        exfalso; apply removeOneNotWAXp with (i := i); try assumption;
        apply WAXp_monotonic with (X1 := X'); try assumption;
        intros j Hj; apply S.remove_spec; split; try (now apply HSubs);
        intro abs; now rewrite abs in Hj.
    Qed.


    (* Duality *)

    Theorem XpDual_compl_of_not_WCXp_is_WAXp :
        forall (X : S.t), ~ WCXp X <-> WAXp (S.compl X).
    Proof.
        intros X; split; intro H.
        -   intros v' Heq;
            destruct (E.K.eq_dec (E.eval E.k E.v) (E.eval E.k v')); try assumption;
            exfalso; apply H; exists v'; split; assumption.
        -   intros (v' & H1 & H2); apply H2, H, H1.
    Qed.

    Theorem XpDual_compl_of_WCXp_is_not_WAXp :
        forall (X : S.t), WCXp X -> ~ WAXp (S.compl X).
    Proof.
        intros X H abs; now rewrite <- XpDual_compl_of_not_WCXp_is_WAXp in abs.
    Qed.

    (* Can't exhibit a WCXp witness in constructive logic *)
    Theorem XpDual_compl_of_WCXp_to_not_WAXp' :
        forall (X : S.t), ~ WAXp (S.compl X) -> ~ ~ WCXp X.
    Proof.
        intros X H abs; apply H, XpDual_compl_of_not_WCXp_is_WAXp, abs.
    Qed.

    Theorem XpDual_uncompl_of_not_WCXp_is_WAXp :
        forall (X : S.t), ~ WCXp (S.compl X) <-> WAXp X.
    Proof.
        intros X;
        assert (H := XpDual_compl_of_not_WCXp_is_WAXp (S.compl X));
        now rewrite P.compl_compl in H.
    Qed.

    Theorem XpDual_uncompl_of_WCXp_is_not_WAXp :
        forall (X : S.t), WCXp (S.compl X) -> ~ WAXp X.
    Proof.
        intros X H abs; now rewrite <- XpDual_uncompl_of_not_WCXp_is_WAXp in abs.
    Qed.

    Theorem XpDual_uncompl_of_WCXp_is_not_WAXp' :
        forall (X : S.t), ~ WAXp X -> ~ ~ WCXp (S.compl X).
    Proof.
        intros X H abs; apply H, XpDual_uncompl_of_not_WCXp_is_WAXp, abs.
    Qed.

End ExplanationsFacts.