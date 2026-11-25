Require Import Bool List.
Require FinFun.
Import ListNotations.

From RFXP Require Import Utils Xp CNF Sat.

(* Base definitions *)

Module ExplainersDefs (Import E : InputProblem).
    Include ExplanationsDefs E.

End ExplainersDefs.

Module EnumeratorsDefs (Import E : InputProblem).
    Include ExplainersDefs E.

    Variant Xp : Type :=
    | isAXp (X : S.t) : Xp
    | isCXp (X : S.t) : Xp.

    Definition isXp (X : Xp) : Prop :=
        match X with
        | isAXp X => AXp X
        | isCXp X => CXp X
        end.

    Inductive stateWf {s : Type} {init : s} {rec : Xp -> s -> s} : s -> Prop :=
    | initWf : stateWf init
    | recordWf : forall X st, stateWf st -> stateWf (rec X st).

    Inductive stateHasSeen {s : Type} {init : s} {rec : Xp -> s -> s} : Xp -> s -> Prop :=
    | recordLast : forall X st,
        @stateWf _ init rec st -> stateHasSeen X (rec X st)
    | recordPrev : forall X Y st,
        @stateWf _ init rec st -> stateHasSeen X st -> stateHasSeen X (rec Y st).

End EnumeratorsDefs.


(* Find minimal explanations from a seed (eliminate redundant features) *)

Module Type AXpFinderOn (Import E : InputProblem).
    Module Import Xp := ExplainersDefs E.

    Parameter findAXp : S.t -> S.t.

    Axiom findAXpSound :
        forall X, WAXp X -> AXp (findAXp X).

    Axiom findAXpSane :
        forall X, S.Subset (findAXp X) X.

End AXpFinderOn.

Module Type AXpFinder.
    Declare Module E : InputProblem.
    Include AXpFinderOn E.
End AXpFinder.


Module Type CXpFinderOn (Import E : InputProblem).
    Module Import Xp := ExplainersDefs E.

    Parameter findCXp : S.t -> S.t.

    Axiom findCXpSound :
        forall X, WCXp X -> CXp (findCXp X).

    Axiom findCXpSane :
        forall X, S.Subset (findCXp X) X.

End CXpFinderOn.

Module Type CXpFinder.
    Declare Module E : InputProblem.
    Include CXpFinderOn E.
End CXpFinder.


(* Decide if a set is a WCXp *)

Module Type WCXpCheckerOn (Import E : InputProblem).
    Module Import Xp := ExplainersDefs E.

    Parameter checkWCXp : S.t -> bool.

    Axiom checkWCXpSound :
        forall X, Bool.reflect (WCXp X) (checkWCXp X).

End WCXpCheckerOn.

Module Type WCXpChecker.
    Declare Module E : InputProblem.
    Include WCXpCheckerOn E.
End WCXpChecker.


(* Default implementations of finders given a WCXp checker *)

Module MakeAXpFinderOn (Import E : InputProblem) (Chk : WCXpChecker with Module E := E) <: AXpFinderOn E.
    Module Import Xp := ExplainersDefs E.

    Local Definition checkWAXp X := negb (Chk.checkWCXp (S.compl X)).

    Definition findAXp := S.shrink checkWAXp.

    Module XpFacts := ExplanationsFacts E.

    Lemma checkWAXp_reflect :
        forall X, Bool.reflect (WAXp X) (checkWAXp X).
    Proof.
        intros X; unfold checkWAXp; destruct (Chk.checkWCXpSound (S.compl X)); constructor.
        -   now apply XpFacts.XpDual_uncompl_of_WCXp_is_not_WAXp.
        -   now apply XpFacts.XpDual_uncompl_of_not_WCXp_is_WAXp.
    Qed.

    Lemma findAXp_isWAXp :
        forall X, WAXp X -> WAXp (findAXp X).
    Proof.
        intros X H;
        apply (Bool.reflect_iff _ _ (checkWAXp_reflect X)),
            S.shrink_spec2 in H;
        now destruct (checkWAXp_reflect (S.shrink checkWAXp X)).
    Qed.

    Theorem findAXpSound :
        forall X, WAXp X -> AXp (findAXp X).
    Proof.
        intros X H; unfold findAXp; split.
        -   now apply findAXp_isWAXp.
        -   intros Y HSubs HY;
            apply S.shrink_spec3 with (p := checkWAXp);
                try (now apply (Bool.reflect_iff _ _ (checkWAXp_reflect _)));
                try assumption;
            intros s1 s2; rewrite <- 2 (Bool.reflect_iff _ _ (checkWAXp_reflect _));
            apply XpFacts.WAXp_monotonic.
    Qed.

    Theorem findAXpSane :
        forall X, E.S.Subset (findAXp X) X.
    Proof. apply S.shrink_spec1. Qed.

End MakeAXpFinderOn.

Module MakeAXpFinder (E_ : InputProblem) (Chk : WCXpChecker with Module E := E_) : AXpFinder with Module E := E_.
    Module E := E_.
    Module Impl := MakeAXpFinderOn E_ Chk.
    Include Impl.
End MakeAXpFinder.


Module MakeCXpFinderOn (Import E : InputProblem) (Chk : WCXpChecker with Module E := E) <: CXpFinderOn E.
    Module Import Xp := ExplainersDefs E.

    Definition findCXp := S.shrink Chk.checkWCXp.

    Module XpFacts := ExplanationsFacts E.

    Lemma findCXp_isWCXp :
        forall X, WCXp X -> WCXp (findCXp X).
    Proof.
        intros X H;
        apply (Bool.reflect_iff _ _ (Chk.checkWCXpSound X)),
            S.shrink_spec2 in H;
        now destruct (Chk.checkWCXpSound (S.shrink Chk.checkWCXp X)).
    Qed.

    Theorem findCXpSound :
        forall X, WCXp X -> CXp (findCXp X).
    Proof.
        intros X H; unfold findCXp; split.
        -   now apply findCXp_isWCXp.
        -   intros Y HSubs HY;
            apply S.shrink_spec3 with (p := Chk.checkWCXp);
                try (now apply (Bool.reflect_iff _ _ (Chk.checkWCXpSound _)));
                try assumption;
            intros s1 s2; rewrite <- 2 (Bool.reflect_iff _ _ (Chk.checkWCXpSound _));
            apply XpFacts.WCXp_monotonic.
    Qed.

    Theorem findCXpSane :
        forall X, E.S.Subset (findCXp X) X.
    Proof. apply S.shrink_spec1. Qed.

End MakeCXpFinderOn.

Module MakeCXpFinder (E_ : InputProblem) (Chk : WCXpChecker with Module E := E_) : CXpFinder with Module E := E_.
    Module E := E_.
    Module Impl := MakeCXpFinderOn E_ Chk.
    Include Impl.
End MakeCXpFinder.


(* Enumerate explanations *)

Module Type EnumeratorOn (Import E : InputProblem).
    Module Import Xp := EnumeratorsDefs E.

    Parameter s : Type.

    Parameter init : s.
    Parameter record : Xp -> s -> s.
    Parameter get : s -> option Xp.

    Axiom getSound : forall s X,
        get s = Some X -> isXp X.

    Axiom getComplete_1 : forall s X,
        get s = Some X ->
        @stateHasSeen _ init record X s ->
        False.

    Axiom getComplete_2 : forall s X,
        @stateWf _ init record s ->
        get s = None ->
        @stateHasSeen _ init record X s.

End EnumeratorOn.

Module Type Enumerator.
    Declare Module E : InputProblem.
    Include EnumeratorOn E.
End Enumerator.


Module Type IteratorOn (S : FinSet).

    Parameter s : Type.
    Parameter sat : S.t -> s -> Prop.

    Parameter init : s.
    Parameter pick : s -> option S.t.
    Parameter block_up : S.t -> s -> s.
    Parameter block_down : S.t -> s -> s.

    Axiom pick_sat : forall st X,
        pick st = Some X -> sat X st.

    Axiom pick_unsat : forall st X,
        pick st = None -> ~ sat X st.

    Axiom sat_init : forall X,
        sat X init.

    Axiom sat_block_up : forall st X Y,
        sat X (block_up Y st) <-> sat X st /\ ~ S.Subset Y X.

    Axiom sat_block_down : forall st X Y,
        sat X (block_down Y st) <-> sat X st /\ ~ S.Subset X Y.

End IteratorOn.

Module Type Iterator.
    Declare Module S : FinSet.
    Include IteratorOn S.
End Iterator.


Module MakeIterator     (S_ : FinSet)
                        (Import Sat : SatSolver)
                    : Iterator  with Module S := S_
                                with Definition s := cnf (S_.elt).

    Module S := S_.

    Definition s := cnf S.elt.

    Definition init : cnf S.elt := [].

    Definition pick (c : cnf S.elt) :=
        match solve c return option S.t with
        | SAT i => Some (S.init i)
        | UNSAT => None
        end.


    Local Lemma In_InA : forall (x : S.elt) (l : list S.elt),
        In x l -> SetoidList.InA eq x l.
    Proof. induction l; intros H; inversion H; [constructor 1 | constructor 2]; auto. Qed.

    Local Lemma NoDupA_NoDup : forall (l : list S.elt),
        SetoidList.NoDupA eq l -> NoDup l.
    Proof. induction l; intros H; inversion H; constructor; auto using In_InA. Qed.

    Local Definition clause_block (p : polarity) (X : S.t) : clause S.elt.
        refine (exist _ (map (fun x => (x, p)) (S.elements X)) _).
        apply FinFun.Injective_map_NoDup;
        [ intros x y H; now inversion H
        | cut (SetoidList.NoDupA eq (S.elements X));
          [ apply NoDupA_NoDup
          | apply S.elements_spec2w ] ].
    Defined.


    Definition block_up (X : S.t) (c : cnf S.elt) := clause_block neg X :: c.

    Definition block_down (X : S.t) (c : cnf S.elt) := clause_block pos (S.compl X) :: c.


    Definition sat X f := eval_cnf (fun x => S.mem x X) f = true.

    Theorem pick_sat : forall st X,
        pick st = Some X -> sat X st.
    Proof.
        intros st X; unfold pick, sat; intros H;
        destruct (solve st) as [I |] eqn:E; inversion H;
        apply sat_correct in E; rewrite eval_cnf_ext with (J := I); try assumption;
        intros x; destruct (I x) eqn:HI.
        -   apply S.mem_spec, S.In_init, HI.
        -   apply not_true_is_false; intros abs;
            apply S.mem_spec, S.In_init in abs;
            now rewrite abs in HI.
    Qed.

    Theorem pick_unsat : forall st X,
        pick st = None -> ~ sat X st.
    Proof.
        intros st X; unfold pick, sat; intros H;
        destruct (solve st) eqn:E; inversion H;
        eapply unsat_correct in E; now rewrite E.
    Qed.

    Theorem sat_init : forall X,
        sat X init.
    Proof. reflexivity. Qed.

    Theorem sat_block_up : forall (st : s) (X Y : S.t),
        sat X (block_up Y st) <-> sat X st /\ ~ S.Subset Y X.
    Proof.
        intros st X Y; unfold block_up, sat; simpl;
        rewrite andb_true_iff, existsb_exists; split.
        -   intros ((x & H1 & H2) & H3);
            apply in_map_iff in H1 as (y & H4 & H5);
            split; try assumption; intros abs;
            rewrite <- H4 in H2; simpl in H2; rewrite negb_true_iff in H2;
            apply In_InA, S.elements_spec1, abs, S.mem_spec in H5;
            now rewrite H2 in H5.
        -   intros (H1 & H2); split; try assumption;
            destruct (S.choose (S.diff Y X)) as [x |] eqn:H3.
            +   apply S.choose_spec1, S.diff_spec in H3 as [H3 H4];
                exists (x, neg); split.
                *   apply in_map_iff; exists x; split; try reflexivity;
                    apply S.elements_spec1 in H3;
                    rewrite SetoidList.InA_altdef, Exists_exists in H3;
                    destruct H3 as (y & H3 & H5); now rewrite H5.
                *   apply eq_true_not_negb; intros abs; now apply H4, S.mem_spec.
            +   exfalso; apply H2; intros x H4;
                apply S.choose_spec2 in H3;
                destruct (S.mem x X) eqn:H5; try (now apply S.mem_spec);
                exfalso; eapply H3, S.diff_spec;
                split; [apply H4 | intros abs; apply S.mem_spec in abs; now rewrite H5 in abs].
    Qed.

    Theorem sat_block_down : forall (st : s) (X Y : S.t),
        sat X (block_down Y st) <-> sat X st /\ ~ S.Subset X Y.
    Proof.
        intros st X Y; unfold block_down, sat; simpl;
        rewrite andb_true_iff, existsb_exists; split.
        -   intros ((x & H1 & H2) & H3);
            apply in_map_iff in H1 as (y & H4 & H5);
            split; try assumption; intros abs;
            rewrite <- H4 in H2; simpl in H2;
            apply In_InA, S.elements_spec1, S.In_compl in H5;
            now apply H5, abs, S.mem_spec.
        -   intros (H1 & H2); split; try assumption.
            destruct (S.choose (S.diff X Y)) as [x |] eqn:H3.
            +   apply S.choose_spec1, S.diff_spec in H3 as [H3 H4];
                exists (x, pos); split.
                *   apply in_map_iff; exists x; split; try reflexivity;
                    apply S.In_compl, S.elements_spec1 in H4;
                    rewrite SetoidList.InA_altdef, Exists_exists in H4;
                    destruct H4 as (y & H4 & H5); now rewrite H5.
                *   now apply S.mem_spec.
            +   exfalso; apply H2; intros x H4;
                apply S.choose_spec2 in H3;
                destruct (S.mem x Y) eqn:H5; try (now apply S.mem_spec);
                exfalso; eapply H3, S.diff_spec;
                split; [apply H4 | intros abs; apply S.mem_spec in abs; now rewrite H5 in abs].
    Qed.

End MakeIterator.


Module MakeEnumerator   (Import E_ : InputProblem)
                        (It : Iterator with Module S := E_.S)
                        (Chk : WCXpChecker with Module E := E_)
                        (FdCXp : CXpFinder with Module E := E_)
                        (FdAXp : AXpFinder with Module E := E_)
                    : Enumerator with Module E := E_ with Definition s := It.s.

    Module E := E_.
    Module Import Xp := EnumeratorsDefs E.
    Module Import XpFacts := ExplanationsFacts E.
    Module FP := FinSetProperties S.

    Definition s := It.s.
    Definition init := It.init.

    Definition record (X : Xp) (st : s) :=
        match X with
        | isAXp X => It.block_down (S.compl X) st
        | isCXp X => It.block_up X st
        end.

    Definition get (st : s) :=
        match It.pick st with
        | None => None
        | Some X =>
            match Chk.checkWCXp X with
            | true => Some (isCXp (FdCXp.findCXp X))
            | false => Some (isAXp (FdAXp.findAXp (S.compl X)))
            end
        end.

    Theorem getSound :
        forall s X, get s = Some X -> isXp X.
    Proof.
        intros s X H; unfold get in H;
        destruct (It.pick s) as [ S |]; try discriminate H;
        destruct (Chk.checkWCXpSound S) as [HS | HS]; inversion H;
        [ apply FdCXp.findCXpSound, HS
        | apply FdAXp.findAXpSound, XpDual_compl_of_not_WCXp_is_WAXp, HS ].
    Qed.

    Theorem getComplete_1 :
        forall s X, get s = Some X -> @stateHasSeen _ init record X s -> False.
    Proof.
        intros s X Hget abs; unfold get in Hget;
        destruct (It.pick s) as [ S |] eqn:Hsat; try discriminate Hget;
        apply It.pick_sat in Hsat;
        destruct (Chk.checkWCXpSound S) as [HWXp | HWXp];
        inversion Hget as [HX];
        induction abs as [X s Hwfs | X Y s Hwfs abs IH];
            try (
                destruct Y;
                try apply It.sat_block_down in Hsat;
                try apply It.sat_block_up in Hsat;
                destruct Hsat; apply IH; try assumption
            );
        rewrite <- HX in Hsat;
        try apply It.sat_block_down in Hsat;
        try apply It.sat_block_up in Hsat;
        destruct Hsat as (Hsat & H).
        -   apply H, FdCXp.findCXpSane.
        -   apply H, FP.Subset_compl; rewrite FP.compl_compl;
            apply FdAXp.findAXpSane.
    Qed.

    Theorem getComplete_2 :
        forall s X,
            @stateWf _ init record s ->
            get s = None ->
            @stateHasSeen _ init record X s.
    Admitted.

End MakeEnumerator.
