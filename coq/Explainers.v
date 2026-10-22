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

Module AXpIterativeFinderOn (Import E : InputProblem) (Chk : WCXpChecker with Module E := E) <: AXpFinderOn E.
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

End AXpIterativeFinderOn.

Module AXpIterativeFinder (E_ : InputProblem) (Chk : WCXpChecker with Module E := E_) : AXpFinder with Module E := E_.
    Module E := E_.
    Module Impl := AXpIterativeFinderOn E_ Chk.
    Include Impl.
End AXpIterativeFinder.


Module CXpIterativeFinderOn (Import E : InputProblem) (Chk : WCXpChecker with Module E := E) <: CXpFinderOn E.
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

End CXpIterativeFinderOn.

Module CXpIterativeFinder (E_ : InputProblem) (Chk : WCXpChecker with Module E := E_) : CXpFinder with Module E := E_.
    Module E := E_.
    Module Impl := CXpIterativeFinderOn E_ Chk.
    Include Impl.
End CXpIterativeFinder.


(* Enumerate explanations *)

Module Type EnumeratorOn (Import E : InputProblem).
    Module Import Xp := EnumeratorsDefs E.

    Parameter s : Type.

    Parameter init : s.
    Parameter record : Xp -> s -> s.

    Parameter get : s -> option Xp.

    Inductive IN (X : Xp) : s -> Prop :=
    | IN_last (st : s) : IN X (record X st)
    | IN_prev (st : s) (Y : Xp) : IN X st -> IN X (record Y st).

    Axiom getSound :
        forall s X, get s = Some X -> isXp X /\ ~ IN X s.

    Axiom getComplete :
        forall s X, get s = None -> isXp X -> IN X s.

End EnumeratorOn.

Module Type Enumerator.
    Declare Module E : InputProblem.
    Include EnumeratorOn E.
End Enumerator.


Module Type IteratorOn (S : FinSet).

    Parameter s : Type.

    Parameter init : s.

    Parameter pick : s -> option S.t.

    Parameter block_up : S.t -> s -> s.

    Parameter block_down : S.t -> s -> s.

    Axiom pick_block_up :
        forall X Y st, pick (block_up X st) = Some Y -> ~ S.Subset X Y.

    Axiom pick_block_down :
        forall X Y st, pick (block_down X st) = Some Y -> ~ S.Subset Y X.

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


    Theorem pick_block_up : forall (X Y : S.t) (st : s),
        pick (block_up X st) = Some Y -> ~ S.Subset X Y.
    Proof.
        unfold pick; intros X Y st H1 abs;
        destruct (solve (block_up X st)) as [I |] eqn:H2; inversion H1; subst Y;
        apply sat_correct in H2;
        apply andb_true_iff in H2 as (H2 & _);
        apply existsb_exists in H2 as (l & H2 & H3);
        apply in_map_iff in H2 as (x & H2 & H4);
        apply In_InA, S.elements_spec1, abs, S.In_init in H4;
        now rewrite <- H2 in H3; simpl in H3; rewrite H4 in H3.
    Qed.

    Theorem pick_block_down : forall (X Y : S.t) (st : s),
        pick (block_down X st) = Some Y -> ~ S.Subset Y X.
    Proof.
        unfold pick; intros X Y st H1 abs;
        destruct (solve (block_down X st)) as [I |] eqn:H2; inversion H1; subst Y;
        apply sat_correct in H2;
        apply andb_true_iff in H2 as (H2 & _);
        apply existsb_exists in H2 as (l & H2 & H3);
        apply in_map_iff in H2 as (x & H2 & H4);
        apply In_InA, S.elements_spec1, S.In_compl in H4;
        rewrite <- H2 in H3; simpl in H3; apply S.In_init in H3; auto.
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

    Inductive IN (X : Xp) : s -> Prop :=
    | IN_last (st : s) : IN X (record X st)
    | IN_prev (st : s) (Y : Xp) : IN X st -> IN X (record Y st).

    Theorem getSound :
        forall s X, get s = Some X -> isXp X /\ ~ IN X s.
    Admitted.

    Theorem getComplete :
        forall s X, get s = None -> isXp X -> IN X s.
    Admitted.

End MakeEnumerator.
